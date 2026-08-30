"""
Evaluation engine for DejaVuMT.

Each subformula node holds a Z3 formula over its free variables, kept in two
copies: `pre` (value at the previous position) and `now` (value at the current
position).  On every observed event the `now` formulas are recomputed bottom-up
from the children's `now` formulas and from `pre`, following the Boolean-formula
semantics of past-time LTL:

    B[true]            = true
    B[p(x)]            = OR over matching event tuples of (x = a)
    B[!phi]            = not B[phi]
    B[phi & psi]       = B[phi] and B[psi]
    B[@ phi]_i         = B[phi]_{i-1}              (i.e. pre[phi])
    B[phi S psi]_i     = B[psi]_i or (B[phi]_i and B[phi S psi]_{i-1})
    B[P phi]_i         = B[phi]_i or B[P phi]_{i-1}
    B[[phi,psi)]_i     = B[phi]_i or (not B[psi]_i and B[[phi,psi)]_{i-1})
    B[Exists x phi]    = Exists x . B[phi]
    B[Forall x phi]    = ForAll x . B[phi]

Quantifiers translate directly to solver quantifiers over the variable's (typed)
sort.  Each `now` formula is run through the solver's `simplify` to curb growth.

All solver-specific operations go through a pluggable `Backend` (see
backend.py), so the same engine runs on either Z3 or CVC5.
"""
from __future__ import annotations

from typing import Dict, List, Tuple

from . import ast
from .backend import Backend, make_backend, BV_SORTS

# Builtin bit-vector operations, usable in term position by name (infix
# &/| would collide with the Boolean connectives).
BVFUNS = {"band": "bvand", "bor": "bvor", "bxor": "bvxor",
          "bnot": "bvnot", "shl": "shl", "lshr": "lshr"}
BVARITY = {"band": 2, "bor": 2, "bxor": 2, "bnot": 1, "shl": 2, "lshr": 2}


# ---------------------------------------------------------------------------
# Macro expansion
# ---------------------------------------------------------------------------

def _subst_term(t, m: Dict[str, ast.Term]):
    if isinstance(t, ast.Var) and t.name in m:
        return m[t.name]
    if isinstance(t, ast.BinExpr):
        return ast.BinExpr(_subst_term(t.left, m), t.op, _subst_term(t.right, m))
    if isinstance(t, ast.Neg):
        return ast.Neg(_subst_term(t.arg, m))
    if isinstance(t, ast.FunApp):
        return ast.FunApp(t.name, tuple(_subst_term(a, m) for a in t.args))
    return t


def _subst(f: ast.LTL, m: Dict[str, ast.Term]) -> ast.LTL:
    """Substitute variables (by name) with terms throughout a formula."""
    if isinstance(f, (ast.TrueC, ast.FalseC)):
        return f
    if isinstance(f, ast.Pred):
        return ast.Pred(f.name, tuple(_subst_term(a, m) for a in f.args))
    if isinstance(f, ast.Compare):
        return ast.Compare(_subst_term(f.left, m), f.op, _subst_term(f.right, m))
    if isinstance(f, ast.Match):
        segs = []
        for seg in f.segments:
            if seg[0] != "hole":
                segs.append(seg)
                continue
            if seg[1] in m:
                tgt = m[seg[1]]
                if isinstance(tgt, ast.Var):
                    segs.append(("hole", tgt.name, seg[2]))
                elif isinstance(tgt, ast.Const) and tgt.kind == "String":
                    segs.append(("lit", str(tgt.value)))
                else:
                    raise TypeError(
                        f"cannot substitute {tgt} into pattern hole {seg[1]}")
            else:
                segs.append(seg)
        return ast.Match(_subst_term(f.subject, m), tuple(segs), f.pattern,
                         f.regex)
    if isinstance(f, (ast.Not, ast.Prev, ast.Once, ast.Hist, ast.Next)):
        return type(f)(_subst(f.arg, m))
    if isinstance(f, (ast.TimedOnce, ast.TimedHist,
                      ast.TimedEventually, ast.TimedAlways)):
        return type(f)(f.low, f.high, _subst(f.arg, m), f.disp)
    if isinstance(f, (ast.TimedSince, ast.TimedZince, ast.TimedUntil)):
        return type(f)(_subst(f.left, m), f.low, f.high,
                       _subst(f.right, m), f.disp)
    if isinstance(f, (ast.And, ast.Or, ast.Implies, ast.Iff, ast.Since,
                      ast.Zince, ast.Interval)):
        return type(f)(_subst(f.left, m), _subst(f.right, m))
    if isinstance(f, (ast.Exists, ast.Forall)):
        # Do not substitute the bound variable itself.
        inner = {k: v for k, v in m.items() if k != f.var}
        return type(f)(f.var, _subst(f.arg, inner), f.sort)
    raise TypeError(f"cannot substitute in {type(f).__name__}")


def expand_macros(f: ast.LTL, macros: Dict[str, ast.Macro]) -> ast.LTL:
    """Replace macro calls by their (recursively expanded) bodies."""
    if isinstance(f, ast.Pred) and f.name in macros:
        mac = macros[f.name]
        if len(mac.params) != len(f.args):
            raise ValueError(
                f"macro {mac.name} expects {len(mac.params)} args, got {len(f.args)}"
            )
        mapping = {p: a for p, a in zip(mac.params, f.args)}
        return expand_macros(_subst(mac.body, mapping), macros)
    if isinstance(f, (ast.TrueC, ast.FalseC, ast.Pred, ast.Compare, ast.Match)):
        return f
    if isinstance(f, (ast.Not, ast.Prev, ast.Once, ast.Hist, ast.Next)):
        return type(f)(expand_macros(f.arg, macros))
    if isinstance(f, (ast.TimedOnce, ast.TimedHist,
                      ast.TimedEventually, ast.TimedAlways)):
        return type(f)(f.low, f.high, expand_macros(f.arg, macros), f.disp)
    if isinstance(f, (ast.TimedSince, ast.TimedZince, ast.TimedUntil)):
        return type(f)(expand_macros(f.left, macros), f.low, f.high,
                       expand_macros(f.right, macros), f.disp)
    if isinstance(f, (ast.And, ast.Or, ast.Implies, ast.Iff, ast.Since,
                      ast.Zince, ast.Interval)):
        return type(f)(expand_macros(f.left, macros), expand_macros(f.right, macros))
    if isinstance(f, (ast.Exists, ast.Forall)):
        return type(f)(f.var, expand_macros(f.arg, macros), f.sort)
    raise TypeError(f"cannot expand {type(f).__name__}")


# ---------------------------------------------------------------------------
# Python functions in specs (the `python:` block)
# ---------------------------------------------------------------------------

_PYSORTS = {str: "String", int: "Int", float: "Real", bool: "Bool"}


def _coerce_val(v, sort):
    """Coerce a raw event argument (a string, from the CSV log) to the
    Python type of its declared sort, for state-variable expressions."""
    if sort in BV_SORTS:
        return int(str(v), 0)
    if sort == "Int":
        return int(v)
    if sort == "Real":
        return float(v)
    if sort == "Bool":
        return v if isinstance(v, bool) else str(v).lower() == "true"
    return v if not isinstance(v, str) else v


def load_pyfuns(code: str, backend: Backend):
    registry, _ns = load_pyblock(code, backend)
    return registry


def load_pyblock(code: str, backend: Backend):
    """Execute the spec's python block and register every function defined
    in it as an *interpreted* SMT function symbol: uninterpreted to the
    solver, with its graph supplied lazily by calling the (pure, memoized)
    Python function once an application's arguments become ground.
    Signatures come from mandatory type annotations
    (str -> String, int -> Int, float -> Real, bool -> Bool).  Returns
    (registry, namespace); the namespace is also the evaluation scope of
    state-variable expressions."""
    import inspect
    import textwrap
    ns: Dict[str, object] = {}
    if not code:
        return {}, ns
    # dont_inherit: this module's `from __future__ import annotations` must
    # not leak into the user's code (it would stringize their annotations).
    exec(compile(textwrap.dedent(code), "<spec-python>", "exec",
                 dont_inherit=True), ns)

    def sort_of(ann):
        if isinstance(ann, str):     # stringized annotation, be lenient
            ann = {"str": str, "int": int, "float": float,
                   "bool": bool}.get(ann, ann)
        return _PYSORTS.get(ann)

    out: Dict[str, dict] = {}
    for name, obj in ns.items():
        if not inspect.isfunction(obj):
            continue
        if obj.__code__.co_filename != "<spec-python>":
            continue          # imported helper, not defined in the block
        sig = inspect.signature(obj)
        arg_sorts = []
        for p in sig.parameters.values():
            s = sort_of(p.annotation)
            if s is None:
                raise ValueError(
                    f"python function '{name}': parameter '{p.name}' needs "
                    f"a type annotation (str, int, float, or bool)")
            arg_sorts.append(s)
        ret = sort_of(sig.return_annotation)
        if ret is None:
            raise ValueError(
                f"python function '{name}' needs a return type annotation "
                f"(-> str, int, float, or bool)")
        out[name] = {"fdecl": backend.func(name, arg_sorts, ret),
                     "fn": obj, "args": arg_sorts, "ret": ret}
    return out, ns


# ---------------------------------------------------------------------------
# Sort inference for variables
# ---------------------------------------------------------------------------

def _walk_formula(f, enter):
    """Generic traversal calling enter(node) on every subformula."""
    enter(f)
    if isinstance(f, (ast.Not, ast.Prev, ast.Once, ast.Hist, ast.Next,
                      ast.TimedOnce, ast.TimedHist,
                      ast.TimedEventually, ast.TimedAlways)):
        _walk_formula(f.arg, enter)
    elif isinstance(f, (ast.And, ast.Or, ast.Implies, ast.Iff, ast.Since,
                        ast.TimedSince, ast.Zince, ast.TimedZince,
                        ast.TimedUntil, ast.Interval)):
        _walk_formula(f.left, enter)
        _walk_formula(f.right, enter)
    elif isinstance(f, (ast.Exists, ast.Forall)):
        _walk_formula(f.arg, enter)


def _check_rules(main: ast.LTL, rules: Dict[str, ast.Rule]):
    """Well-formedness of rule calls, mirroring DejaVu: arguments are
    variables; arities match; inside a rule body every rule call sits below
    an @ (so recursion is a pure recurrence); rule bodies are past-time."""

    def check_calls(g, in_body, below_prev):
        if isinstance(g, ast.Pred) and g.name in rules:
            r = rules[g.name]
            if len(g.args) != len(r.params):
                raise ValueError(
                    f"rule '{g.name}' has {len(r.params)} parameter(s), "
                    f"called with {len(g.args)} argument(s)")
            for a in g.args:
                if not isinstance(a, ast.Var):
                    raise ValueError(
                        f"rule call {g}: arguments must be variables")
            if in_body and not below_prev:
                raise ValueError(
                    f"rule call {g} inside a rule body must be below the "
                    f"@ operator")
        if isinstance(g, ast.Prev):
            check_calls(g.arg, in_body, True)
        elif isinstance(g, (ast.Not, ast.Once, ast.Hist, ast.Next,
                            ast.TimedOnce, ast.TimedHist,
                            ast.TimedEventually, ast.TimedAlways)):
            check_calls(g.arg, in_body, below_prev)
        elif isinstance(g, (ast.And, ast.Or, ast.Implies, ast.Iff, ast.Since,
                            ast.TimedSince, ast.Zince, ast.TimedZince,
                            ast.TimedUntil, ast.Interval)):
            check_calls(g.left, in_body, below_prev)
            check_calls(g.right, in_body, below_prev)
        elif isinstance(g, (ast.Exists, ast.Forall)):
            check_calls(g.arg, in_body, below_prev)

    check_calls(main, False, False)
    for r in rules.values():
        def no_future(g):
            if isinstance(g, (ast.Next, ast.TimedUntil,
                              ast.TimedEventually, ast.TimedAlways)):
                raise ValueError(
                    f"rule '{r.name}': future operators are not supported "
                    f"in rule bodies")
        _walk_formula(r.body, no_future)
        check_calls(r.body, True, False)


def _rule_calls(f, rules):
    """All (name, argnames) rule calls in a formula."""
    out = []

    def enter(g):
        if isinstance(g, ast.Pred) and g.name in rules:
            out.append((g.name,
                        tuple(a.name for a in g.args
                              if isinstance(a, ast.Var))))

    _walk_formula(f, enter)
    return out


def infer_var_sorts(f: ast.LTL, pred_sorts: Dict[str, List[str]],
                    pyfuns: Dict[str, dict] = None,
                    state_sorts: Dict[str, str] = None,
                    enum_cons: Dict[str, str] = None) -> Dict[str, str]:
    """Infer each variable's sort from how it is used as a predicate argument
    (and, as a fallback, from constants it is compared against, or from a
    Python function's signature).  A state variable behaves like a constant
    of its declared sort; an enum constructor like a constant of its enum.
    Constant-based inference is DEFERRED (applied only to otherwise-unsorted
    variables), so an Int literal next to a declared bit-vector or enum
    variable does not conflict."""
    sorts: Dict[str, str] = {}
    ordered_vars: set = set()   # variables occurring in an order relation
    pending: list = []          # deferred (var, sort) suggestions
    pyfuns = pyfuns or {}
    state_sorts = state_sorts or {}
    enum_cons = enum_cons or {}
    enum_sorts = set(enum_cons.values())

    def note(var: str, sort: str):
        if var in sorts and sorts[var] != sort:
            raise ValueError(
                f"variable {var} used at sorts {sorts[var]} and {sort}"
            )
        sorts[var] = sort

    def note_app(name, args):
        reg = pyfuns.get(name)
        if reg is None:
            return
        for a, s in zip(args, reg["args"]):
            if isinstance(a, ast.Var):
                note(a.name, s)

    def walk(g: ast.LTL):
        if isinstance(g, ast.Pred):
            if g.name in pyfuns:      # Boolean Python function used as atom
                note_app(g.name, g.args)
                return
            psorts = pred_sorts.get(g.name)
            for j, arg in enumerate(g.args):
                if isinstance(arg, ast.Var) and psorts is not None and j < len(psorts):
                    note(arg.name, psorts[j])
        elif isinstance(g, ast.Match):
            if isinstance(g.subject, ast.Var):
                note(g.subject.name, "String")
            for seg in g.segments:
                if seg[0] == "hole":
                    note(seg[1], "String")
        elif isinstance(g, ast.Compare):
            # Collect the bare variables and constant kinds on both sides
            # (recursing through arithmetic).  If a single numeric kind
            # (Int/Real) appears, the bare variables are inferred to that kind.
            vs, ks = set(), set()

            def coll(e):
                if isinstance(e, ast.Var):
                    if e.name in state_sorts:
                        ks.add(state_sorts[e.name])
                    elif e.name in enum_cons:
                        ks.add(enum_cons[e.name])
                    else:
                        vs.add(e.name)
                elif isinstance(e, ast.Const):
                    ks.add(e.kind)
                elif isinstance(e, ast.BinExpr):
                    coll(e.left)
                    coll(e.right)
                elif isinstance(e, ast.Neg):
                    coll(e.arg)
                elif isinstance(e, ast.FunApp):
                    # An application behaves like a constant of its return
                    # sort; its arguments are typed by the signature.
                    reg = pyfuns.get(e.name)
                    if reg is not None:
                        ks.add(reg["ret"])
                        note_app(e.name, e.args)
                    for a in e.args:
                        if not isinstance(a, ast.Var):
                            coll(a)

            coll(g.left)
            coll(g.right)
            numeric = {k for k in ks if k in ("Int", "Real")
                       or k in enum_sorts}
            if len(numeric) == 1:
                s = next(iter(numeric))
                for v in vs:
                    pending.append((v, s))
            elif g.op == "contains":
                # `contains` is a string substring test; both operands are
                # String. Type its bare variables so they never default to Int.
                for v in vs:
                    note(v, "String")
            elif g.op in ("<", "<=", ">", ">="):
                # Order relation with no constant to fix the sort: remember the
                # variables so they default to Int (DejaVu compares order
                # relations numerically), unless something else types them.
                ordered_vars.update(vs)
        elif isinstance(g, (ast.Not, ast.Prev, ast.Once, ast.Hist, ast.Next,
                            ast.TimedOnce, ast.TimedHist,
                            ast.TimedEventually, ast.TimedAlways)):
            walk(g.arg)
        elif isinstance(g, (ast.And, ast.Or, ast.Implies, ast.Iff, ast.Since,
                            ast.TimedSince, ast.Zince, ast.TimedZince,
                            ast.TimedUntil, ast.Interval)):
            walk(g.left)
            walk(g.right)
        elif isinstance(g, (ast.Exists, ast.Forall)):
            if g.sort is not None:
                # Explicit annotation: authoritative, like a predicate
                # parameter declaration.
                note(g.var, g.sort)
            walk(g.arg)

    walk(f)
    # Deferred constant-based suggestions: only for otherwise-unsorted vars.
    for v, s in pending:
        sorts.setdefault(v, s)
    # Variables used in order relations but never otherwise typed default to
    # Int, matching DejaVu's numeric comparison semantics for < <= > >=.
    for v in ordered_vars:
        sorts.setdefault(v, "Int")
    return sorts


def collect_vars(f: ast.LTL) -> set:
    """All variable names occurring anywhere in the formula (free, bound, or in
    predicate/relation arguments)."""
    out = set()

    def term(t):
        if isinstance(t, ast.Var):
            out.add(t.name)
        elif isinstance(t, ast.BinExpr):
            term(t.left)
            term(t.right)
        elif isinstance(t, ast.Neg):
            term(t.arg)
        elif isinstance(t, ast.FunApp):
            for a in t.args:
                term(a)

    def walk(g):
        if isinstance(g, ast.Pred):
            for a in g.args:
                term(a)
        elif isinstance(g, ast.Match):
            term(g.subject)
            for seg in g.segments:
                if seg[0] == "hole":
                    out.add(seg[1])
        elif isinstance(g, ast.Compare):
            term(g.left)
            term(g.right)
        elif isinstance(g, (ast.Not, ast.Prev, ast.Once, ast.Hist, ast.Next,
                            ast.TimedOnce, ast.TimedHist,
                            ast.TimedEventually, ast.TimedAlways)):
            walk(g.arg)
        elif isinstance(g, (ast.And, ast.Or, ast.Implies, ast.Iff, ast.Since,
                            ast.TimedSince, ast.Zince, ast.TimedZince,
                            ast.TimedUntil, ast.Interval)):
            walk(g.left)
            walk(g.right)
        elif isinstance(g, (ast.Exists, ast.Forall)):
            out.add(g.var)
            walk(g.arg)

    walk(f)
    return out


def free_vars(f: ast.LTL) -> set:
    """Variable names occurring free in the formula (quantifier-bound ones
    excluded)."""
    if isinstance(f, (ast.Exists, ast.Forall)):
        return free_vars(f.arg) - {f.var}
    if isinstance(f, (ast.Not, ast.Prev, ast.Once, ast.Hist, ast.Next)):
        return free_vars(f.arg)
    if isinstance(f, (ast.TimedOnce, ast.TimedHist,
                      ast.TimedEventually, ast.TimedAlways)):
        return free_vars(f.arg)
    if isinstance(f, (ast.And, ast.Or, ast.Implies, ast.Iff, ast.Since,
                      ast.Zince, ast.Interval,
                      ast.TimedSince, ast.TimedZince, ast.TimedUntil)):
        return free_vars(f.left) | free_vars(f.right)
    if isinstance(f, (ast.Pred, ast.Compare, ast.Match)):
        return collect_vars(f)
    return set()


def collect_params(f: ast.LTL) -> list:
    """Names used as symbolic interval bounds (parametric monitoring), with
    the well-formedness checks of the supported fragment: a symbolic bound
    may be the upper OR the lower bound of any timed operator (S, Z, P, H,
    F, G, U).  A name that is IN SCOPE of a quantifier binding it is not a
    parameter but a DATA-DEPENDENT bound (`Forall n . a(n) -> F[0,n] b`:
    each a-event carries its own deadline; verdicts stay Boolean) -- those
    are collected by collect_bound_vars instead.  Parameters obey: exactly
    one occurrence each, at most one parameter bound per operator.
    Parametric operators may nest anywhere: past occurrences are known at
    their own position, and deep future occurrences resolve conservatively
    (see the deep-node comment in FormulaMonitor.__init__)."""
    counts: Dict[str, int] = {}

    def note(g, scope):
        unscoped = [bnd for bnd in (g.low, g.high)
                    if isinstance(bnd, str) and bnd not in scope]
        if len(unscoped) == 2:
            raise ValueError(
                f"at most one symbolic bound per operator (in {g})")
        for bound in unscoped:
            counts[bound] = counts.get(bound, 0) + 1

    def walk(g, scope):
        if isinstance(g, (ast.TimedEventually, ast.TimedAlways,
                          ast.TimedOnce, ast.TimedHist)):
            note(g, scope)
            walk(g.arg, scope)
        elif isinstance(g, (ast.TimedSince, ast.TimedZince, ast.TimedUntil)):
            note(g, scope)
            walk(g.left, scope)
            walk(g.right, scope)
        elif isinstance(g, (ast.Exists, ast.Forall)):
            walk(g.arg, scope | {g.var})
        elif isinstance(g, (ast.Not, ast.Prev, ast.Once, ast.Hist, ast.Next)):
            walk(g.arg, scope)
        elif isinstance(g, (ast.And, ast.Or, ast.Implies, ast.Iff, ast.Since,
                            ast.Zince, ast.Interval)):
            walk(g.left, scope)
            walk(g.right, scope)

    walk(f, frozenset())
    for name, c in counts.items():
        if c > 1:
            raise ValueError(
                f"parameter '{name}' occurs in {c} bounds; a parameter may "
                f"occur in exactly one")
    return sorted(counts)


def collect_bound_vars(f: ast.LTL) -> set:
    """Names used as DATA-DEPENDENT interval bounds: symbolic bounds that a
    quantifier in scope binds (`Forall n . a(n) -> F[0,n] b`)."""
    out = set()

    def walk(g, scope):
        if isinstance(g, (ast.TimedEventually, ast.TimedAlways,
                          ast.TimedOnce, ast.TimedHist)):
            out.update(bnd for bnd in (g.low, g.high)
                       if isinstance(bnd, str) and bnd in scope)
            walk(g.arg, scope)
        elif isinstance(g, (ast.TimedSince, ast.TimedZince, ast.TimedUntil)):
            out.update(bnd for bnd in (g.low, g.high)
                       if isinstance(bnd, str) and bnd in scope)
            walk(g.left, scope)
            walk(g.right, scope)
        elif isinstance(g, (ast.Exists, ast.Forall)):
            walk(g.arg, scope | {g.var})
        elif isinstance(g, (ast.Not, ast.Prev, ast.Once, ast.Hist, ast.Next)):
            walk(g.arg, scope)
        elif isinstance(g, (ast.And, ast.Or, ast.Implies, ast.Iff, ast.Since,
                            ast.Zince, ast.Interval)):
            walk(g.left, scope)
            walk(g.right, scope)

    walk(f, frozenset())
    return out


# ---------------------------------------------------------------------------
# Compiled node
# ---------------------------------------------------------------------------

# Future-operator node kinds.  Their value at a position generally depends on
# events not yet read, so instead of a value they contribute an obligation that
# is resolved later (see the "Bounded Future Operators" section of the paper).
FUTURE_KINDS = ("fev", "falw", "funtil", "fnext")
# Future nodes whose export is the negation of their table query.
FUTURE_NEGATED = ("falw",)
# Node kinds that are pure functions of their children's values (no state), so
# an obligation's value can be recomputed through them at check time.
STATELESS_KINDS = ("not", "and", "or", "implies", "iff", "exists", "forall")
# The sign of each operator's export in each of its children: +1 monotone,
# -1 antitone, 0 neither.  Every recurrence in this engine is monotone in its
# inputs except negation, the left of an implication, the right of an interval,
# and both sides of an iff (H exports a double negation, hence +1).
OPSIGNS = {
    "not": (-1,), "implies": (-1, 1), "iff": (0, 0),
    "and": (1, 1), "or": (1, 1), "exists": (1,), "forall": (1,),
    "prev": (1,), "since": (1, 1), "once": (1,), "hist": (1,),
    "zince": (1, 1), "interval": (1, -1),
    "tsince": (1, 1), "tzince": (1, 1), "tonce": (1,), "thist": (1,),
    "fev": (1,), "falw": (1,), "funtil": (1, 1), "fnext": (1,),
}


class _Node:
    __slots__ = ("kind", "children", "data", "label")

    def __init__(self, kind, children, data=None, label=""):
        self.kind = kind
        self.children = children
        self.data = data
        self.label = label  # source-form of the subformula, for debug output


class FormulaMonitor:
    """Monitors a single property against a stream of events."""

    def __init__(self, prop: ast.Property, body: ast.LTL,
                 pred_sorts: Dict[str, List[str]], backend: Backend,
                 pyfuns: Dict[str, dict] = None, rules=(),
                 statevals: Dict[str, object] = None,
                 state_sorts: Dict[str, str] = None,
                 enum_cons: Dict[str, str] = None,
                 pyns: Dict[str, object] = None):
        self.name = prop.name
        self.text = str(prop.body)  # source form of the property, for display
        # Anchored: evaluate at position 1 only (trace |= f), instead of the
        # default one-verdict-per-position (implicit-G) mode.
        self.anchored = prop.anchored
        self.pred_sorts = pred_sorts
        self.backend = backend
        # Interpreted Python functions (the spec's python block): SMT
        # function symbols whose graphs are supplied lazily; results are
        # memoized per monitor (functions must be pure).
        self.pyfuns = pyfuns or {}
        self.pycache: Dict[tuple, object] = {}
        self._pydecls = [r["fdecl"] for r in self.pyfuns.values()]
        # State variables: shared, mutable dict of ground values owned by
        # the Monitor (updated there before each step); read here as
        # per-position literals.
        self.statevals = statevals if statevals is not None else {}
        self.state_sorts = state_sorts or {}
        # Enum constructors: literals, resolved before variables.
        self.enum_cons = enum_cons or {}
        # Violation witnesses: position -> {var: value}, the falsifying
        # assignment of the property's leading Forall-prefix, extracted
        # from a solver model when a verdict comes out False.
        self.witnesses: Dict[int, dict] = {}
        # Side-effecting Python actions (evaluated in the python block's
        # namespace): per-rule `do {expr}` and the property's
        # `on violation {expr}`.
        self._pyns = pyns if pyns is not None else {}
        self._viol_action = (compile(prop.action, "<on-violation>", "eval")
                             if prop.action else None)
        self._rule_actions = {r.name: compile(r.action, f"<do-{r.name}>",
                                              "eval")
                              for r in rules if r.action}
        # Recursive rules (the property's where-clause): each rule's
        # extension is recomputed per position; recursion only under @.
        self.rules: Dict[str, ast.Rule] = {}
        for r in rules:
            if (r.name in self.rules or r.name in pred_sorts
                    or r.name in self.pyfuns or r.name in self.state_sorts):
                raise ValueError(
                    f"rule '{r.name}' collides with another rule, a "
                    f"predicate, a python function, or a state variable")
            if len(set(r.params)) != len(r.params):
                raise ValueError(
                    f"rule '{r.name}': duplicate parameters")
            fv = free_vars(r.body) - set(self.state_sorts)
            if fv != set(r.params):
                raise ValueError(
                    f"rule '{r.name}': free variables {sorted(fv)} must "
                    f"be exactly the parameters {list(r.params)}")
            self.rules[r.name] = r
        if self.rules:
            _check_rules(body, self.rules)
        self.var_sorts = self._infer_sorts(body)
        # Every variable needs a solver constant; default any uninferred sort
        # to String.  State variables are values, not variables: excluded.
        allvars = set(collect_vars(body))
        for r in self.rules.values():
            allvars |= collect_vars(r.body)
        allvars -= set(self.state_sorts)
        allvars -= set(self.enum_cons)
        for v in allvars:
            self.var_sorts.setdefault(v, "String")
        self.consts = {v: backend.const(v, self.var_sorts[v])
                       for v in allvars}
        # Parametric monitoring: symbolic interval bounds are Int constants
        # the engine simply never eliminates, so verdicts become constraints
        # on them (e.g. "holds iff n >= 7") instead of Booleans.
        self.pnames = collect_params(body)
        clash = set(self.pnames) & collect_vars(body)
        if clash:
            raise ValueError(
                f"parameter(s) {', '.join(sorted(clash))} also occur as data "
                f"variables; a parameter must be a fresh name")
        self.params = {p: backend.const(p, "Int") for p in self.pnames}
        # Data-dependent bounds: a quantified variable used as an interval
        # bound (`Forall n . a(n) -> F[0,n] b`).  The quantifier discharges
        # it, so verdicts stay Boolean; it must be an Int.
        self.databounds = collect_bound_vars(body)
        for v in sorted(self.databounds):
            if self.var_sorts.get(v) != "Int":
                raise ValueError(
                    f"data-dependent bound '{v}' must be an Int variable "
                    f"(declare the predicate parameter it comes from as Int)")
        # Running feasible region: the conjunction of the constraint-verdicts
        # emitted so far -- the parameter values under which every judged
        # position holds.  Only shrinks.
        self.region = backend.true() if self.params else None
        self.nodes: List[_Node] = []
        # Rule bodies compile FIRST (so a main-formula call finds its target
        # already computed within the step); recursion among bodies goes
        # through @, which reads the previous step's values, so body order
        # is irrelevant.
        self.ruleroot: Dict[str, int] = {}
        self._rule_ranges = []
        for r in self.rules.values():
            rstart = len(self.nodes)
            self.ruleroot[r.name] = self._compile(r.body)
            self._rule_ranges.append((rstart, len(self.nodes)))
        self.root = self._compile(body)
        # Nodes below an @ inside a rule body are deferred to the second
        # evaluation pass (see step): a recursive call there may read its
        # rule root's current value, which pass one computes.
        self._deferred = set()

        def _desc(i):
            for c in self.nodes[i].children:
                self._deferred.add(c)
                _desc(c)

        for rs, re_ in self._rule_ranges:
            for i in range(rs, re_):
                if self.nodes[i].kind == "prev":
                    _desc(i)
        self._deferred_order = sorted(self._deferred)
        n = len(self.nodes)
        # `pre`/`now` hold each node's stored formula (its state).  For every
        # untimed node the state is also the node's value; a timed ("tsince")
        # node stores its stamped relation S over the data variables plus its
        # time constant t, and exports the time-free projection instead.  The
        # exported values live in `preval`/`nowval`; enclosing nodes read those
        # (state and exported value coincide, sharing one object, for untimed
        # nodes).
        self.pre = [backend.false()] * n
        self.now = [backend.false()] * n
        self.preval = [backend.false()] * n
        # --- future operators: obligations, polarity, table storage ---
        self.fnodes = [j for j, nd in enumerate(self.nodes)
                       if nd.kind in FUTURE_KINDS]
        self.future = bool(self.fnodes)
        self.pending: List[dict] = []     # parked obligations (the notebook)
        self.position = 0                 # index of the last processed event
        self.ftab: Dict[int, tuple] = {}  # future node -> its stamped table(s)
        for j in self.fnodes:
            self.ftab[j] = ((backend.false(), backend.false())
                            if self.nodes[j].kind == "funtil"
                            else (backend.false(),))
        self._polarity = self._compute_polarity()
        # A future node is *deep* when its export flows into a stateful node
        # or into another future node's argument; its export is then an
        # uninterpreted placeholder, resolved by substitution later.  Shallow
        # nodes (only stateless ancestors) use the direct query mechanism.
        self.deep = self._deep_nodes()
        # Parametric future operators may also be DEEP (nested under other
        # temporal operators).  A symbolic upper bound gives its placeholder
        # no deadline, so early resolution would need region-guarded
        # bindings (exactness holds only for part of the parameter space);
        # instead such a placeholder simply never resolves early (_fexact is
        # False for it) and is substituted at end of trace -- or sooner when
        # its run dies, or when the obligation brackets (pointwise sound in
        # the parameter, refined by _fbrackets) already agree for every
        # parameter value.  Conservative in latency, exact in verdicts.
        self.qbind: List[dict] = []        # unresolved placeholder bindings
        self._qn = 0                       # fresh placeholder counter
        self._path = self._future_path()   # nodes recomputed when checking
        self.timed = (any(nd.kind in ("tsince", "tzince", "tonce", "thist")
                          for nd in self.nodes)
                      or any(self.nodes[j].data["clock"] == "time"
                             for j in self.fnodes))
        self._time = None            # current event's timestamp (timed specs)
        self._prev_time = None       # previous event's timestamp (tzince)
        self.strong = False          # if True, use solver-backed strong simplify
        self.weak = False            # if True, do no simplification/elimination at all
        self.gc_period = 0           # if > 0, prune dead terms every gc_period events
        self._steps = 0

    # --- compilation: flatten AST into post-order node list ---

    def _add(self, kind, children, data=None) -> int:
        self.nodes.append(_Node(kind, children, data))
        return len(self.nodes) - 1

    def _fdata(self, low, high, f, clock=None, witness=False):
        """Compile-time data of a future node: window, clock, its own time
        constants, and the free data variables of its subformula (the
        parameters of its placeholder, when it needs one).  A window that is
        neither bounded above nor delayed below ([0,*]) needs no timestamps,
        so it is stamped by position instead."""
        if clock is None:
            clock = "pos" if (low == 0 and high is None) else "time"
        n = len(self.nodes)
        b = self.backend
        # A data-dependent bound is one of the node's variables too: a deep
        # node's placeholder must take it as an argument, or the quantifier
        # binding it could not bind through the placeholder.
        fv = sorted((set(free_vars(f)) - set(self.state_sorts))
                    | {bnd for bnd in (low, high)
                       if isinstance(bnd, str) and bnd not in self.params})
        return {"low": low, "high": high, "clock": clock,
                "t": b.const(f"_ft{n}", "Int"),
                "t2": b.const(f"_fw{n}", "Int") if witness else None,
                # Witness rows also carry their POSITION: with duplicate
                # timestamps, a time in the window does not imply a position
                # at or after the anchor (until is immune: runs are per
                # position by construction).
                "p": b.const(f"_fp{n}", "Int"),
                "fvars": fv}

    def _compile(self, f: ast.LTL) -> int:
        idx = self._compile_inner(f)
        # Label the node with the source form of f (this also relabels rewritten
        # nodes, e.g. an H node compiled via !P! keeps its "H ..." label).
        self.nodes[idx].label = str(f)
        return idx

    def _compile_inner(self, f: ast.LTL) -> int:
        if isinstance(f, ast.TrueC):
            return self._add("true", [])
        if isinstance(f, ast.FalseC):
            return self._add("false", [])
        if isinstance(f, ast.Pred):
            if f.name in self.rules:
                # A rule call: value = the rule body's value with the
                # parameters renamed to the call's arguments.
                return self._add("rulecall", [],
                                 (f.name,
                                  tuple(a.name for a in f.args)))
            if f.name in self.state_sorts and not f.args:
                # A Bool state variable used as an atom.
                if self.state_sorts[f.name] != "Bool":
                    raise ValueError(
                        f"state '{f.name}' has sort "
                        f"{self.state_sorts[f.name]}; only Bool states can "
                        f"be used as atoms")
                return self._add("dyn", [], f)
            if f.name in self.pyfuns:
                # A Boolean Python function used as an atom.
                reg = self.pyfuns[f.name]
                if reg["ret"] != "Bool":
                    raise ValueError(
                        f"python function '{f.name}' returns {reg['ret']}; "
                        f"only bool functions can be used as atoms")
                if len(f.args) != len(reg["args"]):
                    raise ValueError(
                        f"python function '{f.name}' expects "
                        f"{len(reg['args'])} arguments, got {len(f.args)}")
                if self._mentions_state(f):
                    return self._add("dyn", [], f)
                expr = self.backend.apply(
                    reg["fdecl"], [self._term_expr(a) for a in f.args])
                return self._add("const_expr", [], expr)
            return self._add("pred", [], (f.name, f.args))
        if isinstance(f, ast.Compare):
            if self._mentions_state(f):
                return self._add("dyn", [], f)
            return self._add("const_expr", [], self._compare_expr(f))
        if isinstance(f, ast.Match):
            if self._mentions_state(f):
                return self._add("dyn", [], f)
            return self._add("const_expr", [], self._match_expr(f))
        if isinstance(f, ast.Not):
            return self._add("not", [self._compile(f.arg)])
        if isinstance(f, ast.And):
            return self._add("and", [self._compile(f.left), self._compile(f.right)])
        if isinstance(f, ast.Or):
            return self._add("or", [self._compile(f.left), self._compile(f.right)])
        if isinstance(f, ast.Implies):
            return self._add("implies", [self._compile(f.left), self._compile(f.right)])
        if isinstance(f, ast.Iff):
            return self._add("iff", [self._compile(f.left), self._compile(f.right)])
        if isinstance(f, ast.Prev):
            return self._add("prev", [self._compile(f.arg)])
        if isinstance(f, ast.Since):
            return self._add("since", [self._compile(f.left), self._compile(f.right)])
        if isinstance(f, ast.Once):
            return self._add("once", [self._compile(f.arg)])
        if isinstance(f, ast.Hist):
            # Dedicated node.  Semantically H phi = !P!phi; the node stores
            # the state of P!phi (the record of phi's failures, starting
            # false = vacuously true) and exports its negation.
            return self._add("hist", [self._compile(f.arg)])
        if isinstance(f, ast.Zince):
            # Dedicated node.  phi Z psi = phi & @(phi S psi): psi strictly in
            # the past, phi ever since (through now).  Reads psi's previous
            # value; evidence-style state, starts false.
            return self._add("zince",
                             [self._compile(f.left), self._compile(f.right)])
        if isinstance(f, ast.TimedSince):
            l = self._compile(f.left)
            r = self._compile(f.right)
            # The node's own time variable (one fresh Int constant per timed
            # node, with the same status as the data variables).
            tc = self.backend.const(f"_t{len(self.nodes)}", "Int")
            return self._add("tsince", [l, r], (f.low, f.high, tc))
        if isinstance(f, ast.TimedZince):
            l = self._compile(f.left)
            r = self._compile(f.right)
            tc = self.backend.const(f"_t{len(self.nodes)}", "Int")
            return self._add("tzince", [l, r], (f.low, f.high, tc))
        if isinstance(f, ast.TimedOnce):
            # Dedicated node.  Semantically P[a,b] phi = true S[a,b] phi;
            # the recurrence is the stamped since-recurrence with the
            # phi-conjunct dropped.
            tc = self.backend.const(f"_t{len(self.nodes)}", "Int")
            return self._add("tonce", [self._compile(f.arg)],
                             (f.low, f.high, tc))
        if isinstance(f, ast.TimedHist):
            # Dedicated node.  Semantically H[a,b] phi = !P[a,b]!phi; the
            # node stores stamped records of phi's failures and exports the
            # negated projection.
            tc = self.backend.const(f"_t{len(self.nodes)}", "Int")
            return self._add("thist", [self._compile(f.arg)],
                             (f.low, f.high, tc))
        if isinstance(f, ast.Next):
            # X phi: the future dual of @.  Stamped by POSITION, window [1,1].
            return self._add("fnext", [self._compile(f.arg)],
                             self._fdata(1, 1, f, clock="pos"))
        if isinstance(f, ast.TimedEventually):
            return self._add("fev", [self._compile(f.arg)],
                             self._fdata(f.low, f.high, f))
        if isinstance(f, ast.TimedAlways):
            # G[a,b] phi: table of phi's counterexamples; export = negation.
            return self._add("falw", [self._compile(f.arg)],
                             self._fdata(f.low, f.high, f))
        if isinstance(f, ast.TimedUntil):
            l = self._compile(f.left)
            r = self._compile(f.right)
            return self._add("funtil", [l, r],
                             self._fdata(f.low, f.high, f, witness=True))
        if isinstance(f, ast.Interval):
            return self._add("interval", [self._compile(f.left), self._compile(f.right)])
        if isinstance(f, (ast.Exists, ast.Forall)):
            if f.var in self.enum_cons:
                raise ValueError(
                    f"quantified variable '{f.var}' shadows an enum "
                    f"constructor")
            kind = "exists" if isinstance(f, ast.Exists) else "forall"
            return self._add(kind, [self._compile(f.arg)], f.var)
        raise TypeError(f"cannot compile {type(f).__name__}")

    # --- term / relation helpers ---

    def _infer_sorts(self, body):
        """Sort inference over the main body and every rule body, with
        rule-call argument sorts propagated from the parameters."""
        sorts = infer_var_sorts(body, self.pred_sorts, self.pyfuns,
                                self.state_sorts, self.enum_cons)

        def merge(d):
            for k, v in d.items():
                if k in sorts and sorts[k] != v:
                    raise ValueError(
                        f"variable {k} used at sorts {sorts[k]} and {v}")
                sorts[k] = v

        for r in self.rules.values():
            merge(infer_var_sorts(r.body, self.pred_sorts, self.pyfuns,
                                  self.state_sorts, self.enum_cons))
        for g in [body] + [r.body for r in self.rules.values()]:
            for name, args in _rule_calls(g, self.rules):
                for a, p in zip(args, self.rules[name].params):
                    if p in sorts:
                        merge({a: sorts[p]})
        return sorts

    def _mentions_state(self, x) -> bool:
        """Does a term/atom mention a state variable?"""
        if isinstance(x, ast.Var):
            return x.name in self.state_sorts
        if isinstance(x, ast.Pred):
            return (x.name in self.state_sorts
                    or any(self._mentions_state(a) for a in x.args))
        if isinstance(x, ast.Compare):
            return (self._mentions_state(x.left)
                    or self._mentions_state(x.right))
        if isinstance(x, ast.Match):
            return self._mentions_state(x.subject)
        if isinstance(x, ast.BinExpr):
            return (self._mentions_state(x.left)
                    or self._mentions_state(x.right))
        if isinstance(x, ast.Neg):
            return self._mentions_state(x.arg)
        if isinstance(x, ast.FunApp):
            return any(self._mentions_state(a) for a in x.args)
        return False

    def _dyn_expr(self, f):
        """Per-event value of an atom mentioning state variables (their
        current ground values are injected as literals)."""
        b = self.backend
        if isinstance(f, ast.Pred):
            if not f.args and f.name in self.state_sorts:
                return b.lit(self.statevals[f.name], "Bool")
            reg = self.pyfuns[f.name]     # Bool python function atom
            return b.apply(reg["fdecl"],
                           [self._term_expr(a) for a in f.args])
        if isinstance(f, ast.Compare):
            return self._compare_expr(f)
        if isinstance(f, ast.Match):
            return self._match_expr(f)
        raise TypeError(f"cannot evaluate dynamic atom {f}")

    def _term_expr(self, t):
        b = self.backend
        if isinstance(t, ast.Var):
            if t.name in self.state_sorts:
                # A state variable reads as its current ground value.
                return b.lit(self.statevals[t.name],
                             self.state_sorts[t.name])
            if t.name in self.enum_cons:
                # An enum constructor is a literal of its sort.
                return b.lit(t.name, self.enum_cons[t.name])
            if t.name not in self.consts:
                # Variable with no inferable sort: default to String.
                self.consts[t.name] = b.const(t.name, "String")
                self.var_sorts[t.name] = "String"
            return self.consts[t.name]
        if isinstance(t, ast.Const):
            return b.lit(t.value, t.kind)
        if isinstance(t, ast.Neg):
            return b.neg(self._term_expr(t.arg))
        if isinstance(t, ast.FunApp):
            if t.name in BVFUNS:
                if len(t.args) != BVARITY[t.name]:
                    raise ValueError(
                        f"{t.name} expects {BVARITY[t.name]} argument(s), "
                        f"got {len(t.args)}")
                args = [self._term_expr(a) for a in t.args]
                return getattr(b, BVFUNS[t.name])(*args)
            reg = self.pyfuns.get(t.name)
            if reg is None:
                raise ValueError(
                    f"unknown function '{t.name}' (not defined in a "
                    f"python block)")
            if len(t.args) != len(reg["args"]):
                raise ValueError(
                    f"python function '{t.name}' expects "
                    f"{len(reg['args'])} arguments, got {len(t.args)}")
            return b.apply(reg["fdecl"],
                           [self._term_expr(a) for a in t.args])
        if isinstance(t, ast.BinExpr):
            l = self._term_expr(t.left)
            r = self._term_expr(t.right)
            if t.op == "+":
                return b.add(l, r)
            if t.op == "-":
                return b.sub(l, r)
            if t.op == "*":
                return b.mul(l, r)
            raise ValueError(f"bad arithmetic operator {t.op}")
        raise TypeError(f"cannot build expression for {type(t).__name__}")

    def _compare_expr(self, c: ast.Compare):
        b = self.backend
        l = self._term_expr(c.left)
        r = self._term_expr(c.right)
        return {"=": b.eq, "<": b.lt, "<=": b.le, ">": b.gt, ">=": b.ge,
                "contains": b.contains}[c.op](l, r)

    def _match_expr(self, f: ast.Match):
        """subject matches a pattern, as a static constraint.

        Holes are the node's free String variables; gaps bind nothing.
        Unconstrained gaps at the pattern's ends compile to the native
        quantifier-free atoms (prefixof/suffixof/contains); every other gap
        becomes a fresh slack constant, existentially wrapped -- the shape on
        which string quantifier elimination may diverge, which the bounded
        qelim tolerates."""
        b = self.backend
        segs = list(f.segments)
        lead = segs and segs[0] == ("gap", None)
        trail = len(segs) > 1 and segs[-1] == ("gap", None)
        core = segs[1 if lead else 0: -1 if trail else len(segs)]

        parts, conjs, slacks = [], [], []
        for seg in core:
            if seg[0] == "lit":
                parts.append(b.lit(seg[1], "String"))
            elif seg[0] == "hole":
                _, name, rast = seg
                hole = self._term_expr(ast.Var(name))
                parts.append(hole)
                if rast is not None:
                    conjs.append(b.in_re(hole, rast))
            else:                                   # internal/constrained gap
                _, rast = seg
                g = b.const(f"_gap{len(self.nodes)}_{len(slacks)}", "String")
                slacks.append(g)
                parts.append(g)
                if rast is not None:
                    conjs.append(b.in_re(g, rast))
        subj = self._term_expr(f.subject)
        body = b.concat(parts)
        if lead and trail:
            base = b.contains(subj, body)
        elif lead:
            base = b.suffixof(body, subj)
        elif trail:
            base = b.prefixof(body, subj)
        else:
            base = b.eq(subj, body)
        out = b.and_(base, *conjs) if conjs else base
        for g in reversed(slacks):
            out = b.exists(g, out)
        return out

    def _arg_sort(self, arg, psorts, j):
        """Sort of predicate argument position j: from the declaration if
        given, else from the argument itself (a variable's inferred sort, or
        a constant's kind).  Undeclared positions must not blanket-default to
        String, or an Int-inferred variable would be compared to a String
        literal (sort mismatch)."""
        if psorts is not None and j < len(psorts):
            return psorts[j]
        if isinstance(arg, ast.Var):
            return self.var_sorts.get(arg.name, "String")
        if isinstance(arg, ast.Const):
            return arg.kind
        return "String"

    def _pred_expr(self, name, args, event):
        """B[p(args)] for the current event: OR over the event's p-tuples.
        Matching is arity-sensitive, as in DejaVu: a fact p(v1,..,vk) only
        matches an occurrence p(t1,..,tn) when k = n."""
        b = self.backend
        tuples = event.get(name, [])
        psorts = self.pred_sorts.get(name)
        disjuncts = []
        for tup in tuples:
            if len(tup) != len(args):
                continue
            conj = []
            for j, (arg, val) in enumerate(zip(args, tup)):
                s = self._arg_sort(arg, psorts, j)
                conj.append(b.eq(self._term_expr(arg), b.lit(val, s)))
            disjuncts.append(b.and_(*conj) if conj else b.true())
        if not disjuncts:
            return b.false()
        return b.or_(*disjuncts)

    # --- per-event evaluation ---

    def step(self, event: Dict[str, List[Tuple]], time: int = None):
        """Process one event; return the verdicts it determines, as a list of
        (position, holds) pairs.  Without future operators that is always the
        verdict for this position; with them a position's verdict may be
        emitted at a later event, and several may arrive at once.  For a timed
        property `time` is the event's (absolute, non-decreasing integer)
        timestamp."""
        if self.timed and time is None:
            raise ValueError(
                f"property {self.name} uses timed operators; "
                f"events need timestamps (timed log: last CSV column)")
        self._time = time
        self.position += 1
        b = self.backend
        now = self.now
        pre = self.pre
        preval = self.preval
        # Enclosing nodes read a child through its exported value (nowval),
        # never its stored state directly; the two differ only at timed nodes.
        # Evaluation is two-pass when rules are present: nodes below an @
        # inside a rule body are deferred to a second pass, so that a
        # recursive rule call there can read the rule root's value computed
        # in the first (its own now-value is only read NEXT step, through
        # the @'s preval).
        nowval = [None] * len(self.nodes)

        def compute(i, node):
            k = node.kind
            ch = node.children
            if k == "true":
                v = b.true()
            elif k == "false":
                v = b.false()
            elif k == "const_expr":
                v = node.data
            elif k == "dyn":
                # An atom mentioning state variables: rebuilt per event with
                # the current (ground) values as literals.
                v = self._dyn_expr(node.data)
            elif k == "rulecall":
                name, argnames = node.data
                v = nowval[self.ruleroot[name]]
                params = self.rules[name].params
                pairs = [(self.consts[p], self.consts[a])
                         for p, a in zip(params, argnames) if p != a]
                if pairs:
                    v = b.subst_consts(v, pairs)
            elif k == "pred":
                v = self._pred_expr(node.data[0], node.data[1], event)
            elif k == "not":
                v = b.not_(nowval[ch[0]])
            elif k == "and":
                v = b.and_(nowval[ch[0]], nowval[ch[1]])
            elif k == "or":
                v = b.or_(nowval[ch[0]], nowval[ch[1]])
            elif k == "implies":
                v = b.implies(nowval[ch[0]], nowval[ch[1]])
            elif k == "iff":
                v = b.iff(nowval[ch[0]], nowval[ch[1]])
            elif k == "prev":
                v = preval[ch[0]]
            elif k == "since":
                v = b.or_(nowval[ch[1]], b.and_(nowval[ch[0]], pre[i]))
            elif k == "once":
                v = b.or_(nowval[ch[0]], pre[i])
            elif k == "interval":
                v = b.or_(nowval[ch[0]], b.and_(b.not_(nowval[ch[1]]), pre[i]))
            elif k == "hist":
                # State = P!phi (the record of phi's failures); the exported
                # value is its negation.  Starting from false the state says
                # "no failure yet", i.e. H phi is vacuously true.
                s = b.or_(b.not_(nowval[ch[0]]), pre[i])
                now[i] = s if self.weak else self._normalize(s)
                nowval[i] = self._normalize(b.not_(now[i]))
                return
            elif k == "zince":
                # phi Z psi: psi held strictly in the past (read at pre),
                # phi ever since through now.
                v = b.and_(nowval[ch[0]], b.or_(preval[ch[1]], pre[i]))
            elif k == "tsince":
                now[i] = self._tsince_state(node, nowval[ch[0]], nowval[ch[1]],
                                            pre[i])
                nowval[i] = self._tsince_value(node, now[i])
                return
            elif k == "tzince":
                now[i] = self._tzince_state(node, nowval[ch[0]],
                                            preval[ch[1]], pre[i])
                nowval[i] = self._tsince_value(node, now[i])
                return
            elif k == "tonce":
                # P[a,b] phi: stamped since-recurrence with phi = true.
                now[i] = self._tsince_state(node, b.true(), nowval[ch[0]],
                                            pre[i])
                nowval[i] = self._tsince_value(node, now[i])
                return
            elif k == "thist":
                # H[a,b] phi: records of phi's failures; value = negated
                # projection.
                now[i] = self._tsince_state(node, b.true(),
                                            b.not_(nowval[ch[0]]), pre[i])
                nowval[i] = self._normalize(
                    b.not_(self._tsince_value(node, now[i])))
                return
            elif k in FUTURE_KINDS:
                # The node records what this event observed.  A *shallow* node
                # then exports its query's value over the table so far -- a
                # lower bound on the eventual answer.  A *deep* node's export
                # feeds a stateful recurrence or another future node's table,
                # where a lower bound would be frozen in, so it exports an
                # opaque placeholder instead, resolved by substitution once
                # its answer is final.
                clockval = self._clock(i, self.position, time)
                phi = nowval[ch[0]] if k == "funtil" else b.true()
                psi = nowval[ch[-1]]
                self._future_update(i, phi, psi, clockval)
                if i in self.deep and not self._fexact(
                        i, self.position, clockval, clockval):
                    nowval[i] = self._new_placeholder(i, clockval)
                else:
                    nowval[i] = self._fval(i, self.position, clockval)
                now[i] = self.ftab[i][0]      # for debug rendering
                return
            elif k == "exists":
                v = self._eliminate(b.exists(self.consts[node.data], nowval[ch[0]]))
            elif k == "forall":
                v = self._eliminate(b.forall(self.consts[node.data], nowval[ch[0]]))
            else:
                raise RuntimeError(f"unknown node kind {k}")
            now[i] = self._normalize(v)
            nowval[i] = now[i]

        for i, node in enumerate(self.nodes):
            if i in self._deferred:
                continue
            compute(i, node)
        for i in self._deferred_order:
            compute(i, self.nodes[i])
        # Rule actions: fire when the rule's extension is non-empty and
        # changed from the previous position, with a satisfying assignment
        # of its parameters bound (exact for functional rules).
        for rname, code in self._rule_actions.items():
            root = self.ruleroot[rname]
            ext = nowval[root]
            if b.is_false(ext) or not b.check_sat(ext):
                continue
            prev = preval[root]
            if prev is not None and not b.check_sat(b.not_(b.iff(ext, prev))):
                continue                      # unchanged extension
            consts = [self.consts[p] for p in self.rules[rname].params]
            env = dict(b.model_values(ext, consts) or {})
            env["pos"] = self.position
            try:
                eval(code, self._pyns, env)
            except Exception as exc:
                raise ValueError(
                    f"rule '{rname}' action failed at position "
                    f"{self.position}: {exc}") from exc
        self.pre = now
        self.preval = nowval
        if self.future:
            # This position's verdict may depend on events not yet read: park
            # the root's value as an obligation.  Then resolve any placeholder
            # whose answer has become final (substituting it into states,
            # tables and obligations), and check the whole notebook -- the new
            # entry included: it resolves at once when the future parts turn
            # out not to matter.  An anchored property parks position 1 only:
            # later positions are not judged (and once position 1 resolves,
            # the empty notebook keeps the tables cleared).
            if not self.anchored or self.position == 1:
                self.pending.append({"pos": self.position, "time": time,
                                     "vals": list(nowval)})
            self._resolve_bindings()
            resolved = self._check_pending()
        elif self.anchored and self.position > 1:
            resolved = []
        else:
            # A parametric verdict (free parameters in the root) is a
            # constraint, not a Boolean; without future operators it is
            # nevertheless final right here.
            v = nowval[self.root]
            verdict = (self._pverdict(b.simplify(v)) if self.params
                       else self._verdict(v))
            if verdict is False and not self.params:
                self._note_witness(self.position, nowval)
            resolved = [(self.position, verdict)]
        self._prev_time = time
        self.now = [b.false()] * len(self.nodes)
        self._steps += 1
        if self.gc_period and self._steps % self.gc_period == 0:
            self._collect_garbage()
        self._fire_violation_actions(resolved)
        return resolved

    # --- future operators: obligations and their resolution ---

    def _compute_polarity(self):
        """Each node's polarity with respect to the root: +1 if the root's
        value is monotone in this node's export, -1 if antitone, 0 if neither
        (under an iff).  Every recurrence is monotone or antitone in each
        input (OPSIGNS), so the sign composes along the path to the root ---
        through stateful operators as well."""
        pol = {}

        def go(i, p):
            pol[i] = p
            nd = self.nodes[i]
            signs = OPSIGNS.get(nd.kind, (0,) * len(nd.children))
            for idx, c in enumerate(nd.children):
                go(c, p * signs[idx])

        go(self.root, 1)
        return pol

    def _deep_nodes(self):
        parent = {}
        for i, nd in enumerate(self.nodes):
            for c in nd.children:
                parent[c] = i
        deep = set()
        for j in self.fnodes:
            i = parent.get(j)
            while i is not None:
                if self.nodes[i].kind not in STATELESS_KINDS:
                    deep.add(j)
                    break
                i = parent.get(i)
        return deep

    def _future_path(self):
        """The nodes recomputed when an obligation is checked: every shallow
        future node and its ancestors -- all stateless by the definition of
        shallow, so recomputation is exact.  Deep future nodes contribute
        through their placeholders instead."""
        parent = {}
        for i, nd in enumerate(self.nodes):
            for c in nd.children:
                parent[c] = i
        path = set()
        for j in self.fnodes:
            if j in self.deep:
                continue
            path.add(j)
            i = parent.get(j)
            while i is not None:
                path.add(i)
                i = parent.get(i)
        return sorted(path)

    def _clock(self, j, pos, time):
        return pos if self.nodes[j].data["clock"] == "pos" else time

    def _bound_term(self, bnd):
        """Solver term for a symbolic interval bound: a global parameter
        (parametric monitoring) or a quantified Int variable
        (data-dependent bound)."""
        if bnd in self.params:
            return self.params[bnd]
        return self.consts[bnd]

    def _future_update(self, j, phi, psi, clockval):
        """Extend a future node's table(s) with what this event observed.
        Everything recorded is an observed fact, stamped with the clock value
        of the position at which it was observed.  For until, a *run* is
        identified by the POSITION at which it starts (positions are unique;
        timestamps need not be), while the witness stamp uses the clock."""
        b = self.backend
        d = self.nodes[j].data
        t, t2 = d["t"], d["t2"]
        if self.nodes[j].kind == "funtil":
            A, W = self.ftab[j]
            # Runs that reach this position: those that survived the previous
            # one, plus the run starting here (identified by position).
            A = self._fnorm(b.or_(A, b.eq(t, b.lit(self.position, "Int"))))
            # A row of W is an answered run: the run begun at position t was
            # answered by a psi with clock stamp t2.  One witness answers every
            # run reaching here -- phi is required strictly *before* the
            # witness, so it is tested after this, not before.
            W = self._fnorm(b.or_(W, b.and_(psi, A,
                                            b.eq(t2, b.lit(clockval, "Int")))))
            # To reach the next position a run needs phi at this one.
            A = self._fnorm(b.and_(phi, A))
            self.ftab[j] = (A, W)
        else:
            (S,) = self.ftab[j]
            # For G the table records phi's counterexamples.  Each row carries
            # its clock stamp AND its position: with duplicate timestamps a
            # row in the time window may still lie before the anchor position.
            obs = b.not_(psi) if self.nodes[j].kind in FUTURE_NEGATED else psi
            self.ftab[j] = (self._fnorm(
                b.or_(S, b.and_(obs, b.eq(t, b.lit(clockval, "Int")),
                                b.eq(d["p"], b.lit(self.position, "Int"))))),)

    def _fnorm(self, v):
        return v if self.weak else self._normalize(v)

    def _fquery(self, j, pos, anchor):
        """The node's query for an obligation created at position `pos` with
        clock anchor `anchor`: is there a witness row whose stamp lies in the
        anchor's window (for until: belonging to this position's run)?  Both
        are concrete numerals; the stamp variables are what the query binds."""
        b = self.backend
        nd = self.nodes[j]
        d = nd.data
        lo, hi, t, t2 = d["low"], d["high"], d["t"], d["t2"]
        if nd.kind == "funtil":
            _, body = self.ftab[j]
            body = b.and_(body, b.eq(t, b.lit(pos, "Int")))
            stamp = t2
        else:
            (body,) = self.ftab[j]
            stamp = t
            # Future means positions >= the anchor's, not merely times in the
            # window (they differ when timestamps repeat).
            body = b.and_(body, b.ge(d["p"], b.lit(pos, "Int")))
        # A symbolic (parametric) bound stays a free constant; the eliminated
        # query is then a formula over it.
        loterm = (b.add(b.lit(anchor, "Int"), self._bound_term(lo))
                  if isinstance(lo, str) else b.lit(anchor + lo, "Int"))
        body = b.and_(body, b.ge(stamp, loterm))
        if hi is not None:
            hiterm = (b.add(b.lit(anchor, "Int"), self._bound_term(hi))
                      if isinstance(hi, str) else b.lit(anchor + hi, "Int"))
            body = b.and_(body, b.le(stamp, hiterm))
        q = b.exists(stamp, body)
        if nd.kind == "funtil":
            q = b.exists(t, q)
        else:
            q = b.exists(d["p"], q)
        return self._normalize(self._eliminate(q))

    def _fval(self, j, pos, anchor):
        """The node's export for this anchor, from the tables as they stand:
        the query's value, negated for G."""
        q = self._fquery(j, pos, anchor)
        return (self.backend.not_(q)
                if self.nodes[j].kind in FUTURE_NEGATED else q)

    def _new_placeholder(self, j, anchor):
        """A fresh opaque placeholder standing for this node's export at the
        current position: an uninterpreted predicate applied to the node's
        free data variables (so that quantifiers above bind through it)."""
        b = self.backend
        d = self.nodes[j].data
        params = [self.consts[v] for v in d["fvars"]]
        self._qn += 1
        fdecl = b.func(f"_q{j}_{self._qn}",
                       [self.var_sorts[v] for v in d["fvars"]])
        self.qbind.append({"node": j, "pos": self.position, "anchor": anchor,
                           "clock": d["clock"], "fdecl": fdecl,
                           "params": params})
        return b.apply(fdecl, params)

    def _subst_binding(self, qb, val):
        """A binding has resolved: substitute its value, as a function, into
        everything that may mention the placeholder -- node states, exported
        values, future tables, and parked obligations."""
        b = self.backend

        def sub(t):
            return b.substitute_fun(t, qb["fdecl"], qb["params"], val)

        self.pre = [b.simplify(sub(t)) for t in self.pre]
        self.preval = [b.simplify(sub(t)) for t in self.preval]
        for j2 in self.fnodes:
            self.ftab[j2] = tuple(self._fnorm(sub(t)) for t in self.ftab[j2])
        for ob in self.pending:
            ob["vals"] = [sub(t) for t in ob["vals"]]

    def _resolve_bindings(self, force=False):
        """Resolve every placeholder whose answer has become final: deadline
        passed (or run dead), and its node's tables free of other unresolved
        placeholders -- so resolution proceeds innermost-first through nested
        future operators.  With `force`, deadlines are ignored (end of
        trace)."""
        b = self.backend
        progress = True
        while progress and self.qbind:
            progress = False
            decls = [qb["fdecl"] for qb in self.qbind]
            for qb in list(self.qbind):
                j = qb["node"]
                clockval = (self.position if qb["clock"] == "pos"
                            else self._time)
                if not (force or self._fexact(j, qb["pos"], qb["anchor"],
                                              clockval)):
                    continue
                if any(b.mentions(t, decls) for t in self.ftab[j]):
                    continue
                val = self._fval(j, qb["pos"], qb["anchor"])
                self.qbind.remove(qb)
                self._subst_binding(qb, val)
                progress = True
                break

    def _fexact(self, j, pos, anchor, clockval):
        """Is the node's answer for this obligation already final?  It is once
        the deadline has passed -- no event can still land in the window;
        positions are strictly increasing, so a position-clocked window closes
        at equality, whereas timestamps only non-decrease, so a time-clocked
        one closes strictly after it -- and, for until, once the run is broken
        for every data value (no later witness can qualify; a satisfiability
        check, since the plain simplifier does not collapse the shape)."""
        b = self.backend
        d = self.nodes[j].data
        # A symbolic (parametric) bound gives no numeric deadline: the window
        # never closes early; obligations resolve by bracket agreement (see
        # _check) or at end of trace.
        if isinstance(d["high"], int):
            closed = (clockval >= anchor + d["high"]
                      if d["clock"] == "pos"
                      else clockval > anchor + d["high"])
            if closed:
                return True
        if self.nodes[j].kind == "funtil":
            A, _ = self.ftab[j]
            alive = b.and_(A, b.eq(d["t"], b.lit(pos, "Int")))
            if not b.check_sat(alive):
                return True
        return False

    def _fready(self, j):
        """A node's query value is only final once its tables mention no
        unresolved placeholder (of a nested future operator)."""
        b = self.backend
        decls = [qb["fdecl"] for qb in self.qbind]
        return not decls or not any(b.mentions(t, decls)
                                    for t in self.ftab[j])

    def _recompute(self, vals):
        """Recompute the root from the frozen values, with the future nodes
        replaced as given.  Only stateless nodes lie on the path, so this is an
        exact re-evaluation of that part of the tree."""
        b = self.backend
        for i in self._path:
            if i in self.ftab:
                continue
            nd = self.nodes[i]
            ch = nd.children
            k = nd.kind
            if k == "not":
                v = b.not_(vals[ch[0]])
            elif k == "and":
                v = b.and_(vals[ch[0]], vals[ch[1]])
            elif k == "or":
                v = b.or_(vals[ch[0]], vals[ch[1]])
            elif k == "implies":
                v = b.implies(vals[ch[0]], vals[ch[1]])
            elif k == "iff":
                v = b.iff(vals[ch[0]], vals[ch[1]])
            elif k == "exists":
                v = self._eliminate(b.exists(self.consts[nd.data], vals[ch[0]]))
            elif k == "forall":
                v = self._eliminate(b.forall(self.consts[nd.data], vals[ch[0]]))
            else:
                raise RuntimeError(f"non-stateless node {k} on future path")
            vals[i] = self._normalize(v)
        return vals[self.root]

    def _fbrackets(self, j, pos, anchor, clockval, q=None):
        """Lower/upper brackets of a future node's eventual export for this
        anchor, from the tables as they stand (tables only grow, so the
        brackets are pointwise sound for every parameter value).  Plain
        nodes: [query, true] (negated: [false, not query]).  A parametric
        upper bound refines the growing side: any future witness lies at
        delay >= max(low, elapsed) -- timestamps are non-decreasing -- and
        contributes at most  n >= that delay  (for until, only while its run
        stays alive), a bracket tight enough to close at the first witness
        (F) or counterexample (G)."""
        b = self.backend
        nd = self.nodes[j]
        if q is None:
            q = self._fquery(j, pos, anchor)
        hi_bound = nd.data["high"]
        if isinstance(hi_bound, str):
            elapsed = 0 if clockval is None else clockval - anchor
            lo_off = (nd.data["low"]
                      if isinstance(nd.data["low"], int) else 0)
            growth = b.ge(self._bound_term(hi_bound),
                          b.lit(max(lo_off, elapsed), "Int"))
            if nd.kind == "funtil":
                A, _ = self.ftab[j]
                alive = self._normalize(self._eliminate(b.exists(
                    nd.data["t"],
                    b.and_(A, b.eq(nd.data["t"], b.lit(pos, "Int"))))))
                growth = b.and_(alive, growth)
            if nd.kind in FUTURE_NEGATED:
                return b.not_(b.or_(q, growth)), b.not_(q)
            return q, b.or_(q, growth)
        val = b.not_(q) if nd.kind in FUTURE_NEGATED else q
        return ((b.false(), val) if nd.kind in FUTURE_NEGATED
                else (val, b.true()))

    def _check(self, ob, clockval_time, clockval_pos, force=False):
        """Check one obligation; return its verdict, or None if undecided.

        Each future node's eventual export lies between a lower and an upper
        bound derived from its table so far (tables only grow).  Substituting
        the bounds according to each node's polarity brackets the eventual
        verdict; the obligation resolves as soon as the brackets decide it, and
        at the latest when every query has become exact."""
        b = self.backend
        lo_vals, hi_vals = list(ob["vals"]), list(ob["vals"])
        all_exact, mixed = True, False
        # Shallow nodes: recompute their queries directly from the tables.
        for j in self.fnodes:
            if j in self.deep:
                continue
            nd = self.nodes[j]
            anchor = ob["pos"] if nd.data["clock"] == "pos" else ob["time"]
            clockval = clockval_pos if nd.data["clock"] == "pos" else clockval_time
            q = self._fquery(j, ob["pos"], anchor)
            val = b.not_(q) if nd.kind in FUTURE_NEGATED else q
            if ((force or self._fexact(j, ob["pos"], anchor, clockval))
                    and self._fready(j)):
                lo_vals[j] = hi_vals[j] = val
                continue
            all_exact = False
            # The export can still grow (or, when negated, shrink).
            vlo, vhi = self._fbrackets(j, ob["pos"], anchor, clockval, q=q)
            pol = self._polarity.get(j, 0)
            if pol > 0:
                lo_vals[j], hi_vals[j] = vlo, vhi
            elif pol < 0:
                lo_vals[j], hi_vals[j] = vhi, vlo
            else:
                mixed = True
                lo_vals[j], hi_vals[j] = vlo, vhi
        root_lo = self._recompute(lo_vals)
        root_hi = self._recompute(hi_vals) if not all_exact else root_lo
        # Deep placeholders still unresolved (in the frozen values, or inside
        # the shallow tables): bracket them too, by substituting bound
        # functions according to each node's polarity.  Repeated until no
        # placeholder remains -- a bound body may itself mention placeholders
        # of nodes nested more deeply.
        decls = [qb["fdecl"] for qb in self.qbind]
        if decls and (b.mentions(root_lo, decls) or b.mentions(root_hi, decls)):
            all_exact = False
            for _ in range(len(self.qbind) + 1):
                if not (b.mentions(root_lo, decls)
                        or b.mentions(root_hi, decls)):
                    break
                for qb in self.qbind:
                    j = qb["node"]
                    cv = (clockval_pos if qb["clock"] == "pos"
                          else clockval_time)
                    vlo, vhi = self._fbrackets(j, qb["pos"], qb["anchor"], cv)
                    pol = self._polarity.get(j, 0)
                    if pol == 0:
                        mixed = True
                        continue
                    blo, bhi = (vlo, vhi) if pol > 0 else (vhi, vlo)
                    root_lo = b.substitute_fun(root_lo, qb["fdecl"],
                                               qb["params"], blo)
                    root_hi = b.substitute_fun(root_hi, qb["fdecl"],
                                               qb["params"], bhi)
            if mixed and (b.mentions(root_lo, decls)
                          or b.mentions(root_hi, decls)):
                return None
        if self.params:
            # Parametric verdicts.  The root is a formula over the free
            # parameters; it is final when the two brackets agree for EVERY
            # parameter value, and the verdict is the constraint itself.
            lo = b.simplify(self._eliminate(root_lo))
            if all_exact:
                return self._pverdict(lo)
            if mixed:
                return None
            hi = b.simplify(self._eliminate(root_hi))
            if not b.check_sat(b.not_(b.iff(lo, hi))):
                return self._pverdict(lo)
            return None
        if all_exact:
            verdict = self._verdict(b.simplify(self._eliminate(root_lo)))
            if verdict is False:
                self._note_witness(ob["pos"], lo_vals)
            return verdict
        if mixed:
            return None
        if self._verdict(b.simplify(self._eliminate(root_lo))):
            return True
        if not self._verdict(b.simplify(self._eliminate(root_hi))):
            # The upper bracket is already false: any assignment falsifying
            # it genuinely violates.
            self._note_witness(ob["pos"], hi_vals)
            return False
        return None

    def _check_pending(self, force=False):
        """Check every parked obligation; return the verdicts resolved now, as
        (position, holds) pairs, and keep the rest."""
        out, keep = [], []
        for ob in self.pending:
            v = self._check(ob, self._time, self.position, force)
            if v is None:
                keep.append(ob)
            else:
                out.append((ob["pos"], v))
        self.pending = keep
        self._prune_futures()
        return out

    def _prune_futures(self):
        """Drop table rows that can serve no parked obligation and no
        unresolved placeholder: everything when both are empty, otherwise
        the rows older than the earliest window still awaited."""
        b = self.backend
        for j in self.fnodes:
            nd = self.nodes[j]
            d = nd.data
            binds = [qb for qb in self.qbind if qb["node"] == j]
            if not self.pending and not binds:
                self.ftab[j] = tuple(b.false() for _ in self.ftab[j])
                continue
            if self.weak:
                continue
            if nd.kind == "funtil":
                # Runs are identified by position, so prune by the earliest
                # position still awaited.
                oldest = min([ob["pos"] for ob in self.pending]
                             + [qb["pos"] for qb in binds])
                A, W = self.ftab[j]
                A = b.prune_expired(A, d["t"], oldest)
                W = b.prune_expired(W, d["t"], oldest)
                self.ftab[j] = (self._normalize(A), self._normalize(W))
            else:
                obs = [ob["pos"] if d["clock"] == "pos" else ob["time"]
                       for ob in self.pending]
                oldest = min(obs + [qb["anchor"] for qb in binds])
                # With a symbolic lower bound the window start is unknown,
                # but rows stamped before the earliest awaited anchor are
                # dead regardless (future witnesses lie at or after their
                # anchor's position, hence time).
                lo_off = d["low"] if isinstance(d["low"], int) else 0
                (S,) = self.ftab[j]
                S = b.prune_expired(S, d["t"], oldest + lo_off)
                self.ftab[j] = (self._normalize(S),)

    def end(self):
        """Close every window: resolve the remaining placeholders (innermost
        first) and force the remaining obligations to a verdict.  Called once
        the trace is over."""
        if not self.pending and not self.qbind:
            return []
        self._resolve_bindings(force=True)
        out = self._check_pending(force=True)
        self.pending = []
        self._fire_violation_actions(out)
        return out

    # --- timed since: stored state vs exported value ---

    def _tsince_state(self, node, phi, psi, prev_state):
        """New state S of a timed-since node:  S <- (B[psi] and t=T) or
        (B[phi] and S_pre), with records kept bounded by the two window
        bounds.  The upper bound is monotone (an expired record stays
        expired), so it is conjoined onto S and the contextual simplifier
        prunes expired records.  Without an upper bound nothing expires;
        instead records that have *matured* past the lower bound satisfy the
        window forever, so their timestamp is projected away, merging them
        into one time-free formula (the analogue of DejaVu's age
        saturation)."""
        b = self.backend
        lo, hi, tc = node.data
        T = b.lit(self._time, "Int")
        S = b.or_(b.and_(psi, b.eq(tc, T)), b.and_(phi, prev_state))
        return self._bound_state(node, S)

    def _tzince_state(self, node, phi, psi_pre, prev_state):
        """New state of a timed-zince node: like timed since, but the witness
        is psi's value at the PREVIOUS step, stamped with the previous
        timestamp, and phi is required at every step through now:
        S <- B[phi] and ((B[psi]_pre and t=T_pre) or S_pre)."""
        b = self.backend
        lo, hi, tc = node.data
        Tp = b.lit(self._prev_time if self._prev_time is not None else 0, "Int")
        S = b.and_(phi, b.or_(b.and_(psi_pre, b.eq(tc, Tp)), prev_state))
        return self._bound_state(node, S)

    def _bound_state(self, node, S):
        """Keep a timed node's freshly-updated state bounded.  The upper
        bound is monotone (an expired record stays expired), so expired
        records are deleted outright.  Without an upper bound nothing
        expires; instead records that have *matured* past the lower bound
        satisfy the window forever, so their timestamp is projected away,
        merging them into one time-free formula (the analogue of DejaVu's
        age saturation)."""
        b = self.backend
        lo, hi, tc = node.data
        if self.weak:
            return S
        S = self._normalize(S)
        if isinstance(hi, str):
            # Parametric upper bound: a record at any age is inside the
            # window for large enough parameter values, so nothing expires;
            # and outside it for small ones, so nothing saturates either.
            # State grows with the trace -- the price of parametric past.
            return S
        if hi is None and isinstance(lo, str):
            # Parametric lower bound with no upper: no expiry to prune by,
            # and maturation depends on the parameter, so no saturation
            # either.  State grows with the trace.  (With a concrete upper
            # bound, expiry pruning below stays valid whatever the lower
            # bound is.)
            return S
        if hi is not None:
            # A record's stamp t = T_j with T_j < T - hi is false under every
            # window the value query will ever apply (timestamps are
            # non-decreasing).
            return self._normalize(b.prune_expired(S, tc, self._time - hi))
        T = b.lit(self._time, "Int")
        age = b.sub(T, tc)
        mature = self._eliminate(
            b.exists(tc, b.and_(S, b.ge(age, b.lit(lo, "Int")))))
        young = b.and_(S, b.lt(age, b.lit(lo, "Int")))
        return self._normalize(b.or_(mature, young))

    def _tsince_value(self, node, state):
        """Exported value of a timed-since node: conjoin the window onto the
        state and project the time variable away."""
        b = self.backend
        lo, hi, tc = node.data
        T = b.lit(self._time, "Int")
        age = b.sub(T, tc)
        q = state
        # A symbolic (parametric) bound stays a free constant; the eliminated
        # value is then a formula over it.
        if isinstance(lo, str):
            q = b.and_(q, b.ge(age, self._bound_term(lo)))
        elif lo > 0:
            q = b.and_(q, b.ge(age, b.lit(lo, "Int")))
        if hi is not None:
            hiterm = (self._bound_term(hi) if isinstance(hi, str)
                      else b.lit(hi, "Int"))
            q = b.and_(q, b.le(age, hiterm))
        return self._normalize(self._eliminate(b.exists(tc, q)))

    def _collect_garbage(self):
        """Periodic dead-term reclamation.  Runs the backend's contextual
        simplifier over each stored formula, pruning the value-terms that have
        become dead in the recurrence but that the per-step syntactic simplifier
        leaves behind (the analogue of DejaVu's garbage collection of dead
        values).  Equivalence-preserving, so verdicts are unchanged.  Amortised:
        paid once every gc_period events rather than every step."""
        b = self.backend
        self.pre = [b.gc_simplify(p) for p in self.pre]

    def _normalize(self, v):
        """Normalize a node's formula.  `simplify` is fast but syntactic;
        `strong` additionally runs a solver-backed simplifier that collapses
        contradictions/subsumed terms (where the backend supports it).  `weak`
        does nothing, leaving the raw formula from the recurrence (debug only)."""
        if self.weak:
            return v
        s = self.backend.simplify(v)
        if self.pyfuns:
            # Fold applications of Python functions whose arguments have
            # become ground (event equalities make them so).
            s = self.backend.simplify(
                self.backend.eval_funs(s, self.pyfuns, self.pycache))
        if self.strong and self.backend.supports_strong:
            s = self.backend.strong_simplify(s)
        return s

    def _eliminate(self, q):
        """Eliminate the quantifier in `q`, returning an equivalent quantifier-
        free formula when the theory permits (the backend falls back to `q` if
        elimination cannot complete)."""
        if self.weak:
            return q
        return self.backend.qelim(q)

    # --- debug rendering ---

    def render_tree(self, values=None, exported=None, color=False) -> str:
        """Render the formula as an indented tree.  If `values` (a list of
        formulas, one per node — the stored states) is given, annotate each
        node with it.  If `exported` is also given, nodes whose exported value
        differs from their state (timed nodes) show the value first and the
        state after it.  With `color`, values are colored: green=true,
        red=false, yellow=other."""
        GREEN, RED, YELLOW, RESET = "\033[32m", "\033[31m", "\033[33m", "\033[0m"
        lines: List[str] = []

        def paint(e):
            s = self.backend.to_str(e)
            if color:
                c = (GREEN if self.backend.is_true(e)
                     else RED if self.backend.is_false(e) else YELLOW)
                s = c + s + RESET
            return s

        def fmt_val(i):
            # The unlabeled annotation is always the node's stored slot; where
            # the exported value differs (timed and H nodes) it follows,
            # labeled.
            if values is None:
                return ""
            if exported is not None and self.nodes[i].kind in (
                    "tsince", "tzince", "tonce", "thist", "hist") + FUTURE_KINDS:
                return f"  {paint(values[i])}   value: {paint(exported[i])}"
            return "  " + paint(values[i])

        def go(i, prefix, is_last, is_root):
            node = self.nodes[i]
            if is_root:
                connector = ""
            else:
                connector = "└─ " if is_last else "├─ "
            lines.append(f"{prefix}{connector}{node.label}{fmt_val(i)}")
            child_prefix = prefix + ("" if is_root else ("   " if is_last else "│  "))
            ch = node.children
            for k, c in enumerate(ch):
                go(c, child_prefix, k == len(ch) - 1, False)

        go(self.root, "", True, True)
        return "\n".join(lines)

    def _pverdict(self, f):
        """Verdict of a parametric obligation: True when the constraint holds
        for every parameter value, False when for none, otherwise the
        constraint on the parameters itself.  Also narrows the running
        feasible region by it."""
        b = self.backend
        self._residual_check(f)
        if b.is_true(f) or not b.check_sat(b.not_(f)):
            return True
        if b.is_false(f) or not b.check_sat(f):
            self.region = b.false()
            return False
        # The region is user-facing output: keep it free of subsumed
        # constraints (n>=7 already implies n>=3) rather than a growing
        # conjunction.  Two satisfiability checks per emitted constraint.
        if not b.check_sat(b.and_(self.region, b.not_(f))):
            pass                                  # region already implies f
        elif not b.check_sat(b.and_(f, b.not_(self.region))):
            self.region = f                       # f is strictly stronger
        else:
            self.region = b.simplify(b.and_(self.region, f))
        return f

    def _fire_violation_actions(self, resolved):
        """Run the property's `on violation` action once per emitted False
        verdict, in emission order, with `pos` and the witness values
        bound."""
        if not self._viol_action:
            return
        for pos, v in resolved:
            if v is not False:
                continue
            env = dict(self.witnesses.get(pos) or {})
            env["pos"] = pos
            try:
                eval(self._viol_action, self._pyns, env)
            except Exception as exc:
                raise ValueError(
                    f"property '{self.name}' on-violation action failed "
                    f"for position {pos}: {exc}") from exc

    def _witness(self, vals):
        """Falsifying assignment for the property's leading Forall-prefix,
        from a node-value array: a model of the negated prefix-child.  None
        when the root is not Forall-led, the child still mentions
        placeholders, or the solver yields no model."""
        b = self.backend
        i = self.root
        consts = []
        while self.nodes[i].kind == "forall":
            consts.append(self.consts[self.nodes[i].data])
            i = self.nodes[i].children[0]
        if not consts or vals[i] is None:
            return None
        body = vals[i]
        if self._pydecls and b.mentions(body, self._pydecls):
            return None
        if self.qbind and b.mentions(body, [qb["fdecl"] for qb in self.qbind]):
            return None
        try:
            return b.model_values(b.not_(body), consts)
        except Exception:
            return None

    def _note_witness(self, pos, vals):
        w = self._witness(vals)
        if w:
            self.witnesses[pos] = w

    def _residual_check(self, f):
        """A verdict must not depend on an application of a Python function
        that never became ground: the solver cannot evaluate it."""
        if self._pydecls and self.backend.mentions(f, self._pydecls):
            raise ValueError(
                f"property {self.name}: an application of a python "
                f"function never became ground -- guard its arguments "
                f"with an event predicate so the trace supplies them")

    def _verdict(self, root_formula) -> bool:
        b = self.backend
        f = b.simplify(root_formula)
        self._residual_check(f)
        if self.weak:
            # In weak mode the stored/displayed formula is left raw, so the root
            # may still contain quantifiers; eliminate them here (for the verdict
            # decision only) to keep the solver check decidable.
            f = b.simplify(b.qelim(f))
        if b.is_true(f):
            return True
        if b.is_false(f):
            return False
        # Closed formula: satisfiable iff valid.
        return b.check_sat(f)


class Monitor:
    """Top-level monitor for a whole specification (one or more properties)."""

    def __init__(self, spec: ast.Spec, solver: str = "z3"):
        macros = {m.name: m for m in spec.macros}
        pred_sorts = {
            e.name: [p.sort for p in e.params] for e in spec.events
        }
        self.pred_sorts = pred_sorts
        self.backend = make_backend(solver)
        # Enumeration sorts: declared on the backend; constructor names
        # become literals, and must be globally unique.
        self.enum_cons: Dict[str, str] = {}   # constructor -> sort name
        for e in spec.enums:
            self.backend.declare_enum(e.name, e.constructors)
            for c in e.constructors:
                if c in self.enum_cons or c in pred_sorts:
                    raise ValueError(
                        f"enum constructor '{c}' collides with another "
                        f"constructor or predicate")
                self.enum_cons[c] = e.name
        # Every declared parameter sort must exist.
        valid_sorts = ({"String", "Int", "Real", "Bool"} | set(BV_SORTS)
                       | {e.name for e in spec.enums})
        for e in spec.events:
            for p in e.params:
                if p.sort not in valid_sorts:
                    raise ValueError(
                        f"predicate {e.name}: unknown sort '{p.sort}' "
                        f"(builtin, BV8/16/32/64, or a declared enum)")

        def check_qsorts(g):
            if (isinstance(g, (ast.Exists, ast.Forall))
                    and g.sort is not None and g.sort not in valid_sorts):
                raise ValueError(
                    f"quantifier '{g.var}: {g.sort}': unknown sort "
                    f"(builtin, BV8/16/32/64, or a declared enum)")

        for prop in spec.properties:
            _walk_formula(prop.body, check_qsorts)
            for r in prop.rules:
                _walk_formula(r.body, check_qsorts)
        # Python functions from the spec's `python:` block, shared by all
        # properties (interpreted SMT symbols; see load_pyblock).  The
        # block's namespace is also the scope of state-variable expressions.
        self.pyfuns, self._pyns = load_pyblock(spec.python, self.backend)
        for n in self.pyfuns:
            if n in pred_sorts or n in macros or n in BVFUNS:
                raise ValueError(
                    f"python function '{n}' collides with a declared "
                    f"predicate, macro, or builtin bit-vector operation")
        # State variables: ground Python values updated per matching event
        # BEFORE the properties evaluate the event, read in formulas as
        # per-position literals.
        self.states: Dict[str, object] = {}
        self.state_sorts: Dict[str, str] = {}
        self._stateclauses = []
        for sv in spec.states:
            if (sv.name in pred_sorts or sv.name in macros
                    or sv.name in self.pyfuns or sv.name in self.state_sorts):
                raise ValueError(
                    f"state variable '{sv.name}' collides with a declared "
                    f"predicate, macro, python function, or state")
            self.state_sorts[sv.name] = sv.sort
            try:
                self.states[sv.name] = eval(
                    compile(sv.init, "<state-init>", "eval"), self._pyns, {})
            except Exception as exc:
                raise ValueError(
                    f"state '{sv.name}': initial expression "
                    f"{{{sv.init}}} failed: {exc}") from exc
            self._stateclauses.append(
                (sv.name, [(pname, params,
                            compile(expr, f"<state-{sv.name}>", "eval"))
                           for pname, params, expr in sv.clauses]))
        self.formulas: List[FormulaMonitor] = []
        for prop in spec.properties:
            body = expand_macros(prop.body, macros)
            rules = tuple(ast.Rule(r.name, r.params,
                                   expand_macros(r.body, macros), r.action)
                          for r in prop.rules)
            self.formulas.append(
                FormulaMonitor(prop, body, pred_sorts, self.backend,
                               self.pyfuns, rules=rules,
                               statevals=self.states,
                               state_sorts=self.state_sorts,
                               enum_cons=self.enum_cons,
                               pyns=self._pyns))
        # Timed specs read their logs with a timestamp as the last CSV column.
        self.timed = any(fm.timed for fm in self.formulas)
        # With future operators verdicts may be delayed; the caller must run
        # end() after the last event to close the remaining windows.
        self.future = any(fm.future for fm in self.formulas)
        self.resolved = []

    def step(self, event: Dict[str, List[Tuple]], time: int = None):
        """Process one event.  Returns the verdict of each property *for this
        position*: True, False, or None when it is still pending (only
        possible with future operators).  For a parametric property (a
        symbolic bound, e.g. F[<=n]) a verdict may instead be a backend
        formula: the constraint on the parameter under which the position
        holds.  Verdicts resolved during this step, for this position or an
        earlier one, are collected in `self.resolved` as (position, property,
        holds) triples."""
        out, self.resolved = {}, []
        # State variables update first: the properties see the values
        # INCLUDING this event's effect (matching the rule reading, whose
        # body pairs the event with the @-previous value).  Multiple
        # matching facts fold left-to-right.
        for name, clauses in self._stateclauses:
            for pname, params, code in clauses:
                psorts = self.pred_sorts.get(pname)
                for tup in event.get(pname, []):
                    if len(tup) != len(params):
                        continue
                    env = dict(self.states)
                    for j, (p, v) in enumerate(zip(params, tup)):
                        s = psorts[j] if psorts and j < len(psorts) else None
                        env[p] = _coerce_val(v, s)
                    try:
                        self.states[name] = eval(code, self._pyns, env)
                    except Exception as exc:
                        raise ValueError(
                            f"state '{name}': on {pname}{tup}: {exc}") from exc
        for fm in self.formulas:
            res = fm.step(event, time)
            for pos, holds in res:
                self.resolved.append((pos, fm.name, holds))
            out[fm.name] = next((h for p, h in res if p == fm.position), None)
        return out

    def end(self):
        """Close the trace: force the remaining obligations to a verdict.
        Returns a list of (position, property, holds), earliest first."""
        out = []
        for fm in self.formulas:
            out += [(pos, fm.name, holds) for pos, holds in fm.end()]
        out.sort(key=lambda r: r[0])
        self.resolved = out
        return out
