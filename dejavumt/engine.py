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
from .backend import Backend, make_backend


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
        return type(f)(f.var, _subst(f.arg, inner))
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
        return type(f)(f.var, expand_macros(f.arg, macros))
    raise TypeError(f"cannot expand {type(f).__name__}")


# ---------------------------------------------------------------------------
# Sort inference for variables
# ---------------------------------------------------------------------------

def infer_var_sorts(f: ast.LTL, pred_sorts: Dict[str, List[str]]) -> Dict[str, str]:
    """Infer each variable's sort from how it is used as a predicate argument
    (and, as a fallback, from constants it is compared against)."""
    sorts: Dict[str, str] = {}
    ordered_vars: set = set()   # variables occurring in an order relation

    def note(var: str, sort: str):
        if var in sorts and sorts[var] != sort:
            raise ValueError(
                f"variable {var} used at sorts {sorts[var]} and {sort}"
            )
        sorts[var] = sort

    def walk(g: ast.LTL):
        if isinstance(g, ast.Pred):
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
                    vs.add(e.name)
                elif isinstance(e, ast.Const):
                    ks.add(e.kind)
                elif isinstance(e, ast.BinExpr):
                    coll(e.left)
                    coll(e.right)
                elif isinstance(e, ast.Neg):
                    coll(e.arg)

            coll(g.left)
            coll(g.right)
            numeric = {k for k in ks if k in ("Int", "Real")}
            if len(numeric) == 1:
                s = next(iter(numeric))
                for v in vs:
                    note(v, s)
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
            walk(g.arg)

    walk(f)
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
    may be the UPPER bound of any timed operator (S, Z, P, H, F, G, U), and
    each parameter name may occur exactly once.  A past occurrence needs no
    nesting restriction (its verdict is known at its own position, and the
    state recurrences carry the parameter through like any constant); for
    the future operators the single positive occurrence keeps the verdict a
    threshold synthesized from witness delays, and the nesting restriction
    is enforced once the formula is compiled -- see
    FormulaMonitor.__init__."""
    counts: Dict[str, int] = {}

    def note(g):
        if isinstance(g.high, str):
            counts[g.high] = counts.get(g.high, 0) + 1

    def walk(g):
        if isinstance(g, (ast.TimedEventually, ast.TimedAlways,
                          ast.TimedOnce, ast.TimedHist)):
            note(g)
            walk(g.arg)
        elif isinstance(g, (ast.TimedSince, ast.TimedZince, ast.TimedUntil)):
            note(g)
            walk(g.left)
            walk(g.right)
        elif isinstance(g, (ast.Not, ast.Prev, ast.Once, ast.Hist, ast.Next,
                            ast.Exists, ast.Forall)):
            walk(g.arg)
        elif isinstance(g, (ast.And, ast.Or, ast.Implies, ast.Iff, ast.Since,
                            ast.Zince, ast.Interval)):
            walk(g.left)
            walk(g.right)

    walk(f)
    for name, c in counts.items():
        if c > 1:
            raise ValueError(
                f"parameter '{name}' occurs in {c} bounds; a parameter may "
                f"occur in exactly one")
    return sorted(counts)


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
                 pred_sorts: Dict[str, List[str]], backend: Backend):
        self.name = prop.name
        self.text = str(prop.body)  # source form of the property, for display
        self.pred_sorts = pred_sorts
        self.backend = backend
        self.var_sorts = infer_var_sorts(body, pred_sorts)
        # Every variable needs a solver constant; default any uninferred sort to String.
        for v in collect_vars(body):
            self.var_sorts.setdefault(v, "String")
        self.consts = {v: backend.const(v, s) for v, s in self.var_sorts.items()}
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
        # Running feasible region: the conjunction of the constraint-verdicts
        # emitted so far -- the parameter values under which every judged
        # position holds.  Only shrinks.
        self.region = backend.true() if self.params else None
        self.nodes: List[_Node] = []
        self.root = self._compile(body)
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
        # A parametric window never closes by deadline, so its node must stay
        # shallow: nested under a stateful or future operator, its exactness
        # (and hence the staged-resolution bookkeeping) would itself become a
        # region over the parameter -- out of the supported fragment.
        for j in self.fnodes:
            if isinstance(self.nodes[j].data["high"], str) and j in self.deep:
                raise ValueError(
                    f"parametric bound '{self.nodes[j].data['high']}' must "
                    f"not be nested under temporal operators "
                    f"(in {self.nodes[j].label or 'future subformula'})")
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
        fv = sorted(free_vars(f))
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
            return self._add("pred", [], (f.name, f.args))
        if isinstance(f, ast.Compare):
            return self._add("const_expr", [], self._compare_expr(f))
        if isinstance(f, ast.Match):
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
        if isinstance(f, ast.Exists):
            return self._add("exists", [self._compile(f.arg)], f.var)
        if isinstance(f, ast.Forall):
            return self._add("forall", [self._compile(f.arg)], f.var)
        raise TypeError(f"cannot compile {type(f).__name__}")

    # --- term / relation helpers ---

    def _term_expr(self, t):
        b = self.backend
        if isinstance(t, ast.Var):
            if t.name not in self.consts:
                # Variable with no inferable sort: default to String.
                self.consts[t.name] = b.const(t.name, "String")
                self.var_sorts[t.name] = "String"
            return self.consts[t.name]
        if isinstance(t, ast.Const):
            return b.lit(t.value, t.kind)
        if isinstance(t, ast.Neg):
            return b.neg(self._term_expr(t.arg))
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
        nowval = [None] * len(self.nodes)
        for i, node in enumerate(self.nodes):
            k = node.kind
            ch = node.children
            if k == "true":
                v = b.true()
            elif k == "false":
                v = b.false()
            elif k == "const_expr":
                v = node.data
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
                continue
            elif k == "zince":
                # phi Z psi: psi held strictly in the past (read at pre),
                # phi ever since through now.
                v = b.and_(nowval[ch[0]], b.or_(preval[ch[1]], pre[i]))
            elif k == "tsince":
                now[i] = self._tsince_state(node, nowval[ch[0]], nowval[ch[1]],
                                            pre[i])
                nowval[i] = self._tsince_value(node, now[i])
                continue
            elif k == "tzince":
                now[i] = self._tzince_state(node, nowval[ch[0]],
                                            preval[ch[1]], pre[i])
                nowval[i] = self._tsince_value(node, now[i])
                continue
            elif k == "tonce":
                # P[a,b] phi: stamped since-recurrence with phi = true.
                now[i] = self._tsince_state(node, b.true(), nowval[ch[0]],
                                            pre[i])
                nowval[i] = self._tsince_value(node, now[i])
                continue
            elif k == "thist":
                # H[a,b] phi: records of phi's failures; value = negated
                # projection.
                now[i] = self._tsince_state(node, b.true(),
                                            b.not_(nowval[ch[0]]), pre[i])
                nowval[i] = self._normalize(
                    b.not_(self._tsince_value(node, now[i])))
                continue
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
                continue
            elif k == "exists":
                v = self._eliminate(b.exists(self.consts[node.data], nowval[ch[0]]))
            elif k == "forall":
                v = self._eliminate(b.forall(self.consts[node.data], nowval[ch[0]]))
            else:
                raise RuntimeError(f"unknown node kind {k}")
            now[i] = self._normalize(v)
            nowval[i] = now[i]
        self.pre = now
        self.preval = nowval
        if self.future:
            # This position's verdict may depend on events not yet read: park
            # the root's value as an obligation.  Then resolve any placeholder
            # whose answer has become final (substituting it into states,
            # tables and obligations), and check the whole notebook -- the new
            # entry included: it resolves at once when the future parts turn
            # out not to matter.
            self.pending.append({"pos": self.position, "time": time,
                                 "vals": list(nowval)})
            self._resolve_bindings()
            resolved = self._check_pending()
        else:
            # A parametric verdict (free parameters in the root) is a
            # constraint, not a Boolean; without future operators it is
            # nevertheless final right here.
            v = nowval[self.root]
            resolved = [(self.position,
                         self._pverdict(b.simplify(v)) if self.params
                         else self._verdict(v))]
        self._prev_time = time
        self.now = [b.false()] * len(self.nodes)
        self._steps += 1
        if self.gc_period and self._steps % self.gc_period == 0:
            self._collect_garbage()
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
        body = b.and_(body, b.ge(stamp, b.lit(anchor + lo, "Int")))
        if hi is not None:
            # A symbolic (parametric) upper bound stays a free constant; the
            # eliminated query is then a formula over it.
            hiterm = (b.add(b.lit(anchor, "Int"), self.params[hi])
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
            hi_bound = nd.data["high"]
            if isinstance(hi_bound, str):
                # Parametric window: the query can only grow by later
                # witnesses.  Timestamps are non-decreasing, so any future
                # witness has delay >= max(low, elapsed) and contributes at
                # most  n >= that delay  -- a tight upper bracket, which
                # meets the lower one exactly when nothing later can matter
                # (e.g. F: the first witness is in; G: the first
                # counterexample is in).
                elapsed = 0 if clockval is None else clockval - anchor
                growth = b.ge(self.params[hi_bound],
                              b.lit(max(nd.data["low"], elapsed), "Int"))
                if nd.kind == "funtil":
                    # A future witness additionally needs its run alive:
                    # phi must have held from the anchor through now, so its
                    # contribution is bounded by the run's surviving data
                    # values as well.
                    A, _ = self.ftab[j]
                    alive = self._normalize(self._eliminate(b.exists(
                        nd.data["t"],
                        b.and_(A, b.eq(nd.data["t"],
                                       b.lit(ob["pos"], "Int"))))))
                    growth = b.and_(alive, growth)
                if nd.kind in FUTURE_NEGATED:
                    vlo, vhi = b.not_(b.or_(q, growth)), b.not_(q)
                else:
                    vlo, vhi = q, b.or_(q, growth)
            else:
                vlo, vhi = ((b.false(), val) if nd.kind in FUTURE_NEGATED
                            else (val, b.true()))
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
                    cur = self._fval(j, qb["pos"], qb["anchor"])
                    vlo, vhi = ((b.false(), cur)
                                if self.nodes[j].kind in FUTURE_NEGATED
                                else (cur, b.true()))
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
            return self._verdict(b.simplify(self._eliminate(root_lo)))
        if mixed:
            return None
        if self._verdict(b.simplify(self._eliminate(root_lo))):
            return True
        if not self._verdict(b.simplify(self._eliminate(root_hi))):
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
                (S,) = self.ftab[j]
                S = b.prune_expired(S, d["t"], oldest + d["low"])
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
        if lo > 0:
            q = b.and_(q, b.ge(age, b.lit(lo, "Int")))
        if hi is not None:
            # A symbolic (parametric) bound stays a free constant; the
            # eliminated value is then a formula over it.
            hiterm = (self.params[hi] if isinstance(hi, str)
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

    def _verdict(self, root_formula) -> bool:
        b = self.backend
        f = b.simplify(root_formula)
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
        self.formulas: List[FormulaMonitor] = []
        for prop in spec.properties:
            body = expand_macros(prop.body, macros)
            self.formulas.append(
                FormulaMonitor(prop, body, pred_sorts, self.backend))
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
