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
    if isinstance(f, (ast.Not, ast.Prev, ast.Once, ast.Hist)):
        return type(f)(_subst(f.arg, m))
    if isinstance(f, (ast.TimedOnce, ast.TimedHist)):
        return type(f)(f.low, f.high, _subst(f.arg, m), f.disp)
    if isinstance(f, ast.TimedSince):
        return ast.TimedSince(_subst(f.left, m), f.low, f.high,
                              _subst(f.right, m), f.disp)
    if isinstance(f, (ast.And, ast.Or, ast.Implies, ast.Iff, ast.Since, ast.Interval)):
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
    if isinstance(f, (ast.TrueC, ast.FalseC, ast.Pred, ast.Compare)):
        return f
    if isinstance(f, (ast.Not, ast.Prev, ast.Once, ast.Hist)):
        return type(f)(expand_macros(f.arg, macros))
    if isinstance(f, (ast.TimedOnce, ast.TimedHist)):
        return type(f)(f.low, f.high, expand_macros(f.arg, macros), f.disp)
    if isinstance(f, ast.TimedSince):
        return ast.TimedSince(expand_macros(f.left, macros), f.low, f.high,
                              expand_macros(f.right, macros), f.disp)
    if isinstance(f, (ast.And, ast.Or, ast.Implies, ast.Iff, ast.Since, ast.Interval)):
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
            elif g.op in ("<", "<=", ">", ">="):
                # Order relation with no constant to fix the sort: remember the
                # variables so they default to Int (DejaVu compares order
                # relations numerically), unless something else types them.
                ordered_vars.update(vs)
        elif isinstance(g, (ast.Not, ast.Prev, ast.Once, ast.Hist,
                            ast.TimedOnce, ast.TimedHist)):
            walk(g.arg)
        elif isinstance(g, (ast.And, ast.Or, ast.Implies, ast.Iff, ast.Since,
                            ast.TimedSince, ast.Interval)):
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
        elif isinstance(g, ast.Compare):
            term(g.left)
            term(g.right)
        elif isinstance(g, (ast.Not, ast.Prev, ast.Once, ast.Hist,
                            ast.TimedOnce, ast.TimedHist)):
            walk(g.arg)
        elif isinstance(g, (ast.And, ast.Or, ast.Implies, ast.Iff, ast.Since,
                            ast.TimedSince, ast.Interval)):
            walk(g.left)
            walk(g.right)
        elif isinstance(g, (ast.Exists, ast.Forall)):
            out.add(g.var)
            walk(g.arg)

    walk(f)
    return out


# ---------------------------------------------------------------------------
# Compiled node
# ---------------------------------------------------------------------------

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
        self.timed = any(nd.kind == "tsince" for nd in self.nodes)
        self._time = None            # current event's timestamp (timed specs)
        self.strong = False          # if True, use solver-backed strong simplify
        self.weak = False            # if True, do no simplification/elimination at all
        self.gc_period = 0           # if > 0, prune dead terms every gc_period events
        self._steps = 0

    # --- compilation: flatten AST into post-order node list ---

    def _add(self, kind, children, data=None) -> int:
        self.nodes.append(_Node(kind, children, data))
        return len(self.nodes) - 1

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
            # H phi  ==  ! P ! phi
            return self._compile(ast.Not(ast.Once(ast.Not(f.arg))))
        if isinstance(f, ast.TimedSince):
            l = self._compile(f.left)
            r = self._compile(f.right)
            # The node's own time variable (one fresh Int constant per timed
            # node, with the same status as the data variables).
            tc = self.backend.const(f"_t{len(self.nodes)}", "Int")
            return self._add("tsince", [l, r], (f.low, f.high, tc))
        if isinstance(f, ast.TimedOnce):
            # P[a,b] phi  ==  true S[a,b] phi
            return self._compile_inner(
                ast.TimedSince(ast.TrueC(), f.low, f.high, f.arg, f.disp))
        if isinstance(f, ast.TimedHist):
            # H[a,b] phi  ==  ! P[a,b] ! phi
            return self._compile_inner(
                ast.Not(ast.TimedOnce(f.low, f.high, ast.Not(f.arg), f.disp)))
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
        return {"=": b.eq, "<": b.lt, "<=": b.le, ">": b.gt, ">=": b.ge}[c.op](l, r)

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

    def step(self, event: Dict[str, List[Tuple]], time: int = None) -> bool:
        """Process one event; return True if the property still holds.  For a
        timed property `time` is the event's (absolute, non-decreasing integer)
        timestamp."""
        if self.timed and time is None:
            raise ValueError(
                f"property {self.name} uses timed operators; "
                f"events need timestamps (timed log: last CSV column)")
        self._time = time
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
            elif k == "tsince":
                now[i] = self._tsince_state(node, nowval[ch[0]], nowval[ch[1]],
                                            pre[i])
                nowval[i] = self._tsince_value(node, now[i])
                continue
            elif k == "exists":
                v = self._eliminate(b.exists(self.consts[node.data], nowval[ch[0]]))
            elif k == "forall":
                v = self._eliminate(b.forall(self.consts[node.data], nowval[ch[0]]))
            else:
                raise RuntimeError(f"unknown node kind {k}")
            now[i] = self._normalize(v)
            nowval[i] = now[i]
        holds = self._verdict(nowval[self.root])
        self.pre = now
        self.preval = nowval
        self.now = [b.false()] * len(self.nodes)
        self._steps += 1
        if self.gc_period and self._steps % self.gc_period == 0:
            self._collect_garbage()
        return holds

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
        if self.weak:
            return S
        S = self._normalize(S)
        if hi is not None:
            # A record older than the upper bound is expired for good
            # (timestamps are non-decreasing), so drop it from the state:
            # its stamp t = T_j with T_j < T - hi is false under every
            # window the value query will ever apply.
            return self._normalize(b.prune_expired(S, tc, self._time - hi))
        # No upper bound: nothing expires, but a record past the lower bound
        # satisfies the window forever, so its timestamp is irrelevant ---
        # project it away, merging all matured records into one time-free
        # formula (the analogue of DejaVu's age saturation at n+1).
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
            q = b.and_(q, b.le(age, b.lit(hi, "Int")))
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
            if values is None:
                return ""
            if exported is not None and self.nodes[i].kind == "tsince":
                return f"  {paint(exported[i])}   state: {paint(values[i])}"
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

    def step(self, event: Dict[str, List[Tuple]], time: int = None) -> Dict[str, bool]:
        return {fm.name: fm.step(event, time) for fm in self.formulas}
