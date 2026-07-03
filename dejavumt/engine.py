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
        elif isinstance(g, (ast.Not, ast.Prev, ast.Once, ast.Hist)):
            walk(g.arg)
        elif isinstance(g, (ast.And, ast.Or, ast.Implies, ast.Iff, ast.Since, ast.Interval)):
            walk(g.left)
            walk(g.right)
        elif isinstance(g, (ast.Exists, ast.Forall)):
            walk(g.arg)

    walk(f)
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
        elif isinstance(g, (ast.Not, ast.Prev, ast.Once, ast.Hist)):
            walk(g.arg)
        elif isinstance(g, (ast.And, ast.Or, ast.Implies, ast.Iff, ast.Since, ast.Interval)):
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
        self.pre = [backend.false()] * n
        self.now = [backend.false()] * n
        self.strong = False          # if True, use solver-backed strong simplify
        self.weak = False            # if True, do no simplification/elimination at all

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

    def _pred_expr(self, name, args, event):
        """B[p(args)] for the current event: OR over the event's p-tuples."""
        b = self.backend
        tuples = event.get(name, [])
        psorts = self.pred_sorts.get(name, ["String"] * len(args))
        disjuncts = []
        for tup in tuples:
            conj = []
            for arg, val, s in zip(args, tup, psorts):
                conj.append(b.eq(self._term_expr(arg), b.lit(val, s)))
            disjuncts.append(b.and_(*conj) if conj else b.true())
        if not disjuncts:
            return b.false()
        return b.or_(*disjuncts)

    # --- per-event evaluation ---

    def step(self, event: Dict[str, List[Tuple]]) -> bool:
        """Process one event; return True if the property still holds."""
        b = self.backend
        now = self.now
        pre = self.pre
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
                v = b.not_(now[ch[0]])
            elif k == "and":
                v = b.and_(now[ch[0]], now[ch[1]])
            elif k == "or":
                v = b.or_(now[ch[0]], now[ch[1]])
            elif k == "implies":
                v = b.implies(now[ch[0]], now[ch[1]])
            elif k == "iff":
                v = b.iff(now[ch[0]], now[ch[1]])
            elif k == "prev":
                v = pre[ch[0]]
            elif k == "since":
                v = b.or_(now[ch[1]], b.and_(now[ch[0]], pre[i]))
            elif k == "once":
                v = b.or_(now[ch[0]], pre[i])
            elif k == "interval":
                v = b.or_(now[ch[0]], b.and_(b.not_(now[ch[1]]), pre[i]))
            elif k == "exists":
                v = self._eliminate(b.exists(self.consts[node.data], now[ch[0]]))
            elif k == "forall":
                v = self._eliminate(b.forall(self.consts[node.data], now[ch[0]]))
            else:
                raise RuntimeError(f"unknown node kind {k}")
            now[i] = self._normalize(v)
        holds = self._verdict(now[self.root])
        self.pre = now
        self.now = [b.false()] * len(self.nodes)
        return holds

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

    def render_tree(self, values=None, color=False) -> str:
        """Render the formula as an indented tree.  If `values` (a list of Z3
        formulas, one per node) is given, annotate each node with its value.
        With `color`, values are colored: green=true, red=false, orange=other."""
        GREEN, RED, YELLOW, RESET = "\033[32m", "\033[31m", "\033[33m", "\033[0m"
        lines: List[str] = []

        def fmt_val(i):
            if values is None:
                return ""
            e = values[i]
            s = self.backend.to_str(e)
            if color:
                c = (GREEN if self.backend.is_true(e)
                     else RED if self.backend.is_false(e) else YELLOW)
                s = c + s + RESET
            return "  " + s

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

    def step(self, event: Dict[str, List[Tuple]]) -> Dict[str, bool]:
        return {fm.name: fm.step(event) for fm in self.formulas}
