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

Quantifiers translate directly to Z3 quantifiers over the variable's (typed)
sort.  Each `now` formula is run through Z3's `simplify` to curb growth.
"""
from __future__ import annotations

from typing import Dict, List, Tuple

import z3

from . import ast


# ---------------------------------------------------------------------------
# Sorts
# ---------------------------------------------------------------------------

def _z3_sort(name: str):
    return {
        "String": z3.StringSort(),
        "Int": z3.IntSort(),
        "Real": z3.RealSort(),
        "Bool": z3.BoolSort(),
    }[name]


def _is_leaf(e) -> bool:
    return z3.is_const(e) or z3.is_var(e)


def z3_to_str(e, scope=None) -> str:
    """Pretty-print a Z3 expression in DejaVuMT's surface syntax (infix
    &, |, !, ->, =, <, ...; Exists/Forall), rather than Z3's Python-API form."""
    scope = scope or []

    def rec(x):
        return z3_to_str(x, scope)

    def wrap_not(x):
        s = z3_to_str(x, scope)
        return s if _is_leaf(x) or z3.is_true(x) or z3.is_false(x) else f"({s})"

    if z3.is_quantifier(e):
        names = [e.var_name(i) for i in range(e.num_vars())]
        q = "∀" if e.is_forall() else "∃"
        inner_scope = list(reversed(names)) + scope
        body = z3_to_str(e.body(), inner_scope)
        return "".join(f"{q} {n} . " for n in names) + body
    if z3.is_var(e):
        return scope[z3.get_var_index(e)]
    if z3.is_true(e):
        return "true"
    if z3.is_false(e):
        return "false"
    if z3.is_not(e):
        return "¬" + wrap_not(e.arg(0))
    if z3.is_and(e):
        return "(" + " ∧ ".join(rec(a) for a in e.children()) + ")"
    if z3.is_or(e):
        return "(" + " ∨ ".join(rec(a) for a in e.children()) + ")"
    if z3.is_implies(e):
        return f"({rec(e.arg(0))} → {rec(e.arg(1))})"
    for pred, op in ((z3.is_eq, "="), (z3.is_le, "<="), (z3.is_lt, "<"),
                     (z3.is_ge, ">="), (z3.is_gt, ">")):
        if pred(e):
            return f"{rec(e.arg(0))} {op} {rec(e.arg(1))}"
    for pred, op in ((z3.is_add, "+"), (z3.is_sub, "-"), (z3.is_mul, "*")):
        if pred(e):
            return "(" + f" {op} ".join(rec(a) for a in e.children()) + ")"
    if z3.is_string_value(e):
        return '"' + e.as_string() + '"'
    if z3.is_int_value(e):
        return str(e.as_long())
    if z3.is_const(e):
        return e.decl().name()
    return str(e).replace("\n", " ")


def _z3_literal(value, sort_name: str):
    if sort_name == "String":
        return z3.StringVal(str(value))
    if sort_name == "Int":
        return z3.IntVal(int(value))
    if sort_name == "Real":
        return z3.RealVal(float(value))
    if sort_name == "Bool":
        return z3.BoolVal(str(value).lower() == "true")
    raise ValueError(f"unknown sort {sort_name}")


# ---------------------------------------------------------------------------
# Macro expansion
# ---------------------------------------------------------------------------

def _subst_term(t: ast.Term, m: Dict[str, ast.Term]) -> ast.Term:
    if isinstance(t, ast.Var) and t.name in m:
        return m[t.name]
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
            # var op const  -> infer var from const's kind
            if isinstance(g.left, ast.Var) and isinstance(g.right, ast.Const):
                note(g.left.name, g.right.kind)
            if isinstance(g.right, ast.Var) and isinstance(g.left, ast.Const):
                note(g.right.name, g.left.kind)
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
                 pred_sorts: Dict[str, List[str]]):
        self.name = prop.name
        self.text = str(prop.body)  # source form of the property, for display
        self.pred_sorts = pred_sorts
        self.var_sorts = infer_var_sorts(body, pred_sorts)
        # Every variable needs a Z3 constant; default any uninferred sort to String.
        for v in collect_vars(body):
            self.var_sorts.setdefault(v, "String")
        self.consts: Dict[str, z3.ExprRef] = {
            v: z3.Const(v, _z3_sort(s)) for v, s in self.var_sorts.items()
        }
        self.nodes: List[_Node] = []
        self.root = self._compile(body)
        n = len(self.nodes)
        self.pre: List[z3.ExprRef] = [z3.BoolVal(False)] * n
        self.now: List[z3.ExprRef] = [z3.BoolVal(False)] * n
        self.solver = z3.Solver()
        self._qe = z3.Tactic("qe2")  # quantifier elimination for Exists/Forall nodes
        self.strong = False          # if True, use solver-backed ctx-solver-simplify
        self._ctx = z3.Tactic("ctx-solver-simplify")

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

    def _term_expr(self, t: ast.Term):
        if isinstance(t, ast.Var):
            if t.name not in self.consts:
                # Variable with no inferable sort: default to String.
                self.consts[t.name] = z3.Const(t.name, z3.StringSort())
                self.var_sorts[t.name] = "String"
            return self.consts[t.name]
        return _z3_literal(t.value, t.kind)

    def _compare_expr(self, c: ast.Compare):
        l = self._term_expr(c.left)
        r = self._term_expr(c.right)
        if c.op == "=":
            return l == r
        if c.op == "<":
            return l < r
        if c.op == "<=":
            return l <= r
        if c.op == ">":
            return l > r
        if c.op == ">=":
            return l >= r
        raise ValueError(f"bad operator {c.op}")

    def _pred_expr(self, name, args, event):
        """B[p(args)] for the current event: OR over the event's p-tuples."""
        tuples = event.get(name, [])
        psorts = self.pred_sorts.get(name, ["String"] * len(args))
        disjuncts = []
        for tup in tuples:
            conj = []
            for arg, val, s in zip(args, tup, psorts):
                lit = _z3_literal(val, s)
                conj.append(self._term_expr(arg) == lit)
            disjuncts.append(z3.And(*conj) if conj else z3.BoolVal(True))
        if not disjuncts:
            return z3.BoolVal(False)
        return z3.Or(*disjuncts)

    # --- per-event evaluation ---

    def step(self, event: Dict[str, List[Tuple]]) -> bool:
        """Process one event; return True if the property still holds."""
        now = self.now
        pre = self.pre
        for i, node in enumerate(self.nodes):
            k = node.kind
            ch = node.children
            if k == "true":
                v = z3.BoolVal(True)
            elif k == "false":
                v = z3.BoolVal(False)
            elif k == "const_expr":
                v = node.data
            elif k == "pred":
                v = self._pred_expr(node.data[0], node.data[1], event)
            elif k == "not":
                v = z3.Not(now[ch[0]])
            elif k == "and":
                v = z3.And(now[ch[0]], now[ch[1]])
            elif k == "or":
                v = z3.Or(now[ch[0]], now[ch[1]])
            elif k == "implies":
                v = z3.Implies(now[ch[0]], now[ch[1]])
            elif k == "iff":
                v = now[ch[0]] == now[ch[1]]
            elif k == "prev":
                v = pre[ch[0]]
            elif k == "since":
                v = z3.Or(now[ch[1]], z3.And(now[ch[0]], pre[i]))
            elif k == "once":
                v = z3.Or(now[ch[0]], pre[i])
            elif k == "interval":
                v = z3.Or(now[ch[0]], z3.And(z3.Not(now[ch[1]]), pre[i]))
            elif k == "exists":
                v = self._eliminate(z3.Exists([self.consts[node.data]], now[ch[0]]))
            elif k == "forall":
                v = self._eliminate(z3.ForAll([self.consts[node.data]], now[ch[0]]))
            else:
                raise RuntimeError(f"unknown node kind {k}")
            now[i] = self._normalize(v)
        holds = self._verdict(now[self.root])
        self.pre = now
        self.now = [z3.BoolVal(False)] * len(self.nodes)
        return holds

    def _normalize(self, v):
        """Normalize a node's formula.  `simplify` is fast but syntactic;
        `strong` additionally runs solver-backed ctx-solver-simplify, which
        collapses contradictions/subsumed terms that `simplify` leaves behind
        (at the cost of a solver call per node)."""
        s = z3.simplify(v)
        if self.strong:
            try:
                s = self._ctx(s).as_expr()
            except z3.Z3Exception:
                pass
        return s

    def _eliminate(self, q):
        """Eliminate the quantifier in `q`, returning an equivalent quantifier-
        free formula when the theory permits.  Falls back to `q` if QE cannot
        complete (e.g. unsupported string constraints)."""
        try:
            return self._qe(q).as_expr()
        except z3.Z3Exception:
            return q

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
            s = z3_to_str(e)
            if color:
                c = GREEN if z3.is_true(e) else RED if z3.is_false(e) else YELLOW
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
        f = z3.simplify(root_formula)
        if z3.is_true(f):
            return True
        if z3.is_false(f):
            return False
        # Closed formula: satisfiable iff valid.
        self.solver.push()
        self.solver.add(f)
        res = self.solver.check()
        self.solver.pop()
        return res == z3.sat


class Monitor:
    """Top-level monitor for a whole specification (one or more properties)."""

    def __init__(self, spec: ast.Spec):
        macros = {m.name: m for m in spec.macros}
        pred_sorts = {
            e.name: [p.sort for p in e.params] for e in spec.events
        }
        self.pred_sorts = pred_sorts
        self.formulas: List[FormulaMonitor] = []
        for prop in spec.properties:
            body = expand_macros(prop.body, macros)
            self.formulas.append(FormulaMonitor(prop, body, pred_sorts))

    def step(self, event: Dict[str, List[Tuple]]) -> Dict[str, bool]:
        return {fm.name: fm.step(event) for fm in self.formulas}
