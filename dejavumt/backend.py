"""
Solver backends for DejaVuMT.

The evaluation engine (engine.py) is written against the small `Backend`
interface below, so the same incremental recurrence can run on different SMT
solvers.  Only the leaf-level solver primitives live here — term construction,
sorts, literals, the connectives/relations/arithmetic, quantifiers, quantifier
elimination, simplification, satisfiability and pretty-printing.  Two
implementations are provided: `Z3Backend` (default) and `Cvc5Backend`.

Each backend represents formulas as its own native term type; the engine treats
those terms as opaque and only combines them through backend methods.
"""
from __future__ import annotations

from fractions import Fraction


# ---------------------------------------------------------------------------
# Interface
# ---------------------------------------------------------------------------

class Backend:
    """Interface a solver must provide.  Term objects are opaque to the engine."""

    name = "backend"
    supports_strong = False  # whether strong_simplify does more than simplify

    # sorts / constants / literals
    def const(self, name: str, sort_name: str): ...
    def lit(self, value, sort_name: str): ...
    def true(self): ...
    def false(self): ...

    # boolean connectives
    def and_(self, *a): ...
    def or_(self, *a): ...
    def not_(self, a): ...
    def implies(self, a, b): ...
    def iff(self, a, b): ...

    # relations
    def eq(self, a, b): ...
    def lt(self, a, b): ...
    def le(self, a, b): ...
    def gt(self, a, b): ...
    def ge(self, a, b): ...

    # arithmetic
    def add(self, a, b): ...
    def sub(self, a, b): ...
    def mul(self, a, b): ...
    def neg(self, a): ...

    # quantifiers (over a free constant, which becomes the bound variable)
    def exists(self, const, body): ...
    def forall(self, const, body): ...

    # normalisation / solving
    def simplify(self, t): ...
    def strong_simplify(self, t): return self.simplify(t)
    def gc_simplify(self, t): return self.simplify(t)   # dead-term reclamation
    def qelim(self, q): ...

    # uninterpreted placeholder functions (future-operator machinery)
    def func(self, name: str, arg_sorts): ...
    def apply(self, f, args): ...

    def substitute_fun(self, t, f, params, body):
        """Replace every application f(a1..an) in t by body[params := a1..an],
        correctly under binders.  `params` are the constants body is written
        over."""
        ...

    def mentions(self, t, fs) -> bool:
        """Does t contain an application of any of the given functions?"""
        ...

    def prune_expired(self, t, tc, deadline: int):
        """Replace every atom  tc = c  (c a concrete integer < deadline)
        occurring in a positive position (under and/or only) by false --- used
        by timed operators to drop expired records from a stored state.  The
        default keeps the formula unchanged, which is always sound (the value
        query re-tests the window)."""
        return t
    def is_true(self, t) -> bool: ...
    def is_false(self, t) -> bool: ...
    def check_sat(self, t) -> bool: ...

    # rendering
    def to_str(self, t) -> str: ...


# ---------------------------------------------------------------------------
# Z3
# ---------------------------------------------------------------------------

class Z3Backend(Backend):
    name = "z3"
    supports_strong = True

    def __init__(self):
        import z3
        self.z3 = z3
        self._solver = z3.Solver()
        self._qe = z3.Tactic("qe2")
        self._ctx = z3.Tactic("ctx-solver-simplify")
        self._gc = z3.Tactic("ctx-simplify")  # cheap contextual dead-term pruning

    def _sort(self, sort_name: str):
        z3 = self.z3
        return {"String": z3.StringSort(), "Int": z3.IntSort(),
                "Real": z3.RealSort(), "Bool": z3.BoolSort()}[sort_name]

    def const(self, name, sort_name):
        return self.z3.Const(name, self._sort(sort_name))

    def lit(self, value, sort_name):
        z3 = self.z3
        if sort_name == "String":
            return z3.StringVal(str(value))
        if sort_name == "Int":
            return z3.IntVal(int(value))
        if sort_name == "Real":
            return z3.RealVal(float(value))
        if sort_name == "Bool":
            return z3.BoolVal(str(value).lower() == "true")
        raise ValueError(f"unknown sort {sort_name}")

    def true(self):  return self.z3.BoolVal(True)
    def false(self): return self.z3.BoolVal(False)

    def and_(self, *a): return self.z3.And(*a)
    def or_(self, *a):  return self.z3.Or(*a)
    def not_(self, a):  return self.z3.Not(a)
    def implies(self, a, b): return self.z3.Implies(a, b)
    def iff(self, a, b): return a == b

    def eq(self, a, b): return a == b
    def lt(self, a, b): return a < b
    def le(self, a, b): return a <= b
    def gt(self, a, b): return a > b
    def ge(self, a, b): return a >= b

    def add(self, a, b): return a + b
    def sub(self, a, b): return a - b
    def mul(self, a, b): return a * b
    def neg(self, a):    return -a

    def exists(self, const, body): return self.z3.Exists([const], body)
    def forall(self, const, body): return self.z3.ForAll([const], body)

    def simplify(self, t): return self.z3.simplify(t)

    def strong_simplify(self, t):
        try:
            return self._ctx(t).as_expr()
        except self.z3.Z3Exception:
            return t

    def gc_simplify(self, t):
        try:
            return self._gc(t).as_expr()
        except self.z3.Z3Exception:
            return t

    def qelim(self, q):
        try:
            return self._qe(q).as_expr()
        except self.z3.Z3Exception:
            return q

    def func(self, name, arg_sorts):
        z3 = self.z3
        return z3.Function(name, *[self._sort(a) for a in arg_sorts],
                           z3.BoolSort())

    def apply(self, f, args):
        return f(*args) if args else f()

    def substitute_fun(self, t, f, params, body):
        z3 = self.z3
        # substitute_funs expects the body over de Bruijn Vars for the
        # function's parameters; it handles shifting under binders itself.
        vbody = z3.substitute(
            body, *[(p, z3.Var(i, p.sort())) for i, p in enumerate(params)])
        return z3.substitute_funs(t, (f, vbody))

    def mentions(self, t, fs):
        z3 = self.z3
        names = {f.name() for f in fs}
        seen = set()
        stack = [t]
        while stack:
            e = stack.pop()
            if e.get_id() in seen:
                continue
            seen.add(e.get_id())
            if z3.is_quantifier(e):
                stack.append(e.body())
            elif z3.is_app(e):
                if e.decl().name() in names:
                    return True
                stack.extend(e.children())
        return False

    def prune_expired(self, t, tc, deadline):
        z3 = self.z3

        def expired(a):  # is `a` the atom  tc = c  with concrete c < deadline?
            if not z3.is_eq(a):
                return False
            l, r = a.arg(0), a.arg(1)
            for u, v in ((l, r), (r, l)):
                if z3.is_int_value(v) and u.eq(tc):
                    return v.as_long() < deadline
            return False

        def walk(e):
            if expired(e):
                return self.false()
            if z3.is_and(e) or z3.is_or(e):
                kids = [walk(c) for c in e.children()]
                return (z3.And if z3.is_and(e) else z3.Or)(*kids)
            return e  # do not cross negations or other operators

        return walk(t)

    def is_true(self, t):  return self.z3.is_true(t)
    def is_false(self, t): return self.z3.is_false(t)

    def check_sat(self, t):
        self._solver.push()
        self._solver.add(t)
        res = self._solver.check()
        self._solver.pop()
        return res == self.z3.sat

    def to_str(self, t):
        return _z3_to_str(self.z3, t)


def _z3_to_str(z3, e, scope=None) -> str:
    scope = scope or []

    def rec(x):
        return _z3_to_str(z3, x, scope)

    def is_leaf(x):
        return z3.is_const(x) or z3.is_var(x)

    def wrap_not(x):
        s = rec(x)
        return s if is_leaf(x) or z3.is_true(x) or z3.is_false(x) else f"({s})"

    if z3.is_quantifier(e):
        names = [e.var_name(i) for i in range(e.num_vars())]
        q = "∀" if e.is_forall() else "∃"
        inner = list(reversed(names)) + scope
        return "".join(f"{q} {n} . " for n in names) + _z3_to_str(z3, e.body(), inner)
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
    if z3.is_app_of(e, z3.Z3_OP_UMINUS):
        return "-" + rec(e.arg(0))
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


# ---------------------------------------------------------------------------
# CVC5
# ---------------------------------------------------------------------------

# cvc5's TermManager/Solver wrappers participate in reference cycles whose
# collection has been observed to corrupt the heap (segfault in a later,
# unrelated GC pass; cvc5 1.3.4, CPython 3.14).  Keeping them alive for the
# process lifetime sidesteps the teardown entirely — they are few and small.
_cvc5_keepalive = []


class Cvc5Backend(Backend):
    name = "cvc5"
    supports_strong = False

    def __init__(self):
        import cvc5
        from cvc5 import Kind
        self.cvc5 = cvc5
        self.Kind = Kind
        self.tm = cvc5.TermManager()
        _cvc5_keepalive.append(self.tm)
        self._simp = self._mk_solver()

    def _mk_solver(self):
        s = self.cvc5.Solver(self.tm)
        s.setOption("produce-models", "true")
        s.setLogic("ALL")
        _cvc5_keepalive.append(s)
        return s

    def _sort(self, sort_name):
        tm = self.tm
        return {"String": tm.getStringSort(), "Int": tm.getIntegerSort(),
                "Real": tm.getRealSort(), "Bool": tm.getBooleanSort()}[sort_name]

    def const(self, name, sort_name):
        return self.tm.mkConst(self._sort(sort_name), name)

    def lit(self, value, sort_name):
        tm = self.tm
        if sort_name == "String":
            return tm.mkString(str(value))
        if sort_name == "Int":
            return tm.mkInteger(int(value))
        if sort_name == "Real":
            fr = Fraction(str(value))
            return tm.mkReal(f"{fr.numerator}/{fr.denominator}")
        if sort_name == "Bool":
            return tm.mkBoolean(str(value).lower() == "true")
        raise ValueError(f"unknown sort {sort_name}")

    def true(self):  return self.tm.mkBoolean(True)
    def false(self): return self.tm.mkBoolean(False)

    def _nary(self, kind, args, empty):
        args = list(args)
        if not args:
            return empty
        if len(args) == 1:
            return args[0]
        return self.tm.mkTerm(kind, *args)

    def and_(self, *a): return self._nary(self.Kind.AND, a, self.true())
    def or_(self, *a):  return self._nary(self.Kind.OR, a, self.false())
    def not_(self, a):  return self.tm.mkTerm(self.Kind.NOT, a)
    def implies(self, a, b): return self.tm.mkTerm(self.Kind.IMPLIES, a, b)
    def iff(self, a, b): return self.tm.mkTerm(self.Kind.EQUAL, a, b)

    def eq(self, a, b): return self.tm.mkTerm(self.Kind.EQUAL, a, b)
    def lt(self, a, b): return self.tm.mkTerm(self.Kind.LT, a, b)
    def le(self, a, b): return self.tm.mkTerm(self.Kind.LEQ, a, b)
    def gt(self, a, b): return self.tm.mkTerm(self.Kind.GT, a, b)
    def ge(self, a, b): return self.tm.mkTerm(self.Kind.GEQ, a, b)

    def add(self, a, b): return self.tm.mkTerm(self.Kind.ADD, a, b)
    def sub(self, a, b): return self.tm.mkTerm(self.Kind.SUB, a, b)
    def mul(self, a, b): return self.tm.mkTerm(self.Kind.MULT, a, b)
    def neg(self, a):    return self.tm.mkTerm(self.Kind.NEG, a)

    def _quant(self, kind, const, body):
        var = self.tm.mkVar(const.getSort(), const.getSymbol())
        nb = body.substitute([const], [var])
        vlist = self.tm.mkTerm(self.Kind.VARIABLE_LIST, var)
        return self.tm.mkTerm(kind, vlist, nb)

    def exists(self, const, body): return self._quant(self.Kind.EXISTS, const, body)
    def forall(self, const, body): return self._quant(self.Kind.FORALL, const, body)

    def simplify(self, t):
        return self._simp.simplify(t)

    def qelim(self, q):
        # Only quantified formulas can be eliminated; fall back to q otherwise.
        if q.getKind() not in (self.Kind.EXISTS, self.Kind.FORALL):
            return q
        try:
            return self._mk_solver().getQuantifierElimination(q)
        except Exception:
            return q

    def func(self, name, arg_sorts):
        tm = self.tm
        srts = [self._sort(a) for a in arg_sorts]
        if not srts:
            return tm.mkConst(tm.getBooleanSort(), name)
        return tm.mkConst(tm.mkFunctionSort(srts, tm.getBooleanSort()), name)

    def apply(self, f, args):
        if not args:
            return f
        return self.tm.mkTerm(self.Kind.APPLY_UF, f, *args)

    def substitute_fun(self, t, f, params, body):
        # Rebuild the term, replacing f(a1..an) by body[params := a1..an].
        # cvc5 binders use named variables (no de Bruijn), so a recursive
        # rebuild is capture-safe.
        K = self.Kind
        tm = self.tm

        def go(e):
            k = e.getKind()
            n = e.getNumChildren()
            if k == K.APPLY_UF and e[0] == f:
                args = [go(e[i]) for i in range(1, n)]
                return body.substitute(list(params), args)
            if n == 0:
                return e if e != f else body   # 0-ary placeholder
            kids = [go(e[i]) for i in range(n)]
            if all(a == b for a, b in zip(kids, (e[i] for i in range(n)))):
                return e
            op = e.getOp() if e.hasOp() else None
            return tm.mkTerm(op, *kids) if op else tm.mkTerm(k, *kids)

        return go(t)

    def mentions(self, t, fs):
        fset = set(fs)
        stack = [t]
        while stack:
            e = stack.pop()
            if e in fset:
                return True
            stack.extend(e[i] for i in range(e.getNumChildren()))
        return False

    def prune_expired(self, t, tc, deadline):
        K = self.Kind

        def expired(a):
            if a.getKind() != K.EQUAL:
                return False
            l, r = a[0], a[1]
            for u, v in ((l, r), (r, l)):
                if v.getKind() == K.CONST_INTEGER and u == tc:
                    return int(v.getIntegerValue()) < deadline
            return False

        def walk(e):
            if expired(e):
                return self.false()
            k = e.getKind()
            if k in (K.AND, K.OR):
                kids = [walk(e[i]) for i in range(e.getNumChildren())]
                return self.tm.mkTerm(k, *kids)
            return e  # do not cross negations or other operators

        return walk(t)

    def is_true(self, t):
        return t.isBooleanValue() and t.getBooleanValue() is True

    def is_false(self, t):
        return t.isBooleanValue() and t.getBooleanValue() is False

    def check_sat(self, t):
        s = self._mk_solver()
        s.assertFormula(t)
        return s.checkSat().isSat()

    def to_str(self, t):
        return _cvc5_to_str(self.Kind, t)


def _cvc5_to_str(Kind, t) -> str:
    def rec(x):
        return _cvc5_to_str(Kind, x)

    def kids(x):
        return [x[i] for i in range(x.getNumChildren())]

    def wrap_not(x):
        k = x.getKind()
        leaf = k in (Kind.CONSTANT, Kind.VARIABLE, Kind.CONST_BOOLEAN,
                     Kind.CONST_STRING, Kind.CONST_INTEGER, Kind.CONST_RATIONAL)
        s = rec(x)
        return s if leaf else f"({s})"

    k = t.getKind()
    if k == Kind.CONST_BOOLEAN:
        return "true" if t.getBooleanValue() else "false"
    if k == Kind.NOT:
        return "¬" + wrap_not(t[0])
    if k == Kind.AND:
        return "(" + " ∧ ".join(rec(c) for c in kids(t)) + ")"
    if k == Kind.OR:
        return "(" + " ∨ ".join(rec(c) for c in kids(t)) + ")"
    if k == Kind.IMPLIES:
        return f"({rec(t[0])} → {rec(t[1])})"
    rels = {Kind.EQUAL: "=", Kind.LT: "<", Kind.LEQ: "<=",
            Kind.GT: ">", Kind.GEQ: ">="}
    if k in rels:
        return f"{rec(t[0])} {rels[k]} {rec(t[1])}"
    ariths = {Kind.ADD: "+", Kind.SUB: "-", Kind.MULT: "*"}
    if k in ariths:
        return "(" + f" {ariths[k]} ".join(rec(c) for c in kids(t)) + ")"
    if k == Kind.NEG:
        return "-" + rec(t[0])
    if k in (Kind.FORALL, Kind.EXISTS):
        q = "∀" if k == Kind.FORALL else "∃"
        names = [v.getSymbol() for v in kids(t[0])]
        return "".join(f"{q} {n} . " for n in names) + rec(t[1])
    if k == Kind.CONST_STRING:
        return '"' + t.getStringValue() + '"'
    if k in (Kind.CONSTANT, Kind.VARIABLE):
        return t.getSymbol()
    return str(t).replace("\n", " ")


# ---------------------------------------------------------------------------

def make_backend(name: str) -> Backend:
    name = (name or "z3").lower()
    if name == "z3":
        return Z3Backend()
    if name == "cvc5":
        return Cvc5Backend()
    raise ValueError(f"unknown solver backend: {name}")
