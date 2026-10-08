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
from collections import OrderedDict


# ---------------------------------------------------------------------------
# Interface
# ---------------------------------------------------------------------------

# Fixed-width bit-vector sorts (unsigned reading; +,-,* wrap around).
BV_SORTS = {"BV8": 8, "BV16": 16, "BV32": 32, "BV64": 64}


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

    # string relations
    def contains(self, a, b): ...  # True iff string a contains substring b

    # arithmetic
    def add(self, a, b): ...
    def sub(self, a, b): ...
    def mul(self, a, b): ...
    def div(self, a, b): ...
    def neg(self, a): ...

    # quantifiers (over a free constant, which becomes the bound variable)
    def exists(self, const, body): ...
    def forall(self, const, body): ...

    # normalisation / solving
    def simplify(self, t): ...
    def strong_simplify(self, t): return self.simplify(t)
    def gc_simplify(self, t): return self.simplify(t)   # dead-term reclamation
    def qelim(self, q): ...

    def declare_enum(self, name, constructors): ...

    # uninterpreted functions (future-operator placeholders; interpreted
    # Python functions from the spec's python block)
    def func(self, name: str, arg_sorts, ret_sort="Bool"): ...
    def apply(self, f, args): ...

    def eval_funs(self, t, registry, cache):
        """Fold applications of registered pure Python functions whose
        arguments have become ground (see Z3Backend.eval_funs)."""
        return t

    def subst_consts(self, t, pairs):
        """Simultaneously substitute constants: pairs = [(from, to), ...]."""
        ...

    def substitute_fun(self, t, f, params, body):
        """Replace every application f(a1..an) in t by body[params := a1..an],
        correctly under binders.  `params` are the constants body is written
        over."""
        ...

    def mentions(self, t, fs) -> bool:
        """Does t contain an application of any of the given functions?"""
        ...

    # strings and regular expressions (for `matches`)
    def concat(self, parts): ...
    def prefixof(self, pre, s): ...
    def suffixof(self, suf, s): ...
    def in_re(self, s, rast):
        """Membership of string term s in the regex given as the neutral AST
        of dejavumt.pattern."""
        ...

    def stamps(self, t, tc):
        """The timestamps c of every atom  tc = c  in a timed node's state, or None if
        tc occurs in any other form. Used to find when the node's value can next change
        (see FormulaMonitor._next_deadline); None means "cannot tell", which disables
        skipping for that property. The default is None, so a backend that does not
        implement it is merely slower, never wrong."""
        return None

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

    def model_values(self, formula, consts):
        """A satisfying assignment of `formula` restricted to `consts`, as
        {name: python value}; None if unsatisfiable/unknown."""
        return None

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
        self.enums = {}   # name -> (sort, {constructor: const})
        self._solver = z3.Solver()
        # qe2 can DIVERGE (not fail) on existentials over string
        # concatenations -- word equations, regex membership.  TryFor turns
        # divergence into a Z3Exception, which qelim() below already treats
        # as "leave the quantifier in place"; the verdict then falls to the
        # closed root's satisfiability check, which handles the ground case.
        self._qe = z3.TryFor(z3.Tactic("qe2"), 3000)
        # ... but TryFor costs a fixed ~70-190 us per call (it arms a timer), which
        # on a typical spec was 15-30% of all monitoring time -- for a divergence that
        # only string concatenation and regex terms can cause. So the limited tactic
        # is used only once the spec has built such a term (_strings_used, set by the
        # builders below, all of which run while the spec is compiled, before any
        # quantifier is eliminated); otherwise plain qe2.
        self._qe_plain = z3.Tactic("qe2")
        self._strings_used = False
        # Memo tables for the two pure, expensive operations (see _memo). A qelim that
        # hits the TryFor limit returns its argument unchanged -- an equivalent formula --
        # so caching that outcome is sound too; it just isn't retried.
        self._qelim_memo = OrderedDict()
        self._simplify_memo = OrderedDict()
        self._ctx = z3.Tactic("ctx-solver-simplify")
        self._gc = z3.Tactic("ctx-simplify")  # cheap contextual dead-term pruning

    # Z3's global context refuses to redeclare an enumeration sort, so the
    # declared sorts are cached process-wide and shared across monitors.
    _enum_cache = {}

    def declare_enum(self, name, constructors):
        """Register a finite enumeration sort; its constructor names become
        literals of that sort."""
        z3 = self.z3
        key = (name, tuple(constructors))
        cached = Z3Backend._enum_cache.get(name)
        if cached is not None:
            if cached[0] != key[1]:
                raise ValueError(
                    f"enum '{name}' already declared in this process with "
                    f"different constructors {list(cached[0])}")
            sort, consts = cached[1]
        else:
            sort, cs = z3.EnumSort(name, list(constructors))
            consts = dict(zip(constructors, cs))
            Z3Backend._enum_cache[name] = (key[1], (sort, consts))
        self.enums[name] = (sort, consts)

    def _sort(self, sort_name: str):
        z3 = self.z3
        if sort_name in self.enums:
            return self.enums[sort_name][0]
        if sort_name in BV_SORTS:
            return z3.BitVecSort(BV_SORTS[sort_name])
        return {"String": z3.StringSort(), "Int": z3.IntSort(),
                "Real": z3.RealSort(), "Bool": z3.BoolSort()}[sort_name]

    def const(self, name, sort_name):
        return self.z3.Const(name, self._sort(sort_name))

    def lit(self, value, sort_name):
        z3 = self.z3
        if sort_name in self.enums:
            consts = self.enums[sort_name][1]
            if str(value) not in consts:
                raise ValueError(
                    f"'{value}' is not a {sort_name} "
                    f"(one of {', '.join(consts)})")
            return consts[str(value)]
        if sort_name in BV_SORTS:
            return z3.BitVecVal(int(str(value), 0), BV_SORTS[sort_name])
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

    def _adapt2(self, a, b):
        """Align an Int literal with a bit-vector operand (the mask/counter
        idiom: w = 0x40, x + 1 over BV)."""
        z3 = self.z3
        if z3.is_bv(a) and z3.is_int_value(b):
            return a, z3.BitVecVal(b.as_long(), a.size())
        if z3.is_bv(b) and z3.is_int_value(a):
            return z3.BitVecVal(a.as_long(), b.size()), b
        return a, b

    def eq(self, a, b):
        a, b = self._adapt2(a, b)
        return a == b

    # Comparisons on bit-vectors are UNSIGNED (the status-word reading).
    def lt(self, a, b):
        a, b = self._adapt2(a, b)
        return self.z3.ULT(a, b) if self.z3.is_bv(a) else a < b

    def le(self, a, b):
        a, b = self._adapt2(a, b)
        return self.z3.ULE(a, b) if self.z3.is_bv(a) else a <= b

    def gt(self, a, b):
        a, b = self._adapt2(a, b)
        return self.z3.UGT(a, b) if self.z3.is_bv(a) else a > b

    def ge(self, a, b):
        a, b = self._adapt2(a, b)
        return self.z3.UGE(a, b) if self.z3.is_bv(a) else a >= b

    def contains(self, a, b):
        self._strings_used = True
        return self.z3.Contains(a, b)

    # +,-,* are native wraparound on bit-vectors.
    def add(self, a, b):
        a, b = self._adapt2(a, b)
        return a + b

    def sub(self, a, b):
        a, b = self._adapt2(a, b)
        return a - b

    def mul(self, a, b):
        a, b = self._adapt2(a, b)
        return a * b

    def div(self, a, b):
        # Integer division on Int, exact division on Real, unsigned on BV.
        a, b = self._adapt2(a, b)
        if isinstance(a, self.z3.BitVecRef):
            return self.z3.UDiv(a, b)
        return a / b

    def neg(self, a):    return -a

    def bvand(self, a, b):
        a, b = self._adapt2(a, b)
        return a & b

    def bvor(self, a, b):
        a, b = self._adapt2(a, b)
        return a | b

    def bvxor(self, a, b):
        a, b = self._adapt2(a, b)
        return a ^ b

    def bvnot(self, a): return ~a

    def shl(self, a, b):
        a, b = self._adapt2(a, b)
        return a << b

    def lshr(self, a, b):
        a, b = self._adapt2(a, b)
        return self.z3.LShR(a, b)

    def exists(self, const, body): return self.z3.Exists([const], body)
    def forall(self, const, body): return self.z3.ForAll([const], body)

    # Quantifier elimination and simplification are pure functions of their argument,
    # and Z3 hash-conses terms, so a term's id identifies it exactly. A monitor asks for
    # the same few terms over and over -- an event that leaves a subformula unchanged
    # re-requests its value -- so caching them is sound and cheap: on the TempControl GDS
    # traces 81% of qelim calls and 95% of simplify calls were repeats.
    #
    # Bounded LRU, because an unbounded table would keep every term the run ever built
    # alive (each entry holds its argument, so a recycled id can never be mistaken for
    # an old term) and would defeat the purpose of the gc flag.
    _MEMO_LIMIT = 8192

    def _memo(self, table, t, fn):
        key = t.get_id()
        hit = table.get(key)
        if hit is not None:
            table.move_to_end(key)
            return hit[1]
        r = fn(t)
        table[key] = (t, r)
        if len(table) > self._MEMO_LIMIT:
            table.popitem(last=False)
        return r

    def simplify(self, t):
        return self._memo(self._simplify_memo, t, self.z3.simplify)

    # Equal ids mean structurally identical terms (Z3 hash-conses), which is how the
    # engine recognises that an irrelevant event changed nothing.
    def term_id(self, t): return t.get_id()

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
        return self._memo(self._qelim_memo, q, self._qelim_uncached)

    def _qelim_uncached(self, q):
        try:
            tactic = self._qe if self._strings_used else self._qe_plain
            return tactic(q).as_expr()
        except self.z3.Z3Exception:
            return q

    def concat(self, parts):
        self._strings_used = True
        z3 = self.z3
        parts = list(parts)
        if not parts:
            return z3.StringVal("")
        return parts[0] if len(parts) == 1 else z3.Concat(*parts)

    def _re(self, r):
        z3 = self.z3
        k = r[0]
        if k == "lit":
            return z3.Re(z3.StringVal(r[1]))
        if k == "any":
            return z3.AllChar(z3.ReSort(z3.StringSort()))
        if k == "class":
            rs = [z3.Range(z3.StringVal(lo), z3.StringVal(hi))
                  for lo, hi in r[1]]
            return rs[0] if len(rs) == 1 else z3.Union(*rs)
        if k == "star":
            return z3.Star(self._re(r[1]))
        if k == "plus":
            return z3.Plus(self._re(r[1]))
        if k == "opt":
            return z3.Option(self._re(r[1]))
        if k == "cat":
            return z3.Concat(*[self._re(x) for x in r[1]])
        if k == "alt":
            return z3.Union(*[self._re(x) for x in r[1]])
        raise ValueError(f"bad regex node {k}")

    def prefixof(self, pre, s):
        self._strings_used = True
        return self.z3.PrefixOf(pre, s)

    def suffixof(self, suf, s):
        self._strings_used = True
        return self.z3.SuffixOf(suf, s)

    def in_re(self, s, rast):
        self._strings_used = True
        return self.z3.InRe(s, self._re(rast))

    def func(self, name, arg_sorts, ret_sort="Bool"):
        z3 = self.z3
        return z3.Function(name, *[self._sort(a) for a in arg_sorts],
                           self._sort(ret_sort))

    def apply(self, f, args):
        return f(*args) if args else f()

    # --- interpreted Python functions: lazy graph folding ---

    def _litval(self, e):
        """Python value of a literal term, or None if not a literal."""
        z3 = self.z3
        if z3.is_string_value(e):
            return e.as_string()
        if z3.is_int_value(e):
            return e.as_long()
        if z3.is_rational_value(e):
            return e.numerator_as_long() / e.denominator_as_long()
        if z3.is_true(e):
            return True
        if z3.is_false(e):
            return False
        return None

    def eval_funs(self, t, registry, cache):
        """Fold applications of registered pure Python functions.  First
        propagate  var = literal  equalities within each conjunction into
        their sibling conjuncts (the equalities themselves are kept), then
        replace every application whose arguments are all literals by the
        memoized result of calling the function.  `registry` maps
        name -> {"fdecl", "fn", "args", "ret"}; `cache` maps
        (name, argvalues) -> result."""
        z3 = self.z3
        PYCONV = {"String": str, "Int": int, "Real": float, "Bool": bool}

        def is_plain_const(x):
            return (z3.is_app(x) and x.num_args() == 0
                    and x.decl().kind() == z3.Z3_OP_UNINTERPRETED
                    and x.decl().name() not in registry)

        def eqs_of(c, positive):
            """var=literal equalities carried by one child: for an And
            scope, positive equalities among the conjuncts; for an Or
            scope, equalities under a negated conjunction (the guard of an
            implication:  !(d=v & R) | C  ==  !(d=v & R) | C[d:=v],  since
            the first disjunct is true whenever d != v)."""
            if positive:
                cands = [c]
            else:
                if not z3.is_not(c):
                    return []
                g = c.arg(0)
                cands = list(g.children()) if z3.is_and(g) else [g]
            out = []
            for cc in cands:
                if z3.is_eq(cc):
                    a, b = cc.arg(0), cc.arg(1)
                    for v, l in ((a, b), (b, a)):
                        if is_plain_const(v) and self._litval(l) is not None:
                            out.append((v, l))
                            break
            return out

        def prop(e):
            if z3.is_quantifier(e):
                return e
            if not z3.is_app(e) or e.num_args() == 0:
                return e
            ch = [prop(c) for c in e.children()]
            conj, disj = z3.is_and(e), z3.is_or(e)
            if conj or disj:
                pairs, sources, seen = [], set(), set()
                for c in ch:
                    got = eqs_of(c, positive=conj)
                    fresh = [(v, l) for v, l in got
                             if v.decl().name() not in seen]
                    if fresh:
                        seen.update(v.decl().name() for v, _ in fresh)
                        pairs.extend(fresh)
                        sources.add(c.get_id())
                if pairs:
                    ch = [c if c.get_id() in sources
                          else prop(z3.substitute(c, *pairs)) for c in ch]
                return z3.And(*ch) if conj else z3.Or(*ch)
            return e.decl()(*ch)

        def scan(e, out):
            if z3.is_quantifier(e):
                scan(e.body(), out)
                return
            for c in e.children():
                scan(c, out)
            if z3.is_app(e):
                reg = registry.get(e.decl().name())
                if (reg is not None
                        and e.decl().kind() == z3.Z3_OP_UNINTERPRETED
                        and e.num_args() == len(reg["args"])):
                    vals = tuple(self._litval(c) for c in e.children())
                    if all(v is not None for v in vals):
                        out[e] = vals

        t = prop(t)
        for _ in range(8):     # nested applications fold inside-out
            out = {}
            scan(t, out)
            if not out:
                break
            pairs = []
            for app, vals in out.items():
                name = app.decl().name()
                reg = registry[name]
                key = (name, vals)
                if key not in cache:
                    args = [PYCONV[s](v) for v, s in zip(vals, reg["args"])]
                    cache[key] = reg["fn"](*args)
                try:
                    pairs.append((app, self.lit(cache[key], reg["ret"])))
                except (TypeError, ValueError) as exc:
                    raise ValueError(
                        f"Python function '{name}' returned "
                        f"{cache[key]!r}, not convertible to its declared "
                        f"return sort {reg['ret']}") from exc
            t = z3.substitute(t, *pairs)
        return t

    def substitute_fun(self, t, f, params, body):
        z3 = self.z3
        # substitute_funs expects the body over de Bruijn Vars for the
        # function's parameters; it handles shifting under binders itself.
        vbody = z3.substitute(
            body, *[(p, z3.Var(i, p.sort())) for i, p in enumerate(params)])
        return z3.substitute_funs(t, (f, vbody))

    def subst_consts(self, t, pairs):
        return self.z3.substitute(t, *pairs)

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

    def stamps(self, t, tc):
        z3 = self.z3
        found, seen = set(), set()
        ok = True

        def walk(e):
            nonlocal ok
            if not ok or e.get_id() in seen:
                return
            seen.add(e.get_id())
            if z3.is_eq(e):
                l, r = e.arg(0), e.arg(1)
                for u, v in ((l, r), (r, l)):
                    if u.eq(tc) and z3.is_int_value(v):
                        found.add(v.as_long())
                        return
            if e.eq(tc):            # tc in any other position: give up
                ok = False
                return
            for c in e.children():
                walk(c)

        walk(t)
        return sorted(found) if ok else None

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

    def model_values(self, formula, consts):
        z3 = self.z3
        s = z3.Solver()
        s.set("timeout", 3000)
        s.add(formula)
        if s.check() != z3.sat:
            return None
        m = s.model()
        out = {}
        for c in consts:
            v = m.eval(c, model_completion=True)
            out[str(c)] = self._model_pyval(v)
        return out

    def _model_pyval(self, v):
        z3 = self.z3
        if z3.is_string_value(v):
            return v.as_string()
        if z3.is_int_value(v):
            return v.as_long()
        if z3.is_bv_value(v):
            return v.as_long()
        if z3.is_rational_value(v):
            return v.numerator_as_long() / v.denominator_as_long()
        if z3.is_true(v):
            return True
        if z3.is_false(v):
            return False
        return str(v)          # enum constructors and anything else

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
    if z3.is_app_of(e, z3.Z3_OP_SEQ_CONTAINS):
        return f"{rec(e.arg(0))} contains {rec(e.arg(1))}"
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
        self.enums = {}   # name -> (sort, {constructor: term})
        _cvc5_keepalive.append(self.tm)
        self._simp = self._mk_solver()

    def _mk_solver(self):
        s = self.cvc5.Solver(self.tm)
        s.setOption("produce-models", "true")
        s.setLogic("ALL")
        _cvc5_keepalive.append(s)
        return s

    def declare_enum(self, name, constructors):
        tm = self.tm
        decl = tm.mkDatatypeDecl(name)
        for c in constructors:
            decl.addConstructor(tm.mkDatatypeConstructorDecl(c))
        sort = tm.mkDatatypeSort(decl)
        dt = sort.getDatatype()
        consts = {c: tm.mkTerm(self.Kind.APPLY_CONSTRUCTOR,
                               dt.getConstructor(c).getTerm())
                  for c in constructors}
        self.enums[name] = (sort, consts)

    def _sort(self, sort_name):
        tm = self.tm
        if sort_name in self.enums:
            return self.enums[sort_name][0]
        if sort_name in BV_SORTS:
            return tm.mkBitVectorSort(BV_SORTS[sort_name])
        return {"String": tm.getStringSort(), "Int": tm.getIntegerSort(),
                "Real": tm.getRealSort(), "Bool": tm.getBooleanSort()}[sort_name]

    def const(self, name, sort_name):
        return self.tm.mkConst(self._sort(sort_name), name)

    def lit(self, value, sort_name):
        tm = self.tm
        if sort_name in self.enums:
            consts = self.enums[sort_name][1]
            if str(value) not in consts:
                raise ValueError(
                    f"'{value}' is not a {sort_name} "
                    f"(one of {', '.join(consts)})")
            return consts[str(value)]
        if sort_name in BV_SORTS:
            return tm.mkBitVector(BV_SORTS[sort_name], int(str(value), 0))
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

    def _adapt2(self, a, b):
        # Align an Int literal with a bit-vector operand.
        tm = self.tm
        if a.getSort().isBitVector() and b.isIntegerValue():
            return a, tm.mkBitVector(a.getSort().getBitVectorSize(),
                                     b.getIntegerValue())
        if b.getSort().isBitVector() and a.isIntegerValue():
            return tm.mkBitVector(b.getSort().getBitVectorSize(),
                                  a.getIntegerValue()), b
        return a, b

    def _isbv(self, a):
        return a.getSort().isBitVector()

    def eq(self, a, b):
        a, b = self._adapt2(a, b)
        return self.tm.mkTerm(self.Kind.EQUAL, a, b)

    # Comparisons on bit-vectors are UNSIGNED.
    def lt(self, a, b):
        a, b = self._adapt2(a, b)
        k = self.Kind.BITVECTOR_ULT if self._isbv(a) else self.Kind.LT
        return self.tm.mkTerm(k, a, b)

    def le(self, a, b):
        a, b = self._adapt2(a, b)
        k = self.Kind.BITVECTOR_ULE if self._isbv(a) else self.Kind.LEQ
        return self.tm.mkTerm(k, a, b)

    def gt(self, a, b):
        a, b = self._adapt2(a, b)
        k = self.Kind.BITVECTOR_UGT if self._isbv(a) else self.Kind.GT
        return self.tm.mkTerm(k, a, b)

    def ge(self, a, b):
        a, b = self._adapt2(a, b)
        k = self.Kind.BITVECTOR_UGE if self._isbv(a) else self.Kind.GEQ
        return self.tm.mkTerm(k, a, b)

    def contains(self, a, b): return self.tm.mkTerm(self.Kind.STRING_CONTAINS, a, b)

    def add(self, a, b):
        a, b = self._adapt2(a, b)
        k = self.Kind.BITVECTOR_ADD if self._isbv(a) else self.Kind.ADD
        return self.tm.mkTerm(k, a, b)

    def sub(self, a, b):
        a, b = self._adapt2(a, b)
        k = self.Kind.BITVECTOR_SUB if self._isbv(a) else self.Kind.SUB
        return self.tm.mkTerm(k, a, b)

    def mul(self, a, b):
        a, b = self._adapt2(a, b)
        k = self.Kind.BITVECTOR_MULT if self._isbv(a) else self.Kind.MULT
        return self.tm.mkTerm(k, a, b)

    def div(self, a, b):
        # Integer division on Int, exact division on Real, unsigned on BV.
        a, b = self._adapt2(a, b)
        if self._isbv(a):
            k = self.Kind.BITVECTOR_UDIV
        elif a.getSort().isInteger():
            k = self.Kind.INTS_DIVISION
        else:
            k = self.Kind.DIVISION
        return self.tm.mkTerm(k, a, b)

    def bvand(self, a, b):
        a, b = self._adapt2(a, b)
        return self.tm.mkTerm(self.Kind.BITVECTOR_AND, a, b)

    def bvor(self, a, b):
        a, b = self._adapt2(a, b)
        return self.tm.mkTerm(self.Kind.BITVECTOR_OR, a, b)

    def bvxor(self, a, b):
        a, b = self._adapt2(a, b)
        return self.tm.mkTerm(self.Kind.BITVECTOR_XOR, a, b)

    def bvnot(self, a):
        return self.tm.mkTerm(self.Kind.BITVECTOR_NOT, a)

    def shl(self, a, b):
        a, b = self._adapt2(a, b)
        return self.tm.mkTerm(self.Kind.BITVECTOR_SHL, a, b)

    def lshr(self, a, b):
        a, b = self._adapt2(a, b)
        return self.tm.mkTerm(self.Kind.BITVECTOR_LSHR, a, b)
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

    def concat(self, parts):
        parts = list(parts)
        if not parts:
            return self.tm.mkString("")
        if len(parts) == 1:
            return parts[0]
        return self.tm.mkTerm(self.Kind.STRING_CONCAT, *parts)

    def _re(self, r):
        tm, K = self.tm, self.Kind
        k = r[0]
        if k == "lit":
            return tm.mkTerm(K.STRING_TO_REGEXP, tm.mkString(r[1]))
        if k == "any":
            return tm.mkTerm(K.REGEXP_ALLCHAR)
        if k == "class":
            rs = [tm.mkTerm(K.REGEXP_RANGE, tm.mkString(lo), tm.mkString(hi))
                  for lo, hi in r[1]]
            return rs[0] if len(rs) == 1 else tm.mkTerm(K.REGEXP_UNION, *rs)
        if k == "star":
            return tm.mkTerm(K.REGEXP_STAR, self._re(r[1]))
        if k == "plus":
            return tm.mkTerm(K.REGEXP_PLUS, self._re(r[1]))
        if k == "opt":
            return tm.mkTerm(K.REGEXP_OPT, self._re(r[1]))
        if k == "cat":
            return tm.mkTerm(K.REGEXP_CONCAT, *[self._re(x) for x in r[1]])
        if k == "alt":
            return tm.mkTerm(K.REGEXP_UNION, *[self._re(x) for x in r[1]])
        raise ValueError(f"bad regex node {k}")

    def prefixof(self, pre, s):
        return self.tm.mkTerm(self.Kind.STRING_PREFIX, pre, s)

    def suffixof(self, suf, s):
        return self.tm.mkTerm(self.Kind.STRING_SUFFIX, suf, s)

    def in_re(self, s, rast):
        return self.tm.mkTerm(self.Kind.STRING_IN_REGEXP, s, self._re(rast))

    def func(self, name, arg_sorts, ret_sort="Bool"):
        tm = self.tm
        srts = [self._sort(a) for a in arg_sorts]
        rs = self._sort(ret_sort)
        if not srts:
            return tm.mkConst(rs, name)
        return tm.mkConst(tm.mkFunctionSort(srts, rs), name)

    # --- interpreted Python functions: lazy graph folding ---

    def _litval(self, e):
        if e.isStringValue():
            return e.getStringValue()
        if e.isIntegerValue():
            return e.getIntegerValue()
        if e.isRealValue():
            num, den = e.getRealValue().as_integer_ratio()
            return num / den
        if e.isBooleanValue():
            return e.getBooleanValue()
        if e.isBitVectorValue():
            return int(e.getBitVectorValue(), 2)
        return None

    def eval_funs(self, t, registry, cache):
        """See Z3Backend.eval_funs: equality propagation within
        conjunctions, then folding of ground applications."""
        K = self.Kind
        tm = self.tm
        PYCONV = {"String": str, "Int": int, "Real": float, "Bool": bool}
        fdecls = {reg["fdecl"]: name for name, reg in registry.items()}

        def is_plain_const(x):
            return (x.getKind() == K.CONSTANT
                    and x not in fdecls)

        def eqs_of(c, positive):
            # See Z3Backend: positive equalities in an And scope; guard
            # equalities under a negated conjunction in an Or scope.
            if positive:
                cands = [c]
            else:
                if c.getKind() != K.NOT:
                    return []
                g = c[0]
                cands = ([g[i] for i in range(g.getNumChildren())]
                         if g.getKind() == K.AND else [g])
            out = []
            for cc in cands:
                if cc.getKind() == K.EQUAL:
                    a, b = cc[0], cc[1]
                    for v, l in ((a, b), (b, a)):
                        if is_plain_const(v) and self._litval(l) is not None:
                            out.append((v, l))
                            break
            return out

        def prop(e):
            k = e.getKind()
            if k in (K.FORALL, K.EXISTS) or e.getNumChildren() == 0:
                return e
            ch = [prop(e[i]) for i in range(e.getNumChildren())]
            if k in (K.AND, K.OR):
                pairs_from, pairs_to, sources, seen = [], [], set(), set()
                for c in ch:
                    got = eqs_of(c, positive=(k == K.AND))
                    fresh = [(v, l) for v, l in got if v not in seen]
                    if fresh:
                        seen.update(v for v, _ in fresh)
                        pairs_from.extend(v for v, _ in fresh)
                        pairs_to.extend(l for _, l in fresh)
                        sources.add(c)
                if pairs_from:
                    ch = [c if c in sources
                          else prop(c.substitute(pairs_from, pairs_to))
                          for c in ch]
                return tm.mkTerm(k, *ch) if len(ch) > 1 else ch[0]
            op = e.getOp() if e.hasOp() else None
            return tm.mkTerm(op, *ch) if op else tm.mkTerm(k, *ch)

        def scan(e, out):
            for i in range(e.getNumChildren()):
                scan(e[i], out)
            if (e.getKind() == K.APPLY_UF and e[0] in fdecls):
                name = fdecls[e[0]]
                reg = registry[name]
                if e.getNumChildren() - 1 == len(reg["args"]):
                    vals = tuple(self._litval(e[i])
                                 for i in range(1, e.getNumChildren()))
                    if all(v is not None for v in vals):
                        out[e] = (name, vals)

        t = prop(t)
        for _ in range(8):
            out = {}
            scan(t, out)
            if not out:
                break
            frm, to = [], []
            for app, (name, vals) in out.items():
                reg = registry[name]
                key = (name, vals)
                if key not in cache:
                    args = [PYCONV[s](v) for v, s in zip(vals, reg["args"])]
                    cache[key] = reg["fn"](*args)
                try:
                    to.append(self.lit(cache[key], reg["ret"]))
                except (TypeError, ValueError) as exc:
                    raise ValueError(
                        f"Python function '{name}' returned "
                        f"{cache[key]!r}, not convertible to its declared "
                        f"return sort {reg['ret']}") from exc
                frm.append(app)
            t = t.substitute(frm, to)
        return t

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

    def subst_consts(self, t, pairs):
        return t.substitute([p[0] for p in pairs], [p[1] for p in pairs])

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

    def model_values(self, formula, consts):
        s = self._mk_solver()
        s.setOption("produce-models", "true")
        s.assertFormula(formula)
        if not s.checkSat().isSat():
            return None
        out = {}
        for c in consts:
            v = s.getValue(c)
            got = self._litval(v)
            out[str(c)] = got if got is not None else str(v)
        return out

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
    if k == Kind.STRING_CONTAINS:
        return f"{rec(t[0])} contains {rec(t[1])}"
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
