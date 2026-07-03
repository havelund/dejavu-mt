"""
Throwaway feasibility probe: does CVC5's quantifier elimination collapse the
STRING quantifiers the way Z3's qe2 does?  This is the one unknown that decides
whether swapping DejaVuMT's Z3 backend for CVC5 is worthwhile.

It does NOT touch the DejaVuMT engine — it hand-builds, in the CVC5 API, the
exact formula shapes the engine produces at quantifier nodes, and runs
simplify / getQuantifierElimination / checkSat on each, printing the result
next to the expected (Z3) outcome.

Run:  .venv/bin/python experiments/cvc5_probe.py
"""
import cvc5
from cvc5 import Kind

tm = cvc5.TermManager()

S = tm.getStringSort()
I = tm.getIntegerSort()

def solver():
    s = cvc5.Solver(tm)
    s.setOption("produce-models", "true")
    s.setLogic("ALL")
    return s

def sstr(v): return tm.mkString(v)
def const(sort, n): return tm.mkConst(sort, n)
def var(sort, n): return tm.mkVar(sort, n)
def AND(*a): return tm.mkTerm(Kind.AND, *a)
def OR(*a):  return tm.mkTerm(Kind.OR, *a)
def NOT(a):  return tm.mkTerm(Kind.NOT, a)
def EQ(a, b): return tm.mkTerm(Kind.EQUAL, a, b)
def LT(a, b): return tm.mkTerm(Kind.LT, a, b)
def ADD(a, b): return tm.mkTerm(Kind.ADD, a, b)
def EXISTS(v, body): return tm.mkTerm(Kind.EXISTS, tm.mkTerm(Kind.VARIABLE_LIST, v), body)
def FORALL(v, body): return tm.mkTerm(Kind.FORALL, tm.mkTerm(Kind.VARIABLE_LIST, v), body)

def try_qe(q):
    try:
        return str(solver().getQuantifierElimination(q))
    except Exception as e:
        return f"<QE error: {type(e).__name__}: {str(e)[:80]}>"

def try_simplify(t):
    try:
        return str(solver().simplify(t))
    except Exception as e:
        return f"<simplify error: {type(e).__name__}: {str(e)[:80]}>"

def try_checksat(closed):
    try:
        s = solver()
        s.setOption("tlimit-per", "4000")  # 4s guard per check
        s.assertFormula(closed)
        return str(s.checkSat())
    except Exception as e:
        return f"<checkSat error: {type(e).__name__}: {str(e)[:80]}>"


# --- the decisive cases -----------------------------------------------------

def case(title, term, expected, closed=None, quantified=True):
    print(f"\n### {title}")
    print(f"    formula   : {term}")
    print(f"    expected  : {expected}   (Z3 qe2)")
    if quantified:
        print(f"    cvc5 QE   : {try_qe(term)}")
    print(f"    cvc5 simp : {try_simplify(term)}")
    if closed is not None:
        print(f"    checkSat  : {try_checksat(closed)}   (sat => holds)")


# 1. string existential, trivially true
m = var(S, "m")
c1 = EXISTS(m, OR(EQ(m, sstr("read")), EQ(m, sstr("write"))))
case("exists m . (m=read | m=write)", c1, "true", closed=c1)

# 2. string universal, must be false over the infinite domain
m = var(S, "m")
c2 = FORALL(m, EQ(m, sstr("read")))
case("forall m . (m=read)", c2, "false", closed=c2)

# 3. existential with a free variable f : QE must keep f
m = var(S, "m"); f = const(S, "f")
c3 = EXISTS(m, AND(EQ(f, sstr("c")), OR(EQ(m, sstr("read")), EQ(m, sstr("write")))))
case("exists m . (f=c & (m=read | m=write))", c3, 'f = "c"')

# 4. arithmetic QE sanity (Z3 handles these fine)
v1 = var(I, "v1"); v2 = const(I, "v2")
c4 = EXISTS(v1, EQ(v2, ADD(v1, tm.mkInteger(1))))
case("exists v1 . (v2 = v1 + 1)", c4, "true (v2 unconstrained)")

v1 = var(I, "v1")
c5 = FORALL(v1, LT(v1, ADD(v1, tm.mkInteger(1))))
case("forall v1 . (v1 < v1 + 1)", c5, "true", closed=c5)

print("\n(If cases 1-3 do NOT reduce to true/false/'f=c' quickly, string QE is the blocker.)")
