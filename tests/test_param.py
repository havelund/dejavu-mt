"""Tests for parametric monitoring: a symbolic upper bound on F/G (F[<=n])
is an Int constant the engine never eliminates, so verdicts become
constraints on it ("holds iff n >= 7") and the monitor keeps a running
feasible region -- the conjunction of the constraints emitted so far.
"""
import pytest

from dejavumt import parse_spec, Monitor
from dejavumt import ast
from dejavumt.parser import parse_spec as parse


SPEC = """
pred req(x: String)
pred ack(x: String)
prop r : Forall x . req(x) -> F[<=n] ack(x)
"""


def equiv(b, f, g):
    """f and g agree for every parameter value."""
    return not b.check_sat(b.not_(b.iff(f, g)))


def pconst(m, name, prop_index=0):
    """The monitor's own constant for the parameter (cvc5 constants are not
    interned by name, so a freshly built one would not be the same term)."""
    return m.formulas[prop_index].params[name]


def n_ge(m, name, k):
    b = m.backend
    return b.ge(pconst(m, name), b.lit(k, "Int"))


def replay(spec_text, events, prop="r", solver="z3"):
    """(monitor, {position: verdict}) after the trace and end()."""
    m = Monitor(parse_spec(spec_text), solver=solver)
    got = {}
    for ev, ts in events:
        m.step(ev, ts)
        for pos, name, holds in m.resolved:
            if name == prop:
                got[pos] = holds
    for pos, name, holds in m.end():
        if name == prop:
            got[pos] = holds
    return m, got


# --- parsing -----------------------------------------------------------------

def test_param_syntax():
    body = parse("prop p : F[<=n] a").properties[0].body
    assert body == ast.TimedEventually(0, "n", ast.Pred("a", ()), "[<=n]")
    body = parse("prop p : G[2,m] a").properties[0].body
    assert body == ast.TimedAlways(2, "m", ast.Pred("a", ()), "[2,m]")


# --- threshold synthesis -----------------------------------------------------

def test_f_threshold():
    events = [({"req": [("a",)]}, 0), ({"ack": [("a",)]}, 7)]
    m, got = replay(SPEC, events)
    b = m.backend
    # Position 1: the ack arrived 7 units after the request.
    assert equiv(b, got[1], n_ge(m, "n", 7))
    # Position 2: no request there, vacuously true for every n.
    assert got[2] is True


def test_f_threshold_early_emission():
    """The verdict is final at the FIRST witness (a later ack can only be
    slower), well before end of trace."""
    m = Monitor(parse_spec(SPEC), solver="z3")
    m.step({"req": [("a",)]}, 0)
    assert not any(name == "r" and pos == 1 for pos, name, _ in m.resolved)
    m.step({"ack": [("a",)]}, 7)
    emitted = {pos: h for pos, name, h in m.resolved if name == "r"}
    assert 1 in emitted
    assert equiv(m.backend, emitted[1], n_ge(m, "n", 7))


def test_f_no_witness_is_false():
    events = [({"req": [("a",)]}, 0), ({"req": [("b",)]}, 5)]
    m, got = replay(SPEC, events)
    b = m.backend
    # No ack ever: false for every n; the region collapses to false.
    assert got[1] is False
    assert b.is_false(b.simplify(m.formulas[0].region))


def test_region_is_max_of_delays():
    events = [({"req": [("a",)]}, 0), ({"ack": [("a",)]}, 7),
              ({"req": [("b",)]}, 10), ({"ack": [("b",)]}, 13)]
    m, got = replay(SPEC, events)
    b = m.backend
    assert equiv(b, got[1], n_ge(m, "n", 7))
    assert equiv(b, got[3], n_ge(m, "n", 3))
    # Feasible region = n >= 7 AND n >= 3 = n >= 7.
    assert equiv(b, m.formulas[0].region, n_ge(m, "n", 7))


def test_g_threshold():
    spec = """
    pred p()
    pred q()
    prop g : G[<=m] p
    """
    events = [({"p": [()]}, 0), ({"p": [()]}, 2), ({"q": [()]}, 5)]
    m, got = replay(spec, events, prop="g")
    b = m.backend
    # Position 1: the first non-p position is at delay 5, so G[<=m] p holds
    # exactly for windows that stop short of it: m < 5.
    assert equiv(b, got[1], b.lt(pconst(m, "m"), b.lit(5, "Int")))


def test_cvc5_threshold():
    events = [({"req": [("a",)]}, 0), ({"ack": [("a",)]}, 7)]
    m, got = replay(SPEC, events, solver="cvc5")
    b = m.backend
    assert equiv(b, got[1], n_ge(m, "n", 7))
    assert got[2] is True


# --- past operators: verdicts are immediate ----------------------------------

PAST_SPEC = """
pred req(x: String)
pred rsp(x: String)
prop t : Forall x . rsp(x) -> P[<=n] req(x)
"""


def test_past_threshold():
    events = [({"req": [("a",)]}, 0), ({"rsp": [("a",)]}, 7)]
    m, got = replay(PAST_SPEC, events, prop="t")
    b = m.backend
    assert got[1] is True                       # no response there: vacuous
    assert equiv(b, got[2], n_ge(m, "n", 7))    # response 7 units after req


def test_past_verdict_is_immediate():
    """A past verdict is known at its own position -- no pending, no end()."""
    m = Monitor(parse_spec(PAST_SPEC), solver="z3")
    m.step({"req": [("a",)]}, 0)
    m.step({"rsp": [("a",)]}, 7)
    emitted = {pos: h for pos, name, h in m.resolved if name == "t"}
    assert 2 in emitted
    assert equiv(m.backend, emitted[2], n_ge(m, "n", 7))


def test_past_no_witness_is_false():
    events = [({"rsp": [("b",)]}, 5)]
    m, got = replay(PAST_SPEC, events, prop="t")
    assert got[1] is False


def test_past_region():
    events = [({"req": [("a",)]}, 0), ({"rsp": [("a",)]}, 7),
              ({"req": [("b",)]}, 10), ({"rsp": [("b",)]}, 13)]
    m, got = replay(PAST_SPEC, events, prop="t")
    b = m.backend
    assert equiv(b, got[2], n_ge(m, "n", 7))
    assert equiv(b, got[4], n_ge(m, "n", 3))
    assert equiv(b, m.formulas[0].region, n_ge(m, "n", 7))


def test_past_since_param():
    spec = """
    pred p()
    pred q()
    prop s : p S[0,n] q
    """
    events = [({"q": [()]}, 0), ({"p": [()]}, 3), ({"p": [()]}, 5)]
    m, got = replay(spec, events, prop="s")
    b = m.backend
    # q at age 5, p ever since: holds iff the window reaches back that far.
    assert equiv(b, got[3], n_ge(m, "n", 5))


def test_past_param_nested_under_once():
    """Past parametric operators may nest under other temporal operators."""
    spec = """
    pred q()
    pred r()
    prop x : P (P[<=n] q)
    """
    events = [({"q": [()]}, 0), ({"r": [()]}, 4)]
    m, got = replay(spec, events, prop="x")
    b = m.backend
    # At position 1 the inner window holds for n >= 0; Once keeps that alive.
    assert equiv(b, got[2], n_ge(m, "n", 0))


# --- until -------------------------------------------------------------------

UNTIL_SPEC = """
pred p()
pred q()
pred r()
prop u : p U[0,n] q
"""


def test_until_threshold():
    events = [({"p": [()]}, 0), ({"p": [()]}, 3), ({"q": [()]}, 7)]
    m, got = replay(UNTIL_SPEC, events, prop="u")
    b = m.backend
    # q arrives at delay 7 with p holding until then.
    assert equiv(b, got[1], n_ge(m, "n", 7))
    assert equiv(b, got[2], n_ge(m, "n", 4))
    assert equiv(b, got[3], n_ge(m, "n", 0))   # q now: delay 0


def test_until_first_witness_is_final():
    """The verdict resolves at the first witness, before end of trace."""
    m = Monitor(parse_spec(UNTIL_SPEC), solver="z3")
    m.step({"p": [()]}, 0)
    m.step({"q": [()]}, 5)
    emitted = {pos: h for pos, name, h in m.resolved if name == "u"}
    assert 1 in emitted
    assert equiv(m.backend, emitted[1], n_ge(m, "n", 5))


def test_until_dead_run_is_false_early():
    """p fails before any witness: false for every n, known at that event."""
    m = Monitor(parse_spec(UNTIL_SPEC), solver="z3")
    m.step({"p": [()]}, 0)
    m.step({"r": [()]}, 2)     # neither p nor q: the run from position 1 dies
    emitted = {pos: h for pos, name, h in m.resolved if name == "u"}
    assert emitted.get(1) is False


# --- lower bounds: discovered minimum delays/ages ----------------------------

def n_le(m, name, k):
    b = m.backend
    return b.le(pconst(m, name), b.lit(k, "Int"))


def test_past_lower_bound():
    """rsp -> P[>=n] req: holds iff the witness request is at least n old --
    the monitor discovers the guaranteed minimum age."""
    spec = """
    pred req(x: String)
    pred rsp(x: String)
    prop t : Forall x . rsp(x) -> P[>=n] req(x)
    """
    events = [({"req": [("a",)]}, 0), ({"rsp": [("a",)]}, 7),
              ({"req": [("b",)]}, 10), ({"rsp": [("b",)]}, 13)]
    m, got = replay(spec, events, prop="t")
    b = m.backend
    assert equiv(b, got[2], n_le(m, "n", 7))
    assert equiv(b, got[4], n_le(m, "n", 3))
    # Region: every response's request was at least n old, iff n <= 3.
    assert equiv(b, m.formulas[0].region, n_le(m, "n", 3))


def test_past_lower_bound_with_concrete_upper():
    """P[n,10]: the concrete upper bound still prunes; verdict over n."""
    spec = """
    pred req(x: String)
    pred rsp(x: String)
    prop t : Forall x . rsp(x) -> P[n,10] req(x)
    """
    events = [({"req": [("a",)]}, 0), ({"rsp": [("a",)]}, 7)]
    m, got = replay(spec, events, prop="t")
    assert equiv(m.backend, got[2], n_le(m, "n", 7))


def test_future_lower_bound_concrete_deadline():
    """F[n,10]: the deadline is concrete, so the obligation resolves once
    time passes it, with the constraint n <= (witness delay)."""
    spec = """
    pred req(x: String)
    pred ack(x: String)
    prop t : Forall x . req(x) -> F[n,10] ack(x)
    """
    m = Monitor(parse_spec(spec), solver="z3")
    m.step({"req": [("a",)]}, 0)
    m.step({"ack": [("a",)]}, 7)
    m.step({"noise": [()]}, 12)          # past the deadline: resolves now
    emitted = {pos: h for pos, name, h in m.resolved if name == "t"}
    assert 1 in emitted
    assert equiv(m.backend, emitted[1], n_le(m, "n", 7))


def test_future_lower_bound_unbounded():
    """F[n,*]: no deadline; resolves at end of trace."""
    spec = """
    pred req(x: String)
    pred ack(x: String)
    prop t : Forall x . req(x) -> F[n,*] ack(x)
    """
    events = [({"req": [("a",)]}, 0), ({"ack": [("a",)]}, 7)]
    m, got = replay(spec, events, prop="t")
    assert equiv(m.backend, got[1], n_le(m, "n", 7))


def test_g_lower_bound():
    """G[n,10] p: the counterexample at delay 5 rules out windows reaching
    it: holds iff n > 5."""
    spec = """
    pred p()
    pred q()
    prop g : G[n,10] p
    """
    events = [({"p": [()]}, 0), ({"p": [()]}, 2), ({"q": [()]}, 5),
              ({"p": [()]}, 12)]
    m, got = replay(spec, events, prop="g")
    b = m.backend
    assert equiv(b, got[1], b.gt(pconst(m, "n"), b.lit(5, "Int")))


def test_reject_two_symbolic_bounds():
    with pytest.raises(ValueError, match="one symbolic bound"):
        Monitor(parse_spec("pred p()\nprop x : P[m,n] p"))


# --- well-formedness ---------------------------------------------------------


def test_reject_param_used_twice():
    with pytest.raises(ValueError, match="exactly one"):
        Monitor(parse_spec("pred p()\npred q()\n"
                           "prop x : (F[<=n] p) & (F[<=n] q)"))


def test_reject_param_clashing_with_variable():
    with pytest.raises(ValueError, match="also occur as data variables"):
        Monitor(parse_spec("pred p(n: Int)\n"
                           "prop x : Forall n . p(n) -> F[<=n] p(n)"))


def test_reject_nested_param():
    with pytest.raises(ValueError, match="not be nested"):
        Monitor(parse_spec("pred p()\nprop x : P (F[<=n] p)"))


def test_two_distinct_params_ok():
    """Different parameters in different operators are each used once."""
    spec = """
    pred p()
    pred q()
    prop x : (F[<=n] p) & (F[<=m] q)
    """
    events = [({"p": [()]}, 3)]
    m, got = replay(spec, events, prop="x")
    b = m.backend
    # p at delay 3, q never: q's conjunct is false for every m.
    assert got[1] is False
