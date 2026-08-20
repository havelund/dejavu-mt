"""Tests for data-dependent interval bounds: a quantified variable used as
a bound (`Forall n . a(n) -> F[0,n] b`) -- each event carries its own
deadline.  The quantifier discharges the bound, so verdicts are Boolean.
"""
import pytest

from dejavumt import parse_spec, Monitor


def replay(spec_text, events, prop="x", solver="z3"):
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


FSPEC = """
pred a(n: Int)
pred b()
pred c()
prop x : Forall n . a(n) -> F[0,n] b
"""


def test_future_databound_met():
    # a carries deadline 5; b arrives at delay 3.
    m, got = replay(FSPEC, [({"a": [(5,)]}, 0), ({"b": [()]}, 3)])
    assert got == {1: True, 2: True}


def test_future_databound_missed():
    # deadline 2, witness at delay 3: violated -- and decided at the witness
    # event, since by then the window [0,2] is already outrun.
    m = Monitor(parse_spec(FSPEC))
    m.step({"a": [(2,)]}, 0)
    m.step({"b": [()]}, 3)
    emitted = {pos: h for pos, name, h in m.resolved if name == "x"}
    assert emitted.get(1) is False


def test_future_databound_deadline_passes():
    # No b at all: false as soon as time outruns the carried deadline.
    m = Monitor(parse_spec(FSPEC))
    m.step({"a": [(5,)]}, 0)
    m.step({"c": [()]}, 10)
    emitted = {pos: h for pos, name, h in m.resolved if name == "x"}
    assert emitted.get(1) is False


def test_future_databound_open_at_end():
    # Trace ends inside the window: forced false at end().
    m, got = replay(FSPEC, [({"a": [(5,)]}, 0), ({"c": [()]}, 2)])
    assert got[1] is False


def test_future_databound_two_deadlines():
    # Two a-events with different deadlines at the same position: the
    # quantifier makes BOTH bind, so the strictest one decides.
    m, got = replay(FSPEC, [({"a": [(2,), (9,)]}, 0), ({"b": [()]}, 5)])
    assert got[1] is False    # deadline 2 missed (9 was met)


def test_past_databound():
    spec = """
    pred req()
    pred rsp(d: Int)
    prop x : Forall d . rsp(d) -> P[0,d] req
    """
    events = [({"req": [()]}, 0), ({"rsp": [(7,)]}, 5),
              ({"rsp": [(3,)]}, 10)]
    m, got = replay(spec, events)
    assert got[2] is True     # req is 5 old, allowance 7
    assert got[3] is False    # req is 10 old, allowance 3


def test_nested_databound():
    """P (F[0,n] b) under Forall n: the deep placeholder must take n as an
    argument so the quantifier binds through it."""
    spec = """
    pred a(n: Int)
    pred b()
    pred q()
    prop x : Forall n . a(n) -> P (F[0,n] b)
    """
    # b at t=2 (position 1); a(3) at t=5: some earlier position (position 1)
    # has b within [2, 2+3] -- holds.
    m, got = replay(spec, [({"b": [()]}, 2), ({"q": [()]}, 4),
                           ({"a": [(3,)]}, 5)])
    assert got[3] is True
    # a(1) at t=5, no b anywhere near: every window [T_k, T_k+1] is empty.
    m, got = replay(spec, [({"q": [()]}, 0), ({"a": [(1,)]}, 5)])
    assert got[2] is False


def test_databound_must_be_int():
    with pytest.raises(ValueError, match="must be an Int"):
        Monitor(parse_spec("pred a(n: String)\npred b()\n"
                           "prop x : Forall n . a(n) -> F[0,n] b"))


def test_databound_with_until():
    spec = """
    pred a(n: Int)
    pred b()
    pred c()
    prop x : Forall n . a(n) -> X (c U[0,n] b)
    """
    # a(5)@0, then c,c,b within 5 of position 2's time: satisfied.
    m, got = replay(spec, [({"a": [(5,)]}, 0), ({"c": [()]}, 1),
                           ({"c": [()]}, 2), ({"b": [()]}, 4)])
    assert got[1] is True
    # a(1)@0: witness needed within 1 unit of position 2, c@1 then b@4: too
    # late.
    m, got = replay(spec, [({"a": [(1,)]}, 0), ({"c": [()]}, 1),
                           ({"c": [()]}, 2), ({"b": [()]}, 4)])
    assert got[1] is False


def test_databound_cvc5():
    m, got = replay(FSPEC, [({"a": [(5,)]}, 0), ({"b": [()]}, 3)],
                    solver="cvc5")
    assert got == {1: True, 2: True}
