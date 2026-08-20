"""Tests for anchored properties: `prop p anchored : f` evaluates f at
position 1 only (the classic trace |= f reading), instead of the default
one-verdict-per-position (implicit-G) mode.
"""
from dejavumt import parse_spec, Monitor
from dejavumt.parser import parse_spec as parse


def replay(spec_text, events, prop, timed=False, solver="z3"):
    """(monitor, {position: verdict}) after the trace and end()."""
    m = Monitor(parse_spec(spec_text), solver=solver)
    got = {}
    for e in events:
        ev, ts = e if timed else (e, None)
        m.step(ev, ts)
        for pos, name, holds in m.resolved:
            if name == prop:
                got[pos] = holds
    for pos, name, holds in m.end():
        if name == prop:
            got[pos] = holds
    return m, got


def test_anchored_parse():
    spec = parse("pred p()\nprop a anchored : F p\nprop b : F p")
    assert spec.properties[0].anchored is True
    assert spec.properties[1].anchored is False


def test_anchored_future_no_tail_flood():
    """F p anchored: one verdict, at position 1; the default mode would also
    report every position after the last p as false."""
    spec = "pred p()\npred q()\nprop a anchored : F p"
    events = [{"q": [()]}, {"p": [()]}, {"q": [()]}, {"q": [()]}]
    m, got = replay(spec, events, prop="a")
    assert got == {1: True}


def test_default_mode_reports_tail():
    """The same property unanchored: the tail after the last p is false."""
    spec = "pred p()\npred q()\nprop a : F p"
    events = [{"q": [()]}, {"p": [()]}, {"q": [()]}, {"q": [()]}]
    m, got = replay(spec, events, prop="a")
    assert got == {1: True, 2: True, 3: False, 4: False}


def test_anchored_future_false():
    spec = "pred p()\npred q()\nprop a anchored : F p"
    events = [{"q": [()]}, {"q": [()]}]
    m, got = replay(spec, events, prop="a")
    assert got == {1: False}


def test_anchored_past():
    """Anchored past formula: judged at position 1, then nothing more."""
    spec = "pred p()\npred q()\nprop a anchored : p"
    events = [{"p": [()]}, {"q": [()]}]
    m, got = replay(spec, events, prop="a")
    assert got == {1: True}


def test_anchored_parametric():
    """Anchored + parametric: one constraint for the whole trace."""
    spec = """
    pred req()
    pred ack()
    prop a anchored : req -> F[<=n] ack
    """
    events = [({"req": [()]}, 0), ({"ack": [()]}, 7)]
    m, got = replay(spec, events, prop="a", timed=True)
    b = m.backend
    assert list(got) == [1]
    n = m.formulas[0].params["n"]
    assert not b.check_sat(b.not_(b.iff(got[1], b.ge(n, b.lit(7, "Int")))))
