"""Tests for sequence patterns (PSL-style SEREs): {e1; e2[*]; e3} |-> psi
and standalone {..} as a formula, desugared to auto-generated @-guarded
rules.  Matching ends at the current position and may start anywhere
(search semantics); data variables are shared across items.
"""
import pytest

from dejavumt import parse_spec, Monitor


def replay(spec_text, events, prop, solver="z3"):
    m = Monitor(parse_spec(spec_text), solver=solver)
    got = {}
    for ev in events:
        m.step(ev)
        for pos, name, holds in m.resolved:
            if name == prop:
                got[pos] = holds
    for pos, name, holds in m.end():
        if name == prop:
            got[pos] = holds
    return [got.get(i + 1) for i in range(len(events))]


def test_plain_sequence_equals_prev_chain():
    """{a; b; c} standalone == c & @b & @@a, checked on a trace."""
    spec = """
    pred a()
    pred b()
    pred c()
    prop s : {a; b; c}
    prop m : c & (@ b) & (@ @ a)
    """
    events = [{"a": [()]}, {"b": [()]}, {"c": [()]}, {"c": [()]}]
    assert (replay(spec, events, "s")
            == replay(spec, events, "m")
            == [False, False, True, False])


def test_star_trigger():
    """Failed logins, then success, then (no logout) then sudo -> vetted."""
    spec = """
    pred fail(u: String)
    pred ok(u: String)
    pred sudo(u: String)
    pred vetted(u: String)
    prop b : Forall u .
        ({fail(u); fail(u); ok(u); (! sudo(u))[*]; sudo(u)}
            |-> P vetted(u))
    """
    good = [{"vetted": [("bob",)]}, {"fail": [("bob",)]},
            {"fail": [("bob",)]}, {"ok": [("bob",)]},
            {"noise": [()]}, {"sudo": [("bob",)]}]
    assert replay(spec, good, "b") == [True] * 6
    bad = good[1:]                     # no prior vetting
    assert replay(spec, bad, "b") == [True, True, True, True, False]


def test_plus_and_count():
    spec = """
    pred t()
    pred c()
    prop p3 : {t[*3]; c}
    prop pp : {c; t[+]}
    """
    events = [{"t": [()]}, {"t": [()]}, {"t": [()]}, {"c": [()]},
              {"t": [()]}]
    assert replay(spec, events, "p3") == [False, False, False, True, False]
    assert replay(spec, events, "pp") == [False] * 4 + [True]


def test_data_binding_across_items():
    """The same u must thread the whole sequence."""
    spec = """
    pred req(u: String)
    pred grant(u: String)
    prop g : Exists u . {req(u); grant(u)}
    """
    events = [{"req": [("a",)]}, {"grant": [("a",)]},
              {"req": [("b",)]}, {"grant": [("c",)]}]
    assert replay(spec, events, "g") == [False, True, False, False]


def test_group_parity_beyond_ltl():
    """{a; {b; b}[*]; c}: c preceded by an EVEN number of b's back to an
    a -- segment parity, not expressible in raw LTL, free via rules."""
    spec = """
    pred a()
    pred b()
    pred c()
    prop even : {a; {b; b}[*]; c}
    """
    ev_even = [{"a": [()]}, {"b": [()]}, {"b": [()]}, {"c": [()]}]
    ev_odd = [{"a": [()]}, {"b": [()]}, {"c": [()]}]
    assert replay(spec, ev_even, "even") == [False, False, False, True]
    assert replay(spec, ev_odd, "even") == [False, False, False]


def test_seq_under_temporal_operator():
    """P {a; b}: a match ended at some point."""
    spec = "pred a()\npred b()\npred q()\nprop p : P {a; b}"
    events = [{"a": [()]}, {"b": [()]}, {"q": [()]}]
    assert replay(spec, events, "p") == [False, True, True]


def test_nullable_sequence_is_true():
    spec = "pred t()\nprop n : {t[*]}"
    assert replay(spec, [{"q": [()]}], "n") == [True]


def test_seq_in_rule_body_rejected():
    with pytest.raises(ValueError, match="not supported inside rule"):
        Monitor(parse_spec("pred a()\npred b()\npred c(x: String)\n"
                           "prop p : Forall x . c(x) -> r(x) "
                           "where r(x) := c(x) & {a; b}"))


def test_future_inside_item_rejected():
    with pytest.raises(ValueError, match="future operators"):
        Monitor(parse_spec("pred a()\npred b()\nprop p : {F a; b}"))


def test_seq_cvc5():
    spec = "pred a()\npred b()\npred c()\nprop s : {a; b; c}"
    events = [{"a": [()]}, {"b": [()]}, {"c": [()]}]
    assert replay(spec, events, "s", solver="cvc5") == [False, False, True]
