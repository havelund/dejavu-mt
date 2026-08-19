"""Tests for `matches`: patterns with holes over String terms.

A pattern is a *constraint*: subject = lit0 ++ hole1 ++ lit1 ++ ... (plus a
regex membership per constrained hole).  Holes are ordinary data variables;
ALL decompositions count (declarative matching, not leftmost-greedy).
"""
import pytest

from dejavumt import parse_spec, Monitor
from dejavumt.pattern import parse_pattern, PatternError


def verdicts(spec_text, events, solver="z3"):
    m = Monitor(parse_spec(spec_text))
    return [m.step(ev)["p"] for ev in events]


def violations(spec_text, events, solver="z3"):
    m = Monitor(parse_spec(spec_text), solver=solver)
    return [i + 1 for i, ev in enumerate(events) if not m.step(ev)["p"]]


def test_capture_binds_the_hole():
    spec = """
    pred login(m: String)
    pred ok(u: String)
    prop p : Forall m . Forall u . login(m) & m matches "user {u}" -> ok(u)
    """
    events = [
        {"login": [("user klaus",)], "ok": [("klaus",)]},   # u = "klaus": ok
        {"login": [("user doron",)], "ok": [("klaus",)]},   # wrong u -> violation
        {"login": [("admin klaus",)]},                       # no match: vacuous
    ]
    assert violations(spec, events) == [2]


def test_all_decompositions_count():
    # "x-y-z" matches "{a}-{c}" in two ways: (x, y-z) and (x-y, z); the
    # Forall covers both, so BOTH a-values must have been started.
    spec = """
    pred log(m: String)
    pred start(a: String)
    prop p : Forall m . Forall a . Forall c .
        log(m) & m matches "{a}-{c}" -> P start(a)
    """
    only_one = [{"start": [("x",)]}, {"log": [("x-y-z",)]}]
    both = [{"start": [("x",)]}, {"start": [("x-y",)]}, {"log": [("x-y-z",)]}]
    assert violations(spec, only_one) == [2]
    assert violations(spec, both) == []


def test_constrained_hole_regex():
    spec = """
    pred log(m: String)
    prop p : Forall m . log(m) -> Exists n . m matches "id {n:[0-9]+}"
    """
    events = [
        {"log": [("id 42",)]},      # digits: ok
        {"log": [("id x7",)]},      # not digits -> violation
        {"log": [("id 7",)]},
    ]
    assert violations(spec, events) == [2]


def test_repeated_hole_forces_equality():
    spec = """
    pred log(m: String)
    prop p : Forall m . log(m) -> Exists u . m matches "{u} and {u}"
    """
    events = [
        {"log": [("a and a",)]},    # same on both sides: ok
        {"log": [("a and b",)]},    # different -> violation
    ]
    assert violations(spec, events) == [2]


def test_capture_feeds_future_obligation():
    # The motivating example: extract the user, await their logout.
    spec = """
    pred login(m: String)
    pred logout(u: String)
    prop p : Forall m . Forall u .
        login(m) & m matches "user {u}" -> F[<=5] logout(u)
    """
    events = [
        ({"login": [("user klaus",)]}, 0),
        ({"logout": [("klaus",)]}, 3),      # discharges position 1, early
        ({"login": [("user doron",)]}, 10),
        ({"logout": [("grigore",)]}, 12),   # wrong user
        ({"r": [()]}, 20),                  # deadline 15 passed
    ]
    m = Monitor(parse_spec(spec))
    got = {}
    for ev, ts in events:
        m.step(ev, ts)
        for pos, _n, holds in m.resolved:
            got[pos] = holds
    for pos, _n, holds in m.end():
        got[pos] = holds
    assert [got.get(i + 1) for i in range(5)] == [True, True, False, True, True]


def test_pattern_errors():
    with pytest.raises(PatternError):
        parse_pattern("user {u")
    with pytest.raises(PatternError):
        parse_pattern("a } b")
    with pytest.raises(PatternError):
        parse_pattern("{u:[0-9}")


def test_match_on_cvc5():
    pytest.importorskip("cvc5")
    spec = """
    pred login(m: String)
    pred ok(u: String)
    prop p : Forall m . Forall u . login(m) & m matches "user {u}" -> ok(u)
    """
    events = [
        {"login": [("user klaus",)], "ok": [("klaus",)]},
        {"login": [("user doron",)], "ok": [("klaus",)]},
    ]
    assert violations(spec, events, solver="cvc5") == [2]
