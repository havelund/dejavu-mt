"""Tests for the bounded future operators: F[a,b], G[a,b], U[a,b], X.

A property with a future operator cannot in general be judged at its own
position, so verdicts carry positions and may be emitted at a later event (or
at the end of the trace, which closes every window).  `run` below replays a
trace and collects the verdict of every position, whenever it arrives.
"""
import pytest

from dejavumt import parse_spec, Monitor
from dejavumt import ast
from dejavumt.parser import parse_spec as parse


def run(spec_text, events, prop="q", timed=True, solver="z3"):
    """Verdicts per position, in position order; None if never determined."""
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
    return [got.get(i + 1) for i in range(len(events))]


def prop_body(text):
    return parse(f"prop p : {text}").properties[0].body


# --- parsing -----------------------------------------------------------------

def test_future_syntax():
    assert prop_body("F[<=5] a") == ast.TimedEventually(
        0, 5, ast.Pred("a", ()), "[<=5]")
    assert prop_body("G[2,7] a") == ast.TimedAlways(
        2, 7, ast.Pred("a", ()), "[2,7]")
    assert prop_body("b U[<=5] a") == ast.TimedUntil(
        ast.Pred("b", ()), 0, 5, ast.Pred("a", ()), "[<=5]")
    assert prop_body("X a") == ast.Next(ast.Pred("a", ()))
    # unbounded forms
    assert prop_body("F a").high is None
    assert prop_body("b U a").high is None
    assert str(prop_body("F[<=5] a")) == "F[<=5] a"


def test_operator_letters_are_not_predicate_names():
    # F/G/U/X only lex as operators when not part of an identifier.
    assert isinstance(prop_body("Fun(x)"), ast.Pred)
    assert isinstance(prop_body("Gate"), ast.Pred)
    assert isinstance(prop_body("Xy(a)"), ast.Pred)


# --- F: eventually -----------------------------------------------------------

def test_eventually_request_response():
    spec = """
    pred req(x: String)
    pred ack(x: String)
    prop q : Forall x . req(x) -> F[<=5] ack(x)
    """
    events = [
        ({"req": [("a",)]}, 3),     # answered at event 3 (T=6, within [3,8])
        ({"ack": [("b",)]}, 4),     # no req: holds at once
        ({"ack": [("a",)]}, 6),
        ({"req": [("c",)]}, 10),    # never answered -> violated
        ({"other": [()]}, 20),      # deadline 15 has passed
    ]
    assert run(spec, events) == [True, True, True, False, True]


def test_eventually_resolves_early_and_at_deadline():
    spec = "prop q : req -> F[<=5] ack"
    events = [({"req": [()]}, 0), ({"ack": [()]}, 2), ({"req": [()]}, 10),
              ({"other": [()]}, 20)]
    assert run(spec, events) == [True, True, False, True]


def test_eventually_includes_present():
    # F[<=n] looks from the current position onwards, inclusive.
    assert run("prop q : F[<=5] p", [({"p": [()]}, 0)]) == [True]


def test_unresolved_at_end_of_trace_is_forced():
    # The window is still open when the trace ends: no witness -> false.
    assert run("prop q : F[<=99] p", [({"r": [()]}, 0)]) == [False]


# --- G: always ---------------------------------------------------------------

def test_always_window():
    spec = "prop q : G[<=5] p"
    events = [({"p": [()]}, 0), ({"p": [()]}, 2), ({"r": [()]}, 4),
              ({"p": [()]}, 9), ({"p": [()]}, 20)]
    #   1,2,3 all see the counterexample at T=4;  4 and 5 do not
    assert run(spec, events) == [False, False, False, True, True]


def test_always_equals_negated_eventually():
    events = [({"r": [()]}, 0), ({"p": [()]}, 3), ({"r": [()]}, 9),
              ({"r": [()]}, 20)]
    assert (run("prop q : G[<=5] !p", events)
            == run("prop q : ! F[<=5] p", events))


# --- U: until ----------------------------------------------------------------

def test_until_basic():
    spec = "prop q : busy U[<=5] ack"
    events = [({"busy": [()]}, 0), ({"busy": [()]}, 2),
              ({"ack": [()]}, 4), ({"r": [()]}, 9)]
    assert run(spec, events) == [True, True, True, False]


def test_until_phi_not_required_at_the_witness():
    # phi is required at every position from the anchor up to, but excluding,
    # the witness.  Here busy fails only at the ack position itself.
    assert run("prop q : busy U[<=5] ack",
               [({"busy": [()]}, 0), ({"ack": [()]}, 1)]) == [True, True]


def test_until_broken_run_resolves_false():
    spec = "prop q : busy U[<=5] ack"
    events = [({"busy": [()]}, 0), ({"r": [()]}, 2), ({"ack": [()]}, 4)]
    assert run(spec, events) == [False, False, True]


def test_until_with_data():
    spec = """
    pred req(x: String)
    pred busy(x: String)
    pred ack(x: String)
    prop q : Forall x . req(x) -> busy(x) U[<=5] ack(x)
    """
    events = [
        ({"req": [("a",)]}, 3),     # busy(a) missing at the anchor -> false
        ({"busy": [("a",)]}, 4),
        ({"ack": [("a",)]}, 6),
        ({"other": [()]}, 9),
    ]
    assert run(spec, events) == [False, True, True, True]


def test_until_lower_bound():
    # A witness before the window's start does not count.
    spec = "prop q : busy U[2,5] ack"
    events = [({"busy": [()]}, 0), ({"ack": [()]}, 1),
              ({"busy": [()]}, 2), ({"ack": [()]}, 3)]
    assert run(spec, events) == [False, False, False, False]


# --- X: next -----------------------------------------------------------------

def test_next():
    events = [{"p": [()]}, {"p": [()]}, {"r": [()]}, {"p": [()]}]
    assert run("prop q : X p", events, timed=False) == [True, False, True, False]


def test_next_needs_no_timestamps():
    m = Monitor(parse_spec("prop q : X p"))
    assert m.future and not m.timed


# --- unbounded (LTL) forms ---------------------------------------------------

def test_unbounded_eventually_and_until():
    events = [{"r": [()]}, {"p": [()]}, {"r": [()]}]
    assert run("prop q : F p", events, timed=False) == [True, True, False]
    assert run("prop q : r U p", events, timed=False) == [True, True, False]


def test_unbounded_needs_no_timestamps():
    m = Monitor(parse_spec("prop q : F p"))
    assert m.future and not m.timed


# --- machinery ---------------------------------------------------------------

def test_verdict_may_be_pending_then_arrive_late():
    m = Monitor(parse_spec("prop q : req -> F[<=5] ack"))
    assert m.step({"req": [()]}, 0) == {"q": None}      # undecided here
    assert m.resolved == []
    m.step({"ack": [()]}, 1)
    assert (1, "q", True) in m.resolved                 # position 1, at event 2


def test_future_under_past_operator_is_rejected():
    for spec in ["prop q : P (F[<=5] a)",
                 "prop q : F[<=5] (F[<=3] a)",
                 "prop q : a S (F[<=5] b)"]:
        with pytest.raises(ValueError, match="future operator"):
            Monitor(parse_spec(spec))


def test_tables_are_cleared_when_nothing_is_pending():
    m = Monitor(parse_spec("prop q : req -> F[<=5] ack"))
    fm = m.formulas[0]
    j = fm.fnodes[0]
    m.step({"ack": [()]}, 0)          # recorded, but no obligation wants it
    assert all(fm.backend.is_false(t) for t in fm.ftab[j])


def test_past_only_spec_is_not_future():
    m = Monitor(parse_spec("prop q : P a"))
    assert not m.future
    assert m.end() == []


# --- cvc5 --------------------------------------------------------------------

def test_future_on_cvc5():
    pytest.importorskip("cvc5")
    spec = "prop q : req -> F[<=5] ack"
    events = [({"req": [()]}, 0), ({"ack": [()]}, 2), ({"req": [()]}, 10),
              ({"other": [()]}, 20)]
    assert run(spec, events, solver="cvc5") == [True, True, False, True]


# --- regressions (Fable review of the first implementation) ------------------

def test_until_runs_with_equal_timestamps_are_distinct():
    # Two positions share timestamp 0; busy fails at the second.  Runs are
    # identified by position, so the break must not be masked by the second
    # run's stamp.
    spec = "prop q : busy U[<=5] ack"
    events = [({"busy": [()]}, 0), ({"r": [()]}, 0), ({"ack": [()]}, 1)]
    assert run(spec, events) == [False, False, True]


def test_next_resolves_at_the_next_event():
    # Positions are strictly increasing: X's window closes at the very next
    # event, not one later.
    m = Monitor(parse_spec("prop q : X p"))
    m.step({"p": [()]})
    assert m.resolved == []
    m.step({"q": [()]})
    assert (1, "q", False) in m.resolved


def test_until_broken_run_resolves_before_deadline():
    # The run breaks at event 2; the verdicts must not wait for deadline 100.
    m = Monitor(parse_spec("prop q : busy U[<=100] ack"))
    m.step({"busy": [()]}, 0)
    m.step({"r": [()]}, 1)
    assert (1, "q", False) in m.resolved and (2, "q", False) in m.resolved
