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


# --- nesting: future below past operators, future inside future --------------

def test_once_of_eventually():
    # P (F[<=2] p): some position so far whose 2-unit lookahead saw a p.
    spec = "prop q : P (F[<=2] p)"
    events = [({"r": [()]}, 0), ({"p": [()]}, 1), ({"r": [()]}, 5),
              ({"r": [()]}, 9)]
    assert run(spec, events) == [True, True, True, True]
    # and with no p at all:
    assert run(spec, [({"r": [()]}, 0), ({"r": [()]}, 5)]) == [False, False]


def test_once_of_eventually_resolves_early():
    m = Monitor(parse_spec("prop q : P (F[<=2] p)"))
    m.step({"r": [()]}, 0)
    assert m.resolved == []            # position 1 pending
    m.step({"p": [()]}, 1)
    assert (1, "q", True) in m.resolved   # resolved by the p, before deadline


def test_eventually_of_eventually():
    # F[<=5] (p & F[<=3] q): a p within 5 that is itself followed by a q
    # within 3.
    spec = "prop q : F[<=5] (p & F[<=3] q)"
    events = [({"p": [()]}, 0), ({"q": [()]}, 2), ({"r": [()]}, 9),
              ({"r": [()]}, 20)]
    assert run(spec, events) == [True, False, False, False]


def test_since_of_eventually():
    # a S (F[<=2] p): the future subformula feeds the since-state.
    spec = "prop q : a S (F[<=2] p)"
    events = [({"a": [()]}, 0), ({"p": [()]}, 1), ({"a": [()]}, 2),
              ({"r": [()]}, 5)]
    assert run(spec, events) == [True, True, True, False]


def test_prev_of_eventually():
    # @ (F[<=2] p): the future subformula read through @.
    spec = "prop q : @ (F[<=2] p)"
    events = [({"r": [()]}, 0), ({"p": [()]}, 1), ({"r": [()]}, 9)]
    assert run(spec, events) == [False, True, True]


def test_nested_with_data():
    # Every req must, within 5, see a grant that is confirmed within 2.
    spec = """
    pred req(x: String)
    pred grant(x: String)
    pred conf(x: String)
    prop q : Forall x . req(x) -> F[<=5] (grant(x) & F[<=2] conf(x))
    """
    events = [
        ({"req": [("a",)]}, 0),
        ({"grant": [("a",)]}, 2),
        ({"conf": [("a",)]}, 3),     # grant@2 confirmed@3 -> pos 1 holds
        ({"req": [("b",)]}, 10),
        ({"grant": [("b",)]}, 12),   # never confirmed
        ({"r": [()]}, 30),
    ]
    assert run(spec, events) == [True, True, True, False, True, True]


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


# --- differential fuzzing against the brute-force reference ------------------

def test_fuzz_against_reference():
    # experiments/fuzz_reference.py transcribes the assignment semantics and
    # diffs verdicts on random formulas and traces (duplicated timestamps
    # included).  A fixed-seed slice runs in the suite; run it standalone with
    # more iterations for real fuzzing.
    import experiments.fuzz_reference as fr
    import random
    rng = random.Random(42)
    for _ in range(60):
        body = fr.rand_formula(rng, rng.randint(1, 3))
        events, times = fr.rand_trace(rng)
        assert fr.disagrees(body, events, times) is None, (
            f"{body} on {[sorted(e) for e in events]} @ {times}")


def test_equal_timestamp_past_position_not_a_future_witness():
    # Found by the reference fuzzer: with duplicate timestamps, a row in the
    # time window may lie BEFORE the anchor position.  Position 2 must not
    # count position 1's r as its future witness.
    events = [({"r": [()]}, 5), ({"q": [()]}, 5)]
    assert run("prop q : F[<=4] r", events) == [True, False]
    assert run("prop q : F[<=4] F[<=2] r", events) == [True, False]
    # dual: position 1's !p must not refute position 2's G either
    ev2 = [({"q": [()]}, 5), ({"p": [()]}, 5)]
    assert run("prop q : G[<=4] p", ev2) == [False, True]
