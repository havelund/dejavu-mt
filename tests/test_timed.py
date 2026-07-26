"""Tests for the timed (metric) operators: S[a,b], S[a,*], P/H variants and
the comparison sugar S[<=n], S[<n], S[>=n], S[>n].

Timed traces are given as (event, timestamp) pairs with absolute,
non-decreasing integer timestamps (in the CSV log format the timestamp is the
last column of each line, as in DejaVu).
"""
import pytest

from dejavumt import parse_spec, Monitor
from dejavumt import ast
from dejavumt.parser import parse_spec as parse


def verdicts(spec_text, timed_events, solver="z3"):
    m = Monitor(parse_spec(spec_text), solver=solver)
    return [m.step(ev, ts) for ev, ts in timed_events]


def violations(spec_text, timed_events, prop, solver="z3"):
    return [i + 1 for i, v in enumerate(verdicts(spec_text, timed_events, solver))
            if not v[prop]]


# --- parsing / sugar ---------------------------------------------------------

def prop_body(text):
    return parse(f"prop p : {text}").properties[0].body


def test_sugar_desugars_to_intervals():
    assert prop_body("a S[<=5] b") == ast.TimedSince(
        ast.Pred("a", ()), 0, 5, ast.Pred("b", ()), "[<=5]")
    assert prop_body("a S[<5] b").low == 0
    assert prop_body("a S[<5] b").high == 4
    assert prop_body("a S[>=5] b").low == 5
    assert prop_body("a S[>=5] b").high is None
    assert prop_body("a S[>5] b").low == 6
    assert prop_body("a S[>5] b").high is None
    assert prop_body("P[10,20] a") == ast.TimedOnce(
        10, 20, ast.Pred("a", ()), "[10,20]")
    assert prop_body("H[3,*] a").high is None


def test_display_preserves_source_bound():
    assert str(prop_body("a S[<=5] b")) == "(a S[<=5] b)"
    assert str(prop_body("P[3,*] a")) == "P[3,*] a"


def test_empty_interval_rejected():
    with pytest.raises(Exception):
        parse("prop p : P[<0] a")
    with pytest.raises(Exception):
        parse("prop p : P[5,3] a")


def test_plain_interval_formula_still_parses():
    # The untimed interval formula [phi, psi) must not be shadowed by bounds.
    body = prop_body("[a,b)")
    assert isinstance(body, ast.Interval)


# --- P[<=n]: the paper's worked example --------------------------------------

def test_once_le_paper_example():
    spec = """
    pred p(x: String)
    prop q : Exists x . P[<=5] p(x)
    """
    events = [
        ({"p": [("a",)]}, 0),
        ({"p": [("b",)]}, 3),
        ({"r": [()]}, 7),     # a expired (7-0>5), b alive
        ({"r": [()]}, 10),    # b expired (10-3>5) -> violation
    ]
    assert violations(spec, events, "q") == [4]


# --- lower bound: records must mature into the window ------------------------

def test_once_ge_maturation():
    spec = "prop q : P[>=3] a"
    events = [
        ({"a": [()]}, 0),    # age 0 < 3 -> violation
        ({"b": [()]}, 2),    # age 2 < 3 -> violation
        ({"b": [()]}, 3),    # age 3 -> holds
        ({"b": [()]}, 50),   # matured records stay forever
    ]
    assert violations(spec, events, "q") == [1, 2]


def test_once_two_sided_interval():
    spec = "prop q : P[2,4] a"
    events = [
        ({"a": [()]}, 0),    # age 0: too young -> violation
        ({"b": [()]}, 1),    # age 1: too young -> violation
        ({"b": [()]}, 2),    # age 2: in window
        ({"b": [()]}, 4),    # age 4: in window
        ({"b": [()]}, 5),    # age 5: expired -> violation
    ]
    assert violations(spec, events, "q") == [1, 2, 5]


# --- timed since with a real phi ---------------------------------------------

def test_since_le_with_data():
    # A use is OK only if granted at most 5 time units ago and not revoked since.
    spec = """
    pred g(x: String)
    pred r(x: String)
    pred u(x: String)
    prop q : Forall x . u(x) -> (!r(x)) S[<=5] g(x)
    """
    events = [
        ({"g": [("a",)]}, 0),
        ({"u": [("a",)]}, 3),    # ok: age 3
        ({"u": [("a",)]}, 7),    # violation: grant expired (7-0>5)
        ({"g": [("a",)]}, 8),
        ({"r": [("a",)]}, 9),
        ({"u": [("a",)]}, 10),   # violation: revoked since grant
    ]
    assert violations(spec, events, "q") == [3, 6]


def test_since_gt_saturation():
    spec = "prop p : r S[>2] q"
    events = [
        ({"q": [()]}, 0),    # age 0, not > 2 -> violation
        ({"r": [()]}, 1),    # age 1 -> violation
        ({"r": [()]}, 3),    # age 3 > 2 -> holds
        ({"r": [()]}, 50),   # matured record persists while r holds
        ({"s": [()]}, 51),   # r fails now and q absent -> violation
    ]
    assert violations(spec, events, "p") == [1, 2, 5]


# --- timed H -----------------------------------------------------------------

def test_hist_le():
    # H[<=2] p: p held at every position at most 2 time units old.
    spec = """
    pred p()
    prop q : H[<=2] p
    """
    events = [
        ({"p": [()]}, 0),
        ({"p": [()]}, 1),
        ({"q": [()]}, 3),    # this position (age 0) has no p -> violation
    ]
    assert violations(spec, events, "q") == [3]


# --- nesting -----------------------------------------------------------------

def test_nested_timed():
    # P[<=10] (P[<=2] p): p held within 2 units of some point within 10 units.
    spec = "prop q : P[<=10] (P[<=2] p)"
    events = [
        ({"p": [()]}, 0),    # inner true -> outer records it
        ({"r": [()]}, 5),    # inner false now, but outer record age 5 <= 10
        ({"r": [()]}, 20),   # outer record expired -> violation
    ]
    assert violations(spec, events, "q") == [3]


# --- interval consistency: sugar and primitive agree -------------------------

def test_sugar_equals_primitive_verdicts():
    events = [
        ({"a": [()]}, 0),
        ({"b": [()]}, 2),
        ({"b": [()]}, 5),
        ({"b": [()]}, 6),
    ]
    assert (violations("prop q : P[<=5] a", events, "q")
            == violations("prop q : P[0,5] a", events, "q"))
    assert (violations("prop q : P[>2] a", events, "q")
            == violations("prop q : P[3,*] a", events, "q"))


# --- machinery ---------------------------------------------------------------

def test_missing_timestamp_raises():
    m = Monitor(parse_spec("prop q : P[<=5] a"))
    assert m.timed
    with pytest.raises(ValueError):
        m.step({"a": [()]})


def test_untimed_spec_not_timed():
    m = Monitor(parse_spec("prop q : P a"))
    assert not m.timed


def test_state_is_pruned():
    # The stored state of a timed node drops expired records (Z3 backend).
    m = Monitor(parse_spec("pred p(x: String)\nprop q : Exists x . P[<=5] p(x)"))
    fm = m.formulas[0]
    tn = next(i for i, n in enumerate(fm.nodes) if n.kind == "tonce")
    m.step({"p": [("a",)]}, 0)
    m.step({"r": [()]}, 100)   # far past the window
    assert fm.backend.is_false(fm.pre[tn])


# --- one node per operator (scheme B) ----------------------------------------

def test_untimed_hist_dedicated_node():
    # H p: vacuously true, true while p holds, false forever after first !p.
    spec = "prop q : H p"
    m = Monitor(parse_spec(spec))
    kinds = [n.kind for n in m.formulas[0].nodes]
    assert "hist" in kinds and "once" not in kinds
    vs = [m.formulas[0].step(ev) for ev in
          [{"p": [()]}, {"p": [()]}, {"r": [()]}, {"p": [()]}]]
    assert vs == [True, True, False, False]


def test_tree_shapes_no_encoding_artifacts():
    # P[<=n] phi: one node, one child (no constant-true leaf).
    fm = Monitor(parse_spec("prop q : P[<=5] a")).formulas[0]
    tn = next(n for n in fm.nodes if n.kind == "tonce")
    assert len(tn.children) == 1
    assert all(n.kind != "true" for n in fm.nodes)
    # H[<=n] phi: one thist node, one child, no not/once chain.
    fm = Monitor(parse_spec("prop q : H[<=5] a")).formulas[0]
    kinds = [n.kind for n in fm.nodes]
    assert kinds.count("thist") == 1
    assert "not" not in kinds and "tonce" not in kinds
    # Untimed H phi: one hist node, no not/once chain.
    fm = Monitor(parse_spec("prop q : H a")).formulas[0]
    kinds = [n.kind for n in fm.nodes]
    assert kinds.count("hist") == 1
    assert "not" not in kinds and "once" not in kinds


def test_hist_le_matches_rewrite_semantics():
    # H[<=n] phi must equal !P[<=n]!phi (written with explicit operators).
    events = [
        ({"p": [()]}, 0),
        ({"p": [()]}, 2),
        ({"q": [()]}, 3),
        ({"p": [()]}, 6),
        ({"p": [()]}, 9),
        ({"p": [()]}, 20),
    ]
    direct = violations("pred p()\nprop q : H[<=4] p", events, "q")
    rewrite = violations("pred p()\nprop q : ! P[<=4] ! p", events, "q")
    assert direct == rewrite


# --- cvc5 cross-check --------------------------------------------------------

def test_timed_on_cvc5():
    pytest.importorskip("cvc5")
    spec = """
    pred p(x: String)
    prop q : Exists x . P[<=5] p(x)
    """
    events = [
        ({"p": [("a",)]}, 0),
        ({"p": [("b",)]}, 3),
        ({"r": [()]}, 7),
        ({"r": [()]}, 10),
    ]
    assert violations(spec, events, "q", solver="cvc5") == [4]
