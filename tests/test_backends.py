"""
Cross-backend tests: the Z3 and CVC5 backends must produce identical verdicts.
"""
import pytest

from dejavumt import parse_spec, Monitor


def _violations(spec_text, events, prop, solver):
    m = Monitor(parse_spec(spec_text), solver=solver)
    return [i + 1 for i, ev in enumerate(events) if not m.step(ev)[prop]]


# (spec, events, prop, expected-violating-event-numbers)
CASES = {
    "file": (
        """
        pred close(f: String)
        pred open(f: String, m: String)
        prop file : Forall f . close(f) -> Exists m . @ [open(f,m),close(f))
        """,
        [{"open": [("a", "read")]}, {"close": [("a",)]}, {"close": [("b",)]},
         {"open": [("c", "write")]}, {"open": [("c", "read")]}, {"close": [("c",)]}],
        "file", [3],
    ),
    "since": (
        """
        pred grant(r: String)
        pred revoke(r: String)
        pred use(r: String)
        prop access : Forall r . use(r) -> (!revoke(r)) S grant(r)
        """,
        [{"grant": [("a",)]}, {"use": [("a",)]}, {"grant": [("b",)]}, {"use": [("b",)]},
         {"revoke": [("a",)]}, {"use": [("a",)]}, {"grant": [("a",)]}, {"use": [("a",)]}],
        "access", [6],
    ),
    "arith_lt": (
        """
        pred bid(i: String, a: Int)
        prop p : Forall i . Forall a1 . Forall a2 . @ P bid(i,a1) & bid(i,a2) -> a1 < a2
        """,
        [{"bid": [("chair", "700")]}, {"bid": [("chair", "800")]},
         {"bid": [("chair", "650")]}, {"bid": [("table", "100")]}],
        "p", [3],
    ),
    "arith_mul": (
        """
        pred a(x: Int)
        pred b(y: Int)
        prop p : Forall x . Forall y . a(x) & b(y) -> y = x * 2
        """,
        [{"a": [("1",)], "b": [("2",)]}, {"a": [("3",)], "b": [("5",)]}],
        "p", [2],
    ),
    "macros": (
        """
        pred login(u: String)
        pred logout(u: String)
        pred open(f: String)
        pred close(f: String)
        pred access(u: String, f: String)
        pred loggedIn(u) = [login(u),logout(u))
        pred opened(f)   = [open(f),close(f))
        prop access : Forall u . Forall f . access(u,f) -> loggedIn(u) & opened(f)
        """,
        [{"login": [("alice",)]}, {"open": [("data",)]},
         {"access": [("alice", "data")]}, {"logout": [("alice",)]},
         {"access": [("alice", "data")]}],
        "access", [5],
    ),
}


@pytest.mark.parametrize("case", sorted(CASES))
@pytest.mark.parametrize("solver", ["z3", "cvc5"])
def test_backend_matches_expected(case, solver):
    spec, events, prop, expected = CASES[case]
    assert _violations(spec, events, prop, solver) == expected


@pytest.mark.parametrize("case", sorted(CASES))
def test_backends_agree(case):
    spec, events, prop, _ = CASES[case]
    z = _violations(spec, events, prop, "z3")
    c = _violations(spec, events, prop, "cvc5")
    assert z == c
