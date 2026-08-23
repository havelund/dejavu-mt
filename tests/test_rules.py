"""Tests for recursive rules (`prop .. where r(x) := body`) and state
variables (`state x: Sort := {init} on p(..): {expr}`).

Rules follow DejaVu: a rule's extension is recomputed at every position
(like an event's), and rule calls inside rule bodies must sit below @ --
recursion is a pure recurrence over the previous position.  State
variables are the functional fragment: a ground Python value updated per
matching event, read in formulas as a term.
"""
import pytest

from dejavumt import parse_spec, Monitor


def replay(spec_text, events, prop, timed=False, solver="z3"):
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
    return m, [got.get(i + 1) for i in range(len(events))]


# --- rules -------------------------------------------------------------------

def test_rule_extension_is_per_position():
    """o(x) := p(x): computing o(4) at one step and o(5) at the next means
    o(4) is forgotten at the next step (unless a past operator kept it)."""
    spec = """
    pred p(x: Int)
    pred c(x: Int)
    prop f : Forall x . c(x) -> o(x)  where  o(x) := p(x)
    """
    m, got = replay(spec, [{"p": [(4,)]},
                           {"p": [(5,)], "c": [(4,)]},   # o = {5}: violated
                           {"c": [(5,)]}],               # o = {}: violated
                    prop="f")
    assert got == [True, False, False]


def test_rule_under_past_operator_remembers():
    """The same rule under P: the past operator's own state remembers."""
    spec = """
    pred p(x: Int)
    pred c(x: Int)
    prop f : Forall x . c(x) -> P o(x)  where  o(x) := p(x)
    """
    m, got = replay(spec, [{"p": [(4,)]},
                           {"p": [(5,)], "c": [(4,)]}], prop="f")
    assert got == [True, True]


def test_recursive_rule_seen():
    """seen(x) := p(x) | @ seen(x): latches per value."""
    spec = """
    pred p(x: String)
    pred check(x: String)
    prop r : Forall x . check(x) -> seen(x)
      where seen(x) := p(x) | (@ seen(x))
    """
    m, got = replay(spec, [{"p": [("a",)]}, {"check": [("a",)]},
                           {"check": [("b",)]}], prop="r")
    assert got == [True, True, False]


def test_counting_rule():
    """x := x + 1 as a pure rule: the extension is a moving singleton."""
    spec = """
    pred tick()
    pred check(n: Int)
    prop c : Forall n . check(n) -> count(n)
      where count(n) := ((! @ true) & n = 1)
                      | (Exists m . (@ count(m)) & n = m + 1)
    """
    m, got = replay(spec, [{"tick": [()]}, {"check": [(2,)]},
                           {"check": [(2,)]}, {"check": [(4,)]}], prop="c")
    assert got == [True, True, False, True]


def test_mutual_recursion():
    """Alternation: a-turn and b-turn flip each step."""
    spec = """
    pred a()
    pred b()
    prop alt : (aturn -> a) & (bturn -> b)
      where aturn := (! @ true) | (@ bturn),
            bturn := (@ aturn)
    """
    m, got = replay(spec, [{"a": [()]}, {"b": [()]}, {"a": [()]},
                           {"a": [()]}], prop="alt")
    assert got == [True, True, True, False]   # position 4 should be b's turn


def test_rule_with_timed_body():
    """Rule bodies may use metric past operators."""
    spec = """
    pred req(x: String)
    pred chk(x: String)
    prop t : Forall x . chk(x) -> recent(x)
      where recent(x) := P[<=5] req(x)
    """
    m, got = replay(spec, [({"req": [("a",)]}, 0), ({"chk": [("a",)]}, 3),
                           ({"chk": [("a",)]}, 9)], prop="t", timed=True)
    assert got == [True, True, False]


def test_rule_call_renaming():
    """Calling r(y) where the rule is r(x): parameters rename."""
    spec = """
    pred p(x: String)
    pred q(y: String)
    prop r : Forall y . q(y) -> (@ latch(y))
      where latch(x) := p(x) | (@ latch(x))
    """
    m, got = replay(spec, [{"p": [("a",)]}, {"q": [("a",)]},
                           {"q": [("b",)]}], prop="r")
    assert got == [True, True, False]


def test_reject_unguarded_recursion():
    with pytest.raises(ValueError, match="below the @"):
        Monitor(parse_spec("pred p(x: String)\npred c(x: String)\n"
                           "prop r : Forall x . c(x) -> q(x) "
                           "where q(x) := p(x) | q(x)"))


def test_reject_future_in_rule_body():
    with pytest.raises(ValueError, match="future operators"):
        Monitor(parse_spec("pred p(x: String)\npred c(x: String)\n"
                           "prop r : Forall x . c(x) -> q(x) "
                           "where q(x) := F p(x)"))


def test_reject_constant_rule_arg():
    # constants as call arguments are rejected (as in DejaVu)
    with pytest.raises(ValueError, match="must be variables"):
        Monitor(parse_spec(
            "pred p(x: String)\npred c(x: String)\n"
            "prop r : Forall x . c(x) -> q(\"a\") where q(x) := p(x)"))


def test_reject_params_not_free():
    with pytest.raises(ValueError, match="exactly the parameters"):
        Monitor(parse_spec("pred p(x: String)\npred c(y: String)\n"
                           "prop r : Forall y . c(y) -> q(y) "
                           "where q(x) := Exists x . p(x)"))


def test_rules_cvc5():
    spec = """
    pred p(x: String)
    pred check(x: String)
    prop r : Forall x . check(x) -> seen(x)
      where seen(x) := p(x) | (@ seen(x))
    """
    m, got = replay(spec, [{"p": [("a",)]}, {"check": [("a",)]},
                           {"check": [("b",)]}], prop="r", solver="cvc5")
    assert got == [True, True, False]


# --- state variables ---------------------------------------------------------

def test_state_total_bytes():
    """TP-DejaVu Example 2, in-spec: running total of written bytes."""
    spec = """
    state total: Int := {0}
        on write(f, d): {total + len(d)}
    pred write(f: String, d: String)
    prop bound : total <= 10
    """
    m, got = replay(spec, [{"write": [("a", "abcd")]},
                           {"write": [("a", "abcdefgh")]},
                           {"noise": [()]}], prop="bound")
    assert got == [True, False, False]
    assert m.states["total"] == 12


def test_state_uses_python_helpers():
    spec = """
    python:
        def cost(item: str) -> int:
            return {"apple": 3, "pear": 5}.get(item, 0)
    end
    state spent: Int := {0}
        on buy(item): {spent + cost(item)}
    pred buy(item: String)
    prop b : spent <= 7
    """
    m, got = replay(spec, [{"buy": [("apple",)]}, {"buy": [("pear",)]},
                           {"buy": [("apple",)]}], prop="b")
    assert got == [True, False, False]


def test_state_dict_valued_helper():
    """Non-scalar state lives in Python (dict), scalar projections are
    what formulas read -- PyDejaVu Example 3's available_space, in-spec."""
    spec = """
    python:
        space = {}
        def alloc(f: str, s: int) -> int:
            space[f] = s
            return 0
        def use(f: str, n: int) -> int:
            space[f] = space.get(f, 0) - n
            return space[f]
    end
    state low: Int := {0}
        on open(f, s): {alloc(f, s)}
        on write(f, d): {use(f, len(d))}
    pred open(f: String, s: Int)
    pred write(f: String, d: String)
    prop ok : low >= 0
    """
    m, got = replay(spec, [{"open": [("a", 5)]},
                           {"write": [("a", "abc")]},      # 2 left
                           {"write": [("a", "abc")]}],     # -1: violation
                    prop="ok")
    assert got == [True, True, False]


def test_state_bool_atom():
    spec = """
    state armed: Bool := {False}
        on arm(): {True}
        on disarm(): {False}
    pred arm()
    pred disarm()
    pred fire()
    prop safe : fire -> armed
    """
    m, got = replay(spec, [{"fire": [()]}, {"arm": [()]},
                           {"fire": [()]}, {"disarm": [()]},
                           {"fire": [()]}], prop="safe")
    assert got == [False, True, True, True, False]


def test_state_under_temporal_operator():
    """P (total = 4): past operators remember the injected literals."""
    spec = """
    state total: Int := {0}
        on w(d): {total + len(d)}
    pred w(d: String)
    pred c()
    prop p : c -> P (total = 4)
    """
    m, got = replay(spec, [{"w": [("abcd",)]}, {"w": [("xy",)]},
                           {"c": [()]}], prop="p")
    assert got == [True, True, True]


def test_state_collision_rejected():
    with pytest.raises(ValueError, match="collides"):
        Monitor(parse_spec("state w: Int := {0}\n"
                           "pred w(d: String)\nprop p : true"))
