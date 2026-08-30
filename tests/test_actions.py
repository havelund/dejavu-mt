"""Tests for Python actions: `do {expr}` on rules (fired when the
extension is non-empty and changed, parameters bound to a satisfying
assignment) and `on violation {expr}` on properties (fired per emitted
violation, with pos and witness values bound).  Actions run in the
python block's namespace.
"""
import pytest

from dejavumt import parse_spec, Monitor


def run(spec_text, events, timed=False):
    m = Monitor(parse_spec(spec_text))
    for e in events:
        ev, ts = e if timed else (e, None)
        m.step(ev, ts)
    m.end()
    return m


def test_counter_rule_action():
    """The count rule's extension is a moving singleton; the action sees
    the exact value each position."""
    m = run("""
    python:
        counts = []
    end
    pred tick()
    prop c : true
      where count(n) := ((! @ true) & n = 1)
                      | (Exists m . (@ count(m)) & n = m + 1)
                      do {counts.append(n)}
    """, [{"tick": [()]}, {"tick": [()]}, {"tick": [()]}])
    assert m._pyns["counts"] == [1, 2, 3]


def test_latch_rule_action_fires_on_change_only():
    m = run("""
    python:
        fires = []
    end
    pred p(x: String)
    prop r : true
      where seen(x) := p(x) | (@ seen(x)) do {fires.append(pos)}
    """, [{"p": [("a",)]}, {"p": [("a",)]},   # unchanged: no fire
          {"p": [("b",)]}, {"q": [()]}])      # grows; then unchanged
    assert m._pyns["fires"] == [1, 3]


def test_violation_action_with_witness():
    m = run("""
    python:
        incidents = []
    end
    pred open(f: String)
    pred write(f: String, d: String)
    prop q : Forall f . Forall d . write(f,d) -> P open(f)
        on violation {incidents.append((pos, f))}
    """, [{"open": [("a",)]}, {"write": [("a", "x")]},
          {"write": [("b", "boom")]}, {"write": [("c", "bad")]}])
    assert m._pyns["incidents"] == [(3, "b"), (4, "c")]


def test_delayed_violation_action():
    """Fired at emission (deadline / end of trace), not at the violating
    position."""
    m = run("""
    python:
        late = []
    end
    pred req(x: String)
    pred ack(x: String)
    prop q : Forall x . req(x) -> F[<=5] ack(x)
        on violation {late.append((pos, x))}
    """, [({"req": [("a",)]}, 0), ({"req": [("b",)]}, 1),
          ({"ack": [("a",)]}, 2), ({"noise": [()]}, 10)], timed=True)
    assert m._pyns["late"] == [(2, "b")]


def test_action_with_where_clause_order():
    """`on violation` and `where` combine on one property."""
    m = run("""
    python:
        bad = []
    end
    pred p(x: Int)
    pred c(x: Int)
    prop f : Forall x . c(x) -> o(x)
        on violation {bad.append(x)}
        where o(x) := p(x)
    """, [{"p": [(4,)]}, {"c": [(7,)]}])
    assert m._pyns["bad"] == [7]


def test_satisfaction_action_with_exists_witness():
    """on satisfaction: fired per True verdict; for an Exists-led property
    the satisfying values are bound."""
    m = run("""
    python:
        found = []
    end
    pred p(x: String)
    pred check()
    prop any : check -> (Exists y . P p(y))
    prop got : Exists y . p(y) on satisfaction {found.append((pos, y))}
    """, [{"p": [("a",)]}, {"q": [()]}, {"p": [("b",)]}])
    assert m._pyns["found"] == [(1, "a"), (3, "b")]


def test_satisfaction_action_delayed():
    """Delayed True verdict (future op): fired at emission, satisfying
    Exists witness bound."""
    m = run("""
    python:
        acked = []
    end
    pred req(x: String)
    pred ack(x: String)
    prop q : Exists x . req(x) & F ack(x)
        on satisfaction {acked.append((pos, x))}
    """, [{"req": [("a",)]}, {"ack": [("a",)]}])
    assert m._pyns["acked"] == [(1, "a")]


def test_both_actions_on_one_property():
    m = run("""
    python:
        log = []
    end
    pred p(n: Int)
    prop q : Forall n . p(n) -> n < 10
        on violation {log.append(("bad", pos))}
        on satisfaction {log.append(("ok", pos))}
    """, [{"p": [(3,)]}, {"p": [(42,)]}, {"p": [(5,)]}])
    assert m._pyns["log"] == [("ok", 1), ("bad", 2), ("ok", 3)]


def test_action_error_reported():
    with pytest.raises(ValueError, match="on-violation action failed"):
        run("""
        pred p()
        prop q : p on violation {1 / 0}
        """, [{"r": [()]}])
