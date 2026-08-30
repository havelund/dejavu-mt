"""Tests for violation witnesses: when a Forall-led property comes out
False, the falsifying assignment of the leading quantifier prefix is
extracted from a solver model and recorded in FormulaMonitor.witnesses.
"""
from dejavumt import parse_spec, Monitor


def run(spec_text, events, timed=False, solver="z3"):
    m = Monitor(parse_spec(spec_text), solver=solver)
    for e in events:
        ev, ts = e if timed else (e, None)
        m.step(ev, ts)
    m.end()
    return m


def test_basic_witness():
    m = run("""
    pred open(f: String)
    pred write(f: String, d: String)
    prop q : Forall f . Forall d . write(f,d) -> P open(f)
    """, [{"open": [("a",)]}, {"write": [("a", "x")]},
          {"write": [("b", "boom")]}])
    assert m.formulas[0].witnesses == {3: {"f": "b", "d": "boom"}}


def test_int_witness():
    m = run("pred p(n: Int)\nprop q : Forall n . p(n) -> n < 10",
            [{"p": [(3,)]}, {"p": [(42,)]}])
    assert m.formulas[0].witnesses == {2: {"n": 42}}


def test_enum_witness():
    m = run("""
    enum Mode = OFF | STANDBY | ACTIVE
    pred fire(m: Mode)
    prop safe : Forall m . fire(m) -> m = ACTIVE
    """, [{"fire": [("STANDBY",)]}])
    assert m.formulas[0].witnesses == {1: {"m": "STANDBY"}}


def test_delayed_witness():
    """A future-operator violation, decided when the deadline passes: the
    witness comes from the obligation's frozen values."""
    m = run("""
    pred req(x: String)
    pred ack(x: String)
    prop q : Forall x . req(x) -> F[<=5] ack(x)
    """, [({"req": [("a",)]}, 0), ({"req": [("b",)]}, 1),
          ({"ack": [("a",)]}, 3), ({"noise": [()]}, 10)], timed=True)
    assert m.formulas[0].witnesses == {2: {"x": "b"}}


def test_end_of_trace_witness():
    m = run("""
    pred req(x: String)
    pred ack(x: String)
    prop q : Forall x . req(x) -> F ack(x)
    """, [{"req": [("c",)]}])
    assert m.formulas[0].witnesses == {1: {"x": "c"}}


def test_rule_witness():
    m = run("""
    pred p(x: Int)
    pred c(x: Int)
    prop f : Forall x . c(x) -> o(x)  where  o(x) := p(x)
    """, [{"p": [(4,)]}, {"c": [(7,)], "p": [(5,)]}])
    assert m.formulas[0].witnesses == {2: {"x": 7}}


def test_no_forall_no_witness():
    """A propositional violation records no witness (nothing to bind)."""
    m = run("pred p()\npred q()\nprop r : q -> p", [{"q": [()]}])
    assert m.formulas[0].witnesses == {}


def test_witness_cvc5():
    m = run("pred p(n: Int)\nprop q : Forall n . p(n) -> n < 10",
            [{"p": [(42,)]}], solver="cvc5")
    assert m.formulas[0].witnesses == {1: {"n": 42}}
