"""Tests for enumeration sorts and bit-vectors.

Enums: declared finite sorts; constructor names are literals in formulas
and validated values in logs; quantifiers over them are finite (coverage
properties become expressible).  Bit-vectors: BV8/16/32/64 with named
operations (band/bor/bxor/bnot/shl/lshr), wraparound arithmetic, unsigned
comparisons, hex literals.
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


ENUM_SPEC = """
enum Mode = OFF | STANDBY | ACTIVE
pred set(m: Mode)
pred fire(m: Mode)
prop safe : Forall m . fire(m) -> m = ACTIVE
prop covered : eof -> Forall m . P set(m)
"""


def test_enum_safe():
    got = replay(ENUM_SPEC, [{"set": [("ACTIVE",)]},
                             {"fire": [("ACTIVE",)]},
                             {"fire": [("STANDBY",)]}], prop="safe")
    assert got == [True, True, False]


def test_enum_coverage():
    """Forall over the whole sort: true only once every mode was set --
    inexpressible over an infinite sort (trivially false there)."""
    events = [{"set": [("OFF",)]}, {"set": [("STANDBY",)]},
              {"eof": [()]},                        # ACTIVE missing
              {"set": [("ACTIVE",)]}, {"eof": [()]}]
    got = replay(ENUM_SPEC, events, prop="covered")
    assert got == [True, True, False, True, True]


def test_enum_exhaustiveness():
    """The solver knows the sort has exactly three values."""
    spec = ENUM_SPEC + "prop exh : Forall m . m = OFF | m = STANDBY | m = ACTIVE\n"
    got = replay(spec, [{"set": [("OFF",)]}], prop="exh")
    assert got == [True]


def test_enum_typo_rejected():
    m = Monitor(parse_spec(ENUM_SPEC))
    with pytest.raises(ValueError, match="not a Mode"):
        m.step({"set": [("ACTVE",)]})


def test_enum_unknown_sort_rejected():
    with pytest.raises(ValueError, match="unknown sort"):
        Monitor(parse_spec("pred set(m: Mood)\nprop p : true"))


def test_enum_shadowing_rejected():
    with pytest.raises(ValueError, match="shadows an enum constructor"):
        Monitor(parse_spec("enum Power = LO | HI\npred p(m: Power)\n"
                           "prop q : Forall LO . p(LO)"))


def test_enum_cvc5():
    got = replay(ENUM_SPEC, [{"set": [("ACTIVE",)]},
                             {"fire": [("STANDBY",)]}], prop="safe",
                 solver="cvc5")
    assert got == [True, False]


BV_SPEC = """
pred stat(w: BV16)
prop err : Forall w . stat(w) -> band(w, 0x40) = 0
"""


def test_bv_mask():
    got = replay(BV_SPEC, [{"stat": [("0x2A",)]},     # bit clear
                           {"stat": [("0x6A",)]},     # bit set
                           {"stat": [("42",)]}],      # decimal ok, bit clear
                 prop="err")
    assert got == [True, False, True]


def test_bv_wraparound():
    """+ on bit-vectors is modular: 0xFFFF + 1 = 0 in BV16."""
    spec = """
    pred seq(x: BV16)
    prop nowrap : Forall x . seq(x) -> ! (x + 1 = 0)
    """
    got = replay(spec, [{"seq": [("7",)]}, {"seq": [("0xFFFF",)]}],
                 prop="nowrap")
    assert got == [True, False]


def test_bv_unsigned_comparison():
    """0x8000 > 0x7FFF unsigned (signed would say the opposite)."""
    spec = """
    pred v(x: BV16)
    prop big : Forall x . v(x) -> x > 0x7FFF
    """
    got = replay(spec, [{"v": [("0x8000",)]}, {"v": [("0x7FFF",)]}],
                 prop="big")
    assert got == [True, False]


def test_bv_shift():
    spec = """
    pred p(x: BV8)
    prop s : Forall x . p(x) -> shl(x, 4) = 0x10
    """
    got = replay(spec, [{"p": [("1",)]}, {"p": [("2",)]}], prop="s")
    assert got == [True, False]


def test_bv_cross_event_comparison():
    """Successor frames increment the counter modulo 2^16."""
    spec = """
    pred frame(c: BV16)
    prop inc : Forall c . Forall c0 .
        (frame(c) & @ frame(c0)) -> c = c0 + 1
    """
    got = replay(spec, [{"frame": [("0xFFFE",)]}, {"frame": [("0xFFFF",)]},
                        {"frame": [("0",)]},      # wraparound: ok
                        {"frame": [("5",)]}],     # skip: violation
                 prop="inc")
    assert got == [True, True, True, False]


def test_bv_cvc5():
    got = replay(BV_SPEC, [{"stat": [("0x2A",)]}, {"stat": [("0x6A",)]}],
                 prop="err", solver="cvc5")
    assert got == [True, False]
