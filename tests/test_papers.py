"""The examples of the TP-DejaVu (VMCAI 2024) and PyDejaVu (2025) papers,
done in DejaVuMT -- declaratively where the two-phase tools needed an
operational phase, since the formula representation already carries
arithmetic and cross-time comparisons.

Not covered (genuine aggregation -- running sums/counts over the trace,
e.g. TP-DejaVu Example 2's total bytes, PyDejaVu Example 3's per-file
available space): counting is not first-order definable; see
doc/pyfun.md's triangle and OPTIMIZATION.md.
"""
from dejavumt import parse_spec, Monitor


def replay(spec_text, events, prop):
    m = Monitor(parse_spec(spec_text))
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


def test_write_property_dejavu_example1():
    """Both papers' Example 1: data written to a file requires the file
    open in write mode and not closed since, in a folder created and not
    deleted since.  Pure past QTL with multi-argument predicates."""
    spec = """
    pred open(F: String, f: String, m: String, s: Int)
    pred close(f: String)
    pred write(f: String, d: String)
    pred create(F: String)
    pred delete(F: String)
    prop ex1 : Forall f . Forall d . write(f,d) ->
        (Exists F . Exists s .
            (((! close(f)) S open(F, f, "w", s)) &
             ((! delete(F)) S create(F))))
    """
    events = [{"create": [("tmp",)]},
              {"open": [("tmp", "f1", "w", 10)]},
              {"write": [("f1", "text")]},          # ok
              {"write": [("f2", "text")]},          # never opened
              {"close": [("f1",)]},
              {"write": [("f1", "more")]}]          # closed since
    assert replay(spec, events, "ex1") == \
        [True, True, True, False, True, False]


def test_average_of_two_past_values():
    """TP-DejaVu's introduction lists this as the case its two-phase
    method CANNOT handle (it needs comparisons against unboundedly many
    stored past values): every p(x) must be the average of two distinct
    previously seen q-values.  The formula state stores all past q-values
    symbolically and quantifier elimination solves the arithmetic."""
    spec = """
    pred p(x: Int)
    pred q(y: Int)
    prop avg : Forall x . p(x) ->
        (Exists y . Exists z .
            (P q(y)) & (P q(z)) & !(y = z) & 2 * x = y + z)
    """
    events = [{"q": [(4,)]}, {"q": [(8,)]},
              {"p": [(6,)]},         # 6 = (4+8)/2
              {"p": [(7,)]},         # no distinct pair sums to 14
              {"q": [(10,)]},
              {"p": [(7,)]}]         # 7 = (4+10)/2
    assert replay(spec, events, "avg") == \
        [True, True, True, False, True, True]


def test_speed_record_declaratively():
    """TP-DejaVu Example 1 tracks a running maximum in its operational
    phase (MaxSpeed := ite(...)).  Declaratively, 'this speed beats every
    previous one' is a quantified order comparison across time -- no
    state, no ite."""
    spec = """
    pred recorded(v: String, s: Int)
    prop rec : Forall v . Forall s . recorded(v,s) ->
        (! (@ P (Exists v2 . Exists s2 . recorded(v2,s2) & s2 >= s)))
    """
    events = [{"recorded": [("audi", 10)]},   # first: record
              {"recorded": [("bmw", 5)]},     # not a record
              {"recorded": [("kia", 12)]}]    # record
    assert replay(spec, events, "rec") == [True, False, True]


def test_temperature_delta():
    """TP-DejaVu Example 2 computes temp - PREVIOUS temp operationally.
    Declaratively: quantify the previous event's reading via @ and
    compare."""
    spec = """
    pred startMeasure(c: String, t: Int)
    pred endMeasure(c: String, t: Int)
    prop warm : Forall c . Forall t2 . endMeasure(c,t2) ->
        (Exists t1 . (@ startMeasure(c,t1)) & t2 - t1 <= 5)
    """
    good = [{"startMeasure": [("car", 20)]}, {"endMeasure": [("car", 24)]}]
    bad = [{"startMeasure": [("car", 20)]}, {"endMeasure": [("car", 28)]}]
    assert replay(spec, good, "warm") == [True, True]
    assert replay(spec, bad, "warm") == [True, False]


def test_tpdejavu_experimental_properties():
    """TP-DejaVu Fig. 7, properties 1 and 2, directly (their Fig. 8
    encodings needed an operational phase for the comparisons)."""
    spec1 = """
    pred p(x: Int)
    pred q(x: Int, y: Int)
    prop e1 : Forall x . p(x) -> (Exists y . (P q(x,y)) & y > 10)
    """
    events = [{"q": [(1, 15)]}, {"p": [(1,)]}, {"p": [(2,)]}]
    assert replay(spec1, events, "e1") == [True, True, False]

    spec2 = """
    pred p(x: Int)
    pred q(y: Int)
    pred r(x: Int, y: Int)
    prop e2 : Forall x . Forall y .
        ((p(x) & (@ q(y)) & x < y) -> P r(x,y))
    """
    events = [{"r": [(1, 5)]}, {"q": [(5,)]}, {"p": [(1,)]},   # ok
              {"q": [(9,)]}, {"p": [(2,)]}]                    # no r(2,9)
    assert replay(spec2, events, "e2") == \
        [True, True, True, True, False]


def test_air_conditioner_bounds():
    """TP-DejaVu Example 3: out-of-bounds set commands are ignored; an
    in-bounds one requires the AC on (and not off since).  The bound
    check is a plain conjunction of comparisons -- no phase needed."""
    spec = """
    pred set(ac: String, temp: Int)
    pred turn_on(ac: String)
    pred turn_off(ac: String)
    prop ac : Forall a . Forall t .
        ((set(a,t) & t >= 17 & t <= 26) ->
            ((! turn_off(a)) S turn_on(a)))
    """
    events = [{"turn_on": [("ac1",)]},
              {"set": [("ac1", 20)]},          # ok
              {"set": [("ac1", 40)]},          # faulty command: ignored
              {"turn_off": [("ac1",)]},
              {"set": [("ac1", 20)]}]          # off: violation
    assert replay(spec, events, "ac") == [True, True, True, True, False]
