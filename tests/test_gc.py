"""
Periodic garbage collection must be verdict-preserving and must bound the
representation on a churn workload.
"""
from dejavumt import parse_spec, Monitor

CHURN_SPEC = """
pred grant(r: String)
pred revoke(r: String)
pred use(r: String)
prop access : Forall r . use(r) -> (!revoke(r)) S grant(r)
"""


def _churn_events(pairs):
    evs = [{"grant": [("perm",)]}]
    for i in range(pairs):
        evs.append({"grant": [(f"t{i}",)]})
        evs.append({"revoke": [(f"t{i}",)]})
    evs.append({"use": [("perm",)]})   # perm is granted and never revoked -> holds
    evs.append({"use": [("t0",)]})     # t0 was revoked -> violation
    return evs


def _verdicts(events, gc_period):
    m = Monitor(parse_spec(CHURN_SPEC))
    for fm in m.formulas:
        fm.gc_period = gc_period
    return [all(m.step(ev).values()) for ev in events]


def _since_size(m):
    fm = m.formulas[0]
    since = [i for i, n in enumerate(fm.nodes) if n.kind == "since"][0]
    seen, stack, n = set(), [fm.pre[since]], 0
    while stack:
        x = stack.pop()
        if x.get_id() in seen:
            continue
        seen.add(x.get_id()); n += 1; stack.extend(x.children())
    return n


def test_gc_preserves_verdicts():
    events = _churn_events(100)
    assert _verdicts(events, 0) == _verdicts(events, 50)


def test_gc_bounds_representation():
    events = _churn_events(150)
    m0 = Monitor(parse_spec(CHURN_SPEC))
    m1 = Monitor(parse_spec(CHURN_SPEC))
    for fm in m1.formulas:
        fm.gc_period = 50
    for ev in events:
        m0.step(ev)
        m1.step(ev)
    # Without GC the since formula grows with the number of churned resources;
    # with GC it stays small.
    assert _since_size(m0) > 10 * _since_size(m1)
