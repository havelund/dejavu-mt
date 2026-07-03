"""
Benchmark: periodic garbage collection on a churn workload.

The property `Forall r . use(r) -> (!revoke(r)) S grant(r)` accumulates a dead
value-term in the `since` formula for every resource that is granted and later
revoked while another resource stays live.  Without GC the formula grows
linearly with the number of churned resources; with periodic GC (the backend's
contextual simplifier applied every `gc_period` events) it stays bounded.

Run:  .venv/bin/python experiments/gc_bench.py
"""
import time

from dejavumt.parser import parse_spec
from dejavumt.engine import Monitor

SPEC = """
pred grant(r: String)
pred revoke(r: String)
pred use(r: String)
prop access : Forall r . use(r) -> (!revoke(r)) S grant(r)
"""


def churn_events(pairs):
    evs = [{"grant": [("perm",)]}]           # one long-lived resource
    for i in range(pairs):
        evs.append({"grant": [(f"t{i}",)]})
        evs.append({"revoke": [(f"t{i}",)]})
    evs.append({"use": [("perm",)]})
    return evs


def formula_size(e):
    # iterative DAG node count (formulas can be very deeply nested)
    seen = set()
    stack = [e]
    n = 0
    while stack:
        x = stack.pop()
        if x.get_id() in seen:
            continue
        seen.add(x.get_id())
        n += 1
        stack.extend(x.children())
    return n


def run(pairs, gc_period):
    events = churn_events(pairs)
    m = Monitor(parse_spec(SPEC))          # z3 backend
    for fm in m.formulas:
        fm.gc_period = gc_period
    t = time.time()
    verdicts = [all(m.step(ev).values()) for ev in events]
    dt = time.time() - t
    fm = m.formulas[0]
    since = [i for i, n in enumerate(fm.nodes) if n.kind == "since"][0]
    return dt, formula_size(fm.pre[since]), verdicts


print(f"{'pairs':>6} {'events':>7} | {'no GC size':>10} {'no GC s':>8} |"
      f" {'GC size':>8} {'GC s':>7} | verdicts match")
for pairs in (100, 300, 600):
    events = 2 * pairs + 2
    t0, s0, v0 = run(pairs, 0)
    t1, s1, v1 = run(pairs, 50)
    print(f"{pairs:>6} {events:>7} | {s0:>10} {t0:>8.2f} |"
          f" {s1:>8} {t1:>7.2f} | {v0 == v1}")
