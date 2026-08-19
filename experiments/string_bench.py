"""
How expensive is the `contains` string operator, and how do the backends
compare on it?

Three properties over the same synthetic MODE_CHANGED logs:

  equality   Forall c,d . !(MODE_CHANGED(c,d) & d = "...AUTOMATIC...")
             -- the string-free baseline: same shape, equality only
  contains   Forall c,d . !(MODE_CHANGED(c,d) & d contains "AUTOMATIC")
             -- the new operator (quantified, so QE must handle Contains)
  temporal   Forall c . Forall d .
                MODE_CHANGED(c,d) & d contains "AUTO" -> P[<=5] armed(c)
             -- contains feeding a timed operator, i.e. stored state

Each is run on both backends over log prefixes of increasing length;
wall-clock per run and verdict agreement are reported.

    .venv/bin/python experiments/string_bench.py [maxlen]
"""
from __future__ import annotations

import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from dejavumt import parse_spec, Monitor  # noqa: E402

EQ_SPEC = """
pred MODE_CHANGED(c: String, d: String)
prop p : Forall c . Forall d .
    !(MODE_CHANGED(c, d) & d = "Control mode changed to AUTOMATIC")
"""
CONTAINS_SPEC = """
pred MODE_CHANGED(c: String, d: String)
prop p : Forall c . Forall d . !(MODE_CHANGED(c, d) & d contains "AUTOMATIC")
"""
TEMPORAL_SPEC = """
pred MODE_CHANGED(c: String, d: String)
pred armed(c: String)
prop p : Forall c . Forall d .
    MODE_CHANGED(c, d) & d contains "AUTO" -> P[<=5] armed(c)
"""

CAPTURE_SPEC = """
pred LOGIN(m: String)
pred armed(u: String)
prop p : Forall m . Forall u .
    LOGIN(m) & m matches "user {u}" -> P[<=5] armed(u)
"""

MODES = ["MANUAL", "SAFE", "AUTOMATIC", "IDLE", "AUTONAV"]
USERS = ["klaus", "doron", "grigore", "eugen"]


def make_log(n, seed=0):
    rng = random.Random(seed)
    events, times = [], []
    t = 0
    for i in range(n):
        c = f"ctrl{rng.randint(0, 3)}"
        r = rng.random()
        if r < 0.3:
            events.append({"armed": [(rng.choice(USERS),)]})
        elif r < 0.45:
            events.append({"LOGIN": [(f"user {rng.choice(USERS)}",)]})
        else:
            d = f"Control mode changed to {rng.choice(MODES)}"
            events.append({"MODE_CHANGED": [(c, d)]})
        t += rng.randint(0, 2)
        times.append(t)
    return events, times


def run(spec_text, events, times, solver):
    m = Monitor(parse_spec(spec_text), solver=solver)
    t0 = time.perf_counter()
    viol = []
    for i, (ev, ts) in enumerate(zip(events, times), 1):
        r = m.step(ev, ts if m.timed else None)
        if r["p"] is False:
            viol.append(i)
    return time.perf_counter() - t0, viol


def main():
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    lengths = [n for n in (50, 100, 200, 400, 800, 1600) if n <= maxlen]
    events, times = make_log(max(lengths))
    print(f"{'property':<10} {'n':>5} {'z3 (s)':>9} {'cvc5 (s)':>9} "
          f"{'ratio':>6}  verdicts")
    for name, spec in (("equality", EQ_SPEC), ("contains", CONTAINS_SPEC),
                       ("temporal", TEMPORAL_SPEC),
                       ("capture", CAPTURE_SPEC)):
        for n in lengths:
            ev, tm = events[:n], times[:n]
            tz, vz = run(spec, ev, tm, "z3")
            try:
                tc, vc = run(spec, ev, tm, "cvc5")
            except Exception as e:
                tc, vc = float("nan"), None
                print(f"  cvc5 failed: {e}")
            agree = "==" if vc == vz else f"DIFFER z3={vz[:4]} cvc5={(vc or [])[:4]}"
            ratio = tc / tz if tz and tc == tc else float("nan")
            print(f"{name:<10} {n:>5} {tz:>9.2f} {tc:>9.2f} {ratio:>6.2f}  "
                  f"{len(vz)} violation(s) {agree}")
        print()


if __name__ == "__main__":
    main()
