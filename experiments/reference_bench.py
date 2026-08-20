"""Performance: the incremental SMT monitor vs the definitional semantic
evaluator used as the fuzzing oracle (experiments/fuzz_reference.py).

The reference evaluator IS the semantics: at each position it evaluates the
defining quantifier chains over the whole trace (reading the future
directly), memoized per (subformula, position) but with no incremental
state.  That makes it the trustworthy oracle for correctness -- and an
offline, propositional, per-position-cost-grows-with-the-trace procedure:
Once/F are O(n^2) over the trace, the interval operator O(n^3).  The
monitor carries state forward and does bounded work per event (for a
saturating property).  This script measures the crossover.

Properties are propositional (the oracle's fragment).  Violations are
injected via occasional time jumps (timed windows) or pattern breaks;
verdict streams are compared position by position (end-of-trace convention
matches on both sides, as the fuzzer established on ~5k random pairs).

    python experiments/reference_bench.py [--sizes 1000,4000,16000]
                                          [--timeout 120]
"""
from __future__ import annotations

import argparse
import multiprocessing as mp
import time
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from dejavumt.parser import parse_spec
from dejavumt.engine import Monitor
from fuzz_reference import reference


SPECS = {
    "prop-past": ("pred open()\npred close()\n"
                  "prop q : close -> P open"),
    "timed-past": ("pred req()\npred rsp()\n"
                   "prop q : rsp -> P[<=10] req"),
    "future": ("pred req()\npred ack()\n"
               "prop q : req -> F[<=10] ack"),
    "interval": ("pred grant()\npred reset()\npred use()\n"
                 "prop q : use -> [grant, reset)"),
}


def make_trace(kind, n):
    """Propositional trace of n events; a violation every ~50 events."""
    events, times = [], []
    t = 0
    for i in range(n):
        t += 1
        if kind == "prop-past":
            # close before the first open is the only way to violate.
            if i < 2:
                ev = {"close": [()]}
            else:
                ev = {"open": [()]} if i % 2 == 0 else {"close": [()]}
        elif kind == "timed-past":
            if i % 50 == 49:
                t += 20                        # last req now out of window
                ev = {"rsp": [()]}
            else:
                ev = {"req": [()]} if i % 2 == 0 else {"rsp": [()]}
        elif kind == "future":
            if i % 50 == 49:
                t += 20                        # previous req went unanswered
                ev = {"req": [()]}
            else:
                ev = {"req": [()]} if i % 2 == 0 else {"ack": [()]}
        else:  # interval
            r = i % 10
            if r == 0:
                ev = {"grant": [()]}
            elif r == 8:
                ev = {"reset": [()]}
            else:
                ev = {"use": [()]}             # r == 9: after reset, violation
        events.append(ev)
        times.append(t)
    return events, times


def run_monitor(spec_text, events, times):
    m = Monitor(parse_spec(spec_text), solver="z3")
    t0 = time.perf_counter()
    got = {}
    for pos0, (ev, ts) in enumerate(zip(events, times)):
        m.step(ev, ts)
        for pos, _, holds in m.resolved:
            got[pos] = holds
    for pos, _, holds in m.end():
        got[pos] = holds
    dt = time.perf_counter() - t0
    return dt, [got.get(i + 1) for i in range(len(events))]


def _ref_child(spec_text, events, times, q):
    body = parse_spec(spec_text).properties[0].body
    t0 = time.perf_counter()
    verdicts = reference(body, events, times)
    q.put((time.perf_counter() - t0, verdicts))


def run_reference(spec_text, events, times, timeout):
    """(seconds, verdicts) or (None, None) on timeout, via a child process."""
    q = mp.Queue()
    p = mp.Process(target=_ref_child, args=(spec_text, events, times, q))
    p.start()
    p.join(timeout)
    if p.is_alive():
        p.terminate()
        p.join()
        return None, None
    return q.get()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sizes", default="1000,4000,16000")
    ap.add_argument("--timeout", type=float, default=120.0)
    args = ap.parse_args()
    sizes = [int(s) for s in args.sizes.split(",")]

    print(f"{'property':<12} {'events':>7} {'reference':>10} {'us/ev':>8} "
          f"{'DejaVuMT':>10} {'us/ev':>7}  verdicts")
    for kind, spec_text in SPECS.items():
        for n in sizes:
            events, times = make_trace(kind, n)
            dt_mt, v_mt = run_monitor(spec_text, events, times)
            dt_rf, v_rf = run_reference(spec_text, events, times, args.timeout)
            if dt_rf is None:
                rf = f"{'>' + str(int(args.timeout)) + 's':>10} {'-':>8}"
                agree = "-"
            else:
                rf = f"{dt_rf:>9.2f}s {dt_rf/n*1e6:>7.0f}"
                agree = ("agree" if v_rf == v_mt else
                         f"MISMATCH at {next(i for i in range(n) if v_rf[i] != v_mt[i]) + 1}")
            nviol = sum(1 for v in v_mt if v is False)
            print(f"{kind:<12} {n:>7} {rf} {dt_mt:>9.2f}s "
                  f"{dt_mt/n*1e6:>6.0f}  {agree} ({nviol})", flush=True)


if __name__ == "__main__":
    main()
