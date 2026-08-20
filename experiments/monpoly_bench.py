"""Performance comparison DejaVuMT vs MonPoly on the shared fragment.

Both monitors run the same property on the same trace: DejaVuMT in-process
(Z3 backend, default settings, monitoring loop timed; construction excluded),
MonPoly as a subprocess in its usual violation mode (-negate; process time
includes its startup, a few ms).  Violation counts are compared as a sanity
check.  Expectation up front: MonPoly evaluates finite relations with an
OCaml relational engine and should win by orders of magnitude; DejaVuMT pays
per event for symbolic formula manipulation and solver calls.  The point of
the comparison is to quantify that price, not to contest it.

    python experiments/monpoly_bench.py [--sizes 1000,4000,16000] [--values 20]
"""
from __future__ import annotations

import argparse
import re
import subprocess
import tempfile
import time
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from dejavumt.parser import parse_spec
from dejavumt.engine import Monitor
import monpoly


# --- properties of the shared fragment ---------------------------------------

SPECS = {
    "prop-past": (
        "pred open(f: String)\npred close(f: String)\n"
        "prop q : Forall f . close(f) -> P open(f)",
        "q"),
    "timed-past": (
        "pred req(x: String)\npred rsp(x: String)\n"
        "prop q : Forall x . rsp(x) -> P[<=10] req(x)",
        "q"),
    "future": (
        "pred req(x: String)\npred ack(x: String)\n"
        "prop q : Forall x . req(x) -> F[<=10] ack(x)",
        "q"),
    "since": (
        "pred grant(x: String)\npred reset(x: String)\npred use(x: String)\n"
        "prop q : Forall x . use(x) -> [grant(x), reset(x))",
        "q"),
}


def make_trace(kind, n, values):
    """A trace of n events with `values` distinct data values cycling.
    Mostly satisfying, with a violation roughly every 50 events."""
    events, times = [], []
    t = 0
    for i in range(n):
        t += 1
        if kind in ("prop-past", "timed-past", "future"):
            a, b = {"prop-past": ("open", "close"),
                    "timed-past": ("req", "rsp"),
                    "future": ("req", "ack")}[kind]
            v = f"v{(i // 2) % values}"     # events pair up: a(v) then b(v)
            if i % 50 == 49:
                # A value that never gets its partner: for the past
                # properties an unmatched b, for the future one an
                # unanswered a -- one violation either way.
                bad = f"never{i}"
                ev = ({"req": [(bad,)]} if kind == "future"
                      else {b: [(bad,)]})
            elif i % 2 == 0:
                ev = {a: [(v,)]}
            else:
                ev = {b: [(v,)]}
        else:  # since: blocks of 10 on one value
            v = f"v{(i // 10) % values}"
            r = i % 10
            if r == 0:
                ev = {"grant": [(v,)]}
            elif r == 8:
                ev = {"reset": [(v,)]}
            elif r == 9:
                ev = {"use": [(v,)]}        # after reset: violation
            else:
                ev = {"use": [(v,)]}
        events.append(ev)
        times.append(t)
    return events, times


# --- runners ------------------------------------------------------------------

def run_dejavumt(spec_text, prop, events, times):
    """(seconds, #violated positions); monitoring loop only."""
    m = Monitor(parse_spec(spec_text), solver="z3")
    t0 = time.perf_counter()
    viol = 0
    for ev, ts in zip(events, times):
        m.step(ev, ts)
        viol += sum(1 for _, _, h in m.resolved if h is False)
    viol += sum(1 for _, _, h in m.end() if h is False)
    return time.perf_counter() - t0, viol


def run_monpoly(spec_text, prop, events, times):
    """(seconds, #violated time points) for one MonPoly -negate run, mirroring
    experiments/monpoly.violations: the translated property itself is passed
    (MonPoly negates it), and the appended maximal timestamp's time point is
    ignored."""
    spec = parse_spec(spec_text)
    body = next(p.body for p in spec.properties if p.name == prop)
    formula = monpoly.to_mfotl(body)
    sig = monpoly.signature(spec)
    log = monpoly.to_log(events, times)
    n = len(events)
    with tempfile.TemporaryDirectory() as d:
        sp, fp, lp = Path(d) / "s.sig", Path(d) / "f.mfotl", Path(d) / "t.log"
        sp.write_text(sig)
        fp.write_text(formula + "\n")
        lp.write_text(log)
        args = [str(monpoly.MONPOLY), "-sig", str(sp), "-formula", str(fp),
                "-log", str(lp), "-negate"]
        t0 = time.perf_counter()
        r = subprocess.run(args, capture_output=True, text=True, timeout=600)
        dt = time.perf_counter() - t0
    if "NOT monitorable" in r.stdout + r.stderr:
        raise RuntimeError(f"not monitorable: {formula}")
    viol = {int(m_.group(1)) for m_ in
            re.finditer(r"\(time point (\d+)\)", r.stdout)}
    return dt, len({tp for tp in viol if tp < n})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sizes", default="1000,4000,16000")
    ap.add_argument("--values", type=int, default=20)
    args = ap.parse_args()
    sizes = [int(s) for s in args.sizes.split(",")]

    print(f"{'property':<12} {'events':>7} {'DejaVuMT':>10} {'us/ev':>8} "
          f"{'MonPoly':>9} {'us/ev':>7} {'ratio':>7}  verdicts")
    for kind, (spec_text, prop) in SPECS.items():
        for n in sizes:
            events, times = make_trace(kind, n, args.values)
            dt_us, v_us = run_dejavumt(spec_text, prop, events, times)
            dt_mp, v_mp = run_monpoly(spec_text, prop, events, times)
            agree = "agree" if v_us == v_mp else f"US {v_us} != MP {v_mp}"
            print(f"{kind:<12} {n:>7} {dt_us:>9.2f}s {dt_us/n*1e6:>7.0f} "
                  f"{dt_mp:>8.3f}s {dt_mp/n*1e6:>6.1f} {dt_us/dt_mp:>6.0f}x"
                  f"  {agree} ({v_us})", flush=True)


if __name__ == "__main__":
    main()
