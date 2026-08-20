"""Performance comparison DejaVu vs DejaVuMT vs MonPoly on shared properties.

All monitors run the same property on the same trace:

- DejaVu (BDD): its generated monitor is compiled once per property (Verify +
  scalac, excluded from timing) and its self-reported "Elapsed analysis
  time" is used (JVM startup excluded).  Past-time only: the future property
  is skipped.
- DejaVuMT: in-process, Z3 backend, default settings; the monitoring loop is
  timed (construction excluded).
- MonPoly: a subprocess in its usual violation mode (-negate); process time
  includes its startup, a few ms.

Violation counts are compared across all tools as a sanity check.
Expectation up front: the specialised representations (BDDs, finite
relations) should win by orders of magnitude; DejaVuMT pays per event for
symbolic formula manipulation and solver calls.  The point of the comparison
is to quantify that price, not to contest it.

    python experiments/monpoly_bench.py [--sizes 1000,4000,16000] [--values 20]
                                        [--no-dejavu]
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


# --- DejaVu (BDD) -------------------------------------------------------------
# Untyped specs (original DejaVu rejects type annotations); no future property
# (past-time only).  The timed log filename must contain ".timed." -- that is
# how DejaVu decides the last column is a timestamp.

DEJAVU_SPECS = {
    "prop-past": "prop q : Forall f . close(f) -> P open(f)",
    "timed-past": "prop q : Forall x . rsp(x) -> P[<=10] req(x)",
    "future": None,
    "since": "prop q : Forall x . use(x) -> [grant(x), reset(x))",
}
DEJAVU_TIMED = {"prop-past": False, "timed-past": True, "future": False,
                "since": False}
DEJAVU_JAR = (Path.home()
              / "Desktop/development/dejavu/out/artifacts/dejavu_jar/dejavu.jar")
_JAVA_HOME = "/opt/homebrew/opt/openjdk@11/libexec/openjdk.jdk/Contents/Home"
_DJV_ENV = None


def _djv_env():
    global _DJV_ENV
    if _DJV_ENV is None:
        import os
        _DJV_ENV = dict(os.environ, JAVA_HOME=_JAVA_HOME,
                        PATH=f"{_JAVA_HOME}/bin:"
                             f"/opt/homebrew/opt/scala@2.12/bin:"
                             + os.environ.get("PATH", ""))
    return _DJV_ENV


def dejavu_available():
    return DEJAVU_JAR.exists() and Path(_JAVA_HOME).exists()


def dejavu_compile(spec_text, workdir: Path):
    """Verify + scalac: generate and compile the monitor once per property."""
    (workdir / "spec.qtl").write_text(spec_text + "\n")
    jar = str(DEJAVU_JAR)
    r = subprocess.run(["java", "-cp", jar, "dejavu.Verify", "spec.qtl"],
                       cwd=workdir, env=_djv_env(), capture_output=True,
                       text=True, timeout=120)
    if "error" in (r.stdout + r.stderr).lower():
        raise RuntimeError(f"dejavu.Verify: {(r.stdout + r.stderr)[:300]}")
    subprocess.run(["scalac", "-cp", f".:{jar}", "TraceMonitor.scala"],
                   cwd=workdir, env=_djv_env(), capture_output=True,
                   text=True, timeout=300, check=True)


def run_dejavu(workdir: Path, events, times, timed, bits=20):
    """(seconds from DejaVu's own 'Elapsed analysis time', #violations)."""
    name = "log.timed.csv" if timed else "log.csv"
    rows = []
    for ev, ts in zip(events, times):
        for pname, tuples in ev.items():
            for tup in tuples:
                row = [pname] + [str(a) for a in tup]
                if timed:
                    row.append(str(ts))
                rows.append(",".join(row))
    (workdir / name).write_text("\n".join(rows) + "\n")
    res = workdir / "dejavu-results"
    if res.exists():
        res.unlink()
    r = subprocess.run(["scala", "-J-Xmx8g", "-cp", f".:{DEJAVU_JAR}",
                        "TraceMonitor", name, str(bits)],
                       cwd=workdir, env=_djv_env(), capture_output=True,
                       text=True, timeout=600)
    m = re.search(r"Elapsed analysis time:\s*([\d.]+)s", r.stdout)
    if not m:
        raise RuntimeError(f"no analysis time in output: {r.stdout[-300:]}")
    viol = (len([ln for ln in res.read_text().splitlines() if ln.strip()])
            if res.exists() else 0)
    return float(m.group(1)), viol


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
    ap.add_argument("--no-dejavu", action="store_true")
    args = ap.parse_args()
    sizes = [int(s) for s in args.sizes.split(",")]
    use_djv = not args.no_dejavu and dejavu_available()
    if not args.no_dejavu and not use_djv:
        print("(DejaVu jar/toolchain not found; skipping the DejaVu column)")

    print(f"{'property':<12} {'events':>7} {'DejaVu':>9} {'us/ev':>6} "
          f"{'DejaVuMT':>10} {'us/ev':>7} {'MonPoly':>9} {'us/ev':>6}"
          f"  verdicts")
    for kind, (spec_text, prop) in SPECS.items():
        djv_dir = None
        if use_djv and DEJAVU_SPECS[kind]:
            djv_dir = Path(tempfile.mkdtemp(prefix=f"djv-{kind}-"))
            dejavu_compile(DEJAVU_SPECS[kind], djv_dir)
        for n in sizes:
            events, times = make_trace(kind, n, args.values)
            if djv_dir:
                dt_dv, v_dv = run_dejavu(djv_dir, events, times,
                                         DEJAVU_TIMED[kind])
                dv = f"{dt_dv:>8.3f}s {dt_dv/n*1e6:>5.1f}"
            else:
                dt_dv = v_dv = None
                dv = f"{'-':>9} {'-':>5}"
            dt_us, v_us = run_dejavumt(spec_text, prop, events, times)
            dt_mp, v_mp = run_monpoly(spec_text, prop, events, times)
            counts = {"MT": v_us, "MP": v_mp}
            if v_dv is not None:
                counts["DV"] = v_dv
            agree = ("agree" if len(set(counts.values())) == 1
                     else " ".join(f"{k}={v}" for k, v in counts.items()))
            print(f"{kind:<12} {n:>7} {dv} {dt_us:>9.2f}s "
                  f"{dt_us/n*1e6:>6.0f} {dt_mp:>8.3f}s {dt_mp/n*1e6:>5.1f}"
                  f"  {agree} ({v_us})", flush=True)


if __name__ == "__main__":
    main()
