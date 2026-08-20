"""Four-system performance comparison on shared properties:

- reference: the semantic evaluator of fuzz_reference.py -- the assignment
  semantics run as a program (whole trace, memoised, not incremental; now
  first-order via universe enumeration).  Run in a child process with a
  timeout; once it times out at some size, larger sizes are skipped.
- MonPoly: subprocess, its usual violation mode (-negate); process time
  (startup ~4 ms included).
- DejaVu (BDD): its generated monitor compiled once per property (excluded
  from timing); its self-reported "Elapsed analysis time" (JVM startup
  excluded).  Past-time only: future properties are skipped.
- DejaVuMT: in-process, Z3 backend, defaults; monitoring loop timed.

Properties come in propositional and first-order versions of the same four
patterns (past, metric past, bounded future, interval), plus a two-variable
first-order property.  Violation counts are cross-checked over all systems
on every run.

    python experiments/perf_bench.py [--sizes 1000,4000,16000] [--values 20]
                                     [--timeout 120] [--no-dejavu]
"""
from __future__ import annotations

import argparse
import multiprocessing as mp
import os
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
from fuzz_reference import reference
import monpoly


# --- properties ---------------------------------------------------------------
# id: (DejaVuMT spec, DejaVu spec or None (future: past-only tool),
#      timed?, trace kind)

PROPS = {
    # propositional
    "past-p": (
        "pred open()\npred close()\nprop q : close -> P open",
        "prop q : close -> P open", False, "past"),
    "tpast-p": (
        "pred req()\npred rsp()\nprop q : rsp -> P[<=10] req",
        "prop q : rsp -> P[<=10] req", True, "tpast"),
    "future-p": (
        "pred req()\npred ack()\nprop q : req -> F[<=10] ack",
        None, True, "future"),
    "intv-p": (
        "pred grant()\npred reset()\npred use()\n"
        "prop q : use -> [grant, reset)",
        "prop q : use -> [grant, reset)", False, "intv"),
    # first-order
    "past-fo": (
        "pred open(f: String)\npred close(f: String)\n"
        "prop q : Forall f . close(f) -> P open(f)",
        "prop q : Forall f . close(f) -> P open(f)", False, "past"),
    "tpast-fo": (
        "pred req(x: String)\npred rsp(x: String)\n"
        "prop q : Forall x . rsp(x) -> P[<=10] req(x)",
        "prop q : Forall x . rsp(x) -> P[<=10] req(x)", True, "tpast"),
    "future-fo": (
        "pred req(x: String)\npred ack(x: String)\n"
        "prop q : Forall x . req(x) -> F[<=10] ack(x)",
        None, True, "future"),
    "intv-fo": (
        "pred grant(x: String)\npred reset(x: String)\npred use(x: String)\n"
        "prop q : Forall x . use(x) -> [grant(x), reset(x))",
        "prop q : Forall x . use(x) -> [grant(x), reset(x))", False, "intv"),
    # first-order, two variables (the classic access-control shape)
    "access-fo2": (
        "pred open(f: String)\npred access(u: String, f: String)\n"
        "prop q : Forall u . Forall f . access(u,f) -> P open(f)",
        "prop q : Forall u . Forall f . access(u,f) -> P open(f)",
        False, "access"),
}


def make_trace(kind, n, values, fo):
    """n events; ~1 violation per 50.  Propositional variants use 0-ary
    facts and violate timed windows via time jumps; first-order variants
    cycle `values` distinct data values."""
    events, times = [], []
    t = 0
    for i in range(n):
        t += 1
        if kind in ("past", "tpast", "future"):
            a, b = {"past": ("open", "close"), "tpast": ("req", "rsp"),
                    "future": ("req", "ack")}[kind]
            if fo:
                v = (f"v{(i // 2) % values}",)
                if i % 50 == 49:
                    bad = (f"never{i}",)
                    ev = ({"req": [bad]} if kind == "future"
                          else {b: [bad]})
                elif i % 2 == 0:
                    ev = {a: [v]}
                else:
                    ev = {b: [v]}
            else:
                if kind == "past":
                    # only a close before the first open violates
                    if i < 2:
                        ev = {"close": [()]}
                    else:
                        ev = {a: [()]} if i % 2 == 0 else {b: [()]}
                elif i % 50 == 49:
                    t += 20        # time jump: window violated either way
                    ev = {"rsp": [()]} if kind == "tpast" else {"req": [()]}
                else:
                    ev = {a: [()]} if i % 2 == 0 else {b: [()]}
        elif kind == "intv":
            arg = (f"v{(i // 10) % values}",) if fo else ()
            r = i % 10
            if r == 0:
                ev = {"grant": [arg]}
            elif r == 8:
                ev = {"reset": [arg]}
            else:
                ev = {"use": [arg]}        # r == 9: after reset, violation
        else:  # access: open files, then accesses; every 50th unopened
            f_ = f"f{(i // 10) % values}"
            u = f"u{i % 5}"
            if i % 10 == 0:
                ev = {"open": [(f_,)]}
            elif i % 50 == 49:
                ev = {"access": [(u, f"nope{i}")]}
            else:
                ev = {"access": [(u, f_)]}
        events.append(ev)
        times.append(t)
    return events, times


# --- DejaVu (BDD) -------------------------------------------------------------

DEJAVU_JAR = (Path.home()
              / "Desktop/development/dejavu/out/artifacts/dejavu_jar/dejavu.jar")
_JAVA_HOME = "/opt/homebrew/opt/openjdk@11/libexec/openjdk.jdk/Contents/Home"


def _djv_env():
    return dict(os.environ, JAVA_HOME=_JAVA_HOME,
                PATH=f"{_JAVA_HOME}/bin:/opt/homebrew/opt/scala@2.12/bin:"
                     + os.environ.get("PATH", ""))


def dejavu_available():
    return DEJAVU_JAR.exists() and Path(_JAVA_HOME).exists()


def dejavu_compile(spec_text, workdir: Path):
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


# --- MonPoly ------------------------------------------------------------------

def run_monpoly(spec_text, events, times):
    spec = parse_spec(spec_text)
    body = spec.properties[0].body
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
        return None, None
    viol = {int(m_.group(1)) for m_ in
            re.finditer(r"\(time point (\d+)\)", r.stdout)}
    return dt, len({tp for tp in viol if tp < n})


# --- DejaVuMT -----------------------------------------------------------------

def run_dejavumt(spec_text, events, times):
    m = Monitor(parse_spec(spec_text), solver="z3")
    t0 = time.perf_counter()
    viol = 0
    for ev, ts in zip(events, times):
        m.step(ev, ts)
        viol += sum(1 for _, _, h in m.resolved if h is False)
    viol += sum(1 for _, _, h in m.end() if h is False)
    return time.perf_counter() - t0, viol


# --- reference ----------------------------------------------------------------

def _ref_child(spec_text, events, times, q):
    body = parse_spec(spec_text).properties[0].body
    t0 = time.perf_counter()
    verdicts = reference(body, events, times)
    q.put((time.perf_counter() - t0,
           sum(1 for v in verdicts if v is False)))


def run_reference(spec_text, events, times, timeout):
    q = mp.Queue()
    p = mp.Process(target=_ref_child, args=(spec_text, events, times, q))
    p.start()
    p.join(timeout)
    if p.is_alive():
        p.terminate()
        p.join()
        return None, None
    return q.get()


# --- driver -------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sizes", default="1000,4000,16000")
    ap.add_argument("--values", type=int, default=20)
    ap.add_argument("--timeout", type=float, default=120.0)
    ap.add_argument("--no-dejavu", action="store_true")
    args = ap.parse_args()
    sizes = [int(s) for s in args.sizes.split(",")]
    use_djv = not args.no_dejavu and dejavu_available()

    print(f"{'property':<11} {'events':>7} {'reference':>10} {'us/ev':>7} "
          f"{'MonPoly':>9} {'us/ev':>6} {'DejaVu':>8} {'us/ev':>6} "
          f"{'DejaVuMT':>9} {'us/ev':>7}  verdicts")
    for pid, (mt_spec, dv_spec, timed, kind) in PROPS.items():
        fo = pid.endswith("fo") or pid.endswith("fo2")
        djv_dir = None
        if use_djv and dv_spec:
            djv_dir = Path(tempfile.mkdtemp(prefix=f"djv-{pid}-"))
            dejavu_compile(dv_spec, djv_dir)
        ref_dead = False
        for n in sizes:
            events, times = make_trace(kind, n, args.values, fo)
            dt_mt, v_mt = run_dejavumt(mt_spec, events, times)
            counts = {"MT": v_mt}
            if ref_dead:
                dt_rf = v_rf = None
            else:
                dt_rf, v_rf = run_reference(mt_spec, events, times,
                                            args.timeout)
                ref_dead = dt_rf is None
            if v_rf is not None:
                counts["ref"] = v_rf
            rf = (f"{dt_rf:>9.2f}s {dt_rf/n*1e6:>6.0f}" if dt_rf is not None
                  else f"{'>' + str(int(args.timeout)) + 's':>10} {'-':>6}")
            dt_mp, v_mp = run_monpoly(mt_spec, events, times)
            if v_mp is not None:
                counts["MP"] = v_mp
            mpc = (f"{dt_mp:>8.3f}s {dt_mp/n*1e6:>5.1f}" if dt_mp is not None
                   else f"{'n/m':>9} {'-':>5}")
            if djv_dir:
                dt_dv, v_dv = run_dejavu(djv_dir, events, times, timed)
                counts["DV"] = v_dv
                dv = f"{dt_dv:>7.3f}s {dt_dv/n*1e6:>5.1f}"
            else:
                dv = f"{'-':>8} {'-':>5}"
            agree = ("agree" if len(set(counts.values())) == 1
                     else " ".join(f"{k}={v}" for k, v in counts.items()))
            print(f"{pid:<11} {n:>7} {rf} {mpc} {dv} {dt_mt:>8.2f}s "
                  f"{dt_mt/n*1e6:>6.0f}  {agree} ({v_mt})", flush=True)


if __name__ == "__main__":
    main()
