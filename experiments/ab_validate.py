"""
A/B validation harness: run every runnable (spec, log) pair from the DejaVu
distribution through both the original BDD-based DejaVu and DejaVuMT, and diff
the verdicts (sets of violating event numbers).

Usage:
    .venv/bin/python experiments/ab_validate.py [options]

Options:
    --max-events N    prefix cap per log (default 3000)
    --timeout S       per-pair DejaVuMT timeout in seconds (default 120)
    --solver S        z3 | cvc5 for DejaVuMT (default z3)
    --only SUBSTR     only pairs whose spec or log path contains SUBSTR
    --workdir DIR     scratch dir (default: mkdtemp)

Requires the DejaVu toolchain: JDK 11 and Scala 2.12 (see README/memory).
Outputs experiments/ab_report.md and experiments/ab_report.json.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from dejavumt.parser import parse_file  # noqa: E402
from dejavumt.engine import Monitor     # noqa: E402
from dejavumt.log import read_events    # noqa: E402

DEJAVU_CODE = ROOT / "requirements/dejavu/dejavu-code"
JAR = DEJAVU_CODE / "out/artifacts/dejavu_jar/dejavu.jar"
# Classpath for the DejaVu tool itself; overridable via --dejavu-cp to run
# against a locally built (e.g. fixed) DejaVu instead of the shipped fat jar.
DEJAVU_CP = str(JAR)
JAVA_HOME = "/opt/homebrew/opt/openjdk@11/libexec/openjdk.jdk/Contents/Home"
SCALA_BIN = "/opt/homebrew/opt/scala@2.12/bin"

ENV = dict(os.environ,
           JAVA_HOME=JAVA_HOME,
           PATH=f"{JAVA_HOME}/bin:{SCALA_BIN}:" + os.environ.get("PATH", ""))


# ---------------------------------------------------------------------------
# Discovery and gating
# ---------------------------------------------------------------------------

def discover_pairs():
    """All (spec, log) pairs: every .qtl with every non-empty .csv in its dir."""
    pairs = []
    for base in (DEJAVU_CODE / "out/examples",
                 DEJAVU_CODE / "src/test/scala/tests"):
        for d in sorted({p.parent for p in base.rglob("*.qtl")}):
            specs = sorted(d.glob("*.qtl"))
            logs = [l for l in sorted(d.glob("*.csv")) if l.stat().st_size > 0]
            for s in specs:
                for l in logs:
                    pairs.append((s, l))
    return pairs


def skip_reason(spec: Path) -> str | None:
    """None if our parser accepts the spec; otherwise a reason bucket."""
    try:
        parse_file(str(spec))
        return None
    except Exception:
        text = spec.read_text()
        if re.search(r"\[<=|\[>|(?<![A-Za-z])Z(?![A-Za-z])", text):
            return "timed-operators"
        if ":=" in text:
            return "rules"
        if re.search(r"\b(exists|forall)\b", text):
            return "lowercase-quantifier"
        return "parse-error"


# ---------------------------------------------------------------------------
# DejaVu side
# ---------------------------------------------------------------------------

def sh(cmd, cwd, timeout=300):
    return subprocess.run(cmd, cwd=cwd, env=ENV, timeout=timeout,
                          capture_output=True, text=True)


def dejavu_compile(spec: Path, workdir: Path) -> str | None:
    """Generate + compile the DejaVu monitor for a spec. None on success."""
    r = sh(["java", "-cp", DEJAVU_CP, "dejavu.Verify", str(spec)], workdir)
    out = r.stdout + r.stderr
    if r.returncode != 0 or "error" in out.lower() and "0 errors" not in out:
        if not (workdir / "TraceMonitor.scala").exists():
            return f"codegen failed: {out.strip().splitlines()[-1] if out.strip() else r.returncode}"
    r = sh(["scalac", "-cp", f".:{DEJAVU_CP}", "TraceMonitor.scala"], workdir)
    if r.returncode != 0:
        return f"scalac failed: {(r.stderr or r.stdout).strip().splitlines()[-1]}"
    return None


def dejavu_run(workdir: Path, log: Path, bits: int) -> tuple[set[int] | None, str]:
    """Run the compiled monitor on a log. Returns (violations, error)."""
    results = workdir / "dejavu-results"
    if results.exists():
        results.unlink()
    r = sh(["scala", "-J-Xmx8g", "-cp", f".:{DEJAVU_CP}", "TraceMonitor",
            str(log), str(bits)], workdir, timeout=600)
    if not results.exists():
        return None, f"no results file (rc={r.returncode})"
    lines = results.read_text().split()
    if any(l == "oom" for l in lines):
        return None, "oom"
    viol = {int(l) for l in results.read_text().splitlines()
            if re.fullmatch(r"\d+", l.strip())}
    return viol, ""


# ---------------------------------------------------------------------------
# DejaVuMT side
# ---------------------------------------------------------------------------

class Timeout(Exception):
    pass


def mt_run(spec: Path, log: Path, solver: str, timeout_s: int
           ) -> tuple[set[int] | None, str]:
    def handler(sig, frame):
        raise Timeout()
    old = signal.signal(signal.SIGALRM, handler)
    signal.alarm(timeout_s)
    try:
        m = Monitor(parse_file(str(spec)), solver=solver)
        viol = set()
        for i, ev in enumerate(read_events(str(log)), 1):
            if not all(m.step(ev).values()):
                viol.add(i)
        return viol, ""
    except Timeout:
        return None, "timeout"
    except Exception as e:
        return None, f"{type(e).__name__}: {str(e)[:100]}"
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-events", type=int, default=3000)
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--solver", default="z3", choices=["z3", "cvc5"])
    ap.add_argument("--only", default=None)
    ap.add_argument("--workdir", default=None)
    ap.add_argument("--dejavu-cp", default=None,
                    help="classpath for the DejaVu tool (default: shipped jar); "
                         "use to test a locally built/fixed DejaVu")
    args = ap.parse_args()

    if args.dejavu_cp:
        global DEJAVU_CP
        DEJAVU_CP = args.dejavu_cp

    scratch = Path(args.workdir) if args.workdir else Path(
        tempfile.mkdtemp(prefix="ab_validate_"))
    scratch.mkdir(parents=True, exist_ok=True)

    pairs = discover_pairs()
    if args.only:
        pairs = [(s, l) for s, l in pairs
                 if args.only in str(s) or args.only in str(l)]
    print(f"{len(pairs)} (spec, log) pairs discovered")

    rows = []
    compiled: dict[Path, tuple[Path, str | None]] = {}  # spec -> (workdir, err)
    t_start = time.time()

    for spec, log in pairs:
        rel_s = str(spec.relative_to(DEJAVU_CODE))
        rel_l = str(log.relative_to(DEJAVU_CODE))
        row = {"spec": rel_s, "log": rel_l}

        reason = skip_reason(spec)
        if reason:
            row.update(status="SKIP_UNSUPPORTED", reason=reason)
            rows.append(row)
            continue

        # prefix-capped copy of the log (same input for both tools)
        with open(log) as f:
            lines = [ln for ln in f][: args.max_events]
        n_events = len(lines)
        capped = scratch / "current_log.csv"
        capped.write_text("".join(lines))
        row["events"] = n_events

        # DejaVu: compile once per spec
        if spec not in compiled:
            wd = scratch / f"dv_{len(compiled):03d}"
            wd.mkdir(exist_ok=True)
            compiled[spec] = (wd, dejavu_compile(spec, wd))
        wd, cerr = compiled[spec]
        if cerr:
            row.update(status="DEJAVU_ERROR", reason=cerr)
            rows.append(row)
            print(f"  DEJAVU_ERROR {rel_s}: {cerr}")
            continue

        dv, derr = dejavu_run(wd, capped, 20)
        if derr == "oom":
            dv, derr = dejavu_run(wd, capped, 24)
        if dv is None:
            row.update(status="DEJAVU_ERROR", reason=derr)
            rows.append(row)
            print(f"  DEJAVU_ERROR {rel_s} / {rel_l}: {derr}")
            continue

        mt, merr = mt_run(spec, capped, args.solver, args.timeout)
        if mt is None:
            row.update(status="MT_TIMEOUT" if merr == "timeout" else "MT_ERROR",
                       reason=merr, dejavu_violations=sorted(dv))
            rows.append(row)
            print(f"  {row['status']} {rel_s} / {rel_l}: {merr}")
            continue

        row.update(dejavu_violations=sorted(dv), mt_violations=sorted(mt),
                   status="MATCH" if dv == mt else "MISMATCH")
        if dv != mt:
            print(f"  MISMATCH {rel_s} / {rel_l}: dejavu={sorted(dv)[:8]} "
                  f"mt={sorted(mt)[:8]}")
        rows.append(row)

    # ---- report ----
    counts: dict[str, int] = {}
    for r in rows:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    dur = time.time() - t_start

    md = ["# A/B validation: DejaVu vs DejaVuMT",
          "",
          f"solver: {args.solver}; max events/log: {args.max_events}; "
          f"pairs: {len(rows)}; wall time: {dur:.0f}s",
          "",
          "## Summary",
          ""]
    for k in sorted(counts):
        md.append(f"- {k}: {counts[k]}")
    md += ["", "## Pairs", "",
           "| spec | log | events | dejavu viol | mt viol | status |",
           "|---|---|---|---|---|---|"]
    for r in rows:
        md.append("| {} | {} | {} | {} | {} | {} |".format(
            r["spec"], r["log"], r.get("events", ""),
            len(r.get("dejavu_violations", [])) if "dejavu_violations" in r else "",
            len(r.get("mt_violations", [])) if "mt_violations" in r else "",
            r["status"] + (f" ({r['reason']})" if "reason" in r else "")))
    (ROOT / "experiments/ab_report.md").write_text("\n".join(md) + "\n")
    (ROOT / "experiments/ab_report.json").write_text(json.dumps(rows, indent=1))

    print()
    print(f"=== summary ({dur:.0f}s) ===")
    for k in sorted(counts):
        print(f"  {k}: {counts[k]}")
    print("report: experiments/ab_report.md")


if __name__ == "__main__":
    main()
