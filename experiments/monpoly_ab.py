"""
Differential comparison of DejaVuMT against MonPoly.

MonPoly is a second oracle for the fragment DejaVu cannot check -- metric past
AND bounded future -- so it plays for Section "Bounded Future Operators" the
role DejaVu plays for the past fragment.  Two experiments:

  verdicts   random formulas (in the shared syntax) and random timed traces
             through both tools; verdicts diffed per position, mismatches
             shrunk to minimal counterexamples.

  fragment   how often a random formula of the shared syntax falls outside
             MonPoly's *monitorable* fragment -- the syntactic restriction its
             finite-relation representation forces, which the formula
             representation does not need.

    .venv/bin/python experiments/monpoly_ab.py [verdicts|fragment] [n] [seed]
"""
from __future__ import annotations

import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import monpoly                                    # noqa: E402
import fuzz_reference as fr                       # noqa: E402
from dejavumt import parse_spec, Monitor          # noqa: E402
from dejavumt import ast                          # noqa: E402

SIG = "".join(f"{p}()\n" for p in fr.PREDS)


def dejavumt_violations(body, events, times):
    spec = ("prop q : " + str(body)
            .replace("¬", "!").replace("∧", "&").replace("∨", "|")
            .replace("↔", "<->").replace("→", "->"))
    m = Monitor(parse_spec(spec))
    got = {}
    for ev, ts in zip(events, times):
        m.step({p: [()] for p in ev}, ts)
        for pos, _n, holds in m.resolved:
            got[pos] = holds
    for pos, _n, holds in m.end():
        got[pos] = holds
    return {i + 1 for i in range(len(events)) if got.get(i + 1) is False}


def compare(body, events, times):
    """None if the tools agree (or MonPoly cannot take the formula);
    otherwise a message."""
    try:
        mf = monpoly.to_mfotl(body)
    except monpoly.Unsupported:
        return None
    log = monpoly.to_log([{p: [()] for p in ev} for ev in events], times)
    mp, msg = monpoly.violations(SIG, mf, log, len(events))
    if mp is None:
        return None                      # outside its fragment, or a timeout
    try:
        ours = dejavumt_violations(body, events, times)
    except Exception as e:
        return f"DejaVuMT error: {type(e).__name__}: {e}"
    if ours != mp:
        return (f"positions differ\n         monpoly  {sorted(mp)}"
                f"\n         dejavumt {sorted(ours)}"
                f"\n         mfotl    {mf}")
    return None


def shrink(body, events, times):
    changed = True
    while changed and len(events) > 1:
        changed = False
        for i in range(len(events)):
            ev2, tm2 = events[:i] + events[i + 1:], times[:i] + times[i + 1:]
            if compare(body, ev2, tm2):
                events, times, changed = ev2, tm2, True
                break
    return events, times


def run_verdicts(n, seed):
    rng = random.Random(seed)
    compared = fails = skipped = 0
    for it in range(n):
        body = fr.rand_formula(rng, rng.randint(1, 3))
        events, times = fr.rand_trace(rng)
        try:
            monpoly.to_mfotl(body)
        except monpoly.Unsupported:
            skipped += 1
            continue
        msg = compare(body, events, times)
        mf = monpoly.to_mfotl(body)
        log = monpoly.to_log([{p: [()] for p in ev} for ev in events], times)
        if monpoly.violations(SIG, mf, log, len(events))[0] is None:
            skipped += 1
            continue
        compared += 1
        if msg:
            fails += 1
            events, times = shrink(body, events, times)
            print(f"[{it}] MISMATCH  {body}")
            print(f"    trace: {[sorted(e) for e in events]} @ {times}")
            print(f"         {compare(body, events, times)}")
            if fails >= 5:
                break
    print(f"{n} formulas: {compared} compared, {fails} mismatches, "
          f"{skipped} not usable by MonPoly (seed {seed})")
    return 1 if fails else 0


def run_fragment(n, seed):
    rng = random.Random(seed)
    total = ok = 0
    reasons = {}
    for _ in range(n):
        body = fr.rand_formula(rng, rng.randint(1, 3))
        try:
            mf = monpoly.to_mfotl(body)
        except monpoly.Unsupported:
            continue
        total += 1
        good, out = monpoly.monitorable(SIG, mf)
        if good:
            ok += 1
        else:
            key = "not monitorable"
            for line in out.splitlines():
                if "because" in line:
                    key = line.strip()[:80]
            reasons[key] = reasons.get(key, 0) + 1
    print(f"{total} random formulas of the shared syntax:")
    print(f"  monitorable by MonPoly:  {ok} ({100*ok/max(total,1):.0f}%)")
    print(f"  rejected:                {total-ok} "
          f"({100*(total-ok)/max(total,1):.0f}%)")
    for k, v in sorted(reasons.items(), key=lambda kv: -kv[1])[:5]:
        print(f"     {v:4}  {k}")
    print("  DejaVuMT monitors all of them (no fragment restriction).")
    return 0


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "verdicts"
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    if not monpoly.available():
        print(f"MonPoly not built at {monpoly.MONPOLY}")
        return 2
    return run_fragment(n, seed) if mode == "fragment" else run_verdicts(n, seed)


if __name__ == "__main__":
    sys.exit(main())
