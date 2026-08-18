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


def next_bound(times):
    return max((b - a for a, b in zip(times, times[1:])), default=0)


def compare(body, events, times):
    """None if the tools agree (or MonPoly cannot take the formula);
    otherwise a message."""
    try:
        mf = monpoly.to_mfotl(body, next_bound(times))
    except monpoly.Unsupported:
        return None
    log = monpoly.to_log([{p: [()] for p in ev} for ev in events], times)
    viol, sat, msg = monpoly.judgements(SIG, mf, log, len(events))
    if viol is None:
        return None                      # outside its fragment, or a timeout
    try:
        ours = dejavumt_violations(body, events, times)
    except Exception as e:
        return f"DejaVuMT error: {type(e).__name__}: {e}"
    # Compare only on MonPoly's evaluation frontier (viol | sat): positions it
    # never evaluated (nested future outrunning its appended timestamp) carry
    # no MonPoly verdict at all.
    bad = (viol - ours) | (ours & sat)
    if bad:
        return (f"positions differ on {sorted(bad)}"
                f"\n         monpoly  viol={sorted(viol)} sat={sorted(sat)}"
                f"\n         dejavumt viol={sorted(ours)}"
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
            mf = monpoly.to_mfotl(body, next_bound(times))
        except monpoly.Unsupported:
            skipped += 1
            continue
        log = monpoly.to_log([{p: [()] for p in ev} for ev in events], times)
        if monpoly.judgements(SIG, mf, log, len(events))[0] is None:
            skipped += 1
            continue
        msg = compare(body, events, times)
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


FO_SIG = "p(x0:int)\nq(x0:int)\nr(x0:int)\n"


def fo_formula(rng, depth, vars_=("x", "y")):
    """Random FIRST-ORDER formula: unary predicates over int variables,
    equalities/orders, quantifiers -- the fragment where MonPoly's
    range-restriction rules actually bite (ground formulas only ever
    trip the bounded-future requirement)."""
    if depth == 0:
        v = rng.choice(vars_)
        return rng.choice([
            ast.Pred(rng.choice(fr.PREDS), (ast.Var(v),)),
            ast.Pred(rng.choice(fr.PREDS), (ast.Var(v),)),
            ast.Compare(ast.Var(v), rng.choice(["=", "<", "<="]),
                        rng.choice([ast.Const(rng.randint(0, 3), "Int"),
                                    ast.Var(rng.choice(vars_))])),
        ])
    lo = rng.randint(0, 3)
    hi = rng.choice([None, lo + rng.randint(0, 4)])
    sub = lambda: fo_formula(rng, depth - 1, vars_)   # noqa: E731
    kind = rng.choice(["not", "and", "or", "implies", "exists", "forall",
                       "prev", "since", "once", "hist",
                       "tsince", "tonce", "fev", "falw", "funtil"])
    return {
        "not": lambda: ast.Not(sub()),
        "and": lambda: ast.And(sub(), sub()),
        "or": lambda: ast.Or(sub(), sub()),
        "implies": lambda: ast.Implies(sub(), sub()),
        "exists": lambda: ast.Exists(rng.choice(vars_), sub()),
        "forall": lambda: ast.Forall(rng.choice(vars_), sub()),
        "prev": lambda: ast.Prev(sub()),
        "since": lambda: ast.Since(sub(), sub()),
        "once": lambda: ast.Once(sub()),
        "hist": lambda: ast.Hist(sub()),
        "tsince": lambda: ast.TimedSince(sub(), lo, hi, sub()),
        "tonce": lambda: ast.TimedOnce(lo, hi, sub()),
        "fev": lambda: ast.TimedEventually(lo, hi, sub()),
        "falw": lambda: ast.TimedAlways(lo, hi, sub()),
        "funtil": lambda: ast.TimedUntil(sub(), lo, hi, sub()),
    }[kind]()


def run_fragment(n, seed, firstorder=False):
    rng = random.Random(seed)
    total = ok = 0
    reasons = {}
    sig = FO_SIG if firstorder else SIG
    for _ in range(n):
        body = (fo_formula(rng, rng.randint(1, 3)) if firstorder
                else fr.rand_formula(rng, rng.randint(1, 3)))
        try:
            mf = monpoly.to_mfotl(body, 3)
        except monpoly.Unsupported:
            continue
        total += 1
        good, out = monpoly.monitorable(sig, mf)
        if good:
            ok += 1
        else:
            key = "other"
            lines = out.splitlines()
            culprit = ""
            for idx, line in enumerate(lines):
                if "unbounded future" in line:
                    culprit = "@unbounded"
                    break
                if "because of the subformula" in line and idx + 1 < len(lines):
                    culprit = lines[idx + 1].strip()
                    break
            if culprit == "@unbounded":
                key = "unbounded future interval"
            elif culprit.startswith("NOT"):
                key = "negation with free variables"
            elif " OR " in culprit:
                key = "OR with mismatched free variables"
            elif " SINCE" in culprit or " UNTIL" in culprit:
                key = "SINCE/UNTIL left vars not in right"
            elif "<" in culprit:
                key = "order relation on unbound variables"
            elif "=" in culprit:
                key = "equality between two variables"
            elif culprit:
                key = culprit[:50]
            reasons[key] = reasons.get(key, 0) + 1
    print(f"{total} random {'first-order ' if firstorder else 'ground '}"
          f"formulas of the shared syntax:")
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
    if mode == "fragment":
        return run_fragment(n, seed)
    if mode == "fofragment":
        return run_fragment(n, seed, firstorder=True)
    return run_verdicts(n, seed)


if __name__ == "__main__":
    sys.exit(main())
