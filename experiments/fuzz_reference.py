"""
Differential fuzzing of the monitor against a brute-force reference.

The reference evaluator below is the assignment semantics of the paper,
transcribed case by case, evaluated over the whole (finite) trace with the
end-of-trace convention: position quantifiers range over 1..n.  It is
deliberately naive -- no tables, no obligations, no incrementality -- so that
each case is one line of the definition.

Random ground formulas (past + future operators, small time bounds) and random
timed traces (short, small alphabet, non-decreasing timestamps WITH
duplicates) are run through both; any verdict difference is shrunk to a
minimal counterexample and reported.

    .venv/bin/python experiments/fuzz_reference.py [#iterations] [seed]
"""
from __future__ import annotations

import random
import sys
from functools import lru_cache
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from dejavumt import parse_spec, Monitor  # noqa: E402
from dejavumt import ast                  # noqa: E402


# --- the reference: assignment semantics over the whole trace ---------------

def reference(body, events, times):
    """Verdict of `body` at every position (1-based), by the definitions."""
    n = len(events)

    def holds(f, i):
        return _holds(f, i)

    @lru_cache(maxsize=None)
    def _holds(f, i):
        if isinstance(f, ast.TrueC):
            return True
        if isinstance(f, ast.FalseC):
            return False
        if isinstance(f, ast.Pred):
            return f.name in events[i - 1]
        if isinstance(f, ast.Not):
            return not holds(f.arg, i)
        if isinstance(f, ast.And):
            return holds(f.left, i) and holds(f.right, i)
        if isinstance(f, ast.Or):
            return holds(f.left, i) or holds(f.right, i)
        if isinstance(f, ast.Implies):
            return (not holds(f.left, i)) or holds(f.right, i)
        if isinstance(f, ast.Iff):
            return holds(f.left, i) == holds(f.right, i)
        if isinstance(f, ast.Prev):
            return i > 1 and holds(f.arg, i - 1)
        if isinstance(f, ast.Next):
            return i < n and holds(f.arg, i + 1)
        if isinstance(f, ast.Since):
            return any(holds(f.right, j)
                       and all(holds(f.left, k) for k in range(j + 1, i + 1))
                       for j in range(1, i + 1))
        if isinstance(f, ast.Zince):
            return any(holds(f.right, j)
                       and all(holds(f.left, k) for k in range(j + 1, i + 1))
                       for j in range(1, i))
        if isinstance(f, ast.Once):
            return any(holds(f.arg, j) for j in range(1, i + 1))
        if isinstance(f, ast.Hist):
            return all(holds(f.arg, j) for j in range(1, i + 1))
        if isinstance(f, ast.Interval):
            return any(holds(f.left, j)
                       and not any(holds(f.right, k)
                                   for k in range(j + 1, i + 1))
                       for j in range(1, i + 1))

        def in_window(j, low, high):
            d = times[j - 1] - times[i - 1]
            return d >= low and (high is None or d <= high)

        def in_past_window(j, low, high):
            d = times[i - 1] - times[j - 1]
            return d >= low and (high is None or d <= high)

        if isinstance(f, ast.TimedSince):
            return any(holds(f.right, j) and in_past_window(j, f.low, f.high)
                       and all(holds(f.left, k) for k in range(j + 1, i + 1))
                       for j in range(1, i + 1))
        if isinstance(f, ast.TimedZince):
            return any(holds(f.right, j) and in_past_window(j, f.low, f.high)
                       and all(holds(f.left, k) for k in range(j + 1, i + 1))
                       for j in range(1, i))
        if isinstance(f, ast.TimedOnce):
            return any(holds(f.arg, j) and in_past_window(j, f.low, f.high)
                       for j in range(1, i + 1))
        if isinstance(f, ast.TimedHist):
            return all(holds(f.arg, j)
                       for j in range(1, i + 1)
                       if in_past_window(j, f.low, f.high))
        if isinstance(f, ast.TimedEventually):
            return any(holds(f.arg, j) and in_window(j, f.low, f.high)
                       for j in range(i, n + 1))
        if isinstance(f, ast.TimedAlways):
            return all(holds(f.arg, j)
                       for j in range(i, n + 1)
                       if in_window(j, f.low, f.high))
        if isinstance(f, ast.TimedUntil):
            return any(holds(f.right, j) and in_window(j, f.low, f.high)
                       and all(holds(f.left, k) for k in range(i, j))
                       for j in range(i, n + 1))
        raise TypeError(type(f).__name__)

    return [holds(body, i) for i in range(1, n + 1)]


# --- the monitor side --------------------------------------------------------

def monitored(spec_text, events, times):
    m = Monitor(parse_spec(spec_text))
    got = {}
    for ev, ts in zip(events, times):
        m.step({p: [()] for p in ev}, ts)
        for pos, _name, holds in m.resolved:
            got[pos] = holds
    for pos, _name, holds in m.end():
        got[pos] = holds
    return [got.get(i + 1) for i in range(len(events))]


# --- random generation --------------------------------------------------------

PREDS = ["p", "q", "r"]


def rand_formula(rng, depth):
    if depth == 0:
        return rng.choice([ast.Pred(rng.choice(PREDS), ()),
                           ast.TrueC(), ast.FalseC()])
    lo = rng.randint(0, 3)
    hi = rng.choice([None, lo + rng.randint(0, 4)])
    kind = rng.choice([
        "not", "and", "or", "implies", "iff", "prev", "next",
        "since", "zince", "once", "hist", "interval",
        "tsince", "tzince", "tonce", "thist",
        "fev", "falw", "funtil",
    ])
    sub = lambda: rand_formula(rng, depth - 1)   # noqa: E731
    return {
        "not": lambda: ast.Not(sub()),
        "and": lambda: ast.And(sub(), sub()),
        "or": lambda: ast.Or(sub(), sub()),
        "implies": lambda: ast.Implies(sub(), sub()),
        "iff": lambda: ast.Iff(sub(), sub()),
        "zince": lambda: ast.Zince(sub(), sub()),
        "tzince": lambda: ast.TimedZince(sub(), lo, hi, sub()),
        "prev": lambda: ast.Prev(sub()),
        "next": lambda: ast.Next(sub()),
        "since": lambda: ast.Since(sub(), sub()),
        "once": lambda: ast.Once(sub()),
        "hist": lambda: ast.Hist(sub()),
        "interval": lambda: ast.Interval(sub(), sub()),
        "tsince": lambda: ast.TimedSince(sub(), lo, hi, sub()),
        "tonce": lambda: ast.TimedOnce(lo, hi, sub()),
        "thist": lambda: ast.TimedHist(lo, hi, sub()),
        "fev": lambda: ast.TimedEventually(lo, hi, sub()),
        "falw": lambda: ast.TimedAlways(lo, hi, sub()),
        "funtil": lambda: ast.TimedUntil(sub(), lo, hi, sub()),
    }[kind]()


def rand_trace(rng, maxlen=14):
    n = rng.randint(1, maxlen)
    events, times, t = [], [], 0
    for _ in range(n):
        events.append(frozenset(rng.sample(PREDS, rng.randint(0, 2))))
        t += rng.choice([0, 0, 1, 1, 2, 3])   # duplicates on purpose
        times.append(t)
    return events, times


# --- shrinking ----------------------------------------------------------------

def disagrees(body, events, times):
    spec = ("prop q : " + str(body)
            .replace("¬", "!").replace("∧", "&").replace("∨", "|")
            .replace("↔", "<->").replace("→", "->"))
    try:
        got = monitored(spec, events, times)
    except Exception as e:
        return f"monitor error: {e}"
    want = reference(body, events, times)
    if [bool(x) for x in got] != want:
        return f"want {want}\n         got  {got}"
    return None


def shrink(body, events, times):
    changed = True
    while changed and len(events) > 1:
        changed = False
        for i in range(len(events)):
            ev2 = events[:i] + events[i + 1:]
            tm2 = times[:i] + times[i + 1:]
            if disagrees(body, ev2, tm2):
                events, times = ev2, tm2
                changed = True
                break
    return events, times


# --- main ----------------------------------------------------------------------

def main():
    iters = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    rng = random.Random(seed)
    fails = 0
    for it in range(iters):
        body = rand_formula(rng, rng.randint(1, 3))
        events, times = rand_trace(rng)
        msg = disagrees(body, events, times)
        if msg:
            fails += 1
            events, times = shrink(body, events, times)
            print(f"[{it}] MISMATCH  {body}")
            print(f"    trace: {[sorted(e) for e in events]} @ {times}")
            print(f"         {disagrees(body, events, times)}")
            if fails >= 5:
                break
    print(f"{iters} iterations, {fails} mismatches (seed {seed})")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
