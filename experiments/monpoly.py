"""
Translation from DejaVuMT's QTL to MonPoly's MFOTL, and a runner.

MonPoly (https://bitbucket.org/monpoly/monpoly) monitors metric first-order
temporal logic over finite relations.  Its language overlaps ours on the
first-order temporal core -- metric past *and* bounded future -- which makes it
a second oracle for the fragment DejaVu cannot check (Section "Bounded Future
Operators" of the paper).

Conventions that matter for the comparison, verified against the tool:

  * MonPoly numbers time points from 0; DejaVuMT numbers positions from 1.
  * On a closed formula, `-negate` reports the time points at which the
    formula is *violated* -- exactly our violating positions.
  * Every temporal operator carries an interval; our untimed operators are the
    interval [0,*).
  * The signature file must declare every predicate, with argument sorts
    (int/string/float).
  * By default MonPoly appends a maximal last timestamp, which closes the
    bounded-future windows at the end of the trace -- the counterpart of our
    end-of-trace forcing.
"""
from __future__ import annotations

import os
import re
import subprocess
import tempfile
from pathlib import Path

from dejavumt import ast

MONPOLY_DIR = Path.home() / "Desktop/development/monpoly"
MONPOLY = MONPOLY_DIR / "_build/default/src/main.exe"
SORTS = {"String": "string", "Int": "int", "Real": "float", "Bool": "int"}


class Unsupported(Exception):
    """The formula uses something MonPoly's language does not have."""


# --- formula ---------------------------------------------------------------

def _iv(low, high):
    return f"[{low},{high}]" if high is not None else f"[{low},*)"


def to_mfotl(f, next_bound=None) -> str:
    """Our AST as an MFOTL formula (fully parenthesised).

    `next_bound`: our X is position-based ("the next event, whenever it is"),
    so it translates to NEXT with an interval covering every consecutive time
    delta of the trace at hand.  This must be finite: MonPoly by default
    appends a phantom time point at a maximal timestamp (its analogue of our
    end-of-trace closing), and NEXT[0,*) would look across the trace boundary
    into it -- X true would hold at the last position.  With the interval
    bounded by the trace's own maximal delta, the phantom (huge delta) is
    excluded and the two conventions coincide."""
    def r(g):
        return to_mfotl(g, next_bound)
    if isinstance(f, ast.TrueC):
        return "TRUE"
    if isinstance(f, ast.FalseC):
        return "FALSE"
    if isinstance(f, ast.Pred):
        args = ",".join(_term(a) for a in f.args)
        return f"{f.name}({args})"
    if isinstance(f, ast.Compare):
        # MonPoly has =, <, <=; flip the others.
        l, op, rr = _term(f.left), f.op, _term(f.right)
        if op in (">", ">="):
            l, rr, op = rr, l, {">": "<", ">=": "<="}[op]
        return f"({l} {op} {rr})"
    if isinstance(f, ast.Not):
        return f"(NOT {r(f.arg)})"
    if isinstance(f, ast.And):
        return f"({r(f.left)} AND {r(f.right)})"
    if isinstance(f, ast.Or):
        return f"({r(f.left)} OR {r(f.right)})"
    if isinstance(f, ast.Implies):
        return f"({r(f.left)} IMPLIES {r(f.right)})"
    if isinstance(f, ast.Iff):
        return f"({r(f.left)} EQUIV {r(f.right)})"
    if isinstance(f, ast.Prev):
        return f"(PREV[0,*) {r(f.arg)})"
    if isinstance(f, ast.Next):
        if next_bound is None:
            raise Unsupported("X needs a per-trace NEXT bound (next_bound)")
        return f"(NEXT[0,{next_bound}] {r(f.arg)})"
    if isinstance(f, ast.Since):
        return f"({r(f.left)} SINCE[0,*) {r(f.right)})"
    if isinstance(f, ast.TimedSince):
        return f"({r(f.left)} SINCE{_iv(f.low, f.high)} {r(f.right)})"
    if isinstance(f, ast.Once):
        return f"(ONCE[0,*) {r(f.arg)})"
    if isinstance(f, ast.TimedOnce):
        return f"(ONCE{_iv(f.low, f.high)} {r(f.arg)})"
    if isinstance(f, ast.Hist):
        return f"(PAST_ALWAYS[0,*) {r(f.arg)})"
    if isinstance(f, ast.TimedHist):
        return f"(PAST_ALWAYS{_iv(f.low, f.high)} {r(f.arg)})"
    if isinstance(f, ast.TimedEventually):
        return f"(EVENTUALLY{_iv(f.low, f.high)} {r(f.arg)})"
    if isinstance(f, ast.TimedAlways):
        return f"(ALWAYS{_iv(f.low, f.high)} {r(f.arg)})"
    if isinstance(f, ast.TimedUntil):
        return f"({r(f.left)} UNTIL{_iv(f.low, f.high)} {r(f.right)})"
    if isinstance(f, ast.Zince):
        # phi Z psi  ==  phi AND PREV (phi SINCE psi)
        return (f"({r(f.left)} AND (PREV[0,*) "
                f"({r(f.left)} SINCE[0,*) {r(f.right)})))")
    if isinstance(f, ast.Interval):
        # [phi,psi)  ==  (NOT psi) SINCE phi
        return f"((NOT {r(f.right)}) SINCE[0,*) {r(f.left)})"
    if isinstance(f, ast.Exists):
        return f"(EXISTS {f.var}. {r(f.arg)})"
    if isinstance(f, ast.Forall):
        return f"(FORALL {f.var}. {r(f.arg)})"
    if isinstance(f, ast.TimedZince):
        raise Unsupported("Z[a,b] has no MFOTL counterpart")
    raise Unsupported(type(f).__name__)


def _term(t) -> str:
    if isinstance(t, ast.Var):
        return t.name
    if isinstance(t, ast.Const):
        return f'"{t.value}"' if t.kind == "String" else str(t.value)
    if isinstance(t, ast.BinExpr):
        return f"({_term(t.left)} {t.op} {_term(t.right)})"
    if isinstance(t, ast.Neg):
        return f"(0 - {_term(t.arg)})"
    raise Unsupported(type(t).__name__)


# --- signature and log -------------------------------------------------------

def signature(spec, extra_preds=None) -> str:
    """MonPoly signature: every predicate with its argument sorts.  Undeclared
    predicates (which our parser allows) are declared from `extra_preds`, a
    {name: [sorts]} mapping."""
    out = {}
    for e in spec.events:
        out[e.name] = [SORTS[p.sort] for p in e.params]
    for name, sorts in (extra_preds or {}).items():
        out.setdefault(name, [SORTS.get(s, "string") for s in sorts])
    return "\n".join(
        f"{n}({','.join(f'x{i}:{s}' for i, s in enumerate(ss))})"
        for n, ss in sorted(out.items())) + "\n"


def to_log(events, times) -> str:
    """Our (event, timestamp) stream as a MonPoly log: one time point per
    event, its facts grouped under the timestamp."""
    lines = []
    for ev, ts in zip(events, times):
        facts = []
        for name, tuples in sorted(ev.items()):
            for tup in tuples:
                args = ",".join(_lit(a) for a in tup)
                facts.append(f"{name}({args})")
        lines.append(f"@{ts} " + " ".join(facts))
    return "\n".join(lines) + "\n"


def _lit(v) -> str:
    s = str(v)
    return s if re.fullmatch(r"-?\d+", s) else f'"{s}"'


# --- runner -------------------------------------------------------------------

def available() -> bool:
    return MONPOLY.exists()


def _run(args, timeout=60):
    env = dict(os.environ)
    return subprocess.run([str(MONPOLY)] + args, capture_output=True,
                          text=True, timeout=timeout, env=env)


def monitorable(sig_text, formula_text):
    """(is_monitorable, message) from MonPoly's own fragment check."""
    with tempfile.TemporaryDirectory() as d:
        sp, fp = Path(d) / "s.sig", Path(d) / "f.mfotl"
        sp.write_text(sig_text)
        fp.write_text(formula_text + "\n")
        r = _run(["-sig", str(sp), "-formula", str(fp), "-check"])
        out = r.stdout + r.stderr
        return ("is monitorable" in out and "NOT monitorable" not in out), out.strip()


def judgements(sig_text, formula_text, log_text, n_events, timeout=60):
    """(violated, satisfied, message): the positions MonPoly reports as
    violating (run with -negate) and as satisfying (run without).  Their
    union is MonPoly's *evaluation frontier*: with nested future operators
    outrunning its single appended maximal timestamp, trailing positions are
    never evaluated at all, and are in neither set."""
    v, msg = violations(sig_text, formula_text, log_text, n_events,
                        timeout, negate=True)
    if v is None:
        return None, None, msg
    s_, msg = violations(sig_text, formula_text, log_text, n_events,
                         timeout, negate=False)
    if s_ is None:
        return None, None, msg
    return v, s_, ""


def violations(sig_text, formula_text, log_text, n_events, timeout=60,
               negate=True):
    """The positions (1-based, as DejaVuMT counts them) at which MonPoly says
    the closed formula is violated.  Returns (set|None, message)."""
    with tempfile.TemporaryDirectory() as d:
        sp, fp, lp = Path(d) / "s.sig", Path(d) / "f.mfotl", Path(d) / "l.log"
        sp.write_text(sig_text)
        fp.write_text(formula_text + "\n")
        lp.write_text(log_text)
        try:
            args = ["-sig", str(sp), "-formula", str(fp), "-log", str(lp)]
            if negate:
                args.append("-negate")
            r = _run(args, timeout=timeout)
        except subprocess.TimeoutExpired:
            return None, "timeout"
        out = r.stdout
        err = r.stderr.strip()
        if "NOT monitorable" in out or "NOT monitorable" in err:
            return None, "not monitorable"
        if r.returncode != 0 or "ERROR" in err.upper():
            return None, (err or f"rc={r.returncode}")[:200]
        pos = set()
        for m in re.finditer(r"\(time point (\d+)\)", out):
            tp = int(m.group(1))
            if tp < n_events:          # ignore the appended maximal timestamp
                pos.add(tp + 1)        # MonPoly counts from 0, we from 1
        return pos, ""
