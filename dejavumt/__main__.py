"""
Command-line entry point for DejaVuMT.

    python -m dejavumt <specfile> <logfile>

Generates no intermediate code (unlike DejaVu): it parses the spec, builds an
SMT-backed monitor, and streams the CSV log through it, reporting violations.
"""
from __future__ import annotations

import sys

from .parser import parse_file
from .engine import Monitor
from .log import read_events, read_jsonl


BANNER = r"""
 /$$$$$$$                          /$$    /$$                 /$$      /$$ /$$$$$$$$
| $$__  $$                        | $$   | $$                | $$$    /$$$|__  $$__/
| $$  \ $$  /$$$$$$  /$$  /$$$$$$ | $$   | $$ /$$   /$$      | $$$$  /$$$$   | $$
| $$  | $$ /$$__  $$|__/ |____  $$|  $$ / $$/| $$  | $$      | $$ $$/$$ $$   | $$
| $$  | $$| $$$$$$$$ /$$  /$$$$$$$ \  $$ $$/ | $$  | $$      | $$  $$$| $$   | $$
| $$  | $$| $$_____/| $$ /$$__  $$  \  $$$/  | $$  | $$      | $$\  $ | $$   | $$
| $$$$$$$/|  $$$$$$$| $$|  $$$$$$$   \  $/   |  $$$$$$/      | $$ \/  | $$   | $$
|_______/  \_______/| $$ \_______/    \_/     \______/       |__/     |__/   |__/
               /$$  | $$
              |  $$$$$$/
               \______/
"""


def _boxed(text: str) -> str:
    lines = [ln.rstrip() for ln in text.strip("\n").split("\n")]
    width = max(len(ln) for ln in lines)
    top = "╭" + "─" * (width + 2) + "╮"
    bot = "╰" + "─" * (width + 2) + "╯"
    body = [f"│ {ln.ljust(width)} │" for ln in lines]
    return "\n".join([top] + body + [bot])


def _fact(event) -> str:
    ((pred, args),) = event.items()
    return pred + ("(" + ",".join(args[0]) + ")" if args[0] else "")


def _verdict_tag(holds) -> str:
    if isinstance(holds, str):
        # Parametric constraint verdict (already rendered by the backend).
        s = f"holds iff {holds}"
        return f"\033[33m{s}\033[0m" if sys.stdout.isatty() else s
    if not sys.stdout.isatty():
        return "holds" if holds else "VIOLATED"
    return "\033[32mholds\033[0m" if holds else "\033[31mVIOLATED\033[0m"


GC_PERIOD = 50  # default period for the `gc` flag


def run(specfile: str, logfile: str, debug: bool = False, trace: bool = False,
        strong: bool = False, weak: bool = False, solver: str = "z3",
        gc: bool = False, json_out: bool = False, timed: bool = False) -> int:
    spec = parse_file(specfile)
    monitor = Monitor(spec, solver=solver)
    # The log carries timestamps when the spec is timed, when the `timed`
    # flag says so, or when the filename follows DejaVu's `.timed.`
    # convention — so a timed log also works with an untimed spec.
    log_timed = (monitor.timed or timed
                 or ".timed." in logfile.rsplit("/", 1)[-1])
    if weak:
        for fm in monitor.formulas:
            fm.weak = True
    elif strong:
        for fm in monitor.formulas:
            fm.strong = True
    if gc:
        for fm in monitor.formulas:
            fm.gc_period = GC_PERIOD
    banner = _boxed(BANNER)
    if sys.stdout.isatty():
        banner = "\033[36m" + banner + "\033[0m"  # cyan
    print("\n\n\n" + banner + "\n")
    print(f"Solver: {monitor.backend.name}"
          + (f"   (GC every {GC_PERIOD} events)" if gc else "")
          + ("   (timed: last log column is the timestamp)" if log_timed
             else "")
          + ("   (future operators: verdicts may be reported late)"
             if monitor.future else ""))
    if strong and not monitor.backend.supports_strong:
        print(f"(note: 'strong' is not supported by {monitor.backend.name}; ignored)")
    print(f"Monitoring {len(monitor.formulas)} property(ies):\n")
    for fm in monitor.formulas:
        print(f"  {fm.name} : {fm.text}"
              + ("   (anchored: judged at position 1 only)"
                 if fm.anchored else ""))
    print()

    if debug:
        print("event definitions:\n")
        if spec.events:
            for e in spec.events:
                params = ", ".join(f"{p.name}: {p.sort}" for p in e.params)
                print(f"  {e.name}({params})" if e.params else f"  {e.name}")
        else:
            print("  (none declared; predicate arguments default to String)")
        for fm in monitor.formulas:
            print(f"\n===== initial state =====\n")
            # pre/now are all false before any event.
            print(fm.render_tree(values=fm.pre, exported=fm.preval,
                                 color=sys.stdout.isatty()))

    violations = 0
    line_nr = 0
    facts = {}            # position -> displayed event
    verdicts_at = {}      # (position, property) -> holds
    fms = {fm.name: fm for fm in monitor.formulas}

    def _wit(name, pos):
        w = fms[name].witnesses.get(pos)
        if not w:
            return ""
        return "  [" + ", ".join(f"{k}={v}" for k, v in w.items()) + "]"
    if logfile.endswith((".jsonl", ".ndjson", ".json")):
        sig = {e.name: [p.name for p in e.params] for e in spec.events}
        stream = read_jsonl(logfile, timed=log_timed, signature=sig)
    else:
        stream = read_events(logfile, timed=log_timed)
    for item in stream:
        event, ts = item if log_timed else (item, None)
        line_nr += 1
        facts[line_nr] = _fact(event) + (f" @ {ts}" if log_timed else "")
        verdicts = monitor.step(event, ts)
        if debug:
            at = f" @ {ts}" if log_timed else ""
            print(f"\n----- event {line_nr}: {_fact(event)}{at} -----\n")
            for fm in monitor.formulas:
                # After step(), fm.pre holds the states just computed and
                # fm.preval the exported values (differing at timed nodes).
                print(fm.render_tree(values=fm.pre, exported=fm.preval,
                                     color=sys.stdout.isatty()))
                if fm.pending:
                    # The notebook: positions still awaiting their verdict.
                    # (The root's annotation above is its value assuming
                    # nothing further arrives, not a verdict.)
                    poss = ", ".join(str(o["pos"]) for o in fm.pending)
                    print(f"   pending obligations for position(s): {poss}")
        for pos, name, holds in monitor.resolved:
            verdicts_at[(pos, name)] = holds
            if holds is False:
                violations += 1
                if not debug and not trace:
                    late = "" if pos == line_nr else f" (determined at event {line_nr})"
                    print(f"*** Violation of {name} at event {pos}: "
                          f"{facts[pos]}{late}{_wit(name, pos)}")
            elif holds is not True and not debug and not trace:
                print(f"--- {name} at event {pos}: {facts[pos]} holds iff "
                      f"{monitor.backend.to_str(holds)}")
    # Close every remaining window: with future operators some positions are
    # still awaiting their verdict when the trace ends.
    for pos, name, holds in monitor.end():
        verdicts_at[(pos, name)] = holds
        if holds is False:
            violations += 1
            if not debug and not trace:
                print(f"*** Violation of {name} at event {pos}: "
                      f"{facts[pos]} (determined at end of trace)"
                      f"{_wit(name, pos)}")
        elif holds is not True and not debug and not trace:
            print(f"--- {name} at event {pos}: {facts[pos]} holds iff "
                  f"{monitor.backend.to_str(holds)} (determined at end of trace)")

    if trace:
        print("\n===== trace =====\n" if debug else "")

        def tag(v):
            return _verdict_tag(v if isinstance(v, bool)
                                else monitor.backend.to_str(v))

        def cell(fm, pos):
            if (pos, fm.name) in verdicts_at:
                return f"{fm.name}: {tag(verdicts_at[(pos, fm.name)])}"
            if fm.anchored:
                return f"{fm.name}: -"     # anchored: only position 1 judged
            return f"{fm.name}: pending"

        for pos in range(1, line_nr + 1):
            tags = "   ".join(cell(fm, pos) for fm in monitor.formulas)
            print(f"{pos:>5}  {facts[pos]:<28}  {tags}")
    # Parametric properties: report the feasible region -- the constraint on
    # the parameters under which every position of the trace holds.
    for fm in monitor.formulas:
        if fm.params:
            print(f"\nParametric verdict for {fm.name}: holds iff "
                  f"{monitor.backend.to_str(fm.region)}")
    # Anchored properties: one verdict for the whole trace.
    for fm in monitor.formulas:
        if fm.anchored:
            v = verdicts_at.get((1, fm.name))
            if v is True:
                tag = "holds"
            elif v is False:
                tag = "VIOLATED" + _wit(fm.name, 1)
            elif v is None:
                tag = "pending"
            else:
                tag = f"holds iff {monitor.backend.to_str(v)}"
            print(f"\nAnchored verdict for {fm.name}: {tag}")
    if json_out:
        import json as _json

        def jv(h):
            return (h if isinstance(h, (bool, type(None)))
                    else monitor.backend.to_str(h))

        def jsafe(v):
            return v if isinstance(v, (bool, int, float, str)) else str(v)

        results = {
            "spec": specfile, "log": logfile,
            "solver": monitor.backend.name, "timed": monitor.timed,
            "events": line_nr,
            "properties": {
                fm.name: {
                    "text": fm.text,
                    "anchored": fm.anchored,
                    "verdicts": [jv(verdicts_at.get((i + 1, fm.name)))
                                 for i in range(line_nr)],
                    "violations": [
                        {"pos": p, "event": facts[p],
                         "witness": fm.witnesses.get(p)}
                        for (p, n2), h in sorted(verdicts_at.items())
                        if n2 == fm.name and h is False],
                    "region": (monitor.backend.to_str(fm.region)
                               if fm.params else None),
                } for fm in monitor.formulas},
            "states": {k: jsafe(v) for k, v in monitor.states.items()},
        }
        out_path = logfile + ".results.json"
        with open(out_path, "w") as f:
            _json.dump(results, f, indent=1)
        print(f"\nResults written to {out_path}")
    print(f"\nProcessed {line_nr} events, {violations} violation(s).")
    return 1 if violations else 0


def main() -> None:
    flags = {"debug", "--debug", "trace", "--trace",
             "strong", "--strong", "weak", "--weak", "z3", "--z3",
             "cvc5", "--cvc5", "gc", "--gc", "json", "--json", "timed", "--timed"}
    args = [a for a in sys.argv[1:] if a not in flags]
    chosen = {a.lstrip("-") for a in sys.argv[1:] if a in flags}
    if len(args) != 2:
        print("usage: python -m dejavumt <specfile> <logfile> "
              "[trace] [debug] [strong|weak] [z3|cvc5] [gc] [json] [timed]")
        sys.exit(2)
    solver = "cvc5" if "cvc5" in chosen else "z3"
    sys.exit(run(args[0], args[1], debug="debug" in chosen,
                 trace="trace" in chosen, strong="strong" in chosen,
                 weak="weak" in chosen, solver=solver, gc="gc" in chosen,
                 json_out="json" in chosen, timed="timed" in chosen))


if __name__ == "__main__":
    main()
