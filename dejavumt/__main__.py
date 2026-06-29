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
from .log import read_events


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


def _verdict_tag(holds: bool) -> str:
    if not sys.stdout.isatty():
        return "holds" if holds else "VIOLATED"
    return "\033[32mholds\033[0m" if holds else "\033[31mVIOLATED\033[0m"


def run(specfile: str, logfile: str, debug: bool = False, trace: bool = False,
        strong: bool = False) -> int:
    spec = parse_file(specfile)
    monitor = Monitor(spec)
    if strong:
        for fm in monitor.formulas:
            fm.strong = True
    banner = _boxed(BANNER)
    if sys.stdout.isatty():
        banner = "\033[36m" + banner + "\033[0m"  # cyan
    print("\n\n\n" + banner + "\n")
    print(f"Monitoring {len(monitor.formulas)} property(ies):\n")
    for fm in monitor.formulas:
        print(f"  {fm.name} : {fm.text}")
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
            print(f"\n===== property {fm.name} =====\n")
            print(fm.render_tree())

    violations = 0
    line_nr = 0
    trace_lines = []
    for event in read_events(logfile):
        line_nr += 1
        verdicts = monitor.step(event)
        if debug:
            print(f"\n----- event {line_nr}: {_fact(event)} -----\n")
        if trace:
            tags = "   ".join(f"{fm.name}: {_verdict_tag(verdicts[fm.name])}"
                              for fm in monitor.formulas)
            line = f"{line_nr:>5}  {_fact(event):<28}  {tags}"
            # With debug, defer the trace to a contiguous block so it is not
            # scattered between the per-event formula trees.
            if debug:
                trace_lines.append(line)
            else:
                print(line)
        if debug:
            for fm in monitor.formulas:
                # After step(), fm.pre holds the now-values just computed.
                print(fm.render_tree(values=fm.pre, color=sys.stdout.isatty()))
        for name, holds in verdicts.items():
            if not holds:
                violations += 1
                if not debug and not trace:
                    print(f"*** Violation of {name} at event {line_nr}: {_fact(event)}")

    if trace and debug:
        print("\n===== trace =====\n")
        print("\n".join(trace_lines))
    print(f"\nProcessed {line_nr} events, {violations} violation(s).")
    return 1 if violations else 0


def main() -> None:
    flags = {"debug", "--debug", "trace", "--trace", "strong", "--strong"}
    args = [a for a in sys.argv[1:] if a not in flags]
    chosen = {a.lstrip("-") for a in sys.argv[1:] if a in flags}
    if len(args) != 2:
        print("usage: python -m dejavumt <specfile> <logfile> [trace] [debug] [strong]")
        sys.exit(2)
    sys.exit(run(args[0], args[1], debug="debug" in chosen,
                 trace="trace" in chosen, strong="strong" in chosen))


if __name__ == "__main__":
    main()
