"""
Reading DejaVu-style CSV logs.

Each line is one event of the form

    predname,arg1,arg2,...

with no leading spaces, e.g.

    open,a,read

producing the event {"open": [("a", "read")]}.  Argument values are kept as raw
strings here; the engine coerces them to each predicate parameter's declared
sort.
"""
from __future__ import annotations

import csv
from typing import Dict, Iterator, List, Tuple


def read_events(path: str, timed: bool = False):
    """Yield events from a CSV log.  Untimed: one event dict per line.  Timed
    (`timed=True`, for specs using timed operators): the last column of each
    line is the event's absolute integer timestamp, as in DejaVu, and the
    yield is a pair (event, timestamp)."""
    with open(path, newline="") as f:
        for row in csv.reader(f):
            if not row or (len(row) == 1 and row[0].strip() == ""):
                continue
            name = row[0].strip()
            args = [a.strip() for a in row[1:]]
            if timed:
                if not args:
                    raise ValueError(
                        f"timed log line lacks a timestamp column: {row}")
                yield {name: [tuple(args[:-1])]}, int(args[-1])
            else:
                yield {name: [tuple(args)]}
