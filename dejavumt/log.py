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


def read_events(path: str) -> Iterator[Dict[str, List[Tuple[str, ...]]]]:
    with open(path, newline="") as f:
        for row in csv.reader(f):
            if not row or (len(row) == 1 and row[0].strip() == ""):
                continue
            name = row[0].strip()
            args = tuple(a.strip() for a in row[1:])
            yield {name: [args]}
