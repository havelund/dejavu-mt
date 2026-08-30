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
import json
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


def read_jsonl(path: str, timed: bool = False, signature=None):
    """Yield events from a JSONL log: one JSON object per line,

        {"name": "open", "f": "data.txt", "m": "w", "time": 3}

    Fields are matched BY NAME to the predicate's declared parameters
    (`signature`: {predicate: [param names]}); for undeclared predicates the
    object's own field order is used.  A missing declared field is an
    error; extra fields are ignored.  For timed specs the integer field
    "time" is the timestamp."""
    signature = signature or {}
    with open(path) as f:
        for nr, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{nr}: bad JSON: {exc}") from exc
            if not isinstance(obj, dict) or "name" not in obj:
                raise ValueError(
                    f"{path}:{nr}: expected an object with a \"name\" field")
            name = obj["name"]
            params = signature.get(name)
            if params is None:
                args = tuple(v for k, v in obj.items()
                             if k not in ("name", "time"))
            else:
                missing = [p for p in params if p not in obj]
                if missing:
                    raise ValueError(
                        f"{path}:{nr}: {name}: missing field(s) "
                        f"{', '.join(missing)}")
                args = tuple(obj[p] for p in params)
            if timed:
                if "time" not in obj:
                    raise ValueError(
                        f"{path}:{nr}: timed spec, but no \"time\" field")
                yield {name: [args]}, int(obj["time"])
            else:
                yield {name: [args]}
