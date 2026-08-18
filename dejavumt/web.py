"""
Local web interface for DejaVuMT.

    python -m dejavumt.web [port]          (default port 5001)

or via the repo-root launcher `./start_web.sh [port]`.  Serves a one-page UI
(dejavumt/webui.html): spec and log editors, an examples browser, and the
monitor's results — the trace table and, per event, the annotated formula
trees of debug mode, rendered with colors.

The server binds to 127.0.0.1 only; it is a local tool, not a deployment.
Flask is an optional dependency:  pip install flask
"""
from __future__ import annotations

import csv
import html
import io
import sys
import time
from pathlib import Path

try:
    from flask import Flask, jsonify, request, Response
except ImportError:  # pragma: no cover
    print("The web interface needs Flask:  .venv/bin/pip install flask",
          file=sys.stderr)
    raise

from .parser import parse_spec
from .engine import Monitor


MAX_EVENTS = 5000       # per run
MAX_SECONDS = 60.0      # wall clock per run

app = Flask(__name__)

_ROOT = Path(__file__).resolve().parent.parent   # repo root (dev checkout)
_UI = Path(__file__).resolve().parent / "webui.html"


# --- helpers ---------------------------------------------------------------

_ANSI = {"\033[32m": '<span class="tv">',   # true / holds: green
         "\033[31m": '<span class="fv">',   # false / violated: red
         "\033[33m": '<span class="ov">',   # other: yellow
         "\033[0m": "</span>"}


def ansi_to_html(s: str) -> str:
    """Escape HTML, then map the three ANSI colors of render_tree to spans."""
    out = html.escape(s, quote=False)
    for code, tag in _ANSI.items():
        out = out.replace(code, tag)
    return out


def parse_log_text(text: str, timed: bool):
    """The CSV log as (event, ts) pairs (ts None when untimed) — the same
    format as dejavumt.log.read_events, but from a string."""
    for row in csv.reader(io.StringIO(text)):
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
            yield {name: [tuple(args)]}, None


def fact_str(event) -> str:
    ((pred, args),) = event.items()
    return pred + ("(" + ",".join(args[0]) + ")" if args[0] else "")


# --- endpoints -------------------------------------------------------------

@app.get("/")
def index() -> Response:
    return Response(_UI.read_text(), mimetype="text/html")


def _safe(relpath: str) -> Path:
    """Resolve a client-supplied path strictly inside the served root."""
    p = (_ROOT / relpath).resolve()
    if p != _ROOT and not p.is_relative_to(_ROOT):
        raise PermissionError(relpath)
    return p


@app.get("/fs")
def fs():
    """List a directory (relative to the served root): subdirectories and
    .qtl/.csv files.  Used by the in-page file browser."""
    rel = request.args.get("path", "").strip("/")
    try:
        d = _safe(rel)
        if not d.is_dir():
            raise OSError(rel)
        dirs, files = [], []
        for e in sorted(d.iterdir(), key=lambda e: e.name.lower()):
            if e.name.startswith("."):
                continue
            if e.is_dir():
                dirs.append(e.name)
            elif e.suffix in (".qtl", ".csv"):
                files.append(e.name)
        return jsonify({"path": rel,
                        "parent": None if not rel else str(Path(rel).parent)
                        if str(Path(rel).parent) != "." else "",
                        "dirs": dirs, "files": files})
    except (OSError, PermissionError):
        return jsonify({"error": "no such directory"}), 404


@app.get("/file")
def file_get():
    try:
        p = _safe(request.args.get("path", ""))
        return jsonify({"path": str(p.relative_to(_ROOT)),
                        "content": p.read_text()})
    except (OSError, PermissionError):
        return jsonify({"error": "no such file"}), 404


@app.post("/save")
def file_save():
    req = request.get_json(force=True)
    rel = (req.get("path") or "").strip()
    if not rel:
        return jsonify({"error": "no path given"}), 400
    try:
        p = _safe(rel)
        if p.suffix not in (".qtl", ".csv"):
            return jsonify({"error": "only .qtl and .csv files"}), 400
        if not p.parent.is_dir():
            return jsonify({"error": f"no such directory: {p.parent.name}/"}), 400
        p.write_text(req.get("content", ""))
        return jsonify({"saved": str(p.relative_to(_ROOT))})
    except PermissionError:
        return jsonify({"error": "path outside the served root"}), 403
    except OSError as e:
        return jsonify({"error": str(e)}), 400


@app.post("/run")
def run():
    req = request.get_json(force=True)
    spec_text = req.get("spec", "")
    log_text = req.get("log", "")
    solver = req.get("solver", "z3")
    debug = bool(req.get("debug", False))
    try:
        spec = parse_spec(spec_text)
        if not spec.properties:
            return jsonify({"error": "the specification declares no prop"})
        monitor = Monitor(spec, solver=solver)
    except Exception as e:
        return jsonify({"error": f"{type(e).__name__}: {e}"})
    for fm in monitor.formulas:
        if req.get("weak"):
            fm.weak = True
        elif req.get("strong"):
            fm.strong = True
        if req.get("gc"):
            fm.gc_period = 50
    events_out = []
    violations = []
    truncated = None
    t0 = time.monotonic()
    try:
        for nr, (event, ts) in enumerate(
                parse_log_text(log_text, monitor.timed), 1):
            if nr > MAX_EVENTS:
                truncated = f"stopped after {MAX_EVENTS} events"
                break
            if time.monotonic() - t0 > MAX_SECONDS:
                truncated = f"stopped after {MAX_SECONDS:.0f}s at event {nr - 1}"
                break
            monitor.step(event, ts)
            row = {"nr": nr, "fact": fact_str(event), "ts": ts,
                   "verdicts": {fm.name: None for fm in monitor.formulas}}
            if debug:
                row["trees"] = [
                    {"name": fm.name,
                     "html": ansi_to_html(fm.render_tree(
                         values=fm.pre, exported=fm.preval, color=True))}
                    for fm in monitor.formulas]
            events_out.append(row)
            # Verdicts resolved by this event, for this position or (with
            # future operators) an earlier one.
            for pos, name, holds in monitor.resolved:
                events_out[pos - 1]["verdicts"][name] = holds
                if not holds:
                    violations.append({"event": pos, "prop": name,
                                       "at": nr})
        for pos, name, holds in monitor.end():
            events_out[pos - 1]["verdicts"][name] = holds
            if not holds:
                violations.append({"event": pos, "prop": name, "at": None})
    except Exception as e:
        return jsonify({"error": f"at event {len(events_out) + 1}: "
                                 f"{type(e).__name__}: {e}"})
    return jsonify({
        "properties": [{"name": fm.name, "text": fm.text}
                       for fm in monitor.formulas],
        "solver": monitor.backend.name,
        "timed": monitor.timed,
        "future": monitor.future,
        "events": events_out,
        "violations": violations,
        "truncated": truncated,
    })


def main():
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 5001
    print(f"DejaVuMT web interface: http://localhost:{port}")
    app.run(host="127.0.0.1", port=port, debug=False)


if __name__ == "__main__":
    main()
