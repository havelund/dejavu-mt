#!/bin/bash
# Start (or restart) the DejaVuMT web interface.
#
#     ./start_web.sh [port]        default port: 5001
#
# Patterned on tasksat's start_web.sh: kill any running instance, launch the
# server in the background, verify it came up, print the URL.

cd "$(dirname "$0")" || exit 1
PORT=${1:-5001}
PY=.venv/bin/python
[ -x "$PY" ] || PY=python3

# Stop any existing instance.
pkill -f "dejavumt.web" 2>/dev/null && sleep 1

if ! "$PY" -c "import flask" 2>/dev/null; then
    echo "Flask is not installed.  Run:  .venv/bin/pip install flask"
    exit 1
fi

"$PY" -m dejavumt.web "$PORT" > /tmp/dejavumt_web.log 2>&1 &
PID=$!
sleep 1.5

if kill -0 "$PID" 2>/dev/null; then
    echo "DejaVuMT web interface running:  http://localhost:$PORT   (pid $PID)"
    echo "Log: /tmp/dejavumt_web.log"
else
    echo "Server failed to start; log follows:"
    cat /tmp/dejavumt_web.log
    exit 1
fi
