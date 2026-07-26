"""Tests for the web interface (skipped when Flask is not installed)."""
import pytest

flask = pytest.importorskip("flask")

from dejavumt.web import app  # noqa: E402


@pytest.fixture()
def client():
    app.config.update(TESTING=True)
    return app.test_client()


def run(client, **body):
    r = client.post("/run", json=body)
    assert r.status_code == 200
    return r.get_json()


ACCESS_SPEC = """
pred grant(r: String)
pred revoke(r: String)
pred use(r: String)
prop access : Forall r . use(r) -> (!revoke(r)) S grant(r)
"""
ACCESS_LOG = "grant,a\nuse,a\nrevoke,a\nuse,a\n"

TIMED_SPEC = "pred p(x: String)\nprop q : Exists x . P[<=5] p(x)\n"
TIMED_LOG = "p,a,0\np,b,3\nr,7\nr,10\n"


def test_untimed_run(client):
    res = run(client, spec=ACCESS_SPEC, log=ACCESS_LOG)
    assert "error" not in res
    assert not res["timed"]
    assert [v["event"] for v in res["violations"]] == [4]
    assert len(res["events"]) == 4
    assert res["events"][3]["verdicts"]["access"] is False


def test_timed_run_with_trees(client):
    res = run(client, spec=TIMED_SPEC, log=TIMED_LOG, debug=True)
    assert res["timed"]
    assert [v["event"] for v in res["violations"]] == [4]
    assert res["events"][0]["ts"] == 0
    tree = res["events"][0]["trees"][0]["html"]
    # colored spans present, ANSI codes gone, records visible
    assert '<span class="' in tree and "\033" not in tree
    assert "_t" in tree and "value:" in tree


def test_parse_error(client):
    res = run(client, spec="prop p : P[5,3] a", log="a,1\n")
    assert "error" in res


def test_examples_listing(client):
    names = client.get("/examples").get_json()
    assert "timed" in names
    d = client.get("/examples/timed").get_json()
    assert "P[<=5]" in d["spec"] and "open" in d["log"]


def test_example_path_traversal_rejected(client):
    r = client.get("/examples/..%2F..%2Fetc")
    assert r.status_code == 404
