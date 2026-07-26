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


def test_fs_browse_and_read(client):
    root = client.get("/fs").get_json()
    assert "examples" in root["dirs"] and root["parent"] is None
    d = client.get("/fs?path=examples/timed").get_json()
    assert "prop.qtl" in d["files"] and "log.csv" in d["files"]
    assert d["parent"] == "examples"
    f = client.get("/file?path=examples/timed/prop.qtl").get_json()
    assert "P[<=5]" in f["content"]


def test_fs_path_traversal_rejected(client):
    assert client.get("/fs?path=../..").status_code == 404
    assert client.get("/file?path=../../etc/passwd").status_code == 404
    r = client.post("/save", json={"path": "../evil.qtl", "content": "x"})
    assert r.status_code == 403


def test_save_roundtrip(client, tmp_path):
    import dejavumt.web as web
    old = web._ROOT
    web._ROOT = tmp_path
    try:
        r = client.post("/save", json={"path": "s.qtl", "content": "prop p : a"})
        assert r.get_json()["saved"] == "s.qtl"
        assert (tmp_path / "s.qtl").read_text() == "prop p : a"
        # non-.qtl/.csv rejected
        assert client.post("/save", json={"path": "x.py", "content": ""}
                           ).status_code == 400
    finally:
        web._ROOT = old
