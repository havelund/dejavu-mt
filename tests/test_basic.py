"""End-to-end tests for the DejaVuMT slice-1 engine."""
from dejavumt import parse_spec, Monitor


def verdicts(spec_text, events):
    """Run a spec over a list of events; return list of per-event verdict dicts."""
    m = Monitor(parse_spec(spec_text))
    return [m.step(ev) for ev in events]


def violations(spec_text, events, prop):
    return [i + 1 for i, v in enumerate(verdicts(spec_text, events)) if not v[prop]]


# --- propositional / equality ------------------------------------------------

def test_file_open_close():
    spec = """
    pred close(f: String)
    pred open(f: String, m: String)
    prop file : Forall f . close(f) -> Exists m . @ [open(f,m),close(f))
    """
    events = [
        {"open": [("a", "read")]},
        {"close": [("a",)]},
        {"close": [("b",)]},      # b never opened -> violation
        {"open": [("c", "write")]},
        {"open": [("c", "read")]},
        {"close": [("c",)]},
    ]
    assert violations(spec, events, "file") == [3]


# --- typed arithmetic (the SMT payoff) --------------------------------------

def test_auction_bids_increase():
    spec = """
    pred bid(i: String, a: Int)
    prop p : Forall i . Forall a1 . Forall a2 . @ P bid(i,a1) & bid(i,a2) -> a1 < a2
    """
    events = [
        {"bid": [("chair", "700")]},
        {"bid": [("chair", "800")]},
        {"bid": [("chair", "650")]},   # 650 < earlier 700/800 -> violation
        {"bid": [("table", "100")]},
    ]
    assert violations(spec, events, "p") == [3]


# --- macros ------------------------------------------------------------------

def test_access_with_macros():
    spec = """
    pred login(u: String)
    pred logout(u: String)
    pred open(f: String)
    pred close(f: String)
    pred access(u: String, f: String)

    pred loggedIn(u) = [login(u),logout(u))
    pred opened(f)   = [open(f),close(f))

    prop access : Forall u . Forall f . access(u,f) -> loggedIn(u) & opened(f)
    """
    events = [
        {"login": [("alice",)]},
        {"open": [("data",)]},
        {"access": [("alice", "data")]},   # ok: logged in and file open
        {"logout": [("alice",)]},
        {"access": [("alice", "data")]},   # alice logged out -> violation
    ]
    assert violations(spec, events, "access") == [5]


# --- once / historically -----------------------------------------------------

def test_demo_grant_revoke_since():
    # A resource may be used only when granted and not revoked since.
    spec = """
    pred grant(r: String)
    pred revoke(r: String)
    pred use(r: String)
    prop access : Forall r . use(r) -> (!revoke(r)) S grant(r)
    """
    events = [
        {"grant": [("a",)]},
        {"use": [("a",)]},
        {"grant": [("b",)]},
        {"use": [("b",)]},
        {"revoke": [("a",)]},
        {"use": [("a",)]},     # a was revoked -> violation
        {"grant": [("a",)]},
        {"use": [("a",)]},
        {"use": [("b",)]},
        {"revoke": [("b",)]},
    ]
    assert violations(spec, events, "access") == [6]


def test_once_and_hist():
    spec = """
    pred p(x: Int)
    prop q : Forall x . p(x) -> P p(x)
    """
    events = [{"p": [("1",)]}, {"p": [("2",)]}]
    # p(x) -> P p(x) is always true (P includes now), so no violations.
    assert violations(spec, events, "q") == []
