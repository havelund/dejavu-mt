"""End-to-end tests for the DejaVuMT slice-1 engine."""
from dejavumt import parse_spec, Monitor
from dejavumt.ast import Forall, Hist, Since, Zince


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


# --- string contains (description substring matching) ------------------------

def test_contains_string_substring():
    # A 2-arg fact E(component, description); `contains` tests the description.
    spec = """
    pred MODE_CHANGED(c: String, d: String)
    prop no_auto : Forall c . Forall d . !(MODE_CHANGED(c, d) & d contains "AUTOMATIC")
    """
    events = [
        {"MODE_CHANGED": [("ctrl", "Control mode changed to MANUAL")]},     # ok
        {"MODE_CHANGED": [("ctrl", "Control mode changed to AUTOMATIC")]},  # violation
    ]
    assert violations(spec, events, "no_auto") == [2]


def test_contains_is_substring_not_equality():
    # `contains` matches a substring, not the whole string.
    spec = """
    pred LOG(c: String, d: String)
    prop p : Forall c . Forall d . LOG(c, d) -> d contains "fault"
    """
    events = [
        {"LOG": [("x", "actuator fault detected")]},   # substring present -> ok
        {"LOG": [("x", "all nominal")]},                # no "fault" -> violation
    ]
    assert violations(spec, events, "p") == [2]


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


def test_arith_multiply():
    spec = """
    pred a(x: Int)
    pred b(y: Int)
    prop p : Forall x . Forall y . a(x) & b(y) -> y = x * 2
    """
    events = [
        {"a": [("1",)], "b": [("2",)]},   # 2 = 1*2 -> holds
        {"a": [("3",)], "b": [("5",)]},   # 5 != 3*2 -> violation
    ]
    assert violations(spec, events, "p") == [2]


def test_arith_minus_and_negative():
    spec = """
    pred v(x: Int)
    prop p : Forall x . v(x) -> x - 1 >= -1
    """
    events = [
        {"v": [("0",)]},     # 0-1 = -1 >= -1 -> holds
        {"v": [("-5",)]},    # -5-1 = -6 >= -1 -> violation
    ]
    assert violations(spec, events, "p") == [2]


def test_arith_no_space_parses_and_runs():
    # x-1 without surrounding spaces must parse and evaluate.
    spec = """
    pred v(x: Int)
    prop p : Forall x . v(x) -> x-1 < x
    """
    events = [{"v": [("7",)]}]
    assert violations(spec, events, "p") == []


def test_arity_sensitive_matching():
    # A 0-ary atom must not be triggered by a fact with arguments (DejaVu
    # matches by name AND arity).  From DejaVu test26_propositional/spec2.
    spec = """
    prop p : access -> [login,logout)
    """
    events = [
        {"login": [("klaus",)]},    # 1-ary: must NOT match 0-ary 'login'
        {"access": [()]},           # 0-ary access: matches; login never seen
    ]
    assert violations(spec, events, "p") == [2]


def test_undeclared_predicate_numeric_inference():
    # x is inferred Int from the relation; the undeclared predicate's log
    # values must then be coerced to Int, not String.  From DejaVu test17.
    spec = """
    prop p : Forall x . (a(x) -> x < 5)
    """
    events = [{"a": [("1",)]}, {"a": [("7",)]}, {"a": [("3",)]}]
    assert violations(spec, events, "p") == [2]


def test_untyped_order_relation_is_numeric():
    # DejaVu compares order relations numerically; untyped variables in an
    # order relation must default to Int, not String (lexicographic would
    # wrongly flag 50 < 110).  From DejaVu examples/auction/prop1 + log1.
    spec = """
    prop p : Forall i . Forall a1 . Forall a2 . @ P bid(i,a1) & bid(i,a2) -> a1 < a2
    """
    events = [
        {"bid": [("hat", "50")]},
        {"bid": [("hat", "110")]},        # 50 < 110 numerically: ok
        {"bid": [("painting", "1000")]},
        {"bid": [("painting", "900")]},   # 1000 < 900 false: violation
        {"bid": [("painting", "1850")]},  # 900,1000 < 1850: ok (lex would flag)
    ]
    assert violations(spec, events, "p") == [4]


def test_once_and_hist():
    spec = """
    pred p(x: Int)
    prop q : Forall x . p(x) -> P p(x)
    """
    events = [{"p": [("1",)]}, {"p": [("2",)]}]
    # p(x) -> P p(x) is always true (P includes now), so no violations.
    assert violations(spec, events, "q") == []


# --- operator vs. ALLCAPS-identifier lexing ----------------------------------
# Regression: the past-time operators S/Z/P/H are single uppercase letters. With
# a dynamic (Earley) lexer and no word boundary they matched the HEAD of an
# ALLCAPS predicate name — e.g. "H" in HEATER_TURNED_ON, splitting it into
# H + EATER_TURNED_ON — so verdicts silently referred to the wrong fact. Every
# predicate below is chosen to START with an operator letter (P/H/S/Z) so a
# regression re-splits it. All-lowercase specs (used elsewhere) never hit this.

def test_once_does_not_split_H_prefixed_name():
    # "X may only happen if Y happened before"  ==  X(c) -> P Y(c)
    spec = """
    pred AUTO_TO_MANUAL_ON_FAULT(c: String)
    pred HEATER_TURNED_ON(c: String)
    prop p : Forall c . AUTO_TO_MANUAL_ON_FAULT(c) -> P HEATER_TURNED_ON(c)
    """
    events = [
        {"HEATER_TURNED_ON": [("ctrl",)]},
        {"AUTO_TO_MANUAL_ON_FAULT": [("ctrl",)]},   # prior ON for ctrl -> ok
        {"AUTO_TO_MANUAL_ON_FAULT": [("other",)]},  # no prior ON -> violation
    ]
    assert violations(spec, events, "p") == [3]


def test_hist_does_not_split_H_prefixed_name():
    # H (historically) applied to an H-prefixed name must keep the name whole.
    spec = "pred HEALTHY(c: String)\nprop p : Forall c . H HEALTHY(c)\n"
    body = parse_spec(spec).properties[0].body
    assert isinstance(body, Forall) and isinstance(body.arg, Hist)
    assert body.arg.arg.name == "HEALTHY"  # not "EALTHY"


def test_since_does_not_split_S_prefixed_name():
    # Binary S (since) between two S-prefixed names — neither may be split.
    spec = ("pred SAFE(c: String)\npred STARTED(c: String)\n"
            "prop p : Forall c . SAFE(c) S STARTED(c)\n")
    body = parse_spec(spec).properties[0].body
    assert isinstance(body.arg, Since)
    assert body.arg.left.name == "SAFE" and body.arg.right.name == "STARTED"


def test_zince_does_not_split_Z_and_P_prefixed_names():
    # Binary Z (zince) between a Z-prefixed and a P-prefixed name.
    spec = ("pred ZONE_CLEAR(c: String)\npred PRIMED(c: String)\n"
            "prop p : Forall c . ZONE_CLEAR(c) Z PRIMED(c)\n")
    body = parse_spec(spec).properties[0].body
    assert isinstance(body.arg, Zince)
    assert body.arg.left.name == "ZONE_CLEAR" and body.arg.right.name == "PRIMED"
