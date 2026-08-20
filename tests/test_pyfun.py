"""Tests for Python functions inside formulas (the spec's `python:` block).

A function is an uninterpreted SMT symbol whose graph is supplied lazily:
once an application's arguments become ground during evaluation (event
equalities make them so), the pure Python function is called (memoized)
and the application folds to its result.  No pre-phase: the property stays
in the formula.
"""
import pytest

from dejavumt import parse_spec, Monitor


def replay(spec_text, events, prop, timed=False, solver="z3"):
    m = Monitor(parse_spec(spec_text), solver=solver)
    got = {}
    for e in events:
        ev, ts = e if timed else (e, None)
        m.step(ev, ts)
        for pos, name, holds in m.resolved:
            if name == prop:
                got[pos] = holds
    for pos, name, holds in m.end():
        if name == prop:
            got[pos] = holds
    return m, got


SIZE_SPEC = """
python:
    def size(d: str) -> int:
        return len(d)
end
pred write(f: String, d: String)
prop q : Forall f . Forall d . write(f,d) -> size(d) < 5
"""


def test_int_function_in_relation():
    m, got = replay(SIZE_SPEC, [{"write": [("a", "abc")]},
                                {"write": [("a", "toolongtext")]},
                                {"other": [()]}], prop="q")
    assert got == {1: True, 2: False, 3: True}


def test_bool_function_as_atom():
    spec = """
    python:
        def risky(cmd: str) -> bool:
            return cmd in {"rm", "dd"}
    end
    pred run(cmd: String)
    prop r : Forall cmd . run(cmd) -> ! risky(cmd)
    """
    m, got = replay(spec, [{"run": [("ls",)]}, {"run": [("rm",)]}], prop="r")
    assert got == {1: True, 2: False}


def test_under_past_operator():
    """The grounded application is stored in a since-style state and keeps
    its value there."""
    spec = """
    python:
        def size(d: str) -> int:
            return len(d)
    end
    pred put(d: String)
    pred check()
    prop q : check -> P (Exists d . put(d) & size(d) > 3)
    """
    m, got = replay(spec, [{"put": [("ab",)]}, {"check": [()]},
                           {"put": [("abcdef",)]}, {"check": [()]}],
                    prop="q")
    assert got == {1: True, 2: False, 3: True, 4: True}


def test_with_future_operator():
    """A grounded value flows into a future obligation."""
    spec = """
    python:
        def half(n: int) -> int:
            return n // 2
    end
    pred req(n: Int)
    pred ack(n: Int)
    prop q : Forall n . req(n) -> F (Exists m . ack(m) & m = half(n))
    """
    m, got = replay(spec, [{"req": [(10,)]}, {"ack": [(5,)]}], prop="q")
    assert got[1] is True
    m, got = replay(spec, [{"req": [(10,)]}, {"ack": [(4,)]}], prop="q")
    assert got[1] is False


def test_memoization():
    spec = """
    python:
        calls = []
        def probe(d: str) -> int:
            calls.append(d)
            return len(d)
    end
    pred put(d: String)
    prop q : Forall d . put(d) -> probe(d) >= 0
    """
    m, got = replay(spec, [{"put": [("x",)]}, {"put": [("x",)]},
                           {"put": [("x",)]}], prop="q")
    assert all(got.values())
    # Same argument, one call.
    assert ("probe", ("x",)) in m.formulas[0].pycache


def test_arithmetic_argument():
    spec = """
    python:
        def double(n: int) -> int:
            return 2 * n
    end
    pred p(n: Int)
    prop q : Forall n . p(n) -> double(n + 1) > n
    """
    m, got = replay(spec, [{"p": [(3,)]}], prop="q")
    assert got == {1: True}


def test_residual_application_raises():
    spec = """
    python:
        def size(d: str) -> int:
            return len(d)
    end
    pred p()
    prop q : Forall d . size(d) > 0
    """
    m = Monitor(parse_spec(spec))
    with pytest.raises(ValueError, match="never became ground"):
        m.step({"p": [()]})


def test_missing_annotation_rejected():
    spec = """
    python:
        def size(d) -> int:
            return len(d)
    end
    pred p()
    prop q : p
    """
    with pytest.raises(ValueError, match="type annotation"):
        Monitor(parse_spec(spec))


def test_name_collision_rejected():
    spec = """
    python:
        def put(d: str) -> bool:
            return True
    end
    pred put(d: String)
    prop q : put("x")
    """
    with pytest.raises(ValueError, match="collides"):
        Monitor(parse_spec(spec))


def test_non_bool_atom_rejected():
    spec = """
    python:
        def size(d: str) -> int:
            return len(d)
    end
    pred p(d: String)
    prop q : Forall d . p(d) -> size(d)
    """
    with pytest.raises(ValueError, match="only bool functions"):
        Monitor(parse_spec(spec))


def test_helpers_and_imports_usable():
    spec = """
    python:
        import re
        def digits(s: str) -> int:
            m = re.search(r"[0-9]+", s)
            return int(m.group(0)) if m else -1
    end
    pred msg(s: String)
    prop q : Forall s . msg(s) -> digits(s) >= 0
    """
    m, got = replay(spec, [{"msg": [("id 42",)]}, {"msg": [("none",)]}],
                    prop="q")
    assert got == {1: True, 2: False}


def test_cvc5():
    m, got = replay(SIZE_SPEC, [{"write": [("a", "abc")]},
                                {"write": [("a", "toolongtext")]}],
                    prop="q", solver="cvc5")
    assert got == {1: True, 2: False}
