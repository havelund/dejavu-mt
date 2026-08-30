"""Tests for JSONL log input: one JSON object per line, fields matched by
name to declared predicate parameters; "time" is the timestamp for timed
specs.
"""
import pytest

from dejavumt import parse_spec, Monitor
from dejavumt.log import read_jsonl


SPEC = """
pred open(f: String, m: String)
pred write(f: String, d: String)
prop q : Forall f . Forall d . write(f,d) ->
    (Exists m . P open(f, m))
"""


def run(spec_text, jsonl_text, tmp_path, timed=False):
    spec = parse_spec(spec_text)
    m = Monitor(spec)
    p = tmp_path / "log.jsonl"
    p.write_text(jsonl_text)
    sig = {e.name: [q.name for q in e.params] for e in spec.events}
    verdicts = []
    for item in read_jsonl(str(p), timed=timed, signature=sig):
        ev, ts = item if timed else (item, None)
        out = m.step(ev, ts)
        verdicts.append(list(out.values())[0])
    m.end()
    return m, verdicts


def test_fields_matched_by_name(tmp_path):
    """Field order in the JSON is irrelevant; declaration order rules."""
    _, v = run(SPEC, '\n'.join([
        '{"name": "open", "m": "w", "f": "a"}',        # scrambled order
        '{"name": "write", "f": "a", "d": "x"}',
        '{"name": "write", "d": "y", "f": "b"}',
    ]), tmp_path)
    assert v == [True, True, False]


def test_extra_fields_ignored(tmp_path):
    _, v = run(SPEC, '{"name": "open", "f": "a", "m": "w", "pid": 7}\n'
                     '{"name": "write", "f": "a", "d": "x"}\n', tmp_path)
    assert v == [True, True]


def test_missing_field_rejected(tmp_path):
    with pytest.raises(ValueError, match="missing field"):
        run(SPEC, '{"name": "write", "f": "a"}\n', tmp_path)


def test_bad_json_rejected(tmp_path):
    with pytest.raises(ValueError, match="bad JSON"):
        run(SPEC, '{"name": "open" oops}\n', tmp_path)


def test_timed_jsonl(tmp_path):
    spec = """
    pred req(x: String)
    pred ack(x: String)
    prop t : Forall x . req(x) -> F[<=5] ack(x)
    """
    m, _ = run(spec, '\n'.join([
        '{"name": "req", "x": "a", "time": 0}',
        '{"name": "ack", "x": "a", "time": 3}',
        '{"name": "req", "x": "b", "time": 4}',
        '{"name": "noise", "time": 20}',
    ]), tmp_path, timed=True)
    # position 3's request went unanswered; the witness names it.
    assert m.formulas[0].witnesses == {3: {"x": "b"}}


def test_json_native_values(tmp_path):
    """JSON ints flow into Int parameters directly."""
    spec = """
    pred meas(v: Int, tag: String)
    prop p : Forall v . Forall tag . meas(v, tag) -> v < 100
    """
    _, v = run(spec, '{"name": "meas", "v": 42, "tag": "a"}\n'
                     '{"name": "meas", "v": 142, "tag": "b"}\n', tmp_path)
    assert v == [True, False]


def test_undeclared_predicate_field_order(tmp_path):
    spec = "prop p : Forall x . q(x) -> P r(x)"
    _, v = run(spec, '{"name": "r", "x": "a"}\n{"name": "q", "x": "a"}\n',
               tmp_path)
    assert v == [True, True]
