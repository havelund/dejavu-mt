"""Bool literals as predicate arguments: cmd(true), cmd(false)."""
from dejavumt import parse_spec, Monitor


def verdicts(spec_text, events):
    m = Monitor(parse_spec(spec_text))
    return [m.step(ev) for ev in events]


SPEC = """
pred cmd(enable: Bool)
pred go
prop on  : go -> P cmd(true)
prop off : go -> P cmd(false)
"""


def test_true_matches_only_true():
    v = verdicts(SPEC, [{"cmd": [(True,)]}, {"go": [()]}])
    assert v[1]["on"] is True and v[1]["off"] is False


def test_false_matches_only_false():
    v = verdicts(SPEC, [{"cmd": [(False,)]}, {"go": [()]}])
    assert v[1]["on"] is False and v[1]["off"] is True


def test_log_text_values():
    # Values read from a CSV log arrive as text; "true"/"True"/"false" are accepted.
    for text, on in (("true", True), ("True", True), ("false", False)):
        v = verdicts(SPEC, [{"cmd": [(text,)]}, {"go": [()]}])
        assert v[1]["on"] is on and v[1]["off"] is (not on)


def test_formula_constants_unchanged():
    # true/false as formulas still mean what they did.
    spec = "pred go\nprop t : go -> true\nprop f : go -> false\n"
    v = verdicts(spec, [{"go": [()]}])
    assert v[0]["t"] is True and v[0]["f"] is False


def test_bool_variable_still_quantifies():
    spec = "pred cmd(enable: Bool)\npred go\nprop any : go -> P (Exists e . cmd(e))\n"
    v = verdicts(spec, [{"cmd": [(False,)]}, {"go": [()]}])
    assert v[1]["any"] is True
