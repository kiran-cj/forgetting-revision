"""The headline test: does the package confirm every claim in the literature?

One parametrised test per cell of the verdict matrix (24 postulates × AGM,
TSR, VFR = 72 cells), against checker.EXPECTED, plus the vacuous passes, the
relationships r1-r3, the transformation properties, and the report itself.

All of it reads the session fixtures in conftest.py, so the 1,500 operators
are checked once for the whole run.
"""

import pytest

from forgetting_revision import Signature, StatePartition, tsr_family
from forgetting_revision.checker import (
    EXPECTED,
    EXPECTED_VACUOUS,
    FAILS_FOR_TSR_AND_VFR,
    RELATIONSHIPS,
    expected_verdicts,
    format_report,
    main,
    mismatches,
    run_all,
    run_family,
)
from forgetting_revision.postulates import POSTULATES
from forgetting_revision.transform_properties import PROPERTIES

SIG1 = Signature.of("p")


# ============================================================ the verdict matrix

@pytest.mark.parametrize(("name", "family"), sorted(EXPECTED), ids=lambda x: str(x))
def test_verdict_matrix(reports2, name, family):
    summary = reports2[family].summary(name)
    if EXPECTED[name, family]:
        assert summary.holds, summary.first_failure and summary.first_failure[1].explain()
    else:
        assert not summary.holds, f"{name} was expected to fail somewhere in {family}"


def test_matrix_covers_every_postulate_and_family():
    assert len(EXPECTED) == 24 * 3
    assert FAILS_FOR_TSR_AND_VFR <= set(POSTULATES)


def test_exactly_the_expected_passes_are_vacuous(reports2):
    vacuous = {(name, family) for family, report in reports2.items()
               for name in POSTULATES if report.summary(name).vacuous}
    assert vacuous == EXPECTED_VACUOUS


@pytest.mark.parametrize("rel", RELATIONSHIPS, ids=lambda r: r.code)
def test_relationships_hold_on_every_operator(reports2, rel):
    for family, report in reports2.items():
        bad = report.relationship_violations(rel)
        assert not bad, f"{rel.code} fails for {family}: {bad[0].describe()}"


def test_no_mismatches_for_two_variables(reports2):
    assert mismatches(reports2) == []


# ============================================================ counts that mean something

def test_success_holds_exactly_under_full_trust(reports2):
    """Only the unit partition (TSR) and U = ∅ (VFR) give Success: B&H Prop 2,
    dissertation Postulate 2. So 75 of each family pass, one per ordering."""
    assert reports2["TSR"].summary("Success").failing == 1_125 - 75
    assert reports2["VFR"].summary("Success").failing == 300 - 75
    for member, res in reports2["VFR"].results:
        assert res["Success"].holds == (not member.untrusted)


def test_family_sizes(reports2):
    assert [r.size for r in reports2.values()] == [75, 1_125, 300]


# ============================================================ one variable

def test_one_variable_needs_its_own_expectations():
    """With one variable a source is trusted on everything or nothing, so
    manipulation is impossible: three expected failures disappear."""
    reports = run_all(SIG1)
    assert mismatches(reports) == []
    flipped = {key for key, v in expected_verdicts(SIG1).items() if v != EXPECTED[key]}
    assert {name for name, _ in flipped} == {"Very weak success", "Negation invariance",
                                             "Non-manipulability"}


# ============================================================ mismatches are reported

def test_a_family_that_breaks_expectations_is_reported(sig2):
    """Only the unit partition: this 'TSR' is really AGM, so it satisfies Success,
    which contradicts the expectation for TSR."""
    unit = StatePartition.unit(sig2)
    only_unit = run_family("TSR", sig2, (m for m in tsr_family(sig2) if m.partition == unit))
    problems = mismatches({"TSR": only_unit})
    assert "Success holds for TSR, expected the opposite" in problems


# ============================================================ transformation properties

def test_all_transforms_satisfy_all_nine(transform_reports2):
    assert [len(tr.results) for tr in transform_reports2.values()] == [1, 15, 4]
    for kind, tr in transform_reports2.items():
        for name in PROPERTIES:
            assert not tr.failing(name), f"{kind} fails {name}"


# ============================================================ the report and the command

def test_report_contents(reports2, transform_reports2):
    text = format_report(reports2, transform_reports2)
    assert "75 AGM, 1,125 TSR, 300 VFR configurations" in text
    assert "Non-manipulability" in text and "✓ vacuous" in text
    assert "First counterexamples" in text
    assert "f7  Pawlak" in text
    assert text.rstrip().endswith("All verdicts match AGM, Booth & Hunter (2018) and the dissertation.")


def test_main_exits_0_when_everything_matches(capsys):
    assert main(["--vars", "1"]) == 0
    assert "All verdicts match" in capsys.readouterr().out


def test_main_exits_1_on_a_disagreement(monkeypatch, capsys):
    """CI relies on this: a wrong verdict must turn the run red."""
    monkeypatch.setitem(EXPECTED, ("Success", "TSR"), True)
    assert main(["--vars", "1"]) == 1
    assert "DISAGREES" in capsys.readouterr().out
