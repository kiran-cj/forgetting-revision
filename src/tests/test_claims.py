"""Tests for the instance claims and negative controls in claims.py.

The claims carry their own checks; these tests make sure every one of them
holds, that the registry is complete, and that a failing claim turns the
check-postulates run red.
"""

import pytest

from forgetting_revision.checker import main
from forgetting_revision.claims import (
    CLAIMS,
    CONTROL,
    INSTANCE,
    Claim,
    ClaimResult,
    claim,
    run_claims,
)


@pytest.fixture(scope="module")
def results():
    return run_claims()


@pytest.mark.parametrize("code", list(CLAIMS))
def test_claim_holds(results, code):
    assert results[code].holds, f"{code} {CLAIMS[code].title}: {results[code].detail}"


def test_registry():
    assert [c for c in CLAIMS if CLAIMS[c].kind == INSTANCE] == [f"i{n}" for n in range(1, 10)]
    assert [c for c in CLAIMS if CLAIMS[c].kind == CONTROL] == [f"c{n}" for n in range(1, 5)]
    for c in CLAIMS.values():
        assert c.title and c.source


def test_registering_a_duplicate_is_an_error():
    with pytest.raises(ValueError, match="registered twice"):
        @claim("i1", "again", "test", INSTANCE)
        def dup():
            return ClaimResult(True, "")


def test_details_record_the_corrections(results):
    """The findings the dissertation should pick up are in the report text."""
    assert "consistent α" in results["i1"].detail
    assert "ignores the" in results["i6"].detail
    assert "3 faithful orderings" in results["i7"].detail


def test_a_failing_claim_makes_the_run_fail(monkeypatch, capsys):
    broken = Claim("i99", "a claim that is false", "test", INSTANCE,
                   lambda: ClaimResult(False, "deliberately broken"))
    monkeypatch.setitem(CLAIMS, "i99", broken)
    assert main(["--vars", "1"]) == 1
    out = capsys.readouterr().out
    assert "✗  a claim that is false" in out
    assert "claim i99 does not hold" in out
