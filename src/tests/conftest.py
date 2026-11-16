"""Shared fixtures for the whole test suite.

pytest loads conftest.py automatically before any test in this folder, and a
fixture defined here can be used by any test file just by naming it as an
argument. With scope="session" it is computed once per test run, however
many tests use it. Checking all 1,500 two-variable operators takes a few
seconds, so sharing that work matters.
"""

import pytest

from forgetting_revision import Signature
from forgetting_revision.checker import (
    FamilyReport,
    TransformReport,
    run_all,
    run_transforms,
)


@pytest.fixture(scope="session")
def sig2() -> Signature:
    return Signature.of("p q")


@pytest.fixture(scope="session")
def reports2(sig2) -> dict[str, FamilyReport]:
    """Every AGM, TSR and VFR operator over (p, q), checked against all 24 postulates."""
    return run_all(sig2)


@pytest.fixture(scope="session")
def transform_reports2(sig2) -> dict[str, TransformReport]:
    """The identity, all 15 TrustExpansions and all 4 ForgetTransforms, checked against f1-f9."""
    return run_transforms(sig2)
