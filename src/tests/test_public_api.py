"""The package's public API: everything in __all__ exists and imports cleanly."""

import forgetting_revision as fr


def test_every_name_in_all_exists():
    missing = [name for name in fr.__all__ if not hasattr(fr, name)]
    assert not missing, f"listed in __all__ but not defined: {missing}"


def test_all_has_no_duplicates():
    assert len(fr.__all__) == len(set(fr.__all__))


def test_core_names_are_exported():
    for name in ("Var", "Signature", "AGMRevision", "StatePartition", "SelectiveRevision",
                 "BooleForget", "ForgetOperator", "RevisionOperator", "Transformation",
                 "ForgetTransform", "TrustExpansion", "IdentityTransform", "TableTransform",
                 "dnf", "meanings", "orderings", "partitions", "untrusted_sets"):
        assert name in fr.__all__, name
