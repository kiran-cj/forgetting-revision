"""Variable Forgetting and Trust-Sensitive Revision in Propositional Logic using Python"""

from .agm_revision import AGMRevision, RevisionOperator
from .forget import BooleForget, ForgetOperator
from .selective_revision import (
    ForgetTransform,
    SelectiveRevision,
    Transformation,
    TrustExpansion,
)
from .semantics import (
    Signature,
    State,
    entails,
    equivalent,
    evaluate,
    is_tautology,
    models,
    satisfiable,
    state_str,
    states_str,
)
from .syntax import (
    BOTTOM,
    TOP,
    And,
    Const,
    Formula,
    Iff,
    Implies,
    Not,
    Or,
    Var,
    variables,
)
from .transform import simplify, substitute
from .trust import StatePartition

__all__ = [
    # agm_revision
    "AGMRevision",
    "RevisionOperator",
    # forget
    "BooleForget",
    "ForgetOperator",
    # selective_revision
    "ForgetTransform",
    "SelectiveRevision",
    "Transformation",
    "TrustExpansion",
    # semantics
    "Signature",
    "State",
    "entails",
    "equivalent",
    "evaluate",
    "is_tautology",
    "models",
    "satisfiable",
    "state_str",
    "states_str",
    # syntax
    "BOTTOM",
    "TOP",
    "And",
    "Const",
    "Formula",
    "Iff",
    "Implies",
    "Not",
    "Or",
    "Var",
    "variables",
    # transform
    "simplify",
    "substitute",
    # trust
    "StatePartition",
]