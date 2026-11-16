"""Variable Forgetting and Trust-Sensitive Revision in Propositional Logic using Python"""

from .agm_revision import AGMRevision, RevisionOperator
from .families import (
    FAMILIES,
    Member,
    agm_family,
    orderings,
    partitions,
    tsr_family,
    untrusted_sets,
    vfr_family,
)
from .forget import BooleForget, ForgetOperator
from .postulates import BeliefChangeOperator, OutcomeTable
from .selective_revision import (
    ForgetTransform,
    IdentityTransform,
    SelectiveRevision,
    TableTransform,
    Transformation,
    TrustExpansion,
)
from .semantics import (
    Signature,
    State,
    cnf,
    dnf,
    entails,
    equivalent,
    evaluate,
    is_tautology,
    meanings,
    models,
    satisfiable,
    state_formula,
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
    # families
    "FAMILIES",
    "Member",
    "agm_family",
    "orderings",
    "partitions",
    "tsr_family",
    "untrusted_sets",
    "vfr_family",
    # forget
    "BooleForget",
    "ForgetOperator",
    # postulates
    "BeliefChangeOperator",
    "OutcomeTable",
    # selective_revision
    "ForgetTransform",
    "IdentityTransform",
    "SelectiveRevision",
    "TableTransform",
    "Transformation",
    "TrustExpansion",
    # semantics
    "Signature",
    "State",
    "cnf",
    "dnf",
    "entails",
    "equivalent",
    "evaluate",
    "is_tautology",
    "meanings",
    "models",
    "satisfiable",
    "state_formula",
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