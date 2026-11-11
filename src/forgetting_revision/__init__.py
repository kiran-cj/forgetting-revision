"""Variable Forgetting and Trust Sensitive Revision in Propositional Logic using Python"""

from .agm_revision import AGMRevision
from .selective_revision import ForgetTransform, SelectiveRevision, TrustExpansion
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
