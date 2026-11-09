"""Variable Forgetting and Trust Sensitive Revision in Propositional Logic using Python"""

from .syntax import BOTTOM, TOP, And, Const, Formula, Iff, Implies, Not, Or, Var, variables
from .semantics import Signature, entails, equivalent, evaluate, is_tautology, models, satisfiable, states_str
from .transform import simplify, substitute