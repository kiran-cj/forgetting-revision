"""
Forgetting layer: the pluggable Forget() operator.

Any forget operator is just "something callable that takes a formula and a
set of variable names, and returns a new formula". The revision operation will
only ever depend on the ForgetOperator, never on a specific implementation, so
swapping to different kind of forget operator means writing a new class and
nothing else.

    forget: ForgetOperator = BooleForget{}
    weakened = forget(alpha, {"q"})
"""
from collections.abc import Iterable
from typing import Protocol

from .syntax import Formula, Or, TOP, BOTTOM
from .transform import simplify, substitute

class ForgetOperator(Protocol):
    """A forget operator takes a formula and a set of variable names, and
    returns a weaker formula that no longer mentions those variables."""

    def __call__(self, formula: Formula, forget: Iterable[str]) -> Formula: ...

class BooleForget: # transformation function for Variable Forgetting Revision
    """
    Boole's syntactic forgetting:
        Remove all trace of the variable/s to be forgotten
        with all possible truth assignments.

        Forget(α, p) = α[p/⊤] ∨ α[p/⊥]

    A set of variables is forgotten one at a time.
    """

    name = "boole"

    def __call__(self, formula: Formula, forget: Iterable[str]) -> Formula:
        if isinstance(forget, str):          # guard: "p1" would iterate as "p", "1"
            forget = [forget]

        result = formula
        for var in sorted(set(forget)):      # sorted -> same output tree every run
            result = self.forget_one(result, var)
        return result

    @staticmethod
    def forget_one(formula: Formula, var: str) -> Formula:
        """Forget(α, p) = α[p/⊤] ∨ α[p/⊥]"""
        if_true = substitute(formula, {var: TOP})
        if_false = substitute(formula, {var: BOTTOM})
        return simplify(Or(if_true, if_false))
