"""The runner: check whole families, compare with the literature, print a report.

    reports = run_all(Signature.of("p q"))
    print(format_report(reports))

or from the command line:

    uv run check-postulates            # two variables, exhaustive
    uv run check-postulates --vars 1

What a report contains:
  - the verdict matrix: each postulate × AGM / TSR / VFR, with the number of
    operators that fail it,
  - the first counterexample for every failure, naming the exact operator,
  - postulates that hold only vacuously (premise never triggered),
  - the nine transformation properties on identity / TrustExpansion / ForgetTransform,
  - the relationships between postulates (r1-r3), which must have no violations,
  - any disagreement with EXPECTED, the verdicts claimed by AGM, Booth &
    Hunter and the dissertation. A disagreement makes main() exit with
    status 1, so the check can run in CI.
"""

import argparse
import sys
from collections.abc import Callable, Iterable, Mapping
from dataclasses import dataclass, field

from .families import FAMILIES, Member, format_partition, partitions, untrusted_sets
from .postulates import POSTULATES, Postulate, PostulateResult, check, format_witness
from .selective_revision import (
    ForgetTransform,
    IdentityTransform,
    Transformation,
    TrustExpansion,
)
from .semantics import Signature
from .transform_properties import PROPERTIES, TransformPropertyResult, check_transform

FAMILY_NAMES = tuple(FAMILIES)          # ("AGM", "TSR", "VFR")


# ============================================================ what the literature claims

#: Postulates that TSR and VFR fail (every other one, they satisfy). AGM satisfies all 24.
FAILS_FOR_TSR_AND_VFR = frozenset({
    "Success", "Vacuity", "Superexpansion", "Subexpansion",
    "Weak success", "Very weak success", "Negation invariance", "Non-manipulability",
})

#: (postulate name, family) -> True if every operator of the family satisfies it.
EXPECTED: Mapping[tuple[str, str], bool] = {
    (name, family): family == "AGM" or name not in FAILS_FOR_TSR_AND_VFR
    for name in POSTULATES
    for family in FAMILY_NAMES
}

#: With ONE variable there are only two partitions, unit (full trust = AGM) and
#: trivial (no trust: K never changes). Both are extremes where B&H §7 shows
#: Non-manipulability holds, and Very weak success cannot fail either. A source
#: that is trusted on one thing but not another needs at least two variables.
HOLD_WITH_ONE_VARIABLE = frozenset({"Very weak success", "Negation invariance", "Non-manipulability"})


def expected_verdicts(sig: Signature) -> Mapping[tuple[str, str], bool]:
    """EXPECTED for n >= 2; for n = 1, the three postulates above also hold."""
    if len(sig) >= 2:
        return EXPECTED
    return {key: holds or key[0] in HOLD_WITH_ONE_VARIABLE for key, holds in EXPECTED.items()}


#: Postulates that hold for AGM only because their premise never arises.
#: Both start "if K ◦ φ ⊬ φ", which Success rules out.
EXPECTED_VACUOUS = frozenset({("Non-manipulability", "AGM"), ("Weak non-manipulability", "AGM")})


# ============================================================ relationships (r1-r3)

@dataclass(frozen=True)
class Relationship:
    """A claim linking postulates, checked on each operator separately."""

    code: str
    statement: str
    source: str
    holds_for: Callable[[Mapping[str, PostulateResult]], bool]


def _h(results: Mapping[str, PostulateResult], name: str) -> bool:
    return results[name].holds


RELATIONSHIPS = (
    Relationship("r1", "Negation invariance ⇔ Very weak success", "B&H §6",
                 lambda r: _h(r, "Negation invariance") == _h(r, "Very weak success")),
    Relationship("r2", "Feeble success ∧ Non-manipulability ⇒ Very weak success", "B&H Prop 13",
                 lambda r: _h(r, "Very weak success")
                 or not (_h(r, "Feeble success") and _h(r, "Non-manipulability"))),
    Relationship("r3", "Success ⇒ Weak success ⇒ Very weak success", "by definition",
                 lambda r: (not _h(r, "Success") or _h(r, "Weak success"))
                 and (not _h(r, "Weak success") or _h(r, "Very weak success"))),
)


# ============================================================ family reports

@dataclass(frozen=True)
class PostulateSummary:
    """One postulate over a whole family."""

    postulate: Postulate
    failing: int                                  # number of operators that fail
    triggered: int                                # premise cases, summed over operators
    first_failure: tuple[Member, PostulateResult] | None

    @property
    def holds(self) -> bool:
        return self.failing == 0

    @property
    def vacuous(self) -> bool:
        return self.holds and self.triggered == 0


@dataclass(frozen=True)
class FamilyReport:
    family: str
    signature: Signature
    results: list[tuple[Member, dict[str, PostulateResult]]] = field(repr=False)

    @property
    def size(self) -> int:
        return len(self.results)

    def summary(self, name: str) -> PostulateSummary:
        failing, triggered, first = 0, 0, None
        for member, res in self.results:
            r = res[name]
            triggered += r.triggered
            if not r.holds:
                failing += 1
                first = first or (member, r)
        return PostulateSummary(POSTULATES[name], failing, triggered, first)

    def holds(self, name: str) -> bool:
        return all(res[name].holds for _, res in self.results)

    def relationship_violations(self, rel: Relationship) -> list[Member]:
        return [member for member, res in self.results if not rel.holds_for(res)]


def run_family(family: str, sig: Signature, members: Iterable[Member] | None = None) -> FamilyReport:
    """Check every operator of a family (or the given members) against all 24 postulates."""
    chosen = FAMILIES[family](sig) if members is None else members
    return FamilyReport(family, sig, [(m, check(m.operator, sig)) for m in chosen])


def run_all(sig: Signature) -> dict[str, FamilyReport]:
    return {family: run_family(family, sig) for family in FAMILY_NAMES}


def mismatches(reports: Mapping[str, FamilyReport]) -> list[str]:
    """Every place the checker disagrees with EXPECTED, in words. Empty is good."""
    problems = []
    sig = next(iter(reports.values())).signature
    for (name, family), expected in expected_verdicts(sig).items():
        if family not in reports:
            continue
        actual = reports[family].holds(name)
        if actual != expected:
            word = "holds" if actual else "fails"
            problems.append(f"{name} {word} for {family}, expected the opposite")
        vacuous = reports[family].summary(name).vacuous
        if vacuous != ((name, family) in EXPECTED_VACUOUS):
            word = "is" if vacuous else "is not"
            problems.append(f"{name} {word} vacuous for {family}, expected the opposite")
    for rel in RELATIONSHIPS:
        for family, report in reports.items():
            bad = report.relationship_violations(rel)
            if bad:
                problems.append(f"{rel.code} violated by {len(bad)} {family} operators, e.g. {bad[0].describe()}")
    return problems


# ============================================================ transformation properties

@dataclass(frozen=True)
class TransformReport:
    kind: str
    results: list[tuple[str, dict[str, TransformPropertyResult]]] = field(repr=False)

    def failing(self, name: str) -> list[tuple[str, TransformPropertyResult]]:
        return [(label, res[name]) for label, res in self.results if not res[name].holds]


def transforms(sig: Signature) -> dict[str, list[tuple[str, Transformation]]]:
    """The three kinds of f, each labelled for the report."""
    return {
        "identity": [("identity", IdentityTransform(sig))],
        "TrustExpansion": [(format_partition(p), TrustExpansion(sig, p)) for p in partitions(sig)],
        "ForgetTransform": [
            ("untrusted {" + ", ".join(sorted(u)) + "}", ForgetTransform(sig, u)) for u in untrusted_sets(sig)
        ],
    }


def run_transforms(sig: Signature) -> dict[str, TransformReport]:
    return {
        kind: TransformReport(kind, [(label, check_transform(f, sig)) for label, f in fs])
        for kind, fs in transforms(sig).items()
    }


# ============================================================ formatting

def format_report(
    reports: Mapping[str, FamilyReport],
    transform_reports: Mapping[str, TransformReport] | None = None,
) -> str:
    sig = next(iter(reports.values())).signature
    sizes = ", ".join(f"{r.size:,} {f}" for f, r in reports.items())
    out = [f"Postulate checker: signature ({', '.join(sig.names)}), {sizes} operators", ""]

    # --- verdict matrix
    col = 12
    out.append(f"{'#':>3}  {'Postulate':<26}" + "".join(f"{f:<{col}}" for f in reports))
    for p in POSTULATES.values():
        cells = []
        for report in reports.values():
            s = report.summary(p.name)
            cells.append("✓ vacuous" if s.vacuous else "✓" if s.holds else f"✗ {s.failing:,}")
        out.append(f"{p.number:>3}  {p.name:<26}" + "".join(f"{c:<{col}}" for c in cells))
    legend = ("✓ every operator satisfies it   ✗ n  n operators fail it   "
              "vacuous  holds only because the premise never arises")
    out += ["", legend, ""]

    # --- one counterexample per failing cell
    out.append("First counterexamples")
    for p in POSTULATES.values():
        for report in reports.values():
            s = report.summary(p.name)
            if s.first_failure is not None:
                member, result = s.first_failure
                out.append(f"  {p.name} [{member.describe()}]")
                out.append(f"      {format_witness(result.counterexample or ())}")
    out.append("")

    # --- transformation properties
    if transform_reports:
        kinds = list(transform_reports)
        counts = ", ".join(f"{len(tr.results)} {k}" for k, tr in transform_reports.items())
        out.append(f"Transformation properties ({counts})")
        out.append(f"{'':>3}  {'Property':<26}" + "".join(f"{k:<17}" for k in kinds))
        for prop in PROPERTIES.values():
            cells = []
            for tr in transform_reports.values():
                bad = tr.failing(prop.name)
                cells.append("✓" if not bad else f"✗ {len(bad)}")
            out.append(f"{prop.code:>3}  {prop.name:<26}" + "".join(f"{c:<17}" for c in cells))
        out.append("")

    # --- relationships
    out.append("Relationships (operators violating each; all should be 0)")
    for rel in RELATIONSHIPS:
        counts = "  ".join(f"{f} {len(r.relationship_violations(rel))}" for f, r in reports.items())
        out.append(f"  {rel.code}  {rel.statement:<58} {counts}")
    out.append("")

    # --- comparison with the literature
    problems = mismatches(reports)
    if transform_reports:
        problems += [f"{k} fails {name}" for k, tr in transform_reports.items()
                     for name in PROPERTIES if tr.failing(name)]
    if problems:
        places = "place" if len(problems) == 1 else "places"
        out.append(f"DISAGREES with the expected verdicts in {len(problems)} {places}:")
        out += [f"  - {p}" for p in problems]
    else:
        out.append("All verdicts match AGM, Booth & Hunter (2018) and the dissertation.")
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="check-postulates",
        description="Check AGM, TSR and VFR against every postulate, exhaustively.",
    )
    parser.add_argument("--vars", type=int, default=2, choices=[1, 2],
                        help="number of propositional variables (default 2; 3 needs sampling)")
    args = parser.parse_args(argv)

    sig = Signature(tuple("pqr"[: args.vars]))
    reports = run_all(sig)
    transform_reports = run_transforms(sig)
    print(format_report(reports, transform_reports))
    failed = bool(mismatches(reports)) or any(
        tr.failing(name) for tr in transform_reports.values() for name in PROPERTIES
    )
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
