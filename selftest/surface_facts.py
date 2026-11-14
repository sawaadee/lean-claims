"""
File: selftest/surface_facts.py
Purpose: Tests `#surface_facts`, the Lean command `claims trust` relies on to list a
project's public declarations and what its claims mention. The library `LeanClaimsTest`
holds code with one declaration of every sort the command must tell apart and claims
that mention some of it. This script builds the library, runs the command over it, and
compares the report, declaration by declaration, with what each was written to be.

Usage: python3 -I selftest/surface_facts.py
Exit status: 0 when every expectation holds, 1 otherwise.
Created: 2026-11-13
Revised: 2026-11-14 (the statements that are or could be `@[csimp]` replacements)
"""

import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parent.parent
# `python3 -I` leaves this script's directory off the import path, so the tools are added here.
sys.path.insert(0, str(REPOSITORY / "tools"))

from leanclaims.process import run_command  # noqa: E402
from leanclaims.trust import TrustError, parse_surface_facts  # noqa: E402

PROBE_FILE_NAME = "LeanClaimsSurfaceFactsProbe.lean"
CODE = "LeanClaimsTest.Surface."
PROOFS = "LeanClaimsTest.Surface.Proofs."
CLAIMS = ["swap_first", "less_of_first", "total_eq", "viaHidden_eq", "fast_eq", "replaced_eq", "slow_eq", "swapped_eq",
          "sealed_eq"]

# declaration -> (kind, runs foreign code, the code that runs in its place, the claim theorems that mention it)
EXPECTED_SURFACE = {
    "Pair": ("type", False, None, {"swap_first", "less_of_first", "total_eq"}),
    "instReprPair": ("instance", False, None, set()),
    "instDecidableEqPair": ("instance", False, None, set()),
    "swap": ("definition", False, None, {"swap_first"}),
    "firstLess": ("definition", False, None, {"less_of_first"}),
    "instLTPair": ("instance", False, None, {"less_of_first"}),
    "helper": ("definition", False, None, set()),
    "sum": ("definition", False, None, {"total_eq"}),
    "total": ("definition", False, None, {"total_eq"}),
    "viaHidden": ("definition", False, None, {"viaHidden_eq"}),
    "unstated": ("definition", False, None, set()),
    "fast": ("definition", True, None, {"fast_eq"}),
    "replacement": ("definition", False, None, set()),
    "replaced": ("definition", False, CODE + "replacement", {"replaced_eq"}),
    "viaHiddenFast": ("definition", False, None, set()),
    "viaHiddenReplaced": ("definition", False, None, set()),
    "Shape": ("type", False, None, set()),
    "Shape.parts": ("definition", False, CODE + "Shape.parts._override", set()),
    "assumed": ("axiom", False, None, set()),
    "sealed": ("opaque", False, None, {"sealed_eq"}),
    "swap_swap": ("theorem", False, None, set()),
    "quick": ("definition", False, None, set()),
    "slow": ("definition", False, None, {"slow_eq"}),
    "slow_eq_quick": ("theorem", False, None, set()),
    "quick_eq_slow": ("theorem", False, None, set()),
    "swapped": ("definition", False, None, {"swapped_eq"}),
    "swapped_eq_different": ("theorem", False, None, set()),
    "inner_eq_different": ("theorem", False, None, set()),
    "viaInner": ("definition", False, None, set()),
    "pred_eq_different": ("theorem", False, None, set()),
    "scopedSlow": ("definition", False, None, set()),
    "scopedSlow_eq_different": ("theorem", False, None, set()),
    "localSlow": ("definition", False, None, set()),
    "localSlow_eq_different": ("theorem", False, None, set()),
    "viaLocal": ("definition", False, None, set()),
    "hiddenSlow": ("definition", False, None, set()),
    "decreedSlow": ("definition", False, None, set()),
}
# definition that is not public -> (runs foreign code, the code that runs in its place, the
# public declaration it belongs to). The first two a person wrote and marked private. The
# third Lean generated for a type with a computed field.
EXPECTED_HIDDEN = {"hiddenFast": (True, None, None), "hiddenReplaced": (False, CODE + "replacement", None),
                   "Shape.casesOn": (False, CODE + "Shape.casesOn._override", CODE + "Shape")}
# statement -> (it is public, what is replaced, that is public, the replacement, Lean has it
# registered, the namespace it is in force in, its axioms beyond the standard ones).
# A name that starts with a capital is not of the test's code and is written in full.
EXPECTED_REPLACEMENTS = {
    "slow_eq_quick": (True, "slow", True, "quick", True, None, ()),
    "quick_eq_slow": (True, "quick", True, "slow", False, None, ()),
    "swapped_eq_different": (True, "swapped", True, "different", True, None, ("swappedIsDifferent",)),
    "swappedIsDifferent": (False, "swapped", True, "different", False, None, ("swappedIsDifferent",)),
    "inner_eq_different": (True, "inner", False, "different", True, None, ("innerIsDifferent",)),
    "innerIsDifferent": (False, "inner", False, "different", False, None, ("innerIsDifferent",)),
    "pred_eq_different": (True, "Nat.pred", False, "different", True, None, ("predIsDifferent",)),
    "predIsDifferent": (False, "Nat.pred", False, "different", False, None, ("predIsDifferent",)),
    "scopedSlow_eq_different": (True, "scopedSlow", True, "different", True, "LeanClaimsTest.Surface",
                                ("scopedSlowIsDifferent",)),
    "scopedSlowIsDifferent": (False, "scopedSlow", True, "different", False, None, ("scopedSlowIsDifferent",)),
    "localSlow_eq_different": (True, "localSlow", True, "different", False, None, ("localSlowIsDifferent",)),
    "localSlowIsDifferent": (False, "localSlow", True, "different", False, None, ("localSlowIsDifferent",)),
    "hiddenSlow_eq_different": (False, "hiddenSlow", True, "different", True, None, ("hiddenSlowIsDifferent",)),
    "hiddenSlowIsDifferent": (False, "hiddenSlow", True, "different", False, None, ("hiddenSlowIsDifferent",)),
    "decreedSlowIsDifferent": (False, "decreedSlow", True, "different", True, None, ("decreedSlowIsDifferent",)),
    # Among the proofs, and about a constant that is not a function. Lean would accept it as
    # a replacement all the same, so it is listed. It is proved and not registered.
    "Proofs.sealed_eq": (False, "sealed", True, "sealed", False, None, ()),
}
# What must not be listed: a private declaration, and what belongs to a type or to a
# derived instance. Any declaration reported beyond EXPECTED_SURFACE fails the test, so
# these are named only to say what the absence means.
NOT_SURFACE = ["hidden", "Shape.casesOn", "Shape.point", "hiddenFast", "hiddenReplaced", "hiddenSealed", "different", "inner", "swappedIsDifferent", "hiddenSlow_eq_different", "Pair.mk", "Pair.first", "Pair.second", "Pair.rec",
               "Pair.casesOn", "instReprPair.repr", "instDecidableEqPair.decEq"]
EXPECTED_VOCABULARY = {"Pair", "swap", "firstLess", "instLTPair", "helper", "sum", "total", "viaHidden", "fast",
                       "replaced", "slow", "swapped", "sealed"}
EXPECTED_PRIVATE_VOCABULARY = {"hidden"}


def main() -> int:
    status, output = run_command(["lake", "build", "LeanClaimsTest"], REPOSITORY)
    if status != 0:
        print(f"FAILED: the test library does not build:\n{output[-2000:]}")
        return 1
    probe_path = REPOSITORY / PROBE_FILE_NAME
    probe_path.write_text(
        "import LeanClaims\nimport LeanClaimsTest\n\n"
        f"#surface_facts claims [{', '.join(PROOFS + name for name in CLAIMS)}] code [LeanClaimsTest.Surface] "
        "proofs [LeanClaimsTest.Surface.Proofs]\n", encoding="utf-8")
    try:
        status, output = run_command(["lake", "env", "lean", PROBE_FILE_NAME], REPOSITORY)
    finally:
        probe_path.unlink(missing_ok=True)
    try:
        facts = parse_surface_facts(output)
    except TrustError as error:
        print(f"FAILED: {error}")
        return 1

    failures = []
    if status != 0:
        failures.append(f"the command failed:\n{output[-1500:]}")
    reported = {declaration.name.removeprefix(CODE): declaration for declaration in facts.surface}
    for short_name, expected in EXPECTED_SURFACE.items():
        declaration = reported.pop(short_name, None)
        found = None if declaration is None else (
            declaration.kind, declaration.is_extern, declaration.implemented_by,
            {name.removeprefix(PROOFS) for name in declaration.stated_by})
        passed = found == expected
        print(f"{'passed' if passed else 'FAILED'}  {short_name}: {expected[0]}, mentioned by {sorted(expected[3]) or 'no claim'}")
        if not passed:
            failures.append(f"{short_name}: reported {found}, expected {expected}")
    passed = not reported
    print(f"{'passed' if passed else 'FAILED'}  nothing else is listed, so none of {', '.join(NOT_SURFACE)}")
    if not passed:
        failures.append(f"declarations listed that are not public declarations of the code: {sorted(reported)}")

    reported_replacements = {replacement.statement.removeprefix(CODE): replacement for replacement in facts.replacements}
    for short_name, expected in EXPECTED_REPLACEMENTS.items():
        replacement = reported_replacements.pop(short_name, None)
        found = None if replacement is None else (
            replacement.statement_is_public, replacement.replaced.removeprefix(CODE), replacement.replaced_is_public,
            replacement.replacement.removeprefix(CODE), replacement.is_registered, replacement.namespace,
            tuple(name.removeprefix(CODE) for name in replacement.axioms))
        passed = found == expected
        in_force = ("not registered" if not expected[4] else f"in force in {expected[5]}" if expected[5]
                    else "in force everywhere")
        print(f"{'passed' if passed else 'FAILED'}  {short_name}: {expected[1]} replaced by {expected[3]}, {in_force}, "
              f"resting on {list(expected[6]) or 'the standard axioms'}")
        if not passed:
            failures.append(f"the statement {short_name}: reported {found}, expected {expected}")
    passed = not reported_replacements
    print(f"{'passed' if passed else 'FAILED'}  no other statement is listed as one that could replace a function")
    if not passed:
        failures.append(f"statements listed that do not state two functions are equal: {sorted(reported_replacements)}")

    reported_hidden = {declaration.name.removeprefix(CODE): (declaration.is_extern, declaration.implemented_by,
                                                             declaration.owner)
                       for declaration in facts.hidden}
    passed = reported_hidden == EXPECTED_HIDDEN
    print(f"{'passed' if passed else 'FAILED'}  the definitions that are not public and run other code are "
          f"{sorted(EXPECTED_HIDDEN)}, the last belonging to `Shape`, and not the private opaque `hiddenSealed`")
    if not passed:
        failures.append(f"hidden code: reported {reported_hidden}, expected {EXPECTED_HIDDEN}")

    vocabulary = {name.removeprefix(CODE) for name in facts.vocabulary}
    passed = vocabulary == EXPECTED_VOCABULARY
    print(f"{'passed' if passed else 'FAILED'}  the vocabulary holds `helper`, which `sum` is defined by, and not `unstated`")
    if not passed:
        failures.append(f"vocabulary: reported {sorted(vocabulary)}, expected {sorted(EXPECTED_VOCABULARY)}")
    private_vocabulary = {name.removeprefix(CODE) for name in facts.private_vocabulary}
    passed = private_vocabulary == EXPECTED_PRIVATE_VOCABULARY
    print(f"{'passed' if passed else 'FAILED'}  the private vocabulary is `hidden`")
    if not passed:
        failures.append(f"private vocabulary: reported {sorted(private_vocabulary)}, expected {sorted(EXPECTED_PRIVATE_VOCABULARY)}")

    for claim_name, expected_mentions in (("less_of_first", {"Pair", "instLTPair", "firstLess"}),
                                          ("total_eq", {"Pair", "total", "sum"})):
        mentions = {name.removeprefix(CODE) for name in facts.mentions.get(PROOFS + claim_name, ())}
        passed = mentions == expected_mentions
        print(f"{'passed' if passed else 'FAILED'}  {claim_name} mentions {sorted(expected_mentions)}")
        if not passed:
            failures.append(f"{claim_name}: mentions {sorted(mentions)}, expected {sorted(expected_mentions)}")

    total = len(EXPECTED_SURFACE) + len(EXPECTED_REPLACEMENTS) + 7
    if failures:
        print(f"{len(failures)} expectations of #surface_facts do not hold")
    else:
        print(f"all {total} expectations of #surface_facts hold")
    for failure in failures:
        print(f"FAILED: {failure}")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
