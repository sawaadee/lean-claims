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
CLAIMS = ["swap_first", "less_of_first", "total_eq", "viaHidden_eq", "fast_eq", "replaced_eq", "sealed_eq"]

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
    "assumed": ("axiom", False, None, set()),
    "sealed": ("opaque", False, None, {"sealed_eq"}),
    "swap_swap": ("theorem", False, None, set()),
}
# What must not be listed: a private declaration, and what belongs to a type or to a
# derived instance. Any declaration reported beyond EXPECTED_SURFACE fails the test, so
# these are named only to say what the absence means.
NOT_SURFACE = ["hidden", "Pair.mk", "Pair.first", "Pair.second", "Pair.rec", "Pair.casesOn", "instReprPair.repr",
               "instDecidableEqPair.decEq"]
EXPECTED_VOCABULARY = {"Pair", "swap", "firstLess", "instLTPair", "helper", "sum", "total", "viaHidden", "fast",
                       "replaced", "sealed"}
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

    total = len(EXPECTED_SURFACE) + 5
    if failures:
        print(f"{len(failures)} expectations of #surface_facts do not hold")
    else:
        print(f"all {total} expectations of #surface_facts hold")
    for failure in failures:
        print(f"FAILED: {failure}")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
