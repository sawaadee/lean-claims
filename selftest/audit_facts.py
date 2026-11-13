"""
File: selftest/audit_facts.py
Purpose: Tests `#audit_facts`, the Lean command `claims audit` relies on to confirm what
an audit theorem's statement is. The library `LeanClaimsTest` holds audit theorems of
every shape the command must recognise and of the shapes it must refuse. This script
builds the library, runs the command over it, and compares the report, theorem by
theorem, with what each was written to be.

The theorems the command must refuse are all true and proved. A command that took any of
them for an audit would make `claims audit` pass on a theorem that audits nothing, so
each one here is a fault the command has been seen to catch.

Usage: python3 -I selftest/audit_facts.py
Exit status: 0 when every expectation holds, 1 otherwise.
Created: 2026-11-13
"""

import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parent.parent
# `python3 -I` leaves this script's directory off the import path, so the tools are added here.
sys.path.insert(0, str(REPOSITORY / "tools"))

from leanclaims.audit import AuditError, parse_audit_facts  # noqa: E402
from leanclaims.process import run_command  # noqa: E402

PROBE_FILE_NAME = "LeanClaimsAuditFactsProbe.lean"
CLAIMS = "LeanClaimsTest.Proofs."
AUDITS = "LeanClaimsTest.Audits."
EVEN, GE, POS, BOUNDED, FIXES, EQ = (CLAIMS + name for name in (
    "double_even", "double_ge", "double_pos", "double_lt_of_bounded", "double_fixesZero", "double_eq"))

EXPECTED_HYPOTHESES = {EVEN: 0, GE: 0, POS: 1, BOUNDED: 2, FIXES: 0, EQ: 0}

# property -> the claim theorems it must be tied to. A property absent here must have no tie.
EXPECTED_TIES = {
    AUDITS + "IsEven": {EVEN},
    AUDITS + "GrowsAndStaysPositive": {GE, POS},
    AUDITS + "StaysBelowTwoHundred": {BOUNDED},
    "LeanClaimsTest.FixesZero": {FIXES},
    AUDITS + "IsDoubling": {EQ},
}

# theorem -> (fails, negated property, determines, can hold). A theorem absent here must
# be reported with nothing found.
NOTHING = (set(), None, set(), set())
EXPECTED_THEOREMS = {
    "constantOne_fails_isEven": ({EVEN}, AUDITS + "IsEven", set(), set()),
    "constantZero_fails_gathered": ({GE, POS}, AUDITS + "GrowsAndStaysPositive", set(), set()),
    "constantTwoHundred_fails_bound": ({BOUNDED}, AUDITS + "StaysBelowTwoHundred", set(), set()),
    "constantOne_fails_fixesZero": ({FIXES}, "LeanClaimsTest.FixesZero", set(), set()),
    "constantOne_fails_otherWords": (set(), AUDITS + "IsEvenInOtherWords", set(), set()),
    "triple_fails_growsAndIsBounded": (set(), AUDITS + "GrowsAndIsBounded", set(), set()),
    "writtenOut_negation": NOTHING,
    "empty": NOTHING,
    "determined_through_properties": (set(), None, {EVEN, GE, POS}, set()),
    "determined_through_statement": (set(), None, {GE}, set()),
    "doubling_is_double": (set(), None, {EQ}, set()),
    "two_doublings_agree": (set(), None, {EQ}, set()),
    "conclusion_says_nothing": NOTHING,
    "isDoubling_tie": NOTHING,
    "conclusion_without_candidate": NOTHING,
    "hypothesis_about_the_implementation": NOTHING,
    "positive_can_hold": (set(), None, set(), {POS}),
    "both_can_hold": (set(), None, set(), {POS, BOUNDED}),
    "instances_of_the_hypotheses": NOTHING,
    "one_hypothesis_left_out": NOTHING,
    "isEven_tie": NOTHING,
    "gathered_tie": NOTHING,
    "conjunction_tie": NOTHING,
    "otherWords_holds": NOTHING,
    "growsAndIsBounded_holds": NOTHING,
}


def main() -> int:
    status, output = run_command(["lake", "build", "LeanClaimsTest"], REPOSITORY)
    if status != 0:
        print(f"FAILED: the test library does not build:\n{output[-2000:]}")
        return 1
    probe_path = REPOSITORY / PROBE_FILE_NAME
    probe_path.write_text(
        "import LeanClaims\nimport LeanClaimsTest\n\n"
        f"#audit_facts claims [{', '.join(EXPECTED_HYPOTHESES)}] modules [LeanClaimsTest.Audits]\n", encoding="utf-8")
    try:
        status, output = run_command(["lake", "env", "lean", PROBE_FILE_NAME], REPOSITORY)
    finally:
        probe_path.unlink(missing_ok=True)
    try:
        facts = parse_audit_facts(output)
    except AuditError as error:
        print(f"FAILED: {error}")
        return 1

    failures = []
    if status != 0:
        failures.append(f"the command failed:\n{output[-1500:]}")
    if facts.hypotheses != EXPECTED_HYPOTHESES:
        failures.append(f"hypotheses: reported {facts.hypotheses}, expected {EXPECTED_HYPOTHESES}")
    if facts.gave_up:
        failures.append(f"Lean gave up on comparisons: {facts.gave_up}")

    reported_ties: dict[str, set[str]] = {}
    for tie in facts.ties:
        reported_ties.setdefault(tie.property_name, set()).update(tie.claim_theorems)
    for property_name in sorted(set(reported_ties) | set(EXPECTED_TIES)):
        reported, expected = reported_ties.get(property_name, set()), EXPECTED_TIES.get(property_name, set())
        passed = reported == expected
        print(f"{'passed' if passed else 'FAILED'}  the property {property_name} is tied to {sorted(expected) or 'nothing'}")
        if not passed:
            failures.append(f"the property {property_name}: tied to {sorted(reported)}, expected {sorted(expected)}")

    reported_theorems = {theorem.name: theorem for theorem in facts.theorems}
    for short_name, expected in EXPECTED_THEOREMS.items():
        theorem = reported_theorems.pop(AUDITS + short_name, None)
        if theorem is None:
            reported = None
        else:
            reported = (set(theorem.fails), theorem.negated_property, set(theorem.determines), set(theorem.can_hold))
        passed = reported == expected
        print(f"{'passed' if passed else 'FAILED'}  {short_name}")
        if not passed:
            failures.append(f"{short_name}: reported {reported}, expected {expected}")
    if reported_theorems:
        failures.append(f"theorems reported that this test does not expect: {sorted(reported_theorems)}")

    total = len(EXPECTED_THEOREMS) + len(set(reported_ties) | set(EXPECTED_TIES))
    if failures:
        print(f"{len(failures)} expectations of #audit_facts do not hold")
    else:
        print(f"all {total} expectations of #audit_facts hold")
    for failure in failures:
        print(f"FAILED: {failure}")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
