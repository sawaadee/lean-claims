"""
File: tools/leanclaims/audit.py
Purpose: The audit rule. A proof shows that a claim is true of the code. It does not show
that the claim says enough, or anything at all: a claim with contradictory hypotheses is
true, and so is one so weak that a wrong implementation meets it. An audit is a theorem
about the claims themselves, proved in the test package, and this check requires every
claim to have its audits.

For every claim the spec still makes:

  fails       At least one audit theorem shows that a realistic wrong implementation
              violates the claim, so the claim is not empty. The property it fails must
              state theorems of this claim only.
  determines  An audit theorem shows that any implementation meeting the claims equals
              the project's, so the claims leave nothing unsaid.
  can hold    For every theorem of the claim that has hypotheses, an audit theorem shows
              they can be true together.
  mutation    At least one bug in `mutations.toml` is refuted by a theorem of the claim.

A requirement that cannot be met is lifted by a `[[waiver]]` in `claims.toml` with its
reason. A waiver for a requirement that is met, or for a claim that does not need it, is
an error, so the list of waivers stays a true list of gaps.

An audit theorem says what it is about in the first line of its doc comment:

  /-- Audit: fails claim 9. ...
  /-- Audit: determines claims 8, 9 and 10. ...
  /-- Audit: hypotheses of claims 2 to 4 can hold. ...

The line is a statement of intent, and it is not taken on trust. Lean reads the theorem's
statement (the `#audit_facts` command of the LeanClaims package, described in
`LeanClaims/Audit.lean`) and the check requires Lean to confirm the line for every claim
it names. A theorem proving `True` under an `Audit:` line is an error. The theorems, their
doc comments and their statements all come from the compiled audit modules, so nothing
here depends on reading Lean source as text.

The check also requires every `[[tested]]` entry of `claims.toml` to name a check that
exists and a fault in `faults.toml` planted for that check, so that nothing rests on a
test nobody has seen fail.

What this check cannot do: Lean confirms that a property, asked of the project's own
implementation, is the claim's statement. Whether the property asks the same of every
other candidate is for the reviewer who reads it. Whether the wrong implementations are
realistic is also a reviewer's question, and whether the claims catch real bugs is the
mutation run's.
Created: 2026-11-13
"""

import json
import re
from dataclasses import dataclass

from leanclaims.config import ProjectConfig
from leanclaims.faults import BUILT_IN_CHECK_IDS, Check, PlannedFault
from leanclaims.lean_source import declared_theorems
from leanclaims.mutations import Mutation
from leanclaims.process import run_command
from leanclaims.spec import Spec

AUDIT_KINDS = ("fails", "determines", "can hold")
AUDIT_PROBE_FILE_NAME = "LeanClaimsAuditProbe.lean"
_AUDIT_LINE = re.compile(r"/--\s*Audit:(?P<rest>[^\n]*)")
_NUMBERS = re.compile(r"(?P<first>[1-9][0-9]*)(?:\s+to\s+(?P<last>[1-9][0-9]*))?")
_FACTS_LINE = re.compile(r"audit-facts (?P<document>\{.*\})\s*$", re.MULTILINE)


class AuditError(Exception):
    """The audit could not be carried out: an audit module is missing or does not build,
    an `Audit:` line is malformed, or Lean could not be asked about the audit theorems."""


def audit_module_file(config: ProjectConfig, module: str) -> str:
    return f"{config.tests_directory}/{module.replace('.', '/')}.lean"


def parse_audit_line(rest: str, where: str) -> tuple[str, tuple[int, ...]]:
    """Read what follows `Audit:` on its line: the kind and the claim numbers."""
    text = rest.strip()
    if text.startswith("fails claim"):
        kind = "fails"
    elif text.startswith("determines claim"):
        kind = "determines"
    elif text.startswith("hypotheses of claim") and "can hold" in text:
        kind = "can hold"
    else:
        raise AuditError(
            f"{where}: an Audit line reads 'Audit: fails claim N.', 'Audit: determines claims N, M.' or "
            f"'Audit: hypotheses of claim N can hold.'; found 'Audit: {text}'")
    # The claim numbers are those of the Audit sentence itself, which ends at the first
    # full stop. What follows on the line is explanation and may hold other numbers.
    sentence = text.split(".")[0]
    numbers: list[int] = []
    for match in _NUMBERS.finditer(sentence):
        first = int(match.group("first"))
        last = int(match.group("last")) if match.group("last") else first
        if last < first:
            raise AuditError(f"{where}: the range {first} to {last} runs backwards")
        numbers.extend(range(first, last + 1))
    if not numbers:
        raise AuditError(f"{where}: the Audit line names no claim number")
    return kind, tuple(sorted(set(numbers)))


@dataclass(frozen=True)
class TaggedTheorem:
    """A theorem with an `Audit:` line, as found in an audit module's text."""

    module: str
    name: str
    kind: str
    claim_numbers: tuple[int, ...]
    doc_comment: str


def tagged_theorems_in_source(config: ProjectConfig) -> list[TaggedTheorem]:
    """The theorems with an `Audit:` line, read from the text of the audit modules. The
    audit itself reads them from Lean. This reading is for planting faults, which needs
    the place in the file where a theorem's doc comment is."""
    tagged = []
    for module in config.audit_modules:
        relative_path = audit_module_file(config, module)
        path = config.project_directory / relative_path
        if not path.is_file():
            raise AuditError(f"the audit module {module} has no file {relative_path}")
        for theorem in declared_theorems(path.read_text(encoding="utf-8")):
            audit_line = _AUDIT_LINE.match(theorem.doc_comment) if theorem.doc_comment else None
            if audit_line is not None:
                where = f"{relative_path}:{theorem.line_number}: {theorem.name}"
                kind, claim_numbers = parse_audit_line(audit_line.group("rest"), where)
                tagged.append(TaggedTheorem(module, theorem.name, kind, claim_numbers, theorem.doc_comment))
    return tagged


@dataclass(frozen=True)
class LeanTheorem:
    """A theorem of an audit module, and what Lean finds its statement to be. The names in
    `fails`, `determines` and `can_hold` are the qualified names of claim theorems."""

    name: str
    module: str
    line_number: int
    doc_comment: str | None
    fails: tuple[str, ...] = ()
    negated_property: str | None = None
    determines: tuple[str, ...] = ()
    can_hold: tuple[str, ...] = ()


@dataclass(frozen=True)
class PropertyTie:
    """A property of an audit module and the claim theorems whose statement it is."""

    property_name: str
    claim_theorems: tuple[str, ...]
    tied_by: str


@dataclass(frozen=True)
class AuditFacts:
    """Everything `#audit_facts` reported."""

    # For every theorem of the spec, by qualified name, the number of its hypotheses.
    hypotheses: dict[str, int]
    theorems: tuple[LeanTheorem, ...] = ()
    ties: tuple[PropertyTie, ...] = ()
    # Comparisons Lean gave up on. Each one may hide a fact, so each is a problem.
    gave_up: tuple[str, ...] = ()


def parse_audit_facts(output: str) -> AuditFacts:
    """Read the line `#audit_facts` printed."""
    found = _FACTS_LINE.search(output)
    if found is None:
        raise AuditError(f"Lean did not report the audit facts:\n{output[-1500:]}")
    document = json.loads(found.group("document"))
    return AuditFacts(
        hypotheses={entry["name"]: entry["hypotheses"] for entry in document["claims"]},
        theorems=tuple(sorted((LeanTheorem(
            name=entry["name"], module=entry["module"], line_number=entry["line"], doc_comment=entry["doc"],
            fails=tuple(entry["fails"]), negated_property=entry["negated_property"],
            determines=tuple(entry["determines"]), can_hold=tuple(entry["can_hold"]))
            for entry in document["theorems"]), key=lambda theorem: (theorem.module, theorem.line_number))),
        ties=tuple(PropertyTie(entry["property"], tuple(entry["claim_theorems"]), entry["tied_by"])
                   for entry in document["ties"]),
        gave_up=tuple(document["gave_up"]))


def lean_audit_facts(config: ProjectConfig, spec: Spec) -> AuditFacts:
    """Build the test package, so that what Lean reads is what the files now say, then ask
    Lean about the claims and the audit modules. The claim theorems are the proved ones;
    the comparator and the verify file establish that their statements are the spec's."""
    for module in config.audit_modules:
        relative_path = audit_module_file(config, module)
        if not (config.project_directory / relative_path).is_file():
            raise AuditError(f"the audit module {module} has no file {relative_path}")
    tests_directory = config.project_directory / config.tests_directory
    status, output = run_command(["lake", "build"], tests_directory)
    if status != 0:
        raise AuditError(f"the test package does not build, so its audit theorems cannot be read:\n{output[-3000:]}")
    names = [theorem.qualified_name for theorem in spec.theorems]
    imports = ["LeanClaims", config.proofs_module, *config.audit_modules]
    probe_text = ("".join(f"import {module}\n" for module in imports)
                  + f"\n#audit_facts claims [{', '.join(names)}] modules [{', '.join(config.audit_modules)}]\n")
    probe_path = tests_directory / AUDIT_PROBE_FILE_NAME
    probe_path.write_text(probe_text, encoding="utf-8")
    try:
        status, output = run_command(["lake", "env", "lean", AUDIT_PROBE_FILE_NAME], tests_directory)
    finally:
        probe_path.unlink(missing_ok=True)
    if status != 0:
        raise AuditError(f"Lean could not be asked about the audit theorems:\n{output[-3000:]}")
    return parse_audit_facts(output)


@dataclass(frozen=True)
class ClaimAudit:
    """What was found for one claim. The three tuples hold the names of the audit theorems
    Lean confirmed for it."""

    number: int
    title: str
    fails: tuple[str, ...]
    determines: tuple[str, ...]
    can_hold: tuple[str, ...]
    has_hypotheses: bool
    mutations: int
    waived: tuple[str, ...]


@dataclass(frozen=True)
class AuditReport:
    claims: tuple[ClaimAudit, ...]
    problems: tuple[str, ...]
    audit_theorem_count: int
    untagged_theorem_count: int


def _why_not_confirmed(theorem: LeanTheorem, kind: str, number: int, facts: AuditFacts,
                       claim_of_theorem: dict[str, int]) -> str:
    """Why Lean does not find `theorem` to be an audit of this kind for claim `number`."""
    if kind == "fails":
        if theorem.negated_property is None:
            return "its statement is not '¬ P candidate' for a property P"
        if not theorem.fails:
            return (f"its property {theorem.negated_property} is not tied to a claim: no audit theorem states "
                    "the property of the project's own implementation with a claim's statement as the result")
        claims = sorted({claim_of_theorem[name] for name in theorem.fails if name in claim_of_theorem})
        return (f"its property {theorem.negated_property} is the statement of {', '.join(theorem.fails)}, "
                f"of claim {', '.join(str(claim) for claim in claims)}")
    if kind == "determines":
        return (f"no hypothesis of it asks a property tied to claim {number} of a candidate that its "
                "conclusion mentions")
    return f"its statement is not 'hypotheses_can_hold% T' for a theorem T of claim {number}"


def audit(config: ProjectConfig, spec: Spec, mutations: list[Mutation], declared_checks: dict[str, Check],
          catalog_faults: list[PlannedFault], facts: AuditFacts) -> AuditReport:
    """Check every claim against the rule, every `Audit:` line against what Lean found,
    and every tested entry against the fault catalog."""
    problems: list[str] = [f"Lean gave up on a comparison, which may hide an audit: {reason}" for reason in facts.gave_up]
    made_claims = {claim.number: claim for claim in spec.claims if not claim.withdrawn}
    all_numbers = {claim.number for claim in spec.claims}
    claim_of_theorem = {theorem.qualified_name: claim.number for claim in spec.claims for theorem in claim.theorems}

    confirmed: dict[tuple[int, str], list[str]] = {}
    # The theorems of each claim whose hypotheses some audit theorem shows can hold.
    hypotheses_shown: dict[int, set[str]] = {}
    tagged_count = 0
    for theorem in facts.theorems:
        doc_comment = (theorem.doc_comment or "").strip()
        if not doc_comment.startswith("Audit:"):
            continue
        tagged_count += 1
        where = f"{audit_module_file(config, theorem.module)}:{theorem.line_number}: {theorem.name}"
        first_line = doc_comment.split("\n")[0]
        kind, claim_numbers = parse_audit_line(first_line[len("Audit:"):], where)
        found_names = {"fails": theorem.fails, "determines": theorem.determines, "can hold": theorem.can_hold}[kind]
        for number in claim_numbers:
            if number not in all_numbers:
                problems.append(f"{where} is about claim {number}, which the spec does not have")
                continue
            if number not in made_claims:
                problems.append(f"{where} is about claim {number}, which is withdrawn")
                continue
            of_this_claim = [name for name in found_names if claim_of_theorem.get(name) == number]
            # A property that gathers theorems of several claims can be failed by failing
            # any one of them, so failing it does not show that this claim is the one.
            other_claims = sorted({claim_of_theorem[name] for name in found_names
                                   if name in claim_of_theorem and claim_of_theorem[name] != number})
            if kind == "fails" and of_this_claim and other_claims:
                problems.append(
                    f"{where}: the Audit line names claim {number} and Lean does not confirm it: its property "
                    f"{theorem.negated_property} gathers theorems of claims "
                    f"{', '.join(str(claim) for claim in sorted([number, *other_claims]))}, so failing it does not "
                    "show which claim fails. Use a property that states this claim alone")
                continue
            if not of_this_claim:
                problems.append(
                    f"{where}: the Audit line names claim {number} and Lean does not confirm it: "
                    f"{_why_not_confirmed(theorem, kind, number, facts, claim_of_theorem)}")
                continue
            confirmed.setdefault((number, kind), []).append(theorem.name)
            if kind == "can hold":
                hypotheses_shown.setdefault(number, set()).update(of_this_claim)

    namespace_of_layer = {layer.name: layer.namespace for layer in config.layers}
    mutation_counts: dict[int, int] = {}
    for mutation in mutations:
        if mutation.refuted_claim is not None:
            number = claim_of_theorem.get(f"{namespace_of_layer[mutation.layer_name]}.{mutation.refuted_claim}")
            if number is not None:
                mutation_counts[number] = mutation_counts.get(number, 0) + 1

    waivers = {(waiver.claim, waiver.kind): waiver for waiver in config.waivers}
    for number in sorted({claim_number for claim_number, _ in waivers}):
        if number not in all_numbers:
            problems.append(f"a waiver names claim {number}, which the spec does not have")
        elif number not in made_claims:
            problems.append(f"a waiver names claim {number}, which is withdrawn and needs none")

    results = []
    for number, claim in sorted(made_claims.items()):
        with_hypotheses = [theorem.name for theorem in claim.theorems
                           if facts.hypotheses.get(theorem.qualified_name, 0) > 0]
        not_shown = [theorem.name for theorem in claim.theorems
                     if facts.hypotheses.get(theorem.qualified_name, 0) > 0
                     and theorem.qualified_name not in hypotheses_shown.get(number, set())]
        found = {kind: tuple(confirmed.get((number, kind), ())) for kind in AUDIT_KINDS}
        met = {
            "fails": bool(found["fails"]),
            "determines": bool(found["determines"]),
            "can hold": not not_shown,
            "mutation": mutation_counts.get(number, 0) > 0,
        }
        needed = {"fails": True, "determines": True, "can hold": bool(with_hypotheses), "mutation": True}
        what_is_missing = {
            "fails": "no audit theorem shows a wrong implementation failing it",
            "determines": "no audit theorem shows the claims determine the implementation",
            "can hold": f"no audit theorem shows the hypotheses of {', '.join(not_shown)} can hold",
            "mutation": "no mutation in mutations.toml is refuted by one of its theorems",
        }
        waived = []
        for kind in ("fails", "determines", "can hold", "mutation"):
            waiver = waivers.get((number, kind))
            if waiver is not None:
                if not needed[kind]:
                    problems.append(f"claim {number}: the waiver for '{kind}' is not needed, the claim has no hypotheses")
                elif met[kind]:
                    problems.append(f"claim {number}: the waiver for '{kind}' is not needed, the requirement is met")
                else:
                    waived.append(kind)
            elif needed[kind] and not met[kind]:
                problems.append(f"claim {number} ({claim.title}): {what_is_missing[kind]}")
        results.append(ClaimAudit(
            number=number, title=claim.title, fails=found["fails"], determines=found["determines"],
            can_hold=found["can hold"], has_hypotheses=bool(with_hypotheses),
            mutations=mutation_counts.get(number, 0), waived=tuple(waived)))

    known_checks = set(BUILT_IN_CHECK_IDS) | set(declared_checks)
    faults_by_id = {fault.fault_id: fault for fault in catalog_faults}
    for entry in config.tested:
        if entry.test not in known_checks:
            problems.append(f"tested entry '{entry.what}': no check is named '{entry.test}'")
        fault = faults_by_id.get(entry.fault)
        if fault is None:
            problems.append(f"tested entry '{entry.what}': faults.toml has no fault '{entry.fault}'")
        elif fault.check_id != entry.test:
            problems.append(
                f"tested entry '{entry.what}': the fault '{entry.fault}' is planted for the check "
                f"'{fault.check_id}', not for '{entry.test}'")

    return AuditReport(claims=tuple(results), problems=tuple(problems), audit_theorem_count=tagged_count,
                       untagged_theorem_count=len(facts.theorems) - tagged_count)
