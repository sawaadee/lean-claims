"""
File: tools/leanclaims/generated_faults.py
Purpose: Builds the faults that apply to every project, from its spec and `claims.toml`
alone, so that no project has to write them by hand. Each fault is the thing one check
exists to catch, and that check must fail when the fault is planted.

In every layer:
  - a theorem declared a second time under a name the layer already uses, which the
    theorem name check must report;
  - the same behind `set_option … in`, where a reading of the text does not see it and
    the name check must report that its reading differs from what Lean declares;
  - a theorem proved with `native_decide`, which the axiom assertion must name;
  - a theorem whose proof is `sorry`, which the build must refuse.
In every module of the test package that holds theorems:
  - a theorem proved with `native_decide`, which the axiom assertion must name.
Each of those adds text at the end of one file and changes nothing else in it, so it
cannot disturb the theorems already there.

From the spec:
  - a claim's title changed with the lock left alone, which `claims lock --check` must
    report;
  - a generated file changed by hand, which `claims sync --check` must report;
  - the statements of two claims exchanged in the verify file, which the build must
    refuse through `recall`;
  - the statements of two claims exchanged in the spec, with the lock brought up to
    date, which `lake comparator` must reject. This is the case the lock cannot catch:
    a spec changed on purpose to say something the proofs do not prove.

From the audits and the tested surface:
  - the `Audit:` line taken off the only theorem that shows a wrong implementation
    failing some claim, which `claims audit` must report;
  - a theorem proving `True` under an `Audit:` line of each of the three kinds, which
    `claims audit` must refuse because Lean does not confirm the line;
  - the fault a `[[tested]]` entry names taken out of `faults.toml`, which `claims audit`
    must report.

From the surface:
  - a public function added to the code that no claim mentions and no entry lists,
    which `claims trust --check` must report;
  - the trust report changed by hand, which `claims trust --check` must report.
Created: 2026-11-13
"""

from leanclaims.audit import audit_module_file, tagged_theorems_in_source
from leanclaims.config import Layer, ProjectConfig
from leanclaims.faults import FAULTS_FILE_NAME, PlannedFault
from leanclaims.lean_source import declared_theorems
from leanclaims.lock import LOCK_FILE_NAME, lock_text
from leanclaims.spec import Claim, ClaimLine, Spec, SpecTheorem, parse_spec
from leanclaims.trust import TRUST_FILE_NAME

# Names chosen so that they cannot collide with a project's own theorems.
PLANTED_AXIOM_THEOREM = "leanClaimsPlantedAxiom"
PLANTED_GAP_THEOREM = "leanClaimsPlantedGap"
PLANTED_AXIOM_TEXT = f"\n\ntheorem {PLANTED_AXIOM_THEOREM} : (2 : Nat) + 2 = 4 := by native_decide\n"


class NoFaultPossible(Exception):
    """The project gives nothing to build the fault from."""


def _read(config: ProjectConfig, relative_path: str) -> str:
    return (config.project_directory / relative_path).read_text(encoding="utf-8")


def _last_proof_file(config: ProjectConfig, layer: Layer) -> tuple[str, str]:
    """The relative path and the text of the layer's last proof file that declares a
    theorem. A file that only imports the others is not asserted about, so a fault planted
    there would test nothing."""
    for proof_file in reversed(layer.proof_files):
        text = proof_file.read_text(encoding="utf-8")
        if declared_theorems(text):
            return proof_file.relative_to(config.project_directory).as_posix(), text
    raise NoFaultPossible(f"layer '{layer.name}' declares no theorem")


def duplicate_theorem_fault(config: ProjectConfig, layer: Layer) -> PlannedFault:
    """Declare the layer's first theorem a second time, at the end of its last file. The
    second declaration sits outside every namespace the file opens, which is a case Lean
    accepts and the name check must not."""
    for proof_file in layer.proof_files:
        theorems = declared_theorems(proof_file.read_text(encoding="utf-8"))
        if theorems:
            existing_name = theorems[0].name
            break
    else:
        raise NoFaultPossible(f"layer '{layer.name}' declares no theorem")
    relative_path, text = _last_proof_file(config, layer)
    return PlannedFault(
        fault_id=f"generated-duplicate-theorem-{layer.name}",
        description=f"layer '{layer.name}': the theorem {existing_name} declared a second time",
        check_id="names",
        new_texts={relative_path: text + f"\n\ntheorem {existing_name} : True := trivial\n"},
        expected_in_output=(f"{layer.namespace}.{existing_name} is declared in",))


def unseen_theorem_fault(config: ProjectConfig, layer: Layer) -> PlannedFault:
    """Declare the layer's first theorem a second time behind `set_option … in`, where the
    reading of the file as text does not see a declaration. Lean accepts it, the search
    for duplicates passes it by, and only the comparison with what Lean declares can
    report it."""
    for proof_file in layer.proof_files:
        theorems = declared_theorems(proof_file.read_text(encoding="utf-8"))
        if theorems:
            existing_name = theorems[0].name
            break
    else:
        raise NoFaultPossible(f"layer '{layer.name}' declares no theorem")
    relative_path, text = _last_proof_file(config, layer)
    planted = f"\n\nset_option maxRecDepth 512 in theorem {existing_name} : True := trivial\n"
    return PlannedFault(
        fault_id=f"generated-unseen-theorem-{layer.name}",
        description=f"layer '{layer.name}': the theorem {existing_name} declared again where reading the text misses it",
        check_id="names",
        new_texts={relative_path: text + planted},
        expected_in_output=(f"Lean declares the theorem {existing_name} here",
                            "the reading of the file as text did not find it"))


def non_standard_axiom_fault(config: ProjectConfig, layer: Layer) -> PlannedFault:
    """Add a theorem proved by `native_decide`, which rests on `Lean.ofReduceBool` and on
    trusting the compiler, to the layer's last proof file."""
    relative_path, text = _last_proof_file(config, layer)
    return PlannedFault(
        fault_id=f"generated-axiom-{layer.name}",
        description=f"layer '{layer.name}': a theorem proved with native_decide",
        check_id="axioms",
        new_texts={relative_path: text + PLANTED_AXIOM_TEXT},
        expected_in_output=(PLANTED_AXIOM_THEOREM, "beyond the allowed axioms"))


def test_module_axiom_fault(config: ProjectConfig, module: str) -> PlannedFault:
    """Add a theorem proved by `native_decide` to a module of theorems in the test package."""
    relative_path = f"{config.tests_directory}/{module.replace('.', '/')}.lean"
    if not (config.project_directory / relative_path).is_file():
        raise NoFaultPossible(f"the test module {module} has no file {relative_path}")
    return PlannedFault(
        fault_id=f"generated-axiom-test-module-{module}",
        description=f"test module {module}: a theorem proved with native_decide",
        check_id="axioms",
        new_texts={relative_path: _read(config, relative_path) + PLANTED_AXIOM_TEXT},
        expected_in_output=(PLANTED_AXIOM_THEOREM, "beyond the allowed axioms"))


def unfinished_proof_fault(config: ProjectConfig, layer: Layer) -> PlannedFault:
    """Add a theorem whose proof is `sorry` to the layer's last proof file."""
    relative_path, text = _last_proof_file(config, layer)
    planted = f"\n\ntheorem {PLANTED_GAP_THEOREM} : (1 : Nat) = 1 := by sorry\n"
    return PlannedFault(
        fault_id=f"generated-unfinished-proof-{layer.name}",
        description=f"layer '{layer.name}': an unfinished proof",
        check_id="build",
        new_texts={relative_path: text + planted},
        expected_in_output=("sorry",))


def _replace_once(text: str, find: str, replace: str, what: str) -> str:
    if text.count(find) != 1:
        raise NoFaultPossible(f"{what}: the text to change occurs {text.count(find)} times")
    return text.replace(find, replace)


def _setting(claim: Claim, theorem: SpecTheorem) -> tuple[str, ...]:
    """The namespace, open and end lines that come before a theorem inside its claim: the
    setting its statement is read in."""
    lines = []
    for part in claim.parts:
        if part is theorem:
            break
        if isinstance(part, ClaimLine):
            lines.append(part.text)
    return tuple(lines)


def _two_theorems_to_exchange(spec: Spec) -> tuple[SpecTheorem, SpecTheorem]:
    """The first two theorems of the spec that are read in the same setting and have
    different statements, so that each one's statement is well formed under the other's
    name and is not what that name proves."""
    placed = [(theorem, _setting(claim, theorem)) for claim in spec.claims for theorem in claim.theorems]
    for first_index, (first, first_setting) in enumerate(placed):
        for second, second_setting in placed[first_index + 1:]:
            if first_setting == second_setting and first.signature != second.signature:
                return first, second
    raise NoFaultPossible("the spec has no two theorems in one setting with different statements")


def spec_changed_without_lock_fault(config: ProjectConfig, spec: Spec) -> PlannedFault:
    """Change the title of the first claim that is still made, and leave the lock alone."""
    claim = next((claim for claim in spec.claims if not claim.withdrawn), None)
    if claim is None:
        raise NoFaultPossible("every claim is withdrawn")
    header = f"/-! ## Claim {claim.number}. {claim.title}"
    new_spec = _replace_once(_read(config, spec.file_name), header, header + " (changed)", "the claim header")
    return PlannedFault(
        fault_id="generated-spec-changed-lock-left-alone",
        description=f"claim {claim.number} changed in the spec with the lock left alone",
        check_id="lock",
        new_texts={spec.file_name: new_spec},
        expected_in_output=(f"claim {claim.number} changed",))


def generated_file_edited_fault(config: ProjectConfig, spec: Spec) -> PlannedFault:
    """Add a line by hand to the verify file, which only `claims sync` may write."""
    return PlannedFault(
        fault_id="generated-file-edited-by-hand",
        description="a generated file changed by hand",
        check_id="sync",
        new_texts={config.verify_file: _read(config, config.verify_file) + "\n-- a line added by hand\n"},
        expected_in_output=(config.verify_file,))


def verify_statements_exchanged_fault(config: ProjectConfig, spec: Spec) -> PlannedFault:
    """Give each of two theorems the other's statement in the verify file."""
    first, second = _two_theorems_to_exchange(spec)
    verify = _read(config, config.verify_file)
    marker = "recall leanClaimsExchangePlaceholder"
    verify = _replace_once(verify, f"recall {first.name}{first.signature}\n", f"{marker}\n", "the first recall")
    verify = _replace_once(verify, f"recall {second.name}{second.signature}\n",
                           f"recall {second.name}{first.signature}\n", "the second recall")
    verify = _replace_once(verify, f"{marker}\n", f"recall {first.name}{second.signature}\n", "the placeholder")
    return PlannedFault(
        fault_id="generated-verify-statements-exchanged",
        description=f"the statements of {first.name} and {second.name} exchanged in the verify file",
        check_id="build",
        new_texts={config.verify_file: verify},
        expected_in_output=(config.verify_file,))


def spec_statements_exchanged_fault(config: ProjectConfig, spec: Spec) -> PlannedFault:
    """Give each of two theorems the other's statement in the spec, and bring the lock up
    to date, as someone changing the spec on purpose would."""
    first, second = _two_theorems_to_exchange(spec)
    spec_text = _read(config, spec.file_name)
    marker = "theorem leanClaimsExchangePlaceholder"
    spec_text = _replace_once(spec_text, f"theorem {first.name}{first.signature}", marker, "the first theorem")
    spec_text = _replace_once(spec_text, f"theorem {second.name}{second.signature}",
                              f"theorem {second.name}{first.signature}", "the second theorem")
    spec_text = _replace_once(spec_text, marker, f"theorem {first.name}{second.signature}", "the placeholder")
    new_lock = lock_text(parse_spec(spec_text, spec.file_name), _read(config, LOCK_FILE_NAME))
    return PlannedFault(
        fault_id="generated-spec-statements-exchanged",
        description=f"the statements of {first.name} and {second.name} exchanged in the spec, lock updated",
        check_id="comparator",
        new_texts={spec.file_name: spec_text, LOCK_FILE_NAME: new_lock},
        expected_in_output=("theorem statement do not match", first.name))


def audit_line_removed_fault(config: ProjectConfig, spec: Spec) -> PlannedFault:
    """Take the `Audit:` line off an audit theorem that is the only one showing a wrong
    implementation failing its claim. The theorem stays, and stays proved; only its
    standing as an audit goes, which is what `claims audit` reads."""
    audits = tagged_theorems_in_source(config)
    waived = {waiver.claim for waiver in config.waivers if waiver.kind == "fails"}
    fails_of_claim: dict[int, list] = {}
    for theorem in audits:
        if theorem.kind == "fails":
            for number in theorem.claim_numbers:
                fails_of_claim.setdefault(number, []).append(theorem)
    for number in sorted(fails_of_claim):
        if len(fails_of_claim[number]) == 1 and number not in waived:
            theorem = fails_of_claim[number][0]
            relative_path = audit_module_file(config, theorem.module)
            text = _read(config, relative_path)
            new_doc_comment = theorem.doc_comment.replace("Audit:", "Note:", 1)
            return PlannedFault(
                fault_id="generated-audit-line-removed",
                description=f"the Audit line taken off {theorem.name}, the only theorem failing claim {number}",
                check_id="audit",
                new_texts={relative_path: _replace_once(text, theorem.doc_comment, new_doc_comment, "the doc comment")},
                expected_in_output=(f"claim {number} (", "no audit theorem shows a wrong implementation failing it"))
    raise NoFaultPossible("no claim has exactly one audit theorem showing a wrong implementation failing it")


PLANTED_EMPTY_AUDIT_THEOREM = "leanClaimsPlantedEmptyAudit"
AUDIT_SENTENCES = {
    "fails": "fails claim {number}.",
    "determines": "determines claim {number}.",
    "can hold": "hypotheses of claim {number} can hold.",
}


def empty_audit_theorem_fault(config: ProjectConfig, spec: Spec, kind: str) -> PlannedFault:
    """Add to the first audit module a theorem that proves `True` under an `Audit:` line of
    the given kind. It compiles and rests on no axiom, so only a check that reads the
    statement, and not the comment, can refuse it."""
    claim = next((claim for claim in spec.claims if not claim.withdrawn), None)
    if claim is None:
        raise NoFaultPossible("every claim is withdrawn")
    relative_path = audit_module_file(config, config.audit_modules[0])
    sentence = AUDIT_SENTENCES[kind].format(number=claim.number)
    planted = f"\n\n/-- Audit: {sentence} -/\ntheorem {PLANTED_EMPTY_AUDIT_THEOREM} : True := trivial\n"
    return PlannedFault(
        fault_id=f"generated-empty-audit-theorem-{kind.replace(' ', '-')}",
        description=f"a theorem proving True under the line 'Audit: {sentence}'",
        check_id="audit",
        new_texts={relative_path: _read(config, relative_path) + planted},
        expected_in_output=(PLANTED_EMPTY_AUDIT_THEOREM,
                            f"the Audit line names claim {claim.number} and Lean does not confirm it"))


def tested_entry_fault_removed_fault(config: ProjectConfig, spec: Spec) -> PlannedFault:
    """Take the fault a tested entry names out of `faults.toml`, by renaming it."""
    if not config.tested:
        raise NoFaultPossible("claims.toml has no tested entry")
    entry = config.tested[0]
    catalog = _read(config, FAULTS_FILE_NAME)
    return PlannedFault(
        fault_id="generated-tested-entry-fault-removed",
        description=f"the fault '{entry.fault}', which a tested entry names, taken out of {FAULTS_FILE_NAME}",
        check_id="audit",
        new_texts={FAULTS_FILE_NAME: _replace_once(
            catalog, f'id = "{entry.fault}"', f'id = "{entry.fault}-removed"', "the fault's id")},
        expected_in_output=(f"{FAULTS_FILE_NAME} has no fault '{entry.fault}'",))


PLANTED_UNLISTED_DEFINITION = "leanClaimsPlantedUnlisted"


def unlisted_public_declaration_fault(config: ProjectConfig, spec: Spec) -> PlannedFault:
    """Add a public function to the code's root module that no claim mentions and no
    entry lists. It compiles and breaks no proof. Only the surface check can report it."""
    relative_path = f"{config.code_modules[0].replace('.', '/')}.lean"
    if not (config.project_directory / relative_path).is_file():
        raise NoFaultPossible(f"the code module {config.code_modules[0]} has no file {relative_path}")
    planted = (f"\n\n/-- A function no claim mentions. -/\n"
               f"def {PLANTED_UNLISTED_DEFINITION} (number : Nat) : Nat := number + 1\n")
    return PlannedFault(
        fault_id="generated-unlisted-public-declaration",
        description="a public function added to the code that no claim mentions and no entry lists",
        check_id="trust",
        new_texts={relative_path: _read(config, relative_path) + planted},
        expected_in_output=(PLANTED_UNLISTED_DEFINITION, "is public and is not proved, tested or trusted"))


def trust_report_edited_fault(config: ProjectConfig, spec: Spec) -> PlannedFault:
    """Add a line by hand to the trust report, which only `claims trust` may write."""
    if not (config.project_directory / TRUST_FILE_NAME).is_file():
        raise NoFaultPossible(f"the project has no {TRUST_FILE_NAME}")
    return PlannedFault(
        fault_id="generated-trust-report-edited-by-hand",
        description="the trust report changed by hand",
        check_id="trust",
        new_texts={TRUST_FILE_NAME: _read(config, TRUST_FILE_NAME) + "\nA line added by hand.\n"},
        expected_in_output=(f"{TRUST_FILE_NAME} is out of date",))


def generated_faults(config: ProjectConfig, spec: Spec) -> tuple[list[PlannedFault], list[str]]:
    """Every generated fault for the project, and the reasons for any that could not be
    built. A project too small for a fault, such as a spec with one theorem and so nothing
    to exchange it with, still gets the rest."""
    builders = []
    for layer in config.layers:
        builders.append(lambda layer=layer: duplicate_theorem_fault(config, layer))
        builders.append(lambda layer=layer: unseen_theorem_fault(config, layer))
        builders.append(lambda layer=layer: non_standard_axiom_fault(config, layer))
        builders.append(lambda layer=layer: unfinished_proof_fault(config, layer))
    for module in list(config.audit_modules) + list(config.tests_theorem_modules):
        builders.append(lambda module=module: test_module_axiom_fault(config, module))
    builders.append(lambda: spec_changed_without_lock_fault(config, spec))
    builders.append(lambda: generated_file_edited_fault(config, spec))
    builders.append(lambda: verify_statements_exchanged_fault(config, spec))
    builders.append(lambda: spec_statements_exchanged_fault(config, spec))
    if config.audit_modules:
        builders.append(lambda: audit_line_removed_fault(config, spec))
        for kind in AUDIT_SENTENCES:
            builders.append(lambda kind=kind: empty_audit_theorem_fault(config, spec, kind))
    if config.tested:
        builders.append(lambda: tested_entry_fault_removed_fault(config, spec))
    builders.append(lambda: unlisted_public_declaration_fault(config, spec))
    builders.append(lambda: trust_report_edited_fault(config, spec))
    faults, not_possible = [], []
    for build in builders:
        try:
            faults.append(build())
        except NoFaultPossible as reason:
            not_possible.append(str(reason))
    return faults, not_possible
