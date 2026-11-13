"""
File: tools/leanclaims/mutate.py
Purpose: The mutation run. It plants one deliberate bug at a time in a project's code and
reports two things for each.

  Broken proofs: which claims stop holding. A claim counts as broken when its proof fails
  or when it ends up depending on anything beyond the allowed axioms. Lean keeps a lemma
  whose proof fails as an admitted gap (`sorryAx`), or, when the proof ran out of time,
  leaves the lemma unchecked and lists it by name among the axioms of whatever uses it;
  either way the claims built on it still compile, and only their axioms show the gap. A
  proof can also break only because it was written against the exact old expression, so
  a broken proof alone does not show that the bug violates the claim.

  Refutation: for every bug that changes behaviour, a Lean proof that the claim's
  statement, taken from the spec, is false of the mutated code. The refutation applies
  the spec's theorem to a concrete input and derives `False`. The spec's theorems are
  admitted with `sorry`, which is expected here: the refutation shows they cannot all be
  true of this code. If the bug did not really violate the statement, the refutation
  does not compile.

A bug is caught only when both happen: a proof broke, and the claim was proved false.

Two controls run before any bug is planted, and the run stops if either fails. On the
unchanged code no claim may read as broken; a tool that read every claim as broken would
otherwise call every bug caught. And on the unchanged code no refutation may compile; a
refutation that proved `False` of correct code would otherwise refute anything.

Every file is restored after each mutation, even on failure and even when the run is
killed: the originals are journalled before any file changes, and a run begins by
replaying a journal an interrupted run left.
Created: 2026-11-13
"""

import re
from dataclasses import dataclass
from pathlib import Path

from leanclaims.config import Layer, ProjectConfig
from leanclaims.journal import PlantedFaults, PlantingError
from leanclaims.lean_source import blank_comments_and_strings, declared_theorems
from leanclaims.mutations import Mutation
from leanclaims.process import run_command
from leanclaims.spec import Spec
from leanclaims.sync import module_name

PROBE_FILE_NAME = "LeanClaimsMutationProbe.lean"
REFUTATION_FILE_NAME = "LeanClaimsRefutationProbe.lean"
_IMPORT_LINE = re.compile(r"^import[ \t]+(?P<module>\S+)[ \t]*$", re.MULTILINE)


class MutationRunError(Exception):
    """The run could not start or could not continue."""


@dataclass(frozen=True)
class MutationResult:
    """What happened when one bug was planted."""

    mutation: Mutation
    rejected_by_build: str | None
    broken: tuple[str, ...]
    refuted: bool | None

    @property
    def caught(self) -> bool:
        return bool(self.broken)


def _imports_of(source: str) -> list[str]:
    return [match.group("module") for match in _IMPORT_LINE.finditer(blank_comments_and_strings(source))]


def probe_files_in_order(config: ProjectConfig, layer: Layer) -> list[Path]:
    """The layer's files to join into the probe, each after the files it imports. The
    order written in `claims.toml` is used when there is one. Otherwise the files that
    declare a theorem are ordered by their imports, ties broken by name."""
    if layer.probe_files:
        return list(layer.probe_files)
    candidates = [path for path in layer.proof_files if declared_theorems(path.read_text(encoding="utf-8"))]
    module_of = {path: module_name(path.relative_to(config.project_directory).as_posix()) for path in candidates}
    path_of = {module: path for path, module in module_of.items()}
    needs = {
        path: {path_of[module] for module in _imports_of(path.read_text(encoding="utf-8")) if module in path_of}
        for path in candidates
    }
    ordered: list[Path] = []
    while len(ordered) < len(candidates):
        ready = sorted(path for path in candidates if path not in ordered and needs[path] <= set(ordered))
        if not ready:
            raise MutationRunError(f"layer '{layer.name}': its proof files import each other in a circle")
        ordered.append(ready[0])
    return ordered


def claims_of_layer(spec: Spec, layer: Layer) -> list[str]:
    """The spec's theorems in the layer's namespace: the claims the layer's proofs must prove."""
    return [theorem.name for theorem in spec.theorems if theorem.namespace == layer.namespace]


def probe_source(config: ProjectConfig, spec: Spec, layer: Layer) -> str:
    """The layer's proof files joined into one file, with an axiom print for each claim.
    Joined, a lemma that fails in one file is an admitted gap in the claims of the next,
    where separate files would only fail to import."""
    files = probe_files_in_order(config, layer)
    own_modules = {module_name(path.relative_to(config.project_directory).as_posix()) for path in files}
    imports: list[str] = []
    bodies = []
    for path in files:
        source = path.read_text(encoding="utf-8")
        readable = blank_comments_and_strings(source)
        body = source
        # Import lines are taken out of the body, last first so that positions stay right.
        for match in reversed(list(_IMPORT_LINE.finditer(readable))):
            if match.group("module") not in own_modules and match.group("module") not in imports:
                imports.append(match.group("module"))
            body = body[:match.start()] + body[match.end():]
        bodies.append(body)
    prints = "\n".join(f"#print axioms {layer.namespace}.{name}" for name in claims_of_layer(spec, layer))
    # Theorems are checked one after another, so that a failed one is missing, or
    # admitted, by the time the next is checked.
    return ("\n".join(f"import {name}" for name in sorted(imports)) + "\n\nset_option Elab.async false\n\n"
            + "\n\n".join(bodies) + "\n\n" + prints + "\n")


class MutationRun:
    """One mutation run over one project."""

    def __init__(self, config: ProjectConfig, spec: Spec, mutations: list[Mutation], report=print):
        self.config = config
        self.spec = spec
        self.mutations = mutations
        self.report = report
        self.project_directory = config.project_directory
        self.probe_path = self.project_directory / PROBE_FILE_NAME
        self.refutation_path = self.project_directory / REFUTATION_FILE_NAME
        self.planted_faults = PlantedFaults(self.project_directory)

    def broken_claims(self, layer: Layer) -> list[str]:
        """Compile the layer's proofs with an axiom print for each claim, and return the
        claims whose proof failed or that depend on anything beyond the allowed axioms.
        The test is the allowed list, not the presence of `sorryAx`: a proof that fails by
        running out of time is not replaced by `sorry`, and a claim built on it then lists
        the failed theorem by name among its axioms."""
        self.probe_path.write_text(probe_source(self.config, self.spec, layer), encoding="utf-8")
        _, output = run_command(["lake", "env", "lean", PROBE_FILE_NAME], self.project_directory)
        allowed = set(self.config.allowed_axioms)
        broken = []
        for name in claims_of_layer(self.spec, layer):
            qualified = re.escape(f"{layer.namespace}.{name}")
            with_axioms = re.search(rf"'{qualified}' depends on axioms: \[([^\]]*)\]", output)
            without_axioms = re.search(rf"'{qualified}' does not depend on any axioms", output)
            if with_axioms is not None:
                axioms = {axiom.strip() for axiom in with_axioms.group(1).split(",") if axiom.strip()}
                if not axioms <= allowed:
                    broken.append(name)
            elif without_axioms is None:
                broken.append(name)
        return broken

    def refutes(self, layer: Layer, refutation: str) -> tuple[bool, str]:
        """Whether `False` follows from the spec's statement on the code as it stands,
        with the compiler's output so that a failure can be read."""
        spec_status, spec_output = run_command(["lake", "build", self.config.spec_library], self.project_directory)
        if spec_status != 0:
            return False, spec_output
        prelude = (self.project_directory / layer.refutation_prelude).read_text(encoding="utf-8")
        self.refutation_path.write_text(
            prelude.rstrip() + f"\n\ntheorem statement_fails_on_mutated_code : False :=\n  {refutation}\n",
            encoding="utf-8")
        status, output = run_command(["lake", "env", "lean", REFUTATION_FILE_NAME], self.project_directory)
        errors = [line for line in output.splitlines() if ": error" in line]
        return status == 0 and not errors, output

    def control_problems(self) -> list[str]:
        """Check the run against the unchanged code. Returns the problems found."""
        targets = [self.config.code_library, self.config.proofs_library, self.config.spec_library]
        status, output = run_command(["lake", "build"] + targets, self.project_directory)
        if status != 0:
            return [f"the unchanged project does not build:\n{output[-800:]}"]
        problems = []
        for layer_name in sorted({mutation.layer_name for mutation in self.mutations}):
            layer = self.config.layer_named(layer_name)
            if not claims_of_layer(self.spec, layer):
                problems.append(f"layer '{layer_name}': the spec states no theorem in {layer.namespace}")
                continue
            broken = self.broken_claims(layer)
            if broken:
                problems.append(f"layer '{layer_name}': claims read as broken on unchanged code: {', '.join(broken)}")
        for mutation in self.mutations:
            if mutation.refutation is None:
                continue
            compiled, _ = self.refutes(self.config.layer_named(mutation.layer_name), mutation.refutation)
            if compiled:
                problems.append(f"the refutation for '{mutation.description}' compiles on unchanged code")
        return problems

    def run_one(self, mutation: Mutation) -> MutationResult:
        """Plant one bug, judge it, and restore the files."""
        layer = self.config.layer_named(mutation.layer_name)
        try:
            self.planted_faults.plant_edits(list(mutation.edits), mutation.description)
        except PlantingError as error:
            raise MutationRunError(str(error)) from error
        try:
            status, build_output = run_command(["lake", "build", self.config.code_library], self.project_directory)
            if status != 0:
                # Where warnings are errors, some bugs never reach the proofs: an argument
                # the bug stops using, for instance, is an unused variable.
                reasons = [line.split(": ", 2)[-1] for line in build_output.splitlines()
                           if line.startswith("error: ") and "build failed" not in line]
                return MutationResult(mutation, reasons[0] if reasons else "no reason found", (), None)
            # Modules outside the probe hold the project's other theorems. The probe imports
            # them, so it can only run when they still build; otherwise their compiled form
            # would be stale.
            broken = [module for module in layer.also_builds
                      if run_command(["lake", "build", module], self.project_directory)[0] != 0]
            if not broken:
                broken = self.broken_claims(layer)
            refuted = None
            if mutation.refutation is not None:
                refuted, refutation_output = self.refutes(layer, mutation.refutation)
                if not refuted:
                    self.report(refutation_output[-1500:])
            return MutationResult(mutation, None, tuple(broken), refuted)
        finally:
            self.planted_faults.restore()

    def run(self) -> tuple[list[MutationResult], bool]:
        """Run the controls and then every mutation. Returns the results and whether every
        behaviour-changing bug was caught and refuted."""
        leftover = self.planted_faults.restore_leftover()
        if leftover:
            self.report(f"restored {len(leftover)} file(s) an interrupted run had left with a planted bug: "
                        f"{', '.join(leftover)}\n")
        self.probe_path.unlink(missing_ok=True)
        self.refutation_path.unlink(missing_ok=True)
        results: list[MutationResult] = []
        try:
            problems = self.control_problems()
            if problems:
                self.report("The controls on unchanged code failed, so no bug was planted:")
                for problem in problems:
                    self.report(f"  {problem}")
                return results, False
            refutation_count = sum(1 for mutation in self.mutations if mutation.refutation is not None)
            self.report(f"controls passed: no claim reads as broken on unchanged code, and none of the "
                        f"{refutation_count} refutations compiles on it\n")
            for mutation in self.mutations:
                result = self.run_one(mutation)
                results.append(result)
                if result.rejected_by_build is not None:
                    self.report(f"rejected  [{mutation.layer_name}] {mutation.description}")
                    self.report(f"          the build refuses it: {result.rejected_by_build}")
                    continue
                if mutation.changes_behaviour:
                    verdict = "caught" if result.caught else "SURVIVED"
                    self.report(f"{verdict:9} [{mutation.layer_name}] {mutation.description}")
                else:
                    # Nothing is expected of a change that keeps behaviour. A proof it breaks
                    # is a proof written against the exact old expression.
                    self.report(f"{'same':9} [{mutation.layer_name}] {mutation.description}   (keeps behaviour)")
                self.report(f"          broken proofs: {', '.join(result.broken) or 'none'}")
                if mutation.changes_behaviour:
                    outcome = "statement proved false" if result.refuted else "NOT REFUTED"
                    self.report(f"          {mutation.refuted_claim}: {outcome}")
        finally:
            self.probe_path.unlink(missing_ok=True)
            self.refutation_path.unlink(missing_ok=True)
            # Rebuild the unchanged project so that no mutated build output is left behind.
            run_command(["lake", "build", self.config.code_library, self.config.proofs_library,
                         self.config.spec_library], self.project_directory)

        judged = [result for result in results if result.rejected_by_build is None]
        behaviour_changing = [result for result in judged if result.mutation.changes_behaviour]
        same_behaviour = [result for result in judged if not result.mutation.changes_behaviour]
        rejected = [result for result in results if result.rejected_by_build is not None]
        caught = [result for result in behaviour_changing if result.caught]
        refuted = [result for result in behaviour_changing if result.refuted]
        self.report(f"\n{len(caught)} of {len(behaviour_changing)} behaviour-changing bugs broke at least one proof")
        self.report(f"{len(refuted)} of {len(behaviour_changing)} had their claim's statement proved false "
                    f"on the mutated code")
        self.report(f"{len(same_behaviour)} changed the code without changing behaviour: "
                    f"{sum(1 for result in same_behaviour if result.caught)} of them broke a proof")
        self.report(f"{len(rejected)} more never compiled, because the build refused them: "
                    f"{'; '.join(result.mutation.description for result in rejected) or 'none'}")
        passed = len(caught) == len(behaviour_changing) and len(refuted) == len(behaviour_changing)
        return results, passed
