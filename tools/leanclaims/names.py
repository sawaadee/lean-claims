"""
File: tools/leanclaims/names.py
Purpose: Finds theorems declared more than once under one name within a layer. Lean
accepts some of these without a word, for example two `private` theorems in different
files, or a theorem repeated outside the namespace its file opens. A claim's name must
identify one theorem, because the spec, the comparator and the mutation run all refer to
theorems by name.

The check has two parts.

The first reads source text. It runs on files that do not compile, which is what lets it
report a duplicate before the build does, or where the build never would.

The second holds that reading to account. A pattern over text has blind spots: it does
not see a theorem behind `set_option … in`, or one a macro makes. So the project is
built, Lean is asked which theorems every proof module declares (the `#declared_theorems`
command of the LeanClaims package), and any difference from what was read in the text is
a failure. A theorem the text reading misses is then reported, not silently left out of
the search for duplicates. Theorems declared with `instance` are left out of the
comparison: the text reading is of `theorem` declarations, and an instance has a name
Lean makes up.
Created: 2026-11-13
"""

import json
import re
from collections import defaultdict
from dataclasses import dataclass

from leanclaims.config import ProjectConfig
from leanclaims.lean_source import declared_theorems
from leanclaims.process import run_command

DECLARED_PROBE_FILE_NAME = "LeanClaimsDeclaredProbe.lean"
_DECLARED_LINE = re.compile(r"declared-theorems (?P<document>\{.*\})\s*$", re.MULTILINE)


class NamesError(Exception):
    """Lean could not be asked which theorems the proof modules declare."""


@dataclass(frozen=True)
class DuplicateTheorem:
    """One name declared in more than one place within a layer."""

    layer_name: str
    namespace: str
    theorem_name: str
    places: tuple[str, ...]

    def describe(self) -> str:
        return f"{self.namespace}.{self.theorem_name} is declared in {' and '.join(self.places)}"


def find_duplicate_theorems(config: ProjectConfig) -> list[DuplicateTheorem]:
    """Every theorem name declared more than once among one layer's proof files, in the
    order of the layers and then of the names."""
    duplicates = []
    for layer in config.layers:
        places_by_name: dict[str, list[str]] = defaultdict(list)
        for proof_file in layer.proof_files:
            relative_path = proof_file.relative_to(config.project_directory).as_posix()
            for theorem in declared_theorems(proof_file.read_text(encoding="utf-8")):
                places_by_name[theorem.name].append(f"{relative_path}:{theorem.line_number}")
        for theorem_name, places in sorted(places_by_name.items()):
            if len(places) > 1:
                duplicates.append(DuplicateTheorem(
                    layer_name=layer.name,
                    namespace=layer.namespace,
                    theorem_name=theorem_name,
                    places=tuple(places)))
    return duplicates


def proof_module_count(config: ProjectConfig) -> int:
    return sum(len(layer.proof_files) for layer in config.layers)


def module_of_file(relative_path: str) -> str:
    """`Example/Proofs/Clamp.lean` is the module `Example.Proofs.Clamp`."""
    return relative_path.removesuffix(".lean").replace("/", ".")


def proof_files_by_module(config: ProjectConfig) -> dict[str, str]:
    """Every proof file of every layer, by module name, as a path relative to the project."""
    files = {}
    for layer in config.layers:
        for proof_file in layer.proof_files:
            relative_path = proof_file.relative_to(config.project_directory).as_posix()
            files[module_of_file(relative_path)] = relative_path
    return files


@dataclass(frozen=True)
class LeanDeclaredTheorem:
    """A theorem Lean reports a module to declare."""

    name: str
    module: str
    line_number: int
    is_instance: bool


def parse_declared_theorems(output: str) -> list[LeanDeclaredTheorem]:
    """Read the line `#declared_theorems` printed."""
    found = _DECLARED_LINE.search(output)
    if found is None:
        raise NamesError(f"Lean did not report the declared theorems:\n{output[-1500:]}")
    return [LeanDeclaredTheorem(entry["name"], entry["module"], entry["line"], entry["instance"])
            for entry in json.loads(found.group("document"))["theorems"]]


def lean_declared_theorems(config: ProjectConfig) -> list[LeanDeclaredTheorem]:
    """Build the test package, which builds the proofs it imports, and ask Lean which
    theorems every proof module declares."""
    tests_directory = config.project_directory / config.tests_directory
    status, output = run_command(["lake", "build"], tests_directory)
    if status != 0:
        raise NamesError(
            "the test package does not build, so the reading of the proof files could not be compared "
            f"with what Lean declares:\n{output[-3000:]}")
    modules = sorted(proof_files_by_module(config))
    probe_path = tests_directory / DECLARED_PROBE_FILE_NAME
    probe_path.write_text(
        f"import LeanClaims\nimport {config.proofs_module}\n\n#declared_theorems modules [{', '.join(modules)}]\n",
        encoding="utf-8")
    try:
        status, output = run_command(["lake", "env", "lean", DECLARED_PROBE_FILE_NAME], tests_directory)
    finally:
        probe_path.unlink(missing_ok=True)
    if status != 0:
        raise NamesError(f"Lean could not be asked which theorems the proof modules declare:\n{output[-3000:]}")
    return parse_declared_theorems(output)


def reading_differences(config: ProjectConfig, lean_theorems: list[LeanDeclaredTheorem]) -> list[str]:
    """Where the reading of the proof files as text and Lean's own list of their theorems
    differ. A theorem is the same in both when it is on the same line of the same file
    and the name in the text is the end of the name Lean gives."""
    files = proof_files_by_module(config)
    differences = []
    for module, relative_path in sorted(files.items()):
        read_in_text = {theorem.line_number: theorem.name for theorem in
                        declared_theorems((config.project_directory / relative_path).read_text(encoding="utf-8"))}
        declared = {theorem.line_number: theorem.name for theorem in lean_theorems
                    if theorem.module == module and not theorem.is_instance}
        for line_number, lean_name in sorted(declared.items()):
            text_name = read_in_text.pop(line_number, None)
            if text_name is None:
                differences.append(
                    f"{relative_path}:{line_number}: Lean declares the theorem {lean_name} here, and the reading of "
                    "the file as text did not find it")
            elif lean_name != text_name and not lean_name.endswith("." + text_name):
                differences.append(
                    f"{relative_path}:{line_number}: Lean declares the theorem {lean_name} here, and the reading of "
                    f"the file as text found '{text_name}'")
        for line_number, text_name in sorted(read_in_text.items()):
            differences.append(
                f"{relative_path}:{line_number}: the reading of the file as text found the theorem '{text_name}' "
                "here, and Lean declares none")
    return differences
