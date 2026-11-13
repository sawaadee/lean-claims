"""
File: tools/leanclaims/sync.py
Purpose: Writes the three files that follow from the spec and `claims.toml`, so that a
claim's statement is written by hand once, in the spec, and nowhere else.

  1. `comparator.json` names every theorem of the spec for `lake comparator`, which
     confirms through independent kernels that the proofs prove exactly those statements.
  2. The verify file restates every theorem of the spec with `recall`, which fails to
     compile when a restatement differs from what is proved. It is part of the ordinary
     build, so that check runs wherever the project builds.
  3. The test package's `Axioms.lean` asserts that every theorem in every proof module
     and every listed test module rests only on the allowed axioms.

Nothing here writes to the spec. The direction is one way: spec to generated files.
Created: 2026-11-13
"""

import json
from pathlib import Path

from leanclaims.config import ProjectConfig
from leanclaims.lock import created_line
from leanclaims.spec import ClaimLine, Spec

COMPARATOR_FILE_NAME = "comparator.json"
LINE_WIDTH = 100


def module_name(relative_path: str) -> str:
    """The Lean module a source file holds: `Lib/Proofs/A.lean` is `Lib.Proofs.A`."""
    return relative_path.removesuffix(".lean").replace("/", ".")


def comparator_text(config: ProjectConfig, spec: Spec) -> str:
    document = {
        "challenge_module": config.spec_module,
        "solution_module": config.proofs_module,
        "theorem_names": [theorem.qualified_name for theorem in spec.theorems],
        "permitted_axioms": list(config.allowed_axioms),
    }
    return json.dumps(document, indent=2) + "\n"


def verify_text(config: ProjectConfig, spec: Spec, existing_text: str | None) -> str:
    lines = [
        "/-",
        f"  File: {config.verify_file}",
        f"  Purpose: Every claim of {spec.file_name} restated with `recall`. `recall` fails to compile",
        "  when the statement written here differs from the one proved, so the ordinary build",
        "  checks that the proofs prove what the spec states. Each `#print axioms` line reports",
        "  the axioms a claim rests on, for reading; the check that fails on an axiom outside",
        "  the allowed list is the axiom assertion in the test package.",
        "",
        f"  Written by `claims sync` from {spec.file_name}. Not edited by hand.",
        f"  {created_line(existing_text)}",
        "-/",
        "",
        f"import {config.proofs_module}",
        "",
    ]
    if spec.preamble_open_lines:
        lines.extend(spec.preamble_open_lines)
        lines.append("")
    for claim in spec.claims:
        lines.append(f"/-! ## Claim {claim.number}. {claim.title} -/")
        lines.append("")
        for part in claim.parts:
            if isinstance(part, ClaimLine):
                lines.append(part.text)
            else:
                lines.append(f"recall {part.name}{part.signature}")
                lines.append(f"#print axioms {part.name}")
            lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def _wrapped(words: list[str], indent: str) -> list[str]:
    """`words` laid out on lines no wider than LINE_WIDTH, each starting with `indent`."""
    lines = []
    current = indent
    for word in words:
        if current != indent and len(current) + 1 + len(word) > LINE_WIDTH:
            lines.append(current)
            current = indent
        current = current + word if current == indent else current + " " + word
    if current != indent:
        lines.append(current)
    return lines


def axioms_file_name(config: ProjectConfig) -> str:
    return f"{config.tests_directory}/Axioms.lean"


def axioms_text(config: ProjectConfig, existing_text: str | None) -> str:
    # Every proof file is listed, and Lean finds the theorems in each. Nothing is decided
    # here by reading the files, so a theorem the tools' reading of source text would not
    # see is asserted about like any other. A proof file may declare no theorem, as one
    # that only imports the others does, so the proof modules are asserted `across`.
    proof_modules = [
        module_name(proof_file.relative_to(config.project_directory).as_posix())
        for layer in config.layers
        for proof_file in layer.proof_files
    ]
    test_modules = list(config.audit_modules) + list(config.tests_theorem_modules)
    lines = [
        "/-",
        f"  File: {axioms_file_name(config)}",
        "  Purpose: Asserts that every theorem in the project's proof modules, and in the test",
        "  package's modules of theorems, rests only on the allowed axioms. A theorem that used",
        "  `sorry`, `native_decide` or a new axiom would make this file fail to compile, which",
        "  fails the build of the test library. The theorems are the ones Lean finds in each",
        "  module. The proof modules are checked together, since a proof file may only import",
        "  the others. A test module in which no theorem is found is an error, so a misspelt",
        "  or emptied one cannot pass by checking nothing.",
        "",
        "  Written by `claims sync` from `claims.toml`. Not edited by hand.",
        f"  {created_line(existing_text)}",
        "-/",
        "",
        "import LeanClaims",
        f"import {config.proofs_module}",
    ]
    lines.extend(f"import {module}" for module in test_modules)
    lines.append("")
    allowed = ", ".join(config.allowed_axioms)
    lines.append(f"#assert_axioms_among [{allowed}] across")
    lines.extend(_wrapped(proof_modules, indent="  "))
    if test_modules:
        lines.append("")
        lines.append(f"#assert_axioms_among [{allowed}] in")
        lines.extend(_wrapped(test_modules, indent="  "))
    return "\n".join(lines) + "\n"


def _existing_text(project_directory: Path, relative_path: str) -> str | None:
    path = project_directory / relative_path
    return path.read_text(encoding="utf-8") if path.is_file() else None


def generated_files(config: ProjectConfig, spec: Spec) -> dict[str, str]:
    """The text every generated file should hold, by path relative to the project."""
    project_directory = config.project_directory
    return {
        COMPARATOR_FILE_NAME: comparator_text(config, spec),
        config.verify_file: verify_text(config, spec, _existing_text(project_directory, config.verify_file)),
        axioms_file_name(config): axioms_text(
            config, _existing_text(project_directory, axioms_file_name(config))),
    }


def files_out_of_date(config: ProjectConfig, spec: Spec) -> list[str]:
    """The generated files whose text on disk differs from what would be written."""
    return [
        relative_path
        for relative_path, text in generated_files(config, spec).items()
        if _existing_text(config.project_directory, relative_path) != text
    ]


def write_generated_files(config: ProjectConfig, spec: Spec) -> list[str]:
    """Write every generated file that is out of date. Returns the files written."""
    written = []
    for relative_path, text in generated_files(config, spec).items():
        if _existing_text(config.project_directory, relative_path) != text:
            path = config.project_directory / relative_path
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
            written.append(relative_path)
    return written
