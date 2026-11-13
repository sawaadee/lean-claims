"""
File: tools/leanclaims/faults.py
Purpose: The faults a project plants to show that its checks can fail, and the checks
they are planted for. A check that has never been seen to fail has not been shown to
work, so for every check there is a fault it exists to catch, and the check must fail
when that fault is planted.

A check is a command run in a directory. Eight are built in and need no entry:
  lock        `claims lock --check`
  sync        `claims sync --check`
  names       `claims names`
  build       `lake build` in the project
  axioms      `lake build` of the test library, which holds the axiom assertion
  comparator  `lake comparator --paranoid`
  audit       `claims audit`
  trust       `claims trust --check`
A project declares its own, such as its test suite, in `faults.toml`.

A fault is a set of edits, or a change to the environment a check runs in, with the
check it is planted for and the text that check's output must hold. A fault is caught
only when the check fails and its output names what was planted, so that a failure for
some other reason is not counted.

`faults.toml` is optional. Without it a project still gets the generated faults, which
are built from its spec and `claims.toml` alone.
Created: 2026-11-13
"""

import sys
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

from leanclaims.config import ProjectConfig
from leanclaims.journal import Edit, PlantingError, texts_after_edits

FAULTS_FILE_NAME = "faults.toml"
BUILT_IN_CHECK_IDS = ("lock", "sync", "names", "build", "axioms", "comparator", "audit", "trust")


class FaultCatalogError(Exception):
    """`faults.toml` is not valid TOML or breaks a rule above."""


@dataclass(frozen=True)
class Check:
    """A command whose failure means something is wrong with the project."""

    check_id: str
    command: tuple[str, ...]
    # Relative to the project directory.
    directory: str


@dataclass(frozen=True)
class PlannedFault:
    """A fault ready to plant: the full new text of every file it changes, the check it
    is planted for, and how that check's output shows the fault was the reason."""

    fault_id: str
    description: str
    check_id: str
    new_texts: dict[str, str]
    # Every one of these must be in the check's output.
    expected_in_output: tuple[str, ...] = ()
    # At least one of these must be in the check's output, when any are given.
    expected_any_in_output: tuple[str, ...] = ()
    # Environment variables set for the check while the fault is planted.
    environment: dict[str, str] = field(default_factory=dict)

    def is_caught_by(self, exit_status: int, output: str) -> tuple[bool, str]:
        if exit_status == 0:
            return False, "the check passed with the fault planted"
        missing = [text for text in self.expected_in_output if text not in output]
        if missing:
            return False, f"the check failed without mentioning {missing}:\n{output[-1500:]}"
        if self.expected_any_in_output and not any(text in output for text in self.expected_any_in_output):
            return False, f"the check failed without mentioning any of {list(self.expected_any_in_output)}:\n{output[-1500:]}"
        return True, ""


def built_in_checks(config: ProjectConfig, tools_directory: Path) -> dict[str, Check]:
    """The eight checks every project has."""
    claims = (sys.executable, "-I", str(tools_directory / "claims.py"), "--project", str(config.project_directory))
    return {
        "lock": Check("lock", claims + ("lock", "--check"), "."),
        "sync": Check("sync", claims + ("sync", "--check"), "."),
        "names": Check("names", claims + ("names",), "."),
        "build": Check("build", ("lake", "build"), "."),
        "axioms": Check("axioms", ("lake", "build", config.tests_library), config.tests_directory),
        # Every kernel the comparator has, not only the default ones. A proof that one of
        # them cannot check is a finding, whichever one it is.
        "comparator": Check("comparator", ("lake", "comparator", "--paranoid"), "."),
        "audit": Check("audit", claims + ("audit",), "."),
        "trust": Check("trust", claims + ("trust", "--check"), "."),
    }


def _text(table: dict, key: str, where: str) -> str:
    value = table.get(key)
    if not isinstance(value, str) or not value.strip():
        raise FaultCatalogError(f"{where}: '{key}' must be a non-empty string")
    return value


def _texts(table: dict, key: str, where: str) -> tuple[str, ...]:
    value = table.get(key, [])
    if not isinstance(value, list) or not all(isinstance(entry, str) and entry for entry in value):
        raise FaultCatalogError(f"{where}: '{key}' must be a list of non-empty strings")
    return tuple(value)


def load_fault_catalog(config: ProjectConfig, catalog_path: Path | None = None,
                       apply_edits: bool = True) -> tuple[dict[str, Check], list[PlannedFault]]:
    """Read `faults.toml`: the checks it declares and the faults it lists, each fault with
    its edits already applied to the files' current text. A project with no `faults.toml`
    has neither. `catalog_path` names a file other than the project's own.

    With `apply_edits` false the edits are read and not applied, and the faults carry no
    new text. `claims audit` reads the catalog this way: it needs each fault's id and
    check, and it must give its answer while a fault of the catalog is planted, when
    that fault's own edit no longer finds its text."""
    path = catalog_path or config.project_directory / FAULTS_FILE_NAME
    if not path.is_file():
        if catalog_path is not None:
            raise FaultCatalogError(f"{path} does not exist")
        return {}, []
    try:
        document = tomllib.loads(path.read_text(encoding="utf-8"))
    except tomllib.TOMLDecodeError as error:
        raise FaultCatalogError(f"{path}: not valid TOML: {error}") from error
    unknown = sorted(set(document) - {"check", "fault"})
    if unknown:
        raise FaultCatalogError(f"{path.name}: unknown key {', '.join(unknown)}")

    checks: dict[str, Check] = {}
    for index, table in enumerate(document.get("check", []), start=1):
        where = f"[[check]] number {index}"
        unknown = sorted(set(table) - {"id", "command", "directory"})
        if unknown:
            raise FaultCatalogError(f"{where}: unknown key {', '.join(unknown)}")
        check_id = _text(table, "id", where)
        if check_id in BUILT_IN_CHECK_IDS:
            raise FaultCatalogError(f"{where}: '{check_id}' is the name of a built-in check")
        if check_id in checks:
            raise FaultCatalogError(f"{where}: the id '{check_id}' is used twice")
        command = _texts(table, "command", where)
        if not command:
            raise FaultCatalogError(f"{where}: 'command' must name a program")
        directory = table.get("directory", ".")
        if not isinstance(directory, str) or not (config.project_directory / directory).is_dir():
            raise FaultCatalogError(f"{where}: directory '{directory}' is not a directory of the project")
        checks[check_id] = Check(check_id, command, directory)

    faults = []
    fault_ids: set[str] = set()
    for index, table in enumerate(document.get("fault", []), start=1):
        where = f"[[fault]] number {index}"
        unknown = sorted(set(table) - {"id", "description", "check", "caught_when_output_has",
                                       "caught_when_output_has_any", "environment", "edit"})
        if unknown:
            raise FaultCatalogError(f"{where}: unknown key {', '.join(unknown)}")
        fault_id = _text(table, "id", where)
        where = f"{where} ({fault_id})"
        if fault_id in fault_ids:
            raise FaultCatalogError(f"{where}: the id is used twice")
        fault_ids.add(fault_id)
        check_id = _text(table, "check", where)
        if check_id not in checks and check_id not in BUILT_IN_CHECK_IDS:
            raise FaultCatalogError(f"{where}: no check is named '{check_id}'")
        expected = _texts(table, "caught_when_output_has", where)
        expected_any = _texts(table, "caught_when_output_has_any", where)
        if not expected and not expected_any:
            raise FaultCatalogError(
                f"{where}: say what the check's output must hold, so that a failure for another reason is not counted")
        environment = table.get("environment", {})
        if not isinstance(environment, dict) or not all(isinstance(value, str) for value in environment.values()):
            raise FaultCatalogError(f"{where}: 'environment' must be a table of strings")
        edits = []
        for edit_table in table.get("edit", []):
            if not isinstance(edit_table, dict) or set(edit_table) != {"file", "find", "replace"}:
                raise FaultCatalogError(f"{where}: an edit has exactly the keys file, find and replace")
            if not (config.project_directory / str(edit_table["file"])).is_file():
                raise FaultCatalogError(f"{where}: {edit_table['file']} does not exist")
            edits.append(Edit(file=edit_table["file"], find=edit_table["find"], replace=edit_table["replace"]))
        if not edits and not environment:
            raise FaultCatalogError(f"{where}: a fault changes a file or the environment, and this one changes neither")
        new_texts: dict[str, str] = {}
        if apply_edits:
            try:
                new_texts = texts_after_edits(config.project_directory, edits, fault_id)
            except PlantingError as error:
                raise FaultCatalogError(f"{where}: {error}") from error
        faults.append(PlannedFault(
            fault_id=fault_id, description=_text(table, "description", where), check_id=check_id,
            new_texts=new_texts, expected_in_output=expected, expected_any_in_output=expected_any,
            environment=dict(environment)))
    return checks, faults
