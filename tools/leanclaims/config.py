"""
File: tools/leanclaims/config.py
Purpose: Reads and validates a project's `claims.toml`, the file that holds everything
the tools need to know about a project that is not a claim: its module names, its
layers, the axioms it allows, where its tests live, and the parts of its surface that
are tested or trusted instead of proved.

Validation is strict. An unknown key, a missing key, a value of the wrong type, a layer
whose pattern matches no file and a repeated layer name are all errors, each reported
with the place in the file it came from. A misspelt key therefore cannot be silently
ignored.
Created: 2026-11-13
"""

import tomllib
from dataclasses import dataclass
from pathlib import Path

CONFIG_FILE_NAME = "claims.toml"

# The kinds of requirement a waiver can lift, as `docs/audit.md` names them, and
# "mutation" for the rule that every claim is refuted by at least one planted bug.
WAIVER_KINDS = ("fails", "determines", "can hold", "mutation")


class ConfigError(Exception):
    """`claims.toml` is missing, is not valid TOML, or breaks a rule above."""


@dataclass(frozen=True)
class Layer:
    """A set of proof modules that share one namespace."""

    name: str
    namespace: str
    proof_files_pattern: str
    proof_files: tuple[Path, ...]
    refutation_prelude: str | None
    also_builds: tuple[str, ...]
    probe_files: tuple[Path, ...]


@dataclass(frozen=True)
class TestedEntry:
    """A part of the surface covered by a test, and the planted fault that fails it."""

    what: str
    test: str
    fault: str
    # The public declarations this entry covers, by full name. May be empty: an entry
    # can be about behaviour that is no single declaration's.
    declarations: tuple[str, ...] = ()


@dataclass(frozen=True)
class TrustedEntry:
    """A part of the surface that is neither proved nor tested, with the reason."""

    what: str
    why: str
    # The public declarations this entry covers, by full name. May be empty.
    declarations: tuple[str, ...] = ()


@dataclass(frozen=True)
class Waiver:
    """A requirement lifted for one claim, with the reason."""

    claim: int
    kind: str
    reason: str


@dataclass(frozen=True)
class ProjectConfig:
    """Everything `claims.toml` says about one project."""

    project_directory: Path
    name: str
    spec_module: str
    spec_library: str
    code_library: str
    # The root modules of the project's code. Every module whose name is one of these or
    # starts with one is code, unless it is a proof module. The library's name by default.
    code_modules: tuple[str, ...]
    proofs_library: str
    proofs_module: str
    verify_file: str
    allowed_axioms: tuple[str, ...]
    tests_directory: str
    tests_library: str
    tests_theorem_modules: tuple[str, ...]
    audit_modules: tuple[str, ...]
    layers: tuple[Layer, ...]
    tested: tuple[TestedEntry, ...]
    trusted: tuple[TrustedEntry, ...]
    waivers: tuple[Waiver, ...]

    def layer_named(self, layer_name: str) -> Layer:
        for layer in self.layers:
            if layer.name == layer_name:
                return layer
        raise ConfigError(f"no layer is named '{layer_name}'")


def _table(parent: dict, key: str, where: str) -> dict:
    value = parent.get(key)
    if not isinstance(value, dict):
        raise ConfigError(f"{where}: the table [{key}] is missing")
    return value


def _tables(parent: dict, key: str, where: str, required: bool) -> list[dict]:
    value = parent.get(key, [])
    if not isinstance(value, list) or not all(isinstance(entry, dict) for entry in value):
        raise ConfigError(f"{where}: [[{key}]] must be an array of tables")
    if required and not value:
        raise ConfigError(f"{where}: at least one [[{key}]] is required")
    return value


def _reject_unknown_keys(table: dict, known_keys: set[str], where: str) -> None:
    unknown = sorted(set(table) - known_keys)
    if unknown:
        raise ConfigError(f"{where}: unknown key {', '.join(unknown)}")


def _text(table: dict, key: str, where: str) -> str:
    value = table.get(key)
    if not isinstance(value, str) or not value.strip():
        raise ConfigError(f"{where}: '{key}' must be a non-empty string")
    return value


def _optional_text(table: dict, key: str, where: str) -> str | None:
    if key not in table:
        return None
    return _text(table, key, where)


def _texts(table: dict, key: str, where: str, required: bool) -> tuple[str, ...]:
    if key not in table and not required:
        return ()
    value = table.get(key)
    if not isinstance(value, list) or not all(isinstance(entry, str) and entry.strip() for entry in value):
        raise ConfigError(f"{where}: '{key}' must be a list of non-empty strings")
    if required and not value:
        raise ConfigError(f"{where}: '{key}' must not be empty")
    if len(set(value)) != len(value):
        raise ConfigError(f"{where}: '{key}' names something twice")
    return tuple(value)


def _read_layer(table: dict, project_directory: Path, where: str) -> Layer:
    _reject_unknown_keys(
        table, {"name", "namespace", "proof_files", "refutation_prelude", "also_builds", "probe_files"}, where)
    pattern = _text(table, "proof_files", where)
    proof_files = tuple(sorted(path for path in project_directory.glob(pattern) if path.is_file()))
    if not proof_files:
        raise ConfigError(f"{where}: proof_files = \"{pattern}\" matches no file")
    # The files joined into the mutation probe, in the order given. Each must be one of
    # the layer's proof files. Left out, the order is worked out from the files' imports.
    probe_files = []
    for relative_path in _texts(table, "probe_files", where, required=False):
        probe_file = (project_directory / relative_path).resolve()
        if probe_file not in proof_files:
            raise ConfigError(f"{where}: probe file {relative_path} is not one of the layer's proof files")
        probe_files.append(probe_file)
    return Layer(
        name=_text(table, "name", where),
        namespace=_text(table, "namespace", where),
        proof_files_pattern=pattern,
        proof_files=proof_files,
        refutation_prelude=_optional_text(table, "refutation_prelude", where),
        also_builds=_texts(table, "also_builds", where, required=False),
        probe_files=tuple(probe_files),
    )


def load_config(project_directory: Path) -> ProjectConfig:
    """Read and validate `claims.toml` in `project_directory`."""
    project_directory = project_directory.resolve()
    config_path = project_directory / CONFIG_FILE_NAME
    if not config_path.is_file():
        raise ConfigError(f"{config_path} does not exist")
    try:
        document = tomllib.loads(config_path.read_text(encoding="utf-8"))
    except tomllib.TOMLDecodeError as error:
        raise ConfigError(f"{config_path}: not valid TOML: {error}") from error

    where = CONFIG_FILE_NAME
    _reject_unknown_keys(document, {"project", "tests", "audit", "layer", "tested", "trusted", "waiver"}, where)

    project = _table(document, "project", where)
    _reject_unknown_keys(
        project, {"name", "spec_module", "spec_library", "code_library", "code_modules", "proofs_library",
                  "proofs_module", "verify_file", "allowed_axioms"}, "[project]")

    tests = _table(document, "tests", where)
    _reject_unknown_keys(tests, {"directory", "library", "theorem_modules"}, "[tests]")
    tests_directory = _text(tests, "directory", "[tests]")
    if not (project_directory / tests_directory).is_dir():
        raise ConfigError(f"[tests]: directory = \"{tests_directory}\" is not a directory")

    audit = document.get("audit", {})
    if not isinstance(audit, dict):
        raise ConfigError(f"{where}: [audit] must be a table")
    _reject_unknown_keys(audit, {"modules"}, "[audit]")

    layers = []
    for index, table in enumerate(_tables(document, "layer", where, required=True), start=1):
        layers.append(_read_layer(table, project_directory, f"[[layer]] number {index}"))
    layer_names = [layer.name for layer in layers]
    if len(set(layer_names)) != len(layer_names):
        raise ConfigError(f"{where}: two layers share a name")
    claimed_files: dict[Path, str] = {}
    for layer in layers:
        for proof_file in layer.proof_files:
            if proof_file in claimed_files:
                raise ConfigError(
                    f"{where}: {proof_file.relative_to(project_directory).as_posix()} belongs to both "
                    f"layer '{claimed_files[proof_file]}' and layer '{layer.name}'")
            claimed_files[proof_file] = layer.name

    tested = []
    for index, table in enumerate(_tables(document, "tested", where, required=False), start=1):
        entry_where = f"[[tested]] number {index}"
        _reject_unknown_keys(table, {"what", "test", "fault", "declarations"}, entry_where)
        tested.append(TestedEntry(
            what=_text(table, "what", entry_where),
            test=_text(table, "test", entry_where),
            fault=_text(table, "fault", entry_where),
            declarations=_texts(table, "declarations", entry_where, required=False)))

    trusted = []
    for index, table in enumerate(_tables(document, "trusted", where, required=False), start=1):
        entry_where = f"[[trusted]] number {index}"
        _reject_unknown_keys(table, {"what", "why", "declarations"}, entry_where)
        trusted.append(TrustedEntry(
            what=_text(table, "what", entry_where),
            why=_text(table, "why", entry_where),
            declarations=_texts(table, "declarations", entry_where, required=False)))

    waivers = []
    for index, table in enumerate(_tables(document, "waiver", where, required=False), start=1):
        entry_where = f"[[waiver]] number {index}"
        _reject_unknown_keys(table, {"claim", "kind", "reason"}, entry_where)
        claim = table.get("claim")
        # `bool` is a subclass of `int` in Python, and `claim = true` is not a number.
        if not isinstance(claim, int) or isinstance(claim, bool) or claim < 1:
            raise ConfigError(f"{entry_where}: 'claim' must be a claim number, 1 or greater")
        kind = _text(table, "kind", entry_where)
        if kind not in WAIVER_KINDS:
            raise ConfigError(f"{entry_where}: 'kind' must be one of {', '.join(WAIVER_KINDS)}")
        waivers.append(Waiver(claim=claim, kind=kind, reason=_text(table, "reason", entry_where)))
    if len({(waiver.claim, waiver.kind) for waiver in waivers}) != len(waivers):
        raise ConfigError(f"{where}: the same requirement is waived twice for one claim")

    return ProjectConfig(
        project_directory=project_directory,
        name=_text(project, "name", "[project]"),
        spec_module=_text(project, "spec_module", "[project]"),
        # The Lake library that holds the spec is named after its module unless said otherwise.
        spec_library=_optional_text(project, "spec_library", "[project]") or _text(project, "spec_module", "[project]"),
        code_library=_text(project, "code_library", "[project]"),
        code_modules=(_texts(project, "code_modules", "[project]", required=False)
                      or (_text(project, "code_library", "[project]"),)),
        proofs_library=_text(project, "proofs_library", "[project]"),
        proofs_module=_text(project, "proofs_module", "[project]"),
        verify_file=_text(project, "verify_file", "[project]"),
        allowed_axioms=_texts(project, "allowed_axioms", "[project]", required=True),
        tests_directory=tests_directory,
        tests_library=_text(tests, "library", "[tests]"),
        tests_theorem_modules=_texts(tests, "theorem_modules", "[tests]", required=False),
        audit_modules=_texts(audit, "modules", "[audit]", required=False),
        layers=tuple(layers),
        tested=tuple(tested),
        trusted=tuple(trusted),
        waivers=tuple(waivers),
    )
