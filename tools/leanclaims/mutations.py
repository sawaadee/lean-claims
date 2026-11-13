"""
File: tools/leanclaims/mutations.py
Purpose: Reads and validates a project's `mutations.toml`, the catalog of bugs the
mutation run plants. A mutation is a small edit to the project's code, and either the
claim that edit must make false together with a Lean proof that it does, or a mark that
the edit changes the code without changing what it does.

Validation is strict, as for `claims.toml`: unknown keys, a layer that does not exist, a
claim the spec does not state in that layer's namespace, and a mutation that is neither
refuted nor marked as keeping behaviour are all errors.
Created: 2026-11-13
"""

import tomllib
from dataclasses import dataclass
from pathlib import Path

from leanclaims.config import ProjectConfig
from leanclaims.journal import Edit
from leanclaims.spec import Spec

MUTATIONS_FILE_NAME = "mutations.toml"


class MutationCatalogError(Exception):
    """`mutations.toml` is missing, is not valid TOML, or breaks a rule above."""


@dataclass(frozen=True)
class Mutation:
    """One bug to plant."""

    layer_name: str
    description: str
    edits: tuple[Edit, ...]
    # The claim the bug must make false and the proof of `False` from that claim's
    # statement on the mutated code. Both are None for a mutation that keeps behaviour.
    refuted_claim: str | None
    refutation: str | None

    @property
    def changes_behaviour(self) -> bool:
        return self.refutation is not None


def _require_text(table: dict, key: str, where: str) -> str:
    value = table.get(key)
    if not isinstance(value, str) or not value.strip():
        raise MutationCatalogError(f"{where}: '{key}' must be a non-empty string")
    return value


def load_mutations(config: ProjectConfig, spec: Spec, catalog_path: Path | None = None) -> list[Mutation]:
    """Read and validate the catalog. `catalog_path` names a file other than the
    project's own `mutations.toml`."""
    path = catalog_path or config.project_directory / MUTATIONS_FILE_NAME
    if not path.is_file():
        raise MutationCatalogError(f"{path} does not exist")
    try:
        document = tomllib.loads(path.read_text(encoding="utf-8"))
    except tomllib.TOMLDecodeError as error:
        raise MutationCatalogError(f"{path}: not valid TOML: {error}") from error
    unknown = sorted(set(document) - {"mutation"})
    if unknown:
        raise MutationCatalogError(f"{path.name}: unknown key {', '.join(unknown)}")
    tables = document.get("mutation", [])
    if not isinstance(tables, list) or not tables:
        raise MutationCatalogError(f"{path.name}: at least one [[mutation]] is required")

    claims_by_namespace: dict[str, set[str]] = {}
    for theorem in spec.theorems:
        claims_by_namespace.setdefault(theorem.namespace, set()).add(theorem.name)
    layers = {layer.name: layer for layer in config.layers}

    mutations = []
    seen: set[tuple[str, str]] = set()
    for index, table in enumerate(tables, start=1):
        where = f"[[mutation]] number {index}"
        unknown = sorted(set(table) - {"layer", "description", "refuted_claim", "refutation", "same_behaviour", "edit"})
        if unknown:
            raise MutationCatalogError(f"{where}: unknown key {', '.join(unknown)}")
        layer_name = _require_text(table, "layer", where)
        if layer_name not in layers:
            raise MutationCatalogError(f"{where}: no layer is named '{layer_name}'")
        description = _require_text(table, "description", where)
        where = f"{where} ({description})"
        if (layer_name, description) in seen:
            raise MutationCatalogError(f"{where}: this description is used twice in layer '{layer_name}'")
        seen.add((layer_name, description))

        edit_tables = table.get("edit", [])
        if not isinstance(edit_tables, list) or not edit_tables:
            raise MutationCatalogError(f"{where}: at least one [[mutation.edit]] is required")
        edits = []
        for edit_table in edit_tables:
            if set(edit_table) != {"file", "find", "replace"}:
                raise MutationCatalogError(f"{where}: an edit has exactly the keys file, find and replace")
            file_name = _require_text(edit_table, "file", where)
            if not (config.project_directory / file_name).is_file():
                raise MutationCatalogError(f"{where}: {file_name} does not exist")
            find, replace = edit_table["find"], edit_table["replace"]
            if not isinstance(find, str) or not find or not isinstance(replace, str):
                raise MutationCatalogError(f"{where}: 'find' must be a non-empty string and 'replace' a string")
            if find == replace:
                raise MutationCatalogError(f"{where}: an edit replaces its text with the same text")
            edits.append(Edit(file=file_name, find=find, replace=replace))

        same_behaviour = table.get("same_behaviour", False)
        if not isinstance(same_behaviour, bool):
            raise MutationCatalogError(f"{where}: 'same_behaviour' must be true or false")
        if same_behaviour:
            if "refuted_claim" in table or "refutation" in table:
                raise MutationCatalogError(f"{where}: a mutation that keeps behaviour refutes no claim")
            refuted_claim = refutation = None
        else:
            if "refuted_claim" not in table or "refutation" not in table:
                raise MutationCatalogError(
                    f"{where}: give 'refuted_claim' and 'refutation', or mark the mutation 'same_behaviour = true'")
            refuted_claim = _require_text(table, "refuted_claim", where)
            refutation = _require_text(table, "refutation", where)
            namespace = layers[layer_name].namespace
            if refuted_claim not in claims_by_namespace.get(namespace, set()):
                raise MutationCatalogError(
                    f"{where}: the spec states no theorem {namespace}.{refuted_claim}")
            if layers[layer_name].refutation_prelude is None:
                raise MutationCatalogError(
                    f"{where}: layer '{layer_name}' has no refutation_prelude in claims.toml")
        mutations.append(Mutation(
            layer_name=layer_name, description=description, edits=tuple(edits),
            refuted_claim=refuted_claim, refutation=refutation))
    return mutations
