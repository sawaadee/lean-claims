"""
File: tools/claims.py
Purpose: The one entry point of the lean-claims tools. Each subcommand is one check or
one generator, run against the project in the current directory or the one named with
`--project`.

Subcommands:
  config          read and validate `claims.toml`, and print what it says
  names           fail when a theorem is declared twice under one name within a layer,
                  or when the theorems read from the proof files' text are not the
                  ones Lean declares
  lock --check    fail when the spec differs from what `spec.lock` records
  lock --update   rewrite `spec.lock` from the spec; the only way the lock changes
  sync            check the spec's rules and the lock, then write `comparator.json`, the
                  verify file and the test package's `Axioms.lean`
  sync --check    the same checks, and fail when a generated file is out of date,
                  without writing anything
  mutate          plant each bug of `mutations.toml` in turn and require a proof to
                  break and the claim to be proved false; `--layer NAME` runs one
                  layer's mutations, `--catalog FILE` reads another catalog
  checks          plant, for each check, the fault it exists to catch, and require the
                  check to fail: the generated faults and those of `faults.toml`;
                  `--catalog FILE` reads another catalog
  audit           build the test package, then require every claim to have its audit
                  theorems and a mutation, or a written waiver, every `Audit:` line to
                  be confirmed by Lean, and every tested entry its fault
  trust           build the test package, require every public declaration of the code to
                  be proved, tested or trusted, and write `TRUST.md`
  trust --check   the same requirement, and fail when `TRUST.md` is out of date, without
                  writing anything
  verify          run every check in order and say which passed; `--full` also runs
                  `mutate` and `checks`
  new DIRECTORY --name NAME
                  start a project from the starter project, renamed, with every check
                  passing

Usage: python3 -I tools/claims.py [--project DIRECTORY] SUBCOMMAND [OPTION]
Exit status: 0 when the check passes, 1 when it fails, 2 when it could not run.
Created: 2026-11-13
"""

import argparse
import sys
from pathlib import Path

# `python3 -I` leaves the script's own directory off the import path, so it is added here.
sys.path.insert(0, str(Path(__file__).resolve().parent))

from leanclaims.audit import AuditError, audit, lean_audit_facts  # noqa: E402
from leanclaims.checks import ChecksRun  # noqa: E402
from leanclaims.config import ConfigError, ProjectConfig, load_config  # noqa: E402
from leanclaims.faults import FaultCatalogError, load_fault_catalog  # noqa: E402
from leanclaims.lock import LOCK_FILE_NAME, lock_differences, lock_text  # noqa: E402
from leanclaims.mutate import MutationRun, MutationRunError  # noqa: E402
from leanclaims.mutations import MutationCatalogError, load_mutations  # noqa: E402
from leanclaims.new_project import LeanClaimsSource, NewProjectError, create_project  # noqa: E402
from leanclaims.names import (NamesError, find_duplicate_theorems, lean_declared_theorems,  # noqa: E402
                              proof_module_count, reading_differences)
from leanclaims.spec import Spec, SpecError, load_spec  # noqa: E402
from leanclaims.sync import files_out_of_date, write_generated_files  # noqa: E402
from leanclaims.verify import verify  # noqa: E402
from leanclaims.trust import (TRUST_FILE_NAME, TrustError, lean_surface_facts, surface_levels,  # noqa: E402
                              trust_text)

EXIT_PASSED = 0
EXIT_FAILED = 1
EXIT_COULD_NOT_RUN = 2


def run_config(config: ProjectConfig, arguments: argparse.Namespace) -> int:
    print(f"project {config.name}: spec module {config.spec_module}, proofs module {config.proofs_module}")
    print(f"allowed axioms: {', '.join(config.allowed_axioms)}")
    print(f"tests: library {config.tests_library} in {config.tests_directory}/")
    for layer in config.layers:
        print(f"layer '{layer.name}': namespace {layer.namespace}, {len(layer.proof_files)} proof files "
              f"matching {layer.proof_files_pattern}")
    print(f"audit modules: {len(config.audit_modules)}; tested entries: {len(config.tested)}; "
          f"trusted entries: {len(config.trusted)}; waivers: {len(config.waivers)}")
    return EXIT_PASSED


def run_names(config: ProjectConfig, arguments: argparse.Namespace) -> int:
    duplicates = find_duplicate_theorems(config)
    if duplicates:
        print("theorems declared more than once:")
        for duplicate in duplicates:
            print(f"  {duplicate.describe()}")
        return EXIT_FAILED
    try:
        lean_theorems = lean_declared_theorems(config)
    except NamesError as error:
        print(str(error), file=sys.stderr)
        return EXIT_COULD_NOT_RUN
    differences = reading_differences(config, lean_theorems)
    if differences:
        print("the proof files as read from their text differ from what Lean declares:")
        for difference in differences:
            print(f"  {difference}")
        return EXIT_FAILED
    written = sum(1 for theorem in lean_theorems if not theorem.is_instance)
    print(f"no theorem is declared twice in the {proof_module_count(config)} proof modules, and the {written} "
          "theorems read from their text are the ones Lean declares")
    return EXIT_PASSED


def spec_summary(spec: Spec) -> str:
    withdrawn = sum(1 for claim in spec.claims if claim.withdrawn)
    return (f"{len(spec.claims)} claims ({withdrawn} withdrawn) and {len(spec.theorems)} theorems "
            f"in {spec.file_name}")


def report_lock_differences(differences: list[str]) -> None:
    print(f"the spec differs from {LOCK_FILE_NAME}:")
    for difference in differences:
        print(f"  {difference}")
    print("if the change to the claims is intended, run: claims lock --update")


def run_lock(config: ProjectConfig, arguments: argparse.Namespace) -> int:
    spec = load_spec(config)
    lock_path = config.project_directory / LOCK_FILE_NAME
    if arguments.update:
        existing_text = lock_path.read_text(encoding="utf-8") if lock_path.is_file() else None
        differences = lock_differences(spec, config.project_directory)
        lock_path.write_text(lock_text(spec, existing_text), encoding="utf-8")
        if differences:
            print(f"{LOCK_FILE_NAME} rewritten:")
            for difference in differences:
                print(f"  {difference}")
        else:
            print(f"{LOCK_FILE_NAME} already matched the spec")
        return EXIT_PASSED
    differences = lock_differences(spec, config.project_directory)
    if differences:
        report_lock_differences(differences)
        return EXIT_FAILED
    print(f"{LOCK_FILE_NAME} matches the spec: {spec_summary(spec)}")
    return EXIT_PASSED


def run_sync(config: ProjectConfig, arguments: argparse.Namespace) -> int:
    spec = load_spec(config)
    differences = lock_differences(spec, config.project_directory)
    if differences:
        report_lock_differences(differences)
        return EXIT_FAILED
    if arguments.check:
        out_of_date = files_out_of_date(config, spec)
        if out_of_date:
            print("generated files are out of date; run: claims sync")
            for relative_path in out_of_date:
                print(f"  {relative_path}")
            return EXIT_FAILED
        print(f"the generated files are up to date with {spec_summary(spec)}")
        return EXIT_PASSED
    written = write_generated_files(config, spec)
    print(f"{spec_summary(spec)}; wrote {', '.join(written) if written else 'nothing, every file was up to date'}")
    return EXIT_PASSED


def run_mutate(config: ProjectConfig, arguments: argparse.Namespace) -> int:
    spec = load_spec(config)
    differences = lock_differences(spec, config.project_directory)
    if differences:
        report_lock_differences(differences)
        return EXIT_FAILED
    try:
        mutations = load_mutations(config, spec, arguments.catalog)
    except MutationCatalogError as error:
        print(str(error), file=sys.stderr)
        return EXIT_COULD_NOT_RUN
    if arguments.layer is not None:
        config.layer_named(arguments.layer)
        mutations = [mutation for mutation in mutations if mutation.layer_name == arguments.layer]
    try:
        _, passed = MutationRun(config, spec, mutations, report=lambda line: print(line, flush=True)).run()
    except MutationRunError as error:
        print(str(error), file=sys.stderr)
        return EXIT_COULD_NOT_RUN
    return EXIT_PASSED if passed else EXIT_FAILED


def run_checks(config: ProjectConfig, arguments: argparse.Namespace) -> int:
    spec = load_spec(config)
    differences = lock_differences(spec, config.project_directory)
    if differences:
        report_lock_differences(differences)
        return EXIT_FAILED
    try:
        declared_checks, catalog_faults = load_fault_catalog(config, arguments.catalog)
    except FaultCatalogError as error:
        print(str(error), file=sys.stderr)
        return EXIT_COULD_NOT_RUN
    run = ChecksRun(config, spec, declared_checks, catalog_faults, report=lambda line: print(line, flush=True))
    return EXIT_PASSED if run.run() else EXIT_FAILED


def run_audit(config: ProjectConfig, arguments: argparse.Namespace) -> int:
    spec = load_spec(config)
    differences = lock_differences(spec, config.project_directory)
    if differences:
        report_lock_differences(differences)
        return EXIT_FAILED
    try:
        mutations = load_mutations(config, spec)
        declared_checks, catalog_faults = load_fault_catalog(config, apply_edits=False)
        report = audit(config, spec, mutations, declared_checks, catalog_faults, lean_audit_facts(config, spec))
    except (MutationCatalogError, FaultCatalogError, AuditError) as error:
        print(str(error), file=sys.stderr)
        return EXIT_COULD_NOT_RUN
    for claim in report.claims:
        can_hold = str(len(claim.can_hold)) if claim.has_hypotheses else "no hypotheses"
        waived = f"; waived: {', '.join(claim.waived)}" if claim.waived else ""
        print(f"claim {claim.number}: fails {len(claim.fails)}, determines {len(claim.determines)}, "
              f"can hold {can_hold}, mutations {claim.mutations}{waived}")
    print(f"{report.audit_theorem_count} theorems with an Audit line in {len(config.audit_modules)} modules, "
          f"{report.untagged_theorem_count} other theorems there; {len(config.tested)} tested entries; "
          f"{len(config.waivers)} waivers")
    if report.problems:
        print(f"{len(report.problems)} problems:")
        for problem in report.problems:
            print(f"  {problem}")
        return EXIT_FAILED
    print(f"every one of the {len(report.claims)} claims has its audits and a mutation, or a waiver")
    return EXIT_PASSED


def run_trust(config: ProjectConfig, arguments: argparse.Namespace) -> int:
    spec = load_spec(config)
    differences = lock_differences(spec, config.project_directory)
    if differences:
        report_lock_differences(differences)
        return EXIT_FAILED
    try:
        mutations = load_mutations(config, spec)
        _, catalog_faults = load_fault_catalog(config, apply_edits=False)
        facts = lean_surface_facts(config, spec)
    except (MutationCatalogError, FaultCatalogError, TrustError) as error:
        print(str(error), file=sys.stderr)
        return EXIT_COULD_NOT_RUN
    levels, problems = surface_levels(config, spec, facts)
    trust_path = config.project_directory / TRUST_FILE_NAME
    existing_text = trust_path.read_text(encoding="utf-8") if trust_path.is_file() else None
    new_text = trust_text(config, spec, facts, levels, mutations, catalog_faults, existing_text)
    passed = not problems
    if arguments.check:
        if existing_text != new_text:
            print(f"{TRUST_FILE_NAME} is out of date; run: claims trust")
            passed = False
    elif existing_text != new_text:
        trust_path.write_text(new_text, encoding="utf-8")
        print(f"wrote {TRUST_FILE_NAME}")
    counts = {level_name: sum(1 for level in levels if level_name in level.levels)
              for level_name in ("proved", "tested", "trusted", "supporting", "theorem")}
    print(f"{len(levels)} public declarations: {counts['proved']} mentioned by a claim, {counts['tested']} tested, "
          f"{counts['trusted']} trusted, {counts['supporting']} supporting, {counts['theorem']} a theorem of the code, "
          f"{sum(1 for level in levels if not level.levels)} at no level")
    if problems:
        print(f"{len(problems)} problems:")
        for problem in problems:
            print(f"  {problem}")
    if passed:
        print(f"every public declaration is at a level, and {TRUST_FILE_NAME} says so")
    return EXIT_PASSED if passed else EXIT_FAILED


def run_verify(config: ProjectConfig, arguments: argparse.Namespace) -> int:
    try:
        declared_checks, _ = load_fault_catalog(config, apply_edits=False)
    except FaultCatalogError as error:
        print(str(error), file=sys.stderr)
        return EXIT_COULD_NOT_RUN
    results = verify(config, declared_checks, arguments.full, report=lambda line: print(line, flush=True))
    failed = [result.check_id for result in results if not result.passed]
    if failed:
        print(f"{len(failed)} of {len(results)} failed: {', '.join(failed)}")
        return EXIT_FAILED
    print(f"all {len(results)} passed" + ("" if arguments.full else
                                         "; the mutation run and the test of the checks were not run (--full)"))
    return EXIT_PASSED


def run_new(arguments: argparse.Namespace) -> int:
    """Create a project. This is the one subcommand that is not run against a project."""
    if arguments.leanclaims_git is not None:
        if arguments.leanclaims_rev is None:
            print("--leanclaims-git needs --leanclaims-rev, the commit to pin", file=sys.stderr)
            return EXIT_COULD_NOT_RUN
        source = LeanClaimsSource(git_url=arguments.leanclaims_git, revision=arguments.leanclaims_rev)
    else:
        source = LeanClaimsSource(path=(arguments.leanclaims_path or Path(__file__).resolve().parent.parent).resolve())
    try:
        written = create_project(arguments.directory.resolve(), arguments.name, source)
    except (NewProjectError, ConfigError, SpecError) as error:
        print(str(error), file=sys.stderr)
        return EXIT_COULD_NOT_RUN
    print(f"created the project {arguments.name} in {arguments.directory}: {len(written)} files")
    print("next, in that directory:")
    print("  lake build && (cd tests && lake build)")
    print(f"  python3 -I {Path(__file__).resolve()} verify")
    return EXIT_PASSED


def main() -> int:
    parser = argparse.ArgumentParser(prog="claims", description="The lean-claims checks.")
    parser.add_argument("--project", type=Path, default=Path.cwd(),
                        help="the project directory holding claims.toml (default: the current directory)")
    subparsers = parser.add_subparsers(dest="subcommand", required=True)
    subparsers.add_parser("config", help="validate claims.toml and print it").set_defaults(run=run_config)
    subparsers.add_parser("names", help="no theorem declared twice in a layer").set_defaults(run=run_names)
    lock_parser = subparsers.add_parser("lock", help="the spec lock")
    lock_mode = lock_parser.add_mutually_exclusive_group(required=True)
    lock_mode.add_argument("--check", action="store_true", help="fail when the spec differs from the lock")
    lock_mode.add_argument("--update", action="store_true", help="rewrite the lock from the spec")
    lock_parser.set_defaults(run=run_lock)
    sync_parser = subparsers.add_parser("sync", help="write the files generated from the spec")
    sync_parser.add_argument("--check", action="store_true", help="fail when a generated file is out of date")
    sync_parser.set_defaults(run=run_sync)
    mutate_parser = subparsers.add_parser("mutate", help="plant the bugs of mutations.toml")
    mutate_parser.add_argument("--layer", help="run only this layer's mutations")
    mutate_parser.add_argument("--catalog", type=Path, help="a catalog other than the project's mutations.toml")
    mutate_parser.set_defaults(run=run_mutate)
    checks_parser = subparsers.add_parser("checks", help="plant the fault each check exists to catch")
    checks_parser.add_argument("--catalog", type=Path, help="a catalog other than the project's faults.toml")
    checks_parser.set_defaults(run=run_checks)
    subparsers.add_parser("audit", help="every claim has its audits and a mutation").set_defaults(run=run_audit)
    trust_parser = subparsers.add_parser("trust", help="every public declaration is proved, tested or trusted")
    trust_parser.add_argument("--check", action="store_true", help="fail when TRUST.md is out of date")
    trust_parser.set_defaults(run=run_trust)
    verify_parser = subparsers.add_parser("verify", help="run every check and say which passed")
    verify_parser.add_argument("--full", action="store_true", help="also run the mutation run and the test of the checks")
    verify_parser.set_defaults(run=run_verify)
    new_parser = subparsers.add_parser("new", help="start a project from the starter project")
    new_parser.add_argument("directory", type=Path, help="the directory to create, which must not exist or be empty")
    new_parser.add_argument("--name", required=True, help="the project's name, as in JsonParser")
    new_parser.add_argument("--leanclaims-path", type=Path,
                            help="a directory holding the LeanClaims package (default: this checkout)")
    new_parser.add_argument("--leanclaims-git", help="a git repository holding the LeanClaims package")
    new_parser.add_argument("--leanclaims-rev", help="the commit of that repository to pin")
    new_parser.set_defaults(run=None)
    arguments = parser.parse_args()

    if arguments.subcommand == "new":
        return run_new(arguments)
    try:
        config = load_config(arguments.project)
    except ConfigError as error:
        print(f"claims.toml: {error}", file=sys.stderr)
        return EXIT_COULD_NOT_RUN
    try:
        return arguments.run(config, arguments)
    except SpecError as error:
        print(str(error), file=sys.stderr)
        return EXIT_FAILED


if __name__ == "__main__":
    sys.exit(main())
