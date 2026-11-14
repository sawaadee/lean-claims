"""
File: tools/leanclaims/trust.py
Purpose: The trust report and the surface check. A project can prove every claim it
makes and still ship a function no claim mentions. `claims trust` asks Lean for every
public declaration of the project's code and for what each claim's statement mentions
(the `#surface_facts` command of the LeanClaims package, described in
`LeanClaims/Surface.lean`), and requires every declaration to stand at one of these
levels:

  proved    The statement of at least one claim theorem mentions it.
  tested    A `[[tested]]` entry of `claims.toml` lists it, with a test and a planted
            fault the test has been seen to catch.
  trusted   A `[[trusted]]` entry lists it, with the reason.
  supporting  No claim's statement mentions it, and a declaration that a claim does
            mention is defined by it, directly or through other definitions. The claims
            bind it as far as the mentioned declaration uses it and no further. It is
            listed apart so that nobody reads it as proved in its own right.
  theorem   It is a theorem of the code itself, checked by Lean's kernel like any other.

A declaration at none of them fails the check: state a claim about it, make it private,
or write the entry that says it is tested or trusted.

The supporting level exists because Lean's `private` hides a definition from the proofs
in other files too. A helper that the proofs must unfold cannot be private, and calling
it trusted would say something untrue.

Being mentioned by a claim is not enough for a declaration whose running code is not its
definition (`@[extern]`, `@[implemented_by]`), or that has no definition to prove
anything about (an axiom, an opaque constant). The claims are about the definition, so
such a declaration also needs a tested or trusted entry.

A `@[csimp]` theorem also has the compiler run other code than a definition. It states
`@f = @g`, and the compiler uses `g` wherever later code names `f`. The kernel checks the
statement, so one that depends on the standard axioms only is proved and the report
lists it. One that depends on any other axiom shows nothing about the compiled code, and
needs a tested or trusted entry that lists the replaced declaration or the statement.

`@[extern]` and `@[implemented_by]` can also be put on a private definition that a
public one calls. An entry can list only a public declaration, so such a definition
always fails the check: it is made public and listed, or the attribute comes off. Lean
generates such definitions itself for a type with a computed field. Those belong to the
type, and the entry that lists the type accounts for them.

What is replaced need not be a public declaration: it can be a private helper, or a
function of Lean or of a dependency that the project's code calls. So the rule is applied
to every statement of that form in the project's modules, and not to the public
declarations one by one. It is applied whether or not Lean has the statement registered
as a replacement, because `attribute [local csimp]` puts one in force for a section and
Lean keeps no record of it afterwards.

The report, `TRUST.md`, is written from the spec, `claims.toml`, the catalogs and what
Lean reports, and from nothing else, so writing it twice gives the same file and
`claims trust --check` can fail when the committed file is out of date. It holds every
claim with the declarations it mentions, the vocabulary a reviewer must read, every
public declaration with its level, the tested and trusted entries, the waivers, and what
the mutation and fault catalogs plant.

What this check cannot do: a mention is not a guarantee. A claim may mention a function
and say little about it. The audit and the mutation run are the checks on that.
Created: 2026-11-13
Revised: 2026-11-14 (compiled replacements: every statement that is or could be a `@[csimp]`
replacement, and the entry one needs when an axiom is behind it; definitions that are not public
and run other code than their definition)
"""

import json
import re
from dataclasses import dataclass

from leanclaims.config import ProjectConfig
from leanclaims.faults import PlannedFault
from leanclaims.lock import created_line
from leanclaims.mutations import Mutation
from leanclaims.names import module_of_file, proof_files_by_module
from leanclaims.process import run_command
from leanclaims.spec import Spec

TRUST_FILE_NAME = "TRUST.md"
SURFACE_PROBE_FILE_NAME = "LeanClaimsSurfaceProbe.lean"
_FACTS_LINE = re.compile(r"surface-facts (?P<document>\{.*\})\s*$", re.MULTILINE)
# The kinds of declaration whose running code, or lack of a definition, the proofs do
# not reach.
KINDS_WITHOUT_A_DEFINITION = ("axiom", "opaque")


class TrustError(Exception):
    """Lean could not be asked about the project's surface."""


@dataclass(frozen=True)
class CompiledReplacement:
    """A constant of the project that states `@f = @g`, the form of a `@[csimp]` theorem,
    with which the compiler runs `g` wherever later code names `f`."""

    # The constant that makes the statement: a theorem, or an axiom.
    statement: str
    statement_is_public: bool
    module: str
    line_number: int
    replaced: str
    # Whether what is replaced is a public declaration of the project. It can also be a
    # private one, or a function from outside the project.
    replaced_is_public: bool
    replacement: str
    # Whether Lean has the statement registered as a replacement where the code and the
    # proofs are imported. One that is not can still have been put in force with
    # `attribute [local csimp]`, of which Lean keeps no record.
    is_registered: bool
    # The namespace that must be open for a registered replacement to be in force, or
    # `None` when it is in force everywhere.
    namespace: str | None
    # The axioms the statement depends on beyond the standard ones. Empty when it is proved.
    axioms: tuple[str, ...]


@dataclass(frozen=True)
class SurfaceDeclaration:
    """A public declaration of the project's code, as Lean reports it."""

    name: str
    module: str
    line_number: int
    kind: str
    is_extern: bool
    implemented_by: str | None
    # The qualified names of the claim theorems whose statements mention it.
    stated_by: tuple[str, ...]


@dataclass(frozen=True)
class HiddenCode:
    """A definition of the code that is not a public declaration and whose running code is
    not its definition."""

    name: str
    module: str
    line_number: int
    is_extern: bool
    implemented_by: str | None
    # The public declaration it belongs to, when Lean generated it for one: the `casesOn`
    # of a type with a computed field. `None` for a definition a person marked private.
    owner: str | None = None


@dataclass(frozen=True)
class SurfaceFacts:
    """Everything `#surface_facts` reported."""

    surface: tuple[SurfaceDeclaration, ...]
    # For every claim theorem, by qualified name, the declarations its statement mentions.
    mentions: dict[str, tuple[str, ...]]
    # Every public declaration the claims are written in, directly or through definitions.
    vocabulary: tuple[str, ...]
    # The private declarations among them, which are not surface and are still read.
    private_vocabulary: tuple[str, ...]
    # Every statement of the project that is or could be a `@[csimp]` replacement.
    replacements: tuple[CompiledReplacement, ...] = ()
    # Every definition that is not public and runs other code than its definition.
    hidden: tuple[HiddenCode, ...] = ()


def _compiled_replacement(entry: dict) -> CompiledReplacement:
    return CompiledReplacement(
        statement=entry["statement"], statement_is_public=entry["statement_is_public"], module=entry["module"],
        line_number=entry["line"], replaced=entry["replaced"], replaced_is_public=entry["replaced_is_public"],
        replacement=entry["replacement"], is_registered=entry["registered"], namespace=entry["namespace"],
        axioms=tuple(entry["axioms"]))


def parse_surface_facts(output: str) -> SurfaceFacts:
    """Read the line `#surface_facts` printed."""
    found = _FACTS_LINE.search(output)
    if found is None:
        raise TrustError(f"Lean did not report the surface:\n{output[-1500:]}")
    document = json.loads(found.group("document"))
    missing = sorted({"surface", "claims", "vocabulary", "private_vocabulary", "replacements", "hidden"} - set(document))
    if missing:
        # The report comes from the LeanClaims package the project's test package requires.
        # A project that pins an older one gets a report these tools cannot judge.
        raise TrustError(
            f"the report of #surface_facts has no {', '.join(missing)}: the LeanClaims package this project "
            "requires is older than these tools. Require the same version of lean-claims in the test package's "
            "lakefile as the tools being run, then `lake update LeanClaims` there")
    surface = sorted((SurfaceDeclaration(
        name=entry["name"], module=entry["module"], line_number=entry["line"], kind=entry["kind"],
        is_extern=entry["extern"], implemented_by=entry["implemented_by"], stated_by=tuple(entry["stated_by"]))
        for entry in document["surface"]), key=lambda declaration: (declaration.module, declaration.line_number, declaration.name))
    return SurfaceFacts(
        surface=tuple(surface),
        mentions={entry["name"]: tuple(entry["mentions"]) for entry in document["claims"]},
        vocabulary=tuple(document["vocabulary"]),
        private_vocabulary=tuple(document["private_vocabulary"]),
        replacements=tuple(sorted((_compiled_replacement(entry) for entry in document["replacements"]),
                                  key=lambda replacement: (replacement.module, replacement.line_number,
                                                           replacement.statement))),
        hidden=tuple(sorted((HiddenCode(name=entry["name"], module=entry["module"], line_number=entry["line"],
                                        is_extern=entry["extern"], implemented_by=entry["implemented_by"],
                                        owner=entry["owner"])
                             for entry in document["hidden"]),
                            key=lambda declaration: (declaration.module, declaration.line_number, declaration.name))))


def proof_modules(config: ProjectConfig) -> list[str]:
    """The modules that hold proofs and not code: every proof file, the module that
    gathers them, and the verify file."""
    return sorted(set(proof_files_by_module(config)) | {config.proofs_module, module_of_file(config.verify_file)})


def lean_surface_facts(config: ProjectConfig, spec: Spec) -> SurfaceFacts:
    """Build the code and the test package, then ask Lean for the surface of the code and
    what the claims mention."""
    # The code's root modules are built by name. The test package builds only what its own
    # modules import, and a code module that neither the proofs nor the tests import
    # would otherwise be read as it was when it was last built.
    status, output = run_command(["lake", "build", *(f"+{module}" for module in config.code_modules)],
                                 config.project_directory)
    if status != 0:
        raise TrustError(f"the code does not build, so the surface cannot be read:\n{output[-3000:]}")
    tests_directory = config.project_directory / config.tests_directory
    status, output = run_command(["lake", "build"], tests_directory)
    if status != 0:
        raise TrustError(f"the test package does not build, so the surface cannot be read:\n{output[-3000:]}")
    imports = ["LeanClaims", *config.code_modules, config.proofs_module]
    names = [theorem.qualified_name for theorem in spec.theorems]
    probe_text = ("".join(f"import {module}\n" for module in imports)
                  + f"\n#surface_facts claims [{', '.join(names)}] code [{', '.join(config.code_modules)}] "
                    f"proofs [{', '.join(proof_modules(config))}]\n")
    probe_path = tests_directory / SURFACE_PROBE_FILE_NAME
    probe_path.write_text(probe_text, encoding="utf-8")
    try:
        status, output = run_command(["lake", "env", "lean", SURFACE_PROBE_FILE_NAME], tests_directory)
    finally:
        probe_path.unlink(missing_ok=True)
    if status != 0:
        raise TrustError(f"Lean could not be asked about the surface:\n{output[-3000:]}")
    return parse_surface_facts(output)


@dataclass(frozen=True)
class DeclarationLevel:
    """A public declaration and where it stands."""

    declaration: SurfaceDeclaration
    # The numbers of the claims that mention it.
    claims: tuple[int, ...]
    # The checks of the tested entries that list it.
    tests: tuple[str, ...]
    is_trusted: bool
    # No claim mentions it, and the definition of one a claim mentions reaches it.
    is_supporting: bool = False

    @property
    def levels(self) -> tuple[str, ...]:
        found = []
        if self.claims:
            found.append("proved")
        if self.tests:
            found.append("tested")
        if self.is_trusted:
            found.append("trusted")
        if self.is_supporting:
            found.append("supporting")
        if self.declaration.kind == "theorem":
            found.append("theorem")
        return tuple(found)


def _place(declaration: "SurfaceDeclaration | HiddenCode") -> str:
    return f"{declaration.module.replace('.', '/')}.lean:{declaration.line_number}"


def surface_levels(config: ProjectConfig, spec: Spec, facts: SurfaceFacts) -> tuple[list[DeclarationLevel], list[str]]:
    """Where every public declaration stands, and everything wrong: a declaration at no
    level, one whose running code the proofs do not reach and that has no entry, and an
    entry that lists a declaration the project does not have."""
    claim_of_theorem = {theorem.qualified_name: claim.number for claim in spec.claims for theorem in claim.theorems}
    surface_names = {declaration.name for declaration in facts.surface}
    vocabulary = set(facts.vocabulary)
    tests_of: dict[str, list[str]] = {}
    trusted_names: set[str] = set()
    problems = []
    for entry in config.tested:
        for name in entry.declarations:
            if name not in surface_names:
                problems.append(f"the tested entry '{entry.what}' lists {name}, which is not a public declaration of the project")
            tests_of.setdefault(name, []).append(entry.test)
    for entry in config.trusted:
        for name in entry.declarations:
            if name not in surface_names:
                problems.append(f"the trusted entry '{entry.what}' lists {name}, which is not a public declaration of the project")
            trusted_names.add(name)

    levels = []
    for declaration in facts.surface:
        claims = tuple(sorted({claim_of_theorem[name] for name in declaration.stated_by if name in claim_of_theorem}))
        level = DeclarationLevel(declaration, claims, tuple(sorted(set(tests_of.get(declaration.name, [])))),
                                 declaration.name in trusted_names,
                                 is_supporting=not claims and declaration.name in vocabulary)
        levels.append(level)
        has_entry = bool(level.tests) or level.is_trusted
        if not level.levels:
            problems.append(
                f"{declaration.name} ({_place(declaration)}) is public and is not proved, tested or trusted: no "
                "claim's statement mentions it, nothing a claim mentions is defined by it, and no entry of "
                "claims.toml lists it")
        elif declaration.kind in KINDS_WITHOUT_A_DEFINITION and not has_entry:
            problems.append(
                f"{declaration.name} ({_place(declaration)}) is an {declaration.kind} constant, which has no "
                "definition for a proof to be about, and no tested or trusted entry lists it")
        elif (declaration.is_extern or declaration.implemented_by) and not has_entry:
            other_code = "@[extern]" if declaration.is_extern else f"@[implemented_by {declaration.implemented_by}]"
            problems.append(
                f"{declaration.name} ({_place(declaration)}) runs other code than its definition ({other_code}), "
                "which the proofs do not reach, and no tested or trusted entry lists it")
    listed_names = set(tests_of) | trusted_names
    for declaration in facts.hidden:
        other_code = "@[extern]" if declaration.is_extern else f"@[implemented_by {declaration.implemented_by}]"
        if declaration.owner is None:
            problems.append(
                f"{declaration.name} ({_place(declaration)}) is not a public declaration and runs other code than "
                f"its definition ({other_code}), which the proofs do not reach. An entry can list only a public "
                "declaration, so nothing can say it is tested or trusted: make it public and list it, or take the "
                "attribute off")
        elif declaration.owner not in listed_names:
            problems.append(
                f"{declaration.name}, which Lean generated for {declaration.owner} ({_place(declaration)}), runs "
                f"other code than its definition ({other_code}), as it does for a type with a computed field. The "
                f"proofs do not reach that code, and no tested or trusted entry lists {declaration.owner}")
    for replacement in facts.replacements:
        if replacement.axioms and not replacement_is_listed(replacement, listed_names):
            problems.append(_unproved_replacement_text(replacement))
    return levels, problems


def replacement_is_listed(replacement: CompiledReplacement, listed_names: set[str]) -> bool:
    """Whether a tested or trusted entry lists the statement or what it replaces. Only a
    public declaration can be listed, so a private name that reads the same as a public one
    is not taken for it."""
    return ((replacement.statement_is_public and replacement.statement in listed_names)
            or (replacement.replaced_is_public and replacement.replaced in listed_names))


def _replacement_place(replacement: CompiledReplacement) -> str:
    return f"{replacement.module.replace('.', '/')}.lean:{replacement.line_number}"


def _unproved_replacement_text(replacement: CompiledReplacement) -> str:
    """What is wrong with a replacement that rests on an axiom and that no entry lists."""
    listable = [name for name, is_public in ((replacement.replaced, replacement.replaced_is_public),
                                             (replacement.statement, replacement.statement_is_public)) if is_public]
    remedy = (f"no tested or trusted entry lists {' or '.join(listable)}" if listable else
              f"neither {replacement.replaced} nor {replacement.statement} is a public declaration of the code "
              "that an entry could list, so the statement has to be proved from the standard axioms, or declared "
              "public in the code and listed")
    axioms = ", ".join(replacement.axioms)
    if replacement.is_registered:
        where = f" where the namespace {replacement.namespace} is open" if replacement.namespace else ""
        return (f"{replacement.replaced} is compiled as {replacement.replacement}{where} by the @[csimp] theorem "
                f"{replacement.statement} ({_replacement_place(replacement)}), which depends on {axioms}: nothing "
                f"proves the compiled code computes what the definition does, and {remedy}")
    return (f"{replacement.statement} ({_replacement_place(replacement)}) states that {replacement.replaced} and "
            f"{replacement.replacement} are the same function and depends on {axioms}. `attribute [local csimp]` "
            f"can have the compiler run {replacement.replacement} on the strength of such a statement, and Lean "
            f"keeps no record of that, so it is held to the same rule as a registered one: {remedy}")


def _numbers(numbers: tuple[int, ...]) -> str:
    return ", ".join(str(number) for number in numbers)


def _count(number: int, singular: str, plural: str | None = None) -> str:
    """`1 claim`, `2 claims`."""
    return f"{number} {singular if number == 1 else (plural or singular + 's')}"


def _table_text(text: str) -> str:
    """Text made safe for a cell of a Markdown table."""
    return " ".join(text.split()).replace("|", "\\|")


def trust_text(config: ProjectConfig, spec: Spec, facts: SurfaceFacts, levels: list[DeclarationLevel],
               mutations: list[Mutation], catalog_faults: list[PlannedFault], existing_text: str | None) -> str:
    """The text of `TRUST.md`."""
    made_claims = [claim for claim in spec.claims if not claim.withdrawn]
    theorem_count = sum(len(claim.theorems) for claim in made_claims)
    counts = {level_name: sum(1 for level in levels if level_name in level.levels)
              for level_name in ("proved", "tested", "trusted", "supporting", "theorem")}
    without_level = sum(1 for level in levels if not level.levels)
    refuting = sum(1 for mutation in mutations if mutation.refuted_claim is not None)
    lines = [
        "<!--",
        f"File: {TRUST_FILE_NAME}",
        f"Purpose: What {config.name} guarantees and on what each guarantee rests: which declarations are",
        "proved, which are tested, which are trusted, and what was waived. Written by `claims trust`",
        "from the spec, `claims.toml`, the catalogs and what Lean reports. Not edited by hand:",
        "`claims trust --check` fails when this file differs from what would be written.",
        created_line(existing_text),
        "-->",
        "",
        f"# What {config.name} guarantees",
        "",
        f"{_count(len(made_claims), 'claim')}, stated in `{spec.file_name}` as {_count(theorem_count, 'theorem')}. "
        f"{_count(len(levels), 'public declaration')}: {counts['proved']} mentioned by a claim, "
        f"{counts['tested']} tested, {counts['trusted']} trusted, {counts['supporting']} supporting, "
        f"{counts['theorem']} a theorem of the code, {without_level} at no level.",
        "",
        "A declaration can stand at more than one level. \"Mentioned by a claim\" means a claim's statement",
        "uses it. It does not mean the claims say everything about it: the audits and the mutation run are",
        "the checks on that, and the waivers below are where they were not met. \"Supporting\" means no",
        "claim mentions it and a declaration that a claim does mention is defined by it: the claims bind it",
        "as far as that declaration uses it, and say nothing of it otherwise.",
        "",
        "## Claims",
        "",
        "| Claim | States | Theorems | Mentions |",
        "|-------|--------|----------|----------|",
    ]
    for claim in spec.claims:
        if claim.withdrawn:
            lines.append(f"| {claim.number} | Withdrawn. {_table_text(claim.title)} | | |")
            continue
        mentioned = sorted({name for theorem in claim.theorems for name in facts.mentions.get(theorem.qualified_name, ())})
        lines.append(
            f"| {claim.number} | {_table_text(claim.title)} | "
            f"{', '.join(f'`{theorem.name}`' for theorem in claim.theorems)} | "
            f"{', '.join(f'`{name}`' for name in mentioned) or 'no declaration of the project'} |")
    lines += [
        "",
        "## What a reviewer reads",
        "",
        f"The claims are written in {_count(len(facts.vocabulary), 'public declaration')}, directly or through the",
        "definitions of the ones they use. Knowing what the claims mean requires reading each one.",
        "",
        ", ".join(f"`{name}`" for name in facts.vocabulary) or "None.",
    ]
    if facts.private_vocabulary:
        lines += [
            "",
            f"And {_count(len(facts.private_vocabulary), 'private declaration')}, not part of the public surface:",
            "",
            ", ".join(f"`{name}`" for name in facts.private_vocabulary),
        ]
    lines += [
        "",
        "## Public declarations",
        "",
        "| Declaration | Kind | Where | Proved by claims | Tested by | Trusted | Supporting |",
        "|-------------|------|-------|------------------|-----------|---------|------------|",
    ]
    for level in levels:
        declaration = level.declaration
        notes = []
        if declaration.is_extern:
            notes.append("runs `@[extern]` code")
        if declaration.implemented_by:
            notes.append(f"runs `{declaration.implemented_by}`")
        for generated in facts.hidden:
            if generated.owner == declaration.name:
                short_name = generated.name.removeprefix(declaration.name + ".")
                notes.append(f"its `{short_name}` runs `@[extern]` code" if generated.is_extern
                             else f"its `{short_name}` runs `{generated.implemented_by}`")
        for replacement in facts.replacements:
            if replacement.is_registered and replacement.replaced_is_public and replacement.replaced == declaration.name:
                notes.append(f"compiled as `{replacement.replacement}`, see below")
        kind = declaration.kind + (f" ({'; '.join(notes)})" if notes else "")
        lines.append(
            f"| `{declaration.name}` | {kind} | {_place(declaration)} | {_numbers(level.claims)} | "
            f"{', '.join(level.tests)} | {'yes' if level.is_trusted else ''} | "
            f"{'yes' if level.is_supporting else ''} |")
    # A statement that is proved and not registered changes nothing and is left out.
    shown_replacements = [replacement for replacement in facts.replacements
                          if replacement.is_registered or replacement.axioms]
    lines += ["", "## Compiled replacements", ""]
    if shown_replacements:
        lines += [
            "A `@[csimp]` theorem states that two functions are equal and has the compiler run the second",
            "wherever later code names the first. One proved from the standard axioms is checked by the",
            "kernel. One that rests on another axiom is not, and is covered by the entry that lists it.",
            "",
            "| Replaced | Compiled as | In force | Stated by | Where | Rests on |",
            "|----------|-------------|----------|-----------|-------|----------|",
        ]
        for replacement in shown_replacements:
            if not replacement.is_registered:
                in_force = "not registered; `attribute [local csimp]` could use it"
            elif replacement.namespace:
                in_force = f"where `{replacement.namespace}` is open"
            else:
                in_force = "everywhere"
            rests_on = (", ".join(f"`{name}`" for name in replacement.axioms) if replacement.axioms
                        else "the standard axioms: proved")
            lines.append(
                f"| `{replacement.replaced}` | `{replacement.replacement}` | {in_force} | `{replacement.statement}` | "
                f"{_replacement_place(replacement)} | {rests_on} |")
    else:
        lines.append("None. No statement of the project is, or rests on an axiom and could be, a `@[csimp]` replacement.")
    lines += ["", "## Tested, not proved", ""]
    if config.tested:
        lines += ["| What | Check | Fault it has been seen to catch | Declarations |",
                  "|------|-------|---------------------------------|--------------|"]
        lines += [f"| {_table_text(entry.what)} | `{entry.test}` | `{entry.fault}` | "
                  f"{', '.join(f'`{name}`' for name in entry.declarations)} |" for entry in config.tested]
    else:
        lines.append("Nothing.")
    lines += ["", "## Trusted", ""]
    if config.trusted:
        lines += ["| What | Why | Declarations |", "|------|-----|--------------|"]
        lines += [f"| {_table_text(entry.what)} | {_table_text(entry.why)} | "
                  f"{', '.join(f'`{name}`' for name in entry.declarations)} |" for entry in config.trusted]
    else:
        lines.append("Nothing listed in `claims.toml`.")
    lines += [
        "",
        "Every project built this way also trusts: Lean's kernel and the kernels `lake comparator` runs,",
        "which check the proofs; the Lean compiler and runtime, which turn definitions into the code that",
        f"runs; the axioms {', '.join(f'`{axiom}`' for axiom in config.allowed_axioms)}; and the lean-claims",
        "tools, which are tested and not proved.",
        "",
        "## Waivers",
        "",
    ]
    if config.waivers:
        lines += ["| Claim | Requirement lifted | Reason |", "|-------|--------------------|--------|"]
        lines += [f"| {waiver.claim} | {waiver.kind} | {_table_text(waiver.reason)} |"
                  for waiver in sorted(config.waivers, key=lambda waiver: (waiver.claim, waiver.kind))]
    else:
        lines.append("None. Every claim has every audit and a mutation.")
    lines += [
        "",
        "## What the catalogs plant",
        "",
        f"`claims mutate` plants {_count(len(mutations), 'change')} to the code from `mutations.toml`. "
        f"{refuting} name a claim: each must break a proof and have that claim proved false, unless the build",
        f"refuses the change. {len(mutations) - refuting} keep the code's behaviour and name none.",
        "",
        f"`claims checks` plants {_count(len(catalog_faults), 'fault')} from `faults.toml`, and the faults it",
        "generates for every project. The check each is planted for must catch it.",
        "",
        "This file records what would be planted, not the result of a run. Run the two commands for that.",
    ]
    return "\n".join(lines) + "\n"
