<!--
File: docs/trust.md
Purpose: What the surface check and the trust report catch, how, what they cannot, and
what they trust.
Created: 2026-11-13
-->

# The trust report

`claims trust --check`

## What it catches

A public declaration that no claim mentions and nothing says is tested or trusted, and a
`TRUST.md` that no longer describes the project.

## How

Lean lists every public declaration of the code (`#surface_facts`): definitions, theorems,
types, instances, axioms and opaque constants a person declared and did not mark
`private`. A type's constructors and fields and what Lean generates belong to the type.

Each must be at a level:

- **proved**, when a claim's statement mentions it, directly or through an instance or
  abbreviation;
- **tested** or **trusted**, when an entry of `claims.toml` lists it;
- **supporting**, when no claim mentions it and a declaration that a claim does mention is
  defined by it. The claims bind a supporting declaration as far as the mentioned one
  uses it, and say nothing of it otherwise. The report lists it apart, so nobody reads
  it as proved in its own right;
- a **theorem** of the code.

A public function that is none of these fails the check. Lean's `private` hides a
definition from the proofs in other files as well, so a helper the proofs unfold cannot
be private. That is what the supporting level is for.

A declaration marked `@[extern]` or `@[implemented_by]`, an axiom and an opaque constant
need a tested or trusted entry even when a claim mentions them: the proofs are about the
definition, and what runs is something else. An entry that lists a declaration the
project does not have is an error.

`claims trust` writes `TRUST.md`: the claims and what each mentions, the definitions a
reviewer has to read, every declaration with its level, the entries, the waivers, and
what the catalogs plant. `--check` fails when the file is out of date.

## What it cannot do

A mention is not a guarantee. A claim can mention a function and say little about it. The
audit and the mutation run are the checks on that. The report records what the catalogs
would plant, not the result of a run.

## What it trusts

`#surface_facts`, which `selftest/surface_facts.py` tests on 17 declarations, one of
every sort it has to tell apart.
