<!--
File: docs/trust.md
Purpose: What the surface check and the trust report catch, how, what they cannot, and
what they trust.
Created: 2026-11-13
Revised: 2026-11-14 (compiled replacements, and private definitions that run other code)
-->

# The trust report

`claims trust --check`

## What it catches

A public declaration that no claim mentions and nothing says is tested or trusted, code
that runs in place of a definition with nothing proving or testing that the two agree,
wherever in the project it is hidden, and a `TRUST.md` that no longer describes the
project.

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

The same two attributes on a private definition always fail the check. A public function
that calls it runs code the proofs do not reach, and an entry can list only a public
declaration, so nothing could say the private one is tested or trusted. It is made
public and listed, or the attribute comes off.

Lean generates such definitions itself for a type with a computed field: the type's
`casesOn` runs other code than its definition. That code belongs to the type, and a
tested or trusted entry that lists the type accounts for it.

## Compiled replacements

A `@[csimp]` theorem also has the compiler run other code than a definition. It states
that two functions are equal, `@f = @g`, and the compiler then uses `g` wherever later
code names `f`. The kernel checks the statement. When it depends on the standard axioms
only, the replacement is proved to compute what the definition does, and the report
lists it. When it depends on any other axiom, nothing has shown that. The axiom can be
private and in a code module, where no other check looks for it. Such a statement needs
a tested or trusted entry that lists the function it replaces or the statement itself.

Three things make this rule wider than the one for `@[extern]`:

- What is replaced need not be a public declaration. It can be a private helper, or a
  function of Lean or of a dependency that the project's code calls. So Lean is asked
  for every statement of that form in the project's code and proofs, and not about each
  public declaration in turn.
- The statement need not be a theorem, or public. An axiom can carry the attribute
  itself, and so can a private theorem. If neither it nor what it replaces is a public
  declaration of the code, no entry can list it, and it has to be proved.
- It need not be registered. `attribute [local csimp]` puts a replacement in force for
  the rest of a section, and Lean keeps no record of it afterwards. So a statement of the
  form `@f = @g` that rests on an axiom is held to the rule whether or not Lean has it
  registered. One that is proved and not registered changes nothing and is left alone.

`claims trust` writes `TRUST.md`: the claims and what each mentions, the definitions a
reviewer has to read, every declaration with its level, the entries, the waivers, and
what the catalogs plant. `--check` fails when the file is out of date.

## What it cannot do

A mention is not a guarantee. A claim can mention a function and say little about it. The
audit and the mutation run are the checks on that. The report records what the catalogs
would plant, not the result of a run.

It does not look at the test package. A `@[csimp]` there changes what the tests run and
not what the project ships. The guard against a test that runs something else is the
fault every tested entry names: `claims checks` plants a bug in the real function and
the test has to notice. This was tried on the starter: with its test made to run a
correct copy of `clamp` in the place of the real one, the test passed, and
`claims checks` reported the planted bug as missed.

It has no rule for `@[export]`. Giving a function the compiled name of another one, of
the project, of Lean's runtime or of Lean's library, was tried each way and fails the
build with a duplicate symbol, so it cannot go unnoticed.

It reads the modules named under `code_modules` in `claims.toml` and their proofs. A
library the project builds and does not name there is not read.

A statement of the form `@f = @g` that rests on an axiom is reported even when nothing
uses it as a replacement, since whether a `local` attribute used it cannot be asked.

## What it trusts

`#surface_facts`, which `selftest/surface_facts.py` tests on 37 public declarations, 16
statements that are or could be replacements, 3 definitions that are not public and that it has to list, one of them generated by
Lean, and one it must not, one of every sort it has to tell apart.
