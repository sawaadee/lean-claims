<!--
File: docs/reference.md
Purpose: The reference for every file a lean-claims project holds: what each file is,
who writes it, the rules of `Spec.lean`, and every key of `claims.toml`, `mutations.toml`
and `faults.toml`.
Created: 2026-11-14
-->

# Reference

## The files of a project

`Lib` stands for the project's own name.

| Path | Holds | Written by |
|------|-------|-----------|
| `Spec.lean` | Every claim: English, then the Lean statement with the proof left out | A person, or an agent with a person's approval |
| `spec.lock` | One line per claim with a hash of its text | `claims lock --update`, run on purpose |
| `claims.toml` | Module names, layers, allowed axioms, tested and trusted entries, waivers | A person |
| `Lib/` | The code | A person or an agent |
| `Lib/Proofs/` | The proofs. Each claim is restated here with its proof | A person or an agent |
| `Lib/Verify.lean` | Every claim restated with `recall`, so the ordinary build compares it with the spec | `claims sync` |
| `comparator.json` | The claim names for `lake comparator` | `claims sync` |
| `tests/` | A Lake package of its own: the audit modules and the project's tests | A person or an agent |
| `tests/Axioms.lean` | The axiom assertion over every proof module and test module of theorems | `claims sync` |
| `mutations.toml` | Bugs to plant in the code, each with the claim it must make false | A person or an agent |
| `faults.toml` | The project's own checks, and faults to plant so each is seen to fail | A person or an agent |
| `TRUST.md` | Every public declaration and its level, the entries and the waivers | `claims trust` |
| `AGENTS.md` | The rules and the order of work for adding a guarantee | From the starter |
| `.github/workflows/ci.yml` | Runs `claims verify` on every push and `claims verify --full` each night | From the starter |

## `Spec.lean`

The spec is its own Lake library. It is not a default target and nothing imports it, so
its `sorry`s never reach `lake build`. It may hold only comments, `import` lines,
`namespace`, `open` and `end` lines, claim headers, and theorems. It defines nothing: the
words a claim uses come from the project's own code, and `TRUST.md` lists them.

A claim is a header followed by one or more theorems:

```lean
/-! ## Claim 2. The result is never above the upper bound, when the range is not empty.

A caller who passes a sensible range gets a number inside it. -/

namespace Example.Proofs

open Example

/-- `rangeNotEmpty : low ≤ high` says the range holds at least one number. It is needed:
    for an empty range the result is `low`, which is above `high`. -/
theorem clamp_le_high (low high value : Nat) (rangeNotEmpty : low ≤ high) :
    clamp low high value ≤ high := by
  sorry

end Example.Proofs
```

The rules, each enforced by `claims sync`:

- Claim numbers start at 1, rise by one, and appear in order.
- Every theorem sits under exactly one claim header.
- Every theorem has a doc comment. It should explain each hypothesis in plain words.
- Every proof is exactly `by sorry`.
- A claim closes every namespace it opens. Its meaning then depends only on its own text
  and the lines before the first claim, so its hash covers everything that decides what
  it says.
- Before the first claim the file holds only comments, `import` lines and `open` lines.
- A claim is never renumbered. A withdrawn claim keeps its header, with a title that
  begins "Withdrawn", and has no theorems.

### `spec.lock`

One line per claim: its number, a SHA-256 hash of its full text with the header and the
doc comments, the names of its theorems, and its title. One more line, `context`, is a
hash of everything before the first claim, because an import or an `open` line can change
what every claim means.

`claims lock --check` fails when the spec and the lock differ, and every other command
that reads the spec runs it first. `claims lock --update` rewrites the lock and is the
only thing that does. The lock cannot stop someone who changes a claim and updates the
lock on purpose. It makes that change show in the diff of two files.

## `claims.toml`

```toml
[project]
name = "Example"
spec_module = "Spec"
code_library = "Example"
proofs_library = "ExampleProofs"
proofs_module = "Example.Proofs"
verify_file = "Example/Verify.lean"
allowed_axioms = ["propext", "Classical.choice", "Quot.sound"]

[[layer]]
name = "main"
namespace = "Example.Proofs"
proof_files = "Example/Proofs/*.lean"
refutation_prelude = "mutations/prelude.lean"

[tests]
directory = "tests"
library = "ExampleTests"

[audit]
modules = ["ClampAudit"]

[[tested]]
what = "The compiled `clamp` computes what its definition says."
test = "run"
fault = "compiled-clamp-applies-the-bounds-in-the-other-order"
declarations = ["Example.clamp"]

[[trusted]]
what = "The operating system's source of random bytes."
why = "No test here can show its bytes are unpredictable."
declarations = ["Example.randomBytes"]

[[waiver]]
claim = 1
kind = "determines"
reason = "A consequence of claims 3 to 6. It is stated because it is the property callers rely on."
```

### `[project]`

| Key | Means |
|-----|-------|
| `name` | The project's name, as shown in reports |
| `spec_module` | The module of the spec, normally `Spec` |
| `spec_library` | Optional. The Lake library that holds the spec, when its name is not the module's |
| `code_library` | The Lake library of the code the mutation run plants bugs in |
| `code_modules` | Optional. The root modules of the code, when the library's own root does not import all of it. Every module under one of them is code, unless it is a proof module. The library's name by default |
| `proofs_library` | The Lake library of the proofs |
| `proofs_module` | The module that imports every proof |
| `verify_file` | Where `claims sync` writes the file that restates every claim with `recall` |
| `allowed_axioms` | The axioms a proof may rest on. The three shown are Lean's ordinary logic |

### `[[layer]]`

A layer is a set of proof files that share one namespace. Its claims are the spec's
theorems in that namespace. A project with a simple reference version of its functions
and a fast version has two layers.

| Key | Means |
|-----|-------|
| `name` | The layer's name, used by `mutations.toml` |
| `namespace` | The namespace its theorems are declared in |
| `proof_files` | A pattern matching its proof files |
| `refutation_prelude` | A Lean file put in front of every refutation of this layer: imports, `open` lines and shared values |
| `probe_files` | Optional. The proof files the mutation run joins into one, in order. Left out, the files that declare a theorem are ordered by their imports |
| `also_builds` | Optional. Modules outside the joined files whose failure to build also counts as a broken proof |

### `[tests]` and `[audit]`

| Key | Means |
|-----|-------|
| `tests.directory` | The directory of the test package |
| `tests.library` | The library in it whose build runs the axiom assertion |
| `tests.theorem_modules` | Optional. Modules of the test package that hold theorems and are not audits. The axiom assertion covers them |
| `audit.modules` | The modules that hold the audit theorems |

### `[[tested]]`, `[[trusted]]` and `[[waiver]]`

| Key | Means |
|-----|-------|
| `tested.what` | What is tested and not proved, in a sentence |
| `tested.test` | The check that tests it: a built-in check or one declared in `faults.toml` |
| `tested.fault` | The fault in `faults.toml`, planted for that check, that shows the test can fail |
| `tested.declarations` | Optional. The public declarations the entry covers, which `claims trust` then counts as tested |
| `trusted.what` | What is neither proved nor tested |
| `trusted.why` | The reason |
| `trusted.declarations` | Optional. The public declarations the entry covers |
| `waiver.claim` | The number of the claim |
| `waiver.kind` | The requirement of `claims audit` that is lifted: `fails`, `determines`, `can hold` or `mutation` |
| `waiver.reason` | Why the requirement cannot be met |

A waiver for a requirement that is met is an error, and so is an entry that lists a
declaration the project does not have.

## `mutations.toml`

```toml
[[mutation]]
layer = "main"
description = "the bounds are applied in the other order, which differs only for an empty range"
refuted_claim = "clamp_of_empty"
refutation = "absurd (clamp_of_empty 10 5 7 (by decide)) (by decide)"

  [[mutation.edit]]
  file = "Example/Clamp.lean"
  find = "max low (min high value)"
  replace = "min high (max low value)"

[[mutation]]
layer = "main"
description = "the arguments of min are written the other way round"
same_behaviour = true

  [[mutation.edit]]
  file = "Example/Clamp.lean"
  find = "max low (min high value)"
  replace = "max low (min value high)"
```

| Key | Means |
|-----|-------|
| `layer` | The layer whose proofs must break |
| `description` | What the bug is. It must be unique within its layer |
| `refuted_claim` | The theorem of the spec the bug must make false. It must be one the spec states in the layer's namespace |
| `refutation` | A Lean proof of `False` from that theorem's statement, on the code as mutated. Any proof term, including a `by` block |
| `same_behaviour` | `true` for a change that alters the code and not what it does. It has no `refuted_claim` and no `refutation` |
| `edit.file` | The file to change |
| `edit.find` | The text to replace. It must occur exactly once in the file |
| `edit.replace` | The text to put in its place |

A mutation may have several edits. A bug the build itself refuses, for instance one that
leaves an argument unused where warnings are errors, is reported apart and counts neither
as caught nor as missed.

## `faults.toml`

```toml
[[check]]
id = "run"
command = ["lake", "exe", "runclamp"]
directory = "tests"

[[fault]]
id = "compiled-clamp-applies-the-bounds-in-the-other-order"
description = "clamp applies the upper bound last, which differs for an empty range"
check = "run"
caught_when_output_has = ["clamp 10 5 7 returned 5, expected 10"]

  [[fault.edit]]
  file = "Example/Clamp.lean"
  find = "  max low (min high value)"
  replace = "  min high (max low value)"
```

| Key | Means |
|-----|-------|
| `check.id` | The name of a check of the project's own |
| `check.command` | The command, as a list. It passes when it exits with status 0 |
| `check.directory` | The directory it runs in, relative to the project |
| `fault.id` | The fault's name, which a `[[tested]]` entry can refer to |
| `fault.description` | What the fault is |
| `fault.check` | The check that must catch it: a built-in check or a declared one |
| `fault.caught_when_output_has` | Texts that must all be in the failing check's output |
| `fault.caught_when_output_has_any` | Optional. Texts of which at least one must be in the output |
| `fault.environment` | Optional. Environment variables to set for the check, for a fault such as a missing interpreter |
| `fault.edit` | As in `mutations.toml`. A fault needs an edit or an environment |

The eight built-in checks need no `[[check]]` entry: `lock`, `sync`, `build`, `names`,
`axioms`, `comparator`, `audit` and `trust`.

A fault is caught only when its check fails and the output holds the texts named. A fault
that says nothing about the output is refused, because a check that fails for another
reason has caught nothing.

## Exit status

Every command exits with 0 when its check passes, 1 when it fails, and 2 when it could not
run. A check that could not run is never reported as passed.
