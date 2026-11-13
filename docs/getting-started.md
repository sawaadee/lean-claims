<!--
File: docs/getting-started.md
Purpose: How to start a project with lean-claims and replace the starter's function and
claims with your own.
Created: 2026-11-13
-->

# Getting started

`claims` below stands for `python3 -I <lean-claims>/tools/claims.py`.

## What you need

Lean v4.35.0 with `lake`, on Linux. Python 3.11 or later; the tools use only its standard
library. [bubblewrap](https://github.com/containers/bubblewrap) for `lake comparator`.

## Start a project

```
git clone https://github.com/sawaadee/lean-claims
python3 -I lean-claims/tools/claims.py new json-parser --name JsonParser
cd json-parser
lake build && (cd tests && lake build)
python3 -I ../lean-claims/tools/claims.py verify --full
```

`claims new` copies the starter project under your name. The starter is complete: one
function with its claims, their proofs, the audit of the claims, planted bugs and planted
faults. Everything passes before you change a line, so the first thing that fails is
something you did.

By default the new project's test package requires the LeanClaims package from the
checkout the tool was run from, by its path on your machine. For a project others will
clone, pin a commit of lean-claims instead:

```
claims new json-parser --name JsonParser \
  --leanclaims-git https://github.com/sawaadee/lean-claims --leanclaims-rev COMMIT
```

`COMMIT` is the commit of lean-claims to build against, as `git -C lean-claims rev-parse HEAD`
prints it.

## Running the checks on GitHub

The project comes with `.github/workflows/ci.yml`. On every push it runs `claims verify`,
and each night `claims verify --full`. It fetches the lean-claims tools at the commit the
test package pins, so it needs the project to have been created with `--leanclaims-git`
and `--leanclaims-rev`.

## What is in it

| File | Holds | Who writes it |
|------|-------|---------------|
| `Spec.lean` | Every claim, in English and in Lean, proofs left out | You |
| `spec.lock` | A hash of every claim | `claims lock --update`, on purpose |
| `JsonParser/` | The code | You or an agent |
| `JsonParser/Proofs/` | The proofs | You or an agent |
| `tests/ClampAudit.lean` | Theorems about the claims themselves | You or an agent |
| `mutations.toml` | Bugs to plant | You or an agent |
| `faults.toml` | Faults to plant, and the project's own checks | You or an agent |
| `claims.toml` | Module names, tested and trusted entries, waivers | You |
| `TRUST.md` and the other generated files | | The tools |
| `AGENTS.md` | The rules and the order of work, for an agent | From the starter |

## Make it yours

Replace the starter's content one claim at a time, with every check passing between
steps. `AGENTS.md` in the project gives the steps for adding a guarantee. In short:

1. State your first claim in `Spec.lean` as the next number. `claims lock --update`.
2. Write the function and the proof. `claims sync`, `lake build`.
3. Audit the claim in `tests/`. `claims audit`.
4. Plant a bug in `mutations.toml`. `claims mutate`.
5. `claims trust`, then `claims verify --full`.

When your own claims stand, withdraw the starter's. A withdrawn claim keeps its number and
its header in the spec, with a title that begins "Withdrawn" and no theorem under it, so
numbers never move. Before the first release nothing cites the numbers, and you can
instead delete the starter's claims and number yours from 1. Then delete
`clamp`, its proofs, its audits, its mutations and its test, and run
`claims lock --update`, `claims sync` and `claims trust`.

## A project with more than one kind of code

`claims.toml` has one `[[layer]]` per set of proof files that share a namespace. A project
with a simple reference version of its functions and a fast version has two: claims about
the reference version, and claims that the fast version agrees with it.

Code that has effects (the clock, files, the network) cannot be proved. It gets a test, a
planted fault the test must catch, and a `[[tested]]` entry. Code outside the project
that it relies on gets a `[[trusted]]` entry with the reason. `claims trust` requires
every public declaration to be at one of the three levels.
