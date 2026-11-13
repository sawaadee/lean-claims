<!--
File: README.md
Purpose: The front page of lean-claims: what it is, what a project built with it looks
like, how to start one, and how to check lean-claims itself.
Created: 2026-11-13
-->

# lean-claims

A toolkit and a starter project for software written in Lean 4.

A project built with lean-claims states its guarantees as numbered claims in one file a
person can review, proves them, and has every proof, every statement and every check
tested by machine. The tools exist to answer the questions a proof alone does not: is
this the statement that was agreed, does it say enough to be worth proving, and would
the checks notice if something were wrong.

## What a claim looks like

Every guarantee is a numbered claim in `Spec.lean`: a sentence a user of the library
would understand, the Lean statement, and an explanation of each hypothesis. The proof is
left out, because the spec is the file to review.

```lean
/-! ## Claim 2. The result is never above the upper bound, when the range is not empty.

A caller who passes a sensible range gets a number inside it: with claim 1, the result
lies from `low` to `high`. -/

/-- `rangeNotEmpty : low ≤ high` says the range holds at least one number. It is needed:
    for an empty range the result is `low`, which is above `high`. -/
theorem clamp_le_high (low high value : Nat) (rangeNotEmpty : low ≤ high) :
    clamp low high value ≤ high := by
  sorry
```

The proof lives in another file under the same name. Nothing the tools do writes to the
spec.

## What is checked

| Question | Check |
|----------|-------|
| Did a claim change without anyone deciding it should? | `spec.lock` holds a hash of every claim |
| Is each proof finished, and is it a proof of the statement in the spec? | The build, which compares every proved statement with the spec's |
| Does a proof rest on `sorry`, `native_decide` or an added axiom? | The axiom assertion |
| Would an independent kernel accept it? | `lake comparator`, with six kernels |
| Does the claim rule anything out? Can its hypotheses hold? Do the claims pin the function down? | The audit: theorems about the claims themselves, which Lean must confirm are what they say they are |
| Is there a public function with no claim and no note saying so? | The trust report, which puts every public declaration at a level: proved, tested, trusted or supporting |
| Is there a bug the claims do not rule out? | The mutation run plants bugs and requires a claim to be proved false on each |
| Can each check fail? | The test of the checks plants, for every check, the fault it exists to catch |

The last two are the core of it. A check that has never been seen to fail has not been
shown to work, so every check is run against a fault planted for it, and the fault is
then taken out again. [docs/concepts.md](docs/concepts.md) explains the ideas in a few
minutes, [docs/](docs/README.md) has a page for each check (what it catches, how, what
it cannot do, and what it trusts), and [docs/reference.md](docs/reference.md) lists every
key of every file a project holds.

## Start a project

```
git clone https://github.com/sawaadee/lean-claims
python3 -I lean-claims/tools/claims.py new json-parser --name JsonParser
cd json-parser
lake build && (cd tests && lake build)
python3 -I ../lean-claims/tools/claims.py verify --full
```

`claims new` copies the starter project under your name. It is complete and every check
passes before you change a line, so the first thing that fails is something you did.
[docs/getting-started.md](docs/getting-started.md) takes it from there, and the
project's own `AGENTS.md` gives the steps for adding a guarantee, for a person or a
coding agent.

## Commands

`claims` stands for `python3 -I tools/claims.py`. Every command works on the project in
the current directory, or the one named with `--project`.

| Command | Does |
|---------|------|
| `claims new DIRECTORY --name NAME` | Starts a project from the starter project |
| `claims verify` | Runs every check in order and says which passed |
| `claims verify --full` | The same, then the mutation run and the test of the checks |
| `claims lock --check` | Fails when a claim differs from `spec.lock`, and names it |
| `claims lock --update` | Rewrites the lock. The one step that accepts a changed claim |
| `claims sync` | Enforces the spec's rules and writes the files generated from it |
| `claims names` | Fails when a theorem name is used twice, or is declared where the tools cannot read it |
| `claims audit` | Requires every claim to have its audits and a planted bug, or a written waiver |
| `claims trust` | Requires every public declaration to be at a level, and writes `TRUST.md` |
| `claims mutate` | Plants every bug of `mutations.toml` |
| `claims checks` | Plants every fault, generated and from `faults.toml` |
| `claims config` | Reads and validates `claims.toml` |

The exit status is 0 when a check passes, 1 when it fails, and 2 when it could not run.

## What is in this repository

| Path | Holds |
|------|-------|
| `LeanClaims/` | The Lean package a project's test package requires: the axiom assertion and the commands that report facts about theorems and declarations |
| `tools/` | `claims.py` and the Python modules behind each command |
| `template/` | The starter project: one function, its claims, proofs, audits, planted bugs and planted faults |
| `examples/minijson/` | A second project of another kind: a parser and renderer for a subset of JSON, with recursive values and proofs by induction. Its README says how its claims came about |
| `selftest/` | Tests of the tools themselves |
| `docs/` | The concepts, getting started, a page for each check, and the reference for every file format |
| `AGENTS.md` | The rules for changing lean-claims itself |

## Check lean-claims itself

```
python3 -I selftest/run.py
```

It takes about fifteen minutes and every step must pass. It builds everything, runs the
unit tests of the tools, tests the Lean commands on declarations written to mislead them,
runs every check with both long runs on the starter project and on MiniJson, requires
the two long runs to fail on catalogs made to fail them, creates a project from scratch
and checks it, and adds a second claim to another while taking three wrong turns that
the checks must stop.

GitHub runs the same on every push to `main` and each night, and a shorter set of
checks on every other push and pull request. A project made with `claims new` carries a
workflow of its own.

## Requirements

- Lean v4.35.0, with `lake`. The six kernels `lake comparator` runs come with it.
- Linux.
- Python 3.11 or later. The tools use nothing outside its standard library.
- [bubblewrap](https://github.com/containers/bubblewrap), for the sandbox
  `lake comparator` runs the kernels in.

Mathlib is not used and not required.

## Licence

Apache License 2.0, the licence of Lean itself. The full text is in `LICENSE`.

Copyright 2026 sawaadee

A project started with `claims new` is its author's own, under whatever licence they
choose. The files it is started from may be used under this one.
