<!--
File: docs/mutate.md
Purpose: What the mutation run catches, how, what it cannot, and what it trusts.
Created: 2026-11-13
-->

# The mutation run

`claims mutate`

## What it catches

A bug the claims do not rule out. If a realistic bug can be planted in the code and every
proof still goes through, the claims say less than the code needs.

## How

`mutations.toml` lists bugs: an edit to the code, the claim theorem the bug must make
false, and a refutation, a proof of `False` from that theorem's statement on the buggy
code. For each, the run plants the edit and requires two things: a proof breaks, and the
refutation compiles. A broken proof alone could mean the proof was fragile; the
refutation shows the claim itself is false of the buggy code.

Before planting anything the run checks itself on the unchanged code: no claim may read
as broken, and no refutation may compile.

A mutation marked `same_behaviour = true` changes the code without changing what it does.
It refutes nothing, and the run reports whether a proof broke anyway. A mutation the
build refuses, for an unused variable say, is counted apart: it was never tested.

Edits are planted through a journal, so a run that is killed leaves the files as they
were.

## What it cannot do

It tests the bugs someone thought to write down. A bug nobody listed is not tested. The
audit's determination theorems are the answer to bugs nobody thought of: when the claims
pin the function down, no behaviour-changing bug can survive.

## What it trusts

The catalog. `selftest/mutation_engine.py` runs five catalogs that should make the run
fail and requires each to fail for its reason.
