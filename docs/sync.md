<!--
File: docs/sync.md
Purpose: What `claims sync` enforces and writes, what it cannot do, and what it trusts.
Created: 2026-11-13
-->

# The spec's rules and the generated files

`claims sync --check`

## What it catches

A spec that breaks the rules that make it reviewable, and a generated file that no longer
matches the spec, whether because the spec moved on or because someone edited the file.

## How

The rules of `Spec.lean`: claims are numbered from 1 in order; each claim closes every
namespace it opens, so it reads the same wherever it stands; every theorem has a doc
comment; every proof is exactly `by sorry`; the spec defines nothing, so a claim cannot
hide a definition of its own; a withdrawn claim keeps its number.

From the spec and `claims.toml`, `claims sync` writes three files: `comparator.json`,
naming every claim theorem for `lake comparator`; the verify file, restating every claim
with `recall` so the ordinary build compares each proof's statement with the spec's; and
`tests/Axioms.lean`, the axiom assertion over every proof module and test module of
theorems. `claims sync --check` writes nothing and fails when a file differs from what
would be written.

## What it cannot do

It reads the spec as text, by rules strict enough that anything it does not recognise is
an error. It does not understand Lean: a statement that is well formed text and wrong
Lean is found by the build, not here.

## What it trusts

Its own reading of the spec file. `selftest/test_tools.py` tests it on specs that break
each rule.
