<!--
File: docs/names.md
Purpose: What the theorem name check catches, how, what it cannot, and what it trusts.
Created: 2026-11-13
-->

# Theorem names

`claims names`

## What it catches

A theorem name used twice within a layer, and a theorem the tools' reading of source text
does not see. The spec, the comparator and the mutation run refer to theorems by name,
so a name has to identify one theorem. Lean accepts some duplicates without a word: two
`private` theorems in different files, or a theorem repeated outside the namespace its
file opens.

## How

First it reads the proof files as text and reports any name declared twice in a layer.
Reading text works on files that do not compile.

Then it builds the test package and asks Lean which theorems each proof module declares
(`#declared_theorems`). Any difference from what it read is a failure: a theorem behind
`set_option … in`, or one a macro makes, is reported and not silently left out of the
search. Theorems declared with `instance` are left out of the comparison.

## What it cannot do

The comparison needs the project to build. On a project that does not build, the first
part still runs and the second reports that it could not.

## What it trusts

Lean's record of where each declaration is in its file.
