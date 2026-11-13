<!--
File: docs/axioms.md
Purpose: What the axiom assertion catches, how, what it cannot, and what it trusts.
Created: 2026-11-13
-->

# The axiom assertion

`lake build <tests library>`

## What it catches

A theorem that rests on something other than the allowed axioms: `sorryAx` from an
unfinished proof, `Lean.ofReduceBool` from `native_decide`, which trusts the compiler, or
an axiom someone declared.

## How

`tests/Axioms.lean` is generated. It names every proof module and every module of theorems
in the test package, and for each theorem Lean finds in them it collects the axioms the
proof depends on. One outside `allowed_axioms` in `claims.toml` fails the build of the
test library and names the theorem and the axiom.

The theorems are found by Lean, not read from text, so a new theorem is covered without
being named. A test module in which no theorem is found is an error, so a misspelt or
emptied module cannot pass by checking nothing.

## What it cannot do

It covers the proof modules and the listed test modules. A theorem in a code module is
checked by the kernel like any other and is not asserted about here. It also cannot say
whether the allowed axioms are acceptable: the three standard ones are Lean's ordinary
logic, and adding a fourth is a decision for the project's owner.

## What it trusts

Lean's `collectAxioms`, and the list in `claims.toml`.
