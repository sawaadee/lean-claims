<!--
File: docs/lock.md
Purpose: What the spec lock catches, how, what it cannot, and what it trusts.
Created: 2026-11-13
-->

# The spec lock

`claims lock --check`

## What it catches

A claim whose text is not what was last agreed. A claim can be weakened by one character,
and a weakened claim is easier to prove. The lock makes any change to a claim, its doc
comments or the spec's imports and `open` lines show up as a failure until someone
decides it was meant.

## How

`spec.lock` holds a SHA-256 hash of each claim's full text, and one of the spec's preamble.
`claims lock --check` computes them again and names every claim that differs, was added,
or is gone. Every other command that reads the spec runs this first and stops if it fails.

`claims lock --update` rewrites the lock. Nothing else does. It is the step a person takes
on purpose, and in review a changed line of `spec.lock` is a changed claim.

## What it cannot do

It cannot tell a good change from a bad one. It reports that a claim changed; a person
judges whether it should have. It also does not look at the definitions a claim mentions:
changing what `clamp` means changes every claim about it without touching the spec. The
proofs, the mutation run and review of the code are what stand behind the definitions.

## What it trusts

That whoever runs `claims lock --update` read the change.
