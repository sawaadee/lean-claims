<!--
File: docs/build.md
Purpose: What the ordinary build catches in a lean-claims project, what it cannot, and
what it trusts.
Created: 2026-11-13
-->

# The build

`lake build`

## What it catches

An unfinished proof, a proof that does not check, and a proof whose statement is not the
spec's.

## How

The project's lakefile sets `warningAsError`, and Lean reports `sorry` as a warning, so an
unfinished proof stops the build.

The verify file is a root of the proofs library. It restates every claim with `recall`,
which fails to compile unless the theorem of that name has exactly that statement. A
proof weakened to prove less than the spec says leaves the spec and the lock untouched
and fails here, in the build everyone runs anyway.

## What it cannot do

It uses one kernel, the one in the Lean it runs. It does not show that a proof avoids
`native_decide` or an added axiom: that is the axiom assertion. It says nothing about
whether the claims are worth proving.

## What it trusts

Lean's elaborator and kernel, and that the verify file is the one `claims sync` wrote,
which `claims sync --check` confirms.
