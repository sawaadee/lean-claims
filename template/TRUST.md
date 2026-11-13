<!--
File: TRUST.md
Purpose: What Example guarantees and on what each guarantee rests: which declarations are
proved, which are tested, which are trusted, and what was waived. Written by `claims trust`
from the spec, `claims.toml`, the catalogs and what Lean reports. Not edited by hand:
`claims trust --check` fails when this file differs from what would be written.
Created: 2026-11-13
-->

# What Example guarantees

6 claims, stated in `Spec.lean` as 6 theorems. 1 public declaration: 1 mentioned by a claim, 1 tested, 0 trusted, 0 supporting, 0 a theorem of the code, 0 at no level.

A declaration can stand at more than one level. "Mentioned by a claim" means a claim's statement
uses it. It does not mean the claims say everything about it: the audits and the mutation run are
the checks on that, and the waivers below are where they were not met. "Supporting" means no
claim mentions it and a declaration that a claim does mention is defined by it: the claims bind it
as far as that declaration uses it, and say nothing of it otherwise.

## Claims

| Claim | States | Theorems | Mentions |
|-------|--------|----------|----------|
| 1 | The result is never below the lower bound. | `clamp_ge_low` | `Example.clamp` |
| 2 | The result is never above the upper bound, when the range is not empty. | `clamp_le_high` | `Example.clamp` |
| 3 | A number already in the range is returned unchanged. | `clamp_eq_self` | `Example.clamp` |
| 4 | A number at or below the lower bound becomes the lower bound. | `clamp_of_below` | `Example.clamp` |
| 5 | A number at or above the upper bound becomes the upper bound, when the range is not empty. | `clamp_of_above` | `Example.clamp` |
| 6 | For an empty range the result is the lower bound. | `clamp_of_empty` | `Example.clamp` |

## What a reviewer reads

The claims are written in 1 public declaration, directly or through the
definitions of the ones they use. Knowing what the claims mean requires reading each one.

`Example.clamp`

## Public declarations

| Declaration | Kind | Where | Proved by claims | Tested by | Trusted | Supporting |
|-------------|------|-------|------------------|-----------|---------|------------|
| `Example.clamp` | definition | Example/Clamp.lean:13 | 1, 2, 3, 4, 5, 6 | run |  |  |

## Tested, not proved

| What | Check | Fault it has been seen to catch | Declarations |
|------|-------|---------------------------------|--------------|
| The compiled `clamp` computes what its definition says. The proofs are about the definition; the compiler that turns it into the code that runs is not verified. | `run` | `compiled-clamp-applies-the-bounds-in-the-other-order` | `Example.clamp` |

## Trusted

Nothing listed in `claims.toml`.

Every project built this way also trusts: Lean's kernel and the kernels `lake comparator` runs,
which check the proofs; the Lean compiler and runtime, which turn definitions into the code that
runs; the axioms `propext`, `Classical.choice`, `Quot.sound`; and the lean-claims
tools, which are tested and not proved.

## Waivers

| Claim | Requirement lifted | Reason |
|-------|--------------------|--------|
| 1 | determines | A consequence of claims 3 to 6. It is stated because it is the property callers rely on. |
| 2 | determines | A consequence of claims 3 to 6. It is stated because it is the property callers rely on. |

## What the catalogs plant

`claims mutate` plants 8 changes to the code from `mutations.toml`. 7 name a claim: each must break a proof and have that claim proved false, unless the build
refuses the change. 1 keep the code's behaviour and name none.

`claims checks` plants 6 faults from `faults.toml`, and the faults it
generates for every project. The check each is planted for must catch it.

This file records what would be planted, not the result of a run. Run the two commands for that.
