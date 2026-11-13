<!--
File: docs/audit.md
Purpose: What the audit requires of every claim, how Lean confirms it, what it cannot do,
and what it trusts.
Created: 2026-11-13
-->

# The audit

`claims audit`

## What it catches

A claim that is true and says nothing. A proof shows a claim holds of the code. It does not
show the claim rules anything out, that its hypotheses can ever be met, or that the claims
together say what the function is.

## How

Every claim needs, or has a written waiver for:

| Requirement | An audit theorem of the form |
|-------------|------------------------------|
| fails | `¬ P wrong`: a plausible wrong implementation does not meet the claim |
| determines | Any candidate with the claims' properties is the implementation |
| can hold | `hypotheses_can_hold% T`, for every theorem `T` of the claim with hypotheses |
| mutation | A bug in `mutations.toml` that the claim's theorem refutes |

An audit theorem says what it audits in the first line of its doc comment, `Audit: fails
claim 3.` and so on. The line is not taken on trust. Lean reads the theorem's statement
(`#audit_facts`) and must confirm it:

- `P` is a **property**: a definition in the audit module asking the claim of any
  candidate. It counts when a theorem proves it of the real implementation using the
  claim's theorem, and that statement is the claim's statement by unfolding. A property
  that gathers theorems of several claims does not count as failing any one of them.
- A determination theorem must take the claims of a candidate as hypotheses and conclude
  something that relates the candidate to the implementation or to another candidate.
- `hypotheses_can_hold% T` is built by Lean from `T`, so it cannot leave a hypothesis out.

A theorem proving `True` under an `Audit:` line is an error. So is a waiver for a
requirement that is met, which keeps the waivers a true list of gaps. Every `[[tested]]`
entry must name a check that exists and a fault planted for it.

## What it cannot do

Lean confirms that a property, asked of the project's own implementation, is the claim.
Whether the property asks the same of every other candidate is for the reviewer who reads
it. Whether the wrong implementations are ones a person would write is also a reviewer's
question.

## What it trusts

`#audit_facts`, which `selftest/audit_facts.py` tests on 25 theorems written for it,
nine of them true theorems it must refuse.
