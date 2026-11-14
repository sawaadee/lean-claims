<!--
File: docs/concepts.md
Purpose: The ideas behind lean-claims in one short page: what a proof leaves unanswered,
the spec, the levels of trust, the audit, and planted faults.
Created: 2026-11-14
Revised: 2026-11-14 (the limit on claims that restate the code)
-->

# The ideas

## What a proof does not tell you

Lean checks that a proof proves its statement. It does not check that the statement is
the one you meant, that it says anything, or that the checks around it would notice a
problem. Each of these has failed in real projects:

- A claim is weakened by one character, and the weaker claim is proved.
- A claim has hypotheses that can never all be true, so it is true and says nothing.
- A claim is true of the right function and also of many wrong ones.
- A function ships with no claim about it at all.
- A check reads the wrong file, or never runs, and reports success every time.

lean-claims is a set of checks for these, and a rule that every one of the checks must
itself be seen to fail.

## The spec

Every guarantee is a numbered claim in one file, `Spec.lean`, with the proofs left out.
It is written by hand and no tool writes to it. A reviewer who reads it, and the
definitions it mentions, knows what the project promises.

`spec.lock` holds a hash of every claim. Changing a claim makes every command stop until
someone runs `claims lock --update`, so a changed claim is always a decision and always
shows in review. The proofs live elsewhere under the same names, and the build fails
when a proved statement is not the one in the spec.

## Three levels, and a fourth

Not everything can be proved. Code that reads the clock or the network cannot. The code
the compiler produces is not what the proofs are about. So every public declaration
stands at a level, and `TRUST.md` says which:

| Level | Means |
|-------|-------|
| Proved | A claim's statement mentions it |
| Tested | It has a test, and a planted fault the test has been seen to catch |
| Trusted | Neither, with the reason written down |
| Supporting | No claim mentions it, and something a claim does mention is defined by it |

A declaration at no level fails the check. The point is not that everything is proved.
It is that nothing is left unsaid.

## The audit

A proof shows a claim is true of the code. The audit asks whether the claim is worth
having, with theorems about the claims themselves:

- **Fails.** A plausible wrong implementation does not meet the claim. So the claim rules
  something out.
- **Can hold.** The claim's hypotheses can all be true at once. So the claim applies to
  something.
- **Determines.** Any implementation that meets the claims is the real one. So the
  claims leave nothing unsaid.

A requirement that cannot be met, such as a function that is meant to have more than one
correct implementation, is lifted by a written waiver with its reason. Lean reads each
audit theorem's statement and must confirm it is the audit it says it is.

## Planted faults

A check that says "passed" tells you something only if it can say "failed". So for every
check there is a fault it exists to catch. The tools plant the fault, run the check,
require it to fail for that reason, and take the fault out again. Two commands do this:

- `claims checks` plants faults in the project: an unfinished proof, a changed claim, an
  edited generated file, a theorem that audits nothing, and the project's own.
- `claims mutate` plants bugs in the code and requires a claim to be proved false on
  each. A bug that breaks no claim means the claims say less than the code needs, and
  the answer is a new claim.

Nothing is planted by hand, and nothing stays planted. If a run is killed, the next one
puts the files back.

## What it does not do

- It does not write claims. Deciding what to promise is the author's work.
- It does not make a weak claim strong. It shows that it is weak.
- It does not verify Lean's compiler or runtime. That is why "tested" is a level.
- It does not tell a claim that states what the code should do from one that restates
  what the code does.

That last limit matters most. Suppose a function has a bug, and its claim is written by
copying the function's body: "the result equals this expression", where the expression
is the code. The proof goes through. Every planted bug breaks the claim, because any
change to the code breaks the equality. The audit confirms the claim rules things out and
determines the function. Every check passes, and the bug is still there, because the
claim says only that the code is the code.

No check here can catch that, and no mechanical check is known to. A passing
`claims verify` means the code meets its claims. Whether the claims are the right ones
is for a person to judge by reading `Spec.lean`. The tools keep that reading short: the
claims are in one file, written by hand, and the lock shows when one changes. A claim
worth having says something a reader can check against what the function is for, without
looking at how it is written: a bound, a round trip, an agreement with a simpler
definition.

Every page under `docs/` ends with what its check cannot do and what it trusts.
