<!--
File: AGENTS.md
Purpose: How to work in this project, for a coding agent or a person new to it: what may
be changed without asking, what may not, the order of the steps that add a guarantee, and
what to do when a check fails.
Created: 2026-11-13
-->

# Working in this project

This project states its guarantees as numbered claims in `Spec.lean`, proves them, and
has every proof, statement and check tested by machine. `claims` below stands for
`python3 -I <lean-claims>/tools/claims.py`, run in this directory.

## What you may not do without the owner's approval

1. **Change `Spec.lean`.** The claims are what the project promises. Add, change or
   withdraw a claim only when the owner asked for it or approved the wording. Never edit
   a claim to make a proof go through.
2. **Run `claims lock --update` for a change the owner has not seen.** The lock exists so
   that a changed claim cannot pass unnoticed. Updating it is the owner's signature.
3. **Add a `[[waiver]]`, a `[[trusted]]` entry or an axiom to `allowed_axioms`.** Each
   one lowers what the project guarantees. Propose it with the reason and wait.
4. **Edit a generated file.** `TRUST.md`, `comparator.json`, the verify file and
   `tests/Axioms.lean` are written by `claims sync` and `claims trust`.
5. **Weaken a check to make it pass.** Do not delete an audit theorem, a mutation or a
   fault, loosen a `caught_when_output_has`, or mark a mutation `same_behaviour`, to get
   to green. If a check is wrong, say so and stop.

Never use `sorry`, `native_decide` or a new axiom in a proof. The build and the axiom
assertion refuse them.

## Adding a guarantee

Do the steps in this order. Each ends with the check that says it is done.

1. **State the claim.** Write it in `Spec.lean` under the next free number: a header
   `/-! ## Claim N. Title`, the namespace lines, a doc comment that explains every
   hypothesis in plain words, and the theorem with the proof `by sorry`. Show the owner.
   When they approve, run `claims lock --update`.
2. **Write the code and the proof.** The proof goes in the proofs directory under the
   same name and with the same statement as in the spec. A new code file is imported by
   the library's root module, and a new proof file by the proofs' root module. Run
   `claims sync`, then `lake build`. The build fails if the statement proved is not the
   one stated.
3. **Audit the claim** in the audit module of `tests/`:
   - a property that asks the claim of any candidate implementation, and a theorem that
     ties it to the claim by proving it of the real implementation with the claim's
     theorem;
   - `/-- Audit: fails claim N. … -/` on a theorem `¬ Property wrongImplementation`, for
     a wrong implementation someone could plausibly write;
   - `/-- Audit: hypotheses of claim N can hold. … -/` on a theorem
     `hypotheses_can_hold% TheClaimTheorem`, when the claim has hypotheses;
   - `/-- Audit: determines claims …. -/` on a theorem that any candidate with the
     properties equals the implementation, extended to the new claim when it adds to
     what pins the function down.
   A new audit module is added to `modules` under `[audit]` in `claims.toml` and to the
   `roots` of the test library in `tests/lakefile.toml`, followed by `claims sync`.
   Run `(cd tests && lake build)` and `claims audit`.
4. **Plant a bug.** Add to `mutations.toml` a realistic bug in the new code, the claim
   theorem it must make false, and a proof of `False` from that theorem on the buggy
   code. Run `claims mutate`.
5. **Cover what cannot be proved.** If the change adds code with effects, or code marked
   `@[extern]` or `@[implemented_by]`, add its test, a `[[check]]` and a `[[fault]]` in
   `faults.toml`, and a `[[tested]]` entry in `claims.toml` that lists the declarations.
6. **Write the report.** Run `claims trust`. Every public declaration must be mentioned
   by a claim, be listed as tested or trusted, or be something a mentioned declaration
   is defined by. A helper that nothing mentioned is defined by, and that nobody outside
   should call, is made `private`.
7. **Check everything.** Run `claims verify --full`. Commit when all of it passes.

## When a check fails

| Check | It is telling you | Do |
|-------|-------------------|----|
| `lock` | A claim's text differs from the lock | If you did not mean to change the claim, put it back. If the owner approved the change, `claims lock --update` |
| `sync` | A generated file is out of date or was edited | `claims sync` |
| `build` | A proof is missing, unfinished, or proves another statement than the spec's | Fix the proof. Do not touch the spec |
| `names` | A theorem name is used twice in a layer, or a theorem is declared in a way the tools cannot read | Rename it, or declare it with a plain `theorem` |
| `axioms` | A theorem rests on an axiom outside the allowed list | Prove it without that axiom |
| `comparator` | An independent kernel does not accept a proof as proving its claim | Fix the proof. Report it if you believe the proof is right |
| `audit` | A claim lacks an audit or a mutation, or an `Audit:` line says something Lean does not confirm | Write the missing audit. Read the reason given: it names the property and why it does not count |
| `trust` | A public declaration has no claim, test or trust entry, or `TRUST.md` is out of date | State a claim, make it private, or propose an entry. Then `claims trust` |
| `mutate` | A planted bug broke no proof | The claims do not rule that bug out. Tell the owner: the fix is a new or stronger claim |
| `checks` | A check passed with its fault planted | The check does not work. Tell the owner |

## Style of the claims

- One claim says one thing, in a sentence a user of the library would understand.
- Every hypothesis is explained in the doc comment: what it says, and why it is needed.
- A claim that is only a consequence of others is still worth stating when it is what
  callers rely on. It then carries a waiver for `determines`, with that as the reason.
