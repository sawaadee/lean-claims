<!--
File: README.md
Purpose: What this project guarantees, where each guarantee is written down, and how to
check all of it again.
Created: 2026-11-13
-->

# Example

A library with one function, `Example.clamp`, which brings a number into a range. It is
the starter project of lean-claims: small enough to read in one sitting, and complete,
so that every check has something real to check.

## What is guaranteed

`Spec.lean` states every guarantee as a numbered claim, in English and then in Lean, with
the proofs left out. It is the file to review. `TRUST.md` lists every public declaration
and whether it is proved, tested or trusted, and is written by a tool from the spec.

| File | Holds |
|------|-------|
| `Spec.lean` | The claims. Written by hand. No tool writes to it |
| `spec.lock` | A hash of every claim, so a changed claim cannot pass unnoticed |
| `Example/` | The code |
| `Example/Proofs/` | The proofs, each under the name its claim has in the spec |
| `tests/ClampAudit.lean` | Theorems about the claims themselves: that each rules something out, that their hypotheses can hold, that together they determine the function |
| `tests/RunClamp.lean` | A program that runs the compiled code on a table of cases |
| `mutations.toml` | Bugs to plant in the code, each with the claim it must make false |
| `faults.toml` | Faults to plant so that every check is seen to fail |
| `claims.toml` | What the tools need to know: module names, the tested and trusted surface, waivers |
| `TRUST.md`, `comparator.json`, `Example/Verify.lean`, `tests/Axioms.lean` | Written by the tools |

## Check it again

`claims` below stands for `python3 -I <lean-claims>/tools/claims.py`.

```
lake build && (cd tests && lake build)
claims verify
claims verify --full
```

`claims verify` runs every check in order and says which passed: the lock, the generated
files, the build, the theorem names, the axioms, the comparison of the proofs with the
spec by independent kernels, the audit, the trust report, and the program. `--full` also
plants every bug of `mutations.toml` and every fault, which takes a few minutes.

`.github/workflows/ci.yml` runs `claims verify` on GitHub on a pull request and on a push
to a branch, and `claims verify --full` on a push to `main`.

Lean v4.35.0 on Linux. `lake comparator` needs [bubblewrap](https://github.com/containers/bubblewrap).
