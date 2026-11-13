<!--
File: selftest/second_claim/README.md
Purpose: Says what the files in this directory are and why two of them have no header.
Created: 2026-11-13
-->

# The second claim

`selftest/second_claim.py` creates a project named `RangeTools` from the starter and adds
a second function, `inRange`, with a seventh claim about it, by the steps of the
project's `AGENTS.md`. These are the files it adds. Each `.lean` file carries the header
of the place in the new project it is copied to.

| File | Becomes |
|------|---------|
| `InRange.lean` | `RangeTools/InRange.lean`, the function |
| `ProofsInRange.lean` | `RangeTools/Proofs/InRange.lean`, the proof of claim 7 |
| `InRangeAudit.lean` | `tests/InRangeAudit.lean`, the audit of claim 7 |
| `claim7.lean.txt` | The text added to the end of `Spec.lean` |
| `mutation.toml.txt` | The entry added to the end of `mutations.toml` |

The two `.txt` files are pieces of other files, added to their ends, so they carry no
header of their own and are not valid files by themselves.
