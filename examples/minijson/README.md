<!--
File: README.md
Purpose: What MiniJson is, what it guarantees, what it does not, how its claims came
about, and how to check all of it again. It is a worked example of a lean-claims
project of a kind the starter project is not.
Created: 2026-11-14
-->

# MiniJson

A parser and a renderer for a subset of JSON, written and proved in Lean 4: `null`,
`true`, `false`, natural numbers, and arrays. Strings, objects, a minus sign and fractions
are not part of it. The values are a recursive type, the proofs are by induction and not
by computation, and one of its functions is left undetermined on purpose.

```lean
MiniJson.parse  : String → Option Json
MiniJson.render : Json → String
```

## What is guaranteed

`Spec.lean` states seven claims. `TRUST.md`, written by a tool, lists every public
declaration and where it stands.

| Claim | Says |
|-------|------|
| 1 | A text parses to a value exactly when the text's tokens are the value's tokens |
| 2 | The text the renderer writes for a value has exactly that value's tokens |
| 3 | Parsing the text rendered for a value gives the value back |
| 4 | Two values with the same rendered text are the same value |
| 5 | The functions on strings are the functions on lists of characters |
| 6 | A text that parses to a value is that value's rendered text with white space added |
| 7 | A text parses to a value exactly when it is the value's tokens written out |

To read them a reviewer needs three definitions: `Json`, the values; `tokensOf`, the tokens
that stand for a value; and `writes`, which says in a few lines what it is for a text to
be a sequence of tokens written out, with white space only between them.

Claim 7 says everything about the parser: which texts it accepts and what it returns for
each. It does not mention the tokenizer, so the tokenizer is an implementation detail
that the claim holds to account and not something to take on trust. Claims 3 and 6 follow
from the others and are kept because they are what a caller reads first.

## What is not proved

- **The compiled code.** The proofs are about the definitions. That the code the compiler
  makes from them does the same is tested by the differential test.
- **The renderer is not determined.** Claim 2 leaves white space between tokens free, so
  many renderers meet it. `claims.toml` carries a waiver that says so.

## How the claims came about

MiniJson started with five claims. The other two were added because a planted bug
survived, which is the loop lean-claims is built around.

- **Claim 6.** A tokenizer that accepts a leading zero, planted as a bug, broke proofs
  and could be refuted by none of the first five claims. Claim 1 holds a text to its
  tokens, and the tokenizer decides what the tokens are. Claim 6 says an accepted text
  is the rendered text with white space added, and refutes it.
- **Claim 7.** Two more planted bugs survived claim 6. A tokenizer that reads a tab
  inside `true` passes it, because with its white space taken out `tr<tab>ue` is `true`.
  A tokenizer that refuses a tab as white space passes every claim up to 6, because
  they say what an accepted text must look like and none says a text must be accepted.
  Claim 7 is an "exactly when" that does not mention the tokenizer, and refutes both.

Two other things the checks caught:

- The first run of the differential test failed on `-0`, which JSON reads as the integer
  0. The library was right to refuse it. The answer key had been narrowed by value alone
  and let it through, and now also refuses any text with a minus sign.
- One of the six kernels `lake comparator --paranoid` runs overflowed its stack on one
  proof while the other five accepted it. The proof was restated, and all six accept it.

## The differential test

`tests/differential.py` gives the compiled program 6,043 texts and compares each verdict
with Python's `json` module, narrowed to this subset: fixed cases, random values with
random white space, and random strings of tokens and near-tokens. Python's `json` shares
no code with this library, and `claims.toml` lists it as trusted.

## Check it again

`claims` below stands for `python3 -I ../../tools/claims.py`. The steps for adding a
guarantee are in the starter project's guide, `template/AGENTS.md`.

```
lake build && (cd tests && lake build)
claims verify --full
```

That runs the nine checks (the eight every project has and the differential test), then
plants the twelve changes of `mutations.toml` and 21 faults.

Lean v4.35.0 on Linux. Python 3.11 or later. `lake comparator` needs
[bubblewrap](https://github.com/containers/bubblewrap).
