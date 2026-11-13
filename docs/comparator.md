<!--
File: docs/comparator.md
Purpose: What `lake comparator` catches in a lean-claims project, how, what it cannot, and
what it trusts.
Created: 2026-11-13
-->

# The comparator

`lake comparator --paranoid`

## What it catches

A proof that does not prove its claim, as judged by kernels other than the one that built
it. A bug in one kernel, or a file arranged to mislead the build, would have to fool all
of them the same way.

## How

The spec is the challenge: every claim stated with `sorry`. The proofs are the solution.
`lake comparator` checks, in a sandbox, that for each name in `comparator.json` the
solution's theorem has the challenge's statement, depends only on the allowed axioms, and
is accepted by each kernel it runs. With `--paranoid`, which `claims verify` uses, that is
six. A kernel that cannot finish a proof, for want of stack say, fails the check like one
that rejects it: the proof is then restated until every kernel can check it.

## What it cannot do

It compares statements; it does not judge them. A claim that says too little passes.
It needs bubblewrap and Linux.

## What it trusts

The kernels it runs, the sandbox, and `comparator.json`, which `claims sync --check`
confirms is the one generated from the spec.
