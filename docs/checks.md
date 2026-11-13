<!--
File: docs/checks.md
Purpose: What the test of the checks catches, how, what it cannot, and what it trusts.
Created: 2026-11-13
-->

# The test of the checks

`claims checks`

## What it catches

A check that cannot fail. A check that has never been seen to fail has not been shown to
work.

## How

For each check there is a fault it exists to catch. The run confirms every check passes
on the unchanged project, then plants each fault in turn, runs the check it is planted
for, and requires that check to fail with given text in its output, so that a failure
for another reason is not counted.

Most faults are generated from the spec and `claims.toml` and need no entry: an
unfinished proof, a `native_decide`, a duplicate theorem, one the text reading misses, a
changed claim with a stale lock, an edited generated file, two claims' statements
exchanged in the verify file and in the spec, an `Audit:` line removed, a theorem
proving `True` under each kind of `Audit:` line, a tested entry's fault removed, an
unlisted public function, and an edited `TRUST.md`. A project adds its own in
`faults.toml`, with its own checks, such as its test suite.

The run also kills a process while its fault is planted and requires the file to come
back unchanged, and at the end confirms every file it touched is byte for byte what it
was.

## What it cannot do

It shows each check fails on one fault of its kind. It does not show a check catches every
fault of that kind.

## What it trusts

The faults being the right ones. `selftest/checks_engine.py` runs six catalogs that should
make this run fail and requires each to.
