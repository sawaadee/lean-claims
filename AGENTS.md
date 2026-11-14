<!--
File: AGENTS.md
Purpose: How to work on lean-claims itself, for a coding agent or a person new to the
repository: the rules a change must keep, where things are, and the one command that
says whether a change is sound. A project built with lean-claims has its own guide,
`template/AGENTS.md`.
Created: 2026-11-13
-->

# Working on lean-claims

lean-claims checks other projects. A fault here is a fault in every project that relies
on it, so the tools are held to their own rule: nothing counts as working until it has
been seen to fail on a fault planted for it.

## Rules

1. **A check comes with its fault.** A new check, or a new rule in an existing one, is
   added together with a planted fault it must catch: a generated fault in
   `tools/leanclaims/generated_faults.py` when every project can have it, or an entry in
   `template/faults.toml`. `claims checks` must report it caught.
2. **A Lean command comes with fixtures.** A command in `LeanClaims/` that reports facts
   is tested on declarations written for it in `selftest/LeanClaimsTest/`, including
   true, proved declarations it must refuse to count. The expectations live in a
   `selftest/*_facts.py` file.
3. **Lean decides what Lean can decide.** A fact about a theorem's statement, a module's
   declarations or a definition's attributes is asked of Lean. Source text is read only
   where a file may not compile, and that reading is compared with Lean's where it does.
4. **A tool says what it cannot do.** Every module's header and every page under `docs/`
   states the limit of the check it describes. Do not remove a limit without removing
   the cause.
5. **No dependency beyond Python's standard library**, and Python 3.11 or later. The
   tools run with `python3 -I`.
6. **Exit status**: 0 passed, 1 failed, 2 could not run. A check that could not run is
   never reported as passed.
7. **Every file starts with its name, its purpose and the date it was created.** The
   name is the file's path from the root of the project it belongs to: this repository
   for the tools, `template/` for the starter project, `examples/minijson/` for MiniJson.
   A project is then the same wherever it is copied to. A later change that alters what
   the file is for adds a `Revised:` line. `selftest/repository.py` checks the headers,
   and that the documents name only commands, paths and links that exist. `LICENSE` is the one
   exception: it is the licence's text unchanged, so that tools which recognise licences
   recognise it.
8. **The documents are kept true.** A change to a file format updates
   `docs/reference.md`, and a change to what a check does updates that check's page under
   `docs/`.

## Where things are

| Path | Holds |
|------|-------|
| `LeanClaims/` | The Lean package a project's test package requires |
| `tools/claims.py` | The one entry point; each subcommand is in `tools/leanclaims/` |
| `template/` | The starter project. `claims new` copies it under another name |
| `selftest/` | Tests of the tools: unit tests, fixtures for the Lean commands, and runs that must fail |
| `docs/` | The concepts, getting started, one page per check, and the reference for every file format |
| `.github/workflows/ci.yml` | What GitHub runs on every push |

## Before a change is done

```
python3 -I selftest/run.py
```

Every step must pass. It takes about fifteen minutes. It builds everything, runs the unit
tests and the tests of the Lean commands, checks the repository's own files and
documents, runs every check with the mutation run and the test of the checks on the
starter project and on MiniJson, requires the two long runs to fail on catalogs made to
fail them, creates a new project and checks it from scratch, and adds a second claim to
another.

A change to a generated file's format, to the starter's claims or to its catalogs also
needs `claims sync`, `claims lock --update` and `claims trust` run on `template/`, in
that order as they apply.
