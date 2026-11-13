<!--
File: docs/README.md
Purpose: An index of the documentation: where to start, and one page for each check.
Created: 2026-11-13
-->

# Documentation

Start with [concepts.md](concepts.md), the ideas in one short page. Then
[getting-started.md](getting-started.md) takes a new project from `claims new` to its
first claim of its own.

`examples/minijson` is a second complete project, a parser and renderer for a subset of
JSON. Its README says how planted bugs that survived led to two of its claims.

[reference.md](reference.md) lists every file a project holds and every key of
`claims.toml`, `mutations.toml` and `faults.toml`.

There is one page for each check, each saying what the check catches, how, what it cannot
catch, and what it trusts.

| Page | Check | Catches |
|------|-------|---------|
| [lock.md](lock.md) | `claims lock` | A claim whose text changed without anyone deciding it should |
| [sync.md](sync.md) | `claims sync` | A spec that breaks its rules, and generated files that are stale or edited |
| [build.md](build.md) | `lake build` | An unfinished proof, and a proof of another statement than the spec's |
| [names.md](names.md) | `claims names` | A theorem name used twice, and a theorem the tools' text reading cannot see |
| [axioms.md](axioms.md) | the axiom assertion | A proof that rests on `sorry`, `native_decide` or a new axiom |
| [comparator.md](comparator.md) | `lake comparator` | A proof that does not prove its claim, judged by independent kernels |
| [audit.md](audit.md) | `claims audit` | A claim that rules nothing out, cannot apply, or leaves the function undetermined |
| [trust.md](trust.md) | `claims trust` | A public declaration with no guarantee and no note saying so |
| [mutate.md](mutate.md) | `claims mutate` | A bug the claims do not rule out |
| [checks.md](checks.md) | `claims checks` | A check that cannot fail |

`claims verify` runs the first eight in order, then the project's own checks.
`claims verify --full` adds the last two.

Every page ends with the same two sections, because no check is complete: what it cannot
do, and what it trusts.
