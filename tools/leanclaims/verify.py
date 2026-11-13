"""
File: tools/leanclaims/verify.py
Purpose: Runs every check of a project in one command, in a fixed order, and says which
passed. The checks are the eight every project has and the ones the project declares in
`faults.toml`. With `full`, the two long runs follow: the mutation run and the test of
the checks.

Every check is run even after one fails, so that one run shows everything that is wrong.
The order puts the cheap checks first and the ones that build on them after: the lock
and the generated files, the build, then the checks that read what was built.
Created: 2026-11-13
"""

import sys
import time
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

from leanclaims.config import ProjectConfig
from leanclaims.faults import Check, built_in_checks
from leanclaims.process import run_command

TOOLS_DIRECTORY = Path(__file__).resolve().parent.parent
BUILT_IN_ORDER = ("lock", "sync", "build", "names", "axioms", "comparator", "audit", "trust")
# The two runs that plant things, which take minutes on a small project and longer on a
# large one. They are `claims` subcommands, not checks, because they test the checks.
LONG_RUNS = ("mutate", "checks")
OUTPUT_SHOWN_ON_FAILURE = 3000


@dataclass(frozen=True)
class CheckResult:
    check_id: str
    passed: bool
    seconds: float
    output: str


def checks_in_order(config: ProjectConfig, declared_checks: dict[str, Check]) -> list[Check]:
    """The eight built-in checks in their fixed order, then the project's own in the order
    `faults.toml` declares them."""
    built_in = built_in_checks(config, TOOLS_DIRECTORY)
    return [built_in[check_id] for check_id in BUILT_IN_ORDER] + list(declared_checks.values())


def long_runs(config: ProjectConfig) -> list[Check]:
    claims = (sys.executable, "-I", str(TOOLS_DIRECTORY / "claims.py"), "--project", str(config.project_directory))
    return [Check(subcommand, claims + (subcommand,), ".") for subcommand in LONG_RUNS]


def shown_command(check: Check) -> str:
    """A check's command as a person would type it: the tools' own subcommands as
    `claims …`, without the interpreter and the project path in front."""
    if check.command[0] == sys.executable and "--project" in check.command:
        return "claims " + " ".join(check.command[check.command.index("--project") + 2:])
    return " ".join(check.command)


def verify(config: ProjectConfig, declared_checks: dict[str, Check], full: bool,
           report: Callable[[str], None]) -> list[CheckResult]:
    """Run every check, reporting each as it finishes, and return the results."""
    to_run = checks_in_order(config, declared_checks) + (long_runs(config) if full else [])
    results = []
    for check in to_run:
        started = time.monotonic()
        status, output = run_command(list(check.command), config.project_directory / check.directory)
        result = CheckResult(check.check_id, status == 0, time.monotonic() - started, output)
        results.append(result)
        report(f"{'passed' if result.passed else 'FAILED'}  {check.check_id:<10}  {result.seconds:6.1f}s  "
               f"{shown_command(check)}")
        if not result.passed:
            for line in output[-OUTPUT_SHOWN_ON_FAILURE:].rstrip().splitlines():
                report(f"        {line}")
    return results
