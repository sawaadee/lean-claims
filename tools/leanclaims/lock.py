"""
File: tools/leanclaims/lock.py
Purpose: The spec lock. `spec.lock` records a hash of the spec's preamble and of every
claim's full text, so that the spec cannot change as a side effect of other work, and so
that a review of a change to the claims starts from a short file naming exactly which
claims changed.

The lock is rewritten only by `claims lock --update`. Every other command checks it
first and stops when the spec and the lock differ. The lock does not prevent a change to
the spec; it makes one impossible to miss: the change shows in two files, and a
repository can require its owner's review for both.

One line per entry, fields separated by tabs:
  context <hash>                          the preamble: imports and open lines
  claim <number> <hash> <theorems> <title>
Created: 2026-11-13
"""

from dataclasses import dataclass
from datetime import date
from pathlib import Path

from leanclaims.spec import Spec

LOCK_FILE_NAME = "spec.lock"


@dataclass(frozen=True)
class LockedClaim:
    number: int
    text_hash: str
    theorem_names: str
    title: str


@dataclass(frozen=True)
class Lock:
    preamble_hash: str
    claims: dict[int, LockedClaim]


class LockError(Exception):
    """`spec.lock` is not in the format this module writes."""


def created_line(existing_text: str | None) -> str:
    """The `Created:` line of a generated file: the one it already carries, so that
    writing the file again changes nothing, or today's date for a new file."""
    if existing_text is not None:
        for line in existing_text.splitlines():
            stripped = line.lstrip("# ").strip()
            if stripped.startswith("Created: "):
                return stripped
    return f"Created: {date.today().isoformat()}"


def lock_of(spec: Spec) -> Lock:
    return Lock(
        preamble_hash=spec.preamble_hash,
        claims={
            claim.number: LockedClaim(
                number=claim.number,
                text_hash=claim.text_hash,
                theorem_names=",".join(theorem.qualified_name for theorem in claim.theorems) or "-",
                title=claim.title)
            for claim in spec.claims
        })


def lock_text(spec: Spec, existing_text: str | None) -> str:
    """The full text of `spec.lock` for the spec as it stands."""
    lock = lock_of(spec)
    lines = [
        f"# File: {LOCK_FILE_NAME}",
        f"# Purpose: A hash of the preamble and of every claim of {spec.file_name}. A claim whose",
        "# line changes here is a claim whose text changed. Written by `claims lock --update`",
        "# and not edited by hand.",
        f"# {created_line(existing_text)}",
        f"context\t{lock.preamble_hash}",
    ]
    for number in sorted(lock.claims):
        claim = lock.claims[number]
        lines.append(f"claim\t{claim.number}\t{claim.text_hash}\t{claim.theorem_names}\t{claim.title}")
    return "\n".join(lines) + "\n"


def parse_lock(text: str) -> Lock:
    preamble_hash = None
    claims: dict[int, LockedClaim] = {}
    for line_number, line in enumerate(text.splitlines(), start=1):
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        if fields[0] == "context" and len(fields) == 2 and preamble_hash is None:
            preamble_hash = fields[1]
        elif fields[0] == "claim" and len(fields) == 5 and fields[1].isdigit() and int(fields[1]) not in claims:
            claims[int(fields[1])] = LockedClaim(
                number=int(fields[1]), text_hash=fields[2], theorem_names=fields[3], title=fields[4])
        else:
            raise LockError(f"{LOCK_FILE_NAME}:{line_number}: not a line this tool writes")
    if preamble_hash is None:
        raise LockError(f"{LOCK_FILE_NAME}: the context line is missing")
    return Lock(preamble_hash=preamble_hash, claims=claims)


def lock_differences(spec: Spec, project_directory: Path) -> list[str]:
    """How the spec differs from what `spec.lock` records. Empty when they agree."""
    lock_path = project_directory / LOCK_FILE_NAME
    if not lock_path.is_file():
        return [f"{LOCK_FILE_NAME} does not exist"]
    try:
        recorded = parse_lock(lock_path.read_text(encoding="utf-8"))
    except LockError as error:
        return [str(error)]
    current = lock_of(spec)
    differences = []
    if recorded.preamble_hash != current.preamble_hash:
        differences.append("the preamble (imports and open lines) changed")
    for number in sorted(set(recorded.claims) | set(current.claims)):
        if number not in recorded.claims:
            differences.append(f"claim {number} is in the spec and not in the lock: {current.claims[number].title}")
        elif number not in current.claims:
            differences.append(f"claim {number} is in the lock and not in the spec: {recorded.claims[number].title}")
        elif recorded.claims[number] != current.claims[number]:
            differences.append(f"claim {number} changed: {current.claims[number].title}")
    return differences
