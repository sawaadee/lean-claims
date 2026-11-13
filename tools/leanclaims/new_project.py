"""
File: tools/leanclaims/new_project.py
Purpose: Starts a new project from the starter project in `template/`. The starter is a
complete, passing project about one function, `Example.clamp`. A new project is that
project under the new name: every file copied, the name `Example` replaced, the
LeanClaims requirement of its test package pointed at a place the new project can reach,
and the lock and the generated files written again for the renamed spec.

The new project starts with every check passing, and its author replaces `clamp`, its
claims and its audits with their own, one check at a time.

What is replaced: the identifiers `Example`, `ExampleProofs` and `ExampleTests` wherever
they stand as whole words, the package names `example` and `exampletests` in the two
lakefiles, and the directory `Example/` and the file `Example.lean`. Each file's header gets the day the project
is created as its date, and loses the starter's `Revised:` lines. Build output and
Lake's manifests are not copied. Lake writes the manifests on the first build.
Created: 2026-11-13
"""

import re
from dataclasses import dataclass
from datetime import date
from pathlib import Path

from leanclaims.config import load_config
from leanclaims.lock import LOCK_FILE_NAME, lock_text
from leanclaims.spec import load_spec
from leanclaims.sync import write_generated_files

TEMPLATE_DIRECTORY = Path(__file__).resolve().parent.parent.parent / "template"
TEMPLATE_NAME = "Example"
SKIPPED_DIRECTORIES = {".lake", "__pycache__"}
SKIPPED_FILES = {"lake-manifest.json"}
_VALID_NAME = re.compile(r"[A-Z][A-Za-z0-9]*")
_NAME_AS_A_WORD = re.compile(r"\bExample(?P<suffix>Proofs|Tests)?\b")
_PACKAGE_NAME = re.compile(r'^name = "example(?P<suffix>tests)?"$', re.MULTILINE)
# A file's header says when it was created and how it was revised since. In a new project
# every file is created the day the project is, and has no history yet.
_CREATED_LINE = re.compile(r"Created: \d{4}-\d{2}-\d{2}")
_REVISED_LINE = re.compile(r"^[ \t#]*Revised: .*\n", re.MULTILINE)
# The requirement the starter's test package has on LeanClaims inside this repository,
# and the paragraph of its lakefile's header that explains it. A new project gets its own
# requirement and does not get the paragraph.
_TEMPLATE_REQUIREMENT = '[[require]]\nname = "LeanClaims"\npath = "../.."\n'
_TEMPLATE_REQUIREMENT_NOTE = (
    "#\n"
    "# Inside the lean-claims repository the LeanClaims package is two directories up.\n"
    "# `claims new` gives a project started from this one a requirement of its own.\n")


class NewProjectError(Exception):
    """The new project could not be created."""


@dataclass(frozen=True)
class LeanClaimsSource:
    """Where the new project's test package gets the LeanClaims package: a directory on
    this machine, or a git repository at a fixed revision."""

    path: Path | None = None
    git_url: str | None = None
    revision: str | None = None

    def requirement(self) -> str:
        if self.git_url is not None:
            return f'[[require]]\nname = "LeanClaims"\ngit = "{self.git_url}"\nrev = "{self.revision}"\n'
        return f'[[require]]\nname = "LeanClaims"\npath = "{self.path.as_posix()}"\n'


def renamed(text: str, name: str) -> str:
    """`text` with the starter's name replaced by `name`."""
    text = _CREATED_LINE.sub(f"Created: {date.today().isoformat()}", text, count=1)
    text = _REVISED_LINE.sub("", text)
    text = _NAME_AS_A_WORD.sub(lambda match: name + (match.group("suffix") or ""), text)
    return _PACKAGE_NAME.sub(lambda match: f'name = "{name.lower()}{match.group("suffix") or ""}"', text)


def template_files() -> list[Path]:
    """Every file of the starter project that a new project gets, relative to it."""
    files = []
    for path in sorted(TEMPLATE_DIRECTORY.rglob("*")):
        relative = path.relative_to(TEMPLATE_DIRECTORY)
        if path.is_file() and path.name not in SKIPPED_FILES and not SKIPPED_DIRECTORIES.intersection(relative.parts):
            files.append(relative)
    return files


def create_project(target: Path, name: str, source: LeanClaimsSource) -> list[str]:
    """Create the project `name` in the directory `target`, which must not exist or must
    be empty, and return the files written, relative to it."""
    if not _VALID_NAME.fullmatch(name):
        raise NewProjectError(
            f"'{name}' cannot name a project: use a capital letter followed by letters and digits, as in 'JsonParser'")
    if name == TEMPLATE_NAME:
        raise NewProjectError(f"'{TEMPLATE_NAME}' is the starter project's own name")
    if target.exists() and (not target.is_dir() or any(target.iterdir())):
        raise NewProjectError(f"{target} exists and is not an empty directory")
    if (source.git_url is None) == (source.path is None) or (source.git_url is not None and not source.revision):
        raise NewProjectError("say where LeanClaims is: a directory, or a git repository and a revision")

    written = []
    for relative in template_files():
        new_relative = Path(*(renamed(part, name) for part in relative.parts))
        text = renamed((TEMPLATE_DIRECTORY / relative).read_text(encoding="utf-8"), name)
        if relative.as_posix() == "tests/lakefile.toml":
            if text.count(_TEMPLATE_REQUIREMENT) != 1 or text.count(_TEMPLATE_REQUIREMENT_NOTE) != 1:
                raise NewProjectError("the starter's tests/lakefile.toml does not require LeanClaims as expected")
            text = text.replace(_TEMPLATE_REQUIREMENT, source.requirement()).replace(_TEMPLATE_REQUIREMENT_NOTE, "")
        destination = target / new_relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(text, encoding="utf-8")
        written.append(new_relative.as_posix())

    # The spec's text changed with the name, so its lock and the files generated from it
    # are written again. This is the one time a tool writes the lock unasked: the claims
    # are the starter's, renamed, and nobody has reviewed anything else yet.
    config = load_config(target)
    spec = load_spec(config)
    lock_path = target / LOCK_FILE_NAME
    lock_path.write_text(lock_text(spec, lock_path.read_text(encoding="utf-8")), encoding="utf-8")
    write_generated_files(config, spec)
    return written
