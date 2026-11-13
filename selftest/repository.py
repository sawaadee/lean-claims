"""
File: selftest/repository.py
Purpose: Checks the repository's own files against the rules in `AGENTS.md` that no other
test covers: every file starts with its name, its purpose and the date it was created;
the name is the file's path from the root of the project it belongs to; and the
documents name only commands that exist, paths that exist and links that resolve.

Before it looks at the repository it runs each rule on a text written to break it and
requires the rule to object, so that a rule which had stopped working would not pass
unnoticed.

Usage: python3 -I selftest/repository.py
Exit status: 0 when every file passes, 1 otherwise.
Created: 2026-11-14
"""

import re
import subprocess
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parent.parent
SKIPPED_DIRECTORIES = {".git", ".lake", "__pycache__"}
# Files that cannot carry a header: the licence's text must be unchanged for tools to
# recognise it, the toolchain file is one line that Lean's installer reads whole, and JSON
# has no comments.
WITHOUT_HEADER = {"LICENSE", "lean-toolchain"}
SUFFIXES_WITHOUT_HEADER = {".json"}
# The roots of the projects kept inside this repository. A file under one gives its path
# from that root, so that the project is the same wherever it is copied to.
PROJECT_ROOTS = ("template/", "examples/minijson/")
# The files `selftest/second_claim.py` copies into a new project. Each carries the header
# of the place it is copied to. The two `.txt` files are pieces added to the end of other
# files and carry none. `selftest/second_claim/README.md` says so.
SECOND_CLAIM_FIXTURES = {
    "selftest/second_claim/InRange.lean": "RangeTools/InRange.lean",
    "selftest/second_claim/ProofsInRange.lean": "RangeTools/Proofs/InRange.lean",
    "selftest/second_claim/InRangeAudit.lean": "tests/InRangeAudit.lean",
    "selftest/second_claim/claim7.lean.txt": None,
    "selftest/second_claim/mutation.toml.txt": None,
}
HEADER_LINES = 14
DOCUMENTS = ("README.md", "AGENTS.md", "docs", "template/README.md", "template/AGENTS.md",
             "examples/minijson/README.md")
_FILE_LINE = re.compile(r"File: (\S+)")
_CREATED_LINE = re.compile(r"Created: \d{4}-\d{2}-\d{2}")
_SUBCOMMAND = re.compile(r"`claims ([a-z]+)")
_REPOSITORY_PATH = re.compile(r"`((?:selftest|tools|docs|template|examples|LeanClaims)/[A-Za-z0-9_./-]+)`")
_LINK = re.compile(r"\]\(([^)#\s]+)\)")


def expected_header_path(relative_path: str) -> str | None:
    """The path a file's header must give, or `None` for a file that carries no header."""
    if relative_path in SECOND_CLAIM_FIXTURES:
        return SECOND_CLAIM_FIXTURES[relative_path]
    name = relative_path.rsplit("/", 1)[-1]
    if name in WITHOUT_HEADER or Path(name).suffix in SUFFIXES_WITHOUT_HEADER:
        return None
    for root in PROJECT_ROOTS:
        if relative_path.startswith(root):
            return relative_path[len(root):]
    return relative_path


def header_problems(relative_path: str, text: str) -> list[str]:
    """What is wrong with a file's header."""
    expected = expected_header_path(relative_path)
    if expected is None:
        return []
    header = "\n".join(text.split("\n")[:HEADER_LINES])
    named = _FILE_LINE.search(header)
    problems = []
    if named is None:
        problems.append(f"{relative_path}: no 'File:' line in its first {HEADER_LINES} lines")
    elif named.group(1) != expected:
        problems.append(f"{relative_path}: its header says 'File: {named.group(1)}', and its path is {expected}")
    if "Purpose:" not in header:
        problems.append(f"{relative_path}: no 'Purpose:' in its first {HEADER_LINES} lines")
    if _CREATED_LINE.search(text) is None:
        problems.append(f"{relative_path}: no 'Created:' line with a date")
    return problems


def document_problems(relative_path: str, text: str, subcommands: set[str], exists) -> list[str]:
    """What a document names that is not there: a `claims` subcommand, a path in this
    repository, or the target of a link. `exists` answers whether a path relative to the
    repository exists."""
    problems = []
    for subcommand in sorted(set(_SUBCOMMAND.findall(text)) - subcommands):
        problems.append(f"{relative_path}: names `claims {subcommand}`, which is not a subcommand")
    for named in sorted(set(_REPOSITORY_PATH.findall(text))):
        if not exists(named.rstrip("/")):
            problems.append(f"{relative_path}: names `{named}`, which does not exist")
    directory = relative_path.rsplit("/", 1)[0] if "/" in relative_path else ""
    for target in sorted(set(_LINK.findall(text))):
        if target.startswith(("http://", "https://")):
            continue
        resolved = (Path(directory) / target).as_posix() if directory else target
        if not exists(resolved):
            problems.append(f"{relative_path}: links to {target}, which does not exist")
    return problems


def rules_that_do_not_object() -> list[str]:
    """Run each rule on a text written to break it. The result is the list of rules that
    let their text through, which must be empty."""
    silent = []
    good = "# File: tools/x.py\n# Purpose: A test.\n# Created: 2026-01-02\n"
    cases = [
        ("a header with no File line", header_problems("tools/x.py", good.replace("File: tools/x.py", "x")), "no 'File:' line"),
        ("a header with another file's path", header_problems("tools/y.py", good), "its path is tools/y.py"),
        ("a header with no purpose", header_problems("tools/x.py", good.replace("Purpose", "About")), "no 'Purpose:'"),
        ("a header with no date", header_problems("tools/x.py", good.replace("2026-01-02", "today")), "no 'Created:'"),
        ("a starter file that gives its path from the repository",
         header_problems("template/x.py", "# File: template/x.py\n# Purpose: A test.\n# Created: 2026-01-02\n"), "its path is x.py"),
        ("a command that does not exist",
         document_problems("docs/x.md", "Run `claims frobnicate`.", {"verify"}, lambda path: True), "not a subcommand"),
        ("a path that does not exist",
         document_problems("docs/x.md", "See `tools/missing.py`.", {"verify"}, lambda path: False), "does not exist"),
        ("a link that does not resolve",
         document_problems("docs/x.md", "See [the page](missing.md).", {"verify"}, lambda path: path != "docs/missing.md"),
         "links to missing.md"),
    ]
    for what, problems, expected in cases:
        if not any(expected in problem for problem in problems):
            silent.append(what)
    if header_problems("tools/x.py", good) or header_problems("LICENSE", "Apache License") \
            or document_problems("docs/x.md", "Run `claims verify`.", {"verify"}, lambda path: True):
        silent.append("a file with nothing wrong was objected to")
    return silent


def repository_files() -> list[str]:
    """Every file of the repository, relative to it: the files git tracks, or, in a copy
    without git, every file outside build output."""
    if (REPOSITORY / ".git").exists():
        listed = subprocess.run(["git", "ls-files"], cwd=REPOSITORY, capture_output=True, text=True, check=True)
        return sorted(name for name in listed.stdout.split("\n") if name and (REPOSITORY / name).is_file())
    files = []
    for path in sorted(REPOSITORY.rglob("*")):
        relative = path.relative_to(REPOSITORY)
        if path.is_file() and not SKIPPED_DIRECTORIES.intersection(relative.parts):
            files.append(relative.as_posix())
    return files


def real_subcommands() -> set[str]:
    completed = subprocess.run([sys.executable, "-I", str(REPOSITORY / "tools" / "claims.py"), "--help"],
                               capture_output=True, text=True, check=True)
    return set(re.search(r"\{([a-z,]+)\}", completed.stdout).group(1).split(","))


def main() -> int:
    silent = rules_that_do_not_object()
    if silent:
        print("these rules did not object to a text written to break them:")
        for what in silent:
            print(f"  {what}")
        return 1
    files = repository_files()
    problems = []
    for relative_path in files:
        try:
            text = (REPOSITORY / relative_path).read_text(encoding="utf-8")
        except UnicodeDecodeError:
            problems.append(f"{relative_path}: not a text file")
            continue
        problems += header_problems(relative_path, text)
    subcommands = real_subcommands()
    documents = [name for name in files
                 if any(name == document or name.startswith(document + "/") for document in DOCUMENTS)]
    for relative_path in documents:
        text = (REPOSITORY / relative_path).read_text(encoding="utf-8")
        problems += document_problems(relative_path, text, subcommands, lambda path: (REPOSITORY / path).exists())
    if problems:
        print(f"{len(problems)} problems in the repository's files:")
        for problem in problems:
            print(f"  {problem}")
        return 1
    print(f"all 9 rules object to a text written to break them; {len(files)} files have their header, and "
          f"{len(documents)} documents name only commands, paths and links that exist")
    return 0


if __name__ == "__main__":
    sys.exit(main())
