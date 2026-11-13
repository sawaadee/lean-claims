"""
File: tools/leanclaims/spec.py
Purpose: Reads a project's spec file, the one file a reviewer reads to know what is
guaranteed, and enforces the rules that keep it reviewable. The spec is written by hand
and no tool writes to it; every other tool reads the claims from here.

The shape of a spec file:

  - A preamble: comments, `import` lines and `open` lines.
  - Then claims. A claim starts at a header, `/-! ## Claim N. Title`, and runs to the
    next header. It holds `namespace`, `open` and `end` lines and theorems, and nothing
    else. Each theorem has a doc comment and the proof `by sorry`.

The rules:

  - Claim numbers start at 1, rise by one, and appear in order.
  - Every namespace a claim opens, it closes. A claim therefore reads the same wherever
    it stands in the file, and its meaning depends only on its own text and the preamble.
  - Every theorem has a doc comment, and its proof is exactly `by sorry`.
  - A claim has at least one theorem, unless its title begins with "Withdrawn", in which
    case it has none. A withdrawn claim keeps its number so that numbers never move.
  - No theorem is stated twice.
  - The spec defines nothing: no `def`, no `instance`, no `axiom`, no notation.

The reading is lexical and does not run Lean. That the statements are well formed Lean
is checked by building the spec, and that they are what the proofs prove is checked by
`recall` in the build and by `lake comparator`.
Created: 2026-11-13
"""

import hashlib
import re
from dataclasses import dataclass

from leanclaims.config import ProjectConfig
from leanclaims.lean_source import SourceSpan, blank_comments_and_strings, comment_and_string_spans

CLAIM_HEADER_START = "/-! ## Claim"
_CLAIM_HEADER = re.compile(r"/-! ## Claim (?P<number>[1-9][0-9]*)\. (?P<title>[^\n]*\S)[ \t]*(?:\n|-/)")
_NAMESPACE_LINE = re.compile(r"namespace[ \t]+(?P<name>[^\s]+)[ \t]*")
_END_LINE = re.compile(r"end[ \t]+(?P<name>[^\s]+)[ \t]*")
_OPEN_LINE = re.compile(r"open(?:[ \t]+[^\s()]+)+[ \t]*")
_IMPORT_LINE = re.compile(r"import[ \t]+[^\s]+[ \t]*")
_THEOREM_START = re.compile(r"theorem[ \t]+(?P<name>[^\s:(\[{]+)")
_PROOF_LEFT_OUT = re.compile(r":=\s*by\s+sorry[ \t]*(?=\n|\Z)")
_LINE_START_THEOREM = re.compile(r"^theorem\b", re.MULTILINE)
# `open A in`, `open A hiding b` and `open A renaming b → c` change meaning in ways a
# line-by-line reader would get wrong, so the spec may not use them.
_OPEN_MODIFIERS = {"in", "hiding", "renaming"}


class SpecError(Exception):
    """The spec file breaks one of the rules above."""


@dataclass(frozen=True)
class SpecTheorem:
    """One theorem stated in the spec."""

    name: str
    namespace: str
    doc_comment: str
    # Everything between the theorem's name and its `:= by sorry`: binders, colon, statement.
    signature: str
    line_number: int

    @property
    def qualified_name(self) -> str:
        return f"{self.namespace}.{self.name}" if self.namespace else self.name


@dataclass(frozen=True)
class ClaimLine:
    """A `namespace`, `open` or `end` line inside a claim, kept so that a restatement of
    the claim can be read in the same setting."""

    text: str


@dataclass(frozen=True)
class Claim:
    """One numbered claim: its header and, in order, its setting lines and theorems."""

    number: int
    title: str
    text: str
    parts: tuple[ClaimLine | SpecTheorem, ...]
    line_number: int

    @property
    def withdrawn(self) -> bool:
        return self.title.startswith("Withdrawn")

    @property
    def theorems(self) -> tuple[SpecTheorem, ...]:
        return tuple(part for part in self.parts if isinstance(part, SpecTheorem))

    @property
    def text_hash(self) -> str:
        return text_hash(self.text)


@dataclass(frozen=True)
class Spec:
    """A spec file, read."""

    file_name: str
    preamble: str
    preamble_open_lines: tuple[str, ...]
    claims: tuple[Claim, ...]

    @property
    def theorems(self) -> tuple[SpecTheorem, ...]:
        return tuple(theorem for claim in self.claims for theorem in claim.theorems)

    @property
    def preamble_hash(self) -> str:
        return text_hash(self.preamble)


def text_hash(text: str) -> str:
    """SHA-256 of a piece of the spec. White space at its end is left out, so that blank
    lines between one claim and the next belong to neither."""
    return hashlib.sha256(text.rstrip().encode("utf-8")).hexdigest()


def spec_file_name(config: ProjectConfig) -> str:
    """The spec's path relative to the project: its module name as a file."""
    return config.spec_module.replace(".", "/") + ".lean"


def _line_number(source: str, position: int) -> int:
    return source.count("\n", 0, position) + 1


def _lines_with_positions(text: str, start: int, end: int):
    """Each line of `text[start:end]` with the position its first character has in `text`."""
    position = start
    while position < end:
        line_end = text.find("\n", position, end)
        line_end = end if line_end == -1 else line_end
        yield position, text[position:line_end]
        position = line_end + 1


def _check_open_line(line: str, file_name: str, line_number: int) -> None:
    words = line.split()
    if not _OPEN_LINE.fullmatch(line.strip()) or _OPEN_MODIFIERS & set(words[1:]):
        raise SpecError(f"{file_name}:{line_number}: an open line may only list namespaces: {line.strip()}")


def _read_preamble(source: str, readable: str, end: int, file_name: str) -> tuple[str, ...]:
    open_lines = []
    for position, line in _lines_with_positions(readable, 0, end):
        stripped = line.strip()
        if not stripped:
            continue
        line_number = _line_number(source, position)
        if stripped.startswith("open"):
            _check_open_line(line, file_name, line_number)
            open_lines.append(stripped)
        elif not _IMPORT_LINE.fullmatch(stripped):
            raise SpecError(
                f"{file_name}:{line_number}: before the first claim only comments, import lines and "
                f"open lines may appear: {stripped}")
    return tuple(open_lines)


def _doc_comment_before(source: str, theorem_start: int, block_comments: list[SourceSpan]) -> str | None:
    """The doc comment that ends just before the theorem, with only white space between."""
    for comment in reversed(block_comments):
        if comment.end <= theorem_start:
            if source[comment.end:theorem_start].strip() == "" and source.startswith("/--", comment.start):
                return source[comment.start:comment.end]
            return None
    return None


def _read_claim(source: str, readable: str, header: SourceSpan, block_end: int,
                block_comments: list[SourceSpan], file_name: str) -> Claim:
    header_line = _line_number(source, header.start)
    header_match = _CLAIM_HEADER.match(source, header.start)
    if header_match is None:
        raise SpecError(
            f"{file_name}:{header_line}: a claim header must read '/-! ## Claim N. Title', with a number "
            f"and a title on its first line")
    if header.start > 0 and source[header.start - 1] != "\n":
        raise SpecError(f"{file_name}:{header_line}: a claim header must start its line")
    number = int(header_match.group("number"))
    title = header_match.group("title").removesuffix("-/").rstrip()

    parts: list[ClaimLine | SpecTheorem] = []
    open_namespaces: list[str] = []
    position = header.end
    while position < block_end:
        line_end = readable.find("\n", position, block_end)
        line_end = block_end if line_end == -1 else line_end
        line = readable[position:line_end]
        stripped = line.strip()
        line_number = _line_number(source, position)
        if not stripped:
            position = line_end + 1
            continue
        if line[0] in " \t":
            raise SpecError(f"{file_name}:{line_number}: a line of a claim must start in the first column: {stripped}")
        namespace_match = _NAMESPACE_LINE.fullmatch(stripped)
        end_match = _END_LINE.fullmatch(stripped)
        theorem_match = _THEOREM_START.match(readable, position, line_end)
        if namespace_match is not None:
            open_namespaces.append(namespace_match.group("name"))
            parts.append(ClaimLine(stripped))
            position = line_end + 1
        elif end_match is not None:
            if not open_namespaces or open_namespaces[-1] != end_match.group("name"):
                raise SpecError(f"{file_name}:{line_number}: '{stripped}' closes a namespace that is not the open one")
            open_namespaces.pop()
            parts.append(ClaimLine(stripped))
            position = line_end + 1
        elif stripped.startswith("open"):
            _check_open_line(line, file_name, line_number)
            parts.append(ClaimLine(stripped))
            position = line_end + 1
        elif theorem_match is not None:
            name = theorem_match.group("name")
            proof = _PROOF_LEFT_OUT.search(readable, theorem_match.end(), block_end)
            next_theorem = _LINE_START_THEOREM.search(readable, theorem_match.end(), block_end)
            if proof is None or (next_theorem is not None and next_theorem.start() < proof.start()):
                raise SpecError(f"{file_name}:{line_number}: the proof of {name} must be exactly 'by sorry'")
            signature = source[theorem_match.end():proof.start()].rstrip()
            if ":" not in readable[theorem_match.end():proof.start()]:
                raise SpecError(f"{file_name}:{line_number}: theorem {name} has no statement")
            doc_comment = _doc_comment_before(source, position, block_comments)
            if doc_comment is None:
                raise SpecError(
                    f"{file_name}:{line_number}: theorem {name} needs a doc comment directly above it that "
                    f"explains its statement")
            parts.append(SpecTheorem(
                name=name, namespace=".".join(open_namespaces), doc_comment=doc_comment,
                signature=signature, line_number=line_number))
            following_line = readable.find("\n", proof.end(), block_end)
            position = block_end if following_line == -1 else following_line + 1
        else:
            raise SpecError(
                f"{file_name}:{line_number}: a claim may hold only namespace, open and end lines and "
                f"theorems; the spec defines nothing: {stripped}")
    if open_namespaces:
        raise SpecError(
            f"{file_name}:{header_line}: claim {number} leaves namespace {open_namespaces[-1]} open; a claim "
            f"closes every namespace it opens")

    claim = Claim(number=number, title=title, text=source[header.start:block_end],
                  parts=tuple(parts), line_number=header_line)
    if claim.withdrawn and claim.theorems:
        raise SpecError(f"{file_name}:{header_line}: claim {number} is withdrawn and must hold no theorem")
    if not claim.withdrawn and not claim.theorems:
        raise SpecError(
            f"{file_name}:{header_line}: claim {number} states no theorem; a claim that is no longer made "
            f"keeps its number with a title that begins 'Withdrawn'")
    return claim


def parse_spec(source: str, file_name: str) -> Spec:
    """Read a spec file's text and enforce its rules."""
    source = source.replace("\r\n", "\n")
    readable = blank_comments_and_strings(source)
    block_comments = [span for span in comment_and_string_spans(source) if span.kind == "block comment"]
    headers = [span for span in block_comments if source.startswith(CLAIM_HEADER_START, span.start)]
    if not headers:
        raise SpecError(f"{file_name}: no claim header '/-! ## Claim 1. Title' was found")

    preamble = source[:headers[0].start]
    preamble_open_lines = _read_preamble(source, readable, headers[0].start, file_name)

    claims = []
    for index, header in enumerate(headers):
        block_end = headers[index + 1].start if index + 1 < len(headers) else len(source)
        claims.append(_read_claim(source, readable, header, block_end, block_comments, file_name))

    for expected_number, claim in enumerate(claims, start=1):
        if claim.number != expected_number:
            raise SpecError(
                f"{file_name}:{claim.line_number}: found claim {claim.number} where claim {expected_number} "
                f"belongs; claims are numbered from 1 in order, with no gaps and no repeats")

    stated_in: dict[str, int] = {}
    for claim in claims:
        for theorem in claim.theorems:
            if theorem.qualified_name in stated_in:
                raise SpecError(
                    f"{file_name}:{theorem.line_number}: {theorem.qualified_name} is stated in claim "
                    f"{stated_in[theorem.qualified_name]} and again in claim {claim.number}")
            stated_in[theorem.qualified_name] = claim.number

    return Spec(file_name=file_name, preamble=preamble, preamble_open_lines=preamble_open_lines,
                claims=tuple(claims))


def load_spec(config: ProjectConfig) -> Spec:
    """Read the project's spec file."""
    file_name = spec_file_name(config)
    spec_path = config.project_directory / file_name
    if not spec_path.is_file():
        raise SpecError(f"{file_name} does not exist")
    return parse_spec(spec_path.read_text(encoding="utf-8"), file_name)
