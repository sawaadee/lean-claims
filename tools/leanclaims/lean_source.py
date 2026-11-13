"""
File: tools/leanclaims/lean_source.py
Purpose: Reads Lean source text without running Lean. It blanks out comments and string
literals so that a pattern cannot match text inside them, and it finds the theorems a
file declares together with the line each one is on.

The reading is lexical. It does not resolve namespaces, macros or notation. It is used
where a check must work on files that may not compile, such as a file with a planted
fault, and where the answer needed is "which names does this file's text declare".
Created: 2026-11-13
"""

import re
from dataclasses import dataclass


@dataclass(frozen=True)
class SourceSpan:
    """A comment or a string literal in a file: where it starts, where it ends (one past
    its last character), and which of the three it is."""

    start: int
    end: int
    kind: str  # "line comment", "block comment" or "string"


def comment_and_string_spans(source: str) -> list[SourceSpan]:
    """Every comment and string literal in `source`, in order, none inside another.

    Handled: line comments (`--` to the end of the line), block comments (`/- -/`,
    including doc comments, nested to any depth, reported as one span), string literals
    with backslash escapes, and the character literals that hold a double quote (`'"'`
    and `'\\"'`), which would otherwise open a string and are reported as strings.
    """
    spans = []
    length = len(source)
    position = 0
    while position < length:
        if source.startswith("--", position):
            end = source.find("\n", position)
            end = length if end == -1 else end
            spans.append(SourceSpan(position, end, "line comment"))
            position = end
        elif source.startswith("/-", position):
            depth = 1
            cursor = position + 2
            while cursor < length and depth > 0:
                if source.startswith("/-", cursor):
                    depth += 1
                    cursor += 2
                elif source.startswith("-/", cursor):
                    depth -= 1
                    cursor += 2
                else:
                    cursor += 1
            spans.append(SourceSpan(position, cursor, "block comment"))
            position = cursor
        elif source.startswith("'\"'", position):
            spans.append(SourceSpan(position, position + 3, "string"))
            position += 3
        elif source.startswith("'\\\"'", position):
            spans.append(SourceSpan(position, position + 4, "string"))
            position += 4
        elif source[position] == '"':
            cursor = position + 1
            while cursor < length and source[cursor] != '"':
                cursor += 2 if source[cursor] == "\\" else 1
            cursor = min(cursor + 1, length)
            spans.append(SourceSpan(position, cursor, "string"))
            position = cursor
        else:
            position += 1
    return spans


def blank_comments_and_strings(source: str) -> str:
    """Return `source` with the contents of every comment and string literal replaced by
    spaces. Line breaks are kept, so the result has the same length, the same number of
    lines, and every remaining character sits at its original position."""
    characters = list(source)
    for span in comment_and_string_spans(source):
        for index in range(span.start, span.end):
            if characters[index] != "\n":
                characters[index] = " "
    return "".join(characters)


@dataclass(frozen=True)
class DeclaredTheorem:
    """A theorem declaration found in a file's text."""

    name: str
    line_number: int
    # The doc comment directly above the declaration, or None when there is none.
    doc_comment: str | None = None


# A theorem declaration at the start of a line: optional attributes, optional modifiers,
# the keyword, then the name. The name ends at white space or at the first character that
# can begin a binder or the statement.
_THEOREM_DECLARATION = re.compile(
    r"^[ \t]*"
    r"(?:@\[[^\]\n]*\][ \t\n]*)*"
    r"(?:(?:private|protected|noncomputable|nonrec|unsafe)[ \t]+)*"
    r"theorem[ \t]+"
    r"(?P<name>[^\s:(\[{]+)",
    re.MULTILINE,
)


def declared_theorems(source: str) -> list[DeclaredTheorem]:
    """The theorems `source` declares, in the order they appear, each with the doc comment
    directly above it. A declaration inside a comment or a string is not counted."""
    spans = comment_and_string_spans(source)
    readable = blank_comments_and_strings(source)
    block_comments = [span for span in spans if span.kind == "block comment"]
    theorems = []
    for match in _THEOREM_DECLARATION.finditer(readable):
        line_number = readable.count("\n", 0, match.start("name")) + 1
        # The declaration starts at its attributes and modifiers. Its doc comment is the
        # block comment that ends just before that, with only white space between.
        doc_comment = None
        for comment in reversed(block_comments):
            if comment.end <= match.start():
                if source.startswith("/--", comment.start) and source[comment.end:match.start()].strip() == "":
                    doc_comment = source[comment.start:comment.end]
                break
        theorems.append(DeclaredTheorem(name=match.group("name"), line_number=line_number, doc_comment=doc_comment))
    return theorems
