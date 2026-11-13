"""
File: tests/differential.py
Purpose: The differential test. It gives the compiled parser and renderer several thousand
texts and compares each verdict with an answer key that shares no code with them:
Python's `json` module, narrowed to the values this library has.

The texts are of three kinds: fixed cases that have each caught a bug or stand for a rule
(a leading zero, a trailing comma, white space inside a word), random values rendered with
random white space, and random strings of tokens and near-tokens, most of which are not
valid.

The answer key accepts a text when `json.loads` accepts it, the value holds only `null`,
booleans, integers of zero or more, and lists of those, and the text has no minus sign.
Its rendering is `json.dumps` with no white space. The minus sign is named because JSON
reads `-0` as the integer 0, and this library has no minus sign at all. The first run of
this test is what showed that the narrowing by value alone let `-0` through.

Only spaces and tabs are used as white space, because the program reads one text to a
line. Line feeds and carriage returns as white space are covered by the proofs and not by
this test.

Usage: python3 -I tests/differential.py   (run in the project directory)
Exit status: 0 when every verdict agrees, 1 when one differs, 2 when the program could not run.
Created: 2026-11-14
"""

import json
import random
import subprocess
import sys
from pathlib import Path

TESTS_DIRECTORY = Path(__file__).resolve().parent
SEED = 20261114
RANDOM_VALUES = 2000
RANDOM_TOKEN_STRINGS = 4000

FIXED_CASES = [
    "null", "true", "false", "0", "7", "120", "[]", "[null]", "[1,[true,false],[]]",
    "01", "007", "[01]", "00",
    "[1,]", "[,1]", "[1 2]", "[", "]", "[[]", "[]]", ",",
    "nu ll", "tr\tue", "1 0", "tru", "falsee", "nulll", "Null", "TRUE",
    " null ", "\tnull", "[ 1 , 2 ]", "1 2", "",
    "-1", "-0", "1.5", "1e5", "\"a\"", "{}", "NaN", "Infinity",
    "[[[[[[[[[[1]]]]]]]]]]",
]
PIECES = ["null", "true", "false", "[", "]", ",", " ", "\t", "0", "1", "9", "12", "007", "nul", "e", "-", ".", "\"", "{", "}"]


def in_subset(value: object) -> bool:
    """Whether a value `json.loads` returned is one this library has."""
    if value is None or isinstance(value, bool):
        return True
    if isinstance(value, int):
        return value >= 0
    if isinstance(value, list):
        return all(in_subset(item) for item in value)
    return False


def expected_verdict(text: str) -> str:
    try:
        value = json.loads(text)
    except ValueError:
        return "refused"
    if not in_subset(value) or "-" in text:
        return "refused"
    return "ok " + json.dumps(value, separators=(",", ":"))


def random_value(generator: random.Random, depth: int) -> object:
    kind = generator.randrange(6 if depth < 4 else 4)
    if kind == 0:
        return None
    if kind == 1:
        return generator.random() < 0.5
    if kind in (2, 3):
        return generator.choice([0, 1, 9, 10, 99, 100, generator.randrange(10 ** generator.randrange(1, 30))])
    return [random_value(generator, depth + 1) for _ in range(generator.randrange(4))]


def with_white_space(generator: random.Random, text: str) -> str:
    """The text with spaces and tabs put between its tokens at random. A space is never
    put inside a word or a number, which would change what the text is."""
    result = []
    for index, character in enumerate(text):
        between_tokens = index == 0 or character in "[]," or text[index - 1] in "[],"
        if between_tokens and generator.random() < 0.3:
            result.append(generator.choice([" ", "\t", "  "]))
        result.append(character)
    if generator.random() < 0.3:
        result.append(" ")
    return "".join(result)


def texts() -> list[str]:
    generator = random.Random(SEED)
    generated = list(FIXED_CASES)
    for _ in range(RANDOM_VALUES):
        rendered = json.dumps(random_value(generator, 0), separators=(",", ":"))
        generated.append(with_white_space(generator, rendered))
    for _ in range(RANDOM_TOKEN_STRINGS):
        generated.append("".join(generator.choice(PIECES) for _ in range(generator.randrange(1, 9))))
    return generated


def main() -> int:
    cases = texts()
    completed = subprocess.run(["lake", "exe", "jsoncheck"], cwd=TESTS_DIRECTORY, input="".join(text + "\n" for text in cases),
                               capture_output=True, text=True)
    if completed.returncode != 0:
        print(f"the program could not be built or run:\n{completed.stdout[-2000:]}{completed.stderr[-2000:]}")
        return 2
    verdicts = completed.stdout.split("\n")[:-1]
    if len(verdicts) != len(cases):
        print(f"the program gave {len(verdicts)} verdicts for {len(cases)} texts")
        return 1
    accepted = 0
    mismatches = 0
    for text, verdict in zip(cases, verdicts):
        expected = expected_verdict(text)
        accepted += expected != "refused"
        if verdict != expected:
            mismatches += 1
            if mismatches <= 10:
                print(f"mismatch for the text {text!r}: the program says '{verdict}', the answer key says '{expected}'")
    if mismatches:
        print(f"{mismatches} of {len(cases)} verdicts differ from the answer key")
        return 1
    print(f"all {len(cases)} verdicts agree with the answer key: {accepted} texts accepted, {len(cases) - accepted} refused")
    return 0


if __name__ == "__main__":
    sys.exit(main())
