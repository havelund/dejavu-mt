"""
Patterns with holes, for the `matches` relation:

    m matches "user {u}"
    m matches "{c}: mode {x:[A-Z]+} selected"

A pattern is literal text interleaved with *holes* `{var}`.  A hole names a
data variable and captures a substring; `{var:REGEX}` additionally constrains
the captured substring by a regular expression (a subset: literals, `.`,
classes `[a-z0-9]`, `*`, `+`, `?`, `|`, grouping).  Text between holes is
literal, not regex.

Semantics is a *constraint*, not an extraction: the pattern denotes

    subject = lit0 ++ u1 ++ lit1 ++ u2 ++ ...   (++ = string concatenation)
              and u_i in L(RE_i) for each constrained hole

so a hole with several possible decompositions yields *all* of them (the
enclosing quantifier ranges over every solution) -- declarative matching, not
PCRE's leftmost-greedy rule.

Parsed forms are backend-neutral:
  pattern:  list of ("lit", text) | ("hole", var, regex-or-None)
  regex:    ("lit", s) ("any") ("class", [(lo,hi),...])
            ("star", r) ("plus", r) ("opt", r) ("cat", [r..]) ("alt", [r..])
"""
from __future__ import annotations


class PatternError(ValueError):
    pass


def parse_pattern(text: str):
    """The pattern string as a list of segments."""
    segs = []
    lit = []
    i = 0
    while i < len(text):
        c = text[i]
        if c == "\\" and i + 1 < len(text) and text[i + 1] in "{}\\":
            lit.append(text[i + 1])
            i += 2
        elif c == "{":
            j = text.find("}", i)
            if j < 0:
                raise PatternError(f"unclosed hole in pattern: {text!r}")
            inner = text[i + 1:j]
            name, _, constraint = inner.partition(":")
            if not name.isidentifier():
                raise PatternError(f"bad hole name {name!r} in {text!r}")
            if lit:
                segs.append(("lit", "".join(lit)))
                lit = []
            segs.append(("hole", name,
                         parse_regex(constraint) if constraint else None))
            i = j + 1
        elif c == "}":
            raise PatternError(f"stray '}}' in pattern: {text!r}")
        else:
            lit.append(c)
            i += 1
    if lit:
        segs.append(("lit", "".join(lit)))
    if not segs:
        raise PatternError("empty pattern")
    return segs


def parse_regex(text: str):
    """A small regular-expression subset as a neutral AST."""
    pos = [0]

    def peek():
        return text[pos[0]] if pos[0] < len(text) else None

    def take():
        c = text[pos[0]]
        pos[0] += 1
        return c

    def alt():
        parts = [cat()]
        while peek() == "|":
            take()
            parts.append(cat())
        return parts[0] if len(parts) == 1 else ("alt", parts)

    def cat():
        parts = []
        while peek() not in (None, "|", ")"):
            parts.append(postfix())
        if not parts:
            return ("lit", "")
        return parts[0] if len(parts) == 1 else ("cat", parts)

    def postfix():
        a = atom()
        while peek() in ("*", "+", "?"):
            a = ({"*": "star", "+": "plus", "?": "opt"}[take()], a)
        return a

    def atom():
        c = take()
        if c == "(":
            a = alt()
            if peek() != ")":
                raise PatternError(f"unclosed '(' in regex: {text!r}")
            take()
            return a
        if c == "[":
            return charclass()
        if c == ".":
            return ("any",)
        if c == "\\":
            return ("lit", take())
        if c in "*+?)|":
            raise PatternError(f"unexpected {c!r} in regex: {text!r}")
        return ("lit", c)

    def charclass():
        ranges = []
        while peek() not in (None, "]"):
            lo = take()
            if lo == "\\":
                lo = take()
            if peek() == "-" and pos[0] + 1 < len(text) and text[pos[0] + 1] != "]":
                take()
                hi = take()
            else:
                hi = lo
            ranges.append((lo, hi))
        if peek() != "]":
            raise PatternError(f"unclosed '[' in regex: {text!r}")
        take()
        if not ranges:
            raise PatternError(f"empty character class in regex: {text!r}")
        return ("class", ranges)

    r = alt()
    if pos[0] != len(text):
        raise PatternError(f"trailing characters in regex: {text!r}")
    return r
