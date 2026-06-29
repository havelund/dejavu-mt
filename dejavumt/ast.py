"""
Abstract syntax for DejaVuMT specifications.

The surface language is DejaVu's QTL (first-order past-time LTL with macros and
recursive rules), extended with optional type annotations on declared
predicate/event parameters, e.g.

    pred open(f: String, m: String)
    pred bid(i: String, a: Int)

The AST here is deliberately free of any Z3 dependency: the evaluation engine
(engine.py) walks these nodes and produces the Z3 formulas.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import List, Optional, Union


# ---------------------------------------------------------------------------
# Terms (arguments to predicates and relations)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Var:
    name: str

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class Const:
    # value is a python str or int (or float); kind records the literal sort.
    value: object
    kind: str  # "String" | "Int" | "Real"

    def __str__(self) -> str:
        return repr(self.value) if self.kind == "String" else str(self.value)


Term = Union[Var, Const]


# ---------------------------------------------------------------------------
# Relational operators
# ---------------------------------------------------------------------------

RELOPS = {"=", "<", "<=", ">", ">="}


# ---------------------------------------------------------------------------
# LTL formulas
# ---------------------------------------------------------------------------

class LTL:
    """Base class for all temporal-logic formula nodes."""
    pass


@dataclass(frozen=True)
class TrueC(LTL):
    def __str__(self) -> str:
        return "true"


@dataclass(frozen=True)
class FalseC(LTL):
    def __str__(self) -> str:
        return "false"


@dataclass(frozen=True)
class Pred(LTL):
    name: str
    args: tuple  # tuple[Term, ...]

    def __str__(self) -> str:
        if not self.args:
            return self.name
        return f"{self.name}(" + ",".join(str(a) for a in self.args) + ")"


@dataclass(frozen=True)
class Compare(LTL):
    """A relation between two terms, e.g.  a1 < a2  or  a >= r."""
    left: Term
    op: str
    right: Term

    def __str__(self) -> str:
        return f"{self.left} {self.op} {self.right}"


@dataclass(frozen=True)
class Not(LTL):
    arg: LTL

    def __str__(self) -> str:
        return f"¬{_b(self.arg)}"


@dataclass(frozen=True)
class And(LTL):
    left: LTL
    right: LTL

    def __str__(self) -> str:
        return f"({_b(self.left)} ∧ {_b(self.right)})"


@dataclass(frozen=True)
class Or(LTL):
    left: LTL
    right: LTL

    def __str__(self) -> str:
        return f"({_b(self.left)} ∨ {_b(self.right)})"


@dataclass(frozen=True)
class Implies(LTL):
    left: LTL
    right: LTL

    def __str__(self) -> str:
        return f"({_b(self.left)} → {_b(self.right)})"


@dataclass(frozen=True)
class Iff(LTL):
    left: LTL
    right: LTL

    def __str__(self) -> str:
        return f"({_b(self.left)} ↔ {_b(self.right)})"


@dataclass(frozen=True)
class Prev(LTL):
    """@ phi  -- phi held at the previous step."""
    arg: LTL

    def __str__(self) -> str:
        return f"@ {_b(self.arg)}"


@dataclass(frozen=True)
class Since(LTL):
    left: LTL
    right: LTL

    def __str__(self) -> str:
        return f"({_b(self.left)} S {_b(self.right)})"


@dataclass(frozen=True)
class Once(LTL):
    """P phi  -- phi held at some point in the past or now."""
    arg: LTL

    def __str__(self) -> str:
        return f"P {_b(self.arg)}"


@dataclass(frozen=True)
class Hist(LTL):
    """H phi  -- phi has held at every point in the past and now."""
    arg: LTL

    def __str__(self) -> str:
        return f"H {_b(self.arg)}"


@dataclass(frozen=True)
class Interval(LTL):
    """[phi, psi)  -- phi has occurred (incl. now) and psi has not occurred since."""
    left: LTL
    right: LTL

    def __str__(self) -> str:
        return f"[{self.left},{self.right})"


@dataclass(frozen=True)
class Exists(LTL):
    """Exists x . phi  -- ranges over the full (possibly infinite) domain."""
    var: str
    arg: LTL

    def __str__(self) -> str:
        return f"∃ {self.var} . {_b(self.arg)}"


@dataclass(frozen=True)
class Forall(LTL):
    """Forall x . phi  -- ranges over the full (possibly infinite) domain."""
    var: str
    arg: LTL

    def __str__(self) -> str:
        return f"∀ {self.var} . {_b(self.arg)}"


# ---------------------------------------------------------------------------
# Declarations
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Param:
    name: str
    sort: str  # "String" | "Int" | "Real" | "Bool"


@dataclass(frozen=True)
class EventDecl:
    name: str
    params: tuple  # tuple[Param, ...]


@dataclass(frozen=True)
class Macro:
    name: str
    params: tuple  # tuple[str, ...]
    body: LTL


@dataclass(frozen=True)
class Property:
    name: str
    body: LTL


@dataclass
class Spec:
    events: List[EventDecl] = field(default_factory=list)
    macros: List[Macro] = field(default_factory=list)
    properties: List[Property] = field(default_factory=list)


def _b(x) -> str:
    return str(x)
