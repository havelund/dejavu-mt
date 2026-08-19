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


@dataclass(frozen=True)
class BinExpr:
    """An arithmetic expression: left op right, with op in {"+","-","*"}."""
    left: "Expr"
    op: str
    right: "Expr"

    def __str__(self) -> str:
        return f"({self.left} {self.op} {self.right})"


@dataclass(frozen=True)
class Neg:
    """Unary minus applied to a non-constant expression."""
    arg: "Expr"

    def __str__(self) -> str:
        return f"-{self.arg}"


# An expression is a variable, a constant, or an arithmetic combination of them.
# Relation (Compare) operands are expressions; predicate arguments are Terms.
Term = Union[Var, Const]
Expr = Union[Var, Const, BinExpr, Neg]


# ---------------------------------------------------------------------------
# Relational operators
# ---------------------------------------------------------------------------

RELOPS = {"=", "<", "<=", ">", ">=", "contains"}


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
    """A relation between two expressions, e.g.  a1 < a2  or  v2 = v1 + 1."""
    left: Expr
    op: str
    right: Expr

    def __str__(self) -> str:
        return f"{self.left} {self.op} {self.right}"


@dataclass(frozen=True)
class Match(LTL):
    """subject matches "lit {u} lit {v:regex} ..."  -- a pattern constraint:
    subject equals the concatenation of the literal parts and the hole
    variables, each constrained hole a member of its regex.  Holes are free
    data variables (String); ALL decompositions count (declarative matching,
    not leftmost-greedy)."""
    subject: Term
    segments: tuple    # ("lit", s) | ("hole", var, re-or-None) | ("gap", re-or-None)
    pattern: str       # as written, for display
    regex: bool = False   # slashed flavour /re with {holes}/

    def __str__(self) -> str:
        if self.regex:
            return f"{self.subject} matches /{self.pattern}/"
        return f'{self.subject} matches "{self.pattern}"'


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
class Zince(LTL):
    """phi Z psi  -- psi held at some point strictly in the past, and phi has
    held at every step since (through now); equivalent to phi & @(phi S psi).
    DejaVu has only the timed form Z[<=n]; the untimed form is our extension."""
    left: LTL
    right: LTL

    def __str__(self) -> str:
        return f"({_b(self.left)} Z {_b(self.right)})"


def bound_str(low: int, high: Optional[int]) -> str:
    """Canonical display form of a time bound: [<=n], [a,b], or [a,*]."""
    if high is None:
        return f"[{low},*]"
    if low == 0:
        return f"[<={high}]"
    return f"[{low},{high}]"


@dataclass(frozen=True)
class TimedSince(LTL):
    """phi S[a,b] psi  -- psi held between `low` and `high` time units ago and
    phi has held ever since.  high=None means no upper bound (written `*`).
    The comparison forms are parser sugar: S[<=n] = S[0,n], S[<n] = S[0,n-1],
    S[>=n] = S[n,*], S[>n] = S[n+1,*].  `disp` preserves the bound as written
    in the source, for display only."""
    left: LTL
    low: int
    high: Optional[int]
    right: LTL
    disp: str = ""

    def __str__(self) -> str:
        b = self.disp or bound_str(self.low, self.high)
        return f"({_b(self.left)} S{b} {_b(self.right)})"


@dataclass(frozen=True)
class TimedZince(LTL):
    """phi Z[a,b] psi  -- psi held strictly in the past, between `low` and
    `high` time units ago, and phi has held at every step since."""
    left: LTL
    low: int
    high: Optional[int]
    right: LTL
    disp: str = ""

    def __str__(self) -> str:
        b = self.disp or bound_str(self.low, self.high)
        return f"({_b(self.left)} Z{b} {_b(self.right)})"


@dataclass(frozen=True)
class TimedOnce(LTL):
    """P[a,b] phi  -- phi held between `low` and `high` time units ago."""
    low: int
    high: Optional[int]
    arg: LTL
    disp: str = ""

    def __str__(self) -> str:
        b = self.disp or bound_str(self.low, self.high)
        return f"P{b} {_b(self.arg)}"


@dataclass(frozen=True)
class TimedHist(LTL):
    """H[a,b] phi  -- phi held at every position between `low` and `high` time
    units ago."""
    low: int
    high: Optional[int]
    arg: LTL
    disp: str = ""

    def __str__(self) -> str:
        b = self.disp or bound_str(self.low, self.high)
        return f"H{b} {_b(self.arg)}"


@dataclass(frozen=True)
class Next(LTL):
    """X phi  -- phi holds at the next step (future dual of @)."""
    arg: LTL

    def __str__(self) -> str:
        return f"X {_b(self.arg)}"


@dataclass(frozen=True)
class TimedUntil(LTL):
    """phi U[a,b] psi  -- psi holds at some position between `low` and `high`
    time units ahead, and phi holds at every position from now until then.
    high=None means no upper bound (written `*`)."""
    left: LTL
    low: int
    high: Optional[int]
    right: LTL
    disp: str = ""

    def __str__(self) -> str:
        b = self.disp or bound_str(self.low, self.high)
        return f"({_b(self.left)} U{b} {_b(self.right)})"


@dataclass(frozen=True)
class TimedEventually(LTL):
    """F[a,b] phi  -- phi holds at some position between `low` and `high` time
    units ahead;  = true U[a,b] phi.  `high` may also be a str: a symbolic
    parameter the monitor leaves free, so that verdicts become constraints on
    it (parametric monitoring)."""
    low: int
    high: Optional[int]
    arg: LTL
    disp: str = ""

    def __str__(self) -> str:
        b = self.disp or bound_str(self.low, self.high)
        return f"F{b} {_b(self.arg)}"


@dataclass(frozen=True)
class TimedAlways(LTL):
    """G[a,b] phi  -- phi holds at every position between `low` and `high` time
    units ahead;  = !F[a,b]!phi.  `high` may also be a str: a symbolic
    parameter (see TimedEventually)."""
    low: int
    high: Optional[int]
    arg: LTL
    disp: str = ""

    def __str__(self) -> str:
        b = self.disp or bound_str(self.low, self.high)
        return f"G{b} {_b(self.arg)}"


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
