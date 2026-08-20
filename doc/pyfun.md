# Python functions inside formulas: interpreted symbols, lazy graphs

A spec may define Python functions and use them *inside* formulas:

    python:
        def size(d: str) -> int:
            return len(d)
        def risky(cmd: str) -> bool:
            return cmd in {"rm", "chmod", "dd"}
    end

    pred write(f: String, d: String)
    prop q : Forall f . Forall d . write(f,d) -> size(d) < 100

There is **no pre-phase**: unlike the two-phase designs of TP-DejaVu
(VMCAI 2024) and PyDejaVu (2025), where an operational stage transforms
events before a declarative monitor ever sees them — hiding part of the
property in code — here the property stays whole, in the formula.

## The mechanism

To the engine a Python function is an **uninterpreted SMT function
symbol** (created with `backend.func`, the same machinery as the
staged-resolution placeholders). As a symbol it composes with everything
the engine does — negation, quantifiers, temporal operators, storage in
states, quantifier elimination treats it as opaque — with no fragment
restriction on where it may appear.

Its **graph is supplied lazily**. During each step's normalization the
backend rewrite `eval_funs`:

1. propagates `var = literal` equalities into their sibling subterms —
   within conjunctions, and across the implication shape:
   `!(d=v & R) | C  ==  !(d=v & R) | C[d:=v]` (valid because the first
   disjunct is true whenever `d != v`); this is what makes event-guarded
   applications ground, since a predicate match contributes exactly the
   equalities `d = "abc"`;
2. replaces every application whose arguments are all literals by the
   result of calling the Python function — **memoized** per monitor, so
   functions must be **pure**.

The folded literal then flows like any other value: into since-states,
future-operator tables, obligations. `Forall`/`Exists` above a grounded
application eliminate as usual, since the function symbol is gone before
the quantifier is processed.

## The boundary, honestly

The solver cannot reason symbolically about arbitrary Python (that would
require the function's full graph, or a solver-side axiomatization). So
every verdict-relevant application must become **ground** at some point of
evaluation — in practice: guard its arguments with an event predicate so
the trace supplies them. If a verdict still depends on an unground
application (`Forall d . size(d) > 0` with no guard), the monitor raises a
clear error instead of guessing.

Declarations: functions must carry full type annotations
(`str/int/float/bool` ↔ `String/Int/Real/Bool`); a `bool` function may be
used directly as an atom; others in term position of relations
(`size(d) < 100`, `double(n + 1) > n`). Imports and helper definitions
inside the block are fine (only functions *defined* in the block become
symbols). Function names must not collide with predicates or macros.

## Relation to aggregations (MonPoly)

MonPoly's aggregation operators (SUM/AVG/MAX/CNT) are the *declarative*
route to computing over data: they stay inside the logic but aggregate
over the satisfying assignments of a subformula — which a finite relation
can enumerate and a symbolic formula-state in general cannot. The design
space is a triangle:

- **pointwise computation** — this feature: pure functions of data
  values, fully general, composes with the symbolic engine;
- **aggregation** — declarative operators, feasible exactly where a
  subformula's assignment set is finitely enumerable (the relational-safe
  fragment of `OPTIMIZATION.md`); a natural companion of the hybrid
  relational-state work, future;
- **operational summaries** (TP-DejaVu / PyDejaVu pre-phase) — rejected
  here: hides the property.

Stateful functions (accumulating across calls) are deliberately out:
call order/count during symbolic evaluation is an implementation detail,
and memoization assumes purity. Aggregation is the principled successor.
