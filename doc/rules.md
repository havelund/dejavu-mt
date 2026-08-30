# Recursive rules and state variables

Two related features close the running-summary gap declaratively: **rules**
(DejaVu's `where` clause) and their functional sugar, **state variables**.

## Rules

    prop r : Forall x . check(x) -> seen(x)
      where seen(x) := p(x) | (@ seen(x))

A rule `r(x̄) := body` is a recursively defined predicate. Its semantics
follows DejaVu exactly:

- **Per-position extension.** At every position the rule's extension is
  recomputed, as if its facts occurred in the trace at that position.
  Compute `o(4)` at one step and `o(5)` at the next, and `o(4)` is
  forgotten — unless a past operator over `o` remembers it in its own
  state.
- **Recursion only under `@`.** Every rule call inside a rule body (self,
  mutual, any) must sit below the previous-operator; the main formula may
  call rules at the current position. This makes rules pure recurrences
  over the previous position — no fixpoint computation — which is exactly
  the shape of every stateful node in the engine.
- Rule parameters must be exactly the body's free variables; call
  arguments are variables (constants are rejected, as in DejaVu); rule
  bodies are past-time.

Implementation: rule bodies compile as ordinary node subtrees, *before*
the main formula (so current-position calls read an already-computed
value); a rule call's value is the body root's value with parameters
renamed to the call's arguments (a constant substitution). Nodes below an
`@` inside a rule body evaluate in a second pass, so a recursive call
there can read its rule root's first-pass value — its own now-value is
only ever consumed next step, through the `@`'s previous-value slot.

**Rules can count.** As formulas over an SMT backend, rule bodies carry
arithmetic, and recursion over positions is what pure first-order logic
lacks for counting:

    prop c : Forall n . check(n) -> count(n)
      where count(n) := ((! @ true) & n = 1)
                      | (Exists m . (@ count(m)) & n = m + 1)

The extension of `count` is a moving singleton — the engine's state for it
is literally the formula `n = 7`. A running sum in constant space; DejaVu's
equality-only rules cannot do this.

## Python actions: producing data during monitoring

Monitors can *produce* data, not only verdicts (PyContract-inspired).
Two attachment sites, both running deliberately side-effecting Python in
the `python:` block's namespace:

    prop c : true
      where count(n) := ((! @ true) & n = 1)
                      | (Exists m . (@ count(m)) & n = m + 1)
                      do {counts.append(n)}

    prop q : Forall f . Forall d . write(f,d) -> P open(f)
        on violation {incidents.append((pos, f))}

- **`do {expr}` on a rule** fires at every position where the rule's
  extension is non-empty **and changed** from the previous position (one
  equivalence check), with the parameters bound to a satisfying
  assignment — exact for functional rules (the moving singleton), a
  representative for multi-valued ones — plus `pos`.
- **`on violation {expr}` / `on satisfaction {expr}` on a property** fire
  once per emitted verdict, in emission order (delayed verdicts fire at
  emission, end of trace included), with `pos` and the witness values
  bound: falsifying values of a leading Forall-prefix for violations,
  satisfying values of a leading Exists-prefix for satisfactions.

Contract: actions may not feed back into the spec's state except through
declared state variables; exceptions in actions abort monitoring with the
rule/property named.

## State variables

The assignment idiom `x := x + 1 on ...` is the *functional* fragment of a
rule, and gets direct syntax with Python step-expressions:

    state total: Int := {0}
        on write(f, d): {total + len(d)}

    prop bound : total <= 1000000

Semantics (equivalently: the functional rule it corresponds to):

- the value starts as the `{init}` expression (evaluated in the `python:`
  block's namespace);
- on each event, every matching `on` clause updates the value — the
  clause's parameters bind the event's arguments (coerced by the declared
  predicate sorts), all state names are in scope with their *previous*
  values, and multiple matching facts fold left-to-right;
- updates run **before** the properties evaluate the event (the rule
  reading: the body pairs the event with the `@`-previous value);
- in formulas the state reads as a **term** — its current ground value
  injected as a literal per position. Atoms mentioning states are
  recompiled per event; everything else (past operators over them,
  quantifiers around them) behaves as with any other value. A `Bool`
  state doubles as an atom.

Because state values are ground by construction, none of the symbolic
machinery is involved: the monitor holds a Python value, and the property
stays whole — the trace the temporal operators see is untouched, unlike
the two-phase TP-DejaVu/PyDejaVu designs, whose examples (running byte
totals, per-file available space) are expressible this way in-spec.
Non-scalar bookkeeping (dicts, sets) lives in Python helper functions,
with scalar projections exposed as state values.

State variables must be pure in the same sense as spec Python functions:
their update expressions may compute anything, but the *monitor-visible*
value per position is the single source of truth.
