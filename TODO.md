# DejaVuMT — todo / roadmap

Working list; keep entries short, link designs where they exist.
(Feature history lives in git; decisions-with-rationale at the bottom.)

## Inspired by PyContract (notes/papers/rv-pycontract-2022.pdf)

- [x] **Violation witnesses** (2026-08-30): falsifying assignment of the
      leading Forall-prefix from a solver model, shown in CLI violations
      (`[f=b, d=boom]`) and exposed as `FormulaMonitor.witnesses`.  Works
      for immediate, delayed (future), and rule-based violations; skipped
      gracefully for non-Forall roots, parametric verdicts, and values
      still behind placeholders.  (PyContract analogue: f-string error
      messages — here automatic, from the solver model.)
- [x] **JSONL log input** (2026-08-30): `.jsonl/.ndjson/.json` logs, one
      object per line, fields matched by name to declared parameters,
      `"time"` field for timed specs; native JSON numbers/booleans.
      (Multiple facts per event: the engine supports it, the readers still
      emit one fact per line — extend if a real log needs it.)
- [x] **Producing data during monitoring via Python actions**
      (2026-08-30): `r(x) := body do {expr}` fires when the extension is
      non-empty and changed (params bound to a satisfying assignment —
      exact for functional rules); `prop p : φ on violation {expr}` fires
      per emitted violation with `pos` + witness values.  Actions run in
      the python block's namespace; delayed verdicts fire at emission
      (end of trace included).  `on satisfaction {expr}` added too, with
      satisfying Exists-prefix witnesses (mirror of violation witnesses).
      Open refinement: enumerating multi-valued extensions (currently one
      representative model).
(PyContract's slicing mechanism is not a separate item: it is the first
increment of the relational-state hybrid under Larger projects.)

## Larger projects

- [ ] **Relational-state hybrid** — design notes in the Optimization
      section below.  Confine the
      live-set growth to genuinely symbolic state; ground-relational
      subformulas get set/dict storage.  Two concrete witnesses recorded
      (access log; transitive-closure rule from the DejaVu suite).
      First increment: PyContract-style *slicing* — per-key dispatch of
      state for quantified variables that are event-keyed, so an event
      touches only its own slice.  Would also unlock MonPoly-style
      aggregations (SUM/AVG/CNT over satisfying assignments).
- [ ] **Query-mode properties.** A property with declared free variables
      reports, per position, the constraint describing their valid values
      ("m = 12": the running max; "f = a | f = b": the open files) —
      monitors as query engines, generalizing parametric monitoring's
      constraint verdicts.  Covers MAX/MIN-style aggregations (order-
      definable); SUM/CNT stay with the hybrid above.
- [ ] **Performance kernel** (only when the ideas stop moving): the
      node-list evaluator as a Rust/C++ core against the Z3 C API, Python
      kept as frontend.  Recovers the ~50–100 µs/event interpreter floor;
      see the Optimization section below.

## To investigate

- [x] **SALT / PSL** (2026-09-05): investigated; outcome:
      * **Sequences implemented** — PSL-style SEREs with shared data
        variables, `{e1; e2[*]; e3} |-> phi`, desugared to generated
        @-guarded rules (rules are automata, so regular repetition
        beyond LTL's star-free limit comes free).
      * Scopes (upto/from/between): decided against — each is a
        one-operator guard we already have ([a,b) for between, P/!P for
        after/before, until-with-blocker for future confinement).
      * Aborts (accepton/rejecton/PSL abort): decided against for now —
        the effect is one disjunct (F[<=5] (ack | reset)) or one
        until-blocker per obligation; revisit if a reset-heavy case
        study appears.
      * Counted operators (occurring >= n times): rules count already.

## Small / when touched anyway

- [x] Anchored + trace-table polish (2026-08-30): `-` cells documented;
      `Anchored verdict for ...` summary line in CLI output.
- [x] `{_}` anonymous hole / unanchored `has` sugar for string patterns
      (2026-08-30).
- [x] Web UI (2026-08-30): parametric constraint verdicts render (and no
      longer crash serialization), regions and final states shown,
      violation cells carry witness tooltips, anchored `-` cells.
- [x] JSON results recording (2026-08-30): `json` CLI flag writes
      `<log>.results.json` — verdicts (incl. parametric constraints),
      violations with witnesses, regions, final states.

## Parked (research-grade, revisit deliberately)

- [ ] Eager region-guarded resolution for nested parametric future — low
      priority by design: parameter discovery is offline log analysis;
      end-of-trace delivery is the norm (doc/engine.md, Parametric monitoring).
- [ ] Two symbolic bounds on one operator; multi-occurrence / mixed-
      polarity parameters.

## Decided against (with rationale, do not revive casually)

- Lowercase seen-only quantifiers: occurrence-guarded equivalence — every
  meaningful lowercase formula already contains its guard; DejaVu's
  operative use was the GC annotation.  (README Status, paper evaluation.)
- Operational pre-phase (TP-DejaVu/PyDejaVu architecture): hides the
  property.  Replaced by in-formula Python functions, rules, and state
  variables.
- SMT arrays and general algebraic datatypes: use cases dissolve into
  formula-states/rules (arrays) and pointwise Python functions (ADT
  destructuring).  Enums implemented instead.

---

## Optimization notes: the live-set problem

Notes from a design discussion (2026-08-20), kept for when performance work
starts.  Context: the four-system benchmark (`experiments/perf_bench.py`,
paper table `tab:perf4`) and the access-log row of the paper's performance
table — DejaVu (BDD) 0.10 s, DejaVuMT 67 s on 11,006 events.

### The disease: genuinely-live data

DejaVuMT's one real performance pathology is state that accumulates many
*live* data values.  With 5,000 currently-logged-in users, the state of the
interval subformula is literally

    x = "u1" | x = "u2" | ... | x = "u5000"

one disjunct per value (~2N syntax nodes), and the per-step simplification
re-traverses all of it — quadratic total time.  `gc` cannot help: nothing
is dead, those users really are logged in.  The same information is compact
elsewhere:

- DejaVu: a BDD — the 5,000 values *share structure* (common bit prefixes
  collapse);
- MonPoly: a finite relation — a hash table with O(1) insert/delete/member.

A flat disjunction is the least compact possible representation of a big
set.  Subformulas whose values balance out (matched open/close) stay small;
the cost is concentrated exactly where a large set stays live.

A second concrete witness (2026-08-23, from validating recursive rules
against the DejaVu suite): the transitive-closure rule
`spawned(x,y) := @spawned(x,y) | spawn(x,y) | Exists z . (@spawned(x,z) &
spawn(z,y))` — the extension is a growing *binary relation* with a
relational join (the `Exists z`) per event.  DejaVu's BDDs handle its
10k-event logs in milliseconds; the formula representation needs the log
capped at ~150 events.  Verdicts agree wherever both run; the gap is purely
the representation, and this spec is the acid test for the hybrid design
below (a join over an explicit relation is O(|S|), and exactly what
relational monitors do).

### Candidate encodings

1. **Interval/range compression.**  Mine the disjunction for arithmetic
   structure (`x = 3 | ... | x = 4000` → `3 <= x <= 4000`).  Cheap, helps
   only nice sets.  A peephole, not a fix.

2. **Relational (hybrid) state — the promising one.**  Keep an explicit
   finite set `S` as engine-side data (a Python set/dict) and let the
   formula say `x ∈ S`.  The recurrence updates `S` destructively — insert
   and delete are what since-style operators do to live sets — and the
   formula stays constant-size.  This steals MonPoly's data structure for
   exactly the subformulas where the data *is* a finite relation, keeping
   formulas where it is not.

3. **BDD-as-a-term.**  Encode the value set as a BDD and bridge into the
   solver.  Steals DejaVu's sharing, but the bridging is awkward; least
   attractive.

### The design for option 2

**The boundary question** ("when is a state a plain value-set, when is it
genuinely symbolic like `x < b + 100`?") is not open — it is MonPoly's
monitorability condition in disguise: atoms guarded, negation only under a
guard, stored variables touched only by equality, no symbolic constraint
flowing into the stored set.  A static, per-subformula analysis (we read
the rules in MonPoly's `rewriting.ml`; see `experiments/monpoly_ab.py`
fragment stats) marks nodes *relational-safe*.

On safe nodes the queries stay relational too: at each event only the
event's ground tuples matter, so `Forall x . access(x,f) -> f ∈ S`
evaluates per ground tuple in O(1) — the set is never materialized as a
formula.  Formulas enter only where something genuinely symbolic does.

**Hybrid state**: `x ∈ S ∨ φ` — ground set plus symbolic residue.  Ground
insertions go to `S`, symbolic ones to `φ`.  Negation gives `x ∉ S ∧ ¬φ`;
guardedness is exactly the known sufficient condition making `∉ S` harmless
(the guard supplies finitely many candidates).

**Safety net**: verdict equivalence is provable, and the project has four
oracles (DejaVu, the reference evaluator, MonPoly, CVC5) plus the
differential harness — an unusually safe position for a representation
change.

### What is achievable, honestly

- **Achievable (high confidence):** per-event cost *independent of the
  number of live values* on the guarded fragment.  The access-log row goes
  from 67 s / quadratic to seconds / linear.  The claim for the paper:
  *the growth pathology is confined, by construction, to genuinely symbolic
  state* — the cost of expressiveness becomes local to where
  expressiveness is used.

- **Not achievable / previously oversold:** literal "MonPoly speed".
  MonPoly is fifteen years of OCaml at ~1 µs/event; DejaVuMT's floor is
  Python interpreting a node list, ~50–100 µs/event even on propositional
  properties with tiny state (66 µs/ev with a saturated state in
  `tab:perf4`).  The hybrid kills the O(live-values) *factor*, not the
  constant.

- **Where the real risk sits:** making the hybrid pair compose through
  *every* recurrence — since, intervals, timed windows, the future tables,
  staged resolution.  No single step is mysterious; the invariant must
  hold everywhere, and an analysis that bails to formulas too eagerly
  silently returns the status quo.  Paper-sized, not an afternoon.

### The language constant

OCaml is part of MonPoly's 1 µs/event: native code, cheap persistent
relations, pattern matching.  Python is part of DejaVuMT's velocity: the
heavy lifting (QE, sat) runs in Z3's C++ core, and the language tax
dominates only where per-event solver work is trivial.  If the constant is
ever needed: the node-list evaluator is a small, well-specified kernel — a
Rust/C++ port of `step()` against the Z3 C API, with Python kept as the
frontend, would recover most of the 50–100 µs floor.  An optimization for
after the ideas stop moving.
