# Optimization notes: the live-set problem and what to do about it

Notes from a design discussion (2026-08-20), kept for when performance work
starts.  Context: the four-system benchmark (`experiments/perf_bench.py`,
paper table `tab:perf4`) and the access-log row of the paper's performance
table — DejaVu (BDD) 0.10 s, DejaVuMT 67 s on 11,006 events.

## The disease: genuinely-live data

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

## Candidate encodings

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

## The design for option 2

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

## What is achievable, honestly

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

## The language constant

OCaml is part of MonPoly's 1 µs/event: native code, cheap persistent
relations, pattern matching.  Python is part of DejaVuMT's velocity: the
heavy lifting (QE, sat) runs in Z3's C++ core, and the language tax
dominates only where per-event solver work is trivial.  If the constant is
ever needed: the node-list evaluator is a small, well-specified kernel — a
Rust/C++ port of `step()` against the Z3 C API, with Python kept as the
frontend, would recover most of the 50–100 µs floor.  An optimization for
after the ideas stop moving.
