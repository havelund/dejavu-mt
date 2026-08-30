# DejaVuMT — todo / roadmap

Working list; keep entries short, link designs where they exist.
(Feature history lives in git; decisions-with-rationale at the bottom.)

## Next up

- [ ] **Violation witnesses.** On a False verdict, extract the falsifying
      assignment from the solver model and report it with the violation
      ("violated at event 42 with f=f2").  Automatic explanations for every
      property — no user-written messages (contrast PyContract's f-string
      errors); listed in the paper outlook as "explanations via models".
- [ ] **JSONL log input.** `{"name": "Acquire", "thread": "t1", "lock": 3}`
      — fields matched to declared parameter names; multiple facts per
      event.  Makes real (Europa-Clipper-style) logs first-class.

## Larger projects

- [ ] **Relational-state hybrid** — see `OPTIMIZATION.md`.  Confine the
      live-set growth to genuinely symbolic state; ground-relational
      subformulas get set/dict storage.  Two concrete witnesses recorded
      (access log; transitive-closure rule from the DejaVu suite).
      PyContract-style *slicing* (per-key dispatch) is the natural first
      increment.  Would also unlock MonPoly-style aggregations
      (SUM/AVG/CNT over satisfying assignments).
- [ ] **Query-mode properties.** A property with declared free variables
      reports, per position, the constraint describing their valid values
      ("m = 12": the running max; "f = a | f = b": the open files) —
      monitors as query engines, generalizing parametric monitoring's
      constraint verdicts.  Covers MAX/MIN-style aggregations (order-
      definable); SUM/CNT stay with the hybrid above.
- [ ] **Performance kernel** (only when the ideas stop moving): the
      node-list evaluator as a Rust/C++ core against the Z3 C API, Python
      kept as frontend.  Recovers the ~50–100 µs/event interpreter floor;
      see `OPTIMIZATION.md`.

## Small / when touched anyway

- [ ] Anchored + trace-table polish: `-` cells documented; consider a
      summary line per anchored property in CLI output.
- [ ] `{_}` anonymous hole / unanchored `has` sugar for string patterns
      (offered once, never requested).
- [ ] Web UI: expose parametric verdicts/region and state variables.

## Parked (research-grade, revisit deliberately)

- [ ] Eager region-guarded resolution for nested parametric future — low
      priority by design: parameter discovery is offline log analysis;
      end-of-trace delivery is the norm (`doc/parametric.md`).
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
