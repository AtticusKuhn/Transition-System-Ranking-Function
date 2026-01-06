# System Patterns

## High-level Architecture (Lean Library)
- The central objects are:
  - an automaton/transition system with fairness conditions,
  - runs and reachability,
  - ranking functions (natural/ordinal) and their relationship to fair-emptiness,
  - neural ranking functions (NRFs) and capacity/upper-bound theorems.

## Module Map (Where to Look)
- `Autoomaton/Buchi.lean`: definitions of `Run`, fairness, and `Automaton.IsFairEmpty`.
- `Autoomaton/NatRF.lean`: ranking functions into `Nat` (finite variants / lemmas).
- `Autoomaton/OrdinalRF.lean`, `Autoomaton/Ordinal2.lean`: ordinal ranking functions and the main fair-emptiness characterization.
- `Autoomaton/Path.lean`, `Autoomaton/succeeds.lean`: path/run utilities used in the Büchi/ranking development.
- `Autoomaton/isNRF.lean`: NRF building blocks (sign/relu maps, helper constructions).
- `Autoomaton/isNRFNeurons.lean`: bookkeeping for “number of neurons” used by constructions.
- `Autoomaton/completeNeurons.lean`: major neuron-count upper bounds for piecewise-linear compositions.
- `Autoomaton/imperative_language.lean`: imperative DSL + macros (`stmt| ...`), small-step semantics (`Step`), and compilation to automata (`StatementToAutomaton`).

## Development Patterns
- Keep `Autoomaton.lean` as the “build root” import list for the library.
- Prefer small, compositional lemmas; avoid giant proof scripts that are hard to maintain.
- For important theorems, include `#guard_msgs in #print axioms ...` so regressions in axiom usage are visible.
- Add documentation strings to public definitions/theorems; treat them as part of the interface.
