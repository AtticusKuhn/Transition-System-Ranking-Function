# Progress

## What Works
- Büchi-style fairness and fair-emptiness infrastructure exists (`Autoomaton/Buchi.lean`).
- Fair-emptiness characterization via ordinal ranking functions is present:
  - `Autoomaton/Ordinal2.lean`: `fair_empty_iff_ranking_function`.
- Imperative DSL has a small-step semantics and a compilation to Büchi automata:
  - `Autoomaton/imperative_language.lean`: `Step` and `StatementToAutomaton` (with “all states fair” so fair-emptiness means no runs).
- NRF definitions and helper constructions exist (`Autoomaton/isNRF.lean`, `Autoomaton/isNRFNeurons.lean`).
- Neuron-count upper bounds for key constructions exist:
  - `Autoomaton/completeNeurons.lean`: includes `isNRFNeurons_complete_linear_sum'` and related lemmas.

## What’s Missing
- A proved “correctness bridge” theorem: runs of `StatementToAutomaton` ↔ infinite executions / nontermination (beyond local sanity checks).
- A principled way to turn DSL control-flow/guards into the piecewise-linear objects needed to apply the neuron bounds.
- A synthesis layer (ILP/SMT) and an import/validation story for solver outputs.

## Known Issues / Risks
- Some key results may rely on classical axioms (e.g. `Classical.choice`, `propext`); track this explicitly with axiom checks where it matters.
- Documentation coverage is uneven; new public declarations should include docstrings.
