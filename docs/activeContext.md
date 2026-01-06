# Active Context

## Current Focus
- Flesh out the imperative DSL enough to support “program → automaton” experiments (termination-as-fair-emptiness when all states are fair).

## Next Concrete Steps (Engineering)
- Prove a correctness statement connecting `StatementToAutomaton` runs to infinite executions / nontermination (currently only the construction + sanity checks exist).
- Extend the DSL beyond the current arithmetic/`<` guards as needed (e.g. richer boolean connectives).
- Connect neuron-count bounds to program structure (e.g., count pieces/regions induced by guards/branches).
- Prototype a synthesis interface (likely ILP/SMT) that outputs a candidate ranking function/NRF plus a Lean-checkable certificate.

## Notes / Constraints
- Keep core theorems free of `sorry`; add axiom checks on the most important statements as they stabilize.
- Prefer minimal, local refactors: the library is still in flux and large reorganizations are expensive.
