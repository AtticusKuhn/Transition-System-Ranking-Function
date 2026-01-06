# Project Brief: Autoomaton

## One-liner
Formalize model-checking results in Lean4 and connect them to *constructive* (synthesizable) ranking functions, including neural ranking functions (NRFs).

## Core Goals
- Prove and maintain core theorems relating Büchi fairness to ranking functions in a reusable Lean library.
- Develop a formal theory of neural ranking functions (piecewise-linear / ReLU-style networks) and prove concrete neuron-count upper bounds for program-derived piecewise-linear functions.
- Long-term: build a pipeline from a small imperative DSL → transition system/Büchi automaton → synthesized (neural) ranking function → kernel-checked validation in Lean.

## Key Theorems (Current Anchors)
- `Autoomaton/Ordinal2.lean`: `fair_empty_iff_ranking_function` (fair-emptiness ↔ existence of a well-founded ordinal ranking function).
- `Autoomaton/completeNeurons.lean`: neuron-count bounds for representing piecewise-linear constructions as NRFs (e.g. `isNRFNeurons_complete_linear_sum'`).

## Non-Goals (For Now)
- Production-quality solver integration, performance engineering, or a polished end-user UI.
- Replacing Mathlib abstractions with custom data structures unless strictly necessary.

## Definition of “Done” (Near/Mid Term)
- The core Büchi/ranking results compile cleanly, with no reliance on `sorry` for critical theorems.
- The NRF capacity/bound results are stable, documented, and easy to apply.
- A minimal end-to-end example exists: a toy DSL program whose termination/fair-emptiness is discharged by a synthesized ranking function that is validated in Lean.

