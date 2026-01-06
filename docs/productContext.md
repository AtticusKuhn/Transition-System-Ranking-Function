# Product Context

## Why this exists
Termination and fairness arguments are routinely proved “on paper” using ranking functions and automata-theoretic reductions, but those arguments are fragile when translated into tooling. Autoomaton aims to:

- make the core theory machine-checked (Lean kernel confidence),
- enable *constructive* artifacts (ranking functions / neural ranking functions) that can be synthesized externally and then verified internally.

## What the project should do (Target Workflow)
Given an input transition system (eventually: a program in a small imperative DSL):

1. Convert the program semantics to an automaton/transition system model.
2. Reduce a liveness/fairness/termination question to fair-emptiness.
3. If the system is fair-empty, synthesize a ranking function (ultimately: an NRF with a proven neuron bound).
4. Import the candidate ranking function back into Lean and validate it against the transition relation.

## User Experience Goals
- The formalization stays modular: results are re-usable without needing the entire pipeline.
- Key theorems have discoverable names, documentation, and “axiom footprint” checks.
- External synthesis (e.g. ILP) produces artifacts that are easy to feed into Lean (concrete weights/biases, explicit certificates).

