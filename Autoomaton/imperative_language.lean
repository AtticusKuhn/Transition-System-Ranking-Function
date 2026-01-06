import Autoomaton.Buchi
import Mathlib.Data.Vector.Basic

/-
Note that we can add and scale variables, but we do not multiply a variable
by a variable, because our technique relies on piecewise-linear functions.
-/

/-- The (very small) type language for imperative expressions. -/
inductive Typ : Type where
  | bool
  | int
  deriving DecidableEq, Repr

/-- Expressions over `vars` integer variables. -/
inductive Expression (vars : Nat) : Typ → Type where
  | var : Fin vars → Expression vars .int
  | literalInt : Int → Expression vars .int
  | add : Expression vars .int → Expression vars .int → Expression vars .int
  | scaleConstant : Int → Expression vars .int → Expression vars .int
  | lessThan : Expression vars .int → Expression vars .int → Expression vars .bool
  deriving DecidableEq, Repr

/-- Statements for the toy imperative language. -/
inductive Statement (vars : Nat) : Type where
  | whileLoop : Expression vars .bool → Statement vars → Statement vars
  | ifThenElse : Expression vars .bool → Statement vars →  Statement vars → Statement vars
  | skip : Statement vars
  | assign : Fin vars → Expression vars .int → Statement vars
  | sequence : Statement vars →  Statement vars → Statement vars
  deriving DecidableEq, Repr

/-- Program states consist of the current statement and the current store. -/
structure ProgramState (vars : Nat) : Type where
  currentStatement : Statement vars
  variableValues : List.Vector Int vars
  deriving DecidableEq

namespace Expression

/-- Evaluate an integer expression in a store. -/
def evalInt {vars : Nat} (σ : List.Vector Int vars) : Expression vars .int → Int
  | .var i => σ.get i
  | .literalInt n => n
  | .add e₁ e₂ => evalInt σ e₁ + evalInt σ e₂
  | .scaleConstant k e => k * evalInt σ e

/-- Evaluate a boolean expression in a store. -/
def evalBool {vars : Nat} (σ : List.Vector Int vars) : Expression vars .bool → Bool
  | .lessThan e₁ e₂ => decide (evalInt σ e₁ < evalInt σ e₂)

end Expression

/-- One small-step of the imperative operational semantics. -/
inductive Step {vars : Nat} : ProgramState vars → ProgramState vars → Prop
  | if_true (c : Expression vars .bool) (t e : Statement vars) (σ : List.Vector Int vars)
      (h : Expression.evalBool σ c = true) :
      Step ⟨.ifThenElse c t e, σ⟩ ⟨t, σ⟩
  | if_false (c : Expression vars .bool) (t e : Statement vars) (σ : List.Vector Int vars)
      (h : Expression.evalBool σ c = false) :
      Step ⟨.ifThenElse c t e, σ⟩ ⟨e, σ⟩
  | while_true (c : Expression vars .bool) (body : Statement vars) (σ : List.Vector Int vars)
      (h : Expression.evalBool σ c = true) :
      Step ⟨.whileLoop c body, σ⟩ ⟨.sequence body (.whileLoop c body), σ⟩
  | while_false (c : Expression vars .bool) (body : Statement vars) (σ : List.Vector Int vars)
      (h : Expression.evalBool σ c = false) :
      Step ⟨.whileLoop c body, σ⟩ ⟨.skip, σ⟩
  | assign (x : Fin vars) (rhs : Expression vars .int) (σ : List.Vector Int vars) :
      Step ⟨.assign x rhs, σ⟩ ⟨.skip, σ.set x (Expression.evalInt σ rhs)⟩
  | seq_left (s₁ s₂ s₁' : Statement vars) (σ σ' : List.Vector Int vars)
      (h₁ : s₁ ≠ .skip)
      (h : Step ⟨s₁, σ⟩ ⟨s₁', σ'⟩) :
      Step ⟨.sequence s₁ s₂, σ⟩ ⟨.sequence s₁' s₂, σ'⟩
  | seq_skip (s₂ : Statement vars) (σ : List.Vector Int vars) :
      Step ⟨.sequence .skip s₂, σ⟩ ⟨s₂, σ⟩
 | skip_loop (σ : List.Vector Int vars) :
      Step ⟨ .skip, σ⟩ ⟨ .skip, σ⟩

-- theorem Step.not_from_skip {vars : Nat} (σ : List.Vector Int vars) (s' : ProgramState vars) :
--     ¬ Step ⟨.skip, σ⟩ s' := by
--   intro h
--   cases h

/--
Compile a statement to a Büchi automaton whose (fair) runs correspond to infinite executions.

All states are fair (`F := true`), so fair-emptiness is equivalent to the absence of runs, i.e.
to the program halting (for all initial valuations) in this model.
-/
def StatementToAutomaton {vars : Nat} (statement : Statement vars) : Automaton (ProgramState vars) where
  R := fun s₁ s₂ => Step s₁ s₂
  I := fun s => decide (s.currentStatement = statement)
  F := fun ⟨ p, _vars ⟩  => p ≠ .skip
