import Mathlib.Data.Set.Basic
-- import Mathlib.SetTheory.Ordinal.Basic

structure DFSA (S : Type) (A : Type) : Type where
  initial : S
  transition : A  → S → S
  accepts : S → Bool

structure RecursiveBuchi (S : Type) (A : Type) : Type where
  S0 : S → Bool
  α : A → S → S → Bool
  F : S → Bool

structure Run {S A : Type} (B : RecursiveBuchi S A) (w : Nat → A) : Type where
  run : Nat → S
  init : B.S0 (run 0)
  next: ∀ (n : Nat), B.α (w n) (run n) (run n.succ)
  infinite: ∀(n : Nat), ∃ (m : Nat), m > n ∧ B.F (run m)



-- def BuchiAccepts {S A : Type} (B : RecursiveBuchi S A) (w : Nat → A) : Prop :=
--   ∃ (r : Run B w),



def accepts {S A : Type} (D : DFSA S A) (w : List A) : Bool := D.accepts (w.foldr D.transition D.initial)


structure Program (W : Type) : Type where
  I : W → Prop
  R : W → W → Prop

structure Computation {W : Type} (p : Program W) : Type where
  σ : Nat → W
  init :  p.I (σ 0)
  next : ∀ (x : Nat), p.R (σ x) (σ (x + 1))

def IsCorrect {W : Type} {p : Program W} (φ ψ : Computation p → Prop): Prop := ∀ (c : Computation p), φ c → ψ c
