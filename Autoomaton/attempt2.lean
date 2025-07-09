import Mathlib.Data.Nat.Count
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Max

structure Automaton (S : Type) : Type where
  R : S → S → Bool
  I : S → Bool
  F : S → Bool

structure Run {S : Type} (A : Automaton S) : Type where
  f : Nat → S
  IsInitialized :  A.I (f 0)
  IsValid : ∀ (n : Nat), A.R (f n) (f n.succ)

variable {S : Type} (a : Automaton S) (r : Run a)

@[simp, reducible]
def Run.IsFair : Prop := ∀ (n : Nat), ∃ (k : Nat), k > n ∧ a.F (r.f k)

@[simp, reducible]
def Run.IsUnfair : Prop := ¬ r.IsFair

@[simp, reducible]
def Run.IsFairEmpty : Prop := r.IsUnfair

@[simp, reducible]
def Automaton.IsFairEmpty : Prop := ∀ (r : Run a), r.IsFairEmpty

structure RankingFunction {S : Type} (A : Automaton S) : Type where
  V : S → Nat
  C1 : ∀ (s : S), A.F s → ∀ (s' : S), A.R s s' → V s' < V s
  C2 : ∀ (s : S), ¬ A.F s → ∀ (s' : S), A.R s s' → V s' ≤ V s

@[simp, reducible]
def fairVisits : Set ℕ := { n : Nat | a.F (r.f n) }

lemma BoundedFairVisits2 (V : RankingFunction a) (r : Run a) :  Set.encard (fairVisits a r) < V.V (r.f 0) := by
  simp [fairVisits]
  sorry

lemma BoundedFairVisits3 (V : RankingFunction a) (r : Run a)  :  Set.Finite (fairVisits a r) := by
  sorry

lemma BoundedFairVisits4 (V : RankingFunction a) (r : Run a) (n : Nat) :  Set.encard { m : Nat | a.F (r.f (m + n)) } < V.V (r.f n) := by
  sorry

@[simp, reducible]
noncomputable def fairVisits2 (V : RankingFunction a) : Finset ℕ :=  Set.Finite.toFinset (BoundedFairVisits3 a V r)

theorem Soundness (V : RankingFunction a) : a.IsFairEmpty :=  by
  intros r
  by_contra c
  by_cases empty : (fairVisits2 a r V) = ∅
  simp only [Set.Finite.toFinset_eq_empty] at empty
  rcases (c 0) with ⟨x, y, z⟩
  · have x_mem_s : x ∈ {n | a.F (r.f n) } := by
      simp only [Set.mem_setOf_eq, z]
    simp only [empty, Set.mem_empty_iff_false] at x_mem_s
  · rcases c (Finset.max' (fairVisits2 a r V) (Finset.nonempty_of_ne_empty empty)) with ⟨x, y, z⟩
    simp only [Finset.max'_lt_iff, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at y
    have : x < x := y x z
    omega
