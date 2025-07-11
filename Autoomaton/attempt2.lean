import Mathlib.Data.Nat.Count
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Nth


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
  C4 : ∀ (s1 s2 : S), A.R s1 s2 → V s2 + (if A.F s1 then 1 else 0) ≤ V s1

variable (V : RankingFunction a)

@[simp, reducible]
def fairVisits : Set ℕ := { n : Nat | a.F (r.f n) }

noncomputable def nth_visit (n : Nat) : Nat := Nat.nth (fun m => a.F (r.f m)) n

lemma BoundedFairVisits36 : nth_visit a r (V.V (r.f 0)) ∈ upperBounds (fairVisits a r) := by
  simp [BddAbove, upperBounds, Nonempty]
  intros x x_fair
  simp [nth_visit]
  sorry

lemma BoundedFairVisits38 (y : Nat) : V.V (r.f y) + Nat.count (fun m => a.F (r.f m)) y ≤ V.V (r.f 0)  := by
  induction' y with i ih
  · simp only [Nat.count_zero, add_zero, le_refl]
  · simp only [Nat.count_succ]
    have n : V.V (r.f (i + 1)) + (if a.F (r.f i) then 1 else 0) ≤ V.V (r.f i) := V.C4 (r.f i) (r.f (i + 1)) (r.IsValid i)
    omega

lemma BoundedFairVisits39 (inf : Set.Infinite (fairVisits a r)) (y : Nat) :  Nat.count (fun m => a.F (r.f m)) (nth_visit a r y) = y := by
  exact Nat.count_nth (by
    intro hf
    contradiction)

lemma BoundedFairVisits310 (inf : Set.Infinite (fairVisits a r)) : V.V (r.f (nth_visit a r (V.V (r.f 0)))) = 0  := by
  have x1 := BoundedFairVisits38 a r V (nth_visit a r (V.V (r.f 0)))
  simp only [BoundedFairVisits39 a r inf (V.V (r.f 0)), add_le_iff_nonpos_left, nonpos_iff_eq_zero] at x1
  exact x1

lemma BoundedFairVisits3 (V : RankingFunction a) :  Set.Finite (fairVisits a r) := by
  have y :  BddAbove (fairVisits a r) := by
    apply (Set.nonempty_of_mem)
    exact BoundedFairVisits36 a r V
  exact BddAbove.finite y

@[simp, reducible]
noncomputable def fairVisits2 (V : RankingFunction a) : Finset ℕ :=  Set.Finite.toFinset (BoundedFairVisits3 a r V)

theorem Soundness (V : RankingFunction a) : a.IsFairEmpty :=  by
  intros r
  by_contra r_fair
  by_cases empty : (fairVisits2 a r V) = ∅
  simp only [Set.Finite.toFinset_eq_empty] at empty
  rcases (r_fair 0) with ⟨x, x_gt_0, x_fair⟩
  · have x_mem_s : x ∈ fairVisits a r := by
      simp only [Set.mem_setOf_eq, x_fair]
    simp only [empty, Set.mem_empty_iff_false] at x_mem_s
  · rcases r_fair (Finset.max' (fairVisits2 a r V) (Finset.nonempty_of_ne_empty empty)) with ⟨x, x_gt_max, x_fair⟩
    simp only [Finset.max'_lt_iff, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at x_gt_max
    have x_lt_x : x < x := x_gt_max x x_fair
    omega
