import Mathlib.Data.Nat.Count
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Nth
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.OrderIsoNat

structure Automaton (S : Type) : Type where
  R : S → S → Bool
  I : S → Bool
  F : S → Bool

structure Run {S : Type} (A : Automaton S) : Type where
  f : Nat → S
  IsInitialized : A.I (f 0)
  IsValid : ∀ (n : Nat), A.R (f n) (f n.succ)

variable {S : Type} {a : Automaton S} (r : Run a)

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
  C4 : ∀ (s1 s2 : S), A.R s1 s2 → V s2 + (if A.F s1 then 1 else 0) ≤ V s1

variable (V : RankingFunction a)

@[simp, reducible]
def fairVisits : Set ℕ := { n : Nat | a.F (r.f n) }

@[simp, reducible]
def fairCount : Nat → Nat := Nat.count (fun m => a.F (r.f m))

noncomputable def nth_visit (n : Nat) : Nat := Nat.nth (fun m => a.F (r.f m)) n

lemma count_remaining (y : Nat) : V.V (r.f y) + fairCount r y ≤ V.V (r.f 0) := by
  induction' y with i ih
  · simp only [Nat.count_zero, add_zero, le_refl]
  · simp only [Nat.count_succ, fairCount] at *
    have n : V.V (r.f (i + 1)) + (if a.F (r.f i) then 1 else 0) ≤ V.V (r.f i) := V.C4 (r.f i) (r.f (i + 1)) (r.IsValid i)
    omega

lemma count_bounded (y : Nat) : fairCount r y ≤ V.V (r.f 0) := by
  have := count_remaining r V y
  omega

lemma count_nth (inf : Set.Infinite (fairVisits r)) (y : Nat) : fairCount r (nth_visit r y) = y := Nat.count_nth (by
    intro hf
    contradiction)

lemma count_finite {p : Nat → Prop} [DecidablePred p] {x : Nat} (f : (n : Nat) → Nat.count p n ≤ x) : Set.Finite (setOf p) := by
  by_contra c
  have y := f (Nat.nth p (x + 1))
  simp only [Nat.count_nth_of_infinite c (x + 1), add_le_iff_nonpos_right, nonpos_iff_eq_zero,
    one_ne_zero] at y

lemma fair_visits_finite (V : RankingFunction a) : Set.Finite (fairVisits r) := count_finite (count_bounded r V)

lemma ranking_function_zero (inf : Set.Infinite (fairVisits r)) : V.V (r.f (nth_visit r (V.V (r.f 0)))) = 0 := by
  have x1 := count_remaining r V (nth_visit r (V.V (r.f 0)))
  simp only [count_nth r inf (V.V (r.f 0)), add_le_iff_nonpos_left, nonpos_iff_eq_zero] at x1
  exact x1

@[simp, reducible]
noncomputable def fairVisits2 (V : RankingFunction a) : Finset ℕ := Set.Finite.toFinset (fair_visits_finite r V)

theorem Soundness (V : RankingFunction a) : a.IsFairEmpty :=  by
  intro r
  by_contra r_fair
  by_cases empty : (fairVisits2 r V) = ∅
  · simp only [Set.Finite.toFinset_eq_empty] at empty
    rcases (r_fair 0) with ⟨x, _, x_fair⟩
    have x_mem_s : x ∈ fairVisits r := by
      simp only [Set.mem_setOf_eq, x_fair]
    simp only [empty, Set.mem_empty_iff_false] at x_mem_s
  · rcases r_fair (Finset.max' (fairVisits2 r V) (Finset.nonempty_of_ne_empty empty)) with ⟨x, x_gt_max, x_fair⟩
    simp only [Finset.max'_lt_iff, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at x_gt_max
    have x_lt_x : x < x := x_gt_max x x_fair
    omega

theorem Soundness2 (V : RankingFunction a) : a.IsFairEmpty :=  by
  intro r
  by_contra r_fair
  have empty : fairVisits2 r V ≠ ∅ := by
    intro e
    simp only [Set.Finite.toFinset_eq_empty] at e
    rcases (r_fair 0) with ⟨x, _, x_fair⟩
    apply Set.notMem_empty x
    simp only [← e, fairVisits, Set.mem_setOf_eq, x_fair]
  rcases r_fair (Finset.max' (fairVisits2 r V) (Finset.nonempty_of_ne_empty empty)) with ⟨x, x_gt_max, x_fair⟩
  simp only [Finset.max'_lt_iff, Set.Finite.mem_toFinset] at x_gt_max
  have x_lt_x : x < x := x_gt_max x x_fair
  omega

universe u

structure OrdinalRankingFunction {S : Type} (A : Automaton S) : Type (u + 1) where
  V : S → Ordinal.{u}
  C4 : ∀ (s1 s2 : S), A.R s1 s2 → V s2 + (if A.F s1 then 1 else 0) ≤ V s1

variable (W : OrdinalRankingFunction a)

noncomputable def OrdSeq (n : Nat) : Ordinal := W.V (r.f (nth_visit r n))

theorem fair_infinite (r_fair : r.IsFair) : Set.Infinite (fairVisits r) := by
  simp only [Set.infinite_iff_exists_gt, Set.mem_setOf_eq]
  intro a
  rcases (r_fair a) with ⟨k, k_gt_a, k_fair⟩
  exact ⟨k, ⟨k_fair, by omega⟩⟩

theorem nth_visit_fair (n : Nat) (r_fair : r.IsFair) : a.F (r.f (nth_visit r n)) := Nat.nth_mem_of_infinite (fair_infinite r r_fair) n

theorem Ord_antitone : Antitone (fun n => W.V (r.f n)) := antitone_nat_of_succ_le (fun n => by
  have c := W.C4 (r.f n) (r.f (n + 1)) (r.IsValid n)
  by_cases is_fair : a.F (r.f n)
  <;> simp only [is_fair, ↓reduceIte, Ordinal.add_one_eq_succ, Order.succ_le_iff, Bool.false_eq_true, add_zero] at c
  · exact LT.lt.le c
  · exact c)

theorem nth_succ (r_fair : r.IsFair) (n : ℕ) : OrdSeq r W (n + 1) < OrdSeq r W n := by
  have : nth_visit r n < nth_visit r (n + 1) :=  @Nat.nth_strictMono (fun (x : Nat) => a.F (r.f x)) (fair_infinite r r_fair) n (n + 1) (by omega)
  have y := W.C4 (r.f (nth_visit r n)) (r.f (nth_visit r (n) + 1)) (r.IsValid (nth_visit r n))
  simp only [nth_visit_fair r n r_fair, ↓reduceIte, Ordinal.add_one_eq_succ,
    Order.succ_le_iff] at y
  exact LE.le.trans_lt (by
    apply Ord_antitone
    omega) y

theorem ranking_mono (r_fair : r.IsFair) {m n : ℕ} : OrdSeq r W m < OrdSeq r W n ↔ n < m := StrictAnti.lt_iff_lt (strictAnti_nat_of_succ_lt (nth_succ r W r_fair))

theorem Soundness3 (W : OrdinalRankingFunction.{u} a) : a.IsFairEmpty := fun r r_fair =>
  (RelEmbedding.not_wellFounded_of_decreasing_seq ⟨⟨OrdSeq r W,
      StrictAnti.injective (strictAnti_nat_of_succ_lt (nth_succ r W r_fair))
      ⟩, by
        intros m n
        simp only [Function.Embedding.coeFn_mk, gt_iff_lt]
        exact ranking_mono r W r_fair⟩) (Ordinal.wellFoundedLT.{u}.wf)
