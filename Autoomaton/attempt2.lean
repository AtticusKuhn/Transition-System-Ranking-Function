import Mathlib.Data.Nat.Count
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Nth
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.OrderIsoNat
import Mathlib.Computability.Ackermann
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.SetTheory.Ordinal.NaturalOps
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.SetTheory.Ordinal.Arithmetic

set_option pp.universes true in

/-- A Büchi automaton is a tuple $(S, R, I, F)$ where
- $S$ is a set of states.
- $R \subseteq S \times S$ is a transition relation.
- $I \subseteq S$ is a set of initial states.
- $F \subseteq S$ is a set of fair (or accepting) states.
-/
structure Automaton (S : Type) where
  /-- The transition relation $R \subseteq S \times S$. -/
  R : S → S → Prop
  /-- The set of initial states $I \subseteq S$. -/
  I : S → Bool
  /-- The set of fair (accepting) states $F \subseteq S$. -/
  F : S → Bool

/-- A run of a Büchi automaton is an infinite sequence of states $f : \mathbb{N} \to S$ such that
the first state is initial and all subsequent states are related by the transition relation. -/
structure Run {S : Type} (a : Automaton S) where
  /-- The infinite sequence of states $f : \mathbb{N} \to S$. -/
  f : Nat → S
  /-- The first state must be an initial state, i.e., $f(0) \in I$. -/
  is_init : a.I (f 0)
  /-- Each consecutive pair of states must be in the transition relation, i.e., $\forall n \in \mathbb{N}, (f(n), f(n+1)) \in R$. -/
  is_valid : ∀ n, a.R (f n) (f n.succ)

variable {S : Type} {a : Automaton S} (r : Run a)

/-- A run `r` is fair if it visits the set of fair states infinitely often.
This is expressed as $\forall n \in \mathbb{N}, \exists k > n, f(k) \in F$. -/
@[simp]
def Run.IsFair : Prop := ∀ (n : Nat), ∃ (k : Nat), k > n ∧ a.F (r.f k)

/-- A run `r` is unfair if it is not fair. -/
@[simp]
def Run.IsUnfair : Prop := ¬ r.IsFair

/-- A run is "fair-empty" if it is unfair. This definition is part of establishing that if a ranking function exists, then no fair run exists. -/
@[simp]
def Run.IsFairEmpty : Prop := r.IsUnfair

/-- An automaton is "fair-empty" if all its runs are unfair.
This means the automaton has no fair runs. -/
@[simp]
def Automaton.IsFairEmpty : Prop := ∀ (r : Run a), r.IsFairEmpty

/-- A ranking function for a Büchi automaton maps states to natural numbers.
The rank must not increase along transitions. If the source state of a transition is fair, the rank must strictly decrease.
This is a witness for the emptiness of fair runs for an automaton.
-/
structure RankingFunction {S : Type} (a : Automaton S) where
  /-- The ranking function $V: S \to \mathbb{N}$. -/
  (rank : S → Nat)
  /-- The condition on the ranking function: for all transitions $(s_1, s_2) \in R$,
  $V(s_2) + \mathbb{I}(s_1 \in F) \le V(s_1)$, where $\mathbb{I}$ is the indicator function. -/
  (rank_le_of_rel : ∀ s1 s2, a.R s1 s2 → rank s2 + (if a.F s1 then 1 else 0) ≤ rank s1)

variable (V : RankingFunction a)

/-- The set of natural numbers `n` for which the state `r.f n` is a fair state.
This represents the time indices at which a run `r` visits a fair state.
Formally, $\{n \in \mathbb{N} \mid r.f(n) \in F\}$. -/
@[simp]
def fairVisits : Set ℕ := { n : Nat | a.F (r.f n) }

/-- `fairCount r n` counts the number of visits to fair states up to time `n-1`.
Formally, $|\{m < n \mid r.f(m) \in F\}|$. -/
@[simp]
def fairCount : Nat → Nat := Nat.count (fun m => a.F (r.f m))

/-- `nth_visit r n` gives the time of the `n`-th visit to a fair state.
This is defined using `Nat.nth`, which finds the `n`-th number satisfying a predicate. -/
noncomputable def nth_visit (n : Nat) : Nat := Nat.nth (fun m => a.F (r.f m)) n

/-- For any run `r` and any time `y`, the rank of the state at time `y` plus the number of fair visits up to time `y`
is less than or equal to the rank of the initial state.
$V(r.f(y)) + |\{m < y \mid r.f(m) \in F\}| \le V(r.f(0))$. -/
lemma rank_plus_fairCount_le_rank_zero (y : Nat) : V.rank (r.f y) + fairCount r y ≤ V.rank (r.f 0) := by
  induction' y with i ih
  · simp only [fairCount, Nat.count_zero, add_zero, le_refl]
  · simp only [Nat.count_succ, fairCount] at *
    have : V.rank (r.f (i + 1)) + (if a.F (r.f i) then 1 else 0) ≤ V.rank (r.f i) := V.rank_le_of_rel (r.f i) (r.f (i + 1)) (r.is_valid i)
    omega

/-- The number of fair visits up to any time `y` is bounded by the rank of the initial state.
$|\{m < y \mid r.f(m) \in F\}| \le V(r.f(0))$. -/
lemma fairCount_le_initial_rank (y : Nat) : fairCount r y ≤ V.rank (r.f 0) := by
  have := rank_plus_fairCount_le_rank_zero r V y
  omega

/-- If the set of fair visits is infinite, then the number of fair visits up to the `y`-th fair visit is `y`.
This is a property of `Nat.count` and `Nat.nth`. -/
lemma count_nth (inf : Set.Infinite (fairVisits r)) (y : Nat) : fairCount r (nth_visit r y) = y := Nat.count_nth (by
    intro hf
    contradiction)

/-- If the count of elements satisfying a predicate `p` is bounded by some `x`, then the set of such elements is finite.
This is a general lemma about `Nat.count`. -/
lemma count_finite {p : Nat → Prop} [DecidablePred p] {x : Nat} (f : (n : Nat) → Nat.count p n ≤ x) : Set.Finite (setOf p) := by
  by_contra c
  have y := f (Nat.nth p (x + 1))
  simp only [Nat.count_nth_of_infinite c (x + 1), add_le_iff_nonpos_right, nonpos_iff_eq_zero,
    one_ne_zero] at y

/-- If there exists a ranking function `V`, then for any run `r`, the set of fair visits must be finite. -/
lemma fair_visits_finite (V : RankingFunction a) : Set.Finite (fairVisits r) := count_finite (fairCount_le_initial_rank r V)

/-- If the set of fair visits is infinite, then the rank at the `V(r.f(0))`-th fair visit must be 0. -/
lemma rank_at_nth_visit_eq_zero (inf : Set.Infinite (fairVisits r)) : V.rank (r.f (nth_visit r (V.rank (r.f 0)))) = 0 := by
  have x1 := rank_plus_fairCount_le_rank_zero r V (nth_visit r (V.rank (r.f 0)))
  simp only [count_nth r inf (V.rank (r.f 0)), add_le_iff_nonpos_left, nonpos_iff_eq_zero] at x1
  exact x1

/-- The finite set of fair visits, which is well-defined if a ranking function `V` exists. -/
@[simp]
noncomputable def fairVisitsFinset (V : RankingFunction a) : Finset ℕ := Set.Finite.toFinset (fair_visits_finite r V)

/-- The main theorem for natural-valued ranking functions.
If a ranking function `V` exists for an automaton `a`, then `a` has no fair runs. -/
theorem isFairEmpty_of_rankingFunction (V : RankingFunction a) : a.IsFairEmpty :=  by
  intro r
  by_contra r_fair
  simp only [Run.IsFairEmpty, Run.IsUnfair, Run.IsFair, gt_iff_lt, not_forall, not_exists, not_and,
    Bool.not_eq_true, Classical.not_imp, Bool.not_eq_false] at r_fair
  by_cases empty : (fairVisitsFinset r V) = ∅
  · simp only [Set.Finite.toFinset_eq_empty, fairVisitsFinset] at empty
    rcases (r_fair 0) with ⟨x, _, x_fair⟩
    have x_mem_s : x ∈ fairVisits r := by
      exact x_fair
    simp only [empty, Set.mem_empty_iff_false] at x_mem_s
  · rcases r_fair (Finset.max' (fairVisitsFinset r V) (Finset.nonempty_of_ne_empty empty)) with ⟨x, x_gt_max, x_fair⟩
    simp only [fairVisitsFinset, fairVisits, Finset.max'_lt_iff, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq] at x_gt_max
    have x_lt_x : x < x := x_gt_max x x_fair
    omega

universe u

/-- An ordinal-valued ranking function for a Büchi automaton maps states to ordinals.
The rank must not increase along transitions. If the source state of a transition is fair, the rank must strictly decrease.
This is a more general form of a ranking function.
-/
structure OrdinalRankingFunction {S : Type} (a : Automaton S) : Type (u + 1) where
  /-- The ranking function $W: S \to \text{Ordinal}$. -/
  rank : S → Ordinal.{u}
  /-- The condition on the ranking function: for all transitions $(s_1, s_2) \in R$,
  $W(s_2) + \mathbb{I}(s_1 \in F) \le W(s_1)$, where $\mathbb{I}$ is the indicator function. -/
  rank_le_of_rel_fair : ∀ s1 s2, a.R s1 s2 → a.F s1  → rank s2 < rank s1
  rank_le_of_rel_unfair : ∀ s1 s2, a.R s1 s2 → rank s2 ≤ rank s1

variable (W : OrdinalRankingFunction a)

/-- The sequence of ranks at the times of fair visits.
`ordSeq r W n` is the rank of the state at the `n`-th fair visit, i.e., $W(r.f(\text{nth_visit}(r, n)))$. -/
noncomputable def ordSeq (n : Nat) : Ordinal := W.rank (r.f (nth_visit r n))

/-- If a run `r` is fair, then the set of its fair visits is infinite. This is a direct consequence of the definition of a fair run. -/
theorem fair_infinite (r_fair : r.IsFair) : Set.Infinite (fairVisits r) := by
  simp only [Set.infinite_iff_exists_gt, Set.mem_setOf_eq]
  intro a
  rcases (r_fair a) with ⟨k, k_gt_a, k_fair⟩
  exact ⟨k, ⟨k_fair, by omega⟩⟩

/-- If a run `r` is fair, then the state at the `n`-th fair visit is indeed a fair state.
$r.f(\text{nth_visit}(r, n)) \in F$. -/
theorem is_fair_at_nth_visit (n : Nat) (r_fair : r.IsFair) : a.F (r.f (nth_visit r n)) := Nat.nth_mem_of_infinite (fair_infinite r r_fair) n

/-- The sequence of ranks along a run is antitone (non-increasing).
The function $n \mapsto W(r.f(n))$ is an antitone function from $\mathbb{N}$ to the ordinals. -/
theorem rank_antitone : Antitone (fun n => W.rank (r.f n)) := antitone_nat_of_succ_le (fun n => by
  have cf := W.rank_le_of_rel_fair (r.f n) (r.f (n + 1)) (r.is_valid n)
  have cu := W.rank_le_of_rel_unfair (r.f n) (r.f (n + 1)) (r.is_valid n)
  by_cases is_fair : a.F (r.f n)
  <;> simp only [is_fair, ↓reduceIte, Ordinal.add_one_eq_succ, Order.succ_le_iff, Bool.false_eq_true, add_zero] at cf
  · exact LT.lt.le (W.rank_le_of_rel_fair (r.f n) (r.f (n + 1)) (r.is_valid n) is_fair)
  · exact cu)

/-- For a fair run, the sequence of ranks at fair visits is strictly decreasing.
$W(r.f(\text{nth_visit}(r, n+1))) < W(r.f(\text{nth_visit}(r, n)))$. -/
theorem ordSeq_strict_anti (r_fair : r.IsFair) : StrictAnti (ordSeq r W) := strictAnti_nat_of_succ_lt (fun n => by
  have : nth_visit r n < nth_visit r (n + 1) :=  @Nat.nth_strictMono (fun (x : Nat) => a.F (r.f x)) (fair_infinite r r_fair) n (n + 1) (by omega)
  have yf := W.rank_le_of_rel_fair (r.f (nth_visit r n)) (r.f (nth_visit r (n) + 1)) (r.is_valid (nth_visit r n)) (is_fair_at_nth_visit r n r_fair)
  have yu := W.rank_le_of_rel_unfair (r.f (nth_visit r n)) (r.f (nth_visit r (n) + 1)) (r.is_valid (nth_visit r n))

  simp only [is_fair_at_nth_visit r n r_fair, ↓reduceIte, Ordinal.add_one_eq_succ,
    Order.succ_le_iff] at yf
  exact LE.le.trans_lt (by
    apply rank_antitone
    omega) yf)

/-- The comparison of ranks in the `ordSeq` is equivalent to the reversed comparison of their indices.
This is a property of strictly antitone sequences.
For $m, n \in \mathbb{N}$, $W(r.f(\text{nth_visit}(r, m))) < W(r.f(\text{nth_visit}(r, n))) \iff n < m$. -/
theorem ordSeq_lt_iff_lt (r_fair : r.IsFair) {m n : ℕ} : ordSeq r W m < ordSeq r W n ↔ n < m := StrictAnti.lt_iff_lt (ordSeq_strict_anti r W r_fair)

def stateSucceeds {S : Type} (a : Automaton S) (s2 s1 : S) : Prop :=
  ∃ (f : S),
  Relation.ReflTransGen a.R s1 f
  ∧ a.F f
  ∧ Relation.TransGen a.R f s2
  -- ∧ f ≠ s1
  -- ∃ (r : Run a), ∃ (i j k : Nat), i ≤ j ∧ j < k ∧ s1 = r.f i ∧ s2 = r.f k ∧ a.F (r.f j)
-- theorem suceeds_trans {S : Type} (a : Automaton S) {s1 s2 s3: S} (suc1 : suceeds a s1 s2) (suc2 : suceeds a s2 s3) : suceeds a s2 s3 := by
--   rcases suc1 with ⟨ r1, i1, j1, k1, c1⟩
--   rcases suc2 with ⟨ r2, i2, j2, k2, c2 ⟩
--   exact ⟨⟨ fun n => if n < k1 then r1.f n else r2.f n, by
--     simp
--     sorry, sorry⟩ , by
--       simp

--       sorry ⟩

-- theorem succeeds_wf_2 (a : Automaton S)   (fe : a.IsFairEmpty) : WellFounded (suceeds a) :=
-- s1_r_s2 : a.R s1 s2
-- s : Ordinal.{0}
-- n : S
-- n_suc_s2 : stateSucceeds a n s2
-- ord_suc : Order.succ (IsWellFounded.rank (stateSucceeds a) n) = s
-- ⊢ stateSucceeds a n s1

theorem succeeds_concat { S : Type} (s1 s2 n : S)  (a : Automaton S)  (s1_r_s2 : a.R s1 s2) (n_suc_s2 : stateSucceeds a n s2) : stateSucceeds a n s1 := by
  rcases n_suc_s2 with ⟨ f, rt, f_fair, tg ⟩
  use f
  simp [f_fair, tg]
  rw [Relation.ReflTransGen.cases_head_iff]
  right
  use s2

theorem succeeds_wf (a : Automaton S) (fe : a.IsFairEmpty) : WellFounded (stateSucceeds a) := by
  -- simp [IsWellFounded]
  -- suggest
  -- suggest_hint
  simp [WellFounded.wellFounded_iff_no_descending_seq]
  by_contra c
  simp at c
  simp at fe

  rcases c with ⟨ s, y⟩
  simp [stateSucceeds] at y

  -- have rn : Run a := ⟨fun n => (Exists.choose (y n)).1 n
  --   ,  (Exists.choose (y 0)).2

  --    , sorry⟩
  -- have := fe rn
  sorry

instance n {S  : Type } (a : Automaton S) (fe : a.IsFairEmpty) : IsWellFounded S (stateSucceeds a) where
  wf := succeeds_wf a fe

/-- The main theorem for ordinal-valued ranking functions.
If an ordinal-valued ranking function `W` exists for an automaton `a`, then `a` has no fair runs.
This is proven by showing that a fair run would imply an infinite decreasing sequence of ordinals, which is impossible. -/
theorem isFairEmpty_of_ordinalRankingFunction (W : OrdinalRankingFunction.{0} a) : a.IsFairEmpty := fun r r_fair =>
  (RelEmbedding.not_wellFounded_of_decreasing_seq ⟨⟨ordSeq r W,
      StrictAnti.injective (ordSeq_strict_anti r W r_fair)
      ⟩, by
        intros m n
        simp only [Function.Embedding.coeFn_mk, gt_iff_lt]
        exact ordSeq_lt_iff_lt r W r_fair⟩) (Ordinal.wellFoundedLT.{0}.wf)



noncomputable def completeness (fe : a.IsFairEmpty) : OrdinalRankingFunction.{0} a := ⟨@IsWellFounded.rank S (stateSucceeds a) (n a fe), fun s1 s2  rel => by
    intro s1_fair
    apply IsWellFounded.rank_lt_of_rel (hwf := n a fe)
    use s1
    rw [Relation.ReflTransGen.cases_tail_iff]
    rw [Relation.transGen_iff]
    simp only [s1_fair, true_and, true_or, rel, and_self],
    by
    intros s1 s2 s1_r_s2
    by_contra c
    simp only [not_le] at c
    rw [IsWellFounded.rank_eq] at c
    rw [IsWellFounded.rank_eq] at c
    have :  sSup (Set.range fun (b : { b // stateSucceeds a b s2 }) ↦ Order.succ (IsWellFounded.rank (hwf := n a fe) (stateSucceeds a) ↑b)) ≤ sSup (Set.range fun (b : { b // stateSucceeds a b s1 }) ↦ Order.succ (IsWellFounded.rank (hwf := n a fe) (stateSucceeds a) ↑b)) := csSup_le_csSup (by
      simp [BddAbove, upperBounds, Set.Nonempty]
      use IsWellFounded.rank (hwf := n a fe) (stateSucceeds a) s1
      intros s3 s3_suc_s1
      exact IsWellFounded.rank_lt_of_rel (hwf := n a fe) s3_suc_s1)
      (by
        by_cases n : (∃ (f : S), stateSucceeds a f s2 )
        · rcases n with  ⟨f, f_suc_s2 ⟩
          have nonempt : Nonempty { b // stateSucceeds a b s2 } := by
            use f
          apply Set.range_nonempty (h := nonempt)
        · simp only [not_exists] at n
          have : IsEmpty { b // stateSucceeds a b s2 } := ⟨ fun ⟨ a, a_succ ⟩  => n a a_succ⟩
          simp only [ciSup_of_empty, Ordinal.bot_eq_zero] at c
          simp only [Ordinal.not_lt_zero] at c
          )
      (by
        intro s s_in_b
        simp only [Set.mem_range, Subtype.exists, exists_prop] at s_in_b
        rcases s_in_b with ⟨ n, n_suc_s2, ord_suc⟩
        simp
        use n
        simp only [ord_suc, and_true]
        exact succeeds_concat s1 s2 n a s1_r_s2 n_suc_s2
        )
    have := LT.lt.not_ge c
    contradiction
    ⟩

#print axioms completeness

def ackStep (p : (Nat × List Nat)) : (Nat × List Nat) :=
  match p with
  | (n, []) => (n, [])
  | (n, 0 :: c) => ((n + 1), c)
  | (0, (m + 1) :: c) =>  (1, m :: c)
  | (n + 1, (m + 1) :: c) => (n, (m + 1) :: m :: c)

-- def ackMax (p : Nat × List Nat) :  Nat  := match p with
--   | (x, []) => x
--   | (x, y :: ys) => ackMax (ack x y, ys)

def ackMax2 (x : Nat) (y : List Nat) :  Nat  := match y with
  | [] => x
  | y :: ys => ackMax2 (ack y x) ys




theorem ack_gt_4 (m a b: Nat) (le : a ≤ b): ack m a ≤ ack m b :=
  match m with
    | 0 => by
      simp only [ack_zero, add_le_add_iff_right, le]
    | m + 1 => by
      simp only [ack_le_iff_right, le]

def ack_gt_2 (m n: Nat) (le : 1 ≤ m) : m + n ≤ ack m n :=
  match m, n with
    | 0, n => by
      simp only [zero_add, ack_zero, le_add_iff_nonneg_right, zero_le]
    | m + 1, 0 => by
      simp only [add_zero, ack_succ_zero]
      match (Nat.decEq m 0) with
        | isTrue h =>  simp only [h, zero_add, ack_zero, Nat.reduceAdd, Nat.one_le_ofNat]
        | isFalse _ => exact ack_gt_2 m 1 (by omega);
    | m + 1, n + 1 =>
      match (Nat.decEq m 0) with
        | isTrue h => by
          simp only [h, zero_add, ack_succ_succ, ack_one, ack_zero]
          omega
        | isFalse _ => by
          have := ack_gt_2 m (m + 1 + n) (by omega);
          have := ack_gt_4 m (m + 1 + n) (ack (m + 1) n) (ack_gt_2 (m + 1) n le);
          simp only [ack_succ_succ, ge_iff_le]
          omega
termination_by (m, n)

#print axioms ack_gt_2

def ack_gt_5 (m n: Nat) : m + n ≤ ack m n := by
  by_cases h : m = 0
  simp only [h, zero_add, ack_zero, le_add_iff_nonneg_right, zero_le]
  have := ack_gt_2 m n (by omega)
  omega

theorem ack_gt_1 (m n: Nat) : n ≤ ack m n := by
  have := ack_gt_5 m n
  omega

theorem ackMax2_gt (x : Nat) (y : List Nat)  : x ≤ ackMax2 x y :=
  match y with
    | [] => by simp only [ackMax2, le_refl]
    | y :: ys => by
      simp only [ackMax2]
      have := ack_gt_1 y x
      have := ackMax2_gt (ack y x) ys
      omega

-- theorem ack_gt (n m: Nat) : ack m n ≥ n :=
--   match m, n with
--     | 0, n => by
--       simp
--     | m + 1, 0 => by
--       simp
--     | m + 1, n + 1 => by
--       simp [ack]
--       sorry

-- theorem ackMax_gt (n : Nat) (l  : List Nat) : ackMax2 n l ≥ n :=
--   match l with
--     | [] => by simp only [ackMax2, ge_iff_le, le_refl]
--     | y :: ys => by
--       simp [ackMax2]
--       have re := ackMax_gt (ack y n) ys

--       sorry

def ackMax (p : Nat × List Nat) : Nat := match p with
  | (x, ys) => ackMax2 x ys

def AckSystem : Automaton (Nat × List Nat) where
  R := fun a b => b = ackStep a
  I := fun ⟨_, y⟩  => y.length = 1
  F := fun ⟨_, y⟩ => y ≠ []

-- def ackRankf (p : Nat × List Nat) : Ordinal :=
--   match p with
--   | ⟨ x,  y⟩ => let m : Nat := ackMax (x, y)
--   (@y.foldrIdx Nat Ordinal (fun i b a => a + b * Ordinal.omega0 ^ (m - i)) Ordinal.zero.zero 0) + (m - x)
def ackRankf (p : Nat × List Nat) : Ordinal :=
  match p with
  | ⟨n, l⟩ =>
    let m : Nat := ackMax (n, l)
    let p : Ordinal := List.sum (@l.reverse.mapIdx Nat Ordinal (fun i a =>  a * Ordinal.omega0 ^ (m - i)))
    -- let p : OrdiniSupal := List.sum (@l.mapIdx Nat Ordinal (fun i a =>  a * Ordinal.omega0 ^ (m - l.length + 1 + i)))
    -- let p : Ordinal := @l.foldlIdx Ordinal Nat (fun i a b => b +  a * Ordinal.omega0 ^ (m - i)) (Ordinal.zero.zero) 0
    -- let p : Ordinal := @l.foldrIdx Nat Ordinal (fun i a b => b +  a * Ordinal.omega0 ^ (m - i)) (Ordinal.zero.zero) 0

    p + (m - n)


def test1 : Ordinal := ackRankf ⟨2, [2]⟩
def test2 : Nat := ackMax ⟨ 4, [1]⟩
def test3 : Nat := ackMax ⟨ 3, [2,1]⟩
def test4 : Nat := ackMax ⟨ 2, [2, 1, 1]⟩

-- ackMax2
-- #eval test2
-- #eval test3
-- #eval test4
#eval (ack 2 4)
#eval (ack 1 (ack 2 3))
#eval (ack 1 (ack 1 (ack 2 2)))
#eval (ackMax2 4 [2])
#eval (ackMax2 3 [2, 1])
-- #eval (ackRankf ⟨ 2, [2, 1, 1]⟩)

theorem t1 : ackRankf ⟨ 2, [2, 1, 1]⟩ = Ordinal.omega0^11 + Ordinal.omega0^10 + 2 * Ordinal.omega0^9 + 9  := by
  -- rfl
  simp [ackRankf, ackMax, ackMax2]
  -- rfl

  sorry
-- #reduce test1

-- theorem ord_lt (m : Ordinal.{0}) (t : Ordinal.{0}) : m - Order.succ t < m - t := by
--   sorry

universe v
theorem mapIdx_append {α : Type u} {β : Type v} {f : ℕ → α → β} {l : List α} {e r : α} : List.mapIdx f (l ++ [e, r]) = List.mapIdx f l ++ [f l.length e, f l.length.succ r] := by
    rw [List.append_cons]
    simp only [List.mapIdx_concat, List.length_append, List.length_cons, List.length_nil, zero_add,
      List.nil_append, Nat.succ_eq_add_one]
    simp

theorem f  { n  : Nat}: (Order.succ n : Ordinal.{0}) = (Nat.succ n) := by
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Ordinal.add_one_eq_succ]
theorem g  { m n  : Nat}: (m : Ordinal.{0}) - (n : Ordinal.{0}) = (Nat.cast (m - n)) := by
  simp
theorem h  { m n  : Nat}:  (n : Ordinal.{0}) < m ↔ n < m := by
  simp
theorem h2  { m n  : Nat}:  (n : Ordinal.{0}) ≤  m ↔ n ≤  m := by
  simp
theorem ord_cmp {a1 a2 b1 b2 : Nat} : (a1 * Ordinal.omega0  + b1 <  a2 * Ordinal.omega0  + b2) ↔ (a1 < a2 ∨ (a1 = a2 ∧ b1 < b2)) := by
  sorry
  -- sorry
noncomputable def ackRank : OrdinalRankingFunction.{0} AckSystem where
  rank := ackRankf

  rank_le_of_rel_fair := fun s1 s2 t =>
   match s1 with
      | (n, []) => by
        simp [AckSystem, ackRankf, ackStep] at t
        simp [t,AckSystem, ackRankf]
      | (n, 0 :: c) => by
        simp [AckSystem, ackRankf, ackStep] at t
        simp only [ackRankf, ackMax, t, List.mapIdx_reverse, Nat.cast_add, Nat.cast_one,
          Ordinal.add_one_eq_succ, AckSystem, ne_eq, decide_not, reduceCtorEq, decide_false,
          Bool.not_false, ↓reduceIte, ackMax2, ack_zero, List.reverse_cons, List.mapIdx_concat,
          Nat.cast_zero, List.length_reverse, zero_mul, List.sum_append, List.sum_cons,
          List.sum_nil, add_zero, add_lt_add_iff_left]
        simp
        rw [f]
        repeat rw [g]
        rw [h]
        simp [ackMax2]
        have f := ackMax2_gt (n + 1) c
        omega
      | (0, (m + 1) :: c) =>  by
        simp [AckSystem, ackRankf, ackStep] at t
        simp [ackRankf, ackMax, t, ackMax2, List.reverse_cons, List.mapIdx_concat,
          List.mapIdx_reverse, List.length_reverse, List.sum_append, List.sum_cons, List.sum_nil,
          add_zero, Nat.cast_one, AckSystem, ne_eq, decide_not, reduceCtorEq, decide_false,
          Bool.not_false, ↓reduceIte, Ordinal.add_one_eq_succ, ack_succ_zero, Nat.cast_add,
          Nat.cast_zero, Ordinal.sub_zero, Order.succ_le_iff]
        -- simp [​add_lt_add_iff_left]
        -- simp [add_lt_add_iff_left]
        -- let f: Ordinal.{0} := (List.mapIdx (fun i a ↦ ↑a * Ordinal.omega0 ^ (ackMax2 (ack m 1) c - (c.length - 1 - i))) c).reverse.sum
        -- have feq : (f = (List.mapIdx (fun i a ↦ ↑a * Ordinal.omega0 ^ (ackMax2 (ack m 1) c - (c.length - 1 - i))) c).reverse.sum)  := by rfl
        -- rw [← feq]
        repeat rw [add_assoc]
        simp
        rw [f]
        -- rw [@g (ackMax2 (n + 1) c) n.succ]
        repeat rw [g,f, h]
        -- rw [h]
        -- simp [ackMax2]
        -- apply add_lt_add_of_lt_of_le
        -- linarith
        -- omega
        sorry
      | (n + 1, (m + 1) :: c) => by
        simp [AckSystem, ackRankf, ackStep] at t
        simp [t,AckSystem, ackRankf, ackMax, ack, ackMax2]
        rw [mapIdx_append]
        simp
        repeat rw [add_assoc]
        simp
        sorry

  rank_le_of_rel_unfair := fun s1 s2 t =>
   match s1 with
      | (n, []) => by
        simp [AckSystem, ackRankf, ackStep] at t
        simp [t,AckSystem, ackRankf]
      | (n, 0 :: c) => by
        simp [AckSystem, ackRankf, ackStep] at t
        simp only [ackRankf, ackMax, t, List.mapIdx_reverse, Nat.cast_add, Nat.cast_one,
          Ordinal.add_one_eq_succ, AckSystem, ne_eq, decide_not, reduceCtorEq, decide_false,
          Bool.not_false, ↓reduceIte, ackMax2, ack_zero, List.reverse_cons, List.mapIdx_concat,
          Nat.cast_zero, List.length_reverse, zero_mul, List.sum_append, List.sum_cons,
          List.sum_nil, add_zero, add_lt_add_iff_left]
        simp
        rw [f]
        rw [@g (ackMax2 (n + 1) c) n.succ]
        rw [@g (ackMax2 (n + 1) c) n]
        rw [h2]
        simp [ackMax2]
        have f := ackMax2_gt (n + 1) c
        omega
        -- exact ord_lt (ackMax2 (n + 1) c) n
      | (0, (m + 1) :: c) =>  by
        simp [AckSystem, ackRankf, ackStep] at t
        simp [ackRankf, ackMax, t, ackMax2, List.reverse_cons, List.mapIdx_concat,
          List.mapIdx_reverse, List.length_reverse, List.sum_append, List.sum_cons, List.sum_nil,
          add_zero, Nat.cast_one, AckSystem, ne_eq, decide_not, reduceCtorEq, decide_false,
          Bool.not_false, ↓reduceIte, Ordinal.add_one_eq_succ, ack_succ_zero, Nat.cast_add,
          Nat.cast_zero, Ordinal.sub_zero, Order.succ_le_iff]
        -- simp [​add_lt_add_iff_left]
        -- simp [add_lt_add_iff_left]
        -- let f: Ordinal.{0} := (List.mapIdx (fun i a ↦ ↑a * Ordinal.omega0 ^ (ackMax2 (ack m 1) c - (c.length - 1 - i))) c).reverse.sum
        -- have feq : (f = (List.mapIdx (fun i a ↦ ↑a * Ordinal.omega0 ^ (ackMax2 (ack m 1) c - (c.length - 1 - i))) c).reverse.sum)  := by rfl
        -- rw [← feq]
        repeat rw [add_assoc]
        simp
        -- apply add_lt_add_of_lt_of_le
        -- linarith
        sorry
      | (n + 1, (m + 1) :: c) => by
        simp [AckSystem, ackRankf, ackStep] at t
        simp [t,AckSystem, ackRankf, ackMax, ack, ackMax2]
        rw [mapIdx_append]
        simp
        repeat rw [add_assoc]
        simp
        sorry

theorem ack_halts : AckSystem.IsFairEmpty := isFairEmpty_of_ordinalRankingFunction ackRank
