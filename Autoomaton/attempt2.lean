import Mathlib.Data.Nat.Count
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Nth
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.OrderIsoNat

/-- A Büchi automaton is a tuple $(S, R, I, F)$ where
- $S$ is a set of states.
- $R \subseteq S \times S$ is a transition relation.
- $I \subseteq S$ is a set of initial states.
- $F \subseteq S$ is a set of fair (or accepting) states.
-/
structure Automaton (S : Type) where
  /-- The transition relation $R \subseteq S \times S$. -/
  (R : S → S → Bool)
  /-- The set of initial states $I \subseteq S$. -/
  (I : S → Bool)
  /-- The set of fair (accepting) states $F \subseteq S$. -/
  (F : S → Bool)

/-- A run of a Büchi automaton is an infinite sequence of states $f : \mathbb{N} \to S$ such that
the first state is initial and all subsequent states are related by the transition relation. -/
structure Run {S : Type} (a : Automaton S) where
  /-- The infinite sequence of states $f : \mathbb{N} \to S$. -/
  (f : Nat → S)
  /-- The first state must be an initial state, i.e., $f(0) \in I$. -/
  (is_init : a.I (f 0))
  /-- Each consecutive pair of states must be in the transition relation, i.e., $\forall n \in \mathbb{N}, (f(n), f(n+1)) \in R$. -/
  (is_valid : ∀ n, a.R (f n) (f n.succ))

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
    have n : V.rank (r.f (i + 1)) + (if a.F (r.f i) then 1 else 0) ≤ V.rank (r.f i) := V.rank_le_of_rel (r.f i) (r.f (i + 1)) (r.is_valid i)
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
  simp [Run.IsFairEmpty] at r_fair
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
  (rank : S → Ordinal.{u})
  /-- The condition on the ranking function: for all transitions $(s_1, s_2) \in R$,
  $W(s_2) + \mathbb{I}(s_1 \in F) \le W(s_1)$, where $\mathbb{I}$ is the indicator function. -/
  (rank_le_of_rel : ∀ s1 s2, a.R s1 s2 → rank s2 + (if a.F s1 then 1 else 0) ≤ rank s1)

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
  have c := W.rank_le_of_rel (r.f n) (r.f (n + 1)) (r.is_valid n)
  by_cases is_fair : a.F (r.f n)
  <;> simp only [is_fair, ↓reduceIte, Ordinal.add_one_eq_succ, Order.succ_le_iff, Bool.false_eq_true, add_zero] at c
  · exact LT.lt.le c
  · exact c)

/-- For a fair run, the sequence of ranks at fair visits is strictly decreasing.
$W(r.f(\text{nth_visit}(r, n+1))) < W(r.f(\text{nth_visit}(r, n)))$. -/
theorem ordSeq_strict_anti (r_fair : r.IsFair) (n : ℕ) : ordSeq r W (n + 1) < ordSeq r W n := by
  have : nth_visit r n < nth_visit r (n + 1) :=  @Nat.nth_strictMono (fun (x : Nat) => a.F (r.f x)) (fair_infinite r r_fair) n (n + 1) (by omega)
  have y := W.rank_le_of_rel (r.f (nth_visit r n)) (r.f (nth_visit r (n) + 1)) (r.is_valid (nth_visit r n))
  simp only [is_fair_at_nth_visit r n r_fair, ↓reduceIte, Ordinal.add_one_eq_succ,
    Order.succ_le_iff] at y
  exact LE.le.trans_lt (by
    apply rank_antitone
    omega) y

/-- The comparison of ranks in the `ordSeq` is equivalent to the reversed comparison of their indices.
This is a property of strictly antitone sequences.
For $m, n \in \mathbb{N}$, $W(r.f(\text{nth_visit}(r, m))) < W(r.f(\text{nth_visit}(r, n))) \iff n < m$. -/
theorem ordSeq_lt_iff_lt (r_fair : r.IsFair) {m n : ℕ} : ordSeq r W m < ordSeq r W n ↔ n < m := StrictAnti.lt_iff_lt (strictAnti_nat_of_succ_lt (ordSeq_strict_anti r W r_fair))

/-- The main theorem for ordinal-valued ranking functions.
If an ordinal-valued ranking function `W` exists for an automaton `a`, then `a` has no fair runs.
This is proven by showing that a fair run would imply an infinite decreasing sequence of ordinals, which is impossible. -/
theorem isFairEmpty_of_ordinalRankingFunction (W : OrdinalRankingFunction.{u} a) : a.IsFairEmpty := fun r r_fair =>
  (RelEmbedding.not_wellFounded_of_decreasing_seq ⟨⟨ordSeq r W,
      StrictAnti.injective (strictAnti_nat_of_succ_lt (ordSeq_strict_anti r W r_fair))
      ⟩, by
        intros m n
        simp only [Function.Embedding.coeFn_mk, gt_iff_lt]
        exact ordSeq_lt_iff_lt r W r_fair⟩) (Ordinal.wellFoundedLT.{u}.wf)
