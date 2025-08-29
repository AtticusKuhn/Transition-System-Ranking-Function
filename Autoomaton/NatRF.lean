import Autoomaton.Buchi

variable {S : Type} {a : Automaton S} (r : Run a)

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
