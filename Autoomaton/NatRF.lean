import Autoomaton.Buchi
import Autoomaton.Path
import Autoomaton.succeeds
variable {S : Type} {a : Automaton S} (r : Run a)

/-- A ranking function for a Büchi automaton maps states to natural numbers.
The rank must not increase along transitions. If the source state of a transition is fair, the rank must strictly decrease.
This is a witness for the emptiness of fair runs for an automaton.
-/
structure RankingFunction {S : Type} (a : Automaton S) : Type where
  /-- The ranking function $V: S \to \mathbb{N}$. -/
  rank : S → Nat
  reach : S → Prop
  init_reach : (s : S) → a.I s → reach s
  next_reach (s1 s2 : S) : a.R s1 s2 → reach s1 → reach s2
  /-- The condition on the ranking function: for all transitions $(s_1, s_2) \in R$,
  $V(s_2) + \mathbb{I}(s_1 \in F) \le V(s_1)$, where $\mathbb{I}$ is the indicator function. -/
  (rank_le_of_rel : ∀ s1 s2, a.R s1 s2  → reach s1 → rank s2 + (if a.F s1 then 1 else 0) ≤ rank s1)

variable (V : RankingFunction a)

theorem nat_run_reachable (n : Nat) : V.reach (r.f n) := by
  induction' n with m ih
  · exact V.init_reach (r.f 0) (r.is_init)
  · exact V.next_reach (r.f m) (r.f (m + 1)) (r.is_valid m) ih

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
    have : V.rank (r.f (i + 1)) + (if a.F (r.f i) then 1 else 0) ≤ V.rank (r.f i) := V.rank_le_of_rel (r.f i)  (r.f (i + 1)) (r.is_valid i) (nat_run_reachable r V i)
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

-- def decidable_path (s1 : S) [Finite S] [f : (s1 s2 : S) → Decidable (a.R s1 s2)] : DecidablePred (fun s2 ↦ Relation.ReflTransGen a.R s1 s2) := sorry

noncomputable def fair_successors (s1 : S) [fin : Finite S] : Finset S :=
  let _ : Fintype S := Fintype.ofFinite S
  let _ : DecidablePred (fun s2 ↦ Relation.ReflTransGen a.R s1 s2 ∧ a.F s2) := Classical.decPred (fun s2 ↦ Relation.ReflTransGen a.R s1 s2 ∧ a.F s2)
  {s2 | Relation.ReflTransGen a.R s1 s2 ∧ a.F s2}

noncomputable def fair_count (s1 : S) [fin : Finite S] : Nat :=
  Finset.card (fair_successors (a := a) s1)

theorem lt_le (a b : Nat) :  (a  + 1 ≤ b) ↔ (a < b) := by omega

noncomputable def completeness [fin : Finite S] (a : Automaton S) (fe : a.IsFairEmpty) : RankingFunction a := {
  rank := fun s => fair_count (a := a) s,
  reach := State.IsReachable (a := a),
  init_reach := init_reachable (a := a),
  next_reach := next_reachable (a := a) ,
  rank_le_of_rel := fun s1 s2 s1_r_s2 s1_reach => by
    have f_subset : fair_successors (a := a) s2 ⊆ fair_successors (a := a) s1 := by
      intro e e_mem
      simp only [fair_successors, Finset.mem_filter, Finset.mem_univ, true_and] at e_mem
      rcases e_mem with ⟨e_r_s2, e_f⟩
      simp only [fair_successors, Finset.mem_filter, Finset.mem_univ, e_f, and_true, true_and]
      trans s2
      · exact Relation.ReflTransGen.single s1_r_s2
      · exact e_r_s2
    by_cases s1_fair : a.F s1
    <;> simp only [fair_count, fair_successors, s1_fair, ↓reduceIte, lt_le, gt_iff_lt, s1_fair, Bool.false_eq_true, ↓reduceIte, add_zero, ge_iff_le]
    · apply Finset.card_lt_card
      simp only [fair_successors] at f_subset
      simp only [Finset.ssubset_def, f_subset, true_and]
      intro sub
      have s1_in : s1 ∈ fair_successors (a := a) s2 :=
        sub (by
          simp only [Finset.mem_filter, Finset.mem_univ, s1_fair, and_true, true_and]
          exact Relation.ReflTransGen.refl)
      simp only [fair_successors, Finset.mem_filter, Finset.mem_univ, true_and] at s1_in
      rcases s1_in with ⟨s2_r_s1, _⟩
      apply fe
      apply vardiRun_fair (if Even · then s2 else s1)
      · intro n
        rcases s1_reach with ⟨ i, i_rfm, i_init⟩
        by_cases p : Even n
        <;> simp only [Nat.even_add_one, p, not_false_eq_true, not_true_eq_false, ↓reduceIte]
        <;> use s1, i
        <;> simp only [i_init, i_rfm, Relation.ReflTransGen.refl, s1_fair,
            Relation.TransGen.single s1_r_s2, s2_r_s1, and_self, true_and]
        exact ⟨by
          trans s1
          · exact i_rfm
          · exact Relation.ReflTransGen.single s1_r_s2
            , by
            rw [Relation.TransGen.head'_iff]
            use s2
            ⟩
    · exact Finset.card_le_card f_subset
}

#print axioms completeness
