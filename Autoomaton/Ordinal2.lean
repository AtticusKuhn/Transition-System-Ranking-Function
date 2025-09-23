import Autoomaton.Buchi
import Autoomaton.NatRF
import Autoomaton.Path
import Autoomaton.succeeds


namespace ordinal2
-- universe u
universe u
variable {S : Type} {A : Type u} [Preorder A] [WellFoundedLT A] {a : Automaton S} (r : Run a)


/-- An ordinal-valued ranking function for a Büchi automaton maps states to ordinals.
The rank must not increase along transitions. If the source state of a transition is fair, the rank must strictly decrease.
This is a more general form of a ranking function.
-/
structure OrdinalRankingFunction {S: Type} (A : Type u) [Preorder A]  [w : WellFoundedLT A] (a : Automaton S) : Type u where
  /-- The ranking function $W: S \to \text{Ordinal}$. -/
  rank : S → A
  reach : S → Prop
  init_reach : (s : S) → a.I s → reach s
  next_reach (s1 s2 : S) : a.R s1 s2 → reach s1 → reach s2
  /-- The condition on the ranking function: for all transitions $(s_1, s_2) \in R$,
  $W(s_2) + \mathbb{I}(s_1 \in F) \le W(s_1)$, where $\mathbb{I}$ is the indicator function. -/
  rank_le_of_rel_fair : ∀ s1 s2, a.R s1 s2 → reach s1 → a.F s1  → rank s2 < rank s1
  rank_le_of_rel_unfair : ∀ s1 s2, a.R s1 s2 → reach s1 → rank s2 ≤ rank s1




variable (W : OrdinalRankingFunction A a)
theorem run_reachable2 (n : Nat) : W.reach (r.f n) := by
  induction' n with m ih
  · exact W.init_reach (r.f 0) (r.is_init)
  · exact W.next_reach (r.f m) (r.f (m + 1)) (r.is_valid m) ih

/-- The sequence of ranks at the times of fair visits.
`ordSeq r W n` is the rank of the state at the `n`-th fair visit, i.e., $W(r.f(\text{nth_visit}(r, n)))$. -/
noncomputable def ordSeq (n : Nat) : A := W.rank (r.f (nth_visit r n))

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
  · exact LT.lt.le (W.rank_le_of_rel_fair (r.f n) (r.f (n + 1)) (r.is_valid n) (run_reachable2 r W n) is_fair)
  · exact cu (run_reachable2 r W n))

/-- For a fair run, the sequence of ranks at fair visits is strictly decreasing.
$W(r.f(\text{nth_visit}(r, n+1))) < W(r.f(\text{nth_visit}(r, n)))$. -/
theorem ordSeq_strict_anti (r_fair : r.IsFair) : StrictAnti (ordSeq r W) := strictAnti_nat_of_succ_lt (fun n => by
  have : nth_visit r n < nth_visit r (n + 1) :=  @Nat.nth_strictMono (fun (x : Nat) => a.F (r.f x)) (fair_infinite r r_fair) n (n + 1) (by omega)
  have yf := W.rank_le_of_rel_fair (r.f (nth_visit r n)) (r.f (nth_visit r (n) + 1)) (r.is_valid (nth_visit r n)) (run_reachable2 r W (nth_visit r n)) (is_fair_at_nth_visit r n r_fair)
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


/-
If `a` has no fair runs, then `stateSucceeds a` is well-founded.
-/
theorem succeeds_wf (a : Automaton S) (fe : a.IsFairEmpty) : WellFounded (stateSucceeds a) := by
  simp only [WellFounded.wellFounded_iff_no_descending_seq]
  by_contra c
  simp only [not_isEmpty_iff, nonempty_subtype] at c
  rcases c with ⟨s, y⟩
  exact fe (vardiRun s y) (vardiRun_fair s y)


/-
Provide the `IsWellFounded` instance for `stateSucceeds` from `succeeds_wf`.
-/
instance n {S  : Type} (a : Automaton S) (fe : a.IsFairEmpty) : IsWellFounded S (stateSucceeds a) where
  wf := succeeds_wf a fe

/-- The main theorem for ordinal-valued ranking functions.
If an ordinal-valued ranking function `W` exists for an automaton `a`, then `a` has no fair runs.
This is proven by showing that a fair run would imply an infinite decreasing sequence of ordinals, which is impossible. -/
theorem isFairEmpty_of_ordinalRankingFunction (W : OrdinalRankingFunction A a) : a.IsFairEmpty := fun r r_fair =>
  (RelEmbedding.not_wellFounded_of_decreasing_seq ⟨⟨ordSeq r W,
      StrictAnti.injective (ordSeq_strict_anti r W r_fair)
      ⟩, by
        intros m n
        simp only [Function.Embedding.coeFn_mk, gt_iff_lt]
        exact ordSeq_lt_iff_lt r W r_fair⟩) (wellFounded_lt)

#print axioms isFairEmpty_of_ordinalRankingFunction



/-
Completeness: construct an ordinal ranking from emptiness of fair runs.

Given `fe : a.IsFairEmpty`, the relation `stateSucceeds a` is well-founded, and we
define `W` to be the `WellFounded.rank` on this relation. This yields an
`OrdinalRankingFunction a` whose rank strictly decreases on fair steps and never
increases otherwise. In particular, for every transition `s1 → s2` we have
$$
  W(s_2) + \mathbb{I}(s_1 \in F) \le W(s_1),
$$
where `\mathbb{I}` is the indicator of fairness. This is the converse direction
to `isFairEmpty_of_ordinalRankingFunction`.
-/
noncomputable def ordinalRankingFunction_of_isFairEmpty (fe : a.IsFairEmpty) : (OrdinalRankingFunction (Ordinal.{0}) a) := {
  reach := fun s => State.IsReachable (a := a) s,
  init_reach := init_reachable,
  next_reach := next_reachable,
  rank := @IsWellFounded.rank S (stateSucceeds a) (n a fe),
  rank_le_of_rel_fair := fun s1 s2  rel => by
    intro s1_reachable s1_fair
    apply IsWellFounded.rank_lt_of_rel (hwf := n a fe)
    rcases s1_reachable with ⟨i, i_to_s1, i_initial⟩
    use s1, i
    simp only [i_initial, i_to_s1, s1_fair, true_and]
    rw [Relation.ReflTransGen.cases_head_iff, Relation.transGen_iff]
    simp only [true_or, rel, and_self]
    ,
  rank_le_of_rel_unfair := by
    intros s1 s2 s1_r_s2 s1_reachable
    by_contra c
    simp only [not_le] at c
    repeat rw [IsWellFounded.rank_eq] at c
    have : sSup (Set.range fun (b : { b // stateSucceeds a b s2 }) ↦ Order.succ (IsWellFounded.rank (hwf := n a fe) (stateSucceeds a) ↑b)) ≤ sSup (Set.range fun (b : { b // stateSucceeds a b s1 }) ↦ Order.succ (IsWellFounded.rank (hwf := n a fe) (stateSucceeds a) ↑b)) := csSup_le_csSup (by
      simp only [BddAbove, Set.Nonempty, upperBounds, Set.mem_range, Subtype.exists, exists_prop,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Order.succ_le_iff, Set.mem_setOf_eq]
      use IsWellFounded.rank (hwf := n a fe) (stateSucceeds a) s1
      intros s3
      exact IsWellFounded.rank_lt_of_rel (hwf := n a fe))
      (by
        by_cases n : (∃ (f : S), stateSucceeds a f s2 )
        · rcases n with  ⟨f, f_suc_s2 ⟩
          apply Set.range_nonempty (ι := { b // stateSucceeds a b s2 }) (h := by use f)
        · simp only [not_exists] at n
          have : IsEmpty { b // stateSucceeds a b s2 } := ⟨ fun ⟨ a, a_succ ⟩  => n a a_succ⟩
          simp only [ciSup_of_empty, Ordinal.bot_eq_zero, Ordinal.not_lt_zero] at c
          )
      (by
        intro s s_in_b
        simp only [Set.mem_range, Subtype.exists, exists_prop] at s_in_b
        rcases s_in_b with ⟨ n, n_suc_s2, ord_suc⟩
        simp only [Set.mem_range, Subtype.exists, exists_prop]
        use n
        simp only [ord_suc, and_true]
        exact succeeds_concat4 s1 s2 n a s1_r_s2 n_suc_s2 s1_reachable
        )
    have := LT.lt.not_ge c
    contradiction
  }

theorem fair_empty_iff_ranking_function : a.IsFairEmpty ↔ Nonempty (OrdinalRankingFunction (Ordinal.{0}) a) := by
  constructor
  · intro fe
    exact ⟨ordinalRankingFunction_of_isFairEmpty fe ⟩
  · intro rf
    exact isFairEmpty_of_ordinalRankingFunction (Classical.choice rf)

--info: 'ordinalRankingFunction_of_isFairEmpty' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms ordinalRankingFunction_of_isFairEmpty
