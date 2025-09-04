import Autoomaton.Buchi
import Autoomaton.NatRF
import Autoomaton.Path

variable {S : Type} {a : Automaton S} (r : Run a)

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
  rank_le_of_rel_fair : ∀ s1 s2, a.R s1 s2 → State.IsReachable (a := a) s1 → a.F s1  → rank s2 < rank s1
  rank_le_of_rel_unfair : ∀ s1 s2, a.R s1 s2 → State.IsReachable (a := a) s1 → rank s2 ≤ rank s1

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
  · exact LT.lt.le (W.rank_le_of_rel_fair (r.f n) (r.f (n + 1)) (r.is_valid n) (run_reachable r n) is_fair)
  · exact cu (run_reachable r n))

/-- For a fair run, the sequence of ranks at fair visits is strictly decreasing.
$W(r.f(\text{nth_visit}(r, n+1))) < W(r.f(\text{nth_visit}(r, n)))$. -/
theorem ordSeq_strict_anti (r_fair : r.IsFair) : StrictAnti (ordSeq r W) := strictAnti_nat_of_succ_lt (fun n => by
  have : nth_visit r n < nth_visit r (n + 1) :=  @Nat.nth_strictMono (fun (x : Nat) => a.F (r.f x)) (fair_infinite r r_fair) n (n + 1) (by omega)
  have yf := W.rank_le_of_rel_fair (r.f (nth_visit r n)) (r.f (nth_visit r (n) + 1)) (r.is_valid (nth_visit r n)) (run_reachable r (nth_visit r n)) (is_fair_at_nth_visit r n r_fair)
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
State `s2` succeeds state `s1` via a fair witness reachable from `s1`.

There exists `f` with `R* s1 f`, `f ∈ F`, and `R+ f s2`.
-/
def stateSucceeds2 {S : Type} (a : Automaton S) (s2 s1 : S) : Prop :=
  ∃ (f : S), Relation.ReflTransGen a.R s1 f ∧ a.F f ∧ Relation.TransGen a.R f s2 -- ∧ f ≠ s1



/-
State `s2` succeeds state `s1` with an initial state witness.

There exist `i, f` such that `i ∈ I`, `R* i s1`, `R* s1 f`, `f ∈ F`, and `R+ f s2`.
-/
def stateSucceeds {S : Type} (a : Automaton S) (s2 s1 : S) : Prop :=
  ∃ (f i: S), a.I  i ∧ Relation.ReflTransGen a.R i s1 ∧ Relation.ReflTransGen a.R s1 f ∧ a.F f ∧ Relation.TransGen a.R f s2 -- ∧ f ≠ s1

/-
Dependent pair version carrying explicit path witnesses for each segment.
-/
def stateSucceeds4 {S : Type} (a : Automaton S) (s2 s1 : S) : Type :=
  Σ (f i: S), Inhabited (a.I  i) ×  Path a.R i s1 × Path a.R s1 f × Inhabited (a.F f) × Path a.R f s2 -- ∧ f ≠ s1


/-
Run-based definition: `s2` succeeds `s1` if there is a run visiting `s1` at `i`, then a fair state at `j`, then `s2` at `k` with `i ≤ j < k`.
-/
def stateSucceeds3 {S : Type} (a : Automaton S) (s2 s1 : S) : Prop :=
  ∃ (r : Run a), ∃ (i j k : Nat), i ≤ j ∧ j < k ∧ s1 = r.f i ∧ s2 = r.f k ∧ a.F (r.f j)




/-
If `s1 → s2` and `n` succeeds `s1`, then `n` also succeeds `s2`.

Uses transitivity of `Relation.TransGen` to append the edge `s1 → s2` at the end.
-/
theorem succeeds_concat { S : Type} (s1 s2 n : S)  (a : Automaton S)  (s1_r_s2 : a.R s1 s2) (n_suc_s2 : stateSucceeds a s1 n) : stateSucceeds a s2 n := by
  rcases n_suc_s2 with ⟨ f, i, i_init, i_to_s2, s2_to_f, f_fair, f_to_n  ⟩
  exact ⟨f, i, i_init, i_to_s2 , by
    exact s2_to_f
    ,f_fair ,
    by
    trans s1
    · exact f_to_n
    · exact Relation.TransGen.single s1_r_s2
    ⟩


/-
If `s1` is reachable and `n` succeeds `s2` with an edge `s1 → s2`, then `n` succeeds `s1`.

This moves the initial reachability witness backward along a single edge.
-/
theorem succeeds_concat4 { S : Type} (s1 s2 n : S)  (a : Automaton S)  (s1_r_s2 : a.R s1 s2) (n_suc_s2 : stateSucceeds a n s2) (s1_reach : State.IsReachable (a := a) s1) : stateSucceeds a n s1 := by
  rcases n_suc_s2 with ⟨ f, _i, _i_init, i_to_s2, rt, f_fair, tg ⟩
  rcases s1_reach with ⟨ i, i_to_s1, i_init⟩
  use f, i
  simp only [i_init, i_to_s1, f_fair, tg, and_self, and_true, true_and]
  rw [Relation.ReflTransGen.cases_head_iff]
  right
  use s2


/-
Concatenate the path segments for successive blocks witnessing `stateSucceeds`.

Builds a `Path a.R` from the initial state of `y 0` to `s i` by chaining the segments in blocks `[s n → f_n → s (n+1)]`.
-/
noncomputable def concatPaths (s : ℕ → S) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)) (i : Nat) : Path a.R (Exists.choose (Exists.choose_spec (y 0))) (s i) :=
  match i with
    | 0 =>
      transrefl_to_path (Exists.choose_spec (Exists.choose_spec (y 0))).2.1
    | i + 1 =>
      let k1 := (Exists.choose_spec (Exists.choose_spec (y (i))))
      Path.concat (concatPaths s y i)
        (Path.concat (transrefl_to_path k1.2.2.1) (transgen_to_path k1.2.2.2.2))
/--
y0: I0 ---> s0 ---> f0 ---> s1
y1: I1 ---> s1 ---> f1 ---> s2
...

concat the path
run : Nat -> S
fair run: I0 --> s0 --> f0 --> s1 --> f1 --> s2 --> ....
-/
/-
The run corresponding to the concatenated path up to block `i`.

`mkRun s y i =` the `i`-th vertex along `concatPaths s y (i+1)`.
-/
noncomputable def mkRun (s : ℕ → S) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)) (i : Nat) : S :=
  Path.lookup (concatPaths s y i.succ) i



/-
Factorization: the path to block `m` factors as the path to `n` concatenated with a tail.
-/
lemma factor_after_n {n m : ℕ} (hm : n ≤ m)  (s : Nat → S) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)) :
  ∃ Tail, concatPaths s y m = Path.concat (concatPaths s y n) (Tail) := by
  induction' hm with m hm ih
  · use Path.refl
    symm
    exact Path.concat_refl_right (concatPaths s y n)
  · rcases ih with ⟨Tail, hTail⟩
    let k1 := (Exists.choose_spec (Exists.choose_spec (y m)))
    use Path.concat Tail (Path.concat (transrefl_to_path k1.2.2.1) (transgen_to_path k1.2.2.2.2))
    rw [concatPaths]
    nth_rw 2 [Path.concat_assoc]
    rw [← hTail]

/-
Any path extracted from a `TransGen` witness has positive length: `0 < length (transgen_to_path p)`.
-/
theorem transgen_len {A B :S} {R : S → S → Prop} {p : Relation.TransGen R A B} : 0 < (transgen_to_path p).length :=
  Exists.choose_spec (transgen_to_path_with_pos_length p)

/-
Lower bound on concatenated path length: `n ≤ length (concatPaths s y n)`.
-/
theorem concatPaths_length (s : Nat → S) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)) (n : Nat) : n ≤ (concatPaths s y n).length := by
  induction' n with n ih
  · simp only [Nat.reduceAdd, concatPaths, zero_le]
  · simp only [Nat.reduceAdd, concatPaths, concat_len]
    have := transgen_len (p := (concatPaths._proof_7 s y n))
    omega

/-
Stability of early vertices: the `n`-th vertex is the same between blocks `n+1` and `n+2`.
-/
theorem concat_lookup (s : Nat → S) (n : Nat) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)): (concatPaths s y (n + 1)).lookup n = (concatPaths s y (n + 2)).lookup n := by
  rcases factor_after_n (n := n + 1) (m := n + 2) (by omega) s y  with ⟨ Tail, hTail ⟩
  rw [hTail, lookup_concat_left]
  have := concatPaths_length s y (n + 1)
  omega

/-
Build a run from the infinite concatenation of the `stateSucceeds` blocks (Vardi’s construction).
-/
noncomputable def vardiRun (s : Nat → S)  (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)) : Run a := ⟨mkRun s y, by
  simp only [mkRun, Nat.reduceAdd, Nat.succ_eq_add_one, concatPaths, lookup_zero]
  exact (Exists.choose_spec (concatPaths._proof_2 s y)).1
  , by
  intro n
  simp only [mkRun, Nat.reduceAdd, Nat.succ_eq_add_one]
  rw [concat_lookup]
  apply lookup_succ
  have := concatPaths_length s y (n + 1 + 1)
  omega
  ⟩

/-
The constructed run is fair: each block contributes a fair visit strictly later in the path.
-/
theorem vardiRun_fair (s : Nat → S)  (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)) : (vardiRun s y).IsFair := by
    rw [fair_iff_fair2]
    simp only [Run.IsFair2, ge_iff_le, mkRun, Nat.reduceAdd, Nat.succ_eq_add_one, vardiRun]
    intro n
    let yn := y n
    let f := (Exists.choose yn)                  -- the fair state in the nth block
    let inits := Exists.choose_spec yn           -- ∃ i, ...
    let i := (Exists.choose inits)
    let spec := Exists.choose_spec inits         -- unpack the conjunction
    let hiI : a.I i := spec.1
    let hi_to_sn : Relation.ReflTransGen a.R i (s n) := spec.2.1
    let hsn_to_f : Relation.ReflTransGen a.R (s n) f := spec.2.2.1
    let hf : a.F f := spec.2.2.2.1
    let hf_to_snp1  : Relation.TransGen a.R f (s (n+1)) := spec.2.2.2.2
    let SnF : Path a.R (s n) (f) := transrefl_to_path hsn_to_f
    let Pn := concatPaths s y n
    let k := Pn.length + SnF.length  -- this will be your fair index
    use k
    have t0 : n ≤ k := by
      simp only [Nat.reduceAdd, k, Pn, SnF, vardiRun]
      have := concatPaths_length s y (n)
      omega
    have t1 : (concatPaths s y (n + 1)).lookup k = f := by
      simp only [Nat.reduceAdd, concatPaths, lookup_concat, k, Pn, SnF, f]
      have : hsn_to_f = (concatPaths._proof_6 s y n) := by
        rfl
      rw [← this]
      have : (transrefl_to_path hsn_to_f).length = (transrefl_to_path hsn_to_f).length + 0 := by simp only [add_zero,
        k, SnF, Pn, f]
      rw [this, lookup_concat]
      simp only [lookup_zero, k, SnF, Pn, f]
    have t2 : (concatPaths s y k.succ).lookup k = (concatPaths s y (n + 1)).lookup k := by
      rcases factor_after_n (n := n + 1) (m := k.succ) (by omega) s y with ⟨ Tail, hTail ⟩
      rw [hTail, lookup_concat_left]
      simp only [Nat.reduceAdd, concatPaths, concat_len, add_lt_add_iff_left, lt_add_iff_pos_right,
        transgen_len, k, Pn, SnF, f]
    have t3 : (concatPaths s y k.succ).lookup k = f := by
      simp only [Nat.reduceAdd, Nat.succ_eq_add_one, t2, t1, k, Pn, f, SnF]
    simp only [t0, t3, hf, and_self, k, Pn, f, SnF]

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
theorem isFairEmpty_of_ordinalRankingFunction (W : OrdinalRankingFunction.{0} a) : a.IsFairEmpty := fun r r_fair =>
  (RelEmbedding.not_wellFounded_of_decreasing_seq ⟨⟨ordSeq r W,
      StrictAnti.injective (ordSeq_strict_anti r W r_fair)
      ⟩, by
        intros m n
        simp only [Function.Embedding.coeFn_mk, gt_iff_lt]
        exact ordSeq_lt_iff_lt r W r_fair⟩) (Ordinal.wellFoundedLT.{0}.wf)

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
noncomputable def ordinalRankingFunction_of_isFairEmpty (fe : a.IsFairEmpty) : (OrdinalRankingFunction.{0} a) := ⟨@IsWellFounded.rank S (stateSucceeds a) (n a fe), fun s1 s2  rel => by
    intro s1_reachable s1_fair
    apply IsWellFounded.rank_lt_of_rel (hwf := n a fe)
    rcases s1_reachable with ⟨i, i_to_s1, i_initial⟩
    use s1, i
    simp only [i_initial, i_to_s1, s1_fair, true_and]
    rw [Relation.ReflTransGen.cases_head_iff, Relation.transGen_iff]
    simp only [true_or, rel, and_self]
    ,
    by
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
    ⟩

--info: 'ordinalRankingFunction_of_isFairEmpty' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms ordinalRankingFunction_of_isFairEmpty
