import Autoomaton.Buchi
import Autoomaton.NatRF

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

def stateSucceeds2 {S : Type} (a : Automaton S) (s2 s1 : S) : Prop :=
  ∃ (f : S), Relation.ReflTransGen a.R s1 f ∧ a.F f ∧ Relation.TransGen a.R f s2 -- ∧ f ≠ s1
inductive Path (r : S → S → Prop) (a : S) : S → Type
  | refl : Path r a a
  | tail {b c} : Path r a b → r b c → Path r a c

def Path.head {R : S → S → Prop} {a b  c : S} (rel : R a b) (p : Path R b c ) : Path R a c := match p with
  | .refl => Path.tail Path.refl rel
  | .tail b_to_b' path_b_to_b' => Path.tail (Path.head rel b_to_b') path_b_to_b'

def Path.lookup {R : S → S → Prop} {a b : S} (p : Path R a b) (i : Nat) : S :=
  match p with
    | @Path.refl S R a => a
    | @Path.tail S R a _ c snoc rel =>
      match i with
        | 0 => a
        | i + 1 => Path.lookup snoc i
def Path.lookup' {R : S → S → Prop} {a b : S} (p : Path R a b) (i : Nat) : S :=
  match i with
    | 0 => a
    | i + 1 => match p with
      | @Path.refl S R a => a
      | @Path.tail S R a _ c snoc rel => Path.lookup' snoc i

theorem transrefl_to_path' {a b : S} {R : S → S → Prop} (p : Relation.ReflTransGen R a b) : Nonempty (Path R a b) := by
  induction' p  with b c path_a_b R_b_c ih
  · exact ⟨ Path.refl⟩
  · exact ⟨ Path.tail (Classical.choice ih) R_b_c⟩

theorem transgen_to_path' {a b : S} {R : S → S → Prop} (p : Relation.TransGen R a b) : Nonempty (Path R a b) := by
  induction' p  with b c a' b' a_to_a' a'_to_b' ih
  · exact ⟨ Path.tail (Path.refl) c⟩
  · exact ⟨ Path.tail (Classical.choice ih) a'_to_b'⟩

@[trans]
def path_trans {x y z : S} {R : S → S → Prop} (p1 : Path R x y) (p2 : Path R y z) : Path R x z :=
  match p1 with
    | .refl => p2
    | .tail p1_snoc h => path_trans p1_snoc (Path.head h p2)

def stateSucceeds {S : Type} (a : Automaton S) (s2 s1 : S) : Prop :=
  ∃ (f i: S), a.I  i ∧ Relation.ReflTransGen a.R i s1 ∧ Relation.ReflTransGen a.R s1 f ∧ a.F f ∧ Relation.TransGen a.R f s2 -- ∧ f ≠ s1

def stateSucceeds4 {S : Type} (a : Automaton S) (s2 s1 : S) : Type :=
  Σ (f i: S), Inhabited (a.I  i) ×  Path a.R i s1 × Path a.R s1 f × Inhabited (a.F f) × Path a.R f s2 -- ∧ f ≠ s1

-- inductive ReflTransGen {A : Type} (r : A → A → Prop) (a : A) : A  → Type
--   | refl : ReflTransGen r a a
--   | tail {b c} : ReflTransGen r a b → r b c → ReflTransGen r a c

-- inductive TransGen {A : Type} (r : A → A → Prop)  : A → A  → Type
--   | refl {a b} : r a b → TransGen r a b
--   | tail {a b c} : TransGen r a b → r b c → TransGen r a c

-- def stateSucceeds4 {S : Type} (a : Automaton S) (s2 s1 : S) : Type :=
--   Σ (f i: S), Inhabited (a.I i = true) × ReflTransGen a.R i s1 × ReflTransGen a.R s1 f × Inhabited (a.F f = true) × TransGen a.R f s2

-- def stateSucceeds {S : Type} (a : Automaton S) (s2 s1 : S) : Type :=
--   ∃ (f i: S),  a.I i ∧ ReflTransGen a.R i s1 ∧ ReflTransGen a.R s1 f ∧  Inhabited (a.F f = true) × TransGen a.R f s2

def stateSucceeds3 {S : Type} (a : Automaton S) (s2 s1 : S) : Prop :=
  ∃ (r : Run a), ∃ (i j k : Nat), i ≤ j ∧ j < k ∧ s1 = r.f i ∧ s2 = r.f k ∧ a.F (r.f j)
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

-- theorem succeeds_concat2 { S : Type} (s1 s2 n : S)  (a : Automaton S)  (s1_r_s2 : a.R s2 s1) (n_suc_s2 : stateSucceeds a s1 n) : stateSucceeds a s2 n := by
--   rcases n_suc_s2 with ⟨ f, i, i_init, i_to_s2, s2_to_f, f_fair, f_to_n  ⟩
--   exact ⟨f, i, i_init, sorry , by
--     rw [Relation.ReflTransGen.cases_head_iff]
--     right
--     exact ⟨ s2, sorry, sorry⟩
--     ,f_fair ,sorry ⟩

theorem succeeds_concat { S : Type} (s1 s2 n : S)  (a : Automaton S)  (s1_r_s2 : a.R s1 s2) (n_suc_s2 : stateSucceeds a s1 n) : stateSucceeds a s2 n := by
  rcases n_suc_s2 with ⟨ f, i, i_init, i_to_s2, s2_to_f, f_fair, f_to_n  ⟩
  exact ⟨f, i, i_init, i_to_s2 , by
    exact s2_to_f
    ,f_fair ,
    by
    trans s1
    exact f_to_n
    exact Relation.TransGen.single s1_r_s2
    -- rw [Relation.TransGen.cases_head_iff]
    ⟩
-- theorem succeeds_concat3 { S : Type} (s1 s2 n : S)  (a : Automaton S)  (s1_r_s2 : a.R s1 s2) (n_suc_s2 : stateSucceeds a n s1) : stateSucceeds a n s2 := by
--   rcases n_suc_s2 with ⟨ f, i, i_init, i_to_s2, s2_to_f, f_fair, f_to_n  ⟩
--   sorry
theorem succeeds_concat4 { S : Type} (s1 s2 n : S)  (a : Automaton S)  (s1_r_s2 : a.R s1 s2) (n_suc_s2 : stateSucceeds a n s2) (s1_reach : State.IsReachable (a := a) s1) : stateSucceeds a n s1 := by
  rcases n_suc_s2 with ⟨ f, _i, _i_init, i_to_s2, rt, f_fair, tg ⟩
  rcases s1_reach with ⟨ i, i_to_s1, i_init⟩
  use f, i
  simp only [i_init, i_to_s1, f_fair, tg, and_self, and_true, true_and]
  rw [Relation.ReflTransGen.cases_head_iff]
  right
  use s2
  -- exact ⟨f, i, i_init, i_to_s2 , by
  --   exact s2_to_f
  --   ,f_fair ,
  --   by
  --   trans s1
  --   exact f_to_n
  --   exact Relation.TransGen.single s1_r_s2
  --   -- rw [Relation.TransGen.cases_head_iff]
  --   ⟩
  -- use f
  -- -- sorry
  -- -- simp [f_fair, tg]
  -- --
  -- -- -- right
  -- -- use s2
  -- -- simp
  -- use i
  -- -- rw [Relation.ReflTransGen.cases_head_iff]
  -- simp [i_init, f_fair, i_to_s2, s2_to_f]
  -- rw [Relation.ReflTransGen.cases_head_iff]

  -- right

  -- sorry

-- theorem succeeds_concat {S : Type} (a : Automaton S)
--     {s1 s2 n : S}
--     (h12 : a.R s1 s2)
--     (hn : stateSucceeds a n s2) :
--     stateSucceeds a n s1 := by
--   rcases hn with ⟨f, i, hiI, hi_s1, s1_f, hf, f_s2⟩
--   refine ⟨f, i, hiI, ?_, s1_f, hf, f_s2⟩
--   exact hi_s1.trans (Relation.ReflTransGen.single h12)


-- inductive Path (R : S → S → Prop) : S → S → Type
--   | nil : {x: S} → Path R x x
--   | cons {x y z} (hxy : R x y) (p : Path R y z) : Path R x z

noncomputable def transgen_to_path {a b : S} {R : S → S → Prop} (p : Relation.TransGen R a b) : Path R a b :=
  Classical.choice (transgen_to_path' p)

noncomputable def transrefl_to_path {a b : S} {R : S → S → Prop} (p : Relation.ReflTransGen R a b) : Path R a b :=
  Classical.choice (transrefl_to_path' p)

noncomputable def concatPaths (s : ℕ → S) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)) (i : Nat) : Path a.R (Exists.choose (Exists.choose_spec (y 0))) (s i.succ) :=
  match i with
    | 0 => by
      let y0 := y 0
      let k := (Exists.choose_spec (y0))
      let k1 := (Exists.choose_spec (k))
      rcases k1 with ⟨i_initial,i_to_sn,sn_to_f,f_fair,f_to_ssn⟩
      let s1 := transrefl_to_path i_to_sn
      let s2 := transrefl_to_path sn_to_f
      let s3 := transgen_to_path f_to_ssn
      exact path_trans s1 (path_trans s2 s3)
    | i + 1 => by
      let y0 := y (i + 1)
      let r := concatPaths s y i
      let k := (Exists.choose_spec (y0))
      let k1 := (Exists.choose_spec (k))
      rcases k1 with ⟨i_initial,i_to_sn,sn_to_f,f_fair,f_to_ssn⟩
      let s2 := transrefl_to_path sn_to_f
      let s3 := transgen_to_path f_to_ssn
      exact path_trans r (path_trans s2 s3)
/--
y0: I0 ---> s0 ---> f0 ---> s1
y1: I1 ---> s1 ---> f1 ---> s2
...

concat the path
run : Nat -> S
fair run: I0 --> s0 --> f0 --> s1 --> f1 --> s2 --> ....
-/
noncomputable def mkRun (s : ℕ → S) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)) (i : Nat) : S :=
  Path.lookup' (concatPaths s y i) i
set_option pp.proofs true
theorem succeeds_wf (a : Automaton S) (fe : a.IsFairEmpty) : WellFounded (stateSucceeds a) := by
  -- simp [IsWellFounded]
  -- suggest
  -- suggest_hint
  classical

  simp [WellFounded.wellFounded_iff_no_descending_seq]
  by_contra c
  simp at c
  -- simp at fe

  rcases c with ⟨ s, y⟩
  simp [stateSucceeds] at y
  have r : Run a := by
    exact ⟨ mkRun s y, by
      simp [mkRun, concatPaths, Path.lookup']
      have cs := Exists.choose_spec (concatPaths._proof_2 s y)
      exact cs.1
      , by
      simp [mkRun, concatPaths, Path.lookup']
      intro n
      induction' n with n ih
      · simp [concatPaths, Path.lookup', And.rec]
        have cs := Exists.choose_spec (concatPaths._proof_2 s y)
        rcases cs with ⟨ i_init , x_to_s0, s0_to_y, y_fair, y_to_s1 ⟩
        simp only [s0_to_y, y_fair, y_to_s1, and_self, and_true]

        sorry

      · simp [concatPaths, Path.lookup', And.rec]
        -- have cs := Exists.choose_spec (concatPaths._proof_2 s y)
        -- rcases cs with ⟨ i_init , x_to_s0, s0_to_y, y_fair, y_to_s1 ⟩
        -- simp [s0_to_y, y_fair, y_to_s1, i_init,x_to_s0]

        sorry⟩
  -- have con : ∃ (r : Run a), r.IsFair := by
  --   -- rw [← Run.exists_fairN_fair]
  --    , sorry⟩
  have r_fair : r.IsFair := by
    simp [Run.IsFair]
    sorry
    -- sorry
  exact fe (r) (r_fair)

  -- contradiction
  -- simp at t
  -- have  path (n : Nat) : S := match n with
  --   | 0 => by
  --     have k := (Exists.choose_spec (y 0))
  --     have p := (Exists.choose k)
  --     exact p
  --   | n + 1 => by
  --     have yn := y (n)
  --     have fspec := (Exists.choose_spec yn)
  --     have f := (Exists.choose yn)
  --     have i := (Exists.choose fspec)
  --     have ispec := (Exists.choose_spec fspec)
  --     rcases ispec with ⟨i_initial,i_to_sn,sn_to_f,f_fair,f_to_ssn⟩
  --     sorry


  -- have rn : Run a := ⟨fun n => (Exists.choose (y n)).1 n
  --   ,  (Exists.choose (y 0)).2

  --    , sorry⟩
  -- have := fe rn
  -- sorry

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



noncomputable def completeness (fe : a.IsFairEmpty) : (OrdinalRankingFunction.{0} a) := ⟨@IsWellFounded.rank S (stateSucceeds a) (n a fe), fun s1 s2  rel => by
    intro s1_reachable s1_fair
    apply IsWellFounded.rank_lt_of_rel (hwf := n a fe)
    simp [stateSucceeds]
    rcases s1_reachable with ⟨ i, i_to_s1, i_initial⟩

    use s1, i
    -- rcases s1_reachable with ⟨ i, i_rfm, i_init⟩

    simp [i_initial, true_and, i_to_s1, s1_fair]
    rw [Relation.ReflTransGen.cases_head_iff]
    rw [Relation.transGen_iff]
    simp [true_or, s1_fair, rel, and_self]
    ,
    by
    intros s1 s2 s1_r_s2 s1_reachable
    by_contra c
    simp only [not_le] at c
    rw [IsWellFounded.rank_eq] at c
    rw [IsWellFounded.rank_eq] at c
    have : sSup (Set.range fun (b : { b // stateSucceeds a b s2 }) ↦ Order.succ (IsWellFounded.rank (hwf := n a fe) (stateSucceeds a) ↑b)) ≤ sSup (Set.range fun (b : { b // stateSucceeds a b s1 }) ↦ Order.succ (IsWellFounded.rank (hwf := n a fe) (stateSucceeds a) ↑b)) := csSup_le_csSup (by
      simp only [BddAbove, Set.Nonempty, upperBounds, Set.mem_range, Subtype.exists, exists_prop,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Order.succ_le_iff, Set.mem_setOf_eq]
      use IsWellFounded.rank (hwf := n a fe) (stateSucceeds a) s1
      intros s3
      exact IsWellFounded.rank_lt_of_rel (hwf := n a fe))
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
        exact succeeds_concat4 s1 s2 n a s1_r_s2 n_suc_s2 s1_reachable
        )
    have := LT.lt.not_ge c
    contradiction
    ⟩

#print axioms completeness
