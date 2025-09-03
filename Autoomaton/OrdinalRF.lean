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



def Path.length {R : S → S → Prop} {a b : S} (p : Path R a b) : Nat :=
  match p with
    | @Path.refl S R a => 0
    | @Path.tail S R a _ c snoc rel => 1 + Path.length snoc
@[simp, reducible]
def Path.lookup {R : S → S → Prop} {a b : S} (p : Path R a b) (i : Nat) : S :=
  match p with
    | @Path.refl S R a => a
    | @Path.tail S R a b c snoc rel =>
      if i >= p.length then c else snoc.lookup i
def test : Path ( · < · ) 1 5 := Path.tail (c := 5) (
    Path.tail (c := 3)
      Path.refl (by omega)) (by omega)

@[simp, reducible]
def Path.toList {R : S → S → Prop} {a b : S} (p : Path R a b) : List S:=
  match p with
    | @Path.refl S R a => [a]
    | @Path.tail S R a b c snoc rel => snoc.toList ++ [c]
@[simp, reducible]
def Path.lookup' {R : S → S → Prop} {a b : S} (p : Path R a b) (i : Nat) : S :=
    List.getD (Path.toList p) i b
  -- let rec go {R : S → S → Prop} {a b : S} (p : Path R a b) (l : Nat) (i : Nat) :=
  --   match i with
  --     | 0 => a
  --     | i + 1 => match p with
  --       | @Path.refl S R a => b
  --       | @Path.tail S R a b c snoc rel =>
  --         if i  >= p.length then c else go snoc l i
  -- go p p.length i
/-- info: 2 -/
#guard_msgs in #eval test.length
/-- info: 1 -/
#guard_msgs in #eval test.lookup 0
/-- info: 3 -/
#guard_msgs in #eval test.lookup 1
/-- info: 5 -/
#guard_msgs in #eval test.lookup 2
/-- info: 5 -/
#guard_msgs in #eval test.lookup 3
/-- info: 5 -/
#guard_msgs in #eval test.lookup 4
/-- info: 2 -/
#guard_msgs in #eval test.length
/-- info: 1 -/
#guard_msgs in #eval test.lookup' 0
/-- info: 3 -/
#guard_msgs in #eval test.lookup' 1
/-- info: 5 -/
#guard_msgs in #eval test.lookup' 2
/-- info: 5 -/
#guard_msgs in #eval test.lookup' 3
/-- info: 5 -/
#guard_msgs in #eval test.lookup' 4
#eval test.toList
#eval test.length

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

theorem trans_refl {x y z : S} {R : S → S → Prop} (p : Path R x y) : path_trans p Path.refl = p :=
  match p with
    | .refl => sorry
    | .tail p1_snoc h => sorry


theorem trans_tail {x y z c : S} {R : S → S → Prop} (p : Path R x y)  (snoc : Path R y z) (rel : R z c): path_trans p (Path.tail snoc rel) = Path.tail (path_trans p snoc) rel :=
  sorry

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

noncomputable def concatPaths (s : ℕ → S) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)) (i : Nat) : Path a.R (Exists.choose (Exists.choose_spec (y 0))) (s i) :=
  match i with
    | 0 =>
      -- let k1 :=
      -- rcases k1 with ⟨i_initial,i_to_sn,sn_to_f,f_fair,f_to_ssn⟩
      -- let s1 := transrefl_to_path k1.2.1
      -- let s2 := transrefl_to_path k1.2.2.1
      -- let s3 := transgen_to_path k1.2.2.2.2
      transrefl_to_path (Exists.choose_spec (Exists.choose_spec (y 0))).2.1
      -- exact path_trans s1 (path_trans s2 s3)
    | i + 1 =>
      let k1 := (Exists.choose_spec (Exists.choose_spec (y (i))))
      -- rcases k1 with ⟨i_initial,i_to_sn,sn_to_f,f_fair,f_to_ssn⟩
      path_trans (concatPaths s y i) (path_trans (transrefl_to_path k1.2.2.1) (transgen_to_path k1.2.2.2.2))
/--
y0: I0 ---> s0 ---> f0 ---> s1
y1: I1 ---> s1 ---> f1 ---> s2
...

concat the path
run : Nat -> S
fair run: I0 --> s0 --> f0 --> s1 --> f1 --> s2 --> ....
-/
noncomputable def mkRun (s : ℕ → S) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)) (i : Nat) : S :=
  Path.lookup (concatPaths s y i) i
theorem lookup_succ {R : S → S → Prop} {a b : S} (p : Path R a b) (i : Nat) (le : i < p.length): R (Path.lookup p i) (Path.lookup p i.succ) := by
  match p with
    | Path.refl =>
      simp [Path.length] at le
    | Path.tail a b =>
      simp [Path.toList, List.getD, le]
      have x : ¬ (a.tail b).length ≤ i := by omega
      simp [x]
      sorry
  -- induction' i with i ih
  -- <;> simp [Path.lookup']
  -- ·
  --   -- unfold Path.lookup'
  --   simp [Path.lookup', Path.toList, le]

  --   sorry
  -- · sorry
set_option pp.proofs true

def mkRunFn (s : Nat → S) (p : ∀ (i : Nat), Path a.R (s i) (s i.succ)) (l :∀ (i : Nat),  (p i).length > 0 ) ( i : Nat) : S :=
    if (p i).length ≥ i then (p i).lookup i else mkRunFn (fun i => s (i + 1)) (fun i => p (i + 1)) (fun i => l (i + 1)) (i - (p i).length)
termination_by i
decreasing_by
  have n := l i
  omega
theorem lookup_zero {a b : S} {R : S → S → Prop} (p : Path R a b) : p.lookup 0 = a := by
  induction' p with x y a_to_x x_to_y  ih
  <;> simp only [Path.lookup, ge_iff_le, nonpos_iff_eq_zero]
  simp only [Path.length, Nat.add_eq_zero, one_ne_zero, false_and, ↓reduceIte, ih]


-- theorem lookup_succ {a b : S} {R : S → S → Prop} (p : Path R a b) : p.lookup 0 = a := by
--   induction' p with x y a_to_x x_to_y  ih
--   <;> simp only [Path.lookup, ge_iff_le, nonpos_iff_eq_zero]
--   simp only [Path.length, Nat.add_eq_zero, one_ne_zero, false_and, ↓reduceIte, ih]

def mkRunSeg (s : Nat → S) (p : ∀ (i : Nat), Path a.R (s i) (s i.succ)) (l :∀ (i : Nat),  (p i).length > 0 ) : Run a := by
  exact ⟨mkRunFn s p l, by
    simp [mkRunFn, Path.lookup]
    simp [lookup_zero]

    sorry,

    by
      intro n
      unfold mkRunFn
      induction' n with n ih

      simp [Path.lookup, lookup_zero]


      -- simp [mkRunFn, Path.lookup]

      sorry
      sorry⟩

def Path.contains {a b : S} {R : S → S → Prop} (p : Path R a b) (P : S → Prop) : Prop :=
  ∃ (i : Nat), i ≤ p.length ∧ P (p.lookup i)

theorem concat_len {a b c : S} {R : S → S → Prop} (p1 : Path R a b) (p2 : Path R b c) : (path_trans p1 p2).length = p1.length + p2.length :=
    match p2 with
    | @Path.refl S R _ => by
      simp [Path.length,]
      rw [trans_refl]
      exact b
      -- rfl
      -- sorry
    | .tail p1_snoc h => sorry
-- theorem match_push {A B : Type } {n : Nat} {x : B} {y : Nat → B} {f : B → A}: f (match n with
--   | 0 => x
--   | Nat.succ i => y i) =  (match n with
--   | 0 => f x
--   | Nat.succ i => f (y i)) := sorry

-- theorem run_fair (s : Nat → S) (p : ∀ (i : Nat), Path a.R (s i) (s i.succ)) (h : ∀ (i : Nat), (p i).contains (fun x => a.F x = true)) : (mkRunSeg s p).IsFair := by
  -- sorry
theorem concat_lookup (s : Nat → S) (n : Nat) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)): (concatPaths s y n).lookup n = (concatPaths s y n.succ).lookup n := by
  sorry
theorem lookup_concat {a b c :S} {R : S → S → Prop} {p1 : Path R a b} {p2 : Path R b c} {n : Nat} : (path_trans p1 p2).lookup (p1.length + n) = p2.lookup n :=
  match p2 with
    | .refl => by
      simp [Path.length, path_trans]
      rw [trans_refl p1]
      -- exact

      sorry
      exact b

    | .tail p1_snoc h => by
      have y := lookup_concat (p1 := p1) (p2 := p1_snoc) (n := n)
      -- have t : (if 1 + (p1.length + p1_snoc.length) ≤ p1.length + n) ↔ (if 1 + (p1.length + p1_snoc.length) ≤ p1.length + n) := by sorry
      simp [Path.length, path_trans, trans_tail, concat_len, y]

      sorry
  -- sorry
theorem lookup_concat_2 {a b c :S} {R : S → S → Prop} {p1 : Path R a b} {p2 : Path R b c} {n : Nat} (le : n < p1.length) : (path_trans p1 p2).lookup (n) = p1.lookup n := by
  induction' p1 with x y a_to_x x_to_y ih
  · simp only [Path.length, not_lt_zero'] at le
  · simp [path_trans]
    have  : ¬  ((a_to_x.tail x_to_y).length ≤ n) := by omega
    simp [this]
    by_cases c : n = (a_to_x).length
    ·
      sorry
    · sorry

-- theorem lookup_get : p1.lookup
theorem fair_concat {m n : Nat} (s : Nat → S) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)) : a.F ((concatPaths s y m).lookup (((concatPaths s y n).length + ( transrefl_to_path (Exists.choose_spec (Exists.choose_spec (y m))).2.2.1).length))) := by

  sorry
lemma head_trans {A B C D : S} {R : S → S → Prop} {x_to_y : R A B} {p2 : Path R B C} {p3 : Path R C D}: (Path.head x_to_y (path_trans p2 p3)) = path_trans (Path.head x_to_y p2) p3 := by
  induction' p2 with p q a_to_p p_to_q ih
  · simp only [path_trans, Path.head]
  · simp only [path_trans, ih, Path.head]

lemma path_assoc {A B C D : S} {R : S → S → Prop} {p1 : Path R A B} {p2 : Path R B C} {p3 : Path R C D}: path_trans p1 (path_trans p2 p3) = path_trans (path_trans p1 p2) p3 := by
  induction' p1 with x y a_to_x x_to_y ih
  · simp only [path_trans]
  · simp only [path_trans, head_trans, ih]


-- Step 4: factorization past n
lemma factor_after_n {n m : ℕ} (hm : n ≤ m)  (s : Nat → S) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)) :
  ∃ Tail, concatPaths s y m = path_trans (concatPaths s y n) (Tail) := by
  induction' hm with m hm ih
  · let k1 := (Exists.choose_spec (Exists.choose_spec (y (n))))
    use (path_trans (transrefl_to_path k1.2.2.1) (transgen_to_path k1.2.2.2.2))
    simp only [Nat.reduceAdd, concatPaths]
  · -- step m+1
    rcases ih with ⟨Tail, hTail⟩
    let k1 := (Exists.choose_spec (Exists.choose_spec (y m)))
    let pm : Path a.R (s m) (s (m + 1)) := path_trans (transrefl_to_path k1.2.2.1) (transgen_to_path k1.2.2.2.2)
    use path_trans (Tail) (pm)
    rw [concatPaths]
    nth_rw 2 [path_assoc]
    rw [← hTail]
theorem transgen_len {A B :S} {R : S → S → Prop} {p : Relation.TransGen R A B} : 0 < (transgen_to_path p).length := by
  induction' p with b c a' b' a_to_a' a'_to_b' ih
  · simp [transgen_to_path, transgen_to_path' ]
    sorry
  · sorry
-- theorem path_concat_fe (c : ∃ (i : S), a.I i ∧ ∀  (p : Path a.R i x))
theorem concatPaths_length (s : Nat → S) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)) (n : Nat): n ≤ (concatPaths s y n).length := by
  induction' n with n ih
  · simp [concatPaths]
  · simp [concatPaths, concat_len]
    have := transgen_len (p := (concatPaths._proof_7 s y n))
    omega

theorem succeeds_wf (a : Automaton S) (fe : a.IsFairEmpty) : WellFounded (stateSucceeds a) := by
  -- simp [IsWellFounded]
  -- suggest
  -- suggest_hint
  -- classical

  simp [WellFounded.wellFounded_iff_no_descending_seq]
  by_contra c
  simp at c
  -- simp at fe

  rcases c with ⟨ s, y⟩
  simp [stateSucceeds] at y
  let r : Run a := by
    exact ⟨ mkRun s y, by
      simp only [mkRun, Nat.reduceAdd, Nat.succ_eq_add_one, concatPaths]
      simp only [lookup_zero]
      have cs := Exists.choose_spec (concatPaths._proof_2 s y)
      exact cs.1
      , by
      intro n
      simp only [mkRun, Nat.reduceAdd, Nat.succ_eq_add_one]
      rw [concat_lookup]
      apply lookup_succ
      sorry⟩

  have r_fair : r.IsFair := by

    -- by_contra c
    simp [Run.IsFair]
    simp [r]
    -- rcases c with ⟨ max, t ⟩

    simp [mkRun, concatPaths]
    intro n
    -- let y0 := y (n + 1)
    -- let k := (Exists.choose_spec (y0))
    -- let k1 := (Exists.choose_spec (k))
    -- rcases k1 with ⟨i_initial,i_to_sn,sn_to_f,f_fair,f_to_ssn⟩
    -- let s2 := transrefl_to_path (Exists.choose_spec (Exists.choose_spec (y0))).2.2.1
    -- have thing : 0 < s2.length := by sorry
    -- have thing2 : 0 < n + s2.length := by omega
    -- have things3 : n < (concatPaths s y n).length := by sorry
    -- have thing4 : n < (concatPaths s y n).length + s2.length := by omega
    -- have thing5 : 0 < (concatPaths s y n).length + s2.length := by omega
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

    let SnF :  Path a.R (s n) (f)  := transrefl_to_path hsn_to_f

  -- - Now set
    let Pn := concatPaths s y n
    let k := Pn.length + (SnF.length)  -- this will be your fair index
    use k
    -- simp [k]
    -- have :  (concatPaths s y k).lookup k = (concatPaths s y (n+1)).lookup k := by
      -- sorry
    have t0 : n < k := by
      simp [k, Pn, SnF, transgen_len]
      sorry

    have t1 : (concatPaths s y (n + 1)).lookup k = f := by
      simp [concatPaths, k, Pn]
      simp [lookup_concat, SnF]
      have : hsn_to_f = (concatPaths._proof_6 s y n) := by
        rfl
      rw [← this]
      have : (transrefl_to_path hsn_to_f).length =  (transrefl_to_path hsn_to_f).length + 0 := by simp
      rw [this]
      rw [lookup_concat]
      simp only [lookup_zero, k, SnF, Pn, f]

    have t2 : (concatPaths s y k).lookup k = (concatPaths s y (n + 1)).lookup k := by
      -- extract_goal
      have := factor_after_n (n := n + 1) (m := k) (by omega) s y
      rcases this with ⟨ Tail, hTail ⟩
      rw [hTail]
      rw [lookup_concat_2]
      simp [concatPaths]
      simp [concat_len]
      simp [k, Pn, SnF]
      simp [transgen_len]
    have t3 : (concatPaths s y k).lookup k = f := by
      simp [t1,t2]
    simp [t3, hf, t0]
    -- omega

    -- use (concatPaths s y n).length + s2.length
    -- simp [k, thing4]
    -- nth_rw 2 [concatPaths.eq_def]
    -- simp [thing5]
    -- -- simp [match_push (f := fun p => Path.lookup p)  ]
    -- cases h : ((concatPaths s y n).length + s2.length)  with
    --   | zero =>
    --     have : n < 0 := by
    --       sorry
    --     omega
    --     -- simp [lookup_zero]
    --     -- have cs := Exists.choose_spec (concatPaths._proof_2 s y)
    --     -- exact cs.2.2.2.1
    --     -- sorry
    --   | succ i =>
    --     simp [concat_len, lookup_concat]
    --     simp [← h]
    --     -- simp [add_assoc]
    --     -- rw [lookup_concat (p1 := (concatPaths s y i)) (p2 := path_trans (transrefl_to_path (concatPaths._proof_6 s y i))
    --         -- (transgen_to_path (concatPaths._proof_7 s y i))) (n := s2.length)]

    --     -- rw [i]
    --     -- rw [add_assoc]
    --     sorry
    -- unfold concatPaths
    -- cases n with
    --   | zero =>
    --     simp [concatPaths, concat_len]
    --     -- simp []
    --     sorry
    --   | succ i =>
    --     simp [concatPaths]
    --     simp [concat_len]
    --     repeat rw [concat_len]
    --     rw [add_assoc]
    --     rw [match_push (f := fun p => p.lookup
    --   ((concatPaths s y i).length +
    --     ((transrefl_to_path (concatPaths._proof_6 s y i)).length +
    --         (transgen_to_path (concatPaths._proof_7 s y i)).length +
    --       s2.length))) (n := (concatPaths s y i).length +
    --         ((transrefl_to_path (concatPaths._proof_6 s y i)).length +
    --             (transgen_to_path (concatPaths._proof_7 s y i)).length +
    --           s2.length))]

        -- rw [lookup_concat_2]
        -- unfold concatPaths
        -- simp [lookup_concat]
        -- exact fair_concat s (m := i) y
        -- unfold concatPaths
        -- nth_rw 1 [concatPaths.eq_def]

        -- rw [concatPaths.eq_def]
        -- simp [lookup_concat]
        -- sorry

    -- simp [concatPaths]

    -- simp [mkRun, concatPaths, Path.lookup]
    -- unfold concatPaths
    -- simp [thing2,thing]
    -- sorry
    -- sorry

  exact fe r r_fair


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
