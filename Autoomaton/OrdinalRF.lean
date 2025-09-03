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
    | @Path.tail S R a _ c snoc rel => (Path.length snoc).succ

@[simp, reducible]
def Path.lookup {R : S → S → Prop} {a b : S} (p : Path R a b) (i : Nat) : S :=
  match p with
    | @Path.refl S R a => a
    | @Path.tail S R a _ c snoc rel =>
      if i >= p.length then c else snoc.lookup i

def test : Path ( · < · ) 1 5 := Path.tail (c := 5) (
    Path.tail (c := 3)
      Path.refl (by omega)) (by omega)

@[simp, reducible]
def Path.toList {R : S → S → Prop} {a b : S} (p : Path R a b) : List S:=
  match p with
    | @Path.refl S R a => [a]
    | @Path.tail S R a _ c snoc rel => snoc.toList ++ [c]

@[simp, reducible]
def Path.lookup' {R : S → S → Prop} {a b : S} (p : Path R a b) (i : Nat) : S :=
    List.getD (Path.toList p) i b


theorem transrefl_to_path' {a b : S} {R : S → S → Prop} (p : Relation.ReflTransGen R a b) : Nonempty (Path R a b) := by
  induction' p  with b c path_a_b R_b_c ih
  · exact ⟨ Path.refl⟩
  · exact ⟨ Path.tail (Classical.choice ih) R_b_c⟩

theorem transgen_to_path' {a b : S} {R : S → S → Prop} (p : Relation.TransGen R a b) : Nonempty (Path R a b) := by
  induction' p  with b c a' b' a_to_a' a'_to_b' ih
  · exact ⟨ Path.tail (Path.refl) c⟩
  · exact ⟨ Path.tail (Classical.choice ih) a'_to_b'⟩


theorem transgen_to_path2 {a b : S} {R : S → S → Prop} (p : Relation.TransGen R a b) : ∃ ( p : Path R a b), 0 < p.length := by
  induction' p  with b c a' b' a_to_a' a'_to_b' ih
  · exact ⟨ Path.tail (Path.refl) c, by simp only [Path.length, Nat.succ_eq_add_one, zero_add,
    gt_iff_lt, zero_lt_one]⟩
  · rcases ih with ⟨p1, p1ne ⟩
    exact ⟨ Path.tail p1 a'_to_b', by simp only [Path.length, Nat.succ_eq_add_one, gt_iff_lt,
      lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]⟩


@[trans]
def path_trans {x y z : S} {R : S → S → Prop} (p1 : Path R x y) (p2 : Path R y z) : Path R x z :=
  match p1 with
    | .refl => p2
    | .tail p1_snoc h => path_trans p1_snoc (Path.head h p2)

lemma head_trans {A B C D : S} {R : S → S → Prop} {x_to_y : R A B} {p2 : Path R B C} {p3 : Path R C D}: (Path.head x_to_y (path_trans p2 p3)) = path_trans (Path.head x_to_y p2) p3 := by
  induction' p2 with p q a_to_p p_to_q ih
  · simp only [path_trans, Path.head]
  · simp only [path_trans, ih, Path.head]


lemma path_assoc {A B C D : S} {R : S → S → Prop} {p1 : Path R A B} {p2 : Path R B C} {p3 : Path R C D}: path_trans p1 (path_trans p2 p3) = path_trans (path_trans p1 p2) p3 := by
  induction' p1 with x y a_to_x x_to_y ih
  · simp only [path_trans]
  · simp only [path_trans, head_trans, ih]
theorem trans_tail {x y z c : S} {R : S → S → Prop}
    (p : Path R x y) (snoc : Path R y z) (rel : R z c) :
    path_trans p (Path.tail snoc rel) = Path.tail (path_trans p snoc) rel := by
  induction p with
  | refl =>
      -- path_trans Path.refl p2 = p2
      simp [path_trans]
  | @tail x y b p ih =>
      -- Unfold path_trans on the left, and Path.head on the intermediary “head” step.
      -- Both sides normalize to the same expression after applying the IH.
      simp [path_trans, Path.head, ih]

theorem trans_refl {x y : S} {R : S → S → Prop} (p : Path R x y) :
    path_trans p Path.refl = p :=
  match p with
  | .refl => by
      simp [path_trans]
  | .tail p1_snoc h => by
      -- Induction hypothesis for the prefix:
      have ih := trans_refl (p := p1_snoc)
      -- Use trans_tail with snoc = Path.refl, then rewrite with ih
      simpa [path_trans, Path.head, ih] using
        (trans_tail (p := p1_snoc) (snoc := Path.refl) (rel := h))



def stateSucceeds {S : Type} (a : Automaton S) (s2 s1 : S) : Prop :=
  ∃ (f i: S), a.I  i ∧ Relation.ReflTransGen a.R i s1 ∧ Relation.ReflTransGen a.R s1 f ∧ a.F f ∧ Relation.TransGen a.R f s2 -- ∧ f ≠ s1

def stateSucceeds4 {S : Type} (a : Automaton S) (s2 s1 : S) : Type :=
  Σ (f i: S), Inhabited (a.I  i) ×  Path a.R i s1 × Path a.R s1 f × Inhabited (a.F f) × Path a.R f s2 -- ∧ f ≠ s1


def stateSucceeds3 {S : Type} (a : Automaton S) (s2 s1 : S) : Prop :=
  ∃ (r : Run a), ∃ (i j k : Nat), i ≤ j ∧ j < k ∧ s1 = r.f i ∧ s2 = r.f k ∧ a.F (r.f j)




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


theorem succeeds_concat4 { S : Type} (s1 s2 n : S)  (a : Automaton S)  (s1_r_s2 : a.R s1 s2) (n_suc_s2 : stateSucceeds a n s2) (s1_reach : State.IsReachable (a := a) s1) : stateSucceeds a n s1 := by
  rcases n_suc_s2 with ⟨ f, _i, _i_init, i_to_s2, rt, f_fair, tg ⟩
  rcases s1_reach with ⟨ i, i_to_s1, i_init⟩
  use f, i
  simp only [i_init, i_to_s1, f_fair, tg, and_self, and_true, true_and]
  rw [Relation.ReflTransGen.cases_head_iff]
  right
  use s2



noncomputable def transgen_to_path3 {a b : S} {R : S → S → Prop} (p : Relation.TransGen R a b) : Path R a b :=
  Classical.choice (transgen_to_path' p)

noncomputable def transgen_to_path {a b : S} {R : S → S → Prop} (p : Relation.TransGen R a b) : Path R a b :=
  Exists.choose (transgen_to_path2 p)

noncomputable def transrefl_to_path {a b : S} {R : S → S → Prop} (p : Relation.ReflTransGen R a b) : Path R a b :=
  Classical.choice (transrefl_to_path' p)

noncomputable def concatPaths (s : ℕ → S) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)) (i : Nat) : Path a.R (Exists.choose (Exists.choose_spec (y 0))) (s i) :=
  match i with
    | 0 =>
      transrefl_to_path (Exists.choose_spec (Exists.choose_spec (y 0))).2.1
    | i + 1 =>
      let k1 := (Exists.choose_spec (Exists.choose_spec (y (i))))
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
  Path.lookup (concatPaths s y i.succ) i


-- A helper: beyond the length, lookup is the last vertex.
lemma lookup_ge_len {R : S → S → Prop} {a b : S}
    (p : Path R a b) {i : Nat} (h : p.length ≤ i) :
    p.lookup i = b := by
  induction p with
  | refl =>
      simp only [Path.lookup]
  | tail q rel ih =>
      have : q.length.succ ≤ i := by
        simpa only [Path.length, Nat.succ_eq_add_one] using h
      simp only [Path.lookup, Path.length, Nat.succ_eq_add_one, ge_iff_le, this, ↓reduceIte]

-- The natural adjacency lemma: if i.succ ≤ p.length, the i-th and (i+1)-th states are related.
lemma lookup_succ_le {R : S → S → Prop} {a b : S}
    (p : Path R a b) (i : Nat) (h : i.succ ≤ p.length) :
    R (p.lookup i) (p.lookup (i + 1)) := by
  induction p with
  | refl =>
      cases h  -- impossible: 0 < 0
  | tail q rel ih =>
      rename_i b a
      -- p = tail q rel; p.length = q.length + 1
      have h' : i.succ ≤ q.length.succ := by
        simpa only [Nat.succ_eq_add_one, add_le_add_iff_right, Path.length] using h
      by_cases hle : i.succ ≤ q.length
      · -- We are strictly inside the prefix q
        have hcond1 : ¬ q.length.succ ≤ i := by omega
        have hcond2 : ¬ q.length ≤ i := by omega
        -- Both lookups reduce to q.lookup …
        simp only [Path.lookup, Path.length, Nat.succ_eq_add_one, ge_iff_le, hcond1, ↓reduceIte,
          add_le_add_iff_right, hcond2, ih hle]
      · -- Boundary step: i.succ ≤ q.length.succ but not ≤ q.length ⇒ i = q.length
        have hlen_le_i : q.length ≤ i := by omega
        have hcond1 : ¬ q.length.succ ≤ i := by omega
        -- First lookup reduces to q.lookup i; second reduces to c.
        -- And q.lookup i = b because i ≥ q.length.
        have hqi : q.lookup i = b := lookup_ge_len (p := q) hlen_le_i
        simp only [Path.lookup, Path.length, Nat.succ_eq_add_one, ge_iff_le, hcond1, ↓reduceIte,
          hqi, add_le_add_iff_right, hlen_le_i, rel]


theorem lookup_succ {R : S → S → Prop} {a b : S}
    (p : Path R a b) (i : Nat) (lt : i.succ < p.length) :
    R (p.lookup i) (p.lookup (i + 1)) :=
  lookup_succ_le p i (Nat.le_of_lt lt)



theorem lookup_zero {a b : S} {R : S → S → Prop} (p : Path R a b) : p.lookup 0 = a := by
  induction' p with x y a_to_x x_to_y  ih
  <;> simp only [Path.lookup, ge_iff_le, nonpos_iff_eq_zero]
  simp only [Path.length, Nat.succ_eq_add_one, Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
    ih]


theorem concat_len {a b c : S} {R : S → S → Prop} (p1 : Path R a b) (p2 : Path R b c) : (path_trans p1 p2).length = p1.length + p2.length :=
    match p2 with
    | @Path.refl S R _ => by
      simp only [trans_refl, Path.length, add_zero]
    | .tail p1_snoc h => by
      simp only [trans_tail, Path.length, concat_len, Nat.succ_eq_add_one, add_assoc,
        Nat.add_left_cancel_iff]


theorem lookup_concat {a b c :S} {R : S → S → Prop} {p1 : Path R a b} {p2 : Path R b c} {n : Nat} : (path_trans p1 p2).lookup (p1.length + n) = p2.lookup n :=
  match p2 with
    | .refl => by
      simp only [Path.lookup, trans_refl p1]
      apply lookup_ge_len
      omega
    | .tail p1_snoc h => by
      have y := lookup_concat (p1 := p1) (p2 := p1_snoc) (n := n)
      -- have t : (if 1 + (p1.length + p1_snoc.length) ≤ p1.length + n) ↔ (if 1 + (p1.length + p1_snoc.length) ≤ p1.length + n) := by sorry
      simp only [trans_tail, Path.lookup, Path.length, concat_len, Nat.succ_eq_add_one, add_assoc,
        ge_iff_le, add_le_add_iff_left, y]


theorem lookup_concat_2 {a b c : S} {R : S → S → Prop}
    {p1 : Path R a b} {p2 : Path R b c} {n : Nat}
    (le : n < p1.length) :
    (path_trans p1 p2).lookup n = p1.lookup n := by
  induction' p1 with x y a_to_x x_to_y ih
  · simp only [Path.length, not_lt_zero'] at le
  · -- Inductive step: p1 = Path.tail a_to_x x_to_y
    simp only [path_trans, Path.lookup, Path.length, Nat.succ_eq_add_one, ge_iff_le]
    -- Refine the bound to the prefix
    simp only [Path.length, Nat.succ_eq_add_one] at le
    have hnot : ¬ (a_to_x.length + 1 ≤ n) := by omega
    simp [hnot]
    -- Now goal is (path_trans a_to_x (Path.head x_to_y p2)).lookup n = a_to_x.lookup n
    by_cases hEq : n = a_to_x.length
    · -- Boundary case: n = length of the prefix
      subst hEq
      -- Compute the left side via lookup_concat at offset 0 and lookup_zero
      have hL :
          (path_trans a_to_x (Path.head x_to_y p2)).lookup (a_to_x.length) = x := by
        have := lookup_concat (p1 := a_to_x) (p2 := Path.head x_to_y p2) (n := 0)
        simpa [Nat.add_zero, lookup_zero] using this
      -- Compute the right side: at length, lookup is the endpoint
      have hR : a_to_x.lookup a_to_x.length = x :=
        lookup_ge_len (p := a_to_x) (i := a_to_x.length) (le_rfl)
      simpa [hR] using hL
    · -- Strictly inside the prefix: n < a_to_x.length
      have hlt : n < a_to_x.length := by omega
      simpa using ih (p2 := Path.head x_to_y p2) hlt



lemma factor_after_n {n m : ℕ} (hm : n ≤ m)  (s : Nat → S) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)) :
  ∃ Tail, concatPaths s y m = path_trans (concatPaths s y n) (Tail) := by
  induction' hm with m hm ih
  · use Path.refl
    symm
    exact trans_refl (concatPaths s y n)
  · rcases ih with ⟨Tail, hTail⟩
    let k1 := (Exists.choose_spec (Exists.choose_spec (y m)))
    use path_trans Tail (path_trans (transrefl_to_path k1.2.2.1) (transgen_to_path k1.2.2.2.2))
    rw [concatPaths]
    nth_rw 2 [path_assoc]
    rw [← hTail]

theorem transgen_len {A B :S} {R : S → S → Prop} {p : Relation.TransGen R A B} : 0 < (transgen_to_path p).length :=
  Exists.choose_spec (transgen_to_path2 p)

theorem concatPaths_length (s : Nat → S) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)) (n : Nat) : n ≤ (concatPaths s y n).length := by
  induction' n with n ih
  · simp only [Nat.reduceAdd, concatPaths, zero_le]
  · simp only [Nat.reduceAdd, concatPaths, concat_len]
    have := transgen_len (p := (concatPaths._proof_7 s y n))
    omega

theorem concat_lookup (s : Nat → S) (n : Nat) (y : ∀ (n : ℕ), stateSucceeds a (s (n + 1)) (s n)): (concatPaths s y (n + 1)).lookup n = (concatPaths s y (n + 2)).lookup n := by
  rcases factor_after_n (n := n + 1) (m := n + 2) (by omega) s y  with ⟨ Tail, hTail ⟩
  rw [hTail, lookup_concat_2]
  have := concatPaths_length s y (n + 1)
  omega

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
      rw [hTail, lookup_concat_2]
      simp only [Nat.reduceAdd, concatPaths, concat_len, add_lt_add_iff_left, lt_add_iff_pos_right,
        transgen_len, k, Pn, SnF, f]
    have t3 : (concatPaths s y k.succ).lookup k = f := by
      simp only [Nat.reduceAdd, Nat.succ_eq_add_one, t2, t1, k, Pn, f, SnF]
    simp only [t0, t3, hf, and_self, k, Pn, f, SnF]

theorem succeeds_wf (a : Automaton S) (fe : a.IsFairEmpty) : WellFounded (stateSucceeds a) := by
  simp only [WellFounded.wellFounded_iff_no_descending_seq]
  by_contra c
  simp only [not_isEmpty_iff, nonempty_subtype] at c
  rcases c with ⟨s, y⟩
  exact fe (vardiRun s y) (vardiRun_fair s y)


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



noncomputable def completeness (fe : a.IsFairEmpty) : (OrdinalRankingFunction.{0} a) := ⟨@IsWellFounded.rank S (stateSucceeds a) (n a fe), fun s1 s2  rel => by
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

--info: 'completeness' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms completeness
