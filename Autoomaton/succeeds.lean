import Autoomaton.Buchi
import Autoomaton.Path
variable {S : Type} {a : Automaton S} (r : Run a)

def stateSucceeds {S : Type} (a : Automaton S) (s2 s1 : S) : Prop :=
  ∃ (f i: S), a.I  i ∧ Relation.ReflTransGen a.R i s1 ∧ Relation.ReflTransGen a.R s1 f ∧ a.F f ∧ Relation.TransGen a.R f s2 -- ∧ f ≠ s1



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
    let f := Exists.choose yn                  -- the fair state in the nth block
    let inits := Exists.choose_spec yn           -- ∃ i, ...
    let spec := Exists.choose_spec inits         -- unpack the conjunction
    let hsn_to_f : Relation.ReflTransGen a.R (s n) f := spec.2.2.1
    let hf : a.F f := spec.2.2.2.1
    let SnF : Path a.R (s n) (f) := transrefl_to_path hsn_to_f
    let Pn := concatPaths s y n
    let k := Pn.length + SnF.length  -- this will be your fair index
    use k
    have t0 : n ≤ k := by
      simp only [Nat.reduceAdd, k, Pn, SnF]
      have := concatPaths_length s y n
      omega
    have t1 : (concatPaths s y (n + 1)).lookup k = f := by
      simp only [Nat.reduceAdd, concatPaths, k, Pn, SnF, f, lookup_concat_end, lookup_zero, lookup_concat]
    have t2 : (concatPaths s y k.succ).lookup k = (concatPaths s y (n + 1)).lookup k := by
      rcases factor_after_n (n := n + 1) (m := k.succ) (by omega) s y with ⟨ Tail, hTail ⟩
      rw [hTail, lookup_concat_left]
      simp only [Nat.reduceAdd, concatPaths, concat_len, add_lt_add_iff_left, lt_add_iff_pos_right,
        transgen_len, k, Pn, SnF, f]
    have t3 : (concatPaths s y k.succ).lookup k = f := by
      simp only [Nat.reduceAdd, Nat.succ_eq_add_one, t2, t1, k, Pn, f, SnF]
    simp only [t0, t3, hf, and_self, k, Pn, f, SnF]
