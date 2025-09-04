import Mathlib.Logic.Relation
import Mathlib.Tactic.Cases
import Autoomaton.Buchi
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Group.Defs





variable {S : Type}

/-
An inductive type of finite paths under a binary relation `r`.

`Path r a b` represents a finite sequence of `r`-steps from start state `a` to end state `b`.

- `refl` is the empty path at `a`.
- `tail p h` extends a path `p : Path r a b` by one edge `h : r b c` to obtain `Path r a c`.
-/
inductive Path (r : S → S → Prop) (a : S) : S → Type
  | refl : Path r a a
  | tail {b c} : Path r a b → r b c → Path r a c

/-
Prepend one relation step to the front of a path.

Given `rel : R a b` and `p : Path R b c`, `Path.prepend rel p : Path R a c`.
-/
def Path.prepend {R : S → S → Prop} {a b  c : S} (rel : R a b) (p : Path R b c ) : Path R a c :=
  match p with
  | .refl => Path.tail Path.refl rel
  | .tail b_to_b' path_b_to_b' => Path.tail (Path.prepend rel b_to_b') path_b_to_b'


/-
Length (number of edges) of a path.

`Path.length p = n` counts the number of relation steps in `p`.
-/
def Path.length {R : S → S → Prop} {a b : S} (p : Path R a b) : Nat :=
  match p with
    | @Path.refl S R a => 0
    | @Path.tail S R a _ c snoc rel => (Path.length snoc).succ

/-
Indexing the vertex at position `i` along a path.

- `Path.lookup p 0 = a` (start state),
- for `i ≥ length p`, `Path.lookup p i = b` (end state),
- otherwise, it returns the intermediate vertex at index `i`.
-/
@[simp, reducible]
def Path.lookup {R : S → S → Prop} {a b : S} (p : Path R a b) (i : Nat) : S :=
  match p with
    | @Path.refl S R a => a
    | @Path.tail S R a _ c snoc rel =>
      if i >= p.length then c else snoc.lookup i

/-
A small example path over `<` on naturals: `1 < 3 < 5`.
-/
def test : Path ( · < · ) 1 5 :=
  Path.tail (c := 5) (Path.tail (c := 3) Path.refl (by omega)) (by omega)

/-
Return the list of vertices along the path, from start to end.

`Path.toList p = [a, ..., b]` and has length `= Path.length p + 1`.
-/
@[simp, reducible]
def Path.toList {R : S → S → Prop} {a b : S} (p : Path R a b) : List S:=
  match p with
    | @Path.refl S R a => [a]
    | @Path.tail S R a _ c snoc rel => snoc.toList ++ [c]

/-
Lookup via the list view of a path.

Equivalent to `Path.lookup`, using `List.getD` with default end state.
-/
@[simp, reducible]
def Path.lookup' {R : S → S → Prop} {a b : S} (p : Path R a b) (i : Nat) : S :=
    List.getD (Path.toList p) i b


/-
Convert a reflexive-transitive closure to a nonempty witness of a `Path`.

If `Relation.ReflTransGen R a b` then there exists a `Path R a b`.
-/
theorem transrefl_to_path_nonempty {a b : S} {R : S → S → Prop}
    (p : Relation.ReflTransGen R a b) : Nonempty (Path R a b) := by
  induction' p  with b c path_a_b R_b_c ih
  · exact ⟨ Path.refl⟩
  · exact ⟨ Path.tail (Classical.choice ih) R_b_c⟩

/-
Convert a transitive closure to a nonempty witness of a `Path`.

If `Relation.TransGen R a b` then there exists a `Path R a b`.
-/
theorem transgen_to_path_nonempty {a b : S} {R : S → S → Prop}
    (p : Relation.TransGen R a b) : Nonempty (Path R a b) := by
  induction' p  with b c a' b' a_to_a' a'_to_b' ih
  · exact ⟨ Path.tail (Path.refl) c⟩
  · exact ⟨ Path.tail (Classical.choice ih) a'_to_b'⟩


/-
Produce a path from a transitive closure with positive length.

From `Relation.TransGen R a b` we can obtain `∃ p, Path R a b` with `0 < length p`.
-/
theorem transgen_to_path_with_pos_length {a b : S} {R : S → S → Prop}
    (p : Relation.TransGen R a b) : ∃ ( p : Path R a b), 0 < p.length := by
  induction' p  with b c a' b' a_to_a' a'_to_b' ih
  · exact ⟨ Path.tail (Path.refl) c, by simp only [Path.length, Nat.succ_eq_add_one,
    Nat.zero_add, Nat.lt_add_one]⟩
  · rcases ih with ⟨p1, p1ne ⟩
    exact ⟨ Path.tail p1 a'_to_b', by simp only [Path.length, Nat.succ_eq_add_one,
      Nat.zero_lt_succ]⟩


/-
Concatenate two paths.

`Path.concat p1 p2 : Path R x z` concatenates `p1 : Path R x y` with `p2 : Path R y z`.
Associative, with `Path.refl` as right identity.
-/
@[trans]
def Path.concat {x y z : S} {R : S → S → Prop}
    (p1 : Path R x y) (p2 : Path R y z) : Path R x z :=
  match p1 with
    | .refl => p2
    | .tail p1_snoc h => Path.concat p1_snoc (Path.prepend h p2)

/-
Prepending commutes with concatenation on the left.

`Path.prepend h (p2 ⧺ p3) = (Path.prepend h p2) ⧺ p3`.
-/
lemma Path.prepend_concat {A B C D : S} {R : S → S → Prop}
    {x_to_y : R A B} {p2 : Path R B C} {p3 : Path R C D} :
    (Path.prepend x_to_y (Path.concat p2 p3)) =
    Path.concat (Path.prepend x_to_y p2) p3 := by
  induction' p2 with p q a_to_p p_to_q ih
  · simp only [Path.concat, Path.prepend]
  · simp only [Path.concat, ih, Path.prepend]


/-
Associativity of path concatenation: `(p1 ⧺ p2) ⧺ p3 = p1 ⧺ (p2 ⧺ p3)`.
-/
lemma Path.concat_assoc {A B C D : S} {R : S → S → Prop}
    {p1 : Path R A B} {p2 : Path R B C} {p3 : Path R C D} :
    Path.concat p1 (Path.concat p2 p3) =
    Path.concat (Path.concat p1 p2) p3 := by
  induction' p1 with x y a_to_x x_to_y ih
  · simp only [Path.concat]
  · simp only [Path.concat, Path.prepend_concat, ih]
/-
Concatenation distributes over a final `tail` step on the right.

`Path.concat p (Path.tail q h) = Path.tail (Path.concat p q) h`.
-/
theorem Path.concat_tail {x y z c : S} {R : S → S → Prop}
    (p : Path R x y) (snoc : Path R y z) (rel : R z c) :
    Path.concat p (Path.tail snoc rel) = Path.tail (Path.concat p snoc) rel := by
  induction p with
  | refl =>
      -- Path.concat Path.refl p2 = p2
      simp [Path.concat]
  | @tail x y b p ih =>
      -- Unfold Path.concat on the left, and Path.prepend on the intermediary step.
      -- Both sides normalize to the same expression after applying the IH.
      simp [Path.concat, Path.prepend, ih]

/-
Right identity of concatenation: `p ⧺ Path.refl = p`.
-/
theorem Path.concat_refl_right {x y : S} {R : S → S → Prop} (p : Path R x y) :
    Path.concat p Path.refl = p :=
  match p with
  | .refl => by
      simp [Path.concat]
  | .tail p1_snoc h => by
      -- Induction hypothesis for the prefix:
      have ih := Path.concat_refl_right (p := p1_snoc)
      -- Use concat_tail with snoc = Path.refl, then rewrite with ih
      simpa [Path.concat, Path.prepend, ih] using
        (Path.concat_tail (p := p1_snoc) (snoc := Path.refl) (rel := h))



/-
Noncomputably extract a path from a `TransGen` witness (via `Nonempty`).
-/
noncomputable def transgen_to_path3 {a b : S} {R : S → S → Prop}
    (p : Relation.TransGen R a b) : Path R a b :=
  Classical.choice (transgen_to_path_nonempty p)

/-
Noncomputably extract a path from a `TransGen` witness (with positive length).
-/
noncomputable def transgen_to_path {a b : S} {R : S → S → Prop}
    (p : Relation.TransGen R a b) : Path R a b :=
  Exists.choose (transgen_to_path_with_pos_length p)

/-
Noncomputably extract a path from a `ReflTransGen` witness.
-/
noncomputable def transrefl_to_path {a b : S} {R : S → S → Prop}
    (p : Relation.ReflTransGen R a b) : Path R a b :=
  Classical.choice (transrefl_to_path_nonempty p)


/-
Lookup past the end yields the final vertex.

If `length p ≤ i` then `lookup p i = b`.
-/
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

/-
Adjacent vertices are related along the path when inside bounds.

If `i.succ ≤ length p` then `R (lookup p i) (lookup p (i+1))`.
-/
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
          Nat.add_le_add_iff_right, hcond2, ih hle]
      · -- Boundary step: i.succ ≤ q.length.succ but not ≤ q.length ⇒ i = q.length
        have hlen_le_i : q.length ≤ i := by omega
        have hcond1 : ¬ q.length.succ ≤ i := by omega
        -- First lookup reduces to q.lookup i; second reduces to c.
        -- And q.lookup i = b because i ≥ q.length.
        have hqi : q.lookup i = b := lookup_ge_len (p := q) hlen_le_i
        simp only [Path.lookup, Path.length, Nat.succ_eq_add_one, ge_iff_le, hcond1, ↓reduceIte,
          hqi, Nat.add_le_add_iff_right, hlen_le_i, rel]


/-
Adjacent vertices are related for `i+1 < length` (strict form).
-/
theorem lookup_succ {R : S → S → Prop} {a b : S}
    (p : Path R a b) (i : Nat) (lt : i.succ < p.length) :
    R (p.lookup i) (p.lookup (i + 1)) :=
  lookup_succ_le p i (Nat.le_of_lt lt)



/-
The 0-th vertex of a path is its start: `lookup p 0 = a`.
-/
theorem lookup_zero {a b : S} {R : S → S → Prop} (p : Path R a b) : p.lookup 0 = a := by
  induction' p with x y a_to_x x_to_y  ih
  <;> simp only [Path.lookup, ge_iff_le, nonpos_iff_eq_zero]
  simp only [Path.length, Nat.succ_eq_add_one, Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
    ih]


/-
Length of concatenation: `length (p1 ⧺ p2) = length p1 + length p2`.
-/
theorem concat_len {a b c : S} {R : S → S → Prop}
    (p1 : Path R a b) (p2 : Path R b c) :
    (Path.concat p1 p2).length = p1.length + p2.length :=
    match p2 with
    | @Path.refl S R _ => by
      simp only [Path.concat_refl_right, Path.length, Nat.add_zero]
    | .tail p1_snoc h => by
      simp [Path.concat_tail, Path.length, concat_len, Nat.succ_eq_add_one, add_assoc]


/-
Lookup on the concatenation, right part: for `n`,
`lookup (p1 ⧺ p2) (length p1 + n) = lookup p2 n`.
-/
theorem lookup_concat {a b c :S} {R : S → S → Prop}
    {p1 : Path R a b} {p2 : Path R b c} {n : Nat} :
    (Path.concat p1 p2).lookup (p1.length + n) = p2.lookup n :=
  match p2 with
    | .refl => by
      simp only [Path.lookup, Path.concat_refl_right p1]
      apply lookup_ge_len
      omega
    | .tail p1_snoc h => by
      have y := lookup_concat (p1 := p1) (p2 := p1_snoc) (n := n)
      simp only [Path.concat_tail, Path.lookup, Path.length, concat_len, Nat.succ_eq_add_one,
        add_assoc, ge_iff_le, add_le_add_iff_left, y]


/-
Lookup on the concatenation, left part: for `n < length p1`,
`lookup (p1 ⧺ p2) n = lookup p1 n`.
-/
theorem lookup_concat_left {a b c : S} {R : S → S → Prop}
    {p1 : Path R a b} {p2 : Path R b c} {n : Nat}
    (le : n < p1.length) :
    (Path.concat p1 p2).lookup n = p1.lookup n := by
  induction' p1 with x y a_to_x x_to_y ih
  · simp only [Path.length, not_lt_zero'] at le
  · -- Inductive step: p1 = Path.tail a_to_x x_to_y
    simp only [Path.concat, Path.lookup, Path.length, Nat.succ_eq_add_one, ge_iff_le]
    -- Refine the bound to the prefix
    simp only [Path.length, Nat.succ_eq_add_one] at le
    have hnot : ¬ (a_to_x.length + 1 ≤ n) := by omega
    simp [hnot]
    -- Now goal is (Path.concat a_to_x (Path.prepend x_to_y p2)).lookup n = a_to_x.lookup n
    by_cases hEq : n = a_to_x.length
    · -- Boundary case: n = length of the prefix
      subst hEq
      -- Compute the left side via lookup_concat at offset 0 and lookup_zero
      have hL :
          (Path.concat a_to_x (Path.prepend x_to_y p2)).lookup (a_to_x.length) = x := by
        have := lookup_concat (p1 := a_to_x) (p2 := Path.prepend x_to_y p2) (n := 0)
        simpa [Nat.add_zero, lookup_zero] using this
      -- Compute the right side: at length, lookup is the endpoint
      have hR : a_to_x.lookup a_to_x.length = x :=
        lookup_ge_len (p := a_to_x) (i := a_to_x.length) (le_rfl)
      simpa [hR] using hL
    · -- Strictly inside the prefix: n < a_to_x.length
      have hlt : n < a_to_x.length := by omega
      simpa using ih (p2 := Path.prepend x_to_y p2) hlt
