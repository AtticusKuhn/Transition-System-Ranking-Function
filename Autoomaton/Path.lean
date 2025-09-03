import Mathlib.Logic.Relation
import Mathlib.Tactic.Cases
import Autoomaton.Buchi
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Group.Defs





variable {S : Type}

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
  · exact ⟨ Path.tail (Path.refl) c, by simp only [Path.length, Nat.succ_eq_add_one,
    Nat.zero_add, Nat.lt_add_one]⟩
  · rcases ih with ⟨p1, p1ne ⟩
    exact ⟨ Path.tail p1 a'_to_b', by simp only [Path.length, Nat.succ_eq_add_one,
      Nat.zero_lt_succ]⟩


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



noncomputable def transgen_to_path3 {a b : S} {R : S → S → Prop} (p : Relation.TransGen R a b) : Path R a b :=
  Classical.choice (transgen_to_path' p)

noncomputable def transgen_to_path {a b : S} {R : S → S → Prop} (p : Relation.TransGen R a b) : Path R a b :=
  Exists.choose (transgen_to_path2 p)

noncomputable def transrefl_to_path {a b : S} {R : S → S → Prop} (p : Relation.ReflTransGen R a b) : Path R a b :=
  Classical.choice (transrefl_to_path' p)


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
          Nat.add_le_add_iff_right, hcond2, ih hle]
      · -- Boundary step: i.succ ≤ q.length.succ but not ≤ q.length ⇒ i = q.length
        have hlen_le_i : q.length ≤ i := by omega
        have hcond1 : ¬ q.length.succ ≤ i := by omega
        -- First lookup reduces to q.lookup i; second reduces to c.
        -- And q.lookup i = b because i ≥ q.length.
        have hqi : q.lookup i = b := lookup_ge_len (p := q) hlen_le_i
        simp only [Path.lookup, Path.length, Nat.succ_eq_add_one, ge_iff_le, hcond1, ↓reduceIte,
          hqi, Nat.add_le_add_iff_right, hlen_le_i, rel]


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
      simp only [trans_refl, Path.length, Nat.add_zero]
    | .tail p1_snoc h => by
      simp [trans_tail, Path.length, concat_len, Nat.succ_eq_add_one, add_assoc]


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
