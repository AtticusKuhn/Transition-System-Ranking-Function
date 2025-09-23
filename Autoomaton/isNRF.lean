import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
-- import Mathlib.Init.Logic


set_option linter.unnecessarySimpa false
-- import Mathlib.Algebra.BigOperators.Ring

def signInt (x : Int) : Int := if x > 0 then 1 else -1
def signMap {n : Nat} (vec : Fin n → Int) : Fin n → Int := signInt ∘ vec
def reluMap {n : Nat} (vec : Fin n → Int) : Fin n → Int := fun i => max 0 (vec i)
set_option linter.unusedVariables false

section helpers
open Finset

variable {w : Nat}

lemma sum_if_singleton (i : Fin w) (f : Fin w → Int) :
  ∑ j, (if j = i then f j else 0) = f i := by
  induction' w with w ih
  <;> simp
  exact Fin.elim0 i

lemma sum_if_singleton' (i : Fin w) (f : Fin w → Int) :
  ∑ j, (if i = j then f j else 0) = f i := by
  simpa [eq_comm] using sum_if_singleton (i := i) (f := f)

lemma sum_if_one_neg_one_eq (p : Fin w → Prop) [DecidablePred p] :
  (∑ i, (if p i then (1 : Int) else -1))
    = (2 : Int) * ((Finset.univ.filter p).card : Int) - (w : Int) := by
  have hpoint { b : Prop} [Decidable b] :  (if b then (1 : Int) else -1) = (if b then (2 : Int) else 0) - 1 := by
    by_cases b <;> simp [*, sub_eq_add_neg]
  have h1 : (∑ i, (if p i then (1 : Int) else -1))
      = (∑ i, (if p i then (2 : Int) else 0)) - (∑ (i : Fin w), (1 : Int)) := by
    simp only [Int.reduceNeg, hpoint, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have h2 : (∑ i, (if p i then (2 : Int) else 0))
      = ((Finset.univ.filter p).card : Int) * 2 := by
      have hsum :
          (∑ i, (if p i then (2 : Int) else 0))
            = (∑ i ∈ (Finset.univ.filter p), (2 : Int)) := by
        -- Standard filter/sum lemma
        simpa using
          (Finset.sum_filter (s := (Finset.univ : Finset (Fin w))) (p := p)
            (f := fun _ : Fin w => (2 : Int))).symm
      -- Turn the filtered sum of a constant into card * constant
      simpa [hsum, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h3 : (∑ (i : Fin w), (1 : Int)) = (w : Int) := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_one, Fintype.card_fin]

  simp [h1, h2, h3, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]

end helpers

section sum_bounds
open Finset

variable {w : Nat}

-- If at least one index fails predicate `p`, then the sum of ±1 over `p`
-- is bounded by `w - 1`.
lemma sum_if_one_neg_one_le_sub_one
    (p : Fin w → Prop) [DecidablePred p]
    (hnotall : ∃ j : Fin w, ¬ p j) :
    (∑ i, (if p i then (1 : Int) else -1)) ≤ (w : Int) - 1 := by
  -- Express the sum via the filtered-card identity
  have hs : (∑ i, (if p i then (1 : Int) else -1))
      = (2 : Int) * ((Finset.univ.filter p).card : Int) - (w : Int) :=
    sum_if_one_neg_one_eq (w := w) (p := p)
  rcases hnotall with ⟨j, hj⟩
  -- Show `|S| ≤ w - 1` by embedding S into `univ.erase j`
  have hsubset : (Finset.univ.filter p) ⊆ (Finset.univ.erase j) := by
    intro i hi
    have hip : p i := by simpa [Finset.mem_filter] using hi
    have hij : i ≠ j := by
      intro h; apply hj; simpa [h] using hip
    simpa [Finset.mem_erase, hij]
  have hcard_le_nat : (Finset.univ.filter p).card ≤ (Finset.univ.erase j).card :=
    Finset.card_le_card hsubset
  have hcard_erase : (Finset.univ.erase j).card = w - 1 := by
    have hjmem : j ∈ (Finset.univ : Finset (Fin w)) := by simp
    simpa [Fintype.card_fin]
      using (Finset.card_erase_of_mem (s := (Finset.univ : Finset (Fin w))) (a := j) hjmem)
  have hScard_le : ((Finset.univ.filter p).card : Int) ≤ (w : Int) - 1 := by
    have : (Finset.univ.filter p).card ≤ w - 1 := by simpa [hcard_erase] using hcard_le_nat
    -- Cast to ℤ using `Int.ofNat_sub`; requires `1 ≤ w` since `j : Fin w`.
    have hwpos : 0 < w := (Fin.pos_iff_nonempty.mpr ⟨j⟩)
    have hw1 : 1 ≤ w := Nat.succ_le_of_lt hwpos
    have hcast : ((Finset.univ.filter p).card : Int) ≤ ((w - 1 : Nat) : Int) := by exact_mod_cast this
    simpa [Int.ofNat_sub hw1] using hcast
  -- Derive the target bound on the sum via monotonicity and simple arithmetic
  have hmul : (2 : Int) * ((Finset.univ.filter p).card : Int)
              ≤ (2 : Int) * ((w : Int) - 1) := by
    -- Rewrite 2 * t as t + t and add the inequalities
    simpa [two_mul] using add_le_add hScard_le hScard_le
  have hstep : (2 : Int) * ((w : Int) - 1) - (w : Int) ≤ (w : Int) - 1 := by
    -- 2*(w-1) - w = w - 2 ≤ w - 1
    have : (w : Int) - 2 ≤ (w : Int) - 1 := by
      exact sub_le_sub_left (by decide : (1 : Int) ≤ 2) (w : Int)
    simpa [two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have : (2 : Int) * ((Finset.univ.filter p).card : Int) - (w : Int) ≤ (w : Int) - 1 := by
    exact le_trans (by simpa using sub_le_sub_right hmul (w : Int)) hstep
  simpa [hs]

end sum_bounds

/-- A compact, proof-oriented inductive definition capturing the closure of NRF outputs
under products and sign-affine layers. This is useful for compositional proofs.
def
The base objects are projections from products; `layer` composes with a single
sign-affine map; and `pair` combines two NRFs pointwise into a product. -/
-- Append two output vectors into a single `Fin (n+p)` vector
def appendVec {n p : Nat} (v1 : Fin n → Int) (v2 : Fin p → Int) : Fin (n + p) → Int :=
  fun i => Fin.addCases (fun i0 : Fin n => v1 i0) (fun i1 : Fin p => v2 i1) i

inductive isNRF : {m n: Nat} → ((Fin m → Int) → (Fin n → Int)) → Prop where
  | id : isNRF (fun x => x)
  | layer {m n k : Nat}
      (W : Matrix (Fin m) (Fin n) Int) (b : Fin m → Int)
      {f : (Fin k → Int) → (Fin n → Int)}
      (hf : isNRF f)
      : isNRF (fun x => signMap ((Matrix.mulVec W (f x)) + b))
  | pair {m n p : Nat}
      {f : (Fin m → Int) → (Fin n → Int)} {g : (Fin m → Int) → (Fin p → Int)}
      (hf : isNRF f) (hg : isNRF g) :
      isNRF (fun x => appendVec (f x) (g x))



def g (a : Int) (x : Fin 1 → Int) : Fin 1 → Int := fun i => if (x i) = a then 1 else -1

-- \operatorname{sign}(2\operatorname{sign}(2*x-2a+1)+2\operatorname{sign}(-2*x+2*a+1)-3)
def g'  (a : Int) (x : Fin 1 → Int) : Fin 1 → Int  :=  fun i => signInt (signInt (2 * (x i) - 2 * a + 1) + signInt (2 * a - 2 * (x i)  + 1) - 1)

def g3   (a : Int) (x : Fin 1 → Int) : Fin 2 → Int  :=
  -- First layer producing s₁ = sign(2x - 2a + 1) and s₂ = sign(-2x + 2a + 1)
  let W₁ : Matrix (Fin 2) (Fin 1) Int := fun i _ => if i = 0 then 2 else -2
  let b₁ : Fin 2 → Int := fun i => if i = 0 then (-2 * a + 1) else (2 * a + 1)
  signMap ((Matrix.mulVec W₁ x) + b₁)

def g2  (a : Int) (x : Fin 1 → Int) : Fin 1 → Int  :=
  -- Second layer producing sign(s₁ + s₂ - 1)
  let W₂ : Matrix (Fin 1) (Fin 2) Int := fun _ _ => 1
  let b₂ : Fin 1 → Int := fun _ => -1
  signMap ((Matrix.mulVec W₂ (g3 a x)) + b₂)

lemma g3_zero (a : Int) (x : Fin 1 → Int) :
    g3 a x 0 = signInt (2 * x 0 - 2 * a + 1) := by
  -- compute the first coordinate of the first layer (i = 0)
  have h0 : (0 : Fin 2) = 0 := rfl
  simp [g3, signMap, Matrix.mulVec, dotProduct, Fin.sum_univ_one, h0,
        if_pos rfl, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm]

lemma g3_one (a : Int) (x : Fin 1 → Int) :
    g3 a x 1 = signInt (2 * a - 2 * x 0 + 1) := by
  -- compute the second coordinate of the first layer (i = 1)
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp [g3, signMap, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
        if_neg h10, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm]

theorem if_push  {A : Type} {x a b : A} {c : Prop} [Decidable c]: (x = if c then a else b) ↔ ((x = a ∧ c) ∨ (x = b ∧ !c)) := by
  split
  <;> (rename_i h ; simp [h])

theorem if_push_2  {A : Type} {x a b : A} {c : Prop} [Decidable c]: ((if c then a else b) = x) ↔ ((x = a ∧ c) ∨ (x = b ∧ !c)) := by
  split
  <;> (rename_i h ; simp [h, eq_comm])

theorem if_add {c1 c2 : Prop} [Decidable c1] [Decidable c2] : ((if c1 then 1 else (-1 : Int)) + if c2 then 1 else (-1 : Int)) ≤ 1 ↔ ¬ c1 ∨ ¬ c2 := by
  by_cases isC1 : c1
  <;> by_cases isC2 : c2
  <;> simp [isC1, isC2]

-- Sum of two ±1's exceeds 1 iff both predicates are true
lemma one_lt_sum_if_iff (c1 c2 : Prop) [Decidable c1] [Decidable c2] :
    (1 : Int) < ((if c1 then 1 else -1) + (if c2 then 1 else -1)) ↔ (c1 ∧ c2) := by
  by_cases isC1 : c1
  <;> by_cases isC2 : c2
  <;> simp [isC1, isC2]

theorem g_eq : g = g' := by
  funext a x i
  simp only [g, Int.reduceNeg, g', signInt, gt_iff_lt, Int.sub_pos, if_push, ite_eq_left_iff,
    reduceCtorEq, imp_false, Decidable.not_not, ite_eq_right_iff, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, not_lt]
  by_cases c : x = a
  <;> try simp [c, sub_self, zero_add, Int.reduceLT, ↓reduceIte, Int.reduceAdd, and_self,
    not_true_eq_false, Int.reduceLE, or_false]
  simp only [Int.reduceNeg, if_add, not_lt]
  omega


theorem nrf_g2 {a : Int}: isNRF (g2 a) := by
  apply isNRF.layer
  apply isNRF.layer
  exact isNRF.id



theorem g_eq_2 : g2 = g' := by
  funext a x i
  -- `Fin 1` has a single index; replace `i` by `0` to simplify coordinates
  have hi : i = 0 := Subsingleton.elim i 0
  -- compute both layers explicitly using the lemmas for g3
  simp only [g2, signMap, g3, Fin.isValue, Int.reduceNeg, neg_mul, add_comm, hi,
    Function.comp_apply, Pi.add_apply, Matrix.mulVec, dotProduct, Finset.univ_unique,
    Fin.default_eq_zero, ite_mul, Finset.sum_ite_irrel, Finset.sum_singleton,
    Finset.sum_neg_distrib, one_mul, Fin.sum_univ_two, ↓reduceIte, add_assoc, Fin.one_eq_zero_iff,
    OfNat.ofNat_ne_one, g', sub_eq_add_neg]

theorem nrf_g' {a : Int}: isNRF (g' a) := by
  -- We already built `g2 a` via two sign-affine layers; now use the
  -- pointwise equality `g2 = g'` to conclude.
  have h₂ : isNRF (g2 a) := nrf_g2 (a := a)
  have : g2 a = g' a := by
    simpa using congrArg (fun f => f a) g_eq_2
  simpa [this] using h₂

theorem nrf_g {a : Int} : isNRF (g a) := by
  have h := congrArg (fun f => f a) g_eq
  simpa [h] using nrf_g' (a := a)



#print axioms nrf_g

def const (n : Int) : Fin 1 → Int := fun _ => n

def f {w : Nat} (a : Fin w → Int) (x : Fin w → Int) : Fin 1 → Int := fun _ => if x = a then 1 else -1

def f2 {w : Nat} (a : Fin w → Int) (x : Fin w → Int) : Fin 1 → Int := signMap ((∑ i, g (a i) (const (x i))) - (const ((w : Int) - 1)))

theorem f_eq_f2 {w : Nat} : (f (w := w)) = f2 := by
  funext a x i
  simp only [f, Int.reduceNeg, f2]
  by_cases c : x = a
  · simp only [c, ↓reduceIte, signMap, Function.comp_apply, signInt, Pi.sub_apply,
    Finset.sum_apply, g, const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, sub_sub_cancel, gt_iff_lt, Int.reduceLT]
  · simp only [c, ↓reduceIte, Int.reduceNeg, signMap, Function.comp_apply, signInt, Pi.sub_apply, Finset.sum_apply, Int.sub_pos, right_eq_ite_iff, reduceCtorEq, imp_false, not_lt]
    simp only [const, Int.reduceNeg]
    -- Define the set of equal coordinates and use the helper bound
    let p : Fin w → Prop := fun i => x i = a i
    have hxne : ∃ j : Fin w, ¬ p j := by
      by_contra h
      simp only [not_exists, Decidable.not_not, p] at h
      apply c; funext i; exact h i
    exact sum_if_one_neg_one_le_sub_one (w := w) (p := p) hxne

#print axioms f_eq_f2

-- Shared layer definitions for `f4`
def W1 {w : Nat} (a : Fin w → Int) : Matrix (Fin (w + w)) (Fin w) Int :=
  fun i j =>
    Fin.addCases
      (fun i0 : Fin w => if j = i0 then (2 : Int) else 0)
      (fun i1 : Fin w => if j = i1 then (-2 : Int) else 0)
      i

def b1 {w : Nat} (a : Fin w → Int) : Fin (w + w) → Int :=
  fun i =>
    Fin.addCases
      (fun i0 : Fin w => (-2) * a i0 + 1)
      (fun i1 : Fin w => (2) * a i1 + 1)
      i

def W2 {w : Nat} : Matrix (Fin w) (Fin (w + w)) Int :=
  fun j r =>
    (if r = j.castAdd w then (1 : Int) else 0) +
    (if r = j.addNat w then (1 : Int) else 0)

def b2 {w : Nat} : Fin w → Int := fun _ => (-1 : Int)

def s1 {w : Nat} (a : Fin w → Int) (x : Fin w → Int) : Fin (w + w) → Int :=
  signMap ((Matrix.mulVec (W1 a) x) + (b1 a))

def f4 {w : Nat} (a : Fin w → Int) (x : Fin w → Int) : Fin w → Int :=
  signMap ((Matrix.mulVec (W2 (w := w)) (s1 a x)) + (b2 (w := w)))

-- Coordinate computations for the two layers inside `f4`
lemma s1_left {w : Nat} (a : Fin w → Int) (x : Fin w → Int) (i : Fin w) :
    s1 a x (i.castAdd w) = signInt (2 * x i - 2 * a i + 1) := by
  simp [s1, W1, b1, signMap, Matrix.mulVec, dotProduct, Fin.addCases,
        ite_mul, mul_ite, sum_if_singleton' (i := i), sub_eq_add_neg,
        two_mul, mul_add, add_comm, add_left_comm, add_assoc]

lemma s1_right {w : Nat} (a : Fin w → Int) (x : Fin w → Int) (i : Fin w) :
    s1 a x (i.addNat w) = signInt (2 * a i - 2 * x i + 1) := by
  simp [s1, W1, b1, signMap, Matrix.mulVec, dotProduct, Fin.addCases,
        ite_mul, mul_ite, sum_if_singleton' (i := i), sub_eq_add_neg,
        two_mul, mul_add, add_comm, add_left_comm, add_assoc]

lemma mulW2_coord {w : Nat} (s : Fin (w + w) → Int) (i : Fin w) :
    (Matrix.mulVec (W2 (w := w)) s) i = s (i.addNat w) + s (i.castAdd w) := by
  simp [W2, Matrix.mulVec, dotProduct, ite_mul, mul_ite, mul_add, add_mul,
        Finset.sum_add_distrib, sum_if_singleton (i := i.addNat w),
        sum_if_singleton (i := i.castAdd w), add_comm, add_left_comm, add_assoc]

lemma f4_coord_closed {w : Nat} (a : Fin w → Int) (x : Fin w → Int) (i : Fin w) :
    (f4 a x) i
      = signInt ((signInt (2 * x i - 2 * a i + 1)) +
                 (signInt (2 * a i - 2 * x i + 1)) - 1) := by
  have hf4i : (f4 a x) i = signInt (((Matrix.mulVec (W2 (w := w)) (s1 a x)) + (b2 (w := w))) i) := by
    simp [f4, signMap, Pi.add_apply]
  have hsumW₂ : (Matrix.mulVec (W2 (w := w)) (s1 a x)) i
                  = (s1 a x) (i.addNat w) + (s1 a x) (i.castAdd w) := by
    simpa using mulW2_coord (w := w) (s := s1 a x) i
  have hb₂ : (b2 (w := w)) i = -1 := rfl
  have hx : (s1 a x) (i.addNat w) = signInt (2 * a i - 2 * x i + 1) := by
    simpa using s1_right (w := w) a x i
  have hy : (s1 a x) (i.castAdd w) = signInt (2 * x i - 2 * a i + 1) := by
    simpa using s1_left (w := w) a x i
  simpa [hf4i, hsumW₂, hb₂, hx, hy, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

def f3 {w : Nat} (a : Fin w → Int) (x : Fin w → Int) : Fin 1 → Int :=
  -- Single affine layer summing all coordinates of f4 a x and subtracting (w - 1)
  -- before applying the sign nonlinearity.
  let W : Matrix (Fin 1) (Fin w) Int := fun _ _ => 1
  let b : Fin 1 → Int := fun _ => -((w : Int) - 1)
  signMap ((Matrix.mulVec W (f4 a x)) + b)

theorem g_f4 {w : Nat} (a : Fin w → Int) (x : Fin w → Int) (i : Fin w):
    g (a i) (const (x i)) = const ((f4 a x) i) := by
  ext j
  have hj : j = 0 := Subsingleton.elim j 0
  simp [g, const, hj]
  -- Closed-form for the i-th coordinate of f4
  have h_out := f4_coord_closed (w := w) a x i
  -- Relate with scalar equality `g = g'`
  have : (if x i = a i then 1 else -1)
      = signInt ((signInt (2 * x i - 2 * a i + 1)) + (signInt (2 * a i - 2 * x i + 1)) - 1) := by
    simpa [g, g', const] using congrArg (fun f => f (a i) (const (x i)) 0) g_eq
  simpa [h_out]

theorem f2_eq_f3 {w : Nat} : (f2 (w := w)) = f3 := by
  funext a x i
  simp only [f2, f3]
  congr
  simp only [g_f4]
  funext j
  have hj : j = 0 := Subsingleton.elim j 0
  simp [hj, Matrix.mulVec, dotProduct, const]


theorem isNRF_f3  {w : Nat} (a : Fin w → Int) : isNRF (f3 a) := by
  apply isNRF.layer
  apply isNRF.layer
  apply isNRF.layer
  apply isNRF.id




theorem isNRF_f  {w : Nat} (a : Fin w → Int) : isNRF (f a) := by
  simp only [f_eq_f2, f2_eq_f3]
  exact isNRF_f3 a


#print axioms isNRF_f


def in_range (a b : Int)  (x : Fin 1 → Int):  Fin 1 → Int := fun _ => if a < (x 0) ∧ (x 0) < b then 1 else -1

def in_range_aux (a b : Int) (x : Fin 1 → Int) : Fin 2 → Int  :=
  -- First layer producing s₁ = sign(2x - 2a - 1) and s₂ = sign(2b - 2x - 1)
  let W₁ : Matrix (Fin 2) (Fin 1) Int := fun i _ => if i = 0 then 2 else -2
  let b₁ : Fin 2 → Int := fun i => if i = 0 then (-2 * a - 1) else (2 * b - 1)
  signMap ((Matrix.mulVec W₁ x) + b₁)

def in_range_2  (a b : Int) (x : Fin 1 → Int) : Fin 1 → Int  :=
  -- Second layer producing sign(s₁ + s₂ - 1)
  let W₂ : Matrix (Fin 1) (Fin 2) Int := fun _ _ => 1
  let b₂ : Fin 1 → Int := fun _ => -1
  signMap ((Matrix.mulVec W₂ (in_range_aux a b x)) + b₂)

theorem is_NRF_in_range_2  (a b : Int) : isNRF (in_range_2 a b) := by
  apply isNRF.layer
  apply isNRF.layer
  exact isNRF.id


theorem if_le (c : Prop) [Decidable c]: 0 < (if c then 1 else -1) ↔ c := by
  by_cases ct : c
  <;> simp [ct]

-- Coordinate computations for `in_range_aux`
lemma in_range_aux_zero (a b : Int) (x : Fin 1 → Int) :
    in_range_aux a b x 0 = signInt (2 * x 0 - 2 * a - 1) := by
  -- i = 0 row: 2*x + (-2a - 1)
  have h0 : (0 : Fin 2) = 0 := rfl
  simp [in_range_aux, signMap, Matrix.mulVec, dotProduct, Fin.sum_univ_one, h0,
        if_pos rfl, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm]

lemma in_range_aux_one (a b : Int) (x : Fin 1 → Int) :
    in_range_aux a b x 1 = signInt (2 * b - 2 * x 0 - 1) := by
  -- i = 1 row: -2*x + (2b - 1)
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp [in_range_aux, signMap, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
        if_neg h10, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm]

lemma mulW2_in_range (s : Fin 2 → Int) :
    (Matrix.mulVec (fun (_ : Fin 1) _ => (1 : Int)) s) 0 = s 0 + s 1 := by
  -- sum both entries with weight 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

-- Arithmetic bridges from strict inequalities to sign arguments
lemma pos_iff_lt_left (a x : Int) : 0 < 2 * x - 2 * a - 1 ↔ a < x := by
  constructor
  · intro h
    -- 0 < 2x - (2a + 1) ⇒ 2a + 1 < 2x ⇒ a < x
    have : 2 * a + 1 < 2 * x := by
      -- rearrange and discharge via omega
      omega
    omega
  · intro h
    -- a < x ⇒ 2a + 1 < 2x ⇒ 0 < 2x - (2a + 1)
    have : 2 * a + 1 < 2 * x := by omega
    omega

lemma pos_iff_lt_right (x b : Int) : 0 < 2 * b - 2 * x - 1 ↔ x < b := by
  constructor
  · intro h
    have : 2 * x + 1 < 2 * b := by omega
    omega
  · intro h
    have : 2 * x + 1 < 2 * b := by omega
    omega

-- Variants that `simp` may generate after rearranging `0 < t - 1` into `1 < t`.
lemma one_lt_iff_lt_left (a x : Int) : 1 < 2 * x - 2 * a ↔ a < x := by
  constructor <;> intro h <;> omega

lemma one_lt_iff_lt_right (x b : Int) : 1 < 2 * b - 2 * x ↔ x < b := by
  constructor <;> intro h <;> omega

-- Compute the two rows of the simple {-2,2}×x matrix used above
lemma mul_vec_row0 (x : Fin 1 → Int) :
    (Matrix.mulVec (fun (i : Fin 2) _ => if i = 0 then (2 : Int) else -2) x) 0 = 2 * x 0 := by
  have h0 : (0 : Fin 2) = 0 := rfl
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_one, h0]

lemma mul_vec_row1 (x : Fin 1 → Int) :
    (Matrix.mulVec (fun (i : Fin 2) _ => if i = 0 then (2 : Int) else -2) x) 1 = -2 * x 0 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_one, if_neg h10]

-- Normalization variants to match algebraic forms produced by `simp`
lemma pos_iff_lt_left_add (a x : Int) : 0 < 2 * x + (-(2 * a) + -1) ↔ a < x := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using pos_iff_lt_left a x

lemma pos_iff_lt_right_add (x b : Int) : 0 < (-2) * x + (2 * b + -1) ↔ x < b := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm]
    using pos_iff_lt_right x b

-- Another normalization that may appear when simplifying the right-side inequality
lemma two_mul_add_one_lt_iff (x b : Int) : 2 * x + 1 < 2 * b ↔ x < b := by
  constructor <;> intro h <;> omega

theorem in_range_eq : in_range = in_range_2 := by
  funext a b x i
  have hi : i = 0 := Subsingleton.elim i 0
  -- Reduce both sides to the single coordinate `0` and expand the two-layer form
  -- so the argument inside the final `signInt` is `s₁ + s₂ - 1`.
  simp [in_range, in_range_2, signMap, in_range_aux, hi, mulW2_in_range,
        in_range_aux_zero, in_range_aux_one, sub_eq_add_neg, signInt, gt_iff_lt]
  -- Turn the RHS conjunction into `a < x 0 ∧ x 0 < b` by simplifying each inequality.
  have hleft :
      (0 < Matrix.mulVec (fun (i : Fin 2) _ => if i = 0 then (2 : Int) else -2) x 0 + (-(2 * a) + -1))
        ↔ (a < x 0) := by
    simpa [mul_vec_row0, pos_iff_lt_left_add]
  have hright :
      (0 < Matrix.mulVec (fun (i : Fin 2) _ => if i = 0 then (2 : Int) else -2) x 1 + (2 * b + -1))
        ↔ (x 0 < b) := by
    simp [mul_vec_row1, pos_iff_lt_right_add]
    omega
  -- Package the two 0< … tests as propositional variables to apply `one_lt_sum_if_iff`.
  let P : Prop := 0 < Matrix.mulVec (fun (i : Fin 2) x ↦ if i = 0 then 2 else -2) x 0 + (-(2 * a) + -1)
  let Q : Prop := 0 < Matrix.mulVec (fun (i : Fin 2) x ↦ if i = 0 then 2 else -2) x 1 + (2 * b + -1)
  have hsum : (1 : Int) < ((if P then 1 else -1) + (if Q then 1 else -1))
                ↔ (a < x 0 ∧ x 0 < b) := by
    -- Reduce via the equivalences for each side
    have := (one_lt_sum_if_iff P Q)
    simpa [P, Q, hleft, hright] using this
  -- Rewrite the RHS using `hsum` to match the LHS condition
  simp [P, Q] at hsum
  -- Use propositional extensionality to rewrite the `if` condition
  have hcond :
      ((1 : Int) <
        (if (0 : Int) < Matrix.mulVec (fun (i : Fin 2) x ↦ if i = 0 then 2 else -2) x 0 + (-(2 * a) + -1) then 1 else -1) +
          if (0 : Int) < Matrix.mulVec (fun (i : Fin 2) x ↦ if i = 0 then 2 else -2) x 1 + (2 * b + -1) then 1 else -1)
        = (a < x 0 ∧ x 0 < b) :=
    propext hsum
  simp [hcond]

#print axioms in_range_eq

-- Small helper lemmas to keep the composition proof readable
lemma isNRF_comp_id {a b : Nat}
    {f : (Fin a → Int) → (Fin b → Int)} (hf : isNRF f) :
    isNRF ((fun x => x) ∘ f) := by
  simpa [Function.comp] using hf

lemma isNRF_comp_layer
    {a k n m : Nat}
    (W : Matrix (Fin m) (Fin n) Int) (b : Fin m → Int)
    {h : (Fin k → Int) → (Fin n → Int)}
    {f : (Fin a → Int) → (Fin k → Int)}
    (hhf : isNRF (h ∘ f)) :
    isNRF ((fun y => signMap ((Matrix.mulVec W (h y)) + b)) ∘ f) := by
  simpa [Function.comp] using (isNRF.layer (W := W) (b := b) (hf := hhf))

lemma isNRF_comp_pair
    {a m n p : Nat}
    {h1 : (Fin m → Int) → (Fin n → Int)}
    {h2 : (Fin m → Int) → (Fin p → Int)}
    {f  : (Fin a → Int) → (Fin m → Int)}
    (h1f : isNRF (h1 ∘ f)) (h2f : isNRF (h2 ∘ f)) :
    isNRF ((fun y => appendVec (h1 y) (h2 y)) ∘ f) := by
  simpa [Function.comp] using (isNRF.pair (hf := h1f) (hg := h2f))

-- General composition lemma: pre-compose any NRF with another NRF
lemma isNRF_comp_left {m n : Nat}
    {g : (Fin m → Int) → (Fin n → Int)} (hg : isNRF g) :
    ∀ {a} (f : (Fin a → Int) → (Fin m → Int)), isNRF f → isNRF (g ∘ f) := by
  induction hg with
  | id =>
      intro a f hf; simpa [Function.comp] using hf
  | @layer m n k W b h hh IH =>
      intro a f hf
      have hcomp : isNRF (h ∘ f) := IH f hf
      exact isNRF_comp_layer (a := a) (k := k) (n := n) (m := m) W b hcomp
  | @pair m n p h1 h2 hh1 hh2 IH1 IH2 =>
      intro a f hf
      have h1comp : isNRF (h1 ∘ f) := IH1 f hf
      have h2comp : isNRF (h2 ∘ f) := IH2 f hf
      exact isNRF_comp_pair (a := a) (m := m) (n := n) (p := p) (h1 := h1) (h2 := h2) (f := f) h1comp h2comp

theorem NRF_comp {a b c : Nat}
    {f : (Fin a → Int) → (Fin b → Int)}
    {g : (Fin b → Int) → (Fin c → Int)}
    (hg : isNRF g) (hf : isNRF f) : isNRF (g ∘ f) := by
  simpa using (isNRF_comp_left (m := b) (n := c) (g := g) hg f hf)

#print axioms NRF_comp


def apply_linear {a b : Nat} (M : Matrix (Fin b) (Fin a) Int) (c : Fin b → Int) (x : Fin a → Int) :  Fin b → Int := (Matrix.mulVec M x) + c

-- theorem apply_linear_NRF  {a b : Nat} (M : Matrix (Fin b) (Fin a) Int) (c : Fin b → Int) : isNRF (apply_linear M c ) := by
--   apply isNRF.layer

--   sorry
def decidableAnd {a b : Prop}  (da : Decidable a) (db : Decidable b) : Decidable (a ∧ b) := by
  infer_instance

def decidableNot {a : Prop}  (da : Decidable a) : Decidable (¬ a) := by
  infer_instance

def decidableFinForall {m  : Nat}  (p : Fin m → Prop) (di : ∀ (i : Fin m), Decidable (p i))  : Decidable (∀ (i : Fin m), p i) := by
  exact Nat.decidableForallFin p

instance vec_lt {a : Nat} (x y  : Fin a → ℤ) : Decidable (x < y) := by
  apply decidableAnd
  · apply decidableFinForall
    infer_instance
  · apply decidableNot
    apply decidableFinForall
    infer_instance

def linear_system {a b  : Nat} (A : Matrix (Fin a) (Fin b) Int) (d : Fin a → Int) (x : Fin b → Int) : Int :=
  if (Matrix.mulVec A x) < d then 1 else -1

-- Simpler, per-coordinate semantics: returns 1 iff every coordinate is strictly inside.
def in_range_vec {w: Nat} (a b : Fin w → Int)  (x : Fin w → Int):  Fin w → Int :=
  fun _ => if (∀ i : Fin w, a i < x i ∧ x i < b i) then 1 else -1

-- Pointwise order on functions: x < y ↔ (x ≤ y) ∧ ∃ i, x i < y i
theorem vec_lt_iff  {w: Nat} (a b : Fin w → Int) :
    (a < b) ↔ ((∀ (i : Fin w), a i ≤ b i) ∧ ∃ (i : Fin w), a i < b i) := by
  constructor
  · intro h
    -- Unfold the `Pi`-order strict inequality
    have h' : (∀ i, a i ≤ b i) ∧ ¬ (∀ i, b i ≤ a i) := by
      simpa [LT.lt, LE.le] using h
    rcases h' with ⟨hLe, hnot⟩
    -- Extract a coordinate with strict inequality using ¬∀ ≤
    have : ∃ i, ¬ (b i ≤ a i) := by
      simpa [not_forall] using hnot
    rcases this with ⟨i, hi⟩
    have hi' : a i < b i := lt_of_not_ge hi
    exact ⟨hLe, ⟨i, hi'⟩⟩
  · intro h
    rcases h with ⟨hLe, ⟨i, hi⟩⟩
    have hnot : ¬ (∀ i, b i ≤ a i) := by
      intro hforall
      have : b i ≤ a i := hforall i
      exact (not_le_of_gt hi) this
    simpa [LT.lt, LE.le] using And.intro hLe hnot

-- Vectorized range tester: first layer weights are identical to `W1`,
-- but biases switch to the `-1` variants needed for strict inequalities.
def b1_range {w : Nat} (a b : Fin w → Int) : Fin (w + w) → Int :=
  fun i =>
    Fin.addCases
      (fun i0 : Fin w => (-2) * a i0 - 1)
      (fun i1 : Fin w => (2) * b i1 - 1)
      i

def s_range {w : Nat} (a b : Fin w → Int) (x : Fin w → Int) : Fin (w + w) → Int :=
  signMap ((Matrix.mulVec (W1 (w := w) (a := a)) x) + (b1_range a b))

def in_range_per_coord {w : Nat} (a b : Fin w → Int) (x : Fin w → Int) : Fin w → Int :=
  -- Combine the two signs per index and threshold at 1
  signMap ((Matrix.mulVec (W2 (w := w)) (s_range a b x)) + (b2 (w := w)))

-- Coordinate computations mirroring `s1_left/right` but with `-1` biases
lemma s_range_left {w : Nat} (a b : Fin w → Int) (x : Fin w → Int) (i : Fin w) :
    s_range a b x (i.castAdd w) = signInt (2 * x i - 2 * a i - 1) := by
  simp [s_range, W1, b1_range, signMap, Matrix.mulVec, dotProduct, Fin.addCases,
        ite_mul, mul_ite, sum_if_singleton' (i := i), sub_eq_add_neg,
        two_mul, mul_add, add_comm, add_left_comm, add_assoc]

lemma s_range_right {w : Nat} (a b : Fin w → Int) (x : Fin w → Int) (i : Fin w) :
    s_range a b x (i.addNat w) = signInt (2 * b i - 2 * x i - 1) := by
  simp [s_range, W1, b1_range, signMap, Matrix.mulVec, dotProduct, Fin.addCases,
        ite_mul, mul_ite, sum_if_singleton' (i := i), sub_eq_add_neg,
        two_mul, mul_add, add_comm, add_left_comm, add_assoc]

lemma in_range_per_coord_closed {w : Nat} (a b : Fin w → Int) (x : Fin w → Int) (i : Fin w) :
    in_range_per_coord a b x i
      = signInt ((signInt (2 * x i - 2 * a i - 1)) +
                 (signInt (2 * b i - 2 * x i - 1)) - 1) := by
  have hf : (in_range_per_coord a b x) i
              = signInt (((Matrix.mulVec (W2 (w := w)) (s_range a b x)) + (b2 (w := w))) i) := by
    simp [in_range_per_coord, signMap, Pi.add_apply]
  have hsum : (Matrix.mulVec (W2 (w := w)) (s_range a b x)) i
                = (s_range a b x) (i.addNat w) + (s_range a b x) (i.castAdd w) := by
    simpa using mulW2_coord (w := w) (s := s_range a b x) i
  have hb₂ : (b2 (w := w)) i = -1 := rfl
  have hx : (s_range a b x) (i.castAdd w) = signInt (2 * x i - 2 * a i - 1) := by
    simpa using s_range_left (w := w) a b x i
  have hy : (s_range a b x) (i.addNat w) = signInt (2 * b i - 2 * x i - 1) := by
    simpa using s_range_right (w := w) a b x i
  simpa [hf, hsum, hb₂, hx, hy, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

-- Relate each coordinate to the scalar in_range predicate
-- Scalar closed form for a single coordinate
lemma in_range_scalar_closed (a b x : Int) :
    in_range_2 a b (const x) 0
      = signInt ((signInt (2 * x - 2 * a - 1)) + (signInt (2 * b - 2 * x - 1)) - 1) := by
  simp [in_range_2, signMap, Pi.add_apply, mulW2_in_range, in_range_aux_zero, in_range_aux_one,
        const, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

lemma in_range_per_coord_spec {w : Nat} (a b : Fin w → Int)
    (x : Fin w → Int) (i : Fin w) :
    in_range_per_coord a b x i = (if a i < x i ∧ x i < b i then 1 else -1) := by
  have hcoord := in_range_per_coord_closed (w := w) (a := a) (b := b) (x := x) (i := i)
  -- From the 1-D equivalence `in_range = in_range_2`, derive the predicate form
  have h1D :
      signInt ((signInt (2 * x i - 2 * a i - 1)) + (signInt (2 * b i - 2 * x i - 1)) - 1)
        = (if a i < x i ∧ x i < b i then 1 else -1) := by
    have h := congrArg (fun F => F (a i) (b i) (const (x i)) 0) in_range_eq
    -- Rewrite both sides to closed forms
    have hclosed := in_range_scalar_closed (a := a i) (b := b i) (x := x i)
    simpa [in_range, const, hclosed]
      using h.symm
  simpa [hcoord] using h1D

-- Aggregate all coordinates: 1 iff every coordinate is in range
def in_range_vec_core {w : Nat} (a b : Fin w → Int) (x : Fin w → Int) : Fin 1 → Int :=
  let W : Matrix (Fin 1) (Fin w) Int := fun _ _ => 1
  let b' : Fin 1 → Int := fun _ => -((w : Int) - 1)
  signMap ((Matrix.mulVec W (in_range_per_coord a b x)) + b')

-- Broadcast a single-bit result to `w` identical outputs (idempotent under `signMap`).
def broadcast1 {w : Nat} (y : Fin 1 → Int) : Fin w → Int :=
  let W : Matrix (Fin w) (Fin 1) Int := fun _ _ => 1
  let b : Fin w → Int := fun _ => 0
  signMap ((Matrix.mulVec W y) + b)

def in_range_vec_2 {w : Nat} (a b : Fin w → Int) (x : Fin w → Int) : Fin w → Int :=
  broadcast1 (in_range_vec_core a b x)



-- Prove equivalence of the spec and the constructed two-layer+aggregate network
lemma in_range_vec_eq {w : Nat} (a b : Fin w → Int) :
    in_range_vec a b = in_range_vec_2 a b := by
  funext x j
  -- We reason by cases on whether all coordinates are strictly inside
  -- Turn the sign test into the target `if` via the same bound used in `f_eq_f2`.
  -- If every coordinate satisfies the predicate, the sum is `w` ⇒ positive; otherwise ≤ w-1 ⇒ nonpositive.
  by_cases hall : ∀ i : Fin w, a i < x i ∧ x i < b i
  · -- All in range ⇒ sum = w
    have hterm : ∀ i, in_range_per_coord a b x i = 1 := by
      intro i; simp [in_range_per_coord_spec, hall i]
    have hy : (in_range_vec_core a b x) 0 = 1 := by
      simp [in_range_vec_core, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
            hterm, signMap, Pi.add_apply, sub_eq_add_neg, signInt]
    -- RHS: broadcasting preserves the bit
    have hrhs : (in_range_vec_2 a b x) j = 1 := by
      simp [in_range_vec_2, broadcast1, hy, signMap, Matrix.mulVec, dotProduct,
            Fin.sum_univ_one, signInt]
    -- LHS: by definition
    have hlhs : (in_range_vec a b x) j = 1 := by simp [in_range_vec, hall]
    simpa [hlhs, hrhs]
  · -- Not all in range ⇒ there exists a failing index and the sum ≤ w - 1
    have hxne : ∃ j : Fin w, ¬ (a j < x j ∧ x j < b j) := by
      exact not_forall.mp hall
    have hsum_le : (∑ i, in_range_per_coord a b x i) ≤ (w : Int) - 1 := by
      -- Rewrite via the spec and apply the sum bound
      have :=
        sum_if_one_neg_one_le_sub_one (w := w) (p := fun i : Fin w => a i < x i ∧ x i < b i) hxne
      -- Cast the sum shape
      simpa [in_range_per_coord_spec] using this
    -- The aggregator is nonpositive ⇒ outputs -1
    have hy : (in_range_vec_core a b x) 0 = -1 := by
      have : (∑ i, in_range_per_coord a b x i) - ((w : Int) - 1) ≤ 0 := by
        have := sub_le_sub_right hsum_le ((w : Int) - 1)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      -- Coerce to sign
      have hsign : signInt ((∑ i, in_range_per_coord a b x i) - ((w : Int) - 1)) = -1 := by
        have h' : ¬ (0 < (∑ i, in_range_per_coord a b x i) - ((w : Int) - 1)) :=
          by exact not_lt.mpr this
        by_cases hpos : 0 < (∑ i, in_range_per_coord a b x i) - ((w : Int) - 1)
        · exact (h' hpos).elim
        · simpa [signInt, hpos]
      -- Evaluate the core bit explicitly
      simpa [in_range_vec_core, signMap, Pi.add_apply, Matrix.mulVec, dotProduct,
             Fin.sum_univ_one, sub_eq_add_neg]
        using hsign
    -- Conclude both sides are -1
    have hrhs : (in_range_vec_2 a b x) j = -1 := by
      simp [in_range_vec_2, broadcast1, hy, signMap, Matrix.mulVec, dotProduct,
            Fin.sum_univ_one, signInt]
    have hlhs : (in_range_vec a b x) j = -1 := by simp [in_range_vec, hall]
    simpa [hlhs, hrhs]


-- Show the constructed function is an NRF by stacking four layers
theorem nrf_in_range_vec {w: Nat} (a b : Fin w → Int) : isNRF (in_range_vec a b) := by
  -- Replace with our explicit layered construction
  have hEq : in_range_vec a b = in_range_vec_2 a b := in_range_vec_eq (a := a) (b := b)
  -- Prove the layered form is an NRF
  -- Layer 1: compute the 2w auxiliary signs `s_range`
  have h1 : isNRF (fun x => s_range a b x) := by
    -- This is a single affine+sign layer on `id`
    simpa [s_range] using (isNRF.layer (W := W1 (w := w) (a := a)) (b := b1_range a b) (hf := isNRF.id))
  -- Layer 2: sum each pair and threshold to get per-coordinate range indicators
  have h2 : isNRF (fun x => in_range_per_coord a b x) := by
    simpa [in_range_per_coord] using (isNRF.layer (W := W2 (w := w)) (b := b2 (w := w)) (hf := h1))
  -- Layer 3: aggregate all coordinates (all-of)
  have h3 : isNRF (fun x => in_range_vec_core a b x) := by
    -- Sum with all-ones row and subtract (w-1)
    simpa [in_range_vec_core] using
      (isNRF.layer (W := (fun _ _ => 1)) (b := (fun _ => -((w : Int) - 1))) (hf := h2))
  -- Layer 4: broadcast the bit to `w` outputs
  have h4 : isNRF (fun x => in_range_vec_2 a b x) := by
    let W : Matrix (Fin w) (Fin 1) Int := fun _ _ => 1
    let b : Fin w → Int := fun _ => 0
    simpa [in_range_vec_2, broadcast1] using (isNRF.layer (W := W) (b := b) (hf := h3))
  simpa [hEq]


#print axioms nrf_in_range_vec
