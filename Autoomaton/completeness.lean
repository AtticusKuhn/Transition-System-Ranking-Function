import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card

set_option linter.unnecessarySimpa false
-- import Mathlib.Algebra.BigOperators.Ring

def signInt (x : Int) : Int := if x > 0 then 1 else -1
def signMap {n : Nat} (vec : Fin n → Int) : Fin n → Int := signInt ∘ vec

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
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr
    · rfl
    intro x x_mem
    exact hpoint (b := p x)
  have h2 : (∑ i, (if p i then (2 : Int) else 0))
      = ((Finset.univ.filter p).card : Int) * 2 := by
      classical
      have hsum :
          (∑ i, (if p i then (2 : Int) else 0))
            = (∑ i in (Finset.univ.filter p), (2 : Int)) := by
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

/-- A compact, proof-oriented inductive definition capturing the closure of NRF outputs
under products and sign-affine layers. This is useful for compositional proofs.
def
The base objects are projections from products; `layer` composes with a single
sign-affine map; and `pair` combines two NRFs pointwise into a product. -/
inductive isNRF : {m n: Nat} → ((Fin m → Int) → (Fin n → Int)) → Prop where
  | id : isNRF (fun x => x)
  | layer {m n k : Nat}
      (W : Matrix (Fin m) (Fin n) Int) (b : Fin m → Int)
      {f : (Fin k → Int) → (Fin n → Int)}
      (hf : isNRF f)
      : isNRF (fun x => signMap ((Matrix.mulVec W (f x)) + b))

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

theorem g_eq : g = g' := by
  funext a x i
  simp [g, Int.reduceNeg, g', signInt, gt_iff_lt, Int.sub_pos]
  rw [if_push]
  rw [if_push_2]
  simp only [true_and, Int.reduceNeg, reduceCtorEq, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, false_and, or_false, ite_eq_right_iff, imp_false, not_lt]
  by_cases c : x = a
  <;> try simp [c, sub_self, zero_add, Int.reduceLT, ↓reduceIte, Int.reduceAdd, and_self,
    not_true_eq_false, Int.reduceLE, or_false]
  simp [Int.reduceNeg, false_and, not_false_eq_true, if_add, not_lt, true_and, false_or]
  omega


theorem nrf_g2 {a : Int}: isNRF (g2 a) := by
  apply isNRF.layer
  apply isNRF.layer
  apply isNRF.id

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
    unfold g
    simp only [const, Int.reduceNeg]
    classical
    -- Define the set of equal coordinates
    let p : Fin w → Prop := fun i => x i = a i
    have hs : (∑ i, (if p i then (1 : Int) else -1))
        = (2 : Int) * ((Finset.univ.filter p).card : Int) - (w : Int) :=
      sum_if_one_neg_one_eq (w := w) (p := p)
    -- There exists an index where x and a differ (since x ≠ a)
    have hxne : ∃ j : Fin w, ¬ p j := by
      by_contra h
      push_neg at h
      apply c
      funext i; exact h i
    rcases hxne with ⟨j, hj⟩
    -- Bound the count of equal coordinates by w - 1 using j
    have hsubset : (Finset.univ.filter p) ⊆ (Finset.univ.erase j) := by
      intro i hi
      have hi_univ : i ∈ (Finset.univ : Finset (Fin w)) := by simp
      have hip : p i := by simpa [Finset.mem_filter] using hi
      have hij : i ≠ j := by
        intro hcontr; apply hj; simpa [hcontr] using hip
      simp [Finset.mem_erase, Finset.mem_univ, true_and, hij]
    have hjmem : j ∈ (Finset.univ : Finset (Fin w)) := by simp
    have hcard_le_nat : (Finset.univ.filter p).card ≤ (Finset.univ.erase j).card := by
      exact Finset.card_le_card hsubset
    have hcard_erase : (Finset.univ.erase j).card = w- 1 := by
      have hjmem : j ∈ (Finset.univ : Finset (Fin w)) := by simp
      simpa [Fintype.card_fin] using (Finset.card_erase_of_mem (s := (Finset.univ : Finset (Fin w))) (a := j) hjmem)
    have hScard_le : ((Finset.univ.filter p).card : Int) ≤ (w : Int) - 1 := by
      have : (Finset.univ.filter p).card ≤ w - 1 := by simpa [hcard_erase] using hcard_le_nat
      -- Cast the ℕ-inequality to ℤ and rewrite (w : ℤ) - 1 using Int.ofNat_sub
      have hwpos : 0 < w := by
        -- We have `j : Fin w`, so `w ≠ 0`
        exact (Fin.pos_iff_nonempty.mpr ⟨j⟩)
      have hw1 : 1 ≤ w := Nat.succ_le_of_lt hwpos
      have hcast : ((Finset.univ.filter p).card : Int) ≤ ((w - 1 : Nat) : Int) := by
        exact_mod_cast this
      simpa [Int.ofNat_sub hw1] using hcast
    -- Combine: 2*|S| - w ≤ w - 1
    have h2le : (2 : Int) * ((Finset.univ.filter p).card : Int) - (w : Int) ≤ (w : Int) - 1 := by
      have hmul : (2 : Int) * ((Finset.univ.filter p).card : Int) ≤ (2 : Int) * ((w : Int) - 1) :=
       by
        -- Rewrite 2 * t as t + t and add the inequalities
        simpa [two_mul] using add_le_add hScard_le hScard_le
      have hstep : (2 : Int) * ((w : Int) - 1) - (w : Int) ≤ (w : Int) - 1 := by
        -- 2*(w-1) - w = w - 2 ≤ w - 1
        have : (w : Int) - 2 ≤ (w : Int) - 1 := by
          -- From 1 ≤ 2, subtract both sides from (w : ℤ)
          exact sub_le_sub_left (by decide : (1 : Int) ≤ 2) (w : Int)
        simpa [two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      exact le_trans (by
        have hsub := sub_le_sub_right hmul (w : Int)
        simpa using hsub) hstep
    -- Finally, deduce the preactivation is ≤ (w : ℤ) - 1 (exact goal after simp)
    have hpre : (∑ i, (if p i then (1 : Int) else -1)) ≤ (w : Int) - 1 := by
      simpa [hs] using h2le
    exact hpre

def f4 {w : Nat} (a : Fin w → Int) (x : Fin w → Int) : Fin w → Int :=
  -- Two-layer construction computing, for each coordinate i,
  -- sign( sign(2 x_i - 2 a_i + 1) + sign(2 a_i - 2 x_i + 1) - 1 )
  let W₁ : Matrix (Fin (w + w)) (Fin w) Int :=
    fun i j =>
      Fin.addCases
        (fun i0 : Fin w => if j = i0 then (2 : Int) else 0)
        (fun i1 : Fin w => if j = i1 then (-2 : Int) else 0)
        i
  let b₁ : Fin (w + w) → Int :=
    fun i =>
      Fin.addCases
        (fun i0 : Fin w => (-2) * a i0 + 1)
        (fun i1 : Fin w => (2) * a i1 + 1)
        i
  let s : Fin (w + w) → Int := signMap ((Matrix.mulVec W₁ x) + b₁)
  let W₂ : Matrix (Fin w) (Fin (w + w)) Int :=
    fun j r => (if r = j.castAdd w then (1 : Int) else 0) + (if r = j.addNat w then (1 : Int) else 0)
  let b₂ : Fin w → Int := fun _ => (-1 : Int)
  signMap ((Matrix.mulVec W₂ s) + b₂)

def f3 {w : Nat} (a : Fin w → Int) (x : Fin w → Int) : Fin 1 → Int :=
  -- Single affine layer summing all coordinates of f4 a x and subtracting (w - 1)
  -- before applying the sign nonlinearity.
  let W : Matrix (Fin 1) (Fin w) Int := fun _ _ => 1
  let b : Fin 1 → Int := fun _ => -((w : Int) - 1)
  signMap ((Matrix.mulVec W (f4 a x)) + b)

theorem g_f4 {w : Nat} (a : Fin w → Int) (x : Fin w → Int) (i : Fin w):
    g (a i) (const (x i)) = const ((f4 a x) i) := by
  classical
  ext j
  have hj : j = 0 := Subsingleton.elim j 0
  simp [g, const, hj]
  -- Now show `(f4 a x) i` equals the closed form used in `g'`
  -- Compute the two preactivations s_left and s_right at indices for i
  -- and then the second-layer output at coordinate i.
  -- The `simp` calls below reduce the matrix-vector products to the single
  -- contributing coordinates using `sum_if_singleton`.
  have h_left : (signMap ((Matrix.mulVec
      (fun r c =>
        Fin.addCases (fun i0 : Fin w => if c = i0 then (2 : Int) else 0)
                      (fun i1 : Fin w => if c = i1 then (-2 : Int) else 0) r)
      x) +
      (fun r => Fin.addCases (fun i0 : Fin w => (-2) * a i0 + 1)
                             (fun i1 : Fin w => (2) * a i1 + 1) r))
      (i.castAdd w))
      = signInt (2 * x i - 2 * a i + 1) := by
        -- Evaluate the left branch at row i.castAdd w: picks 2*x i then adds (−2*a i + 1)
        simp [signMap, Matrix.mulVec, dotProduct, Fin.addCases, ite_mul, mul_ite,
              sum_if_singleton' (i := i), sub_eq_add_neg, two_mul, mul_add,
              add_comm, add_left_comm, add_assoc]
  have h_right : (signMap ((Matrix.mulVec
      (fun r c =>
        Fin.addCases (fun i0 : Fin w => if c = i0 then (2 : Int) else 0)
                      (fun i1 : Fin w => if c = i1 then (-2 : Int) else 0) r)
      x) +
      (fun r => Fin.addCases (fun i0 : Fin w => (-2) * a i0 + 1)
                             (fun i1 : Fin w => (2) * a i1 + 1) r))
      (i.addNat w))
      = signInt (2 * a i - 2 * x i + 1) := by
    simp [signMap, Matrix.mulVec, dotProduct, Fin.addCases, ite_mul, mul_ite,
          sub_eq_add_neg, sum_if_singleton' (i := i), two_mul, mul_add, add_comm, add_left_comm, add_assoc]
  -- Now compute the second layer output at coordinate i
  have h_out : (f4 a x) i
      = signInt ((signInt (2 * x i - 2 * a i + 1)) + (signInt (2 * a i - 2 * x i + 1)) - 1) := by
    -- Name the intermediate objects in f4 to simplify the evaluation
    classical
    let W₁ : Matrix (Fin (w + w)) (Fin w) Int :=
      fun i j =>
        Fin.addCases
          (fun i0 : Fin w => if j = i0 then (2 : Int) else 0)
          (fun i1 : Fin w => if j = i1 then (-2 : Int) else 0)
          i
    let b₁ : Fin (w + w) → Int :=
      fun i =>
        Fin.addCases
          (fun i0 : Fin w => (-2) * a i0 + 1)
          (fun i1 : Fin w => (2) * a i1 + 1)
          i
    let s : Fin (w + w) → Int := signMap ((Matrix.mulVec W₁ x) + b₁)
    let W₂ : Matrix (Fin w) (Fin (w + w)) Int :=
      fun j r => (if r = j.castAdd w then (1 : Int) else 0) + (if r = j.addNat w then (1 : Int) else 0)
    let b₂ : Fin w → Int := fun _ => (-1 : Int)
    have hf4i : (f4 a x) i = signInt (((Matrix.mulVec W₂ s) + b₂) i) := by
      simp [f4, W₁, b₁, s, W₂, b₂, signMap, Pi.add_apply]
    have hsumW₂ : (Matrix.mulVec W₂ s) i = s (i.addNat w) + s (i.castAdd w) := by
      -- Expand the dot product and split the two indicator contributions
      simp [W₂, Matrix.mulVec, dotProduct, ite_mul, mul_ite, mul_add, add_mul,
            Finset.sum_add_distrib, sum_if_singleton (i := i.addNat w),
            sum_if_singleton (i := i.castAdd w), add_comm, add_left_comm, add_assoc]
    have hb₂ : b₂ i = -1 := rfl
    -- Put together the pieces and rewrite using h_left and h_right
    -- Unfold `s` to apply the coordinate-wise simplifications `h_left` and `h_right`
    have hsum_out : (f4 a x) i
        = signInt ((s (i.addNat w) + s (i.castAdd w)) - 1) := by
      -- from hf4i, hsumW₂ and hb₂
      simpa [hf4i, hsumW₂, hb₂, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    -- Rewrite s-coordinates using the first-layer computations
    have hx : s (i.addNat w) = signInt (2 * a i - 2 * x i + 1) := by
      simp [s, W₁, b₁, h_right, signMap]
      apply congr_arg
  --     ⊢ Matrix.mulVec (fun i j ↦ Fin.addCases (fun i0 ↦ if j = i0 then 2 else 0) (fun i1 ↦ if j = i1 then -2 else 0) i) x
  --     (i.addNat w) +
  --   Fin.addCases (fun i0 ↦ -(2 * a i0) + 1) (fun i1 ↦ 2 * a i1 + 1) (i.addNat w) =
  -- 2 * a i - 2 * x i + 1
      sorry
    have hy : s (i.castAdd w) = signInt (2 * x i - 2 * a i + 1) := by
      simp [s, W₁, b₁, h_left,signMap]
      apply congr_arg
  --     ⊢ Matrix.mulVec (fun i j ↦ Fin.addCases (fun i0 ↦ if j = i0 then 2 else 0) (fun i1 ↦ if j = i1 then -2 else 0) i) x
  --     (Fin.castAdd w i) +
  --   (-(2 * a i) + 1) =
  -- 2 * x i - 2 * a i + 1
      sorry
    -- Finish by rearranging the sum order
    simpa [hsum_out, hx, hy, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
  -- Conclude by `g_eq` specialized to this scalar case
  have hg : (if x i = a i then 1 else -1)
      = signInt ((signInt (2 * x i - 2 * a i + 1)) + (signInt (2 * a i - 2 * x i + 1)) - 1) := by
    -- Use the previously proved scalar equality g = g'
    have := congrArg (fun f => f (a i) (const (x i)) 0) g_eq
    simpa [g, g', const] using this
  -- Put the pieces together
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
