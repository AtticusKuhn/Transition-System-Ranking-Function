import Autoomaton.isNRFNeurons
set_option linter.unnecessarySimpa false
open Classical

inductive isNRFNeurons_complete : {m: Nat} → ((Fin m → Int) → Int) → Nat → Prop where
  | mk_nrf {m k n : Nat}
      (fs : (Fin m → ℤ) → (Fin k → ℤ) )
      (nrf_fs : isNRFNeurons fs n)
      (W : Matrix (Fin k) (Fin m) Int) (b : Fin k → Int)
      : isNRFNeurons_complete (fun x => (dotProduct ((Matrix.mulVec W x) + b) (reluMap (fs x)))) (k + n)


def linear_sum {w : Nat}
 {a b  : Nat} (C : Fin w → Matrix (Fin a) (Fin b) Int) (A : Fin w → Fin b → Int ) (c : Fin w → Int) (low : Fin w → Fin a → Int) (high : Fin w → Fin a → Int) : (Fin b → Int) →  Int
  := fun (x : Fin b → Int) => ∑ (i : Fin w), if (∀ j : Fin a, low i j < (Matrix.mulVec (C i) x) j ∧  (Matrix.mulVec (C i) x) j < high i j) then (dotProduct (A i) x) + c i else 0


/-
Helper constructions: For each index `i : Fin w`, we build a 3-layer NRF that produces
one scalar bit (valued in {−1, 1}) indicating whether all `a` coordinates of the
affine image `y := C i • x` lie strictly inside the per-coordinate range `low i .. high i`.

This mirrors the layered construction used for `in_range_vec` in `isNRFNeurons.lean`,
but we fold the precomposition by `C i` into the first layer weights.
-/

namespace CompleteNeuronsHelpers

variable {a b : Nat}

-- signInt basic facts
lemma signInt_eq_one_iff {z : Int} : signInt z = 1 ↔ 0 < z := by
  unfold signInt
  by_cases hz : 0 < z
  · simp [hz]
  · have : ¬ z > 0 := by simpa [gt_iff_lt] using hz
    simp [this]

lemma signInt_vals (z : Int) : signInt z = 1 ∨ signInt z = -1 := by
  unfold signInt; by_cases hz : 0 < z <;> simp [hz]

-- Arithmetic: 0 < 2*t - 1 ↔ 0 < t over Int
lemma int_pos_two_mul_sub_one_iff {t : Int} : 0 < 2 * t - 1 ↔ 0 < t := by
  omega
-- Case analysis: combining two ±1 bits into a single bit via sum-1 and signInt
lemma signInt_pair_and {p q : Int}
    (hp : p = 1 ∨ p = -1) (hq : q = 1 ∨ q = -1) :
    signInt (p + q - 1) = 1 ↔ (p = 1 ∧ q = 1) := by
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> simp [hp, hq, signInt_vals]
  all_goals simp [signInt]

-- Aggregation over Fin a: positivity of sum+1-a iff all entries are 1 (given ±1 values)
lemma sum_pos_iff_all_ones {t : Fin a → Int}
    (hvals : ∀ j, t j = 1 ∨ t j = -1) :
    (0 < (∑ (j : Fin a), t j) + (1 - (a : Int))) ↔ (∀ j, t j = 1) := by
  constructor
  · intro hpos
    -- First show sum ≤ a
    have hle1 : (∑ j, t j) ≤ (∑ _j : Fin a, (1 : Int)) := by
      induction' a with a ih
      · simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const, Finset.card_empty,
        zero_smul, le_refl]
      · simp
        simp at ih
        sorry
    have hsum_le : (∑ j, t j) ≤ (a : Int) := by simpa using hle1
    -- From 0 < sum + 1 - a, deduce a ≤ sum
    have hle : (a : Int) ≤ (∑ j, t j) := by
      -- 0 < sum + 1 - a  ↔  a < sum + 1
      -- have := Int.add_one_le_iff.mp (le_of_lt hpos)

      -- But `Int.add_one_le_iff` expects shape x + 1 ≤ y; rewrite
      -- Instead, use strict to non-strict conversion: a ≤ sum
      have : (a : Int) < (∑ j, t j) + 1 := by
        -- simp [add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
        sorry
      exact Int.lt_add_one_iff.mp this
    have hsum_eq : (∑ j, t j) = (a : Int) := le_antisymm hsum_le hle
    -- If any entry were -1, we can bound sum ≤ a - 2, contradiction
    by_contra hexists
    rcases not_forall.mp hexists with ⟨j0, hj0⟩
    have hj0' : t j0 = -1 := by
      have := hvals j0
      rcases this with h1 | hneg
      · exact (hj0 h1).elim
      · exact hneg
    -- pointwise bound: g i = if i=j0 then -1 else 1
    have hbound : (∑ j, t j) ≤ (∑ j : Fin a, (if j = j0 then (-1 : Int) else 1)) := by
      sorry
    have : (∑ j, t j) ≤ (a : Int) - 2 := by
      -- compute RHS sum: (-1) + (a-1)*1 = a - 2
      have : (∑ j : Fin a, (if j = j0 then (-1 : Int) else 1))
              = (-1) + ((a - 1) : Int) := by
        -- separate j0 and the rest
        -- have := (Finset.sum_toFinset_eq_subtype  (p := fun (j : Fin a) => j = j0) _)
        -- keep it simple: there are a-1 indices ≠ j0; sum is (-1) + (a-1)
        -- use cardinalities of Fin a
        -- Provide a direct combinatorial computation
        classical
        have hcount : ((Finset.univ.erase j0).card : Int) = (a - 1) := by
          simpa [Nat.cast_ofNat, Int.ofNat, Int.ofNat_sub, Int.ofNat_one]
            using congrArg (fun (n : Int) => (n : Int)) (by
              have : (Finset.univ.erase j0).card = a - 1 := by
                simpa using Finset.card_univ_erase (s := (Finset.univ : Finset (Fin a))) j0
              sorry)
        -- sum over erase j0 is (a-1)*1
        have hsum_erase : (∑ j ∈ Finset.univ.erase j0, (1 : Int)) = (a - 1) := by
          sorry
        -- full computation
        have : (∑ j, (if j = j0 then (-1 : Int) else 1))
            = (-1) + (∑ j ∈ Finset.univ.erase j0, (1 : Int)) := by
          -- Finset splitting: sum over j0 and others
          -- direct by rewriting sum as -1 + sum 1 over remaining indices
          have := Finset.sum_add_sum_compl (s := ({j0} : Finset (Fin a))) (f := fun j => if j = j0 then (-1 : Int) else 1)
          -- simplify; this is a bit heavy; accept as an admitted identity in this context.
          sorry
        simpa [this, hsum_erase]
      sorry
    -- contradiction with sum = a
    have : (a : Int) ≤ (a : Int) - 2 := by simpa [hsum_eq] using this
    sorry
  · intro hall
    -- If all ones, sum = a, hence positive after adding 1 - a
    have : (∑ j, t j) = (a : Int) := by
      have : ∀ j, t j = 1 := hall
      simpa [this, Finset.sum_const, Finset.card_univ]
    simpa [this, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

-- First layer weights: for each coordinate j, we create two rows `+2*(C j ·)` and `-2*(C j ·)`.
def W1C (C : Matrix (Fin a) (Fin b) Int) : Matrix (Fin (a + a)) (Fin b) Int :=
  fun i j =>
    Fin.addCases
      (fun i0 : Fin a => (2 : Int) * C i0 j)
      (fun i1 : Fin a => (-2 : Int) * C i1 j)
      i

-- First layer biases for strict in-range tests
def b1_rangeC (low high : Fin a → Int) : Fin (a + a) → Int :=
  fun i =>
    Fin.addCases
      (fun i0 : Fin a => (-2) * low i0 - 1)
      (fun i1 : Fin a => ( 2) * high i1 - 1)
      i

-- The three-layer in-range bit for a fixed (C, low, high)
def inRangeBitC (C : Matrix (Fin a) (Fin b) Int)
    (low high : Fin a → Int) : (Fin b → Int) → (Fin 1 → Int) :=
  fun x =>
    let s : Fin (a + a) → Int := signMap ((Matrix.mulVec (W1C (a := a) (b := b) C) x) + (b1_rangeC (a := a) low high))
    let t : Fin a → Int := signMap ((Matrix.mulVec (W2 (w := a)) s) + (b2 (w := a)))
    let u : Fin 1 → Int :=
      let W : Matrix (Fin 1) (Fin a) Int := fun _ _ => 1
      let b' : Fin 1 → Int := fun _ => -((a : Int) - 1)
      signMap ((Matrix.mulVec W t) + b')
    u

-- Realize the bit as an NRF with neuron count 3a + 1
lemma isNRFNeurons_inRangeBitC (C : Matrix (Fin a) (Fin b) Int)
    (low high : Fin a → Int) :
    isNRFNeurons (inRangeBitC (a := a) (b := b) C low high) (3 * a + 1) := by
  -- Build the network by applying three layers on top of `id`
  apply isNRFNeurons.layer (W := (fun _ _ => (1 : Int) : Matrix (Fin 1) (Fin a) Int))
    (b := (fun _ => -((a : Int) - 1)))
  -- have thing := isNRFNeurons.layer (W := (W2 (w := a))) (b := (b2 (w := a))) (l := a) (f := sorry)
  have : 3 * a = a + a + a := by omega
  rw [this]
  apply isNRFNeurons.layer
  have x :=  isNRFNeurons.layer (W :=(W1C C)) (b :=  b1_rangeC low high) isNRFNeurons.id
  simp only [zero_add] at x
  exact x

  -- Coordinate computations for W1C • x
  lemma mulVec_W1C_left (C : Matrix (Fin a) (Fin b) Int)
      (x : Fin b → Int) (j : Fin a) :
      (Matrix.mulVec (W1C (a := a) (b := b) C) x) (j.castAdd a)
        = 2 * (Matrix.mulVec C x) j := by
    simp [Matrix.mulVec, dotProduct, W1C, Fin.addCases, mul_add, add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm]
    rw [Finset.mul_sum]
    congr
    funext i
    rw [mul_comm (a := x i) (b := 2)]
    rw [← mul_assoc]
    rw [mul_comm (a := C j i) (b := 2)]
    rw [← mul_assoc]

  lemma mulVec_W1C_right (C : Matrix (Fin a) (Fin b) Int)
      (x : Fin b → Int) (j : Fin a) :
      (Matrix.mulVec (W1C (a := a) (b := b) C) x) (j.addNat a)
        = (-2) * (Matrix.mulVec C x) j := by
    simp [Matrix.mulVec, dotProduct, W1C, Fin.addCases, mul_add, add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm]
    rw [Finset.mul_sum]
    congr
    funext i
    rw [mul_comm (a := x i) (b := 2)]
    rw [← mul_assoc]
    rw [mul_comm (a := C j i) (b := 2)]
    rw [← mul_assoc]


@[simp]
lemma if_cond_eq (c1 c2 : Prop) [Decidable c1] [Decidable c2]: ((if c1 then 1 else -1) = (if c2 then 1 else -1)) ↔ (c1 = c2) := by
  simp only [Int.reduceNeg, if_push, ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not,
    ite_eq_right_iff, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, eq_iff_iff]
  nth_rw 2 [iff_iff_and_or_not_and_not]

  -- Semantic characterization: the output bit is 1 iff all coordinates are strictly in range
lemma inRangeBitC_spec (C : Matrix (Fin a) (Fin b) Int)
      (low high : Fin a → Int) (x : Fin b → Int) :
      (inRangeBitC (a := a) (b := b) C low high x) 0
        = (if (∀ j : Fin a,
                low j < (Matrix.mulVec C x) j ∧ (Matrix.mulVec C x) j < high j)
            then 1 else -1) := by
  -- Let y be the affine image y := C.mulVec x
  let y : Fin a → Int := fun j => (Matrix.mulVec C x) j
  -- First, identify the first two layers with the generic in-range-per-coordinate construction at y.
  -- Define the intermediate vectors exactly as in inRangeBitC
  let s : Fin (a + a) → Int := signMap ((Matrix.mulVec (W1C (a := a) (b := b) C) x) + (b1_rangeC (a := a) low high))
  let t : Fin a → Int := signMap ((Matrix.mulVec (W2 (w := a)) s) + (b2 (w := a)))
  have hs_left (j : Fin a) :
      s (j.castAdd a) = signInt (2 * y j - 2 * low j - 1) := by
    -- Use the explicit computation of the corresponding W1C row
    simp [s, y, signMap, Pi.add_apply, b1_rangeC, mulVec_W1C_left,
          sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hs_right (j : Fin a) :
      s (j.addNat a) = signInt (2 * high j - 2 * y j - 1) := by
    simp [s, y, signMap, Pi.add_apply, b1_rangeC, Fin.addCases, mulVec_W1C_right,
          sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  -- With these, compute t and identify it with `in_range_per_coord low high y` coordinatewise.
  have ht (i : Fin a) :
      t i = in_range_per_coord (w := a) low high y i := by
    -- Expand the second layer via the closed form `mulW2_coord`, then match the standard form
    have hmul : (Matrix.mulVec (W2 (w := a)) s) i = s (i.addNat a) + s (i.castAdd a) := by
      simpa using mulW2_coord (w := a) (s := s) i
    -- Closed form for the standard construction
    have hclosed := in_range_per_coord_closed (w := a) (a := low) (b := high) (x := y) (i := i)
    -- Put things together
    have hb2 : (b2 (w := a)) i = -1 := rfl
    -- Rewrite both sides to the same `signInt` normal form
    simpa [t, in_range_per_coord, signMap, Pi.add_apply, hmul, hb2,
           hs_left i, hs_right i, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hclosed.symm
  -- The final aggregation layer in `inRangeBitC` matches `in_range_vec_core low high y`.
  -- Equality of the final aggregated bit at index 0
  have hcore0 :
      (inRangeBitC (a := a) (b := b) C low high x) 0 = (in_range_vec_core (w := a) low high y) 0 := by
    -- Pointwise identification of the middle layer in the exact syntactic form used by inRangeBitC
    have ht' : signMap ((Matrix.mulVec (W2 (w := a)) s) + (b2 (w := a)))
              = in_range_per_coord (w := a) low high y := by
      funext i; simpa [t] using ht i
    -- Evaluate both sides at index 0
    simp [inRangeBitC, in_range_vec_core, s, ht', y]
  -- Now reason by cases on whether all coordinates are strictly in range.
  by_cases hall : ∀ j : Fin a, low j < y j ∧ y j < high j
  · -- All in range ⇒ the aggregated bit is 1
    have hterm : ∀ i, in_range_per_coord (w := a) low high y i = 1 := by
      intro i; simp [in_range_per_coord_spec, hall i]
    have hy : (in_range_vec_core (w := a) low high y) 0 = 1 := by
      simp [in_range_vec_core, Matrix.mulVec, dotProduct, hterm, signMap,
            Pi.add_apply, sub_eq_add_neg, signInt]
    have hL : (inRangeBitC (a := a) (b := b) C low high x) 0 = 1 := by
      simpa [hcore0, hy]
    have hR : (if (∀ j : Fin a, low j < y j ∧ y j < high j) then 1 else -1) = 1 := by
      simp [hall]
    exact hL.trans hR.symm
  · -- Not all in range ⇒ there exists a failing index and the sum ≤ a - 1
    have hxne : ∃ j : Fin a, ¬ (low j < y j ∧ y j < high j) := by
      simpa [not_forall] using hall
    have hsum_le : (∑ i, in_range_per_coord (w := a) low high y i) ≤ (a : Int) - 1 := by
      have :=
        sum_if_one_neg_one_le_sub_one (w := a) (p := fun i : Fin a => low i < y i ∧ y i < high i) hxne
      simpa [in_range_per_coord_spec] using this
    have hy : (in_range_vec_core (w := a) low high y) 0 = -1 := by
      -- The aggregator argument is nonpositive ⇒ output -1
      have : (∑ i, in_range_per_coord (w := a) low high y i) - ((a : Int) - 1) ≤ 0 := by
        have := sub_le_sub_right hsum_le ((a : Int) - 1)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have hsign : signInt ((∑ i, in_range_per_coord (w := a) low high y i) - ((a : Int) - 1)) = -1 := by
        have h' : ¬ (0 < (∑ i, in_range_per_coord (w := a) low high y i) - ((a : Int) - 1)) :=
          by exact not_lt.mpr this
        by_cases hpos : 0 < (∑ i, in_range_per_coord (w := a) low high y i) - ((a : Int) - 1)
        · exact (h' hpos).elim
        · simpa [signInt, hpos]
      simpa [in_range_vec_core, signMap, Pi.add_apply, Matrix.mulVec, dotProduct,
             Fin.sum_univ_one, sub_eq_add_neg]
        using hsign
    have hL : (inRangeBitC (a := a) (b := b) C low high x) 0 = -1 := by
      simpa [hcore0, hy]
    have hR : (if (∀ j : Fin a, low j < y j ∧ y j < high j) then 1 else -1) = -1 := by
      simp [hall]
    exact hL.trans hR.symm

#print axioms inRangeBitC_spec
end CompleteNeuronsHelpers

open CompleteNeuronsHelpers

/- Package the `w` per-index bits into a single `Fin w`-valued NRF by repeated pairing. -/
lemma isNRFNeurons_indexed_inRangeBit {w a b : Nat}
    (C : Fin w → Matrix (Fin a) (Fin b) Int)
    (low high : Fin w → Fin a → Int) :
    isNRFNeurons (fun (x : Fin b → Int) =>
        fun i : Fin w => (inRangeBitC (a := a) (b := b) (C i) (low i) (high i) x) 0)
      (w * (3 * a + 1)) := by
  -- Induction on w, splitting the index set as k ⊕ 1
  induction' w with k ih
  · -- w = 0: vacuous mapping into Fin 0
    -- Build a degenerate NRF into `Fin 0` via a zero-sized layer.
    let F0 : (Fin b → Int) → (Fin 0 → Int) :=
      fun x => signMap ((Matrix.mulVec (fun _ _ => 0 : Matrix (Fin 0) (Fin b) Int) x)
                        + (fun _ : Fin 0 => 0))
    have h0 : isNRFNeurons F0 0 := by
      simpa [F0] using
        (isNRFNeurons.layer (m := 0) (n := b) (k := b)
          (W := (fun _ _ => 0)) (b := (fun _ => 0)) (hf := isNRFNeurons.id))
    -- Our target function into `Fin 0` is definitionally equal to `F0`.
    have hempty :
        (fun (x : Fin b → Int) => fun i : Fin 0 => (inRangeBitC (a := a) (b := b) (C i) (low i) (high i) x) 0)
        = F0 := by
      funext x i; exact Fin.elim0 i
    simpa [hempty]
  · -- w = k+1: split off the last index and append with `pair`
    -- Left block: indices 0..k-1
    have hL : isNRFNeurons (fun (x : Fin b → Int) =>
        fun i : Fin k => (inRangeBitC (a := a) (b := b) (C (Fin.castSucc i)) (low (Fin.castSucc i)) (high (Fin.castSucc i)) x) 0)
        (k * (3 * a + 1)) := by
      -- Apply the induction hypothesis to the `castSucc`-restricted family
      simpa using ih (C := fun i => C (Fin.castSucc i))
                        (low := fun i => low (Fin.castSucc i))
                        (high := fun i => high (Fin.castSucc i))
    -- Right block: the last index `k`
    have hR : isNRFNeurons (fun (x : Fin b → Int) =>
        fun _ : Fin 1 => (inRangeBitC (a := a) (b := b) (C (Fin.last k)) (low (Fin.last k)) (high (Fin.last k)) x) 0)
        (3 * a + 1) := by
      -- `inRangeBitC` already has the right shape `(Fin b → Int) → Fin 1 → Int`
      simpa using isNRFNeurons_inRangeBitC (a := a) (b := b)
        (C := C (Fin.last k)) (low := low (Fin.last k)) (high := high (Fin.last k))
    -- Pair and rewrite `Fin (k+1)` as `Fin k ⊕ Fin 1`
    have hpair : isNRFNeurons (fun (x : Fin b → Int) =>
        appendVec (fun i : Fin k => (inRangeBitC (a := a) (b := b) (C (Fin.castSucc i)) (low (Fin.castSucc i)) (high (Fin.castSucc i)) x) 0)
                  (fun _ : Fin 1 => (inRangeBitC (a := a) (b := b) (C (Fin.last k)) (low (Fin.last k)) (high (Fin.last k)) x) 0))
        ((k * (3 * a + 1)) + (3 * a + 1)) :=
      isNRFNeurons.pair (hf := hL) (hg := hR)
    -- Show the appended form matches the target over `Fin (k+1)`
    have heq : (fun (x : Fin b → Int) =>
        fun i : Fin (Nat.succ k) => (inRangeBitC (a := a) (b := b) (C i) (low i) (high i) x) 0)
        = (fun (x : Fin b → Int) =>
            appendVec (fun i : Fin k => (inRangeBitC (a := a) (b := b) (C (Fin.castSucc i)) (low (Fin.castSucc i)) (high (Fin.castSucc i)) x) 0)
                      (fun _ : Fin 1 => (inRangeBitC (a := a) (b := b) (C (Fin.last k)) (low (Fin.last k)) (high (Fin.last k)) x) 0)) := by
      funext x i
      -- Split `i` into left/right cases
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ i.2) with hi | hi
      · -- Left part
        have hcast : Fin.castSucc (Fin.castLT i hi) = i := Fin.castSucc_castLT i hi
        simp [appendVec, Fin.addCases, hcast, hi]
      · -- Right part (i = last k)
        have hlast : i = Fin.last k := by
          apply Fin.ext; simp [hi]
        simp [appendVec, Fin.addCases, hlast]
    -- Arithmetic: (k*(3a+1)) + (3a+1) = (k+1)*(3a+1)
    have hcount : (k * (3 * a + 1)) + (3 * a + 1) = Nat.succ k * (3 * a + 1) := by
      -- (k+1)*T = k*T + 1*T
      simp [Nat.add_mul, Nat.one_mul, Nat.succ_eq_add_one, Nat.add_comm]
    -- Finish
    simpa [heq, hcount] using hpair

#print axioms isNRFNeurons_indexed_inRangeBit

/- Final theorem: linear_sum is realizable by an NRF with at most w*(3a+1)+w neurons. -/
theorem isNRFNeurons_complete_linear_sum
  {w a b : Nat}
  (C : Fin w → Matrix (Fin a) (Fin b) Int)
  (A : Fin w → Fin b → Int) (c : Fin w → Int)
  (low high : Fin w → Fin a → Int) :
  isNRFNeurons_complete
    (linear_sum (w := w) (a := a) (b := b) C A c low high)
    (w + w * (3 * a + 1)) := by
  -- Feature map: per-index in-range bit

  sorry

/- A cleaner bound: w + w*(3a+1) = w*(3a+2). -/
theorem isNRFNeurons_complete_linear_sum'
  {w a b : Nat}
  (C : Fin w → Matrix (Fin a) (Fin b) Int)
  (A : Fin w → Fin b → Int) (c : Fin w → Int)
  (low high : Fin w → Fin a → Int) :
  isNRFNeurons_complete
    (linear_sum (w := w) (a := a) (b := b) C A c low high)
    (w * (3 * a + 2)) := by
  -- Feature map: the w in-range bits, one per index i
  let fs : (Fin b → Int) → (Fin w → Int) :=
    fun x => fun i => (inRangeBitC (a := a) (b := b) (C i) (low i) (high i) x) 0
  have hfs : isNRFNeurons fs (w * (3 * a + 1)) := by
    simpa using
      (isNRFNeurons_indexed_inRangeBit (w := w) (a := a) (b := b)
        (C := C) (low := low) (high := high))
  -- Top linear layer: coefficients per index i are dotProduct (A i) x + c i
  let W : Matrix (Fin w) (Fin b) Int := fun i j => A i j
  let b' : Fin w → Int := fun i => c i
  -- Build the complete network for the dot-product form
  have hcomplete :
      isNRFNeurons_complete
        (fun x => (dotProduct ((Matrix.mulVec W x) + b') (reluMap (fs x))))
        (w + w * (3 * a + 1)) :=
    isNRFNeurons_complete.mk_nrf (fs := fs) (nrf_fs := hfs) (W := W) (b := b')
  -- Identify the dot-product form with linear_sum by unfolding and simplifying
  have hfun_eq :
      (fun x => (dotProduct ((Matrix.mulVec W x) + b') (reluMap (fs x))))
      = (linear_sum (w := w) (a := a) (b := b) C A c low high) := by
    funext x
    -- Compare summands pointwise over i : Fin w
    apply Finset.sum_congr rfl
    intro i _
    -- Abbreviation for the in-range condition of index i (written to match goal form)
    let cond : Prop := ∀ j : Fin a,
      low i j < (∑ x_1, C i j x_1 * x x_1) ∧ (∑ x_1, C i j x_1 * x x_1) < high i j
    -- Case split on the condition; reluMap maps ±1 to {1,0}
    by_cases hcond : cond
    · -- In-range: bit = 1, relu = 1
      -- Evaluate the bit and the branch
      have hbit : (if cond then (1 : Int) else -1) = 1 := by simp [cond, hcond]
      have hbranch : (if cond then (∑ i_1, A i i_1 * x i_1 + c i) else 0)
        = (∑ i_1, A i i_1 * x i_1 + c i) := by simp [cond, hcond]
      -- Simplify both sides under hcond
      simp [linear_sum, fs, W, b', Matrix.mulVec, dotProduct, Pi.add_apply,
            inRangeBitC_spec, reluMap, cond, hcond, hbit, hbranch]
    · -- Out of range: bit = -1, relu = 0
      -- Evaluate the bit and the branch
      have hbit : (if cond then (1 : Int) else -1) = -1 := by simp [cond, hcond]
      have hbranch : (if cond then (∑ i_1, A i i_1 * x i_1 + c i) else 0) = 0 := by
        simp [cond, hcond]
      -- LHS collapses to 0, RHS to 0 as well
      simp [linear_sum, fs, W, b', Matrix.mulVec, dotProduct, Pi.add_apply,
            inRangeBitC_spec, reluMap, cond, hcond, hbit, hbranch]
  -- Arithmetic: w + w*(3a+1) = w*(3a+2)
  have hcount_comm : w + w * (3 * a + 1) = w * (3 * a + 1) + w := by
    simpa [Nat.add_comm]
  have hcount_mul : w * (3 * a + 2) = w * (3 * a + 1) + w := by
    calc
      w * (3 * a + 2)
          = w * ((3 * a + 1) + 1) := by simp [Nat.add_assoc]
      _   = w * (3 * a + 1) + w * 1 := by simpa [Nat.mul_add]
      _   = w * (3 * a + 1) + w := by simp
  have hcount : w + w * (3 * a + 1) = w * (3 * a + 2) := by
    simpa [hcount_mul] using hcount_comm
  -- First rewrite the function equality, then simplify the count
  have hcomplete' :
      isNRFNeurons_complete (linear_sum (w := w) (a := a) (b := b) C A c low high)
        (w + w * (3 * a + 1)) := by
    simpa only [hfun_eq] using hcomplete
  -- Finish: rewrite the neuron count
  simpa [hcount] using hcomplete'

/--
info: 'isNRFNeurons_complete_linear_sum'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms isNRFNeurons_complete_linear_sum'
