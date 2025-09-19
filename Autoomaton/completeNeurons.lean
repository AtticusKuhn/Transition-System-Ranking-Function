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

  -- Semantic characterization: the output bit is 1 iff all coordinates are strictly in range
  lemma inRangeBitC_spec (C : Matrix (Fin a) (Fin b) Int)
      (low high : Fin a → Int) (x : Fin b → Int) :
      (inRangeBitC (a := a) (b := b) C low high x) 0
        = (if (∀ j : Fin a,
                low j < (Matrix.mulVec C x) j ∧ (Matrix.mulVec C x) j < high j)
            then 1 else -1) := by
    -- Unfold definition to expose the three stages s, t, u
    sorry

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
  -- Use the previous bound and simplify the arithmetic
  have h := isNRFNeurons_complete_linear_sum (w := w) (a := a) (b := b)
    C A c low high
  -- Rearrange: w + w*(3a+1) = w*(3a+1) + w = w*((3a+1)+1) = w*(3a+2)
  have hcomm : w + w * (3 * a + 1) = w * (3 * a + 1) + w := by
    simpa [Nat.add_comm]
  have hmulf : w * (3 * a + 2) = w * (3 * a + 1) + w := by
    calc
      w * (3 * a + 2)
          = w * ((3 * a + 1) + 1) := by simp [Nat.add_assoc]
      _   = w * (3 * a + 1) + w * 1 := by simpa [Nat.mul_add]
      _   = w * (3 * a + 1) + w := by simp
  have : w + w * (3 * a + 1) = w * (3 * a + 2) := by
    simpa [hmulf] using hcomm
  simpa [this] using h

#print axioms isNRFNeurons_complete_linear_sum'
