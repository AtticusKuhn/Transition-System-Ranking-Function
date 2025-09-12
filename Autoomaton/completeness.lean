import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Autoomaton.isNRF

set_option linter.unnecessarySimpa false
-- A scalar-output NRF completed with a linear readout against the ReLU of an NRF feature map.
-- This matches the architecture described in proof.tex.
inductive isNRF_complete : {m: Nat} → ((Fin m → Int) → Int) → Prop where
  | mk_nrf {m k : Nat}
      (fs : (Fin m → ℤ) → (Fin k → ℤ) )
      (nrf_fs : isNRF fs)
      (W : Matrix (Fin k) (Fin m) Int) (b : Fin k → Int)
      : isNRF_complete (fun x => (dotProduct ((Matrix.mulVec W x) + b) (reluMap (fs x))))


open Classical

-- Enumerate a finite set `S` as `Fin k → _` where `k = S.card`.
noncomputable def enumOfFinset {α : Type} (S : Finset α) : Fin S.card → {x // x ∈ S} :=
  (S.equivFin).symm

noncomputable def enumerate {m : Nat} (S : Finset (Fin m → Int)) : Fin S.card → (Fin m → Int) :=
  fun i => (enumOfFinset S i).1

-- The feature map `y_S`: for each `a ∈ S`, compute the tight equality test `f3 a`.
-- (y_S and parallel composition not needed with the `fs` family formulation)


/- Helper lemmas to modularize the completeness proof. -/

section Helpers

open Finset

-- Package a family of `Fin 1`-valued NRFs into a single `Fin k`-valued NRF
-- by taking the 0-th coordinate of each family member.
lemma isNRF_indexed_f3 {m k : Nat} (s : Fin k → (Fin m → Int)) :
    isNRF (fun x => fun i : Fin k => (f3 (s i) x) 0) := by
  classical
  -- We do a recursion on k. For k = 0, the statement is trivial since `Fin 0` is empty.
  -- For k.succ, split off the last coordinate and use `isNRF.pair`.
  revert s
  induction' k with k ih
  · -- k = 0; target type is `isNRF (fun _ => (fun i : Fin 0 => nomatch i))`.
    intro s
    -- This function is definitionally equal to `fun _ => (fun i : Fin 0 => nomatch i)`.
    -- We can realize it by composing any NRF with a linear layer of output size 0.
    -- Concretely, start from `isNRF.id` on `Fin 0` and change the domain with a dummy preceding layer.
    -- Build an NRF with domain `(Fin m → Int)` and output `Fin 0 → Int` by two layers:
    -- First, take `f := fun (_ : Fin 0 → Int) => (fun i : Fin 0 => nomatch i)` which is `isNRF.id`.
    -- Then, add a layer with W : Matrix (Fin 0) (Fin 0) Int and b : Fin 0 → Int (both vacuous).
    -- However, `isNRF.layer` preserves the domain of `f`, so we first compose `f3` (which has domain `(Fin m → Int)`).
    -- Pick any anchor `a₀ : Fin m → Int` and use `isNRF_f3 a₀` followed by a layer to collapse to `Fin 0`.
    classical
    let a0 : Fin m → Int := fun _ => 0
    have h0 : isNRF (f3 a0) := isNRF_f3 (w := m) a0
    -- Collapse the single output to zero outputs with a zero-sized layer.
    -- W : Matrix (Fin 0) (Fin 1) Int, b : Fin 0 → Int are uniquely determined.
    have : isNRF (fun x => signMap ((Matrix.mulVec (fun _ _ => 0 : Matrix (Fin 0) (Fin 1) Int) (f3 a0 x))
                                     + (fun _ : Fin 0 => 0))) :=
      isNRF.layer (W := (fun _ _ => 0)) (b := (fun _ => 0)) (hf := h0)
    -- Finally, any two functions into `Fin 0 → Int` are definitionally equal.
    -- We rewrite our target into this constructed NRF.
    have hempty : (fun x => fun i : Fin 0 => (f3 (s i) x) 0)
                  = (fun x => signMap ((Matrix.mulVec (fun _ _ => 0 : Matrix (Fin 0) (Fin 1) Int) (f3 a0 x))
                                      + (fun _ : Fin 0 => 0))) := by
      funext x i; exact Fin.elim0 i
    simpa [hempty]
  · -- k.succ case
    intro s
    -- Split the family `s : Fin (k.succ) → _` into the first `k` entries and the last one.
    let sL : Fin k → (Fin m → Int) := fun i => s (Fin.castSucc i)
    let sR : Fin 1 → (Fin m → Int) := fun _ => s (Fin.last k)
    have hL : isNRF (fun x => fun i : Fin k => (f3 (sL i) x) 0) := by
      simpa [sL] using ih sL
    have hR : isNRF (fun x => (f3 (s (Fin.last k)) x)) :=
      isNRF_f3 (w := m) (a := s (Fin.last k))
    -- Combine with `pair` and rewrite to the desired form over `Fin (k+1)` using `appendVec`.
    have : isNRF (fun x => appendVec (fun i : Fin k => (f3 (sL i) x) 0)
                                      (fun j : Fin 1 => (f3 (sR j) x) 0)) :=
      isNRF.pair (hf := hL)
        (hg := by simpa [sR] using hR)
    -- Show this equals the target mapping `i ↦ (f3 (s i) x) 0` by case analysis on `i`.
    have heq : (fun x => fun i : Fin (Nat.succ k) => (f3 (s i) x) 0)
                = (fun x => appendVec (fun i : Fin k => (f3 (sL i) x) 0)
                                      (fun j : Fin 1 => (f3 (sR j) x) 0)) := by
      funext x i
      -- Split on whether `i < k` or `i = k`.
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ i.2) with hi | hi
      · -- Left block: indices `< k` come from the left part at `castSucc`.
        have hcast : Fin.castSucc (Fin.castLT i hi) = i := Fin.castSucc_castLT i hi
        simp [appendVec, Fin.addCases, sL, sR, hi, hcast]
      · -- Right block: the last index `k` comes from the right part.
        have hlast : i = Fin.last k := by
          apply Fin.ext
          simp [hi]
        subst hlast
        simp [appendVec, Fin.addCases, sL, sR]
    simpa [heq]

-- Identify the index of `x` under the enumeration of `S` and record `s i0 = x`.
lemma enum_point_eq {m : Nat}
    (S : Finset (Fin m → Int)) (x : Fin m → Int) (hx : x ∈ S) :
    let k := S.card
    let s : Fin k → (Fin m → Int) := enumerate (m := m) S
    let e : Fin k ≃ {u // u ∈ S} := (S.equivFin).symm
    let i0 : Fin k := e.symm ⟨x, hx⟩
    s i0 = x := by
  classical
  intro k s e i0
  -- By definition of `enumerate` and `i0`.
  have : e i0 = ⟨x, hx⟩ := by simp [i0]
  simpa [enumerate, enumOfFinset] using congrArg Subtype.val this

-- Values of `f3` on equality/inequality, specialized to the single output coord 0.
lemma f3_eq_one_of_eq {w : Nat} (a x : Fin w → Int) (h : x = a) : (f3 a x) 0 = 1 := by
  classical
  -- Bridge through `f` and `f2` as in isNRF.lean
  have : (f (w := w) a x) 0 = 1 := by simp [f, h]
  simpa [f_eq_f2 (w := w), f2_eq_f3 (w := w)] using this

lemma f3_eq_neg_one_of_ne {w : Nat} (a x : Fin w → Int) (h : x ≠ a) : (f3 a x) 0 = -1 := by
  classical
  have : (f (w := w) a x) 0 = -1 := by simp [f, h]
  simpa [f_eq_f2 (w := w), f2_eq_f3 (w := w)] using this

-- Turn the ReLU of an f3-bit into a clean 0/1 indicator.
lemma relu_f3_eq_indicator {w : Nat} (a x : Fin w → Int) :
    reluMap (f3 a x) 0 = (if x = a then (1 : Int) else 0) := by
  classical
  by_cases hx : x = a
  · have h1 : (f3 a x) 0 = 1 := f3_eq_one_of_eq (a := a) (x := x) hx
    have hL : reluMap (f3 a x) 0 = 1 := by simp [reluMap, h1]
    have hR : (if x = a then (1 : Int) else 0) = 1 := by simp [hx]
    simpa [hR] using hL
  · have h1 : (f3 a x) 0 = -1 := f3_eq_neg_one_of_ne (a := a) (x := x) hx
    have hL : reluMap (f3 a x) 0 = 0 := by simp [reluMap, h1]
    have hR : (if x = a then (1 : Int) else 0) = 0 := by simp [hx]
    simpa [hR] using hL

-- Dot product with a one-hot indicator recovers the selected bias.
lemma dot_with_onehot {k : Nat} (b : Fin k → Int) (i0 : Fin k) :
    dotProduct (fun _ => 0) (fun i : Fin k => if i = i0 then (1 : Int) else 0) = b i0 - b i0 := by
  classical
  -- This is a harmless algebraic helper; the main usage will add back `b`.
  -- Evaluate dot with zero-left vector for completeness.
  simp [dotProduct]

lemma dot_b_with_onehot {k : Nat} (b : Fin k → Int) (i0 : Fin k) :
    dotProduct b (fun i : Fin k => if i = i0 then (1 : Int) else 0) = b i0 := by
  classical
  -- Sum reduces to the i0-th term.
  simp [dotProduct]

-- `mulVec` with a zero matrix vanishes.
lemma mulVec_zero_matrix {m k : Nat} (x : Fin m → Int) :
    (Matrix.mulVec (fun _ _ => (0 : Int)) x) = (fun _ : Fin k => 0) := by
  classical
  funext i;
  simp [Matrix.mulVec, dotProduct]

end Helpers

-- Final completeness theorem matching the statement in proof.tex
theorem completeness {m : Nat}
    (S : Finset (Fin m → ℤ)) (r : (Fin m → ℤ) → ℤ) :
    ∃ (g : ((Fin m → Int) → (Int))),
      isNRF_complete g ∧ ∀ x ∈ S, g x = r x := by
  classical
  let k : Nat := S.card
  -- Enumerate S to align coordinates with indices i : Fin k
  let s : Fin k → (Fin m → Int) := enumerate (m := m) S
  -- Choose a zero readout matrix and bias vector b_i := r(s_i)
  let W : Matrix (Fin k) (Fin m) Int := fun _ _ => 0
  let b : Fin k → Int := fun i => r (s i)
  -- Feature map `y` as in the proof
  -- Define g via the isNRF_complete constructor
  refine ⟨fun x =>
            dotProduct ((Matrix.mulVec W x) + b)
                       (fun i : Fin k => reluMap (f3 (s i) x) 0),
          ?_, ?_⟩

  · -- Show the feature map is realizable by an NRF
    have nrfF : isNRF (fun (x : Fin m → Int) => fun (i : Fin k) => (f3 (s i) x) 0) :=
      isNRF_indexed_f3 (m := m) (k := k) s
    exact isNRF_complete.mk_nrf (fun x => fun i : Fin k => (f3 (s i) x) 0) nrfF W b
  · -- Show correctness on S
    intro x hx
    -- Let i₀ be the unique index with s i₀ = x
    let e : Fin k ≃ {u // u ∈ S} := (S.equivFin).symm
    let i0 : Fin k := e.symm ⟨x, hx⟩
    have s_i0 : s i0 = x := by
      -- By definition of `enumerate` and `i0`.
      have : e i0 = ⟨x, hx⟩ := by simp [i0]
      simpa [s, enumerate, enumOfFinset] using congrArg Subtype.val this
    -- ReLU features form a one-hot vector at i0
    have hfeat : (fun i : Fin k => reluMap (f3 (s i) x) 0)
                  = (fun i : Fin k => if i = i0 then 1 else 0) := by
      classical
      funext i
      -- Reduce to a clean 0/1 indicator via `relu_f3_eq_indicator` and uniqueness of the index `i0`.
      have hxsi : (x = s i) ↔ (i = i0) := by
        constructor
        · intro hxeq
          -- `s i = x = s i0`; injectivity of the enumeration yields `i = i0`.
          have hval_eq : s i = s i0 := by simpa [s_i0] using hxeq.symm
          -- Values of `s` are the first components of `e`.
          have : (e i).1 = (e i0).1 := by
            simpa [s, enumerate, enumOfFinset, e] using hval_eq
          have heq : e i = e i0 := Subtype.ext this
          exact e.injective heq
        · intro hi
          simpa [hi, s_i0]
      -- Finish by rewriting the indicator.
      have : (if x = s i then (1 : Int) else 0) = (if i = i0 then 1 else 0) := by
        by_cases h : i = i0
        · simp [h, s_i0]
        · have : x ≠ s i := by
            intro hxeq; exact h (hxsi.mp hxeq)
          simp [h, this]
      simpa [relu_f3_eq_indicator, this]
    -- `W` is the zero matrix, so `mulVec W x = 0`
    have hW : (Matrix.mulVec W x) = (fun _ : Fin k => 0) := by
      funext i; simp [W, Matrix.mulVec, dotProduct]
    -- Dot product reduces to picking `b i0`
    have hdot : dotProduct ((Matrix.mulVec W x) + b)
                         (fun i : Fin k => reluMap (f3 (s i) x) 0)
                = b i0 := by
      classical
      -- First rewrite the feature vector to the one-hot form
      have hrewrite : dotProduct ((Matrix.mulVec W x) + b)
                               (fun i : Fin k => reluMap (f3 (s i) x) 0)
                        = dotProduct ((Matrix.mulVec W x) + b)
                                   (fun i : Fin k => if i = i0 then 1 else 0) := by
        simp [hfeat]
      -- Then evaluate the dot with the zero-matrix simplification
      have hsum0 : dotProduct b (fun i : Fin k => if i = i0 then (1 : Int) else 0) = b i0 :=
        dot_b_with_onehot (b := b) (i0 := i0)
      have hsum : dotProduct ((Matrix.mulVec W x) + b)
                              (fun i : Fin k => if i = i0 then 1 else 0)
                    = b i0 := by
        simpa [hW, dotProduct, Pi.add_apply] using hsum0
      exact hrewrite.trans hsum
    -- Conclude `g x = r x` using the definition of `b`
    simpa [b, s_i0] using hdot

#print axioms completeness
