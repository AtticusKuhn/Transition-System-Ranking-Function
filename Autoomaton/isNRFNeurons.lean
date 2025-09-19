import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Autoomaton.isNRF


inductive isNRFNeurons : {m n: Nat} → ((Fin m → Int) → (Fin n → Int)) → Nat → Prop where
  | id : isNRFNeurons (fun x => x) 0
  | layer {m n k : Nat}
      (W : Matrix (Fin m) (Fin n) Int) (b : Fin m → Int)
      {f : (Fin k → Int) → (Fin n → Int)}
      {l : Nat}
      (hf : isNRFNeurons f l)
      : isNRFNeurons (fun x => signMap ((Matrix.mulVec W (f x)) + b)) (l + m)
  | pair {m n p : Nat}
      {f : (Fin m → Int) → (Fin n → Int)} {g : (Fin m → Int) → (Fin p → Int)}
      {a b : Nat}
      (hf : isNRFNeurons f a ) (hg : isNRFNeurons g b) :
      isNRFNeurons (fun x => appendVec (f x) (g x)) (a + b)

theorem nrf_neurons_g2 {a : Int}: isNRFNeurons (g2 a) 3 := by
  apply isNRFNeurons.layer
  apply isNRFNeurons.layer
  exact isNRFNeurons.id

theorem nrf_neurons_g {a : Int} : isNRFNeurons (g a) 3 := by
  simp [g_eq, ← g_eq_2]
  exact nrf_neurons_g2


theorem isNRF_neurons_f3  {w : Nat} (a : Fin w → Int) :
    isNRFNeurons (f3 a) (w + w + w + 1) := by
  apply isNRFNeurons.layer (W := (fun _ _ => (1 : Int))) (b := fun _ => -((w : Int) - 1))
  apply isNRFNeurons.layer (W := W2 (w := w)) (b := b2 (w := w))
  have x :=  isNRFNeurons.layer (W := W1 (w := w) (a := a)) (b := b1 (w := w) (a := a)) isNRFNeurons.id
  simp only [zero_add] at x
  exact x

theorem isNRF_neurons_f3'  {w : Nat} (a : Fin w → Int) :
    isNRFNeurons (f3 a) (3 * w + 1) := by
  have : 3 * w + 1 = (w + w + w + 1) := by omega
  simp only [this]
  exact isNRF_neurons_f3 a



theorem isNRF_neurons_f  {w : Nat} (a : Fin w → Int) : isNRFNeurons (f a) (3 * w + 1) := by
  simp only [f_eq_f2, f2_eq_f3]
  exact isNRF_neurons_f3' a


#print axioms isNRF_neurons_f



theorem is_NRF_neurons_in_range_2  (a b : Int) : isNRFNeurons (in_range_2 a b) 3:= by
  apply isNRFNeurons.layer
  apply isNRFNeurons.layer
  exact isNRFNeurons.id


def isNRF_neurons_in_range_vec_2  {w : Nat} (a b : Fin w → Int) : isNRFNeurons (in_range_vec_2 a b) ((w + w + w) + 1 + w) := by
  apply isNRFNeurons.layer
  apply isNRFNeurons.layer
  apply isNRFNeurons.layer
  have x :=  isNRFNeurons.layer (W := W1 (w := w) (a := a)) (b := b1_range a b) isNRFNeurons.id
  simp only [zero_add] at x
  exact x

def isNRF_neurons_in_range_vec_2'  {w : Nat} (a b : Fin w → Int) : isNRFNeurons (in_range_vec_2 a b) (4 * w + 1) := by
  have : 4 * w + 1 =(w + w + w) + 1 + w := by omega
  simp only [this]
  exact isNRF_neurons_in_range_vec_2 a b


-- Neuron count for the vector in-range tester, via equality with the constructed network
theorem isNRF_neurons_in_range_vec  {w : Nat} (a b : Fin w → Int) :
    isNRFNeurons (in_range_vec a b) (4 * w + 1) := by
  -- Rewrite to the layered construction and reuse its neuron count
  simp only [in_range_vec_eq (a := a) (b := b)]
  exact isNRF_neurons_in_range_vec_2' a b

#print axioms isNRF_neurons_in_range_vec
