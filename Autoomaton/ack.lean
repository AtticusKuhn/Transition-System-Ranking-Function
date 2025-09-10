import Autoomaton.Buchi
import Autoomaton.NatRF
import Autoomaton.Ordinal2


def ackStep (p : (Nat × List Nat)) : (Nat × List Nat) :=
  match p with
  | (n, []) => (n, [])
  | (n, 0 :: c) => ((n + 1), c)
  | (0, (m + 1) :: c) =>  (1, m :: c)
  | (n + 1, (m + 1) :: c) => (n, (m + 1) :: m :: c)

-- def ackMax (p : Nat × List Nat) :  Nat  := match p with
--   | (x, []) => x
--   | (x, y :: ys) => ackMax (ack x y, ys)

def ackMax2 (x : Nat) (y : List Nat) :  Nat  := match y with
  | [] => x
  | y :: ys => ackMax2 (ack y x) ys




theorem ack_gt_4 (m a b: Nat) (le : a ≤ b): ack m a ≤ ack m b :=
  match m with
    | 0 => by
      simp only [ack_zero, add_le_add_iff_right, le]
    | m + 1 => by
      simp only [ack_le_iff_right, le]

def ack_gt_2 (m n: Nat) (le : 1 ≤ m) : m + n ≤ ack m n :=
  match m, n with
    | 0, n => by
      simp only [zero_add, ack_zero, le_add_iff_nonneg_right, zero_le]
    | m + 1, 0 => by
      simp only [add_zero, ack_succ_zero]
      match (Nat.decEq m 0) with
        | isTrue h =>  simp only [h, zero_add, ack_zero, Nat.reduceAdd, Nat.one_le_ofNat]
        | isFalse _ => exact ack_gt_2 m 1 (by omega);
    | m + 1, n + 1 =>
      match (Nat.decEq m 0) with
        | isTrue h => by
          simp only [h, zero_add, ack_succ_succ, ack_one, ack_zero]
          omega
        | isFalse _ => by
          have := ack_gt_2 m (m + 1 + n) (by omega);
          have := ack_gt_4 m (m + 1 + n) (ack (m + 1) n) (ack_gt_2 (m + 1) n le);
          simp only [ack_succ_succ, ge_iff_le]
          omega
termination_by (m, n)

#print axioms ack_gt_2

def ack_gt_5 (m n: Nat) : m + n ≤ ack m n := by
  by_cases h : m = 0
  simp only [h, zero_add, ack_zero, le_add_iff_nonneg_right, zero_le]
  have := ack_gt_2 m n (by omega)
  omega

theorem ack_gt_1 (m n: Nat) : n ≤ ack m n := by
  have := ack_gt_5 m n
  omega

theorem ackMax2_gt (x : Nat) (y : List Nat)  : x ≤ ackMax2 x y :=
  match y with
    | [] => by simp only [ackMax2, le_refl]
    | y :: ys => by
      simp only [ackMax2]
      have := ack_gt_1 y x
      have := ackMax2_gt (ack y x) ys
      omega

-- theorem ack_gt (n m: Nat) : ack m n ≥ n :=
--   match m, n with
--     | 0, n => by
--       simp
--     | m + 1, 0 => by
--       simp
--     | m + 1, n + 1 => by
--       simp [ack]
--       sorry

-- theorem ackMax_gt (n : Nat) (l  : List Nat) : ackMax2 n l ≥ n :=
--   match l with
--     | [] => by simp only [ackMax2, ge_iff_le, le_refl]
--     | y :: ys => by
--       simp [ackMax2]
--       have re := ackMax_gt (ack y n) ys

--       sorry

def ackMax (p : Nat × List Nat) : Nat := match p with
  | (x, ys) => ackMax2 x ys

def AckSystem : Automaton (Nat × List Nat) where
  R := fun a b => b = ackStep a
  I := fun ⟨_, y⟩  => y.length = 1
  F := fun ⟨_, y⟩ => y ≠ []

-- def ackRankf (p : Nat × List Nat) : Ordinal :=
--   match p with
--   | ⟨ x,  y⟩ => let m : Nat := ackMax (x, y)
--   (@y.foldrIdx Nat Ordinal (fun i b a => a + b * Ordinal.omega0 ^ (m - i)) Ordinal.zero.zero 0) + (m - x)
def ackRankf (p : Nat × List Nat) : Ordinal.{0} :=
  match p with
  | ⟨n, l⟩ =>
    let m : Nat := ackMax (n, l)
    let p : Ordinal := List.sum (@l.reverse.mapIdx Nat Ordinal (fun i a =>  a * Ordinal.omega0 ^ (m - i)))
    -- let p : OrdiniSupal := List.sum (@l.mapIdx Nat Ordinal (fun i a =>  a * Ordinal.omega0 ^ (m - l.length + 1 + i)))
    -- let p : Ordinal := @l.foldlIdx Ordinal Nat (fun i a b => b +  a * Ordinal.omega0 ^ (m - i)) (Ordinal.zero.zero) 0
    -- let p : Ordinal := @l.foldrIdx Nat Ordinal (fun i a b => b +  a * Ordinal.omega0 ^ (m - i)) (Ordinal.zero.zero) 0

    p + (m - n)


def test1 : Ordinal := ackRankf ⟨2, [2]⟩
def test2 : Nat := ackMax ⟨ 4, [1]⟩
def test3 : Nat := ackMax ⟨ 3, [2,1]⟩
def test4 : Nat := ackMax ⟨ 2, [2, 1, 1]⟩

-- ackMax2
-- #eval test2
-- #eval test3
-- #eval test4
#eval (ack 2 4)
#eval (ack 1 (ack 2 3))
#eval (ack 1 (ack 1 (ack 2 2)))
#eval (ackMax2 4 [2])
#eval (ackMax2 3 [2, 1])
-- #eval (ackRankf ⟨ 2, [2, 1, 1]⟩)

theorem t1 : ackRankf ⟨ 2, [2, 1, 1]⟩ = Ordinal.omega0^11 + Ordinal.omega0^10 + 2 * Ordinal.omega0^9 + 9  := by
  -- rfl
  simp [ackRankf, ackMax, ackMax2]
  -- rfl

  sorry
-- #reduce test1

-- theorem ord_lt (m : Ordinal.{0}) (t : Ordinal.{0}) : m - Order.succ t < m - t := by
--   sorry

universe u v
theorem mapIdx_append {α : Type u} {β : Type v} {f : ℕ → α → β} {l : List α} {e r : α} : List.mapIdx f (l ++ [e, r]) = List.mapIdx f l ++ [f l.length e, f l.length.succ r] := by
    rw [List.append_cons]
    simp only [List.mapIdx_concat, List.length_append, List.length_cons, List.length_nil, zero_add,
      List.nil_append, Nat.succ_eq_add_one]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem f  { n  : Nat}: (Order.succ n : Ordinal.{0}) = (Nat.succ n) := by
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Ordinal.add_one_eq_succ]
theorem g  { m n  : Nat}: (m : Ordinal.{0}) - (n : Ordinal.{0}) = (Nat.cast (m - n)) := by
  simp
theorem h  { m n  : Nat}:  (n : Ordinal.{0}) < m ↔ n < m := by
  simp
theorem h2  { m n  : Nat}:  (n : Ordinal.{0}) ≤  m ↔ n ≤  m := by
  simp
theorem ord_cmp {a1 a2 b1 b2 : Nat} : (a1 * Ordinal.omega0  + b1 <  a2 * Ordinal.omega0  + b2) ↔ (a1 < a2 ∨ (a1 = a2 ∧ b1 < b2)) := by
  sorry
  -- sorry

theorem ackRank_fair (s1 s2 : ℕ × List ℕ) (t : AckSystem.R s1 s2) (reach : State.IsReachable (a := AckSystem) s1 ):   AckSystem.F s1 → ackRankf s2 < ackRankf s1  :=
   match s1 with
      | (n, []) => by
        simp [AckSystem, ackRankf, ackStep] at t
        simp [t,AckSystem, ackRankf]
      | (n, 0 :: c) => by
        simp [AckSystem, ackRankf, ackStep] at t
        simp only [ackRankf, ackMax, t, List.mapIdx_reverse, Nat.cast_add, Nat.cast_one,
          Ordinal.add_one_eq_succ, AckSystem, ne_eq, decide_not, reduceCtorEq, decide_false,
          Bool.not_false, ↓reduceIte, ackMax2, ack_zero, List.reverse_cons, List.mapIdx_concat,
          Nat.cast_zero, List.length_reverse, zero_mul, List.sum_append, List.sum_cons,
          List.sum_nil, add_zero, add_lt_add_iff_left]
        simp
        rw [f (n := n)]
        repeat rw [g]
        rw [h]
        simp [ackMax2]
        have f := ackMax2_gt (n + 1) c
        omega
      | (0, (m + 1) :: c) =>  by
        simp [AckSystem, ackRankf, ackStep] at t
        simp [ackRankf, ackMax, t, ackMax2, List.reverse_cons, List.mapIdx_concat,
          List.mapIdx_reverse, List.length_reverse, List.sum_append, List.sum_cons, List.sum_nil,
          add_zero, Nat.cast_one, AckSystem, ne_eq, decide_not, reduceCtorEq, decide_false,
          Bool.not_false, ↓reduceIte, Ordinal.add_one_eq_succ, ack_succ_zero, Nat.cast_add,
          Nat.cast_zero, Ordinal.sub_zero, Order.succ_le_iff]
        -- simp [​add_lt_add_iff_left]
        -- simp [add_lt_add_iff_left]
        -- let f: Ordinal.{0} := (List.mapIdx (fun i a ↦ ↑a * Ordinal.omega0 ^ (ackMax2 (ack m 1) c - (c.length - 1 - i))) c).reverse.sum
        -- have feq : (f = (List.mapIdx (fun i a ↦ ↑a * Ordinal.omega0 ^ (ackMax2 (ack m 1) c - (c.length - 1 - i))) c).reverse.sum)  := by rfl
        -- rw [← feq]
        repeat rw [add_assoc]
        simp
        rw [f]
        -- rw [@g (ackMax2 (n + 1) c) n.succ]
        repeat rw [g,f, h]
        -- rw [h]
        -- simp [ackMax2]
        -- apply add_lt_add_of_lt_of_le
        -- linarith
        -- omega
        sorry
      | (n + 1, (m + 1) :: c) => by
        simp [AckSystem, ackRankf, ackStep] at t
        simp [t,AckSystem, ackRankf, ackMax, ack, ackMax2]
        rw [mapIdx_append]
        simp
        repeat rw [add_assoc]
        simp
        sorry
noncomputable def ackRank : OrdinalRankingFunction.{0} AckSystem where
  rank := ackRankf

  rank_le_of_rel_fair := ackRank_fair

  rank_le_of_rel_unfair := fun s1 s2 t =>
   match s1 with
      | (n, []) => by
        simp [AckSystem, ackRankf, ackStep] at t
        simp [t,AckSystem, ackRankf]
      | (n, 0 :: c) => by
        simp [AckSystem, ackRankf, ackStep] at t
        simp only [ackRankf, ackMax, t, List.mapIdx_reverse, Nat.cast_add, Nat.cast_one,
          Ordinal.add_one_eq_succ, AckSystem, ne_eq, decide_not, reduceCtorEq, decide_false,
          Bool.not_false, ↓reduceIte, ackMax2, ack_zero, List.reverse_cons, List.mapIdx_concat,
          Nat.cast_zero, List.length_reverse, zero_mul, List.sum_append, List.sum_cons,
          List.sum_nil, add_zero, add_lt_add_iff_left]
        simp
        rw [f]
        rw [@g (ackMax2 (n + 1) c) n.succ]
        rw [@g (ackMax2 (n + 1) c) n]
        rw [h2]
        simp [ackMax2]
        have f := ackMax2_gt (n + 1) c
        omega
        -- exact ord_lt (ackMax2 (n + 1) c) n
      | (0, (m + 1) :: c) =>  by
        simp [AckSystem, ackRankf, ackStep] at t
        simp [ackRankf, ackMax, t, ackMax2, List.reverse_cons, List.mapIdx_concat,
          List.mapIdx_reverse, List.length_reverse, List.sum_append, List.sum_cons, List.sum_nil,
          add_zero, Nat.cast_one, AckSystem, ne_eq, decide_not, reduceCtorEq, decide_false,
          Bool.not_false, ↓reduceIte, Ordinal.add_one_eq_succ, ack_succ_zero, Nat.cast_add,
          Nat.cast_zero, Ordinal.sub_zero, Order.succ_le_iff]
        -- simp [​add_lt_add_iff_left]
        -- simp [add_lt_add_iff_left]
        -- let f: Ordinal.{0} := (List.mapIdx (fun i a ↦ ↑a * Ordinal.omega0 ^ (ackMax2 (ack m 1) c - (c.length - 1 - i))) c).reverse.sum
        -- have feq : (f = (List.mapIdx (fun i a ↦ ↑a * Ordinal.omega0 ^ (ackMax2 (ack m 1) c - (c.length - 1 - i))) c).reverse.sum)  := by rfl
        -- rw [← feq]
        repeat rw [add_assoc]
        simp
        -- apply add_lt_add_of_lt_of_le
        -- linarith
        sorry
      | (n + 1, (m + 1) :: c) => by
        simp [AckSystem, ackRankf, ackStep] at t
        simp [t,AckSystem, ackRankf, ackMax, ack, ackMax2]
        rw [mapIdx_append]
        simp
        repeat rw [add_assoc]
        simp
        sorry

theorem ack_halts : AckSystem.IsFairEmpty := isFairEmpty_of_ordinalRankingFunction ackRank
