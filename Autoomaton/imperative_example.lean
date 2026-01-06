import Autoomaton.Buchi
import Mathlib.Data.Vector.Basic
import Autoomaton.imperative_language
import Autoomaton.imperative_dsl

/-! ## Basic sanity checks -/

section Tests

example {vars : Nat} : (StatementToAutomaton (vars := vars) (stmt| skip)).IsFairEmpty := by
  simp only [Automaton.IsFairEmpty, StatementToAutomaton, ne_eq, Run.IsFairEmpty, Run.IsUnfair,
    Run.IsFair, gt_iff_lt, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, not_forall, not_exists, not_and, Decidable.not_not]
  intro r
  use 0
  intros x x_pos
  induction' x with x ih
  · simp only [lt_self_iff_false] at x_pos
  ·
    have := r.is_valid x
    have i := r.is_init
    simp at this
    simp at i
    by_cases h : x = 0
    · simp [h] at this
      simp [h]
      -- cases this
      sorry
    · have xpos : 0 < x := by omega
      have ih := ih xpos

      sorry
  -- exact hfalse

private def σ0 : List.Vector Int 0 := List.Vector.nil
private def c0 : Expression 0 .bool := (bexpr| 0 < 1)
private def loop0 : Statement 0 := (stmt| while 0 < 1 do skip)
private def loop0Seq : Statement 0 := .sequence .skip loop0

private theorem evalBool_c0 : Expression.evalBool σ0 c0 = true := by
  simp [c0, Expression.evalBool, Expression.evalInt]

private def loopState : Nat → ProgramState 0
  | n =>
      if n % 2 = 0 then
        ⟨loop0, σ0⟩
      else
        ⟨loop0Seq, σ0⟩

private theorem loopState_step (n : Nat) :
    Step (loopState n) (loopState n.succ) := by
  by_cases hn : n % 2 = 0
  · have hsucc : n.succ % 2 ≠ 0 := by
      intro hsucc0
      have hn1 : n % 2 = 1 := (Nat.succ_mod_two_eq_zero_iff).1 hsucc0
      have h01 : (0 : Nat) = 1 := by
        have hn1' := hn1
        rw [hn] at hn1'
        exact hn1'
      exact Nat.zero_ne_one h01
    have hstep :
        Step (vars := 0) ⟨loop0, σ0⟩ ⟨loop0Seq, σ0⟩ := by
      -- `while (0 < 1) do skip` steps to `skip ; while (0 < 1) do skip`.
      simpa [loop0, loop0Seq] using (Step.while_true (c := c0) (body := .skip) (σ := σ0) evalBool_c0)
    simpa [loopState, hn, hsucc] using hstep
  · have hn1 : n % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
      · exact (hn hn0).elim
      · exact hn1
    have hsucc : n.succ % 2 = 0 := (Nat.succ_mod_two_eq_zero_iff).2 hn1
    have hstep : Step (vars := 0) ⟨loop0Seq, σ0⟩ ⟨loop0, σ0⟩ := by
      simpa [loop0Seq] using (Step.seq_skip (s₂ := loop0) (σ := σ0))
    simpa [loopState, hn, hsucc] using hstep

private def loopRun : Run (StatementToAutomaton loop0) where
  f := loopState
  is_init := by
    simp [StatementToAutomaton, loopState]
  is_valid := by
    intro n
    simpa [StatementToAutomaton] using loopState_step n

example : ¬ (StatementToAutomaton loop0).IsFairEmpty := by
  intro h
  have r : Run (StatementToAutomaton loop0) := loopRun
  have hrFair : r.IsFair := by
    intro n
    refine ⟨n.succ, Nat.lt_succ_self n, ?_⟩
    simp [StatementToAutomaton]

    sorry
  exact (h r) hrFair

end Tests


private def countUp : Statement 1 := (stmt|
  v[0] := 0;
  while v[0] < 100 do
    0 := v[0] + 1
  )

#print countUp

/-! ### Termination example -/

/-- `countUp` terminates: every run of its compiled automaton eventually stays at `skip`. -/
theorem countUp_halts : (StatementToAutomaton countUp).IsFairEmpty := by
  simp [StatementToAutomaton]
  intro r
  refine ⟨303, ?_⟩
  intro x hx
  classical
  let i0 : Fin 1 := Fin.ofNat 1 0
  let cond : Expression 1 .bool := (bexpr| v[0] < 100)
  let body : Statement 1 := (stmt| 0 := v[0] + 1)
  let loop : Statement 1 := .whileLoop cond body

  have hinit : (r.f 0).currentStatement = countUp := by
    simpa using r.is_init

  cases hS0 : r.f 0 with
  | mk s0 σ0 =>
    have hs0 : s0 = countUp := by
      simpa [hS0] using hinit
    subst hs0

    -- First two small-steps: assignment, then `skip ; s ↦ s`.
    generalize hs1 : r.f 1 = s1
    have h01 : Step ⟨countUp, σ0⟩ s1 := by
      simpa [hS0, hs1] using r.is_valid 0
    have hs1' : s1 = ⟨.sequence .skip loop, σ0.set i0 0⟩ := by
      have h01' : Step ⟨.sequence (.assign i0 (iexpr| 0)) loop, σ0⟩ s1 := by
        simpa [countUp, loop, body, cond] using h01
      cases h01' with
      | seq_left s₁ s₂ s₁' σ σ' hs₁ h =>
        cases h with
        | assign x rhs σ =>
          simp [Expression.evalInt, loop] at *
    have hf1 : r.f 1 = ⟨.sequence .skip loop, σ0.set i0 0⟩ := by
      simp [hs1, hs1']

    generalize hs2 : r.f 2 = s2
    have h12 : Step (r.f 1) s2 := by
      simpa [hs2] using r.is_valid 1
    have h12' : Step ⟨.sequence .skip loop, σ0.set i0 0⟩ s2 := by
      simpa [hf1] using h12
    have hs2' : s2 = ⟨loop, σ0.set i0 0⟩ := by
      cases h12' with
      | seq_left s₁ s₂ s₁' σ₁ σ' hs₁ h => sorry
      | seq_skip s₂ σ =>
        rfl
    have hf2 : r.f 2 = ⟨loop, σ0.set i0 0⟩ := by
      simp [hs2, hs2']

    -- Invariant: at time `2 + 3*n` we are at the loop head with `v[0] = n`.
    have inv :
        ∀ n, n ≤ 100 →
          (r.f (2 + 3 * n)).currentStatement = loop ∧
            (r.f (2 + 3 * n)).variableValues.get i0 = (n : Int) := by
      intro n hn
      induction' n with n ih
      · constructor
        · simp [hf2]
        · simp [hf2, i0]
          sorry
      · have hn_le : n ≤ 100 := Nat.le_trans (Nat.le_succ n) hn
        have hn_lt : n < 100 := Nat.lt_of_succ_le hn
        have ih' := ih hn_le

        let t : Nat := 2 + 3 * n
        have ht_stmt : (r.f t).currentStatement = loop := by
          simpa [t] using ih'.1

        cases hSt : r.f t with
        | mk st σ =>
          have hst : st = loop := by
            simpa [hSt] using ht_stmt
          subst hst
          have hget : σ.get i0 = (n : Int) := by
            simpa [hSt, t] using ih'.2

          have hlt : σ.get i0 < (100 : Int) := by
            rw [hget]
            exact (Int.ofNat_lt).2 hn_lt
          have hcond : Expression.evalBool σ cond = true := by
            simp [Expression.evalBool, Expression.evalInt, cond]
            sorry

          -- `while` unfolds to `body ; while` (since `v[0] < 100`).
          generalize hs_t1 : r.f t.succ = s_t1
          have hstep1 : Step (r.f t) s_t1 := by
            simpa [hs_t1] using r.is_valid t
          have hstep1' : Step ⟨.whileLoop cond body, σ⟩ s_t1 := by
            simpa [hSt, loop] using hstep1
          have hs_t1' : s_t1 = ⟨.sequence body loop, σ⟩ := by
            cases hstep1' with
            | while_true c body' σ' heval =>
              simp [loop]
            | while_false c body' σ' heval =>
              have : (Expression.evalBool σ cond) = true := hcond
              have : (false : Bool) = true := by
                simpa [heval] using this
              cases this
          have ht1 : r.f t.succ = ⟨.sequence body loop, σ⟩ := by
            simp [hs_t1, hs_t1']

          -- Execute the `body` assignment.
          generalize hs_t2 : r.f t.succ.succ = s_t2
          have hstep2 : Step (r.f t.succ) s_t2 := by
            simpa [hs_t2] using r.is_valid t.succ
          have hstep2' : Step ⟨.sequence body loop, σ⟩ s_t2 := by
            simpa [ht1] using hstep2
          have hs_t2' : s_t2 = ⟨.sequence .skip loop, σ.set i0 (σ.get i0 + 1)⟩ := by

            sorry
          have ht2 : r.f t.succ.succ = ⟨.sequence .skip loop, σ.set i0 (σ.get i0 + 1)⟩ := by
            simp [hs_t2, hs_t2']

          -- `skip ; s ↦ s`.
          generalize hs_t3 : r.f t.succ.succ.succ = s_t3
          have hstep3 : Step (r.f t.succ.succ) s_t3 := by
            simpa [hs_t3] using r.is_valid t.succ.succ
          have hstep3' :
              Step ⟨.sequence .skip loop, σ.set i0 (σ.get i0 + 1)⟩ s_t3 := by
            simpa [ht2] using hstep3
          have hs_t3' : s_t3 = ⟨loop, σ.set i0 (σ.get i0 + 1)⟩ := by
            cases hstep3' with
            | seq_left s₁ s₂ s₁' σ₁ σ' hs₁ h => sorry

            | seq_skip s₂ σ' =>
              rfl
          have ht3 : r.f t.succ.succ.succ = ⟨loop, σ.set i0 (σ.get i0 + 1)⟩ := by
            simp [hs_t3, hs_t3']

          have htindex : t.succ.succ.succ = 2 + 3 * n.succ := by
            simp [t, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            sorry
          constructor
          ·
            sorry
          · have : (σ.set i0 (σ.get i0 + 1)).get i0 = (n.succ : Int) := by
              -- `get_set_same` gives `σ.get i0 + 1`, then rewrite `σ.get i0 = n`.
              simpa [hget] using
                (Vector.get_set_same (v := σ) (i := i0) (a := σ.get i0 + 1))
            simp [htindex, ht3, this]
            sorry

    have h302_stmt : (r.f 302).currentStatement = loop := by
      simpa using (inv 100 (by decide)).1
    have h302_get : (r.f 302).variableValues.get i0 = (100 : Int) := by
      simpa using (inv 100 (by decide)).2

    have h303 : (r.f 303).currentStatement = .skip := by
      cases hS302 : r.f 302 with
      | mk st σ =>
        have hst : st = loop := by
          simpa [hS302] using h302_stmt
        subst hst
        have hget : σ.get i0 = (100 : Int) := by
          simpa [hS302] using h302_get
        have hlt_false : ¬ (σ.get i0 < (100 : Int)) := by
          rw [hget]
          simp
        have hcond : Expression.evalBool σ cond = false := by
          have : decide (σ.get i0 < (100 : Int)) = false := decide_eq_false hlt_false
          simp [Expression.evalBool, Expression.evalInt, cond]
          sorry
        generalize hs303 : r.f 303 = s303
        have hstep : Step (r.f 302) s303 := by
          simpa [hs303] using r.is_valid 302
        have hstep' : Step ⟨.whileLoop cond body, σ⟩ s303 := by
          simpa [hS302, loop] using hstep
        have hs303_stmt : s303.currentStatement = .skip := by
          cases hstep' with
          | while_false c body' σ' heval =>
            rfl
          | while_true c body' σ' heval =>
            have : (false : Bool) = true := by
              calc
                false = Expression.evalBool σ cond := by simpa [hcond]
                _ = true := by simpa using heval
            cases this
        simpa [hs303] using hs303_stmt

    have step_preserves_skip :
        ∀ {s₁ s₂ : ProgramState 1}, s₁.currentStatement = .skip → Step s₁ s₂ → s₂.currentStatement = .skip := by
      intro s₁ s₂ hs h
      cases s₁ with
      | mk st σ =>
        cases hs
        cases h
        rfl

    have hstay : ∀ y, 303 ≤ y → (r.f y).currentStatement = .skip := by
      intro y hy
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hy
      clear hy
      induction' d with d ih
      · simpa using h303
      · have hstep : Step (r.f (303 + d)) (r.f (303 + d).succ) := r.is_valid (303 + d)
        have hs : (r.f (303 + d)).currentStatement = .skip := ih
        have : (r.f (303 + d).succ).currentStatement = .skip :=
          step_preserves_skip hs hstep
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

    exact hstay x (Nat.le_of_lt hx)
