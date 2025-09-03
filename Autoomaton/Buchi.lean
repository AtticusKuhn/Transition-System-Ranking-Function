import Mathlib.Data.Nat.Count
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Nth
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.OrderIsoNat
import Mathlib.Computability.Ackermann
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.SetTheory.Ordinal.NaturalOps
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.SetTheory.Ordinal.Arithmetic

set_option pp.universes true in

/-- A Büchi automaton is a tuple $(S, R, I, F)$ where
- $S$ is a set of states.
- $R \subseteq S \times S$ is a transition relation.
- $I \subseteq S$ is a set of initial states.
- $F \subseteq S$ is a set of fair (or accepting) states.
-/
structure Automaton (S : Type) where
  /-- The transition relation $R \subseteq S \times S$. -/
  R : S → S → Prop
  /-- The set of initial states $I \subseteq S$. -/
  I : S → Bool
  /-- The set of fair (accepting) states $F \subseteq S$. -/
  F : S → Bool

/-- A run of a Büchi automaton is an infinite sequence of states $f : \mathbb{N} \to S$ such that
the first state is initial and all subsequent states are related by the transition relation. -/
structure Run {S : Type} (a : Automaton S) where
  /-- The infinite sequence of states $f : \mathbb{N} \to S$. -/
  f : Nat → S
  /-- The first state must be an initial state, i.e., $f(0) \in I$. -/
  is_init : a.I (f 0)
  /-- Each consecutive pair of states must be in the transition relation, i.e., $\forall n \in \mathbb{N}, (f(n), f(n+1)) \in R$. -/
  is_valid : ∀ n, a.R (f n) (f n.succ)

variable {S : Type} {a : Automaton S} (r : Run a)

/-- A run `r` is fair if it visits the set of fair states infinitely often.
This is expressed as $\forall n \in \mathbb{N}, \exists k > n, f(k) \in F$. -/
@[simp]
def Run.IsFair : Prop := ∀ (n : Nat), ∃ (k : Nat), k > n ∧ a.F (r.f k)
def Run.IsFair2 : Prop := ∀ (n : Nat), ∃ (k : Nat), k ≥ n ∧ a.F (r.f k)

theorem fair_iff_fair2 : r.IsFair ↔ r.IsFair2 := by
  constructor
  · intro h n
    rcases h n with ⟨ k, hk, fk ⟩
    use k
    constructor
    · exact Nat.le_of_lt hk
    · exact fk
  · intro h n
    rcases h n.succ with ⟨ k, hk, fk ⟩
    use k
    simp only [gt_iff_lt, fk, and_true]
    omega

@[simp]
def Run.IsFairN (n k : Nat) : Prop := n ≤ Nat.count (fun m => a.F (r.f m)) k

-- theorem Run.fairN_fair : (∀ (n : Nat), ∃ (k : Nat), r.IsFairN n k) ↔  r.IsFair := by
--   -- intro n
--   -- have y := p (n + 1)
--   -- simp [Run.IsFairN] at y
--   -- to_encard_tac
--   sorry


-- theorem Run.exists_fairN_fair : (∃ (r :Run a), ∀ (n : Nat), ∃ (k : Nat), r.IsFairN n k) ↔ ∃ (r :Run a), r.IsFair := by
--   simp only [Run.fairN_fair]

-- theorem Run.faex_exfa (p : (∀ (n : Nat), ∃ (r :Run a), ∃ (k : Nat),  r.IsFairN n k)) :  (∃ (r :Run a), ∀ (n : Nat),  ∃ (k : Nat), r.IsFairN n k) := by

--   sorry

def State.IsReachable (s : S) : Prop :=
  -- ∃ (r : Run a), ∃ (i : Nat), r.f i = s
  ∃ (i : S), Relation.ReflTransGen a.R i s ∧ a.I i

theorem run_reachable (n : Nat) : State.IsReachable (a := a) (r.f n) := by
  -- use r
  -- use n
  -- sorry
  induction' n with m ih
  · use r.f 0
    rw [Relation.ReflTransGen.cases_head_iff]
    simp only [true_or, r.is_init, and_self]
  · rcases ih with ⟨ i, i_rfm, i_init⟩
    use i
    simp only [i_init, and_true]
    rw [Relation.ReflTransGen.cases_tail_iff]
    right
    use (r.f m)
    simp only [i_rfm, r.is_valid m, and_self]

/-- A run `r` is unfair if it is not fair. -/
@[simp]
def Run.IsUnfair : Prop := ¬ r.IsFair

/-- A run is "fair-empty" if it is unfair. This definition is part of establishing that if a ranking function exists, then no fair run exists. -/
@[simp]
def Run.IsFairEmpty : Prop := r.IsUnfair

/-- An automaton is "fair-empty" if all its runs are unfair.
This means the automaton has no fair runs. -/
@[simp]
def Automaton.IsFairEmpty : Prop := ∀ (r : Run a), r.IsFairEmpty
