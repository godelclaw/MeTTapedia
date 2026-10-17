import Mettapedia.GSLT.Logic.KnowledgeBasedPrograms

/-!
# Ranked systems are decided: a criterion for knowledge-based programs

The grounded inquiry of a system of self-referential judgments decides some
judgments and may leave others undetermined (`KripkeTruth.System.least`).  For
knowledge-based programs a decided inquiry has exactly one implementation
(`KnowledgeBasedPrograms.implementation_eq_of_decided`).  Knapp, Mühlberger and
Reus (*Interpreting knowledge-based programs*, 2023) ask for criteria that
ensure a decided least fixed point.  This module gives one for the one-round
case.

A system is **ranked** when some natural-number rank strictly decreases from
every judgment to each judgment its specification reads (`Ranked`): the
references through truth, and so through knowledge tests, are well founded.

* **A ranked system with bivalent base facts is decided at a finite stage**
  (`stage_decides`): every judgment of rank below `n` is decided at stage `n`,
  so the least fixed point decides every judgment (`least_decides`).
* **Ranked knowledge-based programs have exactly one implementation**
  (`ranked_implementation_unique`).
* The rank is necessary for the conclusion in the sense of the controls:
  "act if I know I will act" reads itself, is not ranked
  (`Controls.teller_not_ranked`), and is undetermined.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.RankedDecision

open Mettapedia.GSLT.KripkeTruth

universe u v

variable {Judgment : Type u} {Base : Type v}

/-- The judgments a formula reads. -/
def reads : Formula Judgment Base → Judgment → Prop
  | .base _, _ => False
  | .truth judgment, other => other = judgment
  | .neg formula, other => reads formula other
  | .conj first second, other => reads first other ∨ reads second other
  | .disj first second, other => reads first other ∨ reads second other

/-- **A ranked system**: the rank decreases along every truth reference. -/
def Ranked (system : System Judgment Base) (rank : Judgment → ℕ) : Prop :=
  ∀ judgment other, reads (system.spec judgment) other → rank other < rank judgment

/-- A valuation decides a judgment. -/
def Decides (valuation : Valuation Judgment) (judgment : Judgment) : Prop :=
  judgment ∈ valuation.holds ∨ judgment ∈ valuation.fails

/-- A formula whose read judgments are all decided is decided, when base facts
are bivalent. -/
theorem eval_decided {system : System Judgment Base} (bivalent : system.Bivalent)
    {valuation : Valuation Judgment} :
    ∀ formula : Formula Judgment Base, (∀ other, reads formula other → Decides valuation other) →
      (system.eval valuation formula).1 ∨ (system.eval valuation formula).2
  | .base fact, _ => bivalent fact
  | .truth judgment, decided => decided judgment rfl
  | .neg formula, decided => (eval_decided bivalent formula decided).symm
  | .conj first second, decided => by
      rcases eval_decided bivalent first (fun other h => decided other (Or.inl h)) with h1 | h1 <;>
        rcases eval_decided bivalent second (fun other h => decided other (Or.inr h)) with h2 | h2
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inr h2)
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inl h1)
  | .disj first second, decided => by
      rcases eval_decided bivalent first (fun other h => decided other (Or.inl h)) with h1 | h1 <;>
        rcases eval_decided bivalent second (fun other h => decided other (Or.inr h)) with h2 | h2
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr h2)
      · exact Or.inr ⟨h1, h2⟩

/-- **A ranked system is decided at a finite stage**: judgments of rank below `n`
are decided at stage `n`. -/
theorem stage_decides {system : System Judgment Base} (bivalent : system.Bivalent)
    {rank : Judgment → ℕ} (ranked : Ranked system rank) :
    ∀ n judgment, rank judgment < n → Decides (system.stage n) judgment := by
  intro n
  induction n with
  | zero => intro _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
      intro judgment h
      exact eval_decided bivalent (system.spec judgment) fun other reading =>
        ih other (by have := ranked judgment other reading; omega)

/-- **The least fixed point of a ranked system decides every judgment.** -/
theorem least_decides {system : System Judgment Base} (bivalent : system.Bivalent)
    {rank : Judgment → ℕ} (ranked : Ranked system rank) (judgment : Judgment) :
    Decides system.least judgment := by
  rcases stage_decides bivalent ranked (rank judgment + 1) judgment (Nat.lt_succ_self _) with h | h
  · exact Or.inl ((system.stage_le_least _).1 h)
  · exact Or.inr ((system.stage_le_least _).2 h)

open Mettapedia.GSLT.KnowledgeBasedPrograms in
/-- **Ranked knowledge-based programs have exactly one implementation.** -/
theorem ranked_implementation_unique {system : System Judgment Base} {baseValue : Base → Bool}
    (agrees : BaseAgrees system baseValue) {rank : Judgment → ℕ} (ranked : Ranked system rank)
    {first second : Judgment → Bool} (implementsFirst : IsImplementation system baseValue first)
    (implementsSecond : IsImplementation system baseValue second) : first = second := by
  have bivalent : system.Bivalent := fun fact => by
    cases h : baseValue fact
    · exact Or.inr ((agrees fact).2.2 h)
    · exact Or.inl ((agrees fact).1.2 h)
  have decided := least_decides bivalent ranked
  funext judgment
  have one := implementation_eq_of_decided system agrees decided implementsFirst judgment
  have two := implementation_eq_of_decided system agrees decided implementsSecond judgment
  cases h1 : first judgment <;> cases h2 : second judgment
  · rfl
  · exact absurd (one.2 (two.1 h2)) (by simp [h1])
  · exact absurd (two.2 (one.1 h1)) (by simp [h2])
  · rfl

/-! ## Controls -/

namespace Controls

open Mettapedia.GSLT.KnowledgeBasedPrograms Mettapedia.GSLT.KnowledgeBasedPrograms.Examples

/-- **"Act if I know I will act" is not ranked**: it reads itself. -/
theorem teller_not_ranked (rank : Context.Judgment Unit Unit Act → ℕ) :
    ¬ Ranked (single.system Teller.program) rank := by
  intro ranked
  have := ranked acts acts (by rw [Teller.spec_eq]; rfl)
  omega

end Controls

end Mettapedia.GSLT.RankedDecision
