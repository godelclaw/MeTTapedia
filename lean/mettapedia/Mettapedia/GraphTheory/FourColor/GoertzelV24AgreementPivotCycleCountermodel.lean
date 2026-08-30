import Mathlib.Tactic

/-!
# A confined agreement-pivot cycle

The confined nine-site repair theorem supplies a transition of agreement
relations: one repaired site gains one partner, loses another, the two
partners disagree afterwards, and pairs not incident with the repaired site
are unchanged.  Those abstract facts alone do not force termination.

This file gives the smallest countermodel.  Three one-edge agreement states
form a directed cycle of confined pivots.  Hence a decreasing or increasing
rank must use geometric or colouring data beyond the agreement relation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AgreementPivotCycleCountermodel

/-- Three abstract sites suffice for the periodic obstruction. -/
abbrev Site := Fin 3

/-- An abstract agreement relation. -/
abbrev AgreementState := Site → Site → Prop

/-- Agreement is reflexive and symmetric, as common-core agreement is. -/
def IsAgreementState (state : AgreementState) : Prop :=
  (∀ site, state site site) ∧
    ∀ first second, state first second ↔ state second first

/-- One abstract confined pivot records exactly the agreement-level receipt
of a one-coordinate confined repair. -/
def ConfinedPivotStep (source target : AgreementState) : Prop :=
  ∃ repaired gained lost : Site,
    repaired ≠ gained ∧
    repaired ≠ lost ∧
    gained ≠ lost ∧
    ¬ source repaired gained ∧
    target repaired gained ∧
    source repaired lost ∧
    ¬ target repaired lost ∧
    ¬ target gained lost ∧
    ∀ first second,
      first ≠ repaired → second ≠ repaired →
        (target first second ↔ source first second)

/-- The reflexive symmetric state with exactly one undirected
off-diagonal agreement. -/
def edgeState (first second : Site) : AgreementState :=
  fun left right =>
    left = right ∨
      (left = first ∧ right = second) ∨
      (left = second ∧ right = first)

theorem edgeState_isAgreementState (first second : Site) :
    IsAgreementState (edgeState first second) := by
  constructor
  · intro site
    exact Or.inl rfl
  · intro left right
    simp only [edgeState]
    aesop

/-- The state whose only nontrivial agreement is `0 ~ 2`. -/
abbrev state02 : AgreementState := edgeState 0 2

/-- The state whose only nontrivial agreement is `0 ~ 1`. -/
abbrev state01 : AgreementState := edgeState 0 1

/-- The state whose only nontrivial agreement is `1 ~ 2`. -/
abbrev state12 : AgreementState := edgeState 1 2

theorem state02_step_state01 : ConfinedPivotStep state02 state01 := by
  refine ⟨0, 1, 2, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [edgeState]
  · simp [edgeState]
  · simp [edgeState]
  · simp [edgeState]
  · simp [edgeState]
  · intro first second hfirst hsecond
    fin_cases first <;> fin_cases second <;> simp_all [edgeState]

theorem state01_step_state12 : ConfinedPivotStep state01 state12 := by
  refine ⟨1, 2, 0, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [edgeState]
  · simp [edgeState]
  · simp [edgeState]
  · simp [edgeState]
  · simp [edgeState]
  · intro first second hfirst hsecond
    fin_cases first <;> fin_cases second <;> simp_all [edgeState]

theorem state12_step_state02 : ConfinedPivotStep state12 state02 := by
  refine ⟨2, 0, 1, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [edgeState]
  · simp [edgeState]
  · simp [edgeState]
  · simp [edgeState]
  · simp [edgeState]
  · intro first second hfirst hsecond
    fin_cases first <;> fin_cases second <;> simp_all [edgeState]

/-- The abstract confined-pivot relation has a nonempty three-step cycle. -/
theorem confinedPivotStep_three_cycle :
    Relation.TransGen ConfinedPivotStep state02 state02 := by
  exact ((Relation.TransGen.single state02_step_state01).tail
    state01_step_state12).tail state12_step_state02

/-- No natural-number rank of agreement relations can increase strictly on
every confined pivot. -/
theorem not_exists_strictlyIncreasing_agreementRank :
    ¬ ∃ rank : AgreementState → Nat,
      ∀ source target,
        ConfinedPivotStep source target → rank source < rank target := by
  rintro ⟨rank, hincreases⟩
  have h01 := hincreases state02 state01 state02_step_state01
  have h12 := hincreases state01 state12 state01_step_state12
  have h20 := hincreases state12 state02 state12_step_state02
  omega

end GoertzelV24AgreementPivotCycleCountermodel

end Mettapedia.GraphTheory.FourColor
