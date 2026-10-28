import Mettapedia.Computability.PNP.ConditioningObstructionCountIndependence

/-!
# Minimal diagonal conditioning countermodel

The two Boolean coordinates are independent before conditioning, but
conditioning on the diagonal couples them and destroys independence.
-/

namespace Mettapedia.Computability.PNP

/-- The smallest finite countermodel for independence-through-conditioning. -/
abbrev ConditioningBoolPair := Bool × Bool

/-- First Boolean coordinate is `true`. -/
def conditioningFirstTrue (ω : ConditioningBoolPair) : Prop := ω.1 = true

instance instDecidablePredConditioningFirstTrue :
    DecidablePred conditioningFirstTrue := by
  intro ω
  unfold conditioningFirstTrue
  infer_instance

/-- Second Boolean coordinate is `true`. -/
def conditioningSecondTrue (ω : ConditioningBoolPair) : Prop := ω.2 = true

instance instDecidablePredConditioningSecondTrue :
    DecidablePred conditioningSecondTrue := by
  intro ω
  unfold conditioningSecondTrue
  infer_instance

/-- Diagonal conditioning event coupling the two coordinates. -/
def conditioningDiagonal (ω : ConditioningBoolPair) : Prop := ω.1 = ω.2

instance instDecidablePredConditioningDiagonal :
    DecidablePred conditioningDiagonal := by
  intro ω
  unfold conditioningDiagonal
  infer_instance

noncomputable def conditioningFirstTrueEquivBool :
    {ω : ConditioningBoolPair // conditioningFirstTrue ω} ≃ Bool where
  toFun ω := ω.1.2
  invFun b := ⟨(true, b), rfl⟩
  left_inv ω := by
    rcases ω with ⟨⟨a, b⟩, h⟩
    simp [conditioningFirstTrue] at h
    subst a
    rfl
  right_inv b := rfl

theorem finiteEventCount_conditioningFirstTrue :
    finiteEventCount ConditioningBoolPair conditioningFirstTrue = 2 := by
  simpa [finiteEventCount] using Fintype.card_congr conditioningFirstTrueEquivBool

noncomputable def conditioningSecondTrueEquivBool :
    {ω : ConditioningBoolPair // conditioningSecondTrue ω} ≃ Bool where
  toFun ω := ω.1.1
  invFun a := ⟨(a, true), rfl⟩
  left_inv ω := by
    rcases ω with ⟨⟨a, b⟩, h⟩
    simp [conditioningSecondTrue] at h
    subst b
    rfl
  right_inv a := rfl

theorem finiteEventCount_conditioningSecondTrue :
    finiteEventCount ConditioningBoolPair conditioningSecondTrue = 2 := by
  simpa [finiteEventCount] using Fintype.card_congr conditioningSecondTrueEquivBool

noncomputable def conditioningBothTrueEquivUnit :
    {ω : ConditioningBoolPair //
      conditioningFirstTrue ω ∧ conditioningSecondTrue ω} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(true, true), by
    simp [conditioningFirstTrue, conditioningSecondTrue]⟩
  left_inv ω := by
    rcases ω with ⟨⟨a, b⟩, ha, hb⟩
    simp [conditioningFirstTrue] at ha
    simp [conditioningSecondTrue] at hb
    subst a
    subst b
    rfl
  right_inv _ := rfl

theorem finiteEventCount_conditioningBothTrue :
    finiteEventCount ConditioningBoolPair
      (fun ω => conditioningFirstTrue ω ∧ conditioningSecondTrue ω) = 1 := by
  simpa [finiteEventCount] using Fintype.card_congr conditioningBothTrueEquivUnit

noncomputable def conditioningDiagonalEquivBool :
    {ω : ConditioningBoolPair // conditioningDiagonal ω} ≃ Bool where
  toFun ω := ω.1.1
  invFun a := ⟨(a, a), by simp [conditioningDiagonal]⟩
  left_inv ω := by
    rcases ω with ⟨⟨a, b⟩, h⟩
    simp [conditioningDiagonal] at h
    subst b
    rfl
  right_inv a := rfl

theorem finiteEventCount_conditioningDiagonal :
    finiteEventCount ConditioningBoolPair conditioningDiagonal = 2 := by
  simpa [finiteEventCount] using Fintype.card_congr conditioningDiagonalEquivBool

noncomputable def conditioningDiagonalFirstTrueEquivUnit :
    {ω : ConditioningBoolPair //
      conditioningDiagonal ω ∧ conditioningFirstTrue ω} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(true, true), by
    simp [conditioningDiagonal, conditioningFirstTrue]⟩
  left_inv ω := by
    rcases ω with ⟨⟨a, b⟩, hdiag, hfirst⟩
    simp [conditioningDiagonal] at hdiag
    simp [conditioningFirstTrue] at hfirst
    subst a
    subst b
    rfl
  right_inv _ := rfl

theorem finiteEventCount_conditioningDiagonalFirstTrue :
    finiteEventCount ConditioningBoolPair
      (fun ω => conditioningDiagonal ω ∧ conditioningFirstTrue ω) = 1 := by
  simpa [finiteEventCount] using
    Fintype.card_congr conditioningDiagonalFirstTrueEquivUnit

noncomputable def conditioningDiagonalNotFirstTrueEquivUnit :
    {ω : ConditioningBoolPair //
      conditioningDiagonal ω ∧ ¬ conditioningFirstTrue ω} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(false, false), by
    simp [conditioningDiagonal, conditioningFirstTrue]⟩
  left_inv ω := by
    rcases ω with ⟨⟨a, b⟩, hdiag, hfirst⟩
    simp [conditioningDiagonal] at hdiag
    simp [conditioningFirstTrue] at hfirst
    subst b
    cases a
    · rfl
    · contradiction
  right_inv _ := rfl

theorem finiteEventCount_conditioningDiagonalNotFirstTrue :
    finiteEventCount ConditioningBoolPair
      (fun ω => conditioningDiagonal ω ∧ ¬ conditioningFirstTrue ω) = 1 := by
  simpa [finiteEventCount] using
    Fintype.card_congr conditioningDiagonalNotFirstTrueEquivUnit

noncomputable def conditioningDiagonalSecondTrueEquivUnit :
    {ω : ConditioningBoolPair //
      conditioningDiagonal ω ∧ conditioningSecondTrue ω} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(true, true), by
    simp [conditioningDiagonal, conditioningSecondTrue]⟩
  left_inv ω := by
    rcases ω with ⟨⟨a, b⟩, hdiag, hsecond⟩
    simp [conditioningDiagonal] at hdiag
    simp [conditioningSecondTrue] at hsecond
    subst b
    subst a
    rfl
  right_inv _ := rfl

theorem finiteEventCount_conditioningDiagonalSecondTrue :
    finiteEventCount ConditioningBoolPair
      (fun ω => conditioningDiagonal ω ∧ conditioningSecondTrue ω) = 1 := by
  simpa [finiteEventCount] using
    Fintype.card_congr conditioningDiagonalSecondTrueEquivUnit

noncomputable def conditioningDiagonalBothTrueEquivUnit :
    {ω : ConditioningBoolPair //
      conditioningDiagonal ω ∧ conditioningFirstTrue ω ∧
        conditioningSecondTrue ω} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(true, true), by
    simp [conditioningDiagonal, conditioningFirstTrue, conditioningSecondTrue]⟩
  left_inv ω := by
    rcases ω with ⟨⟨a, b⟩, _hdiag, hfirst, hsecond⟩
    simp [conditioningFirstTrue] at hfirst
    simp [conditioningSecondTrue] at hsecond
    subst a
    subst b
    rfl
  right_inv _ := rfl

theorem finiteEventCount_conditioningDiagonalBothTrue :
    finiteEventCount ConditioningBoolPair
      (fun ω =>
        conditioningDiagonal ω ∧ conditioningFirstTrue ω ∧
          conditioningSecondTrue ω) = 1 := by
  simpa [finiteEventCount] using
    Fintype.card_congr conditioningDiagonalBothTrueEquivUnit

/-- Before conditioning, the two Boolean coordinates are independent under
uniform counting. -/
theorem conditioningBoolPair_unconditioned_first_second_independent :
    CountIndependent (Ω := ConditioningBoolPair)
      conditioningFirstTrue conditioningSecondTrue := by
  unfold CountIndependent
  rw [finiteEventCount_conditioningBothTrue,
    finiteEventCount_conditioningFirstTrue,
    finiteEventCount_conditioningSecondTrue]
  norm_num

/-- Conditioning on the diagonal destroys that independence: inside the
conditioned event, the first coordinate determines the second. -/
theorem not_conditioningBoolPair_conditioned_on_diagonal_first_second_independent :
    ¬ CountIndependentWithin (Ω := ConditioningBoolPair)
      conditioningDiagonal conditioningFirstTrue conditioningSecondTrue := by
  exact
    not_countIndependentWithin_of_coupled_nonconstant_on_condition
      (Ω := ConditioningBoolPair)
      conditioningDiagonal conditioningFirstTrue conditioningSecondTrue
      (by
        intro ω hdiag
        rcases ω with ⟨a, b⟩
        simp [conditioningDiagonal, conditioningFirstTrue, conditioningSecondTrue] at hdiag ⊢
        subst b
        rfl)
      (by
        rw [finiteEventCount_conditioningDiagonalFirstTrue]
        norm_num)
      (by
        rw [finiteEventCount_conditioningDiagonalNotFirstTrue]
        norm_num)

end Mettapedia.Computability.PNP
