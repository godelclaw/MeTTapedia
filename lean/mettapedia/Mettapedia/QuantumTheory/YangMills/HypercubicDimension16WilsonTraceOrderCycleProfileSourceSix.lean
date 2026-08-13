import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileBandReduction

/-!
# OUR source-six covariant-commutator descent

OUR cycle-profile correction has a possible seven-field channel for a
six-field covariant-derivative commutator.  This file closes that channel
without a representative census.  The two curvature terms have identical
plane/derivative decoration and trace permutations conjugate by the extended
source trace.  Consequently each of OUR three decoration coordinates and OUR
trace-cycle-profile coordinate has identical signed-Reynolds value on the two
terms.  Their opposite row signs then cancel exactly.

Together with the source-band reduction, this proves that OUR correction
annihilates every physical relation generator whose source field count is six,
under either policy.  It is a finite-coordinate descent result only; it does
not assert a complete seven-field relation census or a Wilson-functional
construction.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSix

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationBlocks
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileBandReduction

/-! ## OUR seven-field coordinates of a source-six insertion -/

private theorem exactFieldSevenProjection_sevenTarget_single
    (orbit : FieldSevenOrbitCarrier) (coefficient : ℚ) :
    exactFieldSevenProjection
      (Finsupp.single (⟨ourSevenFieldCount, orbit⟩ :
        ExactFieldRelabelOrbitCarrier) coefficient) =
      Finsupp.single orbit coefficient := by
  change (exactFieldSevenEightProjection
    (Finsupp.single (⟨ourSevenFieldCount, orbit⟩ :
      ExactFieldRelabelOrbitCarrier) coefficient)).1 = _
  rw [exactFieldSevenEightProjection_single]
  simp [exactFieldSevenEightProjectionBasis, exactFieldSevenOrbitCast_self]

private theorem exactFieldEightProjection_sevenTarget_single
    (orbit : FieldSevenOrbitCarrier) (coefficient : ℚ) :
    exactFieldEightProjection
      (Finsupp.single (⟨ourSevenFieldCount, orbit⟩ :
        ExactFieldRelabelOrbitCarrier) coefficient) = 0 := by
  rw [exactFieldEightProjection_single]
  simp [exactFieldEightProjectionBasis, ourSevenFieldCount,
    ourEightFieldCount]

private abbrev sourceSixCarrier
    (sector : DerivativeAlphaReducedSector 6 4) : RelationCarrier :=
  ⟨(6 : Fin 9), sector⟩

private abbrev beforeLabeled (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData (insertCurvatureCarrier site .before).2)

private abbrev afterLabeled (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData (insertCurvatureCarrier site .after).2)

private abbrev beforeOrbit (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    FieldSevenOrbitCarrier := Quotient.mk _ (beforeLabeled sector site)

private abbrev afterOrbit (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    FieldSevenOrbitCarrier := Quotient.mk _ (afterLabeled sector site)

private abbrev beforeExactTarget (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    ExactFieldRelabelOrbitCarrier := ⟨ourSevenFieldCount, beforeOrbit sector site⟩

private abbrev afterExactTarget (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    ExactFieldRelabelOrbitCarrier := ⟨ourSevenFieldCount, afterOrbit sector site⟩

private theorem normalizeBasis_orbit (carrier : RelationCarrier) :
    normalizeExactFieldRelabel (normalizeExactContextualBasis carrier) =
      Finsupp.single (exactFieldRelabelOrbitOfOriented
        (exactNormalizedSectorData carrier))
        (fieldAxisOrientationCoefficient
          (sectorFieldAxisAssignment carrier.2)) := by
  simp [normalizeExactContextualBasis, normalizeExactFieldRelabelBasis]

private theorem sourceSix_normalized_source_zero
    (carrier : RelationCarrier) (hsource : carrier.1 = (6 : Fin 9)) :
    ourCycleProfileInvariantTraceOrderCorrection
      (normalizeExactFieldRelabel (normalizeExactContextualBasis carrier)) = 0 := by
  rw [normalizeBasis_orbit]
  apply ourCycleProfileInvariantTraceOrderCorrection_zero_of_twoBandProjection_zero
  rcases carrier with ⟨fieldCount, sector⟩
  change fieldCount = (6 : Fin 9) at hsource
  subst fieldCount
  rw [exactFieldSevenEightProjection_single]
  unfold exactFieldSevenEightProjectionBasis
  dsimp [exactFieldRelabelOrbitOfOriented, exactNormalizedSectorData]
  simp [ourSevenFieldCount, ourEightFieldCount]

private theorem sourceSix_normalized_single_zero
    (carrier : RelationCarrier) (hsource : carrier.1 = (6 : Fin 9)) :
    ourCycleProfileInvariantTraceOrderCorrection
      (normalizeExactFieldRelabel
        (normalizeExactContextual (Finsupp.single carrier (1 : ℚ)))) = 0 := by
  rw [normalizeExactContextual_single]
  simp only [one_smul]
  exact sourceSix_normalized_source_zero carrier hsource

/-! ## OUR termwise equality through signed Reynolds averaging -/

private theorem before_after_profile_raw
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (h : Hypercubic4) :
    ourTraceCycleProfileAxisMultiplicity
      ((beforeLabeled sector site).hypercubicAct h) =
      ourTraceCycleProfileAxisMultiplicity
        ((afterLabeled sector site).hypercubicAct h) := by
  unfold ourTraceCycleProfileAxisMultiplicity
  rw [show ((beforeLabeled sector site).hypercubicAct h).trace.cycleType =
      ((afterLabeled sector site).hypercubicAct h).trace.cycleType by
        simpa [beforeLabeled, afterLabeled, orientedLocalSectorEquivLabeled,
          normalizedSectorData, insertCurvatureCarrier, insertedTraceOrder,
          LabeledLocalWordSector.hypercubicAct] using
          (our_insertTraceAfter_cycleType sector.trace.traceOrder site.field).symm]
  rfl

private theorem derivativeCoordinate_reynolds_before_after
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (beforeOrbit sector site) (1 : ℚ))) =
      ourDerivativeAxisCoordinate [0, 2]
        (sectorFieldOrbitReynolds 7 2
          (Finsupp.single (afterOrbit sector site) (1 : ℚ))) := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hbefore (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (beforeOrbit sector site) (1 : ℚ))) =
        (beforeLabeled sector site).tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            ((beforeLabeled sector site).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single]
    simp [derivativeAxisOrbitMultiplicity, beforeOrbit]
  have hafter (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (afterOrbit sector site) (1 : ℚ))) =
        (afterLabeled sector site).tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            ((afterLabeled sector site).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single]
    simp [derivativeAxisOrbitMultiplicity, afterOrbit]
  simp_rw [hbefore, hafter]
  congr 2

private theorem ibpCoordinate_reynolds_before_after
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (beforeOrbit sector site) (1 : ℚ))) =
      ourIBPAxisPlanePairCoordinate
        (sectorFieldOrbitReynolds 7 2
          (Finsupp.single (afterOrbit sector site) (1 : ℚ))) := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hbefore (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (beforeOrbit sector site) (1 : ℚ))) =
        (beforeLabeled sector site).tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            ((beforeLabeled sector site).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single]
    simp [ourIBPAxisPlanePairOrbitMultiplicity, beforeOrbit]
  have hafter (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (afterOrbit sector site) (1 : ℚ))) =
        (afterLabeled sector site).tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            ((afterLabeled sector site).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single]
    simp [ourIBPAxisPlanePairOrbitMultiplicity, afterOrbit]
  simp_rw [hbefore, hafter]
  congr 2

private theorem thirdCoordinate_reynolds_before_after
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (beforeOrbit sector site) (1 : ℚ))) =
      ourThirdIBPAxisPlanePairCoordinate
        (sectorFieldOrbitReynolds 7 2
          (Finsupp.single (afterOrbit sector site) (1 : ℚ))) := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hbefore (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (beforeOrbit sector site) (1 : ℚ))) =
        (beforeLabeled sector site).tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            ((beforeLabeled sector site).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single]
    simp [ourThirdIBPAxisPlanePairOrbitMultiplicity, beforeOrbit]
  have hafter (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (afterOrbit sector site) (1 : ℚ))) =
        (afterLabeled sector site).tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            ((afterLabeled sector site).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single]
    simp [ourThirdIBPAxisPlanePairOrbitMultiplicity, afterOrbit]
  simp_rw [hbefore, hafter]
  congr 2

private theorem profileCoordinate_reynolds_before_after
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (beforeOrbit sector site) (1 : ℚ))) =
      ourTraceCycleProfileAxisCoordinate
        (sectorFieldOrbitReynolds 7 2
          (Finsupp.single (afterOrbit sector site) (1 : ℚ))) := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hbefore (h : Hypercubic4) :
      ourTraceCycleProfileAxisCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (beforeOrbit sector site) (1 : ℚ))) =
        (beforeLabeled sector site).tensorSign h *
          ourTraceCycleProfileAxisMultiplicity
            ((beforeLabeled sector site).hypercubicAct h) := by
    rw [signedSectorFieldOrbitAction_single,
      ourTraceCycleProfileAxisCoordinate_single,
      ourTraceCycleProfileAxisOrbitMultiplicity_action]
    simp [beforeOrbit]
  have hafter (h : Hypercubic4) :
      ourTraceCycleProfileAxisCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (afterOrbit sector site) (1 : ℚ))) =
        (afterLabeled sector site).tensorSign h *
          ourTraceCycleProfileAxisMultiplicity
            ((afterLabeled sector site).hypercubicAct h) := by
    rw [signedSectorFieldOrbitAction_single,
      ourTraceCycleProfileAxisCoordinate_single,
      ourTraceCycleProfileAxisOrbitMultiplicity_action]
    simp [afterOrbit]
  simp_rw [hbefore, hafter]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [show (beforeLabeled sector site).tensorSign h =
      (afterLabeled sector site).tensorSign h by rfl]
  exact congrArg (fun value : ℚ =>
    (beforeLabeled sector site).tensorSign h * value)
    (before_after_profile_raw sector site h)

/-! ## OUR equality of all correction components -/

private theorem invariantSevenAxis_before_after
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    ourInvariantSevenAxisCoordinate
      (Finsupp.single (beforeExactTarget sector site) (1 : ℚ)) =
      ourInvariantSevenAxisCoordinate
        (Finsupp.single (afterExactTarget sector site) (1 : ℚ)) := by
  unfold ourInvariantSevenAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_sevenTarget_single,
    exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_sevenTarget_single,
    derivativeCoordinate_reynolds_before_after]

private theorem invariantIBP_before_after
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    ourInvariantIBPAxisCoordinate
      (Finsupp.single (beforeExactTarget sector site) (1 : ℚ)) =
      ourInvariantIBPAxisCoordinate
        (Finsupp.single (afterExactTarget sector site) (1 : ℚ)) := by
  unfold ourInvariantIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_sevenTarget_single,
    exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_sevenTarget_single,
    ibpCoordinate_reynolds_before_after]

private theorem invariantThird_before_after
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    ourInvariantThirdIBPAxisCoordinate
      (Finsupp.single (beforeExactTarget sector site) (1 : ℚ)) =
      ourInvariantThirdIBPAxisCoordinate
        (Finsupp.single (afterExactTarget sector site) (1 : ℚ)) := by
  unfold ourInvariantThirdIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_sevenTarget_single,
    exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_sevenTarget_single,
    thirdCoordinate_reynolds_before_after]

private theorem invariantProfile_before_after
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    ourInvariantTraceCycleProfileCoordinate
      (Finsupp.single (beforeExactTarget sector site) (1 : ℚ)) =
      ourInvariantTraceCycleProfileCoordinate
        (Finsupp.single (afterExactTarget sector site) (1 : ℚ)) := by
  unfold ourInvariantTraceCycleProfileCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_sevenTarget_single,
    exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_sevenTarget_single,
    profileCoordinate_reynolds_before_after]

private theorem exactFieldEightTrace_before_zero
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    exactFieldEightTraceProjection
      (Finsupp.single (beforeExactTarget sector site) (1 : ℚ)) = 0 := by
  unfold exactFieldEightTraceProjection
  simp only [LinearMap.comp_apply]
  rw [exactFieldEightProjection_sevenTarget_single]
  simp

private theorem exactFieldEightTrace_after_zero
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    exactFieldEightTraceProjection
      (Finsupp.single (afterExactTarget sector site) (1 : ℚ)) = 0 := by
  unfold exactFieldEightTraceProjection
  simp only [LinearMap.comp_apply]
  rw [exactFieldEightProjection_sevenTarget_single]
  simp

private theorem correction_before_after_unit
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    ourCycleProfileInvariantTraceOrderCorrection
      (Finsupp.single (beforeExactTarget sector site) (1 : ℚ)) =
      ourCycleProfileInvariantTraceOrderCorrection
        (Finsupp.single (afterExactTarget sector site) (1 : ℚ)) := by
  unfold ourCycleProfileInvariantTraceOrderCorrection
    ourTraceCycleProfileInvariantTraceContribution
    ourThreeCoordinateInvariantTraceOrderCorrection
    ourThirdInvariantTraceContribution
    ourTwoCoordinateInvariantTraceOrderCorrection
    ourTwoCoordinateInvariantSevenTraceCompensator
    ourTwoCoordinateInvariantSevenAxisCoordinate
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply]
  rw [exactFieldEightTrace_before_zero,
    exactFieldEightTrace_after_zero,
    invariantSevenAxis_before_after,
    invariantIBP_before_after,
    invariantThird_before_after,
    invariantProfile_before_after]

private theorem correction_before_after_smul
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (coefficient : ℚ) :
    ourCycleProfileInvariantTraceOrderCorrection
      (Finsupp.single (beforeExactTarget sector site) coefficient) =
      ourCycleProfileInvariantTraceOrderCorrection
        (Finsupp.single (afterExactTarget sector site) coefficient) := by
  rw [show Finsupp.single (beforeExactTarget sector site) coefficient =
      coefficient • Finsupp.single (beforeExactTarget sector site) (1 : ℚ) by simp,
    show Finsupp.single (afterExactTarget sector site) coefficient =
      coefficient • Finsupp.single (afterExactTarget sector site) (1 : ℚ) by simp,
    map_smul, map_smul, correction_before_after_unit]

private theorem sourceSix_curvature_normalized_equal
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    ourCycleProfileInvariantTraceOrderCorrection
      (normalizeExactFieldRelabel
        (normalizeExactContextualBasis (insertCurvatureCarrier site .before))) =
      ourCycleProfileInvariantTraceOrderCorrection
        (normalizeExactFieldRelabel
          (normalizeExactContextualBasis (insertCurvatureCarrier site .after))) := by
  rw [normalizeBasis_orbit, normalizeBasis_orbit]
  set coefficient : ℚ := fieldAxisOrientationCoefficient
    (sectorFieldAxisAssignment (insertCurvatureCarrier site .before).2)
  have hcoefficient : fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment (insertCurvatureCarrier site .after).2) = coefficient := by rfl
  rw [hcoefficient]
  set beforeTarget : ExactFieldRelabelOrbitCarrier :=
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData (insertCurvatureCarrier site .before))
  set afterTarget : ExactFieldRelabelOrbitCarrier :=
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData (insertCurvatureCarrier site .after))
  have hbeforeTarget : beforeTarget = beforeExactTarget sector site := by rfl
  have hafterTarget : afterTarget = afterExactTarget sector site := by rfl
  change ourCycleProfileInvariantTraceOrderCorrection
      (Finsupp.single beforeTarget coefficient) =
    ourCycleProfileInvariantTraceOrderCorrection
      (Finsupp.single afterTarget coefficient)
  rw [hbeforeTarget, hafterTarget]
  exact correction_before_after_smul sector site coefficient

private theorem sourceSix_curvature_normalized_single_equal
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector)) :
    ourCycleProfileInvariantTraceOrderCorrection
      (normalizeExactFieldRelabel
        (normalizeExactContextual
          (Finsupp.single (insertCurvatureCarrier site .before) (1 : ℚ)))) =
      ourCycleProfileInvariantTraceOrderCorrection
        (normalizeExactFieldRelabel
          (normalizeExactContextual
            (Finsupp.single (insertCurvatureCarrier site .after) (1 : ℚ)))) := by
  rw [normalizeExactContextual_single, normalizeExactContextual_single]
  simp only [one_smul]
  exact sourceSix_curvature_normalized_equal sector site

/-! ## OUR source-six physical descent -/

private theorem sourceSix_covariant_physical_zero
    (policy : PhysicalRelationPolicy)
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (coefficient : ℚ) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (.covariantCommutator (sourceSixCarrier sector) site)
          coefficient)) = 0 := by
  unfold orbitPhysicalRelationOperator normalizedPhysicalRelationOperator
  simp only [LinearMap.comp_apply, physicalRelationOperator_single,
    physicalRelationRow, covariantCommutatorRow, map_sub, map_add,
    LinearMap.map_smul]
  rw [sourceSix_normalized_single_zero (sourceSixCarrier sector) rfl]
  rw [sourceSix_normalized_single_zero
    (swapExactDerivativePositions (sourceSixCarrier sector) site.outer site.inner) rfl]
  rw [sourceSix_curvature_normalized_single_equal]
  abel
  simp

/-- OUR full source-six covariant-commutator descent theorem.  The proof is
generic in the carrier and site: after the source field count is identified
with six, its two curvature insertions cancel in OUR correction exactly. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_covariantCommutator_zero_of_source_eq_six
    (policy : PhysicalRelationPolicy) (carrier : RelationCarrier)
    (site : CovariantCommutatorSite carrier) (coefficient : ℚ)
    (hsource : carrier.1 = (6 : Fin 9)) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (.covariantCommutator carrier site)
          coefficient)) = 0 := by
  rcases carrier with ⟨fieldCount, sector⟩
  change fieldCount = (6 : Fin 9) at hsource
  subst fieldCount
  set_option maxRecDepth 100000 in
    exact sourceSix_covariant_physical_zero policy sector site coefficient

/-- OUR complete physical source-six descent theorem.  The standard
same-sector families vanish by the earlier band argument; the only possible
cross-sector family is discharged by OUR curvature-insertion cancellation. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_eq_six
    (policy : PhysicalRelationPolicy)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ)
    (hsource : physicalRelationGeneratorSourceFieldCount generator = (6 : Fin 9)) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient)) = 0 := by
  rcases sourceSixPhysicalRelationGenerator_covariantCommutator_or_profileCorrection_zero
    policy generator coefficient hsource with hcov | hzero
  · rcases hcov with ⟨carrier, site, rfl⟩
    apply ourCycleProfileInvariantTraceOrderCorrection_covariantCommutator_zero_of_source_eq_six
    simpa [physicalRelationGeneratorSourceFieldCount,
      physicalRelationGeneratorSourceCarrier] using hsource
  · exact hzero

#print axioms ourCycleProfileInvariantTraceOrderCorrection_covariantCommutator_zero_of_source_eq_six
#print axioms ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_eq_six

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSix
