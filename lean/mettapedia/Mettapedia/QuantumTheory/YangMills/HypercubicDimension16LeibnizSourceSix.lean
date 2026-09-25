import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldEightTracePhysicalCompleteness
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LeibnizRelationOperator

/-!
# OUR profile-correction descent for the Leibniz-corrected operator

`HypercubicDimension16WilsonTraceOrderCycleProfileSourceSix` shows that OUR
cycle-profile correction annihilates every column of the earlier orbit
operator whose source has six field strengths, and
`HypercubicDimension16FieldEightTracePhysicalCompleteness` extends this to
every source band except seven.  This module proves both statements for the
Leibniz-corrected orbit operator.

The corrected commutator row has one pair of curvature insertions for each
subset `S` of the field's outer derivatives, the inserted curvature letter
carrying the derivatives in `S`.  The two insertions of a pair have the same
letters and differ only in the trace order, `insertTraceBefore` versus
`insertTraceAfter` of the source trace, which are conjugate permutations.  So
each pair has equal values under OUR three decoration coordinates and OUR
trace-cycle-profile coordinate after signed Reynolds averaging, and the pair
cancels exactly as the single pair of the earlier row does.  Below six source
field strengths every term of the corrected row has at most six field
strengths and is invisible to the correction.  With seven or eight source
field strengths a commutator site uses every derivative of its carrier, so the
two operators agree on every column of those bands, and every other generator
has the same row in both operators.

This is a finite-coordinate descent result.  It does not treat the seven-field
source band and does not construct a Wilson functional.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LeibnizSourceSix

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
open HypercubicDimension16FieldEightTracePhysicalCompleteness
open HypercubicDimension16LeibnizCommutator
open HypercubicDimension16LeibnizRelationOperator

/-! ## OUR seven-field coordinates of a source-six Leibniz insertion -/

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

private abbrev SourceSixMoved (sector : DerivativeAlphaReducedSector 6 4) :=
  Finset (Fin (dimension16DerivativeCount (sourceSixCarrier sector).1))

private abbrev beforeLabeled (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData (insertLeibnizCarrier site .before moved).2)

private abbrev afterLabeled (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData (insertLeibnizCarrier site .after moved).2)

private abbrev beforeOrbit (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    FieldSevenOrbitCarrier := Quotient.mk _ (beforeLabeled sector site moved)

private abbrev afterOrbit (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    FieldSevenOrbitCarrier := Quotient.mk _ (afterLabeled sector site moved)

private abbrev beforeExactTarget (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    ExactFieldRelabelOrbitCarrier := ⟨ourSevenFieldCount, beforeOrbit sector site moved⟩

private abbrev afterExactTarget (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    ExactFieldRelabelOrbitCarrier := ⟨ourSevenFieldCount, afterOrbit sector site moved⟩

private theorem normalizeBasis_orbit (carrier : RelationCarrier) :
    normalizeExactFieldRelabel (normalizeExactContextualBasis carrier) =
      Finsupp.single (exactFieldRelabelOrbitOfOriented
        (exactNormalizedSectorData carrier))
        (fieldAxisOrientationCoefficient
          (sectorFieldAxisAssignment carrier.2)) := by
  simp [normalizeExactContextualBasis, normalizeExactFieldRelabelBasis]

/-- A carrier with at most six field strengths is invisible to OUR
correction: its normalized image has no seven- or eight-field component. -/
private theorem normalized_zero_of_fieldCount_lt_seven
    (carrier : RelationCarrier) (hlow : carrier.1.1 < 7) :
    ourCycleProfileInvariantTraceOrderCorrection
      (normalizeExactFieldRelabel (normalizeExactContextualBasis carrier)) = 0 := by
  rw [normalizeBasis_orbit]
  apply ourCycleProfileInvariantTraceOrderCorrection_zero_of_twoBandProjection_zero
  rcases carrier with ⟨fieldCount, sector⟩
  have hseven : fieldCount ≠ ourSevenFieldCount := by
    intro h
    have hval := congrArg Fin.val h
    simp [ourSevenFieldCount] at hval
    change fieldCount.1 < 7 at hlow
    omega
  have height : fieldCount ≠ ourEightFieldCount := by
    intro h
    have hval := congrArg Fin.val h
    simp [ourEightFieldCount] at hval
    change fieldCount.1 < 7 at hlow
    omega
  rw [exactFieldSevenEightProjection_single]
  unfold exactFieldSevenEightProjectionBasis
  dsimp [exactFieldRelabelOrbitOfOriented, exactNormalizedSectorData]
  simp [hseven, height]

private theorem normalized_single_zero_of_fieldCount_lt_seven
    (carrier : RelationCarrier) (hlow : carrier.1.1 < 7) :
    ourCycleProfileInvariantTraceOrderCorrection
      (normalizeExactFieldRelabel
        (normalizeExactContextual (Finsupp.single carrier (1 : ℚ)))) = 0 := by
  rw [normalizeExactContextual_single]
  simp only [one_smul]
  exact normalized_zero_of_fieldCount_lt_seven carrier hlow

/-! ## OUR termwise equality through signed Reynolds averaging -/

private theorem before_after_profile_raw
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector)
    (h : Hypercubic4) :
    ourTraceCycleProfileAxisMultiplicity
      ((beforeLabeled sector site moved).hypercubicAct h) =
      ourTraceCycleProfileAxisMultiplicity
        ((afterLabeled sector site moved).hypercubicAct h) := by
  unfold ourTraceCycleProfileAxisMultiplicity
  rw [show ((beforeLabeled sector site moved).hypercubicAct h).trace.cycleType =
      ((afterLabeled sector site moved).hypercubicAct h).trace.cycleType by
        simpa [beforeLabeled, afterLabeled, orientedLocalSectorEquivLabeled,
          normalizedSectorData, insertLeibnizCarrier, insertedTraceOrder,
          LabeledLocalWordSector.hypercubicAct] using
          (our_insertTraceAfter_cycleType sector.trace.traceOrder site.field).symm]
  rfl

private theorem derivativeCoordinate_reynolds_before_after
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (beforeOrbit sector site moved) (1 : ℚ))) =
      ourDerivativeAxisCoordinate [0, 2]
        (sectorFieldOrbitReynolds 7 2
          (Finsupp.single (afterOrbit sector site moved) (1 : ℚ))) := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hbefore (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (beforeOrbit sector site moved) (1 : ℚ))) =
        (beforeLabeled sector site moved).tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            ((beforeLabeled sector site moved).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single]
    simp [derivativeAxisOrbitMultiplicity, beforeOrbit]
  have hafter (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (afterOrbit sector site moved) (1 : ℚ))) =
        (afterLabeled sector site moved).tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            ((afterLabeled sector site moved).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single]
    simp [derivativeAxisOrbitMultiplicity, afterOrbit]
  simp_rw [hbefore, hafter]
  congr 2

private theorem ibpCoordinate_reynolds_before_after
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (beforeOrbit sector site moved) (1 : ℚ))) =
      ourIBPAxisPlanePairCoordinate
        (sectorFieldOrbitReynolds 7 2
          (Finsupp.single (afterOrbit sector site moved) (1 : ℚ))) := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hbefore (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (beforeOrbit sector site moved) (1 : ℚ))) =
        (beforeLabeled sector site moved).tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            ((beforeLabeled sector site moved).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single]
    simp [ourIBPAxisPlanePairOrbitMultiplicity, beforeOrbit]
  have hafter (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (afterOrbit sector site moved) (1 : ℚ))) =
        (afterLabeled sector site moved).tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            ((afterLabeled sector site moved).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single]
    simp [ourIBPAxisPlanePairOrbitMultiplicity, afterOrbit]
  simp_rw [hbefore, hafter]
  congr 2

private theorem thirdCoordinate_reynolds_before_after
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (beforeOrbit sector site moved) (1 : ℚ))) =
      ourThirdIBPAxisPlanePairCoordinate
        (sectorFieldOrbitReynolds 7 2
          (Finsupp.single (afterOrbit sector site moved) (1 : ℚ))) := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hbefore (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (beforeOrbit sector site moved) (1 : ℚ))) =
        (beforeLabeled sector site moved).tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            ((beforeLabeled sector site moved).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single]
    simp [ourThirdIBPAxisPlanePairOrbitMultiplicity, beforeOrbit]
  have hafter (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (afterOrbit sector site moved) (1 : ℚ))) =
        (afterLabeled sector site moved).tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            ((afterLabeled sector site moved).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single]
    simp [ourThirdIBPAxisPlanePairOrbitMultiplicity, afterOrbit]
  simp_rw [hbefore, hafter]
  congr 2

private theorem profileCoordinate_reynolds_before_after
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (beforeOrbit sector site moved) (1 : ℚ))) =
      ourTraceCycleProfileAxisCoordinate
        (sectorFieldOrbitReynolds 7 2
          (Finsupp.single (afterOrbit sector site moved) (1 : ℚ))) := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hbefore (h : Hypercubic4) :
      ourTraceCycleProfileAxisCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (beforeOrbit sector site moved) (1 : ℚ))) =
        (beforeLabeled sector site moved).tensorSign h *
          ourTraceCycleProfileAxisMultiplicity
            ((beforeLabeled sector site moved).hypercubicAct h) := by
    rw [signedSectorFieldOrbitAction_single,
      ourTraceCycleProfileAxisCoordinate_single,
      ourTraceCycleProfileAxisOrbitMultiplicity_action]
    simp [beforeOrbit]
  have hafter (h : Hypercubic4) :
      ourTraceCycleProfileAxisCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (afterOrbit sector site moved) (1 : ℚ))) =
        (afterLabeled sector site moved).tensorSign h *
          ourTraceCycleProfileAxisMultiplicity
            ((afterLabeled sector site moved).hypercubicAct h) := by
    rw [signedSectorFieldOrbitAction_single,
      ourTraceCycleProfileAxisCoordinate_single,
      ourTraceCycleProfileAxisOrbitMultiplicity_action]
    simp [afterOrbit]
  simp_rw [hbefore, hafter]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [show (beforeLabeled sector site moved).tensorSign h =
      (afterLabeled sector site moved).tensorSign h by rfl]
  exact congrArg (fun value : ℚ =>
    (beforeLabeled sector site moved).tensorSign h * value)
    (before_after_profile_raw sector site moved h)

/-! ## OUR equality of all correction components -/

private theorem invariantSevenAxis_before_after
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    ourInvariantSevenAxisCoordinate
      (Finsupp.single (beforeExactTarget sector site moved) (1 : ℚ)) =
      ourInvariantSevenAxisCoordinate
        (Finsupp.single (afterExactTarget sector site moved) (1 : ℚ)) := by
  unfold ourInvariantSevenAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_sevenTarget_single,
    exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_sevenTarget_single,
    derivativeCoordinate_reynolds_before_after]

private theorem invariantIBP_before_after
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    ourInvariantIBPAxisCoordinate
      (Finsupp.single (beforeExactTarget sector site moved) (1 : ℚ)) =
      ourInvariantIBPAxisCoordinate
        (Finsupp.single (afterExactTarget sector site moved) (1 : ℚ)) := by
  unfold ourInvariantIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_sevenTarget_single,
    exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_sevenTarget_single,
    ibpCoordinate_reynolds_before_after]

private theorem invariantThird_before_after
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    ourInvariantThirdIBPAxisCoordinate
      (Finsupp.single (beforeExactTarget sector site moved) (1 : ℚ)) =
      ourInvariantThirdIBPAxisCoordinate
        (Finsupp.single (afterExactTarget sector site moved) (1 : ℚ)) := by
  unfold ourInvariantThirdIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_sevenTarget_single,
    exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_sevenTarget_single,
    thirdCoordinate_reynolds_before_after]

private theorem invariantProfile_before_after
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    ourInvariantTraceCycleProfileCoordinate
      (Finsupp.single (beforeExactTarget sector site moved) (1 : ℚ)) =
      ourInvariantTraceCycleProfileCoordinate
        (Finsupp.single (afterExactTarget sector site moved) (1 : ℚ)) := by
  unfold ourInvariantTraceCycleProfileCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_sevenTarget_single,
    exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_sevenTarget_single,
    profileCoordinate_reynolds_before_after]

private theorem exactFieldEightTrace_before_zero
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    exactFieldEightTraceProjection
      (Finsupp.single (beforeExactTarget sector site moved) (1 : ℚ)) = 0 := by
  unfold exactFieldEightTraceProjection
  simp only [LinearMap.comp_apply]
  rw [exactFieldEightProjection_sevenTarget_single]
  simp

private theorem exactFieldEightTrace_after_zero
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    exactFieldEightTraceProjection
      (Finsupp.single (afterExactTarget sector site moved) (1 : ℚ)) = 0 := by
  unfold exactFieldEightTraceProjection
  simp only [LinearMap.comp_apply]
  rw [exactFieldEightProjection_sevenTarget_single]
  simp

private theorem correction_before_after_unit
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    ourCycleProfileInvariantTraceOrderCorrection
      (Finsupp.single (beforeExactTarget sector site moved) (1 : ℚ)) =
      ourCycleProfileInvariantTraceOrderCorrection
        (Finsupp.single (afterExactTarget sector site moved) (1 : ℚ)) := by
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
    (moved : SourceSixMoved sector)
    (coefficient : ℚ) :
    ourCycleProfileInvariantTraceOrderCorrection
      (Finsupp.single (beforeExactTarget sector site moved) coefficient) =
      ourCycleProfileInvariantTraceOrderCorrection
        (Finsupp.single (afterExactTarget sector site moved) coefficient) := by
  rw [show Finsupp.single (beforeExactTarget sector site moved) coefficient =
      coefficient • Finsupp.single (beforeExactTarget sector site moved) (1 : ℚ) by simp,
    show Finsupp.single (afterExactTarget sector site moved) coefficient =
      coefficient • Finsupp.single (afterExactTarget sector site moved) (1 : ℚ) by simp,
    map_smul, map_smul, correction_before_after_unit]

private theorem sourceSix_leibniz_normalized_equal
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    ourCycleProfileInvariantTraceOrderCorrection
      (normalizeExactFieldRelabel
        (normalizeExactContextualBasis (insertLeibnizCarrier site .before moved))) =
      ourCycleProfileInvariantTraceOrderCorrection
        (normalizeExactFieldRelabel
          (normalizeExactContextualBasis (insertLeibnizCarrier site .after moved))) := by
  rw [normalizeBasis_orbit, normalizeBasis_orbit]
  set coefficient : ℚ := fieldAxisOrientationCoefficient
    (sectorFieldAxisAssignment (insertLeibnizCarrier site .before moved).2)
  have hcoefficient : fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment (insertLeibnizCarrier site .after moved).2) = coefficient := by rfl
  rw [hcoefficient]
  set beforeTarget : ExactFieldRelabelOrbitCarrier :=
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData (insertLeibnizCarrier site .before moved))
  set afterTarget : ExactFieldRelabelOrbitCarrier :=
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData (insertLeibnizCarrier site .after moved))
  have hbeforeTarget : beforeTarget = beforeExactTarget sector site moved := by rfl
  have hafterTarget : afterTarget = afterExactTarget sector site moved := by rfl
  change ourCycleProfileInvariantTraceOrderCorrection
      (Finsupp.single beforeTarget coefficient) =
    ourCycleProfileInvariantTraceOrderCorrection
      (Finsupp.single afterTarget coefficient)
  rw [hbeforeTarget, hafterTarget]
  exact correction_before_after_smul sector site moved coefficient

private theorem sourceSix_leibniz_normalized_single_equal
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (moved : SourceSixMoved sector) :
    ourCycleProfileInvariantTraceOrderCorrection
      (normalizeExactFieldRelabel
        (normalizeExactContextual
          (Finsupp.single (insertLeibnizCarrier site .before moved) (1 : ℚ)))) =
      ourCycleProfileInvariantTraceOrderCorrection
        (normalizeExactFieldRelabel
          (normalizeExactContextual
            (Finsupp.single (insertLeibnizCarrier site .after moved) (1 : ℚ)))) := by
  rw [normalizeExactContextual_single, normalizeExactContextual_single]
  simp only [one_smul]
  exact sourceSix_leibniz_normalized_equal sector site moved

/-! ## OUR corrected commutator columns -/

private theorem sourceSix_leibniz_physical_zero
    (policy : PhysicalRelationPolicy)
    (sector : DerivativeAlphaReducedSector 6 4)
    (site : CovariantCommutatorSite (sourceSixCarrier sector))
    (coefficient : ℚ) :
    ourCycleProfileInvariantTraceOrderCorrection
      (leibnizOrbitPhysicalRelationOperator policy
        (Finsupp.single (.covariantCommutator (sourceSixCarrier sector) site)
          coefficient)) = 0 := by
  unfold leibnizOrbitPhysicalRelationOperator leibnizNormalizedPhysicalRelationOperator
  simp only [LinearMap.comp_apply, leibnizPhysicalRelationOperator_single,
    leibnizPhysicalRelationRow_covariantCommutator, leibnizCommutatorRow, map_sub,
    map_sum, LinearMap.map_smul]
  rw [normalized_single_zero_of_fieldCount_lt_seven (sourceSixCarrier sector)
      (by change (6 : Fin 9).1 < 7; decide),
    normalized_single_zero_of_fieldCount_lt_seven
      (swapExactDerivativePositions (sourceSixCarrier sector) site.outer site.inner)
      (by change (6 : Fin 9).1 < 7; decide)]
  rw [Finset.sum_eq_zero (fun moved _ => by
    rw [sourceSix_leibniz_normalized_single_equal sector site moved, sub_self])]
  simp

/-- OUR source-six descent for the Leibniz-corrected commutator row: every
curvature pair of the row cancels in OUR correction. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_leibnizCommutator_zero_of_source_eq_six
    (policy : PhysicalRelationPolicy) (carrier : RelationCarrier)
    (site : CovariantCommutatorSite carrier) (coefficient : ℚ)
    (hsource : carrier.1 = (6 : Fin 9)) :
    ourCycleProfileInvariantTraceOrderCorrection
      (leibnizOrbitPhysicalRelationOperator policy
        (Finsupp.single (.covariantCommutator carrier site) coefficient)) = 0 := by
  rcases carrier with ⟨fieldCount, sector⟩
  change fieldCount = (6 : Fin 9) at hsource
  subst fieldCount
  exact sourceSix_leibniz_physical_zero policy sector site coefficient

/-- Below six source field strengths every term of the corrected commutator
row lies outside OUR two observable bands. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_leibnizCommutator_zero_of_source_lt_six
    (policy : PhysicalRelationPolicy) (carrier : RelationCarrier)
    (site : CovariantCommutatorSite carrier) (coefficient : ℚ)
    (hsource : carrier.1.1 < 6) :
    ourCycleProfileInvariantTraceOrderCorrection
      (leibnizOrbitPhysicalRelationOperator policy
        (Finsupp.single (.covariantCommutator carrier site) coefficient)) = 0 := by
  unfold leibnizOrbitPhysicalRelationOperator leibnizNormalizedPhysicalRelationOperator
  simp only [LinearMap.comp_apply, leibnizPhysicalRelationOperator_single,
    leibnizPhysicalRelationRow_covariantCommutator, leibnizCommutatorRow, map_sub,
    map_sum, LinearMap.map_smul]
  rw [normalized_single_zero_of_fieldCount_lt_seven carrier (by omega),
    normalized_single_zero_of_fieldCount_lt_seven
      (swapExactDerivativePositions carrier site.outer site.inner)
      (by change carrier.1.1 < 7; omega)]
  rw [Finset.sum_eq_zero (fun moved _ => by
    rw [normalized_single_zero_of_fieldCount_lt_seven
        (insertLeibnizCarrier site .before moved) (by change carrier.1.1 + 1 < 7; omega),
      normalized_single_zero_of_fieldCount_lt_seven
        (insertLeibnizCarrier site .after moved) (by change carrier.1.1 + 1 < 7; omega),
      sub_self])]
  simp

/-! ## The seven- and eight-field source bands -/

/-- With seven or more field strengths a carrier has at most two derivatives,
so a commutator site uses all of them and its field has no outer derivative. -/
theorem outerSameOwnerPositions_eq_empty_of_seven_le {carrier : RelationCarrier}
    (site : CovariantCommutatorSite carrier) (hseven : 7 ≤ carrier.1.1) :
    outerSameOwnerPositions site = ∅ := by
  ext position
  simp only [mem_outerSameOwnerPositions]
  constructor
  · rintro ⟨hlt, -⟩
    exfalso
    have hinner := site.inner.isLt
    have houter : site.outer.1 < site.inner.1 := site.outer_lt_inner
    have hposition : position.1 < site.outer.1 := hlt
    have hcount : dimension16DerivativeCount carrier.1 ≤ 2 := by
      unfold dimension16DerivativeCount
      omega
    omega
  · intro h
    simp at h

/-- The corrected and earlier orbit operators agree on every column whose
source has seven or eight field strengths. -/
theorem leibnizOrbitPhysicalRelationOperator_single_eq_of_seven_le
    (policy : PhysicalRelationPolicy)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ)
    (hseven : 7 ≤ (physicalRelationGeneratorSourceFieldCount generator).1) :
    leibnizOrbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient) =
      orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient) :=
  leibnizOrbitPhysicalRelationOperator_single_of_row_eq generator coefficient
    (leibnizPhysicalRelationRow_eq_physicalRelationRow generator
      (fun carrier site hgenerator => by
        subst hgenerator
        exact outerSameOwnerPositions_eq_empty_of_seven_le site hseven))

/-! ## OUR corrected descent outside the seven-field source band -/

/-- OUR profile correction annihilates every column of the Leibniz-corrected
operator outside the seven-field source band.  Commutator columns with source
six or below are handled above; a commutator site has fewer than eight field
strengths; every other generator has the same row as in the earlier operator. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_leibnizPhysicalRelation_zero_of_source_ne_seven
    (policy : PhysicalRelationPolicy)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ)
    (hseven : physicalRelationGeneratorSourceFieldCount generator ≠ ourSevenFieldCount) :
    ourCycleProfileInvariantTraceOrderCorrection
      (leibnizOrbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient)) = 0 := by
  by_cases hcommutator : ∃ (carrier : RelationCarrier)
      (site : CovariantCommutatorSite carrier), generator = .covariantCommutator carrier site
  · rcases hcommutator with ⟨carrier, site, rfl⟩
    have hsource : carrier.1 ≠ ourSevenFieldCount := hseven
    have height := site.fieldCount_lt_eight
    by_cases hsix : carrier.1 = (6 : Fin 9)
    · exact ourCycleProfileInvariantTraceOrderCorrection_leibnizCommutator_zero_of_source_eq_six
        policy carrier site coefficient hsix
    · have hnotSeven : carrier.1.1 ≠ 7 := fun h =>
        hsource (by ext; simpa [ourSevenFieldCount] using h)
      have hnotSix : carrier.1.1 ≠ 6 := fun h => hsix (by ext; simpa using h)
      exact ourCycleProfileInvariantTraceOrderCorrection_leibnizCommutator_zero_of_source_lt_six
        policy carrier site coefficient (by omega)
  · rw [leibnizOrbitPhysicalRelationOperator_single_of_row_eq generator coefficient
      (leibnizPhysicalRelationRow_eq_physicalRelationRow generator
        (fun carrier site hgenerator => absurd ⟨carrier, site, hgenerator⟩ hcommutator))]
    exact ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_ne_seven
      policy generator coefficient hseven

/-- OUR complete source-six descent for the corrected operator. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_leibnizPhysicalRelation_zero_of_source_eq_six
    (policy : PhysicalRelationPolicy)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ)
    (hsource : physicalRelationGeneratorSourceFieldCount generator = (6 : Fin 9)) :
    ourCycleProfileInvariantTraceOrderCorrection
      (leibnizOrbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient)) = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_leibnizPhysicalRelation_zero_of_source_ne_seven
    policy generator coefficient (by rw [hsource]; decide)

#print axioms ourCycleProfileInvariantTraceOrderCorrection_leibnizCommutator_zero_of_source_eq_six
#print axioms ourCycleProfileInvariantTraceOrderCorrection_leibnizPhysicalRelation_zero_of_source_ne_seven
#print axioms ourCycleProfileInvariantTraceOrderCorrection_leibnizPhysicalRelation_zero_of_source_eq_six
#print axioms leibnizOrbitPhysicalRelationOperator_single_eq_of_seven_le

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LeibnizSourceSix
