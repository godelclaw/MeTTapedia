import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTraceCycleProfile

/-!
# OUR trace-cycle profile coordinate on the seven-field relation carrier

The complete finite three-cut cycle-profile certificate determines a rational
linear combination of trace-cycle gates.  This module lifts that combination
to an actual signed-`H(4)`-invariant coordinate on the seven-field orbit
space.  It is added to the pre-existing three-coordinate correction, rather
than being attributed to the manuscript.

On the two explicitly normalized canonical trace rows currently available in
the physical relation operator, the lifted profile has value `-1 / 2` on the
polarized trace-anticommutator and zero on the fundamental three-cut row.
It therefore cancels the former's existing residual and retains the latter's
zero.  The finite cycle-profile census supplies the topology calculation for
all `210` ordered three-cut placements on the same seven-cycle, but this file
does not yet identify every such placement with a full physical relation row.
It consequently makes no claim of full relation-submodule descent or of a
Wilson-functional analytic coordinate construction.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileRepair

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open SU2LatticeFDCensusNoGo
open HypercubicRawFDDimension16Census
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16SU2TraceRelations
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceProjection
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceInvariantWitness
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction
open HypercubicDimension16WilsonTraceOrderTraceTopologyRepair
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair

/-- OUR rational trace-cycle profile applied to the derivative-axis
multiplicity.  A trace type may contribute at more than one cycle length. -/
def ourTraceCycleProfileAxisMultiplicity
    (sector : LabeledLocalWordSector 7 2) : ℚ :=
  ((if sector.trace.cycleType.count 2 = 1 then (6 / 5 : ℚ) else 0) +
    (if sector.trace.cycleType.count 3 = 1 then (13 / 10 : ℚ) else 0) +
      (if sector.trace.cycleType.count 4 = 1 then (-1 : ℚ) else 0) +
        (if sector.trace.cycleType.count 5 = 1 then (-7 / 10 : ℚ) else 0) +
          (if sector.trace.cycleType.count 6 = 1 then (-3 / 5 : ℚ) else 0)) *
    (derivativeAxisWordMultiplicity [0, 2] sector : ℚ)

/-- OUR profile multiplicity is invariant under simultaneous field relabeling. -/
theorem ourTraceCycleProfileAxisMultiplicity_relabel
    (rename : Equiv.Perm (Fin 7))
    (sector : LabeledLocalWordSector 7 2) :
    ourTraceCycleProfileAxisMultiplicity (sector.relabel rename) =
      ourTraceCycleProfileAxisMultiplicity sector := by
  unfold ourTraceCycleProfileAxisMultiplicity
  rw [ourTraceCycleType_relabel]
  simp [derivativeAxisWordMultiplicity_relabel]

/-- OUR profile scalar on ordinary seven-field relabel orbits. -/
def ourTraceCycleProfileAxisOrbitMultiplicity : FieldSevenOrbitCarrier → ℚ :=
  Quotient.lift (fun sector => ourTraceCycleProfileAxisMultiplicity sector) (by
    intro left right horbit
    change MulAction.orbitRel (Equiv.Perm (Fin 7))
      (LabeledLocalWordSector 7 2) left right at horbit
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at horbit
    rcases horbit with ⟨rename, hrename⟩
    change LabeledLocalWordSector.relabel rename right = left at hrename
    rw [← hrename]
    exact ourTraceCycleProfileAxisMultiplicity_relabel rename right)

/-- OUR linear profile coordinate on the seven-field ordinary-orbit space. -/
def ourTraceCycleProfileAxisCoordinate : FieldSevenOrbitSpace →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ ourTraceCycleProfileAxisOrbitMultiplicity

@[simp] theorem ourTraceCycleProfileAxisCoordinate_single
    (target : FieldSevenOrbitCarrier) (coefficient : ℚ) :
    ourTraceCycleProfileAxisCoordinate (Finsupp.single target coefficient) =
      coefficient * ourTraceCycleProfileAxisOrbitMultiplicity target := by
  simp [ourTraceCycleProfileAxisCoordinate]

/-- OUR profile orbit scalar follows a labeled sector under signed
hypercubic action. -/
theorem ourTraceCycleProfileAxisOrbitMultiplicity_action
    (sector : LabeledLocalWordSector 7 2) (h : Hypercubic4) :
    ourTraceCycleProfileAxisOrbitMultiplicity
      (FieldRelabelOrbitCarrier.hypercubicAct h (Quotient.mk _ sector)) =
      ourTraceCycleProfileAxisMultiplicity (sector.hypercubicAct h) := by
  simp [ourTraceCycleProfileAxisOrbitMultiplicity]

/-- A bounded signed-weight calculation determines OUR profile coordinate on
one Reynolds-averaged seven-field orbit. -/
theorem ourTraceCycleProfileAxisCoordinate_reynolds_single
    (sector : LabeledLocalWordSector 7 2) (weight : ℚ)
    (hweight :
      (∑ h : Hypercubic4,
        sector.tensorSign h *
          ourTraceCycleProfileAxisMultiplicity (sector.hypercubicAct h)) =
        weight) :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ sector : FieldSevenOrbitCarrier) (1 : ℚ))) =
      weight / 384 := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourTraceCycleProfileAxisCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (Quotient.mk _ sector : FieldSevenOrbitCarrier)
            (1 : ℚ))) =
        sector.tensorSign h *
          ourTraceCycleProfileAxisMultiplicity (sector.hypercubicAct h) := by
    rw [signedSectorFieldOrbitAction_single,
      ourTraceCycleProfileAxisCoordinate_single,
      ourTraceCycleProfileAxisOrbitMultiplicity_action]
    simp
  simp_rw [hterm]
  rw [hweight]
  ring

/-- OUR scaled full-carrier trace-cycle profile coordinate. -/
def ourInvariantTraceCycleProfileCoordinate :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] ℚ :=
  (12 : ℚ) •
    (ourTraceCycleProfileAxisCoordinate.comp
      (exactFieldSevenProjection.comp exactFieldOrbitReynolds))

/-- OUR profile coordinate is signed-`H(4)` invariant. -/
theorem ourInvariantTraceCycleProfileCoordinate_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourInvariantTraceCycleProfileCoordinate
      (signedExactFieldRelabelOrbitAction h value) =
      ourInvariantTraceCycleProfileCoordinate value := by
  unfold ourInvariantTraceCycleProfileCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldOrbitReynolds_action]

/-- OUR profile coordinate is unchanged by exact-field Reynolds averaging. -/
theorem ourInvariantTraceCycleProfileCoordinate_exactFieldOrbitReynolds
    (value : ExactFieldRelabelOrbitSpace) :
    ourInvariantTraceCycleProfileCoordinate (exactFieldOrbitReynolds value) =
      ourInvariantTraceCycleProfileCoordinate value := by
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  simp_rw [ourInvariantTraceCycleProfileCoordinate_signed_action]
  rw [Finset.sum_const, Finset.card_univ, Hypercubic4.card_hypercubic4]
  module

/-- OUR profile contribution to the incoming trace class. -/
def ourTraceCycleProfileInvariantTraceContribution :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ourInvariantTraceCycleProfileCoordinate.smulRight literalIncomingCommutatorClass

/-- OUR profile correction replaces the ad hoc two- and six-cycle calibration
by the complete finite three-cut cycle profile. -/
def ourCycleProfileInvariantTraceOrderCorrection :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ourThreeCoordinateInvariantTraceOrderCorrection +
    ourTraceCycleProfileInvariantTraceContribution

/-! ## Bounded replay on the canonical fundamental three-cut row -/

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutBase_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutBaseLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourFundamentalThreeCutBaseLabeled.hypercubicAct h)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapFirstSecond_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapFirstSecondLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourFundamentalThreeCutSwapFirstSecondLabeled.hypercubicAct h)) =
      -96 / 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapFirstThird_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapFirstThirdLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourFundamentalThreeCutSwapFirstThirdLabeled.hypercubicAct h)) =
      16 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapSecondThird_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapSecondThirdLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourFundamentalThreeCutSwapSecondThirdLabeled.hypercubicAct h)) =
      -96 / 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutForward_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutForwardLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourFundamentalThreeCutForwardLabeled.hypercubicAct h)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutBackward_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutBackwardLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourFundamentalThreeCutBackwardLabeled.hypercubicAct h)) =
      -112 / 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourFundamentalThreeCutBase :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBaseOrbit (1 : ℚ))) = 0 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutBaseLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourFundamentalThreeCutBaseLabeled 0
    ourFundamentalThreeCutBase_profileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourFundamentalThreeCutSwapFirstSecond :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutSwapFirstSecondOrbit (1 : ℚ))) =
      -1 / 20 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutSwapFirstSecondLabeled :
            FieldSevenOrbitCarrier) (1 : ℚ))) = -1 / 20
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourFundamentalThreeCutSwapFirstSecondLabeled (-96 / 5)
    ourFundamentalThreeCutSwapFirstSecond_profileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourFundamentalThreeCutSwapFirstThird :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutSwapFirstThirdOrbit (1 : ℚ))) =
      1 / 24 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutSwapFirstThirdLabeled :
            FieldSevenOrbitCarrier) (1 : ℚ))) = 1 / 24
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourFundamentalThreeCutSwapFirstThirdLabeled 16
    ourFundamentalThreeCutSwapFirstThird_profileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourFundamentalThreeCutSwapSecondThird :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutSwapSecondThirdOrbit (1 : ℚ))) =
      -1 / 20 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutSwapSecondThirdLabeled :
            FieldSevenOrbitCarrier) (1 : ℚ))) = -1 / 20
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourFundamentalThreeCutSwapSecondThirdLabeled (-96 / 5)
    ourFundamentalThreeCutSwapSecondThird_profileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourFundamentalThreeCutForward :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutForwardOrbit (1 : ℚ))) = 0 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutForwardLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourFundamentalThreeCutForwardLabeled 0
    ourFundamentalThreeCutForward_profileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourFundamentalThreeCutBackward :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBackwardOrbit (1 : ℚ))) =
      -7 / 120 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutBackwardLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = -7 / 120
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourFundamentalThreeCutBackwardLabeled (-112 / 5)
    ourFundamentalThreeCutBackward_profileSignedWeight]
  norm_num

theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourFundamentalThreeCut :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBaseOrbit (1 : ℚ) -
          Finsupp.single ourFundamentalThreeCutSwapFirstSecondOrbit (1 : ℚ) -
            Finsupp.single ourFundamentalThreeCutSwapFirstThirdOrbit (1 : ℚ) -
              Finsupp.single ourFundamentalThreeCutSwapSecondThirdOrbit (1 : ℚ) +
                Finsupp.single ourFundamentalThreeCutForwardOrbit (1 : ℚ) +
                  Finsupp.single ourFundamentalThreeCutBackwardOrbit (1 : ℚ))) =
      0 := by
  simp only [map_sub, map_add,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourFundamentalThreeCutBase,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourFundamentalThreeCutSwapFirstSecond,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourFundamentalThreeCutSwapFirstThird,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourFundamentalThreeCutSwapSecondThird,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourFundamentalThreeCutForward,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourFundamentalThreeCutBackward]
  norm_num

theorem ourInvariantTraceCycleProfileCoordinate_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantTraceCycleProfileCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) = 0 := by
  unfold ourInvariantTraceCycleProfileCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourFundamentalThreeCut,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourFundamentalThreeCut]
  norm_num

/-! ## Bounded replay on the canonical trace-anticommutator row -/

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorBase_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorBaseLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourTraceAnticommutatorBaseLabeled.hypercubicAct h)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorSwap_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorSwapLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourTraceAnticommutatorSwapLabeled.hypercubicAct h)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorSplit_profileSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorSplitLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (ourTraceAnticommutatorSplitLabeled.hypercubicAct h)) = 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourTraceAnticommutatorBase :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorBaseOrbit (1 : ℚ))) = 0 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourTraceAnticommutatorBaseLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourTraceAnticommutatorBaseLabeled 0
    ourTraceAnticommutatorBase_profileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourTraceAnticommutatorSwap :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorSwapOrbit (1 : ℚ))) = 0 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourTraceAnticommutatorSwapLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourTraceAnticommutatorSwapLabeled 0
    ourTraceAnticommutatorSwap_profileSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourTraceAnticommutatorSplit :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorSplitOrbit (1 : ℚ))) = 1 / 24 := by
  change ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourTraceAnticommutatorSplitLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 1 / 24
  rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
    ourTraceAnticommutatorSplitLabeled 16
    ourTraceAnticommutatorSplit_profileSignedWeight]
  norm_num

theorem ourTraceCycleProfileAxisCoordinate_reynolds_ourTraceAnticommutator :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorBaseOrbit (1 : ℚ) +
          Finsupp.single ourTraceAnticommutatorSwapOrbit (1 : ℚ) -
            Finsupp.single ourTraceAnticommutatorSplitOrbit (1 : ℚ))) =
      -1 / 24 := by
  simp only [map_sub, map_add,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourTraceAnticommutatorBase,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourTraceAnticommutatorSwap,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourTraceAnticommutatorSplit]
  norm_num

theorem ourInvariantTraceCycleProfileCoordinate_ourTraceAnticommutator
    (policy : PhysicalRelationPolicy) :
    ourInvariantTraceCycleProfileCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      -1 / 2 := by
  unfold ourInvariantTraceCycleProfileCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourTraceAnticommutator,
    ourTraceCycleProfileAxisCoordinate_reynolds_ourTraceAnticommutator]
  norm_num

/-- OUR profile correction annihilates the canonical physical fundamental
three-cut row under either relation policy. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) = 0 := by
  unfold ourCycleProfileInvariantTraceOrderCorrection
    ourTraceCycleProfileInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero,
    ourInvariantTraceCycleProfileCoordinate_ourFundamentalThreeCut_zero]
  simp

/-- OUR profile correction annihilates the canonical physical polarized
trace-anticommutator row under either relation policy. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_ourTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 := by
  unfold ourCycleProfileInvariantTraceOrderCorrection
    ourTraceCycleProfileInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator,
    ourInvariantTraceCycleProfileCoordinate_ourTraceAnticommutator]
  module

/-- The profile correction also kills the corresponding Reynolds-averaged
fundamental relation member. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_invariantFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (ourInvariantFundamentalThreeCutRow policy).1 = 0 := by
  rw [show (ourInvariantFundamentalThreeCutRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) by
        rfl]
  unfold ourCycleProfileInvariantTraceOrderCorrection
    ourTraceCycleProfileInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply]
  rw [ourThreeCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourInvariantTraceCycleProfileCoordinate_exactFieldOrbitReynolds,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero,
    ourInvariantTraceCycleProfileCoordinate_ourFundamentalThreeCut_zero]
  simp

/-- The profile correction also kills the corresponding Reynolds-averaged
polarized trace-anticommutator relation member. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (ourInvariantTraceAnticommutatorRow policy).1 = 0 := by
  rw [show (ourInvariantTraceAnticommutatorRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) by
        rfl]
  unfold ourCycleProfileInvariantTraceOrderCorrection
    ourTraceCycleProfileInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply]
  rw [ourThreeCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourInvariantTraceCycleProfileCoordinate_exactFieldOrbitReynolds,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator,
    ourInvariantTraceCycleProfileCoordinate_ourTraceAnticommutator]
  module

#print axioms ourTraceCycleProfileAxisMultiplicity_relabel
#print axioms ourInvariantTraceCycleProfileCoordinate_signed_action
#print axioms ourFundamentalThreeCutBase_profileSignedWeight
#print axioms ourTraceAnticommutatorSplit_profileSignedWeight
#print axioms ourInvariantTraceCycleProfileCoordinate_ourFundamentalThreeCut_zero
#print axioms ourInvariantTraceCycleProfileCoordinate_ourTraceAnticommutator
#print axioms ourCycleProfileInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_ourTraceAnticommutator_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_invariantFundamentalThreeCut_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileRepair
