import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantBianchi
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantEOM
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldEightTracePhysicalLift

/-!
# OUR compatibility audit for the two-class source-seven repair

The bounded two-class correction repairs two concrete covariant-commutator
rows.  To make it useful as an extension of the existing trace-order
correction, its new secondary profile coordinate must vanish on the already
certified rows.  The finite signed-`H(4)` replays below show that it does
vanish on the first-IBP, Bianchi, EOM, fundamental, polarized-trace, and
derivative-free field-eight rows.  On the genuine second-IBP row, however,
its exact value is one.  Hence subtracting the secondary residual gives an
explicit nonzero second-IBP mismatch.

This is an OUR finite compatibility audit and obstruction certificate.  It
does not claim a complete source-seven census, nor that no further coordinate
can repair the displayed second-IBP mismatch.
-/

set_option autoImplicit false
noncomputable section
set_option maxRecDepth 100000

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibility

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open SU2LatticeFDCensusNoGo
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16IncomingCommutatorTraceCoupledColumn
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceProjection
open HypercubicDimension16IncomingCommutatorTraceInvariantWitness
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderInvariantBianchi
open HypercubicDimension16WilsonTraceOrderInvariantEOM
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
open HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileDifferential
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenCorrectionRefutation
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair

/-! ## First integration by parts -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced secondary-profile replay for each explicit first-IBP
summand. -/
theorem ourIBP_secondaryPlaneProfileSignedWeight (field : Fin 7) :
    (∑ h : Hypercubic4,
      (ourIBPLabeledTerm field).tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2) ((ourIBPLabeledTerm field).hypercubicAct h) : ℚ)) =
      0 := by
  fin_cases field <;> decide +kernel

/-- The secondary profile coordinate vanishes on every Reynolds-averaged
first-IBP summand. -/
theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourIBP
    (field : Fin 7) :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (ourIBPOrbit field) (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ (ourIBPLabeledTerm field) : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 0 2) (ourIBPLabeledTerm field) 0
    (ourIBP_secondaryPlaneProfileSignedWeight field)]
  norm_num

/-- The secondary profile coordinate vanishes on the complete explicit
first-IBP seven-field row. -/
theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourIBPRow :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (∑ field : Fin 7, Finsupp.single (ourIBPOrbit field) (1 : ℚ))) = 0 := by
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro field _
  exact ourSecondaryPlaneProfileCoordinate_reynolds_ourIBP field

/-- The new secondary profile coordinate vanishes on the actual first-IBP
relation. -/
theorem ourSecondaryPlaneProfileInvariantCoordinate_ourIBP_zero :
    ourSecondaryPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  unfold ourSecondaryPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourIBP,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourIBPRow]
  norm_num

/-! ## Second integration by parts -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced aggregate replay for the genuine second-IBP row.  The
value is nonzero, so the individual summands must not be treated as separate
zero certificates. -/
theorem ourSecondIBP_secondaryPlaneProfileAggregateSignedWeight :
    (∑ field : Fin 7, ∑ h : Hypercubic4,
      (ourSecondIBPLabeledTerm field).tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2)
          ((ourSecondIBPLabeledTerm field).hypercubicAct h) : ℚ)) = 16 := by
  decide +kernel

/-- The raw secondary coordinate has value `1 / 24` on the Reynolds average
of the complete second-IBP row. -/
theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourSecondIBPRow :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (∑ field : Fin 7, Finsupp.single (ourSecondIBPOrbit field) (1 : ℚ))) =
      1 / 24 := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (field : Fin 7) (h : Hypercubic4) :
      ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (ourSecondIBPOrbit field) (1 : ℚ))) =
        (ourSecondIBPLabeledTerm field).tensorSign h *
          (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
            (planeLookup 0 2)
            ((ourSecondIBPLabeledTerm field).hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeWordPlanePairCoordinate_single]
    simp [ourDerivativeWordPlanePairOrbitMultiplicity, ourSecondIBPOrbit]
  simp_rw [hterm]
  rw [← Finset.smul_sum, ourSecondIBP_secondaryPlaneProfileAggregateSignedWeight]
  norm_num

/-- The normalized secondary profile coordinate has exact value one on the
actual second-IBP relation under either physical policy. -/
theorem ourSecondaryPlaneProfileInvariantCoordinate_ourSecondIBP
    (policy : PhysicalRelationPolicy) :
    ourSecondaryPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 1 := by
  unfold ourSecondaryPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourSecondIBP,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourSecondIBPRow]
  norm_num

/-! ## Bianchi -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced secondary-profile replay for the base Bianchi summand. -/
theorem ourBianchiBase_secondaryPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourBianchiBaseLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2) (ourBianchiBaseLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced secondary-profile replay for the first rotated Bianchi
summand. -/
theorem ourBianchiRotateOne_secondaryPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourBianchiRotateOneLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2) (ourBianchiRotateOneLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced secondary-profile replay for the second rotated Bianchi
summand. -/
theorem ourBianchiRotateTwo_secondaryPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourBianchiRotateTwoLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2) (ourBianchiRotateTwoLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourBianchiBase :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiBaseOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourBianchiBaseLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 0 2) ourBianchiBaseLabeled 0
    ourBianchiBase_secondaryPlaneProfileSignedWeight]
  norm_num

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourBianchiRotateOne :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourBianchiRotateOneLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 0 2) ourBianchiRotateOneLabeled 0
    ourBianchiRotateOne_secondaryPlaneProfileSignedWeight]
  norm_num

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourBianchiRotateTwo :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateTwoOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourBianchiRotateTwoLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 0 2) ourBianchiRotateTwoLabeled 0
    ourBianchiRotateTwo_secondaryPlaneProfileSignedWeight]
  norm_num

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourBianchiRotateOne_neg :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourBianchiRotateOneOrbit (-1 : ℚ))) = 0 := by
  rw [show Finsupp.single ourBianchiRotateOneOrbit (-1 : ℚ) =
      -Finsupp.single ourBianchiRotateOneOrbit (1 : ℚ) by simp,
    map_neg, map_neg,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourBianchiRotateOne]
  simp

/-- The new secondary profile coordinate vanishes on the actual Bianchi
relation under either physical policy. -/
theorem ourSecondaryPlaneProfileInvariantCoordinate_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourSecondaryPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  unfold ourSecondaryPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourBianchi]
  simp only [LinearMap.map_add,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourBianchiBase,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourBianchiRotateOne_neg,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourBianchiRotateTwo]
  norm_num

/-! ## On-shell equation of motion -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced secondary-profile replay for the first nonzero EOM
summand. -/
theorem ourEOMZero_secondaryPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourEOMZeroLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2) (ourEOMZeroLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced secondary-profile replay for the second nonzero EOM
summand. -/
theorem ourEOMOne_secondaryPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourEOMOneLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2) (ourEOMOneLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced secondary-profile replay for the third nonzero EOM
summand. -/
theorem ourEOMThree_secondaryPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourEOMThreeLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2) (ourEOMThreeLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourEOMZero :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMZeroOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourEOMZeroLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 0 2) ourEOMZeroLabeled 0
    ourEOMZero_secondaryPlaneProfileSignedWeight]
  norm_num

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourEOMOne :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMOneOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourEOMOneLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 0 2) ourEOMOneLabeled 0
    ourEOMOne_secondaryPlaneProfileSignedWeight]
  norm_num

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourEOMThree :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMThreeOrbit (1 : ℚ))) = 0 := by
  change ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourEOMThreeLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 0 2) ourEOMThreeLabeled 0
    ourEOMThree_secondaryPlaneProfileSignedWeight]
  norm_num

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourEOMThree_neg :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourEOMThreeOrbit (-1 : ℚ))) = 0 := by
  rw [show Finsupp.single ourEOMThreeOrbit (-1 : ℚ) =
      -Finsupp.single ourEOMThreeOrbit (1 : ℚ) by simp,
    map_neg, map_neg,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourEOMThree]
  simp

/-- The new secondary profile coordinate vanishes on the actual on-shell EOM
relation. -/
theorem ourSecondaryPlaneProfileInvariantCoordinate_ourEOM_zero :
    ourSecondaryPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  unfold ourSecondaryPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourEOM]
  simp only [LinearMap.map_add,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourEOMZero,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourEOMOne,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourEOMThree_neg]
  norm_num

/-! ## Fundamental and trace relations -/

/-- A reusable zero-weight form of the secondary profile Reynolds replay. -/
theorem ourSecondaryPlaneProfileCoordinate_reynolds_single_zero
    (sector : LabeledLocalWordSector 7 2)
    (hweight :
      (∑ h : Hypercubic4,
        sector.tensorSign h *
          (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
            (planeLookup 0 2) (sector.hypercubicAct h) : ℚ)) = 0) :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ sector : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0 := by
  rw [ourDerivativeWordPlanePairCoordinate_reynolds_single
    (planeLookup 0 2) sector 0 hweight]
  norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced secondary-profile replay for the fundamental base term. -/
theorem ourFundamentalThreeCutBase_secondaryPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutBaseLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2)
          (ourFundamentalThreeCutBaseLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced secondary-profile replay for the first fundamental swap. -/
theorem ourFundamentalThreeCutSwapFirstSecond_secondaryPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapFirstSecondLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2)
          (ourFundamentalThreeCutSwapFirstSecondLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced secondary-profile replay for the second fundamental swap. -/
theorem ourFundamentalThreeCutSwapFirstThird_secondaryPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapFirstThirdLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2)
          (ourFundamentalThreeCutSwapFirstThirdLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced secondary-profile replay for the third fundamental swap. -/
theorem ourFundamentalThreeCutSwapSecondThird_secondaryPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapSecondThirdLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2)
          (ourFundamentalThreeCutSwapSecondThirdLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced secondary-profile replay for the forward fundamental
three-cycle. -/
theorem ourFundamentalThreeCutForward_secondaryPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutForwardLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2)
          (ourFundamentalThreeCutForwardLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced secondary-profile replay for the backward fundamental
three-cycle. -/
theorem ourFundamentalThreeCutBackward_secondaryPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutBackwardLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2)
          (ourFundamentalThreeCutBackwardLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutBase :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBaseOrbit (1 : ℚ))) = 0 := by
  simpa [ourFundamentalThreeCutBaseOrbit] using
    ourSecondaryPlaneProfileCoordinate_reynolds_single_zero
      ourFundamentalThreeCutBaseLabeled
      ourFundamentalThreeCutBase_secondaryPlaneProfileSignedWeight

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutSwapFirstSecond :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutSwapFirstSecondOrbit (1 : ℚ))) =
      0 := by
  simpa [ourFundamentalThreeCutSwapFirstSecondOrbit] using
    ourSecondaryPlaneProfileCoordinate_reynolds_single_zero
      ourFundamentalThreeCutSwapFirstSecondLabeled
      ourFundamentalThreeCutSwapFirstSecond_secondaryPlaneProfileSignedWeight

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutSwapFirstThird :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutSwapFirstThirdOrbit (1 : ℚ))) =
      0 := by
  simpa [ourFundamentalThreeCutSwapFirstThirdOrbit] using
    ourSecondaryPlaneProfileCoordinate_reynolds_single_zero
      ourFundamentalThreeCutSwapFirstThirdLabeled
      ourFundamentalThreeCutSwapFirstThird_secondaryPlaneProfileSignedWeight

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutSwapSecondThird :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutSwapSecondThirdOrbit (1 : ℚ))) =
      0 := by
  simpa [ourFundamentalThreeCutSwapSecondThirdOrbit] using
    ourSecondaryPlaneProfileCoordinate_reynolds_single_zero
      ourFundamentalThreeCutSwapSecondThirdLabeled
      ourFundamentalThreeCutSwapSecondThird_secondaryPlaneProfileSignedWeight

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutForward :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutForwardOrbit (1 : ℚ))) = 0 := by
  simpa [ourFundamentalThreeCutForwardOrbit] using
    ourSecondaryPlaneProfileCoordinate_reynolds_single_zero
      ourFundamentalThreeCutForwardLabeled
      ourFundamentalThreeCutForward_secondaryPlaneProfileSignedWeight

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutBackward :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBackwardOrbit (1 : ℚ))) = 0 := by
  simpa [ourFundamentalThreeCutBackwardOrbit] using
    ourSecondaryPlaneProfileCoordinate_reynolds_single_zero
      ourFundamentalThreeCutBackwardLabeled
      ourFundamentalThreeCutBackward_secondaryPlaneProfileSignedWeight

/-- The new secondary profile coordinate vanishes on the listed fundamental
three-cut row. -/
theorem ourSecondaryPlaneProfileInvariantCoordinate_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourSecondaryPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 := by
  unfold ourSecondaryPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourFundamentalThreeCut]
  simp only [LinearMap.map_sub, LinearMap.map_add,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutBase,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutSwapFirstSecond,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutSwapFirstThird,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutSwapSecondThird,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutForward,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourFundamentalThreeCutBackward]
  norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced secondary-profile replay for the trace-anticommutator base
term. -/
theorem ourTraceAnticommutatorBase_secondaryPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorBaseLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2)
          (ourTraceAnticommutatorBaseLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced secondary-profile replay for the trace-anticommutator
adjacent-swap term. -/
theorem ourTraceAnticommutatorSwap_secondaryPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorSwapLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2)
          (ourTraceAnticommutatorSwapLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Kernel-reduced secondary-profile replay for the trace-anticommutator
split term. -/
theorem ourTraceAnticommutatorSplit_secondaryPlaneProfileSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorSplitLabeled.tensorSign h *
        (ourDerivativeWordPlanePairMultiplicity (planeLookup 0 1) [0, 2]
          (planeLookup 0 2)
          (ourTraceAnticommutatorSplitLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourTraceAnticommutatorBase :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorBaseOrbit (1 : ℚ))) = 0 := by
  simpa [ourTraceAnticommutatorBaseOrbit] using
    ourSecondaryPlaneProfileCoordinate_reynolds_single_zero
      ourTraceAnticommutatorBaseLabeled
      ourTraceAnticommutatorBase_secondaryPlaneProfileSignedWeight

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourTraceAnticommutatorSwap :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorSwapOrbit (1 : ℚ))) = 0 := by
  simpa [ourTraceAnticommutatorSwapOrbit] using
    ourSecondaryPlaneProfileCoordinate_reynolds_single_zero
      ourTraceAnticommutatorSwapLabeled
      ourTraceAnticommutatorSwap_secondaryPlaneProfileSignedWeight

theorem ourSecondaryPlaneProfileCoordinate_reynolds_ourTraceAnticommutatorSplit :
    ourDerivativeWordPlanePairCoordinate (planeLookup 0 2)
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorSplitOrbit (1 : ℚ))) = 0 := by
  simpa [ourTraceAnticommutatorSplitOrbit] using
    ourSecondaryPlaneProfileCoordinate_reynolds_single_zero
      ourTraceAnticommutatorSplitLabeled
      ourTraceAnticommutatorSplit_secondaryPlaneProfileSignedWeight

/-- The new secondary profile coordinate vanishes on the listed polarized
trace-anticommutator row. -/
theorem ourSecondaryPlaneProfileInvariantCoordinate_ourTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourSecondaryPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 := by
  unfold ourSecondaryPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourTraceAnticommutator]
  simp only [LinearMap.map_sub, LinearMap.map_add,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourTraceAnticommutatorBase,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourTraceAnticommutatorSwap,
    ourSecondaryPlaneProfileCoordinate_reynolds_ourTraceAnticommutatorSplit]
  norm_num

/-! ## The augmented correction -/

/-- OUR fixed residual of the existing profile correction on the secondary
source-seven commutator.  It is deliberately defined from the existing
correction, so the new term cancels exactly that certified defect rather than
assuming a presentation for its quotient class. -/
def ourSecondarySourceSevenResidual : FieldEightPhysicalTraceQuotient :=
  ourCycleProfileInvariantTraceOrderCorrection
    (orbitPhysicalRelationOperator .offShell
      (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator .offShell) 1))

/-- The stored secondary residual is nonzero: the augmentation makes a real
change rather than re-expressing the previous correction. -/
theorem ourSecondarySourceSevenResidual_ne_zero :
    ourSecondarySourceSevenResidual ≠ 0 := by
  exact ourCycleProfileInvariantTraceOrderCorrection_ourSecondaryCommutator_ne_zero
    .offShell

/-- The old correction takes the same secondary residual under either
relation policy. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_ourSecondaryCommutator_eq_residual
    (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
      ourSecondarySourceSevenResidual := by
  unfold ourSecondarySourceSevenResidual
  rw [orbitPhysicalRelationOperator_ourSecondaryCommutator_full policy,
    orbitPhysicalRelationOperator_ourSecondaryCommutator_full .offShell]

/-- The secondary profile coordinate is structurally zero on every
derivative-free eight-field inclusion. -/
theorem ourSecondaryPlaneProfileInvariantCoordinate_fieldEightExactEmbed_zero
    (value : FieldEightOrbitSpace) :
    ourSecondaryPlaneProfileInvariantCoordinate (fieldEightExactEmbed value) =
      0 := by
  unfold ourSecondaryPlaneProfileInvariantCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_fieldEightExactEmbed]
  simp

/-- OUR augmented trace-order correction: retain the prior cycle-profile
correction and add one secondary-profile coefficient that cancels its exact
secondary source-seven residual. -/
def ourAugmentedCycleProfileInvariantTraceOrderCorrection :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ourCycleProfileInvariantTraceOrderCorrection -
    ourSecondaryPlaneProfileInvariantCoordinate.smulRight
      ourSecondarySourceSevenResidual

/-- The new secondary coordinate is unchanged by exact-field Reynolds
averaging. -/
theorem ourSecondaryPlaneProfileInvariantCoordinate_exactFieldOrbitReynolds
    (value : ExactFieldRelabelOrbitSpace) :
    ourSecondaryPlaneProfileInvariantCoordinate (exactFieldOrbitReynolds value) =
      ourSecondaryPlaneProfileInvariantCoordinate value := by
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  simp_rw [ourSecondaryPlaneProfileInvariantCoordinate_signed_action]
  rw [Finset.sum_const, Finset.card_univ, Hypercubic4.card_hypercubic4]
  module

/-- OUR augmented correction remains unchanged by exact-field Reynolds
averaging. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_exactFieldOrbitReynolds
    (value : ExactFieldRelabelOrbitSpace) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (exactFieldOrbitReynolds value) =
      ourAugmentedCycleProfileInvariantTraceOrderCorrection value := by
  unfold ourAugmentedCycleProfileInvariantTraceOrderCorrection
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply]
  rw [ourCycleProfileInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourSecondaryPlaneProfileInvariantCoordinate_exactFieldOrbitReynolds]

/-- The augmented correction retains the incoming concrete source-seven
commutator row. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  unfold ourAugmentedCycleProfileInvariantTraceOrderCorrection
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    ourCycleProfileInvariantTraceOrderCorrection_ourCommutator_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_ourCommutator, zero_smul]
  simp

/-- The augmented correction now annihilates the secondary concrete
source-seven commutator row under either relation policy. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourSecondaryCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
      0 := by
  unfold ourAugmentedCycleProfileInvariantTraceOrderCorrection
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    ourCycleProfileInvariantTraceOrderCorrection_ourSecondaryCommutator_eq_residual,
    ourSecondaryPlaneProfileInvariantCoordinate_ourSecondaryCommutator]
  simp

/-- The augmentation retains the explicit first-IBP row. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourIBP_zero :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 := by
  unfold ourAugmentedCycleProfileInvariantTraceOrderCorrection
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    ourCycleProfileInvariantTraceOrderCorrection_ourIBP_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_ourIBP_zero, zero_smul]
  simp

/-- The two-class augmentation has the exact negative secondary residual on
the genuine second-IBP row. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourSecondIBP_eq_neg_residual
    (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) =
      -ourSecondarySourceSevenResidual := by
  unfold ourAugmentedCycleProfileInvariantTraceOrderCorrection
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    ourCycleProfileInvariantTraceOrderCorrection_ourSecondIBP_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_ourSecondIBP]
  simp

/-- The exact second-IBP value refutes compatibility of this two-class
augmentation with that already-certified row. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourSecondIBP_ne_zero
    (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) ≠ 0 := by
  rw [ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourSecondIBP_eq_neg_residual]
  exact neg_ne_zero.mpr ourSecondarySourceSevenResidual_ne_zero

/-- The augmentation retains the explicit Bianchi row. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 := by
  unfold ourAugmentedCycleProfileInvariantTraceOrderCorrection
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    ourCycleProfileInvariantTraceOrderCorrection_ourBianchi_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_ourBianchi_zero, zero_smul]
  simp

/-- The augmentation retains the explicit on-shell EOM row. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourEOM_zero :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  unfold ourAugmentedCycleProfileInvariantTraceOrderCorrection
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    ourCycleProfileInvariantTraceOrderCorrection_ourEOM_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_ourEOM_zero, zero_smul]
  simp

/-- The augmentation retains the listed fundamental three-cut row. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 := by
  unfold ourAugmentedCycleProfileInvariantTraceOrderCorrection
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    ourCycleProfileInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_ourFundamentalThreeCut_zero,
    zero_smul]
  simp

/-- The augmentation retains the listed polarized trace-anticommutator row. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 := by
  unfold ourAugmentedCycleProfileInvariantTraceOrderCorrection
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    ourCycleProfileInvariantTraceOrderCorrection_ourTraceAnticommutator_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_ourTraceAnticommutator_zero,
    zero_smul]
  simp

/-- The new coordinate vanishes uniformly on every lifted derivative-free
eight-field trace relation. -/
theorem ourSecondaryPlaneProfileInvariantCoordinate_liftedTraceGenerator_zero
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourSecondaryPlaneProfileInvariantCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)) =
      0 := by
  rw [show orbitPhysicalRelationOperator policy
      (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1) =
      fieldEightExactEmbed (fieldEightPhysicalTraceRow generator) by
        exact ourOrbitPhysicalRelationOperator_lift policy generator,
    ourSecondaryPlaneProfileInvariantCoordinate_fieldEightExactEmbed_zero]

/-- The augmentation retains every actual lifted derivative-free eight-field
trace relation. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_liftedTraceGenerator_zero
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)) =
      0 := by
  unfold ourAugmentedCycleProfileInvariantTraceOrderCorrection
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    ourCycleProfileInvariantTraceOrderCorrection_liftedTraceGenerator_zero,
    ourSecondaryPlaneProfileInvariantCoordinate_liftedTraceGenerator_zero,
    zero_smul]
  simp

/-- The augmentation retains every physical field-strength antisymmetry row,
which is already zero before applying either correction. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_antisymmetry_zero
    (policy : PhysicalRelationPolicy)
    (carrier : RelationCarrier) (slot : Fin carrier.1.1)
    (coefficient : ℚ) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (.antisymmetry carrier slot) coefficient)) = 0 := by
  rw [orbitPhysicalRelationOperator_antisymmetry_zero]
  simp

/-! ### Coordinate-free invariant representatives -/

/-- The augmented correction annihilates the existing invariant incoming
commutator representative. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_invariantCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (ourInvariantCommutatorRow policy).1 = 0 := by
  rw [show (ourInvariantCommutatorRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) by rfl,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourCommutator_zero]

/-- The augmented correction annihilates the existing invariant first-IBP
representative. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_invariantIBP_zero :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection ourInvariantIBPRow.1 =
      0 := by
  rw [show ourInvariantIBPRow.1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator .offShell
          (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) by rfl,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourIBP_zero]

/-- The two-class augmentation has the same exact mismatch on the invariant
second-IBP representative. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_invariantSecondIBP_eq_neg_residual
    (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (ourInvariantSecondIBPRow policy).1 = -ourSecondarySourceSevenResidual := by
  rw [show (ourInvariantSecondIBPRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) by rfl,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourSecondIBP_eq_neg_residual]

/-- The invariant second-IBP mismatch is nonzero. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_invariantSecondIBP_ne_zero
    (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (ourInvariantSecondIBPRow policy).1 ≠ 0 := by
  rw [ourAugmentedCycleProfileInvariantTraceOrderCorrection_invariantSecondIBP_eq_neg_residual]
  exact neg_ne_zero.mpr ourSecondarySourceSevenResidual_ne_zero

/-- The augmented correction annihilates the existing invariant Bianchi
representative. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_invariantBianchi_zero
    (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (ourInvariantBianchiRow policy).1 = 0 := by
  rw [show (ourInvariantBianchiRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) by rfl,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourBianchi_zero]

/-- The augmented correction annihilates the existing invariant on-shell EOM
representative. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_invariantEOM_zero :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection ourInvariantEOMRow.1 =
      0 := by
  rw [show ourInvariantEOMRow.1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator .onShell
          (Finsupp.single ourFieldSevenEOMGenerator 1)) by rfl,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourEOM_zero]

/-- The augmented correction annihilates the listed invariant fundamental
three-cut representative. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_invariantFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (ourInvariantFundamentalThreeCutRow policy).1 = 0 := by
  rw [show (ourInvariantFundamentalThreeCutRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) by rfl,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero]

/-- The augmented correction annihilates the listed invariant polarized
trace-anticommutator representative. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (ourInvariantTraceAnticommutatorRow policy).1 = 0 := by
  rw [show (ourInvariantTraceAnticommutatorRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) by rfl,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourTraceAnticommutator_zero]

/-- The augmented correction also retains the invariant lifted trace rows. -/
theorem ourAugmentedCycleProfileInvariantTraceOrderCorrection_invariantLiftedTraceGenerator_zero
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1))) =
      0 := by
  rw [ourAugmentedCycleProfileInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourAugmentedCycleProfileInvariantTraceOrderCorrection_liftedTraceGenerator_zero]

#print axioms ourIBP_secondaryPlaneProfileSignedWeight
#print axioms ourSecondaryPlaneProfileInvariantCoordinate_ourIBP_zero
#print axioms ourSecondIBP_secondaryPlaneProfileAggregateSignedWeight
#print axioms ourSecondaryPlaneProfileInvariantCoordinate_ourSecondIBP
#print axioms ourBianchiBase_secondaryPlaneProfileSignedWeight
#print axioms ourSecondaryPlaneProfileInvariantCoordinate_ourBianchi_zero
#print axioms ourEOMZero_secondaryPlaneProfileSignedWeight
#print axioms ourSecondaryPlaneProfileInvariantCoordinate_ourEOM_zero
#print axioms ourFundamentalThreeCutBase_secondaryPlaneProfileSignedWeight
#print axioms ourSecondaryPlaneProfileInvariantCoordinate_ourFundamentalThreeCut_zero
#print axioms ourTraceAnticommutatorBase_secondaryPlaneProfileSignedWeight
#print axioms ourSecondaryPlaneProfileInvariantCoordinate_ourTraceAnticommutator_zero
#print axioms ourSecondarySourceSevenResidual_ne_zero
#print axioms ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourCommutator_zero
#print axioms ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourSecondaryCommutator_zero
#print axioms ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourSecondIBP_ne_zero
#print axioms ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourEOM_zero
#print axioms ourAugmentedCycleProfileInvariantTraceOrderCorrection_liftedTraceGenerator_zero
#print axioms ourAugmentedCycleProfileInvariantTraceOrderCorrection_invariantEOM_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibility
