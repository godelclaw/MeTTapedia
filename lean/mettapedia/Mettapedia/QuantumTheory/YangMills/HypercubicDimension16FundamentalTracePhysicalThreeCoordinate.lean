import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalCycleProfile

/-!
# OUR physical three-cut three-coordinate bridge

The complete `210`-label physical fundamental-trace family has already been
transported into the coordinate-free signed-`H(4)` relation semantics. This
module checks the remaining three-coordinate part of OUR trace-order
correction on that same actual family.

For each physical trace rewiring, the three invariant coordinates reduce to
three signed finite weights: the derivative-axis weight and two independent
derivative-plane weights.  All three weights are trace-order blind: rewiring
changes the trace but not the decorated local word.  Thus the six weights in
every fundamental row are equal and their alternating coefficients cancel
symbolically. The semantic transport uses this structural identity to prove
that the three-coordinate correction vanishes on the whole finite cochain
family.

This is an OUR finite-sector construction. It does not claim a complete
relation census, descent through all of the coordinate-free relation space,
joint conditioning, or Wilson-functional analytic coordinates.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalThreeCoordinate

open V14HypercubicFDCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16SU2TraceRelations
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16FundamentalTraceCycleProfile
open HypercubicDimension16FundamentalTracePhysicalFamily
open HypercubicDimension16FundamentalTracePhysicalCycleProfile
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair
open HypercubicDimension16JointPhysicalQuotient

/-- OUR signed derivative-axis Reynolds weight of one physical trace rewire. -/
def physicalDerivativeAxisSignedWeight
    (rewire : Equiv.Perm (Fin 7)) : ℚ :=
  ∑ h : Hypercubic4,
    (physicalRewireLabeled rewire).tensorSign h *
      (derivativeAxisWordMultiplicity [0, 2]
        ((physicalRewireLabeled rewire).hypercubicAct h) : ℚ)

/-- OUR signed original plane-pair Reynolds weight of one physical trace
rewire. -/
def physicalIBPAxisPlanePairSignedWeight
    (rewire : Equiv.Perm (Fin 7)) : ℚ :=
  ∑ h : Hypercubic4,
    (physicalRewireLabeled rewire).tensorSign h *
      (ourIBPAxisPlanePairMultiplicity
        ((physicalRewireLabeled rewire).hypercubicAct h) : ℚ)

/-- OUR signed third plane-pair Reynolds weight of one physical trace
rewire. -/
def physicalThirdIBPAxisPlanePairSignedWeight
    (rewire : Equiv.Perm (Fin 7)) : ℚ :=
  ∑ h : Hypercubic4,
    (physicalRewireLabeled rewire).tensorSign h *
      (ourThirdIBPAxisPlanePairMultiplicity
        ((physicalRewireLabeled rewire).hypercubicAct h) : ℚ)

/-- OUR signed derivative-axis Reynolds weight of the unrewired physical
base term. -/
def physicalBaseDerivativeAxisSignedWeight : ℚ :=
  ∑ h : Hypercubic4,
    physicalBaseLabeled.tensorSign h *
      (derivativeAxisWordMultiplicity [0, 2]
        (physicalBaseLabeled.hypercubicAct h) : ℚ)

/-- OUR signed original plane-pair Reynolds weight of the unrewired physical
base term. -/
def physicalBaseIBPAxisPlanePairSignedWeight : ℚ :=
  ∑ h : Hypercubic4,
    physicalBaseLabeled.tensorSign h *
      (ourIBPAxisPlanePairMultiplicity
        (physicalBaseLabeled.hypercubicAct h) : ℚ)

/-- OUR signed third plane-pair Reynolds weight of the unrewired physical
base term. -/
def physicalBaseThirdIBPAxisPlanePairSignedWeight : ℚ :=
  ∑ h : Hypercubic4,
    physicalBaseLabeled.tensorSign h *
      (ourThirdIBPAxisPlanePairMultiplicity
        (physicalBaseLabeled.hypercubicAct h) : ℚ)

/-- The alternating six-rewire combination of an OUR physical base weight
and physical rewire weight. -/
def physicalFundamentalTraceAlternatingWeight
    (base : ℚ) (weight : Equiv.Perm (Fin 7) → ℚ)
    (labels : OurCertifiedThreeCutLabel) : ℚ :=
  base - weight (Equiv.swap (ourFundamentalTraceSiteOf labels).first
      (ourFundamentalTraceSiteOf labels).second) -
    weight (Equiv.swap (ourFundamentalTraceSiteOf labels).first
      (ourFundamentalTraceSiteOf labels).third) -
    weight (Equiv.swap (ourFundamentalTraceSiteOf labels).second
      (ourFundamentalTraceSiteOf labels).third) +
    weight (fundamentalCycleForward (ourFundamentalTraceSiteOf labels)) +
    weight (fundamentalCycleBackward (ourFundamentalTraceSiteOf labels))

/-- OUR alternating derivative-axis weight of an actual certified physical
fundamental-trace row. -/
def physicalFundamentalTraceDerivativeAxisWeight :
    OurCertifiedThreeCutLabel → ℚ :=
  physicalFundamentalTraceAlternatingWeight
    physicalBaseDerivativeAxisSignedWeight physicalDerivativeAxisSignedWeight

/-- OUR alternating original plane-pair weight of an actual certified
physical fundamental-trace row. -/
def physicalFundamentalTraceIBPAxisPlanePairWeight :
    OurCertifiedThreeCutLabel → ℚ :=
  physicalFundamentalTraceAlternatingWeight
    physicalBaseIBPAxisPlanePairSignedWeight physicalIBPAxisPlanePairSignedWeight

/-- OUR alternating third plane-pair weight of an actual certified physical
fundamental-trace row. -/
def physicalFundamentalTraceThirdIBPAxisPlanePairWeight :
    OurCertifiedThreeCutLabel → ℚ :=
  physicalFundamentalTraceAlternatingWeight
    physicalBaseThirdIBPAxisPlanePairSignedWeight
    physicalThirdIBPAxisPlanePairSignedWeight

/-- Trace rewiring changes no signed derivative-axis weight, since it leaves
the decorated local word unchanged. -/
theorem physicalRewire_derivativeAxisSignedWeight
    (rewire : Equiv.Perm (Fin 7)) :
    physicalDerivativeAxisSignedWeight rewire =
      physicalBaseDerivativeAxisSignedWeight := by
  unfold physicalDerivativeAxisSignedWeight
    physicalBaseDerivativeAxisSignedWeight
  apply Finset.sum_congr rfl
  intro h _
  rfl

/-- Trace rewiring changes no signed original plane-pair weight, since it
leaves the decorated local word unchanged. -/
theorem physicalRewire_IBPAxisPlanePairSignedWeight
    (rewire : Equiv.Perm (Fin 7)) :
    physicalIBPAxisPlanePairSignedWeight rewire =
      physicalBaseIBPAxisPlanePairSignedWeight := by
  unfold physicalIBPAxisPlanePairSignedWeight
    physicalBaseIBPAxisPlanePairSignedWeight
  apply Finset.sum_congr rfl
  intro h _
  rfl

/-- Trace rewiring changes no signed third plane-pair weight, since it
leaves the decorated local word unchanged. -/
theorem physicalRewire_thirdIBPAxisPlanePairSignedWeight
    (rewire : Equiv.Perm (Fin 7)) :
    physicalThirdIBPAxisPlanePairSignedWeight rewire =
      physicalBaseThirdIBPAxisPlanePairSignedWeight := by
  unfold physicalThirdIBPAxisPlanePairSignedWeight
    physicalBaseThirdIBPAxisPlanePairSignedWeight
  apply Finset.sum_congr rfl
  intro h _
  rfl

/-- Every certified physical placement has zero alternating derivative-axis
weight because all six trace rewires carry the same trace-blind weight. -/
theorem physicalFundamentalTraceDerivativeAxisWeight_all_zero :
    ∀ labels : OurCertifiedThreeCutLabel,
      physicalFundamentalTraceDerivativeAxisWeight labels = 0 := by
  intro labels
  unfold physicalFundamentalTraceDerivativeAxisWeight
    physicalFundamentalTraceAlternatingWeight
  rw [physicalRewire_derivativeAxisSignedWeight,
    physicalRewire_derivativeAxisSignedWeight,
    physicalRewire_derivativeAxisSignedWeight,
    physicalRewire_derivativeAxisSignedWeight,
    physicalRewire_derivativeAxisSignedWeight]
  ring

/-- Every certified physical placement has zero alternating original
plane-pair weight because all six trace rewires carry the same trace-blind
weight. -/
theorem physicalFundamentalTraceIBPAxisPlanePairWeight_all_zero :
    ∀ labels : OurCertifiedThreeCutLabel,
      physicalFundamentalTraceIBPAxisPlanePairWeight labels = 0 := by
  intro labels
  unfold physicalFundamentalTraceIBPAxisPlanePairWeight
    physicalFundamentalTraceAlternatingWeight
  rw [physicalRewire_IBPAxisPlanePairSignedWeight,
    physicalRewire_IBPAxisPlanePairSignedWeight,
    physicalRewire_IBPAxisPlanePairSignedWeight,
    physicalRewire_IBPAxisPlanePairSignedWeight,
    physicalRewire_IBPAxisPlanePairSignedWeight]
  ring

/-- Every certified physical placement has zero alternating third plane-pair
weight because all six trace rewires carry the same trace-blind weight. -/
theorem physicalFundamentalTraceThirdIBPAxisPlanePairWeight_all_zero :
    ∀ labels : OurCertifiedThreeCutLabel,
      physicalFundamentalTraceThirdIBPAxisPlanePairWeight labels = 0 := by
  intro labels
  unfold physicalFundamentalTraceThirdIBPAxisPlanePairWeight
    physicalFundamentalTraceAlternatingWeight
  rw [physicalRewire_thirdIBPAxisPlanePairSignedWeight,
    physicalRewire_thirdIBPAxisPlanePairSignedWeight,
    physicalRewire_thirdIBPAxisPlanePairSignedWeight,
    physicalRewire_thirdIBPAxisPlanePairSignedWeight,
    physicalRewire_thirdIBPAxisPlanePairSignedWeight]
  ring

/-- OUR derivative-axis coordinate on a Reynolds-averaged physical trace
rewire is its signed finite weight divided by the group order. -/
theorem physicalRewire_derivativeAxisCoordinate
    (rewire : Equiv.Perm (Fin 7)) :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (physicalRewireOrbit rewire) (1 : ℚ))) =
      physicalDerivativeAxisSignedWeight rewire / 384 := by
  set_option maxRecDepth 100000 in
    change ourDerivativeAxisCoordinate [0, 2]
        (sectorFieldOrbitReynolds 7 2
          (Finsupp.single
            (Quotient.mk _ (physicalRewireLabeled rewire) : FieldSevenOrbitCarrier)
            (1 : ℚ))) = _
    exact ourDerivativeAxisCoordinate_reynolds_single
      (physicalRewireLabeled rewire) _ (by rfl)

/-- OUR derivative-axis coordinate on the Reynolds-averaged physical base is
its signed finite weight divided by the group order. -/
theorem physicalBase_derivativeAxisCoordinate :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single physicalBaseOrbit (1 : ℚ))) =
      physicalBaseDerivativeAxisSignedWeight / 384 := by
  set_option maxRecDepth 100000 in
    change ourDerivativeAxisCoordinate [0, 2]
        (sectorFieldOrbitReynolds 7 2
          (Finsupp.single
            (Quotient.mk _ physicalBaseLabeled : FieldSevenOrbitCarrier)
            (1 : ℚ))) = _
    exact ourDerivativeAxisCoordinate_reynolds_single
      physicalBaseLabeled _ (by rfl)

/-- OUR original plane-pair coordinate on a Reynolds-averaged physical trace
rewire is its signed finite weight divided by the group order. -/
theorem physicalRewire_IBPAxisPlanePairCoordinate
    (rewire : Equiv.Perm (Fin 7)) :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (physicalRewireOrbit rewire) (1 : ℚ))) =
      physicalIBPAxisPlanePairSignedWeight rewire / 384 := by
  set_option maxRecDepth 100000 in
    change ourIBPAxisPlanePairCoordinate
        (sectorFieldOrbitReynolds 7 2
          (Finsupp.single
            (Quotient.mk _ (physicalRewireLabeled rewire) : FieldSevenOrbitCarrier)
            (1 : ℚ))) = _
    exact ourIBPAxisPlanePairCoordinate_reynolds_single
      (physicalRewireLabeled rewire) _ (by rfl)

/-- OUR original plane-pair coordinate on the Reynolds-averaged physical
base is its signed finite weight divided by the group order. -/
theorem physicalBase_IBPAxisPlanePairCoordinate :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single physicalBaseOrbit (1 : ℚ))) =
      physicalBaseIBPAxisPlanePairSignedWeight / 384 := by
  set_option maxRecDepth 100000 in
    change ourIBPAxisPlanePairCoordinate
        (sectorFieldOrbitReynolds 7 2
          (Finsupp.single
            (Quotient.mk _ physicalBaseLabeled : FieldSevenOrbitCarrier)
            (1 : ℚ))) = _
    exact ourIBPAxisPlanePairCoordinate_reynolds_single
      physicalBaseLabeled _ (by rfl)

/-- OUR third plane-pair coordinate on a Reynolds-averaged physical trace
rewire is its signed finite weight divided by the group order. -/
theorem physicalRewire_thirdIBPAxisPlanePairCoordinate
    (rewire : Equiv.Perm (Fin 7)) :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (physicalRewireOrbit rewire) (1 : ℚ))) =
      physicalThirdIBPAxisPlanePairSignedWeight rewire / 384 := by
  set_option maxRecDepth 100000 in
    change ourThirdIBPAxisPlanePairCoordinate
        (sectorFieldOrbitReynolds 7 2
          (Finsupp.single
            (Quotient.mk _ (physicalRewireLabeled rewire) : FieldSevenOrbitCarrier)
            (1 : ℚ))) = _
    exact ourThirdIBPAxisPlanePairCoordinate_reynolds_single
      (physicalRewireLabeled rewire) _ (by rfl)

/-- OUR third plane-pair coordinate on the Reynolds-averaged physical base
is its signed finite weight divided by the group order. -/
theorem physicalBase_thirdIBPAxisPlanePairCoordinate :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single physicalBaseOrbit (1 : ℚ))) =
      physicalBaseThirdIBPAxisPlanePairSignedWeight / 384 := by
  set_option maxRecDepth 100000 in
    change ourThirdIBPAxisPlanePairCoordinate
        (sectorFieldOrbitReynolds 7 2
          (Finsupp.single
            (Quotient.mk _ physicalBaseLabeled : FieldSevenOrbitCarrier)
            (1 : ℚ))) = _
    exact ourThirdIBPAxisPlanePairCoordinate_reynolds_single
      physicalBaseLabeled _ (by rfl)

/-- The raw derivative-axis coordinate of every actual physical
fundamental-trace row is its alternating signed weight divided by the
Reynolds group order. -/
theorem physicalFundamentalTrace_derivativeAxisCoordinate
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (exactFieldSevenProjection
          (orbitPhysicalRelationOperator policy
            (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1)))) =
      physicalFundamentalTraceDerivativeAxisWeight labels / 384 := by
  rw [physicalRowFieldSevenFormula]
  simp only [LinearMap.map_sub, LinearMap.map_add]
  rw [physicalBase_derivativeAxisCoordinate,
    physicalRewire_derivativeAxisCoordinate
      (Equiv.swap (ourFundamentalTraceSiteOf labels).first
        (ourFundamentalTraceSiteOf labels).second),
    physicalRewire_derivativeAxisCoordinate
      (Equiv.swap (ourFundamentalTraceSiteOf labels).first
        (ourFundamentalTraceSiteOf labels).third),
    physicalRewire_derivativeAxisCoordinate
      (Equiv.swap (ourFundamentalTraceSiteOf labels).second
        (ourFundamentalTraceSiteOf labels).third),
    physicalRewire_derivativeAxisCoordinate
      (fundamentalCycleForward (ourFundamentalTraceSiteOf labels)),
    physicalRewire_derivativeAxisCoordinate
      (fundamentalCycleBackward (ourFundamentalTraceSiteOf labels))]
  unfold physicalFundamentalTraceDerivativeAxisWeight
    physicalFundamentalTraceAlternatingWeight
  ring

/-- The raw original plane-pair coordinate of every actual physical
fundamental-trace row is its alternating signed weight divided by the
Reynolds group order. -/
theorem physicalFundamentalTrace_IBPAxisPlanePairCoordinate
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (exactFieldSevenProjection
          (orbitPhysicalRelationOperator policy
            (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1)))) =
      physicalFundamentalTraceIBPAxisPlanePairWeight labels / 384 := by
  rw [physicalRowFieldSevenFormula]
  simp only [LinearMap.map_sub, LinearMap.map_add]
  rw [physicalBase_IBPAxisPlanePairCoordinate,
    physicalRewire_IBPAxisPlanePairCoordinate
      (Equiv.swap (ourFundamentalTraceSiteOf labels).first
        (ourFundamentalTraceSiteOf labels).second),
    physicalRewire_IBPAxisPlanePairCoordinate
      (Equiv.swap (ourFundamentalTraceSiteOf labels).first
        (ourFundamentalTraceSiteOf labels).third),
    physicalRewire_IBPAxisPlanePairCoordinate
      (Equiv.swap (ourFundamentalTraceSiteOf labels).second
        (ourFundamentalTraceSiteOf labels).third),
    physicalRewire_IBPAxisPlanePairCoordinate
      (fundamentalCycleForward (ourFundamentalTraceSiteOf labels)),
    physicalRewire_IBPAxisPlanePairCoordinate
      (fundamentalCycleBackward (ourFundamentalTraceSiteOf labels))]
  unfold physicalFundamentalTraceIBPAxisPlanePairWeight
    physicalFundamentalTraceAlternatingWeight
  ring

/-- The raw third plane-pair coordinate of every actual physical
fundamental-trace row is its alternating signed weight divided by the
Reynolds group order. -/
theorem physicalFundamentalTrace_thirdIBPAxisPlanePairCoordinate
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (exactFieldSevenProjection
          (orbitPhysicalRelationOperator policy
            (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1)))) =
      physicalFundamentalTraceThirdIBPAxisPlanePairWeight labels / 384 := by
  rw [physicalRowFieldSevenFormula]
  simp only [LinearMap.map_sub, LinearMap.map_add]
  rw [physicalBase_thirdIBPAxisPlanePairCoordinate,
    physicalRewire_thirdIBPAxisPlanePairCoordinate
      (Equiv.swap (ourFundamentalTraceSiteOf labels).first
        (ourFundamentalTraceSiteOf labels).second),
    physicalRewire_thirdIBPAxisPlanePairCoordinate
      (Equiv.swap (ourFundamentalTraceSiteOf labels).first
        (ourFundamentalTraceSiteOf labels).third),
    physicalRewire_thirdIBPAxisPlanePairCoordinate
      (Equiv.swap (ourFundamentalTraceSiteOf labels).second
        (ourFundamentalTraceSiteOf labels).third),
    physicalRewire_thirdIBPAxisPlanePairCoordinate
      (fundamentalCycleForward (ourFundamentalTraceSiteOf labels)),
    physicalRewire_thirdIBPAxisPlanePairCoordinate
      (fundamentalCycleBackward (ourFundamentalTraceSiteOf labels))]
  unfold physicalFundamentalTraceThirdIBPAxisPlanePairWeight
    physicalFundamentalTraceAlternatingWeight
  ring

/-- The first scaled invariant coordinate vanishes on every actual certified
physical fundamental-trace row. -/
theorem ourInvariantSevenAxisCoordinate_physicalFundamentalTrace_zero
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    ourInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1)) = 0 := by
  unfold ourInvariantSevenAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    physicalFundamentalTrace_derivativeAxisCoordinate,
    physicalFundamentalTraceDerivativeAxisWeight_all_zero]
  norm_num

/-- The second scaled invariant coordinate vanishes on every actual certified
physical fundamental-trace row. -/
theorem ourInvariantIBPAxisCoordinate_physicalFundamentalTrace_zero
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    ourInvariantIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1)) = 0 := by
  unfold ourInvariantIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    physicalFundamentalTrace_IBPAxisPlanePairCoordinate,
    physicalFundamentalTraceIBPAxisPlanePairWeight_all_zero]
  norm_num

/-- The third scaled invariant coordinate vanishes on every actual certified
physical fundamental-trace row. -/
theorem ourInvariantThirdIBPAxisCoordinate_physicalFundamentalTrace_zero
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    ourInvariantThirdIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1)) = 0 := by
  unfold ourInvariantThirdIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    physicalFundamentalTrace_thirdIBPAxisPlanePairCoordinate,
    physicalFundamentalTraceThirdIBPAxisPlanePairWeight_all_zero]
  norm_num

/-- The canonical eight-field trace projection vanishes on every actual
certified physical fundamental-trace row, since each term remains seven-field. -/
theorem exactFieldEightTraceProjection_physicalFundamentalTrace_zero
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    exactFieldEightTraceProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1)) = 0 := by
  change exactFieldEightTraceClassMap
    (exactFieldEightProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1))) = 0
  rw [ourExactFieldEightProjection_fundamentalTraceGenerator_zero]
  exact map_zero _

/-- The separate three-coordinate correction annihilates every actual
certified physical fundamental-trace row under either relation policy. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_physicalFundamentalTrace_zero
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1)) = 0 := by
  unfold ourThreeCoordinateInvariantTraceOrderCorrection
    ourThirdInvariantTraceContribution
    ourTwoCoordinateInvariantTraceOrderCorrection
    ourTwoCoordinateInvariantSevenTraceCompensator
    ourTwoCoordinateInvariantSevenAxisCoordinate
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_physicalFundamentalTrace_zero,
    ourInvariantIBPAxisCoordinate_physicalFundamentalTrace_zero,
    exactFieldEightTraceProjection_physicalFundamentalTrace_zero,
    ourInvariantThirdIBPAxisCoordinate_physicalFundamentalTrace_zero]
  simp

/-- The coordinate-free joint semantic image of each certified physical
fundamental-trace label is in the kernel of OUR separate three-coordinate
correction. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_fundamentalTraceSingle_zero
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      ((ourFundamentalTraceToJointRelation policy
        (Finsupp.single labels 1)).1).1 = 0 := by
  rw [ourFundamentalTraceToJointRelation_single_val,
    ourThreeCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourThreeCoordinateInvariantTraceOrderCorrection_physicalFundamentalTrace_zero]

/-- The complete finite physical fundamental-trace cochain family maps into
the kernel of OUR separate three-coordinate correction. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_fundamentalTrace_zero
    (policy : PhysicalRelationPolicy)
    (cochain : OurFundamentalTraceCochainSpace) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      ((ourFundamentalTraceToJointRelation policy cochain).1).1 = 0 := by
  let combined := ourThreeCoordinateInvariantTraceOrderCorrection.comp
    (exactFieldOrbitInvariantSubmodule.subtype.comp
      ((jointInvariantRelationSubmodule policy).subtype.comp
        (ourFundamentalTraceToJointRelation policy)))
  set_option maxRecDepth 100000 in
    change combined cochain = 0
    induction cochain using Finsupp.induction_linear with
    | zero => simp [combined]
    | add left right hleft hright => simp [map_add, hleft, hright]
    | single labels coefficient =>
        rw [show Finsupp.single labels coefficient =
            coefficient • Finsupp.single labels 1 by simp]
        simp only [map_smul]
        change coefficient •
          (ourThreeCoordinateInvariantTraceOrderCorrection
            ((ourFundamentalTraceToJointRelation policy
              (Finsupp.single labels 1)).1).1) = 0
        rw [ourThreeCoordinateInvariantTraceOrderCorrection_fundamentalTraceSingle_zero]
        simp

/-- The full current cycle-profile correction annihilates the complete finite
physical fundamental-trace cochain family: its separate three-coordinate and
trace-cycle-profile contributions both vanish. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_fundamentalTrace_zero
    (policy : PhysicalRelationPolicy)
    (cochain : OurFundamentalTraceCochainSpace) :
    ourCycleProfileInvariantTraceOrderCorrection
      ((ourFundamentalTraceToJointRelation policy cochain).1).1 = 0 := by
  unfold ourCycleProfileInvariantTraceOrderCorrection
    ourTraceCycleProfileInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply]
  rw [ourThreeCoordinateInvariantTraceOrderCorrection_fundamentalTrace_zero,
    ourInvariantTraceCycleProfileCoordinate_fundamentalTrace_zero]
  simp

#print axioms physicalRewire_derivativeAxisSignedWeight
#print axioms physicalRewire_IBPAxisPlanePairSignedWeight
#print axioms physicalRewire_thirdIBPAxisPlanePairSignedWeight
#print axioms physicalFundamentalTraceDerivativeAxisWeight_all_zero
#print axioms physicalFundamentalTraceIBPAxisPlanePairWeight_all_zero
#print axioms physicalFundamentalTraceThirdIBPAxisPlanePairWeight_all_zero
#print axioms ourInvariantSevenAxisCoordinate_physicalFundamentalTrace_zero
#print axioms ourInvariantIBPAxisCoordinate_physicalFundamentalTrace_zero
#print axioms ourInvariantThirdIBPAxisCoordinate_physicalFundamentalTrace_zero
#print axioms exactFieldEightTraceProjection_physicalFundamentalTrace_zero
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_physicalFundamentalTrace_zero
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_fundamentalTraceSingle_zero
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_fundamentalTrace_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_fundamentalTrace_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalThreeCoordinate
