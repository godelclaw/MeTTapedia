import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FDIBPCochainJointBridge
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CovariantCompressionWall
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantBianchi

/-!
# OUR physical family of all certified seven-field fundamental trace sites

The complete finite trace-cycle certificate is indexed by the `210` ordered
triples of distinct labels on the fixed seven-field carrier.  This module
identifies each such triple with an actual `FundamentalTraceSite` and hence
with an actual policy-indexed physical relation generator.  Its finite free
cochain module is embedded into OUR `F,D`/IBP cochain space and then mapped
by the existing signed-`H(4)` Reynolds semantics into the coordinate-free
joint relation submodule.

Thus the finite topology labels no longer stand apart from the physical
relation syntax.  This establishes the source-side semantic identification;
the exact field-eight projection of every one of these physical rows is also
proved zero.  It does not yet prove that the cycle-profile correction
annihilates every member's remaining seven-field component, identify all other
physical relation families, or construct analytic noncommutative
Wilson-functional coordinates.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalFamily

open HypercubicDimension16FundamentalTraceCycleProfile
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16SU2TraceRelations
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16CovariantCompressionWall
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16WilsonTraceOrderInvariantBianchi
open HypercubicDimension16FDIBPCochainJointBridge
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
open V14HypercubicFDCensus

/-- OUR finite index type of certified ordered three-cut labels. -/
abbrev OurCertifiedThreeCutLabel :=
  { labels : OurThreeCutLabels // labels ∈ ourDistinctThreeCutLabels }

/-- Each certified triple determines an actual fundamental trace site on the
fixed seven-field physical carrier. -/
def ourFundamentalTraceSiteOf
    (labels : OurCertifiedThreeCutLabel) :
    FundamentalTraceSite ourFieldSevenCommutatorCarrier where
  label := ⟨![labels.1.1, labels.1.2.1, labels.1.2.2], by
    have hdistinct : labels.1.1 ≠ labels.1.2.1 ∧
        labels.1.1 ≠ labels.1.2.2 ∧ labels.1.2.1 ≠ labels.1.2.2 :=
      (ourDistinctThreeCutLabels_mem_iff labels.1).mp labels.2
    intro left right hleft
    fin_cases left <;> fin_cases right <;> simp_all⟩

/-- Distinct certified triples determine distinct actual fundamental trace
sites, so the finite family has no source-coordinate collisions. -/
theorem ourFundamentalTraceSiteOf_injective :
    Function.Injective ourFundamentalTraceSiteOf := by
  intro left right h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun site => site.label 0) h
  apply Prod.ext
  · exact congrArg (fun site => site.label 1) h
  · exact congrArg (fun site => site.label 2) h

/-- The six trace-cycle types of an actual physical fundamental-trace site. -/
def ourActualFundamentalTraceCycleSignature
    (labels : OurCertifiedThreeCutLabel) : List (Multiset ℕ) :=
  let site := ourFundamentalTraceSiteOf labels
  [ Equiv.Perm.cycleType ourFieldSevenCommutatorCarrier.2.trace.traceOrder
  , Equiv.Perm.cycleType
      (rewireTraceCarrier ourFieldSevenCommutatorCarrier
        (Equiv.swap site.first site.second)).2.trace.traceOrder
  , Equiv.Perm.cycleType
      (rewireTraceCarrier ourFieldSevenCommutatorCarrier
        (Equiv.swap site.first site.third)).2.trace.traceOrder
  , Equiv.Perm.cycleType
      (rewireTraceCarrier ourFieldSevenCommutatorCarrier
        (Equiv.swap site.second site.third)).2.trace.traceOrder
  , Equiv.Perm.cycleType
      (rewireTraceCarrier ourFieldSevenCommutatorCarrier
        (fundamentalCycleForward site)).2.trace.traceOrder
  , Equiv.Perm.cycleType
      (rewireTraceCarrier ourFieldSevenCommutatorCarrier
        (fundamentalCycleBackward site)).2.trace.traceOrder ]

/-- The actual six-row trace topology is exactly the topology already
enumerated by OUR finite cycle-profile certificate. -/
theorem ourActualFundamentalTraceCycleSignature_eq_profile
    (labels : OurCertifiedThreeCutLabel) :
    ourActualFundamentalTraceCycleSignature labels =
      ourFundamentalThreeCutCycleSignature labels.1 := by
  rfl

/-- The integer cycle-profile numerator computed from the actual six physical
trace rewires. -/
def ourActualFundamentalTraceCycleProfileNumerator
    (labels : OurCertifiedThreeCutLabel) : Int :=
  let signature := ourActualFundamentalTraceCycleSignature labels
  12 * ourFundamentalThreeCutCycleGateSum 2 signature +
    13 * ourFundamentalThreeCutCycleGateSum 3 signature -
      10 * ourFundamentalThreeCutCycleGateSum 4 signature -
        7 * ourFundamentalThreeCutCycleGateSum 5 signature -
          6 * ourFundamentalThreeCutCycleGateSum 6 signature

/-- Rational form of the actual physical six-rewire cycle profile. -/
def ourActualFundamentalTraceCycleProfileValue
    (labels : OurCertifiedThreeCutLabel) : ℚ :=
  (ourActualFundamentalTraceCycleProfileNumerator labels : ℚ) / 10

theorem ourActualFundamentalTraceCycleProfileValue_eq_profile
    (labels : OurCertifiedThreeCutLabel) :
    ourActualFundamentalTraceCycleProfileValue labels =
      ourFundamentalThreeCutCycleProfileValue labels.1 := by
  rfl

/-- The forced profile vanishes on the actual six-rewire trace topology of
every certified physical fundamental-trace site. -/
theorem ourActualFundamentalTraceCycleProfileValue_zero
    (labels : OurCertifiedThreeCutLabel) :
    ourActualFundamentalTraceCycleProfileValue labels = 0 := by
  rw [ourActualFundamentalTraceCycleProfileValue_eq_profile]
  exact ourFundamentalThreeCutCycleProfileValue_zero labels.1 labels.2

/-- OUR actual policy-indexed fundamental-trace generator attached to a
certified label triple. -/
def ourFundamentalTraceGeneratorAt
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    PhysicalRelationGenerator policy :=
  .fundamentalTrace ourFieldSevenCommutatorCarrier
    (ourFundamentalTraceSiteOf labels)

/-- Every trace rewire of OUR fixed seven-field source has zero exact
eight-field component after contextual normalization and field relabeling. -/
theorem ourExactFieldEightProjection_normalizedRewire_zero
    (rewire : Equiv.Perm (Fin 7)) :
    exactFieldEightProjection
      (normalizeExactFieldRelabel
        (normalizeExactContextualBasis
          (rewireTraceCarrier ourFieldSevenCommutatorCarrier rewire))) = 0 := by
  rw [normalizeExactContextualBasis_fieldRelabel]
  exact exactFieldEightProjection_sevenTarget_single _ _

/-- The unrewired member of OUR fixed seven-field source also has zero exact
eight-field component after the same normalization. -/
theorem ourExactFieldEightProjection_normalizedBase_zero :
    exactFieldEightProjection
      (normalizeExactFieldRelabel
        (normalizeExactContextualBasis ourFieldSevenCommutatorCarrier)) = 0 := by
  rw [normalizeExactContextualBasis_fieldRelabel]
  exact exactFieldEightProjection_sevenTarget_single _ _

/-- Every actual certified fundamental-trace generator has zero exact
eight-field component.  This is a field-sector transport theorem for the
complete physical three-cut family; it does not assert that the remaining
seven-field quotient coordinates vanish. -/
theorem ourExactFieldEightProjection_fundamentalTraceGenerator_zero
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    exactFieldEightProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1)) = 0 := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp only [one_smul, ourFundamentalTraceGeneratorAt, physicalRelationRow,
    fundamentalTraceRow, map_sub, map_add]
  rw [normalizeExactContextual_single, normalizeExactContextual_single,
    normalizeExactContextual_single, normalizeExactContextual_single,
    normalizeExactContextual_single, normalizeExactContextual_single]
  simp only [one_smul]
  rw [ourExactFieldEightProjection_normalizedBase_zero,
    ourExactFieldEightProjection_normalizedRewire_zero
      (Equiv.swap (ourFundamentalTraceSiteOf labels).first
        (ourFundamentalTraceSiteOf labels).second),
    ourExactFieldEightProjection_normalizedRewire_zero
      (Equiv.swap (ourFundamentalTraceSiteOf labels).first
        (ourFundamentalTraceSiteOf labels).third),
    ourExactFieldEightProjection_normalizedRewire_zero
      (Equiv.swap (ourFundamentalTraceSiteOf labels).second
        (ourFundamentalTraceSiteOf labels).third),
    ourExactFieldEightProjection_normalizedRewire_zero
      (fundamentalCycleForward (ourFundamentalTraceSiteOf labels)),
    ourExactFieldEightProjection_normalizedRewire_zero
      (fundamentalCycleBackward (ourFundamentalTraceSiteOf labels))]
  norm_num

/-- The actual generator constructor preserves the distinction between
certified three-cut labels. -/
theorem ourFundamentalTraceGeneratorAt_injective
    (policy : PhysicalRelationPolicy) :
    Function.Injective (ourFundamentalTraceGeneratorAt policy) := by
  intro left right h
  apply ourFundamentalTraceSiteOf_injective
  injection h

/-- OUR free finite cochain module on the complete certified three-cut family. -/
abbrev OurFundamentalTraceCochainSpace :=
  OurCertifiedThreeCutLabel →₀ ℚ

/-- The finite label cochains embed into the actual policy-indexed `F,D`/IBP
cochain source by their physical fundamental-trace generators. -/
def ourFundamentalTraceCochainEmbedding
    (policy : PhysicalRelationPolicy) :
    OurFundamentalTraceCochainSpace →ₗ[ℚ] OurFDIBPCochainSpace policy :=
  Finsupp.lmapDomain ℚ ℚ (ourFundamentalTraceGeneratorAt policy)

/-- OUR finite source-to-cochain map is injective: no two certified physical
fundamental-trace coordinates are merged. -/
theorem ourFundamentalTraceCochainEmbedding_injective
    (policy : PhysicalRelationPolicy) :
    Function.Injective (ourFundamentalTraceCochainEmbedding policy) := by
  intro left right h
  change Finsupp.mapDomain (ourFundamentalTraceGeneratorAt policy) left =
    Finsupp.mapDomain (ourFundamentalTraceGeneratorAt policy) right at h
  exact Finsupp.mapDomain_injective
    (ourFundamentalTraceGeneratorAt_injective policy) h

/-- OUR physical finite-family semantics into the honest coordinate-free
joint relation submodule. -/
def ourFundamentalTraceToJointRelation
    (policy : PhysicalRelationPolicy) :
    OurFundamentalTraceCochainSpace →ₗ[ℚ]
      jointInvariantRelationSubmodule policy :=
  (ourFDIBPCochainToJointRelation policy).comp
    (ourFundamentalTraceCochainEmbedding policy)

@[simp] theorem ourFundamentalTraceCochainEmbedding_single
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel)
    (coefficient : ℚ) :
    ourFundamentalTraceCochainEmbedding policy
      (Finsupp.single labels coefficient) =
      Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) coefficient := by
  simp [ourFundamentalTraceCochainEmbedding]

/-- On each basis label, OUR finite family map is exactly the signed-Reynolds
average of its actual physical fundamental-trace row. -/
theorem ourFundamentalTraceToJointRelation_single_val
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    ((ourFundamentalTraceToJointRelation policy
      (Finsupp.single labels 1)).1).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1)) := by
  change ((ourFDIBPCochainToJointRelation policy
    (ourFundamentalTraceCochainEmbedding policy
      (Finsupp.single labels 1))).1).1 = _
  rw [ourFundamentalTraceCochainEmbedding_single]
  exact ourFDIBPCochainToJointRelation_val policy
    (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1)

/-- Every value of OUR finite family map is fixed by the signed hypercubic
action, because its target is the invariant joint relation submodule. -/
theorem ourFundamentalTraceToJointRelation_signed_invariant
    (policy : PhysicalRelationPolicy) (cochain : OurFundamentalTraceCochainSpace)
    (h : Hypercubic4) :
    signedExactFieldRelabelOrbitAction h
      ((ourFundamentalTraceToJointRelation policy cochain).1).1 =
      ((ourFundamentalTraceToJointRelation policy cochain).1).1 :=
  (ourFundamentalTraceToJointRelation policy cochain).1.2 h

/-- The canonical `(0,1,2)` three-cut placement is one member of OUR complete
certified physical family. -/
def ourCanonicalThreeCutLabel : OurCertifiedThreeCutLabel :=
  ⟨(0, 1, 2), by decide⟩

theorem ourFundamentalTraceSiteOf_canonical :
    ourFundamentalTraceSiteOf ourCanonicalThreeCutLabel =
      ourFieldSevenFundamentalTraceSite := by
  rfl

theorem ourFundamentalTraceGeneratorAt_canonical
    (policy : PhysicalRelationPolicy) :
    ourFundamentalTraceGeneratorAt policy ourCanonicalThreeCutLabel =
      ourFieldSevenFundamentalTraceGenerator policy := by
  rfl

/-- The complete-family semantics recovers the previously isolated canonical
fundamental three-cut invariant row. -/
theorem ourFundamentalTraceToJointRelation_canonical_val
    (policy : PhysicalRelationPolicy) :
    ((ourFundamentalTraceToJointRelation policy
      (Finsupp.single ourCanonicalThreeCutLabel 1)).1).1 =
      (ourInvariantFundamentalThreeCutRow policy).1 := by
  rw [ourFundamentalTraceToJointRelation_single_val,
    ourFundamentalTraceGeneratorAt_canonical]
  rfl

#print axioms ourFundamentalTraceSiteOf_injective
#print axioms ourActualFundamentalTraceCycleSignature_eq_profile
#print axioms ourActualFundamentalTraceCycleProfileValue_zero
#print axioms ourExactFieldEightProjection_normalizedRewire_zero
#print axioms ourExactFieldEightProjection_fundamentalTraceGenerator_zero
#print axioms ourFundamentalTraceGeneratorAt_injective
#print axioms ourFundamentalTraceCochainEmbedding_injective
#print axioms ourFundamentalTraceToJointRelation_single_val
#print axioms ourFundamentalTraceToJointRelation_signed_invariant
#print axioms ourFundamentalTraceToJointRelation_canonical_val

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalFamily
