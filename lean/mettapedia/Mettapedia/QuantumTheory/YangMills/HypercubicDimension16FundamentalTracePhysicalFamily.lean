import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FDIBPCochainJointBridge

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
it does not yet prove that the cycle-profile correction annihilates every
member of this family, identify all other physical relation families, or
construct analytic noncommutative Wilson-functional coordinates.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalFamily

open HypercubicDimension16FundamentalTraceCycleProfile
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16SU2TraceRelations
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16JointQuotientInvariants
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

/-- OUR actual policy-indexed fundamental-trace generator attached to a
certified label triple. -/
def ourFundamentalTraceGeneratorAt
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    PhysicalRelationGenerator policy :=
  .fundamentalTrace ourFieldSevenCommutatorCarrier
    (ourFundamentalTraceSiteOf labels)

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
#print axioms ourFundamentalTraceGeneratorAt_injective
#print axioms ourFundamentalTraceCochainEmbedding_injective
#print axioms ourFundamentalTraceToJointRelation_single_val
#print axioms ourFundamentalTraceToJointRelation_signed_invariant
#print axioms ourFundamentalTraceToJointRelation_canonical_val

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalFamily
