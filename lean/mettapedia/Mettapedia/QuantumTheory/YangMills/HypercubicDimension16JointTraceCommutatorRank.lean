import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16JointTraceRankTransfer

/-!
# OUR trace--commutator extension of the joint invariant rank certificate

The field-eight trace quotient annihilates every member of OUR transferred
field-eight trace family.  It sends OUR Reynolds-averaged incoming commutator
relation to the nonzero literal incoming commutator class.  Thus the
commutator relation lies outside the span of the `11556` transferred trace
relations.  Adjoining it as one further span generator raises the certified
joint invariant relation-rank lower bound to `11557` for either
physical-relation policy.

This is a strict lower bound on the joint invariant relation rank.  It does
not determine the full joint rank, the quotient dimension, a complete
relation census, or a conditioning bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16JointTraceCommutatorRank

open scoped BigOperators

open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16PhysicalTraceQuotient
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceInvariantWitness
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16JointTraceRankTransfer

/-- OUR exact field-eight trace-quotient projection restricted to the genuine
joint invariant relation submodule. -/
def ourJointExactFieldEightTraceProjection
    (policy : PhysicalRelationPolicy) :
    jointInvariantRelationSubmodule policy →ₗ[ℚ]
      FieldEightPhysicalTraceQuotient :=
  exactFieldEightTraceProjection.comp
    (exactFieldOrbitInvariantSubmodule.subtype.comp
      (jointInvariantRelationSubmodule policy).subtype)

/-- A field-eight physical trace row has zero class in OUR exact trace
quotient. -/
theorem exactFieldEightTraceClassMap_fieldEightPhysicalTraceRow_zero
    (generator : FieldEightTraceGenerator) :
    exactFieldEightTraceClassMap (fieldEightPhysicalTraceRow generator) = 0 := by
  change (Submodule.mkQ fieldEightPhysicalTraceRelationSubmodule)
      (fieldEightCoinvariantTraceRow generator) = 0
  apply (Submodule.Quotient.mk_eq_zero
    fieldEightPhysicalTraceRelationSubmodule).mpr
  exact Submodule.subset_span ⟨generator, rfl⟩

/-- Exact trace classes commute with the field-eight Reynolds average on a
physical trace row. -/
theorem exactFieldEightTraceClassMap_fieldEightReynolds_traceRow_zero
    (generator : FieldEightTraceGenerator) :
    exactFieldEightTraceClassMap
      (sectorFieldOrbitReynolds 8 0
        (fieldEightPhysicalTraceRow generator)) = 0 := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  simp_rw [exactFieldEightTraceClassMap_signed_action]
  rw [exactFieldEightTraceClassMap_fieldEightPhysicalTraceRow_zero]
  simp

/-- OUR transferred invariant trace relation has zero exact trace quotient
class. -/
theorem ourJointExactFieldEightTraceProjection_traceRelation_zero
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourJointExactFieldEightTraceProjection policy
        (ourInvariantFieldEightTraceRelation policy generator) = 0 := by
  change exactFieldEightTraceClassMap
      (exactFieldEightProjection
        (exactFieldOrbitReynolds
          (orbitPhysicalRelationOperator policy
            (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)))) = 0
  rw [ourExactFieldEightProjection_exactFieldOrbitReynolds,
    ourOrbitPhysicalRelationOperator_lift,
    exactFieldEightProjection_fieldEightExactEmbed]
  exact exactFieldEightTraceClassMap_fieldEightReynolds_traceRow_zero generator

/-- OUR invariant incoming commutator relation maps to the literal nonzero
incoming commutator class. -/
theorem ourJointExactFieldEightTraceProjection_commutator
    (policy : PhysicalRelationPolicy) :
    ourJointExactFieldEightTraceProjection policy
        (ourInvariantCommutatorRelation policy) =
      literalIncomingCommutatorClass := by
  change exactFieldEightTraceProjection
      (exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1))) =
    literalIncomingCommutatorClass
  rw [exactFieldEightTraceProjection_exactFieldOrbitReynolds,
    exactFieldEightTraceProjection_ourCommutator]

/-- OUR invariant incoming commutator relation lies outside the span of the
transferred field-eight trace family. -/
theorem ourInvariantCommutator_not_mem_transferredTraceSpan
    (policy : PhysicalRelationPolicy) :
    ourInvariantCommutatorRelation policy ∉
      Submodule.span ℚ
        (Set.range fun index : Fin 11556 =>
          ourInvariantFieldEightTraceRelation policy
            (selectedPhysicalGenerator index)) := by
  intro hmem
  have hkernel :
      Submodule.span ℚ
        (Set.range fun index : Fin 11556 =>
          ourInvariantFieldEightTraceRelation policy
            (selectedPhysicalGenerator index)) ≤
        LinearMap.ker (ourJointExactFieldEightTraceProjection policy) := by
    apply Submodule.span_le.mpr
    rintro value ⟨index, rfl⟩
    exact LinearMap.mem_ker.mpr
      (ourJointExactFieldEightTraceProjection_traceRelation_zero
        policy (selectedPhysicalGenerator index))
  have hzero : ourJointExactFieldEightTraceProjection policy
      (ourInvariantCommutatorRelation policy) = 0 :=
    LinearMap.mem_ker.mp (hkernel hmem)
  rw [ourJointExactFieldEightTraceProjection_commutator] at hzero
  exact literalIncomingCommutatorClass_ne_zero hzero

/-- The genuine joint invariant relation submodule has rational rank at
least `11557`, for either physical-relation policy. -/
theorem jointInvariantRelationSubmodule_rank_lower_bound_trace_commutator
    (policy : PhysicalRelationPolicy) :
    11557 ≤ Module.finrank ℚ (jointInvariantRelationSubmodule policy) := by
  let traceSpan : Submodule ℚ (jointInvariantRelationSubmodule policy) :=
    Submodule.span ℚ
      (Set.range fun index : Fin 11556 =>
        ourInvariantFieldEightTraceRelation policy
          (selectedPhysicalGenerator index))
  have htraceRank : Module.finrank ℚ traceSpan = 11556 := by
    dsimp [traceSpan]
    rw [finrank_span_eq_card
      (ourInvariantFieldEightTraceRelations_linearIndependent policy)]
    simp
  have hnotmem : ourInvariantCommutatorRelation policy ∉ traceSpan := by
    dsimp [traceSpan]
    exact ourInvariantCommutator_not_mem_transferredTraceSpan policy
  have haugmentedRank :
      Module.finrank ℚ
        (traceSpan ⊔
          Submodule.span ℚ {ourInvariantCommutatorRelation policy} :
          Submodule ℚ (jointInvariantRelationSubmodule policy)) = 11557 := by
    rw [Submodule.finrank_sup_span_singleton (p := traceSpan)
      (v := ourInvariantCommutatorRelation policy) hnotmem, htraceRank]
  calc
    11557 = Module.finrank ℚ
        (traceSpan ⊔
          Submodule.span ℚ {ourInvariantCommutatorRelation policy} :
          Submodule ℚ (jointInvariantRelationSubmodule policy)) :=
      haugmentedRank.symm
    _ ≤ Module.finrank ℚ (jointInvariantRelationSubmodule policy) :=
      Submodule.finrank_le _

#print axioms exactFieldEightTraceClassMap_fieldEightPhysicalTraceRow_zero
#print axioms ourJointExactFieldEightTraceProjection_traceRelation_zero
#print axioms ourJointExactFieldEightTraceProjection_commutator
#print axioms ourInvariantCommutator_not_mem_transferredTraceSpan
#print axioms jointInvariantRelationSubmodule_rank_lower_bound_trace_commutator

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16JointTraceCommutatorRank
