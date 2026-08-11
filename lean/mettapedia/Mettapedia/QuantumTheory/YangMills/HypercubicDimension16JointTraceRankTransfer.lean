import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldEightTracePhysicalLift
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceQuotient

/-!
# OUR transfer of the field-eight trace rank certificate

The derivative-free field-eight trace calculation certifies an independent
family of `11556` Reynolds-invariant trace rows.  The preceding physical lift
identifies every such row with a genuine full physical relation before exact
Reynolds averaging.  This module transports that family through the
coordinate-free invariant relation submodule and proves the same lower bound
there, for either physical-relation policy.

The result is a certified lower bound on the joint invariant relation rank.
It does not determine the full joint rank, the quotient dimension, a complete
relation census, or a conditioning bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16JointTraceRankTransfer

open scoped BigOperators

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16PhysicalTraceQuotient
open HypercubicDimension16PhysicalTraceWitnessSemantics
open HypercubicDimension16TraceRankTheorem
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceInvariantWitness
open HypercubicDimension16FieldEightTracePhysicalLift

/-- OUR restriction of the exact field-eight projection to the corresponding
signed invariant submodules. -/
def ourExactFieldEightInvariantProjection :
    exactFieldOrbitInvariantSubmodule →ₗ[ℚ]
      sectorFieldOrbitInvariantSubmodule 8 0 :=
  ((exactFieldEightProjection.comp exactFieldOrbitInvariantSubmodule.subtype).codRestrict
    (sectorFieldOrbitInvariantSubmodule 8 0) (by
      intro value h
      change signedSectorFieldOrbitAction h 8 0
          (exactFieldEightProjection value.1) =
        exactFieldEightProjection value.1
      rw [← exactFieldEightProjection_signed_action]
      exact congrArg exactFieldEightProjection (value.2 h)))

/-- OUR exact field-eight projection commutes with full-carrier Reynolds
averaging. -/
theorem ourExactFieldEightProjection_exactFieldOrbitReynolds
    (value : ExactFieldRelabelOrbitSpace) :
    exactFieldEightProjection (exactFieldOrbitReynolds value) =
      sectorFieldOrbitReynolds 8 0 (exactFieldEightProjection value) := by
  unfold exactFieldOrbitReynolds sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  simp_rw [exactFieldEightProjection_signed_action]

/-- OUR Reynolds-averaged full physical row associated to one field-eight
trace generator. -/
def ourInvariantFieldEightTraceRow
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    exactFieldOrbitInvariantSubmodule :=
  ⟨exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)),
    exactFieldOrbitReynolds_invariant _⟩

/-- OUR averaged lifted trace row belongs to the genuine coordinate-free
joint invariant relation submodule. -/
theorem ourInvariantFieldEightTraceRow_mem
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourInvariantFieldEightTraceRow policy generator ∈
      jointInvariantRelationSubmodule policy := by
  rw [mem_jointInvariantRelationSubmodule_iff]
  change exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)) ∈
      orbitPhysicalRelationSubmodule policy
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  apply (orbitPhysicalRelationSubmodule policy).smul_mem
  apply Submodule.sum_mem
  intro h _
  apply orbitPhysicalRelationSubmodule_signed_invariant policy h
  exact ⟨Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1, rfl⟩

/-- OUR typed invariant physical trace relation. -/
def ourInvariantFieldEightTraceRelation
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    jointInvariantRelationSubmodule policy :=
  ⟨ourInvariantFieldEightTraceRow policy generator,
    ourInvariantFieldEightTraceRow_mem policy generator⟩

/-- OUR field-eight invariant projection restricted to the genuine joint
invariant relation submodule. -/
def ourJointFieldEightInvariantProjection
    (policy : PhysicalRelationPolicy) :
    jointInvariantRelationSubmodule policy →ₗ[ℚ]
      sectorFieldOrbitInvariantSubmodule 8 0 :=
  ourExactFieldEightInvariantProjection.comp
    (jointInvariantRelationSubmodule policy).subtype

/-- OUR joint invariant trace relation maps to its certified field-eight
Reynolds row. -/
theorem ourJointFieldEightInvariantProjection_traceRelation
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourJointFieldEightInvariantProjection policy
        (ourInvariantFieldEightTraceRelation policy generator) =
      fieldEightReynoldsToInvariant (fieldEightPhysicalTraceRow generator) := by
  apply Subtype.ext
  change exactFieldEightProjection
      (exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1))) =
    sectorFieldOrbitReynolds 8 0 (fieldEightPhysicalTraceRow generator)
  rw [ourExactFieldEightProjection_exactFieldOrbitReynolds,
    ourOrbitPhysicalRelationOperator_lift,
    exactFieldEightProjection_fieldEightExactEmbed]

/-- The selected field-eight invariant trace rows are linearly independent. -/
theorem selectedPhysicalInvariantRows_linearIndependent :
    LinearIndependent ℚ
      (fun index : Fin 11556 =>
        fieldEightReynoldsToInvariant
          (fieldEightPhysicalTraceRow (selectedPhysicalGenerator index))) := by
  have hfamily :
      (fun index : Fin 11556 =>
        fieldEightReynoldsToInvariant
          (fieldEightPhysicalTraceRow (selectedPhysicalGenerator index))) =
        fun index : Fin 11556 =>
          rationalChartReynolds (selectedRawVector index) := by
    funext index
    exact selectedPhysicalGenerator_reynolds index
  rw [hfamily]
  exact rationalChartReynolds_selectedRawVector_linearIndependent

/-- OUR selected lifted trace relations are linearly independent in the
genuine joint invariant relation submodule. -/
theorem ourInvariantFieldEightTraceRelations_linearIndependent
    (policy : PhysicalRelationPolicy) :
    LinearIndependent ℚ
      (fun index : Fin 11556 =>
        ourInvariantFieldEightTraceRelation policy
          (selectedPhysicalGenerator index)) := by
  apply LinearIndependent.of_comp (ourJointFieldEightInvariantProjection policy)
  have hfamily :
      (ourJointFieldEightInvariantProjection policy) ∘
          (fun index : Fin 11556 =>
            ourInvariantFieldEightTraceRelation policy
              (selectedPhysicalGenerator index)) =
        fun index : Fin 11556 =>
          fieldEightReynoldsToInvariant
            (fieldEightPhysicalTraceRow (selectedPhysicalGenerator index)) := by
    funext index
    exact ourJointFieldEightInvariantProjection_traceRelation
      policy (selectedPhysicalGenerator index)
  rw [hfamily]
  exact selectedPhysicalInvariantRows_linearIndependent

/-- The genuine joint invariant relation submodule has rational rank at
least `11556`, for either physical-relation policy. -/
theorem jointInvariantRelationSubmodule_rank_lower_bound_trace
    (policy : PhysicalRelationPolicy) :
    11556 ≤ Module.finrank ℚ (jointInvariantRelationSubmodule policy) := by
  let selectedSpan : Submodule ℚ (jointInvariantRelationSubmodule policy) :=
    Submodule.span ℚ
      (Set.range fun index : Fin 11556 =>
        ourInvariantFieldEightTraceRelation policy
          (selectedPhysicalGenerator index))
  have hrank : Module.finrank ℚ selectedSpan = 11556 := by
    dsimp [selectedSpan]
    rw [finrank_span_eq_card
      (ourInvariantFieldEightTraceRelations_linearIndependent policy)]
    simp
  calc
    11556 = Module.finrank ℚ selectedSpan := hrank.symm
    _ ≤ Module.finrank ℚ (jointInvariantRelationSubmodule policy) :=
      Submodule.finrank_le _

#print axioms ourExactFieldEightProjection_exactFieldOrbitReynolds
#print axioms ourInvariantFieldEightTraceRow_mem
#print axioms ourJointFieldEightInvariantProjection_traceRelation
#print axioms selectedPhysicalInvariantRows_linearIndependent
#print axioms ourInvariantFieldEightTraceRelations_linearIndependent
#print axioms jointInvariantRelationSubmodule_rank_lower_bound_trace

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16JointTraceRankTransfer
