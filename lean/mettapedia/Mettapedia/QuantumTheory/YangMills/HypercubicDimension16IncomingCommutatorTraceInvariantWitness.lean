import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16JointQuotientInvariants
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoupledQuotient

/-!
# OUR invariant physical commutator witness

The coordinate-free joint relation space is the invariant part of the full
physical relation range.  A raw physical column is not itself such an
invariant relation.  This module bridges that distinction for the concrete
covariant-commutator column: it proves that the exact field-eight projection
intertwines the signed hypercubic actions, hence that its trace class is
unchanged by the exact Reynolds average.

The Reynolds average of OUR physical commutator column is therefore an
explicit nonzero member of the genuine joint invariant relation submodule for
either relation policy.  Its singleton span has rational rank one, giving a
certified lower bound on that submodule's rank.

This is one semantic physical row, not a full joint-rank or conditioning
calculation, a complete relation census, or a claim about the final quotient
dimension.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceInvariantWitness

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceCertificate

/-- OUR dependent eight-field cast commutes with the hypercubic action. -/
theorem exactFieldEightOrbitCast_hypercubicAct
    (h : Hypercubic4) (fieldCount : Fin 9)
    (hfield : fieldCount = ourEightFieldCount)
    (orbit : FieldRelabelOrbitCarrier fieldCount.1
      (dimension16DerivativeCount fieldCount)) :
    exactFieldEightOrbitCast fieldCount hfield (orbit.hypercubicAct h) =
    (exactFieldEightOrbitCast fieldCount hfield orbit).hypercubicAct h := by
  subst fieldCount
  rfl

/-- OUR dependent eight-field cast preserves the hypercubic tensor sign. -/
theorem exactFieldEightOrbitCast_tensorSign
    (h : Hypercubic4) (fieldCount : Fin 9)
    (hfield : fieldCount = ourEightFieldCount)
    (orbit : FieldRelabelOrbitCarrier fieldCount.1
      (dimension16DerivativeCount fieldCount)) :
    (exactFieldEightOrbitCast fieldCount hfield orbit).tensorSign h =
      orbit.tensorSign h := by
  subst fieldCount
  rfl

/-- OUR exact eight-field projection intertwines the signed hypercubic
actions. -/
theorem exactFieldEightProjection_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    exactFieldEightProjection (signedExactFieldRelabelOrbitAction h value) =
      signedSectorFieldOrbitAction h 8 0 (exactFieldEightProjection value) := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp [hleft, hright]
  | single target coefficient =>
      rcases target with ⟨fieldCount, orbit⟩
      by_cases hfield : fieldCount = ourEightFieldCount
      · subst fieldCount
        simp [exactFieldEightProjection, exactFieldEightProjectionBasis,
          signedExactFieldRelabelOrbitAction_single,
          exactFieldRelabelOrbitAct,
          exactFieldRelabelOrbitTensorSign,
          signedSectorFieldOrbitAction_single,
          exactFieldEightOrbitCast_tensorSign,
          ourEightFieldCount]
        apply congrArg (fun target : FieldEightOrbitCarrier =>
          Finsupp.single target (coefficient * orbit.tensorSign h))
        exact exactFieldEightOrbitCast_hypercubicAct h _ rfl orbit
      · simp [exactFieldEightProjection, exactFieldEightProjectionBasis,
          signedExactFieldRelabelOrbitAction_single,
          exactFieldRelabelOrbitAct,
          exactFieldRelabelOrbitTensorSign,
          hfield]

/-- The difference of a field-eight vector and one signed action lies in the
ordinary signed-orbit relation submodule. -/
theorem value_sub_signedSectorFieldOrbitAction_mem
    (h : Hypercubic4) (value : FieldEightOrbitSpace) :
    value - signedSectorFieldOrbitAction h 8 0 value ∈
      fieldEightSignedOrbitRelationSubmodule := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      rw [LinearMap.map_add]
      convert fieldEightSignedOrbitRelationSubmodule.add_mem hleft hright using 1;
        module
  | single target coefficient =>
      have hbase : fieldEightSignedOrbitRow h target ∈
          fieldEightSignedOrbitRelationSubmodule :=
        Submodule.subset_span ⟨(h, target), rfl⟩
      have hscaled := fieldEightSignedOrbitRelationSubmodule.smul_mem
        coefficient hbase
      simpa [fieldEightSignedOrbitRow,
        signedSectorFieldOrbitAction_single, smul_sub] using hscaled

/-- The signed field-eight coinvariant class is unchanged by the signed
hypercubic action. -/
theorem fieldEightSignedCoinvariant_action
    (h : Hypercubic4) (value : FieldEightOrbitSpace) :
    (Submodule.mkQ fieldEightSignedOrbitRelationSubmodule)
      (signedSectorFieldOrbitAction h 8 0 value) =
    (Submodule.mkQ fieldEightSignedOrbitRelationSubmodule) value := by
  have hmem := value_sub_signedSectorFieldOrbitAction_mem h value
  have hzero : (Submodule.mkQ fieldEightSignedOrbitRelationSubmodule)
      (value - signedSectorFieldOrbitAction h 8 0 value) = 0 := by
    change Submodule.Quotient.mk
      (value - signedSectorFieldOrbitAction h 8 0 value) = 0
    exact (Submodule.Quotient.mk_eq_zero
      fieldEightSignedOrbitRelationSubmodule).mpr hmem
  rw [LinearMap.map_sub] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- OUR canonical eight-field trace-class map is invariant under the signed
hypercubic action. -/
theorem exactFieldEightTraceClassMap_signed_action
    (h : Hypercubic4) (value : FieldEightOrbitSpace) :
    exactFieldEightTraceClassMap
      (signedSectorFieldOrbitAction h 8 0 value) =
    exactFieldEightTraceClassMap value := by
  unfold exactFieldEightTraceClassMap
  change (Submodule.mkQ fieldEightPhysicalTraceRelationSubmodule)
      ((Submodule.mkQ fieldEightSignedOrbitRelationSubmodule)
        (signedSectorFieldOrbitAction h 8 0 value)) =
    (Submodule.mkQ fieldEightPhysicalTraceRelationSubmodule)
      ((Submodule.mkQ fieldEightSignedOrbitRelationSubmodule) value)
  rw [fieldEightSignedCoinvariant_action]

/-- OUR canonical full-carrier eight-field trace projection is invariant
under the signed hypercubic action. -/
theorem exactFieldEightTraceProjection_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    exactFieldEightTraceProjection
      (signedExactFieldRelabelOrbitAction h value) =
    exactFieldEightTraceProjection value := by
  unfold exactFieldEightTraceProjection
  change exactFieldEightTraceClassMap
      (exactFieldEightProjection (signedExactFieldRelabelOrbitAction h value)) =
    exactFieldEightTraceClassMap (exactFieldEightProjection value)
  rw [exactFieldEightProjection_signed_action,
    exactFieldEightTraceClassMap_signed_action]

/-- OUR canonical eight-field trace projection is unchanged by exact Reynolds
averaging of the full orbit carrier. -/
theorem exactFieldEightTraceProjection_exactFieldOrbitReynolds
    (value : ExactFieldRelabelOrbitSpace) :
    exactFieldEightTraceProjection (exactFieldOrbitReynolds value) =
      exactFieldEightTraceProjection value := by
  unfold exactFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum]
  simp_rw [exactFieldEightTraceProjection_signed_action]
  rw [Finset.sum_const, Finset.card_univ, Hypercubic4.card_hypercubic4]
  module

/-- OUR Reynolds-averaged physical commutator row in the exact invariant
carrier. -/
def ourInvariantCommutatorRow (policy : PhysicalRelationPolicy) :
    exactFieldOrbitInvariantSubmodule :=
  ⟨exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)),
    exactFieldOrbitReynolds_invariant _⟩

/-- OUR averaged physical commutator row belongs to the genuine
coordinate-free joint invariant relation submodule. -/
theorem ourInvariantCommutatorRow_mem
    (policy : PhysicalRelationPolicy) :
    ourInvariantCommutatorRow policy ∈
      jointInvariantRelationSubmodule policy := by
  rw [mem_jointInvariantRelationSubmodule_iff]
  change exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) ∈
      orbitPhysicalRelationSubmodule policy
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  apply (orbitPhysicalRelationSubmodule policy).smul_mem
  apply Submodule.sum_mem
  intro h _
  apply orbitPhysicalRelationSubmodule_signed_invariant policy h
  exact ⟨Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1, rfl⟩

/-- OUR averaged physical commutator row is nonzero, witnessed by its
surviving certified eight-field trace class. -/
theorem ourInvariantCommutatorRow_ne_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantCommutatorRow policy ≠ 0 := by
  intro hzero
  have hclass := congrArg
    (fun value : exactFieldOrbitInvariantSubmodule =>
      exactFieldEightTraceProjection value.1) hzero
  change exactFieldEightTraceProjection
      (exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1))) =
      exactFieldEightTraceProjection 0 at hclass
  rw [exactFieldEightTraceProjection_exactFieldOrbitReynolds,
    exactFieldEightTraceProjection_ourCommutator] at hclass
  simpa using literalIncomingCommutatorClass_ne_zero hclass

/-- OUR typed member of the coordinate-free joint invariant relation
submodule. -/
def ourInvariantCommutatorRelation
    (policy : PhysicalRelationPolicy) :
    jointInvariantRelationSubmodule policy :=
  ⟨ourInvariantCommutatorRow policy,
    ourInvariantCommutatorRow_mem policy⟩

/-- OUR typed invariant commutator relation is nonzero. -/
theorem ourInvariantCommutatorRelation_ne_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantCommutatorRelation policy ≠ 0 := by
  intro hzero
  apply ourInvariantCommutatorRow_ne_zero policy
  exact congrArg Subtype.val hzero

/-- The singleton span of OUR typed invariant commutator relation has exact
rational rank one. -/
theorem invariantCommutatorSingleton_finrank
    (policy : PhysicalRelationPolicy) :
    Module.finrank ℚ
      ((ℚ ∙ ourInvariantCommutatorRelation policy) :
        Submodule ℚ (jointInvariantRelationSubmodule policy)) = 1 := by
  exact @finrank_span_singleton ℚ
    (jointInvariantRelationSubmodule policy) _ _ _
    (ourInvariantCommutatorRelation policy)
    (ourInvariantCommutatorRelation_ne_zero policy)

/-- The genuine coordinate-free joint invariant relation submodule has
rational rank at least one, for either relation policy. -/
theorem jointInvariantRelationSubmodule_rank_lower_bound
    (policy : PhysicalRelationPolicy) :
    1 ≤ Module.finrank ℚ (jointInvariantRelationSubmodule policy) := by
  calc
    1 = Module.finrank ℚ
        ((ℚ ∙ ourInvariantCommutatorRelation policy) :
          Submodule ℚ (jointInvariantRelationSubmodule policy)) :=
      (invariantCommutatorSingleton_finrank policy).symm
    _ ≤ Module.finrank ℚ (jointInvariantRelationSubmodule policy) :=
      Submodule.finrank_le _

#print axioms exactFieldEightProjection_signed_action
#print axioms exactFieldEightTraceProjection_exactFieldOrbitReynolds
#print axioms ourInvariantCommutatorRow_mem
#print axioms ourInvariantCommutatorRow_ne_zero
#print axioms jointInvariantRelationSubmodule_rank_lower_bound

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceInvariantWitness
