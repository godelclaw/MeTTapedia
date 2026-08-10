import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16JointPhysicalQuotient

/-!
# Invariants after the joint physical quotient

The coordinate-free joint scalar quotient was defined by first restricting
to signed hypercubic invariants and then quotienting by the invariant vectors
in the full physical relation range.  Over the rationals this order can be
reversed: quotient the complete field-orbit module by all physical relations,
then take the invariant subspace of the induced quotient action.

The equivalence is constructed explicitly.  Surjectivity uses the finite
Reynolds average of an arbitrary quotient representative and therefore does
not choose coordinates or materialize a Reynolds matrix.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16JointQuotientInvariants

open V14HypercubicFDCensus
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16JointPhysicalQuotient

abbrev CompletePhysicalQuotient (policy : PhysicalRelationPolicy) :=
  ExactFieldRelabelOrbitSpace ⧸ orbitPhysicalRelationSubmodule policy

theorem orbitPhysicalRelationSubmodule_le_comap_action
    (policy : PhysicalRelationPolicy) (h : Hypercubic4) :
    orbitPhysicalRelationSubmodule policy ≤
      (orbitPhysicalRelationSubmodule policy).comap
        (signedExactFieldRelabelOrbitAction h) := by
  intro value membership
  exact orbitPhysicalRelationSubmodule_signed_invariant
    policy h value membership

/-- Signed hypercubic action induced on the complete physical quotient. -/
def completePhysicalQuotientAction (policy : PhysicalRelationPolicy)
    (h : Hypercubic4) :
    CompletePhysicalQuotient policy →ₗ[ℚ]
      CompletePhysicalQuotient policy :=
  (orbitPhysicalRelationSubmodule policy).mapQ
    (orbitPhysicalRelationSubmodule policy)
    (signedExactFieldRelabelOrbitAction h)
    (orbitPhysicalRelationSubmodule_le_comap_action policy h)

@[simp] theorem completePhysicalQuotientAction_mk
    (policy : PhysicalRelationPolicy) (h : Hypercubic4)
    (value : ExactFieldRelabelOrbitSpace) :
    completePhysicalQuotientAction policy h
        ((orbitPhysicalRelationSubmodule policy).mkQ value) =
      (orbitPhysicalRelationSubmodule policy).mkQ
        (signedExactFieldRelabelOrbitAction h value) := by
  rfl

def completePhysicalQuotientInvariantSubmodule
    (policy : PhysicalRelationPolicy) :
    Submodule ℚ (CompletePhysicalQuotient policy) where
  carrier := {value |
    ∀ h, completePhysicalQuotientAction policy h value = value}
  zero_mem' := by
    intro h
    exact LinearMap.map_zero _
  add_mem' := by
    intro left right hleft hright h
    rw [LinearMap.map_add, hleft h, hright h]
  smul_mem' := by
    intro scalar value hvalue h
    rw [LinearMap.map_smul, hvalue h]

/-! ## Reynolds lift of invariant quotient classes -/

def exactFieldOrbitReynolds :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] ExactFieldRelabelOrbitSpace :=
  (1 / 384 : ℚ) •
    ∑ h : Hypercubic4, signedExactFieldRelabelOrbitAction h

theorem exactFieldOrbitReynolds_invariant
    (value : ExactFieldRelabelOrbitSpace) :
    exactFieldOrbitReynolds value ∈
      exactFieldOrbitInvariantSubmodule := by
  intro left
  have hsum :
      signedExactFieldRelabelOrbitAction left *
          (∑ h : Hypercubic4,
            signedExactFieldRelabelOrbitAction h) =
        ∑ h : Hypercubic4,
          signedExactFieldRelabelOrbitAction h := by
    rw [Finset.mul_sum]
    have hmul (h : Hypercubic4) :
        signedExactFieldRelabelOrbitAction left *
            signedExactFieldRelabelOrbitAction h =
          signedExactFieldRelabelOrbitAction (left * h) := by
      apply LinearMap.ext
      intro input
      exact (signedExactFieldRelabelOrbitAction_mul left h input).symm
    simp_rw [hmul]
    exact Equiv.sum_comp (Equiv.mulLeft left)
      signedExactFieldRelabelOrbitRepresentation
  change signedExactFieldRelabelOrbitAction left
      (exactFieldOrbitReynolds value) = exactFieldOrbitReynolds value
  unfold exactFieldOrbitReynolds
  change
    (signedExactFieldRelabelOrbitAction left *
        ((1 / 384 : ℚ) •
          ∑ h : Hypercubic4,
            signedExactFieldRelabelOrbitAction h)) value =
      (((1 / 384 : ℚ) •
        ∑ h : Hypercubic4,
          signedExactFieldRelabelOrbitAction h) value)
  rw [mul_smul_comm, hsum]

/-! ## Exact comparison map -/

def jointInvariantToQuotientInvariant
    (policy : PhysicalRelationPolicy) :
    exactFieldOrbitInvariantSubmodule →ₗ[ℚ]
      completePhysicalQuotientInvariantSubmodule policy :=
  ((orbitPhysicalRelationSubmodule policy).mkQ.comp
      exactFieldOrbitInvariantSubmodule.subtype).codRestrict
    (completePhysicalQuotientInvariantSubmodule policy) (by
      intro value h
      change completePhysicalQuotientAction policy h
          ((orbitPhysicalRelationSubmodule policy).mkQ value.1) =
        (orbitPhysicalRelationSubmodule policy).mkQ value.1
      rw [completePhysicalQuotientAction_mk, value.2 h])

theorem ker_jointInvariantToQuotientInvariant
    (policy : PhysicalRelationPolicy) :
    LinearMap.ker (jointInvariantToQuotientInvariant policy) =
      jointInvariantRelationSubmodule policy := by
  ext value
  constructor
  · intro membership
    have hzero := LinearMap.mem_ker.mp membership
    have hvalue := congrArg Subtype.val hzero
    change (orbitPhysicalRelationSubmodule policy).mkQ value.1 = 0 at hvalue
    change value.1 ∈ orbitPhysicalRelationSubmodule policy
    exact (Submodule.Quotient.mk_eq_zero
      (orbitPhysicalRelationSubmodule policy)).mp hvalue
  · intro membership
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change (orbitPhysicalRelationSubmodule policy).mkQ value.1 = 0
    exact (Submodule.Quotient.mk_eq_zero
      (orbitPhysicalRelationSubmodule policy)).mpr membership

theorem jointInvariantToQuotientInvariant_surjective
    (policy : PhysicalRelationPolicy) :
    Function.Surjective (jointInvariantToQuotientInvariant policy) := by
  intro target
  rcases (orbitPhysicalRelationSubmodule policy).mkQ_surjective target.1 with
    ⟨source, hsource⟩
  let averaged : exactFieldOrbitInvariantSubmodule :=
    ⟨exactFieldOrbitReynolds source,
      exactFieldOrbitReynolds_invariant source⟩
  refine ⟨averaged, Subtype.ext ?_⟩
  change (orbitPhysicalRelationSubmodule policy).mkQ
      (exactFieldOrbitReynolds source) = target.1
  have hterm (h : Hypercubic4) :
      (orbitPhysicalRelationSubmodule policy).mkQ
          (signedExactFieldRelabelOrbitAction h source) = target.1 := by
    calc
      (orbitPhysicalRelationSubmodule policy).mkQ
            (signedExactFieldRelabelOrbitAction h source) =
          completePhysicalQuotientAction policy h
            ((orbitPhysicalRelationSubmodule policy).mkQ source) :=
        (completePhysicalQuotientAction_mk policy h source).symm
      _ = completePhysicalQuotientAction policy h target.1 := by
        rw [hsource]
      _ = target.1 := target.2 h
  have hsum :
      (orbitPhysicalRelationSubmodule policy).mkQ
          (∑ h : Hypercubic4,
            signedExactFieldRelabelOrbitAction h source) =
        ∑ _h : Hypercubic4, target.1 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro h _
    exact hterm h
  unfold exactFieldOrbitReynolds
  change (orbitPhysicalRelationSubmodule policy).mkQ
      ((1 / 384 : ℚ) •
        ∑ h : Hypercubic4,
          signedExactFieldRelabelOrbitAction h source) = target.1
  rw [map_smul, hsum, Finset.sum_const, Finset.card_univ,
    Hypercubic4.card_hypercubic4]
  module

/-- Exactness of finite-group invariants over `ℚ`, specialized to our joint
physical relation range. -/
def jointScalarPhysicalQuotientEquivQuotientInvariants
    (policy : PhysicalRelationPolicy) :
    JointScalarPhysicalQuotient policy ≃ₗ[ℚ]
      completePhysicalQuotientInvariantSubmodule policy :=
  (Submodule.quotEquivOfEq (jointInvariantRelationSubmodule policy)
      (LinearMap.ker (jointInvariantToQuotientInvariant policy))
      (ker_jointInvariantToQuotientInvariant policy).symm).trans
    ((jointInvariantToQuotientInvariant policy).quotKerEquivOfSurjective
      (jointInvariantToQuotientInvariant_surjective policy))

theorem jointScalarPhysicalQuotient_finrank_eq_quotientInvariants
    (policy : PhysicalRelationPolicy) :
    Module.finrank ℚ (JointScalarPhysicalQuotient policy) =
      Module.finrank ℚ
        (completePhysicalQuotientInvariantSubmodule policy) :=
  LinearEquiv.finrank_eq
    (jointScalarPhysicalQuotientEquivQuotientInvariants policy)

#print axioms jointScalarPhysicalQuotientEquivQuotientInvariants
#print axioms jointScalarPhysicalQuotient_finrank_eq_quotientInvariants

end HypercubicDimension16JointQuotientInvariants
end YangMills
end QuantumTheory
end Mettapedia
