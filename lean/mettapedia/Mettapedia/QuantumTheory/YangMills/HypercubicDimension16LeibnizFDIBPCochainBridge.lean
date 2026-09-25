import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LeibnizRelationOperator
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FDIBPCochainJointBridge

/-!
# OUR finite `F,D`/IBP cochain bridge to the corrected joint relation space

The cochain bridge of `HypercubicDimension16FDIBPCochainJointBridge` applies
the physical relation operator and then the signed-hypercubic Reynolds
average.  This module builds the same bridge with the Leibniz-corrected
operator.  It is equivariant, and its range is exactly the corrected joint
invariant relation submodule for each relation policy.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LeibnizFDIBPCochainBridge

open V14HypercubicFDCensus
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16FDIBPCochainJointBridge
open HypercubicDimension16LeibnizRelationOperator

/-- OUR corrected relation semantics followed by signed-hypercubic averaging. -/
def leibnizFDIBPCochainSemantics (policy : PhysicalRelationPolicy) :
    OurFDIBPCochainSpace policy →ₗ[ℚ] ExactFieldRelabelOrbitSpace :=
  exactFieldOrbitReynolds.comp (leibnizOrbitPhysicalRelationOperator policy)

/-- OUR corrected semantics with its invariant codomain exposed. -/
def leibnizFDIBPCochainToInvariant (policy : PhysicalRelationPolicy) :
    OurFDIBPCochainSpace policy →ₗ[ℚ] exactFieldOrbitInvariantSubmodule :=
  (leibnizFDIBPCochainSemantics policy).codRestrict exactFieldOrbitInvariantSubmodule (by
    intro cochain
    exact exactFieldOrbitReynolds_invariant
      (leibnizOrbitPhysicalRelationOperator policy cochain))

theorem leibnizFDIBPCochainSemantics_mem (policy : PhysicalRelationPolicy)
    (cochain : OurFDIBPCochainSpace policy) :
    leibnizFDIBPCochainSemantics policy cochain ∈
      leibnizOrbitPhysicalRelationSubmodule policy := by
  change exactFieldOrbitReynolds (leibnizOrbitPhysicalRelationOperator policy cochain) ∈
    leibnizOrbitPhysicalRelationSubmodule policy
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  apply (leibnizOrbitPhysicalRelationSubmodule policy).smul_mem
  apply Submodule.sum_mem
  intro h _
  apply leibnizOrbitPhysicalRelationSubmodule_signed_invariant policy h
  exact ⟨cochain, rfl⟩

/-- OUR semantic map into the corrected joint relation space. -/
def leibnizFDIBPCochainToJointRelation (policy : PhysicalRelationPolicy) :
    OurFDIBPCochainSpace policy →ₗ[ℚ] leibnizJointInvariantRelationSubmodule policy :=
  (leibnizFDIBPCochainToInvariant policy).codRestrict
    (leibnizJointInvariantRelationSubmodule policy) (by
      intro cochain
      rw [mem_leibnizJointInvariantRelationSubmodule_iff]
      change leibnizFDIBPCochainSemantics policy cochain ∈
        leibnizOrbitPhysicalRelationSubmodule policy
      exact leibnizFDIBPCochainSemantics_mem policy cochain)

theorem leibnizFDIBPCochainToJointRelation_equivariant (policy : PhysicalRelationPolicy)
    (h : Hypercubic4) (cochain : OurFDIBPCochainSpace policy) :
    leibnizFDIBPCochainToJointRelation policy
        (signedPhysicalRelationGeneratorAction policy h cochain) =
      leibnizFDIBPCochainToJointRelation policy cochain := by
  apply Subtype.ext
  apply Subtype.ext
  change exactFieldOrbitReynolds
      (leibnizOrbitPhysicalRelationOperator policy
        (signedPhysicalRelationGeneratorAction policy h cochain)) =
    exactFieldOrbitReynolds (leibnizOrbitPhysicalRelationOperator policy cochain)
  rw [leibnizOrbitPhysicalRelationOperator_equivariant]
  exact exactFieldOrbitReynolds_action h (leibnizOrbitPhysicalRelationOperator policy cochain)

/-- Every corrected invariant relation has a finite `F,D`/IBP cochain preimage
after Reynolds averaging. -/
theorem leibnizFDIBPCochainToJointRelation_surjective (policy : PhysicalRelationPolicy) :
    Function.Surjective (leibnizFDIBPCochainToJointRelation policy) := by
  intro target
  rcases (mem_leibnizJointInvariantRelationSubmodule_iff policy target.1).mp target.2
    with ⟨cochain, hcochain⟩
  refine ⟨cochain, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change exactFieldOrbitReynolds (leibnizOrbitPhysicalRelationOperator policy cochain) =
    target.1.1
  rw [hcochain]
  exact exactFieldOrbitReynolds_fixes_invariant target.1.1 target.1.2

theorem leibnizFDIBPCochainToJointRelation_range_eq_top (policy : PhysicalRelationPolicy) :
    LinearMap.range (leibnizFDIBPCochainToJointRelation policy) = ⊤ :=
  LinearMap.range_eq_top.mpr (leibnizFDIBPCochainToJointRelation_surjective policy)

/-- The shared off-shell cochains keep their averaged corrected semantics in
the on-shell policy. -/
theorem leibnizFDIBPCochainSemantics_liftOffShell
    (cochain : OurFDIBPCochainSpace .offShell) :
    leibnizFDIBPCochainSemantics .onShell (liftOffShellGeneratorSpace cochain) =
      leibnizFDIBPCochainSemantics .offShell cochain := by
  change exactFieldOrbitReynolds
      (leibnizOrbitPhysicalRelationOperator .onShell
        (liftOffShellGeneratorSpace cochain)) =
    exactFieldOrbitReynolds (leibnizOrbitPhysicalRelationOperator .offShell cochain)
  rw [leibnizOrbitPhysicalRelationOperator_liftOffShell]

#print axioms leibnizFDIBPCochainToJointRelation_equivariant
#print axioms leibnizFDIBPCochainToJointRelation_surjective
#print axioms leibnizFDIBPCochainSemantics_liftOffShell

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LeibnizFDIBPCochainBridge
