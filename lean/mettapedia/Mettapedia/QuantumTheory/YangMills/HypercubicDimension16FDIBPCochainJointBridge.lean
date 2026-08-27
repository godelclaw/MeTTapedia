import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16JointQuotientInvariants

/-!
# OUR finite `F,D`/IBP cochain bridge to the joint relation space

The exact dimension-sixteen physical relation generator space is built on the
derivative-alpha-reduced `F,D` carrier.  Its generators include field
antisymmetry, Bianchi, the policy-indexed equation of motion, integration by
parts, tracelessness, covariant-commutator, and the two `SU(2)` trace families.
Thus it is a finite cochain realization of the relation side of the Wilson
lattice proof programme, rather than a census of a different ambient space.

This file constructs OUR semantic bridge from those cochains to the honest
coordinate-free joint relation submodule.  The bridge first applies the
physical relation operator and then its finite signed-hypercubic Reynolds
average.  Its range is exactly the joint relation submodule for each relation
policy.  Thus the finite source and coordinate-free target are compared by one
explicit semantics map. No coordinate ordering, dense Reynolds matrix, or
completeness claim for the full relation census is used.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16FDIBPCochainJointBridge

open V14HypercubicFDCensus
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16JointQuotientInvariants

/-- OUR finite `F,D`/IBP relation-cochain source at dimension sixteen. -/
abbrev OurFDIBPCochainSpace (policy : PhysicalRelationPolicy) :=
  PhysicalRelationGeneratorSpace policy

/-- OUR relation semantics followed by signed-hypercubic averaging. -/
def ourFDIBPCochainSemantics (policy : PhysicalRelationPolicy) :
    OurFDIBPCochainSpace policy →ₗ[ℚ] ExactFieldRelabelOrbitSpace :=
  exactFieldOrbitReynolds.comp (orbitPhysicalRelationOperator policy)

/-- OUR relation semantics with its canonical signed-hypercubic invariant
codomain exposed. -/
def ourFDIBPCochainToInvariant (policy : PhysicalRelationPolicy) :
    OurFDIBPCochainSpace policy →ₗ[ℚ]
      exactFieldOrbitInvariantSubmodule :=
  (ourFDIBPCochainSemantics policy).codRestrict
    exactFieldOrbitInvariantSubmodule (by
      intro cochain
      exact exactFieldOrbitReynolds_invariant
        (orbitPhysicalRelationOperator policy cochain))

theorem ourFDIBPCochainSemantics_mem_orbitPhysicalRelationSubmodule
    (policy : PhysicalRelationPolicy) (cochain : OurFDIBPCochainSpace policy) :
    ourFDIBPCochainSemantics policy cochain ∈
      orbitPhysicalRelationSubmodule policy := by
  change exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy cochain) ∈
        orbitPhysicalRelationSubmodule policy
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  apply (orbitPhysicalRelationSubmodule policy).smul_mem
  apply Submodule.sum_mem
  intro h _
  apply orbitPhysicalRelationSubmodule_signed_invariant policy h
  exact ⟨cochain, rfl⟩

/-- OUR semantic map into the honest coordinate-free joint relation space. -/
def ourFDIBPCochainToJointRelation (policy : PhysicalRelationPolicy) :
    OurFDIBPCochainSpace policy →ₗ[ℚ]
      jointInvariantRelationSubmodule policy :=
  (ourFDIBPCochainToInvariant policy).codRestrict
    (jointInvariantRelationSubmodule policy) (by
      intro cochain
      rw [mem_jointInvariantRelationSubmodule_iff]
      change ourFDIBPCochainSemantics policy cochain ∈
        orbitPhysicalRelationSubmodule policy
      exact ourFDIBPCochainSemantics_mem_orbitPhysicalRelationSubmodule policy cochain)

@[simp] theorem ourFDIBPCochainToJointRelation_val
    (policy : PhysicalRelationPolicy) (cochain : OurFDIBPCochainSpace policy) :
    (ourFDIBPCochainToJointRelation policy cochain).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy cochain) :=
  rfl

/-- The bridge is signed-`H(4)` equivariant, with the target already fixed
pointwise by the Reynolds projection. -/
theorem ourFDIBPCochainToJointRelation_equivariant
    (policy : PhysicalRelationPolicy) (h : Hypercubic4)
    (cochain : OurFDIBPCochainSpace policy) :
    ourFDIBPCochainToJointRelation policy
        (signedPhysicalRelationGeneratorAction policy h cochain) =
      ourFDIBPCochainToJointRelation policy cochain := by
  apply Subtype.ext
  apply Subtype.ext
  change exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy
        (signedPhysicalRelationGeneratorAction policy h cochain)) =
    exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy cochain)
  rw [orbitPhysicalRelationOperator_equivariant]
  exact exactFieldOrbitReynolds_action h
    (orbitPhysicalRelationOperator policy cochain)

/-- Every invariant physical relation has a finite `F,D`/IBP cochain
preimage after Reynolds averaging. -/
theorem ourFDIBPCochainToJointRelation_surjective
    (policy : PhysicalRelationPolicy) :
    Function.Surjective (ourFDIBPCochainToJointRelation policy) := by
  intro target
  rcases (mem_jointInvariantRelationSubmodule_iff policy target.1).mp target.2
    with ⟨cochain, hcochain⟩
  refine ⟨cochain, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy cochain) = target.1.1
  rw [hcochain]
  exact exactFieldOrbitReynolds_fixes_invariant target.1.1 target.1.2

/-- The bridge realizes the entire coordinate-free joint relation submodule,
not merely a selected family of its rows. -/
theorem ourFDIBPCochainToJointRelation_range_eq_top
    (policy : PhysicalRelationPolicy) :
    LinearMap.range (ourFDIBPCochainToJointRelation policy) = ⊤ :=
  LinearMap.range_eq_top.mpr
    (ourFDIBPCochainToJointRelation_surjective policy)

/-- The common off-shell relation generators retain exactly their averaged
semantics when regarded in the on-shell policy. -/
theorem ourFDIBPCochainSemantics_liftOffShell
    (cochain : OurFDIBPCochainSpace .offShell) :
    ourFDIBPCochainSemantics .onShell
        (liftOffShellGeneratorSpace cochain) =
      ourFDIBPCochainSemantics .offShell cochain := by
  change exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator .onShell
        (liftOffShellGeneratorSpace cochain)) =
    exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator .offShell cochain)
  rw [orbitPhysicalRelationOperator_liftOffShell]

/-- At the ambient invariant carrier, the two policy-indexed bridge values
agree on every shared off-shell cochain. -/
theorem ourFDIBPCochainToJointRelation_liftOffShell_val
    (cochain : OurFDIBPCochainSpace .offShell) :
    ((ourFDIBPCochainToJointRelation .onShell
      (liftOffShellGeneratorSpace cochain)).1).1 =
      ((ourFDIBPCochainToJointRelation .offShell cochain).1).1 := by
  change ourFDIBPCochainSemantics .onShell
      (liftOffShellGeneratorSpace cochain) =
    ourFDIBPCochainSemantics .offShell cochain
  exact ourFDIBPCochainSemantics_liftOffShell cochain

#print axioms ourFDIBPCochainToJointRelation_equivariant
#print axioms ourFDIBPCochainToJointRelation_surjective
#print axioms ourFDIBPCochainToJointRelation_range_eq_top
#print axioms ourFDIBPCochainToJointRelation_liftOffShell_val

end HypercubicDimension16FDIBPCochainJointBridge
end YangMills
end QuantumTheory
end Mettapedia
