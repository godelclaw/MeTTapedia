import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalOrbitOperator

/-!
# The joint scalar physical quotient at dimension sixteen

The physical relation operator contains field antisymmetry, innermost
Bianchi, optional on-shell equations of motion, integrated total derivatives,
traceless one-letter traces, covariant-derivative commutators, and the two
standard `SU(2)` trace-rewiring families.  Its range is invariant under the
signed hypercubic action, but its commutator columns couple consecutive field
sectors.

This file defines the scalar invariant target before choosing coordinates or
a relation ordering.  The joint relation submodule is the canonical preimage
of the full physical relation range under the invariant-subspace inclusion.
Thus the quotient below is the coordinate-free cokernel whose rank and
conditioning a sparse certificate must decide; its definition does not
materialize a group average or a matrix.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16JointPhysicalQuotient

open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator

/-! ## The scalar invariant target -/

def exactFieldOrbitInvariantSubmodule :
    Submodule ℚ ExactFieldRelabelOrbitSpace where
  carrier := {value |
    ∀ h, signedExactFieldRelabelOrbitAction h value = value}
  zero_mem' := by
    intro h
    exact LinearMap.map_zero _
  add_mem' := by
    intro left right hleft hright h
    rw [LinearMap.map_add, hleft h, hright h]
  smul_mem' := by
    intro scalar value hvalue h
    rw [LinearMap.map_smul, hvalue h]

/-! ## The joint invariant relation range -/

def jointInvariantRelationSubmodule (policy : PhysicalRelationPolicy) :
    Submodule ℚ exactFieldOrbitInvariantSubmodule :=
  (orbitPhysicalRelationSubmodule policy).comap
    exactFieldOrbitInvariantSubmodule.subtype

/-- The joint relations are exactly the invariant vectors in the full
physical relation range. -/
theorem mem_jointInvariantRelationSubmodule_iff
    (policy : PhysicalRelationPolicy)
    (value : exactFieldOrbitInvariantSubmodule) :
    value ∈ jointInvariantRelationSubmodule policy ↔
      (value.1 : ExactFieldRelabelOrbitSpace) ∈
        orbitPhysicalRelationSubmodule policy := by
  rfl

/-! ## Off-shell and on-shell policy comparison -/

/-- Every off-shell generator is also an on-shell generator.  The impossible
off-shell EOM constructor has no case. -/
def liftOffShellGenerator :
    PhysicalRelationGenerator .offShell →
      PhysicalRelationGenerator .onShell
  | .antisymmetry carrier slot => .antisymmetry carrier slot
  | .bianchi carrier field position innermost =>
      .bianchi carrier field position innermost
  | .eom enabled _carrier _field _position _innermost => nomatch enabled
  | .integrationByParts carrier position outermost =>
      .integrationByParts carrier position outermost
  | .traceless carrier field singleton =>
      .traceless carrier field singleton
  | .covariantCommutator carrier site =>
      .covariantCommutator carrier site
  | .traceAnticommutator carrier site =>
      .traceAnticommutator carrier site
  | .fundamentalTrace carrier site =>
      .fundamentalTrace carrier site

theorem physicalRelationRow_liftOffShellGenerator
    (generator : PhysicalRelationGenerator .offShell) :
    physicalRelationRow (liftOffShellGenerator generator) =
      physicalRelationRow generator := by
  cases generator with
  | antisymmetry carrier slot => rfl
  | bianchi carrier field position innermost => rfl
  | eom enabled carrier field position innermost => cases enabled
  | integrationByParts carrier position outermost => rfl
  | traceless carrier field singleton => rfl
  | covariantCommutator carrier site => rfl
  | traceAnticommutator carrier site => rfl
  | fundamentalTrace carrier site => rfl

def liftOffShellGeneratorSpace :
    PhysicalRelationGeneratorSpace .offShell →ₗ[ℚ]
      PhysicalRelationGeneratorSpace .onShell :=
  Finsupp.lmapDomain ℚ ℚ liftOffShellGenerator

theorem orbitPhysicalRelationOperator_liftOffShell
    (value : PhysicalRelationGeneratorSpace .offShell) :
    orbitPhysicalRelationOperator .onShell
        (liftOffShellGeneratorSpace value) =
      orbitPhysicalRelationOperator .offShell value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [LinearMap.map_add, hleft, hright]
  | single generator coefficient =>
      simp [liftOffShellGeneratorSpace, orbitPhysicalRelationOperator,
        normalizedPhysicalRelationOperator,
        physicalRelationOperator_single,
        physicalRelationRow_liftOffShellGenerator]

theorem orbitPhysicalRelationSubmodule_offShell_le_onShell :
    orbitPhysicalRelationSubmodule .offShell ≤
      orbitPhysicalRelationSubmodule .onShell := by
  rintro value ⟨source, rfl⟩
  refine ⟨liftOffShellGeneratorSpace source, ?_⟩
  exact orbitPhysicalRelationOperator_liftOffShell source

theorem jointInvariantRelationSubmodule_offShell_le_onShell :
    jointInvariantRelationSubmodule .offShell ≤
      jointInvariantRelationSubmodule .onShell := by
  intro value membership
  rw [mem_jointInvariantRelationSubmodule_iff] at membership ⊢
  exact orbitPhysicalRelationSubmodule_offShell_le_onShell membership

/-! ## Coordinate-free joint quotient -/

abbrev JointScalarPhysicalQuotient (policy : PhysicalRelationPolicy) :=
  exactFieldOrbitInvariantSubmodule ⧸
    jointInvariantRelationSubmodule policy

theorem jointScalarPhysicalQuotient_finrank_formula
    (policy : PhysicalRelationPolicy) :
    Module.finrank ℚ (JointScalarPhysicalQuotient policy) =
      Module.finrank ℚ exactFieldOrbitInvariantSubmodule -
        Module.finrank ℚ (jointInvariantRelationSubmodule policy) := by
  rw [Submodule.finrank_quotient]

/-- Enabling equations of motion can only decrease the joint quotient
dimension. -/
theorem jointScalarPhysicalQuotient_onShell_finrank_le_offShell :
    Module.finrank ℚ (JointScalarPhysicalQuotient .onShell) ≤
      Module.finrank ℚ (JointScalarPhysicalQuotient .offShell) := by
  rw [jointScalarPhysicalQuotient_finrank_formula,
    jointScalarPhysicalQuotient_finrank_formula]
  have hrank := Submodule.finrank_mono
    jointInvariantRelationSubmodule_offShell_le_onShell
  have hoff := Submodule.finrank_le
    (jointInvariantRelationSubmodule .offShell)
  have hon := Submodule.finrank_le
    (jointInvariantRelationSubmodule .onShell)
  omega

end HypercubicDimension16JointPhysicalQuotient
end YangMills
end QuantumTheory
end Mettapedia
