import Mettapedia.QuantumTheory.YangMills.V14FDQuotientTransferNoGo
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# A postponed-IBP boundary complex for two exact Wilson blocks

This module gives a boundary-aware replacement for the incompatible local
integration-by-parts quotient isolated by `V14FDQuotientTransferNoGo`.
It is a new construction, not a construction stated in v14.

For an arbitrary finite operator census `Op`, degree zero consists of one
coefficient vector on each of two adjacent blocks.  Degree one is the current
on their shared boundary.  Its coboundary puts the current into the left block
with positive orientation and into the right block with negative orientation.
Thus internal descendants are retained locally and are quotiented only after
the two blocks are recombined.

The recovery theorem is exact: the cokernel of the shared-boundary map is
linearly equivalent to one global coefficient vector indexed by `Op`, and its
dimension is exactly `Fintype.card Op`.  Consequently this construction does
not change the census count once integration by parts is valid globally.  The
theorem is parametric because v14 gives only schematic counts, not a finite
type enumerating its claimed dimension-sixteen quotient.

The abstract complex is then evaluated on two copies of the actual `SU(2)`,
`b = 2` Wilson block.  The left field is the MOVE-5 witness.  A new right field
agrees with it on their shared boundary and has the opposite action-Laplacian
density.  Each block contribution is nonzero, while the assembled class is
zero in global degree-zero homology.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14BoundaryCochainComplex

open SU2WilsonBlockPilot
open SU2CanonicalTruncationObstruction
open V14FDQuotientTransferNoGo

/-! ## The parametric two-term boundary complex -/

/-- One global coefficient for every member of an explicit operator census. -/
abbrev CensusCoefficients (Op : Type*) := Op → ℝ

/-- Before recombination, each of the two blocks carries its own census
coefficient vector. -/
abbrev TwoBlockBulkCoefficients (Op : Type*) := Fin 2 → Op → ℝ

/-- The oriented coboundary of a current on the shared face. -/
def sharedBoundaryCoboundary {Op : Type*}
    (current : CensusCoefficients Op) : TwoBlockBulkCoefficients Op :=
  fun block op => if block = 0 then current op else -current op

/-- Linear form of the shared-boundary coboundary. -/
def sharedBoundaryCoboundaryLinear (Op : Type*) :
    CensusCoefficients Op →ₗ[ℝ] TwoBlockBulkCoefficients Op where
  toFun := sharedBoundaryCoboundary
  map_add' := by
    intro x y
    funext block op
    fin_cases block <;> simp [sharedBoundaryCoboundary] <;> ring
  map_smul' := by
    intro c x
    funext block op
    fin_cases block <;> simp [sharedBoundaryCoboundary]

/-- Global recombination adds the two oriented block contributions. -/
def globalRecombineLinear (Op : Type*) :
    TwoBlockBulkCoefficients Op →ₗ[ℝ] CensusCoefficients Op where
  toFun := fun bulk op => bulk 0 op + bulk 1 op
  map_add' := by
    intro x y
    funext op
    simp
    ring
  map_smul' := by
    intro c x
    funext op
    simp
    ring

@[simp] theorem globalRecombine_sharedBoundaryCoboundary
    {Op : Type*} (current : CensusCoefficients Op) :
    globalRecombineLinear Op (sharedBoundaryCoboundary current) = 0 := by
  funext op
  simp [globalRecombineLinear, sharedBoundaryCoboundary]

/-- Exactness at the two-block bulk term: a block coefficient vector has zero
global recombination exactly when it is an internal boundary coboundary. -/
theorem range_sharedBoundaryCoboundary_eq_ker_globalRecombine
    (Op : Type*) :
    LinearMap.range (sharedBoundaryCoboundaryLinear Op) =
      LinearMap.ker (globalRecombineLinear Op) := by
  ext bulk
  constructor
  · rintro ⟨current, rfl⟩
    exact LinearMap.mem_ker.mpr
      (globalRecombine_sharedBoundaryCoboundary current)
  · intro hbulk
    have hzero : globalRecombineLinear Op bulk = 0 :=
      LinearMap.mem_ker.mp hbulk
    refine ⟨bulk 0, ?_⟩
    funext block op
    have hop := congrFun hzero op
    fin_cases block
    · simp [sharedBoundaryCoboundaryLinear, sharedBoundaryCoboundary]
    · simp [globalRecombineLinear] at hop
      simp [sharedBoundaryCoboundaryLinear, sharedBoundaryCoboundary]
      linarith

/-- Degree-zero homology of the two-block boundary complex: local bulk
coefficients modulo currents crossing the shared face. -/
abbrev TwoBlockBoundaryH0 (Op : Type*) :=
  TwoBlockBulkCoefficients Op ⧸
    LinearMap.range (sharedBoundaryCoboundaryLinear Op)

/-- The cokernel is the quotient by the kernel of global recombination. -/
def twoBlockH0EquivGlobalRange (Op : Type*) :
    TwoBlockBoundaryH0 Op ≃ₗ[ℝ]
      LinearMap.range (globalRecombineLinear Op) :=
  (Submodule.quotEquivOfEq
      (LinearMap.range (sharedBoundaryCoboundaryLinear Op))
      (LinearMap.ker (globalRecombineLinear Op))
      (range_sharedBoundaryCoboundary_eq_ker_globalRecombine Op)) ≪≫ₗ
    (globalRecombineLinear Op).quotKerEquivRange

/-- Every global census vector is obtained by putting it on the left block
and zero on the right. -/
theorem globalRecombine_surjective (Op : Type*) :
    Function.Surjective (globalRecombineLinear Op) := by
  intro coefficients
  refine ⟨fun block op => if block = 0 then coefficients op else 0, ?_⟩
  funext op
  simp [globalRecombineLinear]

/-- **Census recovery.**  After global recombination, quotienting the shared
boundary descendants leaves exactly one copy of every explicit census
coordinate.  This is the finite-dimensional counting statement that local
postponement of IBP must satisfy. -/
theorem twoBlockBoundaryH0_finrank
    (Op : Type*) [Fintype Op] :
    Module.finrank ℝ (TwoBlockBoundaryH0 Op) = Fintype.card Op := by
  rw [(twoBlockH0EquivGlobalRange Op).finrank_eq]
  have hrange : LinearMap.range (globalRecombineLinear Op) = ⊤ :=
    LinearMap.range_eq_top.mpr (globalRecombine_surjective Op)
  rw [hrange, finrank_top, Module.finrank_pi]

/-- The five templates explicitly named in the existing v14 source audit
retain their five global coordinates.  This does not turn the manuscript's
schematic `≈ 950` count into an enumeration. -/
theorem displayedTemplateBoundaryH0_finrank :
    Module.finrank ℝ (TwoBlockBoundaryH0 V14ActionOperatorTemplate) = 5 := by
  rw [twoBlockBoundaryH0_finrank]
  decide

/-! ## Two actual, interface-compatible `SU(2)` block fields -/

/-- The central element `-I` of `SU(2)`. -/
def halfTurnMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-1, 0; 0, -1]

def halfTurn : SU2 :=
  ⟨halfTurnMatrix, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [halfTurnMatrix, Matrix.mul_apply]
    · simp [halfTurnMatrix, Matrix.det_fin_two]⟩

theorem halfTurn_trace_real :
    (Matrix.trace (halfTurn : Matrix (Fin 2) (Fin 2) ℂ)).re = -2 := by
  norm_num [halfTurn, halfTurnMatrix, Matrix.trace, Fin.sum_univ_two]

/-- The right block has Wilson-potential profile `(1,2,2)`.  Its interface
plaquette therefore matches the left block's final potential `1`. -/
def rightWitnessField : BlockLinkField := fun edge =>
  if edge = (ibpProfilePlaquette 0).firstLink then quarterTurn
  else if edge = (ibpProfilePlaquette 1).firstLink then halfTurn
  else if edge = (ibpProfilePlaquette 2).firstLink then halfTurn
  else 1

@[simp] theorem profileFirstLink_eq_iff (i j : Fin 3) :
    (ibpProfilePlaquette i).firstLink =
      (ibpProfilePlaquette j).firstLink ↔ i = j := by
  fin_cases i <;> fin_cases j <;> decide

@[simp] theorem profileSecondAfterFirst_ne_first
    (i j : Fin 3) :
    (ibpProfilePlaquette i).secondAfterFirst ≠
      (ibpProfilePlaquette j).firstLink := by
  fin_cases i <;> fin_cases j <;> decide

@[simp] theorem profileFirstAfterSecond_ne_first
    (i j : Fin 3) :
    (ibpProfilePlaquette i).firstAfterSecond ≠
      (ibpProfilePlaquette j).firstLink := by
  fin_cases i <;> fin_cases j <;> decide

@[simp] theorem profileSecondLink_ne_first
    (i j : Fin 3) :
    (ibpProfilePlaquette i).secondLink ≠
      (ibpProfilePlaquette j).firstLink := by
  fin_cases i <;> fin_cases j <;> decide

theorem rightWitnessHolonomy_zero :
    plaquetteHolonomy rightWitnessField (ibpProfilePlaquette 0) = quarterTurn := by
  simp [plaquetteHolonomy, rightWitnessField]

theorem rightWitnessHolonomy_one :
    plaquetteHolonomy rightWitnessField (ibpProfilePlaquette 1) = halfTurn := by
  simp [plaquetteHolonomy, rightWitnessField]

theorem rightWitnessHolonomy_two :
    plaquetteHolonomy rightWitnessField (ibpProfilePlaquette 2) = halfTurn := by
  simp [plaquetteHolonomy, rightWitnessField]

theorem rightWitnessPotential_zero :
    plaquettePotential rightWitnessField (ibpProfilePlaquette 0) = 1 := by
  rw [plaquettePotential, rightWitnessHolonomy_zero]
  norm_num [specialUnitaryWilsonPotential, quarterTurn_trace_real]

theorem rightWitnessPotential_one :
    plaquettePotential rightWitnessField (ibpProfilePlaquette 1) = 2 := by
  rw [plaquettePotential, rightWitnessHolonomy_one]
  norm_num [specialUnitaryWilsonPotential, halfTurn_trace_real]

theorem rightWitnessPotential_two :
    plaquettePotential rightWitnessField (ibpProfilePlaquette 2) = 2 := by
  rw [plaquettePotential, rightWitnessHolonomy_two]
  norm_num [specialUnitaryWilsonPotential, halfTurn_trace_real]

/-- The right block carries the opposite nonzero total-derivative density. -/
theorem actionLaplacianDensity_rightWitness :
    actionLaplacianDensity rightWitnessField = -1 := by
  norm_num [actionLaplacianDensity, actionProfile,
    rightWitnessPotential_zero, rightWitnessPotential_one,
    rightWitnessPotential_two]

/-! ### Exact gluing along the shared boundary -/

/-- Positive links lying in the right face of the left block. -/
abbrev RightInterfaceLink :=
  {edge : BlockLink // edge.origin 0 = (2 : BlockCoordinate)}

/-- Rebase a right-face link of the left block to the left face of the right
block.  Such a link cannot point in direction zero. -/
def rebaseInterfaceLink (edge : RightInterfaceLink) : BlockLink where
  origin := Function.update edge.1.origin 0 (0 : BlockCoordinate)
  direction := edge.1.direction
  canStep := by
    have hdirection : edge.1.direction ≠ 0 := by
      intro h
      have hstep := edge.1.canStep
      rw [h] at hstep
      simp [edge.2] at hstep
    simpa [Function.update, hdirection] using edge.1.canStep

theorem blockLink_ext
    {left right : BlockLink}
    (horigin : left.origin = right.origin)
    (hdirection : left.direction = right.direction) :
    left = right := by
  cases left
  cases right
  simp_all

theorem rebaseInterfaceLink_injective :
    Function.Injective rebaseInterfaceLink := by
  intro left right heq
  apply Subtype.ext
  apply blockLink_ext
  · funext axis
    by_cases haxis : axis = 0
    · subst axis
      simpa [left.2, right.2]
    · have horigin := congrArg BlockLink.origin heq
      have hcoordinate := congrFun horigin axis
      simpa [rebaseInterfaceLink, Function.update, haxis] using hcoordinate
  · simpa [rebaseInterfaceLink] using congrArg BlockLink.direction heq

def leftWitnessInterfaceLink : RightInterfaceLink :=
  ⟨(ibpProfilePlaquette 2).firstLink, by rfl⟩

theorem rebase_leftWitnessInterfaceLink :
    rebaseInterfaceLink leftWitnessInterfaceLink =
      (ibpProfilePlaquette 0).firstLink := by
  apply blockLink_ext
  · funext axis
    fin_cases axis <;>
      simp [rebaseInterfaceLink, leftWitnessInterfaceLink,
        ibpProfilePlaquette, ibpProfileOrigin, Function.update]
  · rfl

theorem rebaseInterfaceLink_ne_profile_one (edge : RightInterfaceLink) :
    rebaseInterfaceLink edge ≠ (ibpProfilePlaquette 1).firstLink := by
  intro heq
  have horigin := congrArg (fun link : BlockLink => link.origin 0) heq
  simp [rebaseInterfaceLink, ibpProfilePlaquette, ibpProfileOrigin,
    Function.update] at horigin

theorem rebaseInterfaceLink_ne_profile_two (edge : RightInterfaceLink) :
    rebaseInterfaceLink edge ≠ (ibpProfilePlaquette 2).firstLink := by
  intro heq
  have horigin := congrArg (fun link : BlockLink => link.origin 0) heq
  simp [rebaseInterfaceLink, ibpProfilePlaquette, ibpProfileOrigin,
    Function.update] at horigin

/-- The two actual block fields agree on every link of their shared face. -/
theorem witnessFields_interfaceCompatible (edge : RightInterfaceLink) :
    ibpWitnessField edge.1 = rightWitnessField (rebaseInterfaceLink edge) := by
  by_cases hedge : edge = leftWitnessInterfaceLink
  · subst edge
    rw [rebase_leftWitnessInterfaceLink]
    simp [ibpWitnessField, rightWitnessField, leftWitnessInterfaceLink]
  · have hleft : edge.1 ≠ (ibpProfilePlaquette 2).firstLink := by
      intro h
      apply hedge
      apply Subtype.ext
      exact h
    have hzero : rebaseInterfaceLink edge ≠
        (ibpProfilePlaquette 0).firstLink := by
      intro h
      have hrebase : rebaseInterfaceLink edge =
          rebaseInterfaceLink leftWitnessInterfaceLink := by
        simpa [rebase_leftWitnessInterfaceLink] using h
      exact hedge (rebaseInterfaceLink_injective hrebase)
    simp [ibpWitnessField, rightWitnessField, hleft, hzero,
      rebaseInterfaceLink_ne_profile_one,
      rebaseInterfaceLink_ne_profile_two]

/-- An exact two-block assembly records both actual Wilson fields and their
full shared-face compatibility. -/
structure ExactTwoBlockAssembly where
  left : BlockLinkField
  right : BlockLinkField
  interfaceCompatible : ∀ edge : RightInterfaceLink,
    left edge.1 = right (rebaseInterfaceLink edge)

def actionLaplacianTwoBlockAssembly : ExactTwoBlockAssembly where
  left := ibpWitnessField
  right := rightWitnessField
  interfaceCompatible := witnessFields_interfaceCompatible

/-! ## The MOVE-5 descendant cancels only after recombination -/

/-- The operator census needed for the acceptance witness has one coordinate,
the scalar descendant `∂² Tr(F²)`. -/
inductive ActionLaplacianCensus where
  | actionLaplacian
deriving DecidableEq, Fintype, Repr

def assembledActionLaplacianBulk :
    TwoBlockBulkCoefficients ActionLaplacianCensus :=
  fun block _ =>
    if block = 0 then
      actionLaplacianDensity actionLaplacianTwoBlockAssembly.left
    else
      actionLaplacianDensity actionLaplacianTwoBlockAssembly.right

def actionFluxAcrossSharedFace :
    CensusCoefficients ActionLaplacianCensus := fun _ => 1

/-- The two nonzero block values are exactly the oriented coboundary of the
unit shared-face current. -/
theorem assembledActionLaplacian_eq_boundaryCoboundary :
    assembledActionLaplacianBulk =
      sharedBoundaryCoboundary actionFluxAcrossSharedFace := by
  funext block op
  fin_cases block <;>
    simp [assembledActionLaplacianBulk,
      actionLaplacianTwoBlockAssembly, actionFluxAcrossSharedFace,
      sharedBoundaryCoboundary, actionLaplacianDensity_witness,
      actionLaplacianDensity_rightWitness]

theorem assembledActionLaplacian_left_nonzero :
    assembledActionLaplacianBulk 0 .actionLaplacian = 1 := by
  simp [assembledActionLaplacianBulk, actionLaplacianTwoBlockAssembly,
    actionLaplacianDensity_witness]

theorem assembledActionLaplacian_right_nonzero :
    assembledActionLaplacianBulk 1 .actionLaplacian = -1 := by
  simp [assembledActionLaplacianBulk, actionLaplacianTwoBlockAssembly,
    actionLaplacianDensity_rightWitness]

/-- **Postponed-IBP acceptance theorem.**  The MOVE-5 dimension-six
descendant is nonzero on each exact block, the two actual fields glue, and the
assembled descendant vanishes in global degree-zero homology. -/
theorem move5Witness_handled_by_postponedIBP :
    assembledActionLaplacianBulk 0 .actionLaplacian = 1 ∧
    assembledActionLaplacianBulk 1 .actionLaplacian = -1 ∧
    (LinearMap.range
        (sharedBoundaryCoboundaryLinear ActionLaplacianCensus)).mkQ
      assembledActionLaplacianBulk = 0 := by
  refine ⟨assembledActionLaplacian_left_nonzero,
    assembledActionLaplacian_right_nonzero, ?_⟩
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨actionFluxAcrossSharedFace, ?_⟩
  exact assembledActionLaplacian_eq_boundaryCoboundary.symm

end V14BoundaryCochainComplex
end YangMills
end QuantumTheory
end Mettapedia
