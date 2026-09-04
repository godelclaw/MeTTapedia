import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAxialFrameConstruction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeStrainSpectralFrame

/-!
# A pointwise axial frame constructed from the strain operator

This module joins the ordered spectral construction to the explicit axial
frame.  For a symmetric three-dimensional strain operator, the eigenvector
with the smallest ordered eigenvalue is converted to the algebraic
three-vector model and then sent to `e_z` by the two-reflection frame.

The construction is pointwise and requires no eigenbasis from the caller.  It
therefore suffices for the existing pointwise variable-frame kernel estimate,
which is uniform over all frames.  Measurability of this spectral selection,
needed only when the selected quantities themselves are integrated, is not
claimed here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeStrainAxialFrame

open scoped RealInnerProductSpace
open PancakeBilinearPeriodization
open PancakeRealCoherentPairEstimate
open PancakeSmoothCoherentSymbol
open PancakeFrameCovariance
open PancakeAnnularPhysicalFrameTransfer
open PancakeStrainSpectralFrame
open PancakeAxialFrameConstruction

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- Coordinate identification from mathlib's Euclidean three-space to the
algebraic nested-product model used by the pancake multiplier. -/
def realVec3OfEuclidean (v : R3) : RealVec3 :=
  (v 0, v 1, v 2)

theorem normSq_realVec3OfEuclidean (v : R3) :
    normSq (realVec3OfEuclidean v) = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [realVec3OfEuclidean, normSq, dot, pow_two]

/-- The smallest-eigenvalue direction in the ordered strain eigenframe. -/
def compressiveDirection
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    RealVec3 :=
  realVec3OfEuclidean ((orderedEigenframe S hSsymm).eigenbasis 2)

theorem normSq_compressiveDirection
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    normSq (compressiveDirection S hSsymm) = 1 := by
  rw [compressiveDirection, normSq_realVec3OfEuclidean,
    (orderedEigenframe S hSsymm).eigenbasis.norm_eq_one]
  norm_num

/-- An oriented Euclidean frame constructed directly from the symmetric
strain, with the most compressive eigenvector as its axial direction. -/
def compressiveAxialFrame
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    OrientedFrameEquiv :=
  axialFrameOfUnit (compressiveDirection S hSsymm)
    (normSq_compressiveDirection S hSsymm)

theorem compressiveAxialFrame_maps_direction_to_ez
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    (compressiveAxialFrame S hSsymm).toFun
        (compressiveDirection S hSsymm) = ez :=
  axialFrameOfUnit_toFun_self _ (normSq_compressiveDirection S hSsymm)

/-- The direction underlying the constructed axial frame is an exact
smallest-eigenvalue eigenvector of the strain operator. -/
theorem compressiveDirection_is_eigenvector
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    S ((orderedEigenframe S hSsymm).eigenbasis 2) =
      (orderedEigenframe S hSsymm).eigenvalue 2 •
        (orderedEigenframe S hSsymm).eigenbasis 2 :=
  (orderedEigenframe S hSsymm).apply_eigenbasis 2

/-- Pointwise axial frame field constructed from a pointwise symmetric strain
field. -/
def compressiveAxialFrameField {X : Type*}
    (S : X → R3 →L[ℝ] R3)
    (hSsymm : ∀ x u v, inner ℝ u (S x v) = inner ℝ (S x u) v) :
    X → OrientedFrameEquiv :=
  fun x ↦ compressiveAxialFrame (S x) (hSsymm x)

theorem compressiveAxialFrameField_maps_direction_to_ez {X : Type*}
    (S : X → R3 →L[ℝ] R3)
    (hSsymm : ∀ x u v, inner ℝ u (S x v) = inner ℝ (S x u) v)
    (x : X) :
    (compressiveAxialFrameField S hSsymm x).toFun
        (compressiveDirection (S x) (hSsymm x)) = ez :=
  compressiveAxialFrame_maps_direction_to_ez (S x) (hSsymm x)

/-- The full-annulus `C/N` endpoint specialized to the frame field built from
the actual pointwise symmetric strain.  No frame is supplied by the caller. -/
theorem exists_uniform_strainFrameAnnularSquareDyadic_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : BilinearSpatialTorus → R3 →L[ℝ] R3)
        (hSsymm : ∀ x u v, inner ℝ u (S x v) = inner ℝ (S x u) v)
        (N : ℕ), 2 ≤ N →
      ∀ (f g : BilinearSpatialTorus → ComplexVec3)
        (x : BilinearSpatialTorus) (M P : ℝ),
        Continuous f → Continuous g →
        (∀ y, ‖f y‖ ≤ M) → (∀ y, ‖g y‖ ≤ P) →
        ‖variablePhysicalFrameAnnularSquareDyadicKernelAction
            (compressiveAxialFrameField S hSsymm) N f g x‖ ≤
          243 * (C / N) * M * P := by
  rcases exists_uniform_variablePhysicalFrameAnnularSquareDyadic_bilinear_bound
    with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro S hSsymm N hN f g x M P hf hg hfb hgb
  exact hbound (compressiveAxialFrameField S hSsymm) N hN
    f g x M P hf hg hfb hgb

end PancakeStrainAxialFrame
end NavierStokes
end FluidDynamics
end Mettapedia
