import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalMisalignmentSplit

/-!
# A full strain eigenframe for the physical pancake split

The axial frame used by the annular multiplier fixes the compressive strain
direction but leaves a rotation around that axis.  The misalignment dynamics,
however, singles out the most expanding eigenline.  This module fixes the
remaining rotation: it constructs an orientation-preserving frame sending the
most expanding strain eigenvector to `e_x` and the most compressive one to
`e_z`.

The construction first uses the checked axial frame and then applies the
unique planar rotation carrying the image of the expanding direction to
`e_x`.  The resulting exact physical coherent/misaligned split therefore uses
the expanding strain eigenline as its transverse coherent reference.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeFullStrainFrame

open scoped RealInnerProductSpace
open PeriodicFourierTriad
open PancakeBilinearPeriodization
open PancakePeriodicCoherentSplit
open PancakeRealCoherentPairEstimate
open PancakeFrameCovariance
open PancakeAxialFrameConstruction
open PancakeStrainSpectralFrame
open PancakeStrainAxialFrame
open PancakeFiniteFourierBilinearTransfer
open PancakePhysicalFrameKernelTransfer
open PancakeAnnularPhysicalFrameTransfer
open PancakeSquareDyadicSectorProjector
open PancakePhysicalMisalignmentSplit

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-! ## A checked planar orientation fix -/

/-- The planar rotation with first row `(q_x,q_y)`.  Under the hypotheses
`|q|=1` and `q ⟂ e_z`, it sends `q` to `e_x`. -/
def transverseAlignMap (q v : RealVec3) : RealVec3 :=
  (q.1 * v.1 + q.2.1 * v.2.1,
    -q.2.1 * v.1 + q.1 * v.2.1,
    v.2.2)

/-- Explicit inverse of `transverseAlignMap`. -/
def transverseAlignInverse (q v : RealVec3) : RealVec3 :=
  (q.1 * v.1 - q.2.1 * v.2.1,
    q.2.1 * v.1 + q.1 * v.2.1,
    v.2.2)

theorem transverseAlignInverse_left (q : RealVec3)
    (hqnorm : normSq q = 1) (hqz : dot q ez = 0) :
    Function.LeftInverse (transverseAlignInverse q)
      (transverseAlignMap q) := by
  obtain ⟨a, b, c⟩ := q
  have hc : c = 0 := by simpa [dot, ez] using hqz
  subst c
  have hab : a * a + b * b = 1 := by
    simpa [normSq, dot] using hqnorm
  rintro ⟨x, y, z⟩
  simp only [transverseAlignMap, transverseAlignInverse]
  apply Prod.ext
  · dsimp
    linear_combination x * hab
  · apply Prod.ext
    · dsimp
      linear_combination y * hab
    · rfl

theorem transverseAlignInverse_right (q : RealVec3)
    (hqnorm : normSq q = 1) (hqz : dot q ez = 0) :
    Function.RightInverse (transverseAlignInverse q)
      (transverseAlignMap q) := by
  obtain ⟨a, b, c⟩ := q
  have hc : c = 0 := by simpa [dot, ez] using hqz
  subst c
  have hab : a * a + b * b = 1 := by
    simpa [normSq, dot] using hqnorm
  rintro ⟨x, y, z⟩
  simp only [transverseAlignMap, transverseAlignInverse]
  apply Prod.ext
  · dsimp
    linear_combination x * hab
  · apply Prod.ext
    · dsimp
      linear_combination y * hab
    · rfl

theorem transverseAlignMap_bijective (q : RealVec3)
    (hqnorm : normSq q = 1) (hqz : dot q ez = 0) :
    Function.Bijective (transverseAlignMap q) :=
  ⟨(transverseAlignInverse_left q hqnorm hqz).injective,
    (transverseAlignInverse_right q hqnorm hqz).surjective⟩

theorem transverseAlignMap_map_add (q u v : RealVec3) :
    transverseAlignMap q (add u v) =
      add (transverseAlignMap q u) (transverseAlignMap q v) := by
  obtain ⟨a, b, c⟩ := q
  obtain ⟨ux, uy, uz⟩ := u
  obtain ⟨vx, vy, vz⟩ := v
  simp only [transverseAlignMap, add]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp <;> ring

theorem transverseAlignMap_map_smul (q : RealVec3) (r : ℝ)
    (v : RealVec3) :
    transverseAlignMap q (smul r v) =
      smul r (transverseAlignMap q v) := by
  obtain ⟨a, b, c⟩ := q
  obtain ⟨x, y, z⟩ := v
  simp only [transverseAlignMap, smul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp <;> ring

theorem transverseAlignMap_map_dot (q u v : RealVec3)
    (hqnorm : normSq q = 1) (hqz : dot q ez = 0) :
    dot (transverseAlignMap q u) (transverseAlignMap q v) = dot u v := by
  obtain ⟨a, b, c⟩ := q
  have hc : c = 0 := by simpa [dot, ez] using hqz
  subst c
  have hab : a * a + b * b = 1 := by
    simpa [normSq, dot] using hqnorm
  obtain ⟨ux, uy, uz⟩ := u
  obtain ⟨vx, vy, vz⟩ := v
  simp only [transverseAlignMap, dot]
  linear_combination (ux * vx + uy * vy) * hab

theorem transverseAlignMap_map_cross (q u v : RealVec3)
    (hqnorm : normSq q = 1) (hqz : dot q ez = 0) :
    transverseAlignMap q (cross u v) =
      cross (transverseAlignMap q u) (transverseAlignMap q v) := by
  obtain ⟨a, b, c⟩ := q
  have hc : c = 0 := by simpa [dot, ez] using hqz
  subst c
  have hab : a * a + b * b = 1 := by
    simpa [normSq, dot] using hqnorm
  obtain ⟨ux, uy, uz⟩ := u
  obtain ⟨vx, vy, vz⟩ := v
  simp only [transverseAlignMap, cross]
  apply Prod.ext
  · dsimp
    ring
  · apply Prod.ext
    · dsimp
      ring
    · dsimp
      calc
        ux * vy - uy * vx =
            (a * a + b * b) * (ux * vy - uy * vx) := by rw [hab, one_mul]
        _ = (a * ux + b * uy) * (-b * vx + a * vy) -
            (-b * ux + a * uy) * (a * vx + b * vy) := by ring

/-- The planar alignment rotation as an oriented Euclidean frame. -/
def transverseAlignFrame (q : RealVec3)
    (hqnorm : normSq q = 1) (hqz : dot q ez = 0) :
    OrientedFrameEquiv where
  toFun := transverseAlignMap q
  bijective := transverseAlignMap_bijective q hqnorm hqz
  map_add := transverseAlignMap_map_add q
  map_smul := transverseAlignMap_map_smul q
  map_dot := fun u v ↦ transverseAlignMap_map_dot q u v hqnorm hqz
  map_cross := fun u v ↦ transverseAlignMap_map_cross q u v hqnorm hqz

theorem transverseAlignMap_self (q : RealVec3)
    (hqnorm : normSq q = 1) (hqz : dot q ez = 0) :
    transverseAlignMap q q = ex := by
  obtain ⟨a, b, c⟩ := q
  have hc : c = 0 := by simpa [dot, ez] using hqz
  subst c
  have hab : a * a + b * b = 1 := by
    simpa [normSq, dot] using hqnorm
  simp only [transverseAlignMap, ex]
  apply Prod.ext
  · dsimp
    exact hab
  · apply Prod.ext
    · dsimp
      ring
    · rfl

@[simp]
theorem transverseAlignMap_ez (q : RealVec3) :
    transverseAlignMap q ez = ez := by
  obtain ⟨a, b, c⟩ := q
  simp [transverseAlignMap, ez]

/-- Composition of two algebraic oriented frame equivalences. -/
def composeOrientedFrames (G F : OrientedFrameEquiv) :
    OrientedFrameEquiv where
  toFun := fun v ↦ G.toFun (F.toFun v)
  bijective := G.bijective.comp F.bijective
  map_add := fun u v ↦ by rw [F.map_add, G.map_add]
  map_smul := fun r v ↦ by rw [F.map_smul, G.map_smul]
  map_dot := fun u v ↦ by rw [G.map_dot, F.map_dot]
  map_cross := fun u v ↦ by rw [F.map_cross, G.map_cross]

/-! ## Completing the pointwise strain frame -/

/-- Coordinate conversion preserves the real inner product. -/
theorem dot_realVec3OfEuclidean (u v : R3) :
    dot (realVec3OfEuclidean u) (realVec3OfEuclidean v) = inner ℝ u v := by
  simp [dot, realVec3OfEuclidean, PiLp.inner_apply,
    RCLike.inner_apply, Fin.sum_univ_three]
  ring

/-- The most expanding direction in the ordered strain eigenframe. -/
def expandingDirection
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    RealVec3 :=
  realVec3OfEuclidean ((orderedEigenframe S hSsymm).eigenbasis 0)

theorem normSq_expandingDirection
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    normSq (expandingDirection S hSsymm) = 1 := by
  rw [expandingDirection, normSq_realVec3OfEuclidean,
    (orderedEigenframe S hSsymm).eigenbasis.norm_eq_one]
  norm_num

theorem dot_expandingDirection_compressiveDirection
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    dot (expandingDirection S hSsymm)
      (compressiveDirection S hSsymm) = 0 := by
  rw [expandingDirection, compressiveDirection, dot_realVec3OfEuclidean]
  simp

/-- Image of the expanding eigenvector after the axial part of the strain
frame has sent the compressive eigenvector to `e_z`. -/
def axiallyTransportedExpandingDirection
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    RealVec3 :=
  (compressiveAxialFrame S hSsymm).toFun (expandingDirection S hSsymm)

theorem normSq_axiallyTransportedExpandingDirection
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    normSq (axiallyTransportedExpandingDirection S hSsymm) = 1 := by
  rw [axiallyTransportedExpandingDirection,
    (compressiveAxialFrame S hSsymm).map_normSq,
    normSq_expandingDirection]

theorem dot_axiallyTransportedExpandingDirection_ez
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    dot (axiallyTransportedExpandingDirection S hSsymm) ez = 0 := by
  rw [axiallyTransportedExpandingDirection,
    ← compressiveAxialFrame_maps_direction_to_ez S hSsymm,
    (compressiveAxialFrame S hSsymm).map_dot,
    dot_expandingDirection_compressiveDirection]

/-- The full orientation-preserving pointwise strain frame: expanding goes to
`e_x`, compressive goes to `e_z`. -/
def fullStrainFrame
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    OrientedFrameEquiv :=
  composeOrientedFrames
    (transverseAlignFrame
      (axiallyTransportedExpandingDirection S hSsymm)
      (normSq_axiallyTransportedExpandingDirection S hSsymm)
      (dot_axiallyTransportedExpandingDirection_ez S hSsymm))
    (compressiveAxialFrame S hSsymm)

theorem fullStrainFrame_maps_expandingDirection_to_ex
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    (fullStrainFrame S hSsymm).toFun
      (expandingDirection S hSsymm) = ex := by
  exact transverseAlignMap_self
    (axiallyTransportedExpandingDirection S hSsymm)
    (normSq_axiallyTransportedExpandingDirection S hSsymm)
    (dot_axiallyTransportedExpandingDirection_ez S hSsymm)

theorem fullStrainFrame_maps_compressiveDirection_to_ez
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    (fullStrainFrame S hSsymm).toFun
      (compressiveDirection S hSsymm) = ez := by
  change transverseAlignMap _
    ((compressiveAxialFrame S hSsymm).toFun
      (compressiveDirection S hSsymm)) = ez
  rw [compressiveAxialFrame_maps_direction_to_ez,
    transverseAlignMap_ez]

/-- In physical complex coordinates, the inverse image of the multiplier's
coherent reference `e_x` is exactly the most expanding strain eigenvector. -/
theorem fullStrainFrame_inverseComplex_ex_eq_expandingDirection
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v) :
    orientedFrameInverseComplexLinearMap (fullStrainFrame S hSsymm)
        (realVec3ToComplexVec3 ex) =
      realVec3ToComplexVec3 (expandingDirection S hSsymm) := by
  have hforward :
      orientedFrameComplexLinearMap (fullStrainFrame S hSsymm)
          (realVec3ToComplexVec3 (expandingDirection S hSsymm)) =
        realVec3ToComplexVec3 ex := by
    unfold orientedFrameComplexLinearMap
    rw [complexifyRealLinearEquiv_realVec3ToComplexVec3]
    change realVec3ToComplexVec3
      ((fullStrainFrame S hSsymm).toFun
        (expandingDirection S hSsymm)) = realVec3ToComplexVec3 ex
    rw [fullStrainFrame_maps_expandingDirection_to_ex]
  rw [← hforward, orientedFrameInverseComplexLinearMap_apply]

/-- Pointwise full eigenframe field constructed from a symmetric strain
field. -/
def fullStrainFrameField {X : Type*}
    (S : X → R3 →L[ℝ] R3)
    (hSsymm : ∀ x u v, inner ℝ u (S x v) = inner ℝ (S x u) v) :
    X → OrientedFrameEquiv :=
  fun x ↦ fullStrainFrame (S x) (hSsymm x)

/-! ## Exact physical split in the full strain eigenframe -/

/-- The full finite-sector physical stretching identity in the frame whose
coherent transverse reference is the expanding strain eigenline and whose
axis is the compressive eigenline. -/
theorem fullStrainFrame_physicalFinitePancakeStretchingSum_eq_kernel_add_misalignment
    (S : BilinearSpatialTorus → R3 →L[ℝ] R3)
    (hSsymm : ∀ x u v, inner ℝ u (S x v) = inner ℝ (S x u) v)
    {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    physicalFiniteFramePancakeStretchingSum
        (fullStrainFrameField S hSsymm x) N s t omega eta x =
      physicalOrientedFrameAnnularSquareDyadicKernelAction
          (fullStrainFrameField S hSsymm x) N
          (squareDyadicPancakeSectorProjection
            (fullStrainFrameField S hSsymm x) N s omega)
          (squareDyadicPancakeSectorProjection
            (fullStrainFrameField S hSsymm x) N t eta) x +
        physicalFiniteFrameMisalignmentPancakeStretchingSum
          (fullStrainFrameField S hSsymm x) N s t omega eta x :=
  physicalFiniteFramePancakeStretchingSum_eq_kernel_add_misalignment
    (fullStrainFrameField S hSsymm x) hN s t omega eta x

/-- The coherent share in the full strain eigenframe has the same uniform
cardinality-free `C/N` bound, with only the exact expanding-line
misalignment remainder left. -/
theorem exists_uniform_fullStrainFramePhysicalPancakeSplit_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : BilinearSpatialTorus → R3 →L[ℝ] R3)
        (hSsymm : ∀ x u v, inner ℝ u (S x v) = inner ℝ (S x u) v)
        (N : ℕ), 2 ≤ N →
      ∀ (s t : Finset Wavevector) (omega eta : FourierVelocity)
        (x : BilinearSpatialTorus) (M P : ℝ),
        (∀ y, ‖squareDyadicPancakeSectorProjection
          (fullStrainFrameField S hSsymm x) N s omega y‖ ≤ M) →
        (∀ y, ‖squareDyadicPancakeSectorProjection
          (fullStrainFrameField S hSsymm x) N t eta y‖ ≤ P) →
        ‖physicalFiniteFramePancakeStretchingSum
            (fullStrainFrameField S hSsymm x)
            N s t omega eta x‖ ≤
          243 * (C / N) * M * P +
            ‖physicalFiniteFrameMisalignmentPancakeStretchingSum
              (fullStrainFrameField S hSsymm x)
              N s t omega eta x‖ := by
  rcases exists_uniform_physicalPancakeSplit_bilinear_bound with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro S hSsymm N hN s t omega eta x M P homega heta
  exact hbound (fullStrainFrameField S hSsymm x) N hN
    s t omega eta x M P homega heta

end PancakeFullStrainFrame
end NavierStokes
end FluidDynamics
end Mettapedia
