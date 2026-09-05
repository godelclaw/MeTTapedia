import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeArbitraryDataMisalignment

/-!
# Energy aggregation on the concrete smooth spatial cover

The explicit `125`-cell cover is pointwise nondegenerate and has a uniform
quadratic-weight upper bound.  This module integrates those two facts.  It
shows that sums of actual smooth-cell localized nonnegative densities both
capture the global integral and overcount it by at most one fixed factor.

The result is then specialized to complete arbitrary-data pancake blocks,
their transverse expanding-line energy, and their frozen-strain Rayleigh
defect.  No frequency-support cardinality enters the estimates.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeConcreteCoverEnergy

open scoped BigOperators RealInnerProductSpace
open MeasureTheory
open PeriodicFourierTriad
open PancakePeriodicCoherentSplit
open PancakeSmoothCoherentSymbol
open PancakeBilinearPeriodization
open PancakeConcreteSmoothCellCutoff
open PancakeMisalignmentEnergyBridge
open PancakeTransverseEnergyFreezing
open PancakeTransverseEnergyCoercivity
open PancakeArbitraryDataBlocks
open PancakeArbitraryDataMisalignment
open PancakeFrameCovariance
open PancakeFullStrainFrame
open PancakePhysicalFrameKernelTransfer
open PancakeStrainSpectralFrame

local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem continuous_spatialCoverWeight (j : SpatialCellIndex) :
    Continuous (spatialCoverWeight j) := by
  unfold spatialCoverWeight
  exact Complex.continuous_normSq.comp (spatialCellCutoff j).continuous

/-- Any nonnegative density is pointwise captured by the concrete cover. -/
theorem density_le_sum_spatialCoverWeight_mul
    (f : BilinearSpatialTorus → ℝ) (hf : ∀ x, 0 ≤ f x)
    (x : BilinearSpatialTorus) :
    f x ≤ ∑ j : SpatialCellIndex, spatialCoverWeight j x * f x := by
  rw [← Finset.sum_mul]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (one_le_sum_spatialCoverWeight x) (hf x)

/-- The smooth cover gives a two-sided integral comparison for every
continuous nonnegative density. -/
theorem concreteSpatialCover_integral_sandwich
    (f : BilinearSpatialTorus → ℝ) (hf : Continuous f)
    (hf_nonneg : ∀ x, 0 ≤ f x) :
    (∫ x, f x) ≤
        ∑ j : SpatialCellIndex,
          ∫ x, spatialCoverWeight j x * f x ∧
      (∑ j : SpatialCellIndex,
          ∫ x, spatialCoverWeight j x * f x) ≤
        (125 * ‖torusCellCutoff‖ ^ 2) * ∫ x, f x := by
  have hglobal : Integrable f := by
    simpa only [integrableOn_univ] using
      hf.continuousOn.integrableOn_compact
        (isCompact_univ : IsCompact (Set.univ : Set BilinearSpatialTorus))
  have hlocal : ∀ j : SpatialCellIndex,
      Integrable (fun x ↦ spatialCoverWeight j x * f x) := by
    intro j
    have hcont : Continuous (fun x ↦ spatialCoverWeight j x * f x) :=
      (continuous_spatialCoverWeight j).mul hf
    simpa only [integrableOn_univ] using
      hcont.continuousOn.integrableOn_compact
        (isCompact_univ : IsCompact (Set.univ : Set BilinearSpatialTorus))
  have hsum : Integrable
      (fun x ↦ ∑ j : SpatialCellIndex, spatialCoverWeight j x * f x) :=
    integrable_finsetSum _ fun j _ ↦ hlocal j
  constructor
  · calc
      (∫ x, f x) ≤
          ∫ x, ∑ j : SpatialCellIndex, spatialCoverWeight j x * f x := by
        exact integral_mono hglobal hsum
          (density_le_sum_spatialCoverWeight_mul f hf_nonneg)
      _ = ∑ j : SpatialCellIndex,
          ∫ x, spatialCoverWeight j x * f x :=
        integral_finsetSum _ fun j _ ↦ hlocal j
  · calc
      (∑ j : SpatialCellIndex,
          ∫ x, spatialCoverWeight j x * f x) =
          ∫ x, ∑ j : SpatialCellIndex, spatialCoverWeight j x * f x :=
        (integral_finsetSum _ fun j _ ↦ hlocal j).symm
      _ ≤ ∫ x, (125 * ‖torusCellCutoff‖ ^ 2) * f x := by
        apply integral_mono hsum (hglobal.const_mul _)
        intro x
        dsimp only
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right
          (sum_spatialCoverWeight_le x) (hf_nonneg x)
      _ = (125 * ‖torusCellCutoff‖ ^ 2) * ∫ x, f x := by
        rw [integral_const_mul]

/-- The actual smooth cover captures the complete arbitrary-data pancake
block energy and overcounts it by at most the fixed cover constant. -/
theorem squareDyadicPancakeBlock_energy_cover_sandwich
    (F : OrientedFrameEquiv) (N : ℕ) (omega : FourierVelocity) :
    (∫ x : BilinearSpatialTorus,
        complexEuclideanNormSq (squareDyadicPancakeBlock F N omega x)) ≤
      ∑ j : SpatialCellIndex,
        ∫ x : BilinearSpatialTorus,
          spatialCoverWeight j x *
            complexEuclideanNormSq (squareDyadicPancakeBlock F N omega x) ∧
    (∑ j : SpatialCellIndex,
        ∫ x : BilinearSpatialTorus,
          spatialCoverWeight j x *
            complexEuclideanNormSq (squareDyadicPancakeBlock F N omega x)) ≤
      (125 * ‖torusCellCutoff‖ ^ 2) *
        ∫ x : BilinearSpatialTorus,
          complexEuclideanNormSq (squareDyadicPancakeBlock F N omega x) := by
  exact concreteSpatialCover_integral_sandwich
    (fun x ↦ complexEuclideanNormSq (squareDyadicPancakeBlock F N omega x))
    (continuous_complexEuclideanNormSq_comp
      (continuous_squareDyadicPancakeBlock F N omega))
    (fun x ↦ complexEuclideanNormSq_nonneg _)

/-- The frame-transformed complete pancake block used by the transverse
misalignment estimate. -/
def arbitraryDataSquareDyadicPancakeFrameBlock
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ u v : R3, inner ℝ u (S v) = inner ℝ (S u) v)
    (N : ℕ) (omega : FourierVelocity) :
    BilinearSpatialTorus → ComplexVec3 :=
  finiteFourierReconstruction
    (squareDyadicPancakeModes (fullStrainFrame S hSsymm) N)
    (fun k ↦ orientedFrameComplexLinearMap
      (fullStrainFrame S hSsymm) (omega k))

theorem continuous_arbitraryDataSquareDyadicPancakeFrameBlock
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ u v : R3, inner ℝ u (S v) = inner ℝ (S u) v)
    (N : ℕ) (omega : FourierVelocity) :
    Continuous
      (arbitraryDataSquareDyadicPancakeFrameBlock S hSsymm N omega) :=
  continuous_finiteFourierReconstruction _ _

/-- The exact coefficient misalignment energy is captured by the sum of
actual smooth-cell localized transverse energies.  The same sum is bounded
by the global transverse energy times the fixed cover constant. -/
theorem arbitraryDataMisalignmentEnergy_le_smoothCoverTransverse_and_le
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ u v : R3, inner ℝ u (S v) = inner ℝ (S u) v)
    {N : ℕ} (hN : 2 ≤ N) (omega : FourierVelocity)
    (hdiv : ∀ k, modeDot k (omega k) = 0) :
    arbitraryDataSquareDyadicPancakeMisalignmentEnergy
        S hSsymm N omega ≤
      ∑ j : SpatialCellIndex,
        ∫ x : BilinearSpatialTorus,
          spatialCoverWeight j x *
            complexTransverseEnergyEx
              (arbitraryDataSquareDyadicPancakeFrameBlock
                S hSsymm N omega x) ∧
    (∑ j : SpatialCellIndex,
        ∫ x : BilinearSpatialTorus,
          spatialCoverWeight j x *
            complexTransverseEnergyEx
              (arbitraryDataSquareDyadicPancakeFrameBlock
                S hSsymm N omega x)) ≤
      (125 * ‖torusCellCutoff‖ ^ 2) *
        ∫ x : BilinearSpatialTorus,
          complexTransverseEnergyEx
            (arbitraryDataSquareDyadicPancakeFrameBlock
              S hSsymm N omega x) := by
  have hcover := concreteSpatialCover_integral_sandwich
    (fun x ↦ complexTransverseEnergyEx
      (arbitraryDataSquareDyadicPancakeFrameBlock S hSsymm N omega x))
    (continuous_complexTransverseEnergyEx_comp
      (continuous_arbitraryDataSquareDyadicPancakeFrameBlock
        S hSsymm N omega))
    (fun x ↦ by
      unfold complexTransverseEnergyEx
      exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
  constructor
  · exact (arbitraryDataSquareDyadicPancakeMisalignmentEnergy_le_integral
      S hSsymm hN omega hdiv).trans hcover.1
  · exact hcover.2

/-- Spectral-gap coercivity survives localization by every actual smooth cell
weight.  This is the weighted cell form needed before summing frozen-strain
estimates over the cover. -/
theorem spatialCell_gap_mul_transverseEnergy_le_defect
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ u v : R3, inner ℝ u (S v) = inner ℝ (S u) v)
    (j : SpatialCellIndex) (N : ℕ) (omega : FourierVelocity) (gap : ℝ)
    (hgap₁ : gap ≤
      (orderedEigenframe S hSsymm).eigenvalue 0 -
        (orderedEigenframe S hSsymm).eigenvalue 1)
    (hgap₂ : gap ≤
      (orderedEigenframe S hSsymm).eigenvalue 0 -
        (orderedEigenframe S hSsymm).eigenvalue 2) :
    gap * (∫ x : BilinearSpatialTorus,
      spatialCoverWeight j x *
        complexTransverseEnergyEx
          (arbitraryDataSquareDyadicPancakeFrameBlock
            S hSsymm N omega x)) ≤
      ∫ x : BilinearSpatialTorus,
        spatialCoverWeight j x *
          complexStrainDefect S hSsymm
            (squareDyadicPancakeBlock
              (fullStrainFrame S hSsymm) N omega x) := by
  let field := squareDyadicPancakeBlock
    (fullStrainFrame S hSsymm) N omega
  let frameField :=
    arbitraryDataSquareDyadicPancakeFrameBlock S hSsymm N omega
  have hfield : Continuous field :=
    continuous_squareDyadicPancakeBlock _ _ _
  have hframeField : Continuous frameField :=
    continuous_arbitraryDataSquareDyadicPancakeFrameBlock S hSsymm N omega
  have htrans : Continuous (fun x ↦ complexTransverseEnergyEx (frameField x)) :=
    continuous_complexTransverseEnergyEx_comp hframeField
  have hdefect : Continuous
      (fun x ↦ complexStrainDefect S hSsymm (field x)) :=
    continuous_complexStrainDefect_comp S hSsymm hfield
  have hlhs : Integrable (fun x ↦ spatialCoverWeight j x *
      complexTransverseEnergyEx (frameField x)) := by
    have hcont : Continuous (fun x : BilinearSpatialTorus ↦
        spatialCoverWeight j x * complexTransverseEnergyEx (frameField x)) :=
      (continuous_spatialCoverWeight j).mul htrans
    simpa only [integrableOn_univ] using
      hcont.continuousOn.integrableOn_compact
        (isCompact_univ : IsCompact (Set.univ : Set BilinearSpatialTorus))
  have hrhs : Integrable (fun x ↦ spatialCoverWeight j x *
      complexStrainDefect S hSsymm (field x)) := by
    have hcont : Continuous (fun x : BilinearSpatialTorus ↦
        spatialCoverWeight j x * complexStrainDefect S hSsymm (field x)) :=
      (continuous_spatialCoverWeight j).mul hdefect
    simpa only [integrableOn_univ] using
      hcont.continuousOn.integrableOn_compact
        (isCompact_univ : IsCompact (Set.univ : Set BilinearSpatialTorus))
  rw [← integral_const_mul]
  apply integral_mono (hlhs.const_mul gap) hrhs
  intro x
  have hframeIdentity :
      complexTransverseEnergyEx (frameField x) =
        complexTransverseLineEnergy
          ((orderedEigenframe S hSsymm).eigenbasis 0) (field x) := by
    exact fullStrainFrame_transverseEnergy_finiteReconstruction_eq
      S hSsymm
      (squareDyadicPancakeModes (fullStrainFrame S hSsymm) N) omega x
  have hbase :
      gap * complexTransverseEnergyEx (frameField x) ≤
        complexStrainDefect S hSsymm (field x) := by
    rw [hframeIdentity]
    exact gap_mul_complexTransverseLineEnergy_le_complexStrainDefect
      S hSsymm (field x) gap hgap₁ hgap₂
  calc
    gap * (spatialCoverWeight j x *
        complexTransverseEnergyEx (frameField x)) =
      spatialCoverWeight j x *
        (gap * complexTransverseEnergyEx (frameField x)) := by ring
    _ ≤ spatialCoverWeight j x *
        complexStrainDefect S hSsymm (field x) :=
      mul_le_mul_of_nonneg_left hbase (spatialCoverWeight_nonneg j x)

/-- Frozen-strain Rayleigh defect on a complete arbitrary-data pancake block
obeys the same concrete-cover comparison. -/
theorem squareDyadicPancakeBlock_defect_cover_sandwich
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ u v : R3, inner ℝ u (S v) = inner ℝ (S u) v)
    (F : OrientedFrameEquiv) (N : ℕ) (omega : FourierVelocity) :
    (∫ x : BilinearSpatialTorus,
        complexStrainDefect S hSsymm
          (squareDyadicPancakeBlock F N omega x)) ≤
      ∑ j : SpatialCellIndex,
        ∫ x : BilinearSpatialTorus,
          spatialCoverWeight j x *
            complexStrainDefect S hSsymm
              (squareDyadicPancakeBlock F N omega x) ∧
    (∑ j : SpatialCellIndex,
        ∫ x : BilinearSpatialTorus,
          spatialCoverWeight j x *
            complexStrainDefect S hSsymm
              (squareDyadicPancakeBlock F N omega x)) ≤
      (125 * ‖torusCellCutoff‖ ^ 2) *
        ∫ x : BilinearSpatialTorus,
          complexStrainDefect S hSsymm
            (squareDyadicPancakeBlock F N omega x) := by
  exact concreteSpatialCover_integral_sandwich
    (fun x ↦ complexStrainDefect S hSsymm
      (squareDyadicPancakeBlock F N omega x))
    (continuous_complexStrainDefect_comp S hSsymm
      (continuous_squareDyadicPancakeBlock F N omega))
    (fun x ↦ complexStrainDefect_nonneg S hSsymm _)

/-- Summing the cellwise weighted coercivity introduces no cell count.  The
only comparison with the global defect is the explicit, frequency-independent
cover constant. -/
theorem gap_mul_sum_spatialCoverTransverseEnergy_le_globalDefect
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ u v : R3, inner ℝ u (S v) = inner ℝ (S u) v)
    (N : ℕ) (omega : FourierVelocity) (gap : ℝ)
    (hgap₁ : gap ≤
      (orderedEigenframe S hSsymm).eigenvalue 0 -
        (orderedEigenframe S hSsymm).eigenvalue 1)
    (hgap₂ : gap ≤
      (orderedEigenframe S hSsymm).eigenvalue 0 -
        (orderedEigenframe S hSsymm).eigenvalue 2) :
    gap * (∑ j : SpatialCellIndex,
        ∫ x : BilinearSpatialTorus,
          spatialCoverWeight j x *
            complexTransverseEnergyEx
              (arbitraryDataSquareDyadicPancakeFrameBlock
                S hSsymm N omega x)) ≤
      (125 * ‖torusCellCutoff‖ ^ 2) *
        ∫ x : BilinearSpatialTorus,
          complexStrainDefect S hSsymm
            (squareDyadicPancakeBlock
              (fullStrainFrame S hSsymm) N omega x) := by
  calc
    gap * (∑ j : SpatialCellIndex,
        ∫ x : BilinearSpatialTorus,
          spatialCoverWeight j x *
            complexTransverseEnergyEx
              (arbitraryDataSquareDyadicPancakeFrameBlock
                S hSsymm N omega x)) =
      ∑ j : SpatialCellIndex, gap *
        ∫ x : BilinearSpatialTorus,
          spatialCoverWeight j x *
            complexTransverseEnergyEx
              (arbitraryDataSquareDyadicPancakeFrameBlock
                S hSsymm N omega x) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ j : SpatialCellIndex,
        ∫ x : BilinearSpatialTorus,
          spatialCoverWeight j x *
            complexStrainDefect S hSsymm
              (squareDyadicPancakeBlock
                (fullStrainFrame S hSsymm) N omega x) := by
      exact Finset.sum_le_sum fun j _ ↦
        spatialCell_gap_mul_transverseEnergy_le_defect
          S hSsymm j N omega gap hgap₁ hgap₂
    _ ≤ (125 * ‖torusCellCutoff‖ ^ 2) *
        ∫ x : BilinearSpatialTorus,
          complexStrainDefect S hSsymm
            (squareDyadicPancakeBlock
              (fullStrainFrame S hSsymm) N omega x) :=
      (squareDyadicPancakeBlock_defect_cover_sandwich
        S hSsymm (fullStrainFrame S hSsymm) N omega).2

end PancakeConcreteCoverEnergy
end NavierStokes
end FluidDynamics
end Mettapedia
