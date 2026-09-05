import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeConcreteCoverEnergy

/-!
# Cell-dependent frozen strains on the concrete smooth cover

The unweighted frame-freezing theorem compares two constant strain frames.
For the spatial aggregation used by the pancake route, that comparison has to
survive multiplication by the actual smooth cover weights, and the frozen
strain must be allowed to differ from one cell to the next.

This module proves exactly that statement.  On the branch where every frozen
cell has a separated top eigenvalue, the complete arbitrary-data
misalignment energy is bounded by the sum of the cell-localized frozen-strain
Rayleigh defects, plus the explicit projector-freezing error.  The latter is
controlled by the fixed quadratic-overlap constant of the concrete 125-cell
cover; no frequency-support cardinality and no additional cell-count factor
appears.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeConcreteWeightedFreezing

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
open PancakeConcreteCoverEnergy
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

/-- Weighted version of the frozen-expanding-line integral estimate.  The
weight may be any continuous nonnegative function on the periodic box. -/
theorem fullStrainFrame_weightedIntegral_smallFrozenGap_or_transverseEnergy_le
    (A B : R3 →L[ℝ] R3)
    (hAsymm : ∀ (u v : R3), inner ℝ u (A v) = inner ℝ (A u) v)
    (hBsymm : ∀ (u v : R3), inner ℝ u (B v) = inner ℝ (B u) v)
    (epsilon threshold : ℝ) (hthreshold : 0 < threshold)
    (hepsilon : 0 ≤ epsilon) (hAB : ‖A - B‖ ≤ epsilon)
    (weight : BilinearSpatialTorus → ℝ) (hweight : Continuous weight)
    (hweight_nonneg : ∀ x, 0 ≤ weight x)
    (s : Finset Wavevector) (omega : FourierVelocity) :
    (orderedEigenframe B hBsymm).eigenvalue 0 -
        (orderedEigenframe B hBsymm).eigenvalue 1 <
          threshold + epsilon ∨
      (orderedEigenframe B hBsymm).eigenvalue 0 -
        (orderedEigenframe B hBsymm).eigenvalue 2 <
          threshold + epsilon ∨
      (∫ x : BilinearSpatialTorus,
          weight x *
            complexTransverseEnergyEx
              (finiteFourierReconstruction s
                (fun k ↦ orientedFrameComplexLinearMap
                  (fullStrainFrame A hAsymm) (omega k)) x)) ≤
        (∫ x : BilinearSpatialTorus,
          weight x *
            complexTransverseEnergyEx
              (finiteFourierReconstruction s
                (fun k ↦ orientedFrameComplexLinearMap
                  (fullStrainFrame B hBsymm) (omega k)) x)) +
        (4 * (epsilon / threshold)) *
          ∫ x : BilinearSpatialTorus,
            weight x * complexEuclideanNormSq
              (finiteFourierReconstruction s omega x) := by
  rcases constructedExpandingLine_smallFrozenGap_or_projectorClose
      A B hAsymm hBsymm epsilon threshold hthreshold hepsilon hAB with
    hgap₁ | hgap₂ | hprojector
  · exact Or.inl hgap₁
  · exact Or.inr (Or.inl hgap₂)
  · apply Or.inr (Or.inr ?_)
    let fieldA : BilinearSpatialTorus → ComplexVec3 :=
      finiteFourierReconstruction s
        (fun k ↦ orientedFrameComplexLinearMap
          (fullStrainFrame A hAsymm) (omega k))
    let fieldB : BilinearSpatialTorus → ComplexVec3 :=
      finiteFourierReconstruction s
        (fun k ↦ orientedFrameComplexLinearMap
          (fullStrainFrame B hBsymm) (omega k))
    let field : BilinearSpatialTorus → ComplexVec3 :=
      finiteFourierReconstruction s omega
    have hfieldA : Continuous fieldA :=
      continuous_finiteFourierReconstruction s _
    have hfieldB : Continuous fieldB :=
      continuous_finiteFourierReconstruction s _
    have hfield : Continuous field :=
      continuous_finiteFourierReconstruction s omega
    have hintA : Integrable
        (fun x ↦ weight x * complexTransverseEnergyEx (fieldA x)) := by
      have hcont : Continuous (fun x : BilinearSpatialTorus ↦
          weight x * complexTransverseEnergyEx (fieldA x)) :=
        hweight.mul (continuous_complexTransverseEnergyEx_comp hfieldA)
      simpa only [integrableOn_univ] using
        hcont.continuousOn.integrableOn_compact
          (isCompact_univ : IsCompact (Set.univ : Set BilinearSpatialTorus))
    have hintB : Integrable
        (fun x ↦ weight x * complexTransverseEnergyEx (fieldB x)) := by
      have hcont : Continuous (fun x : BilinearSpatialTorus ↦
          weight x * complexTransverseEnergyEx (fieldB x)) :=
        hweight.mul (continuous_complexTransverseEnergyEx_comp hfieldB)
      simpa only [integrableOn_univ] using
        hcont.continuousOn.integrableOn_compact
          (isCompact_univ : IsCompact (Set.univ : Set BilinearSpatialTorus))
    have hintEnergy : Integrable
        (fun x ↦ weight x * complexEuclideanNormSq (field x)) := by
      have hcont : Continuous (fun x : BilinearSpatialTorus ↦
          weight x * complexEuclideanNormSq (field x)) :=
        hweight.mul (continuous_complexEuclideanNormSq_comp hfield)
      simpa only [integrableOn_univ] using
        hcont.continuousOn.integrableOn_compact
          (isCompact_univ : IsCompact (Set.univ : Set BilinearSpatialTorus))
    have hpoint : ∀ x,
        weight x * complexTransverseEnergyEx (fieldA x) ≤
          weight x * complexTransverseEnergyEx (fieldB x) +
            (4 * (epsilon / threshold)) *
              (weight x * complexEuclideanNormSq (field x)) := by
      intro x
      have hbase : complexTransverseEnergyEx (fieldA x) ≤
          complexTransverseEnergyEx (fieldB x) +
            (4 * (epsilon / threshold)) *
              complexEuclideanNormSq (field x) := by
        rw [show complexTransverseEnergyEx (fieldA x) =
            complexTransverseLineEnergy
              ((orderedEigenframe A hAsymm).eigenbasis 0) (field x) by
          exact fullStrainFrame_transverseEnergy_finiteReconstruction_eq
            A hAsymm s omega x]
        rw [show complexTransverseEnergyEx (fieldB x) =
            complexTransverseLineEnergy
              ((orderedEigenframe B hBsymm).eigenbasis 0) (field x) by
          exact fullStrainFrame_transverseEnergy_finiteReconstruction_eq
            B hBsymm s omega x]
        refine (complexTransverseLineEnergy_le_add_projectorError
          ((orderedEigenframe A hAsymm).eigenbasis 0)
          ((orderedEigenframe B hBsymm).eigenbasis 0) (field x)).trans ?_
        gcongr
        exact complexEuclideanNormSq_nonneg (field x)
      calc
        weight x * complexTransverseEnergyEx (fieldA x) ≤
            weight x * (complexTransverseEnergyEx (fieldB x) +
              (4 * (epsilon / threshold)) *
                complexEuclideanNormSq (field x)) :=
          mul_le_mul_of_nonneg_left hbase (hweight_nonneg x)
        _ = weight x * complexTransverseEnergyEx (fieldB x) +
            (4 * (epsilon / threshold)) *
              (weight x * complexEuclideanNormSq (field x)) := by ring
    change (∫ x, weight x * complexTransverseEnergyEx (fieldA x)) ≤
      (∫ x, weight x * complexTransverseEnergyEx (fieldB x)) +
        (4 * (epsilon / threshold)) *
          ∫ x, weight x * complexEuclideanNormSq (field x)
    calc
      (∫ x, weight x * complexTransverseEnergyEx (fieldA x)) ≤
          ∫ x, (weight x * complexTransverseEnergyEx (fieldB x) +
            (4 * (epsilon / threshold)) *
              (weight x * complexEuclideanNormSq (field x))) := by
        exact integral_mono hintA
          (hintB.add (hintEnergy.const_mul _)) hpoint
      _ = (∫ x, weight x * complexTransverseEnergyEx (fieldB x)) +
          (4 * (epsilon / threshold)) *
            ∫ x, weight x * complexEuclideanNormSq (field x) := by
        rw [integral_add hintB (hintEnergy.const_mul _), integral_const_mul]

/-- The complete square-dyadic pancake block selected in the `A` frame and
then expressed in the `B` frame. -/
def arbitraryDataSquareDyadicPancakeCrossFrameBlock
    (A B : R3 →L[ℝ] R3)
    (hAsymm : ∀ (u v : R3), inner ℝ u (A v) = inner ℝ (A u) v)
    (hBsymm : ∀ (u v : R3), inner ℝ u (B v) = inner ℝ (B u) v)
    (N : ℕ) (omega : FourierVelocity) :
    BilinearSpatialTorus → ComplexVec3 :=
  finiteFourierReconstruction
    (squareDyadicPancakeModes (fullStrainFrame A hAsymm) N)
    (fun k ↦ orientedFrameComplexLinearMap
      (fullStrainFrame B hBsymm) (omega k))

theorem continuous_arbitraryDataSquareDyadicPancakeCrossFrameBlock
    (A B : R3 →L[ℝ] R3)
    (hAsymm : ∀ (u v : R3), inner ℝ u (A v) = inner ℝ (A u) v)
    (hBsymm : ∀ (u v : R3), inner ℝ u (B v) = inner ℝ (B u) v)
    (N : ℕ) (omega : FourierVelocity) :
    Continuous
      (arbitraryDataSquareDyadicPancakeCrossFrameBlock
        A B hAsymm hBsymm N omega) :=
  continuous_finiteFourierReconstruction _ _

/-- Frozen-frame spectral-gap coercivity after localization by one concrete
cover weight, for a block whose mode selector came from a different frame. -/
theorem spatialCell_gap_mul_crossFrameTransverseEnergy_le_defect
    (A B : R3 →L[ℝ] R3)
    (hAsymm : ∀ (u v : R3), inner ℝ u (A v) = inner ℝ (A u) v)
    (hBsymm : ∀ (u v : R3), inner ℝ u (B v) = inner ℝ (B u) v)
    (j : SpatialCellIndex) (N : ℕ) (omega : FourierVelocity) (gap : ℝ)
    (hgap₁ : gap ≤
      (orderedEigenframe B hBsymm).eigenvalue 0 -
        (orderedEigenframe B hBsymm).eigenvalue 1)
    (hgap₂ : gap ≤
      (orderedEigenframe B hBsymm).eigenvalue 0 -
        (orderedEigenframe B hBsymm).eigenvalue 2) :
    gap * (∫ x : BilinearSpatialTorus,
      spatialCoverWeight j x *
        complexTransverseEnergyEx
          (arbitraryDataSquareDyadicPancakeCrossFrameBlock
            A B hAsymm hBsymm N omega x)) ≤
      ∫ x : BilinearSpatialTorus,
        spatialCoverWeight j x *
          complexStrainDefect B hBsymm
            (squareDyadicPancakeBlock
              (fullStrainFrame A hAsymm) N omega x) := by
  let field := squareDyadicPancakeBlock
    (fullStrainFrame A hAsymm) N omega
  let frameField := arbitraryDataSquareDyadicPancakeCrossFrameBlock
    A B hAsymm hBsymm N omega
  have hfield : Continuous field := continuous_squareDyadicPancakeBlock _ _ _
  have hframeField : Continuous frameField :=
    continuous_arbitraryDataSquareDyadicPancakeCrossFrameBlock
      A B hAsymm hBsymm N omega
  have hlhs : Integrable (fun x ↦ spatialCoverWeight j x *
      complexTransverseEnergyEx (frameField x)) := by
    have hcont : Continuous (fun x : BilinearSpatialTorus ↦
        spatialCoverWeight j x * complexTransverseEnergyEx (frameField x)) :=
      (continuous_spatialCoverWeight j).mul
        (continuous_complexTransverseEnergyEx_comp hframeField)
    simpa only [integrableOn_univ] using
      hcont.continuousOn.integrableOn_compact
        (isCompact_univ : IsCompact (Set.univ : Set BilinearSpatialTorus))
  have hrhs : Integrable (fun x ↦ spatialCoverWeight j x *
      complexStrainDefect B hBsymm (field x)) := by
    have hcont : Continuous (fun x : BilinearSpatialTorus ↦
        spatialCoverWeight j x * complexStrainDefect B hBsymm (field x)) :=
      (continuous_spatialCoverWeight j).mul
        (continuous_complexStrainDefect_comp B hBsymm hfield)
    simpa only [integrableOn_univ] using
      hcont.continuousOn.integrableOn_compact
        (isCompact_univ : IsCompact (Set.univ : Set BilinearSpatialTorus))
  rw [← integral_const_mul]
  apply integral_mono (hlhs.const_mul gap) hrhs
  intro x
  have hframeIdentity : complexTransverseEnergyEx (frameField x) =
      complexTransverseLineEnergy
        ((orderedEigenframe B hBsymm).eigenbasis 0) (field x) := by
    exact fullStrainFrame_transverseEnergy_finiteReconstruction_eq
      B hBsymm
      (squareDyadicPancakeModes (fullStrainFrame A hAsymm) N) omega x
  have hbase : gap * complexTransverseEnergyEx (frameField x) ≤
      complexStrainDefect B hBsymm (field x) := by
    rw [hframeIdentity]
    exact gap_mul_complexTransverseLineEnergy_le_complexStrainDefect
      B hBsymm (field x) gap hgap₁ hgap₂
  calc
    gap * (spatialCoverWeight j x *
        complexTransverseEnergyEx (frameField x)) =
      spatialCoverWeight j x *
        (gap * complexTransverseEnergyEx (frameField x)) := by ring
    _ ≤ spatialCoverWeight j x * complexStrainDefect B hBsymm (field x) :=
      mul_le_mul_of_nonneg_left hbase (spatialCoverWeight_nonneg j x)

/-- A separated concrete cell converts the varying-frame transverse energy
to a frozen-strain Rayleigh defect, with the exact projector oscillation
error retained. -/
theorem spatialCell_gap_mul_observationTransverse_le_frozenDefect
    (A B : R3 →L[ℝ] R3)
    (hAsymm : ∀ (u v : R3), inner ℝ u (A v) = inner ℝ (A u) v)
    (hBsymm : ∀ (u v : R3), inner ℝ u (B v) = inner ℝ (B u) v)
    (epsilon threshold : ℝ) (hthreshold : 0 < threshold)
    (hepsilon : 0 ≤ epsilon) (hAB : ‖A - B‖ ≤ epsilon)
    (hgap₁ : threshold + epsilon ≤
      (orderedEigenframe B hBsymm).eigenvalue 0 -
        (orderedEigenframe B hBsymm).eigenvalue 1)
    (hgap₂ : threshold + epsilon ≤
      (orderedEigenframe B hBsymm).eigenvalue 0 -
        (orderedEigenframe B hBsymm).eigenvalue 2)
    (j : SpatialCellIndex) (N : ℕ) (omega : FourierVelocity) :
    (threshold + epsilon) *
      (∫ x : BilinearSpatialTorus,
        spatialCoverWeight j x *
          complexTransverseEnergyEx
            (arbitraryDataSquareDyadicPancakeFrameBlock
              A hAsymm N omega x)) ≤
      (∫ x : BilinearSpatialTorus,
        spatialCoverWeight j x *
          complexStrainDefect B hBsymm
            (squareDyadicPancakeBlock
              (fullStrainFrame A hAsymm) N omega x)) +
      (threshold + epsilon) * (4 * (epsilon / threshold)) *
        ∫ x : BilinearSpatialTorus,
          spatialCoverWeight j x *
            complexEuclideanNormSq
              (squareDyadicPancakeBlock
                (fullStrainFrame A hAsymm) N omega x) := by
  let sA := squareDyadicPancakeModes (fullStrainFrame A hAsymm) N
  let transverseA := ∫ x : BilinearSpatialTorus,
    spatialCoverWeight j x *
      complexTransverseEnergyEx
        (arbitraryDataSquareDyadicPancakeFrameBlock A hAsymm N omega x)
  let transverseB := ∫ x : BilinearSpatialTorus,
    spatialCoverWeight j x *
      complexTransverseEnergyEx
        (arbitraryDataSquareDyadicPancakeCrossFrameBlock
          A B hAsymm hBsymm N omega x)
  let defectB := ∫ x : BilinearSpatialTorus,
    spatialCoverWeight j x *
      complexStrainDefect B hBsymm
        (squareDyadicPancakeBlock (fullStrainFrame A hAsymm) N omega x)
  let energy := ∫ x : BilinearSpatialTorus,
    spatialCoverWeight j x * complexEuclideanNormSq
      (squareDyadicPancakeBlock (fullStrainFrame A hAsymm) N omega x)
  have hfreeze :=
    fullStrainFrame_weightedIntegral_smallFrozenGap_or_transverseEnergy_le
      A B hAsymm hBsymm epsilon threshold hthreshold hepsilon hAB
      (spatialCoverWeight j) (continuous_spatialCoverWeight j)
      (spatialCoverWeight_nonneg j) sA omega
  have hfar : transverseA ≤ transverseB +
      (4 * (epsilon / threshold)) * energy := by
    rcases hfreeze with hsmall₁ | hsmall₂ | hfar
    · exact False.elim ((not_lt_of_ge hgap₁) hsmall₁)
    · exact False.elim ((not_lt_of_ge hgap₂) hsmall₂)
    · simpa [transverseA, transverseB, energy, sA,
        arbitraryDataSquareDyadicPancakeFrameBlock,
        arbitraryDataSquareDyadicPancakeCrossFrameBlock,
        squareDyadicPancakeBlock] using hfar
  have hcoercive : (threshold + epsilon) * transverseB ≤ defectB := by
    simpa [transverseB, defectB] using
      spatialCell_gap_mul_crossFrameTransverseEnergy_le_defect
        A B hAsymm hBsymm j N omega (threshold + epsilon) hgap₁ hgap₂
  have hgapNonneg : 0 ≤ threshold + epsilon := by linarith
  change (threshold + epsilon) * transverseA ≤
    defectB + (threshold + epsilon) * (4 * (epsilon / threshold)) * energy
  calc
    (threshold + epsilon) * transverseA ≤
        (threshold + epsilon) *
          (transverseB + (4 * (epsilon / threshold)) * energy) :=
      mul_le_mul_of_nonneg_left hfar hgapNonneg
    _ = (threshold + epsilon) * transverseB +
        (threshold + epsilon) * (4 * (epsilon / threshold)) * energy := by ring
    _ ≤ defectB +
        (threshold + epsilon) * (4 * (epsilon / threshold)) * energy :=
      add_le_add hcoercive (le_refl _)

/-- **Concrete cell-dependent freezing theorem.**  A different frozen strain
may be used on each of the 125 cells.  If every cell is close to the
observation strain and has a separated top eigenvalue, the complete
arbitrary-data Fourier misalignment is controlled by the sum of localized
frozen Rayleigh defects and one fixed-cover freezing error. -/
theorem arbitraryDataMisalignmentEnergy_le_cellwiseFrozenDefect
    (A : R3 →L[ℝ] R3)
    (hAsymm : ∀ (u v : R3), inner ℝ u (A v) = inner ℝ (A u) v)
    (B : SpatialCellIndex → R3 →L[ℝ] R3)
    (hBsymm : ∀ j u v, inner ℝ u (B j v) = inner ℝ (B j u) v)
    (epsilon threshold : ℝ) (hthreshold : 0 < threshold)
    (hepsilon : 0 ≤ epsilon)
    (hAB : ∀ j, ‖A - B j‖ ≤ epsilon)
    (hgap₁ : ∀ j, threshold + epsilon ≤
      (orderedEigenframe (B j) (hBsymm j)).eigenvalue 0 -
        (orderedEigenframe (B j) (hBsymm j)).eigenvalue 1)
    (hgap₂ : ∀ j, threshold + epsilon ≤
      (orderedEigenframe (B j) (hBsymm j)).eigenvalue 0 -
        (orderedEigenframe (B j) (hBsymm j)).eigenvalue 2)
    {N : ℕ} (hN : 2 ≤ N) (omega : FourierVelocity)
    (hdiv : ∀ k, modeDot k (omega k) = 0) :
    (threshold + epsilon) *
        arbitraryDataSquareDyadicPancakeMisalignmentEnergy
          A hAsymm N omega ≤
      (∑ j : SpatialCellIndex,
        ∫ x : BilinearSpatialTorus,
          spatialCoverWeight j x *
            complexStrainDefect (B j) (hBsymm j)
              (squareDyadicPancakeBlock
                (fullStrainFrame A hAsymm) N omega x)) +
      (threshold + epsilon) * (4 * (epsilon / threshold)) *
        (125 * ‖torusCellCutoff‖ ^ 2) *
          ∫ x : BilinearSpatialTorus,
            complexEuclideanNormSq
              (squareDyadicPancakeBlock
                (fullStrainFrame A hAsymm) N omega x) := by
  let transverse := fun j : SpatialCellIndex ↦
    ∫ x : BilinearSpatialTorus,
      spatialCoverWeight j x *
        complexTransverseEnergyEx
          (arbitraryDataSquareDyadicPancakeFrameBlock A hAsymm N omega x)
  let defect := fun j : SpatialCellIndex ↦
    ∫ x : BilinearSpatialTorus,
      spatialCoverWeight j x *
        complexStrainDefect (B j) (hBsymm j)
          (squareDyadicPancakeBlock (fullStrainFrame A hAsymm) N omega x)
  let energy := fun j : SpatialCellIndex ↦
    ∫ x : BilinearSpatialTorus,
      spatialCoverWeight j x * complexEuclideanNormSq
        (squareDyadicPancakeBlock (fullStrainFrame A hAsymm) N omega x)
  let globalEnergy := ∫ x : BilinearSpatialTorus,
    complexEuclideanNormSq
      (squareDyadicPancakeBlock (fullStrainFrame A hAsymm) N omega x)
  have hcapture :
      arbitraryDataSquareDyadicPancakeMisalignmentEnergy A hAsymm N omega ≤
        ∑ j : SpatialCellIndex, transverse j := by
    simpa [transverse] using
      (arbitraryDataMisalignmentEnergy_le_smoothCoverTransverse_and_le
        A hAsymm hN omega hdiv).1
  have hcell : ∀ j : SpatialCellIndex,
      (threshold + epsilon) * transverse j ≤
        defect j +
          (threshold + epsilon) * (4 * (epsilon / threshold)) * energy j := by
    intro j
    simpa [transverse, defect, energy] using
      spatialCell_gap_mul_observationTransverse_le_frozenDefect
        A (B j) hAsymm (hBsymm j) epsilon threshold hthreshold hepsilon
        (hAB j) (hgap₁ j) (hgap₂ j) j N omega
  have hgapNonneg : 0 ≤ threshold + epsilon := by linarith
  have hsum : (threshold + epsilon) *
      (∑ j : SpatialCellIndex, transverse j) ≤
        (∑ j : SpatialCellIndex, defect j) +
          (threshold + epsilon) * (4 * (epsilon / threshold)) *
            ∑ j : SpatialCellIndex, energy j := by
    rw [Finset.mul_sum]
    calc
      (∑ j : SpatialCellIndex, (threshold + epsilon) * transverse j) ≤
          ∑ j : SpatialCellIndex,
            (defect j +
              (threshold + epsilon) * (4 * (epsilon / threshold)) * energy j) :=
        Finset.sum_le_sum fun j _ ↦ hcell j
      _ = (∑ j : SpatialCellIndex, defect j) +
          (threshold + epsilon) * (4 * (epsilon / threshold)) *
            ∑ j : SpatialCellIndex, energy j := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
  have henergy : (∑ j : SpatialCellIndex, energy j) ≤
      (125 * ‖torusCellCutoff‖ ^ 2) * globalEnergy := by
    simpa [energy, globalEnergy] using
      (squareDyadicPancakeBlock_energy_cover_sandwich
        (fullStrainFrame A hAsymm) N omega).2
  have hcoefficient :
      0 ≤ (threshold + epsilon) * (4 * (epsilon / threshold)) := by
    positivity
  calc
    (threshold + epsilon) *
        arbitraryDataSquareDyadicPancakeMisalignmentEnergy
          A hAsymm N omega ≤
      (threshold + epsilon) * (∑ j : SpatialCellIndex, transverse j) :=
        mul_le_mul_of_nonneg_left hcapture hgapNonneg
    _ ≤ (∑ j : SpatialCellIndex, defect j) +
        (threshold + epsilon) * (4 * (epsilon / threshold)) *
          ∑ j : SpatialCellIndex, energy j := hsum
    _ ≤ (∑ j : SpatialCellIndex, defect j) +
        (threshold + epsilon) * (4 * (epsilon / threshold)) *
          ((125 * ‖torusCellCutoff‖ ^ 2) * globalEnergy) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left henergy hcoefficient)
    _ = (∑ j : SpatialCellIndex, defect j) +
        (threshold + epsilon) * (4 * (epsilon / threshold)) *
          (125 * ‖torusCellCutoff‖ ^ 2) * globalEnergy := by ring

end PancakeConcreteWeightedFreezing
end NavierStokes
end FluidDynamics
end Mettapedia
