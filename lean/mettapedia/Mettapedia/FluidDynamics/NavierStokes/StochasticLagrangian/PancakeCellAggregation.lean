import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeTransverseEnergyCoercivity

/-!
# Finite-cell aggregation of the pancake coercivity dichotomy

This module packages the checked frozen-cell estimate and sums its separated
branch over an arbitrary finite family.  It also proves the generic
bounded-overlap integral lemma needed to replace a sum of local cell energies
by one global energy integral without a cell-count loss.

The construction of a scale-dependent spatial cover, and verification that
the Navier--Stokes strain oscillates by the required amount on each member,
remain separate analytic tasks.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeCellAggregation

open scoped BigOperators RealInnerProductSpace
open MeasureTheory
open PeriodicFourierTriad
open PancakeAlignmentDynamics
open PancakeComplexMisalignmentExpansion
open PancakeFiniteFourierBilinearTransfer
open PancakeFullStrainFrame
open PancakeMisalignmentEnergyBridge
open PancakePeriodicCoherentSplit
open PancakePhysicalFrameKernelTransfer
open PancakePhysicalMisalignmentSplit
open PancakeSquareDyadicSectorProjector
open PancakeStrainSpectralFrame
open PancakeTransverseEnergyCoercivity
open PancakeTransverseEnergyFreezing

local notation "R3" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] Classical.propDecidable

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- All algebraic data and checked side conditions intended for one frozen
spatial cell.  `A` is the strain selecting the sector at the observation
point and `B` is the strain frozen on the cell.  A region or cutoff is not
part of this structure; connecting its global finite reconstruction to a
localized field is the subsequent analytic step. -/
structure FrozenPancakeCell (epsilon : ℝ) where
  A : R3 →L[ℝ] R3
  B : R3 →L[ℝ] R3
  A_symmetric : ∀ u v : R3, inner ℝ u (A v) = inner ℝ (A u) v
  B_symmetric : ∀ u v : R3, inner ℝ u (B v) = inner ℝ (B u) v
  strain_close : ‖A - B‖ ≤ epsilon
  N : ℕ
  two_le_N : 2 ≤ N
  support : Finset Wavevector
  omega : FourierVelocity
  divergence_free : ∀ k, modeDot k (omega k) = 0

/-- The union of the two top-eigenvalue collision bands for a cell. -/
def smallTopGap {epsilon : ℝ} (threshold : ℝ)
    (c : FrozenPancakeCell epsilon) : Prop :=
  (orderedEigenframe c.B c.B_symmetric).eigenvalue 0 -
      (orderedEigenframe c.B c.B_symmetric).eigenvalue 1 <
        threshold + epsilon ∨
    (orderedEigenframe c.B c.B_symmetric).eigenvalue 0 -
      (orderedEigenframe c.B c.B_symmetric).eigenvalue 2 <
        threshold + epsilon

/-- Exact squared Fourier remainder on the physical square-dyadic sector of
one cell. -/
def cellRemainderEnergy {epsilon : ℝ}
    (c : FrozenPancakeCell epsilon) : ℝ :=
  ∑ k ∈ squareDyadicPancakeSectorModes
        (fullStrainFrame c.A c.A_symmetric) c.N c.support,
    complexEuclideanNormSq
      (complexMisalignmentChartComponent
        (orientedFrameWavevectorCoordinates
          (fullStrainFrame c.A c.A_symmetric) k)
        (orientedFrameComplexLinearMap
          (fullStrainFrame c.A c.A_symmetric) (c.omega k)))

/-- Integrated frozen-strain Rayleigh defect on one cell's finite sector. -/
def cellDefectEnergy {epsilon : ℝ}
    (c : FrozenPancakeCell epsilon) : ℝ :=
  ∫ x : UnitAddTorus (Fin 3),
    complexStrainDefect c.B c.B_symmetric
      (finiteFourierReconstruction
        (squareDyadicPancakeSectorModes
          (fullStrainFrame c.A c.A_symmetric) c.N c.support)
        c.omega x)

/-- Full finite-sector energy appearing in the frame-freezing error. -/
def cellFullEnergy {epsilon : ℝ}
    (c : FrozenPancakeCell epsilon) : ℝ :=
  ∫ x : UnitAddTorus (Fin 3),
    complexEuclideanNormSq
      (finiteFourierReconstruction
        (squareDyadicPancakeSectorModes
          (fullStrainFrame c.A c.A_symmetric) c.N c.support)
        c.omega x)

theorem cellDefectEnergy_nonneg {epsilon : ℝ}
    (c : FrozenPancakeCell epsilon) :
    0 ≤ cellDefectEnergy c := by
  unfold cellDefectEnergy
  exact integral_nonneg fun x ↦
    complexStrainDefect_nonneg c.B c.B_symmetric _

theorem cellFullEnergy_nonneg {epsilon : ℝ}
    (c : FrozenPancakeCell epsilon) :
    0 ≤ cellFullEnergy c := by
  unfold cellFullEnergy
  exact integral_nonneg fun x ↦ complexEuclideanNormSq_nonneg _

/-- The cell theorem in packaged form: a top-gap collision, or the exact
coercive remainder estimate. -/
theorem smallTopGap_or_cellRemainder_le
    {epsilon threshold : ℝ} (hthreshold : 0 < threshold)
    (hepsilon : 0 ≤ epsilon) (c : FrozenPancakeCell epsilon) :
    smallTopGap threshold c ∨
      (threshold + epsilon) * cellRemainderEnergy c ≤
        cellDefectEnergy c +
          (threshold + epsilon) * (4 * (epsilon / threshold)) *
            cellFullEnergy c := by
  rcases smallFrozenGap_or_gap_mul_sectorMisalignment_le_defect
      c.A c.B c.A_symmetric c.B_symmetric epsilon threshold
      hthreshold hepsilon c.strain_close c.two_le_N c.support c.omega
      c.divergence_free with hgap₁ | hgap₂ | hbound
  · exact Or.inl (Or.inl hgap₁)
  · exact Or.inl (Or.inr hgap₂)
  · exact Or.inr (by
      simpa [cellRemainderEnergy, cellDefectEnergy, cellFullEnergy] using
        hbound)

/-- **Separated-cell aggregation.**  Sum the exact coercive estimate over all
cells outside the top-gap collision band.  No factor depending on the number
of cells is introduced. -/
theorem sum_separated_cellRemainder_le
    {ι : Type*} [DecidableEq ι]
    {epsilon threshold : ℝ} (hthreshold : 0 < threshold)
    (hepsilon : 0 ≤ epsilon) (cells : Finset ι)
    (cell : ι → FrozenPancakeCell epsilon) :
    (threshold + epsilon) *
        (∑ i ∈ cells.filter (fun i ↦ ¬ smallTopGap threshold (cell i)),
          cellRemainderEnergy (cell i)) ≤
      (∑ i ∈ cells.filter (fun i ↦ ¬ smallTopGap threshold (cell i)),
          cellDefectEnergy (cell i)) +
        (threshold + epsilon) * (4 * (epsilon / threshold)) *
          ∑ i ∈ cells.filter (fun i ↦ ¬ smallTopGap threshold (cell i)),
            cellFullEnergy (cell i) := by
  let separated := cells.filter (fun i ↦ ¬ smallTopGap threshold (cell i))
  have hcell : ∀ i ∈ separated,
      (threshold + epsilon) * cellRemainderEnergy (cell i) ≤
        cellDefectEnergy (cell i) +
          (threshold + epsilon) * (4 * (epsilon / threshold)) *
            cellFullEnergy (cell i) := by
    intro i hi
    have hnsmall : ¬ smallTopGap threshold (cell i) :=
      (Finset.mem_filter.mp hi).2
    rcases smallTopGap_or_cellRemainder_le hthreshold hepsilon (cell i) with
      hsmall | hbound
    · exact False.elim (hnsmall hsmall)
    · exact hbound
  change (threshold + epsilon) *
      (∑ i ∈ separated, cellRemainderEnergy (cell i)) ≤
    (∑ i ∈ separated, cellDefectEnergy (cell i)) +
      (threshold + epsilon) * (4 * (epsilon / threshold)) *
        ∑ i ∈ separated, cellFullEnergy (cell i)
  rw [Finset.mul_sum]
  calc
    (∑ i ∈ separated,
        (threshold + epsilon) * cellRemainderEnergy (cell i)) ≤
        ∑ i ∈ separated,
          (cellDefectEnergy (cell i) +
            (threshold + epsilon) * (4 * (epsilon / threshold)) *
              cellFullEnergy (cell i)) := by
      exact Finset.sum_le_sum fun i hi ↦ hcell i hi
    _ = (∑ i ∈ separated, cellDefectEnergy (cell i)) +
        (threshold + epsilon) * (4 * (epsilon / threshold)) *
          ∑ i ∈ separated, cellFullEnergy (cell i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- A form with global sums on the right.  Nonnegativity of the Rayleigh
defect and energy permits extending the separated-cell sums to the whole
finite family. -/
theorem sum_separated_cellRemainder_le_all_cellEnergy
    {ι : Type*} [DecidableEq ι]
    {epsilon threshold : ℝ} (hthreshold : 0 < threshold)
    (hepsilon : 0 ≤ epsilon) (cells : Finset ι)
    (cell : ι → FrozenPancakeCell epsilon) :
    (threshold + epsilon) *
        (∑ i ∈ cells.filter (fun i ↦ ¬ smallTopGap threshold (cell i)),
          cellRemainderEnergy (cell i)) ≤
      (∑ i ∈ cells, cellDefectEnergy (cell i)) +
        (threshold + epsilon) * (4 * (epsilon / threshold)) *
          ∑ i ∈ cells, cellFullEnergy (cell i) := by
  let separated := cells.filter (fun i ↦ ¬ smallTopGap threshold (cell i))
  have hbase := sum_separated_cellRemainder_le
    hthreshold hepsilon cells cell
  have hsubset : separated ⊆ cells := Finset.filter_subset _ _
  have hdefect :
      (∑ i ∈ separated, cellDefectEnergy (cell i)) ≤
        ∑ i ∈ cells, cellDefectEnergy (cell i) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun i _ _ ↦ cellDefectEnergy_nonneg (cell i))
  have hfull :
      (∑ i ∈ separated, cellFullEnergy (cell i)) ≤
        ∑ i ∈ cells, cellFullEnergy (cell i) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun i _ _ ↦ cellFullEnergy_nonneg (cell i))
  have hcoefficient :
      0 ≤ (threshold + epsilon) * (4 * (epsilon / threshold)) := by
    positivity
  change (threshold + epsilon) *
      (∑ i ∈ separated, cellRemainderEnergy (cell i)) ≤
    (∑ i ∈ cells, cellDefectEnergy (cell i)) +
      (threshold + epsilon) * (4 * (epsilon / threshold)) *
        ∑ i ∈ cells, cellFullEnergy (cell i)
  exact hbase.trans (add_le_add hdefect
    (mul_le_mul_of_nonneg_left hfull hcoefficient))

/-! ## Generic bounded-overlap transfer -/

/-- The pointwise sum of restrictions of a nonnegative function is bounded
by the overlap multiplicity times that function. -/
theorem sum_indicator_le_overlap_mul
    {X ι : Type*} [DecidableEq ι]
    (cells : Finset ι) (region : ι → Set X) (f : X → ℝ) (overlap : ℕ)
    (hf : ∀ x, 0 ≤ f x)
    (hoverlap : ∀ x, (cells.filter fun i ↦ x ∈ region i).card ≤ overlap)
    (x : X) :
    (∑ i ∈ cells, (region i).indicator f x) ≤ overlap * f x := by
  classical
  rw [Finset.sum_indicator_eq_sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast hoverlap x) (hf x)

/-- **Bounded-overlap integral lemma.**  For a finite measurable family with
pointwise multiplicity at most `overlap`, the sum of local integrals of a
nonnegative integrable density is bounded by `overlap` times its global
integral. -/
theorem sum_setIntegral_le_overlap_mul_integral
    {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
    {μ : Measure X} (cells : Finset ι) (region : ι → Set X)
    (f : X → ℝ) (overlap : ℕ)
    (hf : Integrable f μ) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hregion : ∀ i ∈ cells, MeasurableSet (region i))
    (hoverlap : ∀ x, (cells.filter fun i ↦ x ∈ region i).card ≤ overlap) :
    (∑ i ∈ cells, ∫ x in region i, f x ∂μ) ≤
      overlap * ∫ x, f x ∂μ := by
  classical
  have hindicator : ∀ i ∈ cells, Integrable ((region i).indicator f) μ := by
    intro i hi
    exact hf.indicator (hregion i hi)
  calc
    (∑ i ∈ cells, ∫ x in region i, f x ∂μ) =
        ∫ x, ∑ i ∈ cells, (region i).indicator f x ∂μ := by
      rw [integral_finsetSum cells (fun i hi ↦ hindicator i hi)]
      apply Finset.sum_congr rfl
      intro i hi
      exact (integral_indicator (hregion i hi)).symm
    _ ≤ ∫ x, overlap * f x ∂μ := by
      apply integral_mono
      · exact integrable_finsetSum cells fun i hi ↦ hindicator i hi
      · exact hf.const_mul overlap
      · exact fun x ↦ sum_indicator_le_overlap_mul
          cells region f overlap hf_nonneg hoverlap x
    _ = overlap * ∫ x, f x ∂μ := by
      rw [integral_const_mul]

/-- Smooth-partition counterpart of the set-overlap estimate.  Each local
density may vary with the cell, provided it is dominated by one global
nonnegative density. -/
theorem sum_weight_mul_local_le_overlap_mul
    {X ι : Type*} [DecidableEq ι]
    (cells : Finset ι) (weight localDensity : ι → X → ℝ)
    (global : X → ℝ) (overlap : ℝ)
    (hweight : ∀ i ∈ cells, ∀ x, 0 ≤ weight i x)
    (hlocal : ∀ i ∈ cells, ∀ x, localDensity i x ≤ global x)
    (hglobal : ∀ x, 0 ≤ global x)
    (hsum : ∀ x, (∑ i ∈ cells, weight i x) ≤ overlap)
    (x : X) :
    (∑ i ∈ cells, weight i x * localDensity i x) ≤ overlap * global x := by
  calc
    (∑ i ∈ cells, weight i x * localDensity i x) ≤
        ∑ i ∈ cells, weight i x * global x := by
      exact Finset.sum_le_sum fun i hi ↦
        mul_le_mul_of_nonneg_left (hlocal i hi x) (hweight i hi x)
    _ = (∑ i ∈ cells, weight i x) * global x := by
      rw [Finset.sum_mul]
    _ ≤ overlap * global x :=
      mul_le_mul_of_nonneg_right (hsum x) (hglobal x)

/-- **Smooth bounded-overlap integral lemma.**  A finite family of
nonnegative partition weights with total weight at most `overlap` transfers
cellwise densities dominated by `global` to one global integral. -/
theorem sum_integral_weight_mul_local_le_overlap_mul_integral
    {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
    {μ : Measure X} (cells : Finset ι)
    (weight localDensity : ι → X → ℝ)
    (global : X → ℝ) (overlap : ℝ)
    (hprod : ∀ i ∈ cells,
      Integrable (fun x ↦ weight i x * localDensity i x) μ)
    (hglobalInt : Integrable global μ)
    (hweight : ∀ i ∈ cells, ∀ x, 0 ≤ weight i x)
    (hlocal : ∀ i ∈ cells, ∀ x, localDensity i x ≤ global x)
    (hglobal : ∀ x, 0 ≤ global x)
    (hsum : ∀ x, (∑ i ∈ cells, weight i x) ≤ overlap) :
    (∑ i ∈ cells, ∫ x, weight i x * localDensity i x ∂μ) ≤
      overlap * ∫ x, global x ∂μ := by
  calc
    (∑ i ∈ cells, ∫ x, weight i x * localDensity i x ∂μ) =
        ∫ x, ∑ i ∈ cells, weight i x * localDensity i x ∂μ := by
      exact (integral_finsetSum cells hprod).symm
    _ ≤ ∫ x, overlap * global x ∂μ := by
      apply integral_mono
      · exact integrable_finsetSum cells hprod
      · exact hglobalInt.const_mul overlap
      · exact fun x ↦ sum_weight_mul_local_le_overlap_mul
          cells weight localDensity global overlap hweight hlocal hglobal hsum x
    _ = overlap * ∫ x, global x ∂μ := by
      rw [integral_const_mul]

end PancakeCellAggregation
end NavierStokes
end FluidDynamics
end Mettapedia
