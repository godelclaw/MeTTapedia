import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeArbitraryDataBlocks
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeTransverseEnergyCoercivity

/-!
# Exact pancake/misalignment splitting on arbitrary-data dyadic blocks

`PancakeArbitraryDataBlocks` constructs complete finite frequency blocks from
an arbitrary periodic Fourier field.  This module connects those blocks to the
exact physical stretching decomposition and the frozen-strain coercivity
theorems.  Thus the caller no longer supplies an ambient finite support for
either the coherent/misaligned split or its transverse-energy control.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeArbitraryDataMisalignment

open scoped BigOperators RealInnerProductSpace
open MeasureTheory
open PeriodicFourierTriad
open PancakeBilinearPeriodization
open PancakePeriodicCoherentSplit
open PancakeSmoothCoherentSymbol
open PancakeFrameCovariance
open PancakePhysicalFrameKernelTransfer
open PancakeAnnularPhysicalFrameTransfer
open PancakeFiniteFourierBilinearTransfer
open PancakeComplexCoherentPDEIdentification
open PancakeFullStrainFrame
open PancakeMisalignmentEnergyBridge
open PancakePhysicalMisalignmentSplit
open PancakeSquareDyadicSectorProjector
open PancakeStrainSpectralFrame
open PancakeTransverseEnergyCoercivity
open PancakeArbitraryDataBlocks

local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Full physical stretching sum on the complete square-dyadic pancake block
of arbitrary Fourier coefficient data. -/
def arbitraryDataSquareDyadicPancakeStretchingSum
    (F : OrientedFrameEquiv) (N : ℕ)
    (omega eta : FourierVelocity) (x : BilinearSpatialTorus) : ComplexVec3 :=
  physicalFiniteFramePancakeStretchingSum F N
    (squareDyadicShellModes N) (squareDyadicShellModes N) omega eta x

/-- Exact three-term misalignment remainder on that complete block. -/
def arbitraryDataSquareDyadicPancakeMisalignmentSum
    (F : OrientedFrameEquiv) (N : ℕ)
    (omega eta : FourierVelocity) (x : BilinearSpatialTorus) : ComplexVec3 :=
  physicalFiniteFrameMisalignmentPancakeStretchingSum F N
    (squareDyadicShellModes N) (squareDyadicShellModes N) omega eta x

/-- The arbitrary-data block has the exact physical coherent/misaligned
decomposition.  Finiteness comes from the shell projector, not from the
ambient field. -/
theorem arbitraryDataSquareDyadicPancakeStretchingSum_eq_kernel_add_misalignment
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 2 ≤ N)
    (omega eta : FourierVelocity) (x : BilinearSpatialTorus) :
    arbitraryDataSquareDyadicPancakeStretchingSum F N omega eta x =
      physicalOrientedFrameAnnularSquareDyadicKernelAction F N
        (squareDyadicPancakeBlock F N omega)
        (squareDyadicPancakeBlock F N eta) x +
      arbitraryDataSquareDyadicPancakeMisalignmentSum F N omega eta x := by
  simpa [arbitraryDataSquareDyadicPancakeStretchingSum,
    arbitraryDataSquareDyadicPancakeMisalignmentSum,
    squareDyadicPancakeBlock, squareDyadicPancakeModes,
    squareDyadicPancakeSectorProjection] using
      physicalFiniteFramePancakeStretchingSum_eq_kernel_add_misalignment
        F hN (squareDyadicShellModes N) (squareDyadicShellModes N)
          omega eta x

/-- The coherent share of every complete arbitrary-data block has the
cardinality-free `C/N` bound, leaving precisely the exact misalignment
remainder. -/
theorem exists_uniform_arbitraryDataSquareDyadicPancakeSplit_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : OrientedFrameEquiv) (N : ℕ), 2 ≤ N →
      ∀ (omega eta : FourierVelocity) (x : BilinearSpatialTorus),
        ‖arbitraryDataSquareDyadicPancakeStretchingSum
            F N omega eta x‖ ≤
          243 * (C / N) *
              squareDyadicPancakeCoefficientMass F N omega *
              squareDyadicPancakeCoefficientMass F N eta +
            ‖arbitraryDataSquareDyadicPancakeMisalignmentSum
              F N omega eta x‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_physicalPancakeSplit_bilinear_bound
  refine ⟨C, hC, ?_⟩
  intro F N hN omega eta x
  simpa [arbitraryDataSquareDyadicPancakeStretchingSum,
    arbitraryDataSquareDyadicPancakeMisalignmentSum,
    squareDyadicPancakeBlock, squareDyadicPancakeModes,
    squareDyadicPancakeSectorProjection] using
      hbound F N hN
        (squareDyadicShellModes N) (squareDyadicShellModes N)
        omega eta x
        (squareDyadicPancakeCoefficientMass F N omega)
        (squareDyadicPancakeCoefficientMass F N eta)
        (norm_squareDyadicPancakeBlock_le F N omega)
        (norm_squareDyadicPancakeBlock_le F N eta)

/-- Squared coefficient energy of the coherent-line remainder on the complete
square-dyadic pancake block selected by a frozen strain. -/
def arbitraryDataSquareDyadicPancakeMisalignmentEnergy
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ u v : R3, inner ℝ u (S v) = inner ℝ (S u) v)
    (N : ℕ) (omega : FourierVelocity) : ℝ :=
  ∑ k ∈ squareDyadicPancakeModes (fullStrainFrame S hSsymm) N,
    complexEuclideanNormSq
      (complexMisalignmentChartComponent
        (orientedFrameWavevectorCoordinates
          (fullStrainFrame S hSsymm) k)
        (orientedFrameComplexLinearMap
          (fullStrainFrame S hSsymm) (omega k)))

/-- The complete arbitrary-data pancake block inherits the exact
transverse-energy estimate with no ambient finite-support premise. -/
theorem arbitraryDataSquareDyadicPancakeMisalignmentEnergy_le_integral
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ u v : R3, inner ℝ u (S v) = inner ℝ (S u) v)
    {N : ℕ} (hN : 2 ≤ N) (omega : FourierVelocity)
    (hdiv : ∀ k, modeDot k (omega k) = 0) :
    arbitraryDataSquareDyadicPancakeMisalignmentEnergy
        S hSsymm N omega ≤
      ∫ x : UnitAddTorus (Fin 3),
        complexTransverseEnergyEx
          (finiteFourierReconstruction
            (squareDyadicPancakeModes (fullStrainFrame S hSsymm) N)
            (fun k ↦ orientedFrameComplexLinearMap
              (fullStrainFrame S hSsymm) (omega k)) x) := by
  simpa [arbitraryDataSquareDyadicPancakeMisalignmentEnergy,
    squareDyadicPancakeModes] using
      fullStrainFrame_sectorModes_sum_complexMisalignment_le_integral
        S hSsymm hN (squareDyadicShellModes N) omega hdiv

/-- Time profile of the exact coefficient misalignment energy in one frozen
strain frame and one complete square-dyadic block. -/
def arbitraryDataSquareDyadicPancakeMisalignmentEnergyTimeProfile
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ u v : R3, inner ℝ u (S v) = inner ℝ (S u) v)
    (N : ℕ) (omega : ℝ → FourierVelocity) (t : ℝ) : ℝ :=
  arbitraryDataSquareDyadicPancakeMisalignmentEnergy
    S hSsymm N (omega t)

/-- In a frozen frame, coefficientwise time continuity makes the exact
misalignment-energy profile continuous. -/
theorem continuous_arbitraryDataSquareDyadicPancakeMisalignmentEnergyTimeProfile
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ u v : R3, inner ℝ u (S v) = inner ℝ (S u) v)
    (N : ℕ) (omega : ℝ → FourierVelocity)
    (homega : ∀ k i, Continuous (fun t ↦ omega t k i)) :
    Continuous
      (arbitraryDataSquareDyadicPancakeMisalignmentEnergyTimeProfile
        S hSsymm N omega) := by
  unfold arbitraryDataSquareDyadicPancakeMisalignmentEnergyTimeProfile
    arbitraryDataSquareDyadicPancakeMisalignmentEnergy
    complexEuclideanNormSq complexMisalignmentChartComponent
    complexCoherentChartProject complexCoherentChartCoeff
  apply continuous_finsetSum
  intro k hk
  apply Continuous.add
  · apply Continuous.add <;>
      exact Complex.continuous_normSq.comp (by fun_prop)
  · exact Complex.continuous_normSq.comp (by fun_prop)

/-- Consequently every frozen-frame complete-block misalignment profile is
integrable on a finite time interval. -/
theorem intervalIntegrable_arbitraryDataSquareDyadicPancakeMisalignmentEnergyTimeProfile
    (S : R3 →L[ℝ] R3)
    (hSsymm : ∀ u v : R3, inner ℝ u (S v) = inner ℝ (S u) v)
    (N : ℕ) (omega : ℝ → FourierVelocity)
    (homega : ∀ k i, Continuous (fun t ↦ omega t k i))
    (a b : ℝ) :
    IntervalIntegrable
      (arbitraryDataSquareDyadicPancakeMisalignmentEnergyTimeProfile
        S hSsymm N omega) volume a b :=
  (continuous_arbitraryDataSquareDyadicPancakeMisalignmentEnergyTimeProfile
    S hSsymm N omega homega).intervalIntegrable a b

/-- **Complete-block frozen-strain dichotomy.**  Either the frozen strain has
a small top spectral gap, or the exact arbitrary-data pancake misalignment
energy is controlled by the frozen Rayleigh defect and the explicit
frame-freezing error. -/
theorem arbitraryDataSquareDyadicPancake_smallFrozenGap_or_misalignment_le
    (A B : R3 →L[ℝ] R3)
    (hAsymm : ∀ u v : R3, inner ℝ u (A v) = inner ℝ (A u) v)
    (hBsymm : ∀ u v : R3, inner ℝ u (B v) = inner ℝ (B u) v)
    (epsilon threshold : ℝ) (hthreshold : 0 < threshold)
    (hepsilon : 0 ≤ epsilon) (hAB : ‖A - B‖ ≤ epsilon)
    {N : ℕ} (hN : 2 ≤ N) (omega : FourierVelocity)
    (hdiv : ∀ k, modeDot k (omega k) = 0) :
    (orderedEigenframe B hBsymm).eigenvalue 0 -
        (orderedEigenframe B hBsymm).eigenvalue 1 <
          threshold + epsilon ∨
      (orderedEigenframe B hBsymm).eigenvalue 0 -
        (orderedEigenframe B hBsymm).eigenvalue 2 <
          threshold + epsilon ∨
      (threshold + epsilon) *
          arbitraryDataSquareDyadicPancakeMisalignmentEnergy
            A hAsymm N omega ≤
        (∫ x : UnitAddTorus (Fin 3),
          complexStrainDefect B hBsymm
            (squareDyadicPancakeBlock
              (fullStrainFrame A hAsymm) N omega x)) +
        (threshold + epsilon) * (4 * (epsilon / threshold)) *
          ∫ x : UnitAddTorus (Fin 3),
            complexEuclideanNormSq
              (squareDyadicPancakeBlock
                (fullStrainFrame A hAsymm) N omega x) := by
  simpa [arbitraryDataSquareDyadicPancakeMisalignmentEnergy,
    squareDyadicPancakeBlock, squareDyadicPancakeModes] using
      smallFrozenGap_or_gap_mul_sectorMisalignment_le_defect
        A B hAsymm hBsymm epsilon threshold hthreshold hepsilon hAB hN
          (squareDyadicShellModes N) omega hdiv

end PancakeArbitraryDataMisalignment
end NavierStokes
end FluidDynamics
end Mettapedia
