import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAnnularPhysicalFrameTransfer

/-!
# Concrete finite-Fourier pancake-sector projector

This module turns the normalized annular predicate into an actual mode
selector for finite periodic Fourier fields.  It also identifies the
six-dimensional frozen-frame chart with the pair of independently selected
three-dimensional mode charts.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeAnnularSectorProjector

open PeriodicFourierTriad
open PancakeBilinearPeriodization
open PancakePeriodicCoherentSplit
open PancakeRealCoherentPairEstimate
open PancakeSmoothCoherentSymbol
open PancakeSmoothCoherentStretchSymbol
open PancakeFrameCovariance
open PancakeDyadicKernelScaling
open PancakeFrozenFrameKernelTransfer
open PancakePhysicalFrameKernelTransfer
open PancakeAnnularChartCutoff
open PancakeAnnularMultiplierAssembly
open PancakeAnnularFrozenFrameTransfer
open PancakeAnnularPhysicalFrameTransfer

/-- One periodic wavevector in real Euclidean coordinates. -/
def euclideanWavevectorOfWavevector (k : Wavevector) : EuclideanWavevector :=
  WithLp.toLp 2 ![(k 0 : ℝ), (k 1 : ℝ), (k 2 : ℝ)]

/-- Square-dyadic normalized coordinates of one mode in an oriented frame. -/
def orientedFrameSquareDyadicNormalizedMode
    (F : OrientedFrameEquiv) (N : ℕ) (k : Wavevector) : RealVec3 :=
  let ξ := orientedFrameEuclideanLinearIsometryEquiv F
    (euclideanWavevectorOfWavevector k)
  ((ξ 0) / N, (ξ 1) / N, (ξ 2) / (N ^ 2))

theorem frequencyPairSplit_euclideanFrequencyPairOf_pairWavevector
    (k l : Wavevector) :
    frequencyPairSplitLinearIsometryEquiv
        (euclideanFrequencyPairOfWavevector (pairWavevector k l)) =
      WithLp.toLp 2
        (euclideanWavevectorOfWavevector k,
          euclideanWavevectorOfWavevector l) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    funext i
    fin_cases i <;>
      simp [frequencyPairSplitLinearIsometryEquiv,
        euclideanFrequencyPairOfWavevector, pairWavevector,
        euclideanWavevectorOfWavevector, Fin.append,
        PiLp.sumPiLpEquivProdLpPiLp] <;> rfl
  · apply WithLp.ofLp_injective 2
    funext i
    fin_cases i <;>
      simp [frequencyPairSplitLinearIsometryEquiv,
        euclideanFrequencyPairOfWavevector, pairWavevector,
        euclideanWavevectorOfWavevector, Fin.append,
        PiLp.sumPiLpEquivProdLpPiLp] <;> rfl

theorem frequencyPairSplit_orientedFrame_pairWavevector
    (F : OrientedFrameEquiv) (k l : Wavevector) :
    frequencyPairSplitLinearIsometryEquiv
        (orientedFrameFrequencyPairLinearIsometryEquiv F
          (euclideanFrequencyPairOfWavevector (pairWavevector k l))) =
      WithLp.toLp 2
        (orientedFrameEuclideanLinearIsometryEquiv F
            (euclideanWavevectorOfWavevector k),
          orientedFrameEuclideanLinearIsometryEquiv F
            (euclideanWavevectorOfWavevector l)) := by
  simp [orientedFrameFrequencyPairLinearIsometryEquiv,
    pairFrameLinearIsometryEquiv,
    frequencyPairSplit_euclideanFrequencyPairOf_pairWavevector]

theorem euclideanToFrequencyPairEquiv_anisotropicReciprocalScaling
    (delta : ℝ) (xi : EuclideanFrequencyPair) :
    euclideanToFrequencyPairEquiv
        (anisotropicFrequencyPairReciprocalScaling delta xi) =
      ((delta⁻¹ * xi 0, delta⁻¹ * xi 1, xi 2),
        (delta⁻¹ * xi 3, delta⁻¹ * xi 4, xi 5)) := by
  apply euclideanToFrequencyPairEquiv.symm.injective
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  apply frequencyPairToBilinearKernelCoordinates.injective
  rw [frequencyPairToBilinearKernelCoordinates_reciprocalScaling,
    frequencyPairToBilinearKernelCoordinates_apply,
    frequencyPairToBilinearKernelCoordinates_apply]
  ext i <;> fin_cases i <;>
    simp [euclideanToFrequencyPairEquiv,
      euclideanToFrequencyPairLinearEquiv]

/-- The six-dimensional diagonal frame chart is exactly the pair of the two
independent three-dimensional mode charts. -/
theorem frozenFrameSquareDyadicFrequencyPairChart_orientedFrame
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 0 < N) (k l : Wavevector) :
    frozenFrameSquareDyadicFrequencyPairChart
        (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l =
      (orientedFrameSquareDyadicNormalizedMode F N k,
        orientedFrameSquareDyadicNormalizedMode F N l) := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [frozenFrameSquareDyadicFrequencyPairChart,
    frozenFrameSquareDyadicEuclideanFrequencyPair,
    euclideanToFrequencyPairEquiv_anisotropicReciprocalScaling]
  let X := orientedFrameFrequencyPairLinearIsometryEquiv F
    (euclideanFrequencyPairOfWavevector (pairWavevector k l))
  have hsplit : frequencyPairSplitLinearIsometryEquiv X =
      WithLp.toLp 2
        (orientedFrameEuclideanLinearIsometryEquiv F
            (euclideanWavevectorOfWavevector k),
          orientedFrameEuclideanLinearIsometryEquiv F
            (euclideanWavevectorOfWavevector l)) :=
    frequencyPairSplit_orientedFrame_pairWavevector F k l
  have h0 := congrArg
    (fun q : WithLp 2 (EuclideanWavevector × EuclideanWavevector) ↦
      q.ofLp.1.ofLp 0) hsplit
  have h1 := congrArg
    (fun q : WithLp 2 (EuclideanWavevector × EuclideanWavevector) ↦
      q.ofLp.1.ofLp 1) hsplit
  have h2 := congrArg
    (fun q : WithLp 2 (EuclideanWavevector × EuclideanWavevector) ↦
      q.ofLp.1.ofLp 2) hsplit
  have h3 := congrArg
    (fun q : WithLp 2 (EuclideanWavevector × EuclideanWavevector) ↦
      q.ofLp.2.ofLp 0) hsplit
  have h4 := congrArg
    (fun q : WithLp 2 (EuclideanWavevector × EuclideanWavevector) ↦
      q.ofLp.2.ofLp 1) hsplit
  have h5 := congrArg
    (fun q : WithLp 2 (EuclideanWavevector × EuclideanWavevector) ↦
      q.ofLp.2.ofLp 2) hsplit
  simp [frequencyPairSplitLinearIsometryEquiv] at h0 h1 h2 h3 h4 h5
  have h0' : X 0 =
      orientedFrameEuclideanLinearIsometryEquiv F
        (euclideanWavevectorOfWavevector k) 0 := by
    exact h0
  have h1' : X 1 =
      orientedFrameEuclideanLinearIsometryEquiv F
        (euclideanWavevectorOfWavevector k) 1 := by
    exact h1
  have h2' : X 2 =
      orientedFrameEuclideanLinearIsometryEquiv F
        (euclideanWavevectorOfWavevector k) 2 := by
    exact h2
  have h3' : X 3 =
      orientedFrameEuclideanLinearIsometryEquiv F
        (euclideanWavevectorOfWavevector l) 0 := by
    exact h3
  have h4' : X 4 =
      orientedFrameEuclideanLinearIsometryEquiv F
        (euclideanWavevectorOfWavevector l) 1 := by
    exact h4
  have h5' : X 5 =
      orientedFrameEuclideanLinearIsometryEquiv F
        (euclideanWavevectorOfWavevector l) 2 := by
    exact h5
  change
    (((((1 : ℝ) / N)⁻¹) * ((((N : ℝ) ^ 2)⁻¹) • X) 0,
        (((1 : ℝ) / N)⁻¹) * ((((N : ℝ) ^ 2)⁻¹) • X) 1,
        ((((N : ℝ) ^ 2)⁻¹) • X) 2),
      ((((1 : ℝ) / N)⁻¹) * ((((N : ℝ) ^ 2)⁻¹) • X) 3,
        (((1 : ℝ) / N)⁻¹) * ((((N : ℝ) ^ 2)⁻¹) • X) 4,
        ((((N : ℝ) ^ 2)⁻¹) • X) 5)) = _
  ext <;>
    simp [orientedFrameSquareDyadicNormalizedMode,
      h0', h1', h2', h3', h4', h5'] <;>
    field_simp [hNR]

/-- The finite set of modes lying in the full normalized pancake annulus of
the chosen oriented frame and square-dyadic scale. -/
def annularSectorModes (F : OrientedFrameEquiv) (N : ℕ)
    (support : Finset Wavevector) : Finset Wavevector := by
  classical
  exact support.filter fun k ↦
    InNormalizedPancakeAnnulus
      (orientedFrameSquareDyadicNormalizedMode F N k)

theorem mem_annularSectorModes_iff
    (F : OrientedFrameEquiv) (N : ℕ) (support : Finset Wavevector)
    (k : Wavevector) :
    k ∈ annularSectorModes F N support ↔
      k ∈ support ∧ InNormalizedPancakeAnnulus
        (orientedFrameSquareDyadicNormalizedMode F N k) := by
  simp [annularSectorModes]

/-- Concrete sharp finite-Fourier pancake-sector projection. -/
def annularSectorProjection (F : OrientedFrameEquiv) (N : ℕ)
    (support : Finset Wavevector) (omega : FourierVelocity) :
    BilinearSpatialTorus → ComplexVec3 :=
  finiteFourierReconstruction (annularSectorModes F N support) omega

/-- The selected supports automatically discharge the full-annulus hypothesis
of the exact physical kernel formula. -/
theorem physicalAnnularAction_on_sectorProjections_eq_coherent
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus) :
    physicalOrientedFrameAnnularSquareDyadicKernelAction F N
        (annularSectorProjection F N s omega)
        (annularSectorProjection F N t eta) x =
      orientedFrameInverseComplexLinearMap F
        (∑ k ∈ annularSectorModes F N s,
          ∑ l ∈ annularSectorModes F N t,
          (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
            (((((1 : ℝ) / N) : ℂ)) •
              coherentProjectedNormalizedStretch ((1 : ℝ) / N)
                (frozenFrameSquareDyadicFrequencyPairChart
                  (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l)
                (orientedFrameComplexLinearMap F (omega k))
                (orientedFrameComplexLinearMap F (eta l)))) := by
  apply physicalOrientedFrameAnnularSquareDyadicKernelAction_eq_coherent
    F hN
  intro k hk l hl
  rw [frozenFrameSquareDyadicFrequencyPairChart_orientedFrame F
    (lt_of_lt_of_le (by norm_num) hN)]
  exact ⟨(mem_annularSectorModes_iff F N s k).mp hk |>.2,
    (mem_annularSectorModes_iff F N t l).mp hl |>.2⟩

end PancakeAnnularSectorProjector
end NavierStokes
end FluidDynamics
end Mettapedia
