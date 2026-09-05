import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicVorticityEquation

/-!
# Reality of the hard square-dyadic pancake block

The square-dyadic pancake selector depends only on squared radial and frame
coordinates.  It is therefore closed under `k ↦ -k`.  A real periodic
vorticity field has conjugate-symmetric Fourier coefficients, so the selected
finite reconstruction is itself real-valued.

This file proves both statements.  Consequently the coordinatewise-real-part
block used by the direction law agrees with the full complex reconstruction
embedded from real Euclidean space; taking real part loses no information for
physical Fourier data.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeBlockReality

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad
open PancakeConeDirectionDichotomy
open PancakeRealCoherentPairEstimate
open PancakeBilinearPeriodization
open PancakeFrameCovariance
open PancakePhysicalFrameKernelTransfer
open PancakeAnnularSectorProjector
open PancakeSquareDyadicSectorProjector
open PancakeArbitraryDataBlocks
open PancakePeriodicCoherentSplit
open PancakeTransverseEnergyFreezing
open PancakeDyadicDirectionEvolution

/-! ## Negation symmetry of the selector -/

theorem euclideanWavevectorOfWavevector_neg (k : Wavevector) :
    euclideanWavevectorOfWavevector (-k) =
      -euclideanWavevectorOfWavevector k := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i <;>
    simp [euclideanWavevectorOfWavevector]

theorem orientedFrameWavevectorCoordinates_neg
    (F : OrientedFrameEquiv) (k : Wavevector) :
    orientedFrameWavevectorCoordinates F (-k) =
      -orientedFrameWavevectorCoordinates F k := by
  unfold orientedFrameWavevectorCoordinates
  rw [euclideanWavevectorOfWavevector_neg, map_neg]
  rfl

theorem inRealSquarePancakeConeAnnulus_neg_iff
    (N : ℕ) (v : RealVec3) :
    InRealSquarePancakeConeAnnulus N (-v) ↔
      InRealSquarePancakeConeAnnulus N v := by
  obtain ⟨x, y, z⟩ := v
  simp [InRealSquarePancakeConeAnnulus,
    PancakeRealCoherentPairEstimate.normSq,
    PancakeRealCoherentPairEstimate.dot]

theorem inOrientedSquarePancakeConeAnnulus_neg_iff
    (F : OrientedFrameEquiv) (N : ℕ) (k : Wavevector) :
    InOrientedSquarePancakeConeAnnulus F N (-k) ↔
      InOrientedSquarePancakeConeAnnulus F N k := by
  unfold InOrientedSquarePancakeConeAnnulus
  rw [orientedFrameWavevectorCoordinates_neg,
    inRealSquarePancakeConeAnnulus_neg_iff]

theorem modeSquareNat_neg (k : Wavevector) :
    modeSquareNat (-k) = modeSquareNat k := by
  unfold modeSquareNat
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem mem_squareDyadicShellModes_neg_iff (N : ℕ) (k : Wavevector) :
    -k ∈ squareDyadicShellModes N ↔ k ∈ squareDyadicShellModes N := by
  rw [mem_squareDyadicShellModes_iff, mem_squareDyadicShellModes_iff,
    modeSquareNat_neg]

/-- The actual hard pancake mode set is closed under Fourier conjugation. -/
theorem mem_squareDyadicPancakeModes_neg_iff
    (F : OrientedFrameEquiv) (N : ℕ) (k : Wavevector) :
    -k ∈ squareDyadicPancakeModes F N ↔
      k ∈ squareDyadicPancakeModes F N := by
  rw [mem_squareDyadicPancakeModes_iff,
    mem_squareDyadicPancakeModes_iff,
    mem_squareDyadicShellModes_neg_iff,
    inOrientedSquarePancakeConeAnnulus_neg_iff]

/-! ## A generic real finite Fourier reconstruction -/

/-- A negation-closed finite Fourier set reconstructs a real field whenever
its coefficients obey the physical conjugate symmetry. -/
theorem finiteFourierReconstruction_conj_eq_self_of_neg_closed
    (s : Finset Wavevector) (omega : FourierVelocity)
    (hs : ∀ k, -k ∈ s ↔ k ∈ s)
    (hreal : ∀ k, omega (-k) = fun i ↦ conj (omega k i))
    (x : UnitAddTorus (Fin 3)) :
    (fun i ↦ conj (finiteFourierReconstruction s omega x i)) =
      finiteFourierReconstruction s omega x := by
  classical
  ext i
  unfold finiteFourierReconstruction
  simp only [Finset.sum_apply]
  change (starRingEnd ℂ)
      (∑ k ∈ s, UnitAddTorus.mFourier k x * omega k i) =
    ∑ k ∈ s, UnitAddTorus.mFourier k x * omega k i
  rw [map_sum]
  have hconj :
      (∑ k ∈ s,
          (starRingEnd ℂ) (UnitAddTorus.mFourier k x * omega k i)) =
        ∑ k ∈ s,
          UnitAddTorus.mFourier (-k) x * omega (-k) i := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_mul]
    simp only [starRingEnd_apply]
    rw [UnitAddTorus.mFourier_neg, hreal]
    rfl
  rw [hconj]
  exact Finset.sum_bij (fun k _hk ↦ -k)
    (fun k hk ↦ (hs k).mpr hk)
    (fun a _ha b _hb hab ↦ by
      simpa using congrArg Neg.neg hab)
    (fun b hb ↦ ⟨-b, (hs b).mpr hb, by simp⟩)
    (fun k _hk ↦ by simp)

/-- Every coordinate of such a reconstruction has zero imaginary part. -/
theorem finiteFourierReconstruction_im_eq_zero_of_neg_closed
    (s : Finset Wavevector) (omega : FourierVelocity)
    (hs : ∀ k, -k ∈ s ↔ k ∈ s)
    (hreal : ∀ k, omega (-k) = fun i ↦ conj (omega k i))
    (x : UnitAddTorus (Fin 3)) (i : Fin 3) :
    (finiteFourierReconstruction s omega x i).im = 0 := by
  have hself := congrFun
    (finiteFourierReconstruction_conj_eq_self_of_neg_closed
      s omega hs hreal x) i
  have him := congrArg Complex.im hself
  simp only [Complex.conj_im] at him
  linarith

/-! ## Specialization to the actual hard pancake block -/

/-- A physical conjugate-symmetric Fourier field has a genuinely real hard
square-dyadic pancake reconstruction. -/
theorem squareDyadicPancakeBlock_conj_eq_self
    (F : OrientedFrameEquiv) (N : ℕ) (omega : FourierVelocity)
    (hreal : ∀ k, omega (-k) = fun i ↦ conj (omega k i))
    (x : BilinearSpatialTorus) :
    (fun i ↦ conj (squareDyadicPancakeBlock F N omega x i)) =
      squareDyadicPancakeBlock F N omega x := by
  exact finiteFourierReconstruction_conj_eq_self_of_neg_closed
    (squareDyadicPancakeModes F N) omega
    (mem_squareDyadicPancakeModes_neg_iff F N) hreal x

theorem squareDyadicPancakeBlock_im_eq_zero
    (F : OrientedFrameEquiv) (N : ℕ) (omega : FourierVelocity)
    (hreal : ∀ k, omega (-k) = fun i ↦ conj (omega k i))
    (x : BilinearSpatialTorus) (i : Fin 3) :
    (squareDyadicPancakeBlock F N omega x i).im = 0 := by
  exact finiteFourierReconstruction_im_eq_zero_of_neg_closed
    (squareDyadicPancakeModes F N) omega
    (mem_squareDyadicPancakeModes_neg_iff F N) hreal x i

/-- Taking coordinatewise real part of the physical hard block loses no
information: complexifying it returns the original reconstruction. -/
theorem ofReal_squareDyadicPancakeRealBlock_eq
    (F : OrientedFrameEquiv) (N : ℕ) (omega : FourierVelocity)
    (hreal : ∀ k, omega (-k) = fun i ↦ conj (omega k i))
    (x : BilinearSpatialTorus) :
    (fun i ↦ ((squareDyadicPancakeRealBlock F N omega x i : ℝ) : ℂ)) =
      squareDyadicPancakeBlock F N omega x := by
  ext i
  apply Complex.ext
  · rfl
  · simp [squareDyadicPancakeBlock_im_eq_zero F N omega hreal x i]

end PancakeBlockReality
end NavierStokes
end FluidDynamics
end Mettapedia
