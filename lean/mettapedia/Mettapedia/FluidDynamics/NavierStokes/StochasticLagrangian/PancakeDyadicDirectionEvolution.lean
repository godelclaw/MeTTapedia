import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeArbitraryDataBlocks
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.DirectionEvolutionTilting
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeTransverseEnergyFreezing

/-!
# Direction evolution of the actual square-dyadic pancake block

The geometric coherence estimate and the direction-evolution calculation must
refer to the same object.  The former is already stated for the hard
square-dyadic pancake reconstruction, whereas the latter was previously stated
for an abstract real vector path.  This module joins those two levels.

At a fixed spatial observation point, differentiating every Fourier
coefficient differentiates the finite reconstruction term by term.  Taking
coordinatewise real parts is a continuous real-linear operation, so the actual
real pancake block has the reconstructed coefficient derivative.  If that
block is nonzero and factorizes as `r * xi`, its direction therefore satisfies
the exact transverse strain equation with one explicit residual:

`residual = reconstructed block derivative - r * S xi`.

This is an identity, not a regularity estimate.  It makes the remaining
Navier--Stokes burden precise on the very block entering the misalignment
functional: control the transverse part of this residual at the required
scale-critical strength.  Transport, diffusion, interscale transfer, and any
localization commutators must all be accounted for there rather than hidden in
an unrelated full-vorticity direction hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeDyadicDirectionEvolution

open PeriodicFourierTriad
open PancakeSmoothCoherentSymbol
open PancakePeriodicCoherentSplit
open PancakeTransverseEnergyFreezing
open PancakeArbitraryDataBlocks
open DirectionEvolutionTilting
open PancakeFrameCovariance
open PancakeBilinearPeriodization
open scoped RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-! ## Real-linear maps used by time differentiation -/

/-- Multiplication by a complex scalar, regarded as a continuous real-linear
map.  Time differentiation is over `ℝ`, even though Fourier coefficients are
complex. -/
def complexScalarSMulRealCLM (c : ℂ) :
    ComplexVec3 →L[ℝ] ComplexVec3 :=
  (c • ContinuousLinearMap.id ℂ ComplexVec3).restrictScalars ℝ

@[simp]
theorem complexScalarSMulRealCLM_apply (c : ℂ) (u : ComplexVec3) :
    complexScalarSMulRealCLM c u = c • u := by
  rfl

/-- Coordinatewise real part as a continuous real-linear map from the complex
Fourier carrier to Euclidean three-space. -/
def complexRealPartEuclideanCLM : ComplexVec3 →L[ℝ] R3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i ↦
      Complex.reCLM.comp
        (ContinuousLinearMap.proj i : ComplexVec3 →L[ℝ] ℂ)))

@[simp]
theorem complexRealPartEuclideanCLM_apply (u : ComplexVec3) :
    complexRealPartEuclideanCLM u = complexRealPartEuclidean u := by
  ext i
  rfl

/-! ## Differentiating the genuine finite reconstruction -/

/-- A finite Fourier reconstruction can be differentiated coefficient by
coefficient at a fixed spatial point. -/
theorem hasDerivAt_finiteFourierReconstruction_of_coefficients
    (s : Finset Wavevector) (omega : ℝ → FourierVelocity)
    (omegaDot : FourierVelocity) (x : UnitAddTorus (Fin 3)) (t : ℝ)
    (hcoeff : ∀ k ∈ s,
      HasDerivAt (fun τ ↦ omega τ k) (omegaDot k) t) :
    HasDerivAt
      (fun τ ↦ finiteFourierReconstruction s (omega τ) x)
      (finiteFourierReconstruction s omegaDot x) t := by
  unfold finiteFourierReconstruction
  induction s using Finset.induction_on with
  | empty =>
      simpa using (hasDerivAt_const (x := t) (c := (0 : ComplexVec3)))
  | @insert k s hk ih =>
      simp only [Finset.sum_insert hk]
      have hterm : HasDerivAt
          (fun τ ↦ UnitAddTorus.mFourier k x • omega τ k)
          (UnitAddTorus.mFourier k x • omegaDot k) t := by
        convert ((complexScalarSMulRealCLM
            (UnitAddTorus.mFourier k x)).hasFDerivAt.comp
          t (hcoeff k (Finset.mem_insert_self k s)).hasFDerivAt).hasDerivAt using 1
        all_goals first | rfl | simp
      exact hterm.add (ih fun l hl ↦ hcoeff l (Finset.mem_insert_of_mem hl))

/-- Componentwise coefficient differentiability is sufficient for the exact
finite-reconstruction derivative. -/
theorem hasDerivAt_finiteFourierReconstruction_of_components
    (s : Finset Wavevector) (omega : ℝ → FourierVelocity)
    (omegaDot : FourierVelocity) (x : UnitAddTorus (Fin 3)) (t : ℝ)
    (hcoeff : ∀ k ∈ s, ∀ i,
      HasDerivAt (fun τ ↦ omega τ k i) (omegaDot k i) t) :
    HasDerivAt
      (fun τ ↦ finiteFourierReconstruction s (omega τ) x)
      (finiteFourierReconstruction s omegaDot x) t := by
  exact hasDerivAt_finiteFourierReconstruction_of_coefficients
    s omega omegaDot x t fun k hk ↦ hasDerivAt_pi.mpr (hcoeff k hk)

/-- Coordinatewise real part commutes with a real time derivative. -/
theorem hasDerivAt_complexRealPartEuclidean
    {u : ℝ → ComplexVec3} {uDot : ComplexVec3} {t : ℝ}
    (hu : HasDerivAt u uDot t) :
    HasDerivAt (fun τ ↦ complexRealPartEuclidean (u τ))
      (complexRealPartEuclidean uDot) t := by
  rw [← show ∀ v, complexRealPartEuclideanCLM v =
      complexRealPartEuclidean v from complexRealPartEuclideanCLM_apply]
  convert (complexRealPartEuclideanCLM.hasFDerivAt.comp
    t hu.hasFDerivAt).hasDerivAt using 1
  all_goals first | rfl | simp

/-- Real physical observation of a finite complex Fourier reconstruction. -/
def realFiniteFourierReconstruction (s : Finset Wavevector)
    (omega : FourierVelocity) (x : UnitAddTorus (Fin 3)) : R3 :=
  complexRealPartEuclidean (finiteFourierReconstruction s omega x)

/-- The real physical observation inherits the exact reconstructed coefficient
derivative. -/
theorem hasDerivAt_realFiniteFourierReconstruction_of_components
    (s : Finset Wavevector) (omega : ℝ → FourierVelocity)
    (omegaDot : FourierVelocity) (x : UnitAddTorus (Fin 3)) (t : ℝ)
    (hcoeff : ∀ k ∈ s, ∀ i,
      HasDerivAt (fun τ ↦ omega τ k i) (omegaDot k i) t) :
    HasDerivAt
      (fun τ ↦ realFiniteFourierReconstruction s (omega τ) x)
      (realFiniteFourierReconstruction s omegaDot x) t := by
  exact hasDerivAt_complexRealPartEuclidean
    (hasDerivAt_finiteFourierReconstruction_of_components
      s omega omegaDot x t hcoeff)

/-! ## Direction equation on the exact hard pancake block -/

/-- The real physical observation of the same hard square-dyadic pancake
block used by the coherent/misaligned Fourier split. -/
def squareDyadicPancakeRealBlock
    (F : OrientedFrameEquiv) (N : ℕ) (omega : FourierVelocity)
    (x : BilinearSpatialTorus) : R3 :=
  complexRealPartEuclidean (squareDyadicPancakeBlock F N omega x)

/-- Exact time derivative of the real hard pancake block, obtained only from
the coefficients in that block. -/
theorem hasDerivAt_squareDyadicPancakeRealBlock_of_components
    (F : OrientedFrameEquiv) (N : ℕ)
    (omega : ℝ → FourierVelocity) (omegaDot : FourierVelocity)
    (x : BilinearSpatialTorus) (t : ℝ)
    (hcoeff : ∀ k ∈ squareDyadicPancakeModes F N, ∀ i,
      HasDerivAt (fun τ ↦ omega τ k i) (omegaDot k i) t) :
    HasDerivAt
      (fun τ ↦ squareDyadicPancakeRealBlock F N (omega τ) x)
      (squareDyadicPancakeRealBlock F N omegaDot x) t := by
  exact hasDerivAt_realFiniteFourierReconstruction_of_components
    (squareDyadicPancakeModes F N) omega omegaDot x t hcoeff

/-- The exact discrepancy between the differentiated hard pancake block and
pure stretching by the chosen strain operator.  This is where transport,
viscosity, interscale transfer, and localization effects have to be bounded. -/
def dyadicPancakeDirectionResidual
    (S : R3 →L[ℝ] R3) (F : OrientedFrameEquiv) (N : ℕ)
    (omegaDot : FourierVelocity) (r : ℝ) (xi : R3)
    (x : BilinearSpatialTorus) : R3 :=
  squareDyadicPancakeRealBlock F N omegaDot x - r • S xi

theorem blockDerivative_eq_stretching_add_residual
    (S : R3 →L[ℝ] R3) (F : OrientedFrameEquiv) (N : ℕ)
    (omegaDot : FourierVelocity) (r : ℝ) (xi : R3)
    (x : BilinearSpatialTorus) :
    squareDyadicPancakeRealBlock F N omegaDot x =
      r • S xi +
        dyadicPancakeDirectionResidual S F N omegaDot r xi x := by
  simp [dyadicPancakeDirectionResidual]

/-- **Same-block direction bridge.**  A differentiable factorization of the
actual hard pancake block obeys the exact strain-plus-residual direction law.
Thus the direction governing the Fourier misalignment is no longer replaced
by the direction of the unlocalized total vorticity. -/
theorem dyadicPancakeDirectionDerivative_eq_strain_add_residual
    (S : R3 →L[ℝ] R3) (F : OrientedFrameEquiv) (N : ℕ)
    {omega : ℝ → FourierVelocity} (omegaDot : FourierVelocity)
    (x : BilinearSpatialTorus)
    {r : ℝ → ℝ} {xi : ℝ → R3}
    {eta : R3} {radialRate t : ℝ}
    (hcoeff : ∀ k ∈ squareDyadicPancakeModes F N, ∀ i,
      HasDerivAt (fun τ ↦ omega τ k i) (omegaDot k i) t)
    (hr : HasDerivAt r radialRate t)
    (hxi : HasDerivAt xi eta t)
    (hfactor :
      (fun τ ↦ squareDyadicPancakeRealBlock F N (omega τ) x) =
        fun τ ↦ r τ • xi τ)
    (hunit : ∀ τ, ⟪xi τ, xi τ⟫ = 1)
    (hrne : r t ≠ 0) :
    eta = transverseComponent (xi t) (S (xi t)) +
      (r t)⁻¹ • transverseComponent (xi t)
        (dyadicPancakeDirectionResidual S F N omegaDot (r t) (xi t) x) := by
  have hblock := hasDerivAt_squareDyadicPancakeRealBlock_of_components
    F N omega omegaDot x t hcoeff
  have hevolution : HasDerivAt
      (fun τ ↦ squareDyadicPancakeRealBlock F N (omega τ) x)
      (r t • S (xi t) +
        dyadicPancakeDirectionResidual S F N omegaDot (r t) (xi t) x) t := by
    rw [← blockDerivative_eq_stretching_add_residual
      S F N omegaDot (r t) (xi t) x]
    exact hblock
  exact directionDerivative_eq_stretching_diffusion_of_factorization
    S hevolution hr hxi hfactor hunit hrne

end PancakeDyadicDirectionEvolution
end NavierStokes
end FluidDynamics
end Mettapedia
