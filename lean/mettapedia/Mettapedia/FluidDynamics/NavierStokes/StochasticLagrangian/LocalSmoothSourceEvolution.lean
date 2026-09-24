import Mettapedia.Analysis.SmoothAmplitudePairingRate
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularStretchEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSmoothAnnularDiffusion

/-!
# Actual material derivative of the smooth retained annular source

The derivative holds at every interior time where both paths are tangent
to the actual velocity, including zero and equal-amplitude contacts.
The viscosity channel is exactly the endpoint rate used in the spatial
integration-by-parts identity. A signed time budget is not asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSmoothSourceEvolution

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths
open PancakeLocalMaterialTrajectories LocalLowDiffusionBudget LocalJointDiffusionBudget
open LocalAlignmentForcing LocalAnnularStretchEvolution VorticityAnnularKernelTransport
open Mettapedia.Analysis SmoothAmplitudeCutoff SmoothAmplitudePairing SignedCrossKernel
local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "H" => PeriodicRieszPolynomial.kernel (d := 3)

def materialRate (n : ℕ) (L : ℝ) (N : ℕ) (u : FourierVelocity)
    (nu : ℝ) (x y : T3) (v w : X3) : ℝ :=
  pairRate L (fullVorticity u x) (fullVorticity u y)
      (fullStrainOperator u x (fullVorticity u x) + nu • fullVorticityLaplacian u x)
      (fullStrainOperator u y (fullVorticity u y) + nu • fullVorticityLaplacian u y) *
        pairedStretch (2 * (n + 1)) (H N (x - y)) (fullVorticity u x) (fullVorticity u y) +
    pairWeight L (fullVorticity u x) (fullVorticity u y) * materialPairedRate n N u nu x y v w

theorem materialRate_eq_channels (n : ℕ) (L : ℝ) (N : ℕ) (u : FourierVelocity)
    (nu : ℝ) (x y : T3) (v w : X3) :
    materialRate n L N u nu x y v w =
      retainedStrainRate n L (fullStrainOperator u x) (fullStrainOperator u y)
        (H N (x - y)) (fullVorticity u x) (fullVorticity u y) +
      retainedStretch (2 * (n + 1)) L (kernelDirectionalRate N (x - y) (v - w))
        (fullVorticity u x) (fullVorticity u y) +
      nu * retainedEndpointRate n L (H N (x - y)) (fullVorticity u x) (fullVorticity u y)
        (fullVorticityLaplacian u x) (fullVorticityLaplacian u y) := by
  unfold materialRate materialPairedRate
  rw [retainedRate_eq_strain_add_kernel_add_endpoint]

theorem materialRate_eq_channels_eighth (L : ℝ) (N : ℕ) (u : FourierVelocity)
    (nu : ℝ) (x y : T3) (v w : X3) :
    materialRate 2 L N u nu x y v w =
      retainedStrainRate 2 L (fullStrainOperator u x) (fullStrainOperator u y)
        (H N (x - y)) (fullVorticity u x) (fullVorticity u y) +
      retainedStretch 6 L (kernelDirectionalRate N (x - y) (v - w))
        (fullVorticity u x) (fullVorticity u y) +
      nu * LocalSmoothAnnularDiffusion.diffusionDensity 1 L N u x y :=
  materialRate_eq_channels 2 L N u nu x y v w

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
  (X Y : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
  (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
  (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t)

include hg hSum hu hab hI ht hX hY

theorem hasDerivAt_retainedStretch_path (n : ℕ) (L : ℝ) (hL : 0 < L) (N : ℕ) :
    HasDerivAt (fun τ ↦ retainedStretch (2 * (n + 1)) L
      (H N (torusPoint (X τ) - torusPoint (Y τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (Y τ))))
      (materialRate n L N (s.coefficients t) nu (torusPoint (X t)) (torusPoint (Y t))
        (liftedVelocity s t (X t)) (liftedVelocity s t (Y t))) t := by
  have hx := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI X t ht hX
  have hy := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI Y t ht hY
  exact (hasDerivAt_pairWeight L hL hx hy).mul
    (hasDerivAt_pairedStretch_path s g hg hSum hu a b hab hI X Y t ht hX hY n N)

end Mettapedia.FluidDynamics.NavierStokes.LocalSmoothSourceEvolution
