import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalPairedStretchEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityAnnularKernelTransport
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityAnnularPolynomialSource

/-!
# Signed annular-source evolution along actual material paths

The same finite Fourier representative occurs in the material derivative
and in the cutoff-uniform dissipation payment. Full vorticity, full strain,
relative-velocity kernel transport and viscosity remain explicit. Derivatives
of the amplitude cutoff are asserted only on its strict smooth branches.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAnnularStretchEvolution

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths
open PancakeLocalMaterialTrajectories LocalLowDiffusionBudget LocalJointDiffusionBudget
open LocalAlignmentForcing LocalInitialSpectral LocalVorticityPairAngle
open Mettapedia.Analysis SignedCrossKernel
open VorticityAnnularKernelTransport
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "H" => PeriodicRieszPolynomial.kernel (d := 3)

def materialPairedRate (n N : ℕ) (u : FourierVelocity)
    (nu : ℝ) (x y : T3) (v w : X3) : ℝ :=
  pairedStretchRate n (fullStrainOperator u x) (fullStrainOperator u y)
    (H N (x - y)) (kernelDirectionalRate N (x - y) (v - w))
    (fullVorticity u x) (fullVorticity u y)
    (nu • fullVorticityLaplacian u x) (nu • fullVorticityLaplacian u y)

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
  (X Y : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
  (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
  (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t)

include hg hSum hu hab hI ht hX hY

theorem hasDerivAt_pairedStretch_path (n N : ℕ) :
    HasDerivAt (fun τ ↦ pairedStretch (2 * (n + 1))
      (H N (torusPoint (X τ) - torusPoint (Y τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (Y τ))))
      (materialPairedRate n N (s.coefficients t) nu (torusPoint (X t)) (torusPoint (Y t))
        (liftedVelocity s t (X t)) (liftedVelocity s t (Y t))) t := by
  exact LocalPairedStretchEvolution.hasDerivAt_pairedStretch_path_of_kernel
    s g hg hSum hu a b hab hI X Y t ht hX hY n _ _
    (hasDerivAt_kernel_pair_path N X Y _ _ t hX hY)

theorem hasDerivAt_highAmplitudeStretch_path_left (n N : ℕ) (L : ℝ) (hL : 0 < L)
    (hLa : L < ‖fullVorticity (s.coefficients t) (torusPoint (X t))‖)
    (hxy : ‖fullVorticity (s.coefficients t) (torusPoint (X t))‖ <
      ‖fullVorticity (s.coefficients t) (torusPoint (Y t))‖) :
    HasDerivAt (fun τ ↦ highAmplitudeStretch (2 * (n + 1)) L
      (H N (torusPoint (X τ) - torusPoint (Y τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (Y τ))))
      (LocalPairedStretchEvolution.amplitudeWeightRate L (s.coefficients t) nu (torusPoint (X t)) *
          pairedStretch (2 * (n + 1)) (H N (torusPoint (X t) - torusPoint (Y t)))
            (fullVorticity (s.coefficients t) (torusPoint (X t)))
            (fullVorticity (s.coefficients t) (torusPoint (Y t))) +
        (1 - lowAmplitudeWeight L (fullVorticity (s.coefficients t) (torusPoint (X t)))
          (fullVorticity (s.coefficients t) (torusPoint (Y t)))) *
          materialPairedRate n N (s.coefficients t) nu (torusPoint (X t)) (torusPoint (Y t))
            (liftedVelocity s t (X t)) (liftedVelocity s t (Y t))) t := by
  have hx := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI X t ht hX
  have hy := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI Y t ht hY
  exact (hasDerivAt_highAmplitudeWeight_of_left_lt hx hy.continuousAt hL hLa hxy).mul
    (hasDerivAt_pairedStretch_path s g hg hSum hu a b hab hI X Y t ht hX hY n N)

theorem hasDerivAt_highAmplitudeStretch_path_right (n N : ℕ) (L : ℝ) (hL : 0 < L)
    (hLb : L < ‖fullVorticity (s.coefficients t) (torusPoint (Y t))‖)
    (hyx : ‖fullVorticity (s.coefficients t) (torusPoint (Y t))‖ <
      ‖fullVorticity (s.coefficients t) (torusPoint (X t))‖) :
    HasDerivAt (fun τ ↦ highAmplitudeStretch (2 * (n + 1)) L
      (H N (torusPoint (X τ) - torusPoint (Y τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (Y τ))))
      (LocalPairedStretchEvolution.amplitudeWeightRate L (s.coefficients t) nu (torusPoint (Y t)) *
          pairedStretch (2 * (n + 1)) (H N (torusPoint (X t) - torusPoint (Y t)))
            (fullVorticity (s.coefficients t) (torusPoint (X t)))
            (fullVorticity (s.coefficients t) (torusPoint (Y t))) +
        (1 - lowAmplitudeWeight L (fullVorticity (s.coefficients t) (torusPoint (X t)))
          (fullVorticity (s.coefficients t) (torusPoint (Y t)))) *
          materialPairedRate n N (s.coefficients t) nu (torusPoint (X t)) (torusPoint (Y t))
            (liftedVelocity s t (X t)) (liftedVelocity s t (Y t))) t := by
  have hx := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI X t ht hX
  have hy := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI Y t ht hY
  exact (hasDerivAt_highAmplitudeWeight_of_right_lt hx.continuousAt hy hL hLb hyx).mul
    (hasDerivAt_pairedStretch_path s g hg hSum hu a b hab hI X Y t ht hX hY n N)

end Mettapedia.FluidDynamics.NavierStokes.LocalAnnularStretchEvolution
