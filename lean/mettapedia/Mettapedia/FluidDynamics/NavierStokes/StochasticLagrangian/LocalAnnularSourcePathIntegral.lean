import Mettapedia.Analysis.SignedCrossKernelRegularity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpaceTimeExtension
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularStretchEvolution

/-!
# Interface-safe time integration of the actual annular source along paths

On a compact interior interval, full vorticity along locally Lipschitz paths
gives an absolutely continuous high-amplitude paired source. The identity
uses the total almost-everywhere derivative and includes threshold crossings
and equal-amplitude interfaces. It does not identify that derivative on the
interfaces, assert that they are null, or bound its signed integral uniformly
in the annular cutoff. No extension of the PDE solution is claimed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourcePathIntegral

open MeasureTheory
open scoped ContDiff
open PeriodicFourierTriad PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open PancakeCurlOutputTail PancakeFourierMaterialPaths LocalLowDiffusionBudget
open Mettapedia.Analysis SignedCrossKernel
local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
  (X Y : ℝ → X3) (hX : LocallyLipschitz X) (hY : LocallyLipschitz Y)

include hg hSum hu hab hI hX hY

theorem absolutelyContinuousOnInterval_highAmplitudeSource_path (n N : ℕ)
    (L : ℝ) (hL : 0 < L) :
    AbsolutelyContinuousOnInterval (fun τ ↦ highAmplitudeStretch (2 * n) L
      (PeriodicRieszPolynomial.kernel N (torusPoint (X τ) - torusPoint (Y τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (Y τ)))) a b := by
  let w : ℝ × X3 → R3 := fun z ↦
    fullVorticity (LocalSpaceTimeExtension.coefficients s a b hab z.1) (torusPoint z.2)
  have hw : LocallyLipschitz w :=
    LocalSpaceTimeExtension.locallyLipschitz_fullVorticity s a b hab hI g hg hSum hu
  have hx : LocallyLipschitz (fun τ ↦ w (τ, X τ)) :=
    hw.comp (g := fun τ ↦ (τ, X τ)) (LocallyLipschitz.id.prodMk hX)
  have hy : LocallyLipschitz (fun τ ↦ w (τ, Y τ)) :=
    hw.comp (g := fun τ ↦ (τ, Y τ)) (LocallyLipschitz.id.prodMk hY)
  have hkernel : LocallyLipschitz (fun τ ↦
      PeriodicRieszPolynomial.kernel N (torusPoint (X τ) - torusPoint (Y τ))) := by
    have hk : LocallyLipschitz (fun x : X3 ↦ PeriodicRieszPolynomial.kernel N (torusPoint x)) :=
      ((VorticityAnnularKernelTransport.contDiff_kernel_lift N).of_le
        (by simp : (1 : WithTop ℕ∞) ≤ ∞)).locallyLipschitz
    simpa only [Function.comp_def, VorticityStretchingKernel.torusPoint_sub] using
      hk.comp (g := fun τ ↦ X τ - Y τ) (hX.sub hY)
  have hac := absolutelyContinuousOnInterval_highAmplitudeStretch_even
    (a := a) (b := b) n hL hkernel hx hy
  apply AbsolutelyContinuousComposition.congr hac
  intro τ hτ
  have he := LocalSpaceTimeExtension.coefficients_eq s a b hab τ
    (by simpa only [Set.uIcc_of_le hab] using hτ)
  simp only [w, he]

theorem intervalIntegrable_deriv_highAmplitudeSource_path (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    IntervalIntegrable (deriv (fun τ ↦ highAmplitudeStretch (2 * n) L
      (PeriodicRieszPolynomial.kernel N (torusPoint (X τ) - torusPoint (Y τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (Y τ))))) volume a b :=
  (absolutelyContinuousOnInterval_highAmplitudeSource_path
    s g hg hSum hu a b hab hI X Y hX hY n N L hL).intervalIntegrable_deriv

theorem integral_deriv_highAmplitudeSource_path_eq_sub (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    (∫ τ in a..b, deriv (fun r ↦ highAmplitudeStretch (2 * n) L
      (PeriodicRieszPolynomial.kernel N (torusPoint (X r) - torusPoint (Y r)))
      (fullVorticity (s.coefficients r) (torusPoint (X r)))
      (fullVorticity (s.coefficients r) (torusPoint (Y r)))) τ) =
      highAmplitudeStretch (2 * n) L
        (PeriodicRieszPolynomial.kernel N (torusPoint (X b) - torusPoint (Y b)))
        (fullVorticity (s.coefficients b) (torusPoint (X b)))
        (fullVorticity (s.coefficients b) (torusPoint (Y b))) -
      highAmplitudeStretch (2 * n) L
        (PeriodicRieszPolynomial.kernel N (torusPoint (X a) - torusPoint (Y a)))
        (fullVorticity (s.coefficients a) (torusPoint (X a)))
        (fullVorticity (s.coefficients a) (torusPoint (Y a))) :=
  (absolutelyContinuousOnInterval_highAmplitudeSource_path
    s g hg hSum hu a b hab hI X Y hX hY n N L hL).integral_deriv_eq_sub

end Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourcePathIntegral
