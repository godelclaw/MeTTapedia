import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityStretchingKernel
import Mettapedia.Analysis.OperatorQuadraticForm

/-!
# Transport of the actual finite Biot–Savart kernel

The velocity difference differentiates every Fourier character. There is
no independently specified phase derivative and no cutoff-uniform bound
on this transport term.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityStretchingKernel

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFourierMaterialPaths
open PancakePeriodicVorticityEquation
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

def kernelDirectionalRate (modes : Finset Wavevector) (z : T3) (v : X3) : R3 →L[ℝ] R3 :=
  ∑ k ∈ modes, (unitTorusDerivativePhase * (realModeDot k v : ℂ) *
    UnitAddTorus.mFourier k z).re • projectionSymbol k

theorem torusPoint_sub (x y : X3) : torusPoint (x - y) = torusPoint x - torusPoint y := by
  ext i
  simp [torusPoint]

theorem hasDerivAt_kernel_path (modes : Finset Wavevector) (X : ℝ → X3)
    (v : X3) (t : ℝ) (hX : HasDerivAt X v t) :
    HasDerivAt (fun τ ↦ kernel modes (torusPoint (X τ)))
      (kernelDirectionalRate modes (torusPoint (X t)) v) t := by
  unfold kernel kernelDirectionalRate
  apply HasDerivAt.fun_sum
  intro k _
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_mFourier_torusPoint k X v t (hasDerivAt_pi.mp hX))).smul_const (projectionSymbol k)

theorem hasDerivAt_kernel_pair_path (modes : Finset Wavevector) (X Y : ℝ → X3)
    (v w : X3) (t : ℝ) (hX : HasDerivAt X v t) (hY : HasDerivAt Y w t) :
    HasDerivAt (fun τ ↦ kernel modes (torusPoint (X τ) - torusPoint (Y τ)))
      (kernelDirectionalRate modes (torusPoint (X t) - torusPoint (Y t)) (v - w)) t := by
  simpa only [torusPoint_sub] using hasDerivAt_kernel_path modes (fun τ ↦ X τ - Y τ) (v - w) t (hX.sub hY)

end Mettapedia.FluidDynamics.NavierStokes.VorticityStretchingKernel
