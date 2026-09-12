import Mettapedia.Analysis.PeriodicRieszPolynomial
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityKernelTransport

/-!
# Material transport of the annular Fourier representative

Every derivative below belongs to the finite representative whose spatial
integrals equal those of the periodized kernel. Almost-everywhere equality
is not differentiated along a path.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityAnnularKernelTransport

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFourierMaterialPaths
open PancakePeriodicVorticityEquation VorticityStretchingKernel
open Mettapedia.Analysis
open scoped ContDiff
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

def entryDirectionalRate (i j : Fin 3) (N : ℕ) (z : T3) (v : X3) : ℝ :=
  ∑ k ∈ AnnularRieszKernel.frequencySupport N,
    (unitTorusDerivativePhase * (realModeDot k v : ℂ) * UnitAddTorus.mFourier k z).re *
      (AnnularRieszKernel.weight N (UnitTorusLattice.frequency k) *
        AnnularRieszKernel.rieszEntry i j (UnitTorusLattice.frequency k))

def kernelDirectionalRate (N : ℕ) (z : T3) (v : X3) : R3 →L[ℝ] R3 :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    entryDirectionalRate i j N z v • PeriodicRieszOperator.basisOperator i j

theorem contDiff_entry_lift (i j : Fin 3) (N : ℕ) :
    ContDiff ℝ ∞ (fun x : X3 ↦ PeriodicRieszPolynomial.entry i j N (torusPoint x)) := by
  unfold PeriodicRieszPolynomial.entry
  apply ContDiff.sum
  intro k _
  have hc : ContDiff ℝ ∞ (fun x : X3 ↦ UnitAddTorus.mFourier k (torusPoint x)) := by
    simp only [mFourier_torusPoint, realModeDot]
    have hr : ContDiff ℝ ∞ (fun x : X3 ↦ ∑ i, (k i : ℝ) * x i) := by fun_prop
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hr)).cexp
  exact (Complex.reCLM.contDiff.comp hc).mul contDiff_const

theorem contDiff_kernel_lift (N : ℕ) :
    ContDiff ℝ ∞ (fun x : X3 ↦ PeriodicRieszPolynomial.kernel N (torusPoint x)) := by
  unfold PeriodicRieszPolynomial.kernel
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (contDiff_entry_lift i j N).smul contDiff_const

theorem hasDerivAt_entry_path (i j : Fin 3) (N : ℕ) (X : ℝ → X3)
    (v : X3) (t : ℝ) (hX : HasDerivAt X v t) :
    HasDerivAt (fun τ ↦ PeriodicRieszPolynomial.entry i j N (torusPoint (X τ)))
      (entryDirectionalRate i j N (torusPoint (X t)) v) t := by
  unfold PeriodicRieszPolynomial.entry entryDirectionalRate
  apply HasDerivAt.fun_sum
  intro k _
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_mFourier_torusPoint k X v t (hasDerivAt_pi.mp hX))).mul_const _

theorem hasDerivAt_kernel_path (N : ℕ) (X : ℝ → X3)
    (v : X3) (t : ℝ) (hX : HasDerivAt X v t) :
    HasDerivAt (fun τ ↦ PeriodicRieszPolynomial.kernel N (torusPoint (X τ)))
      (kernelDirectionalRate N (torusPoint (X t)) v) t := by
  unfold PeriodicRieszPolynomial.kernel kernelDirectionalRate
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  exact (hasDerivAt_entry_path i j N X v t hX).smul_const (PeriodicRieszOperator.basisOperator i j)

theorem hasDerivAt_kernel_pair_path (N : ℕ) (X Y : ℝ → X3)
    (v w : X3) (t : ℝ) (hX : HasDerivAt X v t) (hY : HasDerivAt Y w t) :
    HasDerivAt (fun τ ↦ PeriodicRieszPolynomial.kernel N
      (torusPoint (X τ) - torusPoint (Y τ)))
      (kernelDirectionalRate N (torusPoint (X t) - torusPoint (Y t)) (v - w)) t := by
  simpa only [torusPoint_sub] using
    hasDerivAt_kernel_path N (fun τ ↦ X τ - Y τ) (v - w) t (hX.sub hY)

end Mettapedia.FluidDynamics.NavierStokes.VorticityAnnularKernelTransport
