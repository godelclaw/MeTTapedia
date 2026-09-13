import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ParallelHeatGeometry
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPolynomialRealAlgebra
import Mettapedia.Analysis.PeriodicRadialPolynomialPairing

/-!
# Collected polynomial coefficients of the actual parallel-flow vorticity

The curl is reconstructed from ordinary derivatives of the full velocity.
Real-part coefficient reflection and exact convolution then construct its
quadratic and quartic endpoint factors. These are spatial identities, not
assumed Fourier expansions or numerical approximations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ParallelHeatFlow

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicVorticityEquation
open PancakeQuadraticFourierSupport FourierPolynomialRealAlgebra
open LocalLowDiffusionBudget Mettapedia.Analysis
local notation "T3" => UnitAddTorus (Fin 3)

/-- Coefficients of one physical coordinate derivative, including `2πi`. -/
def derivativeCoeff (a : FourierCoeff (Fin 3)) (j : Fin 3) : FourierCoeff (Fin 3) :=
  Finsupp.onFinset a.support (fun q ↦ unitTorusDerivativePhase * (q j : ℂ) * a q)
    (fun q hq ↦ Finsupp.mem_support_iff.mpr (by
      intro hz
      exact hq (by simp [hz])))

@[simp] theorem derivativeCoeff_apply (a : FourierCoeff (Fin 3)) (j : Fin 3) (q : Wavevector) :
    derivativeCoeff a j q = unitTorusDerivativePhase * (q j : ℂ) * a q := rfl

theorem support_derivativeCoeff_subset (a : FourierCoeff (Fin 3)) (j : Fin 3) :
    (derivativeCoeff a j).support ⊆ a.support := by
  intro q hq
  by_contra hn
  have hz : a q = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hn
  exact (Finsupp.mem_support_iff.mp hq) (by simp [hz])

theorem fourierPolynomial_derivativeCoeff (a : FourierCoeff (Fin 3)) (j : Fin 3) (x : T3) :
    fourierPolynomial (derivativeCoeff a j) x = scalarGradient a j x := by
  rw [fourierPolynomial_eq_sum_of_support_subset _ a.support (support_derivativeCoeff_subset a j)]
  simp only [derivativeCoeff_apply, scalarGradient, mul_comm]

/-- All three actual real curl components, represented by finite complex coefficients. -/
def vorticityCoeff (a : FourierCoeff (Fin 3)) (i : Fin 3) : FourierCoeff (Fin 3) :=
  if i = 0 then realPartCoeff (derivativeCoeff a 1)
  else if i = 1 then -realPartCoeff (derivativeCoeff a 0) else 0

theorem fourierPolynomial_vorticityCoeff (a : FourierCoeff (Fin 3)) (i : Fin 3) (x : T3) :
    fourierPolynomial (vorticityCoeff a i) x =
      ((fullVorticity (fun q ↦ vertical (a q)) x) i : ℂ) := by
  rw [fullVorticity_vertical]
  fin_cases i <;> simp [-fourierPolynomial_apply,
    vorticityCoeff, fourierPolynomial_neg, fourierPolynomial_realPartCoeff,
    fourierPolynomial_derivativeCoeff]

def normSquareCoeff (a : FourierCoeff (Fin 3)) : FourierCoeff (Fin 3) :=
  productCoeff (vorticityCoeff a 0) (vorticityCoeff a 0) +
    productCoeff (vorticityCoeff a 1) (vorticityCoeff a 1)

theorem fourierPolynomial_normSquareCoeff (a : FourierCoeff (Fin 3)) (x : T3) :
    fourierPolynomial (normSquareCoeff a) x =
      (‖fullVorticity (fun q ↦ vertical (a q)) x‖ ^ 2 : ℝ) := by
  rw [normSquareCoeff, fourierPolynomial_add]
  simp only [ContinuousMap.add_apply, fourierPolynomial_productCoeff, ContinuousMap.mul_apply,
    fourierPolynomial_vorticityCoeff]
  rw [fullVorticity_vertical, EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three, Complex.ofReal_add, sq]

def quarticAmplitudeCoeff (a : FourierCoeff (Fin 3)) : FourierCoeff (Fin 3) :=
  productCoeff (normSquareCoeff a) (normSquareCoeff a)

theorem fourierPolynomial_quarticAmplitudeCoeff (a : FourierCoeff (Fin 3)) (x : T3) :
    fourierPolynomial (quarticAmplitudeCoeff a) x =
      (‖fullVorticity (fun q ↦ vertical (a q)) x‖ ^ 4 : ℝ) := by
  simp only [quarticAmplitudeCoeff, fourierPolynomial_productCoeff, ContinuousMap.mul_apply,
    fourierPolynomial_normSquareCoeff, ← Complex.ofReal_mul]
  congr 1
  ring

def quarticTensorCoeff (a : FourierCoeff (Fin 3)) (i j : Fin 3) : FourierCoeff (Fin 3) :=
  productCoeff (normSquareCoeff a) (productCoeff (vorticityCoeff a i) (vorticityCoeff a j))

theorem fourierPolynomial_quarticTensorCoeff (a : FourierCoeff (Fin 3)) (i j : Fin 3) (x : T3) :
    fourierPolynomial (quarticTensorCoeff a i j) x =
      (PeriodicRadialRiesz.quarticTensorEntry (fullVorticity (fun q ↦ vertical (a q)) x) i j : ℝ) := by
  simp only [quarticTensorCoeff, fourierPolynomial_productCoeff, ContinuousMap.mul_apply,
    fourierPolynomial_normSquareCoeff, fourierPolynomial_vorticityCoeff,
    PeriodicRadialRiesz.quarticTensorEntry, Complex.ofReal_mul]
  ring

end Mettapedia.FluidDynamics.NavierStokes.ParallelHeatFlow
