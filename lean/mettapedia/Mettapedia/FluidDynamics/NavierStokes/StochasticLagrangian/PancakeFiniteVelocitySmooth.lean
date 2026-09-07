import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFiniteLocalizedEvolution
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Smoothness of the actual finite velocity vector field

The state space and extension are the existing finite Fourier Hilbert space.
All denominators in the vector field depend on fixed wave numbers, never on
the evolving state. Consequently its finite quadratic expression is smooth.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFiniteVelocitySmooth

open scoped BigOperators ComplexConjugate ContDiff
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeBlockReality PancakeGalerkinKineticEnergy
open PancakeFiniteLocalizedEvolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_fourierCurl (u : E → FourierVelocity)
    (hu : ∀ q i, ContDiff ℝ ∞ (fun x ↦ u x q i)) (q : Wavevector) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x ↦ fourierCurl (u x) q i) := by
  have h0 := hu q 0
  have h1 := hu q 1
  have h2 := hu q 2
  fin_cases i <;> dsimp [fourierCurl, coefficientCross] <;> fun_prop

theorem contDiff_velocityRHS (M : Finset Wavevector) (u : E → FourierVelocity)
    (hu : ∀ q i, ContDiff ℝ ∞ (fun x ↦ u x q i)) (nu : ℝ)
    (q : Wavevector) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x ↦ velocityRHS M (u x) nu q i) := by
  have hcurl := contDiff_fourierCurl u hu
  have hb (k : Wavevector) (j : Fin 3) :
      ContDiff ℝ ∞ (fun x ↦ complexBiotSavartAmp k (fourierCurl (u x) k) j) := by
    have h0 := hcurl k 0
    have h1 := hcurl k 1
    have h2 := hcurl k 2
    fin_cases j <;> dsimp [complexBiotSavartAmp, coefficientCross] <;> fun_prop
  have ht (j : Fin 3) : ContDiff ℝ ∞ (fun x ↦
      finiteUnitTorusNegativeTransportCoeff M M (fourierCurl (u x)) (u x) q j) := by
    simp only [finiteUnitTorusNegativeTransportCoeff, Finset.sum_apply]
    apply ContDiff.sum
    intro p hp
    simp only [unitTorusNegativeTransportAmp_eq, Pi.smul_apply, smul_eq_mul]
    apply ContDiff.mul _ (hu p.2 j)
    unfold modeDot
    apply ContDiff.sum
    intro a ha
    exact contDiff_const.mul (hb p.1 a)
  have hl : ContDiff ℝ ∞ (fun x ↦ lerayMode q
      (finiteUnitTorusNegativeTransportCoeff M M (fourierCurl (u x)) (u x) q) i) := by
    by_cases hq : modeSquare q = 0
    · simpa [lerayMode, hq] using ht i
    · simp only [lerayMode, hq, dite_false]
      apply (ht i).sub
      apply ContDiff.div_const
      apply contDiff_const.mul
      unfold modeDot
      apply ContDiff.sum
      intro j hj
      exact contDiff_const.mul (ht j)
  exact hl.add (by
    dsimp [unitTorusViscousVorticityCoeff]
    exact contDiff_const.mul (hu q i))

theorem contDiff_extendCoefficients (M : Finset Wavevector) (q : Wavevector) (i : Fin 3) :
    ContDiff ℝ ∞ (fun v : FiniteField M ↦ extendCoefficients M v q i) := by
  by_cases hq : q ∈ M
  · simp only [extendCoefficients, dif_pos hq]
    exact (contDiff_piLp (𝕜 := ℝ) (n := ∞) 2).mp
      (contDiff_id : ContDiff ℝ ∞ (fun v : FiniteField M ↦ v)) (⟨q, hq⟩, i)
  · simp only [extendCoefficients, dif_neg hq]
    exact contDiff_const

/-- Restriction of precisely the previously defined physical velocity RHS. -/
def finiteVelocityRHS (M : Finset Wavevector) (nu : ℝ) (v : FiniteField M) : FiniteField M :=
  restrictCoefficients M (velocityRHS M (extendCoefficients M v) nu)

theorem contDiff_finiteVelocityRHS (M : Finset Wavevector) (nu : ℝ) :
    ContDiff ℝ ∞ (finiteVelocityRHS M nu) := by
  apply (contDiff_piLp 2).mpr
  intro p
  exact contDiff_velocityRHS M (extendCoefficients M) (contDiff_extendCoefficients M) nu p.1 p.2

end Mettapedia.FluidDynamics.NavierStokes.PancakeFiniteVelocitySmooth
