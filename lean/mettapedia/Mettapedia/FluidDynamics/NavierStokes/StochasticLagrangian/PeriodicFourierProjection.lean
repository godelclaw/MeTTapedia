import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicFourierGradientEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeQuadraticFourierSupport
import Mettapedia.Analysis.UnitTorusFourierApproximation

/-!
# Finite coefficient objects for energy-controlled Fourier approximation

The coefficients are restrictions of the actual Fourier coefficients,
not arbitrary density witnesses. Evaluation agrees with the L2 projection,
and the physical gradient budget is preserved for every finite support.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProjection

open scoped BigOperators
open MeasureTheory
open Mettapedia.Analysis.UnitTorusFourierApproximation Mettapedia.Analysis.FiniteMultiplierLocalization
open PeriodicFourierTriad PancakeQuadraticFourierSupport PancakePeriodicVorticityEquation
open PancakeFourierMaterialPaths PeriodicFourierGradientEnergy
open FourierEllipticProductCoefficients FourierEllipticProductEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def projectionCoeff (f : C(T3, ℂ)) (P : Finset Wavevector) : FourierCoeff (Fin 3) := by
  classical
  exact Finsupp.onFinset P (fun q ↦ if q ∈ P then UnitAddTorus.mFourierCoeff f q else 0)
    (fun q hq ↦ by by_contra h; exact hq (if_neg h))

@[simp] theorem projectionCoeff_apply (f : C(T3, ℂ)) (P : Finset Wavevector) (q : Wavevector) :
    projectionCoeff f P q = if q ∈ P then UnitAddTorus.mFourierCoeff f q else 0 := rfl

theorem support_projectionCoeff_subset (f : C(T3, ℂ)) (P : Finset Wavevector) :
    (projectionCoeff f P).support ⊆ P := by
  intro q hq
  by_contra h
  exact (Finsupp.mem_support_iff.mp hq) (by simp only [projectionCoeff_apply, if_neg h])

theorem fourierPolynomial_projectionCoeff (f : C(T3, ℂ)) (P : Finset Wavevector) :
    fourierPolynomial (projectionCoeff f P) = projection f P := by
  rw [fourierPolynomial, Finsupp.sum_of_support_subset _ (support_projectionCoeff_subset f P)
    (fun (q : Wavevector) (z : ℂ) ↦ z • UnitAddTorus.mFourier q)
    (fun q _ ↦ zero_smul ℂ (UnitAddTorus.mFourier q))]
  apply Finset.sum_congr rfl
  intro q hq
  rw [projectionCoeff_apply, if_pos hq]

theorem coordinateEnergy_projectionCoeff (f : C(T3, ℂ)) (P : Finset Wavevector) :
    coordinateEnergy (projectionCoeff f P).support (projectionCoeff f P) =
      coordinateEnergy P (UnitAddTorus.mFourierCoeff f) := by
  unfold coordinateEnergy
  apply Finset.sum_congr rfl
  intro j _
  change (projectionCoeff f P).sum (fun q z ↦ ‖(q j : ℂ) * z‖ ^ 2) = _
  rw [Finsupp.sum_of_support_subset _ (support_projectionCoeff_subset f P)
    _ (fun _ _ ↦ by simp)]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [projectionCoeff_apply, if_pos hq, coordinateMultiplier]

theorem exists_fourier_approximation_gradient_budget {ι : Type*} [Fintype ι]
    (f : ι → T3 → ℝ) (hf : ∀ i, Continuous (f i))
    (hL : ∀ i, LocallyLipschitz (fun r : X3 ↦ f i (torusPoint r)))
    (delta : ℝ) (hd : 0 < delta) :
    ∃ c : ι → FourierCoeff (Fin 3),
      (∑ i, ∫ x : T3, ‖fourierPolynomial (c i) x - (f i x : ℂ)‖ ^ 2) < delta ∧
      ‖unitTorusDerivativePhase‖ ^ 2 * (∑ i, coordinateEnergy (c i).support (c i)) ≤
        ∑ i, ∫ x : T3, gradientSquare (f i) x := by
  let F : ι → C(T3, ℂ) := fun i ↦ ⟨fun x ↦ (f i x : ℂ), Complex.continuous_ofReal.comp (hf i)⟩
  obtain ⟨P, hP⟩ := exists_sum_integral_projection_error_lt F delta hd
  refine ⟨fun i ↦ projectionCoeff (F i) P, ?_, ?_⟩
  · simpa only [fourierPolynomial_projectionCoeff, F, ContinuousMap.coe_mk] using hP
  · simp only [coordinateEnergy_projectionCoeff, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ ↦ gradientEnergy_le (f i) (hf i) (hL i) P)

end Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProjection
