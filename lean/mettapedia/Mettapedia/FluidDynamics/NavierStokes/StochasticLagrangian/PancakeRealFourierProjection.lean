import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeProjectionWeightOscillation

/-!
# Real-part projection on a negation-closed Fourier set

Taking real parts reflects coefficient frequencies. A negation-closed
retained set absorbs this reflection, so its real reconstruction is
orthogonal to disjoint outputs even for arbitrary complex coefficients.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeRealFourierProjection

open MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakeTransverseEnergyFreezing PancakeDyadicDirectionEvolution
open PancakeProjectionWeightOscillation

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def realSymmetricCoeff (a : FourierVelocity) : FourierVelocity :=
  fun q i ↦ (a q i + conj (a (-q) i)) / 2

theorem realSymmetricCoeff_conjugate (a : FourierVelocity) (q : Wavevector) :
    realSymmetricCoeff a (-q) = coefficientConjugate (realSymmetricCoeff a q) := by
  ext i
  simp [realSymmetricCoeff, coefficientConjugate, map_ofNat, add_comm]

theorem reconstruction_reflected_conjugate (s : Finset Wavevector) (a : FourierVelocity)
    (hs : ∀ q, -q ∈ s ↔ q ∈ s) (x : T3) (i : Fin 3) :
    finiteFourierReconstruction s (fun q ↦ coefficientConjugate (a (-q))) x i =
      conj (finiteFourierReconstruction s a x i) := by
  classical
  simp only [finiteFourierReconstruction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    coefficientConjugate, map_sum, map_mul]
  apply Finset.sum_bij (fun k _ ↦ -k)
    (fun k hk ↦ (hs k).mpr hk)
    (fun a _ b _ hab ↦ by simpa using congrArg Neg.neg hab)
    (fun b hb ↦ ⟨-b, (hs b).mpr hb, by simp⟩)
  intro k _
  simp [UnitAddTorus.mFourier_neg]

theorem reconstruction_realSymmetricCoeff (s : Finset Wavevector) (a : FourierVelocity)
    (hs : ∀ q, -q ∈ s ↔ q ∈ s) (x : T3) (i : Fin 3) :
    finiteFourierReconstruction s (realSymmetricCoeff a) x i =
      ((finiteFourierReconstruction s a x i).re : ℂ) := by
  have he : finiteFourierReconstruction s (realSymmetricCoeff a) x i =
      (finiteFourierReconstruction s a x i +
        finiteFourierReconstruction s (fun q ↦ coefficientConjugate (a (-q))) x i) / 2 := by
    simp only [finiteFourierReconstruction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      realSymmetricCoeff, coefficientConjugate, ← mul_div_assoc, mul_add]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [he, reconstruction_reflected_conjugate s a hs]
  apply Complex.ext <;> simp

theorem integral_constant_operator_disjoint_neg_closed
    (s t : Finset Wavevector) (a b : FourierVelocity) (A : R3 →L[ℝ] R3)
    (hd : Disjoint s t) (hs : ∀ q, -q ∈ s ↔ q ∈ s) :
    (∫ x : T3, ⟪A (complexRealPartEuclidean (finiteFourierReconstruction s a x)),
      complexRealPartEuclidean (finiteFourierReconstruction t b x)⟫) = 0 := by
  have he : ∀ x : T3, complexRealPartEuclidean (finiteFourierReconstruction s (realSymmetricCoeff a) x) =
      complexRealPartEuclidean (finiteFourierReconstruction s a x) := by
    intro x
    ext i
    change (finiteFourierReconstruction s (realSymmetricCoeff a) x i).re = _
    rw [reconstruction_realSymmetricCoeff s a hs]
    rfl
  have h := integral_constant_operator_disjoint s t (realSymmetricCoeff a) b A hd (fun x i ↦ by
    rw [reconstruction_realSymmetricCoeff s a hs]
    rfl)
  simpa only [he] using h

end Mettapedia.FluidDynamics.NavierStokes.PancakeRealFourierProjection
