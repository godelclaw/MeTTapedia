import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MiddleEigenvalueAlgebra
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullVorticityGradientTransport
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalEnstrophyBalance

/-!
# Betchov's identity for the actual periodic field

For a divergence-free velocity on the torus with summable third Fourier moments, the square
and cube traces of the velocity gradient are divergences:

```text
tr(A²) = div((v·∇)v),   tr(A³) = div(F),   F_i = (v·∇)v_k ∂_k v_i - v_i tr(A²)/2,
```

so both integrate to zero. With the exact pointwise decompositions of
`MiddleEigenvalueAlgebra`, the enstrophy production and the strain energy are

```text
∫ ⟪ω, S ω⟫ = -(4/3) ∫ tr(S³),        ∫ |S|² = (1/2) ∫ |ω|².
```

This is Betchov's identity: vortex stretching is, after integration, a cubic invariant of
the strain alone. It uses the exact structure of the nonlinearity, not an estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.BetchovIdentity

open scoped RealInnerProductSpace
open MeasureTheory
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl
open PancakeInfiniteSpatialLaplacian PancakeInfiniteRealCurl PancakeHaarTransportRate
open PancakeFourierMaterialPaths PancakeFourierTranslationCurve PancakePeriodicWeakDerivative
open PancakeLocallyLipschitzEnergy FullLambVector FullVorticityGradientTransport
open LocalLowDiffusionBudget LocalVorticitySeparation LocalEnstrophyDiffusion MiddleEigenvalueAlgebra
open PancakeDyadicDirectionEvolution PancakePeriodicVorticityEquation

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The gradient matrix and its derivatives -/

/-- The velocity gradient `A a b = ∂_b u_a` of the full field. -/
def gradMat (u : FourierVelocity) (x : T3) : GradMatrix := fun a b ↦ velocityJet u b x a

/-- The second derivatives `D i j k = ∂_i ∂_j u_k` of the full field. -/
def secondMat (u : FourierVelocity) (x : T3) : Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun i j k ↦ mixedGradient u j i x k

/-- The velocity components. -/
def velVec (u : FourierVelocity) (x : T3) : Fin 3 → ℝ := fun j ↦ realFullField u x j

theorem modeDot_derivative (u : FourierVelocity) (hd : ∀ q, modeDot q (u q) = 0) (j : Fin 3)
    (q : Wavevector) : modeDot q (indexedDerivativeCoeff id j u q) = 0 := by
  have h := hd q
  simp only [modeDot, indexedDerivativeCoeff, id, Pi.smul_apply, smul_eq_mul] at h ⊢
  rw [show (∑ i : Fin 3, (q i : ℂ) * (unitTorusDerivativePhase * (q j : ℂ) * u q i)) =
      (unitTorusDerivativePhase * (q j : ℂ)) * ∑ i : Fin 3, (q i : ℂ) * u q i by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring, h, mul_zero]

theorem gradMat_trace (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    gradMat u x 0 0 + gradMat u x 1 1 + gradMat u x 2 2 = 0 := by
  have h := sum_velocityJet_diagonal u hu hd x
  simpa only [Fin.sum_univ_three, gradMat] using h

theorem secondMat_symm (u : FourierVelocity) (x : T3) (i j k : Fin 3) :
    secondMat u x i j k = secondMat u x j i k := by
  simp only [secondMat, mixedGradient_commute u j i x]

theorem secondMat_trace (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0) (x : T3) (k : Fin 3) :
    secondMat u x 0 k 0 + secondMat u x 1 k 1 + secondMat u x 2 k 2 = 0 := by
  have h := sum_velocityJet_diagonal (indexedDerivativeCoeff id k u)
    (summable_fourierMoment_derivative 2 u hu k) (modeDot_derivative u hd k) x
  simpa only [Fin.sum_univ_three, secondMat, mixedGradient] using h

/-! ## Shift derivatives and Lipschitz lifts -/

theorem shift_zero (x : T3) (i : Fin 3) : x + coordinateShift i 0 = x := by
  rw [coordinateShift_zero, add_zero]

theorem hasDerivAt_vel (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (i j : Fin 3)
    (x : T3) :
    HasDerivAt (fun t ↦ realFullField u (x + coordinateShift i t) j) (gradMat u x j i) 0 := by
  have h := (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_realFullField_shift u hu i x 0)
  rw [shift_zero] at h
  exact h

theorem hasDerivAt_grad (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (i a b : Fin 3)
    (x : T3) :
    HasDerivAt (fun t ↦ velocityJet u b (x + coordinateShift i t) a) (secondMat u x i b a) 0 := by
  have h := (EuclideanSpace.proj a : R3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_velocityJet_shift u hu b i x 0)
  rw [shift_zero] at h
  exact h

theorem locallyLipschitz_vel (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (j : Fin 3) :
    LocallyLipschitz (fun r : X3 ↦ realFullField u (torusPoint r) j) :=
  (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).lipschitzWith.locallyLipschitz.comp
    (complexRealPartEuclideanCLM.lipschitzWith.locallyLipschitz.comp
      (InfiniteFourierTransport.lipschitzWith_fullFourierField_lift u hu).locallyLipschitz)

theorem locallyLipschitz_grad (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (a b : Fin 3) : LocallyLipschitz (fun r : X3 ↦ velocityJet u b (torusPoint r) a) :=
  (EuclideanSpace.proj a : R3 →L[ℝ] ℝ).lipschitzWith.locallyLipschitz.comp
    (complexRealPartEuclideanCLM.lipschitzWith.locallyLipschitz.comp
      (InfiniteFourierTransport.lipschitzWith_fullFourierField_lift _
        (summable_firstMoment_derivative u hu b)).locallyLipschitz)

theorem locallyLipschitz_finsetSum {ι : Type*} (s : Finset ι) (f : ι → X3 → ℝ)
    (hf : ∀ i ∈ s, LocallyLipschitz (f i)) : LocallyLipschitz (fun r ↦ ∑ i ∈ s, f i r) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LocallyLipschitz.const (0 : ℝ)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-! ## The square trace -/

/-- The flux `((v·∇)v)_k`. -/
def sqFlux (u : FourierVelocity) (k : Fin 3) (y : T3) : ℝ :=
  ∑ j, realFullField u y j * velocityJet u j y k

theorem continuous_sqFlux (u : FourierVelocity) (k : Fin 3) : Continuous (sqFlux u k) :=
  continuous_finsetSum _ fun j _ ↦
    ((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).continuous.comp (continuous_realFullField u)).mul
      ((EuclideanSpace.proj k : R3 →L[ℝ] ℝ).continuous.comp (continuous_velocityJet u j))

theorem locallyLipschitz_sqFlux (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (k : Fin 3) : LocallyLipschitz (fun r : X3 ↦ sqFlux u k (torusPoint r)) :=
  locallyLipschitz_finsetSum _ _ fun j _ ↦ locallyLipschitz_mul_real _ _
    (locallyLipschitz_vel u (summable_firstMoment_of_second u hu) j) (locallyLipschitz_grad u hu k j)

theorem hasDerivAt_sqFlux (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (k : Fin 3)
    (x : T3) :
    HasDerivAt (fun t ↦ sqFlux u k (x + coordinateShift k t))
      (∑ j, (gradMat u x j k * gradMat u x k j + velVec u x j * secondMat u x k j k)) 0 := by
  have hu1 := summable_firstMoment_of_second u hu
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ ↦
    (hasDerivAt_vel u hu1 k j x).fun_mul (hasDerivAt_grad u hu k k j x)
  refine h.congr_deriv ?_
  simp only [shift_zero, gradMat, velVec]

theorem integral_trSq_eq_zero (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0) : ∫ x : T3, trSq (gradMat u x) = 0 := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hflux (k : Fin 3) := integral_coordinateRate_zero (sqFlux u k) k (continuous_sqFlux u k)
    (locallyLipschitz_sqFlux u hu2 k)
  have hrate (k : Fin 3) (x : T3) :
      shiftRate (sqFlux u k) (coordinateShift k) x =
        ∑ j, (gradMat u x j k * gradMat u x k j + velVec u x j * secondMat u x k j k) :=
    (hasDerivAt_sqFlux u hu2 k x).deriv
  have hpt (x : T3) : trSq (gradMat u x) =
      ∑ k, shiftRate (sqFlux u k) (coordinateShift k) x := by
    rw [← sqFluxDiv_eq (velVec u x) (gradMat u x) (secondMat u x) (secondMat_trace u hu hd x)]
    simp only [sqFluxDiv, hrate]
  simp only [hpt]
  rw [integral_finsetSum _ fun k _ ↦ (hflux k).1]
  simp only [(hflux _).2, Finset.sum_const_zero]

/-! ## The cube trace -/

/-- The cube flux `F_i = ∑ v_j ∂_j v_k ∂_k v_i - v_i tr(A²)/2`. -/
def cubeFlux (u : FourierVelocity) (i : Fin 3) (y : T3) : ℝ :=
  (∑ j, ∑ k, realFullField u y j * velocityJet u j y k * velocityJet u k y i) -
    realFullField u y i * trSq (gradMat u y) / 2

theorem continuous_cubeFlux (u : FourierVelocity) (i : Fin 3) : Continuous (cubeFlux u i) := by
  have hv (j : Fin 3) : Continuous (fun y ↦ realFullField u y j) :=
    (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).continuous.comp (continuous_realFullField u)
  have hA (a b : Fin 3) : Continuous (fun y ↦ velocityJet u b y a) :=
    (EuclideanSpace.proj a : R3 →L[ℝ] ℝ).continuous.comp (continuous_velocityJet u b)
  have htr : Continuous (fun y ↦ trSq (gradMat u y)) :=
    continuous_finsetSum _ fun a _ ↦ continuous_finsetSum _ fun b _ ↦ (hA a b).mul (hA b a)
  exact (continuous_finsetSum _ fun j _ ↦ continuous_finsetSum _ fun k _ ↦
    ((hv j).mul (hA k j)).mul (hA i k)).sub (((hv i).mul htr).div_const 2)

theorem locallyLipschitz_cubeFlux (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (i : Fin 3) : LocallyLipschitz (fun r : X3 ↦ cubeFlux u i (torusPoint r)) := by
  have hu1 := summable_firstMoment_of_second u hu
  have htr : LocallyLipschitz (fun r : X3 ↦ trSq (gradMat u (torusPoint r))) :=
    locallyLipschitz_finsetSum _ _ fun a _ ↦ locallyLipschitz_finsetSum _ _ fun b _ ↦
      locallyLipschitz_mul_real _ _ (locallyLipschitz_grad u hu a b) (locallyLipschitz_grad u hu b a)
  have h1 : LocallyLipschitz (fun r : X3 ↦ ∑ j, ∑ k, realFullField u (torusPoint r) j *
      velocityJet u j (torusPoint r) k * velocityJet u k (torusPoint r) i) :=
    locallyLipschitz_finsetSum _ _ fun j _ ↦ locallyLipschitz_finsetSum _ _ fun k _ ↦
      locallyLipschitz_mul_real _ _ (locallyLipschitz_mul_real _ _ (locallyLipschitz_vel u hu1 j)
        (locallyLipschitz_grad u hu k j)) (locallyLipschitz_grad u hu i k)
  have h2 : LocallyLipschitz (fun r : X3 ↦ realFullField u (torusPoint r) i *
      trSq (gradMat u (torusPoint r)) / 2) := by
    have h := locallyLipschitz_mul_real _ _
      (locallyLipschitz_mul_real _ _ (locallyLipschitz_vel u hu1 i) htr)
      (LocallyLipschitz.const ((2 : ℝ)⁻¹))
    simpa only [div_eq_mul_inv] using h
  have h := h1.add h2.neg
  simpa only [cubeFlux, sub_eq_add_neg, Pi.neg_apply] using h

theorem hasDerivAt_cubeFlux (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (i : Fin 3)
    (x : T3) :
    HasDerivAt (fun t ↦ cubeFlux u i (x + coordinateShift i t))
      ((∑ j, ∑ k, (gradMat u x j i * gradMat u x k j * gradMat u x i k +
          velVec u x j * secondMat u x i j k * gradMat u x i k +
          velVec u x j * gradMat u x k j * secondMat u x i k i)) -
        (gradMat u x i i * trSq (gradMat u x) + velVec u x i *
          ∑ a, ∑ b, (secondMat u x i b a * gradMat u x b a +
            gradMat u x a b * secondMat u x i a b)) / 2) 0 := by
  have hu1 := summable_firstMoment_of_second u hu
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun j _ ↦
    HasDerivAt.fun_sum (u := Finset.univ) fun k _ ↦
      ((hasDerivAt_vel u hu1 i j x).fun_mul (hasDerivAt_grad u hu i k j x)).fun_mul
        (hasDerivAt_grad u hu i i k x)
  have htr := HasDerivAt.fun_sum (u := Finset.univ) fun a _ ↦
    HasDerivAt.fun_sum (u := Finset.univ) fun b _ ↦
      (hasDerivAt_grad u hu i a b x).fun_mul (hasDerivAt_grad u hu i b a x)
  have h := hs.fun_sub (((hasDerivAt_vel u hu1 i i x).fun_mul htr).div_const 2)
  refine h.congr_deriv ?_
  simp only [shift_zero, gradMat, velVec, trSq, Fin.sum_univ_three]
  ring

theorem integral_trCube_eq_zero (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0) : ∫ x : T3, trCube (gradMat u x) = 0 := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  have hflux (i : Fin 3) := integral_coordinateRate_zero (cubeFlux u i) i (continuous_cubeFlux u i)
    (locallyLipschitz_cubeFlux u hu2 i)
  have hrate (i : Fin 3) (x : T3) := (hasDerivAt_cubeFlux u hu2 i x).deriv
  have hpt (x : T3) : trCube (gradMat u x) =
      ∑ i, shiftRate (cubeFlux u i) (coordinateShift i) x := by
    rw [← cubeFluxDiv_eq (velVec u x) (gradMat u x) (secondMat u x) (gradMat_trace u hu2 hd x)
      (secondMat_trace u hu hd x) (secondMat_symm u x)]
    simp only [cubeFluxDiv]
    exact Finset.sum_congr rfl fun i _ ↦ (hrate i x).symm
  simp only [hpt]
  rw [integral_finsetSum _ fun i _ ↦ (hflux i).1]
  simp only [(hflux _).2, Finset.sum_const_zero]

end Mettapedia.FluidDynamics.NavierStokes.BetchovIdentity
