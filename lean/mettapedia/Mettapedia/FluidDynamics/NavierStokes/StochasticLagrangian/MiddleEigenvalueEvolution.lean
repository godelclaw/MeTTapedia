import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpectralDefectSources
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StrainEigenvalueRates
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MiddleEigenvalueAlgebra
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpatialAdvectionDivergence
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfinitePressurePoisson

/-!
# Material evolution of the middle strain eigenvalue

Along a material path of the actual periodic solution, let `S` be the strain, `ω` the
vorticity, `λ₀ ≥ λ₁ ≥ λ₂` the ordered eigenvalues of `S` and `e₁` the unit eigenvector of the
middle one. At every time where the largest and smallest eigenvalues are differentiable,

```text
d/dt λ₁ = -λ₁² + (|ω|² - ⟪ω, e₁⟫²)/4 + ⟪e₁, (-∇²p + ν ΔS) e₁⟫
        = (λ₀² - 2λ₁² + λ₂²)/3 + (|ω|²/3 - ⟪ω, e₁⟫²)/4 - ⟪e₁, H̃ e₁⟫ + ν ⟪e₁, ΔS e₁⟫,
```

with `H̃` the trace-free part of the pressure Hessian. The first form comes from the strain
equation `S' = -S² - Ω² - ∇²p + ν ΔS`: the self-interaction gives `-λ₁²`, and the spin gives
`|Ω e₁|²`, a quarter of the squared component of the vorticity orthogonal to `e₁`
(`hasDerivAt_secondEigenvalueAlong`). The second form removes the trace of the pressure
Hessian with the Poisson equation `Δp = |ω|²/2 - |S|²`
(`hasDerivAt_secondEigenvalueAlong_anisotropic`).

Dropping `H̃`, viscosity and vorticity leaves the restricted Euler law of Vieillefosse,
`λᵢ' = -λᵢ² + (λ₀² + λ₁² + λ₂²)/3`. Its sheet `λ = (c, c, -2c)` obeys `c' = c²`: the middle
eigenvalue blows up in finite time and its time integral diverges (`restricted_sheet`). The
local terms of the law therefore do not bound the time integral of the positive middle
eigenvalue; a bound has to use the nonlocal trace-free pressure Hessian, the vorticity or
the viscosity.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.MiddleEigenvalueEvolution

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalSpatialVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open PancakeLocalGradientEquation PancakeLocalStrainEquation PancakeLocalStrainReality
open PancakeFilteredStrainDynamics PancakeMatrixCurlAlgebra PancakeInfiniteSpatialCurl
open PancakeInfiniteSpatialPressure PancakeInfinitePressureHessian PancakeInfinitePressurePoisson
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeStrainSpectralFrame PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain
open LocalMaterialVorticity LocalMaterialStrain LocalSpectralDefectSources StrainEigenvalueRates
open SpatialAdvectionDivergence MiddleEigenvalueAlgebra

local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

variable {nu T B : ℝ} {u₀ : FourierVelocity}

/-! ## The real gradient on a material path -/

/-- The real velocity gradient on the path, `A a b = ∂_b u_a`. -/
def gradAlong (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3) (t : ℝ) :
    GradMatrix :=
  fun a b ↦ (spatialVelocityGradient (spatialField s t) (torusPoint (X t)) a b).re

theorem strainAlong_eq (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3) (t : ℝ) :
    strainAlong s X t = matCLM (symm (gradAlong s X t)) := by
  ext v a
  simp only [strainAlong, realMatrixOperator_apply, matCLM_apply,
    PancakeLocalStrainEquation.spatialStrain, symmetrize, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  congr 1
  simp [Complex.mul_re, MiddleEigenvalueAlgebra.symm_apply, gradAlong]
  ring

theorem spinAlong_apply (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3) (t : ℝ)
    (v : R3) (a : Fin 3) :
    spinAlong s X t v a = ∑ b, spin (gradAlong s X t) a b * v b := by
  simp only [spinAlong, realMatrixOperator_apply,
    PancakeLocalStrainEquation.spatialSpin, skewSymmetrize, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.transpose_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  congr 1
  simp [Complex.mul_re, spin_apply, gradAlong]
  ring

theorem vorticityAlong_apply (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3)
    (t : ℝ) (a : Fin 3) :
    vorticityAlong s X t a = vort (gradAlong s X t) a := by
  rw [vorticityAlong, ← matrixCurl_velocityGradient]
  fin_cases a <;> simp [complexRealPartEuclidean, matrixCurl, vort, gradAlong]

theorem norm_vorticityAlong_sq (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3)
    (t : ℝ) : ‖vorticityAlong s X t‖ ^ 2 = vortSq (gradAlong s X t) := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum]
  simp only [vorticityAlong_apply, vortSq, sq]

/-- **The spin term measures misalignment.** `|Ω v|² = (|ω|² |v|² - ⟪ω, v⟫²) / 4`. -/
theorem norm_spinAlong_sq (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3)
    (t : ℝ) (v : R3) :
    ‖spinAlong s X t v‖ ^ 2 =
      (‖vorticityAlong s X t‖ ^ 2 * ‖v‖ ^ 2 - ⟪vorticityAlong s X t, v⟫ ^ 2) / 4 := by
  simp only [← real_inner_self_eq_norm_sq, inner_eq_sum, spinAlong_apply, vorticityAlong_apply]
  exact sum_spin_sq _ _

/-- The squared eigenvalues of the strain sum to its squared Frobenius norm. -/
theorem normSq_symm_gradAlong (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3)
    (t : ℝ) :
    normSq (symm (gradAlong s X t)) =
      topEigenvalue (symmetricStrainAlong s X t) ^ 2 +
        secondEigenvalue (symmetricStrainAlong s X t) ^ 2 +
        thirdEigenvalue (symmetricStrainAlong s X t) ^ 2 := by
  have hnorm : normSq (symm (gradAlong s X t)) = trSq (symm (gradAlong s X t)) := by
    simp only [normSq, trSq, sq]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by
      rw [symm_symm _ b a]
  have happ (i : Fin 3) : strainAlong s X t ((orderedEigenframe (symmetricStrainAlong s X t).1
      (symmetricStrainAlong s X t).2).eigenbasis i) =
      (orderedEigenframe (symmetricStrainAlong s X t).1 (symmetricStrainAlong s X t).2).eigenvalue i •
        (orderedEigenframe (symmetricStrainAlong s X t).1 (symmetricStrainAlong s X t).2).eigenbasis i :=
    (orderedEigenframe _ _).apply_eigenbasis i
  have hunit (i : Fin 3) := (orderedEigenframe (symmetricStrainAlong s X t).1
    (symmetricStrainAlong s X t).2).eigenbasis.norm_eq_one i
  rw [hnorm, ← trace_matCLM_sq, ← strainAlong_eq, trace_eigen (symmetricStrainAlong s X t)]
  simp only [Fin.sum_univ_three, ContinuousLinearMap.comp_apply, happ, map_smul, smul_smul,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hunit, one_pow, mul_one]
  simp only [topEigenvalue, secondEigenvalue, thirdEigenvalue]
  ring

/-! ## The rate along an eigenvector -/

/-- The strain-equation rate along a unit eigenvector: self-interaction, spin
misalignment, pressure and viscosity. -/
theorem inner_rate_eq (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3) (t : ℝ)
    (hm : Summable (fourierMoment 1 (s.coefficients t))) (e : R3) (he : ‖e‖ = 1) (l : ℝ)
    (hv : strainAlong s X t e = l • e) :
    ⟪e, (-strainAlong s X t * strainAlong s X t + strainRemainderAlong s X t) e⟫ =
      -l ^ 2 + (‖vorticityAlong s X t‖ ^ 2 - ⟪vorticityAlong s X t, e⟫ ^ 2) / 4 +
        ⟪e, pressureDiffusionAlong s X t e⟫ := by
  have hskew := spinAlong_skew s X t e (spinAlong s X t e)
  rw [real_inner_self_eq_norm_sq, norm_spinAlong_sq, he] at hskew
  rw [strainRemainderAlong_eq s X t hm]
  simp only [add_apply, neg_apply, mul_apply_eq_comp, inner_add_right, inner_neg_right, hv, map_smul,
    real_inner_smul_right, real_inner_self_eq_norm_sq, he]
  linarith

/-- The unit eigenvector of the middle eigenvalue on the path. -/
def middleAxisAlong (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3) (t : ℝ) : R3 :=
  (orderedEigenframe (symmetricStrainAlong s X t).1 (symmetricStrainAlong s X t).2).eigenbasis 1

theorem norm_middleAxisAlong (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3)
    (t : ℝ) : ‖middleAxisAlong s X t‖ = 1 :=
  (orderedEigenframe _ _).eigenbasis.norm_eq_one 1

/-- **Material evolution of the middle eigenvalue.** Where the extreme eigenvalues are
differentiable, `λ₁' = -λ₁² + (|ω|² - ⟪ω, e₁⟫²)/4 + ⟪e₁, (-∇²p + ν ΔS) e₁⟫`. -/
theorem hasDerivAt_secondEigenvalueAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htop : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (symmetricStrainAlong s X τ)) t)
    (hbottom : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (symmetricStrainAlong s X τ)) t) :
    HasDerivAt (fun τ ↦ secondEigenvalue (symmetricStrainAlong s X τ))
      (-secondEigenvalue (symmetricStrainAlong s X t) ^ 2 +
        (‖vorticityAlong s X t‖ ^ 2 - ⟪vorticityAlong s X t, middleAxisAlong s X t⟫ ^ 2) / 4 +
        ⟪middleAxisAlong s X t, pressureDiffusionAlong s X t (middleAxisAlong s X t)⟫) t := by
  have hm : Summable (fourierMoment 1 (s.coefficients t)) :=
    summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩))
  have h := hasDerivAt_secondEigenvalue (fun τ ↦ symmetricStrainAlong s X τ) _ t
    (hasDerivAt_strainAlong s g hg hSum hu X hX t ht) htop hbottom
  exact h.congr_deriv (inner_rate_eq s X t hm (middleAxisAlong s X t)
    (norm_middleAxisAlong s X t) _ ((orderedEigenframe _ _).apply_eigenbasis 1))

/-! ## Removing the trace of the pressure Hessian -/

/-- The actual pressure Hessian on the path. -/
def pressureHessianAlong (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3) (t : ℝ) :
    R3 →L[ℝ] R3 :=
  realMatrixOperator (spatialHessian (spatialPressure (s.coefficients t)) (torusPoint (X t)))

/-- The viscous term of the strain equation on the path. -/
def viscousStrainAlong (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3) (t : ℝ) :
    R3 →L[ℝ] R3 :=
  realMatrixOperator ((nu : ℂ) • matrixLaplacian
    (PancakeLocalStrainEquation.spatialStrain (spatialField s t)) (torusPoint (X t)))

theorem pressureDiffusionAlong_eq (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3)
    (t : ℝ) :
    pressureDiffusionAlong s X t = -pressureHessianAlong s X t + viscousStrainAlong s X t := by
  rw [pressureDiffusionAlong, realMatrixOperator_add, realMatrixOperator_neg]
  rfl

/-- The trace-free part of the pressure Hessian. -/
def anisotropicPressureAlong (s : LocalInfiniteVelocitySolution nu u₀ T B) (X : ℝ → X3)
    (t : ℝ) : R3 →L[ℝ] R3 :=
  pressureHessianAlong s X t -
    ((1 / 3 : ℝ) * LinearMap.trace ℝ R3 (pressureHessianAlong s X t).toLinearMap) •
      ContinuousLinearMap.id ℝ R3

/-- **The pressure Poisson equation on the path:** `Δp = |ω|²/2 - |S|²`. -/
theorem trace_pressureHessianAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (X : ℝ → X3) (t : ℝ) (hm : Summable (fourierMoment 2 (s.coefficients t))) :
    LinearMap.trace ℝ R3 (pressureHessianAlong s X t).toLinearMap =
      vortSq (gradAlong s X t) / 2 - normSq (symm (gradAlong s X t)) := by
  have hm1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 2) hm
  have hp := spatialPressure_poisson (s.coefficients t) hm (s.transverse t) (torusPoint (X t))
  rw [divergence_advection_eq_trace _ hm (s.transverse t)] at hp
  have hr (a b : Fin 3) :
      (spatialVelocityGradient (spatialField s t) (torusPoint (X t)) a b).im = 0 := by
    have h := congrArg Complex.im
      (spatialVelocityGradient_reality _ hm1 (s.reality t) (torusPoint (X t)) a b)
    simp only [Complex.conj_im] at h
    dsimp [spatialField]
    linarith
  have hre := congrArg Complex.re hp
  simp only [scalarLaplacian_eq_trace, Matrix.trace, Matrix.diag_apply, Complex.re_sum,
    Complex.neg_re, Matrix.mul_apply, Complex.mul_re] at hre
  rw [trace_std]
  have hcol (a : Fin 3) : pressureHessianAlong s X t (EuclideanSpace.single a 1) a =
      (spatialHessian (spatialPressure (s.coefficients t)) (torusPoint (X t)) a a).re := by
    rw [pressureHessianAlong, realMatrixOperator_apply]
    simp only [PiLp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  simp only [hcol, hre]
  change -∑ a, ∑ b, ((spatialVelocityGradient (spatialField s t) (torusPoint (X t)) a b).re *
      (spatialVelocityGradient (spatialField s t) (torusPoint (X t)) b a).re -
    (spatialVelocityGradient (spatialField s t) (torusPoint (X t)) a b).im *
      (spatialVelocityGradient (spatialField s t) (torusPoint (X t)) b a).im) = _
  simp only [hr, mul_zero, sub_zero]
  rw [show vortSq (gradAlong s X t) / 2 - normSq (symm (gradAlong s X t)) =
    -trSq (gradAlong s X t) by rw [trSq_eq]; ring]
  rfl

/-- **Middle eigenvalue law without the isotropic pressure.** With `H̃` the trace-free
pressure Hessian, `λ₁' = (λ₀² - 2λ₁² + λ₂²)/3 + (|ω|²/3 - ⟪ω, e₁⟫²)/4 - ⟪e₁, H̃ e₁⟫ +
ν ⟪e₁, ΔS e₁⟫`. -/
theorem hasDerivAt_secondEigenvalueAlong_anisotropic
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htop : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (symmetricStrainAlong s X τ)) t)
    (hbottom : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (symmetricStrainAlong s X τ)) t) :
    HasDerivAt (fun τ ↦ secondEigenvalue (symmetricStrainAlong s X τ))
      ((topEigenvalue (symmetricStrainAlong s X t) ^ 2 -
          2 * secondEigenvalue (symmetricStrainAlong s X t) ^ 2 +
          thirdEigenvalue (symmetricStrainAlong s X t) ^ 2) / 3 +
        (‖vorticityAlong s X t‖ ^ 2 / 3 - ⟪vorticityAlong s X t, middleAxisAlong s X t⟫ ^ 2) / 4 -
        ⟪middleAxisAlong s X t, anisotropicPressureAlong s X t (middleAxisAlong s X t)⟫ +
        ⟪middleAxisAlong s X t, viscousStrainAlong s X t (middleAxisAlong s X t)⟫) t := by
  have hm2 : Summable (fourierMoment 2 (s.coefficients t)) :=
    summable_fourierMoment_of_le _ (by omega : 2 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩))
  refine (hasDerivAt_secondEigenvalueAlong s g hg hSum hu X hX t ht htop hbottom).congr_deriv ?_
  have htr := trace_pressureHessianAlong s X t hm2
  rw [normSq_symm_gradAlong, ← norm_vorticityAlong_sq] at htr
  rw [pressureDiffusionAlong_eq]
  simp only [anisotropicPressureAlong, add_apply, neg_apply, sub_apply, smul_apply, ContinuousLinearMap.id_apply, inner_add_right,
    inner_neg_right, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_middleAxisAlong, htr]
  ring

/-! ## Restricted Euler: the local terms do not bound the middle eigenvalue -/

/-- Vieillefosse's restricted Euler law for the ordered eigenvalues of an irrotational
strain: the law above without the trace-free pressure Hessian and viscosity. -/
def restrictedRate (l : Fin 3 → ℝ) (i : Fin 3) : ℝ := -l i ^ 2 + (∑ j, l j ^ 2) / 3

/-- The irrotational sheet `(c, c, -2c)` with `c(t) = c₀ / (1 - c₀ t)`. -/
def sheet (c₀ t : ℝ) : Fin 3 → ℝ := fun i ↦ ![(1 : ℝ), 1, -2] i * (c₀ / (1 - c₀ * t))

/-- **A sheet blows up under the restricted law.** The sheet solves the law before `1/c₀`,
and its middle eigenvalue is not integrable up to `1/c₀`. -/
theorem restricted_sheet (c₀ : ℝ) (hc : 0 < c₀) :
    (∀ t < 1 / c₀, ∀ i,
      HasDerivAt (fun τ ↦ sheet c₀ τ i) (restrictedRate (sheet c₀ t) i) t) ∧
      ¬ IntervalIntegrable (fun t ↦ sheet c₀ t 1) MeasureTheory.volume 0 (1 / c₀) := by
  constructor
  · intro t ht i
    have hne : 1 - c₀ * t ≠ 0 := by
      have : c₀ * t < 1 := by rwa [lt_div_iff₀ hc, mul_comm] at ht
      linarith
    have h1 : HasDerivAt (fun τ ↦ 1 - c₀ * τ) (-c₀) t := by
      simpa using ((hasDerivAt_id t).const_mul c₀).const_sub 1
    have hd : HasDerivAt (fun τ ↦ c₀ / (1 - c₀ * τ)) ((c₀ / (1 - c₀ * t)) ^ 2) t :=
      ((hasDerivAt_const t c₀).div h1 hne).congr_deriv (by rw [div_pow]; ring)
    have hw : ![(1 : ℝ), 1, -2] i ^ 2 + ![(1 : ℝ), 1, -2] i - 2 = 0 := by
      fin_cases i <;> norm_num
    have hs : ∑ j, sheet c₀ t j ^ 2 = 6 * (c₀ / (1 - c₀ * t)) ^ 2 := by
      simp only [sheet, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
    exact (hd.const_mul (![(1 : ℝ), 1, -2] i)).congr_deriv (by
      rw [restrictedRate, hs]
      simp only [sheet]
      linear_combination (c₀ / (1 - c₀ * t)) ^ 2 * hw)
  · intro hint
    have hc0 : c₀ ≠ 0 := hc.ne'
    have heq : (fun x : ℝ ↦ (x - 1 / c₀)⁻¹) = fun x ↦ -sheet c₀ x 1 := by
      funext x
      show (x - 1 / c₀)⁻¹ = -((1 : ℝ) * (c₀ / (1 - c₀ * x)))
      rw [one_mul, ← neg_sub (1 / c₀) x, inv_neg,
        show 1 / c₀ - x = (1 - c₀ * x) / c₀ by field_simp, inv_div]
    have hinv : IntervalIntegrable (fun x : ℝ ↦ (x - 1 / c₀)⁻¹) MeasureTheory.volume 0 (1 / c₀) := by
      rw [heq]
      exact hint.neg
    rcases intervalIntegrable_sub_inv_iff.mp hinv with h | h
    · exact (one_div_pos.mpr hc).ne' h.symm
    · exact h Set.right_mem_uIcc

end Mettapedia.FluidDynamics.NavierStokes.MiddleEigenvalueEvolution
