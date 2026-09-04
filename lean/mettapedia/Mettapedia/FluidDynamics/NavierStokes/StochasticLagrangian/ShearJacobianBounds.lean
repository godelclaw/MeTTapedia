import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PullbackOneForm
import Mettapedia.FluidDynamics.NavierStokes.BenH1Break

/-!
# Shear flows: pointwise Jacobian bounds versus Sobolev operator growth

The volume-preserving shear `g_{a,k}(x) = x + a sin(k x₀) e₁` is the family
on which the uniform `H^m → H^m` composition/adjoint bound fails: with the
amplitude normalized so the displacement has fixed `H^m` size `ε`, the `H^m`
operator ratio grows like `√(1 + (εk)²)` (machine-checked obstruction in
`Mettapedia.FluidDynamics.NavierStokes.BenH1Break`).

This file computes the *pointwise* transport quantities of the same family —
the objects that actually enter the stochastic-Lagrangian representation of
the Navier–Stokes equations (Constantin–Iyer) and its continuation gate
`∫₀ᵀ 𝔼‖DX_t‖_∞ dt`:

* the flow Jacobian `Dg = I + a k cos(k x₀) e₁ ⊗ dx₀` (exact formula), with
  exact inverse `g_{-a,k}`, so the covector pullback matrix (the
  inverse-transpose of the Jacobian) belongs to the same family;
* the pointwise Jacobian deviation bound `‖Dg v − v‖ ≤ |a k| ‖v‖`;
* the covector pullbacks of the constant covectors: `dx₀` is preserved
  exactly, and `dx₁` acquires the bounded component `a k cos(k x₀) dx₀`;
* on the `H^m`-normalized family `a_k = ε / k^m` (`m ≥ 1`), all these
  pointwise quantities are bounded by `ε` **uniformly in `k`**, while the
  `H^m` operator ratio of the very same family is unbounded
  (`shearFamily_pointwise_bounded_while_sobolev_ratio_unbounded`).

Consequence, stated precisely: the high-frequency shear mechanism that
refutes any uniform `H^m → H^m` adjoint/composition hypothesis does **not**
constrain pointwise Jacobian gates.  A continuation criterion of the shape
`∫₀ᵀ 𝔼‖DX_t‖_∞ dt < ∞` (Constantin–Iyer representation + averaged Cauchy
vorticity formula) does not factor through the operator that the shear
obstruction kills.  This is an evasion statement only: it does not prove the
gate, whose status for general 3D data is open.

## References

* P. Constantin, G. Iyer, *A stochastic Lagrangian representation of the
  three-dimensional incompressible Navier–Stokes equations*,
  Comm. Pure Appl. Math. **61** (2008), 330–345. arXiv:math/0511067.
* P. Constantin, *An Eulerian–Lagrangian approach to the Navier–Stokes
  equations*, Comm. Math. Phys. **216** (2001), 663–686. arXiv:math/0005116.
* H. Weber, *Ueber eine Transformation der hydrodynamischen Gleichungen*,
  J. Reine Angew. Math. **68** (1868), 286–292.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped RealInnerProductSpace BigOperators

/-- Three-dimensional coordinate space for the shear computations. -/
local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- Wave vector of the shear: magnitude `k` along the phase coordinate. -/
def shearWaveVector (k : ℝ) : R3 := k • EuclideanSpace.single 0 1

/-- The volume-preserving shear `x ↦ x + a sin(k x₀) e₁`. -/
def shearFlowMap (a k : ℝ) : R3 → R3 :=
  fun x => x + profileMode (fun t => a * Real.sin t) (shearWaveVector k)
    (EuclideanSpace.single 1 1) x

section Jacobian

/-- Exact Jacobian of the shear:
`Dg_{a,k}(x) = I + (a cos(⟪k e₀, x⟫)) (e₁ ⊗ (k e₀)ᵀ)`. -/
theorem hasFDerivAt_shearFlowMap (a k : ℝ) (x : R3) :
    HasFDerivAt (shearFlowMap a k)
      (ContinuousLinearMap.id ℝ R3 +
        (((a * Real.cos ⟪shearWaveVector k, x⟫) •
          innerSL ℝ (shearWaveVector k)).smulRight
            (EuclideanSpace.single 1 1))) x :=
  (hasFDerivAt_id x).add
    (hasFDerivAt_profileMode (dφ := fun t => a * Real.cos t)
      (hasDerivAt_amp_sin a) (shearWaveVector k) (EuclideanSpace.single 1 1) x)

/-- The shear with opposite amplitude is an exact two-sided inverse: the
phase coordinate is untouched by the displacement. -/
theorem shearFlowMap_neg_comp (a k : ℝ) (x : R3) :
    shearFlowMap (-a) k (shearFlowMap a k x) = x := by
  unfold shearFlowMap profileMode
  have hphase : ⟪shearWaveVector k,
      x + (a * Real.sin ⟪shearWaveVector k, x⟫) •
        (EuclideanSpace.single 1 1 : R3)⟫ = ⟪shearWaveVector k, x⟫ := by
    rw [inner_add_right, real_inner_smul_right]
    have horth : ⟪shearWaveVector k,
        (EuclideanSpace.single 1 1 : R3)⟫ = 0 := by
      unfold shearWaveVector
      rw [real_inner_smul_left]
      simp [EuclideanSpace.inner_single_left]
    rw [horth, mul_zero, add_zero]
  rw [hphase]
  module

/-- Pointwise Jacobian deviation bound for the shear:
`‖Dg_{a,k}(x) v − v‖ ≤ |a k| ‖v‖` — the shear family is Lipschitz-close to
the identity at scale `|a k|`, uniformly in the base point. -/
theorem shearFlowMap_jacobian_deviation_le (a k : ℝ) (x v : R3) :
    ‖fderiv ℝ (shearFlowMap a k) x v - v‖ ≤ |a * k| * ‖v‖ := by
  rw [(hasFDerivAt_shearFlowMap a k x).fderiv]
  have hexpand : (ContinuousLinearMap.id ℝ R3 +
      (((a * Real.cos ⟪shearWaveVector k, x⟫) •
        innerSL ℝ (shearWaveVector k)).smulRight
          ((EuclideanSpace.single 1 1 : R3)))) v - v =
      ((a * Real.cos ⟪shearWaveVector k, x⟫) * ⟪shearWaveVector k, v⟫) •
        (EuclideanSpace.single 1 1 : R3) := by
    simp [ContinuousLinearMap.smulRight_apply]
  rw [hexpand]
  rw [norm_smul]
  have hnorm1 : ‖(EuclideanSpace.single 1 1 : R3)‖ = 1 := by simp
  rw [hnorm1, mul_one]
  have hkv : ⟪shearWaveVector k, v⟫ =
      k * ⟪(EuclideanSpace.single 0 1 : R3), v⟫ := by
    unfold shearWaveVector
    rw [real_inner_smul_left]
  have hv0 : |⟪(EuclideanSpace.single 0 1 : R3), v⟫| ≤ ‖v‖ := by
    have h := abs_real_inner_le_norm (EuclideanSpace.single 0 1 : R3) v
    have hn : ‖(EuclideanSpace.single 0 1 : R3)‖ = 1 := by simp
    rw [hn, one_mul] at h
    exact h
  have hcos : |Real.cos ⟪shearWaveVector k, x⟫| ≤ 1 :=
    Real.abs_cos_le_one _
  calc ‖a * Real.cos ⟪shearWaveVector k, x⟫ * ⟪shearWaveVector k, v⟫‖
      = |a| * |Real.cos ⟪shearWaveVector k, x⟫| * |k| *
          |⟪(EuclideanSpace.single 0 1 : R3), v⟫| := by
        rw [Real.norm_eq_abs, hkv]
        rw [abs_mul, abs_mul, abs_mul]
        ring
    _ ≤ |a| * 1 * |k| * ‖v‖ := by
        have h1 : |a| * |Real.cos ⟪shearWaveVector k, x⟫| ≤ |a| * 1 :=
          mul_le_mul_of_nonneg_left hcos (abs_nonneg a)
        have h2 : |a| * |Real.cos ⟪shearWaveVector k, x⟫| * |k| ≤
            |a| * 1 * |k| := mul_le_mul_of_nonneg_right h1 (abs_nonneg k)
        exact mul_le_mul h2 hv0 (abs_nonneg _) (by positivity)
    _ = |a * k| * ‖v‖ := by rw [abs_mul]; ring

end Jacobian

section CovectorPullback

/-- Pullback of a constant covector along the shear: the transpose Jacobian
adds the multiple `a k cos(k x₀) c₁` of `dx₀`.  This is the covector-side
(inverse-transpose) form of the shear transport. -/
theorem pullbackOneForm_shearFlowMap_const (a k : ℝ) (c : R3) (x : R3) :
    pullbackOneForm (shearFlowMap a k) (fun _ => c) x =
      c + ((a * Real.cos ⟪shearWaveVector k, x⟫) * k *
        ⟪c, (EuclideanSpace.single 1 1 : R3)⟫) •
          (EuclideanSpace.single 0 1 : R3) := by
  have hD := (hasFDerivAt_shearFlowMap a k x).fderiv
  ext b
  rw [pullbackOneForm_apply, hD]
  have hb : ((ContinuousLinearMap.id ℝ R3 +
      (((a * Real.cos ⟪shearWaveVector k, x⟫) •
        innerSL ℝ (shearWaveVector k)).smulRight
          ((EuclideanSpace.single 1 1 : R3)))) (EuclideanSpace.single b 1)) =
      EuclideanSpace.single b 1 +
        ((a * Real.cos ⟪shearWaveVector k, x⟫) *
          ⟪shearWaveVector k, EuclideanSpace.single b 1⟫) •
            (EuclideanSpace.single 1 1 : R3) := by
    simp [ContinuousLinearMap.smulRight_apply]
  rw [hb, inner_add_right, real_inner_smul_right]
  have hkb : ⟪shearWaveVector k, (EuclideanSpace.single b 1 : R3)⟫ =
      k * ⟪(EuclideanSpace.single 0 1 : R3), EuclideanSpace.single b 1⟫ := by
    unfold shearWaveVector
    rw [real_inner_smul_left]
  rw [hkb]
  fin_cases b <;> simp [EuclideanSpace.inner_single_right]

/-- The phase-direction covector `dx₀` is preserved **exactly** by the shear
pullback, for every amplitude and frequency. -/
theorem pullbackOneForm_shearFlowMap_horizontal (a k : ℝ) :
    pullbackOneForm (shearFlowMap a k)
      (fun _ => (EuclideanSpace.single 0 1 : R3)) =
      fun _ => (EuclideanSpace.single 0 1 : R3) := by
  funext x
  rw [pullbackOneForm_shearFlowMap_const]
  have h10 : ⟪(EuclideanSpace.single 0 1 : R3),
      (EuclideanSpace.single 1 1 : R3)⟫ = 0 := by
    simp [EuclideanSpace.inner_single_left]
  rw [h10, mul_zero, zero_smul, add_zero]

/-- Exact pointwise norm of the pullback of the displaced-direction covector
`dx₁`: the components are orthogonal, so the norm is
`√(1 + (a cos(k x₀) k)²)`. -/
theorem pullbackOneForm_shearFlowMap_vertical_norm (a k : ℝ) (x : R3) :
    ‖pullbackOneForm (shearFlowMap a k)
      (fun _ => (EuclideanSpace.single 1 1 : R3)) x‖ =
      Real.sqrt (1 + (a * Real.cos ⟪shearWaveVector k, x⟫ * k) ^ 2) := by
  rw [pullbackOneForm_shearFlowMap_const]
  have h11 : ⟪(EuclideanSpace.single 1 1 : R3),
      (EuclideanSpace.single 1 1 : R3)⟫ = 1 := by
    simp
  rw [h11, mul_one]
  set s : ℝ := a * Real.cos ⟪shearWaveVector k, x⟫ * k with hs
  set v : R3 := (EuclideanSpace.single 1 1 : R3) +
    s • (EuclideanSpace.single 0 1 : R3) with hv
  have hsq : ‖v‖ ^ 2 = 1 + s ^ 2 := by
    rw [hv, norm_add_sq_real]
    have hinner : ⟪(EuclideanSpace.single 1 1 : R3),
        s • (EuclideanSpace.single 0 1 : R3)⟫ = 0 := by
      rw [real_inner_smul_right]
      simp [EuclideanSpace.inner_single_left]
    have hn1 : ‖(EuclideanSpace.single 1 1 : R3)‖ = 1 := by simp
    have hn0 : ‖(EuclideanSpace.single 0 1 : R3)‖ = 1 := by simp
    rw [hinner, norm_smul, hn1, hn0, Real.norm_eq_abs]
    rw [mul_one, mul_zero, sq_abs]
    ring
  calc ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
    _ = Real.sqrt (1 + s ^ 2) := by rw [hsq]

/-- The pullback of `dx₁` is bounded pointwise by `√(1 + (a k)²)` — the
Lipschitz size of the shear, with no frequency amplification. -/
theorem pullbackOneForm_shearFlowMap_vertical_norm_le (a k : ℝ) (x : R3) :
    ‖pullbackOneForm (shearFlowMap a k)
      (fun _ => (EuclideanSpace.single 1 1 : R3)) x‖ ≤
      Real.sqrt (1 + (a * k) ^ 2) := by
  rw [pullbackOneForm_shearFlowMap_vertical_norm]
  apply Real.sqrt_le_sqrt
  have hcos := Real.cos_sq_le_one ⟪shearWaveVector k, x⟫
  nlinarith [sq_nonneg (a * k), sq_nonneg (a * Real.cos ⟪shearWaveVector k, x⟫ * k)]

end CovectorPullback

section NormalizedFamily

/-- Amplitude of the `H^m`-normalized shear family: `a_k = ε / k^m`, the
scaling for which the displacement `a_k sin(k x₀) e₁` has `H^m` size
comparable to the fixed chart radius `ε` (each of the `m` derivatives
contributes a factor `k`). -/
def shearFamilyAmplitude (ε : ℝ) (m k : ℕ) : ℝ := ε / (k : ℝ) ^ m

/-- On the normalized family the Lipschitz scale `|a_k · k| = ε k^{1−m}` is
at most `ε` for every frequency (`m ≥ 1`). -/
theorem shearFamilyAmplitude_mul_freq_le (ε : ℝ) (hε : 0 ≤ ε)
    {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) :
    |shearFamilyAmplitude ε m k * (k : ℝ)| ≤ ε := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) ^ m := by positivity
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ m := by
    calc (k : ℝ) = (k : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (k : ℝ) ^ m := pow_le_pow_right₀ hk1 hm
  have hval : shearFamilyAmplitude ε m k * (k : ℝ) =
      ε * ((k : ℝ) / (k : ℝ) ^ m) := by
    unfold shearFamilyAmplitude
    ring
  rw [hval, abs_of_nonneg (by positivity)]
  have hquot : (k : ℝ) / (k : ℝ) ^ m ≤ 1 := by
    rw [div_le_one hkpos]
    exact hkk
  calc ε * ((k : ℝ) / (k : ℝ) ^ m) ≤ ε * 1 :=
        mul_le_mul_of_nonneg_left hquot hε
    _ = ε := mul_one ε

/-- **Uniform pointwise Jacobian bound on the normalized family.**  For every
frequency `k ≥ 1` the Jacobian of the normalized shear deviates from the
identity by at most `ε` in operator ratio — uniformly in `k`. -/
theorem shearFamily_jacobian_uniform_bound (ε : ℝ) (hε : 0 ≤ ε)
    {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (x v : R3) :
    ‖fderiv ℝ (shearFlowMap (shearFamilyAmplitude ε m k) (k : ℝ)) x v - v‖ ≤
      ε * ‖v‖ := by
  calc ‖fderiv ℝ (shearFlowMap (shearFamilyAmplitude ε m k) (k : ℝ)) x v - v‖
      ≤ |shearFamilyAmplitude ε m k * (k : ℝ)| * ‖v‖ :=
        shearFlowMap_jacobian_deviation_le _ _ x v
    _ ≤ ε * ‖v‖ :=
        mul_le_mul_of_nonneg_right
          (shearFamilyAmplitude_mul_freq_le ε hε hm hk) (norm_nonneg v)

/-- **The evasion contrast.**  On one and the same `H^m`-normalized shear
family (chart radius `ε > 0`, Sobolev index `m ≥ 1`):

1. every pointwise Jacobian deviation is bounded by `ε`, uniformly in the
   frequency — the quantity feeding a pointwise gate
   `∫₀ᵀ 𝔼‖DX_t‖_∞ dt` is not stressed at all; while
2. the `H^m → H^m` operator ratio `√(1 + (εk)²)` of the same family admits
   **no** finite uniform bound (the machine-checked composition-operator
   obstruction).

Hence the high-frequency-shear derivative-loss mechanism lives entirely in
the Sobolev operator topology; a pointwise Jacobian gate does not factor
through it.  This does not prove any pointwise gate — it shows this family
cannot refute one. -/
theorem shearFamily_pointwise_bounded_while_sobolev_ratio_unbounded
    (ε : ℝ) (hε : 0 < ε) (m : ℕ) (hm : 1 ≤ m) :
    (∀ k : ℕ, 1 ≤ k → ∀ x v : R3,
      ‖fderiv ℝ (shearFlowMap (shearFamilyAmplitude ε m k) (k : ℝ)) x v - v‖ ≤
        ε * ‖v‖) ∧
    ∀ C : ℝ, ¬ (∀ k : ℕ, benH1ModeAdjointRatio ε k ≤ C) :=
  ⟨fun _ hk x v => shearFamily_jacobian_uniform_bound ε hε.le hm hk x v,
    fun _ => benH1ModeAdjointRatio_unbounded hε⟩

end NormalizedFamily

end NavierStokes
end FluidDynamics
end Mettapedia
