import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityStretchingGate

/-!
# Null self-stretching of a single plane-wave vorticity mode

For the divergence-free plane-wave vorticity `ω(x) = α sin(κ x₁) e₀`
(vorticity along `e₀`, wave vector along `e₁` — the pancake configuration of
`FrozenStrainModel.lean`), the Biot–Savart velocity is the shear
`u(x) = −(α/κ) cos(κ x₁) e₂`, and the strain-rate tensor of that velocity
annihilates the vorticity exactly:

* `curlField_planeWaveVelocityMode`: `curl u = ω` (the mode pair is an exact
  curl/velocity pair, not merely a principal-symbol approximation);
* `strainRateApply_planeWaveVelocityMode_vorticity`:
  `S(u) ω = ½(∇u + (∇u)ᵀ) ω = 0` pointwise — a single exact plane-wave
  vorticity mode generates no strain component along itself.

This machine-checks the single-mode Biot–Savart null-structure step of the
2026-07-03 repair analysis for the stochastic-Lagrangian route (its
"Step 1": `u ⊥ k`, `u ⊥ a`, `k·a = 0` force `S(u)ω = 0`), and does so
exactly rather than at the plane-wave symbol level.

**Scope.**  The identity is for one exact Fourier mode.  A pancake *sector*
is a cone of modes of aperture `λ_q^{−1/2}`; the strain acting on it
aggregates cross-mode and cross-scale contributions which do **not** vanish,
and charging them is exactly the scale-local strain-budget obligation
(`ScaleLocalPancakeStrainBudget` in
`StochasticLagrangian/DyadicPancakeClosure.lean`).  This file therefore
verifies the null-structure ingredient of the claimed pancake closure while
leaving the aggregation step as the named open input; see
`ApertureCoverageDichotomy.lean` for why the aggregation cannot be settled
by the narrow-cone/coercive dichotomy alone.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped RealInnerProductSpace BigOperators

/-- Three-dimensional coordinate space. -/
local notation "R3" => EuclideanSpace ℝ (Fin 3)

section StrainRate

/-- The transpose of the velocity gradient applied to a vector, through the
Euclidean inner product: `(∇u)ᵀ v = Σᵢ ⟪∇u eᵢ, v⟫ eᵢ`. -/
def fderivTransposeApply (u : R3 → R3) (x v : R3) : R3 :=
  ∑ i, ⟪fderiv ℝ u x (EuclideanSpace.single i 1), v⟫ •
    (EuclideanSpace.single i 1 : R3)

/-- The strain-rate tensor (symmetric part of the velocity gradient) applied
to a vector: `S(u) v = ½ (∇u v + (∇u)ᵀ v)`. -/
def strainRateApply (u : R3 → R3) (x v : R3) : R3 :=
  (2⁻¹ : ℝ) • (fderiv ℝ u x v + fderivTransposeApply u x v)

end StrainRate

section PlaneWavePair

/-- The plane-wave vorticity mode `ω(x) = α sin(κ x₁) e₀`: vorticity along
`e₀`, wave vector along `e₁` (divergence-free since `e₀ ⊥ e₁`). -/
def planeWaveVorticityMode (α κ : ℝ) : R3 → R3 :=
  profileMode (fun s => α * Real.sin s)
    (κ • (EuclideanSpace.single 1 1 : R3)) (EuclideanSpace.single 0 1)

/-- The Biot–Savart velocity of the plane-wave vorticity mode: the shear
`u(x) = −(α/κ) cos(κ x₁) e₂`. -/
def planeWaveVelocityMode (α κ : ℝ) : R3 → R3 :=
  profileMode (fun s => (α / κ) * -Real.cos s)
    (κ • (EuclideanSpace.single 1 1 : R3)) (EuclideanSpace.single 2 1)

/-- Pointwise form of the vorticity mode. -/
theorem planeWaveVorticityMode_apply (α κ : ℝ) (x : R3) :
    planeWaveVorticityMode α κ x =
      (α * Real.sin (κ * ⟪(EuclideanSpace.single 1 1 : R3), x⟫)) •
        (EuclideanSpace.single 0 1 : R3) := by
  unfold planeWaveVorticityMode profileMode
  rw [real_inner_smul_left]

/-- The Fréchet derivative of the velocity mode, in closed form. -/
theorem fderiv_planeWaveVelocityMode (α κ : ℝ) (x : R3) :
    fderiv ℝ (planeWaveVelocityMode α κ) x =
      (((α / κ) *
          Real.sin ⟪κ • (EuclideanSpace.single 1 1 : R3), x⟫) •
        innerSL ℝ (κ • (EuclideanSpace.single 1 1 : R3))).smulRight
        (EuclideanSpace.single 2 1) :=
  (hasFDerivAt_profileMode (φ := fun s => (α / κ) * -Real.cos s)
    (dφ := fun s => (α / κ) * Real.sin s)
    (hasDerivAt_amp_neg_cos (α / κ))
    (κ • (EuclideanSpace.single 1 1 : R3))
    (EuclideanSpace.single 2 1) x).fderiv

/-- **The mode pair is an exact curl pair:** `curl u = ω`. -/
theorem curlField_planeWaveVelocityMode {κ : ℝ} (hκ : κ ≠ 0) (α : ℝ)
    (x : R3) :
    curlField (planeWaveVelocityMode α κ) x = planeWaveVorticityMode α κ x := by
  unfold curlField
  rw [fderiv_planeWaveVelocityMode, planeWaveVorticityMode_apply]
  ext i
  fin_cases i <;>
    simp [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      real_inner_smul_left, EuclideanSpace.inner_single_left,
      PiLp.smul_apply, smul_eq_mul]
  field_simp

/-- **Null self-stretching:** the strain rate of the Biot–Savart velocity
annihilates its own vorticity mode, `S(u) ω = 0`, exactly and pointwise.
The three orthogonalities `u ⊥ k`, `u ⊥ a`, `k ⊥ a` kill both the direct
and the transposed gradient term. -/
theorem strainRateApply_planeWaveVelocityMode_vorticity (α κ : ℝ) (x : R3) :
    strainRateApply (planeWaveVelocityMode α κ) x
      (planeWaveVorticityMode α κ x) = 0 := by
  unfold strainRateApply fderivTransposeApply
  rw [fderiv_planeWaveVelocityMode, planeWaveVorticityMode_apply]
  simp [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    real_inner_smul_left, real_inner_smul_right,
    EuclideanSpace.inner_single_left, Fin.sum_univ_three]

/-- Non-vacuity: the vorticity mode is not the zero field. -/
theorem planeWaveVorticityMode_ne_zero :
    planeWaveVorticityMode 1 1 ((Real.pi / 2) •
      (EuclideanSpace.single 1 1 : R3)) ≠ 0 := by
  rw [planeWaveVorticityMode_apply]
  intro hzero
  have h1 : ⟪(EuclideanSpace.single 1 1 : R3),
      (Real.pi / 2) • (EuclideanSpace.single 1 1 : R3)⟫ = Real.pi / 2 := by
    rw [real_inner_smul_right]
    simp
  rw [h1] at hzero
  have happ := congrArg (fun v : R3 => v 0) hzero
  simp [Real.sin_pi_div_two] at happ

end PlaneWavePair

end NavierStokes
end FluidDynamics
end Mettapedia
