import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMContinuationCore

/-!
# BKM vorticity-stretching estimates

This module isolates the concrete pointwise term `(omega . grad) u` used in
the three-dimensional vorticity equation.  The results here do not assert the
full BKM continuation criterion; they prove the local inequalities needed by
the later enstrophy and Sobolev-growth estimates.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped ContDiff RealInnerProductSpace

section BKMContinuation

/-- The pointwise vorticity-stretching term `(omega . grad) u`. -/
def vorticityStretchingTerm
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  spatialFDeriv u t x (spatialVorticity u t x)

/-- The scalar enstrophy-production density contributed by vorticity
stretching, before any spatial integration. -/
def vorticityStretchingPower
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : ℝ :=
  ⟪spatialVorticity u t x, vorticityStretchingTerm u t x⟫

/-- A slabwise envelope for the operator norm of the spatial velocity gradient. -/
def spatialGradientOperatorEnvelopeOn
    (u : NSVelocityField) (T : ℝ) (Γ : NSTime → ℝ) : Prop :=
  (∀ t, 0 ≤ t → t ≤ T → 0 ≤ Γ t) ∧
    ∀ t x, 0 ≤ t → t ≤ T → ‖spatialFDeriv u t x‖ ≤ Γ t

/-- A uniform slabwise bound for the operator norm of the spatial velocity
gradient. -/
def uniformSpatialGradientOperatorBoundUpTo
    (u : NSVelocityField) (T G : ℝ) : Prop :=
  0 ≤ G ∧ ∀ t x, 0 ≤ t → t ≤ T → ‖spatialFDeriv u t x‖ ≤ G

/-- If vorticity vanishes at a point, the stretching term vanishes there. -/
theorem vorticityStretchingTerm_eq_zero_of_spatialVorticity_eq_zero
    {u : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hω : spatialVorticity u t x = 0) :
    vorticityStretchingTerm u t x = 0 := by
  simp [vorticityStretchingTerm, hω]

/-- The pointwise stretching vector is bounded by the operator norm of
`grad u` times the vorticity magnitude. -/
theorem norm_vorticityStretchingTerm_le
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    ‖vorticityStretchingTerm u t x‖ ≤
      ‖spatialFDeriv u t x‖ * ‖spatialVorticity u t x‖ := by
  simpa [vorticityStretchingTerm] using
    (ContinuousLinearMap.le_opNorm
      (spatialFDeriv u t x) (spatialVorticity u t x))

/-- The pointwise enstrophy-production scalar coming from stretching is bounded
by `||grad u|| * ||omega|| * ||omega||`. -/
theorem abs_vorticityStretchingPower_le
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    |vorticityStretchingPower u t x| ≤
      ‖spatialFDeriv u t x‖ *
        (‖spatialVorticity u t x‖ * ‖spatialVorticity u t x‖) := by
  let omegaVec : NSSpace := spatialVorticity u t x
  let stretchVec : NSSpace := vorticityStretchingTerm u t x
  have hinner : |⟪omegaVec, stretchVec⟫| ≤ ‖omegaVec‖ * ‖stretchVec‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) (x := omegaVec) (y := stretchVec))
  have hstretch : ‖stretchVec‖ ≤ ‖spatialFDeriv u t x‖ * ‖omegaVec‖ := by
    simpa [stretchVec, omegaVec] using norm_vorticityStretchingTerm_le u t x
  calc
    |vorticityStretchingPower u t x| = |⟪omegaVec, stretchVec⟫| := by
      rfl
    _ ≤ ‖omegaVec‖ * ‖stretchVec‖ := hinner
    _ ≤ ‖omegaVec‖ * (‖spatialFDeriv u t x‖ * ‖omegaVec‖) := by
      exact mul_le_mul_of_nonneg_left hstretch (norm_nonneg omegaVec)
    _ = ‖spatialFDeriv u t x‖ * (‖omegaVec‖ * ‖omegaVec‖) := by
      ring

/-- A gradient envelope and a vorticity envelope control the stretching vector
on the slab. -/
theorem norm_vorticityStretchingTerm_le_of_envelopes
    {u : NSVelocityField} {T : ℝ} {Γ Ω : NSTime → ℝ}
    (hΓ : spatialGradientOperatorEnvelopeOn u T Γ)
    (hΩ : vorticityEnvelopeOn u T Ω)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖vorticityStretchingTerm u t x‖ ≤ Γ t * Ω t := by
  rcases hΓ with ⟨hΓnonneg, hΓbound⟩
  rcases hΩ with ⟨_hΩnonneg, hΩbound⟩
  calc
    ‖vorticityStretchingTerm u t x‖
        ≤ ‖spatialFDeriv u t x‖ * ‖spatialVorticity u t x‖ :=
      norm_vorticityStretchingTerm_le u t x
    _ ≤ Γ t * Ω t := by
      exact
        mul_le_mul (hΓbound t x ht0 htT) (hΩbound t x ht0 htT)
          (norm_nonneg (spatialVorticity u t x)) (hΓnonneg t ht0 htT)

/-- A gradient envelope and a vorticity envelope control the pointwise
stretching contribution to enstrophy production. -/
theorem abs_vorticityStretchingPower_le_of_envelopes
    {u : NSVelocityField} {T : ℝ} {Γ Ω : NSTime → ℝ}
    (hΓ : spatialGradientOperatorEnvelopeOn u T Γ)
    (hΩ : vorticityEnvelopeOn u T Ω)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    |vorticityStretchingPower u t x| ≤ Γ t * (Ω t * Ω t) := by
  rcases hΓ with ⟨hΓnonneg, hΓbound⟩
  rcases hΩ with ⟨hΩnonneg, hΩbound⟩
  have hωprod :
      ‖spatialVorticity u t x‖ * ‖spatialVorticity u t x‖ ≤ Ω t * Ω t := by
    exact
      mul_le_mul (hΩbound t x ht0 htT) (hΩbound t x ht0 htT)
        (norm_nonneg (spatialVorticity u t x)) (hΩnonneg t ht0 htT)
  calc
    |vorticityStretchingPower u t x|
        ≤ ‖spatialFDeriv u t x‖ *
            (‖spatialVorticity u t x‖ * ‖spatialVorticity u t x‖) :=
      abs_vorticityStretchingPower_le u t x
    _ ≤ Γ t * (Ω t * Ω t) := by
      exact
        mul_le_mul (hΓbound t x ht0 htT) hωprod
          (mul_nonneg (norm_nonneg (spatialVorticity u t x))
            (norm_nonneg (spatialVorticity u t x)))
          (hΓnonneg t ht0 htT)

/-- Uniform gradient and vorticity bounds control the stretching vector on the
same slab. -/
theorem uniform_vorticityStretchingTerm_boundUpTo
    {u : NSVelocityField} {T G B : ℝ}
    (hG : uniformSpatialGradientOperatorBoundUpTo u T G)
    (hω : uniformVorticityBoundUpTo u T B) :
    0 ≤ G * B ∧
      ∀ t x, 0 ≤ t → t ≤ T →
        ‖vorticityStretchingTerm u t x‖ ≤ G * B := by
  rcases hG with ⟨hGnonneg, hGbound⟩
  rcases hω with ⟨hBnonneg, hωbound⟩
  refine ⟨mul_nonneg hGnonneg hBnonneg, ?_⟩
  intro t x ht0 htT
  calc
    ‖vorticityStretchingTerm u t x‖
        ≤ ‖spatialFDeriv u t x‖ * ‖spatialVorticity u t x‖ :=
      norm_vorticityStretchingTerm_le u t x
    _ ≤ G * B := by
      exact
        mul_le_mul (hGbound t x ht0 htT) (hωbound t x ht0 htT)
          (norm_nonneg (spatialVorticity u t x)) hGnonneg

/-- Uniform gradient and vorticity bounds control the pointwise stretching
contribution to enstrophy production. -/
theorem uniform_vorticityStretchingPower_boundUpTo
    {u : NSVelocityField} {T G B : ℝ}
    (hG : uniformSpatialGradientOperatorBoundUpTo u T G)
    (hω : uniformVorticityBoundUpTo u T B) :
    0 ≤ G * (B * B) ∧
      ∀ t x, 0 ≤ t → t ≤ T →
        |vorticityStretchingPower u t x| ≤ G * (B * B) := by
  rcases hG with ⟨hGnonneg, hGbound⟩
  rcases hω with ⟨hBnonneg, hωbound⟩
  refine ⟨mul_nonneg hGnonneg (mul_nonneg hBnonneg hBnonneg), ?_⟩
  intro t x ht0 htT
  have hωprod :
      ‖spatialVorticity u t x‖ * ‖spatialVorticity u t x‖ ≤ B * B := by
    exact
      mul_le_mul (hωbound t x ht0 htT) (hωbound t x ht0 htT)
        (norm_nonneg (spatialVorticity u t x)) hBnonneg
  calc
    |vorticityStretchingPower u t x|
        ≤ ‖spatialFDeriv u t x‖ *
            (‖spatialVorticity u t x‖ * ‖spatialVorticity u t x‖) :=
      abs_vorticityStretchingPower_le u t x
    _ ≤ G * (B * B) := by
      exact
        mul_le_mul (hGbound t x ht0 htT) hωprod
          (mul_nonneg (norm_nonneg (spatialVorticity u t x))
            (norm_nonneg (spatialVorticity u t x)))
          hGnonneg

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
