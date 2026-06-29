import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMVorticityEquation
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# BKM vorticity-growth estimates from the standard vorticity equation

Once the pressure-free residual-curl equation has been expanded into the
standard transport/diffusion/stretching vorticity equation, the remaining
pointwise growth term is exactly the stretching term.  This module proves that
bridge and reuses the checked stretching estimates.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped RealInnerProductSpace

section BKMContinuation

/-- The material vorticity derivative after moving diffusion to the left-hand
side.  Under the standard vorticity equation this remainder is exactly
`(omega . grad)u`. -/
def vorticityMaterialDiffusionRemainder
    (ν : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  timeVorticityDerivative u t x + vorticityTransportTerm u t x -
    ν • vorticityDiffusionTerm u t x

/-- Enstrophy-production scalar for the material-minus-diffusion remainder. -/
def vorticityMaterialDiffusionPower
    (ν : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) : ℝ :=
  ⟪spatialVorticity u t x, vorticityMaterialDiffusionRemainder ν u t x⟫

/-- Vorticity enstrophy density, `|omega|^2`.  This is the density used in the
BKM a-priori enstrophy estimate, distinct from the velocity-gradient enstrophy
used in the basic energy identity. -/
def vorticityEnstrophyDensity
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : ℝ :=
  ‖spatialVorticity u t x‖ ^ (2 : ℕ)

/-- Total vorticity enstrophy of a time slice. -/
def vorticityEnstrophyAt (u : NSVelocityField) (t : NSTime) : ℝ :=
  ∫ x, vorticityEnstrophyDensity u t x ∂volume

/-- The conventional `1 / 2`-normalized vorticity enstrophy. -/
def normalizedVorticityEnstrophyAt
    (u : NSVelocityField) (t : NSTime) : ℝ :=
  (1 / 2 : ℝ) * vorticityEnstrophyAt u t

/-- Spatial integral of the BKM stretching power
`omega · ((omega · grad) u)`. -/
def vorticityStretchingPowerIntegral
    (u : NSVelocityField) (t : NSTime) : ℝ :=
  ∫ x, vorticityStretchingPower u t x ∂volume

/-- Density of the viscous vorticity dissipation term `|grad omega|^2`. -/
def vorticityDiffusionDissipationDensity
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : ℝ :=
  ‖spatialFDeriv (fun s y => spatialVorticity u s y) t x‖ ^ (2 : ℕ)

/-- Spatial integral of the viscous vorticity dissipation density. -/
def vorticityDiffusionDissipationAt
    (u : NSVelocityField) (t : NSTime) : ℝ :=
  ∫ x, vorticityDiffusionDissipationDensity u t x ∂volume

/-- The scalar derivative predicted by the vorticity enstrophy balance:
stretching production minus viscous dissipation. -/
def vorticityEnstrophyBalanceDerivative
    (ν : ℝ) (u : NSVelocityField) (t : NSTime) : ℝ :=
  vorticityStretchingPowerIntegral u t -
    ν * vorticityDiffusionDissipationAt u t

/-- Local-in-time vorticity enstrophy balance at one time.  Proving this from
the pointwise vorticity equation requires the transport cancellation and
viscous integration-by-parts step; once supplied, the a-priori inequality below
is pure order algebra. -/
def vorticityEnstrophyBalanceAt
    (ν : ℝ) (u : NSVelocityField) (t : NSTime) : Prop :=
  HasDerivAt (fun s => normalizedVorticityEnstrophyAt u s)
    (vorticityEnstrophyBalanceDerivative ν u t) t

/-- The a-priori control shape for vorticity enstrophy: the derivative of
`1 / 2 * int |omega|^2` exists and is bounded above by the stretching-power
integral. -/
def vorticityEnstrophyStretchingControlledAt
    (_ν : ℝ) (u : NSVelocityField) (t : NSTime) : Prop :=
  ∃ D : ℝ,
    HasDerivAt (fun s => normalizedVorticityEnstrophyAt u s) D t ∧
      D ≤ vorticityStretchingPowerIntegral u t

/-- Vorticity enstrophy density is pointwise nonnegative. -/
theorem vorticityEnstrophyDensity_nonneg
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    0 ≤ vorticityEnstrophyDensity u t x := by
  simp [vorticityEnstrophyDensity]

/-- Total vorticity enstrophy is nonnegative on the unguarded integral surface. -/
theorem vorticityEnstrophyAt_nonneg
    (u : NSVelocityField) (t : NSTime) :
    0 ≤ vorticityEnstrophyAt u t := by
  rw [vorticityEnstrophyAt]
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x => vorticityEnstrophyDensity_nonneg u t x)

/-- Vorticity diffusion-dissipation density is pointwise nonnegative. -/
theorem vorticityDiffusionDissipationDensity_nonneg
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    0 ≤ vorticityDiffusionDissipationDensity u t x := by
  simp [vorticityDiffusionDissipationDensity]

/-- Vorticity diffusion dissipation is nonnegative on the unguarded integral
surface. -/
theorem vorticityDiffusionDissipationAt_nonneg
    (u : NSVelocityField) (t : NSTime) :
    0 ≤ vorticityDiffusionDissipationAt u t := by
  rw [vorticityDiffusionDissipationAt]
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x =>
      vorticityDiffusionDissipationDensity_nonneg u t x)

/-- In the vorticity enstrophy balance, nonnegative viscosity can only decrease
the derivative relative to the stretching-power integral. -/
theorem vorticityEnstrophyBalanceDerivative_le_stretchingPowerIntegral
    {ν : ℝ} (hν : 0 ≤ ν) (u : NSVelocityField) (t : NSTime) :
    vorticityEnstrophyBalanceDerivative ν u t ≤
      vorticityStretchingPowerIntegral u t := by
  unfold vorticityEnstrophyBalanceDerivative
  have hmul : 0 ≤ ν * vorticityDiffusionDissipationAt u t :=
    mul_nonneg hν (vorticityDiffusionDissipationAt_nonneg u t)
  linarith

/-- Once the vorticity enstrophy balance is available, the BKM a-priori
enstrophy estimate is controlled by the stretching-power integral. -/
theorem vorticityEnstrophyStretchingControlledAt_of_balance
    {ν : ℝ} (hν : 0 ≤ ν) (u : NSVelocityField) {t : NSTime}
    (hBal : vorticityEnstrophyBalanceAt ν u t) :
    vorticityEnstrophyStretchingControlledAt ν u t := by
  refine ⟨vorticityEnstrophyBalanceDerivative ν u t, hBal, ?_⟩
  exact vorticityEnstrophyBalanceDerivative_le_stretchingPowerIntegral hν u t

/-- The standard vorticity equation identifies the material-minus-diffusion
remainder with the stretching term. -/
theorem vorticityMaterialDiffusionRemainder_eq_vorticityStretchingTerm
    {ν T : ℝ} {u : NSVelocityField}
    (hEq : concreteVorticityEquationOn ν u T)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityMaterialDiffusionRemainder ν u t x =
      vorticityStretchingTerm u t x := by
  have heq := hEq t x ht0 htT
  unfold vorticityMaterialDiffusionRemainder
  rw [heq]
  abel

/-- The corresponding enstrophy-production scalar is exactly the stretching
power under the standard vorticity equation. -/
theorem vorticityMaterialDiffusionPower_eq_vorticityStretchingPower
    {ν T : ℝ} {u : NSVelocityField}
    (hEq : concreteVorticityEquationOn ν u T)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityMaterialDiffusionPower ν u t x =
      vorticityStretchingPower u t x := by
  simp [vorticityMaterialDiffusionPower, vorticityStretchingPower,
    vorticityMaterialDiffusionRemainder_eq_vorticityStretchingTerm hEq ht0 htT]

/-- Pointwise growth bound from the standard vorticity equation. -/
theorem norm_vorticityMaterialDiffusionRemainder_le
    {ν T : ℝ} {u : NSVelocityField}
    (hEq : concreteVorticityEquationOn ν u T)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖vorticityMaterialDiffusionRemainder ν u t x‖ ≤
      ‖spatialFDeriv u t x‖ * ‖spatialVorticity u t x‖ := by
  rw [vorticityMaterialDiffusionRemainder_eq_vorticityStretchingTerm hEq ht0 htT]
  exact norm_vorticityStretchingTerm_le u t x

/-- Pointwise enstrophy-production bound from the standard vorticity equation. -/
theorem abs_vorticityMaterialDiffusionPower_le
    {ν T : ℝ} {u : NSVelocityField}
    (hEq : concreteVorticityEquationOn ν u T)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    |vorticityMaterialDiffusionPower ν u t x| ≤
      ‖spatialFDeriv u t x‖ *
        (‖spatialVorticity u t x‖ * ‖spatialVorticity u t x‖) := by
  rw [vorticityMaterialDiffusionPower_eq_vorticityStretchingPower hEq ht0 htT]
  exact abs_vorticityStretchingPower_le u t x

/-- Gradient and vorticity envelopes control the material-minus-diffusion
remainder on any slab where the standard vorticity equation holds. -/
theorem norm_vorticityMaterialDiffusionRemainder_le_of_envelopes
    {ν T : ℝ} {u : NSVelocityField} {Γ Ω : NSTime → ℝ}
    (hEq : concreteVorticityEquationOn ν u T)
    (hΓ : spatialGradientOperatorEnvelopeOn u T Γ)
    (hΩ : vorticityEnvelopeOn u T Ω)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖vorticityMaterialDiffusionRemainder ν u t x‖ ≤ Γ t * Ω t := by
  rw [vorticityMaterialDiffusionRemainder_eq_vorticityStretchingTerm hEq ht0 htT]
  exact norm_vorticityStretchingTerm_le_of_envelopes hΓ hΩ ht0 htT

/-- Gradient and vorticity envelopes control enstrophy production from the
material-minus-diffusion remainder. -/
theorem abs_vorticityMaterialDiffusionPower_le_of_envelopes
    {ν T : ℝ} {u : NSVelocityField} {Γ Ω : NSTime → ℝ}
    (hEq : concreteVorticityEquationOn ν u T)
    (hΓ : spatialGradientOperatorEnvelopeOn u T Γ)
    (hΩ : vorticityEnvelopeOn u T Ω)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    |vorticityMaterialDiffusionPower ν u t x| ≤ Γ t * (Ω t * Ω t) := by
  rw [vorticityMaterialDiffusionPower_eq_vorticityStretchingPower hEq ht0 htT]
  exact abs_vorticityStretchingPower_le_of_envelopes hΓ hΩ ht0 htT

/-- Uniform gradient and vorticity bounds control the material-minus-diffusion
remainder under the standard vorticity equation. -/
theorem uniform_vorticityMaterialDiffusionRemainder_boundUpTo
    {ν T G B : ℝ} {u : NSVelocityField}
    (hEq : concreteVorticityEquationOn ν u T)
    (hG : uniformSpatialGradientOperatorBoundUpTo u T G)
    (hω : uniformVorticityBoundUpTo u T B) :
    0 ≤ G * B ∧
      ∀ t x, 0 ≤ t → t ≤ T →
        ‖vorticityMaterialDiffusionRemainder ν u t x‖ ≤ G * B := by
  refine ⟨(uniform_vorticityStretchingTerm_boundUpTo hG hω).1, ?_⟩
  intro t x ht0 htT
  rw [vorticityMaterialDiffusionRemainder_eq_vorticityStretchingTerm hEq ht0 htT]
  exact (uniform_vorticityStretchingTerm_boundUpTo hG hω).2 t x ht0 htT

/-- Uniform gradient and vorticity bounds control enstrophy production from the
material-minus-diffusion remainder under the standard vorticity equation. -/
theorem uniform_vorticityMaterialDiffusionPower_boundUpTo
    {ν T G B : ℝ} {u : NSVelocityField}
    (hEq : concreteVorticityEquationOn ν u T)
    (hG : uniformSpatialGradientOperatorBoundUpTo u T G)
    (hω : uniformVorticityBoundUpTo u T B) :
    0 ≤ G * (B * B) ∧
      ∀ t x, 0 ≤ t → t ≤ T →
        |vorticityMaterialDiffusionPower ν u t x| ≤ G * (B * B) := by
  refine ⟨(uniform_vorticityStretchingPower_boundUpTo hG hω).1, ?_⟩
  intro t x ht0 htT
  rw [vorticityMaterialDiffusionPower_eq_vorticityStretchingPower hEq ht0 htT]
  exact (uniform_vorticityStretchingPower_boundUpTo hG hω).2 t x ht0 htT

/-- The BKM growth estimate available once the residual-curl equation has been
expanded to the standard vorticity equation. -/
def BKMStandardVorticityGrowthEstimateClosed : Prop :=
  ∀ (ν : ℝ) (u : NSVelocityField) (T G B : ℝ),
    concreteVorticityEquationOn ν u T →
      uniformSpatialGradientOperatorBoundUpTo u T G →
        uniformVorticityBoundUpTo u T B →
          (0 ≤ G * B ∧
            ∀ t x, 0 ≤ t → t ≤ T →
              ‖vorticityMaterialDiffusionRemainder ν u t x‖ ≤ G * B) ∧
          (0 ≤ G * (B * B) ∧
            ∀ t x, 0 ≤ t → t ≤ T →
              |vorticityMaterialDiffusionPower ν u t x| ≤ G * (B * B))

/-- Checked proof of the standard-vorticity-equation growth estimate package. -/
theorem BKMStandardVorticityGrowthEstimateClosed_proved :
    BKMStandardVorticityGrowthEstimateClosed := by
  intro ν u T G B hEq hG hB
  exact
    ⟨uniform_vorticityMaterialDiffusionRemainder_boundUpTo hEq hG hB,
      uniform_vorticityMaterialDiffusionPower_boundUpTo hEq hG hB⟩

/-- Checked a-priori vorticity enstrophy estimate: after the enstrophy balance
has been established, the derivative of `1 / 2 * int |omega|^2` is bounded
above by the stretching-power integral. -/
def BKMVorticityEnstrophyAprioriEstimateClosed : Prop :=
  ∀ (ν : ℝ) (u : NSVelocityField) (t : NSTime),
    0 ≤ ν →
      vorticityEnstrophyBalanceAt ν u t →
        vorticityEnstrophyStretchingControlledAt ν u t

/-- Checked proof of the BKM vorticity enstrophy a-priori estimate. -/
theorem BKMVorticityEnstrophyAprioriEstimateClosed_proved :
    BKMVorticityEnstrophyAprioriEstimateClosed := by
  intro ν u t hν hBal
  exact vorticityEnstrophyStretchingControlledAt_of_balance hν u hBal

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
