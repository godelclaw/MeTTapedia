import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMVorticityEquation
import Mathlib.Analysis.InnerProductSpace.Calculus
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

/-- Pointwise `1 / 2`-normalized vorticity enstrophy density. -/
def normalizedVorticityEnstrophyDensity
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : ℝ :=
  (1 / 2 : ℝ) * vorticityEnstrophyDensity u t x

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

/-- Spatial integral of the vorticity time-pairing `omega · partial_t omega`.
This is the derivative of `1 / 2 * int |omega|^2` once differentiation under
the spatial integral has been justified. -/
def vorticityTimePowerIntegral
    (u : NSVelocityField) (t : NSTime) : ℝ :=
  ∫ x, ⟪spatialVorticity u t x, timeVorticityDerivative u t x⟫ ∂volume

/-- Pointwise density derivative integrand for the normalized vorticity
enstrophy density: `omega · partial_t omega`. -/
def vorticityEnstrophyDensityTimeDerivativeIntegrand
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : ℝ :=
  ⟪spatialVorticity u t x, timeVorticityDerivative u t x⟫

/-- Directional derivative of the normalized enstrophy density along the
velocity field.  Transport cancellation reduces this integral to a boundary
or divergence theorem statement under incompressibility. -/
def normalizedVorticityEnstrophyDensityTransport
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : ℝ :=
  (1 / 2 : ℝ) *
    fderiv ℝ (fun y : NSSpace => vorticityEnstrophyDensity u t y) x (u t x)

/-- Spatial integral of the directional derivative of `1 / 2 * |omega|^2`
along the velocity field. -/
def normalizedVorticityEnstrophyDensityTransportIntegral
    (u : NSVelocityField) (t : NSTime) : ℝ :=
  ∫ x, normalizedVorticityEnstrophyDensityTransport u t x ∂volume

/-- Spatial integral of the vorticity transport pairing
`omega · ((u · grad) omega)`.  This is the term that vanishes by
incompressibility and spatial integration by parts in the enstrophy balance. -/
def vorticityTransportPowerIntegral
    (u : NSVelocityField) (t : NSTime) : ℝ :=
  ∫ x, ⟪spatialVorticity u t x, vorticityTransportTerm u t x⟫ ∂volume

/-- Spatial integral of the vorticity diffusion pairing
`omega · Delta omega`.  This becomes `- int |grad omega|^2` after the viscous
integration-by-parts step. -/
def vorticityDiffusionPowerIntegral
    (u : NSVelocityField) (t : NSTime) : ℝ :=
  ∫ x, ⟪spatialVorticity u t x, vorticityDiffusionTerm u t x⟫ ∂volume

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

/-- The derivative obtained directly from pairing the standard vorticity
equation with `omega`, before applying transport cancellation and diffusion
integration by parts. -/
def vorticityEnstrophyRawBalanceDerivative
    (ν : ℝ) (u : NSVelocityField) (t : NSTime) : ℝ :=
  -vorticityTransportPowerIntegral u t +
    ν * vorticityDiffusionPowerIntegral u t +
      vorticityStretchingPowerIntegral u t

/-- Local-in-time vorticity enstrophy balance at one time.  Proving this from
the pointwise vorticity equation requires the transport cancellation and
viscous integration-by-parts step; once supplied, the a-priori inequality below
is pure order algebra. -/
def vorticityEnstrophyBalanceAt
    (ν : ℝ) (u : NSVelocityField) (t : NSTime) : Prop :=
  HasDerivAt (fun s => normalizedVorticityEnstrophyAt u s)
    (vorticityEnstrophyBalanceDerivative ν u t) t

/-- Raw local-in-time vorticity enstrophy derivative before the transport and
diffusion integral identities are applied. -/
def vorticityEnstrophyRawBalanceAt
    (ν : ℝ) (u : NSVelocityField) (t : NSTime) : Prop :=
  HasDerivAt (fun s => normalizedVorticityEnstrophyAt u s)
    (vorticityEnstrophyRawBalanceDerivative ν u t) t

/-- The time-pairing form of the vorticity enstrophy derivative.  The remaining
step from here to the raw BKM balance is pairing the standard vorticity
equation with `omega`. -/
def vorticityEnstrophyTimePairingDerivativeAt
    (u : NSVelocityField) (t : NSTime) : Prop :=
  HasDerivAt (fun s => normalizedVorticityEnstrophyAt u s)
    (vorticityTimePowerIntegral u t) t

/-- The concrete vorticity time derivative represents the derivative of the
vorticity curve at a fixed spatial point. -/
def vorticityTimeDerivativeRepresentedAt
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : Prop :=
  HasDerivAt (fun s => spatialVorticity u s x) (timeVorticityDerivative u t x) t

/-- The concrete spatial derivative of vorticity represents the Fréchet
derivative of the vorticity time slice at a fixed spatial point. -/
def vorticitySpatialDerivativeRepresentedAt
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : Prop :=
  HasFDerivAt (fun y => spatialVorticity u t y)
    (spatialFDeriv (fun s y => spatialVorticity u s y) t x) x

/-- Integrability hypotheses needed to distribute the raw paired vorticity
equation over the spatial integral. -/
def vorticityRawBalanceIntegralComponentsIntegrableAt
    (u : NSVelocityField) (t : NSTime) : Prop :=
  Integrable (fun x => ⟪spatialVorticity u t x, vorticityTransportTerm u t x⟫) ∧
    Integrable (fun x => ⟪spatialVorticity u t x, vorticityDiffusionTerm u t x⟫) ∧
      Integrable (fun x => vorticityStretchingPower u t x)

/-- The incompressible transport cancellation needed by the vorticity
enstrophy balance. -/
def vorticityTransportCancellationAt
    (u : NSVelocityField) (t : NSTime) : Prop :=
  vorticityTransportPowerIntegral u t = 0

/-- The viscous integration-by-parts identity needed by the vorticity enstrophy
balance. -/
def vorticityDiffusionIntegrationByPartsAt
    (u : NSVelocityField) (t : NSTime) : Prop :=
  vorticityDiffusionPowerIntegral u t =
    -vorticityDiffusionDissipationAt u t

/-- The a-priori control shape for vorticity enstrophy: the derivative of
`1 / 2 * int |omega|^2` exists and is bounded above by the stretching-power
integral. -/
def vorticityEnstrophyStretchingControlledAt
    (_ν : ℝ) (u : NSVelocityField) (t : NSTime) : Prop :=
  ∃ D : ℝ,
    HasDerivAt (fun s => normalizedVorticityEnstrophyAt u s) D t ∧
      D ≤ vorticityStretchingPowerIntegral u t

/-- Vorticity enstrophy growth controlled by a pointwise gradient bound:
`d/dt (1 / 2 * int |omega|^2) <= G * int |omega|^2`. -/
def vorticityEnstrophyGradientControlledAt
    (_ν : ℝ) (u : NSVelocityField) (t : NSTime) (G : ℝ) : Prop :=
  ∃ D : ℝ,
    HasDerivAt (fun s => normalizedVorticityEnstrophyAt u s) D t ∧
      D ≤ G * vorticityEnstrophyAt u t

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

/-- At a fixed spatial point, the derivative of `1 / 2 * |omega|^2` is the
time pairing `omega · partial_t omega`. -/
theorem hasDerivAt_normalizedVorticityEnstrophyDensity_of_timeDerivativeRepresented
    {u : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hω : vorticityTimeDerivativeRepresentedAt u t x) :
    HasDerivAt (fun s => normalizedVorticityEnstrophyDensity u s x)
      (vorticityEnstrophyDensityTimeDerivativeIntegrand u t x) t := by
  have hsq :
      HasDerivAt
        (fun s => vorticityEnstrophyDensity u s x)
        (2 * ⟪spatialVorticity u t x, timeVorticityDerivative u t x⟫) t := by
    simpa [vorticityTimeDerivativeRepresentedAt, vorticityEnstrophyDensity]
      using hω.norm_sq
  have hhalf := hsq.const_mul (1 / 2 : ℝ)
  simpa [normalizedVorticityEnstrophyDensity,
    vorticityEnstrophyDensityTimeDerivativeIntegrand] using hhalf

/-- Pointwise transport algebra: `omega · ((u · grad) omega)` is the velocity
directional derivative of `1 / 2 * |omega|^2`. -/
theorem normalizedVorticityEnstrophyDensityTransport_eq_transportPower
    {u : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hω : vorticitySpatialDerivativeRepresentedAt u t x) :
    normalizedVorticityEnstrophyDensityTransport u t x =
      ⟪spatialVorticity u t x, vorticityTransportTerm u t x⟫ := by
  have hsq :
      HasFDerivAt
        (fun y => vorticityEnstrophyDensity u t y)
        (2 • (innerSL ℝ (spatialVorticity u t x)).comp
          (spatialFDeriv (fun s y => spatialVorticity u s y) t x)) x := by
    simpa [vorticitySpatialDerivativeRepresentedAt, vorticityEnstrophyDensity]
      using hω.norm_sq
  have hfderiv :
      fderiv ℝ (fun y : NSSpace => vorticityEnstrophyDensity u t y) x =
        2 • (innerSL ℝ (spatialVorticity u t x)).comp
          (spatialFDeriv (fun s y => spatialVorticity u s y) t x) := by
    simpa using hsq.fderiv
  simp [normalizedVorticityEnstrophyDensityTransport, vorticityTransportTerm,
    hfderiv, innerSL_apply_apply]

/-- If the spatial vorticity derivative is represented pointwise, the transport
power integral is the integral of the velocity directional derivative of
`1 / 2 * |omega|^2`. -/
theorem vorticityTransportPowerIntegral_eq_normalizedDensityTransportIntegral
    {u : NSVelocityField} {t : NSTime}
    (hω : ∀ x, vorticitySpatialDerivativeRepresentedAt u t x) :
    vorticityTransportPowerIntegral u t =
      normalizedVorticityEnstrophyDensityTransportIntegral u t := by
  unfold vorticityTransportPowerIntegral
    normalizedVorticityEnstrophyDensityTransportIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    (normalizedVorticityEnstrophyDensityTransport_eq_transportPower
      (hω x)).symm

/-- Once the normalized density transport integral is zero, the pointwise
transport algebra gives the BKM transport cancellation.  The remaining analytic
work is proving this zero integral from incompressibility and boundary/decay
conditions. -/
theorem vorticityTransportCancellationAt_of_normalizedDensityTransportIntegral_zero
    {u : NSVelocityField} {t : NSTime}
    (hω : ∀ x, vorticitySpatialDerivativeRepresentedAt u t x)
    (hZero : normalizedVorticityEnstrophyDensityTransportIntegral u t = 0) :
    vorticityTransportCancellationAt u t := by
  unfold vorticityTransportCancellationAt
  rw [vorticityTransportPowerIntegral_eq_normalizedDensityTransportIntegral hω,
    hZero]

/-- A pointwise gradient bound controls the integrated vorticity-stretching
power by `G * int |omega|^2`. -/
theorem vorticityStretchingPowerIntegral_le_gradient_mul_enstrophyAt
    {u : NSVelocityField} {t : NSTime} {G : ℝ}
    (hG : 0 ≤ G)
    (hGrad : ∀ x, ‖spatialFDeriv u t x‖ ≤ G)
    (hStretchInt : Integrable (fun x => vorticityStretchingPower u t x))
    (hEnstrophyInt : Integrable (fun x => vorticityEnstrophyDensity u t x)) :
    vorticityStretchingPowerIntegral u t ≤ G * vorticityEnstrophyAt u t := by
  have hRightInt : Integrable (fun x => G * vorticityEnstrophyDensity u t x) :=
    hEnstrophyInt.const_mul G
  calc
    vorticityStretchingPowerIntegral u t
        = ∫ x, vorticityStretchingPower u t x ∂volume := by
          rfl
    _ ≤ ∫ x, G * vorticityEnstrophyDensity u t x ∂volume := by
          exact integral_mono hStretchInt hRightInt fun x => by
            have hωprod_nonneg :
                0 ≤ ‖spatialVorticity u t x‖ *
                  ‖spatialVorticity u t x‖ :=
              mul_nonneg (norm_nonneg _) (norm_nonneg _)
            have habs :
                |vorticityStretchingPower u t x| ≤
                  G * (‖spatialVorticity u t x‖ *
                    ‖spatialVorticity u t x‖) :=
              (abs_vorticityStretchingPower_le u t x).trans
                (mul_le_mul (hGrad x) le_rfl hωprod_nonneg hG)
            calc
              vorticityStretchingPower u t x
                  ≤ |vorticityStretchingPower u t x| := le_abs_self _
              _ ≤ G * (‖spatialVorticity u t x‖ *
                    ‖spatialVorticity u t x‖) := habs
              _ = G * vorticityEnstrophyDensity u t x := by
                    simp [vorticityEnstrophyDensity, pow_two]
    _ = G * vorticityEnstrophyAt u t := by
          rw [vorticityEnstrophyAt, integral_const_mul]

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

/-- Stretching-control plus the integrated gradient/enstrophy comparison gives
the usual BKM enstrophy growth inequality. -/
theorem vorticityEnstrophyGradientControlledAt_of_stretchingControlled_integral
    {ν G : ℝ} {u : NSVelocityField} {t : NSTime}
    (hStretching : vorticityEnstrophyStretchingControlledAt ν u t)
    (hIntegral :
      vorticityStretchingPowerIntegral u t ≤ G * vorticityEnstrophyAt u t) :
    vorticityEnstrophyGradientControlledAt ν u t G := by
  rcases hStretching with ⟨D, hD, hDle⟩
  exact ⟨D, hD, hDle.trans hIntegral⟩

/-- If the enstrophy balance is known and `||grad u||` is pointwise bounded by
`G`, then normalized vorticity enstrophy grows at most like
`G * int |omega|^2`. -/
theorem vorticityEnstrophyGradientControlledAt_of_balance_gradient_bound
    {ν G : ℝ} {u : NSVelocityField} {t : NSTime}
    (hν : 0 ≤ ν)
    (hBal : vorticityEnstrophyBalanceAt ν u t)
    (hG : 0 ≤ G)
    (hGrad : ∀ x, ‖spatialFDeriv u t x‖ ≤ G)
    (hStretchInt : Integrable (fun x => vorticityStretchingPower u t x))
    (hEnstrophyInt : Integrable (fun x => vorticityEnstrophyDensity u t x)) :
    vorticityEnstrophyGradientControlledAt ν u t G := by
  exact
    vorticityEnstrophyGradientControlledAt_of_stretchingControlled_integral
      (vorticityEnstrophyStretchingControlledAt_of_balance hν u hBal)
      (vorticityStretchingPowerIntegral_le_gradient_mul_enstrophyAt
        hG hGrad hStretchInt hEnstrophyInt)

/-- The raw paired vorticity equation becomes the standard enstrophy balance
once transport cancellation and viscous integration by parts are supplied. -/
theorem vorticityEnstrophyBalanceAt_of_rawBalance_transportCancellation_diffusionIBP
    {ν : ℝ} {u : NSVelocityField} {t : NSTime}
    (hRaw : vorticityEnstrophyRawBalanceAt ν u t)
    (hTransport : vorticityTransportCancellationAt u t)
    (hDiffusion : vorticityDiffusionIntegrationByPartsAt u t) :
    vorticityEnstrophyBalanceAt ν u t := by
  unfold vorticityEnstrophyBalanceAt vorticityEnstrophyRawBalanceAt at *
  convert hRaw using 1
  unfold vorticityEnstrophyRawBalanceDerivative
    vorticityEnstrophyBalanceDerivative
    vorticityTransportCancellationAt
    vorticityDiffusionIntegrationByPartsAt at *
  rw [hTransport, hDiffusion]
  ring

/-- Combining the raw balance, transport cancellation, and diffusion
integration by parts gives the stretching-controlled enstrophy estimate. -/
theorem vorticityEnstrophyStretchingControlledAt_of_rawBalance_transportCancellation_diffusionIBP
    {ν : ℝ} (hν : 0 ≤ ν) {u : NSVelocityField} {t : NSTime}
    (hRaw : vorticityEnstrophyRawBalanceAt ν u t)
    (hTransport : vorticityTransportCancellationAt u t)
    (hDiffusion : vorticityDiffusionIntegrationByPartsAt u t) :
    vorticityEnstrophyStretchingControlledAt ν u t := by
  exact
    vorticityEnstrophyStretchingControlledAt_of_balance hν u
      (vorticityEnstrophyBalanceAt_of_rawBalance_transportCancellation_diffusionIBP
        hRaw hTransport hDiffusion)

/-- Pairing the standard vorticity equation with `omega` gives the scalar
time/transport/diffusion/stretching balance at each point. -/
theorem vorticityTimePairing_eq_rawBalanceIntegrand_of_concreteVorticityEquationOn
    {ν T : ℝ} {u : NSVelocityField}
    (hEq : concreteVorticityEquationOn ν u T)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ⟪spatialVorticity u t x, timeVorticityDerivative u t x⟫ =
      -⟪spatialVorticity u t x, vorticityTransportTerm u t x⟫ +
        ν * ⟪spatialVorticity u t x, vorticityDiffusionTerm u t x⟫ +
          vorticityStretchingPower u t x := by
  let ω : NSSpace := spatialVorticity u t x
  have heq := hEq t x ht0 htT
  have htime :
      timeVorticityDerivative u t x =
        ν • vorticityDiffusionTerm u t x +
          vorticityStretchingTerm u t x -
            vorticityTransportTerm u t x := by
    calc
      timeVorticityDerivative u t x =
          timeVorticityDerivative u t x + vorticityTransportTerm u t x -
            vorticityTransportTerm u t x := by
              abel
      _ = ν • vorticityDiffusionTerm u t x +
          vorticityStretchingTerm u t x -
            vorticityTransportTerm u t x := by
              rw [heq]
  rw [htime]
  simp [vorticityStretchingPower, inner_add_right, inner_sub_right,
    real_inner_smul_right]
  ring_nf

/-- The pointwise paired standard vorticity equation integrates to the raw
enstrophy-balance derivative once the transport, diffusion, and stretching
pairings are integrable. -/
theorem vorticityTimePowerIntegral_eq_rawBalanceDerivative_of_concreteVorticityEquationOn
    {ν T : ℝ} {u : NSVelocityField} {t : NSTime}
    (hEq : concreteVorticityEquationOn ν u T)
    (hInt : vorticityRawBalanceIntegralComponentsIntegrableAt u t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityTimePowerIntegral u t =
      vorticityEnstrophyRawBalanceDerivative ν u t := by
  let transportPower : NSSpace → ℝ :=
    fun x => ⟪spatialVorticity u t x, vorticityTransportTerm u t x⟫
  let diffusionPower : NSSpace → ℝ :=
    fun x => ⟪spatialVorticity u t x, vorticityDiffusionTerm u t x⟫
  let stretchingPower : NSSpace → ℝ := fun x => vorticityStretchingPower u t x
  have hTransportInt : Integrable transportPower := hInt.1
  have hDiffusionInt : Integrable diffusionPower := hInt.2.1
  have hStretchingInt : Integrable stretchingPower := hInt.2.2
  have hNegTransportInt : Integrable (fun x => -transportPower x) :=
    hTransportInt.neg
  have hViscousDiffusionInt : Integrable (fun x => ν * diffusionPower x) :=
    hDiffusionInt.const_mul ν
  have hSumInt :
      Integrable (fun x => -transportPower x + ν * diffusionPower x) :=
    hNegTransportInt.add hViscousDiffusionInt
  calc
    vorticityTimePowerIntegral u t
        = ∫ x, (-transportPower x + ν * diffusionPower x + stretchingPower x) ∂volume := by
          unfold vorticityTimePowerIntegral
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x =>
            vorticityTimePairing_eq_rawBalanceIntegrand_of_concreteVorticityEquationOn
              hEq ht0 htT
    _ = (∫ x, (-transportPower x + ν * diffusionPower x) ∂volume) +
          ∫ x, stretchingPower x ∂volume := by
          rw [integral_add hSumInt hStretchingInt]
    _ = ((∫ x, -transportPower x ∂volume) +
          ∫ x, ν * diffusionPower x ∂volume) +
            ∫ x, stretchingPower x ∂volume := by
          rw [integral_add hNegTransportInt hViscousDiffusionInt]
    _ = -vorticityTransportPowerIntegral u t +
          ν * vorticityDiffusionPowerIntegral u t +
            vorticityStretchingPowerIntegral u t := by
          rw [integral_neg, integral_const_mul]
          rfl
    _ = vorticityEnstrophyRawBalanceDerivative ν u t := by
          rfl

/-- If the derivative of vorticity enstrophy is represented by the time
pairing, then the standard vorticity equation gives the raw BKM balance. -/
theorem vorticityEnstrophyRawBalanceAt_of_timePairingDerivative_concreteVorticityEquationOn
    {ν T : ℝ} {u : NSVelocityField} {t : NSTime}
    (hEq : concreteVorticityEquationOn ν u T)
    (hInt : vorticityRawBalanceIntegralComponentsIntegrableAt u t)
    (hTime : vorticityEnstrophyTimePairingDerivativeAt u t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityEnstrophyRawBalanceAt ν u t := by
  unfold vorticityEnstrophyRawBalanceAt vorticityEnstrophyTimePairingDerivativeAt at *
  rw [← vorticityTimePowerIntegral_eq_rawBalanceDerivative_of_concreteVorticityEquationOn
    hEq hInt ht0 htT]
  exact hTime

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

/-- Checked pointwise part of the BKM enstrophy derivative.  The remaining
analytic step is to integrate this pointwise derivative in space and justify
differentiation under the integral. -/
def BKMVorticityPointwiseEnstrophyDerivativeClosed : Prop :=
  ∀ (u : NSVelocityField) (t : NSTime) (x : NSSpace),
    vorticityTimeDerivativeRepresentedAt u t x →
      HasDerivAt (fun s => normalizedVorticityEnstrophyDensity u s x)
        (vorticityEnstrophyDensityTimeDerivativeIntegrand u t x) t

/-- Checked proof of the pointwise normalized vorticity enstrophy derivative. -/
theorem BKMVorticityPointwiseEnstrophyDerivativeClosed_proved :
    BKMVorticityPointwiseEnstrophyDerivativeClosed := by
  intro u t x hω
  exact hasDerivAt_normalizedVorticityEnstrophyDensity_of_timeDerivativeRepresented hω

/-- Checked gradient-bound form of the BKM vorticity enstrophy growth estimate:
after the enstrophy balance is established, a pointwise gradient bound controls
the normalized enstrophy derivative by `G * int |omega|^2`. -/
def BKMVorticityEnstrophyGradientGrowthClosed : Prop :=
  ∀ (ν : ℝ) (u : NSVelocityField) (t : NSTime) (G : ℝ),
    0 ≤ ν →
      vorticityEnstrophyBalanceAt ν u t →
        0 ≤ G →
          (∀ x, ‖spatialFDeriv u t x‖ ≤ G) →
            Integrable (fun x => vorticityStretchingPower u t x) →
              Integrable (fun x => vorticityEnstrophyDensity u t x) →
                vorticityEnstrophyGradientControlledAt ν u t G

/-- Checked proof of the gradient-bound vorticity enstrophy growth package. -/
theorem BKMVorticityEnstrophyGradientGrowthClosed_proved :
    BKMVorticityEnstrophyGradientGrowthClosed := by
  intro ν u t G hν hBal hG hGrad hStretchInt hEnstrophyInt
  exact
    vorticityEnstrophyGradientControlledAt_of_balance_gradient_bound
      hν hBal hG hGrad hStretchInt hEnstrophyInt

/-- Checked transport-cancellation algebra: after the pointwise spatial
vorticity derivative is represented, transport cancellation is reduced to the
zero integral of the velocity directional derivative of `1 / 2 * |omega|^2`. -/
def BKMVorticityTransportCancellationAlgebraClosed : Prop :=
  ∀ (u : NSVelocityField) (t : NSTime),
    (∀ x, vorticitySpatialDerivativeRepresentedAt u t x) →
      normalizedVorticityEnstrophyDensityTransportIntegral u t = 0 →
        vorticityTransportCancellationAt u t

/-- Checked proof of the BKM vorticity transport-cancellation algebra package. -/
theorem BKMVorticityTransportCancellationAlgebraClosed_proved :
    BKMVorticityTransportCancellationAlgebraClosed := by
  intro u t hω hZero
  exact vorticityTransportCancellationAt_of_normalizedDensityTransportIntegral_zero
    hω hZero

/-- Checked assembly of the vorticity enstrophy balance from the raw paired
equation plus the two integral identities. -/
def BKMVorticityEnstrophyBalanceAssemblyClosed : Prop :=
  ∀ (ν : ℝ) (u : NSVelocityField) (t : NSTime),
    vorticityEnstrophyRawBalanceAt ν u t →
      vorticityTransportCancellationAt u t →
        vorticityDiffusionIntegrationByPartsAt u t →
          vorticityEnstrophyBalanceAt ν u t

/-- Checked proof of the vorticity enstrophy balance assembly. -/
theorem BKMVorticityEnstrophyBalanceAssemblyClosed_proved :
    BKMVorticityEnstrophyBalanceAssemblyClosed := by
  intro ν u t hRaw hTransport hDiffusion
  exact
    vorticityEnstrophyBalanceAt_of_rawBalance_transportCancellation_diffusionIBP
      hRaw hTransport hDiffusion

/-- Checked reduction of the raw enstrophy balance to the standard vorticity
equation paired with `omega`, plus differentiation-under-the-integral and
integrability hypotheses. -/
def BKMVorticityRawBalanceFromStandardEquationClosed : Prop :=
  ∀ (ν T : ℝ) (u : NSVelocityField) (t : NSTime),
    concreteVorticityEquationOn ν u T →
      vorticityRawBalanceIntegralComponentsIntegrableAt u t →
        vorticityEnstrophyTimePairingDerivativeAt u t →
          0 ≤ t →
            t ≤ T →
              vorticityEnstrophyRawBalanceAt ν u t

/-- Checked proof that the standard vorticity equation implies the raw
enstrophy balance under the explicit integral derivative hypotheses. -/
theorem BKMVorticityRawBalanceFromStandardEquationClosed_proved :
    BKMVorticityRawBalanceFromStandardEquationClosed := by
  intro ν T u t hEq hInt hTime ht0 htT
  exact
    vorticityEnstrophyRawBalanceAt_of_timePairingDerivative_concreteVorticityEquationOn
      hEq hInt hTime ht0 htT

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
