import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMVorticityEquation
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergySchwartzDissipationViscous
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
open scoped Laplacian LineDeriv RealInnerProductSpace SchwartzMap

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

/-- Density of the viscous vorticity dissipation term `|grad omega|^2`,
coordinatewise in the standard orthonormal basis of `ℝ^3`.  This is the
Hilbert-gradient square that matches the Laplacian integration-by-parts
identity. -/
def vorticityDiffusionDissipationDensity
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : ℝ :=
  ∑ i : NSStdBasisIndex,
    ‖spatialFDeriv (fun s y => spatialVorticity u s y) t x (nsStdBasis i)‖ ^ (2 : ℕ)

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

/-- A scalar Schwartz density transported by a divergence-free Schwartz
velocity slice has zero spatial integral.  This is the boundary/decay part of
the BKM transport cancellation step. -/
theorem integral_schwartzScalar_directionalDerivative_of_schwartzVectorSlice_spatialDivergence_zero
    (u : NSVelocityField) (t : NSTime)
    (v : 𝓢(NSSpace, NSSpace)) (φ : 𝓢(NSSpace, ℝ))
    (hslice : ∀ x, u t x = v x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    ∫ x, fderiv ℝ (φ : NSSpace → ℝ) x (u t x) ∂volume = 0 := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) v
  have hsliceFun : (fun x : NSSpace => u t x) = (v : NSSpace → NSSpace) :=
    funext hslice
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (v x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hCoordDeriv (i : Fin 3) (x : NSSpace) :
      (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x =
        (∂_{EuclideanSpace.single i (1 : ℝ)} v x) i := by
    have hcoordFun : (coord i : NSSpace → ℝ) = fun y : NSSpace => (v y) i := by
      funext y
      simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
    have hproj :=
      congrArg
        (fun L : NSSpace →L[ℝ] ℝ => L (EuclideanSpace.single i (1 : ℝ)))
        (((EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).hasFDerivAt.comp x
          (v.hasFDerivAt x)).fderiv)
    calc
      (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x =
          fderiv ℝ (fun y : NSSpace => (v y) i) x
            (EuclideanSpace.single i (1 : ℝ)) := by
        rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hcoordFun]
      _ = fderiv ℝ v x (EuclideanSpace.single i (1 : ℝ)) i := by
        change fderiv ℝ ((fun y : NSSpace => y i) ∘ (v : NSSpace → NSSpace)) x
            (EuclideanSpace.single i (1 : ℝ)) =
          fderiv ℝ v x (EuclideanSpace.single i (1 : ℝ)) i
        simpa [ContinuousLinearMap.comp_apply] using hproj
      _ = (∂_{EuclideanSpace.single i (1 : ℝ)} v x) i := by
        rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hDirectionalEq :
      (fun x : NSSpace => fderiv ℝ (φ : NSSpace → ℝ) x (u t x)) =
        fun x : NSSpace =>
          ∑ i : Fin 3,
            coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} φ) x := by
    funext x
    have hVec :
        v x = ∑ i : Fin 3, coord i x • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      change (v x).ofLp j =
        (∑ i : Fin 3, coord i x • EuclideanSpace.single i (1 : ℝ)).ofLp j
      fin_cases j <;> rw [Fin.sum_univ_three] <;> simp [hCoordEq]
    rw [hslice x, hVec, map_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [ContinuousLinearMap.map_smul]
    simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} φ) x) := by
    refine ((SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (coord i)
        (∂_{EuclideanSpace.single i (1 : ℝ)} φ)).integrable).congr ?_
    filter_upwards with x
    rw [SchwartzMap.pairing_apply_apply]
    rfl
  have hDivTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * φ x) := by
    refine ((SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i))
        φ).integrable).congr ?_
    filter_upwards with x
    rw [SchwartzMap.pairing_apply_apply]
    rfl
  have hDivEq (x : NSSpace) :
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x = 0 := by
    have hx : spatialDivergence u t x = 0 := hdiv x
    rw [spatialDivergence, spatialFDeriv, hsliceFun] at hx
    convert hx using 1
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact hCoordDeriv i x
  calc
    ∫ x, fderiv ℝ (φ : NSSpace → ℝ) x (u t x) ∂volume
        = ∫ x,
            ∑ i : Fin 3,
              coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} φ) x ∂volume := by
          rw [hDirectionalEq]
    _ = ∑ i : Fin 3,
          ∫ x, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} φ) x ∂volume := by
          rw [integral_finsetSum]
          intro i hi
          exact hTermIntegrable i
    _ = ∑ i : Fin 3,
          -∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * φ x ∂volume := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left
            (coord i) φ (EuclideanSpace.single i (1 : ℝ))]
    _ = -∑ i : Fin 3,
          ∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * φ x ∂volume := by
          rw [Finset.sum_neg_distrib]
    _ = -∫ x,
          ∑ i : Fin 3,
            (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * φ x ∂volume := by
          congr 1
          rw [integral_finsetSum]
          intro i hi
          exact hDivTermIntegrable i
    _ = -∫ x, (0 : ℝ) ∂volume := by
          have hZeroFun :
              (fun x : NSSpace =>
                ∑ i : Fin 3,
                  (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * φ x) =
                fun _ : NSSpace => (0 : ℝ) := by
            funext x
            rw [← Finset.sum_mul, hDivEq x]
            simp
          rw [hZeroFun]
    _ = 0 := by simp

/-- A Schwartz vorticity slice represents the concrete spatial derivative
used in the transport algebra. -/
theorem vorticitySpatialDerivativeRepresentedAt_of_schwartzVorticitySlice
    (u : NSVelocityField) (t : NSTime) (ω : 𝓢(NSSpace, NSSpace))
    (hω : ∀ x, spatialVorticity u t x = ω x) :
    ∀ x, vorticitySpatialDerivativeRepresentedAt u t x := by
  intro x
  have hfun : (fun y : NSSpace => spatialVorticity u t y) =
      (ω : NSSpace → NSSpace) :=
    funext hω
  unfold vorticitySpatialDerivativeRepresentedAt spatialFDeriv
  rw [hfun]
  exact ω.hasFDerivAt x

/-- For a divergence-free Schwartz velocity slice and a Schwartz vorticity
slice, the transported normalized enstrophy density has zero integral. -/
theorem normalizedVorticityEnstrophyDensityTransportIntegral_eq_zero_of_schwartzVelocitySlice_schwartzVorticitySlice_spatialDivergence_zero
    (u : NSVelocityField) (t : NSTime)
    (v ω : 𝓢(NSSpace, NSSpace))
    (hu : ∀ x, u t x = v x)
    (hω : ∀ x, spatialVorticity u t x = ω x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    normalizedVorticityEnstrophyDensityTransportIntegral u t = 0 := by
  let normSq : 𝓢(NSSpace, ℝ) := SchwartzMap.pairing (innerSL ℝ) ω ω
  have hDensityEq :
      (fun y : NSSpace => vorticityEnstrophyDensity u t y) =
        (normSq : NSSpace → ℝ) := by
    funext y
    rw [vorticityEnstrophyDensity, hω y, SchwartzMap.pairing_apply_apply]
    change ‖ω y‖ ^ (2 : ℕ) = ⟪ω y, ω y⟫
    rw [real_inner_self_eq_norm_sq]
  have hTransportEq :
      normalizedVorticityEnstrophyDensityTransport u t =
        fun x : NSSpace =>
          (1 / 2 : ℝ) * fderiv ℝ (normSq : NSSpace → ℝ) x (u t x) := by
    funext x
    unfold normalizedVorticityEnstrophyDensityTransport
    rw [hDensityEq]
  unfold normalizedVorticityEnstrophyDensityTransportIntegral
  rw [hTransportEq, integral_const_mul]
  rw [
    integral_schwartzScalar_directionalDerivative_of_schwartzVectorSlice_spatialDivergence_zero
      u t v normSq hu hdiv]
  ring

/-- The full BKM transport cancellation follows from incompressibility when
both the velocity and vorticity slices are Schwartz. -/
theorem vorticityTransportCancellationAt_of_schwartzVelocitySlice_schwartzVorticitySlice_spatialDivergence_zero
    (u : NSVelocityField) (t : NSTime)
    (v ω : 𝓢(NSSpace, NSSpace))
    (hu : ∀ x, u t x = v x)
    (hω : ∀ x, spatialVorticity u t x = ω x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    vorticityTransportCancellationAt u t := by
  exact
    vorticityTransportCancellationAt_of_normalizedDensityTransportIntegral_zero
      (vorticitySpatialDerivativeRepresentedAt_of_schwartzVorticitySlice
        u t ω hω)
      (normalizedVorticityEnstrophyDensityTransportIntegral_eq_zero_of_schwartzVelocitySlice_schwartzVorticitySlice_spatialDivergence_zero
        u t v ω hu hω hdiv)

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
  unfold vorticityDiffusionDissipationDensity
  exact Finset.sum_nonneg fun i _ => by positivity

/-- The vorticity diffusion dissipation density is the coordinate enstrophy
density of the vorticity field. -/
theorem vorticityDiffusionDissipationDensity_eq_coordinateEnstrophyDensity_vorticityField
    (u : NSVelocityField) (t : NSTime) :
    vorticityDiffusionDissipationDensity u t =
      coordinateEnstrophyDensity (fun s y => spatialVorticity u s y) t := by
  rfl

/-- The vorticity diffusion dissipation is the coordinate enstrophy of the
vorticity field. -/
theorem vorticityDiffusionDissipationAt_eq_coordinateEnstrophyAt_vorticityField
    (u : NSVelocityField) (t : NSTime) :
    vorticityDiffusionDissipationAt u t =
      coordinateEnstrophyAt (fun s y => spatialVorticity u s y) t := by
  rfl

/-- Vorticity diffusion dissipation is nonnegative on the unguarded integral
surface. -/
theorem vorticityDiffusionDissipationAt_nonneg
    (u : NSVelocityField) (t : NSTime) :
    0 ≤ vorticityDiffusionDissipationAt u t := by
  rw [vorticityDiffusionDissipationAt]
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x =>
      vorticityDiffusionDissipationDensity_nonneg u t x)

/-- On a Schwartz vorticity slice, mathlib's Schwartz-space Laplacian
integration by parts gives the viscous vorticity identity
`int omega dot Delta omega = -int |grad omega|^2`. -/
theorem vorticityDiffusionIntegrationByPartsAt_of_schwartzVorticitySlice
    (u : NSVelocityField) (t : NSTime) (ω : 𝓢(NSSpace, NSSpace))
    (hω : ∀ x, spatialVorticity u t x = ω x) :
    vorticityDiffusionIntegrationByPartsAt u t := by
  have hIBP :=
    coordinateViscousEnergyPairingFormula_of_schwartzSlice
      (u := fun s y => spatialVorticity u s y) (t := t) (f := ω) hω
  simpa [vorticityDiffusionIntegrationByPartsAt, vorticityDiffusionPowerIntegral,
    vorticityDiffusionTerm, vorticityDiffusionDissipationAt,
    vorticityDiffusionDissipationDensity, laplacianEnergyPairing,
    coordinateEnstrophyAt, coordinateEnstrophyDensity] using hIBP

/-- Scalar Schwartz representative of a coordinate directional derivative of
a vector-valued Schwartz velocity slice. -/
def schwartzDirectionalComponent
    (v : 𝓢(NSSpace, NSSpace)) (coord comp : Fin 3) : 𝓢(NSSpace, ℝ) :=
  SchwartzMap.bilinLeftCLM
    (ContinuousLinearMap.apply ℝ ℝ)
    (g := fun _ : NSSpace => (EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ))
    (by fun_prop)
    (∂_{EuclideanSpace.single coord (1 : ℝ)} v)

/-- The scalar Schwartz directional component agrees with the concrete
coordinate derivative of the frozen velocity slice. -/
theorem schwartzDirectionalComponent_apply
    (v : 𝓢(NSSpace, NSSpace)) (coord comp : Fin 3) (x : NSSpace) :
    schwartzDirectionalComponent v coord comp x =
      spatialDerivativeComponent (fun _ y => v y) 0 x coord comp := by
  simp [schwartzDirectionalComponent, spatialDerivativeComponent, spatialFDeriv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.bilinLeftCLM_apply,
    ContinuousLinearMap.apply_apply]

/-- The concrete coordinate derivative of a Schwartz velocity slice is
pointwise controlled by the first unweighted Schwartz seminorm of the slice. -/
theorem spatialDerivativeComponent_abs_le_schwartzSeminorm_zero_one
    (v : 𝓢(NSSpace, NSSpace)) (coord comp : Fin 3) (x : NSSpace) :
    |spatialDerivativeComponent (fun _ y => v y) 0 x coord comp| ≤
      SchwartzMap.seminorm ℝ 0 1 v := by
  let e : NSSpace := EuclideanSpace.single coord (1 : ℝ)
  have hcomp :
      ‖(fderiv ℝ (v : NSSpace → NSSpace) x e) comp‖ ≤
        ‖fderiv ℝ (v : NSSpace → NSSpace) x e‖ := by
    exact PiLp.norm_apply_le (fderiv ℝ (v : NSSpace → NSSpace) x e) comp
  have hf_apply :
      ‖fderiv ℝ (v : NSSpace → NSSpace) x e‖ ≤
        ‖fderiv ℝ (v : NSSpace → NSSpace) x‖ := by
    calc
      ‖fderiv ℝ (v : NSSpace → NSSpace) x e‖
          ≤ ‖fderiv ℝ (v : NSSpace → NSSpace) x‖ * ‖e‖ := by
            exact ContinuousLinearMap.le_opNorm
              (fderiv ℝ (v : NSSpace → NSSpace) x) e
      _ ≤ ‖fderiv ℝ (v : NSSpace → NSSpace) x‖ * 1 := by
            gcongr
            simp [e]
      _ = ‖fderiv ℝ (v : NSSpace → NSSpace) x‖ := by
            rw [mul_one]
  have hf_norm :
      ‖fderiv ℝ (v : NSSpace → NSSpace) x‖ ≤
        SchwartzMap.seminorm ℝ 0 1 v := by
    rw [← norm_iteratedFDeriv_one
      (𝕜 := ℝ) (f := (v : NSSpace → NSSpace)) (x := x)]
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ v 1 x
  calc
    |spatialDerivativeComponent (fun _ y => v y) 0 x coord comp|
        = ‖(fderiv ℝ (v : NSSpace → NSSpace) x e) comp‖ := by
          simp [spatialDerivativeComponent, spatialFDeriv, e]
    _ ≤ ‖fderiv ℝ (v : NSSpace → NSSpace) x e‖ := hcomp
    _ ≤ ‖fderiv ℝ (v : NSSpace → NSSpace) x‖ := hf_apply
    _ ≤ SchwartzMap.seminorm ℝ 0 1 v := hf_norm

/-- Inject a scalar Schwartz component into one Euclidean coordinate axis. -/
def schwartzBasisComponent
    (comp : Fin 3) (φ : 𝓢(NSSpace, ℝ)) : 𝓢(NSSpace, NSSpace) :=
  SchwartzMap.bilinLeftCLM
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] NSSpace →L[ℝ] NSSpace)
    (g := fun _ : NSSpace => EuclideanSpace.single comp (1 : ℝ))
    (by fun_prop)
    φ

/-- Pointwise value of a scalar Schwartz component injected into one Euclidean
coordinate axis. -/
theorem schwartzBasisComponent_apply
    (comp : Fin 3) (φ : 𝓢(NSSpace, ℝ)) (x : NSSpace) :
    schwartzBasisComponent comp φ x = EuclideanSpace.single comp (φ x) := by
  ext i
  simp [schwartzBasisComponent, SchwartzMap.bilinLeftCLM_apply]

/-- Curl of a vector-valued Schwartz velocity slice as a vector-valued
Schwartz map. -/
def schwartzSpatialVorticitySlice (v : 𝓢(NSSpace, NSSpace)) :
    𝓢(NSSpace, NSSpace) :=
  schwartzBasisComponent nsCoord0
      (schwartzDirectionalComponent v nsCoord1 nsCoord2 -
        schwartzDirectionalComponent v nsCoord2 nsCoord1) +
    schwartzBasisComponent nsCoord1
      (schwartzDirectionalComponent v nsCoord2 nsCoord0 -
        schwartzDirectionalComponent v nsCoord0 nsCoord2) +
      schwartzBasisComponent nsCoord2
        (schwartzDirectionalComponent v nsCoord0 nsCoord1 -
          schwartzDirectionalComponent v nsCoord1 nsCoord0)

/-- The Schwartz curl slice agrees pointwise with the concrete spatial
vorticity of the frozen velocity slice. -/
theorem schwartzSpatialVorticitySlice_apply
    (v : 𝓢(NSSpace, NSSpace)) (x : NSSpace) :
    schwartzSpatialVorticitySlice v x =
      spatialVorticity (fun _ y => v y) 0 x := by
  ext i
  fin_cases i <;>
    simp [schwartzSpatialVorticitySlice, schwartzBasisComponent_apply,
      schwartzDirectionalComponent_apply, spatialVorticity]

/-- Scalar Schwartz representative of one Euclidean coordinate of a
vector-valued Schwartz slice. -/
def schwartzCoordinate
    (v : 𝓢(NSSpace, NSSpace)) (i : Fin 3) : 𝓢(NSSpace, ℝ) :=
  SchwartzMap.bilinLeftCLM
    (ContinuousLinearMap.apply ℝ ℝ)
    (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
    (by fun_prop) v

/-- The scalar Schwartz coordinate representative agrees pointwise with the
corresponding Euclidean coordinate. -/
theorem schwartzCoordinate_apply
    (v : 𝓢(NSSpace, NSSpace)) (i : Fin 3) (x : NSSpace) :
    schwartzCoordinate v i x = (v x) i := by
  simp [schwartzCoordinate, SchwartzMap.bilinLeftCLM_apply,
    ContinuousLinearMap.apply_apply]

/-- Schwartz representative of the directional field `(a . grad)b` for two
vector-valued Schwartz slices. -/
def schwartzDirectionalVectorField
    (a b : 𝓢(NSSpace, NSSpace)) : 𝓢(NSSpace, NSSpace) :=
  ∑ i : Fin 3,
    SchwartzMap.pairing
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] NSSpace →L[ℝ] NSSpace)
      (schwartzCoordinate a i)
      (∂_{EuclideanSpace.single i (1 : ℝ)} b)

/-- The Schwartz directional field is the concrete Frechet directional
derivative of the target slice. -/
theorem schwartzDirectionalVectorField_apply
    (a b : 𝓢(NSSpace, NSSpace)) (x : NSSpace) :
    schwartzDirectionalVectorField a b x =
      fderiv ℝ (b : NSSpace → NSSpace) x (a x) := by
  have hVec :
      a x = ∑ i : Fin 3, schwartzCoordinate a i x •
        EuclideanSpace.single i (1 : ℝ) := by
    ext j
    change (a x).ofLp j =
      (∑ i : Fin 3, schwartzCoordinate a i x •
        EuclideanSpace.single i (1 : ℝ)).ofLp j
    fin_cases j <;> rw [Fin.sum_univ_three] <;>
      simp [schwartzCoordinate_apply]
  calc
    schwartzDirectionalVectorField a b x
        = ∑ i : Fin 3,
            schwartzCoordinate a i x •
              (∂_{EuclideanSpace.single i (1 : ℝ)} b) x := by
          simp [schwartzDirectionalVectorField,
            SchwartzMap.pairing_apply_apply]
    _ = ∑ i : Fin 3,
            schwartzCoordinate a i x •
              fderiv ℝ (b : NSSpace → NSSpace) x
                (EuclideanSpace.single i (1 : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    _ = fderiv ℝ (b : NSSpace → NSSpace) x
          (∑ i : Fin 3, schwartzCoordinate a i x •
            EuclideanSpace.single i (1 : ℝ)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [ContinuousLinearMap.map_smul]
    _ = fderiv ℝ (b : NSSpace → NSSpace) x (a x) := by
          rw [← hVec]

/-- A Schwartz velocity and vorticity slice represent the concrete vorticity
transport term pointwise. -/
theorem vorticityTransportTerm_eq_schwartzDirectionalVectorField
    (u : NSVelocityField) (t : NSTime)
    (v ω : 𝓢(NSSpace, NSSpace))
    (hu : ∀ x, u t x = v x)
    (hω : ∀ x, spatialVorticity u t x = ω x)
    (x : NSSpace) :
    vorticityTransportTerm u t x = schwartzDirectionalVectorField v ω x := by
  have hωfun : (fun y : NSSpace => spatialVorticity u t y) =
      (ω : NSSpace → NSSpace) :=
    funext hω
  unfold vorticityTransportTerm spatialFDeriv
  rw [hωfun, hu x]
  exact (schwartzDirectionalVectorField_apply v ω x).symm

/-- A Schwartz velocity and vorticity slice represent the concrete vorticity
stretching term pointwise. -/
theorem vorticityStretchingTerm_eq_schwartzDirectionalVectorField
    (u : NSVelocityField) (t : NSTime)
    (v ω : 𝓢(NSSpace, NSSpace))
    (hu : ∀ x, u t x = v x)
    (hω : ∀ x, spatialVorticity u t x = ω x)
    (x : NSSpace) :
    vorticityStretchingTerm u t x = schwartzDirectionalVectorField ω v x := by
  have hufun : (fun y : NSSpace => u t y) = (v : NSSpace → NSSpace) :=
    funext hu
  unfold vorticityStretchingTerm spatialFDeriv
  rw [hufun, hω x]
  exact (schwartzDirectionalVectorField_apply ω v x).symm

/-- A Schwartz vorticity slice represents the concrete vorticity diffusion
term pointwise. -/
theorem vorticityDiffusionTerm_eq_laplacian_schwartz
    (u : NSVelocityField) (t : NSTime)
    (ω : 𝓢(NSSpace, NSSpace))
    (hω : ∀ x, spatialVorticity u t x = ω x)
    (x : NSSpace) :
    vorticityDiffusionTerm u t x = Δ ω x := by
  have hωfun : (fun y : NSSpace => spatialVorticity u t y) =
      (ω : NSSpace → NSSpace) :=
    funext hω
  unfold vorticityDiffusionTerm spatialLaplacian
  rw [hωfun]
  exact (SchwartzMap.laplacian_apply ω x).symm

/-- A Schwartz vorticity slice has integrable vorticity-enstrophy density. -/
theorem integrable_vorticityEnstrophyDensity_of_schwartzVorticitySlice
    (u : NSVelocityField) (t : NSTime) (ω : 𝓢(NSSpace, NSSpace))
    (hω : ∀ x, spatialVorticity u t x = ω x) :
    Integrable (fun x => vorticityEnstrophyDensity u t x) := by
  refine ((SchwartzMap.pairing (innerSL ℝ) ω ω).integrable).congr ?_
  filter_upwards with x
  rw [SchwartzMap.pairing_apply_apply, vorticityEnstrophyDensity, hω x]
  change ⟪ω x, ω x⟫ = ‖ω x‖ ^ (2 : ℕ)
  rw [real_inner_self_eq_norm_sq]

/-- Schwartz velocity and vorticity slices make the three raw paired
vorticity-balance integrands integrable. -/
theorem vorticityRawBalanceIntegralComponentsIntegrableAt_of_schwartzVelocitySlice_schwartzVorticitySlice
    (u : NSVelocityField) (t : NSTime)
    (v ω : 𝓢(NSSpace, NSSpace))
    (hu : ∀ x, u t x = v x)
    (hω : ∀ x, spatialVorticity u t x = ω x) :
    vorticityRawBalanceIntegralComponentsIntegrableAt u t := by
  refine ⟨?_, ?_, ?_⟩
  · refine ((SchwartzMap.pairing (innerSL ℝ) ω
        (schwartzDirectionalVectorField v ω)).integrable).congr ?_
    filter_upwards with x
    rw [SchwartzMap.pairing_apply_apply, hω x,
      vorticityTransportTerm_eq_schwartzDirectionalVectorField
        u t v ω hu hω x]
    rfl
  · refine ((SchwartzMap.pairing (innerSL ℝ) ω (Δ ω)).integrable).congr ?_
    filter_upwards with x
    rw [SchwartzMap.pairing_apply_apply, hω x,
      vorticityDiffusionTerm_eq_laplacian_schwartz u t ω hω x]
    rfl
  · refine ((SchwartzMap.pairing (innerSL ℝ) ω
        (schwartzDirectionalVectorField ω v)).integrable).congr ?_
    filter_upwards with x
    rw [SchwartzMap.pairing_apply_apply, vorticityStretchingPower, hω x,
      vorticityStretchingTerm_eq_schwartzDirectionalVectorField
        u t v ω hu hω x]
    rfl

/-- Time derivative of a scalar-modulated Schwartz vorticity slice. -/
theorem timeVorticityDerivative_scalar_smul_schwartzVorticitySlice
    (u : NSVelocityField) (a a' : ℝ → ℝ) (f : 𝓢(NSSpace, NSSpace))
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hω : ∀ t x, spatialVorticity u t x = a t • f x) :
    ∀ t x, timeVorticityDerivative u t x = a' t • f x := by
  intro t x
  unfold timeVorticityDerivative
  have hDeriv :
      HasDerivAt (fun s : NSTime => spatialVorticity u s x)
        (a' t • f x) t := by
    have hscalar : HasDerivAt (fun s : NSTime => a s • f x)
        (a' t • f x) t := by
      exact (ha t).smul_const (f x)
    convert hscalar using 1
    ext s
    rw [hω s x]
  rw [hDeriv.hasFDerivAt.fderiv]
  simp

/-- Vorticity enstrophy of a scalar-modulated Schwartz vorticity slice. -/
theorem vorticityEnstrophyAt_scalar_smul_schwartzVorticitySlice
    (u : NSVelocityField) (a : ℝ → ℝ) (f : 𝓢(NSSpace, NSSpace))
    (hω : ∀ t x, spatialVorticity u t x = a t • f x) :
    vorticityEnstrophyAt u =
      fun t => (a t) ^ (2 : ℕ) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume := by
  funext t
  rw [vorticityEnstrophyAt]
  have hDensity :
      vorticityEnstrophyDensity u t =
        fun x : NSSpace => (a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ) := by
    funext x
    rw [vorticityEnstrophyDensity, hω t x]
    simp [norm_smul, mul_pow, sq_abs]
  rw [hDensity]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    integral_const_mul ((a t) ^ (2 : ℕ))
      (fun x : NSSpace => ‖f x‖ ^ (2 : ℕ))

/-- Time-pairing integral of a scalar-modulated Schwartz vorticity slice. -/
theorem vorticityTimePowerIntegral_scalar_smul_schwartzVorticitySlice
    (u : NSVelocityField) (a a' : ℝ → ℝ) (f : 𝓢(NSSpace, NSSpace))
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hω : ∀ t x, spatialVorticity u t x = a t • f x) :
    ∀ t,
      vorticityTimePowerIntegral u t =
        (a t * a' t) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume := by
  intro t
  have hPair :
      (fun x : NSSpace =>
        ⟪spatialVorticity u t x, timeVorticityDerivative u t x⟫) =
        fun x : NSSpace => (a t * a' t) * ‖f x‖ ^ (2 : ℕ) := by
    funext x
    rw [hω t x,
      timeVorticityDerivative_scalar_smul_schwartzVorticitySlice
        u a a' f ha hω t x]
    simp [real_inner_smul_left, real_inner_smul_right, mul_assoc,
      mul_left_comm]
  rw [vorticityTimePowerIntegral, hPair]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    integral_const_mul (a t * a' t)
      (fun x : NSSpace => ‖f x‖ ^ (2 : ℕ))

/-- For scalar-modulated Schwartz vorticity slices, the time-pairing integral
is the derivative of the normalized vorticity enstrophy. -/
theorem vorticityEnstrophyTimePairingDerivativeAt_of_scalar_smul_schwartzVorticitySlice
    (u : NSVelocityField) (a a' : ℝ → ℝ) (f : 𝓢(NSSpace, NSSpace))
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hω : ∀ t x, spatialVorticity u t x = a t • f x) :
    ∀ t, vorticityEnstrophyTimePairingDerivativeAt u t := by
  intro t
  let E : ℝ := ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume
  have hEnergy :
      normalizedVorticityEnstrophyAt u =
        fun s => ((1 / 2 : ℝ) * E) * (a s) ^ (2 : ℕ) := by
    funext s
    rw [normalizedVorticityEnstrophyAt,
      vorticityEnstrophyAt_scalar_smul_schwartzVorticitySlice u a f hω]
    simp [E]
    ring
  have hPair :
      vorticityTimePowerIntegral u t = (a t * a' t) * E := by
    simpa [E] using
      vorticityTimePowerIntegral_scalar_smul_schwartzVorticitySlice
        u a a' f ha hω t
  unfold vorticityEnstrophyTimePairingDerivativeAt
  rw [hEnergy, hPair]
  have hPow :
      HasDerivAt (fun s : ℝ => (a s) ^ (2 : ℕ)) (2 * a t * a' t) t := by
    change HasDerivAt (a ^ (2 : ℕ)) (2 * a t * a' t) t
    simpa [pow_one, mul_assoc, mul_left_comm, mul_comm] using (ha t).pow 2
  have hDeriv :
      HasDerivAt
        (fun s : ℝ => ((1 / 2 : ℝ) * E) * (a s) ^ (2 : ℕ))
        (((1 / 2 : ℝ) * E) * (2 * a t * a' t)) t := by
    exact hPow.const_mul (((1 / 2 : ℝ) * E))
  convert hDeriv using 1
  ring

/-- Time derivative of a two-profile scalar Schwartz vorticity superposition. -/
theorem timeVorticityDerivative_add_scalar_smul_schwartzVorticitySlice
    (u : NSVelocityField) (a a' b b' : ℝ → ℝ)
    (f g : 𝓢(NSSpace, NSSpace))
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (hω : ∀ t x, spatialVorticity u t x = a t • f x + b t • g x) :
    ∀ t x, timeVorticityDerivative u t x = a' t • f x + b' t • g x := by
  intro t x
  unfold timeVorticityDerivative
  have hDeriv :
      HasDerivAt (fun s : NSTime => spatialVorticity u s x)
        (a' t • f x + b' t • g x) t := by
    have hscalar :
        HasDerivAt (fun s : NSTime => a s • f x + b s • g x)
          (a' t • f x + b' t • g x) t := by
      exact (ha t).smul_const (f x) |>.add ((hb t).smul_const (g x))
    convert hscalar using 1
    ext s
    rw [hω s x]
  rw [hDeriv.hasFDerivAt.fderiv]
  simp

/-- Vorticity enstrophy of a two-profile scalar Schwartz vorticity
superposition. -/
theorem vorticityEnstrophyAt_add_scalar_smul_schwartzVorticitySlice
    (u : NSVelocityField) (a b : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace))
    (hω : ∀ t x, spatialVorticity u t x = a t • f x + b t • g x) :
    vorticityEnstrophyAt u =
      fun t =>
        (a t) ^ (2 : ℕ) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume +
          (2 * (a t * b t)) * ∫ x, ⟪f x, g x⟫ ∂volume +
            (b t) ^ (2 : ℕ) * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume := by
  funext t
  rw [vorticityEnstrophyAt]
  have hDensity :
      vorticityEnstrophyDensity u t =
        fun x : NSSpace =>
          (a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ) +
            (2 * (a t * b t)) * ⟪f x, g x⟫ +
              (b t) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ) := by
    funext x
    rw [vorticityEnstrophyDensity, hω t x]
    simpa [real_inner_smul_left, real_inner_smul_right, real_inner_comm,
      norm_smul, sq_abs, mul_pow, mul_assoc, mul_left_comm, mul_comm] using
      (norm_add_sq_real (a t • f x) (b t • g x))
  have hIntF :
      Integrable (fun x : NSSpace => (a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ)) := by
    exact (integrable_norm_sq_of_schwartz f).const_mul ((a t) ^ (2 : ℕ))
  have hIntFG :
      Integrable (fun x : NSSpace => (2 * (a t * b t)) * ⟪f x, g x⟫) := by
    exact (integrable_inner_schwartz f g).const_mul (2 * (a t * b t))
  have hIntG :
      Integrable (fun x : NSSpace => (b t) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ)) := by
    exact (integrable_norm_sq_of_schwartz g).const_mul ((b t) ^ (2 : ℕ))
  rw [hDensity]
  calc
    ∫ x,
        ((a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ) +
          (2 * (a t * b t)) * ⟪f x, g x⟫ +
            (b t) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ)) ∂volume
      = ∫ x,
          ((a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ) +
            (2 * (a t * b t)) * ⟪f x, g x⟫) ∂volume
            + ∫ x, (b t) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ) ∂volume := by
          simpa [add_assoc] using integral_add (hIntF.add hIntFG) hIntG
    _ = (∫ x, (a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ) ∂volume
          + ∫ x, (2 * (a t * b t)) * ⟪f x, g x⟫ ∂volume)
          + ∫ x, (b t) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ) ∂volume := by
          rw [integral_add hIntF hIntFG]
    _ = (a t) ^ (2 : ℕ) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume +
          (2 * (a t * b t)) * ∫ x, ⟪f x, g x⟫ ∂volume +
            (b t) ^ (2 : ℕ) * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul]

/-- Time-pairing integral of a two-profile scalar Schwartz vorticity
superposition. -/
theorem vorticityTimePowerIntegral_add_scalar_smul_schwartzVorticitySlice
    (u : NSVelocityField) (a a' b b' : ℝ → ℝ)
    (f g : 𝓢(NSSpace, NSSpace))
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (hω : ∀ t x, spatialVorticity u t x = a t • f x + b t • g x) :
    ∀ t,
      vorticityTimePowerIntegral u t =
        (a t * a' t) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume +
          (a t * b' t + b t * a' t) * ∫ x, ⟪f x, g x⟫ ∂volume +
            (b t * b' t) * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume := by
  intro t
  have hPair :
      (fun x : NSSpace =>
        ⟪spatialVorticity u t x, timeVorticityDerivative u t x⟫) =
        fun x : NSSpace =>
          (a t * a' t) * ‖f x‖ ^ (2 : ℕ) +
            (a t * b' t + b t * a' t) * ⟪f x, g x⟫ +
              (b t * b' t) * ‖g x‖ ^ (2 : ℕ) := by
    funext x
    rw [hω t x,
      timeVorticityDerivative_add_scalar_smul_schwartzVorticitySlice
        u a a' b b' f g ha hb hω t x]
    simp [inner_add_left, inner_add_right, real_inner_smul_right,
      real_inner_comm, add_mul, mul_assoc, mul_left_comm, mul_comm]
    ring
  have hIntF :
      Integrable (fun x : NSSpace => (a t * a' t) * ‖f x‖ ^ (2 : ℕ)) := by
    exact (integrable_norm_sq_of_schwartz f).const_mul (a t * a' t)
  have hIntFG :
      Integrable (fun x : NSSpace => (a t * b' t + b t * a' t) * ⟪f x, g x⟫) := by
    exact (integrable_inner_schwartz f g).const_mul (a t * b' t + b t * a' t)
  have hIntG :
      Integrable (fun x : NSSpace => (b t * b' t) * ‖g x‖ ^ (2 : ℕ)) := by
    exact (integrable_norm_sq_of_schwartz g).const_mul (b t * b' t)
  rw [vorticityTimePowerIntegral, hPair]
  calc
    ∫ x,
        ((a t * a' t) * ‖f x‖ ^ (2 : ℕ) +
          (a t * b' t + b t * a' t) * ⟪f x, g x⟫ +
            (b t * b' t) * ‖g x‖ ^ (2 : ℕ)) ∂volume
      = ∫ x,
          ((a t * a' t) * ‖f x‖ ^ (2 : ℕ) +
            (a t * b' t + b t * a' t) * ⟪f x, g x⟫) ∂volume
            + ∫ x, (b t * b' t) * ‖g x‖ ^ (2 : ℕ) ∂volume := by
          simpa [add_assoc] using integral_add (hIntF.add hIntFG) hIntG
    _ = (∫ x, (a t * a' t) * ‖f x‖ ^ (2 : ℕ) ∂volume
          + ∫ x, (a t * b' t + b t * a' t) * ⟪f x, g x⟫ ∂volume)
          + ∫ x, (b t * b' t) * ‖g x‖ ^ (2 : ℕ) ∂volume := by
          rw [integral_add hIntF hIntFG]
    _ = (a t * a' t) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume +
          (a t * b' t + b t * a' t) * ∫ x, ⟪f x, g x⟫ ∂volume +
            (b t * b' t) * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul]

/-- For two-profile scalar Schwartz vorticity superpositions, the time-pairing
integral is the derivative of the normalized vorticity enstrophy. -/
theorem vorticityEnstrophyTimePairingDerivativeAt_of_add_scalar_smul_schwartzVorticitySlice
    (u : NSVelocityField) (a a' b b' : ℝ → ℝ)
    (f g : 𝓢(NSSpace, NSSpace))
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (hω : ∀ t x, spatialVorticity u t x = a t • f x + b t • g x) :
    ∀ t, vorticityEnstrophyTimePairingDerivativeAt u t := by
  intro t
  let F : ℝ := ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume
  let FG : ℝ := ∫ x, ⟪f x, g x⟫ ∂volume
  let G : ℝ := ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume
  have hEnergy :
      normalizedVorticityEnstrophyAt u =
        fun s =>
          ((1 / 2 : ℝ) * F) * (a s) ^ (2 : ℕ) +
            FG * (a s * b s) +
              ((1 / 2 : ℝ) * G) * (b s) ^ (2 : ℕ) := by
    funext s
    rw [normalizedVorticityEnstrophyAt,
      vorticityEnstrophyAt_add_scalar_smul_schwartzVorticitySlice u a b f g hω]
    simp [F, FG, G]
    ring
  have hPair :
      vorticityTimePowerIntegral u t =
        F * (a t * a' t) + FG * (a t * b' t + b t * a' t) + G * (b t * b' t) := by
    simpa [F, FG, G, mul_comm, mul_left_comm, mul_assoc] using
      vorticityTimePowerIntegral_add_scalar_smul_schwartzVorticitySlice
        u a a' b b' f g ha hb hω t
  unfold vorticityEnstrophyTimePairingDerivativeAt
  rw [hEnergy, hPair]
  have hA2 :
      HasDerivAt (fun s : ℝ => (a s) ^ (2 : ℕ)) (2 * a t * a' t) t := by
    change HasDerivAt (a ^ (2 : ℕ)) (2 * a t * a' t) t
    simpa [pow_one, mul_assoc, mul_left_comm, mul_comm] using (ha t).pow 2
  have hAB :
      HasDerivAt (fun s : ℝ => a s * b s) (a' t * b t + a t * b' t) t := by
    change HasDerivAt (a * b) (a' t * b t + a t * b' t) t
    exact (ha t).mul (hb t)
  have hB2 :
      HasDerivAt (fun s : ℝ => (b s) ^ (2 : ℕ)) (2 * b t * b' t) t := by
    change HasDerivAt (b ^ (2 : ℕ)) (2 * b t * b' t) t
    simpa [pow_one, mul_assoc, mul_left_comm, mul_comm] using (hb t).pow 2
  have hDeriv :
      HasDerivAt
        (fun s : ℝ =>
          ((1 / 2 : ℝ) * F) * (a s) ^ (2 : ℕ) +
            FG * (a s * b s) +
              ((1 / 2 : ℝ) * G) * (b s) ^ (2 : ℕ))
        ((((1 / 2 : ℝ) * F) * (2 * a t * a' t)) +
          (FG * (a' t * b t + a t * b' t)) +
            (((1 / 2 : ℝ) * G) * (2 * b t * b' t))) t := by
    have hraw :=
      (hA2.const_mul (((1 / 2 : ℝ) * F))).add
        ((hAB.const_mul FG).add (hB2.const_mul (((1 / 2 : ℝ) * G))))
    have hfun :
        (fun s : ℝ =>
          ((1 / 2 : ℝ) * F) * (a s) ^ (2 : ℕ) +
            FG * (a s * b s) +
              ((1 / 2 : ℝ) * G) * (b s) ^ (2 : ℕ)) =ᶠ[nhds t]
        ((fun y => ((1 / 2 : ℝ) * F) * a y ^ (2 : ℕ)) +
          ((fun y => FG * (a y * b y)) +
            fun y => ((1 / 2 : ℝ) * G) * b y ^ (2 : ℕ))) := by
      exact Filter.Eventually.of_forall (by
        intro s
        change ((1 / 2 : ℝ) * F) * a s ^ (2 : ℕ) + FG * (a s * b s) +
            ((1 / 2 : ℝ) * G) * b s ^ (2 : ℕ) =
          ((1 / 2 : ℝ) * F) * a s ^ (2 : ℕ) +
            (FG * (a s * b s) + ((1 / 2 : ℝ) * G) * b s ^ (2 : ℕ))
        ring)
    exact (hraw.congr_of_eventuallyEq hfun).congr_deriv (by ring)
  convert hDeriv using 1
  ring

/-- Inner product of two finite scalar Schwartz-vorticity superpositions. -/
theorem inner_fintype_sum_scalar_smul_schwartzVorticitySlice
    {ι : Type} [Fintype ι]
    (a b : ι → ℝ) (f g : ι → 𝓢(NSSpace, NSSpace)) (x : NSSpace) :
    ⟪(∑ i, a i • f i x), (∑ j, b j • g j x)⟫ =
      ∑ j, ∑ i, (a i * b j) * ⟪f i x, g j x⟫ := by
  simp [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    mul_assoc, mul_left_comm]

/-- Time derivative of a finite scalar Schwartz vorticity superposition. -/
theorem timeVorticityDerivative_fintype_sum_scalar_smul_schwartzVorticitySlice
    {ι : Type} [Fintype ι]
    (u : NSVelocityField) (a a' : ι → ℝ → ℝ)
    (f : ι → 𝓢(NSSpace, NSSpace))
    (ha : ∀ i t, HasDerivAt (a i) (a' i t) t)
    (hω : ∀ t x, spatialVorticity u t x = ∑ i, a i t • f i x) :
    ∀ t x, timeVorticityDerivative u t x = ∑ i, a' i t • f i x := by
  intro t x
  unfold timeVorticityDerivative
  have hDeriv :
      HasDerivAt (fun s : NSTime => spatialVorticity u s x)
        (∑ i, a' i t • f i x) t := by
    have hscalar :
        HasDerivAt (fun s : NSTime => ∑ i, a i s • f i x)
          (∑ i, a' i t • f i x) t := by
      exact HasDerivAt.fun_sum (fun i _ => (ha i t).smul_const (f i x))
    convert hscalar using 1
    ext s
    rw [hω s x]
  rw [hDeriv.hasFDerivAt.fderiv]
  simp

/-- Vorticity enstrophy of a finite scalar Schwartz vorticity superposition,
written as its finite Gram matrix quadratic form. -/
theorem vorticityEnstrophyAt_fintype_sum_scalar_smul_schwartzVorticitySlice
    {ι : Type} [Fintype ι]
    (u : NSVelocityField) (a : ι → ℝ → ℝ)
    (f : ι → 𝓢(NSSpace, NSSpace))
    (hω : ∀ t x, spatialVorticity u t x = ∑ i, a i t • f i x) :
    vorticityEnstrophyAt u =
      fun t => ∑ j, ∑ i, (a i t * a j t) *
        ∫ x, ⟪f i x, f j x⟫ ∂volume := by
  funext t
  rw [vorticityEnstrophyAt]
  have hDensity :
      vorticityEnstrophyDensity u t =
        fun x : NSSpace =>
          ∑ j, ∑ i, (a i t * a j t) * ⟪f i x, f j x⟫ := by
    funext x
    rw [vorticityEnstrophyDensity, hω t x, ← real_inner_self_eq_norm_sq]
    exact inner_fintype_sum_scalar_smul_schwartzVorticitySlice
      (fun i => a i t) (fun i => a i t) f f x
  have hInt :
      ∀ j ∈ (Finset.univ : Finset ι), Integrable
        (fun x : NSSpace => ∑ i, (a i t * a j t) * ⟪f i x, f j x⟫) := by
    intro j _hj
    exact MeasureTheory.integrable_finsetSum Finset.univ (fun i _hi =>
      (integrable_inner_schwartz (f i) (f j)).const_mul (a i t * a j t))
  rw [hDensity]
  calc
    ∫ x,
        (∑ j, ∑ i, (a i t * a j t) * ⟪f i x, f j x⟫) ∂volume
      = ∑ j, ∫ x,
          (∑ i, (a i t * a j t) * ⟪f i x, f j x⟫) ∂volume := by
        rw [integral_finsetSum Finset.univ hInt]
    _ = ∑ j, ∑ i, (a i t * a j t) *
          ∫ x, ⟪f i x, f j x⟫ ∂volume := by
      apply Finset.sum_congr rfl
      intro j _hj
      have hIntInner :
          ∀ i ∈ (Finset.univ : Finset ι), Integrable
            (fun x : NSSpace => (a i t * a j t) * ⟪f i x, f j x⟫) := by
        intro i _hi
        exact (integrable_inner_schwartz (f i) (f j)).const_mul (a i t * a j t)
      rw [integral_finsetSum Finset.univ hIntInner]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [integral_const_mul]

/-- Time-pairing integral of a finite scalar Schwartz vorticity superposition,
written as the corresponding finite Gram matrix pairing. -/
theorem vorticityTimePowerIntegral_fintype_sum_scalar_smul_schwartzVorticitySlice
    {ι : Type} [Fintype ι]
    (u : NSVelocityField) (a a' : ι → ℝ → ℝ)
    (f : ι → 𝓢(NSSpace, NSSpace))
    (ha : ∀ i t, HasDerivAt (a i) (a' i t) t)
    (hω : ∀ t x, spatialVorticity u t x = ∑ i, a i t • f i x) :
    ∀ t,
      vorticityTimePowerIntegral u t =
        ∑ j, ∑ i, (a i t * a' j t) *
          ∫ x, ⟪f i x, f j x⟫ ∂volume := by
  intro t
  have hPair :
      (fun x : NSSpace =>
        ⟪spatialVorticity u t x, timeVorticityDerivative u t x⟫) =
        fun x : NSSpace =>
          ∑ j, ∑ i, (a i t * a' j t) * ⟪f i x, f j x⟫ := by
    funext x
    rw [hω t x,
      timeVorticityDerivative_fintype_sum_scalar_smul_schwartzVorticitySlice
        u a a' f ha hω t x]
    exact inner_fintype_sum_scalar_smul_schwartzVorticitySlice
      (fun i => a i t) (fun i => a' i t) f f x
  have hInt :
      ∀ j ∈ (Finset.univ : Finset ι), Integrable
        (fun x : NSSpace => ∑ i, (a i t * a' j t) * ⟪f i x, f j x⟫) := by
    intro j _hj
    exact MeasureTheory.integrable_finsetSum Finset.univ (fun i _hi =>
      (integrable_inner_schwartz (f i) (f j)).const_mul (a i t * a' j t))
  rw [vorticityTimePowerIntegral, hPair]
  calc
    ∫ x,
        (∑ j, ∑ i, (a i t * a' j t) * ⟪f i x, f j x⟫) ∂volume
      = ∑ j, ∫ x,
          (∑ i, (a i t * a' j t) * ⟪f i x, f j x⟫) ∂volume := by
        rw [integral_finsetSum Finset.univ hInt]
    _ = ∑ j, ∑ i, (a i t * a' j t) *
          ∫ x, ⟪f i x, f j x⟫ ∂volume := by
      apply Finset.sum_congr rfl
      intro j _hj
      have hIntInner :
          ∀ i ∈ (Finset.univ : Finset ι), Integrable
            (fun x : NSSpace => (a i t * a' j t) * ⟪f i x, f j x⟫) := by
        intro i _hi
        exact (integrable_inner_schwartz (f i) (f j)).const_mul (a i t * a' j t)
      rw [integral_finsetSum Finset.univ hIntInner]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [integral_const_mul]

/-- Symmetric finite-Gram algebra identifying the half-derivative of a
quadratic form with the time-pairing form. -/
theorem half_fintype_gram_derivative_sum_eq_pairing_sum
    {ι : Type} [Fintype ι]
    (A Ap : ι → ℝ) (G : ι → ι → ℝ)
    (hG : ∀ i j, G i j = G j i) :
    (1 / 2 : ℝ) *
        (∑ j, ∑ i, ((Ap i * A j + A i * Ap j) * G i j)) =
      ∑ j, ∑ i, (A i * Ap j) * G i j := by
  let S1 : ℝ := ∑ j, ∑ i, (Ap i * A j) * G i j
  let S2 : ℝ := ∑ j, ∑ i, (A i * Ap j) * G i j
  have hS1S2 : S1 = S2 := by
    have hSym :
        (∑ j, ∑ i, (Ap i * A j) * G i j) =
          ∑ j, ∑ i, (A i * Ap j) * G i j := by
      calc
        (∑ j, ∑ i, (Ap i * A j) * G i j)
            = ∑ i, ∑ j, (Ap i * A j) * G i j := by
              rw [Finset.sum_comm]
        _ = ∑ i, ∑ j, (A j * Ap i) * G j i := by
              apply Finset.sum_congr rfl
              intro i _hi
              apply Finset.sum_congr rfl
              intro j _hj
              rw [hG i j]
              ring
        _ = ∑ j, ∑ i, (A i * Ap j) * G i j := by
              rw [Finset.sum_comm]
    simpa [S1, S2] using hSym
  have hsplit :
      (∑ j, ∑ i, ((Ap i * A j + A i * Ap j) * G i j)) =
        S1 + S2 := by
    simp [S1, S2, add_mul, Finset.sum_add_distrib]
  rw [hsplit, hS1S2]
  ring

/-- For finite scalar Schwartz vorticity superpositions, the time-pairing
integral is the derivative of the normalized vorticity enstrophy. -/
theorem vorticityEnstrophyTimePairingDerivativeAt_of_fintype_sum_scalar_smul_schwartzVorticitySlice
    {ι : Type} [Fintype ι]
    (u : NSVelocityField) (a a' : ι → ℝ → ℝ)
    (f : ι → 𝓢(NSSpace, NSSpace))
    (ha : ∀ i t, HasDerivAt (a i) (a' i t) t)
    (hω : ∀ t x, spatialVorticity u t x = ∑ i, a i t • f i x) :
    ∀ t, vorticityEnstrophyTimePairingDerivativeAt u t := by
  intro t
  let G : ι → ι → ℝ := fun i j => ∫ x, ⟪f i x, f j x⟫ ∂volume
  have hGramSym : ∀ i j, G i j = G j i := by
    intro i j
    unfold G
    have hPoint :
        (fun x : NSSpace => ⟪f i x, f j x⟫) =
          fun x : NSSpace => ⟪f j x, f i x⟫ := by
      funext x
      exact (real_inner_comm (f i x) (f j x)).symm
    rw [hPoint]
  have hEnergy :
      normalizedVorticityEnstrophyAt u =
        fun s => (1 / 2 : ℝ) * ∑ j, ∑ i, (a i s * a j s) * G i j := by
    funext s
    rw [normalizedVorticityEnstrophyAt,
      vorticityEnstrophyAt_fintype_sum_scalar_smul_schwartzVorticitySlice
        u a f hω]
  have hPair :
      vorticityTimePowerIntegral u t =
        ∑ j, ∑ i, (a i t * a' j t) * G i j := by
    simpa [G] using
      vorticityTimePowerIntegral_fintype_sum_scalar_smul_schwartzVorticitySlice
        u a a' f ha hω t
  unfold vorticityEnstrophyTimePairingDerivativeAt
  rw [hEnergy, hPair]
  have hProdDeriv :
      ∀ i j,
        HasDerivAt (fun s : ℝ => a i s * a j s)
          (a' i t * a j t + a i t * a' j t) t := by
    intro i j
    exact (ha i t).mul (ha j t)
  have hTermDeriv :
      ∀ j (_hj : j ∈ (Finset.univ : Finset ι)) i
          (_hi : i ∈ (Finset.univ : Finset ι)),
        HasDerivAt (fun s : ℝ => (a i s * a j s) * G i j)
          ((a' i t * a j t + a i t * a' j t) * G i j) t := by
    intro j _hj i _hi
    exact (hProdDeriv i j).mul_const (G i j)
  have hInnerDeriv :
      ∀ j (_hj : j ∈ (Finset.univ : Finset ι)),
        HasDerivAt (fun s : ℝ => ∑ i, (a i s * a j s) * G i j)
          (∑ i, (a' i t * a j t + a i t * a' j t) * G i j) t := by
    intro j hj
    exact HasDerivAt.fun_sum (hTermDeriv j hj)
  have hSumDeriv :
      HasDerivAt (fun s : ℝ => ∑ j, ∑ i, (a i s * a j s) * G i j)
        (∑ j, ∑ i, (a' i t * a j t + a i t * a' j t) * G i j) t := by
    exact HasDerivAt.fun_sum hInnerDeriv
  have hDeriv :
      HasDerivAt
        (fun s : ℝ => (1 / 2 : ℝ) * ∑ j, ∑ i, (a i s * a j s) * G i j)
        ((1 / 2 : ℝ) *
          (∑ j, ∑ i, (a' i t * a j t + a i t * a' j t) * G i j)) t := by
    exact HasDerivAt.const_mul (1 / 2 : ℝ) hSumDeriv
  convert hDeriv using 1
  exact (half_fintype_gram_derivative_sum_eq_pairing_sum
    (fun i => a i t) (fun i => a' i t) G hGramSym).symm

/-- Witness-level hypothesis that every certified vorticity slice has a
Schwartz representative.  This is the exact decay/regularity input needed to
instantiate the checked vorticity diffusion integration-by-parts theorem on a
finite-time witness. -/
def finiteTimeWitnessVorticitySchwartzSlices
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) : Prop :=
  ∀ t, 0 ≤ t → t ≤ T →
    ∃ ω : 𝓢(NSSpace, NSSpace), ∀ x, spatialVorticity W.velocity t x = ω x

/-- Witness-level hypothesis that every certified velocity slice has a
Schwartz representative.  Together with the vorticity-slice hypothesis, this
instantiates the checked BKM transport cancellation theorem. -/
def finiteTimeWitnessVelocitySchwartzSlices
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) : Prop :=
  ∀ t, 0 ≤ t → t ≤ T →
    ∃ v : 𝓢(NSSpace, NSSpace), ∀ x, W.velocity t x = v x

/-- A Schwartz velocity slice supplies a Schwartz vorticity slice by taking
the checked Schwartz curl of the frozen velocity representative. -/
theorem finiteTimeWitnessVorticitySchwartzSlices_of_velocitySchwartzSlices
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W) :
    finiteTimeWitnessVorticitySchwartzSlices W := by
  intro t ht0 htT
  rcases hVelocitySlices t ht0 htT with ⟨v, hv⟩
  refine ⟨schwartzSpatialVorticitySlice v, ?_⟩
  intro x
  calc
    spatialVorticity W.velocity t x = spatialVorticity (fun _ y => v y) 0 x := by
      exact spatialVorticity_congr_at (u := W.velocity) (v := fun _ y => v y)
        (t := t) (x := x) hv
    _ = schwartzSpatialVorticitySlice v x := by
      rw [schwartzSpatialVorticitySlice_apply]

/-- A finite-time witness with Schwartz vorticity slices has integrable
vorticity enstrophy density on every certified time slice. -/
theorem integrable_vorticityEnstrophyDensity_of_finiteTimeWitnessVorticitySchwartzSlices
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hSlices : finiteTimeWitnessVorticitySchwartzSlices W)
    {t : NSTime} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    Integrable (fun x => vorticityEnstrophyDensity W.velocity t x) := by
  rcases hSlices t ht0 htT with ⟨ω, hω⟩
  exact integrable_vorticityEnstrophyDensity_of_schwartzVorticitySlice
    W.velocity t ω hω

/-- A finite-time witness with Schwartz velocity slices has integrable
vorticity enstrophy density on every certified time slice. -/
theorem integrable_vorticityEnstrophyDensity_of_finiteTimeWitnessVelocitySchwartzSlices
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    {t : NSTime} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    Integrable (fun x => vorticityEnstrophyDensity W.velocity t x) := by
  exact
    integrable_vorticityEnstrophyDensity_of_finiteTimeWitnessVorticitySchwartzSlices
      W
      (finiteTimeWitnessVorticitySchwartzSlices_of_velocitySchwartzSlices
        W hVelocitySlices)
      ht0 htT

/-- A finite-time witness with Schwartz velocity and vorticity slices has the
raw paired vorticity-balance integrability needed to assemble the raw balance. -/
theorem vorticityRawBalanceIntegralComponentsIntegrableAt_of_finiteTimeWitnessVelocityVorticitySchwartzSlices
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    (hVorticitySlices : finiteTimeWitnessVorticitySchwartzSlices W)
    {t : NSTime} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityRawBalanceIntegralComponentsIntegrableAt W.velocity t := by
  rcases hVelocitySlices t ht0 htT with ⟨v, hv⟩
  rcases hVorticitySlices t ht0 htT with ⟨ω, hω⟩
  exact
    vorticityRawBalanceIntegralComponentsIntegrableAt_of_schwartzVelocitySlice_schwartzVorticitySlice
      W.velocity t v ω hv hω

/-- A finite-time witness with Schwartz velocity slices has the raw paired
vorticity-balance integrability needed to assemble the raw balance. -/
theorem vorticityRawBalanceIntegralComponentsIntegrableAt_of_finiteTimeWitnessVelocitySchwartzSlices
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    {t : NSTime} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityRawBalanceIntegralComponentsIntegrableAt W.velocity t := by
  exact
    vorticityRawBalanceIntegralComponentsIntegrableAt_of_finiteTimeWitnessVelocityVorticitySchwartzSlices
      W hVelocitySlices
      (finiteTimeWitnessVorticitySchwartzSlices_of_velocitySchwartzSlices
        W hVelocitySlices)
      ht0 htT

/-- If a finite-time witness has Schwartz vorticity slices, the checked
vorticity diffusion integration-by-parts identity applies on every certified
time slice. -/
theorem vorticityDiffusionIntegrationByPartsAt_of_finiteTimeWitnessVorticitySchwartzSlices
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hSlices : finiteTimeWitnessVorticitySchwartzSlices W)
    {t : NSTime} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityDiffusionIntegrationByPartsAt W.velocity t := by
  rcases hSlices t ht0 htT with ⟨ω, hω⟩
  exact vorticityDiffusionIntegrationByPartsAt_of_schwartzVorticitySlice
    W.velocity t ω hω

/-- If a finite-time witness has Schwartz velocity and vorticity slices, then
incompressibility gives BKM vorticity transport cancellation on every certified
time slice. -/
theorem vorticityTransportCancellationAt_of_finiteTimeWitnessVelocityVorticitySchwartzSlices
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    (hVorticitySlices : finiteTimeWitnessVorticitySchwartzSlices W)
    {t : NSTime} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityTransportCancellationAt W.velocity t := by
  rcases hVelocitySlices t ht0 htT with ⟨v, hv⟩
  rcases hVorticitySlices t ht0 htT with ⟨ω, hω⟩
  exact
    vorticityTransportCancellationAt_of_schwartzVelocitySlice_schwartzVorticitySlice_spatialDivergence_zero
      W.velocity t v ω hv hω
      (fun x => W.incompressible_on t x ht0 htT)

/-- If a finite-time witness has Schwartz velocity slices, then the vorticity
Schwartz slice needed for transport cancellation is obtained by taking the
Schwartz curl of the velocity slice. -/
theorem vorticityTransportCancellationAt_of_finiteTimeWitnessVelocitySchwartzSlices
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    {t : NSTime} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityTransportCancellationAt W.velocity t := by
  exact
    vorticityTransportCancellationAt_of_finiteTimeWitnessVelocityVorticitySchwartzSlices
      W hVelocitySlices
      (finiteTimeWitnessVorticitySchwartzSlices_of_velocitySchwartzSlices
        W hVelocitySlices)
      ht0 htT

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

/-- Witness-level enstrophy-balance assembly: raw balance plus transport
cancellation and Schwartz vorticity slices give the standard BKM enstrophy
balance on the certified time slice. -/
theorem vorticityEnstrophyBalanceAt_of_rawBalance_transportCancellation_finiteTimeWitnessVorticitySchwartzSlices
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hSlices : finiteTimeWitnessVorticitySchwartzSlices W)
    {t : NSTime}
    (hRaw : vorticityEnstrophyRawBalanceAt ν W.velocity t)
    (hTransport : vorticityTransportCancellationAt W.velocity t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityEnstrophyBalanceAt ν W.velocity t := by
  exact
    vorticityEnstrophyBalanceAt_of_rawBalance_transportCancellation_diffusionIBP
      hRaw hTransport
      (vorticityDiffusionIntegrationByPartsAt_of_finiteTimeWitnessVorticitySchwartzSlices
        W hSlices ht0 htT)

/-- Witness-level a-priori enstrophy estimate: after raw balance and transport
cancellation are supplied, Schwartz vorticity slices give diffusion IBP and
hence derivative control by the stretching term. -/
theorem vorticityEnstrophyStretchingControlledAt_of_rawBalance_transportCancellation_finiteTimeWitnessVorticitySchwartzSlices
    {ν : ℝ} (hν : 0 ≤ ν) {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hSlices : finiteTimeWitnessVorticitySchwartzSlices W)
    {t : NSTime}
    (hRaw : vorticityEnstrophyRawBalanceAt ν W.velocity t)
    (hTransport : vorticityTransportCancellationAt W.velocity t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityEnstrophyStretchingControlledAt ν W.velocity t := by
  exact
    vorticityEnstrophyStretchingControlledAt_of_rawBalance_transportCancellation_diffusionIBP
      hν hRaw hTransport
      (vorticityDiffusionIntegrationByPartsAt_of_finiteTimeWitnessVorticitySchwartzSlices
        W hSlices ht0 htT)

/-- Witness-level enstrophy-balance assembly with the transport cancellation
proved from Schwartz velocity/vorticity slices and incompressibility. -/
theorem vorticityEnstrophyBalanceAt_of_rawBalance_finiteTimeWitnessVelocityVorticitySchwartzSlices
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    (hVorticitySlices : finiteTimeWitnessVorticitySchwartzSlices W)
    {t : NSTime}
    (hRaw : vorticityEnstrophyRawBalanceAt ν W.velocity t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityEnstrophyBalanceAt ν W.velocity t := by
  exact
    vorticityEnstrophyBalanceAt_of_rawBalance_transportCancellation_diffusionIBP
      hRaw
      (vorticityTransportCancellationAt_of_finiteTimeWitnessVelocityVorticitySchwartzSlices
        W hVelocitySlices hVorticitySlices ht0 htT)
      (vorticityDiffusionIntegrationByPartsAt_of_finiteTimeWitnessVorticitySchwartzSlices
        W hVorticitySlices ht0 htT)

/-- Witness-level a-priori enstrophy estimate with both integral identities
instantiated from Schwartz velocity/vorticity slices. -/
theorem vorticityEnstrophyStretchingControlledAt_of_rawBalance_finiteTimeWitnessVelocityVorticitySchwartzSlices
    {ν : ℝ} (hν : 0 ≤ ν) {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    (hVorticitySlices : finiteTimeWitnessVorticitySchwartzSlices W)
    {t : NSTime}
    (hRaw : vorticityEnstrophyRawBalanceAt ν W.velocity t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityEnstrophyStretchingControlledAt ν W.velocity t := by
  exact
    vorticityEnstrophyStretchingControlledAt_of_rawBalance_transportCancellation_diffusionIBP
      hν hRaw
      (vorticityTransportCancellationAt_of_finiteTimeWitnessVelocityVorticitySchwartzSlices
        W hVelocitySlices hVorticitySlices ht0 htT)
      (vorticityDiffusionIntegrationByPartsAt_of_finiteTimeWitnessVorticitySchwartzSlices
        W hVorticitySlices ht0 htT)

/-- Witness-level enstrophy-balance assembly with transport cancellation and
diffusion integration by parts instantiated from Schwartz velocity slices
alone.  The vorticity Schwartz representative is the Schwartz curl of the
velocity representative. -/
theorem vorticityEnstrophyBalanceAt_of_rawBalance_finiteTimeWitnessVelocitySchwartzSlices
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    {t : NSTime}
    (hRaw : vorticityEnstrophyRawBalanceAt ν W.velocity t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityEnstrophyBalanceAt ν W.velocity t := by
  exact
    vorticityEnstrophyBalanceAt_of_rawBalance_finiteTimeWitnessVelocityVorticitySchwartzSlices
      W hVelocitySlices
      (finiteTimeWitnessVorticitySchwartzSlices_of_velocitySchwartzSlices
        W hVelocitySlices)
      hRaw ht0 htT

/-- Witness-level a-priori enstrophy estimate with both integral identities
instantiated from Schwartz velocity slices alone. -/
theorem vorticityEnstrophyStretchingControlledAt_of_rawBalance_finiteTimeWitnessVelocitySchwartzSlices
    {ν : ℝ} (hν : 0 ≤ ν) {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    {t : NSTime}
    (hRaw : vorticityEnstrophyRawBalanceAt ν W.velocity t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityEnstrophyStretchingControlledAt ν W.velocity t := by
  exact
    vorticityEnstrophyStretchingControlledAt_of_rawBalance_finiteTimeWitnessVelocityVorticitySchwartzSlices
      hν W hVelocitySlices
      (finiteTimeWitnessVorticitySchwartzSlices_of_velocitySchwartzSlices
        W hVelocitySlices)
      hRaw ht0 htT

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

/-- The standard vorticity equation gives the raw BKM enstrophy balance for a
finite-time witness with Schwartz velocity slices, after the time-pairing
derivative has been supplied.  The raw component integrability is derived from
the Schwartz slices. -/
theorem vorticityEnstrophyRawBalanceAt_of_timePairingDerivative_concreteVorticityEquationOn_finiteTimeWitnessVelocitySchwartzSlices
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    {t : NSTime}
    (hEq : concreteVorticityEquationOn ν W.velocity T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    (hTime : vorticityEnstrophyTimePairingDerivativeAt W.velocity t)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    vorticityEnstrophyRawBalanceAt ν W.velocity t := by
  exact
    vorticityEnstrophyRawBalanceAt_of_timePairingDerivative_concreteVorticityEquationOn
      hEq
      (vorticityRawBalanceIntegralComponentsIntegrableAt_of_finiteTimeWitnessVelocitySchwartzSlices
        W hVelocitySlices ht0 htT)
      hTime ht0 htT

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

/-- Checked Schwartz-slice transport cancellation: incompressibility plus
Schwartz velocity and vorticity slices make the vorticity transport integral
vanish. -/
def BKMVorticityTransportCancellationSchwartzClosed : Prop :=
  ∀ (u : NSVelocityField) (t : NSTime)
      (v ω : 𝓢(NSSpace, NSSpace)),
    (∀ x, u t x = v x) →
      (∀ x, spatialVorticity u t x = ω x) →
        (∀ x, spatialDivergence u t x = 0) →
          vorticityTransportCancellationAt u t

/-- Checked proof of the Schwartz-slice transport-cancellation package. -/
theorem BKMVorticityTransportCancellationSchwartzClosed_proved :
    BKMVorticityTransportCancellationSchwartzClosed := by
  intro u t v ω hu hω hdiv
  exact
    vorticityTransportCancellationAt_of_schwartzVelocitySlice_schwartzVorticitySlice_spatialDivergence_zero
      u t v ω hu hω hdiv

/-- Checked viscous vorticity integration-by-parts subcase: if a time slice of
vorticity is represented by a Schwartz function, the BKM diffusion pairing
identity follows from the coordinate Laplacian IBP theorem. -/
def BKMVorticityDiffusionIntegrationByPartsSchwartzClosed : Prop :=
  ∀ (u : NSVelocityField) (t : NSTime) (ω : 𝓢(NSSpace, NSSpace)),
    (∀ x, spatialVorticity u t x = ω x) →
      vorticityDiffusionIntegrationByPartsAt u t

/-- Checked proof of the Schwartz-vorticity-slice viscous IBP package. -/
theorem BKMVorticityDiffusionIntegrationByPartsSchwartzClosed_proved :
    BKMVorticityDiffusionIntegrationByPartsSchwartzClosed := by
  intro u t ω hω
  exact vorticityDiffusionIntegrationByPartsAt_of_schwartzVorticitySlice
    u t ω hω

/-- Checked Schwartz-slice raw-balance integrability package: Schwartz
velocity and vorticity slices make the three raw paired vorticity-equation
integrands integrable. -/
def BKMVorticityRawBalanceIntegrabilitySchwartzClosed : Prop :=
  ∀ (u : NSVelocityField) (t : NSTime)
      (v ω : 𝓢(NSSpace, NSSpace)),
    (∀ x, u t x = v x) →
      (∀ x, spatialVorticity u t x = ω x) →
        vorticityRawBalanceIntegralComponentsIntegrableAt u t

/-- Checked proof of the Schwartz-slice raw-balance integrability package. -/
theorem BKMVorticityRawBalanceIntegrabilitySchwartzClosed_proved :
    BKMVorticityRawBalanceIntegrabilitySchwartzClosed := by
  intro u t v ω hu hω
  exact
    vorticityRawBalanceIntegralComponentsIntegrableAt_of_schwartzVelocitySlice_schwartzVorticitySlice
      u t v ω hu hω

/-- Checked scalar-Schwartz vorticity time-pairing package: for
scalar-modulated Schwartz vorticity slices, the time-pairing integral is the
derivative of the normalized vorticity enstrophy. -/
def BKMVorticityScalarSchwartzTimePairingDerivativeClosed : Prop :=
  ∀ (u : NSVelocityField) (a a' : ℝ → ℝ)
      (f : 𝓢(NSSpace, NSSpace)),
    (∀ t, HasDerivAt a (a' t) t) →
      (∀ t x, spatialVorticity u t x = a t • f x) →
        ∀ t, vorticityEnstrophyTimePairingDerivativeAt u t

/-- Checked proof of the scalar-Schwartz vorticity time-pairing package. -/
theorem BKMVorticityScalarSchwartzTimePairingDerivativeClosed_proved :
    BKMVorticityScalarSchwartzTimePairingDerivativeClosed := by
  intro u a a' f ha hω t
  exact
    vorticityEnstrophyTimePairingDerivativeAt_of_scalar_smul_schwartzVorticitySlice
      u a a' f ha hω t

/-- Checked two-profile Schwartz vorticity time-pairing package: for
two scalar-modulated Schwartz vorticity profiles, the time-pairing integral is
the derivative of the normalized vorticity enstrophy, including cross terms. -/
def BKMVorticityTwoProfileSchwartzTimePairingDerivativeClosed : Prop :=
  ∀ (u : NSVelocityField) (a a' b b' : ℝ → ℝ)
      (f g : 𝓢(NSSpace, NSSpace)),
    (∀ t, HasDerivAt a (a' t) t) →
      (∀ t, HasDerivAt b (b' t) t) →
        (∀ t x, spatialVorticity u t x = a t • f x + b t • g x) →
          ∀ t, vorticityEnstrophyTimePairingDerivativeAt u t

/-- Checked proof of the two-profile Schwartz vorticity time-pairing
package. -/
theorem BKMVorticityTwoProfileSchwartzTimePairingDerivativeClosed_proved :
    BKMVorticityTwoProfileSchwartzTimePairingDerivativeClosed := by
  intro u a a' b b' f g ha hb hω t
  exact
    vorticityEnstrophyTimePairingDerivativeAt_of_add_scalar_smul_schwartzVorticitySlice
      u a a' b b' f g ha hb hω t

/-- Checked finite-family Schwartz vorticity time-pairing package: for a
finite scalar-modulated Schwartz vorticity superposition, the time-pairing
integral is the derivative of the normalized vorticity enstrophy. -/
def BKMVorticityFiniteFamilySchwartzTimePairingDerivativeClosed : Prop :=
  ∀ (ι : Type) [Fintype ι] (u : NSVelocityField)
      (a a' : ι → ℝ → ℝ) (f : ι → 𝓢(NSSpace, NSSpace)),
    (∀ i t, HasDerivAt (a i) (a' i t) t) →
      (∀ t x, spatialVorticity u t x = ∑ i, a i t • f i x) →
        ∀ t, vorticityEnstrophyTimePairingDerivativeAt u t

/-- Checked proof of the finite-family Schwartz vorticity time-pairing
package. -/
theorem BKMVorticityFiniteFamilySchwartzTimePairingDerivativeClosed_proved :
    BKMVorticityFiniteFamilySchwartzTimePairingDerivativeClosed := by
  intro ι _ u a a' f ha hω t
  exact
    vorticityEnstrophyTimePairingDerivativeAt_of_fintype_sum_scalar_smul_schwartzVorticitySlice
      u a a' f ha hω t

/-- Checked finite-time witness package: Schwartz velocity slices make the
vorticity enstrophy density integrable on every certified time slice. -/
def BKMVorticityFiniteTimeWitnessVelocitySchwartzEnstrophyIntegrableClosed : Prop :=
  ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) (t : NSTime),
    finiteTimeWitnessVelocitySchwartzSlices W →
      0 ≤ t →
        t ≤ T →
          Integrable (fun x => vorticityEnstrophyDensity W.velocity t x)

/-- Checked proof of the velocity-Schwartz finite-time witness enstrophy
integrability package. -/
theorem BKMVorticityFiniteTimeWitnessVelocitySchwartzEnstrophyIntegrableClosed_proved :
    BKMVorticityFiniteTimeWitnessVelocitySchwartzEnstrophyIntegrableClosed := by
  intro ν u₀ T W t hVelocitySlices ht0 htT
  exact
    integrable_vorticityEnstrophyDensity_of_finiteTimeWitnessVelocitySchwartzSlices
      W hVelocitySlices ht0 htT

/-- Checked finite-time witness package: Schwartz velocity slices make the raw
paired vorticity-equation integrands integrable on every certified time slice. -/
def BKMVorticityFiniteTimeWitnessVelocitySchwartzRawBalanceIntegrabilityClosed : Prop :=
  ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) (t : NSTime),
    finiteTimeWitnessVelocitySchwartzSlices W →
      0 ≤ t →
        t ≤ T →
          vorticityRawBalanceIntegralComponentsIntegrableAt W.velocity t

/-- Checked proof of the velocity-Schwartz finite-time witness raw-balance
integrability package. -/
theorem BKMVorticityFiniteTimeWitnessVelocitySchwartzRawBalanceIntegrabilityClosed_proved :
    BKMVorticityFiniteTimeWitnessVelocitySchwartzRawBalanceIntegrabilityClosed := by
  intro ν u₀ T W t hVelocitySlices ht0 htT
  exact
    vorticityRawBalanceIntegralComponentsIntegrableAt_of_finiteTimeWitnessVelocitySchwartzSlices
      W hVelocitySlices ht0 htT

/-- Checked witness-level a-priori enstrophy package: if the finite-time
witness supplies Schwartz vorticity slices, then raw balance plus transport
cancellation imply derivative control by the stretching term. -/
def BKMVorticityFiniteTimeWitnessSchwartzSliceAprioriClosed : Prop :=
  ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) (t : NSTime),
    0 ≤ ν →
      finiteTimeWitnessVorticitySchwartzSlices W →
        vorticityEnstrophyRawBalanceAt ν W.velocity t →
          vorticityTransportCancellationAt W.velocity t →
            0 ≤ t →
              t ≤ T →
                vorticityEnstrophyStretchingControlledAt ν W.velocity t

/-- Checked proof of the witness-level Schwartz-slice a-priori package. -/
theorem BKMVorticityFiniteTimeWitnessSchwartzSliceAprioriClosed_proved :
    BKMVorticityFiniteTimeWitnessSchwartzSliceAprioriClosed := by
  intro ν u₀ T W t hν hSlices hRaw hTransport ht0 htT
  exact
    vorticityEnstrophyStretchingControlledAt_of_rawBalance_transportCancellation_finiteTimeWitnessVorticitySchwartzSlices
      hν W hSlices hRaw hTransport ht0 htT

/-- Checked witness-level a-priori enstrophy package with both transport
cancellation and diffusion integration by parts instantiated from Schwartz
velocity/vorticity slices. -/
def BKMVorticityFiniteTimeWitnessVelocityVorticitySchwartzAprioriClosed : Prop :=
  ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) (t : NSTime),
    0 ≤ ν →
      finiteTimeWitnessVelocitySchwartzSlices W →
        finiteTimeWitnessVorticitySchwartzSlices W →
          vorticityEnstrophyRawBalanceAt ν W.velocity t →
            0 ≤ t →
              t ≤ T →
                vorticityEnstrophyStretchingControlledAt ν W.velocity t

/-- Checked proof of the witness-level velocity/vorticity Schwartz-slice
a-priori package. -/
theorem BKMVorticityFiniteTimeWitnessVelocityVorticitySchwartzAprioriClosed_proved :
    BKMVorticityFiniteTimeWitnessVelocityVorticitySchwartzAprioriClosed := by
  intro ν u₀ T W t hν hVelocitySlices hVorticitySlices hRaw ht0 htT
  exact
    vorticityEnstrophyStretchingControlledAt_of_rawBalance_finiteTimeWitnessVelocityVorticitySchwartzSlices
      hν W hVelocitySlices hVorticitySlices hRaw ht0 htT

/-- Checked witness-level a-priori enstrophy package with both transport
cancellation and diffusion integration by parts instantiated from Schwartz
velocity slices alone. -/
def BKMVorticityFiniteTimeWitnessVelocitySchwartzAprioriClosed : Prop :=
  ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) (t : NSTime),
    0 ≤ ν →
      finiteTimeWitnessVelocitySchwartzSlices W →
        vorticityEnstrophyRawBalanceAt ν W.velocity t →
          0 ≤ t →
            t ≤ T →
              vorticityEnstrophyStretchingControlledAt ν W.velocity t

/-- Proof of the velocity-only Schwartz-slice finite-time witness a-priori
package. -/
theorem BKMVorticityFiniteTimeWitnessVelocitySchwartzAprioriClosed_proved :
    BKMVorticityFiniteTimeWitnessVelocitySchwartzAprioriClosed := by
  intro ν u₀ T W t hν hVelocitySlices hRaw ht0 htT
  exact
    vorticityEnstrophyStretchingControlledAt_of_rawBalance_finiteTimeWitnessVelocitySchwartzSlices
      hν W hVelocitySlices hRaw ht0 htT

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
