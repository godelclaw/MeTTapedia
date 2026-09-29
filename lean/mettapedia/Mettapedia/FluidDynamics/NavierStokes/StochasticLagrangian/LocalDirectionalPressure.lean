import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalMaterialStretching
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.AlignedPressureReserve

/-!
# Actual directional strain and the pressure-reserve input

On a material path of the constructed unforced local solution, and away
from vorticity zeros, write `σ = ⟨ω,Sω⟩/|ω|²` and
`p = ⟨ω,(Hess p)ω⟩/|ω|²`. Their actual material evolution gives

`σ' = -σ² - p + |Sω-σω|²/|ω|² + viscousRate`.

The nonalignment square is nonnegative. Its work in the aligned joint
reserve is favorable during compression. The viscous rate retains both
ordinary spatial Laplacians; a material path does not remove them.

The physical choice `h = -p - (9/14)σ² + |ω|²/10` identifies the strain
equation with `AlignedPressureReserve.strainRate`, with an explicitly
constructed nonalignment/viscous defect. This does not prove `h ≥ 0`,
the pressure-history equation, or an integrated defect bound. In
particular this `h` is a physical directional pressure expression; it
agrees with the remote excess in the compact test only initially.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalDirectionalPressure

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakeLocalInfiniteVelocity PancakeLocalSpatialVelocity
open PancakeLocalMaterialTrajectories LocalMaterialVorticity LocalMaterialStretching
open PancakeCurlOutputTail

local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

variable {ν T B : ℝ} {u₀ : FourierVelocity}

def strain (s : LocalInfiniteVelocitySolution ν u₀ T B) (X : ℝ → X3) (t : ℝ) : ℝ :=
  ⟪vorticityAlong s X t, stretchingAlong s X t⟫ / ‖vorticityAlong s X t‖ ^ 2

def pressure (s : LocalInfiniteVelocitySolution ν u₀ T B) (X : ℝ → X3) (t : ℝ) : ℝ :=
  ⟪vorticityAlong s X t, pressureHessianAlong s X t (vorticityAlong s X t)⟫ /
    ‖vorticityAlong s X t‖ ^ 2

def nonalignment (s : LocalInfiniteVelocitySolution ν u₀ T B) (X : ℝ → X3) (t : ℝ) : ℝ :=
  ‖stretchingAlong s X t - strain s X t • vorticityAlong s X t‖ ^ 2 /
    ‖vorticityAlong s X t‖ ^ 2

def viscousRate (s : LocalInfiniteVelocitySolution ν u₀ T B) (X : ℝ → X3) (t : ℝ) : ℝ :=
  (⟪diffusionAlong s X t, stretchingAlong s X t⟫ +
    ⟪vorticityAlong s X t, stretchingDiffusionAlong s X t⟫ -
    2 * strain s X t * ⟪vorticityAlong s X t, diffusionAlong s X t⟫) /
      ‖vorticityAlong s X t‖ ^ 2

def pressureInput (s : LocalInfiniteVelocitySolution ν u₀ T B) (X : ℝ → X3) (t : ℝ) : ℝ :=
  -pressure s X t - (9/14) * strain s X t ^ 2 + ‖vorticityAlong s X t‖ ^ 2 / 10

theorem nonalignment_nonneg (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (X : ℝ → X3) (t : ℝ) : 0 ≤ nonalignment s X t := by
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The normalized inner-product derivative retains the part orthogonal
to vorticity, before any sign or size bound is applied. -/
theorem normalized_rate_identity (v y p d e : R3) (hv : v ≠ 0) :
    ((⟪v, -p + e⟫ + ⟪y + d, y⟫) * ‖v‖ ^ 2 -
        ⟪v, y⟫ * (2 * ⟪v, y + d⟫)) / (‖v‖ ^ 2) ^ 2 =
      -(⟪v, y⟫ / ‖v‖ ^ 2) ^ 2 - ⟪v, p⟫ / ‖v‖ ^ 2 +
        ‖y - (⟪v, y⟫ / ‖v‖ ^ 2) • v‖ ^ 2 / ‖v‖ ^ 2 +
        (⟪d, y⟫ + ⟪v, e⟫ - 2 * (⟪v, y⟫ / ‖v‖ ^ 2) * ⟪v, d⟫) / ‖v‖ ^ 2 := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  simp only [inner_add_left, inner_add_right, inner_neg_right, real_inner_self_eq_norm_sq,
    norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [real_inner_comm y v]
  field_simp
  ring

variable (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (X : ℝ → X3)
  (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)

include hg hSum hu hX

/-- Actual material evolution, derived from the unforced PDE identities.
The nonzero-vorticity condition is local; no eigenvector is chosen. -/
theorem hasDerivAt_strain (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hω : vorticityAlong s X t ≠ 0) :
    HasDerivAt (strain s X)
      (-strain s X t ^ 2 - pressure s X t + nonalignment s X t + viscousRate s X t) t := by
  have hv := hasDerivAt_vorticityAlong s g hg hSum hu X hX t ht
  change HasDerivAt _ (stretchingAlong s X t + diffusionAlong s X t) t at hv
  have hy := hasDerivAt_stretchingAlong s g hg hSum hu X hX t ht
  have hd := (HasDerivAt.inner ℝ hv hy).div hv.norm_sq (pow_ne_zero 2 (norm_ne_zero_iff.mpr hω))
  convert! hd using 1
  exact (normalized_rate_identity (vorticityAlong s X t) (stretchingAlong s X t)
    (pressureHessianAlong s X t (vorticityAlong s X t)) (diffusionAlong s X t)
    (stretchingDiffusionAlong s X t) hω).symm

/-- The strain slot of the proposed reserve has a concrete actual-flow
defect. The remaining pressure and amplitude slots need their own laws. -/
theorem hasDerivAt_strain_as_reserve_rate (t w : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hω : vorticityAlong s X t ≠ 0) (hw : w ^ 14 = ‖vorticityAlong s X t‖ ^ 2) :
    HasDerivAt (strain s X)
      (AlignedPressureReserve.strainRate w (strain s X t) (pressureInput s X t)
        (nonalignment s X t + viscousRate s X t)) t := by
  have hd := hasDerivAt_strain s g hg hSum hu X hX t ht hω
  convert hd using 1
  unfold AlignedPressureReserve.strainRate pressureInput
  rw [hw]
  ring

/-- A retained pressure summary may differ from `pressureInput`. The
difference is then an explicit strain-rate cost. In particular an
initial agreement with a remote pressure excess is not an all-time
identification of the two histories. -/
theorem hasDerivAt_strain_with_summary (t w summary : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hω : vorticityAlong s X t ≠ 0) (hw : w ^ 14 = ‖vorticityAlong s X t‖ ^ 2) :
    HasDerivAt (strain s X)
      (AlignedPressureReserve.strainRate w (strain s X t) summary
        (nonalignment s X t + viscousRate s X t + pressureInput s X t - summary)) t := by
  have hd := hasDerivAt_strain_as_reserve_rate s g hg hSum hu X hX t w ht hω hw
  convert hd using 1
  unfold AlignedPressureReserve.strainRate
  ring

omit hg hSum hu hX in
/-- During actual directional compression, the nonalignment part of the
strain defect does nonpositive work in the joint reserve. -/
theorem compression_nonalignment_work_nonpos (t w : ℝ) (hw : 0 ≤ w)
    (hσ : strain s X t ≤ 0) :
    4180 * w ^ 5 * strain s X t * nonalignment s X t ≤ 0 := by
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) hσ) (nonalignment_nonneg s X t)

end Mettapedia.FluidDynamics.NavierStokes.LocalDirectionalPressure
