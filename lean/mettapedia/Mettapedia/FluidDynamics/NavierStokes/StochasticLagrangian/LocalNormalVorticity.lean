import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialNormalEvolution
import Mettapedia.Analysis.RadialAmplitudeBound

/-!
# Normalized normal vorticity along actual material separations

The compression rate is the Rayleigh quotient of the actual strain along
the actual image separation. Its strain defect is orthogonal to that
separation. Internal geometric and viscous forcing remains explicit.
Nonpositive compression alone is not a global vorticity estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity

open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths PancakeLocalSpatialVelocity
open PancakeLocalMaterialTrajectories LocalAlignmentForcing LocalLowDiffusionBudget
open LocalJointDiffusionBudget LocalVorticitySeparation LocalRadialImageEvolution LocalRadialCoherentBound
open LocalMeanAlignmentBalance (velocity)
open Mettapedia.Analysis
open scoped RealInnerProductSpace
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

def strainQuotient (u : FourierVelocity) (x : T3) (h : R3) : ℝ :=
  ⟪h, fullStrainOperator u x h⟫ / ‖h‖ ^ 2

theorem normalDefect_orthogonal (u : FourierVelocity) (x : T3) (h : R3) :
    ⟪h, normalDefect u x (strainQuotient u x h) h⟫ = 0 := by
  by_cases hh : h = 0
  · simp [hh]
  · simp only [normalDefect, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, strainQuotient]
    field_simp [norm_ne_zero_iff.mpr hh]
    ring

def component (z : R3) (u : FourierVelocity) (x y : X3) (w : T3) : ℝ :=
  NormalVorticityEnergy.component (fullVorticity u w) (imageSeparation z x y)

/-- This is constructed internal forcing, not an external force or a bound. -/
def forcing (z : R3) (u : FourierVelocity) (nu : ℝ) (x y : X3) (w : T3) : ℝ :=
  let h := imageSeparation z x y
  NormalVorticityEnergy.forcingNumerator (fullVorticity u w) h
    (normalDefect u (torusPoint x) (strainQuotient u (torusPoint x) h) h)
    (gradientRemainder u (torusPoint x) w + nu • fullVorticityLaplacian u w)
    (imageVelocityRemainder z u x y) / ‖h‖

theorem forcing_eq (z : R3) (u : FourierVelocity) (nu : ℝ) (x y : X3) (w : T3) :
    forcing z u nu x y w =
      (2 * ⟪normalDefect u (torusPoint x)
          (strainQuotient u (torusPoint x) (imageSeparation z x y)) (imageSeparation z x y),
          fullVorticity u w⟫ +
        ⟪imageVelocityRemainder z u x y, fullVorticity u w⟫ +
        ⟪imageSeparation z x y, gradientRemainder u (torusPoint x) w⟫ +
        nu * ⟪imageSeparation z x y, fullVorticityLaplacian u w⟫ -
        ⟪imageSeparation z x y, fullVorticity u w⟫ *
          ⟪imageSeparation z x y, imageVelocityRemainder z u x y⟫ / ‖imageSeparation z x y‖ ^ 2) /
        ‖imageSeparation z x y‖ := by
  unfold forcing
  dsimp only
  rw [NormalVorticityEnergy.forcingNumerator_of_orthogonal _ _ _ _ _
    (normalDefect_orthogonal _ _ _)]
  simp only [inner_add_right, real_inner_smul_right, add_assoc]

theorem forcing_eq_nonviscous_add (z : R3) (u : FourierVelocity) (nu : ℝ)
    (x y : X3) (w : T3) :
    forcing z u nu x y w = forcing z u 0 x y w +
      nu * NormalVorticityEnergy.component (fullVorticityLaplacian u w) (imageSeparation z x y) := by
  simp only [forcing_eq, NormalVorticityEnergy.component, zero_mul, add_zero]
  ring

/-- The coefficient is attached to this image separation, not a selected
strain eigenvector substituted for it. -/
theorem abs_amplitude_image_le (n N : ℕ) (z : R3) (u : FourierVelocity)
    (x y : X3) (w : T3) (v v' : R3) (hz : imageSeparation z x y ≠ 0) :
    |SignedCrossKernel.amplitudeCurvature n
      (RadialRieszRegularization.tensor N (imageSeparation z x y)) (fullVorticity u w) v v'| ≤
      2 * (2 * (n + 2) : ℝ) *
        |RadialRieszRegularization.radialCoefficient N (EuclideanSpace.single 0 1) (imageSeparation z x y)| *
        ‖imageSeparation z x y‖ ^ 2 * ‖fullVorticity u w‖ ^ (2 * (n + 2)) * ‖v - v'‖ ^ 2 *
        |component z u x y w| :=
  RadialPancakeCurvature.abs_amplitudeCurvature_tensor_le N n (EuclideanSpace.single 0 1)
    (by simp) hz _ v v'

theorem rate_eq (z : R3) (u : FourierVelocity) (nu : ℝ)
    (x y : X3) (w : T3) (hz : imageSeparation z x y ≠ 0) :
    NormalVorticityEnergy.rate (fullVorticity u w) (imageSeparation z x y)
      (fullStrainOperator u w (fullVorticity u w) + nu • fullVorticityLaplacian u w)
      (velocity u (torusPoint x) - velocity u (torusPoint y)) =
      strainQuotient u (torusPoint x) (imageSeparation z x y) * component z u x y w +
        forcing z u nu x y w := by
  have he := NormalVorticityEnergy.rate_eq_strain_add_forcing
    (gradient u (torusPoint x)) (fullVorticity u w) (imageSeparation z x y)
    (normalDefect u (torusPoint x) (strainQuotient u (torusPoint x) (imageSeparation z x y))
      (imageSeparation z x y))
    (gradientRemainder u (torusPoint x) w + nu • fullVorticityLaplacian u w)
    (imageVelocityRemainder z u x y) _ hz (symmetric_normal_action _ _ _ _)
  have hw : gradient u (torusPoint x) (fullVorticity u w) +
      (gradientRemainder u (torusPoint x) w + nu • fullVorticityLaplacian u w) =
      fullStrainOperator u w (fullVorticity u w) + nu • fullVorticityLaplacian u w := by
    rw [← gradient_vorticity]
    simp only [gradientRemainder, sub_apply]
    abel
  have hv : gradient u (torusPoint x) (imageSeparation z x y) + imageVelocityRemainder z u x y =
      velocity u (torusPoint x) - velocity u (torusPoint y) := by simp [imageVelocityRemainder]
  rw [hw, hv] at he
  exact he

theorem hasDerivAt_component_path {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X Y W : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
    (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t)
    (hW : HasDerivAt W (liftedVelocity s t (W t)) t) (z : R3)
    (hz : imageSeparation z (X t) (Y t) ≠ 0) :
    HasDerivAt (fun τ ↦ component z (s.coefficients τ) (X τ) (Y τ) (torusPoint (W τ)))
      (strainQuotient (s.coefficients t) (torusPoint (X t)) (imageSeparation z (X t) (Y t)) *
        component z (s.coefficients t) (X t) (Y t) (torusPoint (W t)) +
        forcing z (s.coefficients t) nu (X t) (Y t) (torusPoint (W t))) t := by
  have hw := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI W t ht hW
  let L := (WithLp.linearEquiv 2 ℝ X3).symm.toContinuousLinearEquiv
  have hh : HasDerivAt (fun τ ↦ imageSeparation z (X τ) (Y τ))
      (velocity (s.coefficients t) (torusPoint (X t)) -
        velocity (s.coefficients t) (torusPoint (Y t))) t :=
    (L.hasFDerivAt.comp_hasDerivAt t (hX.sub hY)).const_add z
  exact (NormalVorticityEnergy.hasDerivAt_component hw hh hz).congr_deriv
    (rate_eq z (s.coefficients t) nu (X t) (Y t) (torusPoint (W t)) hz)

end Mettapedia.FluidDynamics.NavierStokes.LocalNormalVorticity
