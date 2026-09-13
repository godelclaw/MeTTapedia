import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialCoherentBound

/-!
# Material evolution of radial pancake normal components

The separation follows two actual material lifts, with a constant image
shift. The vorticity may be evaluated along either lift (or a third material
curve). Its pairing with the separation obeys an exact scalar equation.
The remainder retains strain-normal defect, relative velocity, unequal
endpoint gradient, and viscosity. Normal compression gives a squared-height
damping estimate, not an estimate of the vorticity-weighted source.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalRadialNormalEvolution

open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths PancakeLocalSpatialVelocity
open PancakeLocalMaterialTrajectories LocalAlignmentForcing LocalLowDiffusionBudget
open LocalJointDiffusionBudget
open LocalVorticitySeparation LocalRadialImageEvolution LocalRadialCoherentBound
open LocalMeanAlignmentBalance (velocity)
open Mettapedia.Analysis RadialPancakeCoherence
open scoped RealInnerProductSpace
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

def normalHeight (z : R3) (u : FourierVelocity) (x y : X3) (w : T3) : ℝ :=
  ⟪imageSeparation z x y, fullVorticity u w⟫

/-- Internal geometric and viscous terms; this is not an external body force. -/
def normalForcing (z : R3) (u : FourierVelocity) (nu : ℝ) (x y : X3) (w : T3) (σ : ℝ) : ℝ :=
  2 * ⟪normalDefect u (torusPoint x) σ (imageSeparation z x y), fullVorticity u w⟫ +
    ⟪imageVelocityRemainder z u x y, fullVorticity u w⟫ +
    ⟪imageSeparation z x y, gradientRemainder u (torusPoint x) w⟫ +
    nu * ⟪imageSeparation z x y, fullVorticityLaplacian u w⟫

theorem normalForcing_at_left (z : R3) (u : FourierVelocity) (nu : ℝ)
    (x y : X3) (σ : ℝ) :
    normalForcing z u nu x y (torusPoint x) σ =
      2 * ⟪normalDefect u (torusPoint x) σ (imageSeparation z x y),
        fullVorticity u (torusPoint x)⟫ +
      ⟪imageVelocityRemainder z u x y, fullVorticity u (torusPoint x)⟫ +
      nu * ⟪imageSeparation z x y, fullVorticityLaplacian u (torusPoint x)⟫ := by
  simp [normalForcing, gradientRemainder]

theorem normalRate_eq (z : R3) (u : FourierVelocity) (nu : ℝ)
    (x y : X3) (w : T3) (σ : ℝ) :
    ⟪velocity u (torusPoint x) - velocity u (torusPoint y), fullVorticity u w⟫ +
      ⟪imageSeparation z x y, fullStrainOperator u w (fullVorticity u w) +
        nu • fullVorticityLaplacian u w⟫ =
      2 * σ * normalHeight z u x y w + normalForcing z u nu x y w σ := by
  have h := normalPairRate_eq (gradient u (torusPoint x)) (fullVorticity u w)
    (imageSeparation z x y) (normalDefect u (torusPoint x) σ (imageSeparation z x y))
    (gradientRemainder u (torusPoint x) w + nu • fullVorticityLaplacian u w)
    (imageVelocityRemainder z u x y) σ
    (symmetric_normal_action u (torusPoint x) σ (imageSeparation z x y))
  have hw : gradient u (torusPoint x) (fullVorticity u w) +
      (gradientRemainder u (torusPoint x) w + nu • fullVorticityLaplacian u w) =
      fullStrainOperator u w (fullVorticity u w) + nu • fullVorticityLaplacian u w := by
    rw [← gradient_vorticity]
    simp only [gradientRemainder, sub_apply]
    abel
  have hv : gradient u (torusPoint x) (imageSeparation z x y) + imageVelocityRemainder z u x y =
      velocity u (torusPoint x) - velocity u (torusPoint y) := by
    simp [imageVelocityRemainder]
  rw [hw, hv] at h
  simpa only [normalHeight, normalForcing, inner_add_right, real_inner_smul_right,
    add_assoc] using h

/-- Choose `W = X` and `W = Y` for the two vorticities in the radial source. -/
theorem hasDerivAt_normalHeight_path {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X Y W : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
    (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t)
    (hW : HasDerivAt W (liftedVelocity s t (W t)) t) (z : R3) (σ : ℝ) :
    HasDerivAt (fun τ ↦ normalHeight z (s.coefficients τ) (X τ) (Y τ) (torusPoint (W τ)))
      (2 * σ * normalHeight z (s.coefficients t) (X t) (Y t) (torusPoint (W t)) +
        normalForcing z (s.coefficients t) nu (X t) (Y t) (torusPoint (W t)) σ) t := by
  have hw := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI W t ht hW
  let L := (WithLp.linearEquiv 2 ℝ X3).symm.toContinuousLinearEquiv
  have hh : HasDerivAt (fun τ ↦ imageSeparation z (X τ) (Y τ))
      (velocity (s.coefficients t) (torusPoint (X t)) -
        velocity (s.coefficients t) (torusPoint (Y t))) t :=
    (L.hasFDerivAt.comp_hasDerivAt t (hX.sub hY)).const_add z
  have h := hh.inner ℝ hw
  apply h.congr_deriv
  exact (add_comm _ _).trans (normalRate_eq z (s.coefficients t) nu (X t) (Y t) (torusPoint (W t)) σ)

def normalSquareRate (z : R3) (u : FourierVelocity) (nu : ℝ)
    (x y : X3) (w : T3) (σ : ℝ) : ℝ :=
  2 * normalHeight z u x y w * (2 * σ * normalHeight z u x y w + normalForcing z u nu x y w σ)

theorem hasDerivAt_sq_normalHeight_path {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X Y W : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
    (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t)
    (hW : HasDerivAt W (liftedVelocity s t (W t)) t) (z : R3) (σ : ℝ) :
    HasDerivAt (fun τ ↦ normalHeight z (s.coefficients τ) (X τ) (Y τ) (torusPoint (W τ)) ^ 2)
      (normalSquareRate z (s.coefficients t) nu (X t) (Y t) (torusPoint (W t)) σ) t := by
  have h := hasDerivAt_normalHeight_path s g hg hSum hu a b hab hI X Y W t ht hX hY hW z σ
  convert h.pow 2 using 1 <;> first | rfl | simp [normalSquareRate]

/-- The forcing cost remains explicit and unbounded by this theorem. -/
theorem normalSquareRate_le_of_compressive (z : R3) (u : FourierVelocity) (nu : ℝ)
    (x y : X3) (w : T3) (σ κ : ℝ) (hκ : 0 < κ) (hσ : σ ≤ -κ) :
    normalSquareRate z u nu x y w σ ≤ -2 * κ * normalHeight z u x y w ^ 2 +
      normalForcing z u nu x y w σ ^ 2 / (2 * κ) :=
  squareRate_le_of_compressive σ κ _ _ hκ hσ

def weightedNormalHeight (n : ℕ) (z : R3) (u : FourierVelocity) (x y : X3) (w : T3) : ℝ :=
  weightedHeight n (fullVorticity u w) (imageSeparation z x y)

/-- Exact endpoint weights from the coherent source estimate. -/
theorem normalMoment_eq_weightedNormalHeight (n : ℕ) (z : R3) (u : FourierVelocity) (x y : X3) :
    normalMoment (2 * (n + 1)) (fullVorticity u (torusPoint x))
      (fullVorticity u (torusPoint y)) (imageSeparation z x y) =
    |weightedNormalHeight n z u x y (torusPoint x)| +
      |weightedNormalHeight n z u x y (torusPoint y)| := by
  simp only [normalMoment, weightedNormalHeight, weightedHeight, RadialPower.radialPower,
    real_inner_smul_right, abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]

def weightedNormalRate (n : ℕ) (z : R3) (u : FourierVelocity) (nu : ℝ)
    (x y : X3) (w : T3) (σ : ℝ) : ℝ :=
  ‖fullVorticity u w‖ ^ (2 * (n + 1)) *
    (2 * σ * normalHeight z u x y w + normalForcing z u nu x y w σ) +
  (2 * (n + 1) : ℝ) * ‖fullVorticity u w‖ ^ (2 * n) *
    ⟪fullVorticity u w, fullStrainOperator u w (fullVorticity u w) +
      nu • fullVorticityLaplacian u w⟫ * normalHeight z u x y w

/-- No sign is assigned to the radial amplitude contribution. -/
theorem hasDerivAt_weightedNormalHeight_path {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X Y W : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
    (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t)
    (hW : HasDerivAt W (liftedVelocity s t (W t)) t) (n : ℕ) (z : R3) (σ : ℝ) :
    HasDerivAt (fun τ ↦ weightedNormalHeight n z (s.coefficients τ) (X τ) (Y τ) (torusPoint (W τ)))
      (weightedNormalRate n z (s.coefficients t) nu (X t) (Y t) (torusPoint (W t)) σ) t := by
  have hw := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI W t ht hW
  let L := (WithLp.linearEquiv 2 ℝ X3).symm.toContinuousLinearEquiv
  have hh : HasDerivAt (fun τ ↦ imageSeparation z (X τ) (Y τ))
      (velocity (s.coefficients t) (torusPoint (X t)) -
        velocity (s.coefficients t) (torusPoint (Y t))) t :=
    (L.hasFDerivAt.comp_hasDerivAt t (hX.sub hY)).const_add z
  apply (hasDerivAt_weightedHeight n hw hh).congr_deriv
  rw [weightedHeightRate_eq, normalRate_eq z (s.coefficients t) nu (X t) (Y t) (torusPoint (W t)) σ]
  rfl

end Mettapedia.FluidDynamics.NavierStokes.LocalRadialNormalEvolution
