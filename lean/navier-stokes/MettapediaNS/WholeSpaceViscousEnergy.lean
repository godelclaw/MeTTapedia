import Euler.OrdinaryGradientEnergy
import Euler.OrdinaryFieldScaling

/-!
# Viscous energy production in the upstream smooth-field representation

The nonlinear transport and pressure estimates are imported from the
upstream development. The Laplacian is assembled from its existing actual
directional-derivative fields. Its energy pairing is evaluated by the
imported whole-space integration-by-parts theorem, retaining the exact
nonnegative dissipation at every integer derivative order.

These are estimates for the literal Navier–Stokes right-hand side. Applying
them to a time evolution still requires its actual differential equation
and regularity; no evolution law is encoded as an assumed energy estimate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousEnergy

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanVectorIdentities
  EulerMeanSolenoidal Finset Laplacian
open scoped ContDiff

/-- Commutation in the upstream field representation is just mathlib's
symmetry of the actual second Fréchet derivative. -/
theorem directionalField_comm (A : SmoothL2Field Space) (v w : Space) :
    (A.directionalField v).directionalField w =
      (A.directionalField w).directionalField v := by
  apply field_ext
  funext x
  have hd : DifferentiableAt ℝ (fderiv ℝ A.field) x :=
    ((A.smooth.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have he (a b : Space) :
      fderiv ℝ (fun y ↦ fderiv ℝ A.field y a) x b =
        fderiv ℝ (fderiv ℝ A.field) x b a := by
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  change fderiv ℝ (fun y ↦ fderiv ℝ A.field y v) x w =
    fderiv ℝ (fun y ↦ fderiv ℝ A.field y w) x v
  rw [he, he]
  exact (A.smooth.contDiffAt.isSymmSndFDerivAt (by simp)).eq w v

theorem wordField_directionalField (A : SmoothL2Field Space) (v : Space)
    {n : ℕ} (w : Fin n → Fin 3) :
    wordField (A.directionalField v) w = (wordField A w).directionalField v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (wordField (A.directionalField v) (Fin.tail w)).directionalField (axis (w 0)) =
      ((wordField A (Fin.tail w)).directionalField (axis (w 0))).directionalField v
    rw [ih, directionalField_comm]

/-- The actual Euclidean Laplacian, as an upstream smooth L² field. -/
def laplacianField (A : SmoothL2Field Space) : SmoothL2Field Space :=
  sumField univ (fun i ↦ (A.directionalField (axis i)).directionalField (axis i))

theorem laplacianField_field (A : SmoothL2Field Space) (x : Space) :
    (laplacianField A).field x = Δ A.field x := by
  symm
  exact congrFun (vector_laplacian_eq_sum A.field A.smooth) x

theorem wordField_laplacianField (A : SmoothL2Field Space)
    {n : ℕ} (w : Fin n → Fin 3) :
    wordField (laplacianField A) w = laplacianField (wordField A w) := by
  simp only [laplacianField, wordField_sum, wordField_directionalField]

theorem inner_laplacianField (A : SmoothL2Field Space) :
    ⟪A.toLp, (laplacianField A).toLp⟫_ℝ =
      -∑ i : Fin 3, ‖(A.directionalField (axis i)).toLp‖ ^ 2 := by
  have h (i : Fin 3) :
      ⟪A.toLp, ((A.directionalField (axis i)).directionalField (axis i)).toLp⟫_ℝ =
        -‖(A.directionalField (axis i)).toLp‖ ^ 2 := by
    have hi := field_directional_inner A (A.directionalField (axis i)) (axis i)
    rw [real_inner_self_eq_norm_sq] at hi
    linarith
  simp only [laplacianField, toLp_sumField, inner_sum, h, sum_neg_distrib]

/-- Dissipation of the upstream integer-order velocity energy. -/
def wordDissipation (m : ℕ) (A : SmoothL2Field Space) : ℝ :=
  ∑ n ∈ range (m + 1), ∑ w : Fin n → Fin 3,
    ∑ i : Fin 3, ‖((wordField A w).directionalField (axis i)).toLp‖ ^ 2

theorem wordDissipation_nonneg (m : ℕ) (A : SmoothL2Field Space) :
    0 ≤ wordDissipation m A :=
  sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _

theorem integerEnergyProduction_laplacianField (m : ℕ) (A : SmoothL2Field Space) :
    integerEnergyProduction m A (laplacianField A) = -2 * wordDissipation m A := by
  simp only [integerEnergyProduction, wordField_laplacianField,
    inner_laplacianField, sum_neg_distrib, wordDissipation]
  ring

/-- The literal unforced NS right-hand side; `P` represents the pressure gradient. -/
def navierStokesRhs (ν : ℝ) (A P : SmoothL2Field Space) : SmoothL2Field Space :=
  addField (eulerRhs A P) (scaleField ν (laplacianField A))

theorem navierStokesRhs_field (ν : ℝ) (A P : SmoothL2Field Space) (x : Space) :
    (navierStokesRhs ν A P).field x =
      -fderiv ℝ A.field x (A.field x) - P.field x + ν • Δ A.field x := by
  simp only [navierStokesRhs, addField_field, eulerRhs_field, scaleField_field,
    laplacianField_field]

/-- Viscosity contributes exactly the dissipative term, without altering
the already-proved nonlinear production. -/
theorem integerEnergyProduction_navierStokesRhs
    (m : ℕ) (ν : ℝ) (A P : SmoothL2Field Space) :
    integerEnergyProduction m A (navierStokesRhs ν A P) =
      integerEnergyProduction m A (eulerRhs A P) - 2 * ν * wordDissipation m A := by
  have hw {n : ℕ} (w : Fin n → Fin 3) :
      wordField (scaleField ν (laplacianField A)) w =
        scaleField ν (wordField (laplacianField A) w) :=
    wordField_map _ _ _
  simp only [integerEnergyProduction, navierStokesRhs, wordField_add, hw,
    toLp_addField, scaleField_toLp, inner_add_right, real_inner_smul_right,
    wordField_laplacianField, inner_laplacianField, sum_add_distrib,
    ← mul_sum, wordDissipation, mul_neg, sum_neg_distrib]
  ring

/-- The upstream H³ transport estimate applies unchanged, with viscous
dissipation retained on the left. No nonlinear estimate is re-proved. -/
theorem h3_energyProduction_add_dissipation_le
    (ν : ℝ) (A P : SmoothL2Field Space) (K : ℝ)
    (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K)
    (hdiv : ∀ x, divergence A.field x = 0)
    (hA : A.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace) :
    integerEnergyProduction 3 A (navierStokesRhs ν A P) +
        2 * ν * wordDissipation 3 A ≤
      gradientEnergyConstant * K * wordEnergy 3 A := by
  rw [integerEnergyProduction_navierStokesRhs, sub_add_cancel]
  exact h3_energy_gradient A P K hK hdiv hA hP

/-- For nonnegative viscosity, dropping dissipation recovers exactly the
upstream transport-energy bound for the full NS right-hand side. -/
theorem h3_energyProduction_le_of_nonneg
    {ν : ℝ} (hν : 0 ≤ ν) (A P : SmoothL2Field Space) (K : ℝ)
    (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K)
    (hdiv : ∀ x, divergence A.field x = 0)
    (hA : A.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace) :
    integerEnergyProduction 3 A (navierStokesRhs ν A P) ≤
      gradientEnergyConstant * K * wordEnergy 3 A := by
  apply (le_add_of_nonneg_right
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hν)
      (wordDissipation_nonneg 3 A))).trans
  exact h3_energyProduction_add_dissipation_le ν A P K hK hdiv hA hP

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousEnergy
