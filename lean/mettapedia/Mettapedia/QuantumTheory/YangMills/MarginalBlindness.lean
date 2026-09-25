import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Marginal criteria cannot certify clustering

For a probability measure `μ` on `E` and a finite set of sites `X`, the product
measure `⊗ μ` and the diagonal measure, the law of the constant configuration
`fun _ => e` with `e ∼ μ`, have the same marginal `μ` at every site
(`map_eval_pi`, `map_eval_diagonal`).  Under the product measure, observables at
distinct sites are uncorrelated (`truncated_pi_eq_zero`).  Under the diagonal
measure, the truncated two-point function of `F` and `G` at any two sites is the
covariance of `F` and `G` under `μ` (`truncated_diagonal`), whatever the distance
between the sites.  So no uniform exponential bound holds for the diagonal
measures once the sites can be arbitrarily far apart, unless that covariance
vanishes (`covariance_eq_zero_of_exponentialBound`).

A condition on the one-site laws alone, applied at any block scale (a threshold
on block energies, on the fraction of blocks with large field strength, or on the
law of a blocked plaquette), therefore cannot imply decay of correlations: it
holds or fails for both measures at once.  A crossing criterion has to constrain
correlations or conditional laws.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Mettapedia.QuantumTheory.YangMills.MarginalBlindness

variable {X : Type*} {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]

/-- The diagonal measure: the law of the constant configuration `fun _ => e` with
`e ∼ μ`. -/
def diagonal : Measure (X → E) :=
  μ.map fun e _ => e

theorem measurable_diag : Measurable fun (e : E) (_ : X) => e :=
  measurable_pi_lambda _ fun _ => measurable_id

theorem map_eval_pi [Fintype X] (x : X) : (Measure.pi fun _ : X => μ).map (fun ω => ω x) = μ :=
  (measurePreserving_eval (fun _ : X => μ) x).map_eq

omit [IsProbabilityMeasure μ] in
theorem map_eval_diagonal (x : X) : (diagonal (X := X) μ).map (fun ω => ω x) = μ := by
  unfold diagonal
  rw [Measure.map_map (measurable_pi_apply x) measurable_diag]
  exact Measure.map_id

theorem integral_eval_pi [Fintype X] (F : E → ℝ) (hF : Measurable F) (x : X) :
    ∫ ω, F (ω x) ∂(Measure.pi fun _ : X => μ) = ∫ e, F e ∂μ := by
  calc ∫ ω, F (ω x) ∂(Measure.pi fun _ : X => μ)
      = ∫ e, F e ∂((Measure.pi fun _ : X => μ).map fun ω => ω x) :=
        (integral_map (μ := Measure.pi fun _ : X => μ) (f := F) (measurable_pi_apply x).aemeasurable
          (by rw [map_eval_pi]; exact hF.aestronglyMeasurable)).symm
    _ = ∫ e, F e ∂μ := by rw [map_eval_pi]

/-- Under the product measure, observables at distinct sites are uncorrelated. -/
theorem truncated_pi_eq_zero [Fintype X] [DecidableEq X] (F G : E → ℝ) (hF : Measurable F)
    (hG : Measurable G) {x y : X} (hxy : x ≠ y) :
    ∫ ω, F (ω x) * G (ω y) ∂(Measure.pi fun _ : X => μ) -
      (∫ ω, F (ω x) ∂(Measure.pi fun _ : X => μ)) *
        ∫ ω, G (ω y) ∂(Measure.pi fun _ : X => μ) = 0 := by
  set f : X → E → ℝ := fun i => if i = x then F else if i = y then G else fun _ => 1 with hf
  have hprod : ∀ ω : X → E, ∏ i, f i (ω i) = F (ω x) * G (ω y) := by
    intro ω
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ y),
      ← Finset.prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨hxy, Finset.mem_univ x⟩)]
    have hrest : ∏ i ∈ (Finset.univ.erase y).erase x, f i (ω i) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      obtain ⟨hix, hi'⟩ := Finset.mem_erase.mp hi
      obtain ⟨hiy, -⟩ := Finset.mem_erase.mp hi'
      simp [hf, hix, hiy]
    rw [hrest, one_mul]
    simp [hf, hxy.symm]
  have hint : ∀ i, ∫ e, f i e ∂μ = if i = x then ∫ e, F e ∂μ else if i = y then ∫ e, G e ∂μ
      else 1 := by
    intro i
    by_cases hix : i = x
    · simp [hf, hix]
    · by_cases hiy : i = y
      · subst hiy
        simp [hf, hix]
      · simp [hf, hix, hiy]
  have hmain : ∫ ω, F (ω x) * G (ω y) ∂(Measure.pi fun _ : X => μ) =
      (∫ e, F e ∂μ) * ∫ e, G e ∂μ := by
    simp_rw [← hprod]
    rw [integral_fintype_prod_eq_prod (μ := fun _ : X => μ) f]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ y),
      ← Finset.prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨hxy, Finset.mem_univ x⟩)]
    have hrest : ∏ i ∈ (Finset.univ.erase y).erase x, ∫ e, f i e ∂μ = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      obtain ⟨hix, hi'⟩ := Finset.mem_erase.mp hi
      obtain ⟨hiy, -⟩ := Finset.mem_erase.mp hi'
      rw [hint i]
      simp [hix, hiy]
    rw [hrest, one_mul, hint x, hint y]
    simp [hxy.symm]
  rw [hmain, integral_eval_pi μ F hF, integral_eval_pi μ G hG]
  ring

omit [IsProbabilityMeasure μ] in
/-- Under the diagonal measure, the truncated two-point function of `F` and `G`
at any two sites is their covariance under `μ`. -/
theorem truncated_diagonal (F G : E → ℝ) (hF : Measurable F) (hG : Measurable G) (x y : X) :
    ∫ ω, F (ω x) * G (ω y) ∂(diagonal μ) -
      (∫ ω, F (ω x) ∂(diagonal μ)) * ∫ ω, G (ω y) ∂(diagonal μ) =
    ∫ e, F e * G e ∂μ - (∫ e, F e ∂μ) * ∫ e, G e ∂μ := by
  unfold diagonal
  rw [integral_map (f := fun ω : X → E => F (ω x) * G (ω y)) measurable_diag.aemeasurable
      ((hF.comp (measurable_pi_apply x)).mul (hG.comp (measurable_pi_apply y))).aestronglyMeasurable,
    integral_map (f := fun ω : X → E => F (ω x)) measurable_diag.aemeasurable
      (hF.comp (measurable_pi_apply x)).aestronglyMeasurable,
    integral_map (f := fun ω : X → E => G (ω y)) measurable_diag.aemeasurable
      (hG.comp (measurable_pi_apply y)).aestronglyMeasurable]

omit [IsProbabilityMeasure μ] in
/-- If the diagonal measures on a family of pseudometric site sets satisfied a
uniform exponential bound on truncated two-point functions at pairs of sites that
are arbitrarily far apart, the covariance would vanish. -/
theorem covariance_eq_zero_of_exponentialBound {ι : Type*} (Sites : ι → Type*)
    [∀ L, PseudoMetricSpace (Sites L)]
    (F G : E → ℝ) (hF : Measurable F) (hG : Measurable G) (C κ : ℝ) (hκ : 0 < κ)
    (hbound : ∀ L (x y : Sites L),
      |∫ ω, F (ω x) * G (ω y) ∂(diagonal μ) -
          (∫ ω, F (ω x) ∂(diagonal μ)) * ∫ ω, G (ω y) ∂(diagonal μ)| ≤
        C * Real.exp (-κ * dist x y))
    (hfar : ∀ R : ℝ, ∃ L, ∃ x y : Sites L, R ≤ dist x y) :
    ∫ e, F e * G e ∂μ - (∫ e, F e ∂μ) * ∫ e, G e ∂μ = 0 := by
  set c := ∫ e, F e * G e ∂μ - (∫ e, F e ∂μ) * ∫ e, G e ∂μ
  have hle : ∀ R : ℝ, |c| ≤ |C| * Real.exp (-κ * R) := by
    intro R
    obtain ⟨L, x, y, hR⟩ := hfar R
    have h := hbound L x y
    rw [truncated_diagonal μ F G hF hG x y] at h
    calc |c| ≤ C * Real.exp (-κ * dist x y) := h
      _ ≤ |C| * Real.exp (-κ * dist x y) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      _ ≤ |C| * Real.exp (-κ * R) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
          apply Real.exp_le_exp.mpr
          nlinarith
  by_contra hc
  have hpos : 0 < |c| := abs_pos.mpr hc
  by_cases hC : |C| = 0
  · have := hle 0
    rw [hC, zero_mul] at this
    linarith
  · have hCpos : 0 < |C| := lt_of_le_of_ne (abs_nonneg C) (Ne.symm hC)
    set R := (Real.log |C| - Real.log (|c| / 2)) / κ + 1 with hR
    have h := hle R
    have hlt : |C| * Real.exp (-κ * R) < |c| := by
      have hkR : -κ * R = Real.log (|c| / 2) - Real.log |C| - κ := by
        rw [hR]
        field_simp
        ring
      rw [hkR, Real.exp_sub, Real.exp_sub, Real.exp_log (by positivity), Real.exp_log hCpos]
      have hek : 1 < Real.exp κ := Real.one_lt_exp_iff.mpr hκ
      rw [mul_div_assoc', mul_div_assoc', mul_comm |C|, mul_div_assoc,
        div_self hCpos.ne', mul_one, div_div]
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith

#print axioms truncated_pi_eq_zero
#print axioms truncated_diagonal
#print axioms covariance_eq_zero_of_exponentialBound

end Mettapedia.QuantumTheory.YangMills.MarginalBlindness
