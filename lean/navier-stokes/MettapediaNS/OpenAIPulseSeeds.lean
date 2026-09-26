import NavierStokes.PrimaryPulseBounds

/-!
# The seeds of the pulses in the forced breakdown are smaller than every power

In the breakdown construction for the forced problem, each primary pulse is
the solution of a linear amplitude equation started, at the beginning of its
slot `[0, L]`, from the seed `P(0) e₁`. Here `P` is the reference envelope
`exp ∫_{L/2}^v rate`, normalized to one at the midpoint of the slot. Its rate
`λ/√(1+s²) - λ(1+s²)/(1+u²)^{3/2}` is a coupling proportional to the sine of the
angle between the pulse wavevector `(1, s)` and the shear gradient, minus a
viscous damping proportional to `1 + s²`, and the tilt `s` grows linearly
through the slot.

The imported Gaussian bounds of the envelope give, at the start of the slot,

```text
exp(-u·maxSlope·L/8) ≤ P(0) ≤ exp(-u·minSlope·L/8),
```

so the pulse is amplified from its seed to its midpoint by at least
`exp(u·minSlope·L/8)`. Once the slot length exceeds a multiple of
`log(1/Q)`, the seed is below `Q^N`: the construction's slots have length of
order `log²(1/Q)` in a band of scale `Q`, so its seeds are smaller than every
power of the band scale.

The amplitude equation is linear, so the construction's amplification acts on
every seed: by uniqueness of linear solutions, the solution started from any
seed `σ e₁` is `σ / P(0)` times the constructed pulse at every time of the slot,
hence at least `|σ| exp(u·minSlope·L/8)` times its size. A seed that is only
polynomially small in the band scale is amplified super-polynomially beyond
the constructed pulse. The imported construction is used as proved; nothing
in it is reimplemented.
-/

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.OpenAIPulseSeeds

open Set
open _root_.NavierStokes.PrimaryPulseBounds _root_.NavierStokes.GaussianEnvelope

/-- **The seed of a pulse is a Gaussian tail.** -/
theorem seed_bounds {lam u L : ℝ} (hlam : 0 < lam) (hu : 0 < u) (hL : 0 < L) :
    Real.exp (-(u * referenceMaxSlope lam u) * L / 8) ≤ referenceP lam u L 0 ∧
      referenceP lam u L 0 ≤ Real.exp (-(u * referenceMinSlope lam u) * L / 8) := by
  have h := reference_gaussian_bounds hlam hu hL (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL.le⟩)
  have e1 : -(u * referenceMaxSlope lam u) * (0 - L / 2) ^ 2 / (2 * L) =
      -(u * referenceMaxSlope lam u) * L / 8 := by
    field_simp
    ring
  have e2 : -(u * referenceMinSlope lam u) * (0 - L / 2) ^ 2 / (2 * L) =
      -(u * referenceMinSlope lam u) * L / 8 := by
    field_simp
    ring
  rw [e1, e2] at h
  exact h

/-- The envelope equals one at the midpoint of the slot. -/
theorem referenceP_midpoint (lam u L : ℝ) : referenceP lam u L (L / 2) = 1 := by
  simp [referenceP, envelope]

/-- **The amplification from seed to midpoint is exponential in the slot
length.** -/
theorem amplification_ge {lam u L : ℝ} (hlam : 0 < lam) (hu : 0 < u) (hL : 0 < L) :
    Real.exp (u * referenceMinSlope lam u * L / 8) ≤
      referenceP lam u L (L / 2) / referenceP lam u L 0 := by
  rw [referenceP_midpoint, le_div_iff₀ (referenceP_pos lam u L 0)]
  have h := (seed_bounds hlam hu hL).2
  calc Real.exp (u * referenceMinSlope lam u * L / 8) * referenceP lam u L 0
      ≤ Real.exp (u * referenceMinSlope lam u * L / 8) *
          Real.exp (-(u * referenceMinSlope lam u) * L / 8) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = 1 := by
        rw [← Real.exp_add]
        simp only [neg_mul, neg_div, add_neg_cancel, Real.exp_zero]

/-- **Seeds below every power of the scale.** For a scale `0 < Q < 1` and an
exponent `N ≥ 0`, once the slot length is at least
`8 N log(1/Q) / (u·minSlope)` the seed is at most `Q^N`. -/
theorem seed_le_rpow {lam u L Q N : ℝ} (hlam : 0 < lam) (hu : 0 < u) (hL : 0 < L)
    (hQ0 : 0 < Q) (hL' : 8 * N * Real.log (1 / Q) / (u * referenceMinSlope lam u) ≤ L) :
    referenceP lam u L 0 ≤ Q ^ N := by
  have hm : 0 < u * referenceMinSlope lam u := mul_pos hu (referenceMinSlope_pos hlam hu)
  refine (seed_bounds hlam hu hL).2.trans ?_
  rw [Real.rpow_def_of_pos hQ0]
  apply Real.exp_le_exp.mpr
  rw [div_le_iff₀ hm] at hL'
  have hlog : Real.log (1 / Q) = -Real.log Q := by
    rw [one_div, Real.log_inv]
  rw [hlog] at hL'
  nlinarith

section Linearity

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ P] in
/-- **The homogeneous solution is linear in its seed.** -/
theorem actualSolution_smul {a b : ℝ} (hab : a ≤ b) {U : Set P} (A : P × ℝ → E →L[ℝ] E)
    (x₀ : P → E) (c : ℝ) (hA : ContinuousOn A (U ×ˢ Icc a b)) {p : P} (hp : p ∈ U)
    {t : ℝ} (ht : t ∈ Icc a b) :
    _root_.NavierStokes.JointODE.actualSolution hab A (fun q ↦ c • x₀ q) (fun _ ↦ 0) (p, t) =
      c • _root_.NavierStokes.JointODE.actualSolution hab A x₀ (fun _ ↦ 0) (p, t) := by
  have hf : ContinuousOn (fun _ : P × ℝ ↦ (0 : E)) (U ×ˢ Icc a b) := continuousOn_const
  have hB : ContinuousOn (fun s ↦ A (p, s)) (Icc a b) :=
    hA.comp (continuousOn_const.prodMk continuousOn_id) (fun s hs ↦ ⟨hp, hs⟩)
  set y : ℝ → E := fun s ↦
    _root_.NavierStokes.JointODE.actualSolution hab A (fun q ↦ c • x₀ q) (fun _ ↦ 0) (p, s) with hy_def
  set x : ℝ → E := fun s ↦
    _root_.NavierStokes.JointODE.actualSolution hab A x₀ (fun _ ↦ 0) (p, s) with hx_def
  have hy : ∀ s ∈ Icc a b, HasDerivAt y (A (p, s) (y s) + (fun _ : ℝ ↦ (0 : E)) s) s := by
    intro s hs
    have h := _root_.NavierStokes.JointODE.actualSolution_hasDerivAt hab A
      (fun q ↦ c • x₀ q) (fun _ ↦ (0 : E)) hA hf hp hs
    exact h
  have hw : ∀ s ∈ Icc a b, HasDerivAt (fun s ↦ c • x s)
      (A (p, s) (c • x s) + (fun _ : ℝ ↦ (0 : E)) s) s := by
    intro s hs
    have h := (_root_.NavierStokes.JointODE.actualSolution_hasDerivAt hab A x₀
      (fun _ ↦ (0 : E)) hA hf hp hs).const_smul c
    refine h.congr_deriv ?_
    rw [map_smul]
    simp [hx_def]
  have hinit : y a = c • x a := by
    simp only [hy_def, hx_def, _root_.NavierStokes.JointODE.actualSolution_initial]
  exact _root_.NavierStokes.TangentODE.linear_solution_unique hab (fun s ↦ A (p, s))
    (fun _ ↦ 0) hB hy hw hinit ht

omit [NormedSpace ℝ P] in
/-- The reparametrized homogeneous solution is linear in its seed. -/
theorem reparamSolution_smul {a b : ℝ} (hab : a ≤ b) {U : Set P} (A : P × ℝ → E →L[ℝ] E)
    (x₀ : P → E) (c : ℝ) (hA : ContinuousOn A (U ×ˢ Icc a b)) {z : P × ℝ}
    (hz : z ∈ U ×ˢ Icc a b) :
    _root_.NavierStokes.JointODE.reparamSolution a A (fun q ↦ c • x₀ q) (fun _ ↦ 0) z =
      c • _root_.NavierStokes.JointODE.reparamSolution a A x₀ (fun _ ↦ 0) z := by
  rw [_root_.NavierStokes.JointODE.reparamSolution_eq_actualSolution hab A _ _ hA
      continuousOn_const hz,
    _root_.NavierStokes.JointODE.reparamSolution_eq_actualSolution hab A _ _ hA
      continuousOn_const hz]
  exact actualSolution_smul hab A x₀ c hA hz.1 hz.2

end Linearity

section Response

variable {Q : Type} [NormedAddCommGroup Q]

/-- **Any seed is amplified like the constructed pulse.** The homogeneous
solution started from the seed `σ e₁` is `σ / P(0)` times the constructed pulse
at every time of the slot. -/
theorem seeded_eq_smul_fundamental {d : _root_.NavierStokes.PrimaryODE.FrameData Q}
    {lam u L : ℝ} (hL : 0 < L) {U : Set Q} (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    (σ : ℝ) {p : Q} (hp : p ∈ U) {t : ℝ} (ht : t ∈ Icc 0 L) :
    _root_.NavierStokes.JointODE.reparamSolution 0 (d.coefficient 1) (fun _ ↦ σ • positiveSeed)
        (fun _ ↦ 0) (p, t) =
      (σ / referenceP lam u L 0) • fundamental d lam u L (p, t) := by
  have hP := referenceP_pos lam u L 0
  have e : (fun _ : Q ↦ σ • positiveSeed) =
      (fun q : Q ↦ (σ / referenceP lam u L 0) •
        (fun _ : Q ↦ referenceP lam u L 0 • positiveSeed) q) := by
    funext q
    rw [smul_smul, div_mul_cancel₀ _ hP.ne']
  rw [e]
  exact reparamSolution_smul hL.le (d.coefficient 1) (fun _ ↦ referenceP lam u L 0 • positiveSeed)
    _ hA ⟨hp, ht⟩

/-- **The overshoot factor.** The response to the seed `σ e₁` is at least
`|σ| exp(u·minSlope·L/8)` times the size of the constructed pulse at every time
of the slot. -/
theorem norm_seeded_ge {d : _root_.NavierStokes.PrimaryODE.FrameData Q}
    {lam u L : ℝ} (hlam : 0 < lam) (hu : 0 < u) (hL : 0 < L) {U : Set Q}
    (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L)) (σ : ℝ) {p : Q} (hp : p ∈ U) {t : ℝ}
    (ht : t ∈ Icc 0 L) :
    |σ| * Real.exp (u * referenceMinSlope lam u * L / 8) * ‖fundamental d lam u L (p, t)‖ ≤
      ‖_root_.NavierStokes.JointODE.reparamSolution 0 (d.coefficient 1) (fun _ ↦ σ • positiveSeed)
        (fun _ ↦ 0) (p, t)‖ := by
  rw [seeded_eq_smul_fundamental hL hA σ hp ht, norm_smul, Real.norm_eq_abs, abs_div,
    abs_of_pos (referenceP_pos lam u L 0)]
  have hP := referenceP_pos lam u L 0
  have hs := (seed_bounds hlam hu hL).2
  have hinv : Real.exp (u * referenceMinSlope lam u * L / 8) ≤ 1 / referenceP lam u L 0 := by
    rw [le_div_iff₀ hP]
    calc Real.exp (u * referenceMinSlope lam u * L / 8) * referenceP lam u L 0
        ≤ Real.exp (u * referenceMinSlope lam u * L / 8) *
            Real.exp (-(u * referenceMinSlope lam u) * L / 8) :=
          mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ = 1 := by
          rw [← Real.exp_add]
          simp only [neg_mul, neg_div, add_neg_cancel, Real.exp_zero]
  have hF := norm_nonneg (fundamental d lam u L (p, t))
  have hσ := abs_nonneg σ
  calc |σ| * Real.exp (u * referenceMinSlope lam u * L / 8) * ‖fundamental d lam u L (p, t)‖
      ≤ |σ| * (1 / referenceP lam u L 0) * ‖fundamental d lam u L (p, t)‖ := by gcongr
    _ = |σ| / referenceP lam u L 0 * ‖fundamental d lam u L (p, t)‖ := by ring

end Response

end Mettapedia.FluidDynamics.NavierStokes.OpenAIPulseSeeds
