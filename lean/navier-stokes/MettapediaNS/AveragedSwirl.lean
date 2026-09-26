import MettapediaNS.SwirlBudget
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The averaged swirl of a general flow and the torque that must feed it

For a flow without any symmetry, average the swirl `Γ = x₀ u₁ - x₁ u₀` over
the circles about the third axis. At every spatial local maximum of the
averaged swirl off the axis, its growth is bounded by the average of the
advection of the swirl and of the torque of the force:

```text
∂ₜ ⟨Γ⟩ ≤ -⟨(u · ∇)Γ⟩ + ⟨x₀ f₁ - x₁ f₀⟩.
```

Along each circle the pressure's angular derivative averages to zero; the
Laplacian of the swirl averages to the Laplacian of the average, which is
nonpositive at a maximum; and the axial vorticity averages to zero at a
critical point of the average, because
`x₀ ∂₀Γ + x₁ ∂₁Γ = r² ω₃ + ∂_θ(x₀ u₀ + x₁ u₁)` holds for every velocity and
angular derivatives average to zero. For an axisymmetric flow the average of
the advection vanishes at the maximum; for a general flow it is the angular
momentum that the non-axisymmetric part carries into the maximum. Indeed the
rotation-equivariant average `ū` of the velocity satisfies
`ū(rot φ x) = rot φ (ū x)`, so its contribution is the derivative of the
circle integral along the line through `x` in the direction `ū x`, which
vanishes at a maximum: only the fluctuation `u - ū` carries swirl into it.
Integrated in time, the maximal averaged swirl grows by at most the time
integral of this torque.
-/

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.AveragedSwirl

open Set Filter Topology MeasureTheory
open _root_.NavierStokes.ProblemStatement
open Mettapedia.FluidDynamics.NavierStokes.SwirlBudget

section Rotations

theorem rot_add (φ : ℝ) (x y : Space) : rot φ (x + y) = rot φ x + rot φ y := by
  ext i
  fin_cases i <;> simp [rot] <;> ring

theorem rot_smul (φ c : ℝ) (x : Space) : rot φ (c • x) = c • rot φ x := by
  ext i
  fin_cases i <;> simp [rot] <;> ring

theorem rot_line (φ s : ℝ) (x v : Space) : rot φ (x + s • v) = rot φ x + s • rot φ v := by
  rw [rot_add, rot_smul]

/-- The horizontal part `(x₀, x₁, 0)`. -/
def horiz (x : Space) : Space := !₂[x 0, x 1, 0]

theorem rot_horiz (φ : ℝ) (x : Space) : rot φ (horiz x) = horiz (rot φ x) := by
  ext i
  fin_cases i <;> simp [rot, horiz]

theorem normSq_rot (φ : ℝ) (x : Space) :
    (rot φ x) 0 ^ 2 + (rot φ x) 1 ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  simp only [rot]
  simp
  nlinarith [Real.sin_sq_add_cos_sq φ]

theorem continuous_rot : Continuous (fun p : ℝ × Space ↦ rot p.1 p.2) := by
  have h : ∀ i : Fin 3, Continuous (fun p : ℝ × Space ↦ p.2 i) := fun i ↦
    ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp continuous_snd)
  have hv : Continuous (fun p : ℝ × Space ↦ ![Real.cos p.1 * p.2 0 - Real.sin p.1 * p.2 1,
      Real.sin p.1 * p.2 0 + Real.cos p.1 * p.2 1, p.2 2]) := by
    refine continuous_pi fun i ↦ ?_
    fin_cases i
    · exact ((Real.continuous_cos.comp continuous_fst).mul (h 0)).sub
        ((Real.continuous_sin.comp continuous_fst).mul (h 1))
    · exact ((Real.continuous_sin.comp continuous_fst).mul (h 0)).add
        ((Real.continuous_cos.comp continuous_fst).mul (h 1))
    · exact h 2
  have hc := Continuous.comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous hv
  exact hc

@[fun_prop]
theorem Continuous.rotComp {X : Type*} [TopologicalSpace X] {f : X → ℝ} {g : X → Space}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x ↦ rot (f x) (g x)) := by
  have h := Continuous.comp continuous_rot (Continuous.prodMk hf hg)
  exact h

end Rotations

section Parametric

/-- **Differentiation under the integral sign for continuous data.** -/
theorem hasDerivAt_intervalIntegral_of_continuous {F F' : ℝ → ℝ → ℝ} {a b s₀ : ℝ}
    (hF : ∀ s, Continuous (F s)) (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ s t, HasDerivAt (fun s ↦ F s t) (F' s t) s) :
    HasDerivAt (fun s ↦ ∫ t in a..b, F s t) (∫ t in a..b, F' s₀ t) s₀ := by
  have hK : IsCompact (Metric.closedBall s₀ 1 ×ˢ uIcc a b) :=
    (isCompact_closedBall s₀ 1).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'.continuousOn
  have hF't : ∀ s, Continuous (F' s) := fun s ↦ hF'.comp (continuous_const.prodMk continuous_id)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ ↦ C) (Metric.closedBall_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s ↦ (hF s).aestronglyMeasurable)
    ((hF s₀).intervalIntegrable a b) (hF't s₀).aestronglyMeasurable
    (Eventually.of_forall fun t ht s hs ↦ hC (s, t) ⟨hs, uIoc_subset_uIcc ht⟩)
    intervalIntegrable_const (Eventually.of_forall fun t _ s _ ↦ hd s t)).2

end Parametric

/-- The integral of a scalar field over the circle through `x` about the third axis. -/
def circleInt (g : Space → ℝ) (x : Space) : ℝ := ∫ φ in (0 : ℝ)..(2 * Real.pi), g (rot φ x)

section Line

variable {g : Space → ℝ}

theorem continuous_rot_line (x v : Space) :
    Continuous (fun p : ℝ × ℝ ↦ rot p.2 (x + p.1 • v)) := by
  fun_prop

/-- **The derivative of the circle integral along a line.** -/
theorem hasDerivAt_circleInt_line (hg : ContDiff ℝ 1 g) (x v : Space) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ circleInt g (x + s • v))
      (∫ φ in (0 : ℝ)..(2 * Real.pi), fderiv ℝ g (rot φ (x + s₀ • v)) (rot φ v)) s₀ := by
  have hgd : ∀ y, HasFDerivAt g (fderiv ℝ g y) y :=
    fun y ↦ (hg.differentiable (by norm_num) y).hasFDerivAt
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  refine hasDerivAt_intervalIntegral_of_continuous (F := fun s φ ↦ g (rot φ (x + s • v)))
    (F' := fun s φ ↦ fderiv ℝ g (rot φ (x + s • v)) (rot φ v)) (fun s ↦ ?_) ?_ (fun s φ ↦ ?_)
  · have hc := hg.continuous
    fun_prop
  · have hc := hDc
    fun_prop
  · have hl : HasDerivAt (fun s : ℝ ↦ rot φ (x + s • v)) (rot φ v) s := by
      have e : (fun s : ℝ ↦ rot φ (x + s • v)) = fun s ↦ rot φ x + s • rot φ v :=
        funext fun s ↦ rot_line φ s x v
      rw [e]
      exact HasDerivAt.const_add _ (by simpa using HasDerivAt.smul_const (hasDerivAt_id s) (rot φ v))
    exact HasFDerivAt.comp_hasDerivAt s (hgd _) hl

end Line

section Radial

variable {U : Space → Space}

/-- The radial momentum density `x₀ u₀ + x₁ u₁`, which is `r u_r`. -/
def radialSlice (U : Space → Space) (y : Space) : ℝ := y 0 * U y 0 + y 1 * U y 1

theorem fderiv_radialSlice_apply {y : Space} (hU : DifferentiableAt ℝ U y) (v : Space) :
    fderiv ℝ (radialSlice U) y v =
      y 0 * (fderiv ℝ U y v) 0 + U y 0 * v 0 + (y 1 * (fderiv ℝ U y v) 1 + U y 1 * v 1) := by
  have h := ((hasFDerivAt_coord 0 y).mul (hasFDerivAt_comp_coord hU 0)).add
    ((hasFDerivAt_coord 1 y).mul (hasFDerivAt_comp_coord hU 1))
  have h' : HasFDerivAt (radialSlice U) _ y := h
  rw [h'.fderiv]
  simp [smul_eq_mul]

theorem horiz_eq (y : Space) : horiz y = y 0 • e 0 + y 1 • e 1 := by
  ext i
  fin_cases i <;> simp [horiz, e_apply]

/-- **The radial derivative of the swirl.** For every differentiable velocity,
`x₀ ∂₀Γ + x₁ ∂₁Γ = r² ω₃ + ∂_θ (x₀ u₀ + x₁ u₁)`. -/
theorem fderiv_swirl_horiz {y : Space} (hU : DifferentiableAt ℝ U y) :
    fderiv ℝ (swirlSlice U) y (horiz y) =
      (y 0 ^ 2 + y 1 ^ 2) * ((fderiv ℝ U y (e 0)) 1 - (fderiv ℝ U y (e 1)) 0) +
        angularDeriv (radialSlice U) y := by
  rw [angularDeriv, fderiv_swirlSlice_apply hU, fderiv_radialSlice_apply hU, angular_eq, horiz_eq]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, e_apply]
  simp
  ring

theorem contDiff_swirlSlice {n : WithTop ℕ∞} (hU : ContDiff ℝ n U) : ContDiff ℝ n (swirlSlice U) := by
  have c0 := (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).contDiff (n := n)
  have c1 := (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).contDiff (n := n)
  have h := ContDiff.sub (ContDiff.mul c0 (ContDiff.comp c1 hU)) (ContDiff.mul c1 (ContDiff.comp c0 hU))
  exact h

theorem contDiff_radialSlice {n : WithTop ℕ∞} (hU : ContDiff ℝ n U) : ContDiff ℝ n (radialSlice U) := by
  have c0 := (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).contDiff (n := n)
  have c1 := (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).contDiff (n := n)
  have h := ContDiff.add (ContDiff.mul c0 (ContDiff.comp c0 hU)) (ContDiff.mul c1 (ContDiff.comp c1 hU))
  exact h

/-- **At a local maximum of the circle integral of the swirl, off the axis,
the axial vorticity integrates to zero around the circle.** -/
theorem integral_axialVorticity_eq_zero (hU : ContDiff ℝ 2 U) {x : Space}
    (hmax : IsLocalMax (circleInt (swirlSlice U)) x) (hr : x 0 ^ 2 + x 1 ^ 2 ≠ 0) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
      ((fderiv ℝ U (rot φ x) (e 0)) 1 - (fderiv ℝ U (rot φ x) (e 1)) 0) = 0 := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have hΓ1 : ContDiff ℝ 1 (swirlSlice U) := contDiff_swirlSlice hU1
  have hUd : ∀ y, DifferentiableAt ℝ U y := fun y ↦ hU1.differentiable (by norm_num) y
  -- the derivative along the horizontal radial line vanishes
  have hline := hasDerivAt_circleInt_line hΓ1 x (horiz x) 0
  have hlmax : IsLocalMax (fun s : ℝ ↦ circleInt (swirlSlice U) (x + s • horiz x)) 0 := by
    have hx0 : (fun s : ℝ ↦ x + s • horiz x) 0 = x := by simp
    have h1 : IsLocalMax (circleInt (swirlSlice U)) ((fun s : ℝ ↦ x + s • horiz x) 0) := by
      rw [hx0]
      exact hmax
    have h2 := IsLocalMax.comp_continuous (g := fun s : ℝ ↦ x + s • horiz x) (b := 0) h1
      (hasDerivAt_line x (horiz x) 0).continuousAt
    exact h2
  have h0 := hline.deriv.symm.trans (IsLocalMax.deriv_eq_zero hlmax)
  -- rewrite the integrand pointwise
  have hpt : ∀ φ : ℝ, fderiv ℝ (swirlSlice U) (rot φ (x + (0 : ℝ) • horiz x)) (rot φ (horiz x)) =
      (x 0 ^ 2 + x 1 ^ 2) * ((fderiv ℝ U (rot φ x) (e 0)) 1 - (fderiv ℝ U (rot φ x) (e 1)) 0) +
        angularDeriv (radialSlice U) (rot φ x) := by
    intro φ
    rw [zero_smul, add_zero, rot_horiz, fderiv_swirl_horiz (hUd _), normSq_rot]
  simp only [hpt] at h0
  -- the angular part integrates to zero
  have hang := integral_angularDeriv_rot (contDiff_radialSlice hU1) x
  have hDc : Continuous (fderiv ℝ U) := hU1.continuous_fderiv (by norm_num)
  have hc1 : Continuous (fun φ : ℝ ↦ (fderiv ℝ U (rot φ x) (e 0)) 1 - (fderiv ℝ U (rot φ x) (e 1)) 0) := by
    have h0' : Continuous (fun φ : ℝ ↦ (fderiv ℝ U (rot φ x) (e 0)) 1) :=
      (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).continuous.comp (by fun_prop)
    have h1' : Continuous (fun φ : ℝ ↦ (fderiv ℝ U (rot φ x) (e 1)) 0) :=
      (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).continuous.comp (by fun_prop)
    exact h0'.sub h1'
  have hc2 : Continuous (fun φ : ℝ ↦ angularDeriv (radialSlice U) (rot φ x)) := by
    have hRc : Continuous (fderiv ℝ (radialSlice U)) :=
      (contDiff_radialSlice hU1).continuous_fderiv (by norm_num)
    have hang' : Continuous angular := by
      have e : angular = fun y : Space ↦ y 0 • e 1 - y 1 • e 0 := funext angular_eq
      rw [e]
      fun_prop
    unfold angularDeriv
    fun_prop
  rw [intervalIntegral.integral_add ((hc1.const_mul _).intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _), intervalIntegral.integral_const_mul, hang, add_zero] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h hr
  · exact h

end Radial

section Laplacian

variable {g : Space → ℝ}

/-- The second derivative of the circle integral along a line. -/
theorem hasDerivAt_circleInt_line_deriv (hg : ContDiff ℝ 2 g) (x v : Space) :
    HasDerivAt (fun s : ℝ ↦ ∫ φ in (0 : ℝ)..(2 * Real.pi), fderiv ℝ g (rot φ (x + s • v)) (rot φ v))
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
        fderiv ℝ (fderiv ℝ g) (rot φ (x + (0 : ℝ) • v)) (rot φ v) (rot φ v)) (0 : ℝ) := by
  have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (by norm_num)
  have hD1 : Continuous (fderiv ℝ g) := hg1.continuous
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ g)) := hg1.continuous_fderiv (by norm_num)
  have hDd : ∀ y, HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) y) y :=
    fun y ↦ (hg1.differentiable (by norm_num) y).hasFDerivAt
  refine hasDerivAt_intervalIntegral_of_continuous
    (F := fun s φ ↦ fderiv ℝ g (rot φ (x + s • v)) (rot φ v))
    (F' := fun s φ ↦ fderiv ℝ (fderiv ℝ g) (rot φ (x + s • v)) (rot φ v) (rot φ v))
    (fun s ↦ ?_) ?_ (fun s φ ↦ ?_)
  · fun_prop
  · fun_prop
  · have hl : HasDerivAt (fun s : ℝ ↦ rot φ (x + s • v)) (rot φ v) s := by
      have e : (fun s : ℝ ↦ rot φ (x + s • v)) = fun s ↦ rot φ x + s • rot φ v :=
        funext fun s ↦ rot_line φ s x v
      rw [e]
      exact HasDerivAt.const_add _ (by simpa using HasDerivAt.smul_const (hasDerivAt_id s) (rot φ v))
    have hc := HasFDerivAt.comp_hasDerivAt s (hDd _) hl
    have h := HasDerivAt.clm_apply hc (hasDerivAt_const s (rot φ v))
    simpa using h

/-- **Along every line, the circle integral has nonpositive second derivative
at a local maximum.** -/
theorem second_deriv_circleInt_nonpos (hg : ContDiff ℝ 2 g) {x : Space}
    (hmax : IsLocalMax (circleInt g) x) (v : Space) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), fderiv ℝ (fderiv ℝ g) (rot φ x) (rot φ v) (rot φ v) ≤ 0 := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  set L : ℝ → ℝ := fun s ↦ circleInt g (x + s • v) with hL
  have hderiv : deriv L = fun s ↦ ∫ φ in (0 : ℝ)..(2 * Real.pi),
      fderiv ℝ g (rot φ (x + s • v)) (rot φ v) :=
    funext fun s ↦ (hasDerivAt_circleInt_line hg1 x v s).deriv
  have h2 := (hasDerivAt_circleInt_line_deriv hg x v).deriv
  have hlmax : IsLocalMax L 0 := by
    have hx0 : (fun s : ℝ ↦ x + s • v) 0 = x := by simp
    have h1 : IsLocalMax (circleInt g) ((fun s : ℝ ↦ x + s • v) 0) := by
      rw [hx0]
      exact hmax
    have h3 := IsLocalMax.comp_continuous (g := fun s : ℝ ↦ x + s • v) (b := 0) h1
      (hasDerivAt_line x v 0).continuousAt
    exact h3
  have hLc : ContinuousAt L 0 := (hasDerivAt_circleInt_line hg1 x v 0).continuousAt
  have h := deriv_deriv_nonpos_of_isLocalMax hlmax hLc
  rw [hderiv, h2] at h
  simpa using h

theorem rot_e0 (φ : ℝ) : rot φ (e 0) = Real.cos φ • e 0 + Real.sin φ • e 1 := by
  ext i
  fin_cases i <;> simp [rot, e_apply]

theorem rot_e1 (φ : ℝ) : rot φ (e 1) = (-Real.sin φ) • e 0 + Real.cos φ • e 1 := by
  ext i
  fin_cases i <;> simp [rot, e_apply]

theorem rot_e2 (φ : ℝ) : rot φ (e 2) = e 2 := by
  ext i
  fin_cases i <;> simp [rot, e_apply]

/-- **The trace of a bilinear form is invariant under the rotations about the
third axis.** -/
theorem sum_rot_basis (B : Space →L[ℝ] Space →L[ℝ] ℝ) (φ : ℝ) :
    ∑ i : Fin 3, B (rot φ (e i)) (rot φ (e i)) = ∑ i : Fin 3, B (e i) (e i) := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three, rot_e0, rot_e1, rot_e2]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  linear_combination (B (e 0) (e 0) + B (e 1) (e 1)) * Real.sin_sq_add_cos_sq φ

theorem fderiv_fderiv_apply_eq (hg : ContDiff ℝ 2 g) (y a b : Space) :
    fderiv ℝ (fun z ↦ fderiv ℝ g z a) y b = fderiv ℝ (fderiv ℝ g) y b a := by
  have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (by norm_num)
  have hd : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) y) y :=
    (hg1.differentiable (by norm_num) y).hasFDerivAt
  have h := HasFDerivAt.clm_apply hd (hasFDerivAt_const a y)
  rw [h.fderiv]
  simp

/-- **At a local maximum of the circle integral, the Laplacian integrates to a
nonpositive number around the circle.** -/
theorem integral_laplacian_nonpos (hg : ContDiff ℝ 2 g) {x : Space}
    (hmax : IsLocalMax (circleInt g) x) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
      (∑ i : Fin 3, fderiv ℝ (fun y ↦ fderiv ℝ g y (e i)) (rot φ x) (e i)) ≤ 0 := by
  have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (by norm_num)
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ g)) := hg1.continuous_fderiv (by norm_num)
  have hpt : ∀ φ : ℝ, (∑ i : Fin 3, fderiv ℝ (fun y ↦ fderiv ℝ g y (e i)) (rot φ x) (e i)) =
      ∑ i : Fin 3, fderiv ℝ (fderiv ℝ g) (rot φ x) (rot φ (e i)) (rot φ (e i)) := by
    intro φ
    rw [sum_rot_basis (fderiv ℝ (fderiv ℝ g) (rot φ x)) φ]
    exact Finset.sum_congr rfl fun i _ ↦ fderiv_fderiv_apply_eq hg _ _ _
  simp only [hpt]
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin 3)), IntervalIntegrable
      (fun φ : ℝ ↦ fderiv ℝ (fderiv ℝ g) (rot φ x) (rot φ (e i)) (rot φ (e i))) volume 0
        (2 * Real.pi) := by
    intro i _
    have hc : Continuous (fun φ : ℝ ↦ fderiv ℝ (fderiv ℝ g) (rot φ x) (rot φ (e i)) (rot φ (e i))) := by
      fun_prop
    exact hc.intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hint]
  exact Finset.sum_nonpos fun i _ ↦ second_deriv_circleInt_nonpos hg hmax (e i)

end Laplacian

section Time

variable {u : ℝ × Space → Space}

theorem continuous_coord (i : Fin 3) : Continuous (fun v : Space ↦ v i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous

/-- The time derivative of the swirl, from the space-time derivative. -/
def dtSwirl (u : ℝ × Space → Space) (s : ℝ) (y : Space) : ℝ :=
  y 0 * (fderiv ℝ u (s, y) ((1 : ℝ), (0 : Space))) 1 - y 1 * (fderiv ℝ u (s, y) ((1 : ℝ), (0 : Space))) 0

theorem hasDerivAt_swirl_time (hu : ContDiff ℝ 1 u) (y : Space) (s : ℝ) :
    HasDerivAt (fun s ↦ swirlSlice (fun y ↦ u (s, y)) y) (dtSwirl u s y) s := by
  have hl : HasDerivAt (fun s : ℝ ↦ ((s, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) s :=
    HasDerivAt.prodMk (hasDerivAt_id s) (hasDerivAt_const s y)
  have hd : HasDerivAt (fun s ↦ u (s, y)) (fderiv ℝ u (s, y) ((1 : ℝ), (0 : Space))) s := by
    have h := HasFDerivAt.comp_hasDerivAt s ((hu.differentiable (by norm_num) (s, y)).hasFDerivAt) hl
    exact h
  have hc : ∀ j : Fin 3, HasDerivAt (fun s ↦ u (s, y) j)
      ((fderiv ℝ u (s, y) ((1 : ℝ), (0 : Space))) j) s :=
    fun j ↦ HasFDerivAt.comp_hasDerivAt s (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt hd
  exact HasDerivAt.sub (HasDerivAt.const_mul (y 0) (hc 1)) (HasDerivAt.const_mul (y 1) (hc 0))

/-- **The time derivative of the circle integral of the swirl.** -/
theorem hasDerivAt_circleInt_time (hu : ContDiff ℝ 1 u) (x : Space) (t : ℝ) :
    HasDerivAt (fun s ↦ circleInt (swirlSlice (fun y ↦ u (s, y))) x)
      (∫ φ in (0 : ℝ)..(2 * Real.pi), dtSwirl u t (rot φ x)) t := by
  have hcu : Continuous u := hu.continuous
  have hDu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have c0 := continuous_coord 0
  have c1 := continuous_coord 1
  refine hasDerivAt_intervalIntegral_of_continuous
    (F := fun s φ ↦ swirlSlice (fun y ↦ u (s, y)) (rot φ x))
    (F' := fun s φ ↦ dtSwirl u s (rot φ x)) (fun s ↦ ?_) ?_
    (fun s φ ↦ hasDerivAt_swirl_time hu _ s)
  · unfold swirlSlice
    fun_prop
  · unfold dtSwirl
    fun_prop

end Time

section Assembly

set_option maxHeartbeats 1000000 in
/-- **The averaged swirl can grow at its maxima only through the averaged
advection and torque.** For a space-time `C²` velocity, a pressure that is
`C¹` in space, a force continuous in space and a nonnegative viscosity, at
every spatial local maximum off the axis of the circle integral of the swirl,
`∂ₜ ∮Γ ≤ -∮ (u · ∇)Γ + ∮ (x₀ f₁ - x₁ f₀)`. -/
theorem deriv_circleInt_swirl_le {ν : ℝ} (hν : 0 ≤ ν) {u : ℝ × Space → Space}
    {p : ℝ × Space → ℝ} {f : ℝ × Space → Space} {t : ℝ} {x : Space} (hu : ContDiff ℝ 2 u)
    (hp : ContDiff ℝ 1 (fun y : Space ↦ p (t, y))) (hf : Continuous (fun y : Space ↦ f (t, y)))
    (hres : ∀ y, NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t y = f (t, y))
    (hmax : IsLocalMax (circleInt (swirlSlice (fun y ↦ u (t, y)))) x) (hr : x 0 ^ 2 + x 1 ^ 2 ≠ 0) :
    deriv (fun s ↦ circleInt (swirlSlice (fun y ↦ u (s, y))) x) t ≤
      -(∫ φ in (0 : ℝ)..(2 * Real.pi),
          fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) (rot φ x) (u (t, rot φ x))) +
        ∫ φ in (0 : ℝ)..(2 * Real.pi), torque f t (rot φ x) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hslice : ContDiff ℝ 2 (fun y : Space ↦ u (t, y)) := by
    have h := ContDiff.comp hu (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2
      (fun y : Space ↦ ((t, y) : ℝ × Space)))
    exact h
  have hΓ2 : ContDiff ℝ 2 (swirlSlice (fun y ↦ u (t, y))) := contDiff_swirlSlice hslice
  -- the swirl identity along the circle
  have hid : ∀ φ : ℝ, dtSwirl u t (rot φ x) +
      fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) (rot φ x) (u (t, rot φ x)) =
      ν * ((∑ i : Fin 3, fderiv ℝ (fun y ↦ fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) y (e i))
          (rot φ x) (e i)) - 2 * axialVorticity u t (rot φ x)) -
        angularDerivative p t (rot φ x) + torque f t (rot φ x) := by
    intro φ
    have hdiff : DifferentiableAt ℝ (fun s ↦ u (s, rot φ x)) t := by
      have h := ((hu1.differentiable (by norm_num)).comp
        (differentiable_id.prodMk (differentiable_const (rot φ x)))) t
      exact h
    have h := swirl_identity hslice.contDiffAt hdiff (hres (rot φ x))
    rw [(hasDerivAt_swirl_time hu1 (rot φ x) t).deriv] at h
    exact h
  -- continuity of each term along the circle
  have hDu : Continuous (fderiv ℝ u) := hu1.continuous_fderiv (by norm_num)
  have hΓ1 : Continuous (fderiv ℝ (swirlSlice (fun y ↦ u (t, y)))) :=
    hΓ2.continuous_fderiv (by norm_num)
  have hΓD : Continuous (fderiv ℝ (fderiv ℝ (swirlSlice (fun y ↦ u (t, y))))) :=
    (hΓ2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hsD : Continuous (fderiv ℝ (fun y : Space ↦ u (t, y))) := hslice.continuous_fderiv (by norm_num)
  have hpD : Continuous (fderiv ℝ (fun y : Space ↦ p (t, y))) := hp.continuous_fderiv (by norm_num)
  have hcu : Continuous u := hu1.continuous
  have c0 := continuous_coord 0
  have c1 := continuous_coord 1
  have iT : Continuous (fun φ : ℝ ↦ dtSwirl u t (rot φ x)) := by unfold dtSwirl; fun_prop
  have iA : Continuous (fun φ : ℝ ↦
      fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) (rot φ x) (u (t, rot φ x))) := by fun_prop
  have iL : Continuous (fun φ : ℝ ↦ ∑ i : Fin 3,
      fderiv ℝ (fun y ↦ fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) y (e i)) (rot φ x) (e i)) := by
    simp only [fderiv_fderiv_apply_eq hΓ2]
    fun_prop
  have iW : Continuous (fun φ : ℝ ↦ axialVorticity u t (rot φ x)) := by
    unfold axialVorticity spatialDerivative
    fun_prop
  have iP : Continuous (fun φ : ℝ ↦ angularDerivative p t (rot φ x)) := by
    unfold angularDerivative
    fun_prop
  have iF : Continuous (fun φ : ℝ ↦ torque f t (rot φ x)) := by
    have hrc : Continuous (fun φ : ℝ ↦ rot φ x) := by fun_prop
    have hfr : Continuous (fun φ : ℝ ↦ f (t, rot φ x)) := by
      have h := Continuous.comp hf hrc
      exact h
    have hf0 : Continuous (fun φ : ℝ ↦ f (t, rot φ x) 0) := by
      have h := Continuous.comp c0 hfr
      exact h
    have hf1 : Continuous (fun φ : ℝ ↦ f (t, rot φ x) 1) := by
      have h := Continuous.comp c1 hfr
      exact h
    have hr0 : Continuous (fun φ : ℝ ↦ (rot φ x) 0) := by
      have h := Continuous.comp c0 hrc
      exact h
    have hr1 : Continuous (fun φ : ℝ ↦ (rot φ x) 1) := by
      have h := Continuous.comp c1 hrc
      exact h
    unfold torque
    exact (hr0.mul hf1).sub (hr1.mul hf0)
  -- integrate the identity
  set T : ℝ → ℝ := fun φ ↦ dtSwirl u t (rot φ x) with hT
  set A : ℝ → ℝ := fun φ ↦ fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) (rot φ x) (u (t, rot φ x)) with hA
  set L : ℝ → ℝ := fun φ ↦ ∑ i : Fin 3,
    fderiv ℝ (fun y ↦ fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) y (e i)) (rot φ x) (e i) with hLdef
  set W : ℝ → ℝ := fun φ ↦ axialVorticity u t (rot φ x) with hWdef
  set P : ℝ → ℝ := fun φ ↦ angularDerivative p t (rot φ x) with hPdef
  set F : ℝ → ℝ := fun φ ↦ torque f t (rot φ x) with hFdef
  have hpt : ∀ φ, T φ = ν * (L φ - 2 * W φ) - P φ + F φ - A φ := fun φ ↦ by
    have := hid φ
    simp only [hT, hA, hLdef, hWdef, hPdef, hFdef]
    linarith
  have c1 : Continuous (fun φ ↦ ν * (L φ - 2 * W φ) - P φ + F φ) :=
    ((continuous_const.mul (iL.sub (continuous_const.mul iW))).sub iP).add iF
  have c2 : Continuous (fun φ ↦ ν * (L φ - 2 * W φ) - P φ) :=
    (continuous_const.mul (iL.sub (continuous_const.mul iW))).sub iP
  have c3 : Continuous (fun φ ↦ ν * (L φ - 2 * W φ)) :=
    continuous_const.mul (iL.sub (continuous_const.mul iW))
  have c4 : Continuous (fun φ ↦ 2 * W φ) := continuous_const.mul iW
  have hsum : ∫ φ in (0 : ℝ)..(2 * Real.pi), T φ =
      ν * ((∫ φ in (0 : ℝ)..(2 * Real.pi), L φ) - 2 * ∫ φ in (0 : ℝ)..(2 * Real.pi), W φ) -
        (∫ φ in (0 : ℝ)..(2 * Real.pi), P φ) + (∫ φ in (0 : ℝ)..(2 * Real.pi), F φ) -
          ∫ φ in (0 : ℝ)..(2 * Real.pi), A φ := by
    rw [intervalIntegral.integral_congr (fun φ _ ↦ hpt φ),
      intervalIntegral.integral_sub (c1.intervalIntegrable _ _) (iA.intervalIntegrable _ _),
      intervalIntegral.integral_add (c2.intervalIntegrable _ _) (iF.intervalIntegrable _ _),
      intervalIntegral.integral_sub (c3.intervalIntegrable _ _) (iP.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (iL.intervalIntegrable _ _) (c4.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul]
  -- the three averaged facts
  have hW : ∫ φ in (0 : ℝ)..(2 * Real.pi), W φ = 0 := by
    have h := integral_axialVorticity_eq_zero hslice hmax hr
    simpa [hWdef, axialVorticity, spatialDerivative] using h
  have hP : ∫ φ in (0 : ℝ)..(2 * Real.pi), P φ = 0 := integral_angularDerivative_rot hp x
  have hL : ∫ φ in (0 : ℝ)..(2 * Real.pi), L φ ≤ 0 := integral_laplacian_nonpos hΓ2 hmax
  rw [(hasDerivAt_circleInt_time hu1 x t).deriv]
  change ∫ φ in (0 : ℝ)..(2 * Real.pi), T φ ≤ -(∫ φ in (0 : ℝ)..(2 * Real.pi), A φ) +
    ∫ φ in (0 : ℝ)..(2 * Real.pi), F φ
  rw [hsum, hW, hP]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hν hL]

end Assembly

section Budget

theorem continuous_circleInt_swirl {u : ℝ × Space → Space} (hu : Continuous u) :
    Continuous (fun z : ℝ × Space ↦ circleInt (swirlSlice (fun y ↦ u (z.1, y))) z.2) := by
  have c0 := continuous_coord 0
  have c1 := continuous_coord 1
  have h : Continuous (Function.uncurry (fun (z : ℝ × Space) (φ : ℝ) ↦
      swirlSlice (fun y ↦ u (z.1, y)) (rot φ z.2))) := by
    unfold swirlSlice Function.uncurry
    fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h 0 (2 * Real.pi)

theorem circleInt_swirl_axis {U : Space → Space} {x : Space} (h0 : x 0 = 0) (h1 : x 1 = 0) :
    circleInt (swirlSlice U) x = 0 := by
  unfold circleInt swirlSlice
  have : ∀ φ : ℝ, (rot φ x) 0 = 0 ∧ (rot φ x) 1 = 0 := fun φ ↦ by simp [rot, h0, h1]
  simp [this]

set_option maxHeartbeats 1000000 in
/-- **The swirl budget.** Let the velocity be space-time `C²`, the pressure `C¹`
and the force continuous in space, with Navier–Stokes residual equal to the
force on `(0, T]`, and let the circle integral of the swirl be nonpositive
outside a compact set. If at every spatial local maximum of the circle
integral of the swirl the averaged advection and torque are at most `g(t)`,
for a continuous `g ≥ 0`, then the circle integral of the swirl never exceeds
its initial maximum `M₀ ≥ 0` plus `∫₀ᵗ g`. -/
theorem circleInt_swirl_le_budget {ν : ℝ} (hν : 0 ≤ ν) {u : ℝ × Space → Space}
    {p : ℝ × Space → ℝ} {f : ℝ × Space → Space} {T M₀ : ℝ} {K : Set Space} (hK : IsCompact K)
    (hM₀ : 0 ≤ M₀) {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t) (hu : ContDiff ℝ 2 u)
    (hp : ∀ t, ContDiff ℝ 1 (fun y : Space ↦ p (t, y)))
    (hf : ∀ t, Continuous (fun y : Space ↦ f (t, y)))
    (hres : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ y,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t y = f (t, y))
    (hout : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∉ K, circleInt (swirlSlice (fun y ↦ u (t, y))) x ≤ 0)
    (hinit : ∀ x, circleInt (swirlSlice (fun y ↦ u (0, y))) x ≤ M₀)
    (hbudget : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x, IsLocalMax (circleInt (swirlSlice (fun y ↦ u (t, y)))) x →
      -(∫ φ in (0 : ℝ)..(2 * Real.pi),
          fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) (rot φ x) (u (t, rot φ x))) +
        ∫ φ in (0 : ℝ)..(2 * Real.pi), torque f t (rot φ x) ≤ g t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      circleInt (swirlSlice (fun y ↦ u (t, y))) x ≤ M₀ + ∫ s in (0 : ℝ)..t, g s := by
  intro t ht x
  by_contra hlt
  push Not at hlt
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  set Γb : ℝ × Space → ℝ := fun z ↦ circleInt (swirlSlice (fun y ↦ u (z.1, y))) z.2 with hΓb
  set I : ℝ → ℝ := fun s ↦ ∫ r in (0 : ℝ)..s, g r with hI
  have hIc : Continuous I := intervalIntegral.continuous_primitive (fun a b ↦ hg.intervalIntegrable a b) 0
  have hI0 : I 0 = 0 := by simp [hI]
  have hInn : ∀ s, 0 ≤ s → 0 ≤ I s := fun s hs ↦
    intervalIntegral.integral_nonneg hs fun r _ ↦ hg0 r
  have hΓc : Continuous Γb := continuous_circleInt_swirl hu1.continuous
  -- the tilt
  set ex : ℝ := Γb (t, x) - M₀ - I t with hex
  have hex0 : 0 < ex := by
    have : Γb (t, x) = circleInt (swirlSlice (fun y ↦ u (t, y))) x := rfl
    linarith [hex]
  set ε : ℝ := ex / (2 * (T + 1)) with hε
  have hε0 : 0 < ε := div_pos hex0 (by linarith)
  set G : ℝ × Space → ℝ := fun z ↦ Γb z - I z.1 - ε * z.1 with hG
  have hGc : Continuous G := (hΓc.sub (hIc.comp continuous_fst)).sub (continuous_const.mul continuous_fst)
  have hGtx : M₀ < G (t, x) := by
    have h1 : ε * t ≤ ex / 2 := by
      rw [hε, div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith [ht.1, ht.2]
    show M₀ < Γb (t, x) - I t - ε * t
    linarith
  have hxK : x ∈ K := by
    by_contra hx
    have h1 := hout t ht x hx
    have h2 := hInn t ht.1
    have : Γb (t, x) = circleInt (swirlSlice (fun y ↦ u (t, y))) x := rfl
    linarith
  -- a maximum of the tilted average on the compact region
  have hcpt : IsCompact (Set.Icc (0 : ℝ) T ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨z, hz, hmax⟩ := hcpt.exists_isMaxOn ⟨(t, x), ⟨ht, hxK⟩⟩ hGc.continuousOn
  obtain ⟨ts, xs⟩ := z
  have hts : ts ∈ Set.Icc (0 : ℝ) T := hz.1
  have hxs : xs ∈ K := hz.2
  have hGz : M₀ < G (ts, xs) :=
    lt_of_lt_of_le hGtx (hmax (show ((t, x) : ℝ × Space) ∈ Set.Icc (0 : ℝ) T ×ˢ K from ⟨ht, hxK⟩))
  have hts0 : 0 < ts := by
    rcases eq_or_lt_of_le hts.1 with h | h
    · exfalso
      have h1 : G (ts, xs) = circleInt (swirlSlice (fun y ↦ u (0, y))) xs := by
        simp only [hG, hΓb, ← h, hI0, mul_zero, sub_zero]
      have := hinit xs
      linarith
    · exact h
  have hts' : ts ∈ Set.Ioc (0 : ℝ) T := ⟨hts0, hts.2⟩
  have hGs : G (ts, xs) = Γb (ts, xs) - I ts - ε * ts := rfl
  have hΓpos : 0 < Γb (ts, xs) := by
    have := hInn ts hts.1
    nlinarith
  -- off the axis
  have hr : xs 0 ^ 2 + xs 1 ^ 2 ≠ 0 := by
    intro h
    have h0 : xs 0 = 0 := by nlinarith [sq_nonneg (xs 0), sq_nonneg (xs 1)]
    have h1 : xs 1 = 0 := by nlinarith [sq_nonneg (xs 0), sq_nonneg (xs 1)]
    have : Γb (ts, xs) = 0 := circleInt_swirl_axis h0 h1
    linarith
  -- a spatial maximum
  have hsmax : IsLocalMax (circleInt (swirlSlice (fun y ↦ u (ts, y)))) xs := by
    refine IsMaxOn.isLocalMax (s := Set.univ) (fun y _ ↦ ?_) Filter.univ_mem
    show circleInt (swirlSlice (fun y ↦ u (ts, y))) y ≤ Γb (ts, xs)
    by_cases hy : y ∈ K
    · have := hmax (show ((ts, y) : ℝ × Space) ∈ Set.Icc (0 : ℝ) T ×ˢ K from ⟨hts, hy⟩)
      simp only [Set.mem_ofPred_eq] at this
      have e : G (ts, y) = circleInt (swirlSlice (fun y ↦ u (ts, y))) y - I ts - ε * ts := rfl
      linarith
    · have := hout ts hts y hy
      linarith
  -- the budget at the maximum
  have hcore := (deriv_circleInt_swirl_le hν hu (hp ts) (hf ts) (hres ts hts') hsmax hr).trans
    (hbudget ts hts' xs hsmax)
  -- the left slopes of `Γb(·, xs) - I` are at least `ε`
  have hΓd := hasDerivAt_circleInt_time hu1 xs ts
  have hId : HasDerivAt I (g ts) ts :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
  have hhd := HasDerivAt.sub hΓd hId
  have hlim := HasDerivAt.tendsto_slope_zero_left hhd
  have hev : ∀ᶠ h in 𝓝[<] (0 : ℝ), ε ≤ h⁻¹ •
      ((circleInt (swirlSlice (fun y ↦ u (ts + h, y))) xs - I (ts + h)) -
        (circleInt (swirlSlice (fun y ↦ u (ts, y))) xs - I ts)) := by
    have hmem : Set.Ioo (-ts) 0 ∈ 𝓝[<] (0 : ℝ) := Ioo_mem_nhdsLT (by linarith)
    filter_upwards [hmem] with h hh
    have hsIcc : ts + h ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hh.1], by linarith [hh.2, hts.2]⟩
    have hle := hmax (show ((ts + h, xs) : ℝ × Space) ∈ Set.Icc (0 : ℝ) T ×ˢ K from ⟨hsIcc, hxs⟩)
    simp only [Set.mem_ofPred_eq] at hle
    have e1 : G (ts + h, xs) = circleInt (swirlSlice (fun y ↦ u (ts + h, y))) xs - I (ts + h) -
        ε * (ts + h) := rfl
    have e2 : G (ts, xs) = circleInt (swirlSlice (fun y ↦ u (ts, y))) xs - I ts - ε * ts := rfl
    rw [smul_eq_mul, ← div_eq_inv_mul, le_div_iff_of_neg hh.2]
    linarith
  have hge := ge_of_tendsto hlim hev
  rw [← hΓd.deriv] at hge
  linarith

end Budget

section Fluctuation

theorem rot_rot (φ ψ : ℝ) (x : Space) : rot φ (rot ψ x) = rot (φ + ψ) x := by
  ext i
  fin_cases i <;> simp [rot, Real.cos_add, Real.sin_add] <;> ring

theorem rot_add_two_pi (φ : ℝ) (x : Space) : rot (φ + 2 * Real.pi) x = rot φ x := by
  ext i
  fin_cases i <;> simp [rot]

/-- Rotation about the third axis as a continuous linear map. -/
def rotCLM (φ : ℝ) : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := rot φ
      map_add' := rot_add φ
      map_smul' := fun c y ↦ rot_smul φ c y }

theorem rotCLM_apply (φ : ℝ) (y : Space) : rotCLM φ y = rot φ y := rfl

/-- The mean velocity: the rotation-equivariant average of a velocity over the
circles about the third axis. -/
def meanVel (U : Space → Space) (x : Space) : Space :=
  (2 * Real.pi)⁻¹ • ∫ ψ in (0 : ℝ)..(2 * Real.pi), rot (-ψ) (U (rot ψ x))

/-- **The mean velocity commutes with the rotations.** -/
theorem meanVel_rot {U : Space → Space} (hU : Continuous U) (φ : ℝ) (x : Space) :
    meanVel U (rot φ x) = rot φ (meanVel U x) := by
  set h : ℝ → Space := fun ψ ↦ rot (-ψ) (U (rot ψ x)) with hh
  have hc : Continuous h := by
    have h1 : Continuous (fun ψ : ℝ ↦ U (rot ψ x)) := by
      have := Continuous.comp hU (show Continuous (fun ψ : ℝ ↦ rot ψ x) by fun_prop)
      exact this
    have := Continuous.comp continuous_rot (Continuous.prodMk continuous_neg h1)
    exact this
  have hper : Function.Periodic h (2 * Real.pi) := by
    intro ψ
    simp only [hh]
    rw [rot_add_two_pi, show -(ψ + 2 * Real.pi) = -ψ - 2 * Real.pi by ring]
    have e : rot (-ψ - 2 * Real.pi) = rot (-ψ) := by
      funext v
      rw [← rot_add_two_pi (-ψ - 2 * Real.pi) v]
      ring_nf
    rw [e]
  have hpt : ∀ ψ : ℝ, rot (-ψ) (U (rot ψ (rot φ x))) = rotCLM φ (h (ψ + φ)) := by
    intro ψ
    rw [rotCLM_apply, hh]
    simp only
    rw [rot_rot, rot_rot, show φ + -(ψ + φ) = -ψ by ring, show ψ + φ = ψ + φ from rfl,
      add_comm ψ φ]
  have hint : ∫ ψ in (0 : ℝ)..(2 * Real.pi), rot (-ψ) (U (rot ψ (rot φ x))) =
      rot φ (∫ ψ in (0 : ℝ)..(2 * Real.pi), h ψ) := by
    simp only [hpt]
    have hi : IntervalIntegrable (fun ψ : ℝ ↦ h (ψ + φ)) MeasureTheory.volume 0 (2 * Real.pi) := by
      have hc' : Continuous (fun ψ : ℝ ↦ h (ψ + φ)) := by
        have := Continuous.comp hc (continuous_add_const φ)
        exact this
      exact hc'.intervalIntegrable _ _
    rw [ContinuousLinearMap.intervalIntegral_comp_comm (rotCLM φ) hi,
      intervalIntegral.integral_comp_add_right, rotCLM_apply]
    congr 1
    have := Function.Periodic.intervalIntegral_add_eq hper φ 0
    rw [zero_add, add_comm φ (2 * Real.pi)] at this
    rw [zero_add]
    exact this
  unfold meanVel
  rw [hint, rot_smul]

/-- **At a local maximum of the circle integral, the mean velocity carries no
net swirl into the maximum.** -/
theorem integral_fderiv_meanVel_eq_zero {g : Space → ℝ} (hg : ContDiff ℝ 1 g)
    {U : Space → Space} (hU : Continuous U) {x : Space} (hmax : IsLocalMax (circleInt g) x) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), fderiv ℝ g (rot φ x) (meanVel U (rot φ x)) = 0 := by
  set w := meanVel U x with hw
  have e : ∀ φ : ℝ, fderiv ℝ g (rot φ x) (meanVel U (rot φ x)) =
      fderiv ℝ g (rot φ (x + (0 : ℝ) • w)) (rot φ w) := by
    intro φ
    rw [meanVel_rot hU, zero_smul, add_zero]
  simp only [e]
  have hline := hasDerivAt_circleInt_line hg x w 0
  have hlmax : IsLocalMax (fun s : ℝ ↦ circleInt g (x + s • w)) 0 := by
    have hx0 : (fun s : ℝ ↦ x + s • w) 0 = x := by simp
    have h1 : IsLocalMax (circleInt g) ((fun s : ℝ ↦ x + s • w) 0) := by
      rw [hx0]
      exact hmax
    have h2 := IsLocalMax.comp_continuous (g := fun s : ℝ ↦ x + s • w) (b := 0) h1
      (hasDerivAt_line x w 0).continuousAt
    exact h2
  exact hline.deriv.symm.trans (IsLocalMax.deriv_eq_zero hlmax)

set_option maxHeartbeats 1000000 in
/-- **Only the fluctuation carries swirl into the maximum.** Under the
hypotheses of `deriv_circleInt_swirl_le`, with `U' = u - ū` the deviation of the
velocity from its rotation-equivariant average,
`∂ₜ ∮Γ ≤ -∮ (U' · ∇)Γ + ∮ (x₀ f₁ - x₁ f₀)` at every spatial local maximum off
the axis. For an axisymmetric velocity `U' = 0`. -/
theorem deriv_circleInt_swirl_le_fluct {ν : ℝ} (hν : 0 ≤ ν) {u : ℝ × Space → Space}
    {p : ℝ × Space → ℝ} {f : ℝ × Space → Space} {t : ℝ} {x : Space} (hu : ContDiff ℝ 2 u)
    (hp : ContDiff ℝ 1 (fun y : Space ↦ p (t, y))) (hf : Continuous (fun y : Space ↦ f (t, y)))
    (hres : ∀ y, NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t y = f (t, y))
    (hmax : IsLocalMax (circleInt (swirlSlice (fun y ↦ u (t, y)))) x) (hr : x 0 ^ 2 + x 1 ^ 2 ≠ 0) :
    deriv (fun s ↦ circleInt (swirlSlice (fun y ↦ u (s, y))) x) t ≤
      -(∫ φ in (0 : ℝ)..(2 * Real.pi), fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) (rot φ x)
          (u (t, rot φ x) - meanVel (fun y ↦ u (t, y)) (rot φ x))) +
        ∫ φ in (0 : ℝ)..(2 * Real.pi), torque f t (rot φ x) := by
  have hbase := deriv_circleInt_swirl_le hν hu hp hf hres hmax hr
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hslice : ContDiff ℝ 1 (fun y : Space ↦ u (t, y)) := by
    have h := ContDiff.comp hu1 (contDiff_const.prodMk contDiff_id : ContDiff ℝ 1
      (fun y : Space ↦ ((t, y) : ℝ × Space)))
    exact h
  have hΓ1 : ContDiff ℝ 1 (swirlSlice (fun y ↦ u (t, y))) := contDiff_swirlSlice hslice
  have hDΓ : Continuous (fderiv ℝ (swirlSlice (fun y ↦ u (t, y)))) :=
    hΓ1.continuous_fderiv (by norm_num)
  have hcu : Continuous (fun y : Space ↦ u (t, y)) := hslice.continuous
  have hmean := integral_fderiv_meanVel_eq_zero hΓ1 hcu hmax
  set w := meanVel (fun y ↦ u (t, y)) x with hw
  have hA : Continuous (fun φ : ℝ ↦
      fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) (rot φ x) (u (t, rot φ x))) := by
    have h1 : Continuous (fun φ : ℝ ↦ u (t, rot φ x)) := by
      have := Continuous.comp hcu (show Continuous (fun φ : ℝ ↦ rot φ x) by fun_prop)
      exact this
    fun_prop
  have hM : Continuous (fun φ : ℝ ↦ fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) (rot φ x)
      (meanVel (fun y ↦ u (t, y)) (rot φ x))) := by
    have e : (fun φ : ℝ ↦ fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) (rot φ x)
        (meanVel (fun y ↦ u (t, y)) (rot φ x))) =
        fun φ ↦ fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) (rot φ x) (rot φ w) :=
      funext fun φ ↦ by rw [meanVel_rot hcu]
    rw [e]
    fun_prop
  have hsplit : ∫ φ in (0 : ℝ)..(2 * Real.pi), fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) (rot φ x)
      (u (t, rot φ x) - meanVel (fun y ↦ u (t, y)) (rot φ x)) =
      ∫ φ in (0 : ℝ)..(2 * Real.pi), fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) (rot φ x)
        (u (t, rot φ x)) := by
    simp only [map_sub]
    rw [intervalIntegral.integral_sub (hA.intervalIntegrable _ _) (hM.intervalIntegrable _ _),
      hmean, sub_zero]
  rw [hsplit]
  exact hbase

end Fluctuation

end Mettapedia.FluidDynamics.NavierStokes.AveragedSwirl
