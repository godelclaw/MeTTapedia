import MettapediaNS.AveragedSwirl

/-!
# Circulation as vortex flux, and the eddy vortex flux that must feed its peak

The circle integral of the swirl `Γ = x₀ u₁ - x₁ u₀` about the third axis is
the circulation of the velocity around that circle. By Stokes' theorem it is
the flux of axial vorticity through the disk the circle bounds. In polar
coordinates, with `r` the radius of the circle and `ω₃ = ∂₀u₁ - ∂₁u₀`,

```text
∮ Γ = ∫₀¹ s r² (∮ ω₃ over the circle of radius s r) ds
```

(`circleInt_swirl_eq_flux`), which is `∫_disk ω₃` in the variable `ρ = s r`.

The advection of the swirl by a velocity `U` is the swirl of `(U · ∇)U`, and
`(U · ∇)U = ∇(|U|²/2) - U × ω`. The swirl of a gradient is an angular
derivative, which integrates to zero around the circle, so

```text
-∮ (U · ∇)Γ = ∮ Γ(U × ω),    Γ(U × ω) = r (U × ω)_θ = r (U_z ω_r - U_r ω_z),
```

the rate at which `U` sweeps vortex lines across the circle
(`circleInt_advection_eq_vortexForce`). At a maximum of the averaged swirl the
torque is carried by the fluctuation `u' = u - ū` alone, so

```text
∂ₜ ∮Γ ≤ ∮ Γ(u' × ω') + ∮ (x₀ f₁ - x₁ f₀),    ω' = curl u'
```

(`deriv_circleInt_swirl_le_eddyFlux`). The largest vortex flux through a disk
about the axis grows only as fast as the fluctuation velocity carries
fluctuation vorticity across the disk's rim, plus the torque of the force.
The axisymmetric part of the flow, however intense, cannot raise it.
-/

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.CirculationFlux

open Set Filter Topology MeasureTheory
open _root_.NavierStokes.ProblemStatement
open Mettapedia.FluidDynamics.NavierStokes.SwirlBudget
open Mettapedia.FluidDynamics.NavierStokes.AveragedSwirl

section Flux

variable {U : Space → Space}

/-- The axial part `(0, 0, x₂)`. -/
def vert (x : Space) : Space := !₂[0, 0, x 2]

theorem rot_vert (φ : ℝ) (x : Space) : rot φ (vert x) = vert x := by
  ext i
  fin_cases i <;> simp [rot, vert]

theorem vert_add_horiz (x : Space) : vert x + horiz x = x := by
  ext i
  fin_cases i <;> simp [vert, horiz]

theorem horiz_ray (s : ℝ) (x y : Space) : horiz (vert x + s • horiz y) = s • horiz y := by
  ext i
  fin_cases i <;> simp [vert, horiz]

theorem rot_ray (φ s : ℝ) (x : Space) :
    rot φ (vert x + s • horiz x) = vert x + s • horiz (rot φ x) := by
  rw [rot_line, rot_vert, rot_horiz]

/-- The axial vorticity `∂₀U₁ - ∂₁U₀` of a velocity slice. -/
def axialVort (U : Space → Space) (y : Space) : ℝ :=
  (fderiv ℝ U y (e 0)) 1 - (fderiv ℝ U y (e 1)) 0

/-- The radial derivative of the swirl at a point of the ray from the axis through `x`, at
the fraction `s ≠ 0` of the radius. -/
theorem fderiv_swirl_ray (hU : Differentiable ℝ U) {s : ℝ} (hs : s ≠ 0) (φ : ℝ) (x : Space) :
    fderiv ℝ (swirlSlice U) (rot φ (vert x + s • horiz x)) (rot φ (horiz x)) =
      s * (x 0 ^ 2 + x 1 ^ 2) * axialVort U (rot φ (vert x + s • horiz x)) +
        s⁻¹ * angularDeriv (radialSlice U) (rot φ (vert x + s • horiz x)) := by
  set z := rot φ (vert x + s • horiz x) with hz
  have hz' : z = vert x + s • horiz (rot φ x) := rot_ray φ s x
  have hh : horiz z = s • rot φ (horiz x) := by
    rw [hz', horiz_ray, rot_horiz]
  have hc : z 0 = s * (rot φ x) 0 ∧ z 1 = s * (rot φ x) 1 := by
    rw [hz']
    simp [vert, horiz]
  have hn : z 0 ^ 2 + z 1 ^ 2 = s ^ 2 * (x 0 ^ 2 + x 1 ^ 2) := by
    rw [hc.1, hc.2, ← normSq_rot φ x]
    ring
  have key := fderiv_swirl_horiz (U := U) (hU z)
  rw [hh, map_smul, smul_eq_mul, hn] at key
  have hD : fderiv ℝ (swirlSlice U) z (rot φ (horiz x)) =
      s⁻¹ * (s * fderiv ℝ (swirlSlice U) z (rot φ (horiz x))) := by
    field_simp
  rw [hD, key]
  unfold axialVort
  field_simp

theorem continuous_axialVort_ray (hU : ContDiff ℝ 1 U) (x : Space) :
    Continuous (Function.uncurry
      (fun (s φ : ℝ) ↦ axialVort U (rot φ (vert x + s • horiz x)))) := by
  have hDc : Continuous (fderiv ℝ U) := hU.continuous_fderiv (by norm_num)
  have h0 : Continuous (fun q : ℝ × ℝ ↦ (fderiv ℝ U (rot q.2 (vert x + q.1 • horiz x)) (e 0)) 1) :=
    (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).continuous.comp (by fun_prop)
  have h1 : Continuous (fun q : ℝ × ℝ ↦ (fderiv ℝ U (rot q.2 (vert x + q.1 • horiz x)) (e 1)) 0) :=
    (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).continuous.comp (by fun_prop)
  exact h0.sub h1

/-- **The derivative of the circulation along the ray.** -/
theorem hasDerivAt_circleInt_ray (hU : ContDiff ℝ 1 U) (x : Space) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun s ↦ circleInt (swirlSlice U) (vert x + s • horiz x))
      (s * (x 0 ^ 2 + x 1 ^ 2) *
        ∫ φ in (0 : ℝ)..(2 * Real.pi), axialVort U (rot φ (vert x + s • horiz x))) s := by
  have hΓ1 : ContDiff ℝ 1 (swirlSlice U) := contDiff_swirlSlice hU
  have hUd : Differentiable ℝ U := hU.differentiable (by norm_num)
  have h := hasDerivAt_circleInt_line hΓ1 (vert x) (horiz x) s
  have hW : Continuous (fun φ : ℝ ↦ axialVort U (rot φ (vert x + s • horiz x))) := by
    have h' := (continuous_axialVort_ray hU x).comp
      (Continuous.prodMk continuous_const continuous_id : Continuous (fun φ : ℝ ↦ (s, φ)))
    exact h'
  have hA : Continuous (fun φ : ℝ ↦ angularDeriv (radialSlice U) (rot φ (vert x + s • horiz x))) := by
    have hRc : Continuous (fderiv ℝ (radialSlice U)) :=
      (contDiff_radialSlice hU).continuous_fderiv (by norm_num)
    have hang' : Continuous angular := by
      have e' : angular = fun y : Space ↦ y 0 • e 1 - y 1 • e 0 := funext angular_eq
      rw [e']
      fun_prop
    unfold angularDeriv
    fun_prop
  convert h using 1
  simp only [fderiv_swirl_ray hUd hs]
  rw [intervalIntegral.integral_add ((hW.const_mul _).intervalIntegrable _ _)
      ((hA.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_angularDeriv_rot (contDiff_radialSlice hU),
    mul_zero, add_zero]

/-- **Stokes' theorem for the swirl: the circulation is the axial vortex flux
through the disk.** In the variable `ρ = s r` the right side is
`∫₀^r ∫₀^{2π} ω₃ ρ dφ dρ`, the flux of axial vorticity through the disk of radius
`r = √(x₀² + x₁²)` at height `x₂`. -/
theorem circleInt_swirl_eq_flux (hU : ContDiff ℝ 1 U) (x : Space) :
    circleInt (swirlSlice U) x =
      ∫ s in (0 : ℝ)..1, s * (x 0 ^ 2 + x 1 ^ 2) *
        ∫ φ in (0 : ℝ)..(2 * Real.pi), axialVort U (rot φ (vert x + s • horiz x)) := by
  set F : ℝ → ℝ := fun s ↦ circleInt (swirlSlice U) (vert x + s • horiz x) with hF
  have hF1 : F 1 = circleInt (swirlSlice U) x := by
    simp only [hF, one_smul, vert_add_horiz]
  have hF0 : F 0 = 0 := by
    simp only [hF, zero_smul, add_zero]
    exact circleInt_swirl_axis (by simp [vert]) (by simp [vert])
  have hΓ1 : ContDiff ℝ 1 (swirlSlice U) := contDiff_swirlSlice hU
  have hcont : Continuous F := continuous_iff_continuousAt.mpr fun s ↦
    (hasDerivAt_circleInt_line hΓ1 (vert x) (horiz x) s).continuousAt
  have hint : IntervalIntegrable (fun s : ℝ ↦ s * (x 0 ^ 2 + x 1 ^ 2) *
      ∫ φ in (0 : ℝ)..(2 * Real.pi), axialVort U (rot φ (vert x + s • horiz x))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (continuous_axialVort_ray hU x) 0 (2 * Real.pi)
    exact (continuous_id.mul continuous_const).mul hc
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one hcont.continuousOn
    (fun s hs ↦ (hasDerivAt_circleInt_ray hU x (ne_of_gt hs.1)).hasDerivWithinAt) hint
  rw [h, hF0, sub_zero, hF1]

end Flux

section Mean

variable {U : Space → Space}

/-- The swirl `y₀ v₁ - y₁ v₀` of a vector `v` at the point `y`, as a linear map. -/
def swirlCLM (y : Space) : Space →L[ℝ] ℝ :=
  y 0 • (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ) - y 1 • (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ)

theorem swirlCLM_apply (y v : Space) : swirlCLM y v = y 0 * v 1 - y 1 * v 0 := by
  simp [swirlCLM]

/-- The swirl is unchanged by rotating the point forward and the vector back. -/
theorem swirl_rot (φ : ℝ) (y v : Space) :
    y 0 * (rot (-φ) v) 1 - y 1 * (rot (-φ) v) 0 = (rot φ y) 0 * v 1 - (rot φ y) 1 * v 0 := by
  simp [rot, Real.cos_neg, Real.sin_neg]
  ring

/-- **The swirl of the mean velocity is the averaged swirl.** -/
theorem swirlSlice_meanVel (hU : Continuous U) (y : Space) :
    swirlSlice (meanVel U) y = (2 * Real.pi)⁻¹ * circleInt (swirlSlice U) y := by
  have hc : Continuous (fun ψ : ℝ ↦ rot (-ψ) (U (rot ψ y))) := by
    have h1 : Continuous (fun ψ : ℝ ↦ U (rot ψ y)) := by
      have := Continuous.comp hU (show Continuous (fun ψ : ℝ ↦ rot ψ y) by fun_prop)
      exact this
    have := Continuous.comp continuous_rot (Continuous.prodMk continuous_neg h1)
    exact this
  have e1 : swirlSlice (meanVel U) y = swirlCLM y (meanVel U y) := by
    rw [swirlCLM_apply]
    rfl
  rw [e1]
  unfold meanVel
  rw [map_smul, smul_eq_mul,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hc.intervalIntegrable _ _)]
  congr 1
  unfold circleInt
  congr 1
  funext ψ
  rw [swirlCLM_apply, swirl_rot]
  rfl

/-- **The mean velocity is differentiable.** -/
theorem hasFDerivAt_meanVel (hU : ContDiff ℝ 1 U) (y₀ : Space) :
    HasFDerivAt (meanVel U)
      ((2 * Real.pi)⁻¹ • ∫ ψ in (0 : ℝ)..(2 * Real.pi),
        (rotCLM (-ψ)).comp ((fderiv ℝ U (rot ψ y₀)).comp (rotCLM ψ))) y₀ := by
  have hUd : ∀ y, HasFDerivAt U (fderiv ℝ U y) y :=
    fun y ↦ (hU.differentiable (by norm_num) y).hasFDerivAt
  have hDU : Continuous (fderiv ℝ U) := hU.continuous_fderiv (by norm_num)
  have hcU : Continuous U := hU.continuous
  have hF'c : Continuous (fun z : Space × ℝ ↦
      (rotCLM (-z.2)).comp ((fderiv ℝ U (rot z.2 z.1)).comp (rotCLM z.2))) := by
    refine continuous_clm_apply.mpr fun v ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, rotCLM_apply]
    fun_prop
  have hK : IsCompact (Metric.closedBall y₀ 1 ×ˢ uIcc (0 : ℝ) (2 * Real.pi)) :=
    (isCompact_closedBall y₀ 1).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'c.continuousOn
  have hFc : ∀ y, Continuous (fun ψ : ℝ ↦ rot (-ψ) (U (rot ψ y))) := fun y ↦ by
    have h1 : Continuous (fun ψ : ℝ ↦ U (rot ψ y)) := by
      have := Continuous.comp hcU (show Continuous (fun ψ : ℝ ↦ rot ψ y) by fun_prop)
      exact this
    have := Continuous.comp continuous_rot (Continuous.prodMk continuous_neg h1)
    exact this
  have hF'1 : Continuous (fun ψ : ℝ ↦
      (rotCLM (-ψ)).comp ((fderiv ℝ U (rot ψ y₀)).comp (rotCLM ψ))) := by
    have hl : Continuous (fun ψ : ℝ ↦ ((y₀, ψ) : Space × ℝ)) :=
      Continuous.prodMk continuous_const continuous_id
    have := Continuous.comp hF'c hl
    exact this
  have h := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y ψ ↦ rot (-ψ) (U (rot ψ y)))
    (F' := fun y ψ ↦ (rotCLM (-ψ)).comp ((fderiv ℝ U (rot ψ y)).comp (rotCLM ψ)))
    (bound := fun _ ↦ C) (μ := MeasureTheory.volume) (a := 0) (b := 2 * Real.pi)
    (Metric.closedBall_mem_nhds y₀ one_pos)
    (Eventually.of_forall fun y ↦ (hFc y).aestronglyMeasurable)
    ((hFc y₀).intervalIntegrable _ _) hF'1.aestronglyMeasurable
    (Eventually.of_forall fun ψ hψ y hy ↦ hC (y, ψ) ⟨hy, uIoc_subset_uIcc hψ⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun ψ _ y _ ↦ by
      have hc := HasFDerivAt.comp y (rotCLM (-ψ)).hasFDerivAt
        (HasFDerivAt.comp y (hUd (rot ψ y)) (rotCLM ψ).hasFDerivAt)
      exact hc)
  exact h.const_smul ((2 * Real.pi)⁻¹ : ℝ)

/-- **The mean velocity is `C¹`.** -/
theorem contDiff_meanVel (hU : ContDiff ℝ 1 U) : ContDiff ℝ 1 (meanVel U) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun y ↦ (hasFDerivAt_meanVel hU y).differentiableAt, ?_⟩
  have e' : fderiv ℝ (meanVel U) = fun y ↦ (2 * Real.pi)⁻¹ • ∫ ψ in (0 : ℝ)..(2 * Real.pi),
      (rotCLM (-ψ)).comp ((fderiv ℝ U (rot ψ y)).comp (rotCLM ψ)) :=
    funext fun y ↦ (hasFDerivAt_meanVel hU y).fderiv
  rw [e']
  have hDU : Continuous (fderiv ℝ U) := hU.continuous_fderiv (by norm_num)
  have hG : Continuous (Function.uncurry (fun (y : Space) (ψ : ℝ) ↦
      (rotCLM (-ψ)).comp ((fderiv ℝ U (rot ψ y)).comp (rotCLM ψ)))) := by
    refine continuous_clm_apply.mpr fun v ↦ ?_
    simp only [Function.uncurry, ContinuousLinearMap.comp_apply, rotCLM_apply]
    fun_prop
  have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hG 0 (2 * Real.pi)
  exact hc.const_smul ((2 * Real.pi)⁻¹ : ℝ)

end Mean

section Lamb

variable {U : Space → Space} {y : Space}

/-- The squared speed `U₀² + U₁² + U₂²`. -/
def speedSq (U : Space → Space) (y : Space) : ℝ := U y 0 * U y 0 + U y 1 * U y 1 + U y 2 * U y 2

/-- The first curl component `∂₁U₂ - ∂₂U₁`. -/
def curl0 (U : Space → Space) (y : Space) : ℝ := (fderiv ℝ U y (e 1)) 2 - (fderiv ℝ U y (e 2)) 1

/-- The second curl component `∂₂U₀ - ∂₀U₂`. -/
def curl1 (U : Space → Space) (y : Space) : ℝ := (fderiv ℝ U y (e 2)) 0 - (fderiv ℝ U y (e 0)) 2

/-- The swirl `y₀ (U × ω)₁ - y₁ (U × ω)₀` of the vortex force `U × ω`, which is
`r (U × ω)_θ = r (U_z ω_r - U_r ω_z)`: the rate at which `U` sweeps vortex lines
across the circle through `y` about the axis. -/
def vortexForceSwirl (U : Space → Space) (y : Space) : ℝ :=
  y 0 * (U y 2 * curl0 U y - U y 0 * axialVort U y) -
    y 1 * (U y 1 * axialVort U y - U y 2 * curl1 U y)

theorem fderiv_speedSq_apply (hU : DifferentiableAt ℝ U y) (v : Space) :
    fderiv ℝ (speedSq U) y v =
      2 * (U y 0 * (fderiv ℝ U y v) 0 + U y 1 * (fderiv ℝ U y v) 1 +
        U y 2 * (fderiv ℝ U y v) 2) := by
  have h0 := hasFDerivAt_comp_coord hU 0
  have h1 := hasFDerivAt_comp_coord hU 1
  have h2 := hasFDerivAt_comp_coord hU 2
  have h := ((h0.mul h0).add (h1.mul h1)).add (h2.mul h2)
  have h' : HasFDerivAt (speedSq U) _ y := h
  rw [h'.fderiv]
  simp [smul_eq_mul]
  ring

theorem contDiff_speedSq {n : WithTop ℕ∞} (hU : ContDiff ℝ n U) : ContDiff ℝ n (speedSq U) := by
  have c0 := ContDiff.comp (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).contDiff hU
  have c1 := ContDiff.comp (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).contDiff hU
  have c2 := ContDiff.comp (EuclideanSpace.proj 2 : Space →L[ℝ] ℝ).contDiff hU
  have h := ((c0.mul c0).add (c1.mul c1)).add (c2.mul c2)
  exact h

theorem fderiv_apply_self :
    fderiv ℝ U y (U y) = U y 0 • fderiv ℝ U y (e 0) + U y 1 • fderiv ℝ U y (e 1) +
      U y 2 • fderiv ℝ U y (e 2) := by
  have hv : U y = U y 0 • e 0 + U y 1 • e 1 + U y 2 • e 2 := by
    ext i
    fin_cases i <;> simp [e_apply]
  conv_lhs => rw [hv]
  simp only [map_add, map_smul]

/-- **The advection of the swirl is an angular derivative minus the swirl of
the vortex force.** For every differentiable velocity,
`(U · ∇)Γ = ∂_θ(|U|²/2) - Γ(U × ω)`, from `(U · ∇)U = ∇(|U|²/2) - U × ω`. -/
theorem fderiv_swirl_self (hU : DifferentiableAt ℝ U y) :
    fderiv ℝ (swirlSlice U) y (U y) =
      angularDeriv (speedSq U) y / 2 - vortexForceSwirl U y := by
  rw [fderiv_swirlSlice_apply hU, angularDeriv_eq, fderiv_speedSq_apply hU,
    fderiv_speedSq_apply hU, fderiv_apply_self]
  simp only [vortexForceSwirl, curl0, curl1, axialVort, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul]
  ring

theorem continuous_vortexForceSwirl_rot (hU : ContDiff ℝ 1 U) (x : Space) :
    Continuous (fun φ : ℝ ↦ vortexForceSwirl U (rot φ x)) := by
  have hDc : Continuous (fderiv ℝ U) := hU.continuous_fderiv (by norm_num)
  have hcU : Continuous U := hU.continuous
  have hr : Continuous (fun φ : ℝ ↦ rot φ x) := by fun_prop
  have cU : ∀ i : Fin 3, Continuous (fun φ : ℝ ↦ U (rot φ x) i) := fun i ↦
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp (hcU.comp hr)
  have cD : ∀ i j : Fin 3, Continuous (fun φ : ℝ ↦ (fderiv ℝ U (rot φ x) (e j)) i) := fun i j ↦
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp (by fun_prop)
  have cr : ∀ i : Fin 3, Continuous (fun φ : ℝ ↦ (rot φ x) i) := fun i ↦
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp hr
  unfold vortexForceSwirl curl0 curl1 axialVort
  exact ((cr 0).mul (((cU 2).mul ((cD 2 1).sub (cD 1 2))).sub
      ((cU 0).mul ((cD 1 0).sub (cD 0 1))))).sub
    ((cr 1).mul (((cU 1).mul ((cD 1 0).sub (cD 0 1))).sub
      ((cU 2).mul ((cD 0 2).sub (cD 2 0)))))

/-- **Around a circle, the advection of the swirl is minus the vortex force.** -/
theorem circleInt_advection_eq_vortexForce (hU : ContDiff ℝ 1 U) (x : Space) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), fderiv ℝ (swirlSlice U) (rot φ x) (U (rot φ x)) =
      -∫ φ in (0 : ℝ)..(2 * Real.pi), vortexForceSwirl U (rot φ x) := by
  have hUd : Differentiable ℝ U := hU.differentiable (by norm_num)
  have hK1 : ContDiff ℝ 1 (speedSq U) := contDiff_speedSq hU
  have hA : Continuous (fun φ : ℝ ↦ angularDeriv (speedSq U) (rot φ x) / 2) := by
    have hKc : Continuous (fderiv ℝ (speedSq U)) := hK1.continuous_fderiv (by norm_num)
    have hang' : Continuous angular := by
      have e' : angular = fun y : Space ↦ y 0 • e 1 - y 1 • e 0 := funext angular_eq
      rw [e']
      fun_prop
    unfold angularDeriv
    fun_prop
  simp only [fderiv_swirl_self (hUd _)]
  rw [intervalIntegral.integral_sub (hA.intervalIntegrable _ _)
      ((continuous_vortexForceSwirl_rot hU x).intervalIntegrable _ _),
    intervalIntegral.integral_div, integral_angularDeriv_rot hK1, zero_div, zero_sub]

end Lamb

section Budget

set_option maxHeartbeats 1000000 in
/-- **The averaged swirl grows at its maxima at most by the averaged vortex
force.** Under the hypotheses of `deriv_circleInt_swirl_le`,
`∂ₜ ∮Γ ≤ ∮ Γ(u × ω) + ∮ (x₀ f₁ - x₁ f₀)` at every spatial local maximum off the
axis. -/
theorem deriv_circleInt_swirl_le_vortexForce {ν : ℝ} (hν : 0 ≤ ν) {u : ℝ × Space → Space}
    {p : ℝ × Space → ℝ} {f : ℝ × Space → Space} {t : ℝ} {x : Space} (hu : ContDiff ℝ 2 u)
    (hp : ContDiff ℝ 1 (fun y : Space ↦ p (t, y))) (hf : Continuous (fun y : Space ↦ f (t, y)))
    (hres : ∀ y, NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t y = f (t, y))
    (hmax : IsLocalMax (circleInt (swirlSlice (fun y ↦ u (t, y)))) x) (hr : x 0 ^ 2 + x 1 ^ 2 ≠ 0) :
    deriv (fun s ↦ circleInt (swirlSlice (fun y ↦ u (s, y))) x) t ≤
      (∫ φ in (0 : ℝ)..(2 * Real.pi), vortexForceSwirl (fun y ↦ u (t, y)) (rot φ x)) +
        ∫ φ in (0 : ℝ)..(2 * Real.pi), torque f t (rot φ x) := by
  have hbase := deriv_circleInt_swirl_le hν hu hp hf hres hmax hr
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hslice : ContDiff ℝ 1 (fun y : Space ↦ u (t, y)) := by
    have h := ContDiff.comp hu1 (contDiff_const.prodMk contDiff_id : ContDiff ℝ 1
      (fun y : Space ↦ ((t, y) : ℝ × Space)))
    exact h
  have hL := circleInt_advection_eq_vortexForce hslice x
  rw [hL, neg_neg] at hbase
  exact hbase

set_option maxHeartbeats 1000000 in
/-- **Only fluctuation vorticity carried across the rim can raise the maximal
circulation.** Under the hypotheses of `deriv_circleInt_swirl_le`, with
`u' = u - ū` the deviation of the velocity from its rotation-equivariant mean
and `ω' = curl u'`, at every spatial local maximum off the axis
`∂ₜ ∮Γ ≤ ∮ Γ(u' × ω') + ∮ (x₀ f₁ - x₁ f₀)`. -/
theorem deriv_circleInt_swirl_le_eddyFlux {ν : ℝ} (hν : 0 ≤ ν) {u : ℝ × Space → Space}
    {p : ℝ × Space → ℝ} {f : ℝ × Space → Space} {t : ℝ} {x : Space} (hu : ContDiff ℝ 2 u)
    (hp : ContDiff ℝ 1 (fun y : Space ↦ p (t, y))) (hf : Continuous (fun y : Space ↦ f (t, y)))
    (hres : ∀ y, NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t y = f (t, y))
    (hmax : IsLocalMax (circleInt (swirlSlice (fun y ↦ u (t, y)))) x) (hr : x 0 ^ 2 + x 1 ^ 2 ≠ 0) :
    deriv (fun s ↦ circleInt (swirlSlice (fun y ↦ u (s, y))) x) t ≤
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
          vortexForceSwirl (fun y ↦ u (t, y) - meanVel (fun y ↦ u (t, y)) y) (rot φ x)) +
        ∫ φ in (0 : ℝ)..(2 * Real.pi), torque f t (rot φ x) := by
  have hbase := deriv_circleInt_swirl_le_reynolds hν hu hp hf hres hmax hr
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hslice : ContDiff ℝ 1 (fun y : Space ↦ u (t, y)) := by
    have h := ContDiff.comp hu1 (contDiff_const.prodMk contDiff_id : ContDiff ℝ 1
      (fun y : Space ↦ ((t, y) : ℝ × Space)))
    exact h
  have hfl : ContDiff ℝ 1 (fun y ↦ u (t, y) - meanVel (fun y ↦ u (t, y)) y) :=
    hslice.sub (contDiff_meanVel hslice)
  have hΓ' : (fun y ↦ swirlSlice (fun y ↦ u (t, y)) y -
      (2 * Real.pi)⁻¹ * circleInt (swirlSlice (fun y ↦ u (t, y))) y) =
      swirlSlice (fun y ↦ u (t, y) - meanVel (fun y ↦ u (t, y)) y) := by
    funext y
    rw [← swirlSlice_meanVel hslice.continuous y]
    simp only [swirlSlice, PiLp.sub_apply]
    ring
  rw [hΓ'] at hbase
  have hL : ∫ φ in (0 : ℝ)..(2 * Real.pi),
      fderiv ℝ (swirlSlice (fun y ↦ u (t, y) - meanVel (fun y ↦ u (t, y)) y)) (rot φ x)
        (u (t, rot φ x) - meanVel (fun y ↦ u (t, y)) (rot φ x)) =
      -∫ φ in (0 : ℝ)..(2 * Real.pi),
        vortexForceSwirl (fun y ↦ u (t, y) - meanVel (fun y ↦ u (t, y)) y) (rot φ x) :=
    circleInt_advection_eq_vortexForce hfl x
  rw [hL, neg_neg] at hbase
  exact hbase

end Budget

end Mettapedia.FluidDynamics.NavierStokes.CirculationFlux
