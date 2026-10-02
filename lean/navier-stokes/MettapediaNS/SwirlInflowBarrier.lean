import MettapediaNS.SwirlBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# An inflow barrier for the axisymmetric swirl

For an axisymmetric flow the swirl `Γ = x₀ u₁ - x₁ u₀ = r u_θ` vanishes on the
third axis and obeys the transport–diffusion law of `SwirlBudget`. Write
`s = x₀² + x₁² = r²` and compare the swirl with the profile `φ = c s^q`,
`c, q ≥ 0`. Off the axis

```text
(u · ∇)φ = 2 c q s^(q-1) (x₀ u₀ + x₁ u₁),     Δφ = 4 c q² s^(q-1),
```

and `x₀ u₀ + x₁ u₁ = r u_r`. At a local maximum of `Γ - φ` off the axis the
gradients of `Γ` and `φ` agree, so the identity `x₀ ∂₀Γ + x₁ ∂₁Γ = r² ω₃` of an
axisymmetric velocity gives the axial vorticity `ω₃ = 2 c q s^(q-1)`, and the
swirl identity gives

```text
∂ₜΓ ≤ 2 c q s^(q-1) (-(x₀ u₀ + x₁ u₁) - 2ν (1 - q)) + (x₀ f₁ - x₁ f₀).
```

So where the inflow strength `r (-u_r)` is at most `2ν (1 - q)`, the swirl
cannot rise above `φ` at such a maximum (`deriv_swirl_le_torque_of_barrier_max`).
Maximizing `Γ - φ - ε t` over a compact region gives the comparison
(`swirl_le_barrier`): if the swirl lies below `φ` initially and wherever
`s ≥ R`, the torque of the force is nonpositive, and `x₀ u₀ + x₁ u₁ ≥ -2ν(1-q)`
wherever `s < R`, then `Γ ≤ c (r²)^q` at all later times.

In the radial variable, transport and diffusion of the swirl under the inflow
`u_r = -κ / r` form the generator of a Bessel process of dimension `κ / ν`,
and `r^(2 - κ/ν)` is its scale function; the threshold `κ = 2ν` is dimension
two, where the axis stops being reachable. For `0 < q` the comparison gives
power-law decay `Γ ≤ c r^(2q)` of the swirl at the axis. Combined with the
known logarithmic swirl-decay regularity criteria, which are not formalized
here, a singularity of an unforced axisymmetric flow therefore needs inflow
strengths `r (-u_r)` reaching `2ν` arbitrarily close to the axis and to the
singular time (compare the compression threshold of arXiv:2604.21213). Nothing
here bounds the inflow.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SwirlInflowBarrier

open Set Filter Topology
open _root_.NavierStokes.ProblemStatement
open Mettapedia.FluidDynamics.NavierStokes.SwirlBudget

section Profile

theorem e_zero_zero : (e 0) 0 = 1 := by simp [e_apply]

theorem e_zero_one : (e 0) 1 = 0 := by simp [e_apply]

theorem e_one_zero : (e 1) 0 = 0 := by simp [e_apply]

theorem e_one_one : (e 1) 1 = 1 := by simp [e_apply]

theorem e_two_zero : (e 2) 0 = 0 := by simp [e_apply]

theorem e_two_one : (e 2) 1 = 0 := by simp [e_apply]

/-- The squared distance `x₀² + x₁²` to the third axis. -/
def horizSq (y : Space) : ℝ := y 0 * y 0 + y 1 * y 1

theorem horizSq_nonneg (y : Space) : 0 ≤ horizSq y := by
  unfold horizSq
  nlinarith [mul_self_nonneg (y 0), mul_self_nonneg (y 1)]

/-- The derivative of `horizSq` at `y`. -/
def horizDeriv (y : Space) : Space →L[ℝ] ℝ :=
  (2 * y 0) • (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ) +
    (2 * y 1) • (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ)

theorem horizDeriv_apply (y v : Space) :
    horizDeriv y v = 2 * y 0 * v 0 + 2 * y 1 * v 1 := by
  simp [horizDeriv]

theorem hasFDerivAt_horizSq (y : Space) : HasFDerivAt horizSq (horizDeriv y) y := by
  have h := ((hasFDerivAt_coord 0 y).mul (hasFDerivAt_coord 0 y)).add
    ((hasFDerivAt_coord 1 y).mul (hasFDerivAt_coord 1 y))
  have h' : HasFDerivAt horizSq _ y := h
  refine h'.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  rw [horizDeriv_apply]
  simp
  ring

theorem contDiff_horizSq {n : WithTop ℕ∞} : ContDiff ℝ n horizSq := by
  have c0 : ContDiff ℝ n (fun z : Space ↦ z 0) :=
    (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).contDiff
  have c1 : ContDiff ℝ n (fun z : Space ↦ z 1) :=
    (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).contDiff
  exact (c0.mul c0).add (c1.mul c1)

/-- The barrier profile `c s^q`, with `s = x₀² + x₁²`. -/
def barrier (c q : ℝ) (y : Space) : ℝ := c * horizSq y ^ q

theorem barrier_nonneg {c : ℝ} (hc : 0 ≤ c) (q : ℝ) (y : Space) : 0 ≤ barrier c q y :=
  mul_nonneg hc (Real.rpow_nonneg (horizSq_nonneg y) q)

theorem continuous_barrier (c : ℝ) {q : ℝ} (hq : 0 ≤ q) : Continuous (barrier c q) := by
  have h : Continuous fun y : Space ↦ horizSq y ^ q :=
    (Real.continuous_rpow_const hq).comp (contDiff_horizSq (n := 0)).continuous
  exact continuous_const.mul h

theorem hasFDerivAt_barrier (c q : ℝ) {y : Space} (hy : horizSq y ≠ 0) :
    HasFDerivAt (barrier c q) (c • ((q * horizSq y ^ (q - 1)) • horizDeriv y)) y :=
  ((hasFDerivAt_horizSq y).rpow_const (Or.inl hy)).const_mul c

theorem fderiv_barrier_apply (c q : ℝ) {y : Space} (hy : horizSq y ≠ 0) (v : Space) :
    fderiv ℝ (barrier c q) y v =
      c * q * horizSq y ^ (q - 1) * (2 * y 0 * v 0 + 2 * y 1 * v 1) := by
  rw [(hasFDerivAt_barrier c q hy).fderiv]
  simp only [_root_.smul_apply, smul_eq_mul, horizDeriv_apply]
  ring

theorem contDiffAt_barrier (c q : ℝ) {y : Space} (hy : horizSq y ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (barrier c q) y := by
  have h : ContDiffAt ℝ n (fun z ↦ horizSq z ^ q) y :=
    (contDiff_horizSq.contDiffAt).rpow_const_of_ne hy
  exact contDiffAt_const.mul h

/-- The second derivative of the barrier along a direction, off the axis. -/
theorem fderiv_fderiv_barrier (c q : ℝ) {y : Space} (hy : horizSq y ≠ 0) (v : Space) :
    fderiv ℝ (fun z ↦ fderiv ℝ (barrier c q) z v) y v =
      c * q * ((q - 1) * horizSq y ^ (q - 1 - 1) * (2 * y 0 * v 0 + 2 * y 1 * v 1) ^ 2 +
        horizSq y ^ (q - 1) * (2 * v 0 * v 0 + 2 * v 1 * v 1)) := by
  have hopen : IsOpen {z : Space | horizSq z ≠ 0} :=
    isOpen_ne_fun (contDiff_horizSq (n := 0)).continuous continuous_const
  have hev : (fun z ↦ fderiv ℝ (barrier c q) z v) =ᶠ[𝓝 y]
      fun z ↦ c * q * horizSq z ^ (q - 1) * horizDeriv v z :=
    Filter.eventually_of_mem (hopen.mem_nhds hy) fun z hz ↦ by
      show fderiv ℝ (barrier c q) z v = c * q * horizSq z ^ (q - 1) * horizDeriv v z
      rw [fderiv_barrier_apply c q hz v, horizDeriv_apply]
      ring
  rw [hev.fderiv_eq]
  have h1 : HasFDerivAt (fun z : Space ↦ horizSq z ^ (q - 1))
      (((q - 1) * horizSq y ^ (q - 1 - 1)) • horizDeriv y) y :=
    (hasFDerivAt_horizSq y).rpow_const (Or.inl hy)
  have h3 := (h1.const_mul (c * q)).mul (horizDeriv v).hasFDerivAt
  have h3' : HasFDerivAt (fun z ↦ c * q * horizSq z ^ (q - 1) * horizDeriv v z) _ y := h3
  rw [h3'.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    horizDeriv_apply]
  ring

/-- The Laplacian of the barrier off the axis: `Δ(c s^q) = 4 c q² s^(q-1)`. -/
theorem laplacian_barrier (c q : ℝ) {y : Space} (hy : horizSq y ≠ 0) :
    ∑ i : Fin 3, fderiv ℝ (fun z ↦ fderiv ℝ (barrier c q) z (e i)) y (e i) =
      4 * c * q * q * horizSq y ^ (q - 1) := by
  rw [Fin.sum_univ_three, fderiv_fderiv_barrier c q hy, fderiv_fderiv_barrier c q hy,
    fderiv_fderiv_barrier c q hy]
  have hs : horizSq y ^ (q - 1 - 1) * (y 0 * y 0 + y 1 * y 1) = horizSq y ^ (q - 1) := by
    rw [Real.rpow_sub_one hy (q - 1)]
    exact div_mul_cancel₀ _ hy
  simp only [e_zero_zero, e_zero_one, e_one_zero, e_one_one, e_two_zero, e_two_one]
  linear_combination (4 * c * q * (q - 1)) * hs

end Profile

section Core

/-- **The radial identity of an axisymmetric swirl**: `x₀ ∂₀Γ + x₁ ∂₁Γ = r² ω₃`. -/
theorem radial_swirl {u : VelocityField} {t : ℝ} {x : Space}
    (hu : AxisymmetricVelocity u t) (hd : DifferentiableAt ℝ (fun y ↦ u (t, y)) x) :
    x 0 * fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) x (e 0) +
        x 1 * fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) x (e 1) =
      horizSq x * axialVorticity u t x := by
  have hE := fderiv_angular_eq hu hd
  rw [angular_eq, map_sub, map_smul, map_smul] at hE
  have hE0 := congrArg (fun v : Space ↦ v 0) hE
  have hE1 := congrArg (fun v : Space ↦ v 1) hE
  simp only [angular, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hE0 hE1
  simp at hE0 hE1
  rw [fderiv_swirlSlice_apply hd (e 0), fderiv_swirlSlice_apply hd (e 1), e_zero_zero,
    e_zero_one, e_one_zero, e_one_one]
  unfold horizSq axialVorticity spatialDerivative
  linear_combination x 0 * hE0 + x 1 * hE1

/-- **The pointwise core of the inflow barrier.** At a spatial local maximum
of `Γ - c s^q` off the axis, where the inflow strength satisfies
`x₀ u₀ + x₁ u₁ ≥ -2ν(1-q)`, the swirl grows no faster than the torque of the
force. -/
theorem deriv_swirl_le_torque_of_barrier_max {ν c q : ℝ} (hν : 0 ≤ ν) (hc : 0 ≤ c)
    (hq : 0 ≤ q) {u : VelocityField} {p : PressureField} {f : VelocityField} {t : ℝ}
    {x : Space} (hu : ContDiffAt ℝ 2 (fun y ↦ u (t, y)) x)
    (ht : DifferentiableAt ℝ (fun s ↦ u (s, x)) t)
    (hres : NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x))
    (hmax : IsLocalMax (fun y ↦ swirlSlice (fun y ↦ u (t, y)) y - barrier c q y) x)
    (haxi : AxisymmetricVelocity u t) (hpaxi : AxisymmetricPressure p t)
    (hp : DifferentiableAt ℝ (fun y ↦ p (t, y)) x) (hr : horizSq x ≠ 0)
    (hin : -(2 * ν * (1 - q)) ≤ x 0 * u (t, x) 0 + x 1 * u (t, x) 1) :
    deriv (fun s ↦ swirlSlice (fun y ↦ u (s, y)) x) t ≤ torque f t x := by
  have hid := swirl_identity hu ht hres
  have hUx : DifferentiableAt ℝ (fun y ↦ u (t, y)) x := hu.differentiableAt (by norm_num)
  have hΓ2 : ContDiffAt ℝ 2 (swirlSlice (fun y ↦ u (t, y))) x := contDiffAt_swirlSlice hu
  have hφ2 : ContDiffAt ℝ 2 (barrier c q) x := contDiffAt_barrier c q hr
  have hw2 : ContDiffAt ℝ 2 (fun y ↦ swirlSlice (fun y ↦ u (t, y)) y - barrier c q y) x :=
    hΓ2.sub hφ2
  -- first order: the gradients agree
  have hcrit : fderiv ℝ (fun y ↦ swirlSlice (fun y ↦ u (t, y)) y - barrier c q y) x = 0 :=
    IsLocalMax.fderiv_eq_zero hmax
  have hgrad : ∀ v, fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) x v =
      fderiv ℝ (barrier c q) x v := by
    intro v
    have h := congrArg (fun L : Space →L[ℝ] ℝ ↦ L v) hcrit
    rw [fderiv_fun_sub (hΓ2.differentiableAt (by norm_num))
      (hφ2.differentiableAt (by norm_num))] at h
    simp only [_root_.sub_apply, _root_.zero_apply] at h
    linarith
  -- second order: the Laplacian of the swirl is at most that of the barrier
  have hsec : ∀ i : Fin 3,
      fderiv ℝ (fun y ↦ fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) y (e i)) x (e i) ≤
        fderiv ℝ (fun y ↦ fderiv ℝ (barrier c q) y (e i)) x (e i) := by
    intro i
    have h := secondDeriv_nonpos_of_isLocalMax hw2 hmax (e i)
    have hevΓ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (swirlSlice (fun y ↦ u (t, y))) y :=
      (hΓ2.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by norm_num)
    have hevφ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (barrier c q) y :=
      (hφ2.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by norm_num)
    have hev : (fun y ↦ fderiv ℝ (fun y ↦ swirlSlice (fun y ↦ u (t, y)) y - barrier c q y) y
        (e i)) =ᶠ[𝓝 x] fun y ↦ fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) y (e i) -
          fderiv ℝ (barrier c q) y (e i) :=
      (hevΓ.and hevφ).mono fun y hy ↦ by
        show fderiv ℝ (fun y ↦ swirlSlice (fun y ↦ u (t, y)) y - barrier c q y) y (e i) =
          fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) y (e i) - fderiv ℝ (barrier c q) y (e i)
        rw [fderiv_fun_sub hy.1 hy.2, _root_.sub_apply]
    rw [hev.fderiv_eq] at h
    have hdΓ : DifferentiableAt ℝ
        (fun y ↦ fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) y (e i)) x :=
      ((hΓ2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
        (differentiableAt_const _)
    have hdφ : DifferentiableAt ℝ (fun y ↦ fderiv ℝ (barrier c q) y (e i)) x :=
      ((hφ2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
        (differentiableAt_const _)
    rw [fderiv_fun_sub hdΓ hdφ] at h
    simp only [_root_.sub_apply] at h
    linarith
  have hlap : ∑ i : Fin 3,
      fderiv ℝ (fun y ↦ fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) y (e i)) x (e i) ≤
        4 * c * q * q * horizSq x ^ (q - 1) := by
    rw [← laplacian_barrier c q hr]
    exact Finset.sum_le_sum fun i _ ↦ hsec i
  -- the axial vorticity at the maximum
  have hA0 : 0 ≤ c * q * horizSq x ^ (q - 1) :=
    mul_nonneg (mul_nonneg hc hq) (Real.rpow_nonneg (horizSq_nonneg x) _)
  have hrad := radial_swirl haxi hUx
  rw [hgrad (e 0), hgrad (e 1), fderiv_barrier_apply c q hr, fderiv_barrier_apply c q hr,
    e_zero_zero, e_zero_one, e_one_zero, e_one_one] at hrad
  have hsx : horizSq x = x 0 * x 0 + x 1 * x 1 := rfl
  have hω : axialVorticity u t x = 2 * (c * q * horizSq x ^ (q - 1)) := by
    apply mul_left_cancel₀ hr
    linear_combination -hrad - (2 * (c * q * horizSq x ^ (q - 1))) * hsx
  -- the advection of the swirl at the maximum
  have hadv : fderiv ℝ (swirlSlice (fun y ↦ u (t, y))) x (u (t, x)) =
      c * q * horizSq x ^ (q - 1) * (2 * x 0 * u (t, x) 0 + 2 * x 1 * u (t, x) 1) := by
    rw [hgrad, fderiv_barrier_apply c q hr]
  have hθ := angularDerivative_eq_zero hpaxi hp
  rw [hadv, hω, hθ] at hid
  nlinarith [mul_nonneg hν (sub_nonneg.mpr hlap),
    mul_nonneg hA0 (show 0 ≤ x 0 * u (t, x) 0 + x 1 * u (t, x) 1 + 2 * ν * (1 - q) by
      linarith)]

end Core

section Comparison

/-- **The inflow barrier.** Let an axisymmetric flow with axisymmetric
pressure be continuous on `[0, T] × ℝ³`, twice differentiable in space and
differentiable in time on `(0, T]`, with swirl nonpositive outside a compact
set and a force of nonpositive torque. If the swirl lies below `c s^q`
initially and wherever `s = x₀² + x₁² ≥ R`, and the inflow strength satisfies
`x₀ u₀ + x₁ u₁ ≥ -2ν(1-q)` wherever `s < R`, then the swirl stays below
`c s^q` on `[0, T]`. -/
theorem swirl_le_barrier {ν c q R : ℝ} (hν : 0 ≤ ν) (hc : 0 ≤ c) (hq : 0 ≤ q)
    {u : VelocityField} {p : PressureField} {f : VelocityField} {T : ℝ} {K : Set Space}
    (hK : IsCompact K) (hcont : ContinuousOn u (Set.Icc 0 T ×ˢ Set.univ))
    (hout : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∉ K, swirlSlice (fun y ↦ u (t, y)) x ≤ 0)
    (hinit : ∀ x, swirlSlice (fun y ↦ u (0, y)) x ≤ barrier c q x)
    (hfar : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, R ≤ horizSq x →
      swirlSlice (fun y ↦ u (t, y)) x ≤ barrier c q x)
    (hreg : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x, ContDiffAt ℝ 2 (fun y ↦ u (t, y)) x ∧
      DifferentiableAt ℝ (fun s ↦ u (s, x)) t ∧ DifferentiableAt ℝ (fun y ↦ p (t, y)) x)
    (hres : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x))
    (haxi : ∀ t ∈ Set.Ioc (0 : ℝ) T, AxisymmetricVelocity u t)
    (hpaxi : ∀ t ∈ Set.Ioc (0 : ℝ) T, AxisymmetricPressure p t)
    (htorque : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x, torque f t x ≤ 0)
    (hin : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ x, horizSq x < R →
      -(2 * ν * (1 - q)) ≤ x 0 * u (t, x) 0 + x 1 * u (t, x) 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, swirlSlice (fun y ↦ u (t, y)) x ≤ barrier c q x := by
  intro t ht x
  by_contra hlt
  push Not at hlt
  set δ := swirlSlice (fun y ↦ u (t, y)) x - barrier c q x with hδ
  have hδ0 : 0 < δ := by linarith
  have hT : 0 ≤ T := ht.1.trans ht.2
  -- the tilt
  set ε : ℝ := δ / (2 * (T + 1)) with hε
  have hε0 : 0 < ε := div_pos hδ0 (by linarith)
  set G : ℝ × Space → ℝ := fun z ↦ swirlField u z - barrier c q z.2 - ε * z.1 with hG
  have hGc : ContinuousOn G (Set.Icc 0 T ×ˢ Set.univ) :=
    ((continuousOn_swirlField hcont).sub
      ((continuous_barrier c hq).comp continuous_snd).continuousOn).sub
      (continuousOn_const.mul continuous_fst.continuousOn)
  -- the tilted excess is positive at `(t, x)`
  have hGtx : 0 < G (t, x) := by
    have h1 : ε * t ≤ δ / 2 := by
      rw [hε, div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith [ht.1, ht.2]
    show 0 < swirlField u (t, x) - barrier c q x - ε * t
    have : swirlField u (t, x) = swirlSlice (fun y ↦ u (t, y)) x := rfl
    linarith
  have hxK : x ∈ K := by
    by_contra hx
    have h1 := hout t ht x hx
    have h2 := barrier_nonneg hc q x
    linarith
  -- a maximum of the tilted excess on the compact region
  have hcpt : IsCompact (Set.Icc (0 : ℝ) T ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨z, hz, hmax⟩ := hcpt.exists_isMaxOn ⟨(t, x), ⟨ht, hxK⟩⟩
    (hGc.mono (Set.prod_mono subset_rfl (Set.subset_univ K)))
  obtain ⟨ts, xs⟩ := z
  have hts : ts ∈ Set.Icc (0 : ℝ) T := hz.1
  have hxs : xs ∈ K := hz.2
  have hGz : 0 < G (ts, xs) := lt_of_lt_of_le hGtx (hmax ⟨ht, hxK⟩)
  have hGs : G (ts, xs) = swirlSlice (fun y ↦ u (ts, y)) xs - barrier c q xs - ε * ts := rfl
  have hεts : 0 ≤ ε * ts := mul_nonneg hε0.le hts.1
  -- the maximum is at a positive time
  have hts0 : 0 < ts := by
    rcases eq_or_lt_of_le hts.1 with h | h
    · exfalso
      have h1 : G (ts, xs) = swirlSlice (fun y ↦ u (0, y)) xs - barrier c q xs := by
        simp only [hG, swirlField, ← h, mul_zero, sub_zero]
      have := hinit xs
      linarith
    · exact h
  have hts' : ts ∈ Set.Ioc (0 : ℝ) T := ⟨hts0, hts.2⟩
  -- inside the inflow region
  have hRs : horizSq xs < R := by
    by_contra hge
    push Not at hge
    have := hfar ts hts xs hge
    linarith
  -- off the axis
  have hr : horizSq xs ≠ 0 := by
    intro h0
    have hx0 : xs 0 = 0 := by
      unfold horizSq at h0
      nlinarith [mul_self_nonneg (xs 0), mul_self_nonneg (xs 1)]
    have hx1 : xs 1 = 0 := by
      unfold horizSq at h0
      nlinarith [mul_self_nonneg (xs 0), mul_self_nonneg (xs 1)]
    have hΓ0 : swirlSlice (fun y ↦ u (ts, y)) xs = 0 := by simp [swirlSlice, hx0, hx1]
    have := barrier_nonneg hc q xs
    linarith
  -- a spatial maximum of the excess of the swirl over the barrier
  have hsmax : IsLocalMax (fun y ↦ swirlSlice (fun y ↦ u (ts, y)) y - barrier c q y) xs := by
    refine IsMaxOn.isLocalMax (s := Set.univ) (fun y _ ↦ ?_) Filter.univ_mem
    show swirlSlice (fun y ↦ u (ts, y)) y - barrier c q y ≤
      swirlSlice (fun y ↦ u (ts, y)) xs - barrier c q xs
    by_cases hy : y ∈ K
    · have := hmax (show ((ts, y) : ℝ × Space) ∈ Set.Icc (0 : ℝ) T ×ˢ K from ⟨hts, hy⟩)
      simp only [Set.mem_ofPred_eq] at this
      have e1 : G (ts, y) = swirlSlice (fun y ↦ u (ts, y)) y - barrier c q y - ε * ts := rfl
      linarith
    · have h1 := hout ts hts y hy
      have h2 := barrier_nonneg hc q y
      linarith
  -- the pointwise core at the maximum
  obtain ⟨hu2, htd, hpd⟩ := hreg ts hts' xs
  have hcore := deriv_swirl_le_torque_of_barrier_max hν hc hq hu2 htd (hres ts hts' xs) hsmax
    (haxi ts hts') (hpaxi ts hts') hpd hr (hin ts hts' xs hRs)
  have hcore' : deriv (fun s ↦ swirlSlice (fun y ↦ u (s, y)) xs) ts ≤ 0 :=
    hcore.trans (htorque ts hts' xs)
  -- the time derivative from the left is at least `ε`
  set g : ℝ → ℝ := fun s ↦ swirlSlice (fun y ↦ u (s, y)) xs with hg
  have hgd : DifferentiableAt ℝ g ts := by
    have h0 : DifferentiableAt ℝ (fun s ↦ u (s, xs) 0) ts :=
      DifferentiableAt.comp ts (ContinuousLinearMap.differentiableAt
        (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ)) htd
    have h1 : DifferentiableAt ℝ (fun s ↦ u (s, xs) 1) ts :=
      DifferentiableAt.comp ts (ContinuousLinearMap.differentiableAt
        (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ)) htd
    exact DifferentiableAt.sub (DifferentiableAt.const_mul h1 (xs 0))
      (DifferentiableAt.const_mul h0 (xs 1))
  have hlim := HasDerivAt.tendsto_slope_zero_left (DifferentiableAt.hasDerivAt hgd)
  have hev : ∀ᶠ h in 𝓝[<] (0 : ℝ), ε ≤ h⁻¹ • (g (ts + h) - g ts) := by
    have hmem : Set.Ioo (-ts) 0 ∈ 𝓝[<] (0 : ℝ) := Ioo_mem_nhdsLT (by linarith)
    filter_upwards [hmem] with h hh
    have hsIcc : ts + h ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hh.1], by linarith [hh.2, hts.2]⟩
    have hle := hmax (show ((ts + h, xs) : ℝ × Space) ∈ Set.Icc (0 : ℝ) T ×ˢ K from ⟨hsIcc, hxs⟩)
    simp only [Set.mem_ofPred_eq] at hle
    have e1 : G (ts + h, xs) = g (ts + h) - barrier c q xs - ε * (ts + h) := rfl
    have e2 : G (ts, xs) = g ts - barrier c q xs - ε * ts := rfl
    have hdiff : g (ts + h) - g ts ≤ ε * h := by linarith
    rw [smul_eq_mul, ← div_eq_inv_mul, le_div_iff_of_neg hh.2]
    linarith
  have hge : ε ≤ deriv g ts := ge_of_tendsto hlim hev
  have : deriv g ts = deriv (fun s ↦ swirlSlice (fun y ↦ u (s, y)) xs) ts := rfl
  linarith

end Comparison

end Mettapedia.FluidDynamics.NavierStokes.SwirlInflowBarrier
