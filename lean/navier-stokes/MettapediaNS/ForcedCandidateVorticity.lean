import NavierStokes.R3.ProblemStatement
import MettapediaNS.WholeSpaceBiotSavart

/-!
# Vorticity moments along the whole-space forced blowup candidates

A smooth, compactly supported, divergence-free velocity on `ℝ³` equals the
Alpöge–Buckmaster Biot–Savart velocity of its own curl. The proof uses only
the imported Green representation `N(ΔF) = F`, the commutation of the
Newtonian potential with coordinate derivatives, and the curl–curl identity
`-curl curl v = Δv - ∇ div v`.

The imported gradient kernel has norm `1/(4π|z|²)`. For `p > 3` its conjugate
exponent `q` satisfies `2q < 3`, so the kernel is locally in `L^q`. Hölder's
inequality then gives, for every compact set `K`, one constant `C` such that

```text
‖v(x)‖ ≤ C (∫ ‖curl v‖^p)^(1/p)
```

for every such velocity supported in `K`.

Every whole-space candidate of OpenAI's Theorem 1.1
(`NavierStokesR3.ProblemStatement.CandidateProperties`) keeps its velocity
in one compact set before time one and has unbounded speed at time one.
Consequently its vorticity moments `∫ ‖ω‖^p`, `p > 3`, are unbounded before
time one. This includes the eighth moment `∫ ‖ω‖⁸` used by the periodic
eighth-moment identity. The candidates are driven by smooth, compactly
supported forces. A proposed bound on these moments, finite up to a
candidate singular time, whose derivation also applies to such forced
solutions would contradict these theorems. They say nothing about a
bound that uses the absence of forcing.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open EulerBlowup Ring3D
open scoped ContDiff Laplacian ENNReal

namespace Mettapedia.FluidDynamics.NavierStokes.ForcedCandidateVorticity

/-! ### Index arithmetic on `Fin 3` -/

theorem fin3_add_one_add_one (j : Fin 3) : j + 1 + 1 = j + 2 := by
  fin_cases j <;> rfl

theorem fin3_add_one_add_two (j : Fin 3) : j + 1 + 2 = j := by
  fin_cases j <;> rfl

theorem fin3_add_two_add_one (j : Fin 3) : j + 2 + 1 = j := by
  fin_cases j <;> rfl

theorem fin3_add_two_add_two (j : Fin 3) : j + 2 + 2 = j + 1 := by
  fin_cases j <;> rfl

theorem fin3_sum_rotate (j : Fin 3) (g : Fin 3 → ℝ) :
    ∑ i, g i = g j + g (j + 1) + g (j + 2) := by
  fin_cases j <;> simp [Fin.sum_univ_three] <;> ring

/-! ### Coordinate calculus for the imported operators -/

theorem pd3_fun_sub {f g : R3 → ℝ} {x : R3} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    pd3 i (fun y ↦ f y - g y) x = pd3 i f x - pd3 i g x := by
  simp only [pd3, fderiv_fun_sub hf hg]
  rfl

theorem pd3_fun_add {f g : R3 → ℝ} {x : R3} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    pd3 i (fun y ↦ f y + g y) x = pd3 i f x + pd3 i g x := by
  simp only [pd3, fderiv_fun_add hf hg]
  rfl

/-- Coordinate derivatives of a smooth scalar field commute. -/
theorem pd3_comm {φ : R3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (i j : Fin 3) (x : R3) :
    pd3 i (pd3 j φ) x = pd3 j (pd3 i φ) x := by
  rw [Lit3.newton3_poisson_aux_pdPd φ hφ i j x, Lit3.newton3_poisson_aux_pdPd φ hφ j i x]
  exact hφ.contDiffAt.isSymmSndFDerivAt (by simp) (e3 i) (e3 j)

theorem differentiable_pd3 {φ : R3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (i : Fin 3) :
    Differentiable ℝ (pd3 i φ) :=
  (Lit3.newton3_poisson_aux_pdSmooth φ hφ i).differentiable (by simp)

theorem contDiff_coord {v : R3 → R3} (hv : ContDiff ℝ ∞ v) (k : Fin 3) :
    ContDiff ℝ ∞ (fun y ↦ v y k) :=
  contDiff_euclidean.mp hv k

theorem hasCompactSupport_coord {v : R3 → R3} (hc : HasCompactSupport v) (k : Fin 3) :
    HasCompactSupport (fun y ↦ v y k) :=
  hc.comp_left (g := fun z : R3 ↦ z k) rfl

/-- The coordinate derivative of a component is the component of the derivative. -/
theorem fderiv_coord_apply {v : R3 → R3} {x : R3} (hv : DifferentiableAt ℝ v x)
    (i : Fin 3) (w : R3) : fderiv ℝ (fun y ↦ v y i) x w = fderiv ℝ v x w i := by
  have he : HasFDerivAt (fun y ↦ v y i)
      ((EuclideanSpace.proj i).comp (fderiv ℝ v x)) x :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (v x) i).comp x hv.hasFDerivAt
  rw [he.fderiv]
  rfl

/-- The cyclic coordinate form of the imported curl. -/
theorem curl3_coord (v : R3 → R3) (k : Fin 3) (x : R3) :
    curl3 v x k =
      pd3 (k + 1) (fun y ↦ v y (k + 2)) x - pd3 (k + 2) (fun y ↦ v y (k + 1)) x := by
  fin_cases k <;> simp [curl3, e3]

theorem contDiff_curl3_coord {v : R3 → R3} (hv : ContDiff ℝ ∞ v) (k : Fin 3) :
    ContDiff ℝ ∞ (fun y ↦ curl3 v y k) := by
  simp_rw [curl3_coord]
  exact (Lit3.newton3_poisson_aux_pdSmooth _ (contDiff_coord hv _) _).sub
    (Lit3.newton3_poisson_aux_pdSmooth _ (contDiff_coord hv _) _)

theorem contDiff_curl3 {v : R3 → R3} (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (curl3 v) :=
  contDiff_euclidean.mpr fun k ↦ contDiff_curl3_coord hv k

theorem curl3_eq_zero_of_notMem_tsupport {v : R3 → R3} {x : R3} (hx : x ∉ tsupport v) :
    curl3 v x = 0 := by
  have hk : ∀ k : Fin 3, x ∉ tsupport (fun y ↦ v y k) := fun k h ↦
    hx (tsupport_comp_subset (g := fun z : R3 ↦ z k) rfl v h)
  ext k
  rw [curl3_coord, Lit3.newton3_poisson_aux_pdZero _ x (hk _) _,
    Lit3.newton3_poisson_aux_pdZero _ x (hk _) _]
  simp

theorem tsupport_curl3_subset (v : R3 → R3) : tsupport (curl3 v) ⊆ tsupport v :=
  closure_minimal (fun x hx ↦ by
    by_contra h
    exact hx (curl3_eq_zero_of_notMem_tsupport h)) (isClosed_tsupport v)

theorem hasCompactSupport_curl3 {v : R3 → R3} (hc : HasCompactSupport v) :
    HasCompactSupport (curl3 v) :=
  IsCompact.of_isClosed_subset hc (isClosed_tsupport _) (tsupport_curl3_subset v)

/-! ### The Newtonian potential: linearity, commutation, and Green's identity -/

theorem newton3_fun_sub {F G : R3 → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hG : Continuous G) (hGc : HasCompactSupport G) (x : R3) :
    newton3 (fun y ↦ F y - G y) x = newton3 F x - newton3 G x := by
  have iF := (G3_locallyIntegrable.2.2.2.2 F hF hFc x).1
  have iG := (G3_locallyIntegrable.2.2.2.2 G hG hGc x).1
  simp only [newton3, mul_sub]
  exact integral_sub iF iG

theorem pd3_newton3 {F : R3 → ℝ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (i : Fin 3) (x : R3) : pd3 i (newton3 F) x = newton3 (pd3 i F) x := by
  simpa only [iterPartial3] using (Lit3.newton3_smooth F hF hc).2 [i] x

/-- Green's representation for smooth compactly supported functions. -/
theorem newton3_laplacian {F : R3 → ℝ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (x : R3) : newton3 (fun y ↦ Δ F y) x = F x := by
  change ∫ y, G3 (x - y) * Δ F y = F x
  rw [← Lit3.newton3_poisson_aux_lapNewton F hF hc x, Lit3.newton3_poisson F hF hc x]

/-! ### Biot–Savart reconstruction of a compactly supported velocity -/

/-- The curl–curl identity for one component of a smooth divergence-free field. -/
theorem curlCurl_coord {v : R3 → R3} (hv : ContDiff ℝ ∞ v) (hdiv : ∀ x, div3 v x = 0)
    (j : Fin 3) (y : R3) :
    pd3 (j + 2) (fun z ↦ curl3 v z (j + 1)) y - pd3 (j + 1) (fun z ↦ curl3 v z (j + 2)) y =
      Δ (fun z ↦ v z j) y := by
  have hvs : ∀ k, ContDiff ℝ ∞ (fun z ↦ v z k) := contDiff_coord hv
  have hdp : ∀ k l, Differentiable ℝ (pd3 l (fun z ↦ v z k)) := fun k l ↦
    differentiable_pd3 (hvs k) l
  have e1 : (fun z ↦ curl3 v z (j + 1)) =
      fun z ↦ pd3 (j + 2) (fun w ↦ v w j) z - pd3 j (fun w ↦ v w (j + 2)) z := by
    funext z
    rw [curl3_coord, fin3_add_one_add_one, fin3_add_one_add_two]
  have e2 : (fun z ↦ curl3 v z (j + 2)) =
      fun z ↦ pd3 j (fun w ↦ v w (j + 1)) z - pd3 (j + 1) (fun w ↦ v w j) z := by
    funext z
    rw [curl3_coord, fin3_add_two_add_one, fin3_add_two_add_two]
  have hdivFun : div3 v = fun z ↦ pd3 j (fun w ↦ v w j) z +
      pd3 (j + 1) (fun w ↦ v w (j + 1)) z + pd3 (j + 2) (fun w ↦ v w (j + 2)) z := by
    funext z
    exact fin3_sum_rotate j (fun i ↦ pd3 i (fun w ↦ v w i) z)
  have hd0 : pd3 j (div3 v) y = 0 := by
    have hzero : div3 v = fun _ ↦ 0 := funext hdiv
    rw [hzero]
    simp [pd3]
  have hd : pd3 j (div3 v) y = pd3 j (pd3 j (fun w ↦ v w j)) y +
      pd3 j (pd3 (j + 1) (fun w ↦ v w (j + 1))) y +
      pd3 j (pd3 (j + 2) (fun w ↦ v w (j + 2))) y := by
    rw [hdivFun, pd3_fun_add ((hdp _ _ y).fun_add (hdp _ _ y)) (hdp _ _ y),
      pd3_fun_add (hdp _ _ y) (hdp _ _ y)]
  rw [e1, e2, pd3_fun_sub (hdp _ _ y) (hdp _ _ y), pd3_fun_sub (hdp _ _ y) (hdp _ _ y),
    Lit3.newton3_poisson_aux_lap _ (hvs j) y, fin3_sum_rotate j]
  have c1 := pd3_comm (hvs (j + 2)) (j + 2) j y
  have c2 := pd3_comm (hvs (j + 1)) (j + 1) j y
  linarith

/-- **Biot–Savart reconstruction.** A smooth, compactly supported,
divergence-free field is the imported Biot–Savart velocity of its curl. -/
theorem biotSavart3_curl3 {v : R3 → R3} (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hdiv : ∀ x, div3 v x = 0) (x : R3) : biotSavart3 (curl3 v) x = v x := by
  have hωs : ∀ k, ContDiff ℝ ∞ (fun y ↦ curl3 v y k) := contDiff_curl3_coord hv
  have hωc : ∀ k, HasCompactSupport (fun y ↦ curl3 v y k) := fun k ↦
    hasCompactSupport_coord (hasCompactSupport_curl3 hc) k
  have hpc : ∀ k l, Continuous (pd3 l (fun y ↦ curl3 v y k)) := fun k l ↦
    (Lit3.newton3_poisson_aux_pdSmooth _ (hωs k) l).continuous
  have hps : ∀ k l, HasCompactSupport (pd3 l (fun y ↦ curl3 v y k)) := fun k l ↦
    Lit3.newton3_poisson_aux_pdSupp _ (hωc k) l
  ext j
  change WholeSpaceBiotSavart.velocity (curl3 v) x j = v x j
  rw [WholeSpaceBiotSavart.velocity_apply, pd3_newton3 (hωs _) (hωc _),
    pd3_newton3 (hωs _) (hωc _)]
  have hsub := newton3_fun_sub (hpc (j + 1) (j + 2)) (hps (j + 1) (j + 2))
    (hpc (j + 2) (j + 1)) (hps (j + 2) (j + 1)) x
  have hcc : (fun y ↦ pd3 (j + 2) (fun z ↦ curl3 v z (j + 1)) y -
      pd3 (j + 1) (fun z ↦ curl3 v z (j + 2)) y) = fun y ↦ Δ (fun z ↦ v z j) y :=
    funext (curlCurl_coord hv hdiv j)
  rw [hcc, newton3_laplacian (contDiff_coord hv j) (hasCompactSupport_coord hc j)] at hsub
  linarith

/-- The reconstruction in explicit kernel form. -/
theorem coord_eq_kernel {v : R3 → R3} (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hdiv : ∀ x, div3 v x = 0) (x : R3) (j : Fin 3) :
    v x j = -(∫ y, gradG3 (x - y) (j + 1) * curl3 v y (j + 2)) +
      ∫ y, gradG3 (x - y) (j + 2) * curl3 v y (j + 1) := by
  have hωs : ∀ k, ContDiff ℝ ∞ (fun y ↦ curl3 v y k) := contDiff_curl3_coord hv
  have hωc : ∀ k, HasCompactSupport (fun y ↦ curl3 v y k) := fun k ↦
    hasCompactSupport_coord (hasCompactSupport_curl3 hc) k
  rw [← biotSavart3_curl3 hv hc hdiv x]
  change WholeSpaceBiotSavart.velocity (curl3 v) x j = _
  rw [WholeSpaceBiotSavart.velocity_apply,
    Lit3.newton3_kernel_deriv _ (hωs (j + 2)) (hωc (j + 2)),
    Lit3.newton3_kernel_deriv _ (hωs (j + 1)) (hωc (j + 1))]

/-! ### The kernel and its local integrability -/

theorem norm_gradG3 (z : R3) : ‖gradG3 z‖ = (4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [gradG3]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [gradG3, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.rpow_neg hn.le, Real.rpow_two]
    field_simp

theorem measurable_gradG3 : Measurable gradG3 := by
  unfold gradG3
  fun_prop

/-- The `q`-th power of the kernel norm is locally integrable when `2q < 3`. -/
theorem locallyIntegrable_norm_gradG3_rpow {q : ℝ} (hq3 : 2 * q < 3) :
    LocallyIntegrable (fun z : R3 ↦ ‖gradG3 z‖ ^ q) volume := by
  refine locallyIntegrable_of_norm_le_rpow (C := (4 * Real.pi)⁻¹ ^ q) (α := 2 * q)
    (by simp) (by simpa using hq3) (Eventually.of_forall fun z ↦ ?_)
    ((measurable_gradG3.norm.pow_const q).aestronglyMeasurable)
  rw [norm_gradG3, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (norm_nonneg _)]
  ring_nf
  exact le_rfl

/-! ### Pointwise control by an `L^p` vorticity moment -/

theorem integrable_kernel_mul {F : R3 → ℝ} (hF : Continuous F) (hc : HasCompactSupport F)
    (x : R3) : Integrable (fun y ↦ ‖gradG3 (x - y)‖ * F y) := by
  have hloc : LocallyIntegrable (fun z : R3 ↦ ‖gradG3 z‖) volume := by
    simpa using locallyIntegrable_norm_gradG3_rpow (q := 1) (by norm_num)
  have h := hc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hF hloc x
  simpa [ConvolutionExistsAt, mul_comm] using h

/-- Each velocity component is controlled by the kernel integral of the
vorticity norm. -/
theorem abs_coord_le {v : R3 → R3} (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hdiv : ∀ x, div3 v x = 0) (x : R3) (j : Fin 3) :
    |v x j| ≤ 2 * ∫ y, ‖gradG3 (x - y)‖ * ‖curl3 v y‖ := by
  have hint := integrable_kernel_mul (contDiff_curl3 hv).continuous.norm
    (hasCompactSupport_curl3 hc).norm x
  have hbd : ∀ k m : Fin 3, |∫ y, gradG3 (x - y) k * curl3 v y m| ≤
      ∫ y, ‖gradG3 (x - y)‖ * ‖curl3 v y‖ := by
    intro k m
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun y ↦ ?_)
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _) (norm_nonneg _)
      (norm_nonneg _)
  rw [coord_eq_kernel hv hc hdiv x j]
  have h1 := hbd (j + 1) (j + 2)
  have h2 := hbd (j + 2) (j + 1)
  have htri := abs_add_le (-(∫ y, gradG3 (x - y) (j + 1) * curl3 v y (j + 2)))
    (∫ y, gradG3 (x - y) (j + 2) * curl3 v y (j + 1))
  rw [abs_neg] at htri
  linarith

theorem norm_le_two_mul_of_coord_le {w : R3} {A : ℝ} (h : ∀ j, |w j| ≤ A) :
    ‖w‖ ≤ 2 * A := by
  have hA : 0 ≤ A := (abs_nonneg _).trans (h 0)
  have hsq : ∀ j, ‖w j‖ ^ 2 ≤ A ^ 2 := fun j ↦ by
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h j) 2
  have hs : ∑ j, ‖w j‖ ^ 2 ≤ (2 * A) ^ 2 := by
    rw [Fin.sum_univ_three]
    nlinarith [hsq 0, hsq 1, hsq 2]
  rw [EuclideanSpace.norm_eq]
  calc √(∑ j, ‖w j‖ ^ 2) ≤ √((2 * A) ^ 2) := Real.sqrt_le_sqrt hs
    _ = 2 * A := Real.sqrt_sq (by positivity)

/-- The kernel exponent conjugate to `p > 3`. -/
theorem kernel_exponent {p : ℝ} (hp : 3 < p) :
    (p / (p - 1)).HolderConjugate p ∧ 0 < p / (p - 1) ∧ 2 * (p / (p - 1)) < 3 := by
  have hp1 : 1 < p := by linarith
  refine ⟨?_, div_pos (by linarith) (by linarith), ?_⟩
  · exact (Real.HolderConjugate.conjExponent hp1).symm
  · rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    linarith

/-- **Hölder step.** For a compact set `K` and exponents `q, p` with
`2q < 3`, one constant bounds the kernel integral of every nonnegative
continuous weight vanishing outside `K`, at every point of `K`. -/
theorem kernel_integral_le {K : Set R3} (hK : IsCompact K) {p q : ℝ}
    (hpq : q.HolderConjugate p) (hq3 : 2 * q < 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ g : R3 → ℝ, Continuous g → (∀ y, 0 ≤ g y) →
      (∀ y ∉ K, g y = 0) →
        ∫ y, ‖gradG3 (x - y)‖ * g y ≤ C * (∫ y, g y ^ p) ^ (1 / p) := by
  have hq0 : 0 < q := hpq.pos
  set D : ℝ := Metric.diam K
  set k : R3 → ℝ := fun z ↦ ‖gradG3 z‖ ^ q with hk
  have hkloc : LocallyIntegrable k volume := locallyIntegrable_norm_gradG3_rpow hq3
  have hkball : Integrable ((closedBall (0 : R3) D).indicator k) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (hkloc.integrableOn_isCompact (isCompact_closedBall 0 D))
  set I : ℝ := ∫ z, (closedBall (0 : R3) D).indicator k z
  refine ⟨I ^ (1 / q), Real.rpow_nonneg (integral_nonneg fun z ↦
    indicator_nonneg (fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) z) _, ?_⟩
  intro x hx g hg hg0 hgK
  have hgc : HasCompactSupport g := HasCompactSupport.intro hK hgK
  set f : R3 → ℝ := K.indicator (fun y ↦ ‖gradG3 (x - y)‖) with hf
  have hfmeas : Measurable f :=
    ((measurable_gradG3.comp (measurable_const.sub measurable_id)).norm).indicator
      hK.measurableSet
  have hmaj : Integrable (fun y ↦ (closedBall (0 : R3) D).indicator k (x - y)) :=
    hkball.comp_sub_left x
  have hpt : ∀ y, ‖f y‖ ^ q ≤ (closedBall (0 : R3) D).indicator k (x - y) := by
    intro y
    by_cases hy : y ∈ K
    · have hball : x - y ∈ closedBall (0 : R3) D := by
        rw [mem_closedBall, dist_zero_right, ← dist_eq_norm]
        exact Metric.dist_le_diam_of_mem hK.isBounded hx hy
      simp [f, hy, hball, k]
    · simp only [f, indicator_of_notMem hy, norm_zero]
      rw [Real.zero_rpow hq0.ne']
      exact indicator_nonneg (fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _
  have hfq : Integrable (fun y ↦ ‖f y‖ ^ q) :=
    hmaj.mono' ((hfmeas.norm.pow_const q).aestronglyMeasurable)
      (Eventually.of_forall fun y ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        exact hpt y)
  have hfLp : MemLp f (ENNReal.ofReal q) volume := by
    refine (integrable_norm_rpow_iff hfmeas.aestronglyMeasurable
      (by simpa using hq0) ENNReal.ofReal_ne_top).mp ?_
    simpa [ENNReal.toReal_ofReal hq0.le] using hfq
  have hgLp : MemLp g (ENNReal.ofReal p) volume := hg.memLp_of_hasCompactSupport hgc
  have hfg : ∫ y, ‖gradG3 (x - y)‖ * g y = ∫ y, f y * g y := by
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    by_cases hy : y ∈ K
    · simp [f, hy]
    · simp [f, hy, hgK y hy]
  have hf0 : ∀ y, 0 ≤ f y := fun y ↦ indicator_nonneg (fun _ _ ↦ norm_nonneg _) y
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall hf0) (Eventually.of_forall hg0) hfLp hgLp
  have hIq : ∫ y, f y ^ q ≤ I := by
    calc ∫ y, f y ^ q = ∫ y, ‖f y‖ ^ q := by
          refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
          simp only [Real.norm_eq_abs, abs_of_nonneg (hf0 y)]
      _ ≤ ∫ y, (closedBall (0 : R3) D).indicator k (x - y) :=
          integral_mono hfq hmaj hpt
      _ = I := integral_sub_left_eq_self _ volume x
  have hroot : (∫ y, f y ^ q) ^ (1 / q) ≤ I ^ (1 / q) :=
    Real.rpow_le_rpow (integral_nonneg fun y ↦ Real.rpow_nonneg (hf0 y) _) hIq
      (by positivity)
  have hgp : 0 ≤ (∫ y, g y ^ p) ^ (1 / p) :=
    Real.rpow_nonneg (integral_nonneg fun y ↦ Real.rpow_nonneg (hg0 y) _) _
  rw [hfg]
  exact hholder.trans (mul_le_mul_of_nonneg_right hroot hgp)

/-- **Pointwise control.** For a compact `K` and `p > 3`, one constant
bounds every smooth divergence-free velocity supported in `K` by its
vorticity `L^p` moment. -/
theorem norm_le_vorticity_moment {K : Set R3} (hK : IsCompact K) {p : ℝ} (hp : 3 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : R3 → R3, ContDiff ℝ ∞ v → tsupport v ⊆ K →
      (∀ x, div3 v x = 0) → ∀ x, ‖v x‖ ≤ C * (∫ y, ‖curl3 v y‖ ^ p) ^ (1 / p) := by
  obtain ⟨hpq, -, hq3⟩ := kernel_exponent hp
  obtain ⟨C, hC0, hC⟩ := kernel_integral_le hK hpq hq3
  refine ⟨4 * C, by positivity, fun v hv hsupp hdiv x ↦ ?_⟩
  have hc : HasCompactSupport v := IsCompact.of_isClosed_subset hK (isClosed_tsupport v) hsupp
  have hE : 0 ≤ (∫ y, ‖curl3 v y‖ ^ p) ^ (1 / p) :=
    Real.rpow_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _
  by_cases hx : x ∈ K
  · have hω0 : ∀ y ∉ K, ‖curl3 v y‖ = 0 := fun y hy ↦ by
      rw [curl3_eq_zero_of_notMem_tsupport (fun h ↦ hy (hsupp h)), norm_zero]
    have hk := hC x hx (fun y ↦ ‖curl3 v y‖) (contDiff_curl3 hv).continuous.norm
      (fun _ ↦ norm_nonneg _) hω0
    have hcomp : ∀ j, |v x j| ≤ 2 * (C * (∫ y, ‖curl3 v y‖ ^ p) ^ (1 / p)) := fun j ↦
      (abs_coord_le hv hc hdiv x j).trans (by linarith)
    have := norm_le_two_mul_of_coord_le hcomp
    linarith
  · rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hsupp h)), norm_zero]
    exact mul_nonneg (by positivity) hE

/-! ### The forced candidates of OpenAI's Theorem 1.1 -/

section Candidates

open NavierStokesR3.ProblemStatement

/-- Spatial slices strictly between the initial and singular times are smooth. -/
theorem slice_contDiff {u : VelocityField} (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : ContDiff ℝ ∞ (fun y : Space ↦ u (t, y)) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have hmem : preSingularDomain ∈ 𝓝 ((t, y) : SpaceTime) :=
    Filter.mem_of_superset ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ y⟩)
      (prod_mono Ioo_subset_Ico_self subset_rfl)
  exact (hu.contDiffAt hmem).comp y (contDiffAt_const.prodMk contDiffAt_id)

/-- The imported divergence agrees with the divergence of the problem statement. -/
theorem div3_slice_eq {u : VelocityField} {t : ℝ} {x : Space}
    (hd : DifferentiableAt ℝ (fun y : Space ↦ u (t, y)) x) :
    div3 (fun y ↦ u (t, y)) x = NavierStokes.ProblemStatement.spatialDivergence u t x := by
  unfold div3 NavierStokes.ProblemStatement.spatialDivergence
    NavierStokes.ProblemStatement.spatialDerivative
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact fderiv_coord_apply hd i (e3 i)

/-- **Every whole-space forced candidate has unbounded vorticity moments.**
For `p > 3`, `∫ ‖curl u(t)‖^p` is unbounded for `0 < t < 1`. -/
theorem candidate_vorticityMoment_unbounded {ν : ℝ} {u : VelocityField}
    {pr : PressureField} {f : VelocityField} {K : Set Space}
    (h : CandidateProperties ν u pr f K) {p : ℝ} (hp : 3 < p) :
    ¬ BddAbove ((fun t ↦ ∫ x, ‖curl3 (fun y ↦ u (t, y)) x‖ ^ p) '' Ioo 0 1) := by
  rintro ⟨B, hB⟩
  obtain ⟨C, hC0, hC⟩ := norm_le_vorticity_moment h.support_compact hp
  have hM : 0 < C * max B 0 ^ (1 / p) + 1 :=
    add_pos_of_nonneg_of_pos (mul_nonneg hC0 (Real.rpow_nonneg (le_max_right _ _) _)) one_pos
  obtain ⟨t, x, ht, -, hlt⟩ := h.speed_unbounded _ hM 1 one_pos
  have hsmooth := slice_contDiff h.velocity_smooth ht
  have hsupp : tsupport (fun y ↦ u (t, y)) ⊆ K :=
    h.velocity_support t (Ioo_subset_Ico_self ht)
  have hdiv : ∀ y, div3 (fun y ↦ u (t, y)) y = 0 := fun y ↦ by
    rw [div3_slice_eq ((hsmooth.differentiable (by simp)) y)]
    exact h.divergence_free t (Ioo_subset_Ico_self ht) y
  have hE0 : 0 ≤ ∫ y, ‖curl3 (fun y ↦ u (t, y)) y‖ ^ p :=
    integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hE : ∫ y, ‖curl3 (fun y ↦ u (t, y)) y‖ ^ p ≤ max B 0 :=
    (hB ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  have hroot := Real.rpow_le_rpow (z := 1 / p) hE0 hE (one_div_nonneg.mpr (by linarith))
  have hbound : ‖u (t, x)‖ ≤ C * (∫ y, ‖curl3 (fun y ↦ u (t, y)) y‖ ^ p) ^ (1 / p) :=
    hC _ hsmooth hsupp hdiv x
  have hmul := mul_le_mul_of_nonneg_left hroot hC0
  linarith

/-- The eighth vorticity moment of every forced candidate is unbounded
before its singular time. -/
theorem candidate_eighthVorticityMoment_unbounded {ν : ℝ} {u : VelocityField}
    {pr : PressureField} {f : VelocityField} {K : Set Space}
    (h : CandidateProperties ν u pr f K) :
    ¬ BddAbove ((fun t ↦ ∫ x, ‖curl3 (fun y ↦ u (t, y)) x‖ ^ (8 : ℕ)) '' Ioo 0 1) := by
  have h8 := candidate_vorticityMoment_unbounded h (p := 8) (by norm_num)
  have hfun : (fun t ↦ ∫ x, ‖curl3 (fun y ↦ u (t, y)) x‖ ^ (8 : ℕ)) =
      fun t ↦ ∫ x, ‖curl3 (fun y ↦ u (t, y)) x‖ ^ (8 : ℝ) := by
    funext t
    congr 1
    funext x
    exact (Real.rpow_natCast _ 8).symm
  rw [hfun]
  exact h8

end Candidates

end Mettapedia.FluidDynamics.NavierStokes.ForcedCandidateVorticity
