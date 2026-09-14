import MettapediaNS.WholeSpaceBiotSavart

/-!
# Regularized Newtonian Hessians and singular-integral identification

The regularization, integration by parts, and potential convergence are
imported from Alpöge–Buckmaster. The results identify limits of actual
Hessian kernels, not merely formal derivatives away from the pole.
-/

noncomputable section

open MeasureTheory Filter Topology EulerSmoothLimit
open scoped ContDiff

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceBiotSavart

open EulerBlowup Ring3D

/-- Two integrations by parts, using the existing upstream theorem. -/
theorem integral_mul_partial_partial_eq {f g : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (i j : Fin 3) :
    (∫ y, g y * pd3 i (pd3 j f) y) = ∫ y, pd3 j (pd3 i g) y * f y := by
  have hfj := Lit3.newton3_poisson_aux_pdSmooth f hf j
  have hcfj := Lit3.newton3_poisson_aux_pdSupp f hc j
  have hgi := Lit3.newton3_poisson_aux_pdSmooth g hg i
  have h₁ := Lit3.newton3_poisson_aux_ibp (pd3 j f) g hfj hcfj hg i
  have h₂ := Lit3.newton3_poisson_aux_ibp f (pd3 i g) hf hc hgi j
  simp_rw [mul_comm (g _)]
  have h₃ : (∫ y, pd3 j f y * pd3 i g y) =
      ∫ y, pd3 i g y * pd3 j f y := by simp_rw [mul_comm]
  have h₄ : (∫ y, f y * pd3 j (pd3 i g) y) =
      ∫ y, pd3 j (pd3 i g) y * f y := by simp_rw [mul_comm]
  linarith

/-- The smooth regularized Hessian converges to the actual Newtonian
Hessian after integration against a smooth compactly supported source. -/
theorem tendsto_integral_regularizedHessian {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (i j : Fin 3) (x : Space) :
    Tendsto (fun δ : ℝ ↦ ∫ y, pd3 j (pd3 i (fun z ↦ Lit3.Gdelta δ (x - z))) y * f y)
      (𝓝[>] 0) (𝓝 (pd3 i (pd3 j (newton3 f)) x)) := by
  have hfj := Lit3.newton3_poisson_aux_pdSmooth f hf j
  have hcfj := Lit3.newton3_poisson_aux_pdSupp f hc j
  have hlim := Lit3.newton3_poisson_aux_tendsto_G (pd3 i (pd3 j f))
    (Lit3.newton3_poisson_aux_pdSmooth _ hfj i).continuous
    (Lit3.newton3_poisson_aux_pdSupp _ hcfj i) x
  have hcomm : pd3 i (pd3 j (newton3 f)) x =
      ∫ y, G3 (x - y) * pd3 i (pd3 j f) y := by
    simpa only [iterPartial3, newton3] using (Lit3.newton3_smooth f hf hc).2 [i, j] x
  rw [hcomm]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact integral_mul_partial_partial_eq hf hc
    (Lit3.newton3_poisson_aux_Gdelta_contDiff δ (ne_of_gt hδ) x) i j

/-- The mixed entries extend the upstream diagonal Hessian calculation;
the radial derivative and coordinate derivative are imported unchanged. -/
theorem regularizedHessian_apply (δ : ℝ) (hδ : δ ≠ 0)
    (i j : Fin 3) (x y : Space) :
    pd3 j (pd3 i (fun z ↦ Lit3.Gdelta δ (x - z))) y =
      (4 * Real.pi)⁻¹ *
        ((if i = j then 1 else 0) * (‖y - x‖ ^ 2 + δ ^ 2) ^ (-(3 / 2 : ℝ)) -
          3 * (y i - x i) * (y j - x j) *
            (‖y - x‖ ^ 2 + δ ^ 2) ^ (-(5 / 2 : ℝ))) := by
  rw [Lit3.newton3_poisson_aux_pdG δ hδ x i]
  have hne : ‖y - x‖ ^ 2 + δ ^ 2 ≠ 0 := by positivity
  have hp := (Lit3.newton3_poisson_aux_hasFDerivAt_s x δ y).rpow_const
    (p := -(3 / 2 : ℝ)) (Or.inl hne)
  have hd := (hp.fun_mul (Lit3.newton3_poisson_aux_hasFDerivAt_coord x i y)).const_mul
    ((4 * Real.pi)⁻¹)
  unfold pd3
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul,
    Lit3.newton3_poisson_aux_inner_e3, WithLp.ofLp_sub, Pi.sub_apply]
  have hcoord : (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (e3 j) =
      if i = j then 1 else 0 := by simp [e3]
  rw [hcoord]
  norm_num
  ring

/-- The bounded radial multiplier relating a regularized trace-free Hessian
to its homogeneous singular kernel. -/
def hessianMultiplier (δ : ℝ) (z : Space) : ℝ :=
  (‖z‖ / Real.sqrt (‖z‖ ^ 2 + δ ^ 2)) ^ 5

theorem hessianMultiplier_nonneg (δ : ℝ) (z : Space) : 0 ≤ hessianMultiplier δ z := by
  unfold hessianMultiplier
  positivity

theorem hessianMultiplier_le_one {δ : ℝ} (hδ : δ ≠ 0) (z : Space) :
    hessianMultiplier δ z ≤ 1 := by
  have hs : 0 < Real.sqrt (‖z‖ ^ 2 + δ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hle : ‖z‖ ≤ Real.sqrt (‖z‖ ^ 2 + δ ^ 2) := by
    calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])
  exact pow_le_one₀ (by positivity) ((div_le_one hs).mpr hle)

theorem continuous_hessianMultiplier {δ : ℝ} (hδ : δ ≠ 0) :
    Continuous (hessianMultiplier δ) := by
  unfold hessianMultiplier
  exact (continuous_norm.div
    ((continuous_norm.pow 2).add continuous_const).sqrt
    (fun z ↦ (Real.sqrt_pos.mpr
      (add_pos_of_nonneg_of_pos (sq_nonneg ‖z‖) (sq_pos_of_ne_zero hδ))).ne')).pow 5

theorem tendsto_hessianMultiplier {z : Space} (hz : z ≠ 0) :
    Tendsto (fun δ : ℝ ↦ hessianMultiplier δ z) (𝓝 0) (𝓝 1) := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hc : ContinuousAt (fun δ : ℝ ↦ hessianMultiplier δ z) 0 := by
    unfold hessianMultiplier
    apply ContinuousAt.pow
    exact continuousAt_const.div
      ((continuousAt_const.add (continuousAt_id.pow 2)).sqrt) (by simp [hn])
  simpa [hessianMultiplier, Real.sqrt_sq (norm_nonneg z), hn] using hc.tendsto

/-- Dominated convergence for the Newtonian regularization multiplier.
The integrable majorant is the original integrand itself. -/
theorem tendsto_integral_hessianMultiplier_mul {μ : Measure Space} [NullSingletonClass μ]
    {g : Space → ℂ} (hg : Integrable g μ) :
    Tendsto (fun δ : ℝ ↦ ∫ z, (hessianMultiplier δ z : ℂ) * g z ∂μ)
      (𝓝[>] 0) (𝓝 (∫ z, g z ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun z ↦ ‖g z‖) ?_ ?_
    hg.norm ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (Complex.continuous_ofReal.comp
      (continuous_hessianMultiplier (ne_of_gt hδ))).aestronglyMeasurable.mul hg.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ae_of_all μ fun z ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hessianMultiplier_nonneg δ z)]
      exact mul_le_of_le_one_left (norm_nonneg _) (hessianMultiplier_le_one (ne_of_gt hδ) z)
  · have hae : ∀ᵐ z ∂μ, z ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hae] with z hz
    have ht := (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_hessianMultiplier hz)).mul_const (g z)
    simpa using ht.mono_left nhdsWithin_le_nhds

/-- The regularization converges to the upstream principal value. Both
inner and outer integrability are supplied by its singular-integral theory. -/
theorem tendsto_regularizedPrincipalValue {L : ℝ} {Ω φ : Space → ℂ}
    (hΩ : NS.Lit.CZ.AngularPart L Ω) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (x : Space) :
    Tendsto (fun δ : ℝ ↦
      (∫ z in {z : Space | ‖z‖ < 1},
        (hessianMultiplier δ z : ℂ) * (NS.Lit.CZ.homKer Ω z * (φ (x - z) - φ x))) +
      ∫ z in {z : Space | 1 ≤ ‖z‖},
        (hessianMultiplier δ z : ℂ) * (NS.Lit.CZ.homKer Ω z * φ (x - z)))
      (𝓝[>] 0) (𝓝 (NS.Lit.CZ.pvOp Ω φ x)) :=
  (tendsto_integral_hessianMultiplier_mul (NS.Lit.CZ.integrableOn_pv_inner hΩ hφ hc x)).add
    (tendsto_integral_hessianMultiplier_mul (NS.Lit.CZ.integrableOn_pv_outer hΩ hφ hc x))

/-- Radial regularization preserves the cancellation at the pole. -/
theorem integral_ball_hessianMultiplier_homKer_eq_zero {Ω : Space → ℂ}
    (e : Space ≃ₗᵢ[ℝ] Space) (hΩ : ∀ z, Ω (e z) = -Ω z) (δ : ℝ) :
    ∫ z in {z : Space | ‖z‖ < 1},
      (hessianMultiplier δ z : ℂ) * NS.Lit.CZ.homKer Ω z = 0 := by
  exact Mettapedia.Analysis.QuadraticSingularIntegral.integral_radial_mul_homKer_eq_zero_of_isometry e hΩ
      (fun r ↦ ((r / Real.sqrt (r ^ 2 + δ ^ 2)) ^ 5 : ℝ)) (Set.Iio 1)

theorem hessianMultiplier_mul_coordinateProduct (δ : ℝ) (i j : Fin 3) (z : Space) :
    (hessianMultiplier δ z : ℂ) * NS.Lit.CZ.homKer
      (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateProduct i j) z =
      ((z i * z j / Real.sqrt (‖z‖ ^ 2 + δ ^ 2) ^ 5 : ℝ) : ℂ) := by
  rw [Mettapedia.Analysis.QuadraticSingularIntegral.homKer_coordinateProduct]
  rw [← Complex.ofReal_mul]
  congr 1
  by_cases hz : z = 0
  · simp [hz]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    unfold hessianMultiplier
    field_simp

theorem hessianMultiplier_mul_coordinateSquareDifference (δ : ℝ) (i j : Fin 3)
    (z : Space) :
    (hessianMultiplier δ z : ℂ) * NS.Lit.CZ.homKer
      (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateSquareDifference i j) z =
      (((z i ^ 2 - z j ^ 2) / Real.sqrt (‖z‖ ^ 2 + δ ^ 2) ^ 5 : ℝ) : ℂ) := by
  rw [Mettapedia.Analysis.QuadraticSingularIntegral.homKer_coordinateSquareDifference]
  rw [← Complex.ofReal_mul]
  congr 1
  by_cases hz : z = 0
  · simp [hz]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    unfold hessianMultiplier
    field_simp

/-- Cancellation removes the subtracted local source value, so the actual
regularized convolution has the same limit as the upstream principal value. -/
theorem tendsto_integral_regularizedKernel {L : ℝ} {Ω φ : Space → ℂ}
    (hΩ : NS.Lit.CZ.AngularPart L Ω) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (e : Space ≃ₗᵢ[ℝ] Space)
    (hodd : ∀ z, Ω (e z) = -Ω z)
    (hK : ∀ δ : ℝ, δ ≠ 0 → Continuous (fun z ↦
      (hessianMultiplier δ z : ℂ) * NS.Lit.CZ.homKer Ω z)) (x : Space) :
    Tendsto (fun δ : ℝ ↦ ∫ z,
      ((hessianMultiplier δ z : ℂ) * NS.Lit.CZ.homKer Ω z) * φ (x - z))
      (𝓝[>] 0) (𝓝 (NS.Lit.CZ.pvOp Ω φ x)) := by
  apply (tendsto_regularizedPrincipalValue hΩ hφ hc x).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  let K : Space → ℂ := fun z ↦ (hessianMultiplier δ z : ℂ) * NS.Lit.CZ.homKer Ω z
  have hKc : Continuous K := hK δ (ne_of_gt hδ)
  have hfull : Integrable (fun z ↦ K z * φ (x - z)) :=
    (hKc.mul (hφ.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      ((hc.comp_homeomorph (Homeomorph.subLeft x)).mul_left)
  have hs : MeasurableSet {z : Space | ‖z‖ < 1} :=
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have hlocal : IntegrableOn K {z : Space | ‖z‖ < 1} :=
    (hKc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Space) 1)).mono_set
      (fun z hz ↦ by simpa using le_of_lt hz)
  have hzero : ∫ z in {z : Space | ‖z‖ < 1}, K z = 0 :=
    integral_ball_hessianMultiplier_homKer_eq_zero e hodd δ
  have hsplit := integral_add_compl hs hfull
  have hsub := integral_sub hfull.integrableOn (hlocal.mul_const (φ x))
  rw [integral_mul_const, hzero, zero_mul, sub_zero] at hsub
  simp only [Set.compl_ofPred, not_lt] at hsplit
  change (∫ z in {z : Space | ‖z‖ < 1},
      (hessianMultiplier δ z : ℂ) * (NS.Lit.CZ.homKer Ω z * (φ (x - z) - φ x))) +
    (∫ z in {z : Space | 1 ≤ ‖z‖},
      (hessianMultiplier δ z : ℂ) * (NS.Lit.CZ.homKer Ω z * φ (x - z))) = _
  simp_rw [← mul_assoc]
  change (∫ z in {z : Space | ‖z‖ < 1}, K z * (φ (x - z) - φ x)) +
    (∫ z in {z : Space | 1 ≤ ‖z‖}, K z * φ (x - z)) = _
  simp_rw [mul_sub]
  rw [hsub]
  exact hsplit

private theorem rpow_neg_five_halves (s : ℝ) (hs : 0 ≤ s) :
    s ^ (-(5 / 2 : ℝ)) = (Real.sqrt s ^ 5)⁻¹ := by
  rw [Real.rpow_neg hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs]
  norm_num

theorem regularizedHessian_eq_coordinateProduct {δ : ℝ} (hδ : δ ≠ 0)
    (i j : Fin 3) (hij : i ≠ j) (x y : Space) :
    (pd3 j (pd3 i (fun z ↦ Lit3.Gdelta δ (x - z))) y : ℂ) =
      (-(3 / (4 * Real.pi) : ℝ) : ℂ) *
        ((hessianMultiplier δ (x - y) : ℂ) * NS.Lit.CZ.homKer
          (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateProduct i j) (x - y)) := by
  rw [hessianMultiplier_mul_coordinateProduct, ← Complex.ofReal_neg, ← Complex.ofReal_mul]
  congr 1
  rw [regularizedHessian_apply δ hδ, ite_eq_right hij,
    rpow_neg_five_halves _ (by positivity), norm_sub_rev]
  simp only [zero_mul, zero_sub, WithLp.ofLp_sub, Pi.sub_apply]
  ring

theorem regularizedHessian_sub_eq_coordinateSquareDifference {δ : ℝ} (hδ : δ ≠ 0)
    (i j : Fin 3) (x y : Space) :
    (pd3 i (pd3 i (fun z ↦ Lit3.Gdelta δ (x - z))) y -
      pd3 j (pd3 j (fun z ↦ Lit3.Gdelta δ (x - z))) y : ℂ) =
      (-(3 / (4 * Real.pi) : ℝ) : ℂ) *
        ((hessianMultiplier δ (x - y) : ℂ) * NS.Lit.CZ.homKer
          (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateSquareDifference i j) (x - y)) := by
  rw [hessianMultiplier_mul_coordinateSquareDifference, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  congr 1
  rw [regularizedHessian_apply δ hδ, regularizedHessian_apply δ hδ,
    rpow_neg_five_halves _ (by positivity), norm_sub_rev]
  simp only [ite_true, WithLp.ofLp_sub, Pi.sub_apply]
  ring

theorem continuous_regularizedKernel_coordinateProduct {δ : ℝ} (hδ : δ ≠ 0)
    (i j : Fin 3) : Continuous (fun z : Space ↦ (hessianMultiplier δ z : ℂ) *
      NS.Lit.CZ.homKer
        (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateProduct i j) z) := by
  simp_rw [hessianMultiplier_mul_coordinateProduct]
  apply Complex.continuous_ofReal.comp
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    exact pow_ne_zero 5 (Real.sqrt_pos.mpr
      (add_pos_of_nonneg_of_pos (sq_nonneg ‖z‖) (sq_pos_of_ne_zero hδ))).ne'

theorem continuous_regularizedKernel_coordinateSquareDifference {δ : ℝ} (hδ : δ ≠ 0)
    (i j : Fin 3) : Continuous (fun z : Space ↦ (hessianMultiplier δ z : ℂ) *
      NS.Lit.CZ.homKer
        (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateSquareDifference i j) z) := by
  simp_rw [hessianMultiplier_mul_coordinateSquareDifference]
  apply Complex.continuous_ofReal.comp
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    exact pow_ne_zero 5 (Real.sqrt_pos.mpr
      (add_pos_of_nonneg_of_pos (sq_nonneg ‖z‖) (sq_pos_of_ne_zero hδ))).ne'

/-- The actual off-diagonal Newtonian Hessian is the upstream principal-value
operator, with its normalization and sign fixed by the potential construction. -/
theorem newtonianHessian_eq_principalValue {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (i j : Fin 3) (hij : i ≠ j) (x : Space) :
    (pd3 i (pd3 j (newton3 f)) x : ℂ) =
      (-(3 / (4 * Real.pi) : ℝ) : ℂ) * NS.Lit.CZ.pvOp
        (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateProduct i j)
        (fun y ↦ (f y : ℂ)) x := by
  let Ω := Mettapedia.Analysis.QuadraticSingularIntegral.coordinateProduct i j
  obtain ⟨L, _, hΩ⟩ :=
    Mettapedia.Analysis.QuadraticSingularIntegral.exists_angularPart_coordinateProduct i j hij
  let e : Space ≃ₗᵢ[ℝ] Space := LinearIsometryEquiv.piLpCongrRight 2
    (fun k : Fin 3 ↦ if k = i then LinearIsometryEquiv.neg ℝ else .refl ℝ ℝ)
  have hodd (z : Space) : Ω (e z) = -Ω z := by
    simp [Ω, e, Mettapedia.Analysis.QuadraticSingularIntegral.coordinateProduct, hij.symm]
  have hφ : ContDiff ℝ ∞ (fun y ↦ (f y : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hcφ : HasCompactSupport (fun y ↦ (f y : ℂ)) :=
    hc.comp_left (g := fun r : ℝ ↦ (r : ℂ)) rfl
  have hpv := (tendsto_integral_regularizedKernel hΩ hφ hcφ e hodd
    (fun _ hδ ↦ continuous_regularizedKernel_coordinateProduct hδ i j) x).const_mul
      (-(3 / (4 * Real.pi) : ℝ) : ℂ)
  have hlim := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_integral_regularizedHessian hf hc i j x)
  apply tendsto_nhds_unique hlim
  apply hpv.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  simp only [Function.comp_apply]
  rw [← integral_complex_ofReal]
  simp_rw [Complex.ofReal_mul, regularizedHessian_eq_coordinateProduct (ne_of_gt hδ) i j hij,
    mul_assoc]
  rw [integral_const_mul]
  congr 1
  have h := integral_sub_left_eq_self
    (fun z : Space ↦ ((hessianMultiplier δ z : ℂ) * NS.Lit.CZ.homKer Ω z) *
      (f (x - z) : ℂ)) volume x
  simpa only [sub_sub_cancel, mul_assoc] using h.symm

theorem integrable_regularizedHessian {f : Space → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) {δ : ℝ} (hδ : δ ≠ 0)
    (i j : Fin 3) (x : Space) :
    Integrable (fun y ↦ pd3 j (pd3 i (fun z ↦ Lit3.Gdelta δ (x - z))) y * f y) := by
  have hg := Lit3.newton3_poisson_aux_Gdelta_contDiff δ hδ x
  have hi := Lit3.newton3_poisson_aux_pdSmooth _ hg i
  exact ((Lit3.newton3_poisson_aux_pdSmooth _ hi j).continuous.mul hf).integrable_of_hasCompactSupport
    hc.mul_left

/-- Differences of diagonal entries cancel the local isotropic term at
the pole and are represented by the second family of quadratic kernels. -/
theorem newtonianHessian_sub_eq_principalValue {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (i j : Fin 3) (x : Space) :
    (pd3 i (pd3 i (newton3 f)) x - pd3 j (pd3 j (newton3 f)) x : ℂ) =
      (-(3 / (4 * Real.pi) : ℝ) : ℂ) * NS.Lit.CZ.pvOp
        (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateSquareDifference i j)
        (fun y ↦ (f y : ℂ)) x := by
  let Ω := Mettapedia.Analysis.QuadraticSingularIntegral.coordinateSquareDifference i j
  obtain ⟨L, _, hΩ⟩ :=
    Mettapedia.Analysis.QuadraticSingularIntegral.exists_angularPart_coordinateSquareDifference i j
  let e : Space ≃ₗᵢ[ℝ] Space := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have hodd (z : Space) : Ω (e z) = -Ω z := by
    simp [Ω, e, Mettapedia.Analysis.QuadraticSingularIntegral.coordinateSquareDifference,
      Equiv.piCongrLeft', sub_eq_neg_add, add_comm]
  have hφ : ContDiff ℝ ∞ (fun y ↦ (f y : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hcφ : HasCompactSupport (fun y ↦ (f y : ℂ)) :=
    hc.comp_left (g := fun r : ℝ ↦ (r : ℂ)) rfl
  have hpv := (tendsto_integral_regularizedKernel hΩ hφ hcφ e hodd
    (fun _ hδ ↦ continuous_regularizedKernel_coordinateSquareDifference hδ i j) x).const_mul
      (-(3 / (4 * Real.pi) : ℝ) : ℂ)
  have hlim := Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((tendsto_integral_regularizedHessian hf hc i i x).sub
      (tendsto_integral_regularizedHessian hf hc j j x))
  rw [← Complex.ofReal_sub]
  apply tendsto_nhds_unique hlim
  apply hpv.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  simp only [Function.comp_apply]
  rw [← integral_sub (integrable_regularizedHessian hf.continuous hc (ne_of_gt hδ) i i x)
    (integrable_regularizedHessian hf.continuous hc (ne_of_gt hδ) j j x), ← integral_complex_ofReal]
  simp_rw [← sub_mul, Complex.ofReal_mul, Complex.ofReal_sub,
    regularizedHessian_sub_eq_coordinateSquareDifference (ne_of_gt hδ) i j, mul_assoc]
  rw [integral_const_mul]
  congr 1
  have h := integral_sub_left_eq_self
    (fun z : Space ↦ ((hessianMultiplier δ z : ℂ) * NS.Lit.CZ.homKer Ω z) *
      (f (x - z) : ℂ)) volume x
  simpa only [sub_sub_cancel, mul_assoc] using h.symm

/-- The imported singular-integral estimate now bounds an actual derivative
of the Newtonian potential, without differentiating its source. -/
theorem exists_eLpNorm_newtonianHessian_le (i j : Fin 3) (hij : i ≠ j)
    (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Space → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      eLpNorm (pd3 i (pd3 j (newton3 f))) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hb⟩ :=
    Mettapedia.Analysis.QuadraticSingularIntegral.exists_pv_eLpNorm_bound_coordinateProduct i j hij p hp
  have ha : 0 ≤ 3 / (4 * Real.pi) := by positivity
  refine ⟨3 / (4 * Real.pi) * C, mul_nonneg ha hC, ?_⟩
  intro f hf hc
  have hφ : ContDiff ℝ ∞ (fun y ↦ (f y : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hcφ := hc.comp_left (g := fun r : ℝ ↦ (r : ℂ)) rfl
  have hn : eLpNorm (fun y ↦ (f y : ℂ)) (ENNReal.ofReal p) volume =
      eLpNorm f (ENNReal.ofReal p) volume :=
    eLpNorm_congr_norm_ae (ae_of_all _ fun _ ↦ by simp)
  have hpoint : ∀ x, ‖pd3 i (pd3 j (newton3 f)) x‖ ≤ 3 / (4 * Real.pi) *
      ‖NS.Lit.CZ.pvOp (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateProduct i j)
        (fun y ↦ (f y : ℂ)) x‖ := by
    intro x
    rw [← Complex.norm_real (pd3 i (pd3 j (newton3 f)) x),
      newtonianHessian_eq_principalValue hf hc i j hij x,
      norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ha]
  have h := (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (ae_of_all volume hpoint) (ENNReal.ofReal p)).trans
    (mul_le_mul_right (hb _ hφ hcφ) (ENNReal.ofReal (3 / (4 * Real.pi))))
  simpa only [hn, ENNReal.ofReal_mul ha, mul_assoc] using h

theorem exists_eLpNorm_newtonianHessian_sub_le (i j : Fin 3) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Space → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      eLpNorm (fun x ↦ pd3 i (pd3 i (newton3 f)) x - pd3 j (pd3 j (newton3 f)) x)
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hb⟩ :=
    Mettapedia.Analysis.QuadraticSingularIntegral.exists_pv_eLpNorm_bound_coordinateSquareDifference i j p hp
  have ha : 0 ≤ 3 / (4 * Real.pi) := by positivity
  refine ⟨3 / (4 * Real.pi) * C, mul_nonneg ha hC, ?_⟩
  intro f hf hc
  have hφ : ContDiff ℝ ∞ (fun y ↦ (f y : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hcφ := hc.comp_left (g := fun r : ℝ ↦ (r : ℂ)) rfl
  have hn : eLpNorm (fun y ↦ (f y : ℂ)) (ENNReal.ofReal p) volume =
      eLpNorm f (ENNReal.ofReal p) volume :=
    eLpNorm_congr_norm_ae (ae_of_all _ fun _ ↦ by simp)
  have hpoint : ∀ x, ‖pd3 i (pd3 i (newton3 f)) x - pd3 j (pd3 j (newton3 f)) x‖ ≤
      3 / (4 * Real.pi) * ‖NS.Lit.CZ.pvOp
        (Mettapedia.Analysis.QuadraticSingularIntegral.coordinateSquareDifference i j)
        (fun y ↦ (f y : ℂ)) x‖ := by
    intro x
    rw [← Complex.norm_real (pd3 i (pd3 i (newton3 f)) x - pd3 j (pd3 j (newton3 f)) x),
      Complex.ofReal_sub, newtonianHessian_sub_eq_principalValue hf hc i j x,
      norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ha]
  have h := (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (ae_of_all volume hpoint) (ENNReal.ofReal p)).trans
    (mul_le_mul_right (hb _ hφ hcφ) (ENNReal.ofReal (3 / (4 * Real.pi))))
  simpa only [hn, ENNReal.ofReal_mul ha, mul_assoc] using h

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceBiotSavart
