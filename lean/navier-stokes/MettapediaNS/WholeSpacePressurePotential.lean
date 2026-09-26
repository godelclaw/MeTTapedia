import Euler.MeanPressurePotential
import MettapediaNS.WholeSpaceJointSmooth

/-!
# The scalar pressure of the smooth Navier–Stokes evolutions on `ℝ³`

The pressure force of a smooth evolution is a gradient at every time, and so is its time
derivative, since the gradient fields form a closed subspace of `L²`. The upstream radial
potential `x ↦ ∫₀¹ ⟪G(s x), x⟫ ds` of a smooth gradient field is a smooth scalar whose
gradient is the field. As a function of space and time it has a derivative within
`ℝ³ × [0, T]` at every point: in space it is the field, in time it is the radial potential
of the time derivative, paid uniformly on the radial segment by the mean value inequality.
Induction on the order gives a `C^∞` scalar pressure on `ℝ³ × [0, T]`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceTimeSmooth

open Set Filter MeasureTheory Asymptotics InnerProductSpace
open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerMeanSolenoidal EulerMeanSobolevBoundedField EulerCanonicalGraphPotential
open scoped Topology ContDiff RealInnerProductSpace Interval

theorem fderiv_eq_toDual_gradient (f : Space → ℝ) (x : Space) :
    fderiv ℝ f x = toDual ℝ Space (gradient f x) := by
  rw [gradient, LinearIsometryEquiv.apply_symm_apply]

variable {T : ℝ} (hT : 0 ≤ T)

/-- Every value of the path is a gradient field. -/
def GradientPath (G : FieldPath T) : Prop := ∀ t, (G t).toLp ∈ gradientSpace

/-- The time derivative of a gradient path is a gradient path. -/
theorem GradientPath.deriv (hpos : 0 < T) {G G' : FieldPath T} (hG : GradientPath G)
    (h : TimeDeriv hT G G') : GradientPath G' := by
  have hint : ∀ t (ht : t ∈ Ioo 0 T), (G' ⟨t, ht.1.le, ht.2.le⟩).toLp ∈ gradientSpace := by
    intro t ht
    have hs := hasDerivAt_iff_tendsto_slope.mp (h.toLp t ht)
    apply gradientSpace_closed.mem_of_tendsto hs
    apply Eventually.of_forall
    intro r
    rw [slope_def_module]
    exact gradientSpace.smul_mem _ (gradientSpace.sub_mem (hG _) (hG _))
  intro t
  have hf : Continuous (fun r : ℝ ↦ (G' (projIcc 0 T hT r)).toLp) :=
    (continuous_toLp G' (h.right 0)).comp continuous_projIcc
  have hmem : (t : ℝ) ∈ closure (Ioo (0 : ℝ) T) := by
    rw [closure_Ioo hpos.ne]
    exact t.property
  have hmaps : MapsTo (fun r : ℝ ↦ (G' (projIcc 0 T hT r)).toLp) (Ioo 0 T)
      (gradientSpace : Set L2) := by
    intro r hr
    change (G' (projIcc 0 T hT r)).toLp ∈ gradientSpace
    rw [projIcc_of_mem hT ⟨hr.1.le, hr.2.le⟩]
    exact hint r hr
  have hcl := map_mem_closure hf hmem hmaps
  rw [gradientSpace_closed.closure_eq] at hcl
  simpa only [projIcc_val, SetLike.mem_coe] using hcl

/-- The radial potential of a path, as a function of space and time. -/
def potential (G : FieldPath T) (p : Space × ℝ) : ℝ :=
  radialPotential (G (projIcc 0 T hT p.2)).field p.1

theorem potential_spec {G : FieldPath T} (hG : GradientPath G) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (radialPotential (G t).field) ∧
      ∀ x, gradient (radialPotential (G t).field) x = (G t).field x := by
  have h := EulerMeanPressure.gradientSpace_radial_potential (G t).toLp (hG t) (G t).field
    (G t).toLp_ae (G t).smooth
  exact ⟨h.1, h.2.2⟩

/-- The time derivative of the potential at a fixed point, within `[0, T]`. -/
theorem potential_hasDerivWithinAt {G G' : FieldPath T} (h : TimeDeriv hT G G') (x : Space)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun τ ↦ potential hT G (x, τ)) (potential hT G' (x, t)) (Icc 0 T) t := by
  rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have hK : IsCompact (((fun s : ℝ ↦ s • x) '' Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) T) :=
    (isCompact_Icc.image (continuous_id.smul continuous_const)).prod isCompact_Icc
  have huc := hK.uniformContinuousOn_of_continuous (joint_continuous hT h.right).continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  have hx1 : 0 < ‖x‖ + 1 := by positivity
  obtain ⟨δ, hδ, hδK⟩ := huc (ε / (‖x‖ + 1)) (div_pos hε hx1)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t hδ), self_mem_nhdsWithin]
    with τ hτ hτI
  -- the pointwise estimate on the radial segment
  have hpt : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖joint hT G (s • x, τ) - joint hT G (s • x, t) - (τ - t) • joint hT G' (s • x, t)‖ ≤
        ε / (‖x‖ + 1) * ‖τ - t‖ := by
    intro s hs
    set S := Icc (0 : ℝ) T ∩ Metric.ball t δ with hS
    have hSc : Convex ℝ S := (convex_Icc 0 T).inter (convex_ball t δ)
    have hd : ∀ r ∈ S, HasDerivWithinAt
        (fun r ↦ joint hT G (s • x, r) - (r - t) • joint hT G' (s • x, t))
        (joint hT G' (s • x, r) - joint hT G' (s • x, t)) S r := by
      intro r hr
      have hsub : S ⊆ Icc (0 : ℝ) T := fun r hr ↦ hr.1
      have h1 := (h.within ⟨r, hr.1⟩ (s • x)).mono hsub
      have h2 := (((hasDerivAt_id' (x := r)).hasDerivWithinAt (s := S)).sub_const t).smul_const
        (joint hT G' (s • x, t))
      have he : joint hT G' (s • x, r) = (G' ⟨r, hr.1⟩).field (s • x) := by
        simp only [joint, projIcc_of_mem hT hr.1]
      rw [he]
      simpa only [one_smul, joint] using h1.fun_sub h2
    have hb : ∀ r ∈ S, ‖joint hT G' (s • x, r) - joint hT G' (s • x, t)‖ ≤ ε / (‖x‖ + 1) := by
      intro r hr
      have hmem1 : (s • x, r) ∈ ((fun s : ℝ ↦ s • x) '' Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) T :=
        ⟨⟨s, hs, rfl⟩, hr.1⟩
      have hmem2 : (s • x, t) ∈ ((fun s : ℝ ↦ s • x) '' Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) T :=
        ⟨⟨s, hs, rfl⟩, ht⟩
      have hdist : dist (s • x, r) (s • x, t) < δ := by
        rw [Prod.dist_eq, dist_self]
        exact max_lt hδ (Metric.mem_ball.mp hr.2)
      rw [← dist_eq_norm]
      exact (hδK _ hmem1 _ hmem2 hdist).le
    have hτS : τ ∈ S := ⟨hτI, hτ⟩
    have htS : t ∈ S := ⟨ht, Metric.mem_ball_self hδ⟩
    have hmvt := hSc.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb htS hτS
    have heq : (joint hT G (s • x, τ) - (τ - t) • joint hT G' (s • x, t)) -
        (joint hT G (s • x, t) - (t - t) • joint hT G' (s • x, t)) =
        joint hT G (s • x, τ) - joint hT G (s • x, t) - (τ - t) • joint hT G' (s • x, t) := by
      rw [sub_self, zero_smul, sub_zero]
      abel
    rw [← heq]
    exact hmvt
  -- integrate over the segment
  have hcont (A : FieldPath T) (hA : JetContinuous A) (r : ℝ) :
      Continuous (fun s : ℝ ↦ ⟪joint hT A (s • x, r), x⟫_ℝ) :=
    ((joint_continuous hT hA).comp ((continuous_id.smul continuous_const).prodMk
      continuous_const)).inner continuous_const
  have hint (A : FieldPath T) (hA : JetContinuous A) (r : ℝ) :
      IntervalIntegrable (fun s : ℝ ↦ ⟪joint hT A (s • x, r), x⟫_ℝ) volume 0 1 :=
    (hcont A hA r).intervalIntegrable 0 1
  have hid : potential hT G (x, τ) - potential hT G (x, t) - (τ - t) • potential hT G' (x, t) =
      ∫ s in (0 : ℝ)..1, (⟪joint hT G (s • x, τ), x⟫_ℝ - ⟪joint hT G (s • x, t), x⟫_ℝ -
        (τ - t) * ⟪joint hT G' (s • x, t), x⟫_ℝ) := by
    rw [intervalIntegral.integral_sub ((hint G h.left τ).sub (hint G h.left t))
        ((hint G' h.right t).const_mul (τ - t)),
      intervalIntegral.integral_sub (hint G h.left τ) (hint G h.left t),
      intervalIntegral.integral_const_mul, smul_eq_mul]
    rfl
  rw [hid]
  have hbound : ∀ s ∈ Ι (0 : ℝ) 1,
      ‖⟪joint hT G (s • x, τ), x⟫_ℝ - ⟪joint hT G (s • x, t), x⟫_ℝ -
          (τ - t) * ⟪joint hT G' (s • x, t), x⟫_ℝ‖ ≤ ε / (‖x‖ + 1) * ‖τ - t‖ * ‖x‖ := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at hs
      exact ⟨hs.1.le, hs.2⟩
    have he : ⟪joint hT G (s • x, τ), x⟫_ℝ - ⟪joint hT G (s • x, t), x⟫_ℝ -
        (τ - t) * ⟪joint hT G' (s • x, t), x⟫_ℝ =
        ⟪joint hT G (s • x, τ) - joint hT G (s • x, t) - (τ - t) • joint hT G' (s • x, t), x⟫_ℝ := by
      rw [inner_sub_left, inner_sub_left, real_inner_smul_left]
    rw [he]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hpt s hs') (norm_nonneg x))
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  refine hI.trans ?_
  have hle : ε / (‖x‖ + 1) * ‖x‖ ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hx1]
    nlinarith [norm_nonneg x]
  calc ε / (‖x‖ + 1) * ‖τ - t‖ * ‖x‖ * |(1 : ℝ) - 0|
      = ε / (‖x‖ + 1) * ‖x‖ * ‖τ - t‖ := by rw [sub_zero, abs_one, mul_one]; ring
    _ ≤ ε * ‖τ - t‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-- **The space-time derivative of the potential within `ℝ³ × [0, T]`.** -/
theorem hasFDerivWithinAt_potential {G G' : FieldPath T} (hG : GradientPath G)
    (h : TimeDeriv hT G G') (p : Space × ℝ) (hp : p.2 ∈ Icc (0 : ℝ) T) :
    HasFDerivWithinAt (potential hT G)
      ((toDual ℝ Space ((G ⟨p.2, hp⟩).field p.1) : Space →L[ℝ] ℝ).comp
          (ContinuousLinearMap.fst ℝ Space ℝ) +
        (ContinuousLinearMap.snd ℝ Space ℝ).smulRight (potential hT G' p))
      (univ ×ˢ Icc (0 : ℝ) T) p := by
  obtain ⟨x, t⟩ := p
  change t ∈ Icc (0 : ℝ) T at hp
  have hproj : projIcc 0 T hT t = ⟨t, hp⟩ := projIcc_of_mem hT hp
  have hfd (τ : ℝ) (z : Space) :
      fderiv ℝ (radialPotential (G (projIcc 0 T hT τ)).field) z =
        toDual ℝ Space ((G (projIcc 0 T hT τ)).field z) := by
    rw [fderiv_eq_toDual_gradient, (potential_spec hG _).2 z]
  have hdc : Continuous (fun q : Space × ℝ ↦
      (toDual ℝ Space ((G (projIcc 0 T hT q.2)).field q.1) : Space →L[ℝ] ℝ)) :=
    (toDual ℝ Space).continuous.comp (joint_continuous hT h.left)
  have hsp : (fun χ : Space × ℝ ↦ radialPotential (G (projIcc 0 T hT χ.2)).field χ.1 -
      radialPotential (G (projIcc 0 T hT χ.2)).field x -
        (toDual ℝ Space ((G ⟨t, hp⟩).field x) : Space →L[ℝ] ℝ) (χ.1 - x))
        =o[𝓝[univ ×ˢ Icc (0 : ℝ) T] (x, t)] (fun χ ↦ χ.1 - x) := by
    rw [isLittleO_iff]
    intro ε hε
    have hC := hdc.continuousAt (x := (x, t))
    rw [Metric.continuousAt_iff] at hC
    obtain ⟨δ, hδ, hball⟩ := hC ε hε
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (x, t) hδ)] with χ hχ
    have hχ' : dist χ (x, t) < δ := Metric.mem_ball.mp hχ
    rw [Prod.dist_eq] at hχ'
    have hbound : ∀ z ∈ Metric.ball x δ, ‖fderiv ℝ (radialPotential (G (projIcc 0 T hT χ.2)).field) z -
        (toDual ℝ Space ((G ⟨t, hp⟩).field x) : Space →L[ℝ] ℝ)‖ ≤ ε := by
      intro z hz
      have hq : dist (z, χ.2) (x, t) < δ := by
        rw [Prod.dist_eq]
        exact max_lt (Metric.mem_ball.mp hz) (lt_of_le_of_lt (le_max_right _ _) hχ')
      have hd := hball hq
      simp only [hproj, dist_eq_norm] at hd
      rw [hfd]
      exact hd.le
    have hy : χ.1 ∈ Metric.ball x δ :=
      Metric.mem_ball.mpr (lt_of_le_of_lt (le_max_left _ _) hχ')
    exact (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun z _ ↦ (((potential_spec hG _).1.differentiable (by simp))
        z).hasFDerivAt.hasFDerivWithinAt) hbound (Metric.mem_ball_self hδ) hy
  have hsnd : Tendsto (fun χ : Space × ℝ ↦ χ.2) (𝓝[univ ×ˢ Icc (0 : ℝ) T] (x, t))
      (𝓝[Icc (0 : ℝ) T] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨(continuous_snd.tendsto (x, t)).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun χ hχ ↦ hχ.2⟩
  have htime := (hasDerivWithinAt_iff_isLittleO.mp
    (potential_hasDerivWithinAt hT h x t hp)).comp_tendsto hsnd
  have h1 : (fun χ : Space × ℝ ↦ χ.1 - x) =O[𝓝[univ ×ˢ Icc (0 : ℝ) T] (x, t)]
      (fun χ ↦ χ - (x, t)) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun χ ↦ by simpa using norm_fst_le (χ - (x, t)))
  have h2 : (fun χ : Space × ℝ ↦ χ.2 - t) =O[𝓝[univ ×ˢ Icc (0 : ℝ) T] (x, t)]
      (fun χ ↦ χ - (x, t)) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun χ ↦ by simpa using norm_snd_le (χ - (x, t)))
  have hsum := (hsp.trans_isBigO h1).add (htime.trans_isBigO h2)
  rw [hasFDerivWithinAt_iff_isLittleO]
  refine hsum.congr_left fun χ ↦ ?_
  simp only [potential, Function.comp_apply, add_apply, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd', Prod.fst_sub, Prod.snd_sub, hproj, smul_eq_mul]
  ring

/-- **Space-time smoothness of the potential to every finite order.** -/
theorem contDiffOn_potential (hpos : 0 < T) :
    ∀ (n : ℕ) (G : FieldPath T), GradientPath G → IsTimeSmooth hT G →
      ContDiffOn ℝ n (potential hT G) (univ ×ˢ Icc (0 : ℝ) T)
  | 0, G, hG, h => by
      obtain ⟨G', hGG', -⟩ := h.exists_deriv hpos
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun p hp ↦ (hasFDerivWithinAt_potential hT hG hGG' p hp.2).continuousWithinAt
  | n + 1, G, hG, h => by
      obtain ⟨G', hGG', hG'⟩ := h.exists_deriv hpos
      have hs : UniqueDiffOn ℝ (univ ×ˢ Icc (0 : ℝ) T) :=
        (uniqueDiffOn_univ : UniqueDiffOn ℝ (univ : Set Space)).prod (uniqueDiffOn_Icc hpos)
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hcast, contDiffOn_succ_iff_fderivWithin hs]
      refine ⟨fun p hp ↦ (hasFDerivWithinAt_potential hT hG hGG' p hp.2).differentiableWithinAt,
        fun hω ↦ by simp at hω, ?_⟩
      have hderiv : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) T,
          fderivWithin ℝ (potential hT G) (univ ×ˢ Icc (0 : ℝ) T) p =
            (toDual ℝ Space (joint hT G p) : Space →L[ℝ] ℝ).comp
                (ContinuousLinearMap.fst ℝ Space ℝ) +
              (ContinuousLinearMap.snd ℝ Space ℝ).smulRight (potential hT G' p) := by
        intro p hp
        rw [(hasFDerivWithinAt_potential hT hG hGG' p hp.2).fderivWithin (hs p hp)]
        simp only [joint, projIcc_of_mem hT hp.2]
      apply ContDiffOn.congr _ hderiv
      apply ContDiffOn.add
      · have hd : ContDiffOn ℝ n (fun p ↦ (toDual ℝ Space (joint hT G p) : Space →L[ℝ] ℝ))
            (univ ×ˢ Icc (0 : ℝ) T) :=
          (toDual ℝ Space).toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn
            ((contDiffOn_joint hT hpos n G h))
        exact hd.clm_comp contDiffOn_const
      · exact contDiffOn_const.smulRight
          (contDiffOn_potential hpos n G' (hG.deriv hT hpos hGG') hG')

theorem contDiffOn_potential_infty (hpos : 0 < T) {G : FieldPath T} (hG : GradientPath G)
    (h : IsTimeSmooth hT G) : ContDiffOn ℝ ∞ (potential hT G) (univ ×ˢ Icc (0 : ℝ) T) :=
  contDiffOn_infty.mpr fun n ↦ contDiffOn_potential hT hpos n G hG h

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceTimeSmooth

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow.NSEvolution

open Set EulerSmoothLimit WholeSpaceTimeSmooth
open scoped ContDiff

variable {ν T : ℝ} {hT : 0 ≤ T}

/-- **The scalar pressure is `C^∞` in space and time** on `ℝ³ × [0, T]`, and its spatial
gradient is the pressure force at every time. -/
theorem scalarPressure_contDiffOn (U : NSEvolution ν T hT) (hpos : 0 < T) :
    ContDiffOn ℝ ∞ (potential hT U.pressureForce) (univ ×ˢ Icc (0 : ℝ) T) :=
  contDiffOn_potential_infty hT hpos U.gradient (U.pressure_isTimeSmooth hpos)

theorem scalarPressure_gradient (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) (x : Space) :
    _root_.gradient (fun y ↦ potential hT U.pressureForce (y, t)) x =
      (U.pressureForce t).field x := by
  have h := (potential_spec U.gradient t).2 x
  simpa only [potential, projIcc_val] using h

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow.NSEvolution
