import Mathlib.Analysis.Calculus.FDeriv.Partial
import MettapediaNS.WholeSpaceTimeSmooth

/-!
# Space-time smoothness of the smooth Navier–Stokes evolutions on `ℝ³`

A path of smooth `L²` fields over `[0, T]` defines a function of space and time. When the
path has a time derivative, this function has a derivative within `ℝ³ × [0, T]` at every
point, up to the endpoints: its spatial part is the actual spatial derivative, continuous
jointly in space and time by Sobolev embedding, and its time part is the value of the time
derivative. In coordinates the derivative is built from the three directional derivative
paths and the time-derivative path, which are again smooth in time. Induction on the order
then shows that the function of a path with time derivatives of every order is smooth on
`ℝ³ × [0, T]`, in the sense of derivatives within that set.

Applied to a smooth Navier–Stokes evolution, the velocity and the pressure force are
`C^∞` functions of space and time on `ℝ³ × [0, T]`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceTimeSmooth

open Set Filter MeasureTheory Asymptotics
open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerMeanSobolevBoundedField Finset
open scoped Topology ContDiff

/-- The derivative of a smooth field, in terms of its coordinate directional derivatives. -/
theorem fderiv_eq_sum_directional (A : SmoothL2Field Space) (x v : Space) :
    fderiv ℝ A.field x v = ∑ i : Fin 3, v i • (A.directionalField (axis i)).field x := by
  have ha : (∑ i : Fin 3, v i • axis i) = v := by
    ext j
    simp [axis, Pi.single_apply, mul_ite]
  simpa only [directionalField_field, map_sum, map_smul] using
    (congrArg (fderiv ℝ A.field x) ha).symm

variable {T : ℝ} (hT : 0 ≤ T)

/-- The function of space and time defined by a path of fields (constant in time outside
`[0, T]`). -/
def joint (A : FieldPath T) (p : Space × ℝ) : Space := (A (projIcc 0 T hT p.2)).field p.1

theorem joint_continuous {A : FieldPath T} (hA : JetContinuous A) : Continuous (joint hT A) := by
  have h : Continuous (fun p : Space × ℝ ↦ finiteField (A (projIcc 0 T hT p.2))) :=
    (continuous_finiteField A hA).comp (continuous_projIcc.comp continuous_snd)
  change Continuous (fun p : Space × ℝ ↦ (A (projIcc 0 T hT p.2)).field p.1)
  simpa only [finiteField_apply] using h.eval continuous_fst

theorem jointDeriv_continuous {A : FieldPath T} (hA : JetContinuous A) :
    Continuous (fun p : Space × ℝ ↦ fderiv ℝ (A (projIcc 0 T hT p.2)).field p.1) := by
  have h : Continuous (fun p : Space × ℝ ↦ finiteField (A (projIcc 0 T hT p.2)).derivative) :=
    (continuous_finiteField (fun t ↦ (A t).derivative) (continuous_jetLp_derivative A hA)).comp
      (continuous_projIcc.comp continuous_snd)
  have h' := h.eval continuous_fst
  simp only [finiteField_apply] at h'
  exact h'

/-- **The space-time derivative within `ℝ³ × [0, T]`**, including at the endpoints. -/
theorem hasFDerivWithinAt_joint {A B : FieldPath T} (h : TimeDeriv hT A B) (p : Space × ℝ)
    (hp : p.2 ∈ Icc (0 : ℝ) T) :
    HasFDerivWithinAt (joint hT A)
      ((fderiv ℝ (A ⟨p.2, hp⟩).field p.1).comp (ContinuousLinearMap.fst ℝ Space ℝ) +
        (ContinuousLinearMap.snd ℝ Space ℝ).smulRight ((B ⟨p.2, hp⟩).field p.1))
      (univ ×ˢ Icc (0 : ℝ) T) p := by
  obtain ⟨x, t⟩ := p
  change t ∈ Icc (0 : ℝ) T at hp
  have hproj : projIcc 0 T hT t = ⟨t, hp⟩ := projIcc_of_mem hT hp
  -- the spatial increment at the moving time, by the mean value inequality
  have hsp : (fun χ : Space × ℝ ↦ (A (projIcc 0 T hT χ.2)).field χ.1 -
      (A (projIcc 0 T hT χ.2)).field x - fderiv ℝ (A ⟨t, hp⟩).field x (χ.1 - x))
        =o[𝓝[univ ×ˢ Icc (0 : ℝ) T] (x, t)] (fun χ ↦ χ.1 - x) := by
    rw [isLittleO_iff]
    intro ε hε
    have hG := (jointDeriv_continuous hT h.left).continuousAt (x := (x, t))
    rw [Metric.continuousAt_iff] at hG
    obtain ⟨δ, hδ, hball⟩ := hG ε hε
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (x, t) hδ)] with χ hχ
    have hχ' : dist χ (x, t) < δ := Metric.mem_ball.mp hχ
    rw [Prod.dist_eq] at hχ'
    have hbound : ∀ z ∈ Metric.ball x δ, ‖fderiv ℝ (A (projIcc 0 T hT χ.2)).field z -
        fderiv ℝ (A ⟨t, hp⟩).field x‖ ≤ ε := by
      intro z hz
      have hq : dist (z, χ.2) (x, t) < δ := by
        rw [Prod.dist_eq]
        exact max_lt (Metric.mem_ball.mp hz) (lt_of_le_of_lt (le_max_right _ _) hχ')
      have hd := hball hq
      simp only [hproj, dist_eq_norm] at hd
      exact hd.le
    have hy : χ.1 ∈ Metric.ball x δ :=
      Metric.mem_ball.mpr (lt_of_le_of_lt (le_max_left _ _) hχ')
    exact (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun z _ ↦ ((A (projIcc 0 T hT χ.2)).smooth.differentiable (by simp)
        z).hasFDerivAt.hasFDerivWithinAt) hbound (Metric.mem_ball_self hδ) hy
  -- the time increment at the fixed point
  have hsnd : Tendsto (fun χ : Space × ℝ ↦ χ.2) (𝓝[univ ×ˢ Icc (0 : ℝ) T] (x, t))
      (𝓝[Icc (0 : ℝ) T] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨(continuous_snd.tendsto (x, t)).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun χ hχ ↦ hχ.2⟩
  have htime := (hasDerivWithinAt_iff_isLittleO.mp (h.within ⟨t, hp⟩ x)).comp_tendsto hsnd
  -- comparison with the full increment
  have h1 : (fun χ : Space × ℝ ↦ χ.1 - x) =O[𝓝[univ ×ˢ Icc (0 : ℝ) T] (x, t)]
      (fun χ ↦ χ - (x, t)) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun χ ↦ by simpa using norm_fst_le (χ - (x, t)))
  have h2 : (fun χ : Space × ℝ ↦ χ.2 - t) =O[𝓝[univ ×ˢ Icc (0 : ℝ) T] (x, t)]
      (fun χ ↦ χ - (x, t)) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun χ ↦ by simpa using norm_snd_le (χ - (x, t)))
  have hsum := (hsp.trans_isBigO h1).add (htime.trans_isBigO h2)
  rw [hasFDerivWithinAt_iff_isLittleO]
  refine hsum.congr_left fun χ ↦ ?_
  simp only [joint, Function.comp_apply, add_apply,
    ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd', Prod.fst_sub, Prod.snd_sub, hproj]
  abel

/-- The space-time derivative in terms of the coordinate directional derivative paths and the
time-derivative path. -/
def jointDeriv (A B : FieldPath T) (p : Space × ℝ) : Space × ℝ →L[ℝ] Space :=
  (∑ i : Fin 3, ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
      (ContinuousLinearMap.fst ℝ Space ℝ)).smulRight
        (joint hT (fun t ↦ (A t).directionalField (axis i)) p)) +
    (ContinuousLinearMap.snd ℝ Space ℝ).smulRight (joint hT B p)

theorem jointDeriv_eq (A B : FieldPath T) (p : Space × ℝ) (hp : p.2 ∈ Icc (0 : ℝ) T) :
    (fderiv ℝ (A ⟨p.2, hp⟩).field p.1).comp (ContinuousLinearMap.fst ℝ Space ℝ) +
        (ContinuousLinearMap.snd ℝ Space ℝ).smulRight ((B ⟨p.2, hp⟩).field p.1) =
      jointDeriv hT A B p := by
  have hproj : projIcc 0 T hT p.2 = ⟨p.2, hp⟩ := projIcc_of_mem hT hp
  refine ContinuousLinearMap.ext fun q ↦ ?_
  simp only [jointDeriv, joint, hproj, add_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd',
    FunLike.coe_sum, Finset.sum_apply, fderiv_eq_sum_directional]
  rfl

/-- **Space-time smoothness to every finite order.** -/
theorem contDiffOn_joint (hpos : 0 < T) :
    ∀ (n : ℕ) (A : FieldPath T), IsTimeSmooth hT A →
      ContDiffOn ℝ n (joint hT A) (univ ×ˢ Icc (0 : ℝ) T)
  | 0, A, h => by
      rw [Nat.cast_zero, contDiffOn_zero]
      exact (joint_continuous hT (h 0).jetContinuous).continuousOn
  | n + 1, A, h => by
      obtain ⟨B, hAB, hB⟩ := h.exists_deriv hpos
      have hs : UniqueDiffOn ℝ (univ ×ˢ Icc (0 : ℝ) T) :=
        (uniqueDiffOn_univ : UniqueDiffOn ℝ (univ : Set Space)).prod (uniqueDiffOn_Icc hpos)
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hcast, contDiffOn_succ_iff_fderivWithin hs]
      refine ⟨fun p hp ↦ (hasFDerivWithinAt_joint hT hAB p hp.2).differentiableWithinAt,
        fun hω ↦ by simp at hω, ?_⟩
      have hderiv : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) T,
          fderivWithin ℝ (joint hT A) (univ ×ˢ Icc (0 : ℝ) T) p = jointDeriv hT A B p := by
        intro p hp
        rw [(hasFDerivWithinAt_joint hT hAB p hp.2).fderivWithin (hs p hp)]
        exact jointDeriv_eq hT A B p hp.2
      apply ContDiffOn.congr _ hderiv
      apply ContDiffOn.add
      · apply ContDiffOn.sum
        intro i _
        exact contDiffOn_const.smulRight (contDiffOn_joint hpos n _ (h.directional i))
      · exact contDiffOn_const.smulRight (contDiffOn_joint hpos n B hB)

/-- **Space-time smoothness.** A path with time derivatives of every order defines a `C^∞`
function of space and time on `ℝ³ × [0, T]`. -/
theorem contDiffOn_joint_infty (hpos : 0 < T) {A : FieldPath T} (h : IsTimeSmooth hT A) :
    ContDiffOn ℝ ∞ (joint hT A) (univ ×ˢ Icc (0 : ℝ) T) :=
  contDiffOn_infty.mpr fun n ↦ contDiffOn_joint hT hpos n A h

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceTimeSmooth

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow.NSEvolution

open Set WholeSpaceTimeSmooth
open scoped ContDiff

variable {ν T : ℝ} {hT : 0 ≤ T}

/-- **The velocity is `C^∞` in space and time** on `ℝ³ × [0, T]`. -/
theorem velocity_contDiffOn (U : NSEvolution ν T hT) (hpos : 0 < T) :
    ContDiffOn ℝ ∞ (joint hT U.velocity) (univ ×ˢ Icc (0 : ℝ) T) :=
  contDiffOn_joint_infty hT hpos (U.isTimeSmooth hpos)

/-- **The pressure force is `C^∞` in space and time** on `ℝ³ × [0, T]`. -/
theorem pressure_contDiffOn (U : NSEvolution ν T hT) (hpos : 0 < T) :
    ContDiffOn ℝ ∞ (joint hT U.pressureForce) (univ ×ˢ Icc (0 : ℝ) T) :=
  contDiffOn_joint_infty hT hpos (U.pressure_isTimeSmooth hpos)

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow.NSEvolution
