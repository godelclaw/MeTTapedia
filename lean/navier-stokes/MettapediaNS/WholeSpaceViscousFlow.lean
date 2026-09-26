import Euler.OrdinaryRegularizedFlow
import MettapediaNS.WholeSpaceViscousEnergy

/-!
# Regularized viscous flows on the whole space

The upstream smooth local theory for the Euler equations on `ℝ³` solves a
symmetric regularized equation `u' = B(u, u)` globally in `L²`, where the bounded
bilinear field `B` conserves the energy. This module adds viscosity.

An abstract flow `u' = B(u, u) + L u` with `⟪x, B x x⟫ = 0` and `⟪x, L x⟫ ≤ 0`
exists for all forward time (`exists_forward_viscous`). The quadratic term is
truncated by the retraction onto a ball; since `⟪x, B (c x) (c x)⟫ = c² ⟪x, B x x⟫ = 0`
for every scalar `c`, the truncated flow still loses energy everywhere, so its
forward orbit stays in the ball where the truncation is inactive.

For a smoothing operator `S`, the Laplacian of the smoothed field is a bounded
operator on `L²` (`SmoothingOperator.laplacian`), and the regularized viscous
term `ν S Δ S` dissipates energy: `⟪u, ν S Δ S u⟫ = -ν ∑ᵢ ‖∂ᵢ S u‖²`
(`SmoothingOperator.inner_viscous`). The regularized Navier–Stokes equation
therefore has a global forward `L²` solution whose energy never increases
(`SmoothingOperator.exists_forward_regularized`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap
open scoped Topology NNReal

/-! ## The abstract forward viscous flow -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The retraction onto the closed ball of radius `R`. -/
def retract (R : ℝ) (x : E) : E := (R / max R ‖x‖) • x

omit [CompleteSpace E] in
theorem retract_of_norm_le {R : ℝ} {x : E} (hx : ‖x‖ ≤ R) : retract R x = x := by
  have hR : 0 ≤ R := (norm_nonneg x).trans hx
  unfold retract
  rcases hR.eq_or_lt with h | h
  · have hx0 : x = 0 := norm_le_zero_iff.mp (h ▸ hx)
    simp [hx0]
  · rw [max_eq_left hx, div_self h.ne', one_smul]

omit [CompleteSpace E] in
theorem norm_retract_le {R : ℝ} (hR : 0 < R) (x : E) : ‖retract R x‖ ≤ R := by
  unfold retract
  have hm : 0 < max R ‖x‖ := lt_max_of_lt_left hR
  rw [norm_smul, Real.norm_of_nonneg (div_nonneg hR.le hm.le)]
  calc R / max R ‖x‖ * ‖x‖ ≤ R / max R ‖x‖ * max R ‖x‖ :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (div_nonneg hR.le hm.le)
    _ = R := div_mul_cancel₀ R hm.ne'

omit [CompleteSpace E] in
theorem lipschitzWith_retract {R : ℝ} (hR : 0 < R) : LipschitzWith 2 (retract R : E → E) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_two]
  have hmx : 0 < max R ‖x‖ := lt_max_of_lt_left hR
  have hmy : 0 < max R ‖y‖ := lt_max_of_lt_left hR
  have ha0 : 0 ≤ R / max R ‖x‖ := div_nonneg hR.le hmx.le
  have ha1 : R / max R ‖x‖ ≤ 1 := (div_le_one hmx).mpr (le_max_left _ _)
  have hsplit : retract R x - retract R y =
      (R / max R ‖x‖) • (x - y) + (R / max R ‖x‖ - R / max R ‖y‖) • y := by
    simp only [retract, smul_sub, sub_smul]
    abel
  rw [hsplit]
  have h1 : ‖(R / max R ‖x‖) • (x - y)‖ ≤ ‖x - y‖ := by
    rw [norm_smul, Real.norm_of_nonneg ha0]
    exact mul_le_of_le_one_left (norm_nonneg _) ha1
  have h2 : ‖(R / max R ‖x‖ - R / max R ‖y‖) • y‖ ≤ ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have e : (R / max R ‖x‖ - R / max R ‖y‖) * ‖y‖ =
        (R / max R ‖x‖) * (‖y‖ / max R ‖y‖) * (max R ‖y‖ - max R ‖x‖) := by
      field_simp
      try ring
    have hb0 : 0 ≤ ‖y‖ / max R ‖y‖ := div_nonneg (norm_nonneg _) hmy.le
    have hb1 : ‖y‖ / max R ‖y‖ ≤ 1 := (div_le_one hmy).mpr (le_max_right _ _)
    have hmax : |max R ‖y‖ - max R ‖x‖| ≤ ‖x - y‖ := by
      rw [max_comm R ‖y‖, max_comm R ‖x‖]
      refine (abs_max_sub_max_le_abs _ _ _).trans ?_
      rw [abs_sub_comm]
      exact abs_norm_sub_norm_le x y
    calc |R / max R ‖x‖ - R / max R ‖y‖| * ‖y‖ =
          |(R / max R ‖x‖ - R / max R ‖y‖) * ‖y‖| := by
          rw [abs_mul, abs_of_nonneg (norm_nonneg y)]
      _ = (R / max R ‖x‖) * (‖y‖ / max R ‖y‖) * |max R ‖y‖ - max R ‖x‖| := by
          rw [e, abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hb0]
      _ ≤ 1 * 1 * ‖x - y‖ := by gcongr
      _ = ‖x - y‖ := by ring
  linarith [norm_add_le ((R / max R ‖x‖) • (x - y)) ((R / max R ‖x‖ - R / max R ‖y‖) • y)]

omit [CompleteSpace E] in
theorem bilinear_norm_le (B : E →L[ℝ] E →L[ℝ] E) (x y : E) : ‖B x y‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ :=
  ((B x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg y))

/-- **The forward viscous flow.** A bounded quadratic field that conserves energy,
plus a bounded linear field that dissipates it, has a global forward flow along
which the norm never increases. -/
theorem exists_forward_viscous (B : E →L[ℝ] E →L[ℝ] E) (L : E →L[ℝ] E)
    (hB : ∀ x, ⟪x, B x x⟫_ℝ = 0) (hL : ∀ x, ⟪x, L x⟫_ℝ ≤ 0) (x₀ : E) :
    ∃ u : ℝ → E, u 0 = x₀ ∧ (∀ t, 0 ≤ t → HasDerivAt u (B (u t) (u t) + L (u t)) t) ∧
      ∀ t, 0 ≤ t → ‖u t‖ ≤ ‖x₀‖ := by
  set R := ‖x₀‖ + 1 with hRdef
  have hR : 0 < R := by positivity
  let F : E → E := fun x ↦ B (retract R x) (retract R x) + L x
  have hFlip : LipschitzWith ⟨4 * ‖B‖ * R + ‖L‖, by positivity⟩ F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    show ‖F x - F y‖ ≤ (4 * ‖B‖ * R + ‖L‖) * ‖x - y‖
    have hq : B (retract R x) (retract R x) - B (retract R y) (retract R y) =
        B (retract R x - retract R y) (retract R x) +
          B (retract R y) (retract R x - retract R y) := by
      simp only [map_sub, sub_apply]
      abel
    have hr := (lipschitzWith_retract (E := E) hR).dist_le_mul x y
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_two] at hr
    have hxR := norm_retract_le (E := E) hR x
    have hyR := norm_retract_le (E := E) hR y
    have hB0 := norm_nonneg B
    have hq1 : ‖B (retract R x - retract R y) (retract R x)‖ ≤ ‖B‖ * (2 * ‖x - y‖) * R :=
      (bilinear_norm_le B _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hr hB0) hxR
        (norm_nonneg _) (by positivity))
    have hq2 : ‖B (retract R y) (retract R x - retract R y)‖ ≤ ‖B‖ * R * (2 * ‖x - y‖) :=
      (bilinear_norm_le B _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hyR hB0) hr
        (norm_nonneg _) (by positivity))
    have hl : ‖L x - L y‖ ≤ ‖L‖ * ‖x - y‖ := by
      rw [← map_sub]
      exact L.le_opNorm _
    have hsplit : F x - F y = (B (retract R x - retract R y) (retract R x) +
        B (retract R y) (retract R x - retract R y)) + (L x - L y) := by
      simp only [F]
      rw [← hq]
      abel
    rw [hsplit]
    calc ‖(B (retract R x - retract R y) (retract R x) +
          B (retract R y) (retract R x - retract R y)) + (L x - L y)‖
        ≤ ‖B (retract R x - retract R y) (retract R x)‖ +
          ‖B (retract R y) (retract R x - retract R y)‖ + ‖L x - L y‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ ‖B‖ * (2 * ‖x - y‖) * R + ‖B‖ * R * (2 * ‖x - y‖) + ‖L‖ * ‖x - y‖ := by
          gcongr
      _ = (4 * ‖B‖ * R + ‖L‖) * ‖x - y‖ := by ring
  have hc : Continuous (Function.uncurry (fun _t : ℝ ↦ F)) := hFlip.continuous.comp continuous_snd
  obtain ⟨v, hv0, hv⟩ := EulerPacketExistence.exists_global_solution hc (fun _ ↦ hFlip) x₀
  -- the energy never increases, even for the truncated field
  have hscale : ∀ x : E, ⟪x, B (retract R x) (retract R x)⟫_ℝ = 0 := by
    intro x
    simp only [retract, map_smul, smul_apply, inner_smul_right, hB, mul_zero]
  have hd : ∀ t, HasDerivAt (fun s ↦ ‖v s‖ ^ 2) (2 * ⟪v t, L (v t)⟫_ℝ) t := by
    intro t
    have h := (hv t).norm_sq
    simpa only [F, inner_add_right, hscale, zero_add] using h
  have hanti : Antitone (fun s ↦ ‖v s‖ ^ 2) :=
    antitone_of_hasDerivAt_nonpos hd fun t ↦ by
      have := hL (v t)
      show 2 * ⟪v t, L (v t)⟫_ℝ ≤ 0
      linarith
  have hbound : ∀ t, 0 ≤ t → ‖v t‖ ≤ ‖x₀‖ := by
    intro t ht
    have h := hanti ht
    simp only [hv0] at h
    exact le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) h
  refine ⟨v, hv0, fun t ht ↦ ?_, hbound⟩
  have hin : retract R (v t) = v t := retract_of_norm_le ((hbound t ht).trans (by linarith))
  have h := hv t
  simp only [F, hin] at h
  exact h

end Abstract

/-! ## The regularized viscous term -/

section Regularized

open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerMeanSolenoidal WholeSpaceViscousEnergy Finset

/-- The two-letter derivative word `∂ᵢ∂ᵢ`. -/
def doubleWord (i : Fin 3) : Fin 2 → Fin 3 := fun _ ↦ i

theorem laplacianField_eq_sum_word (A : SmoothL2Field Space) :
    laplacianField A = sumField univ (fun i ↦ wordField A (doubleWord i)) := rfl

theorem toLp_laplacianField (A : SmoothL2Field Space) :
    (laplacianField A).toLp = ∑ i : Fin 3, (wordField A (doubleWord i)).toLp := by
  rw [laplacianField_eq_sum_word, toLp_sumField]

variable (S : SmoothingOperator)

/-- The Laplacian of the smoothed field, as a linear map on `L²`. -/
def laplacianLinear : L2 →ₗ[ℝ] L2 where
  toFun u := (laplacianField (S.field u)).toLp
  map_add' u v := by
    simp only [toLp_laplacianField, S.field_add, wordField_add, toLp_addField,
      Finset.sum_add_distrib]
  map_smul' c u := by
    simp only [toLp_laplacianField, S.field_smul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [EulerOrdinarySobolev.scaleField, wordField_map]
    exact EulerOrdinarySobolev.scaleField_toLp c _

theorem laplacianLinear_apply (u : L2) :
    laplacianLinear S u = (laplacianField (S.field u)).toLp := rfl

theorem laplacianLinear_bound (u : L2) :
    ‖laplacianLinear S u‖ ≤ 3 * ‖S.jetMap 2‖ * ‖u‖ := by
  rw [laplacianLinear_apply, toLp_laplacianField]
  calc ‖∑ i : Fin 3, (wordField (S.field u) (doubleWord i)).toLp‖
      ≤ ∑ i : Fin 3, ‖(wordField (S.field u) (doubleWord i)).toLp‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖S.jetMap 2‖ * ‖u‖ := by
        refine Finset.sum_le_sum fun i _ ↦ (wordField_toLp_norm_le _ _).trans ?_
        rw [S.field_jetLp]
        exact (S.jetMap 2).le_opNorm u
    _ = 3 * ‖S.jetMap 2‖ * ‖u‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- The Laplacian of the smoothed field, as a bounded operator on `L²`. -/
def laplacianOp : L2 →L[ℝ] L2 :=
  (laplacianLinear S).mkContinuous (3 * ‖S.jetMap 2‖) (laplacianLinear_bound S)

theorem laplacianOp_apply (u : L2) : laplacianOp S u = (laplacianField (S.field u)).toLp := rfl

/-- The regularized viscous term `ν S Δ S`. -/
def viscousOp (ν : ℝ) : L2 →L[ℝ] L2 := ν • (S.op.comp (laplacianOp S))

theorem viscousOp_apply (ν : ℝ) (u : L2) :
    viscousOp S ν u = ν • S.op (laplacianField (S.field u)).toLp := rfl

/-- **The regularized viscous term dissipates.**
`⟪u, ν S Δ S u⟫ = -ν ∑ᵢ ‖∂ᵢ S u‖²`. -/
theorem inner_viscousOp (ν : ℝ) (u : L2) :
    ⟪u, viscousOp S ν u⟫_ℝ =
      -ν * ∑ i : Fin 3, ‖((S.field u).directionalField (axis i)).toLp‖ ^ 2 := by
  rw [viscousOp_apply, inner_smul_right, real_inner_comm, S.symmetric, real_inner_comm,
    ← S.field_toLp u, inner_laplacianField]
  ring

theorem inner_viscousOp_nonpos {ν : ℝ} (hν : 0 ≤ ν) (u : L2) : ⟪u, viscousOp S ν u⟫_ℝ ≤ 0 := by
  rw [inner_viscousOp]
  have : 0 ≤ ∑ i : Fin 3, ‖((S.field u).directionalField (axis i)).toLp‖ ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  nlinarith

/-- **The regularized Navier–Stokes equation has a global forward solution** in `L²`,
whose energy never increases. -/
theorem exists_forward_regularized {ν : ℝ} (hν : 0 ≤ ν) (u₀ : L2) :
    ∃ u : ℝ → L2, u 0 = u₀ ∧
      (∀ t, 0 ≤ t → HasDerivAt u (S.quadratic (u t) (u t) + viscousOp S ν (u t)) t) ∧
      ∀ t, 0 ≤ t → ‖u t‖ ≤ ‖u₀‖ :=
  exists_forward_viscous S.quadratic (viscousOp S ν) S.quadratic_energy
    (inner_viscousOp_nonpos S hν) u₀

end Regularized

/-! ## Smooth regularized viscous evolutions -/

section Evolution

open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerMeanSolenoidal EulerVolterraConvolution EulerContinuousTimeIntegral WholeSpaceViscousEnergy

variable (S : SmoothingOperator)

/-- The viscous term as a smooth field. -/
def viscousField (ν : ℝ) (u : L2) : SmoothL2Field Space :=
  EulerOrdinarySobolev.scaleField ν (S.field (laplacianOp S u))

theorem viscousField_toLp (ν : ℝ) (u : L2) : (viscousField S ν u).toLp = viscousOp S ν u := by
  rw [viscousField, EulerOrdinarySobolev.scaleField_toLp, S.field_toLp]
  rfl

/-- The full right-hand side of the regularized Navier–Stokes equation, as a smooth field. -/
def viscousRhs (ν : ℝ) (u : L2) : SmoothL2Field Space := addField (S.rhs u) (viscousField S ν u)

theorem viscousRhs_toLp (ν : ℝ) (u : L2) :
    (viscousRhs S ν u).toLp = S.quadratic u u + viscousOp S ν u := by
  rw [viscousRhs, toLp_addField, S.rhs_toLp, viscousField_toLp]

theorem viscousRhs_continuous {K : Type*} [TopologicalSpace K] (ν : ℝ) (u : K → L2)
    (hu : Continuous u) (n : ℕ) : Continuous (fun t ↦ (viscousRhs S ν (u t)).jetLp n) := by
  apply continuous_jetLp_addField _ _ (S.rhs_continuous u hu)
  intro k
  exact continuous_jetLp_mapField (ν • ContinuousLinearMap.id ℝ Space)
    (fun t ↦ S.field (laplacianOp S (u t)))
    (S.field_jet_continuous _ ((laplacianOp S).continuous.comp hu)) k

/-- A smooth solution of the regularized Navier–Stokes equation on `[0, T]`. -/
structure RegularizedViscousEvolution (ν T : ℝ) (hT : 0 ≤ T) where
  velocity : Icc (0 : ℝ) T → SmoothL2Field Space
  velocity_continuous : ∀ n, Continuous (fun t ↦ (velocity t).jetLp n)
  solenoidal : ∀ t, (velocity t).toLp ∈ solenoidalSpace
  time_law : ∀ t (ht : t ∈ Ioo 0 T),
    HasDerivAt (fun r ↦ (velocity (projIcc 0 T hT r)).toLp)
      (S.quadratic (velocity ⟨t, ht.1.le, ht.2.le⟩).toLp (velocity ⟨t, ht.1.le, ht.2.le⟩).toLp +
        viscousOp S ν (velocity ⟨t, ht.1.le, ht.2.le⟩).toLp) t

/-- **Smooth regularized viscous evolutions exist** from every smooth solenoidal datum,
on every interval. The solution is the datum plus a smoothed time integral, so it keeps
every derivative in `L²`. -/
theorem exists_regularizedViscous {ν : ℝ} (hν : 0 ≤ ν) (T : ℝ) (hT : 0 ≤ T)
    (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    ∃ U : RegularizedViscousEvolution S ν T hT, U.velocity ⟨0, le_rfl, hT⟩ = A := by
  obtain ⟨u, hu0, hu, _⟩ := exists_forward_regularized S hν A.toLp
  have huc : ContinuousOn u (Ici 0) := fun t ht ↦ (hu t ht).continuousAt.continuousWithinAt
  have hucI : Continuous (fun t : Icc (0 : ℝ) T ↦ u t) :=
    huc.comp_continuous continuous_subtype_val fun t ↦ t.2.1
  let a : C(Icc (0 : ℝ) T, L2) :=
    ⟨fun t ↦ -S.advection (u t) (u t) + ν • laplacianOp S (u t),
      ((S.advection.continuous.comp hucI).clm_apply hucI).neg.add
        (((laplacianOp S).continuous.comp hucI).const_smul ν)⟩
  let z : C(Icc (0 : ℝ) T, L2) := EulerContinuousTimeIntegral.integral T hT a
  let v : Icc (0 : ℝ) T → SmoothL2Field Space := fun t ↦ addField A (S.field (z t))
  have hderiv : ∀ s : Icc (0 : ℝ) T,
      HasDerivWithinAt u ((S.op.compLeftContinuous ℝ (Icc (0 : ℝ) T) a) s) (Icc (0 : ℝ) T) s := by
    intro s
    refine ((hu s s.2.1).hasDerivWithinAt (s := Icc (0 : ℝ) T)).congr_deriv ?_
    show S.quadratic (u s) (u s) + viscousOp S ν (u s) =
      S.op (-S.advection (u s) (u s) + ν • laplacianOp S (u s))
    simp only [map_add, map_neg, map_smul, SmoothingOperator.quadratic_apply,
      SmoothingOperator.advection_apply, viscousOp_apply, laplacianOp_apply]
  have hv : ∀ t, (v t).toLp = u t := by
    intro t
    have he := eq_initial_add_integral T hT (S.op.compLeftContinuous ℝ (Icc (0 : ℝ) T) a) u
      hderiv t
    have hi : EulerContinuousTimeIntegral.integral T hT
        (S.op.compLeftContinuous ℝ (Icc (0 : ℝ) T) a) t = S.op (z t) := by
      change (∫ r in (0 : ℝ)..(t : ℝ), S.op (extendPath T hT a r)) = S.op (realIntegral T hT a t)
      rw [S.op.intervalIntegral_comp_comm ((extendPath_continuous T hT a).intervalIntegrable 0 t)]
      rfl
    rw [hu0, hi] at he
    simpa only [v, toLp_addField, S.field_toLp] using he.symm
  have hvcont : ∀ n, Continuous (fun t ↦ (v t).jetLp n) :=
    fun n ↦ continuous_jetLp_addField _ _ (fun _ ↦ continuous_const)
      (S.field_jet_continuous z z.continuous) n
  have hv0 : v ⟨0, le_rfl, hT⟩ = A := by
    apply smoothField_eq_of_toLp_eq
    rw [hv, hu0]
  refine ⟨{ velocity := v
            velocity_continuous := hvcont
            solenoidal := fun t ↦ ?_
            time_law := fun t ht ↦ ?_ }, hv0⟩
  · simpa only [v, toLp_addField, S.field_toLp] using
      solenoidalSpace.add_mem hA (S.solenoidal (z t))
  · simp only [hv]
    have he : (fun r ↦ u (projIcc 0 T hT r : ℝ)) =ᶠ[𝓝 t] u := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      simp only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1.le, hr.2.le⟩)]
    exact (hu t ht.1.le).congr_of_eventuallyEq he

end Evolution

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow
