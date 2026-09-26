import Euler.OrdinaryRegularizedFlow
import Euler.OrdinaryRegularizedEnergy
import Euler.OrdinaryRegularizedCauchy
import Euler.OrdinaryEulerLocalExistence
import Euler.OrdinaryGradientStability
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
(`exists_forward_regularized`), and smooth regularized evolutions exist from every
smooth solenoidal datum (`exists_regularizedViscous`).

The viscous term contributes `-2ν` times the dissipation of the smoothed field to
every integer-order energy production (`viscousField_production`), so the upstream
tame estimate bounds every Sobolev order on the upstream regularized Euler time,
uniformly in the smoothing and the viscosity (`regularizedViscous_all_order`). On
solenoidal fields `‖S Δ S A - Δ A‖ ≤ 6 ε M` (`viscous_error`), and the regularized
evolutions are Cauchy in continuous `L²` as the smoothing is removed
(`regularizedViscous_cauchy`). Along the upstream smooth limit the Laplacians
converge with the second-order word paths, the regularized derivatives converge to
`P(-(u·∇)u) + ν Δu`, and the limit satisfies the Navier–Stokes equations pointwise
with a constructed pressure (`nsEvolution`). Every smooth solenoidal field with all
derivatives in `L²` therefore starts a smooth Navier–Stokes evolution on `ℝ³`, for
every `ν ≥ 0`, on the regularized Euler time of its `H³` energy
(`exists_local_nsEvolution`).
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

/-! ## Uniform Sobolev bounds -/

section Energy

open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerMeanSolenoidal EulerMeanClassical EulerVolterraConvolution EulerContinuousTimeIntegral
  WholeSpaceViscousEnergy Finset

variable (S : SmoothingOperator)

/-- **The regularized viscous term dissipates at every order.** Its energy production
is minus twice the viscosity times the dissipation of the smoothed field. -/
theorem viscousField_production (m : ℕ) (ν : ℝ) (A : SmoothL2Field Space) :
    integerEnergyProduction m A (viscousField S ν A.toLp) =
      -2 * ν * wordDissipation m (S.field A.toLp) := by
  have hw : ∀ {n : ℕ} (w : Fin n → Fin 3),
      ⟪(wordField A w).toLp, (wordField (viscousField S ν A.toLp) w).toLp⟫_ℝ =
        ν * ⟪(wordField (S.field A.toLp) w).toLp,
          (wordField (laplacianField (S.field A.toLp)) w).toLp⟫_ℝ := by
    intro n w
    have e1 : wordField (viscousField S ν A.toLp) w =
        EulerOrdinarySobolev.scaleField ν (wordField (S.field (laplacianOp S A.toLp)) w) :=
      wordField_map _ _ _
    have e2 : (wordField (S.field (laplacianOp S A.toLp)) w).toLp =
        S.op (wordField (laplacianField (S.field A.toLp)) w).toLp := by
      rw [laplacianOp_apply]
      exact S.field_word _ w
    rw [e1, EulerOrdinarySobolev.scaleField_toLp, inner_smul_right, e2, ← S.symmetric,
      ← S.field_word A w]
  have hp := integerEnergyProduction_laplacianField m (S.field A.toLp)
  simp only [integerEnergyProduction, hw, ← mul_sum] at hp ⊢
  rw [mul_left_comm, hp]
  ring

/-- The full regularized right-hand side obeys the upstream tame bound. -/
theorem viscousRhs_energy (m : ℕ) (hm : 3 ≤ m) {ν : ℝ} (hν : 0 ≤ ν) (M : ℝ)
    (A : SmoothL2Field Space) (hM : WordBound 3 M A) :
    integerEnergyProduction m A (viscousRhs S ν A.toLp) ≤
      tameEnergyConstant m * M * wordEnergy m A := by
  have hsplit : integerEnergyProduction m A (viscousRhs S ν A.toLp) =
      integerEnergyProduction m A (S.rhs A.toLp) +
        integerEnergyProduction m A (viscousField S ν A.toLp) := by
    simp only [integerEnergyProduction, viscousRhs, wordField_add, toLp_addField,
      inner_add_right, sum_add_distrib]
    ring
  rw [hsplit, viscousField_production]
  have h1 := S.rhs_energy A m hm M hM
  have h2 := wordDissipation_nonneg m (S.field A.toLp)
  nlinarith [mul_nonneg hν h2]

namespace RegularizedViscousEvolution

variable {S} {ν T : ℝ} {hT : 0 ≤ T} (U : RegularizedViscousEvolution S ν T hT)

def derivative (t : Icc (0 : ℝ) T) : SmoothL2Field Space := viscousRhs S ν (U.velocity t).toLp

theorem derivative_continuous (n : ℕ) : Continuous (fun t ↦ (U.derivative t).jetLp n) :=
  viscousRhs_continuous S ν _ (fieldPath U.velocity U.velocity_continuous).continuous n

theorem pointwise_time (t : Icc (0 : ℝ) T) (x : Space) :
    HasDerivWithinAt (fun r ↦ (U.velocity (projIcc 0 T hT r)).field x)
      ((U.derivative t).field x) (Icc (0 : ℝ) T) t := by
  apply pointwise_derivative_of_l2 T hT U.velocity U.derivative
    U.velocity_continuous U.derivative_continuous _ t x
  intro r hr
  simpa only [derivative, viscousRhs_toLp] using U.time_law r hr

def energy (m : ℕ) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t ↦ wordEnergy m (U.velocity t), wordEnergy_continuous U.velocity U.velocity_continuous m⟩

def energyDerivative (m : ℕ) (t : Icc (0 : ℝ) T) : ℝ :=
  integerEnergyProduction m (U.velocity t) (U.derivative t)

theorem energy_time (m : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (U.energy m)) (U.energyDerivative m t)
      (Icc (0 : ℝ) T) t := by
  apply wordEnergy_hasDerivWithinAt T hT U.velocity U.derivative
    U.velocity_continuous U.derivative_continuous
  intro r hr x
  exact (U.pointwise_time ⟨r, hr.1.le, hr.2.le⟩ x).hasDerivAt (Icc_mem_nhds hr.1 hr.2)

theorem energy_tame (hν : 0 ≤ ν) (m : ℕ) (hm : 3 ≤ m) (M : ℝ) (t : Icc (0 : ℝ) T)
    (hM : WordBound 3 M (U.velocity t)) :
    U.energyDerivative m t ≤ tameEnergyConstant m * M * U.energy m t :=
  viscousRhs_energy S m hm hν M (U.velocity t) hM

theorem energy_quadratic (hν : 0 ≤ ν) (t : Icc (0 : ℝ) T) :
    U.energyDerivative 3 t ≤ tameEnergyConstant 3 * (1 + U.energy 3 t) ^ 2 := by
  have h := U.energy_tame hν 3 (le_refl 3) _ t (wordBound_sqrt_energy 3 (U.velocity t))
  change U.energyDerivative 3 t ≤
    tameEnergyConstant 3 * Real.sqrt (U.energy 3 t) * U.energy 3 t at h
  apply h.trans
  have hx : 0 ≤ U.energy 3 t := wordEnergy_nonneg 3 _
  have hr : 0 ≤ Real.sqrt (U.energy 3 t) := Real.sqrt_nonneg _
  have hs := Real.sq_sqrt hx
  have hsq : Real.sqrt (U.energy 3 t) * U.energy 3 t ≤ (1 + U.energy 3 t) ^ 2 := by
    have hl : Real.sqrt (U.energy 3 t) ≤ 1 + U.energy 3 t := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hl hx]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsq (tameEnergyConstant_nonneg 3)

theorem short_energy (hν : 0 ≤ ν)
    (hsmall : tameEnergyConstant 3 * T ≤ (1 + U.energy 3 ⟨0, le_rfl, hT⟩)⁻¹ / 2)
    (t : Icc (0 : ℝ) T) : U.energy 3 t ≤ 2 * U.energy 3 ⟨0, le_rfl, hT⟩ + 1 := by
  have hp (r : ℝ) (hr : r ∈ Icc 0 T) : projIcc 0 T hT r = ⟨r, hr⟩ := projIcc_of_mem hT hr
  have h := quadratic_energy_bound T (tameEnergyConstant 3) hT
    (extendPath T hT (U.energy 3)) (fun r ↦ U.energyDerivative 3 (projIcc 0 T hT r))
    ((U.energy 3).continuous.comp continuous_projIcc).continuousOn
    (fun r _hr ↦ wordEnergy_nonneg 3 (U.velocity (projIcc 0 T hT r)))
    (fun r hr ↦ by simpa only [hp r hr] using U.energy_time 3 ⟨r, hr⟩)
    (fun r _hr ↦ U.energy_quadratic hν (projIcc 0 T hT r)) (tameEnergyConstant_nonneg 3)
    (by simpa only [extendPath, hp 0 ⟨le_rfl, hT⟩] using hsmall) t t.property
  simpa only [extendPath, hp (t : ℝ) t.property, hp 0 ⟨le_rfl, hT⟩] using h

theorem energy_uniform (hν : 0 ≤ ν) (m : ℕ) (hm : 3 ≤ m) (M : ℝ)
    (hM : ∀ t, WordBound 3 M (U.velocity t)) (t : Icc (0 : ℝ) T) :
    wordEnergy m (U.velocity t) ≤ wordEnergy m (U.velocity ⟨0, le_rfl, hT⟩) *
      Real.exp (tameEnergyConstant m * M * T) := by
  have hd (r : ℝ) (hr : r ∈ Ico 0 T) :
      HasDerivWithinAt (extendPath T hT (U.energy m))
        (U.energyDerivative m (projIcc 0 T hT r)) (Icc 0 T) r := by
    simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1, hr.2.le⟩)] using
      U.energy_time m ⟨r, hr.1, hr.2.le⟩
  have he := linear_stability_within (extendPath T hT (U.energy m))
    (fun r ↦ U.energyDerivative m (projIcc 0 T hT r)) (tameEnergyConstant m * M) T
    ((U.energy m).continuous.comp continuous_projIcc).continuousOn hd
    (fun r _hr ↦ U.energy_tame hν m hm M (projIcc 0 T hT r) (hM _)) t t.property
  have hi : wordEnergy m (U.velocity t) ≤ wordEnergy m (U.velocity ⟨0, le_rfl, hT⟩) *
      Real.exp (tameEnergyConstant m * M * t) := by
    simpa only [extendPath, projIcc_of_mem hT t.property,
      projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩), energy,
      ContinuousMap.coe_mk] using he
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ (wordEnergy_nonneg m _)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left t.property.2
    (mul_nonneg (tameEnergyConstant_nonneg m) (wordBound_nonneg (hM t)))

end RegularizedViscousEvolution

/-- **Uniform `H³` bound on the Euler time.** Every regularized viscous evolution from
`A` keeps the upstream `H³` bound on the regularized Euler lifespan of `A`,
uniformly in the smoothing and in the viscosity. -/
theorem regularizedViscous_h3 (A : SmoothL2Field Space) {ν : ℝ} (hν : 0 ≤ ν)
    (U : RegularizedViscousEvolution S ν (regularizedTime A) (regularizedTime_pos A).le)
    (hinit : U.velocity ⟨0, le_rfl, (regularizedTime_pos A).le⟩ = A)
    (t : Icc (0 : ℝ) (regularizedTime A)) : WordBound 3 (regularizedH3 A) (U.velocity t) := by
  have he : U.energy 3 ⟨0, le_rfl, (regularizedTime_pos A).le⟩ = wordEnergy 3 A :=
    congrArg (wordEnergy 3) hinit
  have hc : 0 < 1 + tameEnergyConstant 3 := by linarith [tameEnergyConstant_nonneg 3]
  have ha : 0 < 1 + wordEnergy 3 A := by linarith [wordEnergy_nonneg 3 A]
  have hs : tameEnergyConstant 3 * regularizedTime A ≤ (1 + wordEnergy 3 A)⁻¹ / 2 := by
    calc
      _ ≤ (1 + tameEnergyConstant 3) * regularizedTime A := by
        nlinarith [regularizedTime_pos A]
      _ = _ := by unfold regularizedTime; field_simp [hc.ne', ha.ne']
  have hu := U.short_energy hν (by simpa only [he] using hs) t
  rw [he] at hu
  intro n hn w
  exact (wordBound_sqrt_energy 3 (U.velocity t) n hn w).trans (Real.sqrt_le_sqrt hu)

/-- **All orders, uniformly.** Every Sobolev order of every regularized viscous
evolution from `A` is bounded on the regularized Euler lifespan of `A` by a constant
independent of the smoothing and of the viscosity. -/
theorem regularizedViscous_all_order (A : SmoothL2Field Space) (q : ℕ) :
    ∃ C : ℝ, ∀ (S : SmoothingOperator) {ν : ℝ} (_ : 0 ≤ ν)
      (U : RegularizedViscousEvolution S ν (regularizedTime A) (regularizedTime_pos A).le),
      U.velocity ⟨0, le_rfl, (regularizedTime_pos A).le⟩ = A →
      ∀ t, tensorNorm q (U.velocity t) ≤ C := by
  let m := max 3 q
  refine ⟨wordCount q * Real.sqrt (wordEnergy m A *
    Real.exp (tameEnergyConstant m * regularizedH3 A * regularizedTime A)), ?_⟩
  intro S ν hν U hinit t
  have hu := U.energy_uniform hν m (le_max_left 3 q) (regularizedH3 A)
    (regularizedViscous_h3 S A hν U hinit) t
  rw [hinit] at hu
  apply tensorNorm_le_wordCount
  intro n hn w
  exact (wordBound_sqrt_energy m (U.velocity t) n (hn.trans (le_max_right 3 q)) w).trans
    (Real.sqrt_le_sqrt hu)

end Energy

/-! ## The Cauchy property as the smoothing is removed -/

section Cauchy

open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerMeanSolenoidal EulerVolterraConvolution EulerSmoothSobolev WholeSpaceViscousEnergy Finset

theorem toLp_laplacianField_fieldSub (X Y : SmoothL2Field Space) :
    (laplacianField (fieldSub X Y)).toLp = (laplacianField X).toLp - (laplacianField Y).toLp := by
  simp only [toLp_laplacianField, fieldSub, wordField_add, wordField_neg, toLp_addField,
    toLp_fieldNeg, Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem norm_laplacianField_le (X : SmoothL2Field Space) {M : ℝ} (hM : WordBound 2 M X) :
    ‖(laplacianField X).toLp‖ ≤ 3 * M := by
  rw [toLp_laplacianField]
  calc ‖∑ i : Fin 3, (wordField X (doubleWord i)).toLp‖
      ≤ ∑ i : Fin 3, ‖(wordField X (doubleWord i)).toLp‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, M := Finset.sum_le_sum fun i _ ↦ hM 2 le_rfl (doubleWord i)
    _ = 3 * M := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

theorem op_laplacianField (S : SmoothingOperator) (B : SmoothL2Field Space) :
    S.op (laplacianField B).toLp = (laplacianField (S.field B.toLp)).toLp := by
  simp only [toLp_laplacianField, map_sum, S.field_word]

/-- **The regularized viscous term approximates the Laplacian** on solenoidal fields,
with the upstream regularization error. -/
theorem viscous_error (n : ℕ) (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace)
    {M : ℝ} (hM : WordBound 3 M A) :
    ‖(regularizer n).op (laplacianOp (regularizer n) A.toLp) - (laplacianField A).toLp‖ ≤
      6 * (regularizerError n * M) := by
  have hB : ((regularizer n).field A.toLp).toLp ∈ solenoidalSpace := by
    rw [SmoothingOperator.field_toLp]
    exact (regularizer n).solenoidal _
  have hBM : WordBound 3 M ((regularizer n).field A.toLp) :=
    (regularizer n).field_wordBound A 3 M hM
  have e1 := regularizer_error_words n ((regularizer n).field A.toLp) hB 2 M hBM
  have e2 := regularizer_error_words n A hA 2 M hM
  have hsplit : (regularizer n).op (laplacianOp (regularizer n) A.toLp) - (laplacianField A).toLp =
      (laplacianField (fieldSub ((regularizer n).field ((regularizer n).field A.toLp).toLp)
        ((regularizer n).field A.toLp))).toLp +
      (laplacianField (fieldSub ((regularizer n).field A.toLp) A)).toLp := by
    rw [toLp_laplacianField_fieldSub, toLp_laplacianField_fieldSub, laplacianOp_apply,
      op_laplacianField]
    abel
  rw [hsplit]
  calc _ ≤ ‖(laplacianField (fieldSub ((regularizer n).field ((regularizer n).field A.toLp).toLp)
          ((regularizer n).field A.toLp))).toLp‖ +
        ‖(laplacianField (fieldSub ((regularizer n).field A.toLp) A)).toLp‖ := norm_add_le _ _
    _ ≤ 3 * (regularizerError n * M) + 3 * (regularizerError n * M) :=
        add_le_add (norm_laplacianField_le _ e1) (norm_laplacianField_le _ e2)
    _ = 6 * (regularizerError n * M) := by ring

namespace RegularizedViscousEvolution

variable {S : SmoothingOperator} {ν T : ℝ} {hT : 0 ≤ T} (U : RegularizedViscousEvolution S ν T hT)

theorem l2_time (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r ↦ (U.velocity (projIcc 0 T hT r)).toLp)
      (U.derivative t).toLp (Icc (0 : ℝ) T) t := by
  have h := ordinaryWord_hasDerivWithinAt T hT U.velocity U.derivative
    U.velocity_continuous U.derivative_continuous
    (fun r hr x ↦ (U.pointwise_time ⟨r, hr.1.le, hr.2.le⟩ x).hasDerivAt (Icc_mem_nhds hr.1 hr.2))
    (n := 0) Fin.elim0 t
  simpa only [wordField_zero] using h

end RegularizedViscousEvolution

theorem viscousRhs_sub (S₁ S₂ : SmoothingOperator) (ν : ℝ) (A B : SmoothL2Field Space) :
    (viscousRhs S₂ ν B.toLp).toLp - (viscousRhs S₁ ν A.toLp).toLp =
      ((S₂.rhs B.toLp).toLp - (S₁.rhs A.toLp).toLp) +
        ν • (((S₂.op (laplacianOp S₂ B.toLp) - (laplacianField B).toLp) -
            (S₁.op (laplacianOp S₁ A.toLp) - (laplacianField A).toLp)) +
          ((laplacianField B).toLp - (laplacianField A).toLp)) := by
  simp only [viscousRhs, toLp_addField, viscousField_toLp, viscousOp_apply, laplacianOp_apply,
    smul_add, smul_sub]
  abel

/-- The comparison constant for two regularized viscous evolutions. -/
def viscousComparisonCost (ν T M : ℝ) : ℝ :=
  Real.sqrt (regularizationCost M ^ 2 + 36 * ν * M ^ 2) *
    Real.sqrt (Real.exp ((2 * ((360 * smoothEmbeddingConstant) * M) + 1 + ν) * T))

theorem viscousComparisonCost_nonneg (ν T M : ℝ) : 0 ≤ viscousComparisonCost ν T M :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- **Two regularized viscous evolutions stay close in `L²`.** Their distance is at most
the sum of the two regularization errors times a constant fixed by the `H⁴` bound, the
viscosity and the time. -/
theorem regularizedViscous_l2_comparison {ν T : ℝ} {hT : 0 ≤ T} (hν : 0 ≤ ν) {j k : ℕ}
    (U : RegularizedViscousEvolution (regularizer j) ν T hT)
    (V : RegularizedViscousEvolution (regularizer k) ν T hT)
    (M : ℝ) (hU : ∀ t, WordBound 4 M (U.velocity t))
    (hV : ∀ t, WordBound 4 M (V.velocity t))
    (hinit : (V.velocity ⟨0, le_rfl, hT⟩).toLp = (U.velocity ⟨0, le_rfl, hT⟩).toLp) :
    ‖fieldPath V.velocity V.velocity_continuous - fieldPath U.velocity U.velocity_continuous‖ ≤
      (regularizerError j + regularizerError k) * viscousComparisonCost ν T M := by
  let G := (360 * smoothEmbeddingConstant) * M
  let C := 2 * G + 1 + ν
  let E := (regularizerError j + regularizerError k) *
    Real.sqrt (regularizationCost M ^ 2 + 36 * ν * M ^ 2)
  have hM : 0 ≤ M := wordBound_nonneg (hU ⟨0, le_rfl, hT⟩)
  have hG : 0 ≤ G := mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) hM
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have herr : 0 ≤ regularizerError j + regularizerError k :=
    add_nonneg (regularizerError_nonneg j) (regularizerError_nonneg k)
  have hE : 0 ≤ E := mul_nonneg herr (Real.sqrt_nonneg _)
  have hE2 : E ^ 2 = (regularizerError j + regularizerError k) ^ 2 *
      (regularizationCost M ^ 2 + 36 * ν * M ^ 2) := by
    dsimp [E]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  let X (r : ℝ) := ‖(V.velocity (projIcc 0 T hT r)).toLp - (U.velocity (projIcc 0 T hT r)).toLp‖ ^ 2
  let X' (r : ℝ) := 2 * ⟪(V.velocity (projIcc 0 T hT r)).toLp - (U.velocity (projIcc 0 T hT r)).toLp,
    (V.derivative (projIcc 0 T hT r)).toLp - (U.derivative (projIcc 0 T hT r)).toLp⟫_ℝ
  have hc : ContinuousOn X (Icc 0 T) :=
    ((((fieldPath V.velocity V.velocity_continuous).continuous.sub
      (fieldPath U.velocity U.velocity_continuous).continuous).comp
        continuous_projIcc).norm.pow 2).continuousOn
  have hx0 : X 0 = 0 := by
    simp only [X, projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩),
      hinit, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  have hd (r : ℝ) (hr : r ∈ Icc 0 T) : HasDerivWithinAt X (X' r) (Icc 0 T) r := by
    have h := ((V.l2_time ⟨r, hr⟩).sub (U.l2_time ⟨r, hr⟩)).norm_sq
    simpa only [X, X', Pi.sub_apply, projIcc_of_mem hT hr] using h
  have hb (r : ℝ) (_hr : r ∈ Icc 0 T) : X' r ≤ C * X r + E ^ 2 := by
    set Ur := U.velocity (projIcc 0 T hT r)
    set Vr := V.velocity (projIcc 0 T hT r)
    set W := Vr.toLp - Ur.toLp with hW
    change 2 * ⟪W, (viscousRhs (regularizer k) ν Vr.toLp).toLp -
        (viscousRhs (regularizer j) ν Ur.toLp).toLp⟫_ℝ ≤ C * ‖W‖ ^ 2 + E ^ 2
    rw [viscousRhs_sub]
    set eu := (regularizer j).op (laplacianOp (regularizer j) Ur.toLp) - (laplacianField Ur).toLp
    set ev := (regularizer k).op (laplacianOp (regularizer k) Vr.toLp) - (laplacianField Vr).toLp
    -- the transport parts
    have htr := perturbed_difference_energy Ur Vr (U.solenoidal _) (V.solenoidal _)
      ((regularizer j).rhs Ur.toLp).toLp ((regularizer k).rhs Vr.toLp).toLp
      G (regularizerError j * regularizationCost M) (regularizerError k * regularizationCost M)
      (wordBound_gradient (wordBound_mono (hU _) (by omega)))
      (regularized_rhs_error j _ (U.solenoidal _) M (hU _))
      (regularized_rhs_error k _ (V.solenoidal _) M (hV _))
    -- the viscous parts
    have hvu : ‖eu‖ ≤ 6 * (regularizerError j * M) :=
      viscous_error j Ur (U.solenoidal _) (wordBound_mono (hU _) (by omega))
    have hvv : ‖ev‖ ≤ 6 * (regularizerError k * M) :=
      viscous_error k Vr (V.solenoidal _) (wordBound_mono (hV _) (by omega))
    have hlap : ⟪W, (laplacianField Vr).toLp - (laplacianField Ur).toLp⟫_ℝ ≤ 0 := by
      rw [← toLp_laplacianField_fieldSub]
      have hWe : W = (fieldSub Vr Ur).toLp := by
        rw [hW, fieldSub, toLp_addField, toLp_fieldNeg, sub_eq_add_neg]
      rw [hWe, inner_laplacianField]
      have := Finset.sum_nonneg fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦
        sq_nonneg ‖((fieldSub Vr Ur).directionalField (axis i)).toLp‖
      linarith
    have hev : ‖ev - eu‖ ≤ 6 * M * (regularizerError j + regularizerError k) := by
      calc ‖ev - eu‖ ≤ ‖ev‖ + ‖eu‖ := norm_sub_le _ _
        _ ≤ 6 * (regularizerError k * M) + 6 * (regularizerError j * M) := add_le_add hvv hvu
        _ = 6 * M * (regularizerError j + regularizerError k) := by ring
    have hcs : ⟪W, ev - eu⟫_ℝ ≤ ‖W‖ * (6 * M * (regularizerError j + regularizerError k)) :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hev (norm_nonneg _))
    have hamgm : 2 * ν * ⟪W, ev - eu⟫_ℝ ≤
        ν * ‖W‖ ^ 2 + ν * (6 * M * (regularizerError j + regularizerError k)) ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hcs (by positivity : (0 : ℝ) ≤ 2 * ν)
      have h2 : 2 * ν * (‖W‖ * (6 * M * (regularizerError j + regularizerError k))) ≤
          ν * ‖W‖ ^ 2 + ν * (6 * M * (regularizerError j + regularizerError k)) ^ 2 := by
        nlinarith [mul_nonneg hν (sq_nonneg (‖W‖ - 6 * M * (regularizerError j + regularizerError k)))]
      linarith
    have hlap' : 2 * ν * ⟪W, (laplacianField Vr).toLp - (laplacianField Ur).toLp⟫_ℝ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hlap
    have hsum : (regularizerError j * regularizationCost M +
          regularizerError k * regularizationCost M) ^ 2 +
        ν * (6 * M * (regularizerError j + regularizerError k)) ^ 2 = E ^ 2 := by
      rw [hE2]
      ring
    rw [inner_add_right, inner_smul_right, inner_add_right]
    change 2 * ⟪W, ((regularizer k).rhs Vr.toLp).toLp - ((regularizer j).rhs Ur.toLp).toLp⟫_ℝ ≤
        (2 * G + 1) * ‖W‖ ^ 2 +
          (regularizerError j * regularizationCost M + regularizerError k * regularizationCost M) ^ 2
      at htr
    dsimp [C]
    nlinarith [hsum]
  have hnorm (t : Icc (0 : ℝ) T) :
      ‖(V.velocity t).toLp - (U.velocity t).toLp‖ ≤ E * Real.sqrt (Real.exp (C * T)) := by
    have h := forced_linear_zero_bound T C E hC X X' hc hx0 hd hb t t.property
    simp only [X, projIcc_of_mem hT t.property] at h
    have hs := Real.sq_sqrt ((Real.exp_pos (C * T)).le)
    have he : 0 ≤ E * Real.sqrt (Real.exp (C * T)) := mul_nonneg hE (Real.sqrt_nonneg _)
    nlinarith [norm_nonneg ((V.velocity t).toLp - (U.velocity t).toLp)]
  apply (ContinuousMap.norm_le _ (mul_nonneg herr (viscousComparisonCost_nonneg ν T M))).mpr
  intro t
  exact (hnorm t).trans_eq (by dsimp [E, C, G, viscousComparisonCost]; ring)

/-- **The regularized viscous evolutions are Cauchy** in continuous `L²` on a common
interval with a common `H⁴` bound. -/
theorem regularizedViscous_cauchy {ν T : ℝ} {hT : 0 ≤ T} (hν : 0 ≤ ν)
    (U : ∀ n, RegularizedViscousEvolution (regularizer n) ν T hT)
    (M : ℝ) (hM : ∀ n t, WordBound 4 M ((U n).velocity t))
    (hinit : ∀ j k, ((U k).velocity ⟨0, le_rfl, hT⟩).toLp = ((U j).velocity ⟨0, le_rfl, hT⟩).toLp) :
    CauchySeq (fun n ↦ fieldPath (U n).velocity (U n).velocity_continuous) := by
  have he : Tendsto (fun n ↦ regularizerError n * viscousComparisonCost ν T M) atTop
      (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using regularizerError_tendsto.mul_const (viscousComparisonCost ν T M)
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hh : ∀ᶠ n in atTop, regularizerError n * viscousComparisonCost ν T M < ε / 2 :=
    (tendsto_order.mp he).2 _ (half_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hh
  refine ⟨N, fun j hj k hk ↦ ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  apply (regularizedViscous_l2_comparison hν (U j) (U k) M (hM j) (hM k) (hinit j k)).trans_lt
  have hj' := hN j hj
  have hk' := hN k hk
  nlinarith

end Cauchy

/-! ## The limit: smooth Navier–Stokes evolutions on `ℝ³` -/

section Limit

open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerMeanSolenoidal EulerVolterraConvolution EulerContinuousTimeIntegral EulerSmoothFieldSobolevTime
  WholeSpaceViscousEnergy Finset Laplacian

/-- **A smooth Navier–Stokes evolution on `ℝ³`** over `[0, T]`: velocity and pressure
force with all `L²` jets, continuous in time, the velocity solenoidal and the pressure
force a gradient, and the equation `∂ₜu = -(u·∇)u - ∇p + ν Δu` at every point and
every interior time. -/
structure NSEvolution (ν T : ℝ) (hT : 0 ≤ T) where
  velocity : Icc (0 : ℝ) T → SmoothL2Field Space
  pressureForce : Icc (0 : ℝ) T → SmoothL2Field Space
  velocity_continuous : ∀ n, Continuous (fun t ↦ (velocity t).jetLp n)
  pressure_continuous : ∀ n, Continuous (fun t ↦ (pressureForce t).jetLp n)
  solenoidal : ∀ t, (velocity t).toLp ∈ solenoidalSpace
  gradient : ∀ t, (pressureForce t).toLp ∈ gradientSpace
  time_law : ∀ t (ht : t ∈ Ioo 0 T) x,
    HasDerivAt (fun r ↦ (velocity (projIcc 0 T hT r)).field x)
      (-fderiv ℝ (velocity ⟨t, ht.1.le, ht.2.le⟩).field x ((velocity ⟨t, ht.1.le, ht.2.le⟩).field x) -
        (pressureForce ⟨t, ht.1.le, ht.2.le⟩).field x +
          ν • Δ (velocity ⟨t, ht.1.le, ht.2.le⟩).field x) t

theorem laplacianField_eq_add (A : SmoothL2Field Space) :
    laplacianField A = addField (addField
      ((A.directionalField (axis 0)).directionalField (axis 0))
      ((A.directionalField (axis 1)).directionalField (axis 1)))
      ((A.directionalField (axis 2)).directionalField (axis 2)) := by
  apply field_ext
  funext x
  simp only [laplacianField, sumField_field, addField_field, Fin.sum_univ_three]

theorem continuous_jetLp_laplacianField {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field Space) (hA : ∀ n, Continuous (fun t ↦ (A t).jetLp n)) (n : ℕ) :
    Continuous (fun t ↦ (laplacianField (A t)).jetLp n) := by
  simp only [laplacianField_eq_add]
  have hdd : ∀ i : Fin 3, ∀ n,
      Continuous (fun t ↦ (((A t).directionalField (axis i)).directionalField (axis i)).jetLp n) :=
    fun i ↦ continuous_jetLp_directionalField _
      (continuous_jetLp_directionalField A hA (axis i)) (axis i)
  exact continuous_jetLp_addField _ _ (continuous_jetLp_addField _ _ (hdd 0) (hdd 1)) (hdd 2) n

variable {T : ℝ}

/-- The Laplacian path of a jet-continuous path of fields. -/
def laplacianPath (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t ↦ (A t).jetLp n)) : C(Icc (0 : ℝ) T, L2) :=
  fieldPath (fun t ↦ laplacianField (A t)) (continuous_jetLp_laplacianField A hA)

theorem laplacianPath_apply (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t ↦ (A t).jetLp n)) (t : Icc (0 : ℝ) T) :
    laplacianPath A hA t = (laplacianField (A t)).toLp := rfl

theorem laplacianPath_eq_words (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t ↦ (A t).jetLp n)) :
    laplacianPath A hA = ∑ i : Fin 3, ordinaryWordPath A hA (doubleWord i) := by
  apply ContinuousMap.ext
  intro t
  rw [laplacianPath_apply, toLp_laplacianField, ContinuousMap.sum_apply]
  simp only [ordinaryWordPath_apply]

/-- **The Laplacians converge** along a smooth limit. -/
theorem laplacianPath_convergence {A : ℕ → Icc (0 : ℝ) T → SmoothL2Field Space}
    {hA : ∀ k n, Continuous (fun t ↦ (A k t).jetLp n)} (L : SmoothLimitData A hA) :
    Tendsto (fun k ↦ laplacianPath (A k) (hA k)) atTop
      (𝓝 (laplacianPath L.field L.field_continuous)) := by
  simp only [laplacianPath_eq_words]
  refine tendsto_finsetSum _ fun i _ ↦ ?_
  let C := (ordinaryWordOperator (doubleWord i)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
  have h := (C.continuous.tendsto (L.tower.realization 2)).comp (L.sobolev_convergence 2)
  have ha : ∀ k, C (sobolevPath (A k) (hA k) 2) = ordinaryWordPath (A k) (hA k) (doubleWord i) :=
    fun k ↦ rfl
  have hb : C (L.tower.realization 2) =
      ordinaryWordPath L.field L.field_continuous (doubleWord i) := by
    rw [← L.tower.smoothField_path 2]
    rfl
  simpa only [Function.comp_def, ha, hb] using h

/-- The Navier–Stokes right-hand side path `P(-(u·∇)u) + ν Δu`. -/
def nsRhsPath (ν : ℝ) (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t ↦ (A t).jetLp n)) : C(Icc (0 : ℝ) T, L2) :=
  projectedRhsPath A hA + ν • laplacianPath A hA

namespace RegularizedViscousEvolution

variable {S : SmoothingOperator} {ν : ℝ} {hT : 0 ≤ T} (U : RegularizedViscousEvolution S ν T hT)

def derivativePath : C(Icc (0 : ℝ) T, L2) := fieldPath U.derivative U.derivative_continuous

theorem integral_equation (t : Icc (0 : ℝ) T) :
    (U.velocity t).toLp = (U.velocity ⟨0, le_rfl, hT⟩).toLp + integral T hT U.derivativePath t := by
  have h := eq_initial_add_integral T hT U.derivativePath
    (fun r ↦ (U.velocity (projIcc 0 T hT r)).toLp) U.l2_time t
  simpa only [projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)] using h

end RegularizedViscousEvolution

section Passage

variable {ν : ℝ} {hT : 0 ≤ T} {U : ∀ n, RegularizedViscousEvolution (regularizer n) ν T hT}
  (L : SmoothLimitData (fun n ↦ (U n).velocity) (fun n ↦ (U n).velocity_continuous))

omit L in
theorem derivativePath_sub_norm_le (n : ℕ) (M : ℝ)
    (hM : ∀ t, WordBound 4 M ((U n).velocity t)) (hM0 : 0 ≤ M) (hν : 0 ≤ ν) :
    ‖(U n).derivativePath - nsRhsPath ν (U n).velocity (U n).velocity_continuous‖ ≤
      regularizerError n * (regularizationCost M + ν * (6 * M)) := by
  apply (ContinuousMap.norm_le _ (by
    have := regularizerError_nonneg n
    have := regularizationCost_nonneg M
    positivity)).mpr
  intro t
  have he := regularized_rhs_error n _ ((U n).solenoidal t) M (hM t)
  have hv := viscous_error n ((U n).velocity t) ((U n).solenoidal t) (wordBound_mono (hM t) (by omega))
  have hsplit : ((U n).derivativePath - nsRhsPath ν (U n).velocity (U n).velocity_continuous) t =
      ((((regularizer n).rhs ((U n).velocity t).toLp).toLp - (projectedRhs ((U n).velocity t)).toLp) +
        ν • ((regularizer n).op (laplacianOp (regularizer n) ((U n).velocity t).toLp) -
          (laplacianField ((U n).velocity t)).toLp)) := by
    simp only [ContinuousMap.sub_apply, nsRhsPath, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      RegularizedViscousEvolution.derivativePath, fieldPath, ContinuousMap.coe_mk,
      RegularizedViscousEvolution.derivative, viscousRhs, toLp_addField, viscousField_toLp,
      viscousOp_apply, projectedRhsPath, laplacianPath_apply, laplacianOp_apply, smul_sub]
    abel
  rw [hsplit]
  calc _ ≤ ‖((regularizer n).rhs ((U n).velocity t).toLp).toLp - (projectedRhs ((U n).velocity t)).toLp‖ +
        ‖ν • ((regularizer n).op (laplacianOp (regularizer n) ((U n).velocity t).toLp) -
          (laplacianField ((U n).velocity t)).toLp)‖ := norm_add_le _ _
    _ ≤ regularizerError n * regularizationCost M + ν * (6 * (regularizerError n * M)) := by
        rw [norm_smul, Real.norm_of_nonneg hν]
        exact add_le_add he (mul_le_mul_of_nonneg_left hv hν)
    _ = regularizerError n * (regularizationCost M + ν * (6 * M)) := by ring

/-- **The regularized derivatives converge** to the Navier–Stokes right-hand side of
the limit. -/
theorem viscous_derivative_convergence (hν : 0 ≤ ν) (M : ℝ)
    (hM : ∀ n t, WordBound 4 M ((U n).velocity t)) :
    Tendsto (fun n ↦ (U n).derivativePath) atTop (𝓝 (nsRhsPath ν L.field L.field_continuous)) := by
  have hM0 : 0 ≤ M := wordBound_nonneg (hM 0 ⟨0, le_rfl, hT⟩)
  have hp := L.projectedRhsPath_convergence hT (40 * M)
    (fun n t ↦ tensorNorm_three_le _ M (wordBound_mono (hM n t) (by omega)))
  have hl := laplacianPath_convergence L
  have hrhs : Tendsto (fun n ↦ nsRhsPath ν (U n).velocity (U n).velocity_continuous) atTop
      (𝓝 (nsRhsPath ν L.field L.field_continuous)) := hp.add (hl.const_smul ν)
  have hz : Tendsto (fun n ↦ (U n).derivativePath -
      nsRhsPath ν (U n).velocity (U n).velocity_continuous) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun n ↦ derivativePath_sub_norm_le n M (hM n) hM0 hν)
    simpa only [zero_mul] using
      regularizerError_tendsto.mul_const (regularizationCost M + ν * (6 * M))
  have h := hz.add hrhs
  simpa only [sub_add_cancel, zero_add] using h

theorem ns_integral_equation (hν : 0 ≤ ν) (M : ℝ)
    (hM : ∀ n t, WordBound 4 M ((U n).velocity t)) (t : Icc (0 : ℝ) T) :
    (L.field t).toLp = (L.field ⟨0, le_rfl, hT⟩).toLp +
      integral T hT (nsRhsPath ν L.field L.field_continuous) t := by
  have hi := (ContinuousMap.evalCLM ℝ t).continuous.tendsto
    (integral T hT (nsRhsPath ν L.field L.field_continuous)) |>.comp
      (((integral (E := L2) T hT).continuous.tendsto _).comp
        (viscous_derivative_convergence L hν M hM))
  have hs := (L.toLp_convergence ⟨0, le_rfl, hT⟩).add hi
  exact tendsto_nhds_unique (L.toLp_convergence t)
    (hs.congr (fun n ↦ ((U n).integral_equation t).symm))

/-- The Navier–Stokes right-hand side of a field, as a smooth field. -/
def nsRhsField (ν : ℝ) (A : SmoothL2Field Space) : SmoothL2Field Space :=
  addField (projectedRhs A) (EulerOrdinarySobolev.scaleField ν (laplacianField A))

omit L in
theorem nsRhsField_toLp (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t ↦ (A t).jetLp n)) (t : Icc (0 : ℝ) T) :
    (nsRhsField ν (A t)).toLp = nsRhsPath ν A hA t := by
  simp only [nsRhsField, toLp_addField, EulerOrdinarySobolev.scaleField_toLp, nsRhsPath,
    ContinuousMap.add_apply, ContinuousMap.smul_apply, projectedRhsPath, fieldPath,
    ContinuousMap.coe_mk, laplacianPath_apply]

omit L in
theorem nsRhsField_continuous (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t ↦ (A t).jetLp n)) (n : ℕ) :
    Continuous (fun t ↦ (nsRhsField ν (A t)).jetLp n) :=
  continuous_jetLp_addField _ _ (projectedRhs_continuous A hA)
    (fun k ↦ continuous_jetLp_mapField _ _ (continuous_jetLp_laplacianField A hA) k) n

theorem ns_time (hν : 0 ≤ ν) (M : ℝ) (hM : ∀ n t, WordBound 4 M ((U n).velocity t))
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r ↦ (L.field (projIcc 0 T hT r)).toLp)
      (nsRhsPath ν L.field L.field_continuous t) (Icc (0 : ℝ) T) t := by
  have he : (fun r ↦ (L.field (projIcc 0 T hT r)).toLp) =
      fun r ↦ (L.field ⟨0, le_rfl, hT⟩).toLp +
        extendPath T hT (integral T hT (nsRhsPath ν L.field L.field_continuous)) r := by
    funext r
    exact ns_integral_equation L hν M hM (projIcc 0 T hT r)
  rw [he]
  exact (integral_hasDerivWithinAt T hT (nsRhsPath ν L.field L.field_continuous) t).const_add _

/-- The limit, as a smooth Navier–Stokes evolution. -/
def nsEvolution (hν : 0 ≤ ν) (M : ℝ) (hM : ∀ n t, WordBound 4 M ((U n).velocity t)) :
    NSEvolution ν T hT where
  velocity := L.field
  pressureForce t := pressureField (L.field t)
  velocity_continuous := L.field_continuous
  pressure_continuous := pressureField_continuous L.field L.field_continuous
  solenoidal t := gradientSpace.isClosed_orthogonal.mem_of_tendsto (L.toLp_convergence t)
    (Eventually.of_forall (fun n ↦ (U n).solenoidal t))
  gradient t := pressureField_mem_gradient (L.field t)
  time_law t ht x := by
    have hd : ∀ r (hr : r ∈ Ioo 0 T),
        HasDerivAt (fun s ↦ (L.field (projIcc 0 T hT s)).toLp)
          (nsRhsField ν (L.field ⟨r, hr.1.le, hr.2.le⟩)).toLp r := by
      intro r hr
      rw [nsRhsField_toLp L.field L.field_continuous]
      exact (ns_time L hν M hM ⟨r, hr.1.le, hr.2.le⟩).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
    have h := pointwise_derivative_of_l2 T hT L.field (fun s ↦ nsRhsField ν (L.field s))
      L.field_continuous (nsRhsField_continuous L.field L.field_continuous) hd
      ⟨t, ht.1.le, ht.2.le⟩ x
    have hf : (nsRhsField ν (L.field ⟨t, ht.1.le, ht.2.le⟩)).field x =
        -fderiv ℝ (L.field ⟨t, ht.1.le, ht.2.le⟩).field x ((L.field ⟨t, ht.1.le, ht.2.le⟩).field x) -
          (pressureField (L.field ⟨t, ht.1.le, ht.2.le⟩)).field x +
            ν • Δ (L.field ⟨t, ht.1.le, ht.2.le⟩).field x := by
      simp only [nsRhsField, addField_field, projectedRhs_field, EulerOrdinarySobolev.scaleField_field,
        laplacianField_field]
    rw [← hf]
    exact h.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end Passage

/-- The regularized viscous evolution from `A` with the `n`-th regularizer. -/
def regularizedViscousSolution {ν : ℝ} (hν : 0 ≤ ν) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (n : ℕ) :
    RegularizedViscousEvolution (regularizer n) ν (regularizedTime A) (regularizedTime_pos A).le :=
  Classical.choose (exists_regularizedViscous (regularizer n) hν (regularizedTime A)
    (regularizedTime_pos A).le A hA)

theorem regularizedViscousSolution_initial {ν : ℝ} (hν : 0 ≤ ν) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (n : ℕ) :
    (regularizedViscousSolution hν A hA n).velocity ⟨0, le_rfl, (regularizedTime_pos A).le⟩ = A :=
  Classical.choose_spec (exists_regularizedViscous (regularizer n) hν (regularizedTime A)
    (regularizedTime_pos A).le A hA)

theorem regularizedViscousSolution_bounds {ν : ℝ} (hν : 0 ≤ ν) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) :
    ∀ q, ∃ M : ℝ, ∀ n t, tensorNorm q ((regularizedViscousSolution hν A hA n).velocity t) ≤ M := by
  intro q
  obtain ⟨M, hM⟩ := regularizedViscous_all_order A q
  exact ⟨M, fun n t ↦ hM _ hν _ (regularizedViscousSolution_initial hν A hA n) t⟩

theorem regularizedViscousSolution_cauchy {ν : ℝ} (hν : 0 ≤ ν) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) :
    CauchySeq (fun n ↦ fieldPath (regularizedViscousSolution hν A hA n).velocity
      (regularizedViscousSolution hν A hA n).velocity_continuous) := by
  obtain ⟨M, hM⟩ := regularizedViscousSolution_bounds hν A hA 4
  apply regularizedViscous_cauchy hν (regularizedViscousSolution hν A hA) M
    (fun n t k hk w ↦ (wordBound_tensorNorm 4 _ k hk w).trans (hM n t))
  intro j k
  simp only [regularizedViscousSolution_initial]

/-- The smooth limit of the regularized viscous evolutions from `A`. -/
def viscousLocalLimit {ν : ℝ} (hν : 0 ≤ ν) (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    SmoothLimitData (fun n ↦ (regularizedViscousSolution hν A hA n).velocity)
      (fun n ↦ (regularizedViscousSolution hν A hA n).velocity_continuous) :=
  smoothLimitData (regularizedTime_pos A).le _ _
    (regularizedViscousSolution_bounds hν A hA) (regularizedViscousSolution_cauchy hν A hA)

/-- The local smooth Navier–Stokes evolution from `A`. -/
def localNSEvolution {ν : ℝ} (hν : 0 ≤ ν) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) :
    NSEvolution ν (regularizedTime A) (regularizedTime_pos A).le :=
  nsEvolution (viscousLocalLimit hν A hA) hν
    (Classical.choose (regularizedViscousSolution_bounds hν A hA 4))
    (fun n t k hk w ↦ (wordBound_tensorNorm 4 _ k hk w).trans
      (Classical.choose_spec (regularizedViscousSolution_bounds hν A hA 4) n t))

theorem localNSEvolution_initial {ν : ℝ} (hν : 0 ≤ ν) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) :
    (localNSEvolution hν A hA).velocity ⟨0, le_rfl, (regularizedTime_pos A).le⟩ = A := by
  apply smoothField_eq_of_toLp_eq
  have h := (viscousLocalLimit hν A hA).toLp_convergence ⟨0, le_rfl, (regularizedTime_pos A).le⟩
  simp only [regularizedViscousSolution_initial] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- **Local existence for the Navier–Stokes equations on `ℝ³`.** Every smooth solenoidal
velocity field with all derivatives in `L²` starts a smooth Navier–Stokes evolution, for
every viscosity `ν ≥ 0`, on an interval whose length depends only on the `H³` energy of the
datum (the upstream regularized Euler time, which does not depend on `ν`). -/
theorem exists_local_nsEvolution {ν : ℝ} (hν : 0 ≤ ν) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) :
    ∃ (T : ℝ) (hT : 0 < T), ∃ U : NSEvolution ν T hT.le, U.velocity ⟨0, le_rfl, hT.le⟩ = A :=
  ⟨regularizedTime A, regularizedTime_pos A, localNSEvolution hν A hA,
    localNSEvolution_initial hν A hA⟩

end Limit

/-! ## Uniqueness -/

section Uniqueness

open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerMeanSolenoidal EulerMeanClassical EulerVolterraConvolution WholeSpaceViscousEnergy
  Finset Laplacian

namespace NSEvolution

variable {ν T : ℝ} {hT : 0 ≤ T}

/-- The Euler part `-(u·∇)u - ∇p` of the right-hand side, as a smooth field. -/
def eulerPart (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) : SmoothL2Field Space :=
  EulerSmoothEulerEvolution.rhs U.velocity U.velocity_continuous U.pressureForce t

/-- The full right-hand side `-(u·∇)u - ∇p + ν Δu`, as a smooth field. -/
def derivative (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) : SmoothL2Field Space :=
  addField (U.eulerPart t) (EulerOrdinarySobolev.scaleField ν (laplacianField (U.velocity t)))

theorem derivative_field (U : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) (x : Space) :
    (U.derivative t).field x = -fderiv ℝ (U.velocity t).field x ((U.velocity t).field x) -
      (U.pressureForce t).field x + ν • Δ (U.velocity t).field x := by
  simp only [derivative, addField_field, eulerPart, EulerSmoothEulerEvolution.rhs_field,
    EulerOrdinarySobolev.scaleField_field, laplacianField_field]

theorem derivative_continuous (U : NSEvolution ν T hT) (n : ℕ) :
    Continuous (fun t ↦ (U.derivative t).jetLp n) :=
  continuous_jetLp_addField _ _
    (EulerSmoothEulerEvolution.rhs_jet_continuous U.velocity U.velocity_continuous
      U.pressureForce U.pressure_continuous)
    (fun k ↦ continuous_jetLp_mapField _ _
      (continuous_jetLp_laplacianField U.velocity U.velocity_continuous) k) n

def difference (U V : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) : SmoothL2Field Space :=
  fieldSub (V.velocity t) (U.velocity t)

def pressureDifference (U V : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) : SmoothL2Field Space :=
  fieldSub (V.pressureForce t) (U.pressureForce t)

def differenceDerivative (U V : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) : SmoothL2Field Space :=
  fieldSub (V.derivative t) (U.derivative t)

theorem difference_continuous (U V : NSEvolution ν T hT) (n : ℕ) :
    Continuous (fun t ↦ (U.difference V t).jetLp n) :=
  continuous_jet_fieldSub V.velocity U.velocity V.velocity_continuous U.velocity_continuous n

theorem differenceDerivative_continuous (U V : NSEvolution ν T hT) (n : ℕ) :
    Continuous (fun t ↦ (U.differenceDerivative V t).jetLp n) :=
  continuous_jet_fieldSub V.derivative U.derivative V.derivative_continuous
    U.derivative_continuous n

theorem difference_time_law (U V : NSEvolution ν T hT) :
    ∀ t (ht : t ∈ Ioo 0 T) x,
      HasDerivAt (fun r ↦ (U.difference V (projIcc 0 T hT r)).field x)
        ((U.differenceDerivative V ⟨t, ht.1.le, ht.2.le⟩).field x) t := by
  intro t ht x
  have h := (V.time_law t ht x).sub (U.time_law t ht x)
  convert! h using 1
  simp only [differenceDerivative, fieldSub_field, derivative_field]

theorem eulerPart_sub (U V : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    fieldSub (V.eulerPart t) (U.eulerPart t) =
      differenceRhs (U.velocity t) (U.difference V t) (U.pressureDifference V t) := by
  apply field_ext
  funext x
  have he : (U.difference V t).field = (V.velocity t).field - (U.velocity t).field :=
    funext (fieldSub_field (V.velocity t) (U.velocity t))
  rw [differenceRhs_field, he, fderiv_sub ((V.velocity t).smooth.differentiable (by simp) x)
    ((U.velocity t).smooth.differentiable (by simp) x)]
  simp only [pressureDifference, fieldSub_field, eulerPart, EulerSmoothEulerEvolution.rhs_field,
    Pi.sub_apply, sub_apply, map_sub]
  abel_nf

theorem differenceDerivative_toLp (U V : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    (U.differenceDerivative V t).toLp =
      (differenceRhs (U.velocity t) (U.difference V t) (U.pressureDifference V t)).toLp +
        ν • (laplacianField (U.difference V t)).toLp := by
  rw [← U.eulerPart_sub V t, difference, toLp_laplacianField_fieldSub]
  simp only [differenceDerivative, derivative, toLp_fieldSub, toLp_addField,
    EulerOrdinarySobolev.scaleField_toLp, smul_sub]
  abel

def l2EnergyPath (U V : NSEvolution ν T hT) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t ↦ ‖(U.difference V t).toLp‖ ^ 2, by
    have h := (ordinaryWordPath (U.difference V) (U.difference_continuous V)
      (Fin.elim0 : Fin 0 → Fin 3)).continuous
    simpa only [Function.comp_def, ordinaryWordPath_apply, wordField_zero] using
      (continuous_pow 2).comp h.norm⟩

def l2EnergyDerivative (U V : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) : ℝ :=
  2 * ⟪(U.difference V t).toLp, (U.differenceDerivative V t).toLp⟫_ℝ

theorem l2Energy_hasDerivWithinAt (U V : NSEvolution ν T hT) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (U.l2EnergyPath V)) (U.l2EnergyDerivative V t)
      (Icc (0 : ℝ) T) t := by
  have hd := (ordinaryWord_hasDerivWithinAt T hT (U.difference V)
    (U.differenceDerivative V) (U.difference_continuous V)
    (U.differenceDerivative_continuous V) (U.difference_time_law V)
    (Fin.elim0 : Fin 0 → Fin 3) t).norm_sq
  change HasDerivWithinAt (fun r ↦ ‖(U.difference V (projIcc 0 T hT r)).toLp‖ ^ 2)
    (2 * ⟪(U.difference V t).toLp, (U.differenceDerivative V t).toLp⟫_ℝ) (Icc (0 : ℝ) T) t
  simpa only [wordField_zero, projIcc_of_mem hT t.property] using hd

/-- **The viscous term only helps the stability estimate.** -/
theorem l2EnergyDerivative_bound (hν : 0 ≤ ν) (U V : NSEvolution ν T hT) (K : ℝ)
    (hK : ∀ t x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K) (t : Icc (0 : ℝ) T) :
    U.l2EnergyDerivative V t ≤ 2 * K * U.l2EnergyPath V t := by
  have hE := differenceRhs_l2_bound (U.velocity t) (U.difference V t) (U.pressureDifference V t)
    K (hK t) (by
      have he : (addField (U.velocity t) (U.difference V t)).field = (V.velocity t).field := by
        funext x
        simp only [addField_field, difference, fieldSub_field]
        abel
      rw [he]
      exact solenoidal_representative_divergence _ (V.solenoidal t) _ (V.velocity t).smooth
        (V.velocity t).toLp_ae)
    (by rw [difference, toLp_fieldSub]; exact solenoidalSpace.sub_mem (V.solenoidal t) (U.solenoidal t))
    (by rw [pressureDifference, toLp_fieldSub]; exact gradientSpace.sub_mem (V.gradient t) (U.gradient t))
  have hL := inner_laplacianField (U.difference V t)
  have hS : 0 ≤ ∑ i : Fin 3, ‖((U.difference V t).directionalField (axis i)).toLp‖ ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  change 2 * ⟪(U.difference V t).toLp, (U.differenceDerivative V t).toLp⟫_ℝ ≤
    2 * K * ‖(U.difference V t).toLp‖ ^ 2
  rw [differenceDerivative_toLp, inner_add_right, inner_smul_right, hL]
  nlinarith [mul_nonneg hν hS]

/-- **`L²` stability.** Two smooth Navier–Stokes evolutions separate at most like
`exp (K t)`, with `K` a bound on the gradient of the first. -/
theorem l2_stability (hν : 0 ≤ ν) (U V : NSEvolution ν T hT) (K : ℝ)
    (hK : ∀ t x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K) (t : Icc (0 : ℝ) T) :
    ‖(U.difference V t).toLp‖ ≤ ‖(U.difference V ⟨0, le_rfl, hT⟩).toLp‖ * Real.exp (K * t) := by
  have hd (r : ℝ) (hr : r ∈ Ico 0 T) :
      HasDerivWithinAt (extendPath T hT (U.l2EnergyPath V))
        (U.l2EnergyDerivative V (projIcc 0 T hT r)) (Icc 0 T) r := by
    have h := U.l2Energy_hasDerivWithinAt V ⟨r, hr.1, hr.2.le⟩
    simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1, hr.2.le⟩)] using h
  have hb (r : ℝ) (_hr : r ∈ Ico 0 T) :
      U.l2EnergyDerivative V (projIcc 0 T hT r) ≤
        (2 * K) * extendPath T hT (U.l2EnergyPath V) r :=
    U.l2EnergyDerivative_bound hν V K hK (projIcc 0 T hT r)
  have h := linear_stability_within (extendPath T hT (U.l2EnergyPath V))
    (fun r ↦ U.l2EnergyDerivative V (projIcc 0 T hT r)) (2 * K) T
    ((U.l2EnergyPath V).continuous.comp continuous_projIcc).continuousOn hd hb t t.property
  have h2 : ‖(U.difference V t).toLp‖ ^ 2 ≤
      ‖(U.difference V ⟨0, le_rfl, hT⟩).toLp‖ ^ 2 * Real.exp (2 * K * t) := by
    simpa only [extendPath, projIcc_of_mem hT t.property,
      projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩),
      l2EnergyPath, ContinuousMap.coe_mk] using h
  rw [show 2 * K * (t : ℝ) = K * t + K * t by ring, Real.exp_add] at h2
  have hp : 0 ≤ ‖(U.difference V ⟨0, le_rfl, hT⟩).toLp‖ * Real.exp (K * t) := by positivity
  nlinarith [norm_nonneg (U.difference V t).toLp]

/-- **Uniqueness of smooth Navier–Stokes evolutions on `ℝ³`.** Two evolutions with the
same initial velocity agree at every time. -/
theorem velocity_eq_of_initial (hν : 0 ≤ ν) (U V : NSEvolution ν T hT)
    (hinit : (V.velocity ⟨0, le_rfl, hT⟩).toLp = (U.velocity ⟨0, le_rfl, hT⟩).toLp)
    (t : Icc (0 : ℝ) T) : V.velocity t = U.velocity t := by
  -- a gradient bound for `U` from the continuity of its `H³` norm on the compact interval
  obtain ⟨M, hM⟩ : ∃ M, ∀ s, tensorNorm 3 (U.velocity s) ≤ M := by
    have hc : Continuous (fun s ↦ tensorNorm 3 (U.velocity s)) :=
      continuous_finsetSum _ fun n _ ↦ (U.velocity_continuous n).norm
    obtain ⟨M, hM⟩ := (isCompact_univ.image hc).isBounded.bddAbove
    exact ⟨M, fun s ↦ hM ⟨s, Set.mem_univ _, rfl⟩⟩
  have hK : ∀ s x, ‖fderiv ℝ (U.velocity s).field x‖ ≤
      (9 * EulerSmoothSobolev.smoothEmbeddingConstant * M) := by
    intro s x
    have hb := EulerSmoothSobolev.real_smooth_fderiv_le_H3 3 (U.velocity s).field
      (U.velocity s).smooth (fun j _ ↦ (U.velocity s).integrable j) x
    rw [← tensorNorm_eq] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (hM s)
      (mul_nonneg (by norm_num) EulerSmoothSobolev.smoothEmbeddingConstant_nonneg))
  have h := U.l2_stability hν V _ hK t
  simp only [difference, toLp_fieldSub, hinit, sub_self, norm_zero, zero_mul] at h
  apply smoothField_eq_of_toLp_eq
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

end NSEvolution

end Uniqueness

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow
