import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Finite-horizon solutions of dissipative finite-dimensional ODEs

A compactly supported smooth cutoff gives a globally bounded Lipschitz
vector field. Dissipation keeps its trajectory inside the region where
the cutoff is one, so the constructed curve solves the original equation.
The result is for every finite horizon, without assuming a continuation
theorem or an already existing trajectory.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeDissipativeFiniteODE

open scoped ContDiff RealInnerProductSpace NNReal
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A bounded globally Lipschitz autonomous vector field has a solution
on any prescribed finite nonnegative interval, differentiable also at its endpoints. -/
theorem exists_bounded_lipschitz_solution (F : E → E) (K L : ℝ≥0)
    (hK : LipschitzWith K F) (hL : ∀ x, ‖F x‖ ≤ L)
    (x₀ : E) (T : ℝ) (hT : 0 ≤ T) :
    ∃ a : ℝ → E, a 0 = x₀ ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt a (F (a t)) t := by
  let t₀ : Icc (-1 : ℝ) (T + 1) := ⟨0, by constructor <;> linarith⟩
  let R : ℝ≥0 := ⟨(L : ℝ) * (T + 1), by positivity⟩
  have hp : IsPicardLindelof (fun _ ↦ F) t₀ x₀ R 0 L K := by
    refine ⟨fun _ _ ↦ hK.lipschitzOnWith, fun _ _ ↦ continuousOn_const,
      fun _ _ x _ ↦ hL x, ?_⟩
    change (L : ℝ) * max (T + 1 - 0) (0 - -1) ≤ (L : ℝ) * (T + 1) - 0
    rw [sub_zero, zero_sub, neg_neg, sub_zero, max_eq_left (by linarith)]
  obtain ⟨a, ha0, ha⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨a, ha0, fun t ht ↦ ?_⟩
  have hleft : (-1 : ℝ) < t := by linarith [ht.1]
  have hright : t < T + 1 := by linarith [ht.2]
  exact (ha t ⟨hleft.le, hright.le⟩).hasDerivAt (Icc_mem_nhds hleft hright)

omit [FiniteDimensional ℝ E] in
/-- Dissipation controls the norm of any curve solving the vector field. -/
theorem norm_le_initial_of_dissipative (F : E → E)
    (hF : ∀ x, ⟪x, F x⟫ ≤ 0) (a : ℝ → E) (T : ℝ)
    (ha : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt a (F (a t)) t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖a t‖ ≤ ‖a 0‖ := by
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) := (ha s hs).norm_sq
  have hm : AntitoneOn (fun s ↦ ‖a s‖ ^ 2) (Icc (0 : ℝ) T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt
    · exact fun s hs ↦ (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hd s (interior_subset hs)).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hF (a s))
  have hb := hm ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  nlinarith [norm_nonneg (a t), norm_nonneg (a 0)]

/-- Smooth dissipative finite-dimensional dynamics can be constructed on
any finite forward interval. The auxiliary compact cutoff is inactive on
the entire output trajectory. -/
theorem exists_dissipative_solution (F : E → E) (hF : ContDiff ℝ ∞ F)
    (hD : ∀ x, ⟪x, F x⟫ ≤ 0) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) :
    ∃ a : ℝ → E, a 0 = x₀ ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt a (F (a t)) t) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ‖a t‖ ≤ ‖x₀‖ := by
  let b : ContDiffBump (0 : E) := {
    rIn := ‖x₀‖ + 1
    rOut := 2 * (‖x₀‖ + 1)
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith [norm_nonneg x₀] }
  let G : E → E := fun x ↦ b x • F x
  have hG : ContDiff ℝ ∞ G := b.contDiff.smul hF
  have hcompact : HasCompactSupport G := b.hasCompactSupport.smul_right
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hG (by simp)
  obtain ⟨L, hL⟩ := hcompact.exists_bound_of_continuous hG.continuous
  let L' : ℝ≥0 := ⟨max L 0, le_max_right _ _⟩
  have hL' (x : E) : ‖G x‖ ≤ L' := (hL x).trans (le_max_left _ _)
  obtain ⟨a, ha0, ha⟩ := exists_bounded_lipschitz_solution G K L' hK hL' x₀ T hT
  have hGD (x : E) : ⟪x, G x⟫ ≤ 0 := by
    dsimp [G]
    rw [inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos b.nonneg (hD x)
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖a t‖ ≤ ‖x₀‖ := by
    simpa only [ha0] using norm_le_initial_of_dissipative G hGD a T ha t ht
  refine ⟨a, ha0, fun t ht ↦ ?_, hb⟩
  have hone : b (a t) = 1 := b.one_of_mem_closedBall (by
    rw [mem_closedBall, dist_zero_right]
    change ‖a t‖ ≤ ‖x₀‖ + 1
    linarith [hb t ht])
  simpa only [G, hone, one_smul] using ha t ht

end Mettapedia.FluidDynamics.NavierStokes.PancakeDissipativeFiniteODE
