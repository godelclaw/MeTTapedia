import Mettapedia.InformationTheory.Pinsker

/-!
# Recovery from finite deterministic observations

The reference law supplies the conditional detail discarded by an observation.
Every recovery row is normalized; a zero-reference observation uses the reference
law itself. Supported inputs give those fallback rows zero weight. The exact
information-loss identity concerns deterministic observations, not noisy channels.
-/

set_option autoImplicit false

namespace Mettapedia.InformationTheory.FiniteRecovery

open Finset Real
open FiniteRV

variable {Ω C D : Type*} [Fintype Ω] [Fintype C] [DecidableEq C]

/-- Conditional reference law on a positive-mass fibre, with a normalized fallback. -/
noncomputable def recoveryKernel (q : Prob Ω) (view : Ω → C) (c : C) : Prob Ω :=
  if possible : 0 < pushforward q.1 view c then
    ⟨fun x => (if view x = c then q.1 x else 0) / pushforward q.1 view c,
      (fun x => div_nonneg (by split_ifs; exact q.2.1 x; exact le_rfl) possible.le), by
        rw [← Finset.sum_div, ← pushforward_eq_sum_ite]
        exact div_self possible.ne'⟩
  else q

/-- Recover a coarse distribution by stochastic prediction through the reference rows. -/
noncomputable def recover (q : Prob Ω) (view : Ω → C) (r : Prob C) : Prob Ω :=
  Prob.bind r (recoveryKernel q view)

omit [Fintype C] in
@[simp] theorem recoveryKernel_apply_pos (q : Prob Ω) (view : Ω → C) (c : C)
    (possible : 0 < pushforward q.1 view c) (x : Ω) :
    (recoveryKernel q view c).1 x =
      (if view x = c then q.1 x else 0) / pushforward q.1 view c := by
  simp only [recoveryKernel, dif_pos possible]

omit [Fintype C] in
@[simp] theorem recoveryKernel_of_zero (q : Prob Ω) (view : Ω → C) (c : C)
    (zero : pushforward q.1 view c = 0) : recoveryKernel q view c = q := by
  simp only [recoveryKernel, zero, lt_self_iff_false, ↓reduceDIte]

omit [Fintype C] in
/-- Off-fibre entries vanish on every observation with positive reference mass. -/
theorem recoveryKernel_off_fiber (q : Prob Ω) (view : Ω → C) {c : C}
    (possible : 0 < pushforward q.1 view c) {x : Ω} (different : view x ≠ c) :
    (recoveryKernel q view c).1 x = 0 := by
  simp only [recoveryKernel_apply_pos q view c possible, if_neg different, zero_div]

/-- Supported incoming observations recover the reference conditional proportions. -/
theorem recover_apply (q : Prob Ω) (view : Ω → C) (r : Prob C)
    (support : ∀ c, 0 < r.1 c → 0 < pushforward q.1 view c) (x : Ω) :
    (recover q view r).1 x = q.1 x * r.1 (view x) / pushforward q.1 view (view x) := by
  classical
  change (∑ c, r.1 c * (recoveryKernel q view c).1 x) = _
  rw [Finset.sum_eq_single (view x)]
  · by_cases possible : 0 < pushforward q.1 view (view x)
    · rw [recoveryKernel_apply_pos q view (view x) possible, if_pos rfl]
      ring
    · have zero : r.1 (view x) = 0 := le_antisymm
        (le_of_not_gt (fun positive => possible (support _ positive))) (r.2.1 _)
      simp [zero]
  · intro c _ different
    by_cases positive : 0 < r.1 c
    · rw [recoveryKernel_off_fiber q view (support _ positive) (Ne.symm different), mul_zero]
    · have zero : r.1 c = 0 := le_antisymm (le_of_not_gt positive) (r.2.1 c)
      rw [zero, zero_mul]
  · simp

/-- Coarsening preserves absolute continuity. -/
theorem coarsen_support (p q : Prob Ω) (view : Ω → C)
    (support : ∀ x, 0 < p.1 x → 0 < q.1 x) :
    ∀ c, 0 < (Prob.coarsen p view).1 c → 0 < pushforward q.1 view c := by
  intro c positive
  obtain ⟨x, same, positive⟩ := (pushforward_pos_iff p.1 p.2.1 view c).mp positive
  exact lt_of_lt_of_le (support x positive) (same ▸ le_pushforward q.1 q.2.1 view x)

/-- The reference itself is recovered exactly, even when some fibres have zero mass. -/
theorem recover_reference (q : Prob Ω) (view : Ω → C) :
    recover q view (Prob.coarsen q view) = q := by
  apply Subtype.ext
  funext x
  rw [recover_apply q view _ (fun _ h => h)]
  by_cases positive : 0 < pushforward q.1 view (view x)
  · exact mul_div_cancel_right₀ (q.1 x) positive.ne'
  · have zero : q.1 x = 0 := le_antisymm
      (le_of_not_gt (fun h => positive (pushforward_pos_of_pos q.1 q.2.1 view h))) (q.2.1 x)
    simp [zero]

/-- Recompression is exact for inputs supported by the observed reference law. -/
theorem coarsen_recover (q : Prob Ω) (view : Ω → C) (r : Prob C)
    (support : ∀ c, 0 < r.1 c → 0 < pushforward q.1 view c) :
    Prob.coarsen (recover q view r) view = r := by
  apply Subtype.ext
  funext c
  change pushforward (recover q view r).1 view c = r.1 c
  have formula : pushforward (recover q view r).1 view c =
      pushforward q.1 view c * r.1 c / pushforward q.1 view c := by
    unfold pushforward
    rw [mul_div_assoc, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x member
    rw [recover_apply q view r support, (Finset.mem_filter.mp member).2]
    exact mul_div_assoc _ _ _
  rw [formula]
  by_cases possible : 0 < pushforward q.1 view c
  · exact mul_div_cancel_left₀ (r.1 c) possible.ne'
  · have zero : r.1 c = 0 := le_antisymm
      (le_of_not_gt (fun positive => possible (support _ positive))) (r.2.1 c)
    simp [zero]

/-- The original source law is supported by its recovered approximation. -/
theorem source_supported_recover (p q : Prob Ω) (view : Ω → C)
    (support : ∀ x, 0 < p.1 x → 0 < q.1 x) :
    ∀ x, 0 < p.1 x → 0 < (recover q view (Prob.coarsen p view)).1 x := by
  intro x positive
  rw [recover_apply q view _ (coarsen_support p q view support)]
  exact div_pos (mul_pos (support x positive)
    (pushforward_pos_of_pos p.1 p.2.1 view positive))
    (pushforward_pos_of_pos q.1 q.2.1 view (support x positive))

/-- Natural-log information discarded by the supplied deterministic observation. -/
noncomputable def klLoss (p q : Prob Ω) (view : Ω → C) : ℝ :=
  klSum p.1 q.1 - klSum (Prob.coarsen p view).1 (Prob.coarsen q view).1

theorem klLoss_nonneg (p q : Prob Ω) (view : Ω → C)
    (support : ∀ x, 0 < p.1 x → 0 < q.1 x) : 0 ≤ klLoss p q view :=
  sub_nonneg.mpr (klSum_pushforward_le p.1 q.1 view p.2.1 q.2.1 support)

/-- Deterministic recovery accounts exactly for the information discarded by observation. -/
theorem klLoss_eq_recovery_divergence (p q : Prob Ω) (view : Ω → C)
    (support : ∀ x, 0 < p.1 x → 0 < q.1 x) :
    klLoss p q view = klSum p.1 (recover q view (Prob.coarsen p view)).1 := by
  have term (x : Ω) :
      p.1 x * log (p.1 x / (recover q view (Prob.coarsen p view)).1 x) =
        p.1 x * log (p.1 x / q.1 x) -
          p.1 x * log (pushforward p.1 view (view x) / pushforward q.1 view (view x)) := by
    by_cases positive : 0 < p.1 x
    · have hq := support x positive
      have hP := pushforward_pos_of_pos p.1 p.2.1 view positive
      have hQ := pushforward_pos_of_pos q.1 q.2.1 view hq
      rw [recover_apply q view _ (coarsen_support p q view support)]
      change p.1 x * log (p.1 x / (q.1 x * pushforward p.1 view (view x) /
        pushforward q.1 view (view x))) = _
      rw [Real.log_div positive.ne' (div_pos (mul_pos hq hP) hQ).ne',
        Real.log_div (mul_pos hq hP).ne' hQ.ne', Real.log_mul hq.ne' hP.ne',
        Real.log_div positive.ne' hq.ne', Real.log_div hP.ne' hQ.ne']
      ring
    · have zero : p.1 x = 0 := le_antisymm (le_of_not_gt positive) (p.2.1 x)
      simp [zero]
  unfold klLoss
  rw [klSum_eq_sum, klSum_eq_sum, klSum_eq_sum, Finset.sum_congr rfl (fun x _ => term x),
    Finset.sum_sub_distrib]
  congr 1
  exact sum_pushforward_mul p.1 view
    (fun c => log (pushforward p.1 view c / pushforward q.1 view c))

/-- Exact reconstruction is equivalent to losing no divergence for this pair of laws. -/
theorem recover_eq_iff_klLoss_eq_zero (p q : Prob Ω) (view : Ω → C)
    (support : ∀ x, 0 < p.1 x → 0 < q.1 x) :
    recover q view (Prob.coarsen p view) = p ↔ klLoss p q view = 0 := by
  constructor
  · intro exactRecovery
    rw [klLoss_eq_recovery_divergence p q view support, exactRecovery]
    exact klSum_self_eq_zero p.1 p.2.1
  · intro zero
    apply Subtype.ext
    funext x
    exact (klSumOn_eq_zero_imp Finset.univ p.1 _ (fun x _ => p.2.1 x)
      (fun x _ => (recover q view (Prob.coarsen p view)).2.1 x)
      (fun x _ => source_supported_recover p q view support x)
      (by rw [p.2.2, (recover q view (Prob.coarsen p view)).2.2])
      (by change klSum p.1 _ = 0; rw [← klLoss_eq_recovery_divergence p q view support, zero])
      x (Finset.mem_univ x)).symm

/-- Agreement with the independent proportional-fibre equality criterion. -/
theorem recover_eq_iff_proportional (p q : Prob Ω) (view : Ω → C)
    (support : ∀ x, 0 < p.1 x → 0 < q.1 x) :
    recover q view (Prob.coarsen p view) = p ↔
      ∀ x, p.1 x * pushforward q.1 view (view x) =
        q.1 x * pushforward p.1 view (view x) := by
  rw [recover_eq_iff_klLoss_eq_zero p q view support, klLoss, sub_eq_zero, eq_comm]
  exact klSum_pushforward_eq_iff p.1 q.1 view p.2.1 q.2.1 support

/-- Pinsker transports the exact discarded-information budget to reconstruction error. -/
theorem recovery_l1_sq_le (p q : Prob Ω) (view : Ω → C)
    (support : ∀ x, 0 < p.1 x → 0 < q.1 x) :
    (∑ x, |p.1 x - (recover q view (Prob.coarsen p view)).1 x|)^2 ≤
      2 * klLoss p q view := by
  rw [klLoss_eq_recovery_divergence p q view support]
  exact l1_sq_le_two_klSum p _ (source_supported_recover p q view support)

/-- The unsquared reconstruction bound uses the natural-log Pinsker constant. -/
theorem recovery_l1_le (p q : Prob Ω) (view : Ω → C)
    (support : ∀ x, 0 < p.1 x → 0 < q.1 x) :
    (∑ x, |p.1 x - (recover q view (Prob.coarsen p view)).1 x|) ≤
      sqrt (2 * klLoss p q view) := by
  have nonneg : 0 ≤ ∑ x, |p.1 x - (recover q view (Prob.coarsen p view)).1 x| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  rw [← sqrt_sq nonneg]
  exact sqrt_le_sqrt (recovery_l1_sq_le p q view support)

/-- Successive deterministic coarsenings add their discarded-information budgets. -/
theorem klLoss_comp [Fintype D] [DecidableEq D] (p q : Prob Ω)
    (first : Ω → C) (second : C → D) :
    klLoss p q (second ∘ first) = klLoss p q first +
      klLoss (Prob.coarsen p first) (Prob.coarsen q first) second := by
  unfold klLoss
  rw [Prob.coarsen_comp, Prob.coarsen_comp]
  ring

omit [Fintype C] in
/-- Recovery cannot introduce mass outside the reference support. -/
theorem recoveryKernel_supported (q : Prob Ω) (view : Ω → C) (c : C) :
    ∀ x, 0 < (recoveryKernel q view c).1 x → 0 < q.1 x := by
  intro x positive
  by_cases possible : 0 < pushforward q.1 view c
  · rw [recoveryKernel_apply_pos q view c possible] at positive
    have numerator := (div_pos_iff_of_pos_right possible).mp positive
    split_ifs at numerator with same
    · exact numerator
    · exact (lt_irrefl _ numerator).elim
  · simpa only [recoveryKernel, dif_neg possible] using positive

/-- Reference-conditioned recovery composes through successive deterministic observations. -/
theorem recoveryKernel_comp [Fintype D] [DecidableEq D] (q : Prob Ω)
    (first : Ω → C) (second : C → D) (d : D) :
    recover q first (recoveryKernel (Prob.coarsen q first) second d) =
      recoveryKernel q (second ∘ first) d := by
  have mass : pushforward (Prob.coarsen q first).1 second d =
      pushforward q.1 (second ∘ first) d := pushforward_pushforward q.1 first second d
  by_cases possible : 0 < pushforward q.1 (second ∘ first) d
  · apply Subtype.ext
    funext x
    rw [recover_apply q first _ (recoveryKernel_supported (Prob.coarsen q first) second d),
      recoveryKernel_apply_pos q (second ∘ first) d possible,
      recoveryKernel_apply_pos (Prob.coarsen q first) second d (mass.symm ▸ possible)]
    change q.1 x * ((if second (first x) = d then pushforward q.1 first (first x) else 0) /
      pushforward (Prob.coarsen q first).1 second d) / pushforward q.1 first (first x) = _
    rw [mass]
    by_cases same : second (first x) = d
    · simp only [same, Function.comp_apply, ↓reduceIte]
      by_cases positive : 0 < pushforward q.1 first (first x)
      · field_simp
      · have zero : q.1 x = 0 := le_antisymm
          (le_of_not_gt (fun h => positive (pushforward_pos_of_pos q.1 q.2.1 first h))) (q.2.1 x)
        simp [zero]
    · simp [Function.comp_apply, same]
  · have zero : pushforward q.1 (second ∘ first) d = 0 :=
      le_antisymm (le_of_not_gt possible) (pushforward_nonneg q.1 q.2.1 _ d)
    rw [recoveryKernel_of_zero q _ d zero,
      recoveryKernel_of_zero (Prob.coarsen q first) second d (mass.trans zero)]
    exact recover_reference q first

/-- Entire reconstructed laws inherit the two-stage kernel composition theorem. -/
theorem recover_comp [Fintype D] [DecidableEq D] (q : Prob Ω)
    (first : Ω → C) (second : C → D) (r : Prob D) :
    recover q first (recover (Prob.coarsen q first) second r) =
      recover q (second ∘ first) r := by
  change Prob.bind (Prob.bind r _) _ = Prob.bind r _
  rw [Prob.bind_assoc]
  congr 1
  funext d
  exact recoveryKernel_comp q first second d

/-- Injective observations recover every source supported by the reference. -/
theorem recover_of_injective (p q : Prob Ω) (view : Ω → C)
    (support : ∀ x, 0 < p.1 x → 0 < q.1 x) (injective : Function.Injective view) :
    recover q view (Prob.coarsen p view) = p := by
  apply (recover_eq_iff_klLoss_eq_zero p q view support).mpr
  change klSum p.1 q.1 - klSum (pushforward p.1 view) (pushforward q.1 view) = 0
  rw [klSum_pushforward_of_injective p.1 q.1 view p.2.1 q.2.1 support injective, sub_self]

namespace Controls

noncomputable def reference : Prob (Fin 3) :=
  ⟨![1/4, 1/4, 1/2], (by intro x; fin_cases x <;> norm_num), by norm_num [Fin.sum_univ_succ]⟩
noncomputable def source : Prob (Fin 3) :=
  ⟨![1/8, 1/8, 3/4], (by intro x; fin_cases x <;> norm_num), by norm_num [Fin.sum_univ_succ]⟩
def mergedView (x : Fin 3) : Bool := decide (x.val = 2)

private theorem reference_positive (x : Fin 3) : 0 < reference.1 x := by
  fin_cases x <;> norm_num [reference]

/-- A real noninjective compression can nevertheless recover this source exactly. -/
theorem noninjective_exact :
    mergedView 0 = mergedView 1 ∧ (0 : Fin 3) ≠ 1 ∧
      recover reference mergedView (Prob.coarsen source mergedView) = source := by
  refine ⟨rfl, by decide, ?_⟩
  apply (recover_eq_iff_proportional source reference mergedView
    (fun x _ => reference_positive x)).mpr
  intro x
  fin_cases x <;> norm_num [source, reference, pushforward_eq_sum_ite,
    mergedView, Fin.sum_univ_succ]

private theorem coarsen_unit (p : Prob (Fin 2)) :
    Prob.coarsen p (fun _ => ()) = Prob.dirac () := by
  apply Subtype.ext
  funext u
  simp [Prob.coarsen_apply, pushforward_eq_sum_ite, Prob.dirac_apply, p.2.2]

/-- Observing a constant discards the source law and reconstructs the reference. -/
theorem constant_recover (p q : Prob (Fin 2)) :
    recover q (fun _ => ()) (Prob.coarsen p (fun _ => ())) = q := by
  have equal : Prob.coarsen p (fun _ => ()) = Prob.coarsen q (fun _ => ()) := by
    rw [coarsen_unit, coarsen_unit]
  rw [equal, recover_reference]

/-- A constant observation loses the fair-reference information of a point mass. -/
theorem constant_loss :
    klLoss (Prob.dirac (0 : Fin 2)) (binaryDist (1/2) (by norm_num) (by norm_num))
      (fun _ => ()) = log 2 := by
  rw [klLoss_eq_recovery_divergence _ _ _
    (by intro x _; fin_cases x <;> norm_num [binaryDist]), constant_recover, klSum_eq_sum]
  norm_num [Prob.dirac_apply, binaryDist, Fin.sum_univ_two]

theorem constant_loss_positive :
    0 < klLoss (Prob.dirac (0 : Fin 2)) (binaryDist (1/2) (by norm_num) (by norm_num))
      (fun _ => ()) := by
  rw [constant_loss]
  exact Real.log_pos (by norm_num)

/-- Zero-reference rows are normalized fallbacks, not a global inverse to observation. -/
theorem zero_reference_row : recoveryKernel (Prob.dirac (0 : Fin 2)) id 1 = Prob.dirac 0 := by
  apply recoveryKernel_of_zero
  norm_num [pushforward_eq_sum_ite, Fin.sum_univ_two, Prob.dirac_apply]

/-- An observation outside the image also receives the normalized fallback law. -/
theorem unreachable_row :
    recoveryKernel (Prob.dirac (0 : Fin 2)) (fun _ => (0 : Fin 3)) 2 = Prob.dirac 0 := by
  apply recoveryKernel_of_zero
  simp [pushforward_eq_sum_ite]

/-- With unsupported inputs the real-log loss can be zero despite failed reconstruction. -/
theorem unsupported_zero_loss :
    klLoss (Prob.dirac (1 : Fin 2)) (Prob.dirac 0) id = 0 ∧
      recover (Prob.dirac 0) id (Prob.coarsen (Prob.dirac (1 : Fin 2)) id) ≠ Prob.dirac 1 := by
  refine ⟨by simp [klLoss, Prob.coarsen_id], ?_⟩
  rw [Prob.coarsen_id, recover, Prob.bind_dirac, zero_reference_row]
  intro equal
  have atZero := congrArg (fun law : Prob (Fin 2) => law.1 0) equal
  norm_num [Prob.dirac_apply] at atZero

end Controls

end Mettapedia.InformationTheory.FiniteRecovery
