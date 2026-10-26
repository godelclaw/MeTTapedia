import Mettapedia.InformationTheory.FiniteRecovery
import Mettapedia.ProbabilityTheory.BayesianInference.Basic

/-!
# Markov projection as reference-conditioned recovery

The reference law is independently constructed as `P_A ⊗ P_BC`. Recovering
the actual `AB` marginal through that reference yields `P_AB P_BC / P_B`,
the established Markov projection. Its reconstruction divergence is exactly
conditional mutual information. This identifies the approximation used by
PLN deduction with the same recovery operation used for belief compression.

The construction includes zero marginal masses; support is derived from the
actual joint law rather than postulated for positive cells only.
-/

set_option autoImplicit false

namespace Mettapedia.InformationTheory.MarkovRecovery

open scoped BigOperators
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.InformationTheory.FiniteRecovery
open Mettapedia.ProbabilityTheory.BayesianInference

variable {Ω α β γ : Type*} [Fintype Ω]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

def retainAB (state : α × β × γ) : α × β := (state.1, state.2.1)

noncomputable def jointLaw (p : Prob Ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    Prob (α × β × γ) := Prob.coarsen p (fun world => (f world, g world, h world))

/-- Independent product of the `A` marginal with the `BC` joint marginal. -/
noncomputable def reference (p : Prob Ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    Prob (α × β × γ) :=
  joint (Prob.coarsen p f) (fun _ => Prob.coarsen p (fun world => (g world, h world)))

/-- The established projection, bundled independently as a normalized law. -/
noncomputable def projectionLaw (p : Prob Ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    Prob (α × β × γ) :=
  ⟨markovProjection p.1 f g h, markovProjection_nonneg p.1 p.2.1 f g h, by
    rw [sum_markovProjection p.1 p.2.1 f g h, p.2.2]⟩

theorem reference_apply (p : Prob Ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ)
    (state : α × β × γ) :
    (reference p f g h).1 state =
      pushforward p.1 f state.1 * law2 p.1 g h state.2 := rfl

omit [DecidableEq γ] in
theorem retainAB_apply (law : Prob (α × β × γ)) (a : α) (b : β) :
    (Prob.coarsen law retainAB).1 (a, b) = ∑ c, law.1 (a, b, c) := by
  simp [Prob.coarsen_apply, pushforward_eq_sum_ite, Fintype.sum_prod_type, retainAB,
    Prod.mk.injEq, ite_and]
  rw [Finset.sum_comm]
  simp

theorem reference_retained (p : Prob Ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ)
    (state : α × β) :
    (Prob.coarsen (reference p f g h) retainAB).1 state =
      pushforward p.1 f state.1 * pushforward p.1 g state.2 := by
  rw [retainAB_apply]
  simp only [reference_apply, ← Finset.mul_sum, sum_law2_right]

theorem joint_retained (p : Prob Ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    Prob.coarsen (jointLaw p f g h) retainAB = Prob.coarsen p (fun world => (f world, g world)) :=
  Prob.coarsen_comp p _ _

theorem supported (p : Prob Ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    ∀ state, 0 < (jointLaw p f g h).1 state → 0 < (reference p f g h).1 state := by
  intro state positive
  change 0 < law3 p.1 f g h state at positive
  rw [reference_apply]
  exact mul_pos
    (positive.trans_le ((law3_le_law2_fg p.1 p.2.1 f g h state).trans
      (law2_le_pushforward_fst p.1 p.2.1 f g (state.1, state.2.1))))
    (positive.trans_le (law3_le_law2_gh p.1 p.2.1 f g h state))

/-- Recovery is identified with the independently defined Markov projection. -/
theorem recover_eq_projection (p : Prob Ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ)
    (state : α × β × γ) :
    (recover (reference p f g h) retainAB (Prob.coarsen (jointLaw p f g h) retainAB)).1 state =
      markovProjection p.1 f g h state := by
  rw [recover_apply _ _ _ (coarsen_support _ _ _ (supported p f g h)), reference_apply,
    ← Prob.coarsen_apply (reference p f g h) retainAB (retainAB state),
    reference_retained, joint_retained, Prob.coarsen_apply, markovProjection_eq_ratio]
  change pushforward p.1 f state.1 * law2 p.1 g h state.2 * law2 p.1 f g (state.1, state.2.1) /
    (pushforward p.1 f state.1 * pushforward p.1 g state.2.1) = _
  by_cases zeroA : pushforward p.1 f state.1 = 0
  · have zeroAB : law2 p.1 f g (state.1, state.2.1) = 0 :=
      le_antisymm ((law2_le_pushforward_fst p.1 p.2.1 f g (state.1, state.2.1)).trans_eq zeroA)
        (pushforward_nonneg p.1 p.2.1 _ _)
    simp [zeroA, zeroAB]
  · by_cases zeroB : pushforward p.1 g state.2.1 = 0
    · simp [zeroB]
    · field_simp

theorem recover_eq_projectionLaw (p : Prob Ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    recover (reference p f g h) retainAB (Prob.coarsen (jointLaw p f g h) retainAB) =
      projectionLaw p f g h := Subtype.ext (funext (recover_eq_projection p f g h))

theorem recovery_divergence_eq_cmi (p : Prob Ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    klSum (jointLaw p f g h).1
      (recover (reference p f g h) retainAB (Prob.coarsen (jointLaw p f g h) retainAB)).1 =
        condMutualInfo p.1 f g h := by
  have recovered := funext (recover_eq_projection p f g h)
  rw [recovered]
  exact klSum_law3_markovProjection_eq_condMutualInfo p.1 p.2.1 f g h

theorem loss_eq_cmi (p : Prob Ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    klLoss (jointLaw p f g h) (reference p f g h) retainAB = condMutualInfo p.1 f g h := by
  rw [klLoss_eq_recovery_divergence _ _ _ (supported p f g h), recovery_divergence_eq_cmi]

/-- An endpoint query consumes no more than the recovery information budget. -/
theorem endpoint_divergence_le_loss (p : Prob Ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ) :
    klSum (law2 p.1 f h) (markovProjectionAC p.1 f g h) ≤
      klLoss (jointLaw p f g h) (reference p f g h) retainAB := by
  let reconstructed := recover (reference p f g h) retainAB
    (Prob.coarsen (jointLaw p f g h) retainAB)
  have bound := klSum_pushforward_le (jointLaw p f g h).1 reconstructed.1
    (fun state => (state.1, state.2.2)) (jointLaw p f g h).2.1 reconstructed.2.1
    (source_supported_recover _ _ _ (supported p f g h))
  have reconstructed_eq : reconstructed.1 = markovProjection p.1 f g h :=
    funext (recover_eq_projection p f g h)
  have budget : klSum (jointLaw p f g h).1 reconstructed.1 =
      klLoss (jointLaw p f g h) (reference p f g h) retainAB :=
    (klLoss_eq_recovery_divergence _ _ _ (supported p f g h)).symm
  have bounded := bound.trans_eq budget
  rw [show (jointLaw p f g h).1 = law3 p.1 f g h from rfl, reconstructed_eq,
    ← law2_fh_eq_pushforward_law3] at bounded
  exact bounded

end Mettapedia.InformationTheory.MarkovRecovery
