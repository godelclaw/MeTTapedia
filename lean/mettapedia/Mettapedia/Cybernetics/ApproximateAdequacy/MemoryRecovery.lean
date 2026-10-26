import Mettapedia.GSLT.Logic.TaskRelativeMemory
import Mettapedia.Cybernetics.ApproximateAdequacy.RecoveryDecision
import Mettapedia.InformationTheory.MarkovRecovery

/-!
# Task-sufficient memory and statistical reconstruction

A score that factors through a deterministic memory has exactly the same
expectation before and after supported reference recovery. Thus exact task
memory transfers approximate optimality without additional regret, even when
reconstructing the complete hidden state has positive KL loss. Scores outside
the supported family instead use the quantitative `RecoveryDecision` bounds.

All statistical statements here concern finite state distributions. They do
not assign a uniform law to an unbounded space of observation histories.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateAdequacy.MemoryRecovery

open scoped BigOperators
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.InformationTheory.FiniteRecovery
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.TaskRelativeMemory

variable {State Memory : Type*} [Fintype State] [Fintype Memory] [DecidableEq Memory]

/-- Supported recovery preserves every score computed solely from memory. -/
theorem expectation_eq_of_factors (p q : Prob State) (memory : State → Memory)
    (support : ∀ state, 0 < p.1 state → 0 < q.1 state) (score : State → ℝ)
    (retained : Factors memory score) :
    (∑ state, (recover q memory (Prob.coarsen p memory)).1 state * score state) =
      ∑ state, p.1 state * score state := by
  obtain ⟨read, agrees⟩ := retained
  have pointwise : score = read ∘ memory := (funext agrees).symm
  rw [pointwise]
  simp only [Function.comp_apply]
  rw [← Prob.coarsen_expectation (recover q memory (Prob.coarsen p memory)) memory read,
    coarsen_recover q memory _ (coarsen_support p q memory support)]
  exact Prob.coarsen_expectation p memory read

/-- A supplied future-task realization gives exact expectation preservation. -/
theorem future_expectation_eq {Input Query : Type*}
    (step : State → Input → State) (observe : Query → State → ℝ)
    (p q : Prob State) (memory : State → Memory)
    (support : ∀ state, 0 < p.1 state → 0 < q.1 state)
    (realization : (futureFamily step observe).ReadoutRealization memory)
    (word : List Input) (query : Query) :
    (∑ state, (recover q memory (Prob.coarsen p memory)).1 state *
        observe query (word.foldl step state)) =
      ∑ state, p.1 state * observe query (word.foldl step state) :=
  expectation_eq_of_factors p q memory support _
    ⟨realization.run (word, query), realization.agrees (word, query)⟩

/-- Sufficient task memory transfers approximate optimality with no compression penalty. -/
theorem regret_le_eta {Candidate : Type*} (p q : Prob State) (memory : State → Memory)
    (support : ∀ state, 0 < p.1 state → 0 < q.1 state)
    (score : Candidate → State → ℝ) (admissible : Candidate → Prop)
    (retained : ∀ candidate, admissible candidate → Factors memory (score candidate))
    (selected : Candidate) (selected_admissible : admissible selected) (η : ℝ)
    (best : ∀ candidate, admissible candidate →
      (∑ state, (recover q memory (Prob.coarsen p memory)).1 state * score candidate state) ≤
        (∑ state, (recover q memory (Prob.coarsen p memory)).1 state * score selected state) + η)
    (alternative : Candidate) (alternative_admissible : admissible alternative) :
    (∑ state, p.1 state * score alternative state) -
      (∑ state, p.1 state * score selected state) ≤ η := by
  have bound := best alternative alternative_admissible
  rw [expectation_eq_of_factors p q memory support _ (retained alternative alternative_admissible),
    expectation_eq_of_factors p q memory support _ (retained selected selected_admissible)] at bound
  linarith

section MarkovDecisions

variable {Ω α β γ Candidate : Type*} [Fintype Ω]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-- A bounded joint readout pays its range times the CMI reconstruction budget. -/
theorem markov_expectation_error (p : Prob Ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ)
    (score : α × β × γ → ℝ) {lo hi : ℝ} (ordered : lo ≤ hi)
    (lower : ∀ state, lo ≤ score state) (upper : ∀ state, score state ≤ hi) :
    |(∑ state, (MarkovRecovery.jointLaw p f g h).1 state * score state) -
        ∑ state, (MarkovRecovery.projectionLaw p f g h).1 state * score state| ≤
      ((hi - lo) / 2) * Real.sqrt (2 * condMutualInfo p.1 f g h) := by
  have bound := RecoveryDecision.expectation_error (MarkovRecovery.jointLaw p f g h)
    (MarkovRecovery.reference p f g h) MarkovRecovery.retainAB (MarkovRecovery.supported p f g h)
    score ordered lower upper
  rwa [MarkovRecovery.recover_eq_projectionLaw, MarkovRecovery.loss_eq_cmi] at bound

/-- Approximate choice under a PLN-style Markov projection has CMI-bounded regret. -/
theorem markov_regret_le (p : Prob Ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ)
    (score : Candidate → α × β × γ → ℝ) (admissible : Candidate → Prop)
    {lo hi : ℝ} (ordered : lo ≤ hi)
    (lower : ∀ candidate, admissible candidate → ∀ state, lo ≤ score candidate state)
    (upper : ∀ candidate, admissible candidate → ∀ state, score candidate state ≤ hi)
    (selected : Candidate) (eligible : admissible selected) (η : ℝ)
    (best : ∀ candidate, admissible candidate →
      (∑ state, (MarkovRecovery.projectionLaw p f g h).1 state * score candidate state) ≤
        (∑ state, (MarkovRecovery.projectionLaw p f g h).1 state * score selected state) + η)
    (alternative : Candidate) (alternative_eligible : admissible alternative) :
    (∑ state, (MarkovRecovery.jointLaw p f g h).1 state * score alternative state) -
        (∑ state, (MarkovRecovery.jointLaw p f g h).1 state * score selected state) ≤
      (hi - lo) * Real.sqrt (2 * condMutualInfo p.1 f g h) + η := by
  have bound := RecoveryDecision.regret_le (MarkovRecovery.jointLaw p f g h)
    (MarkovRecovery.reference p f g h) MarkovRecovery.retainAB (MarkovRecovery.supported p f g h)
    score admissible ordered lower upper selected eligible η
    (by simpa only [MarkovRecovery.recover_eq_projectionLaw] using best)
    alternative alternative_eligible
  rwa [MarkovRecovery.loss_eq_cmi] at bound

end MarkovDecisions

namespace Controls

abbrev HiddenState := Bool × Bool

/-- Inputs can change the visible bit, while the hidden bit is unobserved. -/
def step (state : HiddenState) (flip : Bool) : HiddenState := (xor state.1 flip, state.2)

def observe (_ : Unit) (state : HiddenState) : ℝ := if state.1 then 1 else 0

def visibleRealization : Realization step observe (Prod.fst : HiddenState → Bool) where
  update visible flip := xor visible flip
  read _ visible := if visible then 1 else 0
  update_agrees _ _ := rfl
  read_agrees _ _ := rfl

theorem hidden_tags_same_profile :
    profile step observe (false, false) = profile step observe (false, true) := by
  have sufficient := (supports_iff_constant step observe (Prod.fst : HiddenState → Bool)).mp
    ⟨visibleRealization.futureRealization⟩
  exact sufficient _ _ rfl

/-- An exact implementation may retain more than the minimal task memory. -/
def fullRealization : Realization step observe (id : HiddenState → HiddenState) where
  update := step
  read := observe
  update_agrees _ _ := rfl
  read_agrees _ _ := rfl

theorem profile_does_not_determine_full_memory :
    ¬ Factors (profile step observe) (id : HiddenState → HiddenState) :=
  NonTrivialFiber.not_factors ⟨(false, false), (false, true), hidden_tags_same_profile, by decide⟩

noncomputable def actual : Prob HiddenState := Prob.dirac (false, false)

noncomputable def reference : Prob HiddenState :=
  ⟨fun _ => 1 / 4, (fun _ => by norm_num), by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]⟩

theorem supported : ∀ state, 0 < actual.1 state → 0 < reference.1 state := by
  intro state _
  norm_num [reference]

/-- Forgetting the hidden bit preserves every future visible answer in expectation. -/
theorem all_future_tasks_exact (word : List Bool) :
    (∑ state, (recover reference Prod.fst (Prob.coarsen actual Prod.fst)).1 state *
        observe () (word.foldl step state)) =
      ∑ state, actual.1 state * observe () (word.foldl step state) :=
  future_expectation_eq step observe actual reference Prod.fst supported
    visibleRealization.futureRealization word ()

theorem reconstructed_hidden_distribution :
    (recover reference Prod.fst (Prob.coarsen actual Prod.fst)).1 (false, false) = 1 / 2 := by
  rw [recover_apply reference Prod.fst _ (coarsen_support actual reference Prod.fst supported)]
  norm_num [reference, actual, Prob.coarsen_dirac, Prob.dirac_apply,
    Prob.coarsen_apply, pushforward_fst, Fintype.sum_bool]

/-- Exact future-task memory need not preserve the full hidden-state distribution. -/
theorem exact_tasks_positive_reconstruction_loss : 0 < klLoss actual reference Prod.fst := by
  have nonnegative := klLoss_nonneg actual reference Prod.fst supported
  apply lt_of_le_of_ne nonnegative
  intro zero
  have exact := (recover_eq_iff_klLoss_eq_zero actual reference Prod.fst supported).mpr zero.symm
  have atSource := congrArg (fun law : Prob HiddenState => law.1 (false, false)) exact
  rw [reconstructed_hidden_distribution] at atSource
  norm_num [actual, Prob.dirac_apply] at atSource

/-- The visible task family is nonconstant. -/
theorem observes_distinction : observe () (false, false) ≠ observe () (true, false) := by
  norm_num [observe]

end Controls

end Mettapedia.Cybernetics.ApproximateAdequacy.MemoryRecovery
