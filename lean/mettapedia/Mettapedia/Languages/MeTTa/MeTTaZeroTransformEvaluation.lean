import Mettapedia.Languages.MeTTa.MeTTaZeroWorkClosure

/-!
# Evaluation as one transform that routes between work and answers

`MeTTaZeroWorkClosure` shows that the one-step answer bag of Zero evaluation cannot tell "nothing
interpreted the subject" from "an interpretation produced the subject again"
(`evaluationStatus_not_factors_through_answers`), and that bare Zero has no composable steps. This
module reads one evaluation step as a firing of a transform with two rules and two destinations:

* every interpreted result of the subject (an equation row or a grounded alternative) is sent to the
  **work** channel (`workPart`);
* when there is no row, an absence condition holds, and the subject itself is sent to the **answer**
  channel (`answerPart`).

One firing is the sum of the two (`evaluationFiring`).

## What routing retains

* Erasing the channels gives exactly the Zero answer bag (`evaluationFiring_values`).
* The channel recovers the status the bag forgets (`status_factors_through_firing`): the fibre that
  refutes the factorization through the bag is resolved by the routed firing
  (`routing_retains_what_the_bag_forgets`).

## The traced transform

Feeding the work channel back as pending subjects gives one rewriting system on pending work and
delivered answers (`loopGSLT`). It has composable steps (`loop_has_composable_steps`), and it is
adequate for the status-aware runner of `MeTTaZeroWorkClosure`: an answer is delivered by some run
exactly when the runner completes with it (`loop_delivers_iff_runner_completes`).

## What remains

* **The answer route is an absence decision.** Adding an equation to the space withdraws an answer the
  smaller space delivered (`answer_not_stable_under_new_equation`). The loop is sound for a space held
  fixed while it runs: the program is a stage, and the routing to answers is not monotone in it.
* **Divergence is silent.** A productive self-loop never delivers an answer
  (`selfLoop_never_answers`); the traced transform computes the answers of the completed runs, its
  least fixed point, and nothing for the others.
* **Raw and evaluative destinations.** A raw destination writes a template instance as data. An
  evaluative destination sends it to the work channel and delivers what the loop answers. Under a
  program that interprets nothing, the evaluative destination delivers exactly the instance
  (`evaluative_eq_raw_of_empty_program`).
-/

namespace Mettapedia.Languages.MeTTa.MeTTaZero

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.ClosureCriteria
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-! ## One firing with two destinations -/

/-- Where a firing of the evaluation transform sends what it emits. -/
inductive Channel where
  | work
  | answer
  deriving DecidableEq, Repr

/-- The rule over the rows: every interpreted result goes to the work channel. -/
def workPart (model : Model) (space : model.Space) (subject : Pattern) :
    Multiset (Channel × Pattern) :=
  (interpretedResults model space subject).map fun result => (.work, result)

/-- The rule over the absence of rows: the subject itself goes to the answer channel. -/
def answerPart (model : Model) (space : model.Space) (subject : Pattern) :
    Multiset (Channel × Pattern) :=
  if interpretedResults model space subject = 0 then {(.answer, subject)} else 0

/-- **One firing of the evaluation transform**: the sum of its two rules. -/
def evaluationFiring (model : Model) (space : model.Space) (subject : Pattern) :
    Multiset (Channel × Pattern) :=
  workPart model space subject + answerPart model space subject

theorem evaluationFiring_of_uninterpreted (model : Model) (space : model.Space) (subject : Pattern)
    (empty : interpretedResults model space subject = 0) :
    evaluationFiring model space subject = {(.answer, subject)} := by
  simp [evaluationFiring, workPart, answerPart, empty]

theorem evaluationFiring_of_interpreted (model : Model) (space : model.Space) (subject : Pattern)
    (nonempty : interpretedResults model space subject ≠ 0) :
    evaluationFiring model space subject =
      (interpretedResults model space subject).map fun result => (.work, result) := by
  simp [evaluationFiring, workPart, answerPart, nonempty]

/-- **Erasing the channels gives the Zero answer bag.** -/
theorem evaluationFiring_values (model : Model) (space : model.Space) (subject : Pattern) :
    (evaluationFiring model space subject).map Prod.snd = evaluateOne model space subject := by
  by_cases empty : interpretedResults model space subject = 0
  · simp [evaluationFiring_of_uninterpreted model space subject empty, evaluateOne, empty]
  · simp [evaluationFiring_of_interpreted model space subject empty, evaluateOne, empty,
      Multiset.map_map]

/-- Read the status off a routed firing: an emission on the answer channel means inert. -/
def statusOfFiring (firing : Multiset (Channel × Pattern)) : EvaluationStatus :=
  if Channel.answer ∈ firing.map Prod.fst then .inert else .produced

/-- **The channel determines the status.** -/
theorem statusOfFiring_evaluationFiring (model : Model) (space : model.Space) (subject : Pattern) :
    statusOfFiring (evaluationFiring model space subject) =
      (evaluateReported model space subject).status := by
  by_cases empty : interpretedResults model space subject = 0
  · simp [statusOfFiring, evaluationFiring_of_uninterpreted model space subject empty,
      evaluateReported, empty]
  · rw [evaluationFiring_of_interpreted model space subject empty]
    simp [statusOfFiring, evaluateReported, empty, Multiset.map_map, Multiset.mem_replicate]

/-- An evaluation problem: a model, a space of it and a subject. -/
abbrev EvaluationInput := Σ model : Model, model.Space × Pattern

/-- **The status factors through the routed firing**, for every model, space and subject. -/
theorem status_factors_through_firing :
    Factors (fun input : EvaluationInput => evaluationFiring input.1 input.2.1 input.2.2)
      (fun input : EvaluationInput => (evaluateReported input.1 input.2.1 input.2.2).status) :=
  ⟨statusOfFiring, fun input => statusOfFiring_evaluationFiring input.1 input.2.1 input.2.2⟩

/-- The routed firing on either side of the status canary. -/
def statusCanaryFiring : StatusCanary → Multiset (Channel × Pattern)
  | .inert => evaluationFiring inertStatusCanaryModel (0 : Multiset Pattern) statusCanarySubject
  | .productive =>
      evaluationFiring productiveStatusCanaryModel (0 : Multiset Pattern) statusCanarySubject

/-- **Routing retains what the answer bag forgets**: on the canary the status does not factor through
the bag, and it does factor through the routed firing. -/
theorem routing_retains_what_the_bag_forgets :
    ¬ Factors statusCanaryAnswers statusCanaryStatus ∧
      Factors statusCanaryFiring statusCanaryStatus := by
  refine ⟨evaluationStatus_not_factors_through_answers, statusOfFiring, ?_⟩
  intro canary
  cases canary
  · exact statusOfFiring_evaluationFiring _ _ _
  · exact statusOfFiring_evaluationFiring _ _ _

/-! ## The traced transform -/

/-- What a firing sends to one channel. -/
def emitted (channel : Channel) (firing : Multiset (Channel × Pattern)) : Multiset Pattern :=
  (firing.filter fun emission => emission.1 = channel).map Prod.snd

theorem emitted_work (model : Model) (space : model.Space) (subject : Pattern) :
    emitted .work (evaluationFiring model space subject) = interpretedResults model space subject := by
  by_cases empty : interpretedResults model space subject = 0
  · simp [emitted, evaluationFiring_of_uninterpreted model space subject empty, empty]
  · rw [evaluationFiring_of_interpreted model space subject empty]
    simp [emitted, Multiset.filter_map, Multiset.map_map]

theorem emitted_answer (model : Model) (space : model.Space) (subject : Pattern) :
    emitted .answer (evaluationFiring model space subject) =
      if interpretedResults model space subject = 0 then {subject} else 0 := by
  by_cases empty : interpretedResults model space subject = 0
  · simp [emitted, evaluationFiring_of_uninterpreted model space subject empty, empty,
      Multiset.filter_singleton]
  · rw [evaluationFiring_of_interpreted model space subject empty]
    simp [emitted, Multiset.filter_map, empty]

/-- A state of the traced transform: pending subjects and delivered answers. -/
structure LoopState where
  work : Multiset Pattern
  answers : Multiset Pattern

/-- **One step of the traced transform**: fire on one pending subject; its work is pending again, its
answers are delivered. -/
inductive LoopStep (model : Model) (space : model.Space) : LoopState → LoopState → Prop
  | fire {work answers : Multiset Pattern} {subject : Pattern} (pending : subject ∈ work) :
      LoopStep model space ⟨work, answers⟩
        ⟨work.erase subject + emitted .work (evaluationFiring model space subject),
          answers + emitted .answer (evaluationFiring model space subject)⟩

/-- The traced transform as a rewriting system. -/
def loopGSLT (model : Model) (space : model.Space) : GSLT where
  Term := LoopState
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := LoopStep model space
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact Exists.intro target <| And.intro step rfl
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- **The traced transform has composable steps.** -/
theorem loop_has_composable_steps :
    HasComposableSteps (loopGSLT chainModel chainSpace) := by
  have first : (loopGSLT chainModel chainSpace).Step ⟨{chainA}, 0⟩ ⟨{chainB}, 0⟩ := by
    have step := LoopStep.fire (model := chainModel) (space := chainSpace) (answers := 0)
      (Multiset.mem_singleton_self chainA)
    rw [emitted_work chainModel chainSpace chainA, emitted_answer chainModel chainSpace chainA,
      chain_interpretedResults_a] at step
    show LoopStep chainModel chainSpace _ _
    simpa using step
  have second : (loopGSLT chainModel chainSpace).Step ⟨{chainB}, 0⟩ ⟨{chainC}, 0⟩ := by
    have step := LoopStep.fire (model := chainModel) (space := chainSpace) (answers := 0)
      (Multiset.mem_singleton_self chainB)
    rw [emitted_work chainModel chainSpace chainB, emitted_answer chainModel chainSpace chainB,
      chain_interpretedResults_b] at step
    show LoopStep chainModel chainSpace _ _
    simpa using step
  exact ⟨{ source := _, middle := _, target := _, first := first, second := second }⟩

/-! ## Adequacy for the status-aware runner -/

section Adequacy

variable {model : Model} {space : model.Space}

private theorem multiStep_tail {theory : GSLT} {t u v : theory.Term}
    (run : theory.MultiStep t u) (last : theory.Step u v) : theory.MultiStep t v := by
  induction run with
  | refl _ => exact .step last (.refl _)
  | step first _ ih => exact .step first (ih last)

private theorem completed_multiStep {a : Pattern} {trace : List Nat} {u : (iterativeGSLT model).Term}
    (run : (iterativeGSLT model).MultiStep (.completed space a trace) u) :
    u = .completed space a trace := by
  match run with
  | .refl _ => rfl
  | .step first _ => cases first

private theorem mem_interpreted_of_produced {subject answer : Pattern} {answers : Multiset Pattern}
    {occurrence : Nat} (reported : evaluateReported model space subject = .produced answers)
    (copy : occurrence < Multiset.count answer answers) :
    answer ∈ interpretedResults model space subject := by
  have nonempty : interpretedResults model space subject ≠ 0 := by
    intro empty
    rw [evaluateReported_of_uninterpreted model space subject empty] at reported
    cases reported
  rw [evaluateReported_of_interpreted model space subject nonempty] at reported
  cases reported
  exact Multiset.count_pos.mp (Nat.zero_lt_of_lt copy)

/-- **Completeness**: when the runner completes with an answer, some run of the traced transform
delivers it, whatever else is pending. -/
theorem loop_delivers_of_runner_completes : ∀ {t u : (iterativeGSLT model).Term},
    (iterativeGSLT model).MultiStep t u →
      ∀ {subject trace}, t = .pending space subject trace →
        ∀ {a trace'}, u = .completed space a trace' →
          ∀ work answers, ∃ X, Relation.ReflTransGen (LoopStep model space)
            ⟨subject ::ₘ work, answers⟩ X ∧ a ∈ X.answers := by
  intro t u run
  induction run with
  | refl _ =>
      intro subject trace hs a trace' hu
      rw [hs] at hu
      cases hu
  | @step t₁ t₂ t₃ first rest ih =>
      intro subject trace hs a trace' hu work answers
      subst hs
      cases first with
      | @produced _ _ answersBag next occurrence _ reported copy =>
          have member := mem_interpreted_of_produced reported copy
          obtain ⟨others, split⟩ := Multiset.exists_cons_of_mem member
          obtain ⟨X, reach, delivered⟩ := ih rfl hu (work + others)
            (answers + emitted .answer (evaluationFiring model space subject))
          refine ⟨X, Relation.ReflTransGen.head ?_ reach, delivered⟩
          have step := LoopStep.fire (model := model) (space := space) (answers := answers)
            (Multiset.mem_cons_self subject work)
          rw [emitted_work, split, Multiset.erase_cons_head] at step
          simpa [Multiset.add_cons, add_comm] using step
      | inert reported =>
          have empty : interpretedResults model space subject = 0 :=
            (evaluateReported_status_inert_iff model space subject).mp (by rw [reported]; rfl)
          have same := completed_multiStep rest
          rw [hu] at same
          cases same
          refine ⟨_, Relation.ReflTransGen.single (LoopStep.fire (answers := answers)
            (Multiset.mem_cons_self subject work)), ?_⟩
          simp [emitted_answer, empty]

/-- **Soundness**: along any run of the traced transform from one subject, every pending subject is
reached by the runner, and every delivered answer is a completion of the runner. -/
theorem loop_sound {subject : Pattern} {X : LoopState}
    (reach : Relation.ReflTransGen (LoopStep model space) ⟨{subject}, 0⟩ X) :
    (∀ w ∈ X.work, ∃ trace,
        (iterativeGSLT model).MultiStep (.pending space subject []) (.pending space w trace)) ∧
      (∀ a ∈ X.answers, ∃ trace,
        (iterativeGSLT model).MultiStep (.pending space subject []) (.completed space a trace)) := by
  induction reach with
  | refl =>
      refine ⟨fun w member => ⟨[], ?_⟩, fun a member => by simp at member⟩
      rw [Multiset.mem_singleton.mp member]
      exact .refl _
  | @tail Y Z _ step ih =>
      obtain ⟨pendingOk, answersOk⟩ := ih
      cases step with
      | @fire work answers fired pending =>
          obtain ⟨trace, toFired⟩ := pendingOk fired pending
          constructor
          · intro w member
            rcases Multiset.mem_add.mp member with stillPending | produced
            · exact pendingOk w (Multiset.mem_of_mem_erase stillPending)
            · rw [emitted_work] at produced
              have nonempty : interpretedResults model space fired ≠ 0 := by
                intro empty
                rw [empty] at produced
                simp at produced
              refine ⟨0 :: trace, multiStep_tail toFired ?_⟩
              apply IterativeStep.produced (answers := interpretedResults model space fired)
              · exact evaluateReported_of_interpreted model space fired nonempty
              · exact Multiset.count_pos.mpr produced
          · intro a member
            rcases Multiset.mem_add.mp member with old | delivered
            · exact answersOk a old
            · rw [emitted_answer] at delivered
              by_cases empty : interpretedResults model space fired = 0
              · rw [if_pos empty, Multiset.mem_singleton] at delivered
                subst delivered
                exact ⟨trace, multiStep_tail toFired
                  (IterativeStep.inert (evaluateReported_of_uninterpreted model space a empty))⟩
              · rw [if_neg empty] at delivered
                simp at delivered

/-- **The traced transform delivers exactly the completions of the status-aware runner.** -/
theorem loop_delivers_iff_runner_completes (subject a : Pattern) :
    (∃ X, Relation.ReflTransGen (LoopStep model space) ⟨{subject}, 0⟩ X ∧ a ∈ X.answers) ↔
      ∃ trace, (iterativeGSLT model).MultiStep (.pending space subject [])
        (.completed space a trace) := by
  constructor
  · rintro ⟨X, reach, delivered⟩
    exact (loop_sound reach).2 a delivered
  · rintro ⟨trace, run⟩
    simpa using loop_delivers_of_runner_completes run rfl rfl 0 0

end Adequacy

/-! ## What remains -/

/-- A fourth chain atom. -/
def chainD : Pattern := .apply "zero-chain-d" []

/-- An equation for the last link of the chain. -/
def chainCD : Pattern := .apply "=" [chainC, chainD]

/-- The chain's space with that equation added. -/
def extendedChainSpace : Multiset Pattern := chainCD ::ₘ chainSpace

theorem extended_interpretedResults_c :
    interpretedResults chainModel extendedChainSpace chainC = {chainD} := by
  simp [chainModel, extendedChainSpace, chainSpace, chainAB, chainBC, chainCD, chainA, chainB,
    chainC, chainD, structuralModel, interpretedResults, equationResults, queryAll, query,
    viewEquation?, matchPattern, matchArgs, applyBindings]

/-- **The answer route is an absence decision**: the smaller space delivers `chainC` as an answer, and
adding one equation withdraws it. -/
theorem answer_not_stable_under_new_equation :
    chainSpace ≤ extendedChainSpace ∧
      (Channel.answer, chainC) ∈ evaluationFiring chainModel chainSpace chainC ∧
      (Channel.answer, chainC) ∉ evaluationFiring chainModel extendedChainSpace chainC := by
  refine ⟨Multiset.le_cons_self _ _, ?_, ?_⟩
  · rw [evaluationFiring_of_uninterpreted chainModel chainSpace chainC chain_interpretedResults_c]
    simp
  · rw [evaluationFiring_of_interpreted chainModel extendedChainSpace chainC
      (by rw [extended_interpretedResults_c]; simp), extended_interpretedResults_c]
    simp

/-- **Divergence is silent**: on a productive self-loop no run delivers an answer. -/
theorem selfLoop_never_answers {X : LoopState}
    (reach : Relation.ReflTransGen (LoopStep productiveStatusCanaryModel (0 : Multiset Pattern))
      ⟨{statusCanarySubject}, 0⟩ X) :
    X.answers = 0 := by
  have invariant : X.answers = 0 ∧ ∀ w ∈ X.work, w = statusCanarySubject := by
    induction reach with
    | refl => exact ⟨rfl, fun w member => Multiset.mem_singleton.mp member⟩
    | tail _ step ih =>
        obtain ⟨noAnswers, onlyCanary⟩ := ih
        cases step with
        | @fire work answers fired pending =>
            have isCanary := onlyCanary fired pending
            subst isCanary
            have results : interpretedResults productiveStatusCanaryModel (0 : Multiset Pattern)
                statusCanarySubject = {statusCanarySubject} := by
              simp [productiveStatusCanaryModel, structuralModel, interpretedResults,
                equationResults, queryAll, query]
            dsimp only at noAnswers onlyCanary ⊢
            refine ⟨?_, fun w member => ?_⟩
            · rw [emitted_answer productiveStatusCanaryModel (0 : Multiset Pattern) statusCanarySubject,
                results, noAnswers]
              simp
            · rw [emitted_work productiveStatusCanaryModel (0 : Multiset Pattern) statusCanarySubject,
                results] at member
              rcases Multiset.mem_add.mp member with old | new
              · exact onlyCanary w (Multiset.mem_of_mem_erase old)
              · exact Multiset.mem_singleton.mp new
  exact invariant.1

/-- **Under a program that interprets nothing, an evaluative destination delivers exactly the
instance**, as a raw destination writes it. -/
theorem evaluative_eq_raw_of_empty_program (instance' a : Pattern) :
    (∃ X, Relation.ReflTransGen
        (LoopStep (structuralModel fun _ => 0) (0 : Multiset Pattern)) ⟨{instance'}, 0⟩ X ∧
          a ∈ X.answers) ↔ a = instance' := by
  have empty : ∀ subject, interpretedResults (structuralModel fun _ => 0)
      (0 : Multiset Pattern) subject = 0 := by
    intro subject
    simp [structuralModel, interpretedResults, equationResults, queryAll, query]
  refine (loop_delivers_iff_runner_completes (model := structuralModel fun _ => 0)
    (space := (0 : Multiset Pattern)) instance' a).trans ?_
  constructor
  · rintro ⟨trace, run⟩
    match run with
    | .step first rest =>
        cases first with
        | produced reported copy =>
            rw [evaluateReported_of_uninterpreted _ _ _ (empty _)] at reported
            cases reported
        | inert reported =>
            have same := completed_multiStep rest
            cases same
            rfl
  · rintro rfl
    exact ⟨[], .step (IterativeStep.inert (evaluateReported_of_uninterpreted _ _ _ (empty _)))
      (.refl _)⟩

end Mettapedia.Languages.MeTTa.MeTTaZero
