import Mettapedia.OSLF.NativeTypes.Consumers.PLNEvidenceControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RelationalAnswerFrontDoor

/-!
# Evidence revision through the front door

A revision request has at most one run, computed by `revise?`; so revision has an exact evaluator, and the revision of
one request unfolds into a finite system at the front door (`RelationalAnswers`). Its declared observations are the
answer observation (fresh origin, ordered parents, exact counts, published) and the run observation (every answer of
the run is observed).

- **The revision check is the front door's native type** `◇◇(inRelation "answer")` at the request
  (`check_iff_frontDoor`), and so is the generated two-diamond type of the consumer (`native_iff_frontDoor`).
- **"The request completes and every run is observed"** is `◇⊤ ∧ □(inRelation "run")` (`completes_iff_frontDoor`).
- On the controls' store the generated front door decides, with the kernel evaluating it, that the disjoint request is
  revised (by exploration) and completes with every answer observed (by a closed region), that the request with
  shared evidence is not revised (a closed region), and that the request with an absent origin does not complete.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.PLNEvidence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.RelationalAnswers
open Mettapedia.OSLF.Framework.RelationalAnswerTypeSynthesis (producesAnswerSatisfying)
open Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis (completesOnly)

variable {observations : Nat}

instance (initial : State observations) (request : Request) (final : State observations)
    (answer : Proof observations) : Decidable (observation initial request final answer) := by
  unfold observation
  infer_instance

/-- The runs of a revision request: the published store and proof, when the request is ready. -/
def runs (state : State observations) (request : Request) : List (State observations × List (Proof observations)) :=
  match revise? state request with
  | some (final, answer) => [(final, [answer])]
  | none => []

/-- **Revision's exact evaluator.** -/
def evaluator : Evaluator (source (observations := observations)) where
  evaluate := runs
  exact initial request final answers := by
    constructor
    · intro execution
      obtain ⟨answer, rfl, -⟩ := revision_observation execution
      have computed := (revise?_exact initial request final answer).mpr execution
      simp [runs, computed]
    · intro member
      unfold runs at member
      split at member
      · rename_i final' answer computed
        simp only [List.mem_singleton, Prod.mk.injEq] at member
        obtain ⟨rfl, rfl⟩ := member
        exact (revise?_exact initial request _ _).mp computed
      · simp at member

/-- Every answer of a run is observed. -/
def runObserved (initial : State observations) (request : Request) (final : State observations)
    (answers : List (Proof observations)) : Prop :=
  ∀ answer ∈ answers, observation initial request final answer

instance (initial : State observations) (request : Request) (final : State observations)
    (answers : List (Proof observations)) : Decidable (runObserved initial request final answers) := by
  unfold runObserved
  infer_instance

/-- The revision of one request, unfolded at the front door. -/
def system (state : State observations) (request : Request) : EncodedSystem Node :=
  unfolded (evaluator.runsOf state request) observation runObserved

/-- **The revision check is the front door's native type** `◇◇(inRelation "answer")` at the request. -/
theorem check_iff_frontDoor (state : State observations) (request : Request) :
    check state request = true ↔
      (system state request).observed.reading.sat Env.closed producesFormula (Node.encode .request) :=
  (check_native_exact state request).trans (produces_iff (evaluator.runsOf state request) observation runObserved).symm

/-- **The consumer's generated two-diamond type is the front door's.** -/
theorem native_iff_frontDoor (state : State observations) (request : Request) :
    producesAnswerSatisfying (source (observations := observations)) observation (.request state request) ↔
      (system state request).observed.reading.sat Env.closed producesFormula (Node.encode .request) :=
  (produces_iff (evaluator.runsOf state request) observation runObserved).symm

/-- **The request completes and every run is observed** is the front door's `◇⊤ ∧ □(inRelation "run")`. -/
theorem completes_iff_frontDoor (state : State observations) (request : Request) :
    completesOnly (source (observations := observations)) runObserved (.request state request) ↔
      (system state request).observed.reading.sat Env.closed completesFormula (Node.encode .request) :=
  (completes_iff (evaluator.runsOf state request) observation runObserved).symm

/-- The front door's answer about the revision of a request. -/
def frontAnswer (state : State observations) (request : Request) (formula : Formula 0) (rounds : Nat) : Answer :=
  ask (system state request).observed.env [] systemLanguage 2 formula (Node.encode .request) none rounds

namespace Controls

theorem disjoint_answer : frontAnswer store disjointRequest producesFormula 4 = .proved (.exploration 4) := by
  decide +kernel

/-- **The disjoint request is revised**, found by the front door's exploration. -/
theorem disjoint_revised : check store disjointRequest = true :=
  (check_iff_frontDoor store disjointRequest).mpr (ask_proved disjoint_answer)

theorem shared_answer : frontAnswer store sharedRequest producesFormula 4 = .refuted (.closedRegion 4) := by
  decide +kernel

/-- **The request with shared evidence is not revised**, by a closed region at the front door. -/
theorem shared_not_revised : check store sharedRequest = false := by
  cases checked : check store sharedRequest with
  | false => rfl
  | true => exact absurd ((check_iff_frontDoor store sharedRequest).mp checked) (ask_refuted shared_answer)

theorem disjoint_completes_answer :
    frontAnswer store disjointRequest completesFormula 4 = .proved (.closedRegion 4) := by
  decide +kernel

/-- **The disjoint request completes, and every answer of its run is observed.** -/
theorem disjoint_completes :
    completesOnly (source (observations := 4)) runObserved (.request store disjointRequest) :=
  (completes_iff_frontDoor store disjointRequest).mpr (ask_proved disjoint_completes_answer)

theorem absent_completes_answer :
    frontAnswer store absentRequest completesFormula 4 = .refuted (.closedRegion 4) := by
  decide +kernel

/-- **The request with an absent origin does not complete.** -/
theorem absent_not_completes :
    ¬ completesOnly (source (observations := 4)) runObserved (.request store absentRequest) :=
  fun completes => ask_refuted absent_completes_answer ((completes_iff_frontDoor store absentRequest).mp completes)

end Controls

end Mettapedia.OSLF.NativeTypes.Consumers.PLNEvidence
