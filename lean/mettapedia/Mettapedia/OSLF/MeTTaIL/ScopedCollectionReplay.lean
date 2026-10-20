import Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchReplay

/-!
# Independent checking of collection receipts

Checking follows only the supplied allocation and nested occurrence histories.
It does not rerun allocation search or drain the producer's task agenda.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine

open Syntax RuleBinding ScopedRuleMatching CanonicalBags CollectionSelection
open GeneralScopedMatchMachine

theorem replayArguments_complete {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat}
    {initial final : Assignment} {schemas targets : List Pattern} {trace : List BagChoice}
    (matched : TracedArguments rule spec ambient site path depth initial index schemas targets trace final)
    (suffix : List BagChoice) :
    GeneralScopedMatchReplay.replayArguments rule spec ambient site path depth initial index
      schemas targets (trace ++ suffix) = some (final, suffix) := by
  induction schemas generalizing targets initial final index trace with
  | nil =>
      cases matched
      simp [GeneralScopedMatchReplay.replayArguments]
  | cons schema schemas ih =>
      cases matched with
      | cons head tail =>
          simp only [List.append_assoc, GeneralScopedMatchReplay.replayArguments,
            GeneralScopedMatchReplay.replayAt_complete head,
            GeneralScopedMatchReplay.continueReplay]
          exact ih tail

theorem replayArguments_exact (request : Request) (allocation : Allocation Pattern)
    (trace : List BagChoice) (final : Assignment) :
    GeneralScopedMatchReplay.replayArguments request.rule request.spec request.ambient request.site
      request.path request.depth request.initial request.index request.schemas allocation.values trace =
        some (final, []) ↔
    TracedArguments request.rule request.spec request.ambient request.site request.path
      request.depth request.initial request.index request.schemas allocation.values trace final := by
  constructor
  · intro replayed
    obtain ⟨used, same, matched⟩ :=
      GeneralScopedMatchReplay.replayArguments_sound _ _ _ _ _ _ _ _ _ _ _ replayed
    simp only [List.append_nil] at same
    exact same ▸ matched
  · intro matched
    simpa only [List.append_nil] using replayArguments_complete matched []

theorem allocation_accepts_iff (request : Request) (allocation : Allocation Pattern)
    (answer : GeneralScopedMatchMachine.Answer) :
    StateAccepts request.machine (allocationState request allocation) answer ↔
      ∃ middle,
        TracedArguments request.rule request.spec request.ambient request.site request.path
          request.depth request.initial request.index request.schemas allocation.values answer.trace middle ∧
        ScopedCollectionMatching.Finished request.rule request.spec request.ambient request.site
          request.path request.depth (request.index + request.schemas.length) request.kind
          request.rest middle (arrange request.kind allocation.residual) answer.assignment := by
  cases rest : request.rest with
  | none =>
      cases residual : arrange request.kind allocation.residual with
      | nil =>
          simp only [allocationState, rest, residual, List.isEmpty_nil, ↓reduceIte,
            StateAccepts, List.not_mem_nil, false_or, List.mem_singleton, exists_eq_left,
            workAccepts_singleton, TaskRuns.arguments_iff, List.nil_append]
          constructor
          · rintro ⟨trace, matched, same⟩
            exact ⟨answer.assignment, same ▸ matched, .empty⟩
          · rintro ⟨middle, matched, finished⟩
            cases finished
            exact ⟨_, matched, rfl⟩
      | cons value values =>
          simp only [allocationState, rest, residual, List.isEmpty_cons, Bool.false_eq_true,
            ↓reduceIte, StateAccepts, List.not_mem_nil, false_and, exists_false, or_self]
          refine ⟨False.elim, ?_⟩
          rintro ⟨middle, _, finished⟩
          cases finished
  | some name =>
      simp only [allocationState, rest, StateAccepts, List.not_mem_nil, false_or,
        List.mem_singleton, exists_eq_left, workAccepts_pair,
        TaskRuns.arguments_iff, TaskRuns.restCapture_iff, List.nil_append]
      constructor
      · rintro ⟨middle, first, second, matched, ⟨rfl, captured⟩, same⟩
        simp only [List.append_nil] at same
        exact ⟨middle, same ▸ matched, .captured captured⟩
      · rintro ⟨middle, matched, finished⟩
        cases finished with
        | captured captured =>
            exact ⟨middle, answer.trace, [], matched, ⟨rfl, captured⟩, by simp⟩

def replayAssignment (request : Request) (allocation : Allocation Pattern)
    (trace : List BagChoice) : Option Assignment := do
  let (middle, remaining) ←
    GeneralScopedMatchReplay.replayArguments request.rule request.spec request.ambient request.site
      request.path request.depth request.initial request.index request.schemas allocation.values trace
  if !remaining.isEmpty then none
  else
    let residual := arrange request.kind allocation.residual
    match request.rest with
    | none => if residual.isEmpty then some middle else none
    | some name =>
        captureRest? request.rule request.spec request.ambient request.depth request.site
          (request.path ++ [request.index + request.schemas.length]) middle name request.kind residual

theorem replayAssignment_exact (request : Request) (allocation : Allocation Pattern)
    (answer : GeneralScopedMatchMachine.Answer) :
    replayAssignment request allocation answer.trace = some answer.assignment ↔
      StateAccepts request.machine (allocationState request allocation) answer := by
  rw [allocation_accepts_iff]
  have finish (middle : Assignment) :
      (match request.rest with
       | none => if (arrange request.kind allocation.residual).isEmpty then some middle else none
       | some name =>
           captureRest? request.rule request.spec request.ambient request.depth request.site
             (request.path ++ [request.index + request.schemas.length]) middle name request.kind
             (arrange request.kind allocation.residual)) = some answer.assignment ↔
      ScopedCollectionMatching.Finished request.rule request.spec request.ambient request.site
        request.path request.depth (request.index + request.schemas.length) request.kind
        request.rest middle (arrange request.kind allocation.residual) answer.assignment := by
    rw [← ScopedCollectionMatching.finish_exact]
    cases request.rest with
    | none =>
        simp only [ScopedCollectionMatching.finish]
        split <;> simp only [Option.some.injEq, List.mem_singleton, List.not_mem_nil,
          reduceCtorEq]
        exact eq_comm
    | some name => simp [ScopedCollectionMatching.finish]
  constructor
  · intro accepted
    cases result : GeneralScopedMatchReplay.replayArguments request.rule request.spec request.ambient request.site
        request.path request.depth request.initial request.index request.schemas allocation.values answer.trace with
    | none => simp [replayAssignment, result] at accepted
    | some pair =>
        rcases pair with ⟨middle, remaining⟩
        cases remaining with
        | cons => simp [replayAssignment, result] at accepted
        | nil =>
            refine ⟨middle, (replayArguments_exact request allocation _ _).mp result, ?_⟩
            apply (finish middle).mp
            simpa [replayAssignment, result] using accepted
  · rintro ⟨middle, matched, finished⟩
    have replayed := (replayArguments_exact request allocation _ _).mpr matched
    have completed := (finish middle).mpr finished
    simpa [replayAssignment, replayed] using completed

def checkReceipt (request : Request) (receipt : Receipt) : Bool :=
  decide (receipt.allocation.decisions.length = request.schemas.length) &&
    decide (CollectionSelection.replay (request.kind == .hashSet) request.targets
      receipt.allocation.decisions = some receipt.allocation.erase) &&
    decide (replayAssignment request receipt.allocation receipt.matching.trace = some receipt.matching.assignment)

theorem checkReceipt_exact (request : Request) (receipt : Receipt) :
    checkReceipt request receipt = true ↔ Valid request receipt := by
  simp only [checkReceipt, Bool.and_eq_true, decide_eq_true_eq,
    replayAssignment_exact, Valid, and_assoc]

theorem published_checked (request : Request) (fuel : Nat) {receipt : Receipt}
    (published : receipt ∈ publication (resume request fuel (start request))) :
    checkReceipt request receipt = true :=
  (checkReceipt_exact request receipt).mpr (publication_sound request fuel published)

end Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine
