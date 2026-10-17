import Mettapedia.Machines.BranchLocalNeed.WeightedResumption
import Mettapedia.GSLT.Distinction.LevelAccounts

/-!
# Qualified replay of Need histories

The Need machine's production account is a run account of its event
histories (`NeedWeightedResumption.coefficientAccount` with production-only
factors).  Replaying an alternative history between the same two machine
states is therefore qualified, for that account, exactly when the two
histories' production ledgers denote the same coefficient
(`replay_iff_production_ledger`); and then the replay is qualified inside any
parent history (`replay_in_parent`).  Equal endpoints are not the condition:
the coefficients are monoid elements without inverses, so no potential exists
whose differences they are (for an ordered account two routes with the same
endpoints and trace are not interchangeable,
`LevelAccounts.Controls.grid_ordered_replay_not_qualified`).

The transition work of the same histories is a second, independent reading
(`historyEventPath_length`); a replay may preserve the production account and
change it, or keep it and change the production account.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.Machines.BranchLocalNeed.NeedQualifiedReplay

open Mettapedia.GSLT.Distinction.LevelAccounts
open Mettapedia.GSLT.Causality.OccurrenceMachineHistory
open Mettapedia.OSLF.Binding
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.Machines.BranchLocalNeed.NeedWeightedResumption
open Mettapedia.Machines.BranchLocalNeed.NeedInteractionValuation
open Mettapedia.Machines.BranchLocalNeed.NeedCacheLaws (CompletedReceipt)
open Mettapedia.Machines.BranchLocalNeed.NeedInferenceControl.Reference (pathMachine)
open Mettapedia.Algebra.SharedCoefficientLedger (denote)

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect V : Type} [Monoid V]
variable (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)

/-- **Replaying an alternative Need history is qualified for the production
account exactly when the two production ledgers denote the same
coefficient.** -/
theorem replay_iff_production_ledger
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V)
    (initial : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {before after : RewriteEventHistory.State (system (pathMachine spec initial))}
    (first second : Quiver.Path before after) :
    QualifiedReplay (coefficientAccount spec (productionCoefficient coefficient) initial)
        (source := before) (target := after) first second ↔
      denote (productionLedger spec coefficient (historyEventPath spec initial first)) =
        denote (productionLedger spec coefficient (historyEventPath spec initial second)) := by
  unfold QualifiedReplay
  rw [production_history_account, production_history_account]

/-- **A qualified replay stays qualified inside any parent history.** -/
theorem replay_in_parent
    (coefficient : CompletedReceipt Value StableFault RetryableFault → V)
    (initial : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {start before after finish : RewriteEventHistory.State (system (pathMachine spec initial))}
    (first second : Quiver.Path before after)
    (sameLedger : denote (productionLedger spec coefficient (historyEventPath spec initial first)) =
      denote (productionLedger spec coefficient (historyEventPath spec initial second)))
    (prefixHistory : Quiver.Path start before) (suffixHistory : Quiver.Path after finish) :
    denote (productionLedger spec coefficient
        (historyEventPath spec initial ((prefixHistory.comp first).comp suffixHistory))) =
      denote (productionLedger spec coefficient
        (historyEventPath spec initial ((prefixHistory.comp second).comp suffixHistory))) := by
  have qualified := ((replay_iff_production_ledger spec coefficient initial first second).mpr
    sameLedger).inContext (C := RewriteEventHistory.HistoryCategory (system (pathMachine spec initial)))
    prefixHistory suffixHistory
  unfold QualifiedReplay at qualified
  rw [← production_history_account, ← production_history_account]
  have assocFirst : (prefixHistory.comp first).comp suffixHistory =
      prefixHistory.comp (first.comp suffixHistory) := Quiver.Path.comp_assoc _ _ _
  have assocSecond : (prefixHistory.comp second).comp suffixHistory =
      prefixHistory.comp (second.comp suffixHistory) := Quiver.Path.comp_assoc _ _ _
  rw [assocFirst, assocSecond]
  exact qualified

/-! ## Source replay with arbitrary coefficient monoids

The successor-index interpreter retains the entire Need endpoint and the
ordered production ledger. Its suffix operation keeps an incoming ledger;
it does not replay external services or grant execution authority. Coefficients
are independent of the natural-number successor positions and transition clock.
The current history interface still fixes the source carrier universes at Type.
-/

open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.GSLT.Dynamics.WeightedBranchingResumption
open Mettapedia.Algebra.SharedCoefficientLedger
open Mettapedia.Machines.BranchLocalNeed.NeedInteractionAuthority
open Mettapedia.Machines.BranchLocalNeed.NeedCacheLaws

section TraceReplay

variable {Coefficient : Type}

/- `pathMachine` and `historyEventPath` are stated at `Type`. This helper
matches that API so both concrete runs instantiate one induction. Lifting
the helper to `Type*` is open until the history API is. The induction
below is the proof of replay; it is not an extra premise. -/
variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type}

/-- One production factor of the state about to step. Administrative and
cached instructions contribute `none`. The spec is not an argument: this
reader does not step. -/
def traceProductionFactor?
    (assignment : CompletedReceipt Value StableFault RetryableFault → Coefficient)
    (before : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Option (Factor (CellId × ReceiptId) (Produced Value StableFault RetryableFault) Coefficient) :=
  (productionReceipt? before).map fun receipt =>
    ⟨(receipt.cell, receipt.id), receipt.outcome, assignment receipt⟩

/-- Successor-index replay. A missing index is `none`. The ledger is the
production factors in source order, not a second stored calculus. `spec` is
present because the reader calls `step`. -/
def traceReplay
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (assignment : CompletedReceipt Value StableFault RetryableFault → Coefficient)
    (before : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    List Nat →
      Option (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect ×
        Ledger (CellId × ReceiptId) (Produced Value StableFault RetryableFault) Coefficient)
  | [] => some (before, [])
  | index :: rest =>
      (step spec before)[index]?.bind fun after =>
        (traceReplay spec assignment after rest).map fun later =>
          (later.1, (traceProductionFactor? assignment before).toList ++ later.2)

/-- Replay the suffix and keep an already-earned ledger in front of it. -/
def traceReplayFrom
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (assignment : CompletedReceipt Value StableFault RetryableFault → Coefficient)
    (incoming : Ledger (CellId × ReceiptId) (Produced Value StableFault RetryableFault) Coefficient)
    (before : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (trace : List Nat) :
    Option (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect ×
      Ledger (CellId × ReceiptId) (Produced Value StableFault RetryableFault) Coefficient) :=
  (traceReplay spec assignment before trace).map fun later => (later.1, incoming ++ later.2)

theorem trace_replay_append
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (assignment : CompletedReceipt Value StableFault RetryableFault → Coefficient)
    (before : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (first second : List Nat) :
    traceReplay spec assignment before (first ++ second) =
      (traceReplay spec assignment before first).bind fun earlier =>
        (traceReplay spec assignment earlier.1 second).map fun later =>
          (later.1, earlier.2 ++ later.2) := by
  induction first generalizing before with
  | nil =>
      simp only [List.nil_append, traceReplay.eq_1, Option.bind_some]
      cases traceReplay spec assignment before second with
      | none => rfl
      | some later =>
          simp
  | cons index rest ih =>
      simp only [List.cons_append, traceReplay.eq_2]
      cases found : (step spec before)[index]? with
      | none => rfl
      | some after =>
          simp only [Option.bind_some]
          rw [ih after]
          cases hrest : traceReplay spec assignment after rest with
          | none =>
              simp
          | some earlier =>
              simp only [Option.bind_some]
              cases hsecond : traceReplay spec assignment earlier.1 second with
              | none =>
                  simp [hsecond]
              | some final =>
                  simp [hsecond, List.append_assoc]

/-- Forgetting the production account gives the independently defined
occurrence-machine replay. This holds for every source state and coefficient
interpretation, including unsuccessful successor lookups. -/
theorem trace_replay_follows
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (assignment : CompletedReceipt Value StableFault RetryableFault → Coefficient)
    (initial before : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (trace : List Nat) :
    (traceReplay spec assignment before trace).map Prod.fst =
      (pathMachine spec initial).follow before trace := by
  induction trace generalizing before with
  | nil => rfl
  | cons index rest ih =>
      simp only [traceReplay, Mettapedia.Machines.OccurrenceMachineCore.follow, pathMachine]
      cases (step spec before)[index]? with
      | none => rfl
      | some after =>
          simp only [Option.bind_some, Option.map_map, Function.comp_def]
          exact ih after

theorem one_step_trace_ledger
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (assignment : CompletedReceipt Value StableFault RetryableFault → Coefficient)
    (before after : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (index : Nat) (stepped : (step spec before)[index]? = some after) :
    productionLedger spec assignment
        (EventPath.cons (presentation := machinePresentation spec)
          (source := before) (middle := after) (target := after) (site := index)
          (⟨stepped⟩ : OccurrenceEvidence spec index before after)
          (.nil (presentation := machinePresentation spec) after)) =
      (traceProductionFactor? assignment before).toList := by
  unfold productionLedger productionReceipts traceProductionFactor?
  simp only [EventPath.events, List.filterMap_cons, List.filterMap_nil]
  cases productionReceipt? before <;> rfl

/-- Every history, including a proper prefix that has not halted, replays to
the production ledger of that history. -/
theorem trace_replay_of_history
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (assignment : CompletedReceipt Value StableFault RetryableFault → Coefficient)
    (initial : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {source target : RewriteEventHistory.State (system (pathMachine spec initial))}
    (history : Quiver.Path source target) :
    traceReplay spec assignment source.term (indices (pathMachine spec initial) history) =
      some (target.term,
        productionLedger spec assignment
          (historyEventPath spec initial history)) := by
  induction history with
  | nil =>
      simp [traceReplay, indices, historyEventPath_nil, productionLedger,
        productionReceipts, EventPath.events]
  | @cons middle after past event ih =>
      rw [indices, trace_replay_append spec assignment, ih]
      simp only [Option.bind_some]
      have stepped : (step spec middle.term)[event.val]? = some after.term :=
        event.property
      have oneReplay : traceReplay spec assignment middle.term [event.val] =
          some (after.term, (traceProductionFactor? assignment middle.term).toList) := by
        simp [traceReplay, stepped]
      simp only [oneReplay, Option.map_some]
      rw [historyEventPath_cons spec initial past event,
        productionLedger_append spec assignment
          (historyEventPath spec initial past)
          (EventPath.cons (presentation := machinePresentation spec)
            (source := middle.term) (middle := after.term) (target := after.term)
            (site := event.val)
            (⟨event.property⟩ : OccurrenceEvidence spec event.val
              middle.term after.term)
            (.nil (presentation := machinePresentation spec) after.term)),
        one_step_trace_ledger spec assignment middle.term after.term event.val stepped]

/-- A replay that returns a machine and a ledger has returned the history
endpoint. The machine is `target.term`, so its functional heap is that
endpoint's heap. This is the same induction as `trace_replay_of_history`. -/
theorem replayed_endpoint_of_history
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (assignment : CompletedReceipt Value StableFault RetryableFault → Coefficient)
    (initial : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {source target : RewriteEventHistory.State (system (pathMachine spec initial))}
    (history : Quiver.Path source target)
    {machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {ledger : Ledger (CellId × ReceiptId)
      (Produced Value StableFault RetryableFault) Coefficient}
    (walked : traceReplay spec assignment source.term
        (indices (pathMachine spec initial) history) = some (machine, ledger)) :
    machine = target.term ∧
      ledger = productionLedger spec assignment
        (historyEventPath spec initial history) := by
  exact Prod.ext_iff.mp (Option.some.inj
    (walked.symm.trans (trace_replay_of_history spec assignment initial history)))

/-- Successful replay is exactly a source history with the supplied occurrence
indices and the account earned by that history. The construction reuses
`ofTrace`; it neither authenticates a starting state nor grants authority. -/
theorem trace_replay_exact
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (assignment : CompletedReceipt Value StableFault RetryableFault → Coefficient)
    (before after : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (trace : List Nat)
    (ledger : Ledger (CellId × ReceiptId)
      (Produced Value StableFault RetryableFault) Coefficient) :
    traceReplay spec assignment before trace = some (after, ledger) ↔
      ∃ history : History (pathMachine spec before) before after,
        indices (pathMachine spec before) history = trace ∧
          ledger = productionLedger spec assignment
            (historyEventPath spec before history) := by
  constructor
  · intro checked
    have followed : (pathMachine spec before).follow before trace = some after := by
      rw [← trace_replay_follows spec assignment before before trace, checked]
      rfl
    obtain ⟨history, traced⟩ :=
      (follow_iff_history (pathMachine spec before) trace).mp followed
    have accounted := trace_replay_of_history spec assignment before history
    rw [traced] at accounted
    exact ⟨history, traced,
      (Prod.ext_iff.mp (Option.some.inj (checked.symm.trans accounted))).2⟩
  · rintro ⟨history, traced, accounted⟩
    have replayed := trace_replay_of_history spec assignment before history
    simpa only [traced, ← accounted] using replayed

/-- The suffix replay keeps the incoming production ledger in front. Its
denotation is the incoming denotation times the suffix denotation. The two
factors are not commuted, and the histories need not be halted. -/
theorem trace_replay_keeps_the_incoming_ledger [Monoid Coefficient]
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (assignment : CompletedReceipt Value StableFault RetryableFault → Coefficient)
    (initial : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {source middle target : RewriteEventHistory.State (system (pathMachine spec initial))}
    (earlier : Quiver.Path source middle) (later : Quiver.Path middle target) :
    traceReplayFrom spec assignment
        (productionLedger spec assignment (historyEventPath spec initial earlier))
        middle.term (indices (pathMachine spec initial) later) =
      some (target.term,
        productionLedger spec assignment (historyEventPath spec initial earlier) ++
          productionLedger spec assignment (historyEventPath spec initial later)) ∧
      denote (productionLedger spec assignment
          (historyEventPath spec initial (earlier.comp later))) =
        denote (productionLedger spec assignment (historyEventPath spec initial earlier)) *
          denote (productionLedger spec assignment (historyEventPath spec initial later)) := by
  refine ⟨?_, ?_⟩
  · have suffix := trace_replay_of_history spec assignment initial later
    simp [traceReplayFrom, suffix]
  · rw [historyEventPath_comp, productionLedger_denote_append]

/-- Replay of an arbitrary resumed history accounts both model observers.
The suffix clock starts at `source.term.work.transitions`, and the later
clock starts at `middle.term.work.transitions`; both are
`transitions_eq_pathLength`. The event-count conjunct instantiates
`EventPath.eventCountValuation`, and the payment conjunct instantiates
`productionValuation`. `Work.transitions`, `nextEvaluator`, and
`NativeCostLedger` event or work units remain separate accounts. No
native visited-work total is identified with path length. -/
theorem resumed_replay_accounts_the_work_clock [Monoid Coefficient]
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (assignment : CompletedReceipt Value StableFault RetryableFault → Coefficient)
    (initial : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {source middle target : RewriteEventHistory.State (system (pathMachine spec initial))}
    (earlier : Quiver.Path source middle) (later : Quiver.Path middle target) :
    traceReplayFrom spec assignment
        (productionLedger spec assignment (historyEventPath spec initial earlier))
        middle.term (indices (pathMachine spec initial) later) =
      some (target.term,
        productionLedger spec assignment (historyEventPath spec initial earlier) ++
          productionLedger spec assignment (historyEventPath spec initial later)) ∧
      denote (productionLedger spec assignment
          (historyEventPath spec initial (earlier.comp later))) =
        denote (productionLedger spec assignment (historyEventPath spec initial earlier)) *
          denote (productionLedger spec assignment (historyEventPath spec initial later)) ∧
      middle.term.work.transitions =
        source.term.work.transitions +
          EventPath.pathLength (machinePresentation spec)
            (historyEventPath spec initial earlier) ∧
      target.term.work.transitions =
        middle.term.work.transitions +
          EventPath.pathLength (machinePresentation spec)
            (historyEventPath spec initial later) ∧
      EventPath.grade (machinePresentation spec)
          (EventPath.eventCountValuation (machinePresentation spec))
          (historyEventPath spec initial (earlier.comp later)) =
        some (EventPath.pathLength (machinePresentation spec)
          (historyEventPath spec initial (earlier.comp later))) ∧
      EventPath.grade (machinePresentation spec)
          (productionValuation spec assignment)
          (historyEventPath spec initial (earlier.comp later)) =
        some (denote (productionLedger spec assignment
          (historyEventPath spec initial (earlier.comp later)))) := by
  obtain ⟨replayed, denoted⟩ :=
    trace_replay_keeps_the_incoming_ledger spec assignment initial earlier later
  exact ⟨replayed, denoted,
    transitions_eq_pathLength spec (historyEventPath spec initial earlier),
    transitions_eq_pathLength spec (historyEventPath spec initial later),
    EventPath.eventCount_grade (machinePresentation spec)
      (historyEventPath spec initial (earlier.comp later)),
    production_history_grade spec assignment
      (historyEventPath spec initial (earlier.comp later))⟩

/-- A real contribution, returned or still pending, has the production ledger
named by replaying its trace. The payment is that ledger's denotation. -/
theorem trace_account_of_contribution [Monoid Coefficient]
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (assignment : CompletedReceipt Value StableFault RetryableFault → Coefficient)
    (initial : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (fuel : Nat)
    {leaf : (WorkOccurrence
          (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) ⊕
        WorkOccurrence
          (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) × Coefficient}
    (member : leaf ∈ contributions
      (source spec (productionCoefficient assignment)) fuel ⟨initial, []⟩)
    {trace : List Nat}
    {expected : Ledger (CellId × ReceiptId) (Produced Value StableFault RetryableFault) Coefficient}
    (traceEq : (retained leaf.1).trace = trace)
    (replayed : (traceReplay spec assignment initial trace).map Prod.snd = some expected) :
    ∃ history : History (pathMachine spec initial) initial (retained leaf.1).state,
      indices (pathMachine spec initial) history = trace ∧
        productionLedger spec assignment
            (historyEventPath spec initial history) = expected ∧
          Valid expected ∧
          denote expected = leaf.2 := by
  obtain ⟨history, traced, validLedger, denoted⟩ :=
    retained_production_ledger spec assignment initial fuel ⟨initial, []⟩ member
  have indicesEq : indices (pathMachine spec initial) history = trace := by
    simpa [traceEq] using traced
  have agreed := trace_replay_of_history spec assignment initial history
  rw [indicesEq] at agreed
  have productionEq :
      productionLedger spec assignment
          (historyEventPath spec initial history) = expected := by
    cases hreplay : traceReplay spec assignment initial trace with
    | none => simp [hreplay] at replayed
    | some result =>
        cases result with
        | mk _final ledger =>
            have ledgerEq : ledger = expected := by
              simpa [hreplay] using replayed
            have agreedClean :
                traceReplay spec assignment initial trace =
                  some ((retained leaf.1).state,
                    productionLedger spec assignment
                      (historyEventPath spec initial history)) := agreed
            rw [hreplay] at agreedClean
            cases agreedClean
            exact ledgerEq
  refine ⟨history, indicesEq, productionEq, ?_, ?_⟩
  · rw [← productionEq]
    exact validLedger
  · rw [← productionEq]
    exact denoted

end TraceReplay

end Mettapedia.Machines.BranchLocalNeed.NeedQualifiedReplay
