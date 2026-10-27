import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Source scheduling boundary controls

The maintained closed evaluator completes a producer frontier before invoking
its caller. Concrete reductions distinguish that discipline from an effect
trace independently exercised by native PeTTa callers. The pure example
retains the same answers. Their inequality under an exact trace observer does
not select a language-wide scheduling policy.

The causal controls express one smaller commitment: each consumed occurrence
has an earlier production. Both interleaving and batching satisfy it. These
controls leave multiplicity, explicit sequencing, mutable dependencies and
stopping behavior to their separate laws.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Mettapedia.Machines.SourceSchedulingBoundary
open Mettapedia.Languages.MeTTa.PeTTa
abbrev Atom := Mettapedia.Languages.MeTTa.OSLFCore.Atom

def producerBody (name : String) (number : Int) : Atom :=
  .expression [.symbol "let", .var "ignored",
    .expression [.symbol "println!", .symbol name], .grounded (.int number)]

def program : SpaceSemantics.Program := {
  equations := [⟨"producer", [], producerBody "P1" 1⟩,
    ⟨"producer", [], producerBody "P2" 2⟩]
  declarations := [] }

def query : Atom := .expression [.symbol "collapse",
  .expression [.symbol "let", .var "x", .expression [.symbol "producer"],
    .expression [.symbol "let", .var "ignored",
      .expression [.symbol "println!", .expression [.symbol "B", .var "x"]], .var "x"]]]

def observe (owner : SpaceSemantics.Program) (expression : Atom) :
    Option (List Atom × List Atom) :=
  match Eval.evaluate owner 128 (Effects.loaded owner) expression with
  | .complete _ answers _ printed => some (printed, answers)
  | _ => none

def answers : List Atom := [.expression [.grounded (.int 1), .grounded (.int 2)]]
def firstBody : Atom := .expression [.symbol "B", .grounded (.int 1)]
def secondBody : Atom := .expression [.symbol "B", .grounded (.int 2)]

theorem closed_model_batch_order :
    observe program query = some
      ([.symbol "P1", .symbol "P2", firstBody, secondBody], answers) := by
  decide +kernel

/-- The native trace is independently checked against CeTTa and SWI. -/
theorem differs_from_interleaved_trace :
    observe program query ≠ some
      ([.symbol "P1", firstBody, .symbol "P2", secondBody], answers) := by
  rw [closed_model_batch_order]
  decide

def pureProgram : SpaceSemantics.Program := {
  equations := [⟨"producer", [], .grounded (.int 1)⟩,
    ⟨"producer", [], .grounded (.int 2)⟩]
  declarations := [] }

theorem pure_positive_control :
    observe pureProgram (.expression [.symbol "collapse",
      .expression [.symbol "let", .var "x", .expression [.symbol "producer"], .var "x"]]) =
      some ([], answers) := by
  decide +kernel

inductive OccurrenceEvent where
  | produced (occurrence : Nat)
  | consumed (occurrence : Nat)
  deriving DecidableEq

/-- A missing production has index `length`, after every present consumption.
Occurrence identities distinguish equal answers; this property alone imposes
no multiplicity or global scheduling law. -/
def productionBeforeConsumption (trace : List OccurrenceEvent) : Prop :=
  ∀ event ∈ trace, match event with
    | .produced _ => True
    | .consumed occurrence =>
        trace.idxOf (.produced occurrence) < trace.idxOf (.consumed occurrence)

theorem interleaving_respects_causality :
    productionBeforeConsumption [.produced 1, .consumed 1, .produced 2, .consumed 2] := by
  simp [productionBeforeConsumption, List.idxOf_cons]
  decide +kernel

theorem batching_respects_causality :
    productionBeforeConsumption [.produced 1, .produced 2, .consumed 1, .consumed 2] := by
  simp [productionBeforeConsumption, List.idxOf_cons]
  decide +kernel

theorem early_consumption_rejected :
    ¬ productionBeforeConsumption [.consumed 1, .produced 1] := by
  simp [productionBeforeConsumption, List.idxOf_cons]

theorem missing_production_rejected :
    ¬ productionBeforeConsumption [.consumed 1] := by
  simp [productionBeforeConsumption, List.idxOf_cons]

theorem consumed_has_prior_production (trace : List OccurrenceEvent)
    (causal : productionBeforeConsumption trace) (occurrence : Nat)
    (consumed : .consumed occurrence ∈ trace) :
    .produced occurrence ∈ trace.take (trace.idxOf (.consumed occurrence)) := by
  have order := causal (.consumed occurrence) consumed
  have produced : .produced occurrence ∈ trace :=
    List.idxOf_lt_length_iff.mp (lt_trans order (List.idxOf_lt_length_of_mem consumed))
  exact (List.mem_take_iff_idxOf_lt produced).mpr order

/-- Stopping at any prefix retains the same causal guarantee, without
choosing a complete schedule or requiring the producer to finish. -/
theorem causality_survives_prefix (earlier later : List OccurrenceEvent)
    (causal : productionBeforeConsumption (earlier ++ later)) :
    productionBeforeConsumption earlier := by
  intro event member
  cases event with
  | produced => trivial
  | consumed occurrence =>
    have order := causal (.consumed occurrence) (List.mem_append_left later member)
    change (earlier ++ later).idxOf (.produced occurrence) <
      (earlier ++ later).idxOf (.consumed occurrence) at order
    by_cases produced : OccurrenceEvent.produced occurrence ∈ earlier
    · simpa only [List.idxOf_append_of_mem produced,
        List.idxOf_append_of_mem member] using order
    · rw [List.idxOf_append_of_notMem produced, List.idxOf_append_of_mem member] at order
      have inRange := List.idxOf_lt_length_of_mem member
      omega
end Mettapedia.Machines.SourceSchedulingBoundary
#print axioms Mettapedia.Machines.SourceSchedulingBoundary.closed_model_batch_order
#print axioms Mettapedia.Machines.SourceSchedulingBoundary.differs_from_interleaved_trace
#print axioms Mettapedia.Machines.SourceSchedulingBoundary.pure_positive_control
#print axioms Mettapedia.Machines.SourceSchedulingBoundary.interleaving_respects_causality
#print axioms Mettapedia.Machines.SourceSchedulingBoundary.batching_respects_causality
#print axioms Mettapedia.Machines.SourceSchedulingBoundary.early_consumption_rejected
#print axioms Mettapedia.Machines.SourceSchedulingBoundary.missing_production_rejected
#print axioms Mettapedia.Machines.SourceSchedulingBoundary.consumed_has_prior_production
#print axioms Mettapedia.Machines.SourceSchedulingBoundary.causality_survives_prefix
