import Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.QueryExecution

/-!
# Complete-packet native contracts for executor qualification

The operational relation is the existing evaluation of the actual descent
program, collected once for every candidate source of a native question. The
derived completion type observes the whole returned packet family, including
origins and pending state, rather than just its final membership verdict.

This is a regression oracle for a fixed logical grant. It computes the Lean
reference result; it is not a replacement for inexpensive receipt rechecking
or a proof of a C backend. A canonicalizing compiler needs its own observation
transport if it intentionally changes these physical packets.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.ExecutorQualification

open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis
open Mettapedia.GSLT.Dynamics.RelationalAnswerEvaluation
open Mettapedia.OSLF.NativeTypes.Generation.IndexedModal
open Mettapedia.Languages.MeTTa.PeTTa
open Bridges.NativeTypes

variable {installed : Joined.Installed} {ambient : List String}
  {question : FocusQuery.Question installed ambient}

/-- Each evaluation is the existing actual-target evaluation relation. -/
def source (session : Discovery.Session question) :
    RelationalAnswerSource Effects.State Nat (QueryTransport.Packets question) where
  Evaluates before grant after answers := after = before ∧
    ∃ packets, QueryExecution.Completes before session grant packets ∧ answers = [packets]

def exactObservation (session : Discovery.Session question)
    (before : Effects.State) (grant : Nat) (after : Effects.State)
    (answers : List (QueryTransport.Packets question)) : Prop :=
  after = before ∧ answers = [QueryTransport.observeSession (session.resume grant)]

def nativeType (session : Discovery.Session question) :
    GSLTNativeType (evaluationGSLT (source session)) :=
  completionNativeType (source session) (exactObservation session)

/-- The actual executor earns a non-vacuous universal completion contract. -/
theorem actual_executor_native (session : Discovery.Session question)
    (ready : QueryExecution.portable question = true) (before : Effects.State) (grant : Nat) :
    (gsltOSLF (evaluationGSLT (source session))).satisfies (S := ())
      (.request before grant) (nativeType session).pred := by
  apply (completesOnly_request_iff (source session) (exactObservation session) before grant).mpr
  constructor
  · obtain ⟨packets, completed⟩ := QueryExecution.target_exists before session grant ready
    exact ⟨before, [packets], rfl, packets, completed, rfl⟩
  · rintro after answers ⟨rfl, packets, completed, rfl⟩
    exact ⟨rfl, congrArg (fun value => [value])
      ((QueryExecution.completes_iff _ session grant ready packets).mp completed)⟩

/-- Finite, executable equality with the complete regression oracle. -/
def checkPackets (session : Discovery.Session question) (grant : Nat)
    (packets : QueryTransport.Packets question) : Bool :=
  (List.finRange (Discovery.sources question).length).all fun position =>
    decide (packets position = QueryTransport.observeSession (session.resume grant) position)

theorem checkPackets_exact (session : Discovery.Session question) (grant : Nat)
    (packets : QueryTransport.Packets question) :
    checkPackets session grant packets = true ↔
      packets = QueryTransport.observeSession (session.resume grant) := by
  constructor
  · intro accepted
    exact funext fun position => of_decide_eq_true
      (List.all_eq_true.mp accepted position (List.mem_finRange position))
  · intro same
    simp [checkPackets, same]

theorem checkPackets_iff_target (session : Discovery.Session question) (grant : Nat)
    (ready : QueryExecution.portable question = true) (before : Effects.State)
    (packets : QueryTransport.Packets question) :
    checkPackets session grant packets = true ↔
      QueryExecution.Completes before session grant packets :=
  (checkPackets_exact session grant packets).trans
    (QueryExecution.completes_iff before session grant ready packets).symm

/-- A changed or omitted packet fails even when a coarser verdict agrees. -/
theorem changed_packet_rejected (session : Discovery.Session question) (grant : Nat)
    (packets : QueryTransport.Packets question)
    (position : Fin (Discovery.sources question).length)
    (changed : packets position ≠
      QueryTransport.observeSession (session.resume grant) position) :
    checkPackets session grant packets = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact changed (congrFun ((checkPackets_exact session grant packets).mp accepted) position)

/-- For a fixed-grant executor specialization, coverage and preservation are
both required; the complete contract then transports without redoing logic. -/
theorem specialization_native
    (session : Discovery.Session question)
    (ready : QueryExecution.portable question = true)
    (specialized : RelationalAnswerSource Effects.State Nat (QueryTransport.Packets question))
    (same : ∀ before grant after answers,
      specialized.Evaluates before grant after answers ↔
        (source session).Evaluates before grant after answers)
    (before : Effects.State) (grant : Nat) :
    (gsltOSLF (evaluationGSLT specialized)).satisfies (S := ())
      (.request before grant) (completionNativeType specialized (exactObservation session)).pred := by
  exact (completesOnly_transport (source session) specialized (exactObservation session)
    before grant (fun after answers => (same before grant after answers).symm)).mp
    (actual_executor_native session ready before grant)

end Mettapedia.OSLF.NativeTypes.Consumers.ExecutorQualification
