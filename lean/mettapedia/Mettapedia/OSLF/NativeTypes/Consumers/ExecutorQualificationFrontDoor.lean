import Mettapedia.OSLF.NativeTypes.Consumers.ExecutorQualification
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RelationalAnswerFrontDoor

/-!
# Executor qualification through the front door

For a portable question, the executor's evaluation of a grant has exactly one run: the state is unchanged, and the
single answer is the observed packet family of the resumed session (`runsOf`). So the evaluation of a grant unfolds into
a finite system at the front door (`RelationalAnswers`), and checking a packet family produced by an external runtime
is a native type there:

- **the complete-packet check accepts a packet family exactly when the front door's `◇⊤ ∧ □(inRelation "run")` holds**
  at the grant, for the run observation "the answers are that packet family" (`checkPackets_iff_frontDoor`); a changed
  or omitted packet fails it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.ExecutorQualification

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.Framework.RelationalCompletionTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Generation.IndexedModal
open Mettapedia.Languages.MeTTa.PeTTa
open Bridges.NativeTypes
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.RelationalAnswers

variable {installed : Joined.Installed} {ambient : List String} {question : FocusQuery.Question installed ambient}

/-- **The executor's run of a grant, listed exactly**: the state is unchanged, and the answer is the observed packet
family of the resumed session. -/
def runsOf (session : Discovery.Session question) (ready : QueryExecution.portable question = true)
    (before : Effects.State) (grant : Nat) : RunsOf (source session) before grant where
  runs := [(before, [QueryTransport.observeSession (session.resume grant)])]
  exact after answers := by
    constructor
    · rintro ⟨rfl, packets, completed, rfl⟩
      rw [(QueryExecution.completes_iff _ session grant ready packets).mp completed]
      exact List.mem_singleton_self _
    · intro member
      simp only [List.mem_singleton, Prod.mk.injEq] at member
      obtain ⟨rfl, rfl⟩ := member
      exact ⟨rfl, _, (QueryExecution.completes_iff _ session grant ready _).mpr rfl, rfl⟩

/-- An answer is the packet family. -/
def packetIs (packets : QueryTransport.Packets question) (_ : Effects.State) (_ : Nat) (_ : Effects.State)
    (answer : QueryTransport.Packets question) : Prop := answer = packets

/-- A run answers the packet family alone. -/
def packetsAre (packets : QueryTransport.Packets question) (_ : Effects.State) (_ : Nat) (_ : Effects.State)
    (answers : List (QueryTransport.Packets question)) : Prop := answers = [packets]

instance (packets : QueryTransport.Packets question) (before : Effects.State) (grant : Nat) (after : Effects.State)
    (answer : QueryTransport.Packets question) : Decidable (packetIs packets before grant after answer) := by
  unfold packetIs
  infer_instance

instance (packets : QueryTransport.Packets question) (before : Effects.State) (grant : Nat) (after : Effects.State)
    (answers : List (QueryTransport.Packets question)) : Decidable (packetsAre packets before grant after answers) := by
  unfold packetsAre
  infer_instance

/-- The evaluation of a grant, unfolded at the front door, observing a packet family. -/
def system (session : Discovery.Session question) (ready : QueryExecution.portable question = true)
    (before : Effects.State) (grant : Nat) (packets : QueryTransport.Packets question) : EncodedSystem Node :=
  unfolded (runsOf session ready before grant) (packetIs packets) (packetsAre packets)

/-- **The complete-packet check is the front door's completion formula** at the grant. -/
theorem checkPackets_iff_frontDoor (session : Discovery.Session question)
    (ready : QueryExecution.portable question = true) (before : Effects.State) (grant : Nat)
    (packets : QueryTransport.Packets question) :
    checkPackets session grant packets = true ↔
      (system session ready before grant packets).observed.reading.sat Env.closed completesFormula
        (Node.encode .request) := by
  rw [checkPackets_exact]
  refine Iff.trans ?_ (completes_iff (runsOf session ready before grant) (packetIs packets) (packetsAre packets)).symm
  rw [completesOnly_request_iff]
  constructor
  · rintro rfl
    refine ⟨⟨before, _, rfl, _, (QueryExecution.completes_iff _ session grant ready _).mpr rfl, rfl⟩, ?_⟩
    rintro after answers ⟨rfl, observed, completed, rfl⟩
    rw [(QueryExecution.completes_iff _ session grant ready observed).mp completed]
    rfl
  · rintro ⟨-, every⟩
    exact (List.singleton_inj.mp
      (every before _ ⟨rfl, _, (QueryExecution.completes_iff _ session grant ready _).mpr rfl, rfl⟩)).symm

end Mettapedia.OSLF.NativeTypes.Consumers.ExecutorQualification
