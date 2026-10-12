import Mettapedia.OSLF.NativeTypes.Instances.Rho.Scheduled
import Mettapedia.OSLF.NativeTypes.Instances.Rho.CanonicalControls

open Mettapedia.OSLF.Framework

/-!
# Original rho work and native decision controls

Root and parallel COMM retain the authored reflective matcher. Payload,
guard and quote contexts have complete negative coverage. First-conclusive
decisions can stop at the first receipt before all matching work drains;
universal truth and existential absence require actual cursor closure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.Scheduled.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Decision.Scheduling
open Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls

def originalSource (raw : Pattern) (accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit raw = true) :
    rhoReflectiveGSLT.Term :=
  presentedRhoProcessEquiv.symm (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admittedProcess raw accepted)

def tests : Empty → Test rhoReflectiveGSLT Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.admitted := Empty.elim

def run (raw : Pattern) (accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit raw = true)
    (formula : Formula Empty) (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.check backend tests formula (originalSource raw accepted) budget

def runRaw (formula : Formula Empty) (budget : Nat) (raw : Pattern) : Option (Option Bool) :=
  if accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit raw = true then
    some (run raw accepted formula budget).answer
  else none

#guard targets 0 redex == []
#guard !closed 0 redex
#guard targets 2 redex == []
#guard !closed 2 redex
#guard targets 35 redex == []
#guard targets 36 redex == [zero]
#guard !closed 36 redex
#guard closed 50 redex
#guard runRaw (.possibility .top) 35 redex == some none
#guard runRaw (.possibility .top) 36 redex == some (some true)
#guard runRaw (.outgoingUniversal .bottom) 36 redex == some (some false)
#guard runRaw (.possibility .bottom) 36 redex == some none
#guard runRaw (.possibility .bottom) 50 redex == some (some false)
#guard runRaw (.outgoingUniversal .top) 36 redex == some none
#guard runRaw (.outgoingUniversal .top) 50 redex == some (some true)
#guard ((List.range 51).find? fun budget =>
    (runRaw (.possibility .top) budget redex).join.isSome) == some 36
#guard runRaw (.possibility .top) 100 parallelRedex == some (some true)
#guard runRaw (.possibility .top) 100 equivalentChannelRedex == some (some true)
#guard runRaw (.possibility .top) 100 reflectiveRedex == some (some true)
#guard targets 100 reflectiveRedex == [zero]
#guard runRaw (.possibility (.possibility .top)) 100 redex == some (some false)
#guard runRaw (.possibility .top) 0 payloadRedex == some none
#guard runRaw (.possibility .top) 2 payloadRedex == some (some false)
#guard runRaw (.possibility .top) 2 guardedRedex == some (some false)
#guard runRaw (.possibility .top) 2 quotedRedex == some (some false)
#guard runRaw (.outgoingUniversal .bottom) 2 payloadRedex == some (some true)
#guard targets 36 duplicateRedex == [input]
#guard !closed 36 duplicateRedex
#guard targets 100 duplicateRedex == [input, input]
#guard closed 100 duplicateRedex
#guard (frontier 100 duplicateRedex).map (·.alternativeIndex) == [0, 1]
#guard (frontier 100 duplicateRedex).map (·.declarationIndex) == [0, 0]
#guard (frontier 100 duplicateRedex).map (·.rawTarget) ==
  (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.receipts duplicateRedex).map (·.rawTarget)
#guard runRaw (.possibility .top) 100 (.apply "POutput" [zero, zero]) == none

theorem root_native_positive (accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit redex = true) :
    denotation tests (.possibility .top) (originalSource redex accepted) := by
  obtain ⟨item, listed, _target⟩ := root_communication
  let owned : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.OriginalReceipt (originalSource redex accepted) :=
    ⟨item, listed⟩
  exact (GSLTTypeSynthesis.gsltDiamond_spec _ _ _).mpr
    ⟨Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.originalTarget _ owned,
      Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.originalTarget_sound _ owned, True.intro⟩

theorem payload_native_negative (accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit payloadRedex = true) :
    ¬ denotation tests (.possibility .top) (originalSource payloadRedex accepted) := by
  intro holds
  obtain ⟨target, step, _⟩ := (GSLTTypeSynthesis.gsltDiamond_spec _ _ _).mp holds
  obtain ⟨item, listed, _⟩ :=
    (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.original_successors_exact _ target).mp step
  change item ∈ Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.receipts payloadRedex at listed
  rw [payloadRedex, output_payload_blocked] at listed
  exact List.not_mem_nil listed

theorem root_outgoing_universal_negative
    (accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit redex = true) :
    ¬ denotation tests (.outgoingUniversal .bottom) (originalSource redex accepted) := by
  obtain ⟨target, step, _⟩ :=
    (GSLTTypeSynthesis.gsltDiamond_spec _ _ _).mp (root_native_positive accepted)
  intro universal
  exact universal target step

theorem payload_outgoing_universal_positive
    (accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit payloadRedex = true) :
    denotation tests (.outgoingUniversal .bottom) (originalSource payloadRedex accepted) := by
  intro target step
  exact payload_native_negative accepted
    ((GSLTTypeSynthesis.gsltDiamond_spec _ _ _).mpr ⟨target, step, True.intro⟩)

theorem exact_pause_resume (first more : Nat) :
    state (first + more) duplicateRedex = resume more (state first duplicateRedex) :=
  exact_resume first more duplicateRedex

theorem duplicate_origins_at_completion :
    (frontier (completionBudget duplicateRedex) duplicateRedex).map (·.alternativeIndex) =
      (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.receipts duplicateRedex).map (·.alternativeIndex) :=
  congrArg (fun receipts => receipts.map (·.alternativeIndex))
    (closed_frontier_exact _ _ (complete_at duplicateRedex))

theorem completed_original_receipts (raw : Pattern) :
    frontier (completionBudget raw) raw = Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.receipts raw :=
  closed_frontier_exact _ _ (complete_at raw)

theorem both_native_polarities_complete (raw : Pattern)
    (accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit raw = true) (formula : Formula Empty) :
    (run raw accepted formula
      (workBound backend tests formula (originalSource raw accepted))).Decided :=
  whole_formula_complete tests formula (originalSource raw accepted)

end Mettapedia.OSLF.NativeTypes.Instances.Rho.Scheduled.Controls
