import Mettapedia.OSLF.NativeTypes.Consumers.PLNEvidence

/-!
# Identified-evidence native revision controls

The stores mirror the distinction made by PeTTaChainer between `proof-ref`
origins and `fact-ev` observation tokens. They test the exact additive branch;
the runtime's higher-confidence overlap fallback is outside this consumer.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.PLNEvidence.Controls

open Mettapedia.GSLT.Dynamics.RelationalAnswerEvaluation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- Observations 0, 2 and 3 support the same query; observation 1 opposes it. -/
def truth : Fin 4 → Bool := fun i => i.val != 1

def first : Proof 4 := ⟨10, {0, 1}, (1, 1), []⟩
def disjoint : Proof 4 := ⟨20, {2}, (1, 0), []⟩
/-- Same count summary as `disjoint`, but shared evidence. -/
def shared : Proof 4 := ⟨21, {0}, (1, 0), []⟩
def malformed : Proof 4 := ⟨22, {3}, (2, 0), []⟩

def store : State 4 := ⟨truth, [first, disjoint, shared, malformed]⟩
def disjointRequest : Request := ⟨10, 20, 30⟩
def sharedRequest : Request := ⟨10, 21, 30⟩
def repeatedRequest : Request := ⟨10, 10, 30⟩
def malformedRequest : Request := ⟨10, 22, 30⟩
def reusedOriginRequest : Request := ⟨10, 20, 10⟩
def absentRequest : Request := ⟨10, 99, 30⟩
def reverseRequest : Request := ⟨20, 10, 31⟩

#guard check store disjointRequest
#guard !check store sharedRequest
#guard !check store repeatedRequest
#guard !check store malformedRequest
#guard !check store reusedOriginRequest
#guard !check store absentRequest
#guard check store reverseRequest

theorem same_summary_different_admission :
    disjoint.counts = shared.counts ∧ disjoint.origin ≠ shared.origin ∧
      check store disjointRequest = true ∧ check store sharedRequest = false := by
  decide

theorem disjoint_native_member :
    (gsltOSLF (evaluationGSLT (source (observations := 4)))).satisfies
      (.request store disjointRequest) (nativeType 4).pred :=
  (check_native_exact store disjointRequest).mp (by decide)

theorem shared_not_native_member :
    ¬ (gsltOSLF (evaluationGSLT (source (observations := 4)))).satisfies
      (.request store sharedRequest) (nativeType 4).pred := by
  intro member
  have := (check_native_exact store sharedRequest).mpr member
  contradiction

theorem repeated_not_native_member :
    ¬ (gsltOSLF (evaluationGSLT (source (observations := 4)))).satisfies
      (.request store repeatedRequest) (nativeType 4).pred := by
  intro member
  have := (check_native_exact store repeatedRequest).mpr member
  contradiction

theorem disjoint_publication :
    (revise? store disjointRequest).map (fun result =>
      (result.2.origin, result.2.parents, result.2.counts, result.2.support)) =
        some (30, [10, 20], (2, 1), ({0, 1, 2} : Finset (Fin 4))) := by
  decide

theorem reverse_preserves_parent_order :
    (revise? store reverseRequest).map (fun result => (result.2.parents, result.2.counts)) =
      some ([20, 10], (2, 1)) := by
  decide

theorem observed_publication :
    observation store disjointRequest (publish store (merge disjointRequest first disjoint))
      (merge disjointRequest first disjoint) := by
  exact ⟨rfl, rfl, by decide, by simp [publish]⟩

/-- The same accepted inputs satisfy the actual rule's independent semantics. -/
theorem declared_revision_sound :
    Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusSemantics.Ledger.Model.holds
      (ledgerModel store first disjoint)
      (Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusModule.evidenceRules[0]).conclusion :=
  ready_module_revision (request := disjointRequest) (by decide)

end Mettapedia.OSLF.NativeTypes.Consumers.PLNEvidence.Controls
