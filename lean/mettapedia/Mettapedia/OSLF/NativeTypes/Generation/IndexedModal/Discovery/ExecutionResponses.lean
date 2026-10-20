import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Execution

/-!
# Exact contextual-response filtering of produced source certificates

All candidates are genuine scheduled source receipts. Filtering uses the
existing source-response checker, including selected origin, focus, fixed
indices, rely assignments and the dependent target. A negative result earns
semantic force only after every supplied source session has drained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Execution

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.Modal NativeReceiptRechecking
open FiniteFocusChecking FocusMeaning

variable {installed : Joined.Installed} {index : installed.Index}
  {ambient : List String} {sources : List Pattern}

namespace Batch

def responses (batch : Batch installed index ambient sources)
    (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) : List Witness :=
  batch.certificate.filter (accepts parameters focus values)

theorem response_sound (batch : Batch installed index ambient sources)
    (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) (witness : Witness)
    (member : witness ∈ batch.responses parameters focus values) :
    witness.source ∈ sources ∧
      SourceResponse parameters.meaning focus values witness.source witness.payload := by
  obtain ⟨present, accepted⟩ := List.mem_filter.mp member
  exact ⟨(batch.witness_sound witness present).1,
    (accepts_exact parameters focus values witness).mp accepted⟩

/-- The independent source specification is exactly the filter of actual
produced receipts, once all provided source sessions have drained. -/
theorem responses_exact (batch : Batch installed index ambient sources)
    (complete : batch.settled = true) (parameters : Parameters installed index ambient)
    (focus : Pattern) (values : RelyValues installed index ambient) (witness : Witness) :
    witness ∈ batch.responses parameters focus values ↔ witness.source ∈ sources ∧
      SourceResponse parameters.meaning focus values witness.source witness.payload := by
  constructor
  · exact batch.response_sound parameters focus values witness
  · rintro ⟨present, valid⟩
    exact List.mem_filter.mpr ⟨batch.payload_covered complete witness.source present witness.payload valid.1,
      (accepts_exact parameters focus values witness).mpr valid⟩

def hasResponse (batch : Batch installed index ambient sources)
    (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient) : Bool :=
  batch.certificate.any (accepts parameters focus values)

theorem hasResponse_sound (batch : Batch installed index ambient sources)
    (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient)
    (found : batch.hasResponse parameters focus values = true) :
    ∃ pattern ∈ sources, ∃ payload, SourceResponse parameters.meaning focus values pattern payload := by
  obtain ⟨witness, present, accepted⟩ := List.any_eq_true.mp found
  exact ⟨witness.source, (batch.witness_sound witness present).1, witness.payload,
    (accepts_exact parameters focus values witness).mp accepted⟩

theorem hasResponse_exact (batch : Batch installed index ambient sources)
    (complete : batch.settled = true) (parameters : Parameters installed index ambient)
    (focus : Pattern) (values : RelyValues installed index ambient) :
    batch.hasResponse parameters focus values = true ↔
      ∃ pattern ∈ sources, ∃ payload, SourceResponse parameters.meaning focus values pattern payload := by
  constructor
  · exact batch.hasResponse_sound parameters focus values
  · rintro ⟨pattern, present, payload, valid⟩
    exact List.any_eq_true.mpr ⟨⟨pattern, payload⟩,
      batch.payload_covered complete pattern present payload valid.1,
      (accepts_exact parameters focus values ⟨pattern, payload⟩).mpr valid⟩

theorem no_response (batch : Batch installed index ambient sources)
    (complete : batch.settled = true) (parameters : Parameters installed index ambient)
    (focus : Pattern) (values : RelyValues installed index ambient)
    (missing : batch.hasResponse parameters focus values = false)
    (pattern : Pattern) (present : pattern ∈ sources) (payload : Payload) :
    ¬ SourceResponse parameters.meaning focus values pattern payload := by
  intro valid
  have found := (batch.hasResponse_exact complete parameters focus values).mpr
    ⟨pattern, present, payload, valid⟩
  rw [missing] at found
  cases found

theorem hasResponse_preserved (batch : Batch installed index ambient sources)
    (parameters : Parameters installed index ambient) (focus : Pattern)
    (values : RelyValues installed index ambient)
    (found : batch.hasResponse parameters focus values = true) (fuel : Nat) :
    (batch.resume fuel).hasResponse parameters focus values = true := by
  obtain ⟨witness, present, accepted⟩ := List.any_eq_true.mp found
  exact List.any_eq_true.mpr ⟨witness, batch.certificate_preserved fuel witness present, accepted⟩

theorem responses_stable (batch : Batch installed index ambient sources)
    (complete : batch.settled = true) (parameters : Parameters installed index ambient)
    (focus : Pattern) (values : RelyValues installed index ambient) (fuel : Nat) :
    (batch.resume fuel).responses parameters focus values = batch.responses parameters focus values := by
  unfold responses
  rw [batch.certificate_stable complete fuel]

theorem check_exact (batch : Batch installed index ambient sources)
    (complete : batch.settled = true) (parameters : Parameters installed index ambient) (focus : Pattern) :
    FiniteFocusChecking.check parameters focus batch.certificate = true ↔
      FocusAdmitted installed index ambient focus ∧
        ∀ values, Requested parameters.meaning values →
          ∃ pattern ∈ sources, ∃ payload, SourceResponse parameters.meaning focus values pattern payload := by
  rw [FiniteFocusChecking.check_exact]
  constructor
  · rintro ⟨admitted, covered⟩
    refine ⟨admitted, fun values requested => ?_⟩
    obtain ⟨witness, present, valid⟩ := covered values requested
    exact ⟨witness.source, (batch.witness_sound witness present).1, witness.payload, valid⟩
  · rintro ⟨admitted, covered⟩
    refine ⟨admitted, fun values requested => ?_⟩
    obtain ⟨pattern, present, payload, valid⟩ := covered values requested
    exact ⟨⟨pattern, payload⟩, batch.payload_covered complete pattern present payload valid.1, valid⟩

/-- The supplied list may be incomplete; the theorem exposes that boundary
instead of silently treating an arbitrary finite search space as exhaustive. -/
theorem discovery (batch : Batch installed index ambient sources)
    (parameters : Parameters installed index ambient) (focus : Pattern)
    (admitted : FocusAdmitted installed index ambient focus)
    (covered : ∀ values, Requested parameters.meaning values →
      ∃ pattern ∈ sources, ∃ payload, SourceResponse parameters.meaning focus values pattern payload)
    (fuel : Nat) (enough : completionBudget installed index ambient sources ≤ fuel) :
    FiniteFocusChecking.check parameters focus (batch.resume fuel).certificate = true :=
  ((batch.resume fuel).check_exact (batch.resume_settled fuel enough) parameters focus).mpr ⟨admitted, covered⟩

end Batch

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Execution
