import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.Frontier

/-!
# Receipt-sensitive native checking modulo declared laws

A native continuation can inspect the declaration, captured and completed
assignments, and ordered premise history, not only the result pattern. Such
an observation needs its own local transport law. Target equality alone
cannot establish it. The existing equation/law tiling, followed by complete
physical occurrence coverage, derives the full source specification below
from those local obligations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles

open Mettapedia.OSLF.MeTTaIL Syntax GeneralOccurrenceFrontier Complete

/-- A computable observation of the complete rule receipt. `transport`
concerns one declared law move, not the desired global checking theorem. -/
structure ReceiptTest (request : Request) where
  accepts : GeneralRuleJobs.Receipt → Bool
  transport : ∀ first second,
    Relation.SymmGen (CanonicalBags.StandardStep
      (Normalized.laws request.plan) (Normalized.extrusions request.plan)) first second →
    ∀ receipt, GeneralOccurrenceSemantics.Primitive request.plan request.bound request.expected first receipt →
      ∃ transported, GeneralOccurrenceSemantics.Primitive
        request.plan request.bound request.expected second transported ∧ accepts receipt = accepts transported

namespace ReceiptTest

variable {request : Request} (test : ReceiptTest request)

/-- Independent source response semantics, retaining a complete firing and
the conversion from the requested source's model class. -/
def Holds (source : Pattern) : Prop :=
  ∃ representative receipt,
    Presented.ModelEquiv request.plan request.bound request.expected source representative ∧
    GeneralOccurrenceSemantics.Primitive request.plan request.bound request.expected representative receipt ∧
    test.accepts receipt = true

def Meaning : Prop := test.Holds request.root

/-- A receipt-sensitive may classifier is a predicate of the sole generated
OSLF. Equation saturation is explicit in its independent source meaning. -/
def predicate : Mettapedia.OSLF.Framework.GSLTTypeSynthesis.EquationPredicate
    (Presented.gslt request.plan request.bound request.expected) :=
  ⟨test.Holds, by
    intro first second equivalent
    constructor
    · rintro ⟨representative, receipt, before, fired, accepts⟩
      exact ⟨representative, receipt, .trans _ _ _ (.symm _ _ equivalent) before, fired, accepts⟩
    · rintro ⟨representative, receipt, before, fired, accepts⟩
      exact ⟨representative, receipt, .trans _ _ _ equivalent before, fired, accepts⟩⟩

private theorem transport_chain {first second : Pattern}
    (moves : Relation.ReflTransGen (Relation.SymmGen (CanonicalBags.StandardStep
      (Normalized.laws request.plan) (Normalized.extrusions request.plan))) first second)
    {receipt : GeneralRuleJobs.Receipt}
    (fired : GeneralOccurrenceSemantics.Primitive request.plan request.bound request.expected first receipt) :
    ∃ transported, GeneralOccurrenceSemantics.Primitive
      request.plan request.bound request.expected second transported ∧ test.accepts receipt = test.accepts transported := by
  induction moves with
  | refl => exact ⟨receipt, fired, rfl⟩
  | @tail middle last _ move ih =>
    obtain ⟨intermediate, fires, same⟩ := ih
    obtain ⟨transported, fires', same'⟩ := test.transport middle last move intermediate fires
    exact ⟨transported, fires', same.trans same'⟩

/-- Receipt-sensitive coherence follows from the existing local tiling and
the observation's local transport. No global source coverage is assumed. -/
theorem coherent (commute : Coherence.LocalCommute
      (GeneralOccurrenceSemantics.Equation request.plan request.bound request.expected)
      (CanonicalBags.StandardStep (Normalized.laws request.plan) (Normalized.extrusions request.plan)))
    {representative : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (converted : Presented.ModelEquiv request.plan request.bound request.expected request.root representative)
    (fired : GeneralOccurrenceSemantics.Primitive request.plan request.bound request.expected representative receipt) :
    ∃ reached transported,
      Relation.EqvGen (GeneralOccurrenceSemantics.Equation request.plan request.bound request.expected) request.root reached ∧
      GeneralOccurrenceSemantics.Primitive request.plan request.bound request.expected reached transported ∧
      test.accepts receipt = test.accepts transported := by
  obtain ⟨reached, equations, laws⟩ := Coherence.split_equivalence commute converted
  have reverse : Relation.ReflTransGen (Relation.SymmGen (CanonicalBags.StandardStep
      (Normalized.laws request.plan) (Normalized.extrusions request.plan))) representative reached := by
    rw [Relation.EqvGen.reflTransGen_symmGen]
    exact .symm _ _ laws
  obtain ⟨transported, fires, same⟩ := test.transport_chain reverse fired
  exact ⟨reached, transported, equations, fires, same⟩

def check (state : State request) : Bool :=
  state.answers.any fun answer => test.accepts answer.val.firing

theorem check_sound {state : State request} (checked : test.check state = true) : test.Meaning := by
  obtain ⟨answer, _, accepts⟩ := List.any_eq_true.mp checked
  exact ⟨answer.val.representative, answer.val.firing,
    equations_model answer.property.1.equivalent, answer.property.2, accepts⟩

/-- The received certificate is checked against actual archived occurrences,
so every accepted answer contains a real source receipt, not an endpoint-only
witness. Completeness transports the observation through declared laws. -/
theorem check_exact {state : State request}
    (commute : Coherence.LocalCommute
      (GeneralOccurrenceSemantics.Equation request.plan request.bound request.expected)
      (CanonicalBags.StandardStep (Normalized.laws request.plan) (Normalized.extrusions request.plan)))
    (admitted : Admitted request) (covered : checkCertificate request state = true) :
    test.check state = true ↔ test.Meaning := by
  constructor
  · exact test.check_sound
  · rintro ⟨representative, receipt, converted, fires, accepts⟩
    obtain ⟨reached, transported, equations, fires', same⟩ := test.coherent commute converted fires
    obtain ⟨answer, retained, _, payload⟩ :=
      certified_physical_occurrence admitted covered reached equations transported fires'
    apply List.any_eq_true.mpr
    refine ⟨answer, retained, ?_⟩
    rw [payload, ← same]
    exact accepts

/-- Exact checking of a generated native predicate, including complete
assignment and premise-history observations, under the local profile laws. -/
theorem check_native_exact {state : State request}
    (commute : Coherence.LocalCommute
      (GeneralOccurrenceSemantics.Equation request.plan request.bound request.expected)
      (CanonicalBags.StandardStep (Normalized.laws request.plan) (Normalized.extrusions request.plan)))
    (admitted : Admitted request) (covered : checkCertificate request state = true) :
    test.check state = true ↔
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (Presented.gslt request.plan request.bound request.expected)).satisfies (S := ()) request.root test.predicate :=
  test.check_exact commute admitted covered

structure Response (state : State request) where
  answer : Answer request
  retained : answer ∈ state.answers
  accepts : test.accepts answer.val.firing = true

def response? (state : State request) : Option (test.Response state) :=
  match found : state.answers.find? (fun answer : Answer request => test.accepts answer.val.firing) with
  | none => none
  | some answer => some ⟨answer, List.mem_of_find?_eq_some found,
    List.find?_some (p := fun answer : Answer request => test.accepts answer.val.firing) found⟩

theorem response?_exact (state : State request) :
    (test.response? state).isSome = true ↔ test.check state = true := by
  unfold response?
  split
  · rename_i absent
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    intro positive
    obtain ⟨answer, retained, accepts⟩ := List.any_eq_true.mp positive
    exact (List.find?_eq_none.mp absent answer retained) accepts
  · rename_i answer found
    simp only [Option.isSome_some, true_iff]
    exact List.any_eq_true.mpr ⟨answer, List.mem_of_find?_eq_some found,
      List.find?_some (p := fun answer : Answer request => test.accepts answer.val.firing) found⟩

def readout (state : State request) : CheckResult :=
  if test.check state then .decided true
  else if sourceAdmission request && checkCertificate request state then .decided false else .unknown

theorem readout_refuted {state : State request}
    (commute : Coherence.LocalCommute
      (GeneralOccurrenceSemantics.Equation request.plan request.bound request.expected)
      (CanonicalBags.StandardStep (Normalized.laws request.plan) (Normalized.extrusions request.plan)))
    (compiled : request.plan = GeneralExecutionAdmission.compile request.plan.snapshot request.plan.permissions)
    (negative : test.readout state = .decided false) : ¬ test.Meaning := by
  unfold readout at negative
  split at negative
  · cases negative
  · rename_i missing
    split at negative
    · rename_i covered
      simp only [Bool.and_eq_true] at covered
      intro meaning
      exact missing ((test.check_exact commute (sourceAdmission_sound covered.1 compiled) covered.2).mpr meaning)
    · cases negative

theorem unfinished_unknown {state : State request}
    (missing : test.check state = false) (unfinished : complete request state = false) :
    test.readout state = .unknown := by
  simp [readout, missing, unfinished_certificate_rejected request state unfinished]

/-- A result-pattern classifier is a special case; full native continuations
may instead inspect any receipt field and prove its own transport law. -/
def ofTarget (certificate : LocalCertificate request) (target : Test request) : ReceiptTest request where
  accepts receipt := target.accepts receipt.target
  transport first second move receipt fires := by
    obtain ⟨transported, fires', equal⟩ := certificate.firing first second receipt move fires
    exact ⟨transported, fires', target.invariant _ _ equal⟩

end ReceiptTest

universe u

/-- Finite universal-input membership permits a different full-receipt test
for every rely tuple. Source reconstruction and focus typing are supplied by
the generated native query that calls this companion. -/
theorem receipt_family_exact {Input : Type u} (inputs : List Input)
    (requests : Input → Request) (tests : (input : Input) → ReceiptTest (requests input))
    (states : (input : Input) → State (requests input))
    (commute : ∀ input ∈ inputs, Coherence.LocalCommute
      (GeneralOccurrenceSemantics.Equation (requests input).plan (requests input).bound (requests input).expected)
      (CanonicalBags.StandardStep (Normalized.laws (requests input).plan) (Normalized.extrusions (requests input).plan)))
    (admitted : ∀ input ∈ inputs, Admitted (requests input))
    (covered : ∀ input ∈ inputs, checkCertificate (requests input) (states input) = true) :
    inputs.all (fun input => (tests input).check (states input)) = true ↔
      ∀ input ∈ inputs, (tests input).Meaning := by
  rw [List.all_eq_true]
  constructor
  · intro checked input member
    exact (tests input).check_sound (checked input member)
  · intro meaning input member
    exact ((tests input).check_exact (commute input member) (admitted input member) (covered input member)).mpr
      (meaning input member)

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles
