import Mettapedia.OSLF.NativeTypes.Generation.ReadoutSound
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

open Mettapedia.OSLF.Framework

/-!
# Native outputs of generated operational questions

The generated question denotes a predicate of the same equation-aware GSLT
that its executable frontier implements. Conclusive answers are statements
about that native type. A separate dependent output retains every selected
physical receipt and its target certificate, in the original order.

An outgoing universal question is distinct from the incoming adjoint box.
Partial receipt lists witness existence; only checked coverage reflects all
semantic successors into the list.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Operational

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralOccurrenceFrontier
open Mettapedia.OSLF.NativeTypes.Generation
open GSLTTypeSynthesis

def theory (generated : Generated) (bound : List TypeExpr) (carrier : TypeExpr) :=
  GeneralOccurrenceSemantics.gslt generated.plan bound carrier

def continuationPredicate (request : Request) (test : InvariantTest request) :
    EquationPredicate (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected) where
  val target := test.accepts target = true
  property := by
    intro first second related
    exact congrArg (fun result => result = true) (test.invariant first second related) |>.to_iff

/-- Universal quantification over outgoing reductions. This is not the
incoming right adjoint of OSLF's step-future modality. -/
def outgoingUniversal (system : Mettapedia.GSLT.GSLT) (predicate : EquationPredicate system) :
    EquationPredicate system where
  val source := ∀ target, system.Step source target → predicate target
  property := by
    intro first second equivalent
    constructor
    · intro holds target step
      obtain ⟨actual, firstStep, same⟩ := system.rewrites_resp_left
        (system.equations.iseqv.symm equivalent) step
      exact (predicate.2 same).mpr (holds actual firstStep)
    · intro holds target step
      obtain ⟨actual, secondStep, same⟩ := system.rewrites_resp_left equivalent step
      exact (predicate.2 same).mpr (holds actual secondStep)

def questionPredicate (kind : ModalQuery) (request : Request) (test : InvariantTest request) :
    EquationPredicate (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected) :=
  match kind with
  | .possibility => semanticDiamond _ (continuationPredicate request test)
  | .outgoingUniversal => outgoingUniversal _ (continuationPredicate request test)

def questionType (kind : ModalQuery) (request : Request) (test : InvariantTest request) :
    GSLTNativeType (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected) where
  sort := ()
  pred := questionPredicate kind request test

theorem native_question_exact (kind : ModalQuery) (request : Request) (test : InvariantTest request) :
    (gsltOSLF (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected)).satisfies
      request.root (questionType kind request test).pred ↔ ModalHolds kind request test.accepts := by
  cases kind
  · exact gsltDiamond_spec _ _ _
  · rfl

theorem generated_answer_is_native_membership {generated : Generated} {bound : List TypeExpr}
    {carrier : TypeExpr} {source : Pattern} {kind : ModalQuery}
    {test : InvariantTest (generated.request bound carrier source)} {budget : Nat} {answer : Bool}
    (read : (generated.checkModal bound carrier source kind test budget).result = .decided answer) :
    answer = true ↔
      (gsltOSLF (theory generated bound carrier)).satisfies
        (generated.request bound carrier source).root
        (questionType kind (generated.request bound carrier source) test).pred :=
  (generated_modal_readout_correct read).trans (native_question_exact _ _ _).symm

theorem native_question_equation_invariant (kind : ModalQuery) (request : Request)
    (test : InvariantTest request) {first second : Pattern}
    (related : (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected).Equiv first second) :
    questionPredicate kind request test first ↔ questionPredicate kind request test second :=
  (questionPredicate kind request test).2 related

theorem native_question_on_classes (kind : ModalQuery) (request : Request) (test : InvariantTest request)
    (term : Pattern) :
    descendPredicate _ (questionType kind request test).pred
        (Quotient.mk (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected).equations term) ↔
      questionPredicate kind request test term := Iff.rfl

abbrev AnswerFamily (request : Request) (test : Pattern → Bool) :=
  GeneralOccurrenceNativeReceipts.NativeFamily request.plan request.bound request.expected
    (fun target => PLift (test target = true)) request.root

/-- Filtering annotates the actual selected receipts; it does not deduplicate
origins with the same endpoint or select an arbitrary semantic witness. -/
def retainAnswers (request : Request) (test : Pattern → Bool) : List (Answer request) →
    List (AnswerFamily request test)
  | [] => []
  | answer :: rest =>
      if accepted : test answer.val.target = true then
        ⟨answer, ⟨accepted⟩⟩ :: retainAnswers request test rest
      else retainAnswers request test rest

def answerOutputs (request : Request) (state : State request) (test : Pattern → Bool) :
    List (AnswerFamily request test) := retainAnswers request test state.answers

theorem retained_receipts_exact (request : Request) (test : Pattern → Bool) (answers : List (Answer request)) :
    (retainAnswers request test answers).map Sigma.fst =
      answers.filter (fun answer => test answer.val.target) := by
  induction answers with
  | nil => rfl
  | cons answer rest ih =>
    simp only [retainAnswers]
    by_cases accepted : test answer.val.target = true
    · simp [accepted, ih]
    · simp [accepted, ih]

theorem retained_origins_and_multiplicity (request : Request) (state : State request)
    (test : Pattern → Bool) :
    (answerOutputs request state test).map (fun output => output.1.val) =
      (state.answers.filter (fun answer => test answer.val.target)).map Subtype.val := by
  rw [answerOutputs, ← retained_receipts_exact request test state.answers, List.map_map]
  rfl

theorem output_native_membership {request : Request} {test : InvariantTest request}
    (output : AnswerFamily request test.accepts) :
    questionPredicate .possibility request test request.root := by
  apply (native_question_exact .possibility request test).mpr
  exact ⟨output.1.val.target, emitted_step request output.1, output.2.down⟩

theorem output_native_history_count {request : Request} {test : Pattern → Bool}
    (output : AnswerFamily request test) :
    (GeneralOccurrenceNativeReceipts.history request.plan request.bound request.expected output.1).length = 1 :=
  GeneralOccurrenceNativeReceipts.primitive_count _ _ _ _

theorem outputs_nonempty_iff_any (request : Request) (state : State request) (test : Pattern → Bool) :
    answerOutputs request state test ≠ [] ↔ (targets request state).any test = true := by
  have projected := retained_receipts_exact request test state.answers
  have empty : answerOutputs request state test = [] ↔
      state.answers.filter (fun answer => test answer.val.target) = [] := by
    rw [← projected, List.map_eq_nil_iff]
    rfl
  rw [ne_eq, empty]
  simp only [List.filter_eq_nil_iff, targets, List.any_eq_true, List.mem_map]
  constructor
  · intro nonempty
    by_contra absent
    apply nonempty
    intro answer member accepted
    exact absent ⟨answer.val.target, ⟨answer, member, rfl⟩, accepted⟩
  · rintro ⟨target, ⟨answer, member, same⟩, accepted⟩ allFalse
    exact allFalse answer member (same ▸ accepted)

theorem complete_outputs_exact {request : Request} {state : State request}
    (admitted : Admitted request) (certificate : checkCertificate request state = true)
    (test : InvariantTest request) :
    answerOutputs request state test.accepts ≠ [] ↔
      questionPredicate .possibility request test request.root :=
  (outputs_nonempty_iff_any request state test.accepts).trans
    ((certified_outgoing_diamond admitted certificate test.accepts test.invariant).trans
      (native_question_exact .possibility request test).symm)

theorem incoming_modal_adjunction (request : Request)
    (first second : EquationPredicate (GeneralOccurrenceSemantics.gslt request.plan request.bound request.expected)) :
    semanticDiamond _ first ≤ second ↔ first ≤ semanticBox _ second :=
  semanticGalois _ first second

end Mettapedia.OSLF.NativeTypes.Semantics.Operational
