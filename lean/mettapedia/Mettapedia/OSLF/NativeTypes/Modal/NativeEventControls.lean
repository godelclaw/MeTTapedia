import Mettapedia.OSLF.NativeTypes.Modal.NativeEventInterpretation
import Mettapedia.OSLF.NativeTypes.Modal.NativeEventTyping
import Mettapedia.OSLF.NativeTypes.Modal.NativeContinuation
import Mettapedia.OSLF.NativeTypes.Modal.InstanceExecutionControls
import Mettapedia.OSLF.NativeTypes.Modal.ConditionalControls

/-!
# Generated native event and continuation controls on the original machine

The selected nonroot schema has two nonempty rely slots. Its family and native
continuation comprehension are computed in the finite catalogue alphabet and
checked by the full dependent derivation checker. The original machine run
supplies a complete event; the native fibre recovers its actual contractum.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeEventControls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open NativeEventDeclarations
open NativeContinuation

abbrev plan := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan

def matchesSchema (candidate : Rules.Schema plan) : Bool :=
  candidate.ordinal == 0 && candidate.position == [0] &&
    candidate.programCarrier == .base "Cfg" && candidate.relyNames == ["k", "v"]

private theorem matching_index_exists : ∃ index : Index plan, matchesSchema (schema plan index) = true := by
  have witness : ∃ candidate : Rules.Schema
      Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated.plan,
      candidate ∈ schemas Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated.plan ∧
        candidate.ordinal = 0 ∧ candidate.position = [0] ∧
        candidate.programCarrier = .base "Cfg" ∧ candidate.relyNames = ["k", "v"] := by
    refine ⟨Mettapedia.OSLF.NativeTypes.Decision.Reference.ModalControls.schema, ?_, rfl, ?_, ?_, ?_⟩
    · rw [← Mettapedia.OSLF.NativeTypes.Decision.Reference.ModalControls.actual_catalogue]
      exact Mettapedia.OSLF.NativeTypes.Decision.Reference.ModalControls.actual_schema
    · exact Mettapedia.OSLF.NativeTypes.Decision.Reference.ModalControls.computed_schema.1
    · exact Mettapedia.OSLF.NativeTypes.Decision.Reference.ModalControls.computed_schema.2.2.2.2.2
    · exact Mettapedia.OSLF.NativeTypes.Decision.Reference.ModalControls.computed_schema.2.1
  rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan] at witness
  obtain ⟨candidate, present, ordinal, position, carrier, relies⟩ := witness
  obtain ⟨index, bounded, same⟩ := List.mem_iff_getElem.mp present
  refine ⟨⟨index, bounded⟩, ?_⟩
  change matchesSchema (schemas plan)[index] = true
  rw [same]
  simp only [matchesSchema, ordinal, position, carrier, relies, beq_self_eq_true, Bool.and_self]

def selectedIndex : Index plan :=
  ((List.finRange (schemas plan).length).find? fun index => matchesSchema (schema plan index)).get (by
    rw [List.find?_isSome]
    obtain ⟨index, checked⟩ := matching_index_exists
    exact ⟨index, List.mem_finRange index, checked⟩)

theorem selected_schema : (schema plan selectedIndex).position = [0] ∧
    (schema plan selectedIndex).relyNames = ["k", "v"] := by
  have actual := List.find?_some
    (show (List.finRange (schemas plan).length).find? (fun index => matchesSchema (schema plan index)) =
      some selectedIndex from (Option.some_get _).symm)
  simp only [matchesSchema, Bool.and_eq_true, beq_iff_eq] at actual
  exact ⟨actual.1.1.2, actual.2⟩

def familyJudgment : Judgment (symbols plan) :=
  .type inputContext (eventType selectedIndex (.var 0))

def formedFamily : Certificates.Refinement.Certificate (signature plan) := certificate selectedIndex

#guard Certificates.Refinement.check formedFamily familyJudgment
#guard !(Certificates.Refinement.check formedFamily (.type .nil (carrierType .pattern 0)))
#guard (schema plan selectedIndex).position == [0]
#guard (schema plan selectedIndex).relyNames == ["k", "v"]

def trueContinuation : TermExpr (symbols plan) 1 :=
  .lam (carrierType .pattern 1) .propositions (.quote .truth)

def trueContinuationFormed : Derivation (signature plan) (.term inputContext trueContinuation
    (.pi (carrierType .pattern 1) .propositions)) := by
  let patternTree := carrierFormed .pattern (inputContextFormed (plan := plan))
  let extended := deriveList (.contextExtend inputContext (carrierType .pattern 1))
    (.cons inputContextFormed (.cons patternTree .nil))
  let propositionTree := deriveList (.propositionType (.snoc inputContext (carrierType .pattern 1)))
    (.cons extended .nil)
  let predicateTree := deriveList (.truthFormation (.snoc inputContext (carrierType .pattern 1)))
    (.cons extended .nil)
  let bodyTree := deriveList (.quote (.snoc inputContext (carrierType .pattern 1)) .truth)
    (.cons predicateTree .nil)
  exact deriveList (.lambda inputContext (carrierType .pattern 1) .propositions (.quote .truth))
    (.cons patternTree (.cons propositionTree (.cons bodyTree .nil)))

def nativeResponse : TypeExpr (symbols plan) 1 :=
  responseType selectedIndex (.var 0) trueContinuation

def response : Certificates.Refinement.Certificate (signature plan) :=
  responseCertificate selectedIndex inputContextFormed inputVariableFormed trueContinuationFormed

#guard Certificates.Refinement.check response (.type inputContext nativeResponse)
#guard !(Certificates.Refinement.check response familyJudgment)

theorem response_uses_actual_native_comprehension :
    nativeResponse = .comprehension (eventType selectedIndex (.var 0))
      (.holds (.app (carrierType .pattern 2) .propositions
        (trueContinuation.rename Fin.succ)
        (specifiedTarget selectedIndex (.var 1) (.var 0)))) := rfl

namespace Operational

open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Semantics.Modal.RelyControls

def index : Index runtimePlan :=
  ((List.finRange (schemas runtimePlan).length).find? fun position =>
    (NativeEventDeclarations.schema runtimePlan position).ordinal == 0 &&
      (NativeEventDeclarations.schema runtimePlan position).position == [1]).get (by cbv)

theorem original_schema : NativeEventDeclarations.schema runtimePlan index = Mettapedia.OSLF.NativeTypes.Semantics.Modal.RelyControls.schema := by cbv

def originalEvent : NativeEventFibre.Event Mettapedia.OSLF.NativeTypes.Semantics.Modal.RelyControls.schema where
  focus := Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.alpha
  assignment := supplied Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.alpha
  source := alphaOutcome.source
  target := alphaOutcome.target
  focusTyped := by apply checkHasType_sound; cbv
  filling := alphaOutcome.filling
  specified := alphaOutcome.rhs
  receipt := actualReceipt.val
  valid := actualReceipt.property
  ordinal := rfl
  declaration := rfl
  ambient := rfl
  completed := rfl
  conversion := alphaOutcome.targetConversion

def event : NativeEventFibre.Event (NativeEventDeclarations.schema runtimePlan index) :=
  original_schema.symm ▸ originalEvent

#guard (NativeEventDeclarations.schema runtimePlan index).relyNames == ["X"]
#guard event.source == pair Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.alpha
  Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.alpha
#guard event.target == Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.done
#guard event.receipt.firing.completed == supplied Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.alpha
#guard event.receipt.firing.premiseHistory.isEmpty

def betaPrimitive : GeneralRuleJobs.Receipt where
  job := ⟨0, declaration, GeneralTypedSites.SiteData.here [] Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.carrier
    (pair Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.beta
      Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.alpha)⟩
  matcherTrace := []
  captured := supplied Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.beta
  completed := supplied Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.beta
  premiseHistory := []
  localTarget := Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.done
  target := Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.done

theorem betaPrimitive_valid : betaPrimitive.Valid runtimePlan [] Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.carrier
    (pair Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.beta
      Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.alpha) := by
  apply GeneralRuleJobs.finish_sound (job := betaPrimitive.job) (trace := [])
    (captured := supplied Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.beta)
    (completed := supplied Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.beta) (history := [])
  · refine ⟨List.mem_cons_self, .here rfl rfl ?_⟩
    apply checkHasType_sound
    cbv
  · apply GeneralScopedMatchMachine.TracedMatches.constructor
    refine GeneralScopedMatchMachine.TracedArguments.cons
      (headTrace := []) (tailTrace := [])
      (middle := supplied Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.beta) ?_ ?_
    · apply GeneralScopedMatchMachine.TracedMatches.capture
      cbv
    · exact .cons (.constructor .nil) .nil
  · exact .nil
  · cbv

def originalBetaEvent : NativeEventFibre.Event Mettapedia.OSLF.NativeTypes.Semantics.Modal.RelyControls.schema where
  focus := Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.alpha
  assignment := supplied Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.beta
  source := pair Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.beta
    Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.alpha
  target := Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.done
  focusTyped := by apply checkHasType_sound; cbv
  filling := by cbv
  specified := by cbv
  receipt := ⟨pair Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.beta
    Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.alpha, [], betaPrimitive⟩
  valid := ⟨.nil _, betaPrimitive_valid⟩
  ordinal := rfl
  declaration := rfl
  ambient := rfl
  completed := rfl
  conversion := .refl _

def betaEvent : NativeEventFibre.Event (NativeEventDeclarations.schema runtimePlan index) :=
  original_schema.symm ▸ originalBetaEvent

theorem same_answer_distinct_complete_receipts :
    event.target = betaEvent.target ∧ event.receipt ≠ betaEvent.receipt := by
  constructor
  · decide +kernel
  · intro same
    have captured := congrArg (fun receipt => receipt.firing.completed) same
    have different : event.receipt.firing.completed ≠ betaEvent.receipt.firing.completed := by decide +kernel
    exact different captured

open _root_.CategoryTheory

noncomputable def betaNativeValue (world : Discrete PUnit) :=
  NativeEventFibre.encode (NativeEventDeclarations.schema runtimePlan index) world
    (betaEvent.input _) betaEvent rfl

theorem same_native_output_distinct_receipts (world : Discrete PUnit) :
    NativeEventInterpretation.targetOutput index world (event.input _)
        (NativeEventFibre.encode (NativeEventDeclarations.schema runtimePlan index) world
          (event.input _) event rfl) =
      NativeEventInterpretation.targetOutput index world (betaEvent.input _) (betaNativeValue world) ∧
    (NativeEventFibre.decode (NativeEventDeclarations.schema runtimePlan index) world
        (event.input _) (NativeEventFibre.encode (NativeEventDeclarations.schema runtimePlan index) world
          (event.input _) event rfl)).val.receipt ≠
      (NativeEventFibre.decode (NativeEventDeclarations.schema runtimePlan index) world
        (betaEvent.input _) (betaNativeValue world)).val.receipt := by
  rw [NativeEventInterpretation.target_output_exact, NativeEventInterpretation.target_output_exact]
  change (NativeEventFibre.decode _ _ _ _).val.target = (NativeEventFibre.decode _ _ _ _).val.target ∧ _
  unfold betaNativeValue
  rw [NativeEventFibre.decode_encode, NativeEventFibre.decode_encode]
  exact same_answer_distinct_complete_receipts

open _root_.CategoryTheory

noncomputable def nativeValue (world : Discrete PUnit) :=
  NativeEventFibre.encode (NativeEventDeclarations.schema runtimePlan index) world
    (event.input _) event rfl

theorem native_output_is_actual_contractum (world : Discrete PUnit) :
    NativeEventInterpretation.targetOutput index world (event.input _) (nativeValue world) = event.target := by
  rw [NativeEventInterpretation.target_output_exact]
  exact congrArg (fun result => result.val.target)
    (NativeEventFibre.decode_encode (NativeEventDeclarations.schema runtimePlan index) world
      (event.input _) event rfl)

theorem native_receipt_is_original (world : Discrete PUnit) :
    (NativeEventFibre.decode (NativeEventDeclarations.schema runtimePlan index) world
      (event.input _) (nativeValue world)).val.receipt = event.receipt :=
  congrArg (fun result => result.val.receipt)
    (NativeEventFibre.decode_encode (NativeEventDeclarations.schema runtimePlan index) world
      (event.input _) event rfl)

end Operational

theorem absent_provider_has_no_native_event
    {W : Type} [_root_.CategoryTheory.Category W] (world : W) (input : NativeEventFibre.Input) :
    ¬ Nonempty (NativeEventFibre.NativeFibre ConditionalControls.schema world input) := by
  rintro ⟨value⟩
  exact ConditionalControls.no_primitive
    ((NativeEventFibre.decode ConditionalControls.schema world input value).val.root_firing _)

end Mettapedia.OSLF.NativeTypes.Modal.NativeEventControls
