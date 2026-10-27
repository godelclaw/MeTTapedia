import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedFamilyChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionElaboration

/-!
# Typed declaration computations elaborated to finite conversion certificates

A bubble selects rows of the existing typed iota-schema table. Its states
retain the complete typing index, and each step retains the original row and
a typed substitution instance of its receipt. Elaboration computes an actual
certificate for the existing structural decoder; it does not search for an
equal equation or reconstruct a proof from endpoint equality.

The selected decoder accepts the emitted certificate. Widening permissions
leaves that certificate unchanged, including row addresses, arguments and
composition. These are typed declaration computations in the original
declaration calculus. Uniform raw subject preservation, normalization and an
object-theory equality interpretation remain separate obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Declaration.IndexedFamily.ConversionBubbles

open Mettapedia.TypeTheory
open BubbleConversion BubbleElaboration
open ComputationAuthority

variable {Head : Type} {base : Rules Head} {signature : Signature Head}
    {computation : ProofRelevantRootComputation Head}

abbrev State (base : Rules Head) (signature : Signature Head) (index : TypingIndex Head) :=
  (indexedDeclaredComputation base signature).State index

/-- The original row and typed instance are retained even when another row
has the same endpoints. -/
structure Step (schemas : Checking.Schemas base signature computation)
    (enabled : Fin (Checking.table schemas).length → Bool)
    {index : TypingIndex Head} (source target : State base signature index) where
  row : Fin (Checking.table schemas).length
  permitted : enabled row = true
  occurrence : (Checking.receiptAt schemas row).2.2.InstanceAt
    index.context source.1 target.1 index.type

def bubbles (schemas : Checking.Schemas base signature computation) : Bubbles (TypingIndex Head) where
  State := State base signature
  Bubble := Fin (Checking.table schemas).length → Bool
  Step := Step schemas

variable (schemas : Checking.Schemas base signature computation)

/-- The canonical typed schema is an open-context instance of its original
row. Its telescope and displayed type come from the retained receipt. -/
def canonicalStep (enabled : Fin (Checking.table schemas).length → Bool)
    (row : Fin (Checking.table schemas).length) (permitted : enabled row = true) :
    Step schemas enabled
      (index := ⟨((Checking.table schemas).get row).1,
        (Checking.receiptAt schemas row).1, (Checking.receiptAt schemas row).2.1⟩)
      ⟨((Checking.table schemas).get row).2.1, ⟨(Checking.receiptAt schemas row).2.2.sourceTyping⟩⟩
      ⟨((Checking.table schemas).get row).2.2, ⟨(Checking.receiptAt schemas row).2.2.targetTyping⟩⟩ where
  row := row
  permitted := permitted
  occurrence := (Checking.receiptAt schemas row).2.2.identityInstance

namespace Step

variable {schemas} {enabled : Fin (Checking.table schemas).length → Bool}
    {index : TypingIndex Head} {source target : State base signature index}

def receipt (step : Step schemas enabled source target) :
    ProofRelevantStepReceipt base signature computation index.context source.1 target.1 index.type :=
  step.occurrence.toReceipt

def rootCode (step : Step schemas enabled source target) :
    SchemaTableConversionCode.Code Head index.arity :=
  SchemaTableConversionCode.encode (Checking.table schemas) step.row step.occurrence.substitution

theorem rootCode_accepted (step : Step schemas enabled source target) :
    SchemaTableConversionCode.decode (Checking.table schemas) enabled step.rootCode =
      some (source.1, target.1) := by
  have decoded := SchemaTableConversionCode.decode_encode (Checking.table schemas) enabled
    step.row step.permitted step.occurrence.substitution
  simpa only [rootCode, step.occurrence.sourceEquation,
    step.occurrence.targetEquation] using decoded

def widen {large : Fin (Checking.table schemas).length → Bool}
    (included : ∀ row, enabled row = true → large row = true)
    (step : Step schemas enabled source target) : Step schemas large source target where
  row := step.row
  permitted := included step.row step.permitted
  occurrence := step.occurrence

@[simp] theorem rootCode_widen {large : Fin (Checking.table schemas).length → Bool}
    (included : ∀ row, enabled row = true → large row = true)
    (step : Step schemas enabled source target) : (step.widen included).rootCode = step.rootCode := rfl

end Step

section Certificates

variable [DecidableEq Head] [DecidableRel base.headEq]

/-- All table rows remain explicit citations in the receiving checker. The
source bubble can enable a strict subset. -/
def certificates : (bubbles schemas).GlobalEquality :=
  StructuralConversionCode.Elaboration.equality (bubbles schemas) TypingIndex.arity
    (fun state => state.1) base.headEq
    (SchemaTableConversionCode.decode (Checking.table schemas) (fun _ => true))

def justify {enabled : Fin (Checking.table schemas).length → Bool}
    {index : TypingIndex Head} {source target : State base signature index}
    (step : Step schemas enabled source target) : (certificates schemas).Eq source target :=
  StructuralConversionCode.Certificate.single (.root step.rootCode)
    (decide_eq_true (step.widen (fun _ _ => rfl)).rootCode_accepted)

/-- Fold the actual typed computation tree into the maintained finite code. -/
def elaborate {enabled : Fin (Checking.table schemas).length → Bool}
    {index : TypingIndex Head} {source target : State base signature index}
    (path : (bubbles schemas).Conv enabled source target) :
    (certificates schemas).Eq source target :=
  StructuralConversionCode.Elaboration.emit (B := bubbles schemas)
    (arity := TypingIndex.arity) (readout := fun state => state.1) (justify schemas) path

@[simp] theorem elaborate_step {enabled : Fin (Checking.table schemas).length → Bool}
    {index : TypingIndex Head} {source target : State base signature index}
    (step : Step schemas enabled source target) :
    (elaborate schemas (.step step)).code = .single (.root step.rootCode) := by
  exact StructuralConversionCode.Elaboration.code_step (B := bubbles schemas)
    (arity := TypingIndex.arity) (readout := fun state => state.1) (justify schemas) step

@[simp] theorem elaborate_refl (enabled : Fin (Checking.table schemas).length → Bool)
    {index : TypingIndex Head} (state : State base signature index) :
    (elaborate schemas (enabled := enabled)
      (.refl (computation := FreeConversion.computation (bubbles schemas).State
        ((bubbles schemas).Step enabled)) state)).code = .refl state.1 := by
  exact StructuralConversionCode.Elaboration.code_refl (B := bubbles schemas)
    (arity := TypingIndex.arity) (readout := fun state => state.1) (justify schemas) state

@[simp] theorem elaborate_symm {enabled : Fin (Checking.table schemas).length → Bool}
    {index : TypingIndex Head} {source target : State base signature index}
    (path : (bubbles schemas).Conv enabled source target) :
    (elaborate schemas (.symm path)).code = .symm (elaborate schemas path).code := by
  exact StructuralConversionCode.Elaboration.code_symm (justify schemas) path

@[simp] theorem elaborate_trans {enabled : Fin (Checking.table schemas).length → Bool}
    {index : TypingIndex Head} {source middle target : State base signature index}
    (first : (bubbles schemas).Conv enabled source middle)
    (second : (bubbles schemas).Conv enabled middle target) :
    (elaborate schemas (.trans first second)).code =
      .trans (elaborate schemas first).code (elaborate schemas second).code := by
  exact StructuralConversionCode.Elaboration.code_trans (justify schemas) first second

/-- The emitted code also checks in the exact selected source bubble, rather
than depending on additional permissions of the receiving checker. -/
theorem elaborate_selected {enabled : Fin (Checking.table schemas).length → Bool}
    {index : TypingIndex Head} {source target : State base signature index}
    (path : (bubbles schemas).Conv enabled source target) :
    (elaborate schemas path).code.check base.headEq
      (SchemaTableConversionCode.decode (Checking.table schemas) enabled)
      source.1 target.1 = true := by
  exact StructuralConversionCode.Elaboration.checkWith (B := bubbles schemas)
    (RootCode := SchemaTableConversionCode.Code Head)
    (arity := TypingIndex.arity) (readout := fun state => state.1)
    (justify schemas (enabled := enabled)) base.headEq
    (SchemaTableConversionCode.decode (Checking.table schemas) enabled)
    (fun step => by
      simpa only [justify, StructuralConversionCode.Certificate.single,
        StructuralConversionCode.Code.check, StructuralConversionCode.Code.decode,
        StructuralConversionCode.StepCode.decode] using decide_eq_true step.rootCode_accepted) path

theorem elaborate_work {enabled : Fin (Checking.table schemas).length → Bool}
    {index : TypingIndex Head} {source target : State base signature index}
    (path : (bubbles schemas).Conv enabled source target) :
    (elaborate schemas path).code.stepCount = BubbleElaboration.stepCount path := by
  exact StructuralConversionCode.Elaboration.stepCount (justify schemas) (fun _ => rfl) path

/-- The emitted certificate denotes conversion in the original declaration
calculus, using the independently established support equation. -/
theorem elaborate_original
    (support : signature.computation = computation.support)
    {enabled : Fin (Checking.table schemas).length → Bool}
    {index : TypingIndex Head} {source target : State base signature index}
    (path : (bubbles schemas).Conv enabled source target) :
    Conv (extendRules base signature).headEq source.1 target.1
      (extendRules base signature).computation := by
  have selected := StructuralConversionCode.Code.check_sound (Checking.rootDecoder schemas enabled)
    (elaborate_selected schemas path)
  simpa only [Tm.mapHead_id] using selected.mapHead (fun head => head)
    (Checking.inclusion schemas support enabled).headEq
    (Checking.inclusion schemas support enabled).computation

/-- Increasing permissions preserves the entire emitted code, not only its
endpoints or number of steps. -/
theorem elaborate_widen {small large : Fin (Checking.table schemas).length → Bool}
    (included : ∀ row, small row = true → large row = true)
    {index : TypingIndex Head} {source target : State base signature index}
    (path : (bubbles schemas).Conv small source target) :
    elaborate schemas ((bubbles schemas).widen (Step.widen included) path) =
      elaborate schemas path :=
  BubbleElaboration.sound_widen (bubbles schemas) (certificates schemas)
    (Step.widen included) (justify schemas) (justify schemas) (fun _ => rfl) path

end Certificates

section CheckedInput

variable (decoder : StructuralConversionCode.RootDecoder (extendRules base signature).computation)
variable [DecidableEq Head] [DecidableRel base.headTyping] [DecidablePred base.isUniverse]
    [∀ u v w, Decidable (base.join u v w)] [DecidableRel base.cumulative]
    [DecidableRel base.headEq]

local instance : DecidableRel (extendRules base signature).headTyping :=
  fun h u => inferInstanceAs (Decidable (base.headTyping h u))
local instance : DecidablePred (extendRules base signature).isUniverse :=
  fun h => inferInstanceAs (Decidable (base.isUniverse h))
local instance : ∀ u v w, Decidable ((extendRules base signature).join u v w) :=
  fun u v w => inferInstanceAs (Decidable (base.join u v w))
local instance : DecidableRel (extendRules base signature).cumulative :=
  fun h u => inferInstanceAs (Decidable (base.cumulative h u))
local instance : DecidableRel (extendRules base signature).headEq :=
  fun h u => inferInstanceAs (Decidable (base.headEq h u))

/-- Checked requests supply the typed instance; no extra preservation
hypothesis is added at this entry point. -/
def ofRequest {n : Nat} {context : Ctx Head n}
    (request : Checking.InstanceRequest schemas decoder context)
    (enabled : Fin (Checking.table schemas).length → Bool)
    (left right displayed : Tm Head n)
    (accepted : request.check schemas decoder enabled left right displayed = true) :
    Step schemas enabled
      (index := ⟨n, context, displayed⟩)
      ⟨left, ⟨(request.replay schemas decoder enabled left right displayed accepted).sourceTyping⟩⟩
      ⟨right, ⟨(request.replay schemas decoder enabled left right displayed accepted).targetTyping⟩⟩ := by
  have checked := accepted
  simp only [Checking.InstanceRequest.check, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨request.index, checked.1, request.substitution,
    (request.arguments.sound decoder checked.2.1).2.toRaw,
    checked.2.2.1, checked.2.2.2.1, checked.2.2.2.2⟩

/-- The checker-to-bubble route retains the request's submitted row and
arguments verbatim. -/
theorem ofRequest_rootCode {n : Nat} {context : Ctx Head n}
    (request : Checking.InstanceRequest schemas decoder context)
    (enabled : Fin (Checking.table schemas).length → Bool)
    (left right displayed : Tm Head n)
    (accepted : request.check schemas decoder enabled left right displayed = true) :
    (ofRequest schemas decoder request enabled left right displayed accepted).rootCode =
      request.rootCode schemas decoder := rfl

end CheckedInput

#print axioms Step.rootCode_accepted
#print axioms elaborate_selected
#print axioms elaborate_work
#print axioms elaborate_original
#print axioms elaborate_widen
#print axioms ofRequest

end Declaration.IndexedFamily.ConversionBubbles
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
