import Mettapedia.OSLF.NativeTypes.Modal.Rules
import Mettapedia.OSLF.NativeTypes.Certificates.RefinementChecking
import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedPresheafReadout

/-!
# Scoped operational occurrences as native dependent event fibres

The event relation is constructed from a selected authored schema and actual
sorted occurrence receipts. It retains the chosen focus, complete assignment,
rule origin, ordered premise history and specified right-hand-side instance.
Its actual projection is interpreted by the existing full native dependent
syntax. Complete native fibre values correspond to complete operational events,
through the independently proved presheaf/Yoneda comparison.

Continuation evidence is checked in the same full native judgment grammar.
The event declaration and its meaning are generic; finite symbol installation
and the universal rely formula are separate from this relation-level bridge.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeEventFibre

open _root_.CategoryTheory Opposite
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.TypeTheory.Calculi.NativeDependent
open Rules

universe u v

variable {plan : Plan} (schema : Schema plan)

/-- An event keeps its authored law and every independent execution witness.
The native type will classify this projection, rather than an endpoint set. -/
structure Event where
  focus : Pattern
  assignment : Assignment
  source : Pattern
  target : Pattern
  focusTyped : HasType plan.snapshot.language plan.snapshot.free
    schema.focusBound focus schema.focusCarrier
  filling : schema.fill? assignment focus = some source
  specified : schema.rhs? assignment = some target
  receipt : GeneralOccurrenceSemantics.Receipt
  valid : receipt.Valid plan schema.bound schema.programCarrier source
  ordinal : receipt.firing.job.ordinal = schema.ordinal
  declaration : receipt.firing.job.declaration = schema.declaration
  ambient : receipt.firing.job.site.focusBound = schema.bound
  completed : receipt.firing.completed = assignment
  conversion : Relation.EqvGen
    (GeneralOccurrenceSemantics.Equation plan schema.bound schema.programCarrier)
    receipt.target target

abbrev Input := Pattern × Assignment

def Event.input (event : Event schema) : Input := ⟨event.focus, event.assignment⟩

def Event.origin (event : Event schema) : Nat × List Nat ×
    List GeneralTypedSites.TypingFrame :=
  ⟨event.receipt.firing.job.declaration.declarationIndex,
    event.receipt.firing.job.site.address, event.receipt.firing.job.site.typingFrames⟩

theorem Event.authored_origin (event : Event schema) :
    event.origin.1 = schema.declaration.declarationIndex := by
  change event.receipt.firing.job.declaration.declarationIndex = _
  rw [event.declaration]

theorem Event.root_firing (event : Event schema) :
    GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan)
      event.receipt.firing.job.site.focusBound event.receipt.firing.job.site.focusType
      event.receipt.firing.job.site.focus event.receipt.firing.job.ordinal
      event.receipt.firing.matcherTrace event.receipt.firing.captured
      event.receipt.firing.completed event.receipt.firing.premiseHistory
      event.receipt.firing.localTarget := event.valid.2.2.1

theorem Event.semantic_step (event : Event schema) :
    (GeneralOccurrenceSemantics.gslt plan schema.bound schema.programCarrier).Step
      event.source event.target :=
  ⟨event.receipt.representative, event.receipt.firing,
    event.valid.1.equivalent, event.valid.2, event.conversion⟩

def fromIntroduction {term : Pattern} {assignment : Assignment} {B : Continuation.{u}}
    (enabled : plan.permissions.sites.enabled = true)
    (focusTyped : HasType plan.snapshot.language plan.snapshot.free schema.focusBound term schema.focusCarrier)
    (introduced : IntroductionCase schema term assignment B) : Event schema where
  focus := term
  assignment := assignment
  source := introduced.source
  target := introduced.target
  focusTyped := focusTyped
  filling := (Instantiation.fill_authored introduced.focus).trans introduced.sourceInstance
  specified := introduced.reduct
  receipt := ⟨introduced.source, [], introduced.primitive⟩
  valid := ⟨.nil _, introduced.valid enabled⟩
  ordinal := rfl
  declaration := rfl
  ambient := rfl
  completed := rfl
  conversion := .refl _

theorem fromIntroduction_ordered_origins {term : Pattern} {assignment : Assignment} {B : Continuation.{u}}
    (enabled : plan.permissions.sites.enabled = true)
    (focusTyped : HasType plan.snapshot.language plan.snapshot.free schema.focusBound term schema.focusCarrier)
    (introduced : IntroductionCase schema term assignment B) :
    (fromIntroduction schema enabled focusTyped introduced).receipt.firing.matcherTrace = introduced.trace ∧
      (fromIntroduction schema enabled focusTyped introduced).receipt.firing.captured = introduced.captured ∧
      (fromIntroduction schema enabled focusTyped introduced).receipt.firing.completed = assignment ∧
      (fromIntroduction schema enabled focusTyped introduced).receipt.firing.premiseHistory = introduced.history :=
  ⟨rfl, rfl, rfl, rfl⟩

section NativeMeaning

variable {W : Type u} [Category.{u} W]

abbrev inputPresheaf : Wᵒᵖ ⥤ Type u :=
  (Functor.const Wᵒᵖ).obj (ULift.{u} Input)

abbrev eventPresheaf : Wᵒᵖ ⥤ Type u :=
  (Functor.const Wᵒᵖ).obj (ULift.{u} (Event schema))

/-- Fixed snapshots restrict their complete event values coherently by identity.
The source relation itself retains actual nontrivial matching and firing data. -/
def inputProjection : eventPresheaf schema ⟶ (inputPresheaf (W := W)) where
  app _ := TypeCat.ofHom fun event => ⟨event.down.input⟩
  naturality _ _ _ := rfl

abbrev indexed := Refinement.RepresentableIndexedDeclarations.PresheafReadout.indexed
  (inputProjection (W := W) schema)

noncomputable def nativeType :
    Refinement.TypeExpr
      (Refinement.RepresentableIndexedDeclarations.symbols
        (Refinement.RepresentableIndexedDeclarations.PresheafReadout.Base W)) 1 :=
  Refinement.RepresentableIndexedDeclarations.fibreType (indexed (W := W) schema) (.var 0)

noncomputable def nativeFormation :
    Refinement.Derivation
      (Refinement.RepresentableIndexedDeclarations.signature
        (Refinement.RepresentableIndexedDeclarations.PresheafReadout.Base W))
      (.type (Refinement.RepresentableIndexedDeclarations.objectContext
        (indexed (W := W) schema).target) (nativeType (W := W) schema)) :=
  Refinement.RepresentableIndexedDeclarations.genericFibreFormed (indexed (W := W) schema)

/-- This compares the authored native parser with the independently constructed
original-arrow fibre; it is not a definition of parser correctness. -/
theorem nativeType_evaluates :
    (Refinement.RepresentableIndexedDeclarations.model
      (Refinement.RepresentableIndexedDeclarations.PresheafReadout.Base W)).evaluateType
      (Refinement.RepresentableIndexedDeclarations.objectScope (indexed (W := W) schema).target)
      (nativeType (W := W) schema) =
      some (Refinement.RepresentableIndexedDeclarations.fibreMeaning (indexed (W := W) schema)) :=
  Refinement.RepresentableIndexedDeclarations.generic_fibre_read (indexed (W := W) schema)

abbrev NativeFibre (world : W) (input : Input) :=
  Refinement.RepresentableIndexedDeclarations.PresheafReadout.NativeFibre
    (inputProjection (W := W) schema) world (ULift.up input)

noncomputable def decode (world : W) (input : Input) (value : NativeFibre schema world input) :
    {event : Event schema | event.input = input} := by
  let point := Refinement.RepresentableIndexedDeclarations.PresheafReadout.decodePoint
    (inputProjection (W := W) schema) world (ULift.up input) value
  exact ⟨point.val.down, congrArg ULift.down point.property⟩

noncomputable def encode (world : W) (input : Input) (event : Event schema)
    (same : event.input = input) : NativeFibre schema world input :=
  Refinement.RepresentableIndexedDeclarations.PresheafReadout.encodePoint
    (inputProjection (W := W) schema) world (ULift.up input) (ULift.up event)
    (congrArg ULift.up same)

theorem decode_encode (world : W) (input : Input) (event : Event schema) (same : event.input = input) :
    decode schema world input (encode schema world input event same) = ⟨event, same⟩ := by
  apply Subtype.ext
  have read := Refinement.RepresentableIndexedDeclarations.PresheafReadout.decode_encode
    (inputProjection (W := W) schema) world (ULift.up input) (ULift.up event) (congrArg ULift.up same)
  exact congrArg (fun point => point.val.down) read

theorem encode_decode (world : W) (input : Input) (value : NativeFibre schema world input) :
    encode schema world input (decode schema world input value).val
      (decode schema world input value).property = value := by
  exact Refinement.RepresentableIndexedDeclarations.PresheafReadout.encode_decode
    (inputProjection (W := W) schema) world (ULift.up input) value

noncomputable def eventEquiv (world : W) (input : Input) :
    NativeFibre schema world input ≃ {event : Event schema | event.input = input} where
  toFun := decode schema world input
  invFun := fun event => encode schema world input event.val event.property
  left_inv := encode_decode schema world input
  right_inv := fun event => decode_encode schema world input event.val event.property

theorem encode_injective (world : W) (input : Input)
    (first second : Event schema) (firstInput : first.input = input)
    (secondInput : second.input = input)
    (same : encode schema world input first firstInput = encode schema world input second secondInput) :
    first = second := by
  have read := congrArg (decode schema world input) same
  rw [decode_encode, decode_encode] at read
  exact congrArg Subtype.val read

theorem distinct_origins_remain_distinct (world : W) (input : Input)
    (first second : Event schema) (firstInput : first.input = input)
    (secondInput : second.input = input) (origins : first.origin schema ≠ second.origin schema) :
    encode schema world input first firstInput ≠ encode schema world input second secondInput := by
  intro same
  exact origins (congrArg (Event.origin schema)
    (encode_injective schema world input first second firstInput secondInput same))

theorem complete_event_readout (world : W) (input : Input) (value : NativeFibre schema world input) :
    schema.fill? input.2 input.1 = some (decode schema world input value).val.source ∧
      schema.rhs? input.2 = some (decode schema world input value).val.target ∧
      (GeneralOccurrenceSemantics.gslt plan schema.bound schema.programCarrier).Step
        (decode schema world input value).val.source (decode schema world input value).val.target := by
  let event := (decode schema world input value).val
  have focus : event.focus = input.1 := congrArg Prod.fst (decode schema world input value).property
  have assignment : event.assignment = input.2 := congrArg Prod.snd (decode schema world input value).property
  exact ⟨by rw [← focus, ← assignment]; exact event.filling,
    by rw [← assignment]; exact event.specified, event.semantic_step schema⟩

end NativeMeaning

section CheckedContinuation

variable {S : Refinement.Symbols.{v}} {D : Refinement.Signature S}
variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol] [DecidableEq S.PredicateSymbol]

/-- The continuation is native syntax. Its membership is decided only by the
independent finite derivation-certificate checker, rather than a truth oracle. -/
def CheckedContinuation (continuation : Assignment → Pattern → Refinement.Judgment S) : Continuation.{v} :=
  fun assignment target => Σ certificate : Certificates.Refinement.Certificate D,
    PLift (Certificates.Refinement.check certificate (continuation assignment target) = true)

variable {W : Type u} [Category.{u} W]

structure Response (continuation : Assignment → Pattern → Refinement.Judgment S)
    (world : W) (input : Input) where
  event : NativeFibre schema world input
  certificate : Certificates.Refinement.Certificate D
  checked : Certificates.Refinement.check certificate
    (continuation input.2 (decode schema world input event).val.target) = true

noncomputable def Response.fromIntroduction
    {term : Pattern} {assignment : Assignment}
    {continuation : Assignment → Pattern → Refinement.Judgment S}
    (enabled : plan.permissions.sites.enabled = true)
    (focusTyped : HasType plan.snapshot.language plan.snapshot.free schema.focusBound term schema.focusCarrier)
    (introduced : IntroductionCase schema term assignment (CheckedContinuation (D := D) continuation))
    (world : W) : Response (D := D) schema continuation world ⟨term, assignment⟩ := by
  let event := NativeEventFibre.fromIntroduction schema enabled focusTyped introduced
  refine ⟨encode schema world ⟨term, assignment⟩ event rfl, introduced.certificate.1, ?_⟩
  have read := congrArg (fun value => value.val.target)
    (decode_encode schema world ⟨term, assignment⟩ event rfl)
  dsimp only at read
  rw [read]
  exact introduced.certificate.2.down

theorem Response.fromIntroduction_receipt
    {term : Pattern} {assignment : Assignment}
    {continuation : Assignment → Pattern → Refinement.Judgment S}
    (enabled : plan.permissions.sites.enabled = true)
    (focusTyped : HasType plan.snapshot.language plan.snapshot.free schema.focusBound term schema.focusCarrier)
    (introduced : IntroductionCase schema term assignment (CheckedContinuation (D := D) continuation))
    (world : W) :
    (decode schema world ⟨term, assignment⟩
      (Response.fromIntroduction schema enabled focusTyped introduced world).event).val.receipt =
      (NativeEventFibre.fromIntroduction schema enabled focusTyped introduced).receipt := by
  exact congrArg (fun value => value.val.receipt)
    (decode_encode schema world ⟨term, assignment⟩
      (NativeEventFibre.fromIntroduction schema enabled focusTyped introduced) rfl)

noncomputable def Response.eliminate {continuation : Assignment → Pattern → Refinement.Judgment S}
    {world : W} {input : Input} (response : Response (D := D) schema continuation world input) :
    Σ target : Pattern, Refinement.Derivation D (continuation input.2 target) :=
  ⟨(decode schema world input response.event).val.target,
    Certificates.Refinement.reconstruct response.certificate _ response.checked⟩

theorem Response.specified_rhs {continuation : Assignment → Pattern → Refinement.Judgment S}
    {world : W} {input : Input} (response : Response (D := D) schema continuation world input) :
    schema.rhs? input.2 = some (response.eliminate schema).1 :=
  (complete_event_readout schema world input response.event).2.1

theorem Response.complete_continuation_origin {continuation : Assignment → Pattern → Refinement.Judgment S}
    {world : W} {input : Input} (response : Response (D := D) schema continuation world input) :
    Certificates.Refinement.erase (response.eliminate schema).2 = response.certificate :=
  Certificates.Refinement.erase_reconstruct response.certificate _ response.checked

end CheckedContinuation

end Mettapedia.OSLF.NativeTypes.Modal.NativeEventFibre
