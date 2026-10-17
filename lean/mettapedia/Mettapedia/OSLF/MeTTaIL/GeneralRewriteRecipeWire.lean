import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipe
import Mettapedia.GSLT.LanguageDef.GeneralPremiseReceiptWire

/-!
# Lossless authored rewrite-recipe requests

The wire retains the original snapshot and permissions, the complete caller
context and endpoints, every selected rule/equation occurrence, and all
matching and premise evidence. Validation compiles the decoded snapshot and
permissions itself. A caller cannot substitute a submitted compiled plan.

Canonical data and whole-word decoding reject representation aliases and
trailing input. This is an exact serialization and checking boundary, without
an executed time or space bound.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeWire

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission GeneralOccurrenceSemantics
open Mettapedia.OSLF.Binding.WireCodec

open Mettapedia.GSLT.LanguageDef

/-- Original equation position, complete declaration plan and typed site. -/
def equationJobCodec : Codec GeneralEquationJobs.Job :=
  (Codec.prod Codec.nat
    (Codec.prod GeneralPremiseReceiptWire.equationPlanCodec GeneralPremiseReceiptWire.siteCodec)).mapped
    (fun value => (value.planPosition, value.equation, value.site))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2⟩)
    (fun _ => rfl)

/-- Every original equation-receipt field is retained, including raw reduct
and separately observed target. -/
def equationReceiptCodec : Codec GeneralEquationJobs.Receipt :=
  (Codec.prod equationJobCodec
    (Codec.prod GeneralPremiseReceiptWire.traceCodec
      (Codec.prod GeneralPremiseReceiptWire.assignmentCodec
        (Codec.prod GeneralPremiseReceiptWire.assignmentCodec
          (Codec.prod GeneralPremiseReceiptWire.eventsCodec
            (Codec.prod GeneralPremiseReceiptWire.patternCodec GeneralPremiseReceiptWire.patternCodec)))))).mapped
    (fun value => (value.job, value.matcherTrace, value.captured, value.completed,
      value.premiseHistory, value.rawReduct, value.target))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
      fields.2.2.2.2.1, fields.2.2.2.2.2.1, fields.2.2.2.2.2.2⟩)
    (fun _ => rfl)

private def putConversion : Conversion → Data
  | .forward value => .pair (.atom 0) (equationReceiptCodec.put value)
  | .reverse value => .pair (.atom 1) (equationReceiptCodec.put value)

private def getConversion : Data → Option Conversion
  | .pair (.atom 0) value => (equationReceiptCodec.get value).map .forward
  | .pair (.atom 1) value => (equationReceiptCodec.get value).map .reverse
  | _ => none

/-- Conversion direction is separate from the declaration plan's own
orientation. Both survive decoding literally. -/
def conversionCodec : Codec Conversion := ⟨putConversion, getConversion, fun value => by
  cases value <;> simp only [putConversion, getConversion, Codec.get_put] <;> rfl⟩

theorem conversion_unknown_tag_refused (tag : Nat) (data : Data)
    (notForward : tag ≠ 0) (notReverse : tag ≠ 1) :
    conversionCodec.get (.pair (.atom tag) data) = none := by
  cases tag with
  | zero => exact (notForward rfl).elim
  | succ tag =>
      cases tag with
      | zero => exact (notReverse rfl).elim
      | succ => rfl

/-- The original representative, pre-conversions and physical firing article. -/
def occurrenceReceiptCodec : Codec GeneralOccurrenceSemantics.Receipt :=
  (Codec.prod GeneralPremiseReceiptWire.patternCodec
    (Codec.prod (Codec.list conversionCodec) GeneralPremiseReceiptWire.receiptCodec)).mapped
    (fun value => (value.representative, value.conversions, value.firing))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2⟩)
    (fun _ => rfl)

def stepTraceCodec : Codec GeneralRewriteRecipe.StepTrace :=
  (Codec.prod occurrenceReceiptCodec (Codec.list conversionCodec)).mapped
    (fun value => (value.before, value.after))
    (fun fields => some ⟨fields.1, fields.2⟩)
    (fun _ => rfl)

/-- A request carries the authored data, not a replacement compiled plan. -/
structure Request where
  snapshot : Snapshot
  permissions : Permissions
  bound : List TypeExpr
  type : TypeExpr
  source : Pattern
  target : Pattern
  step : GeneralRewriteRecipe.StepTrace
  deriving Repr

def requestFieldsCodec : Codec Request :=
  (Codec.prod GeneralPremiseReceiptWire.snapshotCodec
    (Codec.prod GeneralPremiseReceiptWire.permissionsCodec
      (Codec.prod (Codec.list Mettapedia.GSLT.LanguageDef.BindingSyntax.Wire.typeCodec)
        (Codec.prod Mettapedia.GSLT.LanguageDef.BindingSyntax.Wire.typeCodec
          (Codec.prod GeneralPremiseReceiptWire.patternCodec
            (Codec.prod GeneralPremiseReceiptWire.patternCodec stepTraceCodec)))))).mapped
    (fun value => (value.snapshot, value.permissions, value.bound, value.type,
      value.source, value.target, value.step))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
      fields.2.2.2.2.1, fields.2.2.2.2.2.1, fields.2.2.2.2.2.2⟩)
    (fun _ => rfl)

def requestTag : String := "gslt-authored-rewrite-recipe-v1"

def requestCodec : Codec Request :=
  (Codec.prod Codec.string requestFieldsCodec).mapped
    (fun value => (requestTag, value))
    (fun fields => if fields.1 = requestTag then some fields.2 else none)
    (fun _ => by simp only [ite_true])

theorem request_unknown_tag_refused (tag : String) (request : Request)
    (different : tag ≠ requestTag) :
    requestCodec.get (.pair (Codec.string.put tag) (requestFieldsCodec.put request)) = none := by
  simp only [requestCodec, Codec.mapped, Codec.prod, Codec.get_put, Bind.bind, Option.bind]
  simp [different]

theorem request_atom_refused (tag : Nat) : requestCodec.get (.atom tag) = none := rfl

/-- The original occurrence semantics supplies the meaning of a request. -/
def Request.Valid (request : Request) : Prop :=
  GeneralRewriteRecipe.StepTrace.Valid (compile request.snapshot request.permissions)
    request.bound request.type request.source request.target request.step

def checkRequest (request : Request) : Bool :=
  GeneralRewriteRecipe.checkAuthored request.snapshot request.permissions request.bound request.type
    request.source request.target request.step

theorem checkRequest_exact (request : Request) :
    checkRequest request = true ↔ request.Valid :=
  GeneralRewriteRecipe.checkAuthored_exact _ _ _ _ _ _ _

/-- Canonical structured data retains precisely the encoder's literal fields. -/
def decodeData (data : Data) : Option Request := requestCodec.canonicalGet data

theorem decodeData_encode (request : Request) :
    decodeData (requestCodec.put request) = some request :=
  Codec.canonicalGet_put requestCodec request

theorem decodeData_exact (data : Data) (request : Request) :
    decodeData data = some request ↔ requestCodec.put request = data := by
  constructor
  · exact Codec.put_of_canonicalGet requestCodec data request
  · intro same
    rw [← same]
    exact decodeData_encode request

def checkData (data : Data) : Bool :=
  match decodeData data with
  | none => false
  | some request => checkRequest request

theorem checkData_exact (data : Data) :
    checkData data = true ↔ ∃ request, requestCodec.put request = data ∧ request.Valid := by
  have decoded : checkData data = true ↔
      ∃ request, decodeData data = some request ∧ request.Valid := by
    cases result : decodeData data with
    | none => simp [checkData, result]
    | some request => simp [checkData, result, checkRequest_exact]
  simpa only [decodeData_exact] using decoded

def encodeRequest (request : Request) : List Binary.Alphabet :=
  Binary.encodeWith requestCodec request

def decodeRequest (word : List Binary.Alphabet) : Option Request :=
  Binary.canonicalDecodeWith requestCodec word

theorem decodeRequest_encodeRequest (request : Request) :
    decodeRequest (encodeRequest request) = some request :=
  Binary.canonicalDecodeWith_encodeWith requestCodec request

theorem decodeRequest_exact (word : List Binary.Alphabet) (request : Request) :
    decodeRequest word = some request ↔ encodeRequest request = word :=
  Binary.canonicalDecodeWith_exact requestCodec word request

theorem encodeRequest_injective : Function.Injective encodeRequest :=
  Binary.encodeWith_injective requestCodec

theorem decodeRequest_trailing_refused (request : Request) (tail : List Binary.Alphabet)
    (nonempty : tail.isEmpty = false) :
    decodeRequest (encodeRequest request ++ tail) = none :=
  Binary.canonicalDecodeWith_trailing_refused requestCodec request tail nonempty

def checkWord (word : List Binary.Alphabet) : Bool :=
  match decodeRequest word with
  | none => false
  | some request => checkRequest request

theorem checkWord_trailing_refused (request : Request) (tail : List Binary.Alphabet)
    (nonempty : tail.isEmpty = false) :
    checkWord (encodeRequest request ++ tail) = false := by
  simp only [checkWord, decodeRequest_trailing_refused request tail nonempty]

theorem checkWord_exact (word : List Binary.Alphabet) :
    checkWord word = true ↔ ∃ request, encodeRequest request = word ∧ request.Valid := by
  have decoded : checkWord word = true ↔
      ∃ request, decodeRequest word = some request ∧ request.Valid := by
    cases result : decodeRequest word with
    | none => simp [checkWord, result]
    | some request => simp [checkWord, result, checkRequest_exact]
  simpa only [decodeRequest_exact] using decoded

@[simp] theorem checkWord_encodeRequest (request : Request) :
    checkWord (encodeRequest request) = checkRequest request := by
  simp only [checkWord, decodeRequest_encodeRequest]

theorem checkWord_encodeRequest_exact (request : Request) :
    checkWord (encodeRequest request) = true ↔ request.Valid := by
  rw [checkWord_encodeRequest, checkRequest_exact]

/-- Encoding a recipe preserves exact finite-evidence coverage for the
authored snapshot's own equation-saturated occurrence semantics. -/
theorem exists_checked_word_iff_step (snapshot : Snapshot) (permissions : Permissions)
    (bound : List TypeExpr) (type : TypeExpr) (source target : Pattern) :
    (∃ recipe, checkWord (encodeRequest ⟨snapshot, permissions, bound, type, source, target, recipe⟩) = true) ↔
      (GeneralOccurrenceSemantics.gslt (compile snapshot permissions) bound type).Step source target := by
  simpa only [checkWord_encodeRequest, checkRequest, GeneralRewriteRecipe.checkAuthored] using
    GeneralRewriteRecipe.exists_checked_iff_step (compile snapshot permissions) bound type source target

end Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeWire
