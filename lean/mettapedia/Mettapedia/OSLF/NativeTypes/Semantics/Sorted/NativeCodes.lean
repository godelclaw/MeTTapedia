import Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes
import Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Formation
import Mettapedia.OSLF.NativeTypes.Modal.NativeElimination

open Mettapedia.OSLF.Framework

/-!
# Structural and dependent modal codes in chosen sort subobjects

A model supplies carrier-bounded native sort subobjects at every dependency
context. Actual generated constructor inputs, rely inputs and substituted
continuations are interpreted inside those subobjects. The generated syntax
and its checked kind are retained separately from this interpretation data.

The specified-contractum eliminator keeps the original primitive receipt and
equation conversion. Its continuation certificate lies in the requested sort
subobject at the actual substituted assignment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation (Generated StructuralInputs structuralDeclaration structuralInputSort structuralOutputSort)
open Mettapedia.OSLF.NativeTypes.Modal.Rules (Schema TypeCode Evidence TypedRequest)
open Mettapedia.OSLF.NativeTypes.Modal.Formation (RelyCode RelyIndex RelyCodes relyMeaning continuationMeaning generatedFormer)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes (SortInterpretation)
open ModalHypercube (HSort)

abbrev Model (generated : Generated) := (bound : List TypeExpr) → SortInterpretation generated bound

def restrictCode {generated : Generated} {bound : List TypeExpr} {carrier : TypeExpr} {sort : HSort}
    (interpretation : SortInterpretation generated bound) (native : TypeCode generated.plan bound carrier sort) :
    TypeCode generated.plan bound carrier sort where
  meaning term := interpretation.sortDomain carrier sort term ∧ native.meaning term
  bounded term inhabited := interpretation.carrierBounded carrier sort term inhabited.1

theorem restricted_code_readout {generated : Generated} {bound : List TypeExpr}
    {carrier : TypeExpr} {sort : HSort} (interpretation : SortInterpretation generated bound)
    (native : TypeCode generated.plan bound carrier sort) (term : Pattern) :
    (restrictCode interpretation native).meaning term ↔
      interpretation.sortDomain carrier sort term ∧ native.meaning term := Iff.rfl

def restrictStructuralInputs {generated : Generated} {bound : List TypeExpr}
    (interpretation : SortInterpretation generated bound)
    {index : Fin generated.snapshot.language.terms.length} (inputs : StructuralInputs generated bound index) :
    StructuralInputs generated bound index := fun position => restrictCode interpretation (inputs position)

def structuralCode {generated : Generated} {bound : List TypeExpr}
    (interpretation : SortInterpretation generated bound)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index) :
    TypeCode generated.plan bound (.base (structuralDeclaration generated index).category)
      (structuralOutputSort generated index) :=
  restrictCode interpretation
    (Mettapedia.OSLF.NativeTypes.Generation.structuralCode generated bound index (restrictStructuralInputs interpretation inputs))

theorem structural_image_exact {generated : Generated} {bound : List TypeExpr}
    (interpretation : SortInterpretation generated bound)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (term : Pattern) :
    (structuralCode interpretation index inputs).meaning term ↔
      interpretation.sortDomain (.base (structuralDeclaration generated index).category)
        (structuralOutputSort generated index) term ∧
      HasType generated.snapshot.language generated.snapshot.free bound term
        (.base (structuralDeclaration generated index).category) ∧
      ∃ value : Mettapedia.OSLF.NativeTypes.Structural.ConstructorValue generated.snapshot.language generated.snapshot.free bound
          (structuralDeclaration generated index),
        Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound
          (.base (structuralDeclaration generated index).category)) term value.pattern ∧
        ∀ position,
          interpretation.sortDomain (structuralDeclaration generated index).params[position].typeExpr
            (structuralInputSort generated index position)
            (value.arguments[position.val]'(by rw [value.arguments_length]; exact position.isLt)) ∧
          (inputs position).meaning
            (value.arguments[position.val]'(by rw [value.arguments_length]; exact position.isLt)) := Iff.rfl

/-- Constructor introduction is interpreted in the chosen model. Sort-domain
membership is model data and is never inferred from finite center admission. -/
theorem structural_intro {generated : Generated} {bound : List TypeExpr}
    (interpretation : SortInterpretation generated bound)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (value : Mettapedia.OSLF.NativeTypes.Structural.ConstructorValue generated.snapshot.language generated.snapshot.free bound
      (structuralDeclaration generated index))
    (outputSort : interpretation.sortDomain (.base (structuralDeclaration generated index).category)
      (structuralOutputSort generated index) value.pattern)
    (arguments : ∀ position, (restrictCode interpretation (inputs position)).meaning
      (value.arguments[position.val]'(by rw [value.arguments_length]; exact position.isLt))) :
    (structuralCode interpretation index inputs).meaning value.pattern :=
  ⟨outputSort, Mettapedia.OSLF.NativeTypes.Generation.structural_intro generated bound index
    (restrictStructuralInputs interpretation inputs) value arguments⟩

def restrictRely {generated : Generated} {schema : Schema generated.plan} {name : String} {sort : HSort}
    (model : Model generated) (native : RelyCode schema name sort) : RelyCode schema name sort where
  carrier := native.carrier
  dependencies := native.dependencies
  declaredCarrier := native.declaredCarrier
  declaredDependencies := native.declaredDependencies
  meaning value := native.meaning value ∧
    (model (native.dependencies ++ schema.bound)).sortDomain native.carrier sort value.body
  bounded value inhabited := native.bounded value inhabited.1

theorem restricted_rely_readout {generated : Generated} {schema : Schema generated.plan}
    {name : String} {sort : HSort} (model : Model generated) (native : RelyCode schema name sort)
    (value : ContextualValue) : (restrictRely model native).meaning value ↔
      native.meaning value ∧
        (model (native.dependencies ++ schema.bound)).sortDomain native.carrier sort value.body := Iff.rfl

def restrictRelyCodes {generated : Generated} {schema : Schema generated.plan}
    {sorts : RelyIndex schema → HSort} (model : Model generated) (inputs : RelyCodes schema sorts) :
    RelyCodes schema sorts := fun name => restrictRely model (inputs name)

def restrictContinuations {generated : Generated} {schema : Schema generated.plan} {sort : HSort}
    (model : Model generated)
    (continuations : Assignment → TypeCode generated.plan schema.bound schema.programCarrier sort) :
    Assignment → TypeCode generated.plan schema.bound schema.programCarrier sort :=
  fun assignment => restrictCode (model schema.bound) (continuations assignment)

def modalCode {generated : Generated} (model : Model generated) (schema : Schema generated.plan)
    (parameters : Mettapedia.OSLF.NativeTypes.Generation.ModalParameters schema)
    (inputs : Mettapedia.OSLF.NativeTypes.Generation.ModalInputs schema (some parameters)) :
    TypeCode generated.plan schema.focusBound schema.focusCarrier parameters.output :=
  restrictCode (model schema.focusBound)
    (generatedFormer schema parameters.inputs parameters.output parameters.output
      (restrictRelyCodes model inputs.1) (restrictContinuations model inputs.2))

theorem modal_inhabitant_exact {generated : Generated} (model : Model generated)
    (schema : Schema generated.plan) (parameters : Mettapedia.OSLF.NativeTypes.Generation.ModalParameters schema)
    (inputs : Mettapedia.OSLF.NativeTypes.Generation.ModalInputs schema (some parameters)) (term : Pattern) :
    (modalCode model schema parameters inputs).meaning term ↔
      (model schema.focusBound).sortDomain schema.focusCarrier parameters.output term ∧
      Nonempty (Evidence schema (relyMeaning (restrictRelyCodes model inputs.1))
        (continuationMeaning (restrictContinuations model inputs.2)) term) := Iff.rfl

theorem modal_m_form {generated : Generated} {model : Model generated}
    {schema : Schema generated.plan} {parameters : Mettapedia.OSLF.NativeTypes.Generation.ModalParameters schema}
    {inputs : Mettapedia.OSLF.NativeTypes.Generation.ModalInputs schema (some parameters)} {term : Pattern}
    (inhabited : (modalCode model schema parameters inputs).meaning term) :
    (model schema.focusBound).sortDomain schema.focusCarrier parameters.output term ∧
      HasType generated.snapshot.language generated.snapshot.free schema.focusBound term schema.focusCarrier :=
  ⟨inhabited.1, (model schema.focusBound).carrierBounded _ _ _ inhabited.1⟩

/-- This is a native eliminator of a genuine interpreted inhabitant. The
assignment-indexed certificate is read at the specified RHS, while the original
primitive target and all equation conversions remain in its native family. -/
def modalEliminate {generated : Generated} {model : Model generated}
    {schema : Schema generated.plan} {parameters : Mettapedia.OSLF.NativeTypes.Generation.ModalParameters schema}
    {inputs : Mettapedia.OSLF.NativeTypes.Generation.ModalInputs schema (some parameters)} {term : Pattern}
    (implementation : Evidence schema (relyMeaning (restrictRelyCodes model inputs.1))
      (continuationMeaning (restrictContinuations model inputs.2)) term)
    (assignment : Assignment)
    (request : TypedRequest schema (relyMeaning (restrictRelyCodes model inputs.1)) implementation.anchor assignment) :=
  Mettapedia.OSLF.NativeTypes.Modal.NativeElimination.eliminate implementation assignment request

theorem modal_m_step_elim {generated : Generated} {model : Model generated}
    {schema : Schema generated.plan} {parameters : Mettapedia.OSLF.NativeTypes.Generation.ModalParameters schema}
    {inputs : Mettapedia.OSLF.NativeTypes.Generation.ModalInputs schema (some parameters)} {term : Pattern}
    (implementation : Evidence schema (relyMeaning (restrictRelyCodes model inputs.1))
      (continuationMeaning (restrictContinuations model inputs.2)) term)
    (assignment : Assignment)
    (request : TypedRequest schema (relyMeaning (restrictRelyCodes model inputs.1)) implementation.anchor assignment) :
    let result := modalEliminate implementation assignment request
    schema.fill? assignment term = some result.source ∧
      schema.rhs? assignment = some result.native.2.1 ∧
      (GeneralOccurrenceSemantics.gslt generated.plan schema.bound schema.programCarrier).Step
        result.source result.native.2.1 ∧
      (model schema.bound).sortDomain schema.programCarrier parameters.output result.native.2.1 ∧
      (inputs.2 assignment).meaning result.native.2.1 := by
  let result := modalEliminate implementation assignment request
  have contract := Mettapedia.OSLF.NativeTypes.Modal.NativeElimination.elimination_contract result
  exact ⟨contract.1, contract.2.1, contract.2.2.1, result.native.2.2.2.down⟩

theorem modal_elimination_keeps_primitive_origin {generated : Generated} {model : Model generated}
    {schema : Schema generated.plan} {parameters : Mettapedia.OSLF.NativeTypes.Generation.ModalParameters schema}
    {inputs : Mettapedia.OSLF.NativeTypes.Generation.ModalInputs schema (some parameters)} {term : Pattern}
    (implementation : Evidence schema (relyMeaning (restrictRelyCodes model inputs.1))
      (continuationMeaning (restrictContinuations model inputs.2)) term)
    (assignment : Assignment)
    (request : TypedRequest schema (relyMeaning (restrictRelyCodes model inputs.1)) implementation.anchor assignment) :
    (modalEliminate implementation assignment request).native.1.val =
      (implementation.respond assignment request).receipt ∧
    (GeneralOccurrenceNativeReceipts.history generated.plan schema.bound schema.programCarrier
      (modalEliminate implementation assignment request).native.1).length = 1 :=
  ⟨rfl, Mettapedia.OSLF.NativeTypes.Modal.NativeElimination.elimination_primitive_count _⟩

theorem modal_inhabitant_has_complete_elimination {generated : Generated} {model : Model generated}
    {schema : Schema generated.plan} {parameters : Mettapedia.OSLF.NativeTypes.Generation.ModalParameters schema}
    {inputs : Mettapedia.OSLF.NativeTypes.Generation.ModalInputs schema (some parameters)} {term : Pattern}
    (inhabited : (modalCode model schema parameters inputs).meaning term) :
    ∃ implementation : Evidence schema (relyMeaning (restrictRelyCodes model inputs.1))
        (continuationMeaning (restrictContinuations model inputs.2)) term,
      ∀ assignment (request : TypedRequest schema (relyMeaning (restrictRelyCodes model inputs.1))
        implementation.anchor assignment),
        let result := modalEliminate implementation assignment request
        schema.rhs? assignment = some result.native.2.1 ∧
          (GeneralOccurrenceSemantics.gslt generated.plan schema.bound schema.programCarrier).Step
            result.source result.native.2.1 ∧
          (model schema.bound).sortDomain schema.programCarrier parameters.output result.native.2.1 ∧
          (inputs.2 assignment).meaning result.native.2.1 := by
  obtain ⟨implementation⟩ := inhabited.2
  exact ⟨implementation, fun assignment request => (modal_m_step_elim implementation assignment request).2⟩

/-- Reinterpreting a completed response preserves its actual receipt. The
additional sort certificate is checked at its specified target, not substituted
for the dependent continuation or for the execution path. -/
def interpretOutcome {generated : Generated} {model : Model generated}
    {schema : Schema generated.plan} {term : Pattern} {assignment : Assignment} {sort : HSort}
    {continuations : Assignment → TypeCode generated.plan schema.bound schema.programCarrier sort}
    (outcome : Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome schema term assignment (continuationMeaning continuations))
    (sorted : (model schema.bound).sortDomain schema.programCarrier sort outcome.target) :
    Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome schema term assignment
      (continuationMeaning (restrictContinuations model continuations)) where
  source := outcome.source
  target := outcome.target
  filling := outcome.filling
  rhs := outcome.rhs
  receipt := outcome.receipt
  valid := outcome.valid
  targetConversion := outcome.targetConversion
  certificate := ⟨sorted, outcome.certificate.down⟩

theorem interpreted_outcome_keeps_execution {generated : Generated} {model : Model generated}
    {schema : Schema generated.plan} {term : Pattern} {assignment : Assignment} {sort : HSort}
    {continuations : Assignment → TypeCode generated.plan schema.bound schema.programCarrier sort}
    (outcome : Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome schema term assignment (continuationMeaning continuations))
    (sorted : (model schema.bound).sortDomain schema.programCarrier sort outcome.target) :
    (interpretOutcome outcome sorted).receipt = outcome.receipt ∧
      (interpretOutcome outcome sorted).target = outcome.target ∧
      (interpretOutcome outcome sorted).certificate.down.2 = outcome.certificate.down := ⟨rfl, rfl, rfl⟩

end Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes
