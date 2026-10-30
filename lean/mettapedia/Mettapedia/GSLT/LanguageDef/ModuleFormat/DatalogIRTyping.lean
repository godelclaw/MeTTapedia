import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
import Mettapedia.Languages.Datalog.IRCodec
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! Declared primitive carriers type compact semantic IR payloads directly.
This bridge uses the shared carrier judgment; selecting a native realization
for that judgment is a separate executor obligation. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Typing

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext UsesBareCollection)
open Mettapedia.Languages.Datalog

abbrev Typed (sort : String) (term : Pattern) : Prop :=
  _root_.Mettapedia.GSLT.LanguageDef.CarrierWellSorted.HasType language FreeTypeContext.empty [] term (.base sort)

private theorem ctor (index : Fin language.terms.length) (arguments : List Pattern)
    (typed : _root_.Mettapedia.GSLT.LanguageDef.CarrierWellSorted.ArgumentsHaveTypes language FreeTypeContext.empty [] arguments (language.terms.get index).params) :
    Typed (language.terms.get index).category (.apply (language.terms.get index).label arguments) := by
  apply _root_.Mettapedia.GSLT.LanguageDef.CarrierWellSorted.HasType.constructor (List.get_mem language.terms index) _ typed
  fin_cases index <;> simp [UsesBareCollection,GrammarRule.bareParams,language]

private theorem string_atom (sort : String)
    (declared : List.Mem (TypeDecl.mk sort .builtinString) language.types) (text : String) :
    Typed sort (IRCodec.atom text) :=
  .builtinAtom ⟨_,declared,rfl,rfl⟩

private theorem integer_atom (sort : String)
    (declared : List.Mem (TypeDecl.mk sort .builtinInt) language.types) (input : Int) :
    Typed sort (IRCodec.atom input.repr) := by
  apply _root_.Mettapedia.GSLT.LanguageDef.CarrierWellSorted.HasType.builtinAtom
  refine ⟨_,declared,rfl,?_⟩
  simp [CarrierWellSorted.carrierAcceptsAtom]

private theorem natural_atom (sort : String)
    (declared : List.Mem (TypeDecl.mk sort .builtinInt) language.types) (input : Nat) :
    Typed sort (IRCodec.atom input.repr) := by
  apply _root_.Mettapedia.GSLT.LanguageDef.CarrierWellSorted.HasType.builtinAtom
  refine ⟨_,declared,rfl,?_⟩
  simp [CarrierWellSorted.carrierAcceptsAtom]

private theorem elements {α : Type} (sort : String) (encode : α → Pattern)
    (typed : ∀ input, Typed sort (encode input)) (inputs : List α) :
    _root_.Mettapedia.GSLT.LanguageDef.CarrierWellSorted.ElementsHaveTypes language FreeTypeContext.empty [] (inputs.map encode) (.base sort) := by
  induction inputs with
  | nil => exact .nil
  | cons input inputs ih => exact .cons (typed input) ih

private theorem vector {α : Type} (sort : String) (encode : α → Pattern)
    (typed : ∀ input, Typed sort (encode input)) (inputs : List α) :
    _root_.Mettapedia.GSLT.LanguageDef.CarrierWellSorted.HasType language FreeTypeContext.empty [] (IRCodec.vector encode inputs) (.collection .vec (.base sort)) :=
  .collection (elements sort encode typed inputs)

theorem value_typed (input : Value) : Typed "DlValue" (IRCodec.value input) := by
  cases input with
  | symbol text =>
    apply ctor ⟨1,by decide +kernel⟩ [IRCodec.atom text]
    exact .cons trivial rfl (string_atom _ (by exact List.get_mem language.types ⟨0,by decide +kernel⟩) text) .nil
  | number number =>
    apply ctor ⟨2,by decide +kernel⟩ [IRCodec.atom number.repr]
    exact .cons trivial rfl (integer_atom _ (by exact List.get_mem language.types ⟨1,by decide +kernel⟩) number) .nil
  | unsigned number =>
    apply ctor ⟨3,by decide +kernel⟩ [IRCodec.atom number.repr]
    exact .cons trivial rfl (natural_atom _ (by exact List.get_mem language.types ⟨2,by decide +kernel⟩) number) .nil
  | floating word =>
    apply ctor ⟨4,by decide +kernel⟩ [IRCodec.atom word.toNat.repr]
    exact .cons trivial rfl (natural_atom _ (by exact List.get_mem language.types ⟨3,by decide +kernel⟩) word.toNat) .nil

theorem qualifiedName_typed (name : QualifiedName) : Typed "DlQualifiedName" (IRCodec.qualifiedName name) := by
  apply ctor ⟨0,by decide +kernel⟩ [IRCodec.vector IRCodec.atom name]
  exact .cons trivial rfl (vector "DlIdentifier" IRCodec.atom (string_atom _ (by exact List.get_mem language.types ⟨4,by decide +kernel⟩)) name) .nil

theorem relation_typed (name : QualifiedName) : Typed "DlRelation" (IRCodec.relation name) := by
  apply ctor ⟨11,by decide +kernel⟩ [IRCodec.qualifiedName name]
  exact .cons trivial rfl (qualifiedName_typed name) .nil

theorem argument_typed (input : Argument) : Typed "DlArgument" (IRCodec.argument input) := by
  cases input with
  | literal input =>
    apply ctor ⟨6,by decide +kernel⟩ [IRCodec.value input]
    exact .cons trivial rfl (value_typed input) .nil
  | var name =>
    apply ctor ⟨7,by decide +kernel⟩ [.apply "Variable" [IRCodec.atom name]]
    refine .cons trivial rfl ?_ .nil
    apply ctor ⟨5,by decide +kernel⟩ [IRCodec.atom name]
    exact .cons trivial rfl (string_atom _ (by exact List.get_mem language.types ⟨4,by decide +kernel⟩) name) .nil
  | anonymous => exact ctor ⟨8,by decide +kernel⟩ [] .nil

theorem tuple_typed (inputs : List Argument) : Typed "DlTuple" (IRCodec.tuple inputs) := by
  apply ctor ⟨10,by decide +kernel⟩ [IRCodec.vector IRCodec.argument inputs]
  exact .cons trivial rfl (vector _ _ argument_typed inputs) .nil

theorem groundTuple_typed (inputs : List Value) : Typed "DlGroundTuple" (IRCodec.groundTuple inputs) := by
  apply ctor ⟨9,by decide +kernel⟩ [IRCodec.vector IRCodec.value inputs]
  exact .cons trivial rfl (vector _ _ value_typed inputs) .nil

theorem positiveAtom_typed (input : Atom) : Typed "DlPositiveLiteralData" (IRCodec.positiveAtom input) := by
  apply ctor ⟨24,by decide +kernel⟩ [IRCodec.relation input.relation,IRCodec.tuple input.arguments]
  exact .cons trivial rfl (relation_typed _) (.cons trivial rfl (tuple_typed _) .nil)

theorem groundFact_typed (input : GroundFact) : Typed "DlStatement" (IRCodec.groundFact input) := by
  apply ctor ⟨28,by decide +kernel⟩ [IRCodec.relation input.relation,IRCodec.groundTuple input.values]
  exact .cons trivial rfl (relation_typed _) (.cons trivial rfl (groundTuple_typed _) .nil)

theorem comparison_typed (input : Comparison) : Typed "DlComparisonData" (IRCodec.comparison input) := by
  rcases input with ⟨operator,left,right⟩
  cases operator
  all_goals
    first
    | apply ctor ⟨18,by decide +kernel⟩ [IRCodec.argument left,IRCodec.argument right]
    | apply ctor ⟨19,by decide +kernel⟩ [IRCodec.argument left,IRCodec.argument right]
    | apply ctor ⟨20,by decide +kernel⟩ [IRCodec.argument left,IRCodec.argument right]
    | apply ctor ⟨21,by decide +kernel⟩ [IRCodec.argument left,IRCodec.argument right]
    | apply ctor ⟨22,by decide +kernel⟩ [IRCodec.argument left,IRCodec.argument right]
    | apply ctor ⟨23,by decide +kernel⟩ [IRCodec.argument left,IRCodec.argument right]
  all_goals exact .cons trivial rfl (argument_typed _) (.cons trivial rfl (argument_typed _) .nil)

theorem premise_typed (input : Mettapedia.Languages.Datalog.Premise) : Typed "DlPositiveLiteralData" (IRCodec.premise input) := by
  cases input with
  | atom input => exact positiveAtom_typed input
  | comparison input =>
    apply ctor ⟨25,by decide +kernel⟩ [IRCodec.comparison input]
    exact .cons trivial rfl (comparison_typed _) .nil

theorem clause_typed (input : Clause) : Typed "DlClause" (IRCodec.clause input) := by
  apply ctor ⟨26,by decide +kernel⟩
    [IRCodec.relation input.head.relation,IRCodec.tuple input.head.arguments,IRCodec.vector IRCodec.premise input.body]
  exact .cons trivial rfl (relation_typed _) (.cons trivial rfl (tuple_typed _)
    (.cons trivial rfl (vector _ _ premise_typed _) .nil))

theorem attributeType_typed (input : AttributeType) : Typed "DlAttributeType" (IRCodec.attributeType input) := by
  cases input
  · exact ctor ⟨12,by decide +kernel⟩ [] .nil
  · exact ctor ⟨13,by decide +kernel⟩ [] .nil
  · exact ctor ⟨14,by decide +kernel⟩ [] .nil
  · exact ctor ⟨15,by decide +kernel⟩ [] .nil

theorem attribute_typed (input : Attribute) : Typed "DlAttributeData" (IRCodec.attributeData input) := by
  apply ctor ⟨16,by decide +kernel⟩ [IRCodec.atom input.name,IRCodec.attributeType input.type]
  exact .cons trivial rfl (string_atom _ (by exact List.get_mem language.types ⟨4,by decide +kernel⟩) _)
    (.cons trivial rfl (attributeType_typed _) .nil)

theorem declaration_typed (input : RelationDeclaration) : Typed "DlRelationDeclaration" (IRCodec.declaration input) := by
  apply ctor ⟨17,by decide +kernel⟩ [IRCodec.relation input.name,IRCodec.vector IRCodec.attributeData input.attributes]
  exact .cons trivial rfl (relation_typed _) (.cons trivial rfl (vector _ _ attribute_typed _) .nil)

theorem statement_typed (input : Statement) : Typed "DlStatement" (IRCodec.statement input) := by
  cases input with
  | declaration input =>
    apply ctor ⟨27,by decide +kernel⟩ [IRCodec.declaration input]
    exact .cons trivial rfl (declaration_typed _) .nil
  | fact input => exact groundFact_typed input
  | rule input =>
    apply ctor ⟨29,by decide +kernel⟩ [IRCodec.clause input]
    exact .cons trivial rfl (clause_typed _) .nil
  | input name =>
    apply ctor ⟨30,by decide +kernel⟩ [IRCodec.relation name]
    exact .cons trivial rfl (relation_typed _) .nil
  | output name =>
    apply ctor ⟨31,by decide +kernel⟩ [IRCodec.relation name]
    exact .cons trivial rfl (relation_typed _) .nil

theorem program_typed (input : Program) : Typed "DlProgramData" (IRCodec.program input) := by
  apply ctor ⟨32,by decide +kernel⟩ [IRCodec.vector IRCodec.statement input.statements]
  exact .cons trivial rfl (vector _ _ statement_typed _) .nil

#print axioms value_typed
#print axioms qualifiedName_typed
#print axioms program_typed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Typing
