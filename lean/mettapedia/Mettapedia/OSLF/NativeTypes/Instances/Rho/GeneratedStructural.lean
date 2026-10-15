import Mettapedia.OSLF.NativeTypes.Structural.InterpretedCodes
import Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedChecking

open Mettapedia.OSLF.Framework

/-!
# Original rho checking of the generated structural native codes

Constructor indices, input carriers and universe slots come from the generated
signature. Original rho canonical equations interpret that same syntax. Native
input codes are compared at actual typed object arguments; the whole-output
comparison is then proved from the independently checked ordered fibres.

This does not identify the original equation model with the separately bounded
GeneralOccurrence equation engine.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.GeneratedStructural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation (Generated StructuralInputs structuralDeclaration structuralInputSort structuralOutputSort)
open Mettapedia.OSLF.NativeTypes.Modal.Rules (TypeCode)
open Mettapedia.OSLF.NativeTypes.Structural (ConstructorValue)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.PropositionalCodes (SortInterpretation)
open Mettapedia.OSLF.NativeTypes.Instances.Rho.CarrierEquations
open Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedDecomposition
open Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedChecking
open Mettapedia.OSLF.NativeTypes.Structural.InterpretedCodes (Introduction)

def changeLanguage {first second : LanguageDef} (same : first = second)
    {free : FreeTypeContext} {bound : List TypeExpr} {rule : GrammarRule}
    (value : ConstructorValue first free bound rule) : ConstructorValue second free bound rule :=
  same ▸ value

theorem change_language_pattern {first second : LanguageDef} (same : first = second)
    {free : FreeTypeContext} {bound : List TypeExpr} {rule : GrammarRule}
    (value : ConstructorValue first free bound rule) : (changeLanguage same value).pattern = value.pattern := by
  cases same
  rfl

theorem change_language_arguments {first second : LanguageDef} (same : first = second)
    {free : FreeTypeContext} {bound : List TypeExpr} {rule : GrammarRule}
    (value : ConstructorValue first free bound rule) : (changeLanguage same value).arguments = value.arguments := by
  cases same
  rfl

theorem parameters_exact {rule : GrammarRule} (member : rule ∈ rhoCalc.terms)
    (position : Fin rule.params.length) :
    parameterType? rule.params[position.val] = some rule.params[position.val].typeExpr := by
  simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases position <;> rfl

private theorem arguments_typed_at {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
    (typed : ArgumentsHaveTypes language free bound arguments parameters)
    (index : Nat) (inRange : index < parameters.length) {carrier : TypeExpr}
    (expected : parameterType? parameters[index] = some carrier) :
    HasType language free bound (arguments[index]'(by rw [typed.length_eq]; exact inRange)) carrier := by
  induction index generalizing arguments parameters carrier with
  | zero =>
    cases typed with
    | nil => simp at inRange
    | @cons _ first rest parameter parameters actual representation parameterType firstTyped tailTyped =>
      have same : actual = carrier := Option.some.inj (parameterType.symm.trans expected)
      exact same ▸ firstTyped
  | succ index ih =>
    cases typed with
    | nil => simp at inRange
    | cons representation parameterType firstTyped tailTyped =>
      exact ih tailTyped (Nat.lt_of_succ_lt_succ inRange) expected

theorem object_arguments {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {rule : GrammarRule}
    (value : ConstructorValue language free bound rule) (object : isObjectPattern value.pattern = true) :
    isObjectPatternList value.arguments = true := by
  cases value with
  | ordinary arguments ordinary typed => exact object
  | collection name kind elementType elements rest shape typed =>
    simpa only [ConstructorValue.pattern, ConstructorValue.arguments,
      isObjectPatternList, Bool.and_true] using object

private theorem object_list_get {arguments : List Pattern} (object : isObjectPatternList arguments = true)
    (index : Nat) (inRange : index < arguments.length) : isObjectPattern arguments[index] = true := by
  induction arguments generalizing index with
  | nil => simp at inRange
  | cons first rest ih =>
    have objects := Bool.and_eq_true_iff.mp object
    cases index with
    | zero => exact objects.1
    | succ index => exact ih objects.2 index (Nat.lt_of_succ_lt_succ inRange)

def checkedInputs {generated : Generated}
    (index : Fin generated.snapshot.language.terms.length) : Type :=
  Inputs (structuralDeclaration generated index)

abbrev InputComparison {generated : Generated} {bound : List TypeExpr}
    (model : SortInterpretation generated bound)
    (index : Fin generated.snapshot.language.terms.length)
    (native : StructuralInputs generated bound index) (checked : checkedInputs index) :=
  ∀ position term,
    HasType generated.snapshot.language generated.snapshot.free bound term
      (structuralDeclaration generated index).params[position.val].typeExpr →
    isObjectPattern term = true →
    ((model.sortDomain (structuralDeclaration generated index).params[position.val].typeExpr
      (structuralInputSort generated index position) term ∧ (native position).meaning term) ↔
      (checked position).meaning term)

@[instance_reducible]
def rhoEquations : Mettapedia.OSLF.NativeTypes.Structural.InterpretedCodes.Equations := fun carrier =>
  if carrier = TypeExpr.bag TypeExpr.proc then bagEquations else canonicalEquations

theorem output_equations (category : String) : rhoEquations (.base category) = canonicalEquations := by
  simp [rhoEquations, TypeExpr.bag]

theorem native_image_exact {generated : Generated} {bound : List TypeExpr}
    (language : generated.snapshot.language = rhoCalc) (model : SortInterpretation generated bound)
    (index : Fin generated.snapshot.language.terms.length)
    (native : StructuralInputs generated bound index) (checked : checkedInputs index)
    (compareInputs : InputComparison model index native checked) (source : Pattern) :
    (Mettapedia.OSLF.NativeTypes.Structural.InterpretedCodes.structuralCode rhoEquations model index native).meaning source ↔
      model.sortDomain (.base (structuralDeclaration generated index).category)
        (structuralOutputSort generated index) source ∧
      isObjectPattern source = true ∧
      Holds generated.snapshot.free bound (structuralDeclaration generated index) checked source := by
  have member : structuralDeclaration generated index ∈ rhoCalc.terms := by
    rw [← language]
    exact List.getElem_mem index.isLt
  constructor
  · rintro ⟨output, object, value, valueObject, related, arguments⟩
    let converted := changeLanguage language value
    let rhoValue : Value generated.snapshot.free bound (structuralDeclaration generated index) :=
      ⟨converted, by rw [change_language_pattern]; exact valueObject⟩
    have represents : canonicalEquations.r source rhoValue.val.pattern := by
      rw [change_language_pattern]
      rw [output_equations] at related
      exact related
    refine ⟨output, object, rhoValue, represents, ?_⟩
    intro position
    have typed := arguments_typed_at rhoValue.val.arguments_typed position.val position.isLt
      (parameters_exact member position)
    have objects := object_list_get (object_arguments rhoValue.val rhoValue.property)
      position.val (by rw [rhoValue.val.arguments_length]; exact position.isLt)
    have typedOriginal : HasType generated.snapshot.language generated.snapshot.free bound
        (argument rhoValue position) (structuralDeclaration generated index).params[position.val].typeExpr := by
      rw [language]
      exact typed
    apply (compareInputs position (argument rhoValue position) typedOriginal objects).mp
    simpa [rhoValue, converted, argument, Mettapedia.OSLF.NativeTypes.Structural.InterpretedCodes.argument,
      change_language_arguments] using arguments position
  · rintro ⟨output, object, value, related, arguments⟩
    let converted := changeLanguage language.symm value.val
    refine ⟨output, object, converted, ?_, ?_, ?_⟩
    · rw [change_language_pattern]
      exact value.property
    · rw [change_language_pattern, output_equations]
      exact related
    · intro position
      have typed := arguments_typed_at value.val.arguments_typed position.val position.isLt
        (parameters_exact member position)
      have objects := object_list_get (object_arguments value.val value.property)
        position.val (by rw [value.val.arguments_length]; exact position.isLt)
      have typedOriginal : HasType generated.snapshot.language generated.snapshot.free bound
          (argument value position) (structuralDeclaration generated index).params[position.val].typeExpr := by
        rw [language]
        exact typed
      have accepted := (compareInputs position (argument value position) typedOriginal objects).mpr
        (arguments position)
      simpa [converted, argument, Mettapedia.OSLF.NativeTypes.Structural.InterpretedCodes.argument,
        change_language_arguments] using accepted

theorem executable_native_exact {generated : Generated} {bound : List TypeExpr}
    (language : generated.snapshot.language = rhoCalc) (model : SortInterpretation generated bound)
    (index : Fin generated.snapshot.language.terms.length)
    (native : StructuralInputs generated bound index) (checked : checkedInputs index)
    (compareInputs : InputComparison model index native checked) (source : Pattern)
    (output : model.sortDomain (.base (structuralDeclaration generated index).category)
      (structuralOutputSort generated index) source) (object : isObjectPattern source = true) :
    evaluate generated.snapshot.free bound (structuralDeclaration generated index) checked
      (completionBudget source) source = some true ↔
      (Mettapedia.OSLF.NativeTypes.Structural.InterpretedCodes.structuralCode rhoEquations model index native).meaning source := by
  have member : structuralDeclaration generated index ∈ rhoCalc.terms := by
    rw [← language]
    exact List.getElem_mem index.isLt
  rw [checked_exact _ _ _ member checked source,
    native_image_exact language model index native checked compareInputs source]
  exact ⟨fun holds => ⟨output, object, holds⟩, fun inhabited => inhabited.2.2⟩

/-- A concrete object-carrier interpretation. Universe coordinates remain the
computed generated coordinates; the semantic domain is explicitly supplied. -/
def objectModel (generated : Generated) (bound : List TypeExpr) : SortInterpretation generated bound where
  sortDomain carrier _ term :=
    HasType generated.snapshot.language generated.snapshot.free bound term carrier ∧ isObjectPattern term = true
  carrierBounded _ _ _ inhabited := inhabited.1

def nativeInputCodes (generated : Generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length)
    (checked : checkedInputs index) : StructuralInputs generated bound index :=
  fun position => {
    meaning term := HasType generated.snapshot.language generated.snapshot.free bound term
        (structuralDeclaration generated index).params[position.val].typeExpr ∧
      isObjectPattern term = true ∧ (checked position).meaning term
    bounded _ inhabited := inhabited.1}

theorem native_input_codes_exact {generated : Generated} {bound : List TypeExpr}
    (index : Fin generated.snapshot.language.terms.length)
    (checked : checkedInputs index) :
    InputComparison (objectModel generated bound) index (nativeInputCodes generated bound index checked) checked := by
  intro position term typed object
  constructor
  · intro inhabited
    exact inhabited.2.2.2
  · intro accepted
    exact ⟨⟨typed, object⟩, typed, object, accepted⟩

def nativeCode (generated : Generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length)
    (checked : checkedInputs index) :
    TypeCode generated.plan bound (.base (structuralDeclaration generated index).category)
      (structuralOutputSort generated index) :=
  Mettapedia.OSLF.NativeTypes.Structural.InterpretedCodes.structuralCode rhoEquations (objectModel generated bound) index
    (nativeInputCodes generated bound index checked)

theorem generated_native_check_exact {generated : Generated} {bound : List TypeExpr}
    (language : generated.snapshot.language = rhoCalc)
    (index : Fin generated.snapshot.language.terms.length)
    (checked : checkedInputs index) (source : Pattern)
    (typed : HasType generated.snapshot.language generated.snapshot.free bound source
      (.base (structuralDeclaration generated index).category)) (object : isObjectPattern source = true) :
    evaluate generated.snapshot.free bound (structuralDeclaration generated index) checked
      (completionBudget source) source = some true ↔ (nativeCode generated bound index checked).meaning source :=
  executable_native_exact language (objectModel generated bound) index
    (nativeInputCodes generated bound index checked) checked (native_input_codes_exact index checked)
    source ⟨typed, object⟩ object

/-- Native outputs are selected through the actual generated constructor
catalogue, rather than a second list of supported constructor labels. -/
def generatedFormer? (generated : Generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length)
    (checked : checkedInputs index) :
    Option (Σ sort, TypeCode generated.plan bound (.base (structuralDeclaration generated index).category) sort) :=
  if (⟨index.val, structuralDeclaration generated index⟩ : Mettapedia.OSLF.NativeTypes.Structural.Former) ∈
      generated.structuralCatalogue then
    some ⟨structuralOutputSort generated index, nativeCode generated bound index checked⟩
  else none

theorem generated_former_selected {generated : Generated} {bound : List TypeExpr}
    (index : Fin generated.snapshot.language.terms.length)
    (checked : checkedInputs index)
    (selected : (⟨index.val, structuralDeclaration generated index⟩ : Mettapedia.OSLF.NativeTypes.Structural.Former) ∈
      generated.structuralCatalogue) :
    generatedFormer? generated bound index checked =
      some ⟨structuralOutputSort generated index, nativeCode generated bound index checked⟩ := by
  simp [generatedFormer?, selected]

#print axioms native_image_exact
#print axioms executable_native_exact
#print axioms generated_native_check_exact

end Mettapedia.OSLF.NativeTypes.Instances.Rho.GeneratedStructural
