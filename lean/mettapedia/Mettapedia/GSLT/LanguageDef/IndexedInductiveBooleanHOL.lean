import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLFacts
import Mettapedia.Logic.HOL.BooleanFacts
import Mathlib.Tactic.FinCases

/-!
# The admitted Boolean family and its selected HOL interpretation

The two nullary source constructors generate the actual polynomial fixed
family. Its comparison with Boolean data is an equivalence, and the selected
structural manifest retains recursion, induction and no-confusion. Finiteness
rules out the infinity witness used by the separate natural-number profile.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductiveBooleanHOL

open Mettapedia.TypeTheory
open IndexedPolynomial IndexedPolynomial.Description

def interface : Interface where
  SortCode := Empty
  Value := Empty.elim
  Index := Unit
  IndexExpr := fun _ => Unit
  evalIndex := fun expression _ => expression

def resultCode : Code interface [] := .result ()

def admitted : IndexedInductive.Admitted interface [] :=
  ⟨[⟨"False", resultCode⟩, ⟨"True", resultCode⟩], by decide⟩

def source : IndexedInductive.Document interface [] := .bundle
  [.declaration ⟨"False", .result ()⟩, .declaration ⟨"True", .result ()⟩]

theorem source_admitted : IndexedInductive.admit? source = some admitted :=
  IndexedInductive.admit_quote admitted

abbrev Carrier := admitted.Family PUnit.unit ()

def falseValue : Carrier :=
  .roll ⟨(0 : Fin 2), ⟨⟨rfl⟩⟩⟩ (fun impossible => by
    change PEmpty at impossible
    exact impossible.elim)

def trueValue : Carrier :=
  .roll ⟨(1 : Fin 2), ⟨⟨rfl⟩⟩⟩ (fun impossible => by
    change PEmpty at impossible
    exact impossible.elim)

def ofBool : Bool → Carrier
  | false => falseValue
  | true => trueValue

def toBool : Carrier → Bool
  | .roll shape _children => shape.1.val == 1

@[simp] theorem toBool_ofBool (value : Bool) : toBool (ofBool value) = value := by
  cases value <;> rfl

@[simp] theorem ofBool_toBool : ∀ tree : Carrier, ofBool (toBool tree) = tree
  | .roll shape children => by
      rcases shape with ⟨occurrence, fields⟩
      fin_cases occurrence
      all_goals
        change ULift (PLift (() = ())) at fields
        have fieldsSame : fields = ⟨⟨rfl⟩⟩ := Subsingleton.elim _ _
        subst fields
        first | change falseValue = _ | change trueValue = _
        first | unfold falseValue | unfold trueValue
        congr 1
        funext position
        change PEmpty at position
        exact position.elim

def boolEquiv : Carrier ≃ Bool where
  toFun := toBool
  invFun := ofBool
  left_inv := ofBool_toBool
  right_inv := toBool_ofBool

theorem constructors_distinct : falseValue ≠ trueValue := by
  intro same
  have codes := congrArg toBool same
  exact Bool.noConfusion codes

theorem false_generated : admitted.construct (environment := PUnit.unit) (index := ())
    ⟨(0 : Fin 2), (⟨⟨rfl⟩⟩ : ULift (PLift (() = ())))⟩ = falseValue := by
  apply boolEquiv.injective
  rfl
theorem true_generated : admitted.construct (environment := PUnit.unit) (index := ())
    ⟨(1 : Fin 2), (⟨⟨rfl⟩⟩ : ULift (PLift (() = ())))⟩ = trueValue := by
  apply boolEquiv.injective
  rfl

theorem source_cases (value : Carrier) : value = falseValue ∨ value = trueValue := by
  obtain ⟨flag, rfl⟩ := boolEquiv.symm.surjective value
  cases flag
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem finite_carrier : Finite Carrier := Finite.of_equiv Bool boolEquiv.symm

def caseAlgebra {Result : Type 1} (falseResult trueResult : Result) :
    Algebra admitted.polynomial (fun _ _ => Result) where
  act := fun _ _ layer => if layer.1.1.val == 1 then trueResult else falseResult

noncomputable def generatedRecursor {Result : Type 1} (falseResult trueResult : Result) : Carrier → Result :=
  Fix.fold admitted.polynomial (caseAlgebra falseResult trueResult).act PUnit.unit ()

@[simp] theorem generatedRecursor_false {Result : Type 1} (falseResult trueResult : Result) :
    generatedRecursor falseResult trueResult falseValue = falseResult := rfl

@[simp] theorem generatedRecursor_true {Result : Type 1} (falseResult trueResult : Result) :
    generatedRecursor falseResult trueResult trueValue = trueResult := rfl

/-- The ordinary Boolean reading is selected only for this finite source
family. The comparison retains its constructor names and generated fold. -/
noncomputable def logicalReading : Carrier ≃ ULift.{1} Prop :=
  boolEquiv.trans (Equiv.ulift.symm.trans Mettapedia.Logic.HOL.BooleanFacts.boolPropEquiv)

@[simp] theorem logicalReading_false : logicalReading falseValue = ⟨False⟩ := rfl
@[simp] theorem logicalReading_true : logicalReading trueValue = ⟨True⟩ := rfl

noncomputable def logicalRecursor {Result : Type 1} (falseResult trueResult : Result)
    (value : ULift.{1} Prop) : Result :=
  generatedRecursor falseResult trueResult (logicalReading.symm value)

theorem logicalRecursor_commutes {Result : Type 1} (falseResult trueResult : Result) (value : Carrier) :
    logicalRecursor falseResult trueResult (logicalReading value) =
      generatedRecursor falseResult trueResult value := by
  unfold logicalRecursor
  rw [logicalReading.symm_apply_apply]

@[simp] theorem logicalRecursor_false {Result : Type 1} (falseResult trueResult : Result) :
    logicalRecursor falseResult trueResult ⟨False⟩ = falseResult := by
  have inverse : logicalReading.symm ⟨False⟩ = falseValue :=
    logicalReading.symm_apply_apply falseValue
  exact (congrArg (generatedRecursor falseResult trueResult) inverse).trans rfl

@[simp] theorem logicalRecursor_true {Result : Type 1} (falseResult trueResult : Result) :
    logicalRecursor falseResult trueResult ⟨True⟩ = trueResult := by
  have inverse : logicalReading.symm ⟨True⟩ = trueValue :=
    logicalReading.symm_apply_apply trueValue
  exact (congrArg (generatedRecursor falseResult trueResult) inverse).trans rfl

namespace NativeMeaning

open Mettapedia.Logic.HOL.BooleanFacts

/-- The native statement's witness is the actual source-generated recursor,
transported through the selected two-value reading. -/
theorem models_recursion (Result : Type 1) : (model Result).models recursion := by
  intro falseResult _ trueResult _
  exact ⟨logicalRecursor falseResult trueResult, trivial,
    logicalRecursor_false falseResult trueResult, logicalRecursor_true falseResult trueResult⟩

theorem models_induction (M : Mettapedia.Logic.HOL.HenkinModel.{0, 0, 0} Base Const) : M.models induction := by
  intro predicate _ bases value _
  obtain ⟨sourceValue, rfl⟩ := logicalReading.surjective value
  rcases source_cases sourceValue with same | same
  · subst sourceValue
    exact bases.1
  · subst sourceValue
    exact bases.2

theorem models_noConfusion (M : Mettapedia.Logic.HOL.HenkinModel.{0, 0, 0} Base Const) : M.models noConfusion := by
  intro same
  have images : logicalReading falseValue = logicalReading trueValue :=
    ULift.down_injective (propext same)
  exact constructors_distinct (logicalReading.injective images)

theorem models_cases (M : Mettapedia.Logic.HOL.HenkinModel.{0, 0, 0} Base Const) : M.models cases := by
  intro value _
  obtain ⟨sourceValue, rfl⟩ := logicalReading.surjective value
  rcases source_cases sourceValue with same | same
  · subst sourceValue
    exact Or.inl Iff.rfl
  · subst sourceValue
    exact Or.inr Iff.rfl

theorem models_finite (M : Mettapedia.Logic.HOL.HenkinModel.{0, 0, 0} Base Const) : M.models finite := by
  intro function _ injective target _
  change (ULift.{1} Prop → ULift.{1} Prop) at function
  change ULift.{1} Prop at target
  let sourceFunction : Carrier → Carrier := fun value => logicalReading.symm (function (logicalReading value))
  have sourceInjective : Function.Injective sourceFunction := by
    intro first second same
    have imageSame : function (logicalReading first) = function (logicalReading second) :=
      logicalReading.symm.injective same
    apply logicalReading.injective
    apply ULift.down_injective
    apply propext
    apply injective (logicalReading first) (M.prop_mem _) (logicalReading second) (M.prop_mem _)
    change (function (logicalReading first)).down ↔ (function (logicalReading second)).down
    rw [imageSame]
  let : Finite Carrier := finite_carrier
  obtain ⟨sourceValue, same⟩ := Finite.surjective_of_injective sourceInjective (logicalReading.symm target)
  refine ⟨logicalReading sourceValue, M.prop_mem _, ?_⟩
  have imageSame : function (logicalReading sourceValue) = target := logicalReading.symm.injective same
  change (function (logicalReading sourceValue)).down ↔ target.down
  rw [imageSame]

theorem all_models (Result : Type 1) (fact : Fact) : (model Result).models (formula fact) := by
  cases fact with
  | recursion => exact models_recursion Result
  | induction => exact models_induction (model Result)
  | separation => exact models_noConfusion (model Result)
  | cases => exact models_cases (model Result)
  | finite => exact models_finite (model Result)

/-- An explicit admissible choice family suffices to admit the transported
source fold. This states no necessity claim about choice. -/
theorem logicalRecursor_admissible
    (M : Mettapedia.Logic.HOL.HenkinModel.{0, 0, 0} Base Const) (choice : M.HilbertChoice)
    (falseResult trueResult : Mettapedia.Logic.HOL.Ty.denote.{0, 0} M.Carrier result) :
    M.adm (.arr boolean result) (logicalRecursor falseResult trueResult) := by
  have same : logicalRecursor falseResult trueResult =
      HenkinChoice.function M choice falseResult trueResult := by
    funext value
    rcases proposition_cases value with rfl | rfl
    · exact (logicalRecursor_false falseResult trueResult).trans
        (HenkinChoice.function_false M choice falseResult trueResult).symm
    · exact (logicalRecursor_true falseResult trueResult).trans
        (HenkinChoice.function_true M choice falseResult trueResult).symm
  rw [same]
  exact HenkinChoice.function_admissible M choice falseResult trueResult

theorem models_recursion_of_choice
    (M : Mettapedia.Logic.HOL.HenkinModel.{0, 0, 0} Base Const) (choice : M.HilbertChoice) :
    M.models recursion := by
  intro falseResult _ trueResult _
  exact ⟨logicalRecursor falseResult trueResult,
    logicalRecursor_admissible M choice falseResult trueResult,
    logicalRecursor_false falseResult trueResult, logicalRecursor_true falseResult trueResult⟩

theorem all_models_of_choice
    (M : Mettapedia.Logic.HOL.HenkinModel.{0, 0, 0} Base Const) (choice : M.HilbertChoice)
    (fact : Fact) : M.models (formula fact) := by
  cases fact with
  | recursion => exact models_recursion_of_choice M choice
  | induction => exact models_induction M
  | separation => exact models_noConfusion M
  | cases => exact models_cases M
  | finite => exact models_finite M

end NativeMeaning

def interpretation : IndexedInductive.HOLFacts.Interpretation admitted PUnit.unit where
  Carrier := ULift.{1} Bool
  sourceEquiv :=
    { toFun := fun value => ⟨toBool value.2⟩
      invFun := fun value => ⟨(), ofBool value.down⟩
      left_inv := by rintro ⟨⟨⟩, value⟩; simp
      right_inv := by rintro ⟨value⟩; simp }

def selection : IndexedInductive.HOLFacts.Selection interpretation := ⟨none⟩

theorem selected_facts : selection.facts =
    [.structuralRecursion, .structuralInduction, .constructorNoConfusion] := rfl

theorem infinity_not_selected :
    IndexedInductive.HOLFacts.Fact.carrierInfinity ∉ selection.facts := by
  simp [selected_facts]

theorem no_infinity_witness :
    IsEmpty (IndexedInductive.HOLFacts.InfinityWitness interpretation.Carrier) := by
  let : Finite interpretation.Carrier := by
    change Finite (ULift.{1} Bool)
    infer_instance
  constructor
  intro witness
  exact IndexedInductive.HOLFacts.no_infinityWitness_of_finite interpretation.Carrier ⟨witness⟩

#print axioms source_admitted
#print axioms ofBool_toBool
#print axioms constructors_distinct
#print axioms no_infinity_witness
#print axioms logicalRecursor_commutes
#print axioms NativeMeaning.logicalRecursor_admissible
#print axioms NativeMeaning.all_models_of_choice
#print axioms NativeMeaning.all_models

end Mettapedia.GSLT.LanguageDef.IndexedInductiveBooleanHOL
