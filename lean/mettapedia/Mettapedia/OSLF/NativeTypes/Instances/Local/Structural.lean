import Mettapedia.OSLF.NativeTypes.Structural.Execution
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics

open Mettapedia.OSLF.Framework

/-!
# Direct structural evidence in an equation-free presentation

Constructor inspection returns the actual typed introduction, including its
ordered arguments. It does not run successor search or enumerate a term
universe. The completeness theorem applies to every object introduction in
every authored signature, with its free and bound typing contexts retained.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Local.Structural

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Structural

/-- A computational decoder retaining the introduction, rather than just
its constructor label or a boolean membership answer. -/
def inspect (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (declaration : GrammarRule) (term : Pattern) :
    Option {value : ConstructorValue language free bound declaration // value.pattern = term} :=
  match term with
  | .apply label arguments =>
      if checked : label == declaration.label && !usesBareCollection? declaration &&
          checkArgumentsHaveTypes language free bound arguments declaration.params then
        have checks := Bool.and_eq_true_iff.mp checked
        have heads := Bool.and_eq_true_iff.mp checks.1
        have ordinary : ¬ UsesBareCollection declaration := by
          intro bare
          have flag := (usesBareCollection?_eq_true_iff declaration).mpr bare
          simp [flag] at heads
        have typed : ArgumentsHaveTypes language free bound arguments declaration.params :=
          checkArgumentsHaveTypes_sound_of
            (fun _ _ _ accepted => checkHasType_sound accepted) checks.2
        some ⟨.ordinary arguments ordinary typed, by
          simp only [ConstructorValue.pattern]
          exact congrArg (fun head => Pattern.apply head arguments) (beq_iff_eq.mp heads.1).symm⟩
      else none
  | .collection kind elements rest =>
      match shape : declaration.bareParams with
      | [.simple name (.collection declaredKind elementType)] =>
          if accepted : declaredKind = kind then
            if checked : rest.isNone && checkElementsHaveType language free bound elements elementType then
              some ⟨.collection name kind elementType elements rest
                (by simpa only [accepted] using shape)
                (checkElementsHaveType_sound (Bool.and_eq_true_iff.mp checked).2), rfl⟩
            else none
          else none
      | _ => none
  | _ => none

theorem inspect_complete (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (declaration : GrammarRule)
    (value : ConstructorValue language free bound declaration)
    (object : isObjectPattern value.pattern = true) :
    inspect language free bound declaration value.pattern = some ⟨value, rfl⟩ := by
  cases value with
  | ordinary arguments ordinary typed =>
      have bare : usesBareCollection? declaration = false := by
        apply Bool.eq_false_of_not_eq_true
        exact fun accepted => ordinary ((usesBareCollection?_eq_true_iff declaration).mp accepted)
      have checked := checkArgumentsHaveTypes_complete_of_objects typed object
      simp [inspect, ConstructorValue.pattern, bare, checked]
  | collection name kind elementType elements rest shape typed =>
      change (rest.isNone && isObjectPatternList elements) = true at object
      have objects := Bool.and_eq_true_iff.mp object
      have checked := checkElementsHaveType_complete_of_objects typed objects.2
      have bare := (GrammarRule.bareParams_cons_iff _ _ _).mp shape |>.1
      rcases declaration with ⟨label, category, parameters, surfacePattern, policy, algebra, representation⟩
      change representation = .bare at bare
      subst representation
      dsimp only [GrammarRule.bareParams] at shape
      subst parameters
      simp [inspect, ConstructorValue.pattern, GrammarRule.bareParams, objects.1, checked]

/-- Equal introduction terms determine the same ordered input terms, even
when their typing proofs or declaration witnesses were constructed differently. -/
theorem arguments_eq_of_pattern_eq {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {declaration : GrammarRule}
    (first second : ConstructorValue language free bound declaration)
    (same : first.pattern = second.pattern) : first.arguments = second.arguments := by
  cases first <;> cases second <;>
    simp_all [ConstructorValue.pattern, ConstructorValue.arguments]

def decompositions (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (declaration : GrammarRule) (term : Pattern) :
    List (ConstructorValue language free bound declaration) :=
  ((inspect language free bound declaration term).map Subtype.val).toList

theorem decomposition_sound {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {declaration : GrammarRule} {term : Pattern}
    {value : ConstructorValue language free bound declaration}
    (member : value ∈ decompositions language free bound declaration term) :
    value.pattern = term := by
  cases found : inspect language free bound declaration term with
  | none => simp [decompositions, found] at member
  | some result =>
      have same : value = result.val := by simpa [decompositions, found] using member
      exact same ▸ result.property

theorem decomposition_complete {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {declaration : GrammarRule} {term : Pattern}
    (object : isObjectPattern term = true)
    (value : ConstructorValue language free bound declaration) (same : value.pattern = term) :
    value ∈ decompositions language free bound declaration term := by
  subst term
  simp [decompositions, inspect_complete language free bound declaration value object]

theorem decomposition_unique_arguments {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {declaration : GrammarRule} {term : Pattern}
    {first second : ConstructorValue language free bound declaration}
    (left : first ∈ decompositions language free bound declaration term)
    (right : second.pattern = term) : first.arguments = second.arguments :=
  arguments_eq_of_pattern_eq first second ((decomposition_sound left).trans right.symm)

/-- Empty selected equation declarations cannot hide another representative.
This proves the semantic boundary before using singleton decomposition. -/
theorem no_equation_edge {plan : GeneralExecutionAdmission.Plan}
    (empty : plan.equations = []) (bound : List TypeExpr) (carrier : TypeExpr)
    (first second : Pattern) : ¬ GeneralOccurrenceSemantics.Equation plan bound carrier first second := by
  rintro ⟨receipt, completed, _⟩
  have declared := completed.job.1
  rw [empty] at declared
  exact List.not_mem_nil declared

theorem no_equation_iff_eq {plan : GeneralExecutionAdmission.Plan}
    (empty : plan.equations = []) (bound : List TypeExpr) (carrier : TypeExpr)
    (first second : Pattern) :
    Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound carrier) first second ↔ first = second := by
  constructor
  · intro related
    induction related with
    | rel first second edge => exact False.elim (no_equation_edge empty bound carrier first second edge)
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ left right => exact left.trans right
  · rintro rfl
    exact .refl _

theorem local_structural_exact {plan : GeneralExecutionAdmission.Plan}
    (empty : plan.equations = []) (bound : List TypeExpr) (carrier : TypeExpr)
    (former : Former) (term : Pattern) (object : isObjectPattern term = true) :
    checkStructural plan.snapshot.language plan.snapshot.free bound former [term] = true ↔
      StructuralHolds plan.snapshot.language plan.snapshot.free bound
        (Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound carrier)) former term := by
  apply checkStructural_iff
  · intro representative member
    have same := List.mem_singleton.mp member
    subst representative
    exact .refl _
  · intro representative related
    have same := (no_equation_iff_eq empty bound carrier term representative).mp related
    simpa only [same] using List.mem_singleton_self representative
  · intro representative related
    have same := (no_equation_iff_eq empty bound carrier term representative).mp related
    exact same ▸ object

namespace RepresentationControls

def elementRule (label : String) : GrammarRule :=
  { label := label, category := "Item", params := [], syntaxPattern := [] }

def bareRule : GrammarRule :=
  { label := "Bag", category := "Items",
    params := [.simple "items" (.collection .hashBag (.base "Item"))], syntaxPattern := [] }

def wrappedRule : GrammarRule := { bareRule with collectionRepresentation := .wrapped }

def language (rule : GrammarRule) : LanguageDef :=
  { name := "collection-inspection", types := [],
    terms := [elementRule "A", elementRule "B", rule], equations := [], rewrites := [] }

def collection : Pattern := .collection .hashBag [.apply "A" [], .apply "B" []] none

theorem bare_collection_inspected :
    (inspect (language bareRule) FreeTypeContext.empty [] bareRule collection).isSome = true := by
  decide +kernel

theorem wrapped_declaration_refuses_bare_collection :
    inspect (language wrappedRule) FreeTypeContext.empty [] wrappedRule collection = none := by
  decide +kernel

end RepresentationControls

end Mettapedia.OSLF.NativeTypes.Instances.Local.Structural
