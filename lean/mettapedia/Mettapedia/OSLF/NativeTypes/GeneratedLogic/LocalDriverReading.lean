import Mettapedia.OSLF.NativeTypes.GeneratedLogic.DriverBridge
import Mettapedia.OSLF.NativeTypes.Instances.Local.Driver
import Mettapedia.OSLF.Framework.GeneralReferenceAgreement

/-!
# The local driver, read at the front door

The authored local profile turns an admitted language into a runtime driver: its terms are well-sorted patterns, its
steps are the general typed semantics of the language's compiled plan, and its tests are constructor tests
(`Instances.Local.Driver`). On a language whose rules fire at the root, are first-order and are aligned with the
reference relation, this driver is read faithfully in the language's reference structure:

- **Without equations a step is one firing** (`step_iff_firing`), and its target is well sorted
  (`step_target_typed`), so the well-sorted closed terms are a region the driver's steps do not leave.
- **Its steps are the reference steps there** (`rootStep_iff_reference`): a well-sorted closed term is a state
  (`isState_of_typed`), the reference structure steps between states by the reference relation when there are no
  equations (`reference_step_any_iff`), and on such a profile the general typed semantics is the reference relation
  (`FirstOrderProfile.general_step_iff_reference`).
- **Its constructor tests are constructor formulas** (`structural_iff`, `test_iff`): "built by the constructor from
  arguments of its parameters' types", for a represented declaration, whose parameters are simple or abstractions over
  one variable (`RepresentedParam`), since a well-sorted closed object of an arrow type is an abstraction
  (`representedParam_abstraction`).

So the local driver has a faithful reading (`reading`) covering every test a name looks up (`lookup_covered`), and its
decided answers are the truth of closed generated formulas (`Embeddings.decided_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.LocalReading

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement (rootPlan FirstOrderProfile ReadsProvider)

/-! ## Without equations a step is one firing -/

theorem not_equation {plan : Plan} {bound : List TypeExpr} {type : TypeExpr} (empty : plan.equations = [])
    {source target : Pattern} : ¬ GeneralOccurrenceSemantics.Equation plan bound type source target := by
  rintro ⟨receipt, completed, -⟩
  have impossible := completed.job.1
  rw [empty] at impossible
  exact List.not_mem_nil impossible

theorem eq_of_eqvGen_of_empty {α : Type} {r : α → α → Prop} (never : ∀ a b, ¬ r a b) {a b : α}
    (related : Relation.EqvGen r a b) : a = b := by
  induction related with
  | rel a b holds => exact absurd holds (never a b)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **Without equations, a step of the general typed semantics is one valid firing.** -/
theorem step_iff_firing {plan : Plan} {bound : List TypeExpr} {type : TypeExpr} (empty : plan.equations = [])
    {source target : Pattern} :
    (GeneralOccurrenceSemantics.gslt plan bound type).Step source target ↔
      ∃ receipt : GeneralRuleJobs.Receipt, receipt.Valid plan bound type source ∧ receipt.target = target := by
  constructor
  · rintro ⟨representative, receipt, before, valid, after⟩
    have same := eq_of_eqvGen_of_empty (fun _ _ => not_equation empty) before
    have same' := eq_of_eqvGen_of_empty (fun _ _ => not_equation empty) after
    subst same
    exact ⟨receipt, valid, same'⟩
  · rintro ⟨receipt, valid, rfl⟩
    exact ⟨source, receipt, .refl _, valid, .refl _⟩

/-- **The target of a step is well sorted.** -/
theorem step_target_typed {plan : Plan} {bound : List TypeExpr} {type : TypeExpr} (empty : plan.equations = [])
    {source target : Pattern} (step : (GeneralOccurrenceSemantics.gslt plan bound type).Step source target) :
    OpenPatternWellSorted plan.snapshot.language plan.snapshot.free bound type target := by
  obtain ⟨receipt, valid, rfl⟩ := (step_iff_firing empty).mp step
  exact (GeneralPlanEnvironment.typing_iff plan bound type receipt.target).mp valid.2.2.2.2

/-- **A well-sorted closed term is a state.** -/
theorem isState_of_typed {language : LanguageDef} {free : FreeTypeContext} {type : TypeExpr} {pattern : Pattern}
    (typed : OpenPatternWellSorted language free [] type pattern) : IsState pattern :=
  ⟨typed.2.2.2, typed.2.2.1⟩

/-! ## Reference steps without equations -/

/-- **Without equations the reference structure steps between states by the reference relation.** -/
theorem reference_step_any_iff {relEnv : RelationEnv} {language : LanguageDef} (free : language.isEquationFree = true)
    {source target : Pattern} :
    (referenceStructure relEnv language).step source .any target ↔
      IsState source ∧ IsState target ∧ ReferenceStep.Step relEnv language source target := by
  constructor
  · rintro ⟨sourceState, targetState, redex, contractum, witness, toRedex, -, valid, -, toTarget, -⟩
    rw [placed_iff rfl] at toRedex
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at toRedex toTarget
    subst toRedex
    subst toTarget
    exact ⟨sourceState, targetState, witness, valid⟩
  · rintro ⟨sourceState, targetState, witness, valid⟩
    exact ⟨sourceState, targetState, source, target, witness, Relation.EqvGen.refl _, sourceState, valid, targetState,
      Relation.EqvGen.refl _, rfl⟩

/-! ## The root plan's steps are the reference steps on well-sorted closed terms -/

variable {language : LanguageDef} {provider : GeneralPremise.ProviderSnapshot}

/-- **On an aligned first-order profile, at a well-sorted closed term, the reference structure's steps are the
general typed semantics' steps.** -/
theorem rootStep_iff_reference (profile : FirstOrderProfile language provider)
    (aligned : ReferenceStep.ReferenceProfile language) (relEnv : RelationEnv) (reads : ReadsProvider relEnv provider)
    (expected : TypeExpr) {source target : Pattern}
    (typed : OpenPatternWellSorted (rootPlan language provider).snapshot.language
      (rootPlan language provider).snapshot.free [] expected source) :
    (referenceStructure relEnv language).step source .any target ↔
      (GeneralOccurrenceSemantics.gslt (rootPlan language provider) [] expected).Step source target := by
  rw [reference_step_any_iff profile.equationFree]
  constructor
  · rintro ⟨-, -, step⟩
    exact (profile.general_step_iff_reference aligned relEnv reads [] expected typed).mpr step
  · intro step
    exact ⟨isState_of_typed typed, isState_of_typed (step_target_typed profile.equations step),
      (profile.general_step_iff_reference aligned relEnv reads [] expected typed).mp step⟩

/-! ## Constructor tests as formulas -/

/-- The formulas of a declaration's parameters: each parameter's type. -/
def paramFormulas : List TermParam → Formulas 0
  | [] => .nil
  | param :: params =>
    .cons (match parameterType? param with | some type => .typed type | none => .bot) (paramFormulas params)

/-- **A constructor test as a formula**: built by the declaration's constructor from arguments of its parameters'
types. -/
def constructorFormula (rule : GrammarRule) : Formula 0 := .built rule.label (paramFormulas rule.params)

/-- Arguments the reference structure types at the parameters' types. -/
inductive ArgumentsTyped (language : LanguageDef) : List TermParam → List Pattern → Prop
  | nil : ArgumentsTyped language [] []
  | cons {param : TermParam} {params : List TermParam} {argument : Pattern} {arguments : List Pattern}
      {type : TypeExpr} : parameterType? param = some type → IsObject argument →
      OpenPatternWellSorted language FreeTypeContext.empty [] type argument →
      ArgumentsTyped language params arguments → ArgumentsTyped language (param :: params) (argument :: arguments)

variable {relEnv : RelationEnv}

theorem sat_typed_iff (free : language.isEquationFree = true)
    (carriers : CarrierTyping.NoBuiltinCarriers language = true) {type : TypeExpr} {term : Pattern} :
    (referenceStructure relEnv language).sat Env.closed (.typed type) term ↔
      IsObject term ∧ OpenPatternWellSorted language FreeTypeContext.empty [] type term := by
  show (IsObject term ∧ ∃ representative, ObjectEquivalent relEnv language .syntax term representative ∧
    CarrierTyped language type representative) ↔ _
  simp only [carrierTyped_iff_wellSorted carriers]
  constructor
  · rintro ⟨object, representative, equivalent, typed⟩
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at equivalent
    subst equivalent
    exact ⟨object, typed⟩
  · rintro ⟨object, typed⟩
    exact ⟨object, term, Relation.EqvGen.refl _, typed⟩

theorem satAll_paramFormulas_iff (free : language.isEquationFree = true)
    (carriers : CarrierTyping.NoBuiltinCarriers language = true) :
    ∀ (params : List TermParam) (parts : List Pattern),
      (referenceStructure relEnv language).satAll Env.closed (paramFormulas params) parts ↔
        ArgumentsTyped language params parts
  | [], [] => iff_of_true trivial .nil
  | [], _ :: _ => iff_of_false id (fun typed => nomatch typed)
  | _ :: _, [] => iff_of_false id (fun typed => nomatch typed)
  | param :: params, part :: parts => by
    have rest := satAll_paramFormulas_iff free carriers params parts
    show ((referenceStructure relEnv language).sat Env.closed
      (match parameterType? param with | some type => .typed type | none => .bot) part ∧
        (referenceStructure relEnv language).satAll Env.closed (paramFormulas params) parts) ↔ _
    cases found : parameterType? param with
    | none =>
      refine iff_of_false (fun held => held.1) ?_
      intro typed
      cases typed with
      | cons known _ _ _ => rw [found] at known; cases known
    | some type =>
      rw [sat_typed_iff free carriers, rest]
      constructor
      · rintro ⟨⟨object, wellSorted⟩, others⟩
        exact .cons found object wellSorted others
      · intro typed
        cases typed with
        | cons known object wellSorted others =>
          rw [found] at known
          cases known
          exact ⟨⟨object, wellSorted⟩, others⟩

/-- **The constructor formula holds at an object term built by the constructor from typed arguments.** -/
theorem sat_constructorFormula_iff (free : language.isEquationFree = true)
    (carriers : CarrierTyping.NoBuiltinCarriers language = true) (rule : GrammarRule) (term : Pattern) :
    (referenceStructure relEnv language).sat Env.closed (constructorFormula rule) term ↔
      IsObject term ∧ ∃ parts, term = .apply rule.label parts ∧ ArgumentsTyped language rule.params parts := by
  show (∃ parts, (IsObject term ∧ ObjectEquivalent relEnv language .syntax term (.apply rule.label parts)) ∧
    (referenceStructure relEnv language).satAll Env.closed (paramFormulas rule.params) parts) ↔ _
  constructor
  · rintro ⟨parts, ⟨object, equivalent⟩, arguments⟩
    rw [objectEquivalent_iff_eq_of_isEquationFree free] at equivalent
    exact ⟨object, parts, equivalent, (satAll_paramFormulas_iff free carriers _ _).mp arguments⟩
  · rintro ⟨object, parts, rfl, arguments⟩
    exact ⟨parts, ⟨object, Relation.EqvGen.refl _⟩, (satAll_paramFormulas_iff free carriers _ _).mpr arguments⟩

/-- Typed arguments of a well-sorted closed term are typed by the reference structure. -/
theorem argumentsTyped_of_typed : ∀ {parts : List Pattern} {params : List TermParam},
    ArgumentsHaveTypes language FreeTypeContext.empty [] parts params →
    isObjectPatternList parts = true → Pattern.hasCanonicalBinderMetadataList parts = true →
    Pattern.isWellScopedListAt 0 parts = true → ArgumentsTyped language params parts
  | [], [], _, _, _, _ => .nil
  | [], _ :: _, typed, _, _, _ => by cases typed
  | _ :: _, [], typed, _, _, _ => by cases typed
  | _ :: _, _ :: _, typed, objects, metadata, inScope => by
    cases typed with
    | cons _ expectedType argumentTyped rest =>
      simp only [isObjectPatternList, Pattern.hasCanonicalBinderMetadataList, Pattern.isWellScopedListAt,
        Bool.and_eq_true] at objects metadata inScope
      exact .cons expectedType objects.1 ⟨argumentTyped, metadata.1, objects.1, inScope.1⟩
        (argumentsTyped_of_typed rest objects.2 metadata.2 inScope.2)

/-- **A represented parameter**: its parameter type is its declared type, and a well-sorted closed object of that type
has the parameter's representation. Simple parameters are represented, and so are abstractions over one variable. -/
def RepresentedParam (param : TermParam) : Prop :=
  parameterType? param = some param.typeExpr ∧
    ∀ (language : LanguageDef) (argument : Pattern),
      OpenPatternWellSorted language FreeTypeContext.empty [] param.typeExpr argument →
        MatchesParameterRepresentation param argument

theorem representedParam_simple (name : String) (type : TypeExpr) : RepresentedParam (.simple name type) :=
  ⟨rfl, fun _ _ _ => trivial⟩

/-- **An abstraction over one variable is represented**: a well-sorted closed object of an arrow type whose domain is
no multi-binder is an abstraction, and its binder carries no name. -/
theorem representedParam_abstraction (binder : Option String) (body : String) (domain codomain : TypeExpr)
    (single : ∀ inner, domain ≠ .multiBinder inner) :
    RepresentedParam (.abstractionNamed binder body (.arrow domain codomain)) := by
  refine ⟨rfl, fun language argument typed => ?_⟩
  have objects := typed.2.2.1
  have metadata := typed.2.1
  cases argument with
  | bvar index =>
    cases typed.1 with
    | bvar found => simp at found
  | fvar name =>
    cases typed.1 with
    | fvar found => cases found
  | apply label parts => cases typed.1
  | lambda name inner =>
    simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true, Option.isNone_iff_eq_none] at metadata
    rw [metadata.1]
    trivial
  | multiLambda arity names inner =>
    cases typed.1 with
    | multiLambda _ => exact absurd rfl (single _)
  | subst inner replacement => simp [isObjectPattern] at objects
  | collection kind elements rest => cases typed.1

/-- Arguments typed by the reference structure at represented parameters are typed arguments. -/
theorem typed_of_argumentsTyped {parts : List Pattern} {params : List TermParam}
    (represented : ∀ param ∈ params, RepresentedParam param)
    (arguments : ArgumentsTyped language params parts) :
    ArgumentsHaveTypes language FreeTypeContext.empty [] parts params := by
  induction arguments with
  | nil => exact .nil
  | @cons param params argument arguments type found _ wellSorted _ ih =>
    have this := represented param List.mem_cons_self
    rw [this.1, Option.some.injEq] at found
    subst found
    exact .cons (this.2 _ _ wellSorted) this.1 wellSorted.1
      (ih fun other member => represented other (List.mem_cons_of_mem _ member))

/-- **Each typed argument at a represented parameter**: an object of the parameter's declared type. -/
theorem ArgumentsTyped.get {params : List TermParam} {parts : List Pattern}
    (represented : ∀ param ∈ params, RepresentedParam param)
    (arguments : ArgumentsTyped language params parts) :
    ∀ (index : ℕ) (inParams : index < params.length) (inParts : index < parts.length),
      OpenPatternWellSorted language FreeTypeContext.empty [] params[index].typeExpr parts[index] := by
  induction arguments with
  | nil => intro index inParams; exact absurd inParams (Nat.not_lt_zero _)
  | @cons param params argument arguments type found object wellSorted _ ih =>
    intro index inParams inParts
    cases index with
    | zero =>
      rw [(represented param List.mem_cons_self).1, Option.some.injEq] at found
      subst found
      exact wellSorted
    | succ index =>
      exact ih (fun other member => represented other (List.mem_cons_of_mem _ member)) index
        (Nat.lt_of_succ_lt_succ inParams) (Nat.lt_of_succ_lt_succ inParts)

/-! ## The local driver's tests -/

open Mettapedia.OSLF.NativeTypes.Generation (Generated structuralDeclaration)
open Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated (booleanModel booleanInputs booleanCode)

/-- **A represented declaration**: its parameters are represented, and it is no bare collection. -/
def RepresentedDeclaration (rule : GrammarRule) : Prop :=
  (∀ param ∈ rule.params, RepresentedParam param) ∧ ¬ UsesBareCollection rule

/-- **The sort mask admits every well-sorted closed term** at the sorts the declarations use. -/
structure MaskAdmits (generated : Generated)
    (mask : List TypeExpr → TypeExpr → Mettapedia.OSLF.Framework.ModalHypercube.HSort → Pattern → Bool) : Prop where
  output : ∀ index source, OpenPatternWellSorted generated.snapshot.language generated.snapshot.free []
    (.base (structuralDeclaration generated index).category) source →
      mask [] (.base (structuralDeclaration generated index).category)
        (Mettapedia.OSLF.NativeTypes.Generation.structuralOutputSort generated index) source = true
  input : ∀ index position source, OpenPatternWellSorted generated.snapshot.language generated.snapshot.free []
    (structuralDeclaration generated index).params[position].typeExpr source →
      mask [] (structuralDeclaration generated index).params[position].typeExpr
        (Mettapedia.OSLF.NativeTypes.Generation.structuralInputSort generated index position) source = true

/-- **The sort mask admits well-sorted closed terms at one declaration.** -/
structure MaskAdmitsAt (generated : Generated)
    (mask : List TypeExpr → TypeExpr → Mettapedia.OSLF.Framework.ModalHypercube.HSort → Pattern → Bool)
    (index : Fin generated.snapshot.language.terms.length) : Prop where
  output : ∀ source, OpenPatternWellSorted generated.snapshot.language generated.snapshot.free []
    (.base (structuralDeclaration generated index).category) source →
      mask [] (.base (structuralDeclaration generated index).category)
        (Mettapedia.OSLF.NativeTypes.Generation.structuralOutputSort generated index) source = true
  input : ∀ position source, OpenPatternWellSorted generated.snapshot.language generated.snapshot.free []
    (structuralDeclaration generated index).params[position].typeExpr source →
      mask [] (structuralDeclaration generated index).params[position].typeExpr
        (Mettapedia.OSLF.NativeTypes.Generation.structuralInputSort generated index position) source = true

theorem MaskAdmits.at {generated : Generated}
    {mask : List TypeExpr → TypeExpr → Mettapedia.OSLF.Framework.ModalHypercube.HSort → Pattern → Bool}
    (admits : MaskAdmits generated mask) (index : Fin generated.snapshot.language.terms.length) :
    MaskAdmitsAt generated mask index :=
  ⟨admits.output index, admits.input index⟩

/-- Typing reads only a language's declarations. -/
theorem openPatternWellSorted_of_terms {source target : LanguageDef} (same : source.terms = target.terms)
    {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr} {pattern : Pattern}
    (typed : OpenPatternWellSorted source free bound type pattern) : OpenPatternWellSorted target free bound type pattern :=
  ⟨HasType.of_terms_subset (fun _ member => same ▸ member) typed.1, typed.2⟩

/-- **A constructor code is its constructor formula**, at well-sorted closed terms of the declaration's category, for
a represented declaration and an acceptor accepting everything, when the sort mask admits well-sorted closed terms. -/
theorem structural_iff (generated : Generated) (equationFree : generated.plan.equations = [])
    (mask : List TypeExpr → TypeExpr → Mettapedia.OSLF.Framework.ModalHypercube.HSort → Pattern → Bool)
    (sameTerms : generated.snapshot.language.terms = language.terms)
    (sameFree : generated.snapshot.free = FreeTypeContext.empty) (free : language.isEquationFree = true)
    (carriers : CarrierTyping.NoBuiltinCarriers language = true)
    (index : Fin generated.snapshot.language.terms.length) (admits : MaskAdmitsAt generated mask index)
    (accepts : Fin (structuralDeclaration generated index).params.length → Pattern → Bool)
    (acceptsAll : ∀ position pattern, accepts position pattern = true)
    (represented : RepresentedDeclaration (structuralDeclaration generated index)) {source : Pattern}
    (typed : OpenPatternWellSorted generated.snapshot.language generated.snapshot.free []
      (.base (structuralDeclaration generated index).category) source) :
    (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode (booleanModel generated mask []) index
        (booleanInputs generated [] index accepts)).meaning source ↔
      (referenceStructure relEnv language).sat Env.closed
        (constructorFormula (structuralDeclaration generated index)) source := by
  rw [Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structural_image_exact,
    sat_constructorFormula_iff free carriers]
  have hasType : HasType generated.snapshot.language generated.snapshot.free [] source
      (.base (structuralDeclaration generated index).category) := typed.1
  constructor
  · rintro ⟨-, -, value, related, -⟩
    have same := eq_of_eqvGen_of_empty (fun _ _ => not_equation equationFree) related
    cases value with
    | ordinary arguments ordinary typedArguments =>
      have objects := typed.2.2.1
      have metadata := typed.2.1
      have inScope : source.isWellScopedAt 0 = true := typed.2.2.2
      change source = .apply _ arguments at same
      rw [same] at objects metadata inScope
      simp only [isObjectPattern, Pattern.hasCanonicalBinderMetadata, Pattern.isWellScopedAt] at objects metadata inScope
      refine ⟨same ▸ typed.2.2.1, arguments, same, argumentsTyped_of_typed ?_ objects metadata inScope⟩
      rw [← sameFree]
      exact ArgumentsHaveTypes.of_terms_subset (fun _ member => sameTerms ▸ member) typedArguments
    | collection name kind elementType elements rest shape _ =>
      exact absurd ⟨name, kind, elementType, shape⟩ represented.2
  · rintro ⟨object, parts, rfl, arguments⟩
    have typedArguments : ArgumentsHaveTypes generated.snapshot.language generated.snapshot.free [] parts
        (structuralDeclaration generated index).params := by
      rw [sameFree]
      exact ArgumentsHaveTypes.of_terms_subset (fun _ member => sameTerms ▸ member)
        (typed_of_argumentsTyped represented.1 arguments)
    have outputTyped : OpenPatternWellSorted generated.snapshot.language generated.snapshot.free []
        (.base (structuralDeclaration generated index).category)
        (.apply (structuralDeclaration generated index).label parts) := typed
    refine ⟨⟨checkHasType_complete_of_object hasType typed.2.2.1, admits.output _ outputTyped⟩, hasType,
      .ordinary parts represented.2 typedArguments, Relation.EqvGen.refl _, fun position => ?_⟩
    have inParts : position.val < parts.length := by
      rw [typedArguments.length_eq]
      exact position.isLt
    have partTyped : OpenPatternWellSorted generated.snapshot.language generated.snapshot.free []
        (structuralDeclaration generated index).params[position].typeExpr parts[position.val] := by
      rw [sameFree]
      exact openPatternWellSorted_of_terms sameTerms.symm (arguments.get represented.1 position.val position.isLt inParts)
    have checked : checkHasType generated.snapshot.language generated.snapshot.free [] parts[position.val]
        (structuralDeclaration generated index).params[position].typeExpr = true :=
      checkHasType_complete_of_object partTyped.1 partTyped.2.2.1
    exact ⟨⟨checked, admits.input _ _ partTyped⟩, checked, acceptsAll _ _⟩

theorem isObjectPatternList_get : ∀ {parts : List Pattern}, isObjectPatternList parts = true →
    ∀ (slot : ℕ) (inParts : slot < parts.length), isObjectPattern parts[slot] = true
  | [], _, _, inParts => absurd inParts (Nat.not_lt_zero _)
  | _ :: _, objects, 0, _ => by
    simp only [isObjectPatternList, Bool.and_eq_true] at objects
    exact objects.1
  | _ :: rest, objects, slot + 1, inParts => by
    simp only [isObjectPatternList, Bool.and_eq_true] at objects
    exact isObjectPatternList_get (parts := rest) objects.2 slot (Nat.lt_of_succ_lt_succ inParts)

theorem hasCanonicalBinderMetadataList_get : ∀ {parts : List Pattern},
    Pattern.hasCanonicalBinderMetadataList parts = true →
      ∀ (slot : ℕ) (inParts : slot < parts.length), parts[slot].hasCanonicalBinderMetadata = true
  | [], _, _, inParts => absurd inParts (Nat.not_lt_zero _)
  | _ :: _, metadata, 0, _ => by
    simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at metadata
    exact metadata.1
  | _ :: rest, metadata, slot + 1, inParts => by
    simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at metadata
    exact hasCanonicalBinderMetadataList_get (parts := rest) metadata.2 slot (Nat.lt_of_succ_lt_succ inParts)

theorem isWellScopedListAt_get {depth : ℕ} : ∀ {parts : List Pattern}, Pattern.isWellScopedListAt depth parts = true →
    ∀ (slot : ℕ) (inParts : slot < parts.length), parts[slot].isWellScopedAt depth = true
  | [], _, _, inParts => absurd inParts (Nat.not_lt_zero _)
  | _ :: _, inScope, 0, _ => by
    simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at inScope
    exact inScope.1
  | _ :: rest, inScope, slot + 1, inParts => by
    simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at inScope
    exact isWellScopedListAt_get (parts := rest) inScope.2 slot (Nat.lt_of_succ_lt_succ inParts)

/-- **A refused output sort empties a constructor code** at well-sorted closed terms of the declaration's category. -/
theorem structural_refused_output (generated : Generated)
    (mask : List TypeExpr → TypeExpr → Mettapedia.OSLF.Framework.ModalHypercube.HSort → Pattern → Bool)
    (index : Fin generated.snapshot.language.terms.length)
    (accepts : Fin (structuralDeclaration generated index).params.length → Pattern → Bool)
    (refuses : ∀ source, OpenPatternWellSorted generated.snapshot.language generated.snapshot.free []
      (.base (structuralDeclaration generated index).category) source →
        mask [] (.base (structuralDeclaration generated index).category)
          (Mettapedia.OSLF.NativeTypes.Generation.structuralOutputSort generated index) source = false)
    {source : Pattern} (typed : OpenPatternWellSorted generated.snapshot.language generated.snapshot.free []
      (.base (structuralDeclaration generated index).category) source) :
    ¬ (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode (booleanModel generated mask []) index
        (booleanInputs generated [] index accepts)).meaning source := by
  rw [Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structural_image_exact]
  rintro ⟨⟨-, admitted⟩, -⟩
  rw [refuses source typed] at admitted
  cases admitted

/-- **A refused input sort empties a constructor code** at well-sorted closed terms of the declaration's category, for a
declaration that is no bare collection. -/
theorem structural_refused_input (generated : Generated) (equationFree : generated.plan.equations = [])
    (mask : List TypeExpr → TypeExpr → Mettapedia.OSLF.Framework.ModalHypercube.HSort → Pattern → Bool)
    (index : Fin generated.snapshot.language.terms.length)
    (accepts : Fin (structuralDeclaration generated index).params.length → Pattern → Bool)
    (notBare : ¬ UsesBareCollection (structuralDeclaration generated index))
    (position : Fin (structuralDeclaration generated index).params.length)
    (refuses : ∀ part, OpenPatternWellSorted generated.snapshot.language generated.snapshot.free []
      (structuralDeclaration generated index).params[position].typeExpr part →
        mask [] (structuralDeclaration generated index).params[position].typeExpr
          (Mettapedia.OSLF.NativeTypes.Generation.structuralInputSort generated index position) part = false)
    {source : Pattern} (typed : OpenPatternWellSorted generated.snapshot.language generated.snapshot.free []
      (.base (structuralDeclaration generated index).category) source) :
    ¬ (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode (booleanModel generated mask []) index
        (booleanInputs generated [] index accepts)).meaning source := by
  rw [Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structural_image_exact]
  rintro ⟨-, -, value, related, inputs⟩
  have same := eq_of_eqvGen_of_empty (fun _ _ => not_equation equationFree) related
  cases value with
  | ordinary arguments ordinary typedArguments =>
    have objects := typed.2.2.1
    have metadata := typed.2.1
    have inScope : source.isWellScopedAt 0 = true := typed.2.2.2
    change source = .apply _ arguments at same
    rw [same] at objects metadata inScope
    simp only [isObjectPattern, Pattern.hasCanonicalBinderMetadata, Pattern.isWellScopedAt] at objects metadata inScope
    have inParts : position.val < arguments.length := by
      rw [typedArguments.length_eq]
      exact position.isLt
    obtain ⟨⟨checked, admitted⟩, -⟩ := inputs position
    have partTyped : OpenPatternWellSorted generated.snapshot.language generated.snapshot.free []
        (structuralDeclaration generated index).params[position].typeExpr arguments[position.val] :=
      ⟨checkHasType_sound checked, hasCanonicalBinderMetadataList_get metadata _ inParts,
        isObjectPatternList_get objects _ inParts, isWellScopedListAt_get inScope _ inParts⟩
    have admittedHere : mask [] (structuralDeclaration generated index).params[position].typeExpr
        (Mettapedia.OSLF.NativeTypes.Generation.structuralInputSort generated index position)
          arguments[position.val] = true := admitted
    rw [refuses _ partTyped] at admittedHere
    cases admittedHere
  | collection name kind elementType elements rest shape _ =>
    exact notBare ⟨name, kind, elementType, shape⟩

/-- **A constructor test of the local driver is its constructor formula**, at well-sorted closed terms, for a
represented declaration and an acceptor accepting everything, when the sort mask admits well-sorted closed terms. -/
theorem test_iff (generated : Generated) (expected : TypeExpr) (equationFree : generated.plan.equations = [])
    (mask : List TypeExpr → TypeExpr → Mettapedia.OSLF.Framework.ModalHypercube.HSort → Pattern → Bool)
    (admits : MaskAdmits generated mask)
    (sameTerms : generated.snapshot.language.terms = language.terms)
    (sameFree : generated.snapshot.free = FreeTypeContext.empty) (free : language.isEquationFree = true)
    (carriers : CarrierTyping.NoBuiltinCarriers language = true)
    (leaf : Mettapedia.OSLF.NativeTypes.Instances.Local.Driver.Leaf generated expected)
    (accepts : ∀ position pattern, leaf.accepts position pattern = true)
    (represented : RepresentedDeclaration (structuralDeclaration generated leaf.index)) {source : Pattern}
    (typed : OpenPatternWellSorted generated.snapshot.language generated.snapshot.free [] expected source) :
    (Mettapedia.OSLF.NativeTypes.Instances.Local.Driver.tests generated [] expected equationFree mask leaf).predicate.1
        source ↔
      (referenceStructure relEnv language).sat Env.closed
        (constructorFormula (structuralDeclaration generated leaf.index)) source :=
  (Mettapedia.OSLF.NativeTypes.Instances.Local.Driver.native_structural_meaning generated [] expected
    equationFree mask leaf source).trans
    (structural_iff generated equationFree mask sameTerms sameFree free carriers leaf.index (admits.at leaf.index) leaf.accepts accepts
      represented (by rw [leaf.carrier]; exact typed))

/-! ## The reading -/

theorem forwardList_paramFormulas : ∀ params : List TermParam, Formula.forwardList (paramFormulas params) = true
  | [] => rfl
  | param :: params => by
    cases found : parameterType? param <;>
      simp [paramFormulas, found, Formula.forward, Formula.forwardList, forwardList_paramFormulas params]

theorem forward_constructorFormula (rule : GrammarRule) : (constructorFormula rule).forward = true := by
  simp only [constructorFormula, Formula.forward, forwardList_paramFormulas]

/-- **The variable of a test at a polarity**, among `n` tests: one pair of variables per test. -/
def pairVariable {n : ℕ} (index : Fin n) (polarity : Bool) : Fin (2 * n) :=
  ⟨2 * index.val + (if polarity then 0 else 1), by
    cases polarity <;> (simp only [if_true, Bool.false_eq_true, if_false]; omega)⟩

/-- **The closing formulas of `n` test formulas**: each test's formula at its positive variable, and its dual at its
negative one. -/
def pairClosing {n : ℕ} (formulaOf : Fin n → Formula 0) (slot : Fin (2 * n)) : Formula 0 :=
  if slot.val % 2 = 0 then formulaOf ⟨slot.val / 2, by omega⟩ else (formulaOf ⟨slot.val / 2, by omega⟩).dual

theorem pairClosing_positive {n : ℕ} (formulaOf : Fin n → Formula 0) (index : Fin n) :
    pairClosing formulaOf (pairVariable index true) = formulaOf index := by
  have parity : (2 * index.val + 0) % 2 = 0 := by omega
  simp only [pairClosing, pairVariable, if_true, parity]
  congr 2
  omega

theorem pairClosing_negative {n : ℕ} (formulaOf : Fin n → Formula 0) (index : Fin n) :
    pairClosing formulaOf (pairVariable index false) = (formulaOf index).dual := by
  have half : (2 * index.val + 1) / 2 = index.val := by omega
  have parity : (2 * index.val + 1) % 2 = 1 := by omega
  simp only [pairClosing, pairVariable, Bool.false_eq_true, if_false, parity, one_ne_zero, if_false]
  congr 2
  exact Fin.ext half

theorem pairClosing_forward {n : ℕ} (formulaOf : Fin n → Formula 0) (forward : ∀ index, (formulaOf index).forward = true)
    (slot : Fin (2 * n)) : (pairClosing formulaOf slot).forward = true := by
  unfold pairClosing
  split_ifs
  · exact forward _
  · rw [Formula.forward_dual]
    exact forward _

/-- The variable of a constructor test, at a polarity: one pair of variables per declaration. -/
def testVariable (generated : Generated) (index : Fin generated.snapshot.language.terms.length) (polarity : Bool) :
    Fin (2 * generated.snapshot.language.terms.length) :=
  pairVariable index polarity

/-- **The closing formulas of test formulas**: each declaration's test formula at its positive variable, and its dual at
its negative one. -/
def closingOf (generated : Generated) (formulaOf : Fin generated.snapshot.language.terms.length → Formula 0) :
    Fin (2 * generated.snapshot.language.terms.length) → Formula 0 :=
  pairClosing formulaOf

theorem closingOf_positive (generated : Generated) (formulaOf : Fin generated.snapshot.language.terms.length → Formula 0)
    (index : Fin generated.snapshot.language.terms.length) :
    closingOf generated formulaOf (testVariable generated index true) = formulaOf index :=
  pairClosing_positive formulaOf index

theorem closingOf_negative (generated : Generated) (formulaOf : Fin generated.snapshot.language.terms.length → Formula 0)
    (index : Fin generated.snapshot.language.terms.length) :
    closingOf generated formulaOf (testVariable generated index false) = (formulaOf index).dual :=
  pairClosing_negative formulaOf index

theorem closingOf_forward (generated : Generated) (formulaOf : Fin generated.snapshot.language.terms.length → Formula 0)
    (forward : ∀ index, (formulaOf index).forward = true) (slot : Fin (2 * generated.snapshot.language.terms.length)) :
    (closingOf generated formulaOf slot).forward = true :=
  pairClosing_forward formulaOf forward slot

/-- **The closing formulas of constructor tests**: each declaration's constructor formula at its positive variable, and
its dual at its negative one. -/
def closing (generated : Generated) : Fin (2 * generated.snapshot.language.terms.length) → Formula 0 :=
  closingOf generated fun index => constructorFormula (structuralDeclaration generated index)

theorem closing_positive (generated : Generated) (index : Fin generated.snapshot.language.terms.length) :
    closing generated (testVariable generated index true) = constructorFormula (structuralDeclaration generated index) :=
  closingOf_positive generated _ index

theorem closing_negative (generated : Generated) (index : Fin generated.snapshot.language.terms.length) :
    closing generated (testVariable generated index false) =
      (constructorFormula (structuralDeclaration generated index)).dual :=
  closingOf_negative generated _ index

theorem closing_forward (generated : Generated) (slot : Fin (2 * generated.snapshot.language.terms.length)) :
    (closing generated slot).forward = true :=
  closingOf_forward generated _ (fun _ => forward_constructorFormula _) slot

open Mettapedia.OSLF.NativeTypes.Instances.Local.Driver (driver Leaf)
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionTotalAdmission (checkGeneric)

theorem snapshot_language_of_plan {generated : Generated} (samePlan : generated.plan = rootPlan language provider) :
    generated.snapshot.language = language :=
  congrArg (fun plan : Plan => plan.snapshot.language) samePlan

theorem snapshot_free_of_plan {generated : Generated} (samePlan : generated.plan = rootPlan language provider) :
    generated.snapshot.free = FreeTypeContext.empty := by
  have same := congrArg (fun plan : Plan => plan.snapshot.free) samePlan
  refine same.trans ?_
  funext name
  rfl

/-- **The local driver's faithful reading in the reference structure**, for a language whose rules fire at the root,
are first-order and are aligned with the reference relation, with a sort mask admitting well-sorted closed terms: on
its well-sorted
closed terms its steps are the reference steps, and its constructor tests for represented declarations with
everything accepted are constructor formulas. -/
def reading (profile : FirstOrderProfile language provider) (aligned : ReferenceStep.ReferenceProfile language)
    (relEnv : RelationEnv) (reads : ReadsProvider relEnv provider) (generated : Generated)
    (samePlan : generated.plan = rootPlan language provider) (expected : TypeExpr)
    (foundation : generated.plan.complete = true) (equationFree : generated.plan.equations = [])
    (generic : checkGeneric generated.plan = true)
    (mask : List TypeExpr → TypeExpr → Mettapedia.OSLF.Framework.ModalHypercube.HSort → Pattern → Bool)
    (admits : MaskAdmits generated mask) (carriers : CarrierTyping.NoBuiltinCarriers language = true) :
    Embeddings.Faithful (driver generated [] expected foundation equationFree generic mask) relEnv language
      (fun leaf : Leaf generated expected => testVariable generated leaf.index true)
      (fun leaf : Leaf generated expected => testVariable generated leaf.index false) where
  structure_ := referenceStructure relEnv language
  region := Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.Source generated.plan [] expected
  steps := by
    intro source inside target
    show _ ↔ (GeneralOccurrenceSemantics.gslt generated.plan [] expected).Step source target
    have typed : OpenPatternWellSorted (rootPlan language provider).snapshot.language
        (rootPlan language provider).snapshot.free [] expected source := by
      have inside' : OpenPatternWellSorted generated.plan.snapshot.language generated.plan.snapshot.free [] expected
          source := inside
      rw [samePlan] at inside'
      exact inside'
    rw [samePlan]
    exact rootStep_iff_reference profile aligned relEnv reads expected typed
  closed := fun _ _ _ step => step_target_typed equationFree step
  rendering := (BoundedMorphism.identity _).toSplit
  renders := rfl
  covers leaf := (∀ position pattern, leaf.accepts position pattern = true) ∧
    RepresentedDeclaration (structuralDeclaration generated leaf.index)
  test leaf := constructorFormula (structuralDeclaration generated leaf.index)
  testAgrees leaf covered source inside :=
    test_iff generated expected equationFree mask admits (congrArg LanguageDef.terms (snapshot_language_of_plan samePlan))
      (snapshot_free_of_plan samePlan) profile.equationFree carriers leaf covered.1 covered.2 inside
  closing := closing generated
  closesPositive leaf := closing_positive generated leaf.index
  closesNegative leaf := closing_negative generated leaf.index
  closingForward := closing_forward generated

/-! ## Queries through the reading -/

/-- **A represented parameter, checked**: simple, or an abstraction over one variable. -/
def isRepresentedParam : TermParam → Bool
  | .simple _ _ => true
  | .abstractionNamed _ _ (.arrow (.multiBinder _) _) => false
  | .abstractionNamed _ _ (.arrow _ _) => true
  | _ => false

theorem representedParam_of_check : ∀ {param : TermParam}, isRepresentedParam param = true → RepresentedParam param
  | .simple name type, _ => representedParam_simple name type
  | .abstractionNamed binder body (.arrow domain codomain), checked => by
    refine representedParam_abstraction binder body domain codomain fun inner same => ?_
    subst same
    simp [isRepresentedParam] at checked

/-- **A represented declaration, checked.** -/
def isRepresentedDeclaration (rule : GrammarRule) : Bool :=
  rule.params.all isRepresentedParam &&
    !(match rule.bareParams with | [.simple _ (.collection _ _)] => true | _ => false)

theorem representedDeclaration_of_check {rule : GrammarRule} (checked : isRepresentedDeclaration rule = true) :
    RepresentedDeclaration rule := by
  simp only [isRepresentedDeclaration, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at checked
  refine ⟨fun param member => representedParam_of_check (checked.1 param member), ?_⟩
  rintro ⟨name, kind, element, shape⟩
  rw [shape] at checked
  exact absurd checked.2 (by simp)

/-- The local driver looks up only tests accepting everything. -/
theorem lookup_accepts {generated : Generated} {expected : TypeExpr} {label : String} {leaf : Leaf generated expected}
    (found : Mettapedia.OSLF.NativeTypes.Instances.Local.Driver.lookup generated expected label = some leaf) :
    ∀ position pattern, leaf.accepts position pattern = true := by
  have member := List.mem_of_find?_eq_some found
  simp only [Mettapedia.OSLF.NativeTypes.Instances.Local.Driver.leaves, List.mem_filterMap, List.mem_finRange,
    true_and] at member
  obtain ⟨index, built⟩ := member
  split_ifs at built with carrier
  cases built
  intro _ _
  rfl

/-- **Every test a name looks up is covered by the reading**, when every declaration is first-order. -/
theorem lookup_covered (profile : FirstOrderProfile language provider) (aligned : ReferenceStep.ReferenceProfile language)
    (relEnv : RelationEnv) (reads : ReadsProvider relEnv provider) (generated : Generated)
    (samePlan : generated.plan = rootPlan language provider) (expected : TypeExpr)
    (foundation : generated.plan.complete = true) (equationFree : generated.plan.equations = [])
    (generic : checkGeneric generated.plan = true)
    (mask : List TypeExpr → TypeExpr → Mettapedia.OSLF.Framework.ModalHypercube.HSort → Pattern → Bool)
    (admits : MaskAdmits generated mask) (carriers : CarrierTyping.NoBuiltinCarriers language = true)
    (represented : ∀ index, RepresentedDeclaration (structuralDeclaration generated index)) :
    ∀ name leaf, (driver generated [] expected foundation equationFree generic mask).lookup name = some leaf →
      (reading profile aligned relEnv reads generated samePlan expected foundation equationFree generic mask
        admits carriers).covers leaf :=
  fun _ _ found => ⟨lookup_accepts found, represented _⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.LocalReading
