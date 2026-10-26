import Mettapedia.OSLF.MeTTaIL.LawNormalTyping
import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.GSLT.LanguageDef.ModuleSource.Elaborate
import Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraExtraction
import Mettapedia.GSLT.LanguageDef.EquationInvariant
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef
import Mettapedia.GSLT.LanguageDef.BagNormalForm

/-!
# Forward typing and bare readback have different domains

The supplied law list removes a unit inside a named collection argument and
keeps that argument's type and wrapper. Its forward typing interface is
available even though the language has no bare carrier. The stricter witness
needed to insert bare collections is unavailable. These are typing controls;
the compiler's declared-law extraction still excludes this wrapped row.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls

open Syntax CollectionLaws
open Mettapedia.GSLT.LanguageDef.WellSorted

def atom (label : String) : GrammarRule :=
  { label, category := "Token", params := [], syntaxPattern := [] }

def wrapper : GrammarRule :=
  { label := "Wrapped", category := "Token",
    params := [.simple "items" (.collection .hashBag (.base "Token"))],
    syntaxPattern := [], collectionRepresentation := .wrapped,
    algebra? := some { flatten := true, unit := some "Zero" } }

def language : LanguageDef :=
  LanguageDef.ofCore "WrappedLawTyping" ["Token"] [atom "Zero",atom "A",wrapper] [] []

def laws : List Laws := [⟨.hashBag,some "Zero"⟩]

theorem forward_admission : LawsTyped laws language FreeTypeContext.empty where
  homogeneous law kind found rule member name element parameters := by
    simp only [language, LanguageDef.ofCore, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp_all [atom, wrapper]
  parameters rule member parameter parameterMember type typed := by
    simp only [language, LanguageDef.ofCore, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · simp [atom] at parameterMember
    · simp [atom] at parameterMember
    · have shape : parameter = .simple "items" (.collection .hashBag (.base "Token")) := by
        simpa [wrapper] using parameterMember
      subst parameter
      simp only [parameterType?, Option.some.injEq] at typed
      subst type
      exact ⟨trivial, fun _ _ _ same => by cases same⟩
  freeNames name type found := by simp [FreeTypeContext.empty] at found

def subject : Pattern :=
  .apply "Wrapped" [.collection .hashBag [.apply "Zero" [],.apply "A" []] none]

theorem subject_typed : HasType language FreeTypeContext.empty [] subject (.base "Token") :=
  checkHasType_sound (by decide)

theorem normalized_changes_content : normalize laws subject =
    .apply "Wrapped" [.collection .hashBag [.apply "A" []] none] := by
  simp [normalize, laws, subject, splice]

theorem normalized_stays_typed :
    HasType language FreeTypeContext.empty [] (normalize laws subject) (.base "Token") :=
  normalize_hasType forward_admission subject (by simp) trivial (by decide) subject_typed

theorem no_bare_carrier :
    ¬ ∃ rule ∈ language.terms, ∃ name,
      rule.bareParams = [.simple name (.collection .hashBag (.base rule.category))] := by
  rintro ⟨rule, member, name, shape⟩
  simp only [language, LanguageDef.ofCore, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [GrammarRule.bareParams, atom, wrapper] at shape

theorem no_strict_collection_license :
    ¬ LawTypeOk laws language (.collection .hashBag (.base "Token")) := by
  intro license
  obtain ⟨rule, member, name, shape, _⟩ := license.lawful
    (law := ⟨.hashBag,some "Zero"⟩) (by decide)
  exact no_bare_carrier ⟨rule,member,name,shape⟩

theorem forward_admission_does_not_supply_readback :
    ¬ LawsTypedStrict laws language FreeTypeContext.empty := by
  intro strict
  apply no_strict_collection_license
  exact strict.parameters wrapper (by simp [language, LanguageDef.ofCore])
    (.simple "items" (.collection .hashBag (.base "Token"))) (by simp [wrapper]) _ rfl

#guard (CollectionLaws.declared language).isEmpty

end Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.KindOnly

set_option maxHeartbeats 1800000

open Mettapedia.OSLF.MeTTaIL Syntax CollectionLaws CanonicalBags
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ModuleSource

def termType : TypeExpr := .base "Term"
def bagType : TypeExpr := .collection .hashBag termType
def nestedBagType : TypeExpr := .collection .hashBag bagType

def atom : GrammarRule :=
  { label := "A", category := "Term", params := [], syntaxPattern := [] }

def tokens : GrammarRule :=
  { label := "Tokens", category := "Term",
    params := [.simple "items" bagType], syntaxPattern := [],
    algebra? := some {flatten := true} }

def nest : GrammarRule :=
  { label := "Nest", category := "Term",
    params := [.simple "groups" nestedBagType], syntaxPattern := [],
    collectionRepresentation := .wrapped }

def nestWithTag : GrammarRule :=
  { label := "Nest", category := "Term",
    params := [.simple "groups" nestedBagType, .simple "tag" termType], syntaxPattern := [],
    collectionRepresentation := .wrapped }

def language : LanguageDef := LanguageDef.ofCore "NestedCarrier" ["Term"] [atom,tokens,nest] [] []
def taggedLanguage : LanguageDef := LanguageDef.ofCore "NestedCarrierTagged" ["Term"]
  [atom,tokens,nestWithTag] [] []

def subject : Pattern := .apply "Nest"
  [.collection .hashBag [.collection .hashBag [.apply "A" []] none] none]

def taggedSubject : Pattern := .apply "Nest"
  [.collection .hashBag [.collection .hashBag [.apply "A" []] none] none, .apply "A" []]

theorem tokens_bare_homogeneous :
    tokens.bareParams = [.simple "items" (.collection .hashBag (.base tokens.category))] := rfl

theorem single_bare_kind :
    language.terms.filter (fun rule => bareKind rule == some .hashBag) = [tokens] := by decide

theorem tagged_single_bare_kind :
    taggedLanguage.terms.filter (fun rule => bareKind rule == some .hashBag) = [tokens] := by decide

theorem declared_laws : CollectionLaws.declared language = [⟨.hashBag,none⟩] := by decide
theorem tagged_declared_laws : CollectionLaws.declared taggedLanguage = [⟨.hashBag,none⟩] := by decide

theorem subject_typed : HasType language FreeTypeContext.empty [] subject termType :=
  checkHasType_sound (by decide)

theorem tagged_subject_typed : HasType taggedLanguage FreeTypeContext.empty [] taggedSubject termType :=
  checkHasType_sound (by decide)

theorem normalized_shape : normalize (CollectionLaws.declared language) subject =
    .apply "Nest" [.collection .hashBag [.apply "A" []] none] := by
  simp [declared_laws, subject, normalize, splice]

theorem tagged_normalized_shape : normalize (CollectionLaws.declared taggedLanguage) taggedSubject =
    .apply "Nest" [.collection .hashBag [.apply "A" []] none, .apply "A" []] := by
  simp [tagged_declared_laws, taggedSubject, normalize, splice]

theorem normalization_breaks_typing :
    ¬ HasType language FreeTypeContext.empty [] (normalize (CollectionLaws.declared language) subject) termType := by
  rw [normalized_shape]
  intro typed
  have checked := checkHasType_complete_of_object typed (by decide)
  change false = true at checked
  cases checked

theorem tagged_normalization_breaks_typing :
    ¬ HasType taggedLanguage FreeTypeContext.empty []
      (normalize (CollectionLaws.declared taggedLanguage) taggedSubject) termType := by
  rw [tagged_normalized_shape]
  intro typed
  have checked := checkHasType_complete_of_object typed (by decide)
  change false = true at checked
  cases checked

theorem protected_single_has_no_laws :
    CollectionLaws.declared (retainSharedCollectionLabels language) = [] := by decide

theorem unprotected_tagged_breaks_typing :
    HasType taggedLanguage FreeTypeContext.empty [] taggedSubject termType ∧
    ¬ HasType taggedLanguage FreeTypeContext.empty []
      (normalize (CollectionLaws.declared taggedLanguage) taggedSubject) termType :=
  ⟨tagged_subject_typed, tagged_normalization_breaks_typing⟩

theorem explicit_metadata_guard_keeps_declaration :
    retainSharedCollectionLabels taggedLanguage = taggedLanguage := by cbv

theorem explicit_metadata_guard_keeps_laws :
    CollectionLaws.declared (retainSharedCollectionLabels taggedLanguage) = [⟨.hashBag,none⟩] := by cbv

theorem explicit_metadata_still_requires_role_certificate :
    ¬ HasType (retainSharedCollectionLabels taggedLanguage) FreeTypeContext.empty []
      (normalize (CollectionLaws.declared (retainSharedCollectionLabels taggedLanguage)) taggedSubject) termType := by
  rw [explicit_metadata_guard_keeps_declaration]
  exact tagged_normalization_breaks_typing

def parameterLanguage (field : TermParam) : LanguageDef :=
  LanguageDef.ofCore "ParameterDataRole" ["Term"] [atom,{tokens with algebra? := none},
    {nestWithTag with params := [field,.simple "tag" termType]}] [] []

theorem protected_binder_parameter :
    let field := TermParam.abstractionNamed (some "bound") "body" (.arrow termType nestedBagType)
    (retainSharedCollectionLabels (parameterLanguage field) ["Tokens"]).terms =
      [atom,{tokens with algebra? := none,collectionRepresentation := .wrapped},
        {nestWithTag with params := [field,.simple "tag" termType]}] := by cbv

theorem protected_multiBinder_parameter :
    let field := TermParam.multiAbstractionNamed ["left","right"] "body" (.multiBinder bagType)
    (retainSharedCollectionLabels (parameterLanguage field) ["Tokens"]).terms =
      [atom,{tokens with algebra? := none,collectionRepresentation := .wrapped},
        {nestWithTag with params := [field,.simple "tag" termType]}] := by cbv

theorem different_kind_parameter_keeps_declaration :
    let language := parameterLanguage (.simple "sets" (.collection .hashSet termType))
    retainSharedCollectionLabels language ["Tokens"] = language := by cbv

def binaryCarrierLanguage : LanguageDef :=
  {taggedLanguage with terms := [atom,{tokens with algebra? := none},nestWithTag]}

theorem binary_origin_protects_data_role :
    (retainSharedCollectionLabels binaryCarrierLanguage ["Tokens"]).terms =
      [atom,{tokens with algebra? := none,collectionRepresentation := .wrapped},nestWithTag] := by cbv

theorem absent_algebra_authority_keeps_declaration :
    retainSharedCollectionLabels binaryCarrierLanguage = binaryCarrierLanguage := by cbv

theorem nested_parameter_not_NoNested :
    ¬ NoNested (CollectionLaws.declared taggedLanguage) nestedBagType := by
  intro admitted
  exact admitted.2 ⟨.hashBag,none⟩ (by decide) termType rfl

theorem tagged_not_forward_profile :
    ¬ LawsTyped (CollectionLaws.declared taggedLanguage) taggedLanguage FreeTypeContext.empty := by
  intro admission
  apply nested_parameter_not_NoNested
  exact admission.parameters nestWithTag (by simp [taggedLanguage, LanguageDef.ofCore])
    (.simple "groups" nestedBagType) (by simp [nestWithTag]) _ rfl

theorem tagged_not_strict_profile :
    ¬ LawsTypedStrict (CollectionLaws.declared taggedLanguage) taggedLanguage FreeTypeContext.empty := by
  intro admission
  have ok := admission.parameters nestWithTag (by simp [taggedLanguage, LanguageDef.ofCore])
    (.simple "groups" nestedBagType) (by simp [nestWithTag]) _ rfl
  obtain ⟨rule, member, param, shape, impossible⟩ := ok.lawful
    (law := ⟨.hashBag,none⟩) (by decide)
  cases impossible

#print axioms tokens_bare_homogeneous
#print axioms single_bare_kind
#print axioms tagged_single_bare_kind
#print axioms declared_laws
#print axioms tagged_declared_laws
#print axioms subject_typed
#print axioms tagged_subject_typed
#print axioms normalized_shape
#print axioms tagged_normalized_shape
#print axioms normalization_breaks_typing
#print axioms tagged_normalization_breaks_typing
#print axioms protected_single_has_no_laws
#print axioms unprotected_tagged_breaks_typing
#print axioms explicit_metadata_guard_keeps_declaration
#print axioms explicit_metadata_guard_keeps_laws
#print axioms explicit_metadata_still_requires_role_certificate
#print axioms protected_binder_parameter
#print axioms protected_multiBinder_parameter
#print axioms different_kind_parameter_keeps_declaration
#print axioms binary_origin_protects_data_role
#print axioms absent_algebra_authority_keeps_declaration
#print axioms nested_parameter_not_NoNested
#print axioms tagged_not_forward_profile
#print axioms tagged_not_strict_profile

end Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.KindOnly

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.KindOnly.Representation

open Mettapedia.OSLF.MeTTaIL Syntax CollectionLaws CanonicalBags CoreReduction Match
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ModuleSource
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

def binary : GrammarRule :=
  { label := "Op", category := "Term", syntaxPattern := [],
    params := [.simple "x" termType, .simple "y" termType] }

def zero : GrammarRule :=
  { label := "Zero", category := "Term", syntaxPattern := [], params := [] }

def dataNest : GrammarRule :=
  { label := "Nest", category := "Term", syntaxPattern := [],
    params := [.simple "items" bagType, .simple "tag" termType],
    collectionRepresentation := .wrapped }

def associative : Equation :=
  { name := "assoc", typeContext := [], premises := [],
    left := .apply "Op" [.apply "Op" [.fvar "x",.fvar "y"],.fvar "z"],
    right := .apply "Op" [.fvar "x",.apply "Op" [.fvar "y",.fvar "z"]] }

def commutative : Equation :=
  { name := "comm", typeContext := [], premises := [],
    left := .apply "Op" [.fvar "x",.fvar "y"],
    right := .apply "Op" [.fvar "y",.fvar "x"] }

def leftUnit : Equation :=
  { name := "leftUnit", typeContext := [], premises := [],
    left := .apply "Op" [.apply "Zero" [],.fvar "x"], right := .fvar "x" }

def rightUnit : Equation :=
  { name := "rightUnit", typeContext := [], premises := [],
    left := .apply "Op" [.fvar "x",.apply "Zero" []], right := .fvar "x" }

def sourceValue : Value :=
  { entries := [newItem 0 .sort "Term" (.sort "Term"),
      newItem 0 .term "A" (.term atom), newItem 0 .term "Zero" (.term zero),
      newItem 0 .term "Op" (.term binary), newItem 0 .term "Nest" (.term dataNest),
      newItem 0 .equation "assoc" (.equation associative),
      newItem 0 .equation "comm" (.equation commutative),
      newItem 0 .equation "leftUnit" (.equation leftUnit),
      newItem 0 .equation "rightUnit" (.equation rightUnit)] }

def replacement : Replacement := { old := "Op", rule := {tokens with algebra? := none} }
def result : Value := (replaceRow sourceValue replacement).toOption.getD sourceValue
def source : LanguageDef := flattenRaw "DataBagSource" sourceValue
def unprotectedTarget : LanguageDef :=
  declareAlgebras (flattenRaw "DataBagTarget" result) (binaryCollectionLabels result)

def first : Pattern := .apply "Nest"
  [.collection .hashBag [.apply "Op" [.apply "A" [], .apply "A" []]] none, .apply "A" []]

def second : Pattern := .apply "Nest"
  [.collection .hashBag [.apply "A" [],.apply "A" []] none, .apply "A" []]

def unprotectedLowered (pattern : Pattern) : Pattern :=
  unwrap (bareLabels unprotectedTarget)
    (renameConstructor binary.label replacement.rule.label
      ((argumentMap binary replacement.rule).getD id) pattern)

theorem source_entries_valid :
    Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Valid sourceValue.entries.toFinset := by decide +kernel

theorem source_entry_labels_coherent :
    sourceValue.entries.all (fun item => match item.body with
      | .term rule => decide (item.label = (.term,rule.label))
      | _ => true) = true := by decide +kernel

theorem actual_replacement_accepted : replaceRow sourceValue replacement = .ok result := by
  have accepted : (replaceRow sourceValue replacement).isOk = true := by decide +kernel
  unfold result
  generalize actual : replaceRow sourceValue replacement = computed at accepted ⊢
  cases computed with
  | error _ => cases accepted
  | ok _ => rfl

theorem unprotected_target_inventory : unprotectedTarget.terms =
    [atom,zero,{tokens with algebra? := some {flatten := true,unit := some "Zero"}},dataNest] := by
  cbv

theorem unprotected_target_laws : CollectionLaws.declared unprotectedTarget = [⟨.hashBag,some "Zero"⟩] := by
  unfold CollectionLaws.declared
  rw [unprotected_target_inventory]
  decide +kernel

theorem first_typed : HasType source FreeTypeContext.empty [] first termType :=
  checkHasType_sound (by decide +kernel)

theorem second_typed : HasType source FreeTypeContext.empty [] second termType :=
  checkHasType_sound (by decide +kernel)

theorem unprotected_lowered_first : unprotectedLowered first = .apply "Nest"
    [.collection .hashBag [.collection .hashBag [.apply "A" [],.apply "A" []] none] none, .apply "A" []] := by
  cbv

theorem unprotected_lowered_second : unprotectedLowered second = second := by cbv

theorem unprotected_lowered_first_typed : HasType unprotectedTarget FreeTypeContext.empty [] (unprotectedLowered first) termType := by
  rw [unprotected_lowered_first]
  apply checkHasType_sound
  simp [checkHasType, checkArgumentsHaveTypes, checkElementsHaveType, unprotected_target_inventory,
    usesBareCollection?, bareCollectionElementType?, matchesParameterRepresentation?,
    atom, zero, tokens, dataNest, parameterType?, bagType, termType, GrammarRule.bareParams]

theorem unprotected_lowered_second_typed : HasType unprotectedTarget FreeTypeContext.empty [] (unprotectedLowered second) termType := by
  rw [unprotected_lowered_second]
  apply checkHasType_sound
  simp [checkHasType, checkArgumentsHaveTypes, checkElementsHaveType, unprotected_target_inventory,
    usesBareCollection?, bareCollectionElementType?, matchesParameterRepresentation?,
    atom, zero, tokens, dataNest, parameterType?, bagType, termType, GrammarRule.bareParams, second]

theorem unprotected_normal_forms_identified :
    normalize (CollectionLaws.declared unprotectedTarget) (unprotectedLowered first) =
      normalize (CollectionLaws.declared unprotectedTarget) (unprotectedLowered second) := by
  rw [unprotected_lowered_first,unprotected_lowered_second,unprotected_target_laws]
  simp [second,normalize,splice]

def operations (label : String) (arguments : List Nat) : Nat :=
  if label = "Op" then arguments.sum
  else if label = "Nest" then arguments.headD 0
  else 0

mutual
  def observe : Pattern → Nat
    | .bvar _ => 0
    | .fvar _ => 0
    | .apply label arguments => operations label (observeArguments arguments)
    | .lambda _ body => observe body
    | .multiLambda _ _ body => observe body
    | .subst body argument => observe body + observe argument
    | .collection _ elements _ => elements.length

  def observeArguments : List Pattern → List Nat
    | [] => []
    | first :: rest => observe first :: observeArguments rest
end

theorem observeArguments_append (first second : List Pattern) :
    observeArguments (first ++ second) = observeArguments first ++ observeArguments second := by
  induction first with
  | nil => rfl
  | cons first rest ih => simp only [List.cons_append,observeArguments,ih]

theorem observe_fill_congr (context : OneHoleContext) {first second : Pattern}
    (same : observe first = observe second) :
    observe (context.fill first) = observe (context.fill second) := by
  induction context with
  | hole => exact same
  | apply label before inner after ih =>
      simp only [OneHoleContext.fill,observe,observeArguments_append,observeArguments,ih]
  | lambda binder inner ih => simpa only [OneHoleContext.fill,observe] using ih
  | multiLambda arity binders inner ih => simpa only [OneHoleContext.fill,observe] using ih
  | substBody inner argument ih => simp only [OneHoleContext.fill,observe,ih]
  | substReplacement body inner ih => simp only [OneHoleContext.fill,observe,ih]
  | collection kind before inner after rest ih =>
      simp only [OneHoleContext.fill,observe,List.length_append,List.length_cons]

theorem source_inventory : source.terms = [atom,zero,binary,dataNest] := rfl
theorem source_equations : source.equations = [associative,commutative,leftUnit,rightUnit] := rfl

theorem source_plain : PlainEquations source := by
  intro equation member
  change equation ∈ [associative,commutative,leftUnit,rightUnit] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

theorem no_source_collection_carrier {rule : GrammarRule} {kind : CollType}
    (carrier : CollectionCarrierRule source rule kind) : False := by
  have member := carrier.authored
  have shape := carrier.selfSorted
  rw [source_inventory] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp [atom,zero,binary,dataNest] at shape

theorem no_source_algebra {rule : GrammarRule} {kind : CollType} {algebra : CollectionAlgebra}
    (carrier : AlgebraRule source rule kind algebra) : False := by
  have member := carrier.authored
  have declared := carrier.declared
  rw [source_inventory] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp [atom,zero,binary,dataNest] at declared

theorem source_instances_observed (equation : Equation) (member : equation ∈ source.equations)
    (bindings : Bindings) :
    observe (applyBindings bindings equation.left) = observe (applyBindings bindings equation.right) := by
  rw [source_equations] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp [associative,commutative,leftUnit,rightUnit,applyBindings,observe,observeArguments,operations] <;> omega

theorem source_equivalence_observed (base : ContextualStep.BasePremiseEvaluator)
    {left right : Pattern} (equivalent : EquationEquiv base source left right) :
    observe left = observe right := by
  apply equationEquiv_invariant observe (fun context _ _ same => observe_fill_congr context same) _ equivalent
  intro first second generator
  rcases generator with authored | derived
  · obtain ⟨equation, member, bindings, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ :=
      equationInstance_sides source_plain authored
    · exact source_instances_observed equation member bindings
    · exact (source_instances_observed equation member bindings).symm
  · cases derived with
    | bagPerm _ _ permutation => exact permutation.length_eq
    | setPerm _ _ permutation => exact permutation.length_eq
    | setDedup member kindTyped =>
        have uses := usesCollection_eq_true_of_collectionTypedAt member kindTyped
        have absent : source.usesCollection .hashSet = false := by cbv
        rw [absent] at uses
        cases uses
    | flatten carrier _ _ => exact False.elim (no_source_algebra carrier)
    | singleton carrier _ _ => exact False.elim (no_source_algebra carrier)
    | unitElim carrier _ _ => exact False.elim (no_source_algebra carrier)
    | emptyUnit carrier _ _ => exact False.elim (no_source_algebra carrier)

theorem source_inequivalent (base : ContextualStep.BasePremiseEvaluator) :
    ¬ EquationEquiv base source first second := by
  intro equivalent
  have observed := source_equivalence_observed base equivalent
  change (1 : Nat) = 2 at observed
  cases observed

theorem unprotected_target_law_equivalent :
    LawSame (CollectionLaws.declared unprotectedTarget) (unprotectedLowered first) (unprotectedLowered second) :=
  (lawNormal_iff _ _ _).mp (congrArg canon unprotected_normal_forms_identified)

theorem unprotected_collection_law_readout_does_not_reflect_source_equations
    (base : ContextualStep.BasePremiseEvaluator) :
    ¬ (∀ left right,
      HasType source FreeTypeContext.empty [] left termType →
      HasType source FreeTypeContext.empty [] right termType →
      LawSame (CollectionLaws.declared unprotectedTarget) (unprotectedLowered left) (unprotectedLowered right) →
      EquationEquiv base source left right) := by
  intro reflect
  exact source_inequivalent base (reflect first second first_typed second_typed unprotected_target_law_equivalent)

theorem unprotected_target_bag_type_licensed : LawTypeOk (CollectionLaws.declared unprotectedTarget) unprotectedTarget bagType := by
  refine .inr ⟨{tokens with algebra? := some {flatten := true,unit := some "Zero"}}, ?_, "items", rfl, rfl⟩
  rw [unprotected_target_inventory]
  simp

theorem unprotected_target_strict_typing_profile :
    LawsTypedStrict (CollectionLaws.declared unprotectedTarget) unprotectedTarget FreeTypeContext.empty where
  homogeneous law kind found rule member parameter element parameters := by
    rw [unprotected_target_inventory] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp_all [atom,zero,tokens,dataNest,bagType,termType]
  units law kind found label unit rule member parameter element parameters := by
    have lawMember := List.mem_of_find?_eq_some found
    rw [unprotected_target_laws] at lawMember
    have same := List.mem_singleton.mp lawMember
    subst law
    have labelEq := Option.some.inj unit
    subst label
    refine ⟨zero, ?_, rfl, rfl, ?_⟩
    · rw [unprotected_target_inventory]; simp
    · rw [unprotected_target_inventory] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> rfl
  parameters rule member parameter parameterMember type typed := by
    rw [unprotected_target_inventory] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · simp [atom] at parameterMember
    · simp [zero] at parameterMember
    · have shape : parameter = .simple "items" bagType := by simpa [tokens] using parameterMember
      subst parameter
      have typeEq : bagType = type := Option.some.inj typed
      subst type
      exact unprotected_target_bag_type_licensed
    · simp only [dataNest,List.mem_cons,List.not_mem_nil,or_false] at parameterMember
      rcases parameterMember with rfl | rfl
      · have typeEq : bagType = type := Option.some.inj typed
        subst type
        exact unprotected_target_bag_type_licensed
      · have typeEq : termType = type := Option.some.inj typed
        subst type
        trivial
  freeNames name type found := by simp [FreeTypeContext.empty] at found

theorem unprotected_target_fails_other_collection_free_parameters :
    ¬ (∀ rule ∈ unprotectedTarget.terms,
      rule ≠ {tokens with algebra? := some {flatten := true,unit := some "Zero"}} →
      ∀ parameter ∈ rule.params,
        Mettapedia.GSLT.LanguageDef.BagNormalForm.collectionFree (TermParam.typeExpr parameter) = true) := by
  intro otherParameters
  have notTokens : dataNest ≠ {tokens with algebra? := some {flatten := true,unit := some "Zero"}} := by decide
  have impossible := otherParameters dataNest (by rw [unprotected_target_inventory]; simp) notTokens
    (.simple "items" bagType) (by simp [dataNest])
  change false = true at impossible
  cases impossible

/-- The actual protected pass keeps the algebra operation named and retains
all translated authored equations, rather than assigning a kind-wide law. -/
def protectedTarget : LanguageDef := flatten "DataBagTarget" result

def protectedLowered (pattern : Pattern) : Pattern :=
  unwrap (bareLabels protectedTarget)
    (renameConstructor binary.label replacement.rule.label
      ((argumentMap binary replacement.rule).getD id) pattern)

theorem actual_binary_origin : binaryCollectionLabels result = ["Tokens"] := by cbv

theorem replacement_origins_retained :
    result.entries.map (·.origin) = sourceValue.entries.map (·.origin) := by cbv

theorem protected_target_inventory : protectedTarget.terms =
    [atom,zero,{tokens with algebra? := none,collectionRepresentation := .wrapped},dataNest] := by cbv

theorem protected_fold_unchanged :
    declareAlgebras
      (retainSharedCollectionLabels (flattenRaw "DataBagTarget" result) (binaryCollectionLabels result))
      (binaryCollectionLabels result) =
      retainSharedCollectionLabels (flattenRaw "DataBagTarget" result) (binaryCollectionLabels result) := by
  apply declareAlgebras_eq_self_of_unavailable
  intro rule member
  have inventory :
      (retainSharedCollectionLabels (flattenRaw "DataBagTarget" result) (binaryCollectionLabels result)).terms =
        [atom,zero,{tokens with algebra? := none,collectionRepresentation := .wrapped},dataNest] := by cbv
  rw [inventory] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> right <;> cbv

theorem protected_target_equations_retained :
    protectedTarget.equations = (flattenRaw "DataBagTarget" result).equations := by
  change (declareAlgebras
    (retainSharedCollectionLabels (flattenRaw "DataBagTarget" result) (binaryCollectionLabels result))
    (binaryCollectionLabels result)).equations = _
  rw [protected_fold_unchanged]
  rfl

theorem protected_target_equation_count : protectedTarget.equations.length = 4 := by cbv

theorem protected_target_has_no_kind_laws : CollectionLaws.declared protectedTarget = [] := by cbv

theorem protected_target_named : (bareLabels protectedTarget).lookup "Tokens" = none := by cbv

theorem protected_lowered_first : protectedLowered first = .apply "Nest"
    [.collection .hashBag [.apply "Tokens" [.collection .hashBag [.apply "A" [],.apply "A" []] none]] none,
      .apply "A" []] := by cbv

theorem protected_lowered_second : protectedLowered second = second := by cbv

theorem protected_lowered_first_typed :
    HasType protectedTarget FreeTypeContext.empty [] (protectedLowered first) termType :=
  checkHasType_sound (by cbv)

theorem protected_lowered_second_typed :
    HasType protectedTarget FreeTypeContext.empty [] (protectedLowered second) termType :=
  checkHasType_sound (by cbv)

theorem protected_normal_forms_distinct :
    normalize (CollectionLaws.declared protectedTarget) (protectedLowered first) ≠
      normalize (CollectionLaws.declared protectedTarget) (protectedLowered second) := by
  cbv
  decide

theorem protected_law_readout_distinct :
    lawNormal (CollectionLaws.declared protectedTarget) (protectedLowered first) ≠
      lawNormal (CollectionLaws.declared protectedTarget) (protectedLowered second) := by
  cbv
  decide

theorem protected_not_kind_law_equivalent :
    ¬ LawSame (CollectionLaws.declared protectedTarget) (protectedLowered first) (protectedLowered second) := by
  intro equivalent
  exact protected_law_readout_distinct ((lawNormal_iff _ _ _).mpr equivalent)

#print axioms actual_binary_origin
#print axioms replacement_origins_retained
#print axioms protected_target_inventory
#print axioms protected_fold_unchanged
#print axioms protected_target_equations_retained
#print axioms protected_target_equation_count
#print axioms protected_target_has_no_kind_laws
#print axioms protected_target_named
#print axioms protected_lowered_first
#print axioms protected_lowered_second
#print axioms protected_lowered_first_typed
#print axioms protected_lowered_second_typed
#print axioms protected_normal_forms_distinct
#print axioms protected_law_readout_distinct
#print axioms protected_not_kind_law_equivalent

#print axioms actual_replacement_accepted
#print axioms source_entries_valid
#print axioms source_entry_labels_coherent
#print axioms unprotected_target_inventory
#print axioms unprotected_target_laws
#print axioms first_typed
#print axioms second_typed
#print axioms unprotected_lowered_first
#print axioms unprotected_lowered_second
#print axioms unprotected_lowered_first_typed
#print axioms unprotected_lowered_second_typed
#print axioms unprotected_normal_forms_identified
#print axioms observeArguments_append
#print axioms observe_fill_congr
#print axioms source_inventory
#print axioms source_equations
#print axioms source_plain
#print axioms no_source_collection_carrier
#print axioms no_source_algebra
#print axioms source_instances_observed
#print axioms source_equivalence_observed
#print axioms source_inequivalent
#print axioms unprotected_target_law_equivalent
#print axioms unprotected_collection_law_readout_does_not_reflect_source_equations
#print axioms unprotected_target_bag_type_licensed
#print axioms unprotected_target_strict_typing_profile
#print axioms unprotected_target_fails_other_collection_free_parameters

end Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.KindOnly.Representation

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.RoleAwareControls

set_option maxHeartbeats 1800000

open Mettapedia.OSLF.MeTTaIL Syntax CanonicalBags RoleAware CollectionLaws
open Mettapedia.GSLT.LanguageDef.WellSorted
open GeneralPremise.SchemaTyping
open Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.KindOnly

abbrev unprotectedLanguage := Representation.unprotectedTarget
abbrev unprotectedLaws := CollectionLaws.declared unprotectedLanguage

theorem nested_profile_checked : checkBareHomogeneous (CollectionLaws.declared taggedLanguage) taggedLanguage = true := by decide

theorem nested_data_stays : reduceAt (CollectionLaws.declared taggedLanguage) [] taggedLanguage
    FreeTypeContext.empty [] taggedSubject termType = taggedSubject := by cbv

theorem nested_data_typed : HasType taggedLanguage FreeTypeContext.empty []
    (reduceAt (CollectionLaws.declared taggedLanguage) [] taggedLanguage FreeTypeContext.empty [] taggedSubject termType)
      termType := reduceAt_hasType nested_profile_checked [] taggedSubject tagged_subject_typed

theorem unprotected_profile_checked : checkBareHomogeneous unprotectedLaws unprotectedLanguage = true := by cbv

theorem data_first_stays : reduceAt unprotectedLaws [] unprotectedLanguage FreeTypeContext.empty []
    (Representation.unprotectedLowered Representation.first) termType = Representation.unprotectedLowered Representation.first := by
  rw [Representation.unprotected_lowered_first]
  cbv

theorem data_second_stays : reduceAt unprotectedLaws [] unprotectedLanguage FreeTypeContext.empty []
    (Representation.unprotectedLowered Representation.second) termType = Representation.unprotectedLowered Representation.second := by
  rw [Representation.unprotected_lowered_second]
  cbv

theorem data_presentations_distinct :
    reduceAt unprotectedLaws [] unprotectedLanguage FreeTypeContext.empty [] (Representation.unprotectedLowered Representation.first) termType ≠
      reduceAt unprotectedLaws [] unprotectedLanguage FreeTypeContext.empty [] (Representation.unprotectedLowered Representation.second) termType := by
  rw [data_first_stays,data_second_stays,Representation.unprotected_lowered_first,Representation.unprotected_lowered_second]
  decide

def algebraSubject : Pattern := .collection .hashBag
  [.collection .hashBag [.apply "A" [],.apply "A" []] none,.apply "Zero" []] none

theorem algebra_flattens_and_removes_unit : reduceAt unprotectedLaws [] unprotectedLanguage FreeTypeContext.empty [] algebraSubject termType =
    .collection .hashBag [.apply "A" [],.apply "A" []] none := by cbv

theorem algebra_stays_typed : HasType unprotectedLanguage FreeTypeContext.empty []
    (reduceAt unprotectedLaws [] unprotectedLanguage FreeTypeContext.empty [] algebraSubject termType) termType := by
  apply reduceAt_hasType unprotected_profile_checked
  apply checkHasType_sound
  simp [checkHasType,checkArgumentsHaveTypes,checkElementsHaveType,Representation.unprotected_target_inventory,
    usesBareCollection?,bareCollectionElementType?,
    Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.KindOnly.atom,Representation.zero,tokens,Representation.dataNest,bagType,termType,
    GrammarRule.bareParams,algebraSubject]

def lambdaSubject : Pattern := .lambda none
  (.collection .hashBag [.collection .hashBag [.bvar 0,.apply "A" []] none,.apply "Zero" []] none)

theorem lambda_scope : reduceAt unprotectedLaws [] unprotectedLanguage FreeTypeContext.empty [] lambdaSubject (.arrow termType termType) =
    .lambda none (.collection .hashBag [.bvar 0,.apply "A" []] none) := by cbv

def multiSubject : Pattern := .multiLambda 2 []
  (.collection .hashBag [.collection .hashBag [.bvar 1,.bvar 0] none,.apply "Zero" []] none)

theorem multi_scope : reduceAt unprotectedLaws [] unprotectedLanguage FreeTypeContext.empty [] multiSubject
    (.arrow (.multiBinder termType) termType) =
    .multiLambda 2 [] (.collection .hashBag [.bvar 1,.bvar 0] none) := by cbv

def substitutionBody : Pattern := .collection .hashBag [.collection .hashBag [.bvar 0,.apply "A" []] none] none
def substitutionSubject : Pattern := .subst substitutionBody algebraSubject
def substitutionSchema : RewriteRule :=
  { name := "ScopedNormalization",typeContext := [],premises := [],left := substitutionSubject,right := .apply "A" [] }
def unprotectedDomains : List TypeExpr := declaredDomains unprotectedLanguage substitutionSchema []

theorem substitution_domain_from_signature :
    substitutionDomain? unprotectedDomains unprotectedLanguage FreeTypeContext.empty [] termType substitutionBody algebraSubject = some termType := by cbv

theorem substitution_scopes : reduceAt unprotectedLaws unprotectedDomains unprotectedLanguage FreeTypeContext.empty [] substitutionSubject termType =
    .subst (.collection .hashBag [.bvar 0,.apply "A" []] none)
      (.collection .hashBag [.apply "A" [],.apply "A" []] none) := by cbv

theorem missing_substitution_domain_retains : reduceAt unprotectedLaws [] unprotectedLanguage FreeTypeContext.empty [] substitutionSubject termType =
    substitutionSubject := by cbv

theorem lambda_source_typed : HasType unprotectedLanguage FreeTypeContext.empty [] lambdaSubject (.arrow termType termType) :=
  checkSchemaType_sound (domains := []) (by cbv)

theorem multi_source_typed : HasType unprotectedLanguage FreeTypeContext.empty [] multiSubject
    (.arrow (.multiBinder termType) termType) := checkSchemaType_sound (domains := []) (by cbv)

theorem substitution_source_typed : HasType unprotectedLanguage FreeTypeContext.empty [] substitutionSubject termType :=
  checkSchemaType_sound (domains := unprotectedDomains) (by cbv)

theorem substitution_typed_after_missing_domain : HasType unprotectedLanguage FreeTypeContext.empty []
    (reduceAt unprotectedLaws [] unprotectedLanguage FreeTypeContext.empty [] substitutionSubject termType) termType :=
  reduceAt_hasType unprotected_profile_checked [] substitutionSubject substitution_source_typed

def holder : GrammarRule :=
  { label := "Holder",category := "Term",syntaxPattern := [],
    params := [.abstractionNamed none "body" (.arrow termType termType)] }
def holderLanguage : LanguageDef := {unprotectedLanguage with terms := unprotectedLanguage.terms ++ [holder]}
def holderSubject : Pattern := .apply "Holder" [lambdaSubject]
def malformedHolder : Pattern := .apply "Holder" [
  .lambda (some "named") (.collection .hashBag [.collection .hashBag [.bvar 0,.apply "A" []] none] none)]

theorem constructor_binder_slot : reduceAt unprotectedLaws [] holderLanguage FreeTypeContext.empty [] holderSubject termType =
    .apply "Holder" [.lambda none (.collection .hashBag [.bvar 0,.apply "A" []] none)] := by cbv

theorem constructor_binder_source_typed : HasType holderLanguage FreeTypeContext.empty [] holderSubject termType :=
  checkSchemaType_sound (domains := []) (by cbv)

theorem malformed_binder_slot_retained :
    reduceAt unprotectedLaws [] holderLanguage FreeTypeContext.empty [] malformedHolder termType = malformedHolder := by cbv

theorem malformed_binder_slot_untyped : ¬ HasType holderLanguage FreeTypeContext.empty [] malformedHolder termType := by
  intro typed
  have checked := checkHasType_complete_of_object typed (by decide)
  have rejected : checkHasType holderLanguage FreeTypeContext.empty [] malformedHolder termType = false := by cbv
  rw [rejected] at checked
  cases checked

def freeCapture : FreeTypeContext := fun name => if name = "z" then some termType else none
def captureSubject : Pattern := .lambda none (.collection .hashBag [
  .collection .hashBag [.bvar 0,.fvar "z"] none,.apply "Zero" []] none)

theorem captured_scope_kept : reduceAt unprotectedLaws [] unprotectedLanguage freeCapture [] captureSubject (.arrow termType termType) =
    .lambda none (.collection .hashBag [.bvar 0,.fvar "z"] none) := by cbv

theorem captured_name_kept :
    (reduceAt unprotectedLaws [] unprotectedLanguage freeCapture [] captureSubject (.arrow termType termType)).freeFvarNames = ["z"] := by
  rw [captured_scope_kept]
  cbv

theorem singleton_and_empty_boundaries_kept :
    reduceAt unprotectedLaws [] unprotectedLanguage FreeTypeContext.empty []
      (.collection .hashBag [.apply "A" []] none) termType = .collection .hashBag [.apply "A" []] none ∧
    reduceAt unprotectedLaws [] unprotectedLanguage FreeTypeContext.empty []
      (.collection .hashBag [] none) termType = .collection .hashBag [] none := by cbv

theorem data_unit_kept : reduceAt unprotectedLaws [] unprotectedLanguage FreeTypeContext.empty []
    (.apply "Nest" [.collection .hashBag [.apply "Zero" [],.apply "A" []] none,.apply "A" []]) termType =
    .apply "Nest" [.collection .hashBag [.apply "Zero" [],.apply "A" []] none,.apply "A" []] := by cbv

#print axioms nested_profile_checked
#print axioms nested_data_stays
#print axioms nested_data_typed
#print axioms unprotected_profile_checked
#print axioms data_first_stays
#print axioms data_second_stays
#print axioms data_presentations_distinct
#print axioms algebra_flattens_and_removes_unit
#print axioms algebra_stays_typed
#print axioms lambda_scope
#print axioms multi_scope
#print axioms substitution_domain_from_signature
#print axioms substitution_scopes
#print axioms missing_substitution_domain_retains
#print axioms lambda_source_typed
#print axioms multi_source_typed
#print axioms substitution_source_typed
#print axioms substitution_typed_after_missing_domain
#print axioms constructor_binder_slot
#print axioms constructor_binder_source_typed
#print axioms malformed_binder_slot_retained
#print axioms malformed_binder_slot_untyped
#print axioms captured_scope_kept
#print axioms captured_name_kept
#print axioms singleton_and_empty_boundaries_kept
#print axioms data_unit_kept

end Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.RoleAwareControls

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.MetadataDomainControls
open Mettapedia.OSLF.MeTTaIL Syntax CollectionLaws
open Mettapedia.GSLT.LanguageDef ModuleSource WellSorted EquationSemantics
open CanonicalBags.LawRepresentationControls.KindOnly

def algebra : CollectionAlgebra := {flatten := true,unit := some "Zero"}
def carrier : GrammarRule := {tokens with algebra? := some algebra}
def metadataValue : Value :=
  {entries := [newItem 0 .sort "Term" (.sort "Term"),
    newItem 0 .term "A" (.term Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.KindOnly.atom),
    newItem 0 .term "Zero" (.term Representation.zero),
    newItem 0 .term "Tokens" (.term carrier),
    newItem 0 .term "Nest" (.term Representation.dataNest)]}
def source : LanguageDef := flattenRaw "Metadata" metadataValue
/-- Wrapping only the declaration loses the existing bare-law interpretation. -/
def wrappedOnly : LanguageDef :=
  {source with terms := [Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.KindOnly.atom,Representation.zero,
    {carrier with collectionRepresentation := .wrapped},Representation.dataNest]}

def actual : LanguageDef := flatten "Metadata" metadataValue

def presentation : Module :=
  ⟨[], "ExplicitMetadata", [⟨"Main",[],
    .extend none [.types ["Term"],.terms [Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.KindOnly.atom,Representation.zero,carrier,Representation.dataNest]]⟩],
    some (["Main"],[])⟩

def nested : Pattern := .collection .hashBag [.collection .hashBag [.apply "A" [],.apply "A" []] none] none
def flat : Pattern := .collection .hashBag [.apply "A" [],.apply "A" []] none

theorem no_binary_origin : binaryCollectionLabels metadataValue = [] := by cbv
theorem no_equation_rows : source.equations = [] ∧ wrappedOnly.equations = [] := by cbv
theorem programmatic_module_accepted : (elaborate [] presentation).isOk = true := by cbv
theorem programmatic_module_preserves_laws :
    CollectionLaws.declared ((elaborate [] presentation).toOption.getD (LanguageDef.empty "")) = [⟨.hashBag,some "Zero"⟩] := by cbv
theorem source_declared_laws : CollectionLaws.declared source = [⟨.hashBag,some "Zero"⟩] := by cbv
theorem wrapped_metadata_inventory : wrappedOnly.terms =
    [Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.KindOnly.atom,Representation.zero,{carrier with collectionRepresentation := .wrapped},Representation.dataNest] := by cbv
theorem wrapped_metadata_field_retained : wrappedOnly.terms[2]?.bind (·.algebra?) = some algebra := by cbv
theorem wrapped_metadata_loses_kind_laws : CollectionLaws.declared wrappedOnly = [] := by cbv

theorem source_inventory : source.terms = [Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.KindOnly.atom,Representation.zero,carrier,Representation.dataNest] := by cbv

theorem source_algebra : AlgebraRule source carrier .hashBag algebra where
  authored := by rw [source_inventory]; simp
  declared := rfl
  selfSorted := ⟨"items",rfl⟩
  unitAuthored unit present := by
    have same : "Zero" = unit := Option.some.inj present
    subst unit
    exact ⟨Representation.zero,by rw [source_inventory]; simp,rfl,rfl,rfl⟩

theorem source_nested_typed : HasType source FreeTypeContext.empty [] nested termType :=
  checkHasType_sound (by cbv)
theorem source_nested_sorted : SortedAt source nested "Term" :=
  ⟨FreeTypeContext.empty,[],source_nested_typed⟩
theorem source_flatten_instance : DerivedInstance source nested flat :=
  DerivedInstance.flatten (pre := []) (inner := [.apply "A" [],.apply "A" []])
    (post := []) source_algebra rfl source_nested_sorted

theorem wrapped_metadata_no_collection_sort (sort : String) {free : FreeTypeContext} {bound : List TypeExpr}
    {elements : List Pattern} :
    ¬ HasSort wrappedOnly free bound (.collection .hashBag elements none) sort := by
  intro typed
  cases typed with
  | collectionConstructor member shape _ =>
    rw [wrapped_metadata_inventory] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [GrammarRule.bareParams,Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.KindOnly.atom,Representation.zero,Representation.dataNest] at shape

theorem wrapped_metadata_no_bare_sorted {elements : List Pattern} :
    ¬ SortedAt wrappedOnly (.collection .hashBag elements none) "Term" := by
  rintro ⟨free,bound,typed⟩
  exact wrapped_metadata_no_collection_sort "Term" typed

theorem source_normalizer_flattens : normalize (CollectionLaws.declared source) nested = flat := by cbv
theorem wrapped_metadata_normalizer_retains_nested : normalize (CollectionLaws.declared wrappedOnly) nested = nested := by cbv

theorem source_empty_unit : DerivedInstance source (.collection .hashBag [] none) (.apply "Zero" []) :=
  DerivedInstance.emptyUnit source_algebra rfl
    ⟨FreeTypeContext.empty,[],checkHasType_sound (by cbv)⟩

theorem explicit_metadata_not_pending : collectionAlgebraCandidate carrier [] = false := by cbv

theorem explicit_metadata_with_origin_not_pending :
    collectionAlgebraCandidate carrier ["Tokens"] = false := by cbv

theorem actual_metadata_profile_preserved : actual = source := by cbv

theorem actual_declared_laws_preserved :
    CollectionLaws.declared actual = [⟨.hashBag,some "Zero"⟩] := by
  rw [actual_metadata_profile_preserved]
  exact source_declared_laws

theorem actual_flatten_instance_preserved : DerivedInstance actual nested flat := by
  rw [actual_metadata_profile_preserved]
  exact source_flatten_instance

theorem actual_unit_instance_preserved :
    DerivedInstance actual (.collection .hashBag [] none) (.apply "Zero" []) := by
  rw [actual_metadata_profile_preserved]
  exact source_empty_unit

/-- Missing binary equation rows cannot create a successful replacement. -/
def binaryWithoutRows : Value :=
  {Representation.sourceValue with
    entries := Representation.sourceValue.entries.filter
      (fun item => match item.body with | .equation _ => false | _ => true)}

theorem binary_without_rows_replacement_refused :
    replaceRow binaryWithoutRows Representation.replacement =
      .error (.replaceAddsLaws "Op" "Tokens" "commutativity") := by cbv

/-- A manually supplied origin list is not a source-origin certificate. Even
this raw value cannot make the extraction pass invent missing algebra laws. -/
def syntheticMissingRowsCandidate : Value :=
  {metadataValue with
    entries := [newItem 0 .sort "Term" (.sort "Term"),
    newItem 0 .term "A" (.term Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.KindOnly.atom),newItem 0 .term "Zero" (.term Representation.zero),
    newItem 0 .term "Tokens" (.term {carrier with algebra? := none}),
    newItem 0 .term "Nest" (.term Representation.dataNest)]
    binaryCollections := [⟨0,"Tokens"⟩]}

theorem synthetic_origin_does_not_supply_laws :
    let result := flatten "MissingRows" syntheticMissingRowsCandidate
    result.equations = [] ∧ CollectionLaws.declared result = [] ∧
      result.terms[2]?.bind (·.algebra?) = none := by cbv

#print axioms explicit_metadata_not_pending
#print axioms explicit_metadata_with_origin_not_pending
#print axioms actual_metadata_profile_preserved
#print axioms actual_declared_laws_preserved
#print axioms actual_flatten_instance_preserved
#print axioms actual_unit_instance_preserved
#print axioms binary_without_rows_replacement_refused
#print axioms synthetic_origin_does_not_supply_laws

#print axioms no_binary_origin
#print axioms no_equation_rows
#print axioms programmatic_module_accepted
#print axioms programmatic_module_preserves_laws
#print axioms source_declared_laws
#print axioms wrapped_metadata_inventory
#print axioms wrapped_metadata_field_retained
#print axioms wrapped_metadata_loses_kind_laws
#print axioms source_inventory
#print axioms source_algebra
#print axioms source_nested_typed
#print axioms source_nested_sorted
#print axioms source_flatten_instance
#print axioms wrapped_metadata_no_collection_sort
#print axioms wrapped_metadata_no_bare_sorted
#print axioms source_normalizer_flattens
#print axioms wrapped_metadata_normalizer_retains_nested
#print axioms source_empty_unit
end Mettapedia.OSLF.MeTTaIL.CanonicalBags.LawRepresentationControls.MetadataDomainControls
