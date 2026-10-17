import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension
import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NamedSubstitutionElaboration

/-!
# Derived tuple categories in the existing core

A finite tuple declaration expands to one ordinary carrier sort and one
ordinary constructor row. Its component sorts have already been elaborated to
base sorts. No `TypeExpr.product` or extra LanguageDef field is introduced.

The typing theorem compares the core constructor judgment with independent,
pointwise component typing, in both directions. Fresh generated labels prevent
an old constructor from masquerading as the tuple constructor. A separate
signature theorem validates this expansion over an inert syntax carrier.
Every old typing derivation is preserved, and typing is reflected on patterns
that do not use the new constructor. Equations and rewrites are retained
verbatim; the executable top-level rewrite list stays exactly the same.

This is a tuple-syntax derivation. It does not manufacture projection equations,
eta laws, or a categorical universal property. Nested category elaboration,
validation stability for a base with laws, full modulo-equations
conservativity, and textual notation transport have their own obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.ProductCategoryElaboration

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition

structure Declaration where
  sort : String
  constructor : String
  components : List String
deriving Repr, DecidableEq

/-- Slot names are positional; repeated component sorts do not merge slots. -/
def parametersFrom (index : Nat) : List String → List TermParam
  | [] => []
  | sort :: rest =>
      .simple s!"component:{index}" (.base sort) :: parametersFrom (index + 1) rest

def tupleRule (declaration : Declaration) : GrammarRule :=
  let parameters := parametersFrom 0 declaration.components
  { label := declaration.constructor
    category := declaration.sort
    params := parameters
    syntaxPattern := parameters.map fun parameter => .nonTerminal parameter.bodyName }

def compile (core : LanguageDef) (declaration : Declaration) : LanguageDef :=
  { core with
    types := core.types ++ [TypeDecl.plain declaration.sort]
    terms := core.terms ++ [tupleRule declaration] }

def codec : ExactDeclarationCodec (String × String × List String) Declaration where
  encode := fun declaration =>
    (declaration.sort, declaration.constructor, declaration.components)
  decode := fun source => ⟨source.1, source.2.1, source.2.2⟩
  decode_encode := by intro declaration; cases declaration; rfl
  encode_decode := by rintro ⟨sort, constructor, components⟩; rfl

def tupleLayer : CompositionalLayer LanguageDef :=
  CompositionalLayer.ofCodec LanguageDef codec

theorem parameters_length (index : Nat) (components : List String) :
    (parametersFrom index components).length = components.length := by
  induction components generalizing index with
  | nil => rfl
  | cons sort rest ih => simp [parametersFrom, ih]

/-- The source tuple judgment checks each component independently in order. -/
def ComponentsTyped (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (sorts : List String) (arguments : List Pattern) : Prop :=
  List.Forall₂ (fun sort argument => HasSort language free bound argument sort)
    sorts arguments

theorem arguments_typed_iff_components (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr)
    (index : Nat) (sorts : List String) (arguments : List Pattern) :
    ArgumentsHaveTypes language free bound arguments (parametersFrom index sorts) ↔
      ComponentsTyped language free bound sorts arguments := by
  induction sorts generalizing index arguments with
  | nil =>
      cases arguments with
      | nil => exact ⟨fun _ => .nil, fun _ => .nil⟩
      | cons argument arguments =>
          constructor <;> intro impossible <;> cases impossible
  | cons sort sorts ih =>
      cases arguments with
      | nil => constructor <;> intro impossible <;> cases impossible
      | cons argument arguments =>
          constructor
          · intro typed
            have headTail := ArgumentsHaveTypes.simple_cons_inv typed
            exact .cons headTail.1 ((ih (index + 1) arguments).mp headTail.2)
          · intro typed
            cases typed with
            | cons head tail =>
                exact .cons trivial rfl head ((ih (index + 1) arguments).mpr tail)

theorem tuple_not_bare_collection (declaration : Declaration) :
    ¬ UsesBareCollection (tupleRule declaration) := by
  rintro ⟨name, kind, element, shape⟩
  cases components : declaration.components with
  | nil => simp [tupleRule, components, parametersFrom] at shape
  | cons first rest =>
      cases rest <;> simp [tupleRule, components, parametersFrom] at shape

theorem tuple_rule_unique (core : LanguageDef) (declaration : Declaration)
    (fresh : declaration.constructor ∉ core.terms.map GrammarRule.label)
    (rule : GrammarRule) (member : rule ∈ (compile core declaration).terms)
    (label : rule.label = declaration.constructor) : rule = tupleRule declaration := by
  change rule ∈ core.terms ++ [tupleRule declaration] at member
  rcases List.mem_append.mp member with old | added
  · exact False.elim (fresh (List.mem_map.mpr ⟨rule, old, label⟩))
  · exact List.mem_singleton.mp added

theorem constructor_arguments_of_hasType
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {constructor : String} {arguments : List Pattern} {type : TypeExpr}
    (typed : HasType language free bound (.apply constructor arguments) type) :
    ∃ rule ∈ language.terms, rule.label = constructor ∧
      ArgumentsHaveTypes language free bound arguments rule.params := by
  cases typed with
  | constructor member notBare argumentsTyped =>
      exact ⟨_, member, rfl, argumentsTyped⟩

/-- Exact typing of the derived tuple constructor: neither missing nor extra
components can pass through the core signature. -/
theorem tuple_typing_iff (core : LanguageDef) (declaration : Declaration)
    (fresh : declaration.constructor ∉ core.terms.map GrammarRule.label)
    (free : FreeTypeContext) (bound : List TypeExpr) (arguments : List Pattern) :
    HasType (compile core declaration) free bound
        (.apply declaration.constructor arguments) (.base declaration.sort) ↔
      ComponentsTyped (compile core declaration) free bound declaration.components
        arguments := by
  constructor
  · intro typed
    obtain ⟨rule, member, label, argumentsTyped⟩ := constructor_arguments_of_hasType typed
    have same := tuple_rule_unique core declaration fresh rule member label
    subst rule
    exact (arguments_typed_iff_components _ free bound 0
      declaration.components arguments).mp argumentsTyped
  · intro components
    exact HasType.constructor (List.mem_append_right _ (List.mem_singleton_self _))
      (tuple_not_bare_collection declaration)
      ((arguments_typed_iff_components _ free bound 0
        declaration.components arguments).mpr components)

/-- The existing executable rewrite observation gains no new rule or result
occurrence from adding tuple syntax. -/
theorem rewrite_observation_exact (core : LanguageDef) (declaration : Declaration)
    (term : Pattern) :
    rewriteStep (compile core declaration) term = rewriteStep core term := rfl

/-- A support predicate on the existing pattern carrier, including application
heads that the schema constructor-reference checker treats as metasyntax. -/
def ExcludesConstructor (constructor : String) : Pattern → Prop
  | .bvar _ => True
  | .fvar _ => True
  | .apply head arguments =>
      head ≠ constructor ∧ ∀ argument ∈ arguments, ExcludesConstructor constructor argument
  | .lambda _ body => ExcludesConstructor constructor body
  | .multiLambda _ _ body => ExcludesConstructor constructor body
  | .subst body replacement =>
      ExcludesConstructor constructor body ∧ ExcludesConstructor constructor replacement
  | .collection _ elements _ =>
      ∀ element ∈ elements, ExcludesConstructor constructor element
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

mutual
  /-- Appending tuple syntax preserves every existing typing derivation. -/
  theorem typing_preserved (core : LanguageDef) (declaration : Declaration)
      {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType core free bound pattern type) :
      HasType (compile core declaration) free bound pattern type := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | constructor member notBare argumentsTyped =>
        exact .constructor (List.mem_append_left _ member) notBare
          (arguments_typing_preserved core declaration argumentsTyped)
    | lambda bodyTyped => exact .lambda (typing_preserved core declaration bodyTyped)
    | multiLambda bodyTyped => exact .multiLambda (typing_preserved core declaration bodyTyped)
    | subst bodyTyped replacementTyped =>
        exact .subst (typing_preserved core declaration bodyTyped)
          (typing_preserved core declaration replacementTyped)
    | collection elementsTyped =>
        exact .collection (elements_typing_preserved core declaration elementsTyped)
    | collectionConstructor member shape elementsTyped =>
        exact .collectionConstructor (List.mem_append_left _ member) shape
          (elements_typing_preserved core declaration elementsTyped)

  theorem arguments_typing_preserved (core : LanguageDef) (declaration : Declaration)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes core free bound arguments parameters) :
      ArgumentsHaveTypes (compile core declaration) free bound arguments parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation type argumentTyped argumentsTyped =>
        exact .cons representation type (typing_preserved core declaration argumentTyped)
          (arguments_typing_preserved core declaration argumentsTyped)

  theorem elements_typing_preserved (core : LanguageDef) (declaration : Declaration)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {type : TypeExpr}
      (typed : ElementsHaveType core free bound elements type) :
      ElementsHaveType (compile core declaration) free bound elements type := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons (typing_preserved core declaration elementTyped)
          (elements_typing_preserved core declaration elementsTyped)
end

private theorem old_rule_of_different_head (core : LanguageDef) (declaration : Declaration)
    (rule : GrammarRule) (member : rule ∈ (compile core declaration).terms)
    (different : rule.label ≠ declaration.constructor) : rule ∈ core.terms := by
  rcases List.mem_append.mp member with old | added
  · exact old
  · have same := List.mem_singleton.mp added
    subst rule
    exact False.elim (different rfl)

mutual
  /-- Tuple syntax cannot introduce a typing judgment for a term whose entire
support stays in the previous constructor vocabulary. -/
  theorem typing_reflected (core : LanguageDef) (declaration : Declaration)
      {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType (compile core declaration) free bound pattern type)
      (oldSyntax : ExcludesConstructor declaration.constructor pattern) :
      HasType core free bound pattern type := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | constructor member notBare argumentsTyped =>
        simp only [ExcludesConstructor] at oldSyntax
        exact .constructor
          (old_rule_of_different_head core declaration _ member oldSyntax.1) notBare
          (arguments_typing_reflected core declaration argumentsTyped oldSyntax.2)
    | lambda bodyTyped =>
        simp only [ExcludesConstructor] at oldSyntax
        exact .lambda (typing_reflected core declaration bodyTyped oldSyntax)
    | multiLambda bodyTyped =>
        simp only [ExcludesConstructor] at oldSyntax
        exact .multiLambda (typing_reflected core declaration bodyTyped oldSyntax)
    | subst bodyTyped replacementTyped =>
        simp only [ExcludesConstructor] at oldSyntax
        exact .subst (typing_reflected core declaration bodyTyped oldSyntax.1)
          (typing_reflected core declaration replacementTyped oldSyntax.2)
    | collection elementsTyped =>
        simp only [ExcludesConstructor] at oldSyntax
        exact .collection (elements_typing_reflected core declaration elementsTyped oldSyntax)
    | collectionConstructor member shape elementsTyped =>
        simp only [ExcludesConstructor] at oldSyntax
        rcases List.mem_append.mp member with old | added
        · exact .collectionConstructor old shape
            (elements_typing_reflected core declaration elementsTyped oldSyntax)
        · have same := List.mem_singleton.mp added
          subst_vars
          exact False.elim (tuple_not_bare_collection declaration ⟨_, _, _, shape⟩)

  theorem arguments_typing_reflected (core : LanguageDef) (declaration : Declaration)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes (compile core declaration) free bound arguments parameters)
      (oldSyntax : ∀ argument ∈ arguments, ExcludesConstructor declaration.constructor argument) :
      ArgumentsHaveTypes core free bound arguments parameters := by
    cases typed with
    | nil => exact .nil
    | cons representation type argumentTyped argumentsTyped =>
        exact .cons representation type
          (typing_reflected core declaration argumentTyped
            (oldSyntax _ List.mem_cons_self))
          (arguments_typing_reflected core declaration argumentsTyped
            (fun argument member => oldSyntax argument (List.mem_cons_of_mem _ member)))

  theorem elements_typing_reflected (core : LanguageDef) (declaration : Declaration)
      {free : FreeTypeContext} {bound : List TypeExpr}
      {elements : List Pattern} {type : TypeExpr}
      (typed : ElementsHaveType (compile core declaration) free bound elements type)
      (oldSyntax : ∀ element ∈ elements, ExcludesConstructor declaration.constructor element) :
      ElementsHaveType core free bound elements type := by
    cases typed with
    | nil => exact .nil _ _
    | cons elementTyped elementsTyped =>
        exact .cons
          (typing_reflected core declaration elementTyped
            (oldSyntax _ List.mem_cons_self))
          (elements_typing_reflected core declaration elementsTyped
            (fun element member => oldSyntax element (List.mem_cons_of_mem _ member)))
end

/-- Exact old-syntax typing conservativity; it holds even for a base with laws,
and does not substitute a validation claim for an operational one. -/
theorem old_typing_iff (core : LanguageDef) (declaration : Declaration)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (oldSyntax : ExcludesConstructor declaration.constructor pattern) :
    HasType (compile core declaration) free bound pattern type ↔
      HasType core free bound pattern type :=
  ⟨fun typed => typing_reflected core declaration typed oldSyntax,
    typing_preserved core declaration⟩

theorem parameter_sorts (index : Nat) (components : List String)
    (parameter : TermParam) (member : parameter ∈ parametersFrom index components) :
    ∃ sort ∈ components, parameter.typeExpr = .base sort := by
  induction components generalizing index with
  | nil => cases member
  | cons sort rest ih =>
      rcases List.mem_cons.mp member with head | tail
      · subst parameter
        exact ⟨sort, List.mem_cons.mpr (Or.inl rfl), rfl⟩
      · obtain ⟨component, componentMember, type⟩ := ih (index + 1) tail
        exact ⟨component, List.mem_cons.mpr (Or.inr componentMember), type⟩

theorem tuple_row_valid (core : LanguageDef) (declaration : Declaration)
    (componentsKnown : ∀ sort ∈ declaration.components, sort ∈ core.typeNames) :
    (compile core declaration).validateTerm (tupleRule declaration) = [] := by
  have resultKnown : (tupleRule declaration).category ∈
      (compile core declaration).typeNames := by
    simp [tupleRule, compile, LanguageDef.typeNames, TypeDecl.plain]
  simp only [LanguageDef.validateTerm, if_pos resultKnown, List.nil_append]
  rw [show (tupleRule declaration).syntaxPattern =
    (tupleRule declaration).params.map (fun parameter => .nonTerminal parameter.bodyName) from rfl]
  rw [LanguageDef.validateSyntaxPattern_termParameters, List.append_nil]
  rw [List.flatMap_eq_nil_iff]
  intro parameter member
  obtain ⟨sort, sortMember, type⟩ := parameter_sorts 0 declaration.components parameter member
  apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
  intro name nameMember
  rw [type] at nameMember
  have same : name = sort := by simpa [TypeExpr.baseNames] using nameMember
  subst name
  simpa [compile, LanguageDef.typeNames, TypeDecl.plain] using
    List.mem_append_left [declaration.sort] (componentsKnown sort sortMember)

/-- Fresh tuple syntax is a validated core signature over any validated inert
syntax carrier. The hypotheses do not silently assert stability of old laws. -/
theorem compile_valid_inert (core : LanguageDef) (declaration : Declaration)
    (coreValid : core.validate = [])
    (noEquations : core.equations = []) (noRewrites : core.rewrites = [])
    (sortFresh : declaration.sort ∉ core.typeNames)
    (constructorFresh : declaration.constructor ∉ core.terms.map GrammarRule.label)
    (componentsKnown : ∀ sort ∈ declaration.components, sort ∈ core.typeNames) :
    (compile core declaration).validate = [] := by
  let carrier : CalculusLanguageDef := { toLanguageDef := core }
  have compiled :
      ((ConstructorSignatureExtension.ofLists [TypeDecl.plain declaration.sort]
        [tupleRule declaration] none).apply carrier).toLanguageDef =
        compile core declaration := by
    simp [ConstructorSignatureExtension.ofLists, CalculusLanguageExtension.apply, compile, carrier]
  rw [← compiled]
  apply ConstructorSignatureExtension.apply_language_validate carrier
    [TypeDecl.plain declaration.sort] [tupleRule declaration] none
    coreValid noEquations noRewrites
  · simp
  · simpa [TypeDecl.plain] using sortFresh
  · simp
  · simpa [tupleRule] using constructorFresh
  · intro rule member
    have same := List.mem_singleton.mp member
    subst rule
    rw [compiled]
    exact tuple_row_valid core declaration componentsKnown

/-- Tuple declarations and named-substitution declarations have one composed
authoring GSLT over the unchanged base. -/
def composedLayer : CompositionalLayer LanguageDef :=
  tupleLayer.product NamedSubstitutionElaboration.namedLayer

def withFields (core : LanguageDef) (tuples : List Declaration)
    (substitutions : List NamedSubstitutionElaboration.Declaration) :
    ExtendedLanguageDef composedLayer :=
  ExtendedLanguageDef.ofProduct core tupleLayer NamedSubstitutionElaboration.namedLayer
    tuples substitutions

/-- Attaching the authoring fields retains the exact base. Executing the
tuple expansion is the separate `compile` operation above. -/
theorem withFields_core (core : LanguageDef) (tuples : List Declaration)
    (substitutions : List NamedSubstitutionElaboration.Declaration) :
    (withFields core tuples substitutions).toLanguageDef = core := rfl

theorem composed_quote_exact (core : LanguageDef) (tuples : List Declaration)
    (substitutions : List NamedSubstitutionElaboration.Declaration) :
    composedLayer.elaborate core (composedLayer.quote core (tuples, substitutions)) =
      some (tuples, substitutions) := composedLayer.elaborate_quote _ _

theorem composed_tuple_only (core : LanguageDef)
    (source : (tupleLayer.system core).authoring.theory.Term) :
    composedLayer.elaborate core [Sum.inl source] =
      (tupleLayer.elaborate core source).map
        (fun declarations => (declarations,
          (NamedSubstitutionElaboration.namedLayer.system core).emptyPayload)) :=
  tupleLayer.product_elaborates_left_only NamedSubstitutionElaboration.namedLayer core source

theorem composed_substitution_only (core : LanguageDef)
    (source : (NamedSubstitutionElaboration.namedLayer.system core).authoring.theory.Term) :
    composedLayer.elaborate core [Sum.inr source] =
      (NamedSubstitutionElaboration.namedLayer.elaborate core source).map
        (fun declarations => ((tupleLayer.system core).emptyPayload, declarations)) :=
  tupleLayer.product_elaborates_right_only NamedSubstitutionElaboration.namedLayer core source

namespace Controls

private def pair : Declaration := ⟨"Pair", "MakePair", ["A", "A"]⟩
private def carrier : CalculusLanguageDef :=
  { name := "tuple-control", types := [TypeDecl.plain "A"]
    terms := [], equations := [], rewrites := [] }

theorem repeated_component_sorts_keep_two_slots :
    (tupleRule pair).params.length = 2 := by
  exact parameters_length 0 pair.components

theorem fresh_tuple_valid : (compile carrier.toLanguageDef pair).validate = [] := by
  apply compile_valid_inert
  · apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [carrier, LanguageDef.typeNames, TypeDecl.plain]
  · rfl
  · rfl
  · simp [pair, carrier, LanguageDef.typeNames, TypeDecl.plain]
  · simp [pair, carrier]
  · intro sort member
    have same : sort = "A" := by simpa [pair] using member
    subst sort
    simp [carrier, LanguageDef.typeNames, TypeDecl.plain]

theorem missing_component_is_not_typed (free : FreeTypeContext)
    (bound : List TypeExpr) (argument : Pattern) :
    ¬ HasType (compile carrier.toLanguageDef pair) free bound
      (.apply "MakePair" [argument]) (.base "Pair") := by
  intro typed
  have components := (tuple_typing_iff carrier.toLanguageDef pair
    (by simp [pair, carrier]) free bound [argument]).mp typed
  have lengths := List.Forall₂.length_eq components
  simp [pair] at lengths

theorem two_components_are_typed (free : FreeTypeContext)
    (assigned : free "x" = some (.base "A")) :
    HasType (compile carrier.toLanguageDef pair) free []
      (.apply "MakePair" [.fvar "x", .fvar "x"]) (.base "Pair") := by
  apply (tuple_typing_iff carrier.toLanguageDef pair
    (by simp [pair, carrier]) free [] _).mpr
  exact .cons (.fvar assigned) (.cons (.fvar assigned) .nil)

private def colliding : Declaration := ⟨"A", "MakePair", ["A", "A"]⟩

theorem colliding_sort_invalid :
    (compile carrier.toLanguageDef colliding).validate ≠ [] := by
  intro valid
  have nodup := LanguageDef.typeNames_nodup_of_validate_eq_nil _ valid
  simp [compile, carrier, colliding, LanguageDef.typeNames, TypeDecl.plain] at nodup

private def constructorCollision : LanguageDef :=
  { name := "constructor-collision", types := [TypeDecl.plain "A"]
    terms := [{ label := "MakePair", category := "A", params := [], syntaxPattern := [] }]
    equations := [], rewrites := [] }

theorem colliding_constructor_invalid :
    (compile constructorCollision pair).validate ≠ [] := by
  intro valid
  have nodup := LanguageDef.constructorLabels_nodup_of_validate_eq_nil _ valid
  simp [compile, constructorCollision, pair, tupleRule] at nodup

theorem new_tuple_is_not_an_old_term (free : FreeTypeContext) (arguments : List Pattern) :
    ¬ HasType carrier.toLanguageDef free []
      (.apply "MakePair" arguments) (.base "Pair") := by
  intro typed
  obtain ⟨rule, member, _, _⟩ := constructor_arguments_of_hasType typed
  simp [carrier] at member

end Controls

#print axioms tuple_typing_iff
#print axioms old_typing_iff
#print axioms compile_valid_inert
#print axioms composed_quote_exact
#print axioms Controls.missing_component_is_not_typed
#print axioms Controls.two_components_are_typed
#print axioms Controls.colliding_sort_invalid
#print axioms Controls.colliding_constructor_invalid
#print axioms Controls.new_tuple_is_not_an_old_term
#print axioms composed_tuple_only
#print axioms composed_substitution_only

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.ProductCategoryElaboration
