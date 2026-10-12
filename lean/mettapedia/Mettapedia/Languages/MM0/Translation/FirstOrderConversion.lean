import Mettapedia.Languages.MM0.Translation.FirstOrderTyping
import Mettapedia.Languages.MM0.Kernel.Conversion
import Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversion

/-!
# Definitions of a language as MM0 definitions

Each definition of the source language compiles to an MM0 definition with
no dummy variables: the body, with its formals numbered, stored at the
source position of the defined constructor.

The source equation theory and MM0's typed conversion then agree. Two typed
first-order terms are equal in the language's equation theory exactly when
their encodings convert in the generated theory.

The conversion evidence is computed, not searched for. Unfolding one
definition is a congruence followed, at each application of the defined
constructor, by one unfolding step. Full unfolding composes the passes. Two
terms with the same full unfolding are joined through it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderConversion

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversion
open Kernel FirstOrderSyntax FirstOrderTyping

/-! ## The definition table -/

/-- The MM0 body of a constructor that a row defines: the row's body with
its formals numbered, and no dummy variables. -/
def body? (names : List String) (rows : List Row) (rule : GrammarRule) :
    Option Definition.Body := do
  let row ← rows.find? (fun row => row.head == rule.label)
  let expression ← encode names (numbered row.formals row.body)
  pure ⟨[], expression⟩

/-- The definition table of the generated theory. A defined constructor
keeps its source position. -/
def definitionSignature (source : Signature) (rows : List Row) : Definition.Signature :=
  fun index => source.language.terms[index]?.bind (body? source.names rows)

theorem definitionSignature_nil (source : Signature) (index : Nat) :
    definitionSignature source [] index = none := by
  cases position : source.language.terms[index]? <;> simp [definitionSignature, position, body?]

theorem find?_of_distinct_heads {rows : List Row}
    (distinct : rows.Pairwise (fun earlier later => earlier.head ≠ later.head)) {row : Row}
    (member : row ∈ rows) : rows.find? (fun other => other.head == row.head) = some row := by
  induction rows with
  | nil => cases member
  | cons first rest inductionHypothesis =>
    obtain ⟨firstDistinct, restDistinct⟩ := List.pairwise_cons.mp distinct
    rcases List.mem_cons.mp member with same | inRest
    · subst same
      simp
    · have differs : first.head ≠ row.head := firstDistinct row inRest
      simp [differs, inductionHypothesis restDistinct inRest]

theorem contextEncodes_of_simple {sorts : List String} {parameters : List TermParam}
    {types : List TypeExpr} (simple : SimpleParameters parameters types) :
    ∀ {context : Context}, parameters? sorts parameters = some context →
      ContextEncodes sorts types context := by
  induction simple with
  | nil =>
    intro context compiled
    simp only [parameters?, Option.some.injEq] at compiled
    subst compiled
    exact .nil
  | @cons parameter type parameters types shape _ inductionHypothesis =>
    intro context compiled
    obtain ⟨name, rfl⟩ := shape
    cases found : type? sorts type with
    | none => simp [parameters?, found] at compiled
    | some sort =>
      cases rest : parameters? sorts parameters with
      | none => simp [parameters?, found, rest] at compiled
      | some remaining =>
        have same : Binder.regular sort ∅ :: remaining = context := by
          simpa [parameters?, found, rest] using compiled
        subst same
        exact .cons ⟨sort, found, rfl⟩ (inductionHypothesis rest)

/-- What the generated theory holds for one definition: its term
declaration and its body, at the position of its head. -/
structure Compiled (source : Signature) (rows : List Row) (row : Row) (index : Nat)
    (declaration : TermDecl) (expression : Preterm) : Prop where
  name : index? source.names row.head = some index
  term : source.termSignature index = some declaration
  body : definitionSignature source rows index = some ⟨[], expression⟩
  encoded : Encodes source.names (numbered row.formals row.body) expression
  arity : declaration.arguments.length = row.formals.length
  typed : Preterm.HasType source.termSignature declaration.arguments expression []
    declaration.resultSort

/-- Every definition of a definitional language is compiled. -/
theorem compiled_exists {source : Signature} {rows : List Row}
    (definitional : DefinitionalLanguage source.language rows) {row : Row} (member : row ∈ rows) :
    ∃ index declaration expression, Compiled source rows row index declaration expression := by
  obtain ⟨rule, types, typedAt⟩ := definitional.typed row member
  have formed := definitional.acyclic.wellFormed row member
  have ruleMember := typedAt.mem
  have label := typedAt.label_eq
  obtain ⟨declaration, compiledRule⟩ := source.ordinaryConstructors rule ruleMember
  obtain ⟨parameters, result, -⟩ := declaration?_fields compiledRule
  have nameMember : rule.label ∈ source.names := List.mem_map_of_mem ruleMember
  have found : index? source.names rule.label = some (source.names.idxOf rule.label) :=
    index?_some _ _ nameMember
  have termLookup : source.termSignature (source.names.idxOf rule.label) = some declaration :=
    (source.lookup ruleMember found).trans compiledRule
  have position : source.language.terms[source.names.idxOf rule.label]? = some rule :=
    getElem?_named source.language.terms GrammarRule.label source.distinctConstructors
      ruleMember found
  have contexts : ContextEncodes source.sorts types declaration.arguments :=
    contextEncodes_of_simple typedAt.simple parameters
  have fragment : isMatchCorrectAux (numbered row.formals row.body) = true :=
    formed.schema.numbered_firstOrder formed.distinct
  have sortEncoding : type? source.sorts (.base rule.category) = some declaration.resultSort :=
    result
  obtain ⟨expression, encoded⟩ := typed_source_image typedAt.body fragment sortEncoding
  have located : rows.find? (fun other => other.head == rule.label) = some row := by
    rw [label]
    exact find?_of_distinct_heads definitional.acyclic.distinctHeads member
  refine ⟨source.names.idxOf rule.label, declaration, expression, ?_, termLookup, ?_, encoded,
    ?_, preserves_type encoded contexts typedAt.body sortEncoding⟩
  · rw [← label]
    exact found
  · simp [definitionSignature, position, body?, located, encoded.eval]
  · rw [← contexts.length_eq, typedAt.arity]

/-- A defined position of the table is a compiled definition. -/
theorem compiled_of_lookup {source : Signature} {rows : List Row}
    (definitional : DefinitionalLanguage source.language rows) {index : Nat}
    {body : Definition.Body} (lookup : definitionSignature source rows index = some body) :
    ∃ row ∈ rows, ∃ declaration expression,
      Compiled source rows row index declaration expression ∧ body = ⟨[], expression⟩ := by
  have original := lookup
  unfold definitionSignature at lookup
  cases position : source.language.terms[index]? with
  | none => simp [position] at lookup
  | some rule =>
    cases located : rows.find? (fun row => row.head == rule.label) with
    | none => simp [position, body?, located] at lookup
    | some row =>
      have member := List.mem_of_find?_eq_some located
      have head : row.head = rule.label := by simpa using List.find?_some located
      obtain ⟨other, declaration, expression, compiled⟩ := compiled_exists definitional member
      have nameLookup : source.names[index]? = some row.head := by
        simp [Signature.names, constructorNames, List.getElem?_map, position, head]
      have same : other = index := Option.some.inj
        (compiled.name.symm.trans (index?_getElem? source.distinctConstructors nameLookup))
      subst same
      exact ⟨row, member, declaration, expression, compiled,
        Option.some.inj (original.symm.trans compiled.body)⟩

/-- A constructor that no row defines has no body. -/
theorem definitionSignature_eq_none {source : Signature} {rows : List Row} {index : Nat}
    {rule : GrammarRule} (position : source.language.terms[index]? = some rule)
    (primitive : Primitive rows rule.label) : definitionSignature source rows index = none := by
  have absent : rows.find? (fun row => row.head == rule.label) = none := by
    rw [List.find?_eq_none]
    intro row member
    simpa using fun same => primitive row member same.symm
  simp [definitionSignature, position, body?, absent]

/-! ## Unfolding is instantiation -/

theorem map_applyBindings_zip {names : List String} (distinct : names.Nodup)
    {values : List Pattern} (arity : values.length = names.length) :
    names.map (fun name => applyBindings (names.zip values) (.fvar name)) = values := by
  apply List.ext_getElem?
  intro index
  rw [List.getElem?_map]
  cases nameLookup : names[index]? with
  | none =>
    have outside : values[index]? = none := by
      rw [List.getElem?_eq_none_iff] at nameLookup ⊢
      omega
    simp [outside]
  | some name =>
    have inside : index < values.length := by
      have := (List.getElem?_eq_some_iff.mp nameLookup).1
      omega
    have valueLookup : values[index]? = some values[index] := List.getElem?_eq_getElem inside
    rw [Option.map_some, valueLookup]
    exact congrArg some
      (applyBindings_fvar_of_find (find?_zip distinct nameLookup valueLookup))

/-- The defined constructor applied to arguments is the instance of the
left side at those arguments. -/
theorem applyBindings_zip_left {row : Row} (formed : row.WellFormed) {arguments : List Pattern}
    (arity : arguments.length = row.formals.length) :
    applyBindings (row.formals.zip arguments) row.left = .apply row.head arguments := by
  rw [applyBindings_left, map_applyBindings_zip formed.distinct arity]

/-- The MM0 substitution of encoded arguments into a compiled body encodes
the source instance of the body. -/
theorem Compiled.unfold_encodes {source : Signature} {rows : List Row} {row : Row}
    {index : Nat} {declaration : TermDecl} {expression : Preterm}
    (compiled : Compiled source rows row index declaration expression) (formed : row.WellFormed)
    {arguments : List Pattern} {images : List Preterm} {result : Preterm}
    (encoded : List.Forall₂ (Encodes source.names) arguments images)
    (arity : arguments.length = row.formals.length)
    (substituted : Preterm.Substitutes (Substitution.ofList images) expression result) :
    Encodes source.names (applyBindings (row.formals.zip arguments) row.body) result := by
  rw [formed.schema.instantiate_numbered formed.distinct arguments arity]
  exact compiled.encoded.substitute (argumentAt arguments) substituted
    (fun _ _ lookup => encoded_arguments_lookup encoded lookup)

/-! ## Sorts of typed terms -/

/-- A typed first-order source term has a type with an MM0 sort. -/
theorem source_sort_exists {source : Signature} {bound : List TypeExpr} {context : Context}
    (contexts : ContextEncodes source.sorts bound context) {pattern : Pattern} {type : TypeExpr}
    (typed : HasType source.language FreeTypeContext.empty bound pattern type)
    (fragment : isMatchCorrectAux pattern = true) : ∃ sort, type? source.sorts type = some sort := by
  cases typed with
  | bvar lookup =>
    obtain ⟨binder, -, sort, found, -⟩ := contexts.lookup lookup
    exact ⟨sort, found⟩
  | fvar lookup => simp [FreeTypeContext.empty] at lookup
  | @constructor _ rule _ member _ _ =>
    obtain ⟨declaration, compiledRule⟩ := source.ordinaryConstructors rule member
    exact ⟨declaration.resultSort, (declaration?_fields compiledRule).2.1⟩
  | lambda _ => simp [isMatchCorrectAux] at fragment
  | multiLambda _ => simp [isMatchCorrectAux] at fragment
  | subst _ _ => simp [isMatchCorrectAux] at fragment
  | collection _ => simp [isMatchCorrectAux] at fragment
  | collectionConstructor _ _ _ => simp [isMatchCorrectAux] at fragment

/-- The sort of a typed MM0 term over the generated signature is the sort
of a source type. -/
theorem target_type_exists {source : Signature} {bound : List TypeExpr} {context : Context}
    (contexts : ContextEncodes source.sorts bound context) {expression : Preterm} {sort : Nat}
    (typed : Preterm.HasType source.termSignature context expression [] sort) :
    ∃ type, type? source.sorts type = some sort := by
  obtain ⟨-, pattern, encoded, -⟩ := typed_encodable typed
  cases encoded with
  | boundVariable index =>
    cases typed with
    | var lookup =>
      obtain ⟨type, -, sort, found, rfl⟩ := contexts.lookup_source lookup
      exact ⟨type, found⟩
  | @constructor name index arguments images found encodedArguments =>
    obtain ⟨consumed, headTyped, -⟩ := (Preterm.HasType.applyArgs_iff _ _ _ _ _ _).mp typed
    rw [List.append_nil] at headTyped
    cases headTyped with
    | term lookup =>
      obtain ⟨rule, -, compiledRule⟩ := source.lookup_source lookup
      exact ⟨.base rule.category, (declaration?_fields compiledRule).2.1⟩

theorem encodable_arguments {source : Signature} {context formals : Context}
    {arguments : List Preterm}
    (typed : List.Forall₂ (Preterm.FitsBinder source.termSignature context) arguments formals) :
    ∃ patterns, List.Forall₂ (Encodes source.names) patterns arguments := by
  induction typed with
  | nil => exact ⟨[], .nil⟩
  | cons first _ inductionHypothesis =>
    obtain ⟨patterns, encoded⟩ := inductionHypothesis
    cases first with
    | bound _ => exact ⟨.bvar _ :: patterns, .cons (.boundVariable _) encoded⟩
    | regular typing =>
      obtain ⟨-, pattern, patternEncoded, -⟩ := typed_encodable typing
      exact ⟨pattern :: patterns, .cons patternEncoded encoded⟩

/-! ## Reflection: MM0 conversion is source equality -/

section Reflection

variable {base : BasePremiseEvaluator} {source : Signature} {rows : List Row}

/-- Every conversion of the generated theory relates the encodings of two
source terms that are equal in the language's equation theory. -/
theorem converts_reflected (definitional : DefinitionalLanguage source.language rows)
    {context : Context} {left right : Preterm} {sort : Nat}
    (converted : Converts source.termSignature (definitionSignature source rows) context
      left right sort) :
    ∃ leftPattern rightPattern, Encodes source.names leftPattern left ∧
      Encodes source.names rightPattern right ∧
      EquationEquiv base source.language leftPattern rightPattern := by
  induction converted using Converts.rec
      (motive_2 := fun lefts rights _ _ => ∃ leftPatterns rightPatterns,
        List.Forall₂ (Encodes source.names) leftPatterns lefts ∧
        List.Forall₂ (Encodes source.names) rightPatterns rights ∧
        List.Forall₂ (EquationEquiv base source.language) leftPatterns rightPatterns) with
  | refl typed =>
    obtain ⟨-, pattern, encoded, -⟩ := typed_encodable typed
    exact ⟨pattern, pattern, encoded, encoded, Relation.EqvGen.refl _⟩
  | symm _ inductionHypothesis =>
    obtain ⟨leftPattern, rightPattern, leftEncoded, rightEncoded, equivalent⟩ :=
      inductionHypothesis
    exact ⟨rightPattern, leftPattern, rightEncoded, leftEncoded,
      Relation.EqvGen.symm _ _ equivalent⟩
  | trans _ _ firstHypothesis secondHypothesis =>
    obtain ⟨leftPattern, middlePattern, leftEncoded, middleEncoded, first⟩ := firstHypothesis
    obtain ⟨otherMiddle, rightPattern, otherEncoded, rightEncoded, second⟩ := secondHypothesis
    have same := encoded_injective middleEncoded otherEncoded
    subst same
    exact ⟨leftPattern, rightPattern, leftEncoded, rightEncoded,
      Relation.EqvGen.trans _ _ _ first second⟩
  | @congruence symbol _ _ _ lookup _ inductionHypothesis =>
    obtain ⟨leftPatterns, rightPatterns, leftEncoded, rightEncoded, pointwise⟩ :=
      inductionHypothesis
    obtain ⟨rule, position, -⟩ := source.lookup_source lookup
    have nameLookup : source.names[symbol]? = some rule.label := by
      simp [Signature.names, constructorNames, List.getElem?_map, position]
    have found := index?_getElem? source.distinctConstructors nameLookup
    exact ⟨.apply rule.label leftPatterns, .apply rule.label rightPatterns,
      .constructor found leftEncoded, .constructor found rightEncoded,
      equationEquiv_apply_of_forall₂ rule.label pointwise⟩
  | unfold _ unfolded _ =>
    cases unfolded with
    | intro termLookup bodyLookup typedArguments fresh substituted =>
      obtain ⟨row, member, declaration, expression, compiled, rfl⟩ :=
        compiled_of_lookup definitional bodyLookup
      have noImages : Definition.FreshDummies _ _ [] _ := fresh
      cases noImages
      obtain ⟨patterns, encodedArguments⟩ := encodable_arguments typedArguments
      have formed := definitional.acyclic.wellFormed row member
      have sameDeclaration := Option.some.inj (compiled.term.symm.trans termLookup)
      subst sameDeclaration
      have arity : patterns.length = row.formals.length :=
        encodedArguments.length_eq.trans (typedArguments.length_eq.trans compiled.arity)
      have instanceEncoded := compiled.unfold_encodes formed encodedArguments arity
        (by simpa [Definition.substitutionValues] using substituted)
      obtain ⟨equation, authored, defines⟩ := definitional.presents.authored row member
      have related := instance_equivalent (base := base) authored defines formed
        (row.formals.zip patterns)
      rw [applyBindings_zip_left formed arity] at related
      exact ⟨.apply row.head patterns, _, .constructor compiled.name encodedArguments,
        instanceEncoded, related⟩
  | nil => exact ⟨[], [], .nil, .nil, .nil⟩
  | cons _ _ _ _ headHypothesis tailHypothesis =>
    obtain ⟨leftPattern, rightPattern, leftEncoded, rightEncoded, equivalent⟩ := headHypothesis
    obtain ⟨leftPatterns, rightPatterns, leftsEncoded, rightsEncoded, pointwise⟩ :=
      tailHypothesis
    exact ⟨leftPattern :: leftPatterns, rightPattern :: rightPatterns,
      .cons leftEncoded leftsEncoded, .cons rightEncoded rightsEncoded,
      .cons equivalent pointwise⟩

end Reflection

/-! ## Computed conversion evidence -/

mutual
/-- Evidence that a term converts to its unfolding by one definition:
congruence everywhere, and one unfolding step at each application of the
defined constructor. -/
def unfoldWitness? (names : List String) (row : Row) : Pattern → Option ConvWitness
  | .bvar index => some (.refl (.var index))
  | .apply name arguments => do
      let symbol ← index? names name
      let children ← unfoldWitnesses? names row arguments
      if name = row.head ∧ arguments.length = row.formals.length then do
        let unfolded ← encodeList names (unfoldOneList row arguments)
        pure (.trans (.congruence symbol children) (.unfold symbol unfolded []))
      else pure (.congruence symbol children)
  | .fvar _ => none
  | .lambda _ _ => none
  | .multiLambda _ _ _ => none
  | .subst _ _ => none
  | .collection _ _ _ => none

def unfoldWitnesses? (names : List String) (row : Row) : List Pattern → Option (List ConvWitness)
  | [] => some []
  | pattern :: patterns => do
      let first ← unfoldWitness? names row pattern
      let rest ← unfoldWitnesses? names row patterns
      pure (first :: rest)
end

/-- Evidence that a term converts to its full unfolding: the last definition
first. -/
def expandWitness? (names : List String) : List Row → Pattern → Option ConvWitness
  | [], pattern => (encode names pattern).map ConvWitness.refl
  | row :: rows, pattern => do
      let inner ← expandWitness? names rows pattern
      let outer ← unfoldWitness? names row (expand rows pattern)
      pure (.trans inner outer)

/-- Evidence that two terms with the same full unfolding convert: each
converts to the unfolding. -/
def conversionWitness? (names : List String) (rows : List Row) (left right : Pattern) :
    Option ConvWitness := do
  let leftWitness ← expandWitness? names rows left
  let rightWitness ← expandWitness? names rows right
  pure (.trans leftWitness (.symm rightWitness))

section Witnesses

variable {source : Signature} {rows : List Row}

mutual
  /-- The one-pass evidence is accepted, between the encoding of a typed
  term and the encoding of its unfolding. -/
  theorem unfoldWitness_checks (definitional : DefinitionalLanguage source.language rows)
      {row : Row} (member : row ∈ rows) {bound : List TypeExpr} {context : Context}
      (contexts : ContextEncodes source.sorts bound context) {pattern : Pattern}
      {type : TypeExpr} {sort : Nat}
      (typed : HasType source.language FreeTypeContext.empty bound pattern type)
      (fragment : isMatchCorrectAux pattern = true)
      (sortEncoding : type? source.sorts type = some sort) {expression : Preterm}
      (encoded : Encodes source.names pattern expression) :
      ∃ witness image, unfoldWitness? source.names row pattern = some witness ∧
        Encodes source.names (unfoldOne row pattern) image ∧
        ConvWitness.Checks source.termSignature (definitionSignature source rows) context
          witness expression image sort := by
    cases pattern with
    | bvar index =>
      cases encoded
      refine ⟨.refl (.var index), .var index, by rw [unfoldWitness?], ?_,
        .refl (preserves_type (.boundVariable index) contexts typed sortEncoding)⟩
      rw [unfoldOne_bvar]
      exact .boundVariable index
    | fvar name =>
      cases typed with
      | fvar impossible => simp [FreeTypeContext.empty] at impossible
    | apply name arguments =>
      cases typed with
      | @constructor _ rule _ ruleMember _ argumentsTyped =>
        cases encoded with
        | @constructor _ symbol _ images found encodedArguments =>
          obtain ⟨declaration, compiledRule⟩ := source.ordinaryConstructors rule ruleMember
          obtain ⟨parameters, result, -⟩ := declaration?_fields compiledRule
          have sameSort : declaration.resultSort = sort :=
            Option.some.inj (result.symm.trans sortEncoding)
          subst sameSort
          have termLookup : source.termSignature symbol = some declaration :=
            (source.lookup ruleMember found).trans compiledRule
          obtain ⟨children, unfoldedImages, childrenComputed, unfoldedEncoded, unfoldedFit,
              childrenChecked⟩ :=
            unfoldWitnesses_check definitional member contexts argumentsTyped
              (by simpa [isMatchCorrectAux] using fragment) parameters encodedArguments
          have congruence := ConvWitness.Checks.congruence termLookup childrenChecked
          by_cases saturated : rule.label = row.head ∧ arguments.length = row.formals.length
          · obtain ⟨other, otherDeclaration, body, compiled⟩ := compiled_exists definitional member
            have sameIndex : other = symbol :=
              Option.some.inj (compiled.name.symm.trans (saturated.1 ▸ found))
            subst sameIndex
            have sameDeclaration := Option.some.inj (compiled.term.symm.trans termLookup)
            subst sameDeclaration
            have formed := definitional.acyclic.wellFormed row member
            obtain ⟨unfolded, unfoldedComputed, unfoldedTyped⟩ :=
              Definition.unfold_typed_total termLookup compiled.body unfoldedFit
                (.nil unfoldedImages) (by simpa using compiled.typed)
            have unfolds := (Definition.unfold_eq_some_iff _ _ _ _ _ _ _).mp unfoldedComputed
            have substituted : Preterm.Substitutes (Substitution.ofList unfoldedImages) body
                unfolded := by
              cases unfolds with
              | intro _ bodyLookup _ _ bodySubstituted =>
                have sameBody := Option.some.inj (bodyLookup.symm.trans compiled.body)
                subst sameBody
                simpa [Definition.substitutionValues] using bodySubstituted
            have arity : (arguments.map (unfoldOne row)).length = row.formals.length := by
              simpa using saturated.2
            refine ⟨.trans (.congruence other children) (.unfold other unfoldedImages []),
              unfolded, ?_, ?_, .trans congruence (.unfold termLookup unfolds unfoldedTyped)⟩
            · rw [unfoldWitness?]
              simp [compiled.name, childrenComputed, saturated, unfoldOneList_eq_map,
                encodesList_eval unfoldedEncoded]
            · rw [unfoldOne_apply, if_pos saturated]
              exact compiled.unfold_encodes formed unfoldedEncoded arity substituted
          · refine ⟨.congruence symbol children,
              Preterm.applyArgs (.term symbol) unfoldedImages, ?_, ?_, congruence⟩
            · rw [unfoldWitness?]
              simp [found, childrenComputed, saturated]
            · rw [unfoldOne_apply, if_neg saturated]
              exact .constructor found unfoldedEncoded
    | lambda _ _ => simp [isMatchCorrectAux] at fragment
    | multiLambda _ _ _ => simp [isMatchCorrectAux] at fragment
    | subst _ _ => simp [isMatchCorrectAux] at fragment
    | collection _ _ _ => simp [isMatchCorrectAux] at fragment
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem unfoldWitnesses_check (definitional : DefinitionalLanguage source.language rows)
      {row : Row} (member : row ∈ rows) {bound : List TypeExpr} {context : Context}
      (contexts : ContextEncodes source.sorts bound context) {patterns : List Pattern}
      {parameters : List TermParam} {formals : Context}
      (typed : ArgumentsHaveTypes source.language FreeTypeContext.empty bound patterns
        parameters)
      (fragment : isMatchCorrectListAux patterns = true)
      (compiled : parameters? source.sorts parameters = some formals)
      {expressions : List Preterm}
      (encoded : List.Forall₂ (Encodes source.names) patterns expressions) :
      ∃ witnesses images, unfoldWitnesses? source.names row patterns = some witnesses ∧
        List.Forall₂ (Encodes source.names) (patterns.map (unfoldOne row)) images ∧
        List.Forall₂ (Preterm.FitsBinder source.termSignature context) images formals ∧
        ConvWitness.ChecksArgs source.termSignature (definitionSignature source rows) context
          witnesses expressions images formals := by
    cases typed with
    | nil =>
      cases encoded
      simp only [parameters?, Option.some.injEq] at compiled
      subst compiled
      exact ⟨[], [], by rw [unfoldWitnesses?], .nil, .nil, .nil⟩
    | @cons _ pattern patterns parameter parameters expected _ parameterType first rest =>
      cases encoded with
      | cons firstEncoded restEncoded =>
        have fragments : isMatchCorrectAux pattern = true ∧
            isMatchCorrectListAux patterns = true := by
          simpa [isMatchCorrectListAux] using fragment
        cases parameter with
        | simple name type =>
          simp only [parameterType?, Option.some.injEq] at parameterType
          subst expected
          cases found : type? source.sorts type with
          | none => simp [parameters?, found] at compiled
          | some sort =>
            cases remaining : parameters? source.sorts parameters with
            | none => simp [parameters?, found, remaining] at compiled
            | some target =>
              have same : Binder.regular sort ∅ :: target = formals := by
                simpa [parameters?, found, remaining] using compiled
              subst same
              obtain ⟨witness, image, computed, imageEncoded, checked⟩ :=
                unfoldWitness_checks definitional member contexts first fragments.1 found
                  firstEncoded
              obtain ⟨witnesses, images, restComputed, imagesEncoded, imagesFit, restChecked⟩ :=
                unfoldWitnesses_check definitional member contexts rest fragments.2 remaining
                  restEncoded
              refine ⟨witness :: witnesses, image :: images, ?_, .cons imageEncoded imagesEncoded,
                .cons (.regular checked.typed.2) imagesFit,
                .cons (.regular checked.typed.1) (.regular checked.typed.2) checked restChecked⟩
              rw [unfoldWitnesses?]
              simp [computed, restComputed]
        | abstractionNamed _ _ _ => simp [parameters?] at compiled
        | multiAbstractionNamed _ _ _ => simp [parameters?] at compiled
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- The evidence for full unfolding is accepted, for every list of passes
drawn from the definitions. -/
theorem expandWitness_checks (definitional : DefinitionalLanguage source.language rows)
    {bound : List TypeExpr} {context : Context}
    (contexts : ContextEncodes source.sorts bound context) {pattern : Pattern}
    {type : TypeExpr} {sort : Nat}
    (typed : HasType source.language FreeTypeContext.empty bound pattern type)
    (fragment : isMatchCorrectAux pattern = true)
    (sortEncoding : type? source.sorts type = some sort) {expression : Preterm}
    (encoded : Encodes source.names pattern expression) :
    ∀ passes : List Row, (∀ row ∈ passes, row ∈ rows) →
      ∃ witness image, expandWitness? source.names passes pattern = some witness ∧
        Encodes source.names (expand passes pattern) image ∧
        ConvWitness.Checks source.termSignature (definitionSignature source rows) context
          witness expression image sort
  | [], _ =>
      ⟨.refl expression, expression, by simp [expandWitness?, encoded.eval], encoded,
        .refl (preserves_type encoded contexts typed sortEncoding)⟩
  | row :: passes, within => by
      have later : ∀ other ∈ passes, other ∈ rows :=
        fun other otherMember => within other (List.mem_cons_of_mem _ otherMember)
      obtain ⟨inner, middle, innerComputed, middleEncoded, innerChecked⟩ :=
        expandWitness_checks definitional contexts typed fragment sortEncoding encoded passes
          later
      have middleTyped := DefinitionalEquations.hasType_expand passes
        (fun other otherMember =>
          ⟨definitional.acyclic.wellFormed other (later other otherMember),
            definitional.typed other (later other otherMember)⟩) typed
      have middleFragment := isMatchCorrect_expand passes
        (fun other otherMember => definitional.acyclic.wellFormed other (later other otherMember))
        pattern fragment
      obtain ⟨outer, image, outerComputed, imageEncoded, outerChecked⟩ :=
        unfoldWitness_checks definitional (within row (by simp)) contexts middleTyped
          middleFragment sortEncoding middleEncoded
      exact ⟨.trans inner outer, image, by simp [expandWitness?, innerComputed, outerComputed],
        by rw [expand_cons]; exact imageEncoded, .trans innerChecked outerChecked⟩

/-- **The computed evidence is accepted.** Two typed terms of one type with
the same full unfolding have accepted conversion evidence between their
encodings. -/
theorem conversionWitness_checks (definitional : DefinitionalLanguage source.language rows)
    {bound : List TypeExpr} {context : Context}
    (contexts : ContextEncodes source.sorts bound context) {left right : Pattern}
    {type : TypeExpr} {sort : Nat}
    (leftTyped : HasType source.language FreeTypeContext.empty bound left type)
    (rightTyped : HasType source.language FreeTypeContext.empty bound right type)
    (leftFragment : isMatchCorrectAux left = true)
    (rightFragment : isMatchCorrectAux right = true)
    (sortEncoding : type? source.sorts type = some sort)
    {leftExpression rightExpression : Preterm}
    (leftEncoded : Encodes source.names left leftExpression)
    (rightEncoded : Encodes source.names right rightExpression)
    (same : expand rows left = expand rows right) :
    ∃ witness, conversionWitness? source.names rows left right = some witness ∧
      ConvWitness.Checks source.termSignature (definitionSignature source rows) context witness
        leftExpression rightExpression sort := by
  obtain ⟨leftWitness, leftImage, leftComputed, leftImageEncoded, leftChecked⟩ :=
    expandWitness_checks definitional contexts leftTyped leftFragment sortEncoding leftEncoded
      rows (fun _ member => member)
  obtain ⟨rightWitness, rightImage, rightComputed, rightImageEncoded, rightChecked⟩ :=
    expandWitness_checks definitional contexts rightTyped rightFragment sortEncoding
      rightEncoded rows (fun _ member => member)
  rw [same] at leftImageEncoded
  have sameImage : leftImage = rightImage :=
    Option.some.inj (leftImageEncoded.eval.symm.trans rightImageEncoded.eval)
  subst sameImage
  exact ⟨.trans leftWitness (.symm rightWitness),
    by simp [conversionWitness?, leftComputed, rightComputed],
    .trans leftChecked (.symm rightChecked)⟩

/-- **Source equality is MM0 conversion.** Two typed first-order terms of
one type are equal in the language's equation theory exactly when their
encodings convert in the generated theory. -/
theorem converts_iff {base : BasePremiseEvaluator}
    (definitional : DefinitionalLanguage source.language rows)
    {bound : List TypeExpr} {context : Context}
    (contexts : ContextEncodes source.sorts bound context) {left right : Pattern}
    {type : TypeExpr} {sort : Nat}
    (leftTyped : HasType source.language FreeTypeContext.empty bound left type)
    (rightTyped : HasType source.language FreeTypeContext.empty bound right type)
    (leftFragment : isMatchCorrectAux left = true)
    (rightFragment : isMatchCorrectAux right = true)
    (sortEncoding : type? source.sorts type = some sort)
    {leftExpression rightExpression : Preterm}
    (leftEncoded : Encodes source.names left leftExpression)
    (rightEncoded : Encodes source.names right rightExpression) :
    EquationEquiv base source.language left right ↔
      Converts source.termSignature (definitionSignature source rows) context leftExpression
        rightExpression sort := by
  constructor
  · intro equivalent
    obtain ⟨witness, -, checked⟩ := conversionWitness_checks definitional contexts leftTyped
      rightTyped leftFragment rightFragment sortEncoding leftEncoded rightEncoded
      ((definitional.equationEquiv_iff _ _).mp equivalent)
    exact checked.derives
  · intro converted
    obtain ⟨leftPattern, rightPattern, leftDecoded, rightDecoded, equivalent⟩ :=
      converts_reflected (base := base) definitional converted
    rw [encoded_injective leftEncoded leftDecoded, encoded_injective rightEncoded rightDecoded]
    exact equivalent

end Witnesses

end Mettapedia.Languages.MM0.Translation.FirstOrderConversion
