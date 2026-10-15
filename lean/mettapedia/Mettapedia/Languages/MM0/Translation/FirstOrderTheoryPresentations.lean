import Mettapedia.Languages.MM0.Translation.FirstOrderNaming
import Mettapedia.Languages.MM0.Translation.FirstOrderAdmission

/-!
# Every first-order MM0 theory is the theory of a presentation

The translation of a presentation produces an MM0 theory. This module goes
the other way. Given a first-order MM0 theory and a name for each of its
sorts, term constructors and assertions, it reads off a language, its
definitional equations, its judgment sorts and its inference rules, proves
that they form a presentation, and proves that the theory generated from
that presentation has the term, definition and assertion tables of the
theory it was read from.

So the first-order fragment of MM0 is exactly the class of sorted
first-order rule presentations with definitions: `Presentation.theory` maps
that class into the fragment, and `sourcePresentation` is a section of it.
`derives_iff` restates derivability in the MM0 theory as derivability modulo
the definitions of the language that was read off.

The reading needs the order of the definitions, not only the finished
tables: equations are authored in the order of admission, which is the
order in which no body mentions a later constant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderTheoryPresentations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversion
open Kernel FirstOrderSyntax FirstOrderTyping FirstOrderConversion FirstOrderRules
open FirstOrderAdmission FirstOrderNaming

/-! ## Names -/

/-- The names of a development: one for each sort, each term constructor and
each assertion, at its index. -/
structure Names where
  sorts : List String
  terms : List String
  rules : List String

/-- The names fit the theory: they are distinct, and each table is declared
exactly at the indices that carry a name. -/
structure Names.Fit (names : Names) (theory : Theory) : Prop where
  distinctSorts : names.sorts.Nodup
  distinctTerms : names.terms.Nodup
  distinctRules : names.rules.Nodup
  sorts : ∀ index, theory.sortSignature index ≠ none ↔ index < names.sorts.length
  terms : ∀ index, theory.termSignature index ≠ none ↔ index < names.terms.length
  rules : ∀ index, theory.theoremSignature index ≠ none ↔ index < names.rules.length

/-! ## The source read off a theory -/

section Reading

variable (names : Names) (theory : Theory)

def sortName (sort : Nat) : String := names.sorts[sort]?.getD ""

def sortType (sort : Nat) : TypeExpr := .base (sortName names sort)

/-- The formals of a constructor, named by position. -/
def parameters : Nat → Context → List TermParam
  | _, [] => []
  | position, binder :: rest =>
      .simple (variableName position) (sortType names binder.sort) ::
        parameters (position + 1) rest

def contextTypes (context : Context) : List TypeExpr :=
  context.map fun binder => sortType names binder.sort

def constructorRule (index : Nat) (declaration : TermDecl) : GrammarRule :=
  { label := names.terms[index]?.getD ""
    category := sortName names declaration.resultSort
    params := parameters names 0 declaration.arguments
    syntaxPattern := [] }

def termDeclaration (index : Nat) : TermDecl :=
  (theory.termSignature index).getD ⟨[], 0, ∅⟩

/-- One constructor per term index, in index order. -/
def constructorRules : List GrammarRule :=
  (List.range names.terms.length).map fun index =>
    constructorRule names index (termDeclaration theory index)

/-- The source pattern of an expression. -/
def sourcePattern (expression : Preterm) : Pattern :=
  (decode names.terms expression).getD (.bvar 0)

def sourceRow (entry : Nat × Definition.Body) : Row :=
  { head := names.terms[entry.1]?.getD ""
    formals := formalNames (termDeclaration theory entry.1).arguments.length
    body := named (formalNames (termDeclaration theory entry.1).arguments.length)
      (sourcePattern names entry.2.expression) }

/-- The definitions, in the order of their admission. -/
def sourceRows : List Row := theory.definitions.reverse.map (sourceRow names theory)

def sourceEquation (row : Row) : Equation :=
  { name := row.head, typeContext := [], premises := [], left := row.left, right := row.body }

def theoremDeclaration (index : Nat) : TheoremDecl :=
  (theory.theoremSignature index).getD ⟨[], [], .var 0⟩

def sourceRule (index : Nat) (declaration : TheoremDecl) : Rule :=
  { row :=
      { id := names.rules[index]?.getD ""
        vars := formalNames declaration.arguments.length
        premises := declaration.hypotheses.map fun expression =>
          named (formalNames declaration.arguments.length) (sourcePattern names expression)
        conclusion := named (formalNames declaration.arguments.length)
          (sourcePattern names declaration.conclusion) }
    variableTypes := contextTypes names declaration.arguments }

/-- One rule per assertion index, in index order. -/
def sourceRules : List Rule :=
  (List.range names.rules.length).map fun index =>
    sourceRule names index (theoremDeclaration theory index)

/-- The names of the provable sorts. -/
def judgmentNames : List String :=
  ((List.range names.sorts.length).filter fun sort =>
    ((theory.sortSignature sort).map (·.provable)).getD false).map (sortName names)

def sourceLanguage : LanguageDef :=
  { name := "mm0"
    types := names.sorts.map TypeDecl.plain
    terms := constructorRules names theory
    equations := (sourceRows names theory).map sourceEquation
    rewrites := [] }

end Reading

/-! ## Tables by position -/

theorem range_map_getD (items : List String) :
    (List.range items.length).map (fun index => items[index]?.getD "") = items := by
  refine List.ext_getElem? fun index => ?_
  rw [List.getElem?_map]
  by_cases below : index < items.length
  · rw [List.getElem?_range below, List.getElem?_eq_getElem below]
    simp [below]
  · have beyond : items.length ≤ index := Nat.le_of_not_lt below
    have left : (List.range items.length)[index]? = none :=
      List.getElem?_eq_none (by simpa using beyond)
    have right : items[index]? = none := List.getElem?_eq_none beyond
    rw [left, right]
    rfl

theorem forall₂_map_left {α β : Type} {relation : β → α → Prop} {function : α → β} :
    ∀ items : List α, (∀ item ∈ items, relation (function item) item) →
      List.Forall₂ relation (items.map function) items
  | [], _ => .nil
  | item :: rest, every =>
      .cons (every item (by simp))
        (forall₂_map_left rest fun other member => every other (by simp [member]))

/-- A list of constructors with distinct labels has one constructor per label. -/
theorem filter_label_singleton {rules : List GrammarRule}
    (distinct : (rules.map (·.label)).Nodup) {rule : GrammarRule} (member : rule ∈ rules) :
    rules.filter (fun other => other.label == rule.label) = [rule] := by
  induction rules with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      have split : (head.label :: tail.map (·.label)).Nodup := distinct
      obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp split
      rcases List.mem_cons.mp member with same | inTail
      · subst same
        have none : tail.filter (fun other => other.label == rule.label) = [] := by
          refine List.filter_eq_nil_iff.mpr fun other otherMember same => ?_
          exact absent (List.mem_map.mpr ⟨other, otherMember, by simpa using same⟩)
        simp [none]
      · have different : head.label ≠ rule.label := fun same =>
          absent (List.mem_map.mpr ⟨rule, inTail, same.symm⟩)
        simp [different, inductionHypothesis tailDistinct inTail]

section Tables

variable (names : Names) (theory : Theory)

theorem sortNames_sourceLanguage :
    sortNames (sourceLanguage names theory) = names.sorts := by
  simp [sortNames, sourceLanguage, TypeDecl.plain, Function.comp_def]

theorem typeNames_sourceLanguage :
    (sourceLanguage names theory).typeNames = names.sorts := by
  simp [LanguageDef.typeNames, sourceLanguage, TypeDecl.plain, Function.comp_def]

theorem constructorNames_sourceLanguage :
    constructorNames (sourceLanguage names theory) = names.terms := by
  simp only [constructorNames, sourceLanguage, constructorRules, List.map_map,
    Function.comp_def, constructorRule]
  exact range_map_getD names.terms

theorem constructorRules_getElem? {index : Nat} (below : index < names.terms.length) :
    (sourceLanguage names theory).terms[index]? =
      some (constructorRule names index (termDeclaration theory index)) := by
  show ((List.range names.terms.length).map fun index =>
    constructorRule names index (termDeclaration theory index))[index]? = _
  rw [List.getElem?_map, List.getElem?_range below]
  rfl

theorem constructorRules_getElem?_none {index : Nat} (beyond : names.terms.length ≤ index) :
    (sourceLanguage names theory).terms[index]? = none := by
  show ((List.range names.terms.length).map fun index =>
    constructorRule names index (termDeclaration theory index))[index]? = _
  rw [List.getElem?_map, List.getElem?_eq_none (by simpa using beyond)]
  rfl

theorem sourceRules_ids :
    (sourceRules names theory).map (fun rule => rule.row.id) = names.rules := by
  simp only [sourceRules, List.map_map, Function.comp_def, sourceRule]
  exact range_map_getD names.rules

theorem sourceRules_getElem? {index : Nat} (below : index < names.rules.length) :
    (sourceRules names theory)[index]? =
      some (sourceRule names index (theoremDeclaration theory index)) := by
  show ((List.range names.rules.length).map fun index =>
    sourceRule names index (theoremDeclaration theory index))[index]? = _
  rw [List.getElem?_map, List.getElem?_range below]
  rfl

theorem sourceRules_getElem?_none {index : Nat} (beyond : names.rules.length ≤ index) :
    (sourceRules names theory)[index]? = none := by
  show ((List.range names.rules.length).map fun index =>
    sourceRule names index (theoremDeclaration theory index))[index]? = _
  rw [List.getElem?_map, List.getElem?_eq_none (by simpa using beyond)]
  rfl

end Tables

variable {names : Names} {theory : Theory}

theorem mem_constructorRules {rule : GrammarRule}
    (member : rule ∈ (sourceLanguage names theory).terms) :
    ∃ index, index < names.terms.length ∧
      rule = constructorRule names index (termDeclaration theory index) := by
  obtain ⟨index, inRange, same⟩ := List.mem_map.mp
    (show rule ∈ (List.range names.terms.length).map fun index =>
      constructorRule names index (termDeclaration theory index) from member)
  exact ⟨index, List.mem_range.mp inRange, same.symm⟩

theorem mem_sourceRules {rule : Rule} (member : rule ∈ sourceRules names theory) :
    ∃ index, index < names.rules.length ∧
      rule = sourceRule names index (theoremDeclaration theory index) := by
  obtain ⟨index, inRange, same⟩ := List.mem_map.mp
    (show rule ∈ (List.range names.rules.length).map fun index =>
      sourceRule names index (theoremDeclaration theory index) from member)
  exact ⟨index, List.mem_range.mp inRange, same.symm⟩

/-! ## Sorts and contexts -/

theorem sortName_mem (names : Names) {sort : Nat} (below : sort < names.sorts.length) :
    sortName names sort ∈ names.sorts := by
  have lookup : names.sorts[sort]? = some names.sorts[sort] := List.getElem?_eq_getElem below
  simp only [sortName, lookup, Option.getD_some]
  exact List.getElem_mem below

theorem index?_sortName (names : Names) (distinct : names.sorts.Nodup) {sort : Nat}
    (below : sort < names.sorts.length) :
    index? names.sorts (sortName names sort) = some sort := by
  have lookup : names.sorts[sort]? = some names.sorts[sort] := List.getElem?_eq_getElem below
  simp only [sortName, lookup, Option.getD_some]
  exact index?_getElem? distinct lookup

theorem type?_sortType (names : Names) (distinct : names.sorts.Nodup) {sort : Nat}
    (below : sort < names.sorts.length) :
    type? names.sorts (sortType names sort) = some sort := by
  simpa only [sortType, type?] using index?_sortName names distinct below

theorem contextEncodes (names : Names) (distinct : names.sorts.Nodup) :
    ∀ context : Context, Context.DependencyFree context →
      (∀ binder ∈ context, binder.sort < names.sorts.length) →
      ContextEncodes names.sorts (contextTypes names context) context
  | [], _, _ => .nil
  | binder :: rest, regular, below => by
      obtain ⟨sort, rfl⟩ := regular binder (by simp)
      exact .cons ⟨sort, type?_sortType names distinct (below (.regular sort ∅) (by simp)), rfl⟩
        (contextEncodes names distinct rest
          (fun other member => regular other (by simp [member]))
          (fun other member => below other (by simp [member])))

theorem parameters?_parameters (names : Names) (distinct : names.sorts.Nodup) :
    ∀ (context : Context) (position : Nat), Context.DependencyFree context →
      (∀ binder ∈ context, binder.sort < names.sorts.length) →
      parameters? names.sorts (parameters names position context) = some context
  | [], _, _, _ => rfl
  | binder :: rest, position, regular, below => by
      obtain ⟨sort, rfl⟩ := regular binder (by simp)
      have typed : type? names.sorts (sortType names sort) = some sort :=
        type?_sortType names distinct (below (.regular sort ∅) (by simp))
      have tail := parameters?_parameters names distinct rest (position + 1)
        (fun other member => regular other (by simp [member]))
        (fun other member => below other (by simp [member]))
      simp [parameters, parameters?, Binder.sort, typed, tail]

theorem simpleParameters (names : Names) :
    ∀ (position : Nat) (context : Context),
      SimpleParameters (parameters names position context) (contextTypes names context)
  | _, [] => List.Forall₂.nil
  | position, _ :: rest =>
      List.Forall₂.cons ⟨_, rfl⟩ (simpleParameters names (position + 1) rest)

theorem parameters_mentionsCollection (names : Names) (kind : CollType) :
    ∀ (position : Nat) (context : Context),
      ∀ parameter ∈ parameters names position context,
        (TermParam.typeExpr parameter).mentionsCollection kind = false
  | _, [], _, member => by cases member
  | position, _ :: rest, parameter, member => by
      rcases List.mem_cons.mp member with same | inRest
      · subst same
        rfl
      · exact parameters_mentionsCollection names kind (position + 1) rest parameter inRest

theorem declaration?_constructorRule (names : Names) (distinct : names.sorts.Nodup)
    (index : Nat) {declaration : TermDecl} (regular : declaration.DependencyFree)
    (below : ∀ binder ∈ declaration.arguments, binder.sort < names.sorts.length)
    (result : declaration.resultSort < names.sorts.length) :
    declaration? names.sorts (constructorRule names index declaration) = some declaration := by
  rcases declaration with ⟨arguments, resultSort, dependencies⟩
  have noDependencies : dependencies = ∅ := regular.dependencies
  subst noDependencies
  have compiled := parameters?_parameters names distinct arguments 0 regular.arguments below
  have found := index?_sortName names distinct result
  simp [declaration?, constructorRule, compiled, found]

theorem mem_judgmentNames (names : Names) {theory : Theory} {sort : Nat} {info : SortInfo}
    (below : sort < names.sorts.length) (declared : theory.sortSignature sort = some info)
    (provable : info.provable = true) : sortName names sort ∈ judgmentNames names theory :=
  List.mem_map.mpr ⟨sort,
    List.mem_filter.mpr ⟨List.mem_range.mpr below, by simp [declared, provable]⟩, rfl⟩

/-! ## What the fit and the invariant give -/

namespace Names.Fit

theorem sort_below (fit : names.Fit theory) {sort : Nat} {info : SortInfo}
    (declared : theory.sortSignature sort = some info) : sort < names.sorts.length :=
  (fit.sorts sort).mp (by simp [declared])

theorem context_below (fit : names.Fit theory) {context : Context}
    (formed : Context.WellFormed theory.sortSignature context) :
    ∀ binder ∈ context, binder.sort < names.sorts.length :=
  fun binder member =>
    (fit.sorts _).mp (Context.Extension.sortDeclared formed binder member)

theorem term_lookup (fit : names.Fit theory) {index : Nat}
    (below : index < names.terms.length) :
    theory.termSignature index = some (termDeclaration theory index) := by
  have declared := (fit.terms index).mpr below
  cases known : theory.termSignature index with
  | none => exact absurd known declared
  | some declaration => simp [termDeclaration, known]

theorem theorem_lookup (fit : names.Fit theory) {index : Nat}
    (below : index < names.rules.length) :
    theory.theoremSignature index = some (theoremDeclaration theory index) := by
  have declared := (fit.rules index).mpr below
  cases known : theory.theoremSignature index with
  | none => exact absurd known declared
  | some declaration => simp [theoremDeclaration, known]

end Names.Fit

theorem term_facts (fit : names.Fit theory) (firstOrder : theory.FirstOrder) {index : Nat}
    {declaration : TermDecl} (known : theory.termSignature index = some declaration) :
    declaration.DependencyFree ∧
      (∀ binder ∈ declaration.arguments, binder.sort < names.sorts.length) ∧
      declaration.resultSort < names.sorts.length := by
  have admissible := firstOrder.wellFormed.terms index declaration known
  obtain ⟨info, declared, -⟩ := admissible.result
  exact ⟨firstOrder.terms (index, declaration) (mem_of_lookup known),
    fit.context_below admissible.context, fit.sort_below declared⟩

theorem theorem_facts (fit : names.Fit theory) (firstOrder : theory.FirstOrder) {index : Nat}
    {declaration : TheoremDecl} (known : theory.theoremSignature index = some declaration) :
    Context.DependencyFree declaration.arguments ∧
      (∀ binder ∈ declaration.arguments, binder.sort < names.sorts.length) ∧
      TheoremDecl.Admissible theory.sortSignature theory.termSignature declaration := by
  have admissible := firstOrder.wellFormed.theorems index declaration known
  exact ⟨firstOrder.theorems (index, declaration) (mem_of_lookup known),
    fit.context_below admissible.context, admissible⟩

theorem declaration?_term (fit : names.Fit theory) (firstOrder : theory.FirstOrder)
    {index : Nat} (below : index < names.terms.length) :
    declaration? names.sorts (constructorRule names index (termDeclaration theory index)) =
      some (termDeclaration theory index) := by
  obtain ⟨regular, arguments, result⟩ := term_facts fit firstOrder (fit.term_lookup below)
  exact declaration?_constructorRule names fit.distinctSorts index regular arguments result

/-! ## The syntax signature -/

/-- The syntax signature read off a first-order theory. -/
def sourceSignature (names : Names) (theory : Theory) (fit : names.Fit theory)
    (firstOrder : theory.FirstOrder) : Signature where
  language := sourceLanguage names theory
  distinctSorts := by
    rw [sortNames_sourceLanguage]
    exact fit.distinctSorts
  distinctConstructors := by
    rw [constructorNames_sourceLanguage]
    exact fit.distinctTerms
  ordinaryConstructors := by
    intro rule member
    obtain ⟨index, below, rfl⟩ := mem_constructorRules member
    rw [sortNames_sourceLanguage]
    exact ⟨_, declaration?_term fit firstOrder below⟩

section Signature

variable (fit : names.Fit theory) (firstOrder : theory.FirstOrder)
include fit firstOrder

theorem sourceSignature_sorts :
    (sourceSignature names theory fit firstOrder).sorts = names.sorts :=
  sortNames_sourceLanguage names theory

theorem sourceSignature_names :
    (sourceSignature names theory fit firstOrder).names = names.terms :=
  constructorNames_sourceLanguage names theory

/-- The read signature declares the theory's own term constructors. -/
theorem sourceSignature_termSignature :
    (sourceSignature names theory fit firstOrder).termSignature = theory.termSignature := by
  funext index
  show (sourceLanguage names theory).terms[index]?.bind
    (declaration? (sortNames (sourceLanguage names theory))) = theory.termSignature index
  rw [sortNames_sourceLanguage]
  by_cases below : index < names.terms.length
  · rw [constructorRules_getElem? names theory below, Option.bind_some,
      declaration?_term fit firstOrder below, fit.term_lookup below]
  · rw [constructorRules_getElem?_none names theory (Nat.le_of_not_lt below)]
    have absent : theory.termSignature index = none := by
      by_contra present
      exact below ((fit.terms index).mp present)
    rw [absent]
    rfl

/-- A typed expression of the theory is the encoding of a typed source
pattern over the same context. -/
theorem typed_source {context : Context} {expression : Preterm} {sort : Nat}
    (regular : Context.DependencyFree context)
    (below : ∀ binder ∈ context, binder.sort < names.sorts.length)
    (sortBelow : sort < names.sorts.length)
    (typing : Preterm.HasType theory.termSignature context expression [] sort) :
    Encodes names.terms (sourcePattern names expression) expression ∧
      HasType (sourceLanguage names theory) FreeTypeContext.empty (contextTypes names context)
        (sourcePattern names expression) (sortType names sort) ∧
      Numbered context.length (sourcePattern names expression) := by
  have typing' : Preterm.HasType (sourceSignature names theory fit firstOrder).termSignature
      context expression [] sort := by
    rw [sourceSignature_termSignature]
    exact typing
  have contexts : ContextEncodes (sourceSignature names theory fit firstOrder).sorts
      (contextTypes names context) context := by
    rw [sourceSignature_sorts]
    exact contextEncodes names fit.distinctSorts context regular below
  have sortEncoding : type? (sourceSignature names theory fit firstOrder).sorts
      (sortType names sort) = some sort := by
    rw [sourceSignature_sorts]
    exact type?_sortType names fit.distinctSorts sortBelow
  obtain ⟨pattern, encoded, typed⟩ := typed_image contexts sortEncoding typing'
  rw [sourceSignature_names] at encoded
  have decoded : sourcePattern names expression = pattern := by
    simp [sourcePattern, encoded.decode]
  rw [decoded]
  exact ⟨encoded, typed, encodes_numbered encoded typing.varsBelow⟩

/-- A statement of the theory is a source statement at a judgment sort. -/
theorem statement_source {context : Context} {expression : Preterm}
    (regular : Context.DependencyFree context)
    (below : ∀ binder ∈ context, binder.sort < names.sorts.length)
    (statement : Preterm.IsStatement theory.sortSignature theory.termSignature context
      expression) :
    Encodes names.terms (sourcePattern names expression) expression ∧
      Statement (sourceLanguage names theory) (judgmentNames names theory)
        (contextTypes names context) (sourcePattern names expression) ∧
      Numbered context.length (sourcePattern names expression) := by
  obtain ⟨sort, info, typing, declared, provable⟩ := statement
  have sortBelow := fit.sort_below declared
  obtain ⟨encoded, typed, wellNumbered⟩ :=
    typed_source fit firstOrder regular below sortBelow typing
  exact ⟨encoded,
    ⟨sortName names sort, mem_judgmentNames names sortBelow declared provable, typed⟩,
    wellNumbered⟩

/-! ## The definitions -/

/-- What the invariant says about one entry of the definition table. -/
theorem entry_facts {entry : Nat × Definition.Body} (member : entry ∈ theory.definitions) :
    entry.1 < names.terms.length ∧ entry.2.dummies = [] ∧
      (∀ binder ∈ (termDeclaration theory entry.1).arguments,
        binder.sort < names.sorts.length) ∧
      Encodes names.terms (sourcePattern names entry.2.expression) entry.2.expression ∧
      HasType (sourceLanguage names theory) FreeTypeContext.empty
        (contextTypes names (termDeclaration theory entry.1).arguments)
        (sourcePattern names entry.2.expression)
        (sortType names (termDeclaration theory entry.1).resultSort) ∧
      Numbered (termDeclaration theory entry.1).arguments.length
        (sourcePattern names entry.2.expression) := by
  obtain ⟨noDummies, declaration, known, admitted⟩ := firstOrder.bodies entry member
  have same : termDeclaration theory entry.1 = declaration := by
    simp [termDeclaration, known]
  have below : entry.1 < names.terms.length := (fit.terms _).mp (by simp [known])
  obtain ⟨regular, arguments, result⟩ := term_facts fit firstOrder known
  have typed : Preterm.HasType theory.termSignature declaration.arguments entry.2.expression
      [] declaration.resultSort := by
    have raw := admitted.typed
    simpa only [Definition.Body.context, noDummies, List.map_nil, List.append_nil] using raw
  obtain ⟨encoded, sourceTyped, wellNumbered⟩ :=
    typed_source fit firstOrder regular.arguments arguments result typed
  rw [same]
  exact ⟨below, noDummies, arguments, encoded, sourceTyped, wellNumbered⟩

theorem sourceRow_wellFormed {entry : Nat × Definition.Body}
    (member : entry ∈ theory.definitions) : (sourceRow names theory entry).WellFormed := by
  obtain ⟨-, -, -, -, -, wellNumbered⟩ := entry_facts fit firstOrder member
  exact ⟨formalNames_nodup _,
    Numbered.named_schema (names := formalNames (termDeclaration theory entry.1).arguments.length)
      (by simpa using wellNumbered)⟩

theorem sourceRow_numbered {entry : Nat × Definition.Body}
    (member : entry ∈ theory.definitions) :
    numbered (sourceRow names theory entry).formals (sourceRow names theory entry).body =
      sourcePattern names entry.2.expression := by
  obtain ⟨-, -, -, -, -, wellNumbered⟩ := entry_facts fit firstOrder member
  exact Numbered.numbered_named (formalNames_nodup _) (by simpa using wellNumbered)

theorem sourceRow_typed {entry : Nat × Definition.Body}
    (member : entry ∈ theory.definitions) :
    (sourceRow names theory entry).Typed (sourceLanguage names theory) := by
  obtain ⟨below, -, arguments, -, sourceTyped, -⟩ := entry_facts fit firstOrder member
  refine ⟨constructorRule names entry.1 (termDeclaration theory entry.1),
    contextTypes names (termDeclaration theory entry.1).arguments, ?_⟩
  refine { declared := ?_, simple := ?_, arity := ?_, sorts := ?_, body := ?_ }
  · have inRules : constructorRule names entry.1 (termDeclaration theory entry.1) ∈
        (sourceLanguage names theory).terms :=
      List.mem_of_getElem? (constructorRules_getElem? names theory below)
    have distinct : ((sourceLanguage names theory).terms.map (·.label)).Nodup := by
      have labels := constructorNames_sourceLanguage names theory
      rw [constructorNames] at labels
      rw [labels]
      exact fit.distinctTerms
    exact filter_label_singleton distinct inRules
  · exact simpleParameters names 0 _
  · simp [contextTypes, sourceRow]
  · intro type typeMember
    obtain ⟨binder, binderMember, rfl⟩ := List.mem_map.mp
      (show type ∈ (termDeclaration theory entry.1).arguments.map
        (fun binder => sortType names binder.sort) from typeMember)
    refine ⟨sortName names binder.sort, rfl, ?_⟩
    rw [typeNames_sourceLanguage]
    exact sortName_mem names (arguments binder binderMember)
  · rw [sourceRow_numbered fit firstOrder member]
    exact sourceTyped

/-- A body that does not mention a term symbol does not mention its name. -/
theorem sourceRow_avoids {entry other : Nat × Definition.Body}
    (member : entry ∈ theory.definitions) (otherMember : other ∈ theory.definitions)
    (within : entry.2.expression.SymbolsWithin (· ≠ other.1)) :
    Avoids (sourceRow names theory other).head (sourceRow names theory entry).body := by
  obtain ⟨-, -, -, encoded, -, wellNumbered⟩ := entry_facts fit firstOrder member
  obtain ⟨otherBelow, -⟩ := entry_facts fit firstOrder otherMember
  have lookup : names.terms[other.1]? = some names.terms[other.1] :=
    List.getElem?_eq_getElem otherBelow
  have located := index?_getElem? fit.distinctTerms lookup
  have pattern : ConstructorsWithin (· ≠ names.terms[other.1])
      (sourcePattern names entry.2.expression) := by
    refine encodes_constructorsWithin ?_ encoded within
    intro name index found different same
    rw [same] at found
    exact different (Option.some.inj (found.symm.trans located))
  have head : (sourceRow names theory other).head = names.terms[other.1] := by
    simp [sourceRow, lookup]
  rw [head]
  exact wellNumbered.constructorsWithin_named pattern

theorem sourceRow_head_injective {first second : Nat × Definition.Body}
    (firstMember : first ∈ theory.definitions) (secondMember : second ∈ theory.definitions)
    (sameHead : (sourceRow names theory first).head = (sourceRow names theory second).head) :
    first.1 = second.1 := by
  obtain ⟨firstBelow, -⟩ := entry_facts fit firstOrder firstMember
  obtain ⟨secondBelow, -⟩ := entry_facts fit firstOrder secondMember
  have left : names.terms[first.1]? = some names.terms[first.1] :=
    List.getElem?_eq_getElem firstBelow
  have right : names.terms[second.1]? = some names.terms[second.1] :=
    List.getElem?_eq_getElem secondBelow
  simp only [sourceRow, left, right, Option.getD_some] at sameHead
  exact (List.Nodup.getElem_inj_iff fit.distinctTerms).mp sameHead

/-- The definitions are acyclic in the order of their admission. -/
theorem sourceRows_acyclic : Acyclic (sourceRows names theory) := by
  have members : ∀ row ∈ sourceRows names theory,
      ∃ entry ∈ theory.definitions, row = sourceRow names theory entry := by
    intro row member
    obtain ⟨entry, inReverse, same⟩ := List.mem_map.mp member
    exact ⟨entry, List.mem_reverse.mp inReverse, same.symm⟩
  refine { wellFormed := ?_, distinctHeads := ?_, ownHead := ?_, laterHeads := ?_ }
  · intro row member
    obtain ⟨entry, inDefinitions, rfl⟩ := members row member
    exact sourceRow_wellFormed fit firstOrder inDefinitions
  · show List.Pairwise _ (theory.definitions.reverse.map (sourceRow names theory))
    rw [List.pairwise_map, List.pairwise_reverse]
    have keys : theory.definitions.Pairwise (fun first second => first.1 ≠ second.1) :=
      List.pairwise_map.mp firstOrder.definitionKeys
    exact keys.imp_of_mem fun firstMember secondMember different sameHead =>
      different (sourceRow_head_injective fit firstOrder secondMember firstMember sameHead).symm
  · intro row member
    obtain ⟨entry, inDefinitions, rfl⟩ := members row member
    exact sourceRow_avoids fit firstOrder inDefinitions inDefinitions
      (firstOrder.ownSymbol entry inDefinitions)
  · show List.Pairwise _ (theory.definitions.reverse.map (sourceRow names theory))
    rw [List.pairwise_map, List.pairwise_reverse]
    exact firstOrder.laterSymbols.imp_of_mem fun laterMember earlierMember within =>
      sourceRow_avoids fit firstOrder earlierMember laterMember within

end Signature

theorem forall₂_defines (rows : List Row) :
    List.Forall₂ Defines (rows.map sourceEquation) rows :=
  forall₂_map_left rows fun _ _ => ⟨rfl, rfl, rfl⟩

/-- The definitions of the read language are the rows it was given. -/
theorem definitions_sourceLanguage (names : Names) (theory : Theory) :
    DefinitionalEquations.definitions (sourceLanguage names theory) = sourceRows names theory := by
  simp [DefinitionalEquations.definitions, sourceLanguage,
    rows?_complete (forall₂_defines (sourceRows names theory))]

theorem usesCollection_sourceLanguage (names : Names) (theory : Theory) (kind : CollType) :
    (sourceLanguage names theory).usesCollection kind = false := by
  simp only [LanguageDef.usesCollection, List.any_eq_false]
  intro rule member
  obtain ⟨index, -, rfl⟩ := mem_constructorRules member
  rw [Bool.not_eq_true]
  refine List.any_eq_false.mpr fun parameter parameterMember => ?_
  simp [parameters_mentionsCollection names kind 0 _ parameter parameterMember]

theorem hasAlgebraDeclarations_sourceLanguage (names : Names) (theory : Theory) :
    (sourceLanguage names theory).hasAlgebraDeclarations = false := by
  simp only [LanguageDef.hasAlgebraDeclarations, List.any_eq_false]
  intro rule member
  obtain ⟨index, -, rfl⟩ := mem_constructorRules member
  simp [constructorRule]

section Presentation

variable (fit : names.Fit theory) (firstOrder : theory.FirstOrder)
include fit firstOrder

/-- The read language is definitional at the read rows. -/
theorem sourceLanguage_definitional :
    DefinitionalLanguage (sourceLanguage names theory) (sourceRows names theory) :=
  { authored := forall₂_defines _
    acyclic := sourceRows_acyclic fit firstOrder
    typed := by
      intro row member
      obtain ⟨entry, inReverse, rfl⟩ := List.mem_map.mp member
      exact sourceRow_typed fit firstOrder (List.mem_reverse.mp inReverse)
    noBags := usesCollection_sourceLanguage names theory .hashBag
    noSets := usesCollection_sourceLanguage names theory .hashSet
    noAlgebra := hasAlgebraDeclarations_sourceLanguage names theory }

/-! ## The rules -/

theorem sourceRule_wellFormed {index : Nat} {declaration : TheoremDecl}
    (known : theory.theoremSignature index = some declaration) :
    (sourceRule names index declaration).WellFormed (sourceLanguage names theory)
      (judgmentNames names theory) := by
  obtain ⟨regular, below, admissible⟩ := theorem_facts fit firstOrder known
  have conclusion := statement_source fit firstOrder regular below admissible.conclusion
  have hypotheses := fun expression member =>
    statement_source fit firstOrder regular below (admissible.hypotheses expression member)
  refine { distinctNames := formalNames_nodup _, arity := ?_, declaredTypes := ?_,
           premiseSchemas := ?_, conclusionSchema := ?_, hypotheses := ?_, conclusion := ?_ }
  · simp [sourceRule, contextTypes]
  · intro type typeMember
    obtain ⟨binder, binderMember, rfl⟩ := List.mem_map.mp
      (show type ∈ declaration.arguments.map (fun binder => sortType names binder.sort)
        from typeMember)
    refine ⟨sortName names binder.sort, rfl, ?_⟩
    rw [typeNames_sourceLanguage]
    exact sortName_mem names (below binder binderMember)
  · refine schemas_of_forall _ fun pattern member => ?_
    obtain ⟨expression, expressionMember, rfl⟩ := List.mem_map.mp member
    exact Numbered.named_schema (names := formalNames declaration.arguments.length)
      (by simpa using (hypotheses expression expressionMember).2.2)
  · exact Numbered.named_schema (names := formalNames declaration.arguments.length)
      (by simpa using conclusion.2.2)
  · intro pattern member
    obtain ⟨expression, expressionMember, rfl⟩ := List.mem_map.mp member
    have facts := hypotheses expression expressionMember
    have renumbered : numbered (sourceRule names index declaration).row.vars
        (named (formalNames declaration.arguments.length) (sourcePattern names expression)) =
        sourcePattern names expression :=
      Numbered.numbered_named (formalNames_nodup _) (by simpa using facts.2.2)
    rw [renumbered]
    exact facts.2.1
  · have renumbered : numbered (sourceRule names index declaration).row.vars
        (sourceRule names index declaration).row.conclusion =
        sourcePattern names declaration.conclusion :=
      Numbered.numbered_named (formalNames_nodup _) (by simpa using conclusion.2.2)
    rw [renumbered]
    exact conclusion.2.1

/-! ## The presentation -/

/-- **The presentation of a first-order MM0 theory.** -/
def sourcePresentation (names : Names) (theory : Theory) (fit : names.Fit theory)
    (firstOrder : theory.FirstOrder) : Presentation where
  syntaxSignature := sourceSignature names theory fit firstOrder
  judgmentSorts := judgmentNames names theory
  rules := sourceRules names theory
  definitional := by
    show DefinitionalLanguage (sourceLanguage names theory)
      (DefinitionalEquations.definitions (sourceLanguage names theory))
    rw [definitions_sourceLanguage]
    exact sourceLanguage_definitional fit firstOrder
  noRewrites := rfl
  ordinaryPolicies := by
    intro entry member
    obtain ⟨index, -, rfl⟩ := mem_constructorRules member
    exact ⟨rfl, rfl⟩
  declaredJudgments := by
    intro name member
    obtain ⟨sort, inFilter, rfl⟩ := List.mem_map.mp member
    have below := List.mem_range.mp (List.mem_filter.mp inFilter).1
    show sortName names sort ∈ sortNames (sourceLanguage names theory)
    rw [sortNames_sourceLanguage]
    exact sortName_mem names below
  distinctRules := by
    rw [sourceRules_ids]
    exact fit.distinctRules
  formedRules := by
    intro rule member
    obtain ⟨index, below, rfl⟩ := mem_sourceRules member
    exact sourceRule_wellFormed fit firstOrder (fit.theorem_lookup below)

theorem sourcePresentation_rows :
    (sourcePresentation names theory fit firstOrder).rows = sourceRows names theory :=
  definitions_sourceLanguage names theory

/-! ## The generated theory is the theory that was read -/

theorem termSignature_eq :
    (sourcePresentation names theory fit firstOrder).theory.termSignature =
      theory.termSignature :=
  ((sourcePresentation names theory fit firstOrder).theory_termSignature).trans
    (sourceSignature_termSignature fit firstOrder)

theorem body?_defined {index : Nat} {body : Definition.Body}
    (member : (index, body) ∈ theory.definitions) :
    body? names.terms (sourceRows names theory)
      (constructorRule names index (termDeclaration theory index)) = some body := by
  obtain ⟨-, noDummies, -, encoded, -, -⟩ := entry_facts fit firstOrder member
  have inRows : sourceRow names theory (index, body) ∈ sourceRows names theory :=
    List.mem_map.mpr ⟨_, List.mem_reverse.mpr member, rfl⟩
  have found : (sourceRows names theory).find? (fun row => row.head ==
      (constructorRule names index (termDeclaration theory index)).label) =
      some (sourceRow names theory (index, body)) :=
    find?_of_distinct_heads (sourceRows_acyclic fit firstOrder).distinctHeads inRows
  have evaluated : encode names.terms (numbered (sourceRow names theory (index, body)).formals
      (sourceRow names theory (index, body)).body) = some body.expression := by
    rw [sourceRow_numbered fit firstOrder member]
    exact encoded.eval
  rcases body with ⟨dummies, expression⟩
  have empty : dummies = [] := noDummies
  subst empty
  simp [body?, found, evaluated]

theorem body?_undefined {index : Nat} (below : index < names.terms.length)
    (absent : theory.definitionSignature index = none) :
    body? names.terms (sourceRows names theory)
      (constructorRule names index (termDeclaration theory index)) = none := by
  have notFound : (sourceRows names theory).find? (fun row => row.head ==
      (constructorRule names index (termDeclaration theory index)).label) = none := by
    refine List.find?_eq_none.mpr fun row member same => ?_
    obtain ⟨entry, inReverse, rfl⟩ := List.mem_map.mp member
    have inDefinitions := List.mem_reverse.mp inReverse
    obtain ⟨entryBelow, -⟩ := entry_facts fit firstOrder inDefinitions
    have left : names.terms[entry.1]? = some names.terms[entry.1] :=
      List.getElem?_eq_getElem entryBelow
    have right : names.terms[index]? = some names.terms[index] :=
      List.getElem?_eq_getElem below
    have equal : names.terms[entry.1] = names.terms[index] := by
      simpa [sourceRow, constructorRule, left, right] using same
    have sameIndex : entry.1 = index :=
      (List.Nodup.getElem_inj_iff fit.distinctTerms).mp equal
    have present : theory.definitions.lookup entry.1 = some entry.2 :=
      lookup_of_mem firstOrder.definitionKeys inDefinitions
    rw [sameIndex] at present
    exact absurd (present.symm.trans absent) (by simp)
  simp [body?, notFound]

theorem definitionSignature_eq :
    (sourcePresentation names theory fit firstOrder).theory.definitionSignature =
      theory.definitionSignature := by
  rw [Presentation.theory_definitionSignature, sourcePresentation_rows]
  funext index
  show (sourceLanguage names theory).terms[index]?.bind
    (body? (constructorNames (sourceLanguage names theory)) (sourceRows names theory)) =
      theory.definitionSignature index
  rw [constructorNames_sourceLanguage]
  by_cases below : index < names.terms.length
  · rw [constructorRules_getElem? names theory below, Option.bind_some]
    cases known : theory.definitionSignature index with
    | some body => exact body?_defined fit firstOrder (mem_of_lookup known)
    | none => exact body?_undefined fit firstOrder below known
  · rw [constructorRules_getElem?_none names theory (Nat.le_of_not_lt below)]
    cases known : theory.definitionSignature index with
    | none => rfl
    | some body =>
        obtain ⟨entryBelow, -⟩ := entry_facts fit firstOrder (mem_of_lookup known)
        exact absurd entryBelow below

theorem rule?_sourceRule {index : Nat} {declaration : TheoremDecl}
    (known : theory.theoremSignature index = some declaration) :
    rule? (sourceSignature names theory fit firstOrder) (sourceRule names index declaration) =
      some declaration := by
  obtain ⟨regular, below, admissible⟩ := theorem_facts fit firstOrder known
  refine (rule?_eq_some_iff _ _ _).mpr ⟨?_, ?_, ?_⟩
  · rw [sourceSignature_sorts]
    exact contextEncodes names fit.distinctSorts _ regular below
  · rw [sourceSignature_names]
    show List.Forall₂ (Encodes names.terms)
      ((declaration.hypotheses.map fun expression =>
        named (formalNames declaration.arguments.length) (sourcePattern names expression)).map
          (numbered (formalNames declaration.arguments.length))) declaration.hypotheses
    rw [List.map_map]
    refine forall₂_map_left _ fun expression member => ?_
    have facts := statement_source fit firstOrder regular below
      (admissible.hypotheses expression member)
    show Encodes names.terms (numbered (formalNames declaration.arguments.length)
      (named (formalNames declaration.arguments.length) (sourcePattern names expression)))
      expression
    rw [Numbered.numbered_named (formalNames_nodup _) (by simpa using facts.2.2)]
    exact facts.1
  · rw [sourceSignature_names]
    have facts := statement_source fit firstOrder regular below admissible.conclusion
    show Encodes names.terms (numbered (formalNames declaration.arguments.length)
      (named (formalNames declaration.arguments.length)
        (sourcePattern names declaration.conclusion))) declaration.conclusion
    rw [Numbered.numbered_named (formalNames_nodup _) (by simpa using facts.2.2)]
    exact facts.1

theorem theoremSignature_eq :
    (sourcePresentation names theory fit firstOrder).theory.theoremSignature =
      theory.theoremSignature := by
  funext index
  rw [Presentation.theory_theoremSignature]
  show (sourceRules names theory)[index]?.bind
    (rule? (sourceSignature names theory fit firstOrder)) = theory.theoremSignature index
  by_cases below : index < names.rules.length
  · rw [sourceRules_getElem? names theory below, Option.bind_some,
      rule?_sourceRule fit firstOrder (fit.theorem_lookup below), fit.theorem_lookup below]
  · rw [sourceRules_getElem?_none names theory (Nat.le_of_not_lt below)]
    have absent : theory.theoremSignature index = none := by
      by_contra present
      exact below ((fit.rules index).mp present)
    rw [absent]
    rfl

/-- The generated theory has the theory's sorts, with the same provable
ones. The other sort modifiers of MM0 restrict what may be declared; a
first-order theory declares nothing they could refuse. -/
theorem sortSignature_provable (index : Nat) :
    ((sourcePresentation names theory fit firstOrder).theory.sortSignature index).map
        (·.provable) = (theory.sortSignature index).map (·.provable) := by
  rw [Presentation.theory_sortSignature]
  show ((sortNames (sourceLanguage names theory))[index]?.map
    (sourcePresentation names theory fit firstOrder).sortInfo).map (·.provable) = _
  rw [sortNames_sourceLanguage]
  by_cases below : index < names.sorts.length
  · have lookup : names.sorts[index]? = some names.sorts[index] :=
      List.getElem?_eq_getElem below
    have declared := (fit.sorts index).mpr below
    cases known : theory.sortSignature index with
    | none => exact absurd known declared
    | some info =>
        have membership : names.sorts[index] ∈ judgmentNames names theory ↔
            info.provable = true := by
          constructor
          · intro member
            obtain ⟨sort, inFilter, same⟩ := List.mem_map.mp member
            obtain ⟨inRange, provable⟩ := List.mem_filter.mp inFilter
            have sortBelow := List.mem_range.mp inRange
            have sortLookup : names.sorts[sort]? = some names.sorts[sort] :=
              List.getElem?_eq_getElem sortBelow
            have equal : names.sorts[sort] = names.sorts[index] := by
              simpa [sortName, sortLookup] using same
            have sameIndex : sort = index :=
              (List.Nodup.getElem_inj_iff fit.distinctSorts).mp equal
            subst sameIndex
            simpa [known] using provable
          · intro provable
            have member := mem_judgmentNames names below known provable
            simpa [sortName, lookup] using member
        have flag : decide (names.sorts[index] ∈ judgmentNames names theory) =
            info.provable := by
          by_cases provable : info.provable = true
          · rw [provable]
            exact decide_eq_true (membership.mpr provable)
          · have off : info.provable = false := by simpa using provable
            rw [off]
            exact decide_eq_false fun member => provable (membership.mp member)
        rw [lookup]
        show (some (decide (names.sorts[index] ∈ judgmentNames names theory)) : Option Bool) =
          some info.provable
        rw [flag]
  · have beyond := Nat.le_of_not_lt below
    have absent : theory.sortSignature index = none := by
      by_contra present
      exact below ((fit.sorts index).mp present)
    rw [List.getElem?_eq_none beyond, absent]
    rfl

/-- **Every first-order MM0 theory is the theory of a presentation.** The
theory generated from the presentation read off a first-order theory has
that theory's term constructors, definitions and assertions, and its sorts
with the same provable ones. -/
theorem theory_sourcePresentation :
    (sourcePresentation names theory fit firstOrder).theory.termSignature =
        theory.termSignature ∧
      (sourcePresentation names theory fit firstOrder).theory.definitionSignature =
        theory.definitionSignature ∧
      (sourcePresentation names theory fit firstOrder).theory.theoremSignature =
        theory.theoremSignature ∧
      ∀ index,
        ((sourcePresentation names theory fit firstOrder).theory.sortSignature index).map
          (·.provable) = (theory.sortSignature index).map (·.provable) :=
  ⟨termSignature_eq fit firstOrder, definitionSignature_eq fit firstOrder,
    theoremSignature_eq fit firstOrder, sortSignature_provable fit firstOrder⟩

/-- **Derivability in a first-order MM0 theory is derivability modulo the
definitions of its presentation.** The statement is about the theory's own
tables: no translated copy of them appears. -/
theorem derives_iff {base : BasePremiseEvaluator} {bound : List TypeExpr} {context : Context}
    {hypotheses : List Pattern} {targetHypotheses : List Preterm} {pattern : Pattern}
    {expression : Preterm}
    (contexts : ContextEncodes names.sorts bound context)
    (localScope : List.Forall₂ (Encodes names.terms) hypotheses targetHypotheses)
    (encoded : Encodes names.terms pattern expression) :
    DerivesModulo base (sourceLanguage names theory) (sourceRules names theory) bound
      hypotheses pattern ↔
    Kernel.Derives theory.termSignature theory.definitionSignature theory.theoremSignature
      context targetHypotheses expression := by
  have transported := Presentation.derivability_iff (base := base)
    (presentation := sourcePresentation names theory fit firstOrder)
    (bound := bound) (context := context) (hypotheses := hypotheses)
    (targetHypotheses := targetHypotheses) (pattern := pattern) (expression := expression)
    (by rw [show (sourcePresentation names theory fit firstOrder).syntaxSignature.sorts =
          names.sorts from sourceSignature_sorts fit firstOrder]
        exact contexts)
    (by rw [show (sourcePresentation names theory fit firstOrder).syntaxSignature.names =
          names.terms from sourceSignature_names fit firstOrder]
        exact localScope)
    (by rw [show (sourcePresentation names theory fit firstOrder).syntaxSignature.names =
          names.terms from sourceSignature_names fit firstOrder]
        exact encoded)
  rw [termSignature_eq, definitionSignature_eq, theoremSignature_eq] at transported
  exact transported

end Presentation

end Mettapedia.Languages.MM0.Translation.FirstOrderTheoryPresentations
