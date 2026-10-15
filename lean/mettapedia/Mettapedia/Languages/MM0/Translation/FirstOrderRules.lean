import Mettapedia.Languages.MM0.Translation.FirstOrderConversion
import Mettapedia.GSLT.LanguageDef.SortedFirstOrderAdmission
import Mettapedia.GSLT.LanguageDef.DefinitionalAdmission
import Mettapedia.Languages.MM0.Kernel.TheoryAdmission
import Mettapedia.Languages.MM0.Kernel.ProofChecking
import Mettapedia.Data.List.FiniteLookup

/-!
# Compiling many-sorted inference rules to MM0 axioms

Named rule parameters are numbered in their authored order. Premise order
and constructor names are retained by the source presentation; the target
contains the actual MM0 declarations and application spines. Every argument
is checked against its declared source sort before a rule is instantiated.
The translation uses the existing named-schema and MM0 substitution actions.
Every admitted row compiles to a formed MM0 axiom.

The equations of the source language are its definitions. Each compiles to
an MM0 definition, and source derivations are read modulo the language's
equation theory. `derivability_iff` proves preservation and reflection for
the complete finite generated theory, including open local assumptions and
conversion steps; `derivability_iff_checked` uses the existing MM0
certificate checker. A language without equations is the case with no
definitions, where conversion steps change nothing:
`derivability_iff_of_equationFree`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversion
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Kernel FirstOrderSyntax FirstOrderTyping FirstOrderConversion

/-- Compile the full declaration, without dropping any premise or formal. -/
def rule? (source : Signature) (rule : Rule) : Option TheoremDecl := do
  let arguments ← context? source.sorts rule.variableTypes
  let hypotheses ← encodeList source.names (rule.row.premises.map (numbered rule.row.vars))
  let conclusion ← encode source.names (numbered rule.row.vars rule.row.conclusion)
  pure ⟨arguments, hypotheses, conclusion⟩

/-- Structural graph of a successful rule translation. -/
structure Compiles (source : Signature) (rule : Rule) (declaration : TheoremDecl) : Prop where
  contexts : ContextEncodes source.sorts rule.variableTypes declaration.arguments
  hypotheses : List.Forall₂ (Encodes source.names)
    (rule.row.premises.map (numbered rule.row.vars)) declaration.hypotheses
  conclusion : Encodes source.names (numbered rule.row.vars rule.row.conclusion) declaration.conclusion

theorem rule?_eq_some_iff (source : Signature) (rule : Rule) (declaration : TheoremDecl) :
    rule? source rule = some declaration ↔ Compiles source rule declaration := by
  constructor
  · intro compiled
    cases arguments : context? source.sorts rule.variableTypes with
    | none => simp [rule?, arguments] at compiled
    | some argumentsValue =>
        cases hypotheses : encodeList source.names (rule.row.premises.map (numbered rule.row.vars)) with
        | none => simp [rule?, arguments, hypotheses] at compiled
        | some hypothesesValue =>
            cases conclusion : encode source.names (numbered rule.row.vars rule.row.conclusion) with
            | none => simp [rule?, arguments, hypotheses, conclusion] at compiled
            | some conclusionValue =>
                have same : (⟨argumentsValue, hypothesesValue, conclusionValue⟩ : TheoremDecl) =
                    declaration := by simpa [rule?, arguments, hypotheses, conclusion] using compiled
                subst declaration
                exact ⟨(context?_eq_some_iff _ _ _).mp arguments,
                  encodeList_sound hypotheses, encode_sound conclusion⟩
  · intro compiled
    simp [rule?, (context?_eq_some_iff _ _ _).mpr compiled.contexts,
      encodesList_eval compiled.hypotheses, compiled.conclusion.eval]

/-- Separate compilation before and after a join changes only global references. -/
theorem Compiles.relocate {originalSource joinedSource : Signature} {rule : Rule}
    {original image : TheoremDecl}
    (before : Compiles originalSource rule original)
    (after : Compiles joinedSource rule image) :
    original.relocate? (references? originalSource.sorts joinedSource.sorts)
      (references? originalSource.names joinedSource.names) = some image := by
  simp [TheoremDecl.relocate?, before.contexts.relocate after.contexts,
    encodesList_relocate_eval before.hypotheses after.hypotheses,
    before.conclusion.relocate after.conclusion]

/-- A target axiom instance has exactly the source premises and conclusion. -/
theorem Compiles.instance_encodes {source : Signature} {judgmentSorts : List String}
    {rule : Rule} {declaration : TheoremDecl}
    (compiled : Compiles source rule declaration)
    (formed : rule.WellFormed source.language judgmentSorts)
    {context : Context} {patterns : List Pattern} {expressions : List Preterm}
    {instantiation : TheoremInstance}
    (encoded : List.Forall₂ (Encodes source.names) patterns expressions)
    (arity : patterns.length = rule.row.vars.length)
    (instantiated : TheoremDecl.Instantiates source.termSignature context declaration expressions instantiation) :
    List.Forall₂ (Encodes source.names) (rule.row.instPremises patterns) instantiation.hypotheses ∧
      Encodes source.names (rule.row.instConclusion patterns) instantiation.conclusion := by
  have images := fun index image lookup => encoded_arguments_lookup encoded (index := index)
    (image := image) lookup
  constructor
  · rw [formed.instPremises_numbered patterns arity]
    exact encodesList_substitute (argumentAt patterns) compiled.hypotheses instantiated.hypotheses images
  · rw [formed.instConclusion_numbered patterns arity]
    exact compiled.conclusion.substitute (argumentAt patterns) instantiated.conclusion images

theorem encodesList_left_member {names : List String} {patterns : List Pattern} {expressions : List Preterm}
    (encoded : List.Forall₂ (Encodes names) patterns expressions) {pattern : Pattern}
    (member : pattern ∈ patterns) :
    ∃ expression, expression ∈ expressions ∧ Encodes names pattern expression := by
  induction encoded with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | restMember
      · exact ⟨_, by simp, first⟩
      · obtain ⟨expression, member, encoding⟩ := ih restMember
        exact ⟨expression, List.mem_cons_of_mem _ member, encoding⟩

theorem encodesList_right_member {names : List String} {patterns : List Pattern} {expressions : List Preterm}
    (encoded : List.Forall₂ (Encodes names) patterns expressions) {expression : Preterm}
    (member : expression ∈ expressions) :
    ∃ pattern, pattern ∈ patterns ∧ Encodes names pattern expression := by
  induction encoded with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | restMember
      · exact ⟨_, by simp, first⟩
      · obtain ⟨pattern, member, encoding⟩ := ih restMember
        exact ⟨pattern, List.mem_cons_of_mem _ member, encoding⟩

/-- Complete admitted source data for the first-order backend. The
equations of the language are its definitions; a language without equations
has none. -/
structure Presentation where
  syntaxSignature : Signature
  judgmentSorts : List String
  rules : List Rule
  definitional : DefinitionalLanguage syntaxSignature.language
    (DefinitionalEquations.definitions syntaxSignature.language)
  noRewrites : syntaxSignature.language.rewrites = []
  ordinaryPolicies : ∀ constructor ∈ syntaxSignature.language.terms,
    constructor.evalPolicy? = none ∧ constructor.algebra? = none
  declaredJudgments : ∀ name ∈ judgmentSorts, name ∈ syntaxSignature.sorts
  distinctRules : (rules.map (fun rule => rule.row.id)).Nodup
  formedRules : ∀ rule ∈ rules, rule.WellFormed syntaxSignature.language judgmentSorts

namespace Presentation

/-- The definitions of the presentation, in authored order. -/
def rows (presentation : Presentation) : List Row :=
  DefinitionalEquations.definitions presentation.syntaxSignature.language

/-- The presentation's language is definitional at its rows. -/
theorem definitionalRows (presentation : Presentation) :
    DefinitionalLanguage presentation.syntaxSignature.language presentation.rows :=
  presentation.definitional

/-- Structural and semantic admission, after the ordinary syntax signature check. -/
def checkBody (language : LanguageDef) (judgments : List String) (rules : List Rule) : Bool :=
  checkDefinitional language && decide (language.rewrites = []) &&
    language.terms.all (fun constructor =>
      decide (constructor.evalPolicy? = none ∧ constructor.algebra? = none)) &&
    judgments.all (fun sortName => (sortNames language).contains sortName) &&
    decide (rules.map (fun rule => rule.row.id)).Nodup &&
    rules.all (fun rule => rule.check language judgments)

theorem checkBody_iff (language : LanguageDef) (judgments : List String) (rules : List Rule) :
    checkBody language judgments rules = true ↔
      DefinitionalLanguage language (DefinitionalEquations.definitions language) ∧
      language.rewrites = [] ∧
      (∀ constructor ∈ language.terms,
        constructor.evalPolicy? = none ∧ constructor.algebra? = none) ∧
      (∀ sortName ∈ judgments, sortName ∈ sortNames language) ∧
      (rules.map (fun rule => rule.row.id)).Nodup ∧
      (∀ rule ∈ rules, rule.WellFormed language judgments) := by
  simp only [checkBody, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem, Rule.check_iff, checkDefinitional_iff_definitions]
  tauto

def check (language : LanguageDef) (judgments : List String) (rules : List Rule) : Bool :=
  Signature.check language && checkBody language judgments rules

/-- Construct all proof fields from executable admission of the authored data. -/
def admit? (language : LanguageDef) (judgments : List String) (rules : List Rule) :
    Option Presentation :=
  match signatureCheck : Signature.admit? language with
  | none => none
  | some signature =>
      if admitted : checkBody language judgments rules = true then
        let checked := (checkBody_iff language judgments rules).mp admitted
        let retained := Signature.admit?_language signatureCheck
        some {
          syntaxSignature := signature
          judgmentSorts := judgments
          rules := rules
          definitional := by simpa only [retained] using checked.1
          noRewrites := by simpa only [retained] using checked.2.1
          ordinaryPolicies := by simpa only [retained] using checked.2.2.1
          declaredJudgments := by
            simpa only [Signature.sorts, retained] using checked.2.2.2.1
          distinctRules := checked.2.2.2.2.1
          formedRules := by simpa only [retained] using checked.2.2.2.2.2 }
      else none

theorem admit?_isSome_iff (language : LanguageDef) (judgments : List String) (rules : List Rule) :
    (admit? language judgments rules).isSome = true ↔ check language judgments rules = true := by
  unfold admit?
  split
  next found =>
      have refused : Signature.check language = false := by
        have := Signature.admit?_isSome_iff language
        simp only [found, Option.isSome_none, Bool.false_eq_true, false_iff] at this
        exact Bool.eq_false_iff.mpr this
      simp [check, refused]
  next signature found =>
      have accepted : Signature.check language = true :=
        (Signature.admit?_isSome_iff language).mp (by simp [found])
      by_cases admitted : checkBody language judgments rules = true <;>
        simp [check, accepted, admitted]

theorem admit?_retains {language : LanguageDef} {judgments : List String} {rules : List Rule}
    {source : Presentation} (admitted : admit? language judgments rules = some source) :
    source.syntaxSignature.language = language ∧ source.judgmentSorts = judgments ∧
      source.rules = rules := by
  unfold admit? at admitted
  split at admitted
  · contradiction
  · split at admitted
    · cases admitted
      exact ⟨Signature.admit?_language (by assumption), rfl, rfl⟩
    · contradiction

def sortInfo (presentation : Presentation) (name : String) : SortInfo :=
  { strict := true, provable := decide (name ∈ presentation.judgmentSorts) }

/-- Real MM0 tables. Compilation keeps the source position of each row. -/
def theory (presentation : Presentation) : Theory where
  sorts := List.compileIndexed (fun name => some (presentation.sortInfo name))
    presentation.syntaxSignature.sorts
  terms := List.compileIndexed (declaration? presentation.syntaxSignature.sorts)
    presentation.syntaxSignature.language.terms
  definitions := List.compileIndexed
    (body? presentation.syntaxSignature.names presentation.rows)
    presentation.syntaxSignature.language.terms
  theorems := List.compileIndexed (rule? presentation.syntaxSignature) presentation.rules

theorem theory_sortSignature (presentation : Presentation) (index : Nat) :
    presentation.theory.sortSignature index =
      (presentation.syntaxSignature.sorts[index]?).map presentation.sortInfo := by
  simp only [theory, Theory.sortSignature, List.lookup_compileIndexed_zero]
  cases presentation.syntaxSignature.sorts[index]? <;> rfl

theorem theory_termSignature (presentation : Presentation) :
    presentation.theory.termSignature = presentation.syntaxSignature.termSignature := by
  funext index
  simp only [theory, Theory.termSignature, List.lookup_compileIndexed_zero,
    Signature.termSignature]
  rfl

/-- The definition table of the generated theory is the compiled table of
the presentation's definitions. -/
theorem theory_definitionSignature (presentation : Presentation) :
    presentation.theory.definitionSignature =
      definitionSignature presentation.syntaxSignature presentation.rows := by
  funext index
  exact List.lookup_compileIndexed_zero _ _ _

/-- The source language generates no equations when it authors none. -/
theorem isEquationFree (presentation : Presentation)
    (equationFree : presentation.syntaxSignature.language.equations = []) :
    presentation.syntaxSignature.language.isEquationFree = true := by
  simp [LanguageDef.isEquationFree, equationFree, presentation.definitional.noBags,
    presentation.definitional.noSets, presentation.definitional.noAlgebra]

/-- Without equations there are no definitions. -/
theorem rows_eq_nil (presentation : Presentation)
    (equationFree : presentation.syntaxSignature.language.equations = []) :
    presentation.rows = [] := by
  simp [rows, DefinitionalEquations.definitions, equationFree, rows?]

/-- Without equations the generated theory has no definition bodies. -/
theorem theory_definitionSignature_eq_none (presentation : Presentation)
    (equationFree : presentation.syntaxSignature.language.equations = []) (index : Nat) :
    presentation.theory.definitionSignature index = none := by
  rw [presentation.theory_definitionSignature, presentation.rows_eq_nil equationFree]
  exact definitionSignature_nil _ index

theorem theory_theoremSignature (presentation : Presentation) (index : Nat) :
    presentation.theory.theoremSignature index =
      presentation.rules[index]?.bind (rule? presentation.syntaxSignature) := by
  exact List.lookup_compileIndexed_zero _ _ _

theorem statement_preserved {presentation : Presentation} {types : List TypeExpr}
    {context : Context} {pattern : Pattern} {expression : Preterm}
    (contexts : ContextEncodes presentation.syntaxSignature.sorts types context)
    (encoded : Encodes presentation.syntaxSignature.names pattern expression)
    (statement : Statement presentation.syntaxSignature.language presentation.judgmentSorts types pattern) :
    Preterm.IsStatement presentation.theory.sortSignature presentation.syntaxSignature.termSignature
      context expression := by
  obtain ⟨name, judgment, typed⟩ := statement
  have declared := presentation.declaredJudgments name judgment
  have found := index?_some presentation.syntaxSignature.sorts name declared
  refine ⟨presentation.syntaxSignature.sorts.idxOf name, presentation.sortInfo name,
    preserves_type encoded contexts typed found, ?_, ?_⟩
  · rw [presentation.theory_sortSignature, getElem?_index? found]
    rfl
  · simp [sortInfo, judgment]

theorem context_wellFormed {presentation : Presentation} {types : List TypeExpr} {context : Context}
    (contexts : ContextEncodes presentation.syntaxSignature.sorts types context) :
    Context.WellFormed presentation.theory.sortSignature context := by
  have extension : ∀ initial, Context.Extension presentation.theory.sortSignature initial context := by
    induction contexts with
    | nil => exact fun initial => .nil initial
    | @cons type binder types context first rest ih =>
        obtain ⟨sort, typeEncoding, rfl⟩ := first
        cases type with
        | base name =>
            have found := getElem?_index? typeEncoding
            have known : presentation.theory.sortSignature sort =
                some (presentation.sortInfo name) := by
              rw [presentation.theory_sortSignature, found]
              rfl
            intro initial
            exact .cons (.regular known (by simp)) (ih _)
        | _ => simp [type?] at typeEncoding
  exact extension []

theorem compiled_admitted {presentation : Presentation} {rule : Rule} {declaration : TheoremDecl}
    (compiled : Compiles presentation.syntaxSignature rule declaration)
    (formed : rule.WellFormed presentation.syntaxSignature.language presentation.judgmentSorts) :
    TheoremDecl.Admissible presentation.theory.sortSignature
      presentation.syntaxSignature.termSignature declaration := by
  refine ⟨context_wellFormed compiled.contexts, ?_,
    statement_preserved compiled.contexts compiled.conclusion formed.conclusion⟩
  have statements : ∀ pattern ∈ rule.row.premises.map (numbered rule.row.vars),
      Statement presentation.syntaxSignature.language presentation.judgmentSorts
        rule.variableTypes pattern := by
    intro pattern patternMember
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp patternMember
    exact formed.hypotheses original originalMember
  have preserveStatements : ∀ (patterns : List Pattern) (expressions : List Preterm),
      List.Forall₂ (Encodes presentation.syntaxSignature.names) patterns expressions →
      (∀ pattern ∈ patterns, Statement presentation.syntaxSignature.language
        presentation.judgmentSorts rule.variableTypes pattern) →
      ∀ expression ∈ expressions, Preterm.IsStatement presentation.theory.sortSignature
        presentation.syntaxSignature.termSignature declaration.arguments expression := by
    intro patterns expressions encoded
    induction encoded with
    | nil => simp
    | @cons pattern expression patterns expressions first rest ih =>
        intro sourceStatements result resultMember
        rcases List.mem_cons.mp resultMember with rfl | restMember
        · exact statement_preserved compiled.contexts first (sourceStatements pattern (by simp))
        · exact ih (fun pattern patternMember =>
            sourceStatements pattern (List.mem_cons_of_mem _ patternMember)) result restMember
  exact preserveStatements _ _ compiled.hypotheses statements

private theorem declared_context_exists (source : Signature) (types : List TypeExpr)
    (declared : ∀ type ∈ types, ∃ name, type = .base name ∧ name ∈ source.sorts) :
    ∃ context, ContextEncodes source.sorts types context := by
  induction types with
  | nil => exact ⟨[], .nil⟩
  | cons first rest ih =>
      obtain ⟨name, rfl, member⟩ := declared first (by simp)
      obtain ⟨context, encoded⟩ :=
        ih (fun type member => declared type (List.mem_cons_of_mem _ member))
      exact ⟨.regular (source.sorts.idxOf name) ∅ :: context,
        .cons ⟨_, index?_some _ _ member, rfl⟩ encoded⟩

private theorem encode_list_total (names : List String) (patterns : List Pattern)
    (total : ∀ pattern ∈ patterns, ∃ expression, Encodes names pattern expression) :
    ∃ expressions, List.Forall₂ (Encodes names) patterns expressions := by
  induction patterns with
  | nil => exact ⟨[], .nil⟩
  | cons first rest ih =>
      obtain ⟨expression, firstEncoded⟩ := total first (by simp)
      obtain ⟨expressions, restEncoded⟩ :=
        ih (fun pattern member => total pattern (List.mem_cons_of_mem _ member))
      exact ⟨expression :: expressions, .cons firstEncoded restEncoded⟩

/-- Every admitted source rule compiles; no rule disappears from the target theory. -/
theorem rule_compiles (presentation : Presentation) {rule : Rule} (member : rule ∈ presentation.rules) :
    ∃ declaration, Compiles presentation.syntaxSignature rule declaration := by
  have formed := presentation.formedRules rule member
  obtain ⟨context, contexts⟩ := declared_context_exists presentation.syntaxSignature rule.variableTypes
    formed.declaredTypes
  have encodeStatement : ∀ pattern,
      isMatchCorrectAux pattern = true →
      Statement presentation.syntaxSignature.language presentation.judgmentSorts rule.variableTypes pattern →
      ∃ expression, Encodes presentation.syntaxSignature.names pattern expression := by
    intro pattern fragment statement
    obtain ⟨name, judgment, typed⟩ := statement
    exact typed_source_image typed fragment (index?_some _ _
      (presentation.declaredJudgments name judgment))
  obtain ⟨conclusion, conclusionEncoded⟩ := encodeStatement _
    (formed.conclusionSchema.numbered_firstOrder formed.distinctNames) formed.conclusion
  obtain ⟨hypotheses, hypothesesEncoded⟩ := encode_list_total presentation.syntaxSignature.names
    (rule.row.premises.map (numbered rule.row.vars)) (by
      intro pattern patternMember
      have fragment := (SortedFirstOrderConversion.isMatchCorrectList_iff _).mp
        (formed.premiseSchemas.numbered_firstOrder formed.distinctNames) pattern patternMember
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp patternMember
      exact encodeStatement _ fragment (formed.hypotheses original originalMember))
  exact ⟨⟨context, hypotheses, conclusion⟩, contexts, hypothesesEncoded, conclusionEncoded⟩

theorem rule_lookup (presentation : Presentation) {rule : Rule} (member : rule ∈ presentation.rules)
    {index : Nat} (found : index? (presentation.rules.map (fun rule => rule.row.id)) rule.row.id = some index)
    {declaration : TheoremDecl} (compiled : Compiles presentation.syntaxSignature rule declaration) :
    presentation.theory.theoremSignature index = some declaration := by
  rw [presentation.theory_theoremSignature,
    getElem?_named presentation.rules (fun rule => rule.row.id) presentation.distinctRules member found]
  exact (rule?_eq_some_iff _ _ _).mpr compiled

theorem rule_of_lookup {presentation : Presentation} {index : Nat} {declaration : TheoremDecl}
    (lookup : presentation.theory.theoremSignature index = some declaration) :
    ∃ rule, presentation.rules[index]? = some rule ∧
      Compiles presentation.syntaxSignature rule declaration := by
  rw [presentation.theory_theoremSignature] at lookup
  cases found : presentation.rules[index]? with
  | none => simp [found] at lookup
  | some rule =>
      exact ⟨rule, rfl, (rule?_eq_some_iff _ _ _).mp (by simpa [found] using lookup)⟩

/-- Source derivations give MM0 derivations in the translated context and
local scope. A source conversion becomes an MM0 conversion. -/
theorem derives_preserved {base : BasePremiseEvaluator} {presentation : Presentation}
    {bound : List TypeExpr} {context : Context}
    {hypotheses : List Pattern} {targetHypotheses : List Preterm} {pattern : Pattern}
    (contexts : ContextEncodes presentation.syntaxSignature.sorts bound context)
    (localScope : List.Forall₂ (Encodes presentation.syntaxSignature.names) hypotheses targetHypotheses)
    (derived : DerivesModulo base presentation.syntaxSignature.language presentation.rules
      bound hypotheses pattern) {expression : Preterm}
    (encoded : Encodes presentation.syntaxSignature.names pattern expression) :
    Kernel.Derives presentation.theory.termSignature presentation.theory.definitionSignature
      presentation.theory.theoremSignature context targetHypotheses expression := by
  rw [presentation.theory_termSignature, presentation.theory_definitionSignature]
  induction derived generalizing expression with
  | hypothesis member =>
      obtain ⟨target, targetMember, targetEncoded⟩ := encodesList_left_member localScope member
      have same := Option.some.inj (targetEncoded.eval.symm.trans encoded.eval)
      subst expression
      exact .hypothesis targetMember
  | @rule rule member arguments arity typed fragment _ ih =>
      have formed := presentation.formedRules rule member
      obtain ⟨declaration, compiled⟩ := presentation.rule_compiles member
      obtain ⟨targetArguments, argumentsEncoded⟩ := typed_source_vector typed compiled.contexts fragment
      have argumentsAdmitted := (vector_admissibility_iff argumentsEncoded contexts compiled.contexts).mp typed
      obtain ⟨instantiation, instantiated⟩ := (compiled_admitted compiled formed).instantiates argumentsAdmitted
      have instances := compiled.instance_encodes formed argumentsEncoded arity instantiated
      have targetChildren : Kernel.DerivesList presentation.syntaxSignature.termSignature
          (definitionSignature presentation.syntaxSignature presentation.rows)
          presentation.theory.theoremSignature
          context targetHypotheses instantiation.hypotheses := by
        apply (Kernel.derivesList_iff _ _ _ _ _ _).mpr
        intro child childMember
        obtain ⟨premise, premiseMember, premiseEncoded⟩ := encodesList_right_member instances.1 childMember
        exact ih premise premiseMember premiseEncoded
      have same := Option.some.inj (instances.2.eval.symm.trans encoded.eval)
      subst expression
      apply Kernel.Derives.theoremApp (presentation.rule_lookup member
        (index?_some _ _ (List.mem_map_of_mem member)) compiled) instantiated targetChildren
  | conversion equivalent leftFragment rightFragment leftTyped rightTyped _ ih =>
      obtain ⟨sort, sortEncoding⟩ := source_sort_exists contexts leftTyped leftFragment
      obtain ⟨leftExpression, leftEncoded⟩ := typed_source_image leftTyped leftFragment sortEncoding
      exact .conversion
        ((converts_iff presentation.definitional contexts leftTyped rightTyped leftFragment
          rightFragment sortEncoding leftEncoded encoded).mp equivalent)
        (ih leftEncoded)

/-- Every target derivation reflects to a source derivation. Actual target
arguments, including open terms, are reconstructed through their typing, and
a target conversion reflects to a source conversion. -/
theorem derives_reflected {base : BasePremiseEvaluator} {presentation : Presentation}
    {bound : List TypeExpr} {context : Context}
    {hypotheses : List Pattern} {targetHypotheses : List Preterm} {expression : Preterm}
    (contexts : ContextEncodes presentation.syntaxSignature.sorts bound context)
    (localScope : List.Forall₂ (Encodes presentation.syntaxSignature.names) hypotheses targetHypotheses)
    (derived : Kernel.Derives presentation.theory.termSignature presentation.theory.definitionSignature
      presentation.theory.theoremSignature context targetHypotheses expression) :
    ∃ pattern, Encodes presentation.syntaxSignature.names pattern expression ∧
      DerivesModulo base presentation.syntaxSignature.language presentation.rules
        bound hypotheses pattern := by
  rw [presentation.theory_termSignature, presentation.theory_definitionSignature] at derived
  induction derived using Kernel.Derives.rec
      (motive_2 := fun expressions _ => ∀ expression ∈ expressions,
        ∃ pattern, Encodes presentation.syntaxSignature.names pattern expression ∧
          DerivesModulo base presentation.syntaxSignature.language presentation.rules
            bound hypotheses pattern) with
  | hypothesis member =>
      obtain ⟨pattern, patternMember, encoding⟩ := encodesList_right_member localScope member
      exact ⟨pattern, encoding, .hypothesis patternMember⟩
  | theoremApp lookup instantiated _ ih =>
      obtain ⟨rule, ruleLookup, compiled⟩ := presentation.rule_of_lookup lookup
      have member := List.mem_of_getElem? ruleLookup
      have formed := presentation.formedRules rule member
      obtain ⟨arguments, argumentsEncoded, argumentsTyped⟩ :=
        typed_vector_image contexts compiled.contexts instantiated.admissible.typed
      have arity : arguments.length = rule.row.vars.length :=
        argumentsEncoded.length_eq.trans (instantiated.admissible.length_eq.trans
          (compiled.contexts.length_eq.symm.trans formed.arity))
      have instances := compiled.instance_encodes formed argumentsEncoded arity instantiated
      refine ⟨rule.row.instConclusion arguments, instances.2, .rule member arguments arity
        argumentsTyped ((SortedFirstOrderConversion.isMatchCorrectList_iff _).mp
          (encodesList_matchCorrect argumentsEncoded)) ?_⟩
      intro premise premiseMember
      obtain ⟨child, childMember, childEncoded⟩ := encodesList_left_member instances.1 premiseMember
      obtain ⟨reflected, reflectedEncoded, reflectedDerived⟩ := ih child childMember
      have same := encoded_injective reflectedEncoded childEncoded
      simpa only [same] using reflectedDerived
  | conversion converted _ ih =>
      obtain ⟨leftPattern, leftEncoded, leftDerived⟩ := ih
      obtain ⟨leftDecoded, rightPattern, leftDecodedEncoded, rightEncoded, equivalent⟩ :=
        converts_reflected (base := base) presentation.definitional converted
      have same := encoded_injective leftDecodedEncoded leftEncoded
      subst same
      obtain ⟨leftTarget, rightTarget⟩ := converted.typed
      obtain ⟨type, sortEncoding⟩ := target_type_exists contexts leftTarget
      exact ⟨rightPattern, rightEncoded,
        .conversion equivalent (encoded_matchCorrect leftEncoded)
          (encoded_matchCorrect rightEncoded)
          (reflects_type leftEncoded contexts leftTarget sortEncoding)
          (reflects_type rightEncoded contexts rightTarget sortEncoding) leftDerived⟩
  | nil => rename_i expression member; cases member
  | cons _ _ first rest =>
      rename_i expression member
      rcases List.mem_cons.mp member with rfl | member
      · exact first
      · exact rest expression member

/-- **Derivability modulo the definitions is MM0 derivability.** It is
preserved and reflected by the actual MM0 theory construction, with the
definitions compiled to MM0 definitions. -/
theorem derivability_iff {base : BasePremiseEvaluator} {presentation : Presentation}
    {bound : List TypeExpr} {context : Context}
    {hypotheses : List Pattern} {targetHypotheses : List Preterm} {pattern : Pattern} {expression : Preterm}
    (contexts : ContextEncodes presentation.syntaxSignature.sorts bound context)
    (localScope : List.Forall₂ (Encodes presentation.syntaxSignature.names) hypotheses targetHypotheses)
    (encoded : Encodes presentation.syntaxSignature.names pattern expression) :
    DerivesModulo base presentation.syntaxSignature.language presentation.rules
      bound hypotheses pattern ↔
    Kernel.Derives presentation.theory.termSignature presentation.theory.definitionSignature
      presentation.theory.theoremSignature context targetHypotheses expression := by
  constructor
  · exact fun derived => derives_preserved contexts localScope derived encoded
  · intro derived
    obtain ⟨reflected, reflectedEncoded, reflectedDerived⟩ :=
      derives_reflected (base := base) contexts localScope derived
    have same := encoded_injective reflectedEncoded encoded
    simpa only [same] using reflectedDerived

/-- The existing supplied-witness checker recognizes exactly the translated source judgments. -/
theorem derivability_iff_checked {base : BasePremiseEvaluator} {presentation : Presentation}
    {bound : List TypeExpr}
    {context : Context} {hypotheses : List Pattern} {targetHypotheses : List Preterm}
    {pattern : Pattern} {expression : Preterm}
    (contexts : ContextEncodes presentation.syntaxSignature.sorts bound context)
    (localScope : List.Forall₂ (Encodes presentation.syntaxSignature.names) hypotheses targetHypotheses)
    (encoded : Encodes presentation.syntaxSignature.names pattern expression) :
    DerivesModulo base presentation.syntaxSignature.language presentation.rules
      bound hypotheses pattern ↔
    ∃ witness, ProofWitness.check presentation.theory.termSignature
      presentation.theory.definitionSignature presentation.theory.theoremSignature
      context targetHypotheses witness expression = true :=
  (derivability_iff contexts localScope encoded).trans (Kernel.derives_iff_checked _ _ _ _ _ _)

/-- **The equation-free case.** A language without equations has no
definitions, a conversion step changes nothing, and derivability by the
rules alone is MM0 derivability. -/
theorem derivability_iff_of_equationFree {presentation : Presentation}
    (equationFree : presentation.syntaxSignature.language.equations = [])
    {bound : List TypeExpr} {context : Context}
    {hypotheses : List Pattern} {targetHypotheses : List Preterm} {pattern : Pattern} {expression : Preterm}
    (contexts : ContextEncodes presentation.syntaxSignature.sorts bound context)
    (localScope : List.Forall₂ (Encodes presentation.syntaxSignature.names) hypotheses targetHypotheses)
    (encoded : Encodes presentation.syntaxSignature.names pattern expression) :
    SortedFirstOrderRules.Derives presentation.syntaxSignature.language presentation.rules
      bound hypotheses pattern ↔
    Kernel.Derives presentation.theory.termSignature presentation.theory.definitionSignature
      presentation.theory.theoremSignature context targetHypotheses expression :=
  (derivesModulo_iff_derives (base := fun _ _ _ => [])
    (presentation.isEquationFree equationFree)).symm.trans
    (derivability_iff contexts localScope encoded)

/-- The equation-free case, through the supplied-witness checker. -/
theorem derivability_iff_checked_of_equationFree {presentation : Presentation}
    (equationFree : presentation.syntaxSignature.language.equations = [])
    {bound : List TypeExpr} {context : Context}
    {hypotheses : List Pattern} {targetHypotheses : List Preterm} {pattern : Pattern} {expression : Preterm}
    (contexts : ContextEncodes presentation.syntaxSignature.sorts bound context)
    (localScope : List.Forall₂ (Encodes presentation.syntaxSignature.names) hypotheses targetHypotheses)
    (encoded : Encodes presentation.syntaxSignature.names pattern expression) :
    SortedFirstOrderRules.Derives presentation.syntaxSignature.language presentation.rules
      bound hypotheses pattern ↔
    ∃ witness, ProofWitness.check presentation.theory.termSignature
      presentation.theory.definitionSignature presentation.theory.theoremSignature
      context targetHypotheses witness expression = true :=
  (derivability_iff_of_equationFree equationFree contexts localScope encoded).trans
    (Kernel.derives_iff_checked _ _ _ _ _ _)

end Presentation

end Mettapedia.Languages.MM0.Translation.FirstOrderRules
