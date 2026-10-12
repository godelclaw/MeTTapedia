import Mettapedia.GSLT.LanguageDef.DefinitionalBaseLanguage

/-!
# Deduction modulo definitions, and why definitions add nothing

Many-sorted inference rules over a language whose equations are definitions
are read modulo those equations: besides citing a hypothesis and applying a
rule, a derivation may replace its conclusion by an equal term of the same
type. The equality is the language's own equation theory. This relation is
defined on the language with its definitions; it does not mention unfolding.

The base presentation is over the base language, which has neither the
defined constructors nor any equation. Its rules are the same rules with
every schema fully unfolded, and they are well formed there. A judgment is
derivable modulo the definitions exactly when its unfolding is derivable
from the unfolded hypotheses in the base presentation. So a definition
changes how statements are written and never what can be proved.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversion

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations

/-- Derivability modulo the language's equation theory. A conversion
relates two first-order terms that are typed at one type. -/
inductive DerivesModulo (base : BasePremiseEvaluator) (language : LanguageDef)
    (rules : List Rule) (context : List TypeExpr)
    (hypotheses : List Pattern) : Pattern → Prop where
  | hypothesis {pattern : Pattern} : pattern ∈ hypotheses →
      DerivesModulo base language rules context hypotheses pattern
  | rule {rule : Rule} : rule ∈ rules → (arguments : List Pattern) →
      arguments.length = rule.row.vars.length →
      List.Forall₂ (fun argument type =>
        HasType language FreeTypeContext.empty context argument type)
        arguments rule.variableTypes →
      (∀ argument ∈ arguments, isMatchCorrectAux argument = true) →
      (∀ premise ∈ rule.row.instPremises arguments,
        DerivesModulo base language rules context hypotheses premise) →
      DerivesModulo base language rules context hypotheses
        (rule.row.instConclusion arguments)
  | conversion {left right : Pattern} {type : TypeExpr} :
      EquationEquiv base language left right →
      isMatchCorrectAux left = true →
      isMatchCorrectAux right = true →
      HasType language FreeTypeContext.empty context left type →
      HasType language FreeTypeContext.empty context right type →
      DerivesModulo base language rules context hypotheses left →
      DerivesModulo base language rules context hypotheses right

/-- Derivability depends on the language only through the typing of rule
arguments. -/
theorem Derives.of_typing {source target : LanguageDef} {rules : List Rule}
    {context : List TypeExpr} {hypotheses : List Pattern}
    (typing : ∀ {pattern : Pattern} {type : TypeExpr},
      HasType source FreeTypeContext.empty context pattern type →
        HasType target FreeTypeContext.empty context pattern type)
    {pattern : Pattern} (derived : Derives source rules context hypotheses pattern) :
    Derives target rules context hypotheses pattern := by
  induction derived with
  | hypothesis member => exact .hypothesis member
  | @rule rule member arguments arity typed fragment _ inductionHypothesis =>
    exact .rule member arguments arity
      (List.Forall₂.imp (fun _ _ argumentTyped => typing argumentTyped) typed) fragment
      inductionHypothesis

/-- A derivation that uses no conversion is a derivation modulo. -/
theorem DerivesModulo.of_derives {base : BasePremiseEvaluator} {language : LanguageDef}
    {rules : List Rule} {context : List TypeExpr}
    {hypotheses : List Pattern} {pattern : Pattern}
    (derived : Derives language rules context hypotheses pattern) :
    DerivesModulo base language rules context hypotheses pattern := by
  induction derived with
  | hypothesis member => exact .hypothesis member
  | @rule rule member arguments arity typed fragment _ inductionHypothesis =>
    exact .rule member arguments arity typed fragment inductionHypothesis

/-! ## The first-order fragment is closed under unfolding -/

theorem isMatchCorrectList_iff :
    ∀ patterns : List Pattern, isMatchCorrectListAux patterns = true ↔
      ∀ pattern ∈ patterns, isMatchCorrectAux pattern = true
  | [] => by simp [isMatchCorrectListAux]
  | pattern :: patterns => by
      simp only [isMatchCorrectListAux, Bool.and_eq_true, isMatchCorrectList_iff patterns,
        List.mem_cons, forall_eq_or_imp]

theorem isMatchCorrect_applyBindings_zip {formals : List String} {values : List Pattern}
    (every : ∀ value ∈ values, isMatchCorrectAux value = true) :
    ∀ pattern : Pattern, Schema formals pattern →
      isMatchCorrectAux (applyBindings (formals.zip values) pattern) = true
  | .fvar name, _ => by
      rcases applyBindings_zip_value name formals values with unbound | member
      · rw [unbound]
        rfl
      · exact every _ member
  | .apply constructor arguments, schema => by
      cases schema with
      | constructor schemas =>
        rw [applyBindings_apply]
        simp only [isMatchCorrectAux]
        rw [isMatchCorrectList_iff]
        exact List.forall_mem_map.mpr (fun argument member =>
          isMatchCorrect_applyBindings_zip every argument (schemas.member member))
  | .bvar _, schema => by cases schema
  | .lambda _ _, schema => by cases schema
  | .multiLambda _ _ _, schema => by cases schema
  | .subst _ _, schema => by cases schema
  | .collection _ _ _, schema => by cases schema
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

theorem isMatchCorrect_unfoldOne {row : Row} (formed : row.WellFormed) :
    ∀ pattern : Pattern, isMatchCorrectAux pattern = true →
      isMatchCorrectAux (unfoldOne row pattern) = true
  | .bvar _, _ => by simp [isMatchCorrectAux]
  | .fvar _, _ => by simp [isMatchCorrectAux]
  | .apply name arguments, correct => by
      have inner : ∀ argument ∈ arguments, isMatchCorrectAux argument = true :=
        (isMatchCorrectList_iff arguments).mp (by simpa [isMatchCorrectAux] using correct)
      have every : ∀ value ∈ arguments.map (unfoldOne row), isMatchCorrectAux value = true :=
        List.forall_mem_map.mpr (fun argument member =>
          isMatchCorrect_unfoldOne formed argument (inner argument member))
      rw [unfoldOne_apply]
      split
      · exact isMatchCorrect_applyBindings_zip every row.body formed.schema
      · simp only [isMatchCorrectAux]
        exact (isMatchCorrectList_iff _).mpr every
  | .lambda _ _, correct => by simp [isMatchCorrectAux] at correct
  | .multiLambda _ _ _, correct => by simp [isMatchCorrectAux] at correct
  | .subst _ _, correct => by simp [isMatchCorrectAux] at correct
  | .collection _ _ _, correct => by simp [isMatchCorrectAux] at correct
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

theorem isMatchCorrect_expand :
    ∀ rows : List Row, (∀ row ∈ rows, row.WellFormed) →
      ∀ pattern : Pattern, isMatchCorrectAux pattern = true →
        isMatchCorrectAux (expand rows pattern) = true
  | [], _, _, correct => correct
  | row :: rows, every, pattern, correct =>
      isMatchCorrect_unfoldOne (every row (by simp)) _
        (isMatchCorrect_expand rows (fun other member => every other (by simp [member]))
          pattern correct)

/-! ## Unfolded rules and their instances -/

theorem expand_bvar (index : Nat) : ∀ rows : List Row, expand rows (.bvar index) = .bvar index
  | [] => rfl
  | row :: rows => by rw [expand_cons, expand_bvar index rows, unfoldOne_bvar]

/-- The rule with every schema fully unfolded. Names and sorts are kept. -/
def expandRule (rows : List Row) (rule : Rule) : Rule :=
  { rule with
    row := { rule.row with
      premises := rule.row.premises.map (expand rows)
      conclusion := expand rows rule.row.conclusion } }

theorem instConclusion_expand {rows : List Row} (formed : ∀ row ∈ rows, row.WellFormed)
    {rule : Rule} (schema : Schema rule.row.vars rule.row.conclusion)
    (arguments : List Pattern) :
    expand rows (rule.row.instConclusion arguments) =
      (expandRule rows rule).row.instConclusion (arguments.map (expand rows)) :=
  expand_applyBindings_zip rows formed arguments rule.row.conclusion schema

theorem instPremises_expand {rows : List Row} (formed : ∀ row ∈ rows, row.WellFormed)
    {rule : Rule} (schemas : Schemas rule.row.vars rule.row.premises)
    (arguments : List Pattern) :
    (rule.row.instPremises arguments).map (expand rows) =
      (expandRule rows rule).row.instPremises (arguments.map (expand rows)) := by
  simp only [FORule.instPremises, expandRule, List.map_map]
  apply List.map_congr_left
  intro premise member
  exact expand_applyBindings_zip rows formed arguments premise (schemas.member member)

/-- Numbering the metavariables commutes with full unfolding. -/
theorem numbered_expand {rows : List Row} (formed : ∀ row ∈ rows, row.WellFormed)
    {names : List String} {pattern : Pattern} (schema : Schema names pattern) :
    numbered names (expand rows pattern) = expand rows (numbered names pattern) := by
  have fixed : ((List.range names.length).map Pattern.bvar).map (expand rows) =
      (List.range names.length).map Pattern.bvar := by
    rw [List.map_map]
    apply List.map_congr_left
    intro index _
    exact expand_bvar index rows
  have unfolded := expand_applyBindings_zip rows formed
    ((List.range names.length).map Pattern.bvar) pattern schema
  rw [fixed] at unfolded
  exact unfolded.symm

/-- An instance of a typed schema at typed arguments is typed. -/
theorem hasType_instance {language : LanguageDef} {context types : List TypeExpr}
    {names : List String} {pattern : Pattern} {type : TypeExpr} (distinct : names.Nodup)
    (schema : Schema names pattern)
    (typedSchema : HasType language FreeTypeContext.empty types (numbered names pattern) type)
    {arguments : List Pattern} (arity : arguments.length = names.length)
    (typedArguments : List.Forall₂ (fun argument argumentType =>
      HasType language FreeTypeContext.empty context argument argumentType) arguments types) :
    HasType language FreeTypeContext.empty context
      (applyBindings (names.zip arguments) pattern) type := by
  rw [schema.instantiate_numbered distinct arguments arity]
  exact HasType.substituteBound
    ⟨argumentAt arguments, fun lookup => hasType_argumentAt typedArguments lookup⟩ typedSchema

theorem statement_instance {language : LanguageDef} {judgmentSorts : List String}
    {context types : List TypeExpr} {names : List String} {pattern : Pattern}
    (distinct : names.Nodup) (schema : Schema names pattern)
    (typedSchema : Statement language judgmentSorts types (numbered names pattern))
    {arguments : List Pattern} (arity : arguments.length = names.length)
    (typedArguments : List.Forall₂ (fun argument argumentType =>
      HasType language FreeTypeContext.empty context argument argumentType) arguments types) :
    Statement language judgmentSorts context (applyBindings (names.zip arguments) pattern) := by
  obtain ⟨name, member, typed⟩ := typedSchema
  exact ⟨name, member, hasType_instance distinct schema typed arity typedArguments⟩

/-! ## Conservativity -/

section Conservativity

variable {base : BasePremiseEvaluator} {language : LanguageDef} {rows : List Row}
  {judgmentSorts : List String} {rules : List Rule} {context : List TypeExpr}
  {hypotheses : List Pattern}

/-- The unfolded rules are well formed over the base language. -/
theorem expandRule_wellFormed (definitional : DefinitionalLanguage language rows)
    {rule : Rule} (formed : rule.WellFormed language judgmentSorts) :
    (expandRule rows rule).WellFormed (baseLanguage language rows) judgmentSorts := by
  have rowsFormed := definitional.acyclic.wellFormed
  have statement : ∀ {pattern : Pattern}, Schema rule.row.vars pattern →
      Statement language judgmentSorts rule.variableTypes (numbered rule.row.vars pattern) →
      Statement (baseLanguage language rows) judgmentSorts rule.variableTypes
        (numbered rule.row.vars (expand rows pattern)) := by
    rintro pattern schema ⟨name, member, typed⟩
    refine ⟨name, member, ?_⟩
    rw [numbered_expand rowsFormed schema]
    exact definitional.hasType_base_expand typed
  refine ⟨formed.distinctNames, formed.arity, formed.declaredTypes, ?_, ?_, ?_, ?_⟩
  · apply schemas_of_forall
    intro pattern member
    obtain ⟨premise, premiseMember, rfl⟩ := List.mem_map.mp member
    exact schema_expand rows rowsFormed premise (formed.premiseSchemas.member premiseMember)
  · exact schema_expand rows rowsFormed _ formed.conclusionSchema
  · intro pattern member
    obtain ⟨premise, premiseMember, rfl⟩ := List.mem_map.mp member
    exact statement (formed.premiseSchemas.member premiseMember)
      (formed.hypotheses premise premiseMember)
  · exact statement formed.conclusionSchema formed.conclusion

/-- The unfolding of a statement is a statement of the base language. -/
theorem statement_base_expand (definitional : DefinitionalLanguage language rows)
    {pattern : Pattern} (statement : Statement language judgmentSorts context pattern) :
    Statement (baseLanguage language rows) judgmentSorts context (expand rows pattern) := by
  obtain ⟨name, member, typed⟩ := statement
  exact ⟨name, member, definitional.hasType_base_expand typed⟩

/-- A derivation modulo the definitions unfolds to a derivation in the base
presentation. -/
theorem derives_expand_of_derivesModulo (definitional : DefinitionalLanguage language rows)
    (formedRules : ∀ rule ∈ rules, rule.WellFormed language judgmentSorts) {pattern : Pattern}
    (derived : DerivesModulo base language rules context hypotheses pattern) :
    Derives (baseLanguage language rows) (rules.map (expandRule rows)) context
      (hypotheses.map (expand rows)) (expand rows pattern) := by
  have formed := definitional.acyclic.wellFormed
  induction derived with
  | hypothesis member => exact .hypothesis (List.mem_map_of_mem member)
  | @rule rule member arguments arity typed fragment _ inductionHypothesis =>
    have ruleFormed := formedRules rule member
    rw [instConclusion_expand formed ruleFormed.conclusionSchema]
    refine Derives.rule (List.mem_map_of_mem member) (arguments.map (expand rows))
      (by simpa [expandRule] using arity) ?_ ?_ ?_
    · exact List.forall₂_map_left_iff.mpr
        (List.Forall₂.imp
          (fun _ _ argumentTyped => definitional.hasType_base_expand argumentTyped) typed)
    · exact List.forall_mem_map.mpr (fun argument argumentMember =>
        isMatchCorrect_expand rows formed argument (fragment argument argumentMember))
    · rw [← instPremises_expand formed ruleFormed.premiseSchemas]
      exact List.forall_mem_map.mpr inductionHypothesis
  | conversion equivalent _ _ _ _ _ inductionHypothesis =>
    rw [← (definitional.equationEquiv_iff _ _).mp equivalent]
    exact inductionHypothesis

/-- An instance of a schema and the same instance of its unfolding are equal
in the equation theory. -/
theorem equationEquiv_instance_expand (definitional : DefinitionalLanguage language rows)
    {names : List String} {pattern : Pattern} (schema : Schema names pattern)
    (arguments : List Pattern) :
    EquationEquiv base language (applyBindings (names.zip arguments) (expand rows pattern))
      (applyBindings (names.zip arguments) pattern) := by
  have formed := definitional.acyclic.wellFormed
  rw [definitional.equationEquiv_iff,
    expand_applyBindings_zip rows formed arguments _ (schema_expand rows formed pattern schema),
    expand_applyBindings_zip rows formed arguments pattern schema, definitional.expand_expand]

/-- A derivation by the unfolded rules, from the unfolded hypotheses, is a
derivation modulo the definitions. The arguments of its rule applications
may still mention defined constructors. -/
theorem derivesModulo_of_derives_expanded (definitional : DefinitionalLanguage language rows)
    (formedRules : ∀ rule ∈ rules, rule.WellFormed language judgmentSorts)
    (hypothesisFragments : ∀ hypothesis ∈ hypotheses, isMatchCorrectAux hypothesis = true)
    (hypothesisTyped : ∀ hypothesis ∈ hypotheses, ∃ type,
      HasType language FreeTypeContext.empty context hypothesis type) {pattern : Pattern}
    (derived : Derives language (rules.map (expandRule rows)) context
      (hypotheses.map (expand rows)) pattern) :
    DerivesModulo base language rules context hypotheses pattern := by
  have formed := definitional.acyclic.wellFormed
  induction derived with
  | hypothesis member =>
    obtain ⟨hypothesis, hypothesisMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨type, typed⟩ := hypothesisTyped hypothesis hypothesisMember
    have fragment := hypothesisFragments hypothesis hypothesisMember
    exact .conversion (definitional.equationEquiv_expand hypothesis) fragment
      (isMatchCorrect_expand rows formed hypothesis fragment) typed
      (definitional.hasType_expand typed) (.hypothesis hypothesisMember)
  | @rule unfolded member arguments arity typed fragment _ inductionHypothesis =>
    obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp member
    have ruleFormed := formedRules rule ruleMember
    have instances : ∀ {schema : Pattern}, Schema rule.row.vars schema →
        Statement language judgmentSorts rule.variableTypes (numbered rule.row.vars schema) →
        (∃ type,
          HasType language FreeTypeContext.empty context
            (applyBindings (rule.row.vars.zip arguments) (expand rows schema)) type ∧
          HasType language FreeTypeContext.empty context
            (applyBindings (rule.row.vars.zip arguments) schema) type) ∧
        isMatchCorrectAux
            (applyBindings (rule.row.vars.zip arguments) (expand rows schema)) = true ∧
          isMatchCorrectAux (applyBindings (rule.row.vars.zip arguments) schema) = true := by
      rintro schema schemaFormed ⟨name, -, typedSchema⟩
      have unfoldedSchema := schema_expand rows formed _ schemaFormed
      refine ⟨⟨.base name, ?_, ?_⟩, isMatchCorrect_applyBindings_zip fragment _ unfoldedSchema,
        isMatchCorrect_applyBindings_zip fragment _ schemaFormed⟩
      · refine hasType_instance ruleFormed.distinctNames unfoldedSchema ?_ arity typed
        rw [numbered_expand formed schemaFormed]
        exact definitional.hasType_expand typedSchema
      · exact hasType_instance ruleFormed.distinctNames schemaFormed typedSchema arity typed
    have original : DerivesModulo base language rules context hypotheses
        (rule.row.instConclusion arguments) := by
      refine .rule ruleMember arguments arity typed fragment ?_
      intro premise premiseMember
      obtain ⟨schema, schemaMember, rfl⟩ := List.mem_map.mp premiseMember
      have unfoldedPremise : applyBindings (rule.row.vars.zip arguments) (expand rows schema) ∈
          (expandRule rows rule).row.instPremises arguments := by
        simp only [FORule.instPremises, expandRule, List.map_map]
        exact List.mem_map.mpr ⟨schema, schemaMember, rfl⟩
      have schemaFormed := ruleFormed.premiseSchemas.member schemaMember
      obtain ⟨both, bothFragments⟩ := instances schemaFormed
        (ruleFormed.hypotheses schema schemaMember)
      obtain ⟨type, unfoldedTyped, authoredTyped⟩ := both
      exact .conversion (equationEquiv_instance_expand definitional schemaFormed arguments)
        bothFragments.1 bothFragments.2 unfoldedTyped authoredTyped
        (inductionHypothesis _ unfoldedPremise)
    obtain ⟨both, bothFragments⟩ := instances ruleFormed.conclusionSchema ruleFormed.conclusion
    obtain ⟨type, unfoldedTyped, authoredTyped⟩ := both
    exact .conversion
      (Relation.EqvGen.symm _ _
        (equationEquiv_instance_expand definitional ruleFormed.conclusionSchema arguments))
      bothFragments.2 bothFragments.1 authoredTyped unfoldedTyped original

/-- **Definitions add nothing.** A typed term is derivable modulo the
definitions exactly when its full unfolding is derivable in the base
presentation: over the language without the defined constructors and
without equations, from the unfolded hypotheses, by the rules with every
schema unfolded. -/
theorem derivesModulo_iff_base (definitional : DefinitionalLanguage language rows)
    (formedRules : ∀ rule ∈ rules, rule.WellFormed language judgmentSorts)
    (hypothesisFragments : ∀ hypothesis ∈ hypotheses, isMatchCorrectAux hypothesis = true)
    (hypothesisTyped : ∀ hypothesis ∈ hypotheses, ∃ type,
      HasType language FreeTypeContext.empty context hypothesis type) {pattern : Pattern}
    {type : TypeExpr} (fragment : isMatchCorrectAux pattern = true)
    (typed : HasType language FreeTypeContext.empty context pattern type) :
    DerivesModulo base language rules context hypotheses pattern ↔
      Derives (baseLanguage language rows) (rules.map (expandRule rows)) context
        (hypotheses.map (expand rows)) (expand rows pattern) := by
  constructor
  · exact derives_expand_of_derivesModulo definitional formedRules
  · intro derived
    exact .conversion
      (Relation.EqvGen.symm _ _ (definitional.equationEquiv_expand pattern))
      (isMatchCorrect_expand rows definitional.acyclic.wellFormed pattern fragment) fragment
      (definitional.hasType_expand typed) typed
      (derivesModulo_of_derives_expanded definitional formedRules hypothesisFragments
        hypothesisTyped (Derives.of_typing hasType_of_base derived))

/-- **A term of the base language gains no proof from the definitions.**
It is derivable modulo the definitions exactly when it is derivable in the
base presentation. -/
theorem derivesModulo_iff_base_of_base (definitional : DefinitionalLanguage language rows)
    (formedRules : ∀ rule ∈ rules, rule.WellFormed language judgmentSorts)
    (hypothesisFragments : ∀ hypothesis ∈ hypotheses, isMatchCorrectAux hypothesis = true)
    (hypothesisTyped : ∀ hypothesis ∈ hypotheses, ∃ type,
      HasType (baseLanguage language rows) FreeTypeContext.empty context hypothesis type)
    {pattern : Pattern} {type : TypeExpr} (fragment : isMatchCorrectAux pattern = true)
    (typed : HasType (baseLanguage language rows) FreeTypeContext.empty context pattern type) :
    DerivesModulo base language rules context hypotheses pattern ↔
      Derives (baseLanguage language rows) (rules.map (expandRule rows)) context hypotheses
        pattern := by
  have fixedHypotheses : hypotheses.map (expand rows) = hypotheses := by
    conv_rhs => rw [← List.map_id hypotheses]
    apply List.map_congr_left
    intro hypothesis member
    obtain ⟨hypothesisType, hypothesisTyping⟩ := hypothesisTyped hypothesis member
    exact expand_eq_self_of_base hypothesisTyping
  have unfolded := derivesModulo_iff_base (base := base) definitional formedRules
    hypothesisFragments
    (fun hypothesis member =>
      (hypothesisTyped hypothesis member).imp (fun _ typing => hasType_of_base typing))
    fragment (hasType_of_base typed)
  rw [fixedHypotheses, expand_eq_self_of_base typed] at unfolded
  exact unfolded

/-- Without equations, a conversion changes nothing: derivability modulo the
equation theory is derivability. -/
theorem derivesModulo_iff_derives (free : language.isEquationFree = true) {pattern : Pattern} :
    DerivesModulo base language rules context hypotheses pattern ↔
      Derives language rules context hypotheses pattern := by
  constructor
  · intro derived
    induction derived with
    | hypothesis member => exact .hypothesis member
    | @rule rule member arguments arity typed fragment _ inductionHypothesis =>
      exact .rule member arguments arity typed fragment inductionHypothesis
    | conversion equivalent _ _ _ _ _ inductionHypothesis =>
      rw [← (equationEquiv_iff_eq_of_no_generators free _ _).mp equivalent]
      exact inductionHypothesis
  · exact DerivesModulo.of_derives

end Conservativity

end Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversion
