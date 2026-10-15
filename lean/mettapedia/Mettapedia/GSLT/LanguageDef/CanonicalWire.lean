import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Canonical five-field LanguageDef wire projection

This renderer is deliberately partial.  It accepts the first-order constructor,
free-variable, application, freshness, relation-query, and recursive-congruence profile
used by the executable language presentations, and rejects unsupported syntax
rather than erasing it. The five-field rewrite rows have no binding-metadata
slot, so rows carrying rule-local dependency or occurrence annotations are
rejected.
-/

namespace Mettapedia.GSLT.LanguageDef.CanonicalWire

open Mettapedia.OSLF.MeTTaIL.Syntax

private def quote (text : String) : String :=
  "\"" ++ (text.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

private def renderList (entries : List String) : String :=
  entries.foldr (fun entry rest => s!"(LCons {entry} {rest})") "LNil"

private def renderCarrier : CarrierKind → String
  | .ast => "CarrierAst"
  | .tokenLabel => "CarrierTokenLabel"
  | .tokenRaw => "CarrierTokenRaw"
  | .tokenProof => "CarrierTokenProof"
  | .tokenPath => "CarrierTokenPath"
  | .builtinInt => "CarrierBuiltinInt"
  | .builtinString => "CarrierBuiltinString"
  | .builtinBool => "CarrierBuiltinBool"

private def renderTypeDecl (declaration : TypeDecl) : String :=
  s!"(TypeDecl {quote declaration.name} {renderCarrier declaration.carrier})"

def renderTypeExpr? : TypeExpr → Option String
  | .base name => some s!"(TBase {quote name})"
  | _ => none

def renderTermParam? : TermParam → Option String
  | .simple name type => do
      let renderedType ← renderTypeExpr? type
      pure s!"(TermSimple {quote name} {renderedType})"
  | _ => none

def renderSyntaxItem? : SyntaxItem → Option String
  | .terminal text => some s!"(SyntaxTerminal {quote text})"
  | .nonTerminal parameter =>
      some s!"(SyntaxNonTerminal {quote parameter})"
  | _ => none

private def renderEvalPolicy : Option TermEvalPolicy → String
  | none => "EvalNone"
  | some .rewrite => "(EvalSome EvalRewrite)"
  | some .fold => "(EvalSome EvalFold)"
  | some .oracle => "(EvalSome EvalOracle)"

/-- A collection-algebra declaration is rendered only when present, so wires
of undeclared rules are unchanged. -/
private def renderCollectionAlgebra : Option CollectionAlgebra → String
  | none => ""
  | some algebra =>
      let flatten := if algebra.flatten then "FlattenTrue" else "FlattenFalse"
      let unit := match algebra.unit with
        | none => "UnitNone"
        | some name => s!"(UnitSome {quote name})"
      s!" (AlgebraSome {flatten} {unit})"

def renderGrammarRule? (rule : GrammarRule) : Option String := do
  let parameters ← rule.params.mapM renderTermParam?
  let renderedSyntax ← rule.syntaxPattern.mapM renderSyntaxItem?
  pure (s!"(GrammarRule {quote rule.label} {quote rule.category} " ++
    s!"{renderList parameters} {renderList renderedSyntax} " ++
    s!"{renderEvalPolicy rule.evalPolicy?}{renderCollectionAlgebra rule.algebra?})")

def renderPattern? : Pattern → Option String
  | .fvar name => some s!"(FVar {quote name})"
  | .apply constructor arguments => do
      let renderedArguments ← arguments.mapM renderPattern?
      pure s!"(PApp {quote constructor} {renderList renderedArguments})"
  | _ => none
termination_by pattern => sizeOf pattern
decreasing_by
  all_goals simp_wf
  all_goals
    have _smaller := List.sizeOf_lt_of_mem ‹_›
    omega

def renderPremise? : Premise → Option String
  | .freshness condition => do
      let renderedTerm ← renderPattern? condition.term
      pure s!"(Freshness {quote condition.varName} {renderedTerm})"
  | .congruence source target => do
      let renderedSource ← renderPattern? source
      let renderedTarget ← renderPattern? target
      pure s!"(Congruence {renderedSource} {renderedTarget})"
  | .relationQuery relation arguments => do
      let renderedArguments ← arguments.mapM renderPattern?
      pure s!"(RelationQuery {quote relation} {renderList renderedArguments})"
  | _ => none

def renderTypeBinding? (binding : String × TypeExpr) : Option String := do
  let renderedType ← renderTypeExpr? binding.2
  pure s!"(TypeBinding {quote binding.1} {renderedType})"

/-- Render only rows whose information fits the existing five-field wire.
Binding metadata has no representation in this wire and is never discarded. -/
def renderRewrite? (rewrite : RewriteRule) : Option String :=
  if rewrite.bindings.isNone then do
    let context ← rewrite.typeContext.mapM renderTypeBinding?
    let premises ← rewrite.premises.mapM renderPremise?
    let left ← renderPattern? rewrite.left
    let right ← renderPattern? rewrite.right
    pure (s!"(RewriteRule {quote rewrite.name} {renderList context} " ++
      s!"{renderList premises} {left} {right})")
  else
    none

/-- Partial structural projection into `GSLTLanguageDefWireV1`. -/
def renderLanguage? (language : LanguageDef) : Option String :=
  if language.equations.isEmpty then do
    let terms ← language.terms.mapM renderGrammarRule?
    let rewrites ← language.rewrites.mapM renderRewrite?
    pure (s!"(GSLTLanguageDefWireV1 {quote language.name}\n  " ++
      s!"{renderList (language.types.map renderTypeDecl)}\n  " ++
      s!"{renderList terms}\n  LNil\n  {renderList rewrites})\n")
  else
    none

/-! ## Compositional renderability -/

/-- Structural type-expression fragment represented by the canonical wire. -/
def typeExprSupported : TypeExpr → Bool
  | .base _ => true
  | _ => false

/-- Structural term-parameter fragment represented by the canonical wire. -/
def termParamSupported : TermParam → Bool
  | .simple _ type => typeExprSupported type
  | _ => false

/-- Structural concrete-syntax fragment represented by the canonical wire. -/
def syntaxItemSupported : SyntaxItem → Bool
  | .terminal _ => true
  | .nonTerminal _ => true
  | _ => false

mutual
  /-- Structural pattern fragment represented by the canonical wire. -/
  def patternSupported : Pattern → Bool
    | .fvar _ => true
    | .apply _ arguments => patternListSupported arguments
    | _ => false
  termination_by pattern => sizeOf pattern

  /-- Structural list fragment used by application arguments. -/
  def patternListSupported : List Pattern → Bool
    | [] => true
    | pattern :: patterns =>
        patternSupported pattern && patternListSupported patterns
  termination_by patterns => sizeOf patterns
end

/-- Structural premise fragment represented by the canonical wire. -/
def premiseSupported : Premise → Bool
  | .freshness condition => patternSupported condition.term
  | .congruence source target =>
      patternSupported source && patternSupported target
  | .relationQuery _ arguments => patternListSupported arguments
  | _ => false

/-- Structural type-binding fragment represented by the canonical wire. -/
def typeBindingSupported (binding : String × TypeExpr) : Bool :=
  typeExprSupported binding.2

/-- A constructor row is supported when every parameter and concrete-syntax
item belongs to the independently defined structural wire fragment. -/
def grammarRuleSupported (rule : GrammarRule) : Bool :=
  rule.params.all termParamSupported &&
    rule.syntaxPattern.all syntaxItemSupported

/-- A rewrite row is supported when its context, premises, and both patterns
belong to the independently defined structural wire fragment and it carries
no binding metadata that the five-field wire cannot represent. -/
def rewriteSupported (rewrite : RewriteRule) : Bool :=
  rewrite.bindings.isNone &&
    (rewrite.typeContext.all typeBindingSupported &&
    rewrite.premises.all premiseSupported &&
    patternSupported rewrite.left &&
    patternSupported rewrite.right)

/-- Structural admission cannot omit an authored binding annotation. -/
theorem rewriteSupported_has_no_binding_metadata (rewrite : RewriteRule)
    (supported : rewriteSupported rewrite) : rewrite.bindings = none := by
  simp only [rewriteSupported, Bool.and_eq_true] at supported
  exact Option.isNone_iff_eq_none.mp supported.1

/-- The exact structural profile accepted by `renderLanguage?`. -/
def languageSupported (language : LanguageDef) : Bool :=
  language.equations.isEmpty &&
    language.terms.all grammarRuleSupported &&
    language.rewrites.all rewriteSupported

private theorem mapM_isSome_eq_all (f : α → Option β) :
    ∀ values : List α,
      (values.mapM f).isSome = values.all (fun value => (f value).isSome) := by
  intro values
  induction values with
  | nil => simp
  | cons value values inductionHypothesis =>
      cases head : f value with
      | none => simp [head]
      | some result =>
          cases tail : values.mapM f <;>
            simpa [head, tail] using inductionHypothesis

private theorem all_congr_of_mem (values : List α) (left right : α → Bool)
    (equal : ∀ value ∈ values, left value = right value) :
    values.all left = values.all right := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp only [List.all_cons]
      rw [equal value (by simp)]
      rw [inductionHypothesis]
      intro tail member
      exact equal tail (by simp [member])

private theorem all_patternSupported_eq_patternListSupported
    (patterns : List Pattern) :
    patterns.all patternSupported = patternListSupported patterns := by
  induction patterns with
  | nil => simp [patternListSupported]
  | cons pattern patterns inductionHypothesis =>
      simp [patternListSupported, inductionHypothesis]

theorem renderTypeExpr?_isSome_eq_supported (type : TypeExpr) :
    (renderTypeExpr? type).isSome = typeExprSupported type := by
  cases type <;> rfl

theorem renderTermParam?_isSome_eq_supported (parameter : TermParam) :
    (renderTermParam? parameter).isSome = termParamSupported parameter := by
  cases parameter with
  | simple name type =>
      have supported := renderTypeExpr?_isSome_eq_supported type
      cases rendered : renderTypeExpr? type <;>
        simp [renderTermParam?, termParamSupported, rendered] at supported ⊢ <;>
        simp_all
  | abstractionNamed => rfl
  | multiAbstractionNamed => rfl

theorem renderSyntaxItem?_isSome_eq_supported (item : SyntaxItem) :
    (renderSyntaxItem? item).isSome = syntaxItemSupported item := by
  cases item <;> rfl

theorem renderPattern?_isSome_eq_supported (pattern : Pattern) :
    (renderPattern? pattern).isSome = patternSupported pattern := by
  fun_induction renderPattern? with
  | case1 => simp [patternSupported]
  | case2 constructor arguments inductionHypothesis =>
      have rendered := mapM_isSome_eq_all renderPattern? arguments
      have supported :
          arguments.all (fun argument => (renderPattern? argument).isSome) =
            arguments.all patternSupported :=
        all_congr_of_mem arguments _ _ inductionHypothesis
      rw [supported] at rendered
      rw [all_patternSupported_eq_patternListSupported] at rendered
      cases result : arguments.mapM renderPattern? <;>
        simp [patternSupported, result] at rendered ⊢ <;>
        simp_all
  | case3 pattern notFVar notApply =>
      cases pattern <;> simp_all [patternSupported]

theorem renderPremise?_isSome_eq_supported (premise : Premise) :
    (renderPremise? premise).isSome = premiseSupported premise := by
  cases premise with
  | freshness condition =>
      have supported := renderPattern?_isSome_eq_supported condition.term
      cases rendered : renderPattern? condition.term <;>
        simp [renderPremise?, premiseSupported, rendered] at supported ⊢ <;>
        simp_all
  | congruence source target =>
      have sourceSupported := renderPattern?_isSome_eq_supported source
      have targetSupported := renderPattern?_isSome_eq_supported target
      cases renderedSource : renderPattern? source <;>
        cases renderedTarget : renderPattern? target <;>
        simp [renderPremise?, premiseSupported, renderedSource, renderedTarget]
          at sourceSupported targetSupported ⊢ <;>
        simp_all
  | relationQuery relation arguments =>
      have rendered := mapM_isSome_eq_all renderPattern? arguments
      have supported :
          arguments.all (fun argument => (renderPattern? argument).isSome) =
            arguments.all patternSupported :=
        all_congr_of_mem arguments _ _
          (fun argument _ => renderPattern?_isSome_eq_supported argument)
      rw [supported] at rendered
      rw [all_patternSupported_eq_patternListSupported] at rendered
      cases result : arguments.mapM renderPattern? <;>
        simp [renderPremise?, premiseSupported, result] at rendered ⊢ <;>
        simp_all
  | scopedStep => rfl
  | forAll => rfl

theorem renderTypeBinding?_isSome_eq_supported
    (binding : String × TypeExpr) :
    (renderTypeBinding? binding).isSome = typeBindingSupported binding := by
  rcases binding with ⟨name, type⟩
  have supported := renderTypeExpr?_isSome_eq_supported type
  cases rendered : renderTypeExpr? type <;>
    simp [renderTypeBinding?, typeBindingSupported, rendered] at supported ⊢ <;>
    simp_all

theorem renderGrammarRule?_isSome_eq_supported (rule : GrammarRule) :
    (renderGrammarRule? rule).isSome = grammarRuleSupported rule := by
  have renderedParameters := mapM_isSome_eq_all renderTermParam? rule.params
  have supportedParameters :
      rule.params.all (fun parameter => (renderTermParam? parameter).isSome) =
        rule.params.all termParamSupported :=
    all_congr_of_mem rule.params _ _
      (fun parameter _ => renderTermParam?_isSome_eq_supported parameter)
  rw [supportedParameters] at renderedParameters
  have renderedSyntax := mapM_isSome_eq_all renderSyntaxItem? rule.syntaxPattern
  have supportedSyntax :
      rule.syntaxPattern.all (fun item => (renderSyntaxItem? item).isSome) =
        rule.syntaxPattern.all syntaxItemSupported :=
    all_congr_of_mem rule.syntaxPattern _ _
      (fun item _ => renderSyntaxItem?_isSome_eq_supported item)
  rw [supportedSyntax] at renderedSyntax
  cases parameters : rule.params.mapM renderTermParam? <;>
    cases renderedItems : rule.syntaxPattern.mapM renderSyntaxItem? <;>
    simp [renderGrammarRule?, grammarRuleSupported, parameters, renderedItems]
      at renderedParameters renderedSyntax ⊢ <;>
    simp_all

theorem renderRewrite?_isSome_eq_supported (rewrite : RewriteRule) :
    (renderRewrite? rewrite).isSome = rewriteSupported rewrite := by
  cases metadata : rewrite.bindings with
  | some spec => simp [renderRewrite?, rewriteSupported, metadata]
  | none =>
      have renderedContext := mapM_isSome_eq_all renderTypeBinding? rewrite.typeContext
      have supportedContext :
          rewrite.typeContext.all (fun binding => (renderTypeBinding? binding).isSome) =
            rewrite.typeContext.all typeBindingSupported :=
        all_congr_of_mem rewrite.typeContext _ _
          (fun binding _ => renderTypeBinding?_isSome_eq_supported binding)
      rw [supportedContext] at renderedContext
      have renderedPremises := mapM_isSome_eq_all renderPremise? rewrite.premises
      have supportedPremises :
          rewrite.premises.all (fun premise => (renderPremise? premise).isSome) =
            rewrite.premises.all premiseSupported :=
        all_congr_of_mem rewrite.premises _ _
          (fun premise _ => renderPremise?_isSome_eq_supported premise)
      rw [supportedPremises] at renderedPremises
      have supportedLeft := renderPattern?_isSome_eq_supported rewrite.left
      have supportedRight := renderPattern?_isSome_eq_supported rewrite.right
      cases context : rewrite.typeContext.mapM renderTypeBinding? <;>
        cases premises : rewrite.premises.mapM renderPremise? <;>
        cases left : renderPattern? rewrite.left <;>
        cases right : renderPattern? rewrite.right <;>
        simp [renderRewrite?, rewriteSupported, metadata, context, premises, left, right]
          at renderedContext renderedPremises supportedLeft supportedRight ⊢ <;>
        simp_all

/-- Successful rendering excludes binding metadata that the current wire
cannot represent. -/
theorem accepted_rewrite_has_no_binding_metadata (rewrite : RewriteRule)
    (accepted : (renderRewrite? rewrite).isSome) : rewrite.bindings = none := by
  rw [renderRewrite?_isSome_eq_supported] at accepted
  exact rewriteSupported_has_no_binding_metadata rewrite accepted

theorem annotated_rewrite_rejected (rewrite : RewriteRule) (spec : RuleBindingSpec)
    (annotated : rewrite.bindings = some spec) : renderRewrite? rewrite = none := by
  simp [renderRewrite?, annotated]

/-- Canonical-wire renderability is precisely the conjunction of its
compositional row obligations. -/
theorem renderLanguage?_isSome_eq_supported (language : LanguageDef) :
    (renderLanguage? language).isSome = languageSupported language := by
  have renderedTerms := mapM_isSome_eq_all renderGrammarRule? language.terms
  have supportedTerms :
      language.terms.all (fun rule => (renderGrammarRule? rule).isSome) =
        language.terms.all grammarRuleSupported :=
    all_congr_of_mem language.terms _ _
      (fun rule _ => renderGrammarRule?_isSome_eq_supported rule)
  rw [supportedTerms] at renderedTerms
  have renderedRewrites := mapM_isSome_eq_all renderRewrite? language.rewrites
  have supportedRewrites :
      language.rewrites.all (fun rewrite => (renderRewrite? rewrite).isSome) =
        language.rewrites.all rewriteSupported :=
    all_congr_of_mem language.rewrites _ _
      (fun rewrite _ => renderRewrite?_isSome_eq_supported rewrite)
  rw [supportedRewrites] at renderedRewrites
  cases equations : language.equations <;>
    cases terms : language.terms.mapM renderGrammarRule? <;>
    cases rewrites : language.rewrites.mapM renderRewrite? <;>
    simp [renderLanguage?, languageSupported, equations, terms, rewrites]
      at renderedTerms renderedRewrites ⊢ <;>
    simp_all

/-- Successful language rendering admits every authored row without losing
rule-local binding metadata. -/
theorem accepted_language_has_no_binding_metadata (language : LanguageDef)
    (accepted : (renderLanguage? language).isSome)
    (rewrite : RewriteRule) (membership : rewrite ∈ language.rewrites) :
    rewrite.bindings = none := by
  rw [renderLanguage?_isSome_eq_supported] at accepted
  simp only [languageSupported, Bool.and_eq_true] at accepted
  exact rewriteSupported_has_no_binding_metadata rewrite
    (List.all_eq_true.mp accepted.2 rewrite membership)

/-- An unrepresentable row rejects the enclosing language rather than
silently projecting away its annotation. -/
theorem annotated_language_rejected (language : LanguageDef)
    (rewrite : RewriteRule) (spec : RuleBindingSpec)
    (membership : rewrite ∈ language.rewrites)
    (annotated : rewrite.bindings = some spec) : renderLanguage? language = none := by
  cases rendered : renderLanguage? language with
  | none => rfl
  | some wire =>
      have accepted : (renderLanguage? language).isSome := by simp [rendered]
      have omitted := accepted_language_has_no_binding_metadata language accepted rewrite membership
      simp [annotated] at omitted

namespace Canary

def supportedCongruence : Premise :=
  .congruence
    (.apply "wire-canary:source" [.fvar "input"])
    (.apply "wire-canary:target" [.fvar "output"])

theorem supportedCongruence_renders :
    (renderPremise? supportedCongruence).isSome := by
  simp [supportedCongruence, renderPremise?, renderPattern?]

def unsupportedCongruence : Premise :=
  .congruence (.bvar 0) (.fvar "output")

theorem unsupportedCongruence_rejected :
    renderPremise? unsupportedCongruence = none := by
  simp [unsupportedCongruence, renderPremise?, renderPattern?]

def unannotatedRewrite : RewriteRule := {
  name := "wire-canary:rewrite"
  typeContext := [("input", .base "Term"), ("output", .base "Term")]
  premises := [supportedCongruence]
  left := .apply "wire-canary:source" [.fvar "input"]
  right := .apply "wire-canary:target" [.fvar "output"]
}

def bindingSpec : RuleBindingSpec := {
  dependencies := [("input", [.base "Term"])]
  occurrences := [{
    name := "input"
    site := .left
    path := [0]
    arguments := [.bvar 0]
  }]
}

/-- The negative row differs only by information omitted by the old wire. -/
def annotatedRewrite : RewriteRule :=
  { unannotatedRewrite with bindings := some bindingSpec }

def unannotatedLanguage : LanguageDef := {
  name := "wire-canary:language"
  types := ["Term"]
  terms := []
  equations := []
  rewrites := [unannotatedRewrite]
}

def annotatedLanguage : LanguageDef :=
  { unannotatedLanguage with rewrites := [unannotatedRewrite, annotatedRewrite] }

theorem unannotatedRewrite_renders :
    (renderRewrite? unannotatedRewrite).isSome := by
  rw [renderRewrite?_isSome_eq_supported]
  simp [unannotatedRewrite, supportedCongruence, rewriteSupported, typeBindingSupported,
    typeExprSupported, premiseSupported, patternSupported, patternListSupported]

theorem annotatedRewrite_rejected : renderRewrite? annotatedRewrite = none :=
  annotated_rewrite_rejected annotatedRewrite bindingSpec rfl

theorem unannotatedLanguage_renders :
    (renderLanguage? unannotatedLanguage).isSome := by
  rw [renderLanguage?_isSome_eq_supported]
  simp [unannotatedLanguage, languageSupported,
    ← renderRewrite?_isSome_eq_supported, unannotatedRewrite_renders]

theorem annotatedLanguage_rejected : renderLanguage? annotatedLanguage = none :=
  annotated_language_rejected annotatedLanguage annotatedRewrite bindingSpec
    (by simp [annotatedLanguage]) rfl

def supportedFreshness : Premise :=
  .freshness {varName := "atom", term := .apply "Pair" [.fvar "subject", .fvar "subject"]}

theorem supportedFreshness_renders :
    (renderPremise? supportedFreshness).isSome := by
  simp [supportedFreshness, renderPremise?, renderPattern?]

theorem binder_freshness_rejected :
    renderPremise? (.freshness {varName := "atom", term := .lambda none (.bvar 0)}) = none := by
  simp [renderPremise?, renderPattern?]

#print axioms supportedFreshness_renders
#print axioms binder_freshness_rejected

#print axioms supportedCongruence_renders
#print axioms unsupportedCongruence_rejected
#print axioms unannotatedRewrite_renders
#print axioms annotatedRewrite_rejected
#print axioms unannotatedLanguage_renders
#print axioms annotatedLanguage_rejected

end Canary

#print axioms renderRewrite?_isSome_eq_supported
#print axioms renderLanguage?_isSome_eq_supported
#print axioms accepted_rewrite_has_no_binding_metadata
#print axioms accepted_language_has_no_binding_metadata
#print axioms annotated_language_rejected

end Mettapedia.GSLT.LanguageDef.CanonicalWire
