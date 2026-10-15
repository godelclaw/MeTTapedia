import Mettapedia.Languages.MM0.Translation.FirstOrderRules

/-!
# The base presentation: unfold first, then check without definitions

A presentation with definitions has a base presentation: the language
without the defined constructors and without equations, and the same rules
with every schema fully unfolded. It is a presentation of the same backend,
and its generated MM0 theory has no definition.

There are then two exact routes to MM0. One keeps the definitions: each
becomes an MM0 definition, and conversion steps become MM0 conversions. The
other unfolds everything first and checks the result in the definition-free
theory. The two agree: MM0 derivability with the definitions is MM0
derivability of the unfolding without them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversion
open Kernel FirstOrderSyntax FirstOrderTyping FirstOrderConversion

namespace Presentation

/-- The syntax signature of the base language: the primitive constructors,
in their authored order. -/
def baseSignature (presentation : Presentation) : Signature where
  language := baseLanguage presentation.syntaxSignature.language presentation.rows
  distinctSorts := presentation.syntaxSignature.distinctSorts
  distinctConstructors :=
    presentation.syntaxSignature.distinctConstructors.sublist
      (List.Sublist.map _ List.filter_sublist)
  ordinaryConstructors := fun rule member =>
    presentation.syntaxSignature.ordinaryConstructors rule (List.mem_filter.mp member).1

/-- The base presentation: the base language and the unfolded rules. -/
def base (presentation : Presentation) : Presentation where
  syntaxSignature := presentation.baseSignature
  judgmentSorts := presentation.judgmentSorts
  rules := presentation.rules.map (expandRule presentation.rows)
  definitional :=
    show DefinitionalLanguage (baseLanguage presentation.syntaxSignature.language presentation.rows)
        [] from
      { authored := .nil
        acyclic := Acyclic.nil
        typed := by simp
        noBags := any_filter_eq_false presentation.definitional.noBags
        noSets := any_filter_eq_false presentation.definitional.noSets
        noAlgebra := any_filter_eq_false presentation.definitional.noAlgebra }
  noRewrites := presentation.noRewrites
  ordinaryPolicies := fun constructor member =>
    presentation.ordinaryPolicies constructor (List.mem_filter.mp member).1
  declaredJudgments := presentation.declaredJudgments
  distinctRules := by
    have same : (presentation.rules.map (expandRule presentation.rows)).map
        (fun rule => rule.row.id) = presentation.rules.map (fun rule => rule.row.id) := by
      rw [List.map_map]
      rfl
    rw [same]
    exact presentation.distinctRules
  formedRules := by
    intro rule member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact expandRule_wellFormed presentation.definitionalRows
      (presentation.formedRules original originalMember)

/-- The base presentation authors no equation. -/
theorem base_equations (presentation : Presentation) :
    presentation.base.syntaxSignature.language.equations = [] := rfl

/-- The generated theory of the base presentation has no definition. -/
theorem base_definitionSignature (presentation : Presentation) (index : Nat) :
    presentation.base.theory.definitionSignature index = none :=
  presentation.base.theory_definitionSignature_eq_none presentation.base_equations index

/-- **Unfold first, then check without definitions.** A typed term is
derivable modulo the definitions exactly when the definition-free MM0 theory
of the base presentation derives its full unfolding from the unfolded
hypotheses. -/
theorem derivesModulo_iff_base_theory {evaluator : BasePremiseEvaluator}
    {presentation : Presentation} {bound : List TypeExpr} {context : Context}
    {hypotheses : List Pattern} {targetHypotheses : List Preterm} {pattern : Pattern}
    {type : TypeExpr} {expression : Preterm}
    (contexts : ContextEncodes presentation.base.syntaxSignature.sorts bound context)
    (hypothesisFragments : ∀ hypothesis ∈ hypotheses, isMatchCorrectAux hypothesis = true)
    (hypothesisTyped : ∀ hypothesis ∈ hypotheses, ∃ hypothesisType,
      HasType presentation.syntaxSignature.language FreeTypeContext.empty bound hypothesis
        hypothesisType)
    (fragment : isMatchCorrectAux pattern = true)
    (typed : HasType presentation.syntaxSignature.language FreeTypeContext.empty bound pattern
      type)
    (localScope : List.Forall₂ (Encodes presentation.base.syntaxSignature.names)
      (hypotheses.map (expand presentation.rows)) targetHypotheses)
    (encoded : Encodes presentation.base.syntaxSignature.names (expand presentation.rows pattern)
      expression) :
    DerivesModulo evaluator presentation.syntaxSignature.language presentation.rules bound
      hypotheses pattern ↔
    Kernel.Derives presentation.base.theory.termSignature
      presentation.base.theory.definitionSignature presentation.base.theory.theoremSignature
      context targetHypotheses expression :=
  (derivesModulo_iff_base presentation.definitionalRows presentation.formedRules
    hypothesisFragments hypothesisTyped fragment typed).trans
    (derivability_iff_of_equationFree (presentation := presentation.base)
      presentation.base_equations contexts localScope encoded)

/-- **MM0 definitions are conservative for these theories.** The generated
theory with the definitions derives a typed term exactly when the generated
theory of the base presentation, which has none, derives its unfolding. The
two theories number their constructors differently; the statement relates
the encodings of one source term and of its unfolding. -/
theorem definitions_conservative {presentation : Presentation} {bound : List TypeExpr}
    {context baseContext : Context} {hypotheses : List Pattern}
    {targetHypotheses baseHypotheses : List Preterm} {pattern : Pattern} {type : TypeExpr}
    {expression baseExpression : Preterm}
    (contexts : ContextEncodes presentation.syntaxSignature.sorts bound context)
    (baseContexts : ContextEncodes presentation.base.syntaxSignature.sorts bound baseContext)
    (hypothesisFragments : ∀ hypothesis ∈ hypotheses, isMatchCorrectAux hypothesis = true)
    (hypothesisTyped : ∀ hypothesis ∈ hypotheses, ∃ hypothesisType,
      HasType presentation.syntaxSignature.language FreeTypeContext.empty bound hypothesis
        hypothesisType)
    (fragment : isMatchCorrectAux pattern = true)
    (typed : HasType presentation.syntaxSignature.language FreeTypeContext.empty bound pattern
      type)
    (localScope : List.Forall₂ (Encodes presentation.syntaxSignature.names) hypotheses
      targetHypotheses)
    (baseScope : List.Forall₂ (Encodes presentation.base.syntaxSignature.names)
      (hypotheses.map (expand presentation.rows)) baseHypotheses)
    (encoded : Encodes presentation.syntaxSignature.names pattern expression)
    (baseEncoded : Encodes presentation.base.syntaxSignature.names
      (expand presentation.rows pattern) baseExpression) :
    Kernel.Derives presentation.theory.termSignature presentation.theory.definitionSignature
      presentation.theory.theoremSignature context targetHypotheses expression ↔
    Kernel.Derives presentation.base.theory.termSignature
      presentation.base.theory.definitionSignature presentation.base.theory.theoremSignature
      baseContext baseHypotheses baseExpression :=
  (derivability_iff (base := fun _ _ _ => []) contexts localScope encoded).symm.trans
    (derivesModulo_iff_base_theory baseContexts hypothesisFragments hypothesisTyped fragment
      typed baseScope baseEncoded)

end Presentation

end Mettapedia.Languages.MM0.Translation.FirstOrderRules
