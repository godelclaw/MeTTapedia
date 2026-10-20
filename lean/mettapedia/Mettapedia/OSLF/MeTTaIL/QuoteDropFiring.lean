import Mettapedia.OSLF.MeTTaIL.QuoteDropSites
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineComparison
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics

/-!
# Firing at quote-drop normal forms

A rule fires at quote-drop normal forms when it has no premises, its left side never mentions the
quote constructor, every explicit substitution on its right side puts an explicit quotation into a
capture occurring with a variable spine, and its binder operation is ordinary substitution or the
presentation's reflective substitution (`QuoteDropFiringAdmissible`). The captures at the normal
form are the normal forms of the original captures, and the reduct reaches the new reduct by a
forward chain of quote-drop steps (`rootFiring_normal`). With licensed sites that never pass under a
quote, every firing of a plan has a counterpart at the normal form of its source
(`primitive_normal`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.QuoteDrop

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralTypedSites ReflectiveSubstitution CanonicalBags
open GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {declaration : ReflectivePresentationDecl}

/-- A rule fires at quote-drop normal forms: no premises, a left side without quotes, explicit
quotations as the replacements of its substitutions, and a binder operation that is ordinary or
the presentation's reflective substitution. -/
def QuoteDropFiringAdmissible (environment : GeneralPremise.Environment) (declaration : ReflectivePresentationDecl)
    (index : Nat) : Prop :=
  ∀ rule spec, environment.language.rewrites[index]? = some rule →
    GeneralPremise.specification? environment index = some spec →
    rule.premises = [] ∧ quoteFree declaration rule.left = true ∧
      substQuoted declaration rule spec .right [] rule.right = true ∧
      (substitutionPresentationForRule? environment.reflection rule = none ∨
        substitutionPresentationForRule? environment.reflection rule = some declaration)

theorem binderRespects_binderOperation (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {profile : Reflection.ReflectionProfile} {rule : RewriteRule}
    (selection : substitutionPresentationForRule? profile rule = none ∨
      substitutionPresentationForRule? profile rule = some declaration) :
    BinderRespects declaration (ScopedReflectiveExecution.binderOperation profile rule) := by
  rcases selection with ordinary | reflective
  · simp only [ScopedReflectiveExecution.binderOperation, ordinary]
    exact binderRespects_ordinary
  · simp only [ScopedReflectiveExecution.binderOperation, reflective]
    exact binderRespects_reflective distinct

/-- **A root firing has a counterpart at the quote-drop normal form of its focus**, with normal
captures and a result reached by a forward chain. -/
theorem rootFiring_normal {environment : GeneralPremise.Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event} {target : Pattern}
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target)
    (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (typedPresentation : QuoteDropTyped environment.language declaration)
    (admissible : QuoteDropFiringAdmissible environment declaration index) :
    ∃ trace' target', GeneralPremise.RootFiring environment bound type (normal declaration source) index trace'
        (normalAssignment declaration captured) (normalAssignment declaration completed) history target' ∧
      QuoteDropForward declaration target target' := by
  cases fired with
  | @fire _ _ _ _ _ rule spec _ _ _ _ selected specified admitted sourceSorted matched typed premises reduced
      targetSorted =>
    obtain ⟨unconditional, free, quoted, selection⟩ := admissible rule spec selected specified
    rw [unconditional] at premises
    cases premises
    obtain ⟨trace', traced⟩ := GeneralScopedMatchMachine.traced_iff_matches.mpr
      (matches_normal free (GeneralScopedMatchMachine.traced_iff_matches.mp ⟨_, matched⟩))
    have named : CapturesNamed declaration captured := by
      intro entry member
      obtain ⟨sorts, objects⟩ := typed
      obtain ⟨_, _, _, _, _, _, bodyTyped⟩ := sorts entry.1 entry.2 member
      exact dropsNamed_of_typed typedPresentation _ bodyTyped (objects entry.1 entry.2 member)
    obtain ⟨target', reduced', forward⟩ := instantiateWith?_normal distinct rule spec bound.length
      (ScopedReflectiveExecution.binderOperation environment.reflection rule)
      (binderRespects_binderOperation distinct selection) rule.right .right [] 0 captured target quoted named reduced
    refine ⟨trace', target', ?_, forward⟩
    refine .fire selected specified admitted (openPatternWellSorted_normal typedPresentation sourceSorted) traced
      (typedAssignment_normal typedPresentation typed) ?_ reduced'
      (forward.openPatternWellSorted typedPresentation targetSorted)
    rw [unconditional]
    exact .nil

/-- Every rule of the plan fires at quote-drop normal forms. -/
def RulesFireAtNormal (plan : Plan) (declaration : ReflectivePresentationDecl) : Prop :=
  ∀ rule ordinal, (rule, ordinal) ∈ plan.rules.zipIdx →
    QuoteDropFiringAdmissible (GeneralPlanEnvironment.environment plan) declaration ordinal

/-- **Every firing has a counterpart at the quote-drop normal form of its source**, with a result
reached by a forward chain. -/
theorem primitive_normal {plan : Plan} {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    {receipt : GeneralRuleJobs.Receipt}
    (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (typedPresentation : QuoteDropTyped (GeneralPlanEnvironment.environment plan).language declaration)
    (quoteOpaque : QuoteOpaque plan.permissions.sites declaration) (admissible : RulesFireAtNormal plan declaration)
    (fired : GeneralOccurrenceSemantics.Primitive plan bound expected source receipt) :
    ∃ receipt', GeneralOccurrenceSemantics.Primitive plan bound expected (normal declaration source) receipt' ∧
      QuoteDropForward declaration receipt.target receipt'.target := by
  obtain ⟨⟨declared, licensed⟩, rooted, accepts, endpoint, sorted⟩ := fired
  have licensed' := licensed_normal typedPresentation quoteOpaque licensed
  obtain ⟨trace', localTarget', rooted', forwardLocal⟩ :=
    rootFiring_normal rooted distinct typedPresentation (admissible _ _ declared)
  have forwardTarget : QuoteDropForward declaration receipt.target
      ((normalContext declaration receipt.job.site.context).fill localTarget') := by
    rw [endpoint]; exact fill_forward _ forwardLocal
  refine ⟨⟨⟨receipt.job.ordinal, receipt.job.declaration, normalSite declaration receipt.job.site⟩, trace',
    normalAssignment declaration receipt.captured, normalAssignment declaration receipt.completed,
    receipt.premiseHistory, localTarget', (normalContext declaration receipt.job.site.context).fill localTarget'⟩,
    ⟨⟨declared, licensed'⟩, rooted', ?_, rfl, ?_⟩, forwardTarget⟩
  · simp only [SiteData.acceptsReplacementRepresentation, normalSite] at accepts ⊢
    exact replacementRepresentations?_forward _ _ forwardLocal accepts
  · exact forwardTarget.openPatternWellSorted typedPresentation sorted

end Mettapedia.OSLF.MeTTaIL.QuoteDrop
