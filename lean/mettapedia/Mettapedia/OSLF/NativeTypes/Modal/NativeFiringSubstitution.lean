import Mettapedia.OSLF.NativeTypes.Modal.NativeEventSubstitution

/-!
# Actual scoped firing transport for the computed positive profile

This is a forward action on complete independent firing witnesses. It
retains rule indices, match traces, assignment order, provider origins,
quantified occurrences and every directed child history. Freshness is refused
by the contextual profile, and ordinary binder elimination is earned rather
than assumed. The fixed-snapshot executor has its broader admission boundary.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeFiringSubstitution

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open NativePremiseSubstitutionBase NativePremisePosition NativeOperationalProfile

mutual
theorem premise_substitutes {environment : Environment} {original : Context} {premise : Premise}
    {initial final : ScopedRuleMatching.Assignment} {history : Event}
    (held : PremiseHolds environment original premise initial final history)
    (ready : NativeOperationalProfile.Admitted environment)
    (admitted : admittedFor original.rule original.spec = true)
    (located : Located original premise) (scopes : ScopedPremise premise)
    {target : List TypeExpr}
    (substitution : TypedBoundAssignment environment.language environment.free original.bound target)
    (canonical : ∀ index, (substitution.assignment index).hasCanonicalBinderMetadata = true)
    (objects : ∀ index, isObjectPattern (substitution.assignment index) = true) :
    PremiseHolds environment (context target original) premise
      (NativeContextualSubstitution.assignment target.length substitution.assignment initial)
      (NativeContextualSubstitution.assignment target.length substitution.assignment final)
      (NativeEventSubstitution.event original.bound target substitution.assignment history) :=
  match held with
  | .query query => by
      cases scopes with
      | query argumentScopes =>
          simpa only [NativeEventSubstitution.event, context] using
            (PremiseHolds.query (context := context target original) (NativeQuerySubstitution.query_substitutes query admitted located argumentScopes
              ready.prerequisites.closed substitution objects))
  | .freshness interpreted fresh => by cases scopes
  | .step selected interpreted firing matched finalTyped => by
      cases scopes with
      | child sourceScope targetScope =>
          have interpretedNew := NativeRuleInstantiationSubstitution.instantiateAt_substitutes interpreted
            admitted (child_source_coherent located) sourceScope substitution.assignment substitution.wellScoped
          have firingNew := firing_substitutes firing ready substitution canonical objects
          have matchedNew := NativeTracedMatchSubstitution.matched_substitutes matched targetScope
            substitution.assignment substitution.wellScoped
          simp only [ContextSubstitution.lift_zero] at interpretedNew matchedNew
          have finalTypedNew := typed_assignment substitution objects finalTyped
          simpa only [NativeEventSubstitution.child_unscoped, context, Context.site, ContextSubstitution.lift_zero] using
            (PremiseHolds.step (context := context target original) selected interpretedNew firingNew matchedNew finalTypedNew)
  | .scopedStep interpreted firing matched finalTyped => by
      cases scopes with
      | scopedChild sourceScope targetScope =>
          have interpretedNew := NativeRuleInstantiationSubstitution.instantiateAt_substitutes interpreted
            admitted (scoped_source_coherent located) sourceScope substitution.assignment substitution.wellScoped
          have firingNew := firing_substitutes firing ready (substitution.liftContext _)
            (canonical_lift canonical _) (objects_lift objects _)
          have matchedNew := NativeTracedMatchSubstitution.matched_substitutes matched targetScope
            substitution.assignment substitution.wellScoped
          have finalTypedNew := typed_assignment substitution objects finalTyped
          simpa only [NativeEventSubstitution.child_scoped, context, Context.site, TypedBoundAssignment.liftContext,
            List.length_append] using
            (PremiseHolds.scopedStep (context := context target original) interpretedNew firingNew matchedNew finalTypedNew)
  | .quantified collectionRead elementsHeld => by
      cases scopes with
      | quantified bodyScopes =>
          have collectionNew := finite_collection collectionRead substitution.assignment substitution.wellScoped
          have elementsNew := quantified_substitutes elementsHeld ready admitted located.quantified bodyScopes
            substitution canonical objects
          simpa only [NativeEventSubstitution.event, context] using
            (PremiseHolds.quantified (context := context target original) collectionNew elementsNew)

termination_by structural held

theorem premises_substitute {environment : Environment} {original : Context} {premises : List Premise}
    {initial final : ScopedRuleMatching.Assignment} {history : List Event}
    (held : PremisesHold environment original premises initial final history)
    (ready : NativeOperationalProfile.Admitted environment)
    (admitted : admittedFor original.rule original.spec = true)
    (located : PremisesLocated original premises)
    (scopes : ∀ premise ∈ premises, ScopedPremise premise)
    {target : List TypeExpr}
    (substitution : TypedBoundAssignment environment.language environment.free original.bound target)
    (canonical : ∀ index, (substitution.assignment index).hasCanonicalBinderMetadata = true)
    (objects : ∀ index, isObjectPattern (substitution.assignment index) = true) :
    PremisesHold environment (context target original) premises
      (NativeContextualSubstitution.assignment target.length substitution.assignment initial)
      (NativeContextualSubstitution.assignment target.length substitution.assignment final)
      (NativeEventSubstitution.events original.bound target substitution.assignment history) :=
  match held with
  | .nil => by simpa only [NativeEventSubstitution.events] using (PremisesHold.nil (context := context target original))
  | .cons head tail => by
      have headNew := premise_substitutes head ready admitted located.head
        (scopes _ List.mem_cons_self) substitution canonical objects
      have tailNew := premises_substitute tail ready admitted located.tail
        (fun premise member => scopes premise (List.mem_cons_of_mem _ member)) substitution canonical objects
      simpa only [NativeEventSubstitution.events, context_next, Context.next] using (PremisesHold.cons headNew tailNew)

termination_by structural held

theorem quantified_substitutes {environment : Environment} {original : Context}
    {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : ScopedRuleMatching.Assignment} {history : List (Nat × Pattern × List Event)}
    (held : QuantifiedElements environment original parameter body index elements initial final history)
    (ready : NativeOperationalProfile.Admitted environment)
    (admitted : admittedFor original.rule original.spec = true)
    (located : Located original.quantified body) (scopes : ScopedPremise body)
    {target : List TypeExpr}
    (substitution : TypedBoundAssignment environment.language environment.free original.bound target)
    (canonical : ∀ index, (substitution.assignment index).hasCanonicalBinderMetadata = true)
    (objects : ∀ index, isObjectPattern (substitution.assignment index) = true) :
    QuantifiedElements environment (context target original) parameter body index
      (elements.map (ContextSubstitution.substitute substitution.assignment))
      (NativeContextualSubstitution.assignment target.length substitution.assignment initial)
      (NativeContextualSubstitution.assignment target.length substitution.assignment final)
      (NativeEventSubstitution.quantified original.bound target substitution.assignment history) :=
  match held with
  | .nil => by simpa only [NativeEventSubstitution.quantified, List.map_nil] using
      (QuantifiedElements.nil (context := context target original))
  | .cons localTyped head tail => by
      have localTypedNew := typed_assignment substitution objects localTyped
      have headNew := premise_substitutes head ready admitted located scopes substitution canonical objects
      have tailNew := quantified_substitutes tail ready admitted located scopes substitution canonical objects
      simp only [bind_parameter, local_value, context_quantified] at localTypedNew headNew
      rw [restore_parameter] at tailNew
      simpa only [NativeEventSubstitution.quantified, NativeEventSubstitution.events, List.map_cons, Context.quantified] using
        (QuantifiedElements.cons localTypedNew headNew tailNew)

termination_by structural held

theorem firing_substitutes {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source result : Pattern} {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List Event}
    (firing : RootFiring environment bound type source index trace captured completed history result)
    (ready : NativeOperationalProfile.Admitted environment) {target : List TypeExpr}
    (substitution : TypedBoundAssignment environment.language environment.free bound target)
    (canonical : ∀ index, (substitution.assignment index).hasCanonicalBinderMetadata = true)
    (objects : ∀ index, isObjectPattern (substitution.assignment index) = true) :
    RootFiring environment target type (ContextSubstitution.substitute substitution.assignment source) index trace
      (NativeContextualSubstitution.assignment target.length substitution.assignment captured)
      (NativeContextualSubstitution.assignment target.length substitution.assignment completed)
      (NativeEventSubstitution.events bound target substitution.assignment history)
      (ContextSubstitution.substitute substitution.assignment result) :=
  match firing with
  | .fire declared specified admitted sourceTyped matched capturedTyped premises interpreted resultTyped => by
      rename_i rule spec
      have member := List.mem_of_getElem? declared
      have scopes := ready.scopes _ member
      have ordinary := ready.ordinary _ member
      have sourceTypedNew := well_sorted substitution canonical objects sourceTyped
      have matchedNew := NativeTracedMatchSubstitution.matched_substitutes matched scopes.left
        substitution.assignment substitution.wellScoped
      simp only [NativeContextualSubstitution.assignment, List.map_nil, ContextSubstitution.lift_zero] at matchedNew
      have capturedTypedNew := typed_assignment substitution objects capturedTyped
      have premisesNew := premises_substitute premises ready admitted
        (premises_root _ _ _ _) scopes.premises substitution canonical objects
      simp only [ScopedReflectiveExecution.binderOperation, ordinary] at interpreted
      have interpretedNew := NativeRuleInstantiationSubstitution.reduct_substitutes interpreted admitted
        scopes.right substitution.assignment substitution.wellScoped
      have interpretedActual : reductWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule)
          rule spec target.length (NativeContextualSubstitution.assignment target.length substitution.assignment completed) =
          some (ContextSubstitution.substitute substitution.assignment result) := by
        simpa only [ScopedReflectiveExecution.binderOperation, ordinary, reductWith?_ordinary] using interpretedNew
      have resultTypedNew := well_sorted substitution canonical objects resultTyped
      simpa only [NativeContextualSubstitution.assignment, List.map_nil, ContextSubstitution.lift_zero,
        context, ScopedReflectiveExecution.binderOperation, ordinary,
        ScopedRuleMatching.reductWith?_ordinary] using
        (RootFiring.fire declared specified admitted sourceTypedNew matchedNew capturedTypedNew
          premisesNew interpretedActual resultTypedNew)
termination_by structural firing
end

end Mettapedia.OSLF.NativeTypes.Modal.NativeFiringSubstitution
