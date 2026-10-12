import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics

/-!
# Binding-flow guarantees of successful scoped premises

Structural output matches bind every authored metavariable occurrence. The
provider modes therefore justify the compiler's produced-name flow. This is
a theorem about the actual scoped matching judgment, including collection
rest bindings, rather than a claim based only on type signatures.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching

def BoundNames (assignment : Assignment) (names : List String) : Prop :=
  ∀ name ∈ names, ∃ value, lookup assignment name = some value

theorem BoundNames.extension {initial final : Assignment} {names : List String}
    (bound : BoundNames initial names) (preserved : Extension initial final) :
    BoundNames final names := by
  intro name member
  obtain ⟨value, found⟩ := bound name member
  exact ⟨value, preserved name value found⟩

theorem BoundNames.append {assignment : Assignment} {left right : List String}
    (front : BoundNames assignment left) (back : BoundNames assignment right) :
    BoundNames assignment (left ++ right) := by
  intro name member
  rcases List.mem_append.mp member with member | member
  · exact front name member
  · exact back name member

mutual
 theorem matching_bound_names {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
    {pattern target : Pattern}
    (matching : GeneralScopedMatch.Matches rule spec ambient site path depth initial
      pattern target final) : BoundNames final pattern.freeFvarNames :=
  match matching with
  | .capture captured => by
      obtain ⟨_, _, value, _, _, _, found, _, _⟩ :=
        GeneralScopedMatch.capture_interpretation captured
      intro name member
      simp only [Pattern.freeFvarNames, List.mem_singleton] at member
      subst name
      exact ⟨value, found⟩
  | .bound => by intro name member; simp [Pattern.freeFvarNames] at member
  | .constructor arguments => by
      simpa only [Pattern.freeFvarNames] using matching_arguments_bound_names arguments
  | .binder body => by
      simpa only [Pattern.freeFvarNames] using matching_bound_names body
  | .binders body => by
      simpa only [Pattern.freeFvarNames] using matching_bound_names body
  | .substitution body replacement => by
      simpa only [Pattern.freeFvarNames] using
        ((matching_bound_names body).extension replacement.extends).append
          (matching_bound_names replacement)
  | .bag _ bag => by
      simpa only [Pattern.freeFvarNames] using matching_bag_bound_names bag
  | .vector arguments => by
      simpa only [Pattern.freeFvarNames, Option.toList_none, List.append_nil] using
        matching_arguments_bound_names arguments
  | .vectorRest arguments captured => by
      have before := (matching_arguments_bound_names arguments).extension
        (GeneralScopedMatch.capture_extends (by simpa [captureRest?] using captured))
      obtain ⟨_, _, value, _, _, _, found, _, _⟩ :=
        GeneralScopedMatch.capture_interpretation (by simpa [captureRest?] using captured)
      simp only [Pattern.freeFvarNames]
      apply before.append
      intro name member
      simp only [Option.toList_some, List.mem_singleton] at member
      subst name
      exact ⟨value, found⟩

 theorem matching_arguments_bound_names {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial final : Assignment} {index : Nat} {patterns targets : List Pattern}
    (matching : GeneralScopedMatch.Arguments rule spec ambient site path depth initial index
      patterns targets final) : BoundNames final (patterns.flatMap Pattern.freeFvarNames) :=
  match matching with
  | .nil => by intro name member; simp at member
  | .cons head tail =>
      ((matching_bound_names head).extension tail.extends).append
        (matching_arguments_bound_names tail)

 theorem matching_bag_bound_names {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
    {initial final : Assignment} {index : Nat} {patterns targets : List Pattern}
    {rest : Option String} {kind : CollType}
    (matching : GeneralScopedMatch.Bag rule spec ambient site path depth initial index
      patterns rest kind targets final) :
    BoundNames final (patterns.flatMap Pattern.freeFvarNames ++ rest.toList) :=
  match matching with
  | .nil => by intro name member; simp at member
  | .rest captured => by
      obtain ⟨_, _, value, _, _, _, found, _, _⟩ :=
        GeneralScopedMatch.capture_interpretation (by simpa [captureRest?] using captured)
      intro name member
      simp only [List.flatMap_nil, Option.toList_some, List.nil_append,
        List.mem_singleton] at member
      subst name
      exact ⟨value, found⟩
  | .cons _ _ head tail => by
      have all := ((matching_bound_names head).extension tail.extends).append
        (matching_bag_bound_names tail)
      simpa only [List.flatMap_cons, List.append_assoc] using all
end

theorem ArgumentsHold.produces {context : Context} {index : Nat}
    {initial final : Assignment} {schemas values : List Pattern} {modes : List RelationArgMode}
    (held : ArgumentsHold context index initial schemas values modes final) :
    BoundNames final (queryOutputNames schemas modes) := by
  induction held with
  | nil => intro name member; simp [queryOutputNames] at member
  | cons head tail inductionHypothesis =>
      cases head with
      | input _ =>
          simpa only [queryOutputNames, List.zip_cons_cons, List.flatMap_cons,
            List.nil_append] using inductionHypothesis
      | output matching =>
          simpa only [queryOutputNames, List.zip_cons_cons, List.flatMap_cons] using
            ((matching_bound_names matching).extension tail.extension).append inductionHypothesis

theorem QueryHolds.produces {environment : Environment} {context : Context}
    {relation : String} {arguments : List Pattern} {initial final : Assignment} {rowIndex : Nat}
    (held : QueryHolds environment context relation arguments initial rowIndex final)
    (signature : Signature)
    (found : signature? environment.provider relation arguments.length = some signature) :
    BoundNames final (queryOutputNames arguments signature.modes) := by
  cases held with
  | row _ actual _ arguments _ =>
      cases Option.some.inj (actual.symm.trans found)
      exact arguments.produces

theorem BoundNames.eraseDups {assignment : Assignment} {names : List String}
    (bound : BoundNames assignment names) : BoundNames assignment names.eraseDups := by
  intro name member
  exact bound name (List.mem_eraseDups.mp member)

theorem PremiseHolds.bindingFlow {environment : Environment} {context : Context}
    {premise : Premise} {initial final : Assignment} {event : Event}
    (held : PremiseHolds environment context premise initial final event)
    (available : List String) (bound : BoundNames initial available) :
    BoundNames final (premiseFlow environment.language environment.provider context.rule context.spec
      available premise).available := by
  cases held with
  | query traced =>
      cases traced with
      | row _ found _ arguments typed =>
          simp only [premiseFlow, found]
          exact (arguments.readout.produces.append
            (bound.extension arguments.readout.extension)).eraseDups
  | freshness _ _ => exact bound
  | step _ _ _ matching _ =>
      exact ((matching_bound_names matching.matching).append
        (bound.extension matching.matching.extends)).eraseDups
  | scopedStep _ _ matching _ =>
      exact ((matching_bound_names matching.matching).append
        (bound.extension matching.matching.extends)).eraseDups
  | quantified read elements =>
      simp only [forall_flow_preserves_available]
      exact bound.extension (PremiseHolds.quantified read elements).extension

theorem PremisesHold.bindingFlow {environment : Environment} {context : Context}
    {premises : List Premise} {initial final : Assignment} {events : List Event}
    (held : PremisesHold environment context premises initial final events)
    (available : List String) (bound : BoundNames initial available) :
    BoundNames final (premisesFlow environment.language environment.provider context.rule context.spec
      available premises).available :=
  match held with
  | .nil => bound
  | .cons head tail => tail.bindingFlow _ (head.bindingFlow available bound)
termination_by premises.length

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
