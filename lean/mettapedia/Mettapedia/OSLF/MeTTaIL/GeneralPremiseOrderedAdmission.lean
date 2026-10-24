import Mettapedia.OSLF.MeTTaIL.GeneralPremiseOrder
import Mettapedia.OSLF.MeTTaIL.GeneralRuleMatchingHeads
import Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment

/-!
# Checked declaration order covers independent child firings

The static source-head classifier is connected to the independent premise
judgment. Every directed child firing of an admitted declaration is earlier
than its caller, including calls beneath finite quantification and binders.
This is derived from the authored declarations rather than assumed by the
runtime or added to the semantic firing judgment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching

def SourcesWithin (context : Context) (premise : Premise) : Prop :=
  ∀ source ∈ stepSources premise, source ∈ context.rule.premises.flatMap stepSources

theorem SourcesWithin.step_source {context : Context} {source target : Pattern}
    (within : SourcesWithin context (.congruence source target)) :
    source ∈ context.rule.premises.flatMap stepSources :=
  within source (by simp only [stepSources, List.mem_singleton])

theorem SourcesWithin.scoped_source {context : Context} {step : ScopedStepPremise}
    (within : SourcesWithin context (.scopedStep step)) :
    step.source ∈ context.rule.premises.flatMap stepSources :=
  within step.source (by simp only [stepSources, List.mem_singleton])

theorem actual_earlier {environment : Environment} {context : Context}
    (checked : checkStepStratification environment.language = true)
    (declared : (context.rule, context.ruleIndex) ∈ environment.language.rewrites.zipIdx)
    {schema actualSource target : Pattern} {depth index : Nat} {type : TypeExpr}
    {initial captured completed : Assignment} {trace : List GeneralScopedMatchMachine.BagChoice}
    {history : List Event} {bound : List TypeExpr}
    (called : schema ∈ context.rule.premises.flatMap stepSources)
    (interpreted : instantiateAt? context.rule context.spec context.bound.length
      (context.site 0) [] depth initial schema = some actualSource)
    (bounds : bound.length = depth + context.bound.length)
    (firing : GeneralPremise.RootFiring environment bound type actualSource index trace captured completed history target) :
    index < context.ruleIndex := by
  cases firing with
  | fire childDeclared _ _ _ matching _ _ _ _ =>
    have child := List.mk_mem_zipIdx_iff_getElem?.mpr childDeclared
    have matched := matching.matching
    rw [bounds] at matched
    exact GeneralRuleMatchingHeads.actual_child_stratum checked declared child called interpreted matched

mutual
 theorem Interpreted.PremiseHolds.ordered {environment : Environment} {context : Context}
    {premise : Premise} {initial final : Assignment} {event : Event}
    (held : GeneralPremise.PremiseHolds environment context premise initial final event)
    (checked : checkStepStratification environment.language = true)
    (declared : (context.rule, context.ruleIndex) ∈ environment.language.rewrites.zipIdx)
    (within : SourcesWithin context premise) : eventOrdered context.ruleIndex event = true :=
  match held with
  | .query _ => by simp only [eventOrdered]
  | .freshness _ _ => by simp only [eventOrdered]
  | .step _ interpreted firing _ _ => by
      have called := within.step_source
      have earlier := actual_earlier checked declared called interpreted (by simp) firing
      have child := firing.ordered checked
      simp only [eventOrdered, decide_eq_true earlier, child, Bool.and_self]
  | .scopedStep interpreted firing _ _ => by
      have called := within.scoped_source
      have earlier := actual_earlier checked declared called interpreted (by simp) firing
      have child := firing.ordered checked
      simp only [eventOrdered, decide_eq_true earlier, child, Bool.and_self]
  | .quantified _ elements => by
      simpa only [eventOrdered] using elements.ordered checked declared within

 theorem Interpreted.PremisesHold.ordered {environment : Environment} {context : Context}
    {premises : List Premise} {initial final : Assignment} {events : List Event}
    (held : GeneralPremise.PremisesHold environment context premises initial final events)
    (checked : checkStepStratification environment.language = true)
    (declared : (context.rule, context.ruleIndex) ∈ environment.language.rewrites.zipIdx)
    (within : ∀ premise ∈ premises, SourcesWithin context premise) :
    eventsOrdered context.ruleIndex events = true :=
  match held with
  | .nil => by simp only [eventsOrdered]
  | .cons head tail => by
      have first := head.ordered checked declared (within _ (by simp))
      have rest := tail.ordered checked declared (fun premise occurs => within premise (by simp [occurs]))
      change eventsOrdered context.ruleIndex _ = true at rest
      simp only [eventsOrdered, first, rest, Bool.and_self]

 theorem Interpreted.QuantifiedElements.ordered {environment : Environment} {context : Context}
    {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
    {initial final : Assignment} {events : List (Nat × Pattern × List Event)}
    (held : GeneralPremise.QuantifiedElements environment context parameter body index elements initial final events)
    (checked : checkStepStratification environment.language = true)
    (declared : (context.rule, context.ruleIndex) ∈ environment.language.rewrites.zipIdx)
    (within : SourcesWithin context body) : quantifiedOrdered context.ruleIndex events = true :=
  match held with
  | .nil => by simp only [quantifiedOrdered]
  | .cons _ head tail => by
      have first := head.ordered checked declared within
      have rest := tail.ordered checked declared within
      change eventOrdered context.ruleIndex _ = true at first
      simp only [quantifiedOrdered, eventsOrdered, first, rest, Bool.and_self]

 theorem Interpreted.RootFiring.ordered {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List Event}
    (firing : GeneralPremise.RootFiring environment bound type source index trace captured completed history target)
    (checked : checkStepStratification environment.language = true) : eventsOrdered index history = true :=
  match firing with
  | .fire declared _ _ _ _ _ premises _ _ => by
      apply premises.ordered checked (List.mk_mem_zipIdx_iff_getElem?.mpr declared)
      intro premise occurs schema sourceOccurs
      exact List.mem_flatMap.mpr ⟨premise, occurs, sourceOccurs⟩
end

theorem compiled_root_ordered {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions}
    (accepted : (GeneralExecutionAdmission.compile snapshot permissions).complete = true)
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List Event}
    (firing : RootFiring (GeneralPlanEnvironment.environment
      (GeneralExecutionAdmission.compile snapshot permissions)) bound type source index
      trace captured completed history target) : eventsOrdered index history = true :=
  firing.ordered (GeneralExecutionAdmission.complete_snapshot_checks accepted).2.2.2

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
