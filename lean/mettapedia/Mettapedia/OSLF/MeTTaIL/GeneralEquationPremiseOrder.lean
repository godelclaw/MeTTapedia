import Mettapedia.OSLF.MeTTaIL.GeneralPremiseOrderedAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobs

/-!
# Ordered child evaluation for conditional equations

An equation uses the derived caller stratum above all selected directed
declarations. Every actual child firing has a registered lower index, and
the authored rule stratification orders its recursively retained history.
No reverse truth condition on equation guards is required.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching

theorem Interpreted.RootFiring.index_within {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List Event}
    (firing : GeneralPremise.RootFiring environment bound type source index trace captured completed history target) :
    index < environment.language.rewrites.length := by
  cases firing with
  | fire declared _ _ _ _ _ _ _ _ => exact (List.getElem?_eq_some_iff.mp declared).1

mutual
  theorem Interpreted.PremiseHolds.top_ordered {environment : Environment} {context : Context}
      {premise : Premise} {initial final : Assignment} {event : Event}
      (held : GeneralPremise.PremiseHolds environment context premise initial final event)
      (checked : checkStepStratification environment.language = true)
      (top : environment.language.rewrites.length ≤ context.ruleIndex) :
      eventOrdered context.ruleIndex event = true :=
    match held with
    | .query _ => by simp only [eventOrdered]
    | .freshness _ _ => by simp only [eventOrdered]
    | .step _ _ firing _ _ => by
        have earlier := firing.index_within.trans_le top
        have child := firing.ordered checked
        simp only [eventOrdered, decide_eq_true earlier, child, Bool.and_self]
    | .scopedStep _ firing _ _ => by
        have earlier := firing.index_within.trans_le top
        have child := firing.ordered checked
        simp only [eventOrdered, decide_eq_true earlier, child, Bool.and_self]
    | .quantified _ elements => by simpa only [eventOrdered] using elements.top_ordered checked top

  theorem Interpreted.PremisesHold.top_ordered {environment : Environment} {context : Context}
      {premises : List Premise} {initial final : Assignment} {events : List Event}
      (held : GeneralPremise.PremisesHold environment context premises initial final events)
      (checked : checkStepStratification environment.language = true)
      (top : environment.language.rewrites.length ≤ context.ruleIndex) :
      eventsOrdered context.ruleIndex events = true :=
    match held with
    | .nil => by simp only [eventsOrdered]
    | .cons head tail => by
        have first := head.top_ordered checked top
        have rest := tail.top_ordered checked top
        change eventsOrdered context.ruleIndex _ = true at rest
        simp only [eventsOrdered, first, rest, Bool.and_self]

  theorem Interpreted.QuantifiedElements.top_ordered {environment : Environment} {context : Context}
      {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
      {initial final : Assignment} {events : List (Nat × Pattern × List Event)}
      (held : GeneralPremise.QuantifiedElements environment context parameter body index elements initial final events)
      (checked : checkStepStratification environment.language = true)
      (top : environment.language.rewrites.length ≤ context.ruleIndex) :
      quantifiedOrdered context.ruleIndex events = true :=
    match held with
    | .nil => by simp only [quantifiedOrdered]
    | .cons _ head tail => by
        have first := head.top_ordered checked top
        have rest := tail.top_ordered checked top
        change eventOrdered context.ruleIndex _ = true at first
        simp only [quantifiedOrdered, eventsOrdered, first, rest, Bool.and_self]
end

end Mettapedia.OSLF.MeTTaIL.GeneralPremise

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationJobs

theorem Completion.ordered {plan : GeneralExecutionAdmission.Plan} {bound : List Syntax.TypeExpr}
    {type : Syntax.TypeExpr} {source : Syntax.Pattern} {receipt : Receipt}
    (completion : Completion plan bound type source receipt)
    (checked : GeneralPremise.checkStepStratification (GeneralPlanEnvironment.environment plan).language = true) :
    GeneralPremise.eventsOrdered (receipt.job.context plan).ruleIndex receipt.premiseHistory = true := by
  apply completion.premises.top_ordered checked
  simp only [Job.context, GeneralPlanEnvironment.environment, List.length_map]
  exact Nat.le_refl _

end Mettapedia.OSLF.MeTTaIL.GeneralEquationJobs
