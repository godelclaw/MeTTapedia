import Mettapedia.OSLF.MeTTaIL.StructuralDescentCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralEquationCaptureDomain

/-!
# How deep an equation's premises can go

An equation job's premises are searched from the assignment its left side captured. When the
environment's rules descend structurally (`checkEnvironment`) and the equation's own premises
descend from its left side (`checkPremises`), every premise derivation fits in a depth computed
from the capture alone: the left side's constant contribution plus the sizes of the captured
values of its variables, with multiplicity.

`premises_depth_le`: every premise derivation's depth is at most `leftWeight`, provided the capture
binds every variable of the left side. No match of the left side is needed, only the capture.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.EquationDepth

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching GeneralPremise PatternTreeSize
open GeneralEquationMeasures GeneralEquationAdmission GeneralScopedMatch
open StructuralDescent

/-- The size of a rule's left side instantiated by a capture, in affine form. -/
def leftWeight (rule : RewriteRule) (captured : Assignment) : Nat :=
  constantContribution rule.left + (rule.left.freeFvarNames.map (capturedWeight captured)).sum

theorem leftWeight_eq (rule : RewriteRule) (captured : Assignment) :
    leftWeight rule captured = evaluate (capturedWeight captured) rule.left :=
  (evaluate_affine _ _).symm

/-- An extension keeps the weight of every captured name. -/
theorem weight_sum_extends {captured assignment : Assignment} (extension : Extends captured assignment) :
    ∀ {names : List String}, GeneralEquationCaptureDomain.Captures captured names →
      (names.map (capturedWeight assignment)).sum = (names.map (capturedWeight captured)).sum := by
  intro names
  induction names with
  | nil => intro _; rfl
  | cons name rest ih =>
    intro captures
    obtain ⟨value, found⟩ := captures name List.mem_cons_self
    have later := ih (fun other member => captures other (List.mem_cons_of_mem _ member))
    simp only [List.map_cons, List.sum_cons, later, capturedWeight, found, extension name value found]

/-- **A descending premise source is lighter than the left side under the capture.** -/
theorem source_weight_lt {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient premiseIndex quantifierDepth localDepth : Nat}
    {captured assignment : Assignment} {child source : Pattern}
    (checked : checkSource rule spec premiseIndex quantifierDepth localDepth source = true)
    (captures : GeneralEquationCaptureDomain.Captures captured rule.left.freeFvarNames)
    (extension : Extends captured assignment)
    (instantiated : instantiateAt? rule spec ambient
      (.premise premiseIndex quantifierDepth 0) [] localDepth assignment source = some child) :
    nodes child < leftWeight rule captured := by
  simp only [checkSource, Bool.and_eq_true, beq_iff_eq] at checked
  obtain ⟨⟨⟨_, sourceSide⟩, sourceRest⟩, descent⟩ := checked
  have childCount := instantiate_nodes rule spec ambient
    (.premise premiseIndex quantifierDepth 0) [] localDepth assignment source child sourceSide instantiated
  have positive : ∀ name ∈ rule.left.freeFvarNames, 1 ≤ capturedWeight assignment name := by
    intro name member
    obtain ⟨value, found⟩ := captures name member
    simp only [capturedWeight, extension name value found, Option.map_some, Option.getD_some]
    exact nodes_positive value.body
  have lighter := checkDescent_sound descent (capturedWeight assignment) positive
  rw [evaluate_affine (capturedWeight assignment) rule.left, weight_sum_extends extension captures] at lighter
  rw [leftWeight]
  omega

theorem premise_depth_le {environment : Environment} {context : Context}
    {premise : Premise} {captured initial final : Assignment} {event : Event}
    (held : PremiseHolds environment context premise initial final event)
    (checked : checkPremise context.rule context.spec context.premiseIndex 0 premise = true)
    (rootDepth : context.quantifierDepth = 0)
    (captures : GeneralEquationCaptureDomain.Captures captured context.rule.left.freeFvarNames)
    (extension : Extends captured initial)
    (admitted : checkEnvironment environment = true) : eventDepth event ≤ leftWeight context.rule captured := by
  cases held with
  | query _ => simp only [eventDepth]; omega
  | freshness _ _ => simp only [eventDepth]; omega
  | @step _ source target actualSource actualTarget type initial final childCaptured completed
      childIndex trace targetTrace history typed interpreted child matched finalTyped =>
      have sourceChecked : checkSource context.rule context.spec context.premiseIndex
          context.quantifierDepth 0 source = true := by
        simpa only [checkPremise, rootDepth] using checked
      have lighter := source_weight_lt sourceChecked captures extension interpreted
      have bounded := firing_depth_bound environment admitted actualSource context.bound type
        ⟨childIndex, trace, childCaptured, completed, history, actualTarget, child⟩
      simp only [eventDepth]
      exact (lt_of_le_of_lt bounded lighter).le
  | @scopedStep _ step actualSource actualTarget initial final childCaptured completed
      childIndex trace targetTrace history interpreted child matched finalTyped =>
      have sourceChecked : checkSource context.rule context.spec context.premiseIndex
          context.quantifierDepth step.binders.length step.source = true := by
        simpa only [checkPremise, rootDepth] using checked
      have lighter := source_weight_lt sourceChecked captures extension interpreted
      have bounded := firing_depth_bound environment admitted actualSource (step.binders ++ context.bound)
        step.resultType ⟨childIndex, trace, childCaptured, completed, history, actualTarget, child⟩
      simp only [eventDepth]
      exact (lt_of_le_of_lt bounded lighter).le
  | @quantified _ collection parameter body initial final kind elements history read held =>
      have empty : stepSources body = [] := by
        exact List.isEmpty_iff.mp checked
      have zero := elements_depth_zero environment context parameter body _ _ _ _ _ held
        (fun _ _ _ bodyHeld => premise_depth_zero bodyHeld empty)
      simp only [eventDepth, zero]
      omega

/-- **Every premise derivation fits in the left side's weight.** -/
theorem premises_depth_le {environment : Environment} {context : Context}
    {premises : List Premise} {captured initial final : Assignment} {history : List Event}
    (held : PremisesHold environment context premises initial final history)
    (checked : checkPremises context.rule context.spec context.premiseIndex premises = true)
    (rootDepth : context.quantifierDepth = 0)
    (captures : GeneralEquationCaptureDomain.Captures captured context.rule.left.freeFvarNames)
    (extension : Extends captured initial)
    (admitted : checkEnvironment environment = true) : eventsDepth history ≤ leftWeight context.rule captured := by
  cases held with
  | nil => simp only [eventsDepth]; omega
  | cons head tail =>
      simp only [checkPremises, Bool.and_eq_true] at checked
      have headBound := premise_depth_le head checked.1 rootDepth captures extension admitted
      have tailBound := premises_depth_le tail checked.2 rfl captures (extension.trans head.extension) admitted
      simpa only [eventsDepth] using max_le headBound tailBound
termination_by premises.length

/-- Whether a capture binds every variable of a rule's left side. -/
def capturesLeft (rule : RewriteRule) (captured : Assignment) : Bool :=
  rule.left.freeFvarNames.all fun name => (lookup captured name).isSome

theorem captures_of_capturesLeft {rule : RewriteRule} {captured : Assignment}
    (checked : capturesLeft rule captured = true) :
    GeneralEquationCaptureDomain.Captures captured rule.left.freeFvarNames := by
  intro name member
  have some := List.all_eq_true.mp checked name member
  cases found : lookup captured name with
  | none => rw [found] at some; cases some
  | some value => exact ⟨value, rfl⟩

end Mettapedia.OSLF.MeTTaIL.Complete.EquationDepth
