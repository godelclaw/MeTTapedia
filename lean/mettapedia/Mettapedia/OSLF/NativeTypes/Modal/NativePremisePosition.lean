import Mettapedia.OSLF.NativeTypes.Modal.NativeOperationalProfile

/-!
# Original authored addresses of premise arguments

A premise position records the actual declaration index and quantified-body
path. All scoped instantiation addresses are derived from those original
positions, rather than supplied as a separate site catalogue.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativePremisePosition

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding

def Located (context : Context) (premise : Premise) : Prop :=
  ∃ outer, context.rule.premises[context.premiseIndex]? = some outer ∧
    quantifiedBody? context.quantifierDepth outer = some premise

theorem quantifiedBody_next (depth : Nat) (premise : Premise) :
    quantifiedBody? (depth + 1) premise =
      (quantifiedBody? depth premise).bind (quantifiedBody? 1) := by
  induction depth generalizing premise with
  | zero => rfl
  | succ depth ih =>
      cases premise <;> simp only [quantifiedBody?, Option.bind_none]
      exact ih _

theorem Located.quantified {context : Context} {collection parameter : String} {body : Premise}
    (located : Located context (.forAll collection parameter body)) :
    Located context.quantified body := by
  obtain ⟨outer, selected, path⟩ := located
  refine ⟨outer, selected, ?_⟩
  change quantifiedBody? (context.quantifierDepth + 1) outer = some body
  rw [quantifiedBody_next, path]
  rfl

theorem query_coherent {context : Context} {relation : String} {arguments : List Pattern}
    (located : Located context (.relationQuery relation arguments)) {index : Nat} {schema : Pattern}
    (selected : arguments[index]? = some schema) :
    DepthCoherent context.rule (context.site index) [] 0 schema := by
  obtain ⟨outer, premise, path⟩ := located
  have within := (List.getElem?_eq_some_iff.mp selected).1
  apply depthCoherent_of_site
  · simp only [Context.site, sitePattern?, premise, Option.bind_eq_bind, Option.bind_some, path, selected]
  · simp only [Context.site, siteBinderDepth?, premise, Option.bind_eq_bind, Option.bind_some, path, within, ite_true]

theorem child_source_coherent {context : Context} {source target : Pattern}
    (located : Located context (.congruence source target)) :
    DepthCoherent context.rule (context.site 0) [] 0 source := by
  obtain ⟨outer, premise, path⟩ := located
  apply depthCoherent_of_site <;>
    simp only [Context.site, sitePattern?, siteBinderDepth?, premise, Option.bind_eq_bind,
      Option.bind_some, path, beq_self_eq_true, ite_true, Nat.zero_lt_succ]

theorem child_target_coherent {context : Context} {source target : Pattern}
    (located : Located context (.congruence source target)) :
    DepthCoherent context.rule (context.site 1) [] 0 target := by
  obtain ⟨outer, premise, path⟩ := located
  apply depthCoherent_of_site <;>
    simp only [Context.site, sitePattern?, siteBinderDepth?, premise, Option.bind_eq_bind,
      Option.bind_some, path, beq_self_eq_true, show (1 == 0) = false from rfl, Bool.false_eq_true, ite_false, ite_true, Nat.lt_succ_self]

theorem scoped_source_coherent {context : Context} {step : ScopedStepPremise}
    (located : Located context (.scopedStep step)) :
    DepthCoherent context.rule (context.site 0) [] step.binders.length step.source := by
  obtain ⟨outer, premise, path⟩ := located
  apply depthCoherent_of_site <;>
    simp only [Context.site, sitePattern?, siteBinderDepth?, premise, Option.bind_eq_bind,
      Option.bind_some, path, beq_self_eq_true, ite_true, Nat.zero_lt_succ]

theorem scoped_target_coherent {context : Context} {step : ScopedStepPremise}
    (located : Located context (.scopedStep step)) :
    DepthCoherent context.rule (context.site 1) [] step.binders.length step.target := by
  obtain ⟨outer, premise, path⟩ := located
  apply depthCoherent_of_site <;>
    simp only [Context.site, sitePattern?, siteBinderDepth?, premise, Option.bind_eq_bind,
      Option.bind_some, path, beq_self_eq_true, show (1 == 0) = false from rfl, Bool.false_eq_true, ite_false, ite_true, Nat.lt_succ_self]

def PremisesLocated (context : Context) (premises : List Premise) : Prop :=
  context.quantifierDepth = 0 ∧ ∀ offset premise, premises[offset]? = some premise →
    context.rule.premises[context.premiseIndex + offset]? = some premise

theorem PremisesLocated.head {context : Context} {premise : Premise} {premises : List Premise}
    (located : PremisesLocated context (premise :: premises)) : Located context premise := by
  refine ⟨premise, ?_, ?_⟩
  · simpa only [Nat.add_zero] using located.2 0 premise rfl
  · rw [located.1]; rfl

theorem PremisesLocated.tail {context : Context} {premise : Premise} {premises : List Premise}
    (located : PremisesLocated context (premise :: premises)) : PremisesLocated context.next premises := by
  refine ⟨rfl, ?_⟩
  intro offset selected present
  have found := located.2 (offset + 1) selected (by simpa using present)
  simpa only [Context.next, Nat.add_assoc, Nat.add_comm 1 offset] using found

theorem premises_root (ruleIndex : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (bound : List TypeExpr) : PremisesLocated ⟨ruleIndex, rule, spec, bound, 0, 0⟩ rule.premises :=
  ⟨rfl, by intro offset premise present; simpa only [Nat.zero_add] using present⟩

end Mettapedia.OSLF.NativeTypes.Modal.NativePremisePosition
