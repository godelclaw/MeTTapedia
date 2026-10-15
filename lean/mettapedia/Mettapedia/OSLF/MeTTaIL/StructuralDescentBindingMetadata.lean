import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics

/-!
# Scoped semantic independence from stored binding annotations

The explicit occurrence specification is the operational input. Adding its
checked annotation to a source declaration changes neither capture nor
instantiation. Traced matching retains all selected bag occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.BindingMetadata

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatchMachine

def annotate (rule : RewriteRule) (bindings : Option RuleBindingSpec) : RewriteRule :=
  {rule with bindings := bindings}

theorem arguments (rule : RewriteRule) (bindings : Option RuleBindingSpec)
    (spec : RuleBindingSpec) (name : String) (site : RulePatternSite) (path : List Nat) :
    arguments? (annotate rule bindings) spec name site path = arguments? rule spec name site path := by
  have sites : ∀ position, sitePattern? (annotate rule bindings) position = sitePattern? rule position := by
    intro position
    cases position <;> rfl
  simp only [arguments?, occurrenceDeclared, sites]
  rfl

theorem capture (rule : RewriteRule) (bindings : Option RuleBindingSpec)
    (spec : RuleBindingSpec) (ambient depth : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : Assignment) (name : String) (target : Pattern) :
    capture? (annotate rule bindings) spec ambient depth site path assignment name target =
      capture? rule spec ambient depth site path assignment name target := by
  simp only [capture?, arguments]

theorem captureRest (rule : RewriteRule) (bindings : Option RuleBindingSpec)
    (spec : RuleBindingSpec) (ambient depth : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : Assignment) (name : String) (kind : CollType) (targets : List Pattern) :
    captureRest? (annotate rule bindings) spec ambient depth site path assignment name kind targets =
      captureRest? rule spec ambient depth site path assignment name kind targets := by
  simp only [captureRest?, capture]

theorem admitted (rule : RewriteRule) (bindings : Option RuleBindingSpec) (spec : RuleBindingSpec) :
    admittedFor (annotate rule bindings) spec = admittedFor rule spec := by
  have sites : ∀ position, sitePattern? (annotate rule bindings) position = sitePattern? rule position := by
    intro position
    cases position <;> rfl
  have depths : ∀ position, siteBinderDepth? (annotate rule bindings) position = siteBinderDepth? rule position := by
    intro position
    cases position <;> rfl
  simp only [admittedFor, annotate, occurrenceDeclared, occurrenceDepthAtSite?] at sites depths ⊢
  simp only [sites, depths]
  rfl

mutual
theorem traced {rule : RewriteRule} (bindings : Option RuleBindingSpec)
    {spec : RuleBindingSpec} {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {schema target : Pattern} {trace : List BagChoice}
    (matched : TracedMatches rule spec ambient site path depth initial schema target trace final) :
    TracedMatches (annotate rule bindings) spec ambient site path depth initial schema target trace final := by
  cases matched with
  | capture accepted => exact .capture (by simpa only [capture] using accepted)
  | bound => exact .bound
  | constructor children => exact .constructor (tracedArguments bindings children)
  | binder body => exact .binder (traced bindings body)
  | binders body => exact .binders (traced bindings body)
  | substitution body replacement => exact .substitution (traced bindings body) (traced bindings replacement)
  | bag different children => exact .bag different (tracedBag bindings children)
  | vector children => exact .vector (tracedArguments bindings children)
  | vectorRest children captured =>
      exact .vectorRest (tracedArguments bindings children) (by simpa only [captureRest] using captured)
termination_by sizeOf schema

theorem tracedArguments {rule : RewriteRule} (bindings : Option RuleBindingSpec)
    {spec : RuleBindingSpec} {ambient depth index : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {schemas targets : List Pattern} {trace : List BagChoice}
    (matched : TracedArguments rule spec ambient site path depth initial index schemas targets trace final) :
    TracedArguments (annotate rule bindings) spec ambient site path depth initial index schemas targets trace final := by
  cases matched with
  | nil => exact .nil
  | cons head tail => exact .cons (traced bindings head) (tracedArguments bindings tail)
termination_by sizeOf schemas

theorem tracedBag {rule : RewriteRule} (bindings : Option RuleBindingSpec)
    {spec : RuleBindingSpec} {ambient depth index : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {schemas targets : List Pattern} {rest : Option String}
    {kind : CollType} {trace : List BagChoice}
    (matched : TracedBag rule spec ambient site path depth initial index schemas rest kind targets trace final) :
    TracedBag (annotate rule bindings) spec ambient site path depth initial index schemas rest kind targets trace final := by
  cases matched with
  | nil => exact .nil
  | rest captured => exact .rest (by simpa only [captureRest] using captured)
  | cons selected within head tail => exact .cons selected within (traced bindings head) (tracedBag bindings tail)
termination_by sizeOf schemas
end

theorem traced_iff (rule : RewriteRule) (bindings : Option RuleBindingSpec)
    (spec : RuleBindingSpec) (ambient depth : Nat) (site : RulePatternSite) (path : List Nat)
    (initial final : Assignment) (schema target : Pattern) (trace : List BagChoice) :
    TracedMatches (annotate rule bindings) spec ambient site path depth initial schema target trace final ↔
      TracedMatches rule spec ambient site path depth initial schema target trace final := by
  constructor
  · intro matched
    simpa only [annotate] using traced rule.bindings matched
  · exact traced bindings

mutual
theorem instantiate (operation : Pattern → Pattern → Pattern) (rule : RewriteRule)
    (bindings : Option RuleBindingSpec) (spec : RuleBindingSpec) (ambient depth : Nat)
    (site : RulePatternSite) (path : List Nat) (assignment : Assignment) (schema : Pattern) :
    instantiateWith? operation (annotate rule bindings) spec ambient site path depth assignment schema =
      instantiateWith? operation rule spec ambient site path depth assignment schema := by
  cases schema with
  | fvar name => simp only [instantiateWith?, arguments]
  | bvar index => simp only [instantiateWith?]
  | apply label schemas =>
      simp only [instantiateWith?]
      rw [instantiateArguments operation rule bindings spec ambient depth 0 site path assignment schemas]
  | lambda display body =>
      simp only [instantiateWith?]
      rw [instantiate operation rule bindings spec ambient (depth + 1) site (path ++ [0]) assignment body]
  | multiLambda arity display body =>
      simp only [instantiateWith?]
      rw [instantiate operation rule bindings spec ambient (depth + arity) site (path ++ [0]) assignment body]
  | subst body replacement =>
      simp only [instantiateWith?]
      rw [instantiate operation rule bindings spec ambient (depth + 1) site (path ++ [0]) assignment body,
        instantiate operation rule bindings spec ambient depth site (path ++ [1]) assignment replacement]
  | collection kind schemas rest =>
      simp only [instantiateWith?, arguments]
      rw [instantiateArguments operation rule bindings spec ambient depth 0 site path assignment schemas]
termination_by sizeOf schema

theorem instantiateArguments (operation : Pattern → Pattern → Pattern) (rule : RewriteRule)
    (bindings : Option RuleBindingSpec) (spec : RuleBindingSpec) (ambient depth index : Nat)
    (site : RulePatternSite) (path : List Nat) (assignment : Assignment) (schemas : List Pattern) :
    instantiateArgsWith? operation (annotate rule bindings) spec ambient site path depth assignment index schemas =
      instantiateArgsWith? operation rule spec ambient site path depth assignment index schemas := by
  cases schemas with
  | nil => simp only [instantiateArgsWith?]
  | cons head tail =>
      simp only [instantiateArgsWith?]
      rw [instantiate operation rule bindings spec ambient depth site (path ++ [index]) assignment head,
        instantiateArguments operation rule bindings spec ambient depth (index + 1) site path assignment tail]
termination_by sizeOf schemas
end

theorem reduct (operation : Pattern → Pattern → Pattern) (rule : RewriteRule)
    (bindings : Option RuleBindingSpec) (spec : RuleBindingSpec) (ambient : Nat) (assignment : Assignment) :
    reductWith? operation (annotate rule bindings) spec ambient assignment =
      reductWith? operation rule spec ambient assignment :=
  instantiate operation rule bindings spec ambient 0 .right [] assignment rule.right

theorem binderOperation (profile : Reflection.ReflectionProfile) (rule : RewriteRule)
    (bindings : Option RuleBindingSpec) :
    ScopedReflectiveExecution.binderOperation profile (annotate rule bindings) =
      ScopedReflectiveExecution.binderOperation profile rule := by
  simp only [ScopedReflectiveExecution.binderOperation,
    ReflectiveSubstitution.substitutionPresentationForRule?,
    ReflectiveSubstitution.reflectiveRuleForRule?, annotate]

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.BindingMetadata
