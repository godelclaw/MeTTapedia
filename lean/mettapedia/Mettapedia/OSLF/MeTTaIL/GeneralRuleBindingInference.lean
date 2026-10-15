import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch
import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

/-!
# Conservative inference of omitted rule binding declarations

Root input inference retains its previous empty dependency interpretation.
The fallback obtains occurrence contexts from the original grammar and
retains independently inferred implicit result types. Supplied binding
declarations are checked rather than replaced. Rejected inference leaves an
explicit admission obligation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch

mutual
  def rootInput (depth : Nat) : Pattern → Bool
    | .fvar _ => depth == 0
    | .bvar _ => true
    | .apply _ arguments => rootArguments depth arguments
    | .lambda _ body => rootInput (depth + 1) body
    | .multiLambda arity _ body => rootInput (depth + arity) body
    | .subst body replacement => rootInput (depth + 1) body && rootInput depth replacement
    | .collection _ elements rest =>
        rootArguments depth elements && (rest.isNone || depth == 0)
  termination_by pattern => sizeOf pattern

  def rootArguments (depth : Nat) : List Pattern → Bool
    | [] => true
    | pattern :: patterns => rootInput depth pattern && rootArguments depth patterns
  termination_by patterns => sizeOf patterns
end

def inferredSpec (rule : RewriteRule) : RuleBindingSpec where
  dependencies := rule.typeContext.map fun entry => (entry.1, [])

inductive Origin where
  | authored
  | inferredRootInputs
  | inferredGrammar (implicitTypes : List (String × TypeExpr))
  deriving DecidableEq, Repr

structure BindingPlan where
  spec : RuleBindingSpec
  origin : Origin
  deriving DecidableEq, Repr

def BindingPlan.implicitTypes (plan : BindingPlan) : List (String × TypeExpr) :=
  match plan.origin with
  | .inferredGrammar extraTypes => extraTypes
  | .authored | .inferredRootInputs => []

def BindingPlan.elaborate (plan : BindingPlan) (rule : RewriteRule) : RewriteRule :=
  {rule with
    typeContext := rule.typeContext ++ plan.implicitTypes
    bindings := some plan.spec}

def rootDeclared (rule : RewriteRule) : Bool :=
  (rule.left.freeFvarNames ++ rule.right.freeFvarNames).all fun name =>
    rule.typeContext.any fun entry => entry.1 == name

def grammarPlan? (language : LanguageDef) (rule : RewriteRule) : Option BindingPlan :=
  (GeneralRuleBindingGrammar.infer? language rule).map fun result =>
    ⟨result.spec, .inferredGrammar result.extraTypes⟩

def compile? (language : LanguageDef) (rule : RewriteRule) : Option BindingPlan :=
  match rule.bindings with
  | some spec =>
      if admittedFor rule spec && dependencySortsDeclared language spec then
        some ⟨spec, .authored⟩
      else none
  | none =>
      let spec := inferredSpec rule
      if rootInput 0 rule.left && rootDeclared rule && admittedFor rule spec &&
          dependencySortsDeclared language spec then
        some ⟨spec, .inferredRootInputs⟩
      else grammarPlan? language rule

theorem compile_admitted {language : LanguageDef} {rule : RewriteRule} {plan : BindingPlan}
    (compiled : compile? language rule = some plan) :
    admittedFor (plan.elaborate rule) plan.spec = true ∧
      dependencySortsDeclared language plan.spec = true := by
  unfold compile? at compiled
  cases declared : rule.bindings with
  | some spec =>
      simp only [declared] at compiled
      split at compiled
      next accepted =>
        cases Option.some.inj compiled
        simpa [BindingPlan.elaborate, BindingPlan.implicitTypes, admittedFor,
          occurrenceDeclared, occurrenceDepthAtSite?, sitePattern?, siteBinderDepth?]
          using Bool.and_eq_true_iff.mp accepted
      next => contradiction
  | none =>
      simp only [declared] at compiled
      split at compiled
      next accepted =>
        cases Option.some.inj compiled
        simpa [BindingPlan.elaborate, BindingPlan.implicitTypes, admittedFor,
          occurrenceDeclared, occurrenceDepthAtSite?, sitePattern?, siteBinderDepth?] using
          (show admittedFor rule (inferredSpec rule) = true ∧
            dependencySortsDeclared language (inferredSpec rule) = true from
            ⟨(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).1).2,
              (Bool.and_eq_true_iff.mp accepted).2⟩)
      next =>
        obtain ⟨result, inferred, same⟩ := Option.map_eq_some_iff.mp compiled
        subst plan
        exact GeneralRuleBindingGrammar.infer_admitted inferred

theorem compile_origin {language : LanguageDef} {rule : RewriteRule} {plan : BindingPlan}
    (compiled : compile? language rule = some plan) :
    (plan.origin = .authored ∧ rule.bindings = some plan.spec) ∨
      (plan.origin = .inferredRootInputs ∧ rule.bindings = none ∧
        plan.spec = inferredSpec rule ∧ rootInput 0 rule.left = true ∧ rootDeclared rule = true) ∨
      (rule.bindings = none ∧ ∃ result,
        GeneralRuleBindingGrammar.infer? language rule = some result ∧
          plan.origin = .inferredGrammar result.extraTypes ∧ plan.spec = result.spec) := by
  unfold compile? at compiled
  cases declared : rule.bindings with
  | some spec =>
      simp only [declared] at compiled
      split at compiled
      next =>
        cases Option.some.inj compiled
        exact Or.inl ⟨rfl, rfl⟩
      next => contradiction
  | none =>
      simp only [declared] at compiled
      split at compiled
      next accepted =>
        cases Option.some.inj compiled
        exact Or.inr (Or.inl ⟨rfl, rfl, rfl,
          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
            (Bool.and_eq_true_iff.mp accepted).1).1).1,
          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
            (Bool.and_eq_true_iff.mp accepted).1).1).2⟩)
      next =>
        obtain ⟨result, inferred, same⟩ := Option.map_eq_some_iff.mp compiled
        subst plan
        exact Or.inr (Or.inr ⟨rfl, result, inferred, rfl, rfl⟩)

theorem elaborate_source (plan : BindingPlan) (rule : RewriteRule) :
    (plan.elaborate rule).name = rule.name ∧
      (plan.elaborate rule).left = rule.left ∧
      (plan.elaborate rule).right = rule.right ∧
      (plan.elaborate rule).premises = rule.premises := ⟨rfl, rfl, rfl, rfl⟩

theorem inferred_dependencies_empty {rule : RewriteRule} {name : String}
    {dependencies : List TypeExpr}
    (found : dependencies? (inferredSpec rule) name = some dependencies) : dependencies = [] := by
  unfold dependencies? at found
  split at found <;> try contradiction
  next rowName rowDependencies rows =>
    have members : (rowName, rowDependencies) ∈ (inferredSpec rule).dependencies := by
      have first : (rowName, rowDependencies) ∈
          (inferredSpec rule).dependencies.filter (fun entry => entry.1 == name) := by
        rw [rows]
        simp
      exact List.mem_of_mem_filter first
    obtain ⟨entry, _, equal⟩ := List.mem_map.mp members
    have empty : rowDependencies = [] := (Prod.ext_iff.mp equal).2.symm
    cases Option.some.inj found
    exact empty

theorem inferred_arguments_empty {rule : RewriteRule} {name : String}
    {site : RulePatternSite} {path : List Nat} {arguments : List Pattern}
    (declared : dependencies? (inferredSpec rule) name = some [])
    (occurrence : arguments? rule (inferredSpec rule) name site path = some arguments) :
    arguments = [] := by
  unfold arguments? at occurrence
  rw [declared] at occurrence
  simp only [Option.bind_some, inferredSpec, List.filter_nil, List.isEmpty_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff] at occurrence
  obtain ⟨token, _guarded, equal⟩ := occurrence
  exact (Option.some.inj equal).symm

/-- Every successful inferred capture is read back using no local bound
dependencies. The checked forward substitution recovers the actual input. -/
theorem inferred_capture_interpretation {rule : RewriteRule} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : Assignment}
    {name : String} {target : Pattern}
    (captured : capture? rule (inferredSpec rule) ambient depth site path initial name target = some final) :
    ∃ value,
      value.dependencies = [] ∧ value.ambient = ambient ∧
      lookup final name = some value ∧ instantiateValue? value ambient depth [] = some target := by
  obtain ⟨dependencies, arguments, value, declared, occurrence, recovered, retained, interpreted, _⟩ :=
    capture_interpretation captured
  have emptyDependencies := inferred_dependencies_empty declared
  have emptyArguments := inferred_arguments_empty (emptyDependencies ▸ declared) occurrence
  have contextual := recoverValue?_context dependencies ambient depth arguments target value recovered
  exact ⟨value, contextual.1.trans emptyDependencies, contextual.2, retained,
    emptyArguments ▸ interpreted⟩

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference
