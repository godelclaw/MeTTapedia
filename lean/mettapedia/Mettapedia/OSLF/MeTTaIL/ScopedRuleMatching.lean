import Mettapedia.OSLF.MeTTaIL.RuleBinding
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Matching and instantiation with rule occurrence contexts

This interpreter consumes a binding specification attached to an authored
`RewriteRule`. Each captured value retains its declared dependency context and
the caller's ambient context. An explicit occurrence substitution determines
how that value is used at each later site. The matcher supports injective
variable spines at input occurrences; output occurrences may supply general
terms. All collection choices remain list occurrences.
-/

namespace Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)

set_option autoImplicit false

abbrev Assignment := List (String × ContextualValue)

def lookup (assignment : Assignment) (name : String) : Option ContextualValue :=
  assignment.find? (fun entry => entry.1 == name) |>.map (·.2)

/-- Extend an assignment or check a repeated occurrence. A second occurrence
may have a different binder depth or spine, but must recover the same body. -/
def assign (assignment : Assignment) (name : String) (value : ContextualValue) :
    Option Assignment :=
  match lookup assignment name with
  | none => some ((name, value) :: assignment)
  | some prior => if prior == value then some assignment else none

/-- The ordinary comparison observes the exact captured body. -/
def literalBodyComparison (_name : String) (left right : Pattern) : Bool := left == right

/-- Compare repeated bodies only after checking their exact contextual
indices. A successful repeat keeps the first raw value and its occurrence. -/
def assignWith (compare : String → Pattern → Pattern → Bool)
    (assignment : Assignment) (name : String) (value : ContextualValue) : Option Assignment :=
  match lookup assignment name with
  | none => some ((name, value) :: assignment)
  | some prior =>
      if prior.dependencies == value.dependencies && prior.ambient == value.ambient &&
          compare name prior.body value.body then some assignment else none

/-- Literal body comparison recovers the original whole-value equality check. -/
@[simp] theorem assignWith_literal (assignment : Assignment) (name : String)
    (value : ContextualValue) :
    assignWith literalBodyComparison assignment name value = assign assignment name value := by
  cases stored : lookup assignment name with
  | none => simp only [assignWith, assign, stored]
  | some prior =>
      simp only [assignWith, assign, stored, literalBodyComparison]
      by_cases same : prior = value
      · subst prior
        simp
      · have rejected : (prior.dependencies == value.dependencies &&
            prior.ambient == value.ambient && prior.body == value.body) = false := by
          apply Bool.eq_false_iff.mpr
          intro accepted
          apply same
          cases prior
          cases value
          simp_all only [Bool.and_eq_true, beq_iff_eq]
        simp [rejected, same]

/-- Capture at this exact occurrence; the source pattern, path and declared
spine are all read from the same authored rule. -/
def capture? (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient depth : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : Assignment) (name : String) (target : Pattern) :
    Option Assignment := do
  let dependencies ← dependencies? spec name
  let arguments ← arguments? rule spec name site path
  let value ← recoverValue? dependencies ambient depth arguments target
  assign assignment name value

/-- Capture a collection rest with the same context semantics as an ordinary
metavariable, retaining its tag and the multiplicity/order of the residual. -/
def captureRest? (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient depth : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : Assignment) (name : String) (kind : CollType)
    (elements : List Pattern) : Option Assignment :=
  capture? rule spec ambient depth site path assignment name
    (.collection kind elements none)

/-- Recover the same contextual value and use the chosen body observation
only when reconciling a repeated metavariable. -/
def captureWith? (compare : String → Pattern → Pattern → Bool)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient depth : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : Assignment) (name : String) (target : Pattern) : Option Assignment := do
  let dependencies ← dependencies? spec name
  let arguments ← arguments? rule spec name site path
  let value ← recoverValue? dependencies ambient depth arguments target
  assignWith compare assignment name value

/-- Collection residuals retain their tag, order and multiplicity. -/
def captureRestWith? (compare : String → Pattern → Pattern → Bool)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient depth : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : Assignment) (name : String) (kind : CollType)
    (elements : List Pattern) : Option Assignment :=
  captureWith? compare rule spec ambient depth site path assignment name
    (.collection kind elements none)

@[simp] theorem captureWith?_literal (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient depth : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : Assignment) (name : String) (target : Pattern) :
    captureWith? literalBodyComparison rule spec ambient depth site path assignment name target =
      capture? rule spec ambient depth site path assignment name target := by
  simp only [captureWith?, capture?, assignWith_literal]

@[simp] theorem captureRestWith?_literal (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient depth : Nat) (site : RulePatternSite) (path : List Nat)
    (assignment : Assignment) (name : String) (kind : CollType) (elements : List Pattern) :
    captureRestWith? literalBodyComparison rule spec ambient depth site path assignment name kind elements =
      captureRest? rule spec ambient depth site path assignment name kind elements := by
  simp only [captureRestWith?, captureRest?, captureWith?_literal]

mutual
/-- Match a pattern under its actual binder depth. -/
def matchAtWith (compare : String → Pattern → Pattern → Bool)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) : Pattern → Pattern → List Assignment
  | .fvar name, target =>
      (captureWith? compare rule spec ambient depth site path assignment name target).toList
  | .bvar expected, .bvar actual =>
      if expected == actual then [assignment] else []
  | .apply constructor patterns, .apply actualConstructor targets =>
      if constructor == actualConstructor then
        matchArgsAtWith compare rule spec ambient site path depth assignment 0 patterns targets
      else []
  | .lambda _ body, .lambda _ target =>
      matchAtWith compare rule spec ambient site (path ++ [0]) (depth + 1)
        assignment body target
  | .multiLambda arity _ body, .multiLambda actualArity _ target =>
      if arity == actualArity then
        matchAtWith compare rule spec ambient site (path ++ [0]) (depth + arity)
          assignment body target
      else []
  | .subst body replacement, .subst targetBody targetReplacement =>
      (matchAtWith compare rule spec ambient site (path ++ [0]) (depth + 1)
        assignment body targetBody).flatMap fun found =>
        matchAtWith compare rule spec ambient site (path ++ [1]) depth
          found replacement targetReplacement
  | .collection kind patterns rest, .collection actualKind targets actualRest =>
      if kind == actualKind && actualRest.isNone then
        if kind == .vec then
          match rest with
          | none =>
              matchArgsAtWith compare rule spec ambient site path depth assignment 0 patterns targets
          | some name =>
              (matchArgsAtWith compare rule spec ambient site path depth assignment 0
                patterns (targets.take patterns.length)).filterMap fun found =>
                  captureRestWith? compare rule spec ambient depth site
                    (path ++ [patterns.length]) found name kind
                    (targets.drop patterns.length)
        else
          matchBagAtWith compare rule spec ambient site path depth assignment 0
            patterns rest kind targets
      else []
  | _, _ => []
termination_by pattern _target => sizeOf pattern

/-- Match an ordered argument or vector-element row. -/
def matchArgsAtWith (compare : String → Pattern → Pattern → Bool)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (index : Nat) :
    List Pattern → List Pattern → List Assignment
  | [], [] => [assignment]
  | pattern :: patterns, target :: targets =>
      (matchAtWith compare rule spec ambient site (path ++ [index]) depth
        assignment pattern target).flatMap fun found =>
        matchArgsAtWith compare rule spec ambient site path depth found (index + 1)
          patterns targets
  | _, _ => []
termination_by patterns _targets => sizeOf patterns

/-- Enumerate bag/set element choices without collapsing occurrences. -/
def matchBagAtWith (compare : String → Pattern → Pattern → Bool)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (index : Nat) :
    List Pattern → Option String → CollType → List Pattern → List Assignment
  | [], none, _, targets => if targets.isEmpty then [assignment] else []
  | [], some name, kind, targets =>
      (captureRestWith? compare rule spec ambient depth site (path ++ [index])
        assignment name kind targets).toList
  | pattern :: patterns, rest, kind, targets =>
      targets.zipIdx.flatMap fun (target, selected) =>
        (matchAtWith compare rule spec ambient site (path ++ [index]) depth
          assignment pattern target).flatMap fun found =>
            matchBagAtWith compare rule spec ambient site path depth found (index + 1)
              patterns rest kind (targets.eraseIdx selected)
termination_by patterns _rest _kind _targets => sizeOf patterns
end

/-- Match one authored rule in a caller-supplied ambient context. -/
def matchRuleWithAt (compare : String → Pattern → Pattern → Bool)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (target : Pattern) : List Assignment :=
  matchAtWith compare rule spec ambient .left [] 0 [] rule.left target

/-- Ordinary matching specializes the shared traversal to literal bodies. -/
def matchAt (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) : Pattern → Pattern → List Assignment :=
  matchAtWith literalBodyComparison rule spec ambient site path depth assignment

def matchArgsAt (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (index : Nat) : List Pattern → List Pattern → List Assignment :=
  matchArgsAtWith literalBodyComparison rule spec ambient site path depth assignment index

def matchBagAt (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (index : Nat) :
    List Pattern → Option String → CollType → List Pattern → List Assignment :=
  matchBagAtWith literalBodyComparison rule spec ambient site path depth assignment index

/-- A metavariable match exposes the same retained contextual capture as
the ordinary capture interface. -/
theorem matchAt_fvar (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (name : String) (target : Pattern) :
    matchAt rule spec ambient site path depth assignment (.fvar name) target =
      (capture? rule spec ambient depth site path assignment name target).toList := by
  simp only [matchAt, matchAtWith, captureWith?_literal]

/-- The ordinary rule interface retains all match occurrences. -/
def matchRuleAt (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (target : Pattern) : List Assignment :=
  matchRuleWithAt literalBodyComparison rule spec ambient target

/-- Reuse the ordinary interface after selecting literal comparison. -/
theorem matchRuleWithAt_literal (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (target : Pattern) :
    matchRuleWithAt literalBodyComparison rule spec ambient target =
      matchRuleAt rule spec ambient target := rfl

mutual
/-- Instantiate a rule pattern at one exact site. This uses the captured
context rather than reading the first LHS occurrence's depth. -/
def instantiateWith? (operation : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) : Pattern → Option Pattern
  | .fvar name => do
      let value ← lookup assignment name
      let arguments ← arguments? rule spec name site path
      instantiateValue? value ambient depth arguments
  | .bvar index => some (.bvar index)
  | .apply constructor arguments => do
      let results ← instantiateArgsWith? operation rule spec ambient site path depth
        assignment 0 arguments
      some (.apply constructor results)
  | .lambda binder body => do
      let result ← instantiateWith? operation rule spec ambient site (path ++ [0])
        (depth + 1) assignment body
      some (.lambda binder result)
  | .multiLambda arity binders body => do
      let result ← instantiateWith? operation rule spec ambient site (path ++ [0])
        (depth + arity) assignment body
      some (.multiLambda arity binders result)
  | .subst body replacement => do
      let body' ← instantiateWith? operation rule spec ambient site (path ++ [0])
        (depth + 1) assignment body
      let replacement' ← instantiateWith? operation rule spec ambient site (path ++ [1])
        depth assignment replacement
      some (operation replacement' body')
  | .collection kind elements rest => do
      let explicit ← instantiateArgsWith? operation rule spec ambient site path depth
        assignment 0 elements
      match rest with
      | none => some (.collection kind explicit none)
      | some name =>
          let value ← lookup assignment name
          let arguments ← arguments? rule spec name site (path ++ [elements.length])
          match ← instantiateValue? value ambient depth arguments with
          | .collection actualKind residual none =>
              if actualKind == kind then
                some (.collection kind (explicit ++ residual) none)
              else none
          | _ => none
termination_by pattern => sizeOf pattern

/-- Instantiate an ordered row without changing its occurrence addresses. -/
def instantiateArgsWith? (operation : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (index : Nat) :
    List Pattern → Option (List Pattern)
  | [] => some []
  | pattern :: patterns => do
      let head ← instantiateWith? operation rule spec ambient site (path ++ [index])
        depth assignment pattern
      let tail ← instantiateArgsWith? operation rule spec ambient site path depth assignment
        (index + 1) patterns
      some (head :: tail)
termination_by patterns => sizeOf patterns
end

/-- Ordinary binder elimination specializes the shared scoped traversal. -/
def instantiateAt? (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (pattern : Pattern) : Option Pattern :=
  instantiateWith? instantiateBVar rule spec ambient site path depth assignment pattern

/-- Ordered ordinary instantiation uses the same occurrence traversal. -/
def instantiateArgsAt? (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (index : Nat) (patterns : List Pattern) :
    Option (List Pattern) :=
  instantiateArgsWith? instantiateBVar rule spec ambient site path depth assignment index patterns

/-- Instantiate the exact authored RHS with the chosen binder operation. -/
def reductWith? (operation : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (assignment : Assignment) : Option Pattern :=
  instantiateWith? operation rule spec ambient .right [] 0 assignment rule.right

/-- The reduct is the instantiated authored right-hand side. -/
def reduct? (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (assignment : Assignment) : Option Pattern :=
  instantiateAt? rule spec ambient .right [] 0 assignment rule.right

/-- Specializing the whole RHS preserves its ordinary public interface. -/
@[simp] theorem reductWith?_ordinary (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) :
    reductWith? instantiateBVar rule spec ambient = reduct? rule spec ambient := rfl

/-- Project values available at the rule root for the existing ordered
premise interpreter. A value that still needs a local binder is unavailable
there; its explicit occurrence spine must be interpreted in a later extension
of the premise machine. -/
def projectRoot? (ambient : Nat) (assignment : Assignment) : Option Bindings :=
  assignment.mapM fun (name, value) => do
    let result ← instantiateValue? value ambient 0 []
    some (name, result)

/-- Reconcile one root-premise output with a scoped assignment. Repeated
names retain their earlier contextual value when projection agrees. -/
def reconcileRootResult? (spec : RuleBindingSpec) (ambient : Nat)
    (assignment : Assignment) (entry : String × Pattern) : Option Assignment :=
  match entry with
  | (name, result) =>
    match lookup assignment name with
    | some existing => do
        let projected ← instantiateValue? existing ambient 0 []
        if projected == result then some assignment else none
    | none => do
        let dependencies ← dependencies? spec name
        let value ← recoverValue? dependencies ambient 0 [] result
        assign assignment name value

/-- Reconcile ordered premise machine results with the scoped assignment.
New outputs are recovered at the rule root and retain ambient variables. -/
def extendRoot? (spec : RuleBindingSpec) (ambient : Nat)
    (assignment : Assignment) (raw : Bindings) : Option Assignment :=
  raw.foldlM (init := assignment) (reconcileRootResult? spec ambient)

/-- Patterns whose collections retain a fixed element order. Collection rest
capture is included; unordered collection choices are a separate fragment. -/
inductive OrderedPattern : Pattern → Prop where
  | fvar (name : String) : OrderedPattern (.fvar name)
  | bvar (index : Nat) : OrderedPattern (.bvar index)
  | apply (label : String) (patterns : List Pattern)
      (children : ∀ pattern ∈ patterns, OrderedPattern pattern) : OrderedPattern (.apply label patterns)
  | lambda (display : Option String) (body : Pattern) (child : OrderedPattern body) :
      OrderedPattern (.lambda display body)
  | multiLambda (arity : Nat) (display : List String) (body : Pattern) (child : OrderedPattern body) :
      OrderedPattern (.multiLambda arity display body)
  | subst (body replacement : Pattern) (first : OrderedPattern body) (second : OrderedPattern replacement) :
      OrderedPattern (.subst body replacement)
  | vector (patterns : List Pattern) (rest : Option String)
      (children : ∀ pattern ∈ patterns, OrderedPattern pattern) : OrderedPattern (.collection .vec patterns rest)


end Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

/-! ## Free-name coverage of the original operations -/

namespace Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

open Mettapedia.OSLF.MeTTaIL.Syntax
open RuleBinding
open Substitution

theorem lookup_member (assignment : Assignment) (name : String)
    (value : ContextualValue) (found : lookup assignment name = some value) :
    (name, value) ∈ assignment := by
  unfold lookup at found
  cases selected : assignment.find? (fun entry => entry.1 == name) with
  | none => simp [selected] at found
  | some pair =>
      have member := List.mem_of_find?_eq_some selected
      have named := List.find?_some selected
      simp only [beq_iff_eq] at named
      simp only [selected, Option.map_some, Option.some.injEq] at found
      cases pair with
      | mk actualName actualValue =>
          dsimp only at named found member
          subst actualName
          subst actualValue
          exact member

def assignmentFreeWithin (footprint : List String) (assignment : Assignment) : Prop :=
  ∀ entry ∈ assignment, ∀ name ∈ entry.2.body.freeFvarNames, name ∈ footprint
theorem assigned_free_within (footprint : List String) (initial final : Assignment)
    (name : String) (value : ContextualValue)
    (before : assignmentFreeWithin footprint initial)
    (captured : ∀ name ∈ value.body.freeFvarNames, name ∈ footprint)
    (assigned : assign initial name value = some final) : assignmentFreeWithin footprint final := by
  unfold assign at assigned
  cases found : lookup initial name with
  | none =>
      simp only [found, Option.some.injEq] at assigned
      subst final
      intro entry member free occurs
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact captured free occurs
      · exact before entry member free occurs
  | some prior =>
      simp only [found] at assigned
      split at assigned
      · cases assigned
        exact before
      · cases assigned

theorem capture_free_within (footprint : List String)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient depth : Nat)
    (site : RulePatternSite) (path : List Nat) (initial final : Assignment) (name : String) (target : Pattern)
    (before : assignmentFreeWithin footprint initial)
    (covered : ∀ name ∈ target.freeFvarNames, name ∈ footprint)
    (captured : capture? rule spec ambient depth site path initial name target = some final) :
    assignmentFreeWithin footprint final := by
  unfold capture? at captured
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at captured
  rcases captured with ⟨dependencies, _dependenciesFound, arguments, _argumentsFound, value, recovered, assigned⟩
  apply assigned_free_within footprint initial final name value before _ assigned
  rw [recovered_body_free_names dependencies ambient depth arguments target value recovered]
  exact covered

theorem capture_rest_free_within (footprint : List String)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient depth : Nat)
    (site : RulePatternSite) (path : List Nat) (initial final : Assignment)
    (name : String) (kind : CollType) (targets : List Pattern)
    (before : assignmentFreeWithin footprint initial)
    (covered : patternsFreeWithin footprint targets)
    (captured : captureRest? rule spec ambient depth site path initial name kind targets = some final) :
    assignmentFreeWithin footprint final := by
  apply capture_free_within footprint rule spec ambient depth site path initial final name (.collection kind targets none) before _ captured
  intro free occurs
  simp only [Pattern.freeFvarNames, Option.toList_none, List.append_nil, List.mem_flatMap] at occurs
  rcases occurs with ⟨target, member, occurs⟩
  exact covered target member free occurs
mutual
theorem instantiate_with_free_within (footprint : List String)
    (operation : Pattern → Pattern → Pattern)
    (operationCovered : ∀ replacement body,
      (∀ name ∈ replacement.freeFvarNames, name ∈ footprint) →
      (∀ name ∈ body.freeFvarNames, name ∈ footprint) →
      ∀ name ∈ (operation replacement body).freeFvarNames, name ∈ footprint)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (schema target : Pattern)
    (stored : assignmentFreeWithin footprint assignment)
    (argumentsCovered : ∀ name site path arguments,
      arguments? rule spec name site path = some arguments →
      patternsFreeWithin footprint arguments)
    (success : instantiateWith? operation rule spec ambient site path depth assignment schema = some target) :
    ∀ name ∈ target.freeFvarNames, name ∈ footprint := by
  cases schema with
  | bvar index =>
      simp only [instantiateWith?, Option.some.injEq] at success
      cases success
      intro name occurs
      simp only [Pattern.freeFvarNames, List.not_mem_nil] at occurs
  | fvar name =>
      simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      rcases success with ⟨value, found, arguments, argumentLookup, instantiated⟩
      exact instantiate_value_free_within footprint value ambient depth arguments target
        (stored _ (lookup_member assignment name value found))
        (argumentsCovered name site path arguments argumentLookup) instantiated
  | apply constructor arguments =>
      simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      rcases success with ⟨results, completed, success⟩
      cases success
      intro name occurs
      simp only [Pattern.freeFvarNames, List.mem_flatMap] at occurs
      rcases occurs with ⟨result, member, occurs⟩
      exact instantiate_args_with_free_within footprint operation operationCovered rule spec ambient
        site path depth assignment 0 arguments results stored argumentsCovered completed result member name occurs
  | lambda binder body =>
      simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      rcases success with ⟨result, completed, success⟩
      cases success
      simp only [Pattern.freeFvarNames]
      exact instantiate_with_free_within footprint operation operationCovered rule spec ambient site
        (path ++ [0]) (depth + 1) assignment body result stored argumentsCovered completed
  | multiLambda arity binders body =>
      simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      rcases success with ⟨result, completed, success⟩
      cases success
      simp only [Pattern.freeFvarNames]
      exact instantiate_with_free_within footprint operation operationCovered rule spec ambient site
        (path ++ [0]) (depth + arity) assignment body result stored argumentsCovered completed
  | subst body replacement =>
      simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      rcases success with ⟨bodyResult, bodyCompleted, replacementResult, replacementCompleted, success⟩
      cases success
      apply operationCovered replacementResult bodyResult
      · exact instantiate_with_free_within footprint operation operationCovered rule spec ambient site
          (path ++ [1]) depth assignment replacement replacementResult stored argumentsCovered replacementCompleted
      · exact instantiate_with_free_within footprint operation operationCovered rule spec ambient site
          (path ++ [0]) (depth + 1) assignment body bodyResult stored argumentsCovered bodyCompleted
  | collection kind elements rest =>
      simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      rcases success with ⟨explicit, completed, success⟩
      have explicitCovered := instantiate_args_with_free_within footprint operation operationCovered
        rule spec ambient site path depth assignment 0 elements explicit stored argumentsCovered completed
      cases rest with
      | none =>
          cases success
          intro name occurs
          simp only [Pattern.freeFvarNames, Option.toList_none, List.append_nil, List.mem_flatMap] at occurs
          rcases occurs with ⟨element, member, occurs⟩
          exact explicitCovered element member name occurs
      | some name =>
          simp only [Option.bind_eq_some_iff] at success
          rcases success with ⟨value, found, arguments, argumentLookup, resolved, instantiated, success⟩
          have resolvedCovered := instantiate_value_free_within footprint value ambient depth arguments resolved
            (stored _ (lookup_member assignment name value found))
            (argumentsCovered name site (path ++ [elements.length]) arguments argumentLookup) instantiated
          split at success <;> try cases success
          split at success <;> cases success
          intro free occurs
          simp only [Pattern.freeFvarNames, Option.toList_none, List.append_nil,
            List.flatMap_append, List.mem_append] at occurs
          rcases occurs with occurs | occurs
          · rcases List.mem_flatMap.mp occurs with ⟨element, member, occurs⟩
            exact explicitCovered element member free occurs
          · apply resolvedCovered free
            simpa only [Pattern.freeFvarNames, Option.toList_none, List.append_nil] using occurs
termination_by sizeOf schema

theorem instantiate_args_with_free_within (footprint : List String)
    (operation : Pattern → Pattern → Pattern)
    (operationCovered : ∀ replacement body,
      (∀ name ∈ replacement.freeFvarNames, name ∈ footprint) →
      (∀ name ∈ body.freeFvarNames, name ∈ footprint) →
      ∀ name ∈ (operation replacement body).freeFvarNames, name ∈ footprint)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (index : Nat) (schemas targets : List Pattern)
    (stored : assignmentFreeWithin footprint assignment)
    (argumentsCovered : ∀ name site path arguments,
      arguments? rule spec name site path = some arguments →
      patternsFreeWithin footprint arguments)
    (success : instantiateArgsWith? operation rule spec ambient site path depth assignment index schemas = some targets) :
    patternsFreeWithin footprint targets := by
  cases schemas with
  | nil =>
      simp only [instantiateArgsWith?, Option.some.injEq] at success
      cases success
      intro pattern member
      simp only [List.not_mem_nil] at member
  | cons schema schemas =>
      simp only [instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      rcases success with ⟨head, headCompleted, tail, tailCompleted, success⟩
      cases success
      intro pattern member
      rcases List.mem_cons.mp member with rfl | member
      · exact instantiate_with_free_within footprint operation operationCovered rule spec ambient
          site (path ++ [index]) depth assignment schema _ stored argumentsCovered headCompleted
      · exact instantiate_args_with_free_within footprint operation operationCovered rule spec ambient
          site path depth assignment (index + 1) schemas tail stored argumentsCovered tailCompleted pattern member
termination_by sizeOf schemas
end

private theorem ground_list_each (depth : Nat) (patterns : List Pattern)
    (ground : Pattern.isGroundListAt depth patterns = true) :
    ∀ pattern ∈ patterns, pattern.isGroundAt depth = true := by
  induction patterns with
  | nil => intro pattern member; cases member
  | cons head tail ih =>
      simp only [Pattern.isGroundListAt, Bool.and_eq_true] at ground
      intro pattern member
      rcases List.mem_cons.mp member with rfl | member
      · exact ground.1
      · exact ih ground.2 pattern member
theorem admitted_occurrence_arguments_free (rule : RewriteRule) (spec : RuleBindingSpec)
    (admitted : admittedFor rule spec = true) (row : MetavariableOccurrence)
    (member : row ∈ spec.occurrences) :
    ∀ argument ∈ row.arguments, argument.freeFvarNames = [] := by
  have rows := admitted
  simp only [admittedFor, Bool.and_eq_true] at rows
  have rows := rows.2
  have checked := List.all_eq_true.mp rows row member
  simp only [Bool.and_eq_true] at checked
  cases dependenciesFound : dependencies? spec row.name with
  | none =>
      simp only [dependenciesFound, Bool.false_eq_true] at checked
      exact False.elim checked.2
  | some dependencies =>
      cases depthFound : occurrenceDepthAtSite? rule row.site row.path with
      | none =>
          simp only [dependenciesFound, depthFound, Bool.false_eq_true] at checked
          exact False.elim checked.2
      | some depth =>
          simp only [dependenciesFound, depthFound, Bool.and_eq_true] at checked
          intro argument member
          exact ground_free_names argument depth (List.all_eq_true.mp checked.2.2 argument member)

theorem admitted_arguments_free (rule : RewriteRule) (spec : RuleBindingSpec)
    (admitted : admittedFor rule spec = true)
    (name : String) (site : RulePatternSite) (path : List Nat) (arguments : List Pattern)
    (success : arguments? rule spec name site path = some arguments) :
    ∀ argument ∈ arguments, argument.freeFvarNames = [] := by
  unfold arguments? at success
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at success
  rcases success with ⟨dependencies, _dependencyLookup, guardValue, _declared, success⟩
  split at success
  · split at success <;> cases success
    intro argument member
    cases member
  · rename_i row rows
    split at success <;> cases success
    apply admitted_occurrence_arguments_free rule spec admitted row
    have selected : row ∈ spec.occurrences.filter
        (fun candidate => candidate.name == name && candidate.site == site && candidate.path == path) := by
      rw [rows]
      simp
    exact (List.mem_filter.mp selected).1
  · cases success

theorem admitted_arguments_free_within (footprint : List String)
    (rule : RewriteRule) (spec : RuleBindingSpec) (admitted : admittedFor rule spec = true)
    (name : String) (site : RulePatternSite) (path : List Nat) (arguments : List Pattern)
    (success : arguments? rule spec name site path = some arguments) :
    patternsFreeWithin footprint arguments := by
  intro argument member free occurs
  rw [admitted_arguments_free rule spec admitted name site path arguments success argument member] at occurs
  cases occurs

theorem admitted_instantiate_with_free_within (footprint : List String)
    (operation : Pattern → Pattern → Pattern)
    (operationCovered : ∀ replacement body,
      (∀ name ∈ replacement.freeFvarNames, name ∈ footprint) →
      (∀ name ∈ body.freeFvarNames, name ∈ footprint) →
      ∀ name ∈ (operation replacement body).freeFvarNames, name ∈ footprint)
    (rule : RewriteRule) (spec : RuleBindingSpec) (admitted : admittedFor rule spec = true)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (schema target : Pattern)
    (stored : assignmentFreeWithin footprint assignment)
    (success : instantiateWith? operation rule spec ambient site path depth assignment schema = some target) :
    ∀ name ∈ target.freeFvarNames, name ∈ footprint :=
  instantiate_with_free_within footprint operation operationCovered rule spec ambient site path depth
    assignment schema target stored (admitted_arguments_free_within footprint rule spec admitted) success

theorem admitted_reduct_with_free_within (footprint : List String)
    (operation : Pattern → Pattern → Pattern)
    (operationCovered : ∀ replacement body,
      (∀ name ∈ replacement.freeFvarNames, name ∈ footprint) →
      (∀ name ∈ body.freeFvarNames, name ∈ footprint) →
      ∀ name ∈ (operation replacement body).freeFvarNames, name ∈ footprint)
    (rule : RewriteRule) (spec : RuleBindingSpec) (admitted : admittedFor rule spec = true)
    (ambient : Nat) (assignment : ScopedRuleMatching.Assignment) (target : Pattern)
    (stored : assignmentFreeWithin footprint assignment)
    (success : reductWith? operation rule spec ambient assignment = some target) :
    ∀ name ∈ target.freeFvarNames, name ∈ footprint :=
  admitted_instantiate_with_free_within footprint operation operationCovered rule spec admitted ambient
    .right [] 0 assignment rule.right target stored success

theorem ordinary_reduct_free_within (footprint : List String)
    (rule : RewriteRule) (spec : RuleBindingSpec) (admitted : admittedFor rule spec = true)
    (ambient : Nat) (assignment : ScopedRuleMatching.Assignment) (target : Pattern)
    (stored : assignmentFreeWithin footprint assignment)
    (success : reduct? rule spec ambient assignment = some target) :
    ∀ name ∈ target.freeFvarNames, name ∈ footprint :=
  admitted_reduct_with_free_within footprint Substitution.instantiateBVar
    (instantiate_bvar_free_within footprint) rule spec admitted ambient assignment target stored success

namespace FootprintControls

theorem complete_stored_body_covered :
    assignmentFreeWithin ["kept"] [("unused", ⟨[.base "Name"], 2, .fvar "kept"⟩)] := by
  simp [assignmentFreeWithin, Pattern.freeFvarNames]

theorem unused_stored_body_cannot_be_ignored :
    ¬ assignmentFreeWithin [] [("unused", ⟨[.base "Name"], 2, .fvar "outside"⟩)] := by
  simp [assignmentFreeWithin, Pattern.freeFvarNames]

end FootprintControls

#print axioms Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.lookup_member
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.assignmentFreeWithin
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.assigned_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.capture_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.capture_rest_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.instantiate_with_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.instantiate_args_with_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.admitted_occurrence_arguments_free
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.admitted_arguments_free
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.admitted_arguments_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.admitted_instantiate_with_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.admitted_reduct_with_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.ordinary_reduct_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.FootprintControls.complete_stored_body_covered
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.FootprintControls.unused_stored_body_cannot_be_ignored

end Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
