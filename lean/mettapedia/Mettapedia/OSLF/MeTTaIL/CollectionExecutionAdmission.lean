import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
import Mettapedia.OSLF.MeTTaIL.CollectionSelectionSites
import Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine

/-!
# Admission for the finite root-collection execution strategy

This certificate permits one additional case beyond the general executor:
the selected rule may decompose a set at the root of its left side. Its element
schemas must still decompose no set and the rule must be unconditional, because
the finite collection batch publishes its reduct directly. Equations remain
set-free, and reduction contexts may not enter sets. Every other admission
obligation is retained unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionExecutionAdmission

open Syntax GeneralExecutionAdmission CanonicalBags GeneralTypedSites

/-- The specialized batch handles exactly one set layer. Nested schemas
continue through the original matcher. Premises are rejected until this
matcher is routed through the generic premise machine. -/
def ruleReady (rule : RewriteRule) : Bool :=
  match rule.left with
  | .collection .hashSet schemas _ =>
      setFreeList schemas && rule.premises.isEmpty
  | _ => setFreeRule rule

theorem ruleReady_spec {rule : RewriteRule} (ready : ruleReady rule = true) :
    setFreeRule rule = true ∨
      ∃ schemas rest, rule.left = .collection .hashSet schemas rest ∧
        setFreeList schemas = true ∧ rule.premises = [] := by
  cases left : rule.left with
  | collection kind schemas rest =>
      cases kind with
      | hashSet =>
          have parts : setFreeList schemas = true ∧ rule.premises = [] := by
            simpa [ruleReady, left] using ready
          exact .inr ⟨schemas, rest, rfl, parts⟩
      | vec | hashBag => exact .inl (by simpa [ruleReady, left] using ready)
  | _ => exact .inl (by simpa [ruleReady, left] using ready)

/-- All obligations except the one implemented by this execution strategy. -/
def inheritedObligations (plan : Plan) : List Obligation :=
  plan.obligations.filter (fun obligation => obligation != .setDecomposition)

/-- Decidable admission for the root-collection strategy. -/
def check (plan : Plan) : Bool :=
  (inheritedObligations plan).isEmpty &&
    (!plan.permissions.sites.collectionKinds.contains .hashSet &&
      (plan.rules.all (fun rule => ruleReady rule.rule) &&
        (plan.rules.all (fun rule =>
          RuleBinding.admittedFor rule.rule rule.binding.spec) &&
          plan.equations.all (fun equation => setFreeEquation equation.authored))))

structure Certificate (plan : Plan) : Type where
  checked : check plan = true

def admit? (plan : Plan) : Option (Certificate plan) :=
  if checked : check plan = true then some ⟨checked⟩ else none

theorem admit?_sound {plan : Plan} {certificate : Certificate plan}
    (_accepted : admit? plan = some certificate) : check plan = true :=
  certificate.checked

theorem inherited_discharged {plan : Plan} (certificate : Certificate plan) :
    inheritedObligations plan = [] := by
  have checked := certificate.checked
  have parts : (inheritedObligations plan).isEmpty = true ∧
      (!plan.permissions.sites.collectionKinds.contains .hashSet) = true ∧
      plan.rules.all (fun rule => ruleReady rule.rule) = true ∧
      plan.rules.all (fun rule =>
        RuleBinding.admittedFor rule.rule rule.binding.spec) = true ∧
      plan.equations.all (fun equation => setFreeEquation equation.authored) = true := by
    simpa only [check, Bool.and_eq_true] using checked
  exact List.isEmpty_iff.mp parts.1

theorem no_set_descent {plan : Plan} (certificate : Certificate plan) :
    NoSetDescent plan.permissions.sites := by
  have checked := certificate.checked
  have parts : (inheritedObligations plan).isEmpty = true ∧
      (!plan.permissions.sites.collectionKinds.contains .hashSet) = true ∧
      plan.rules.all (fun rule => ruleReady rule.rule) = true ∧
      plan.rules.all (fun rule =>
        RuleBinding.admittedFor rule.rule rule.binding.spec) = true ∧
      plan.equations.all (fun equation => setFreeEquation equation.authored) = true := by
    simpa only [check, Bool.and_eq_true] using checked
  simpa [NoSetDescent] using parts.2.1

theorem rules_ready {plan : Plan} (certificate : Certificate plan) {rule : RulePlan}
    (member : rule ∈ plan.rules) : ruleReady rule.rule = true := by
  have checked := certificate.checked
  have parts : (inheritedObligations plan).isEmpty = true ∧
      (!plan.permissions.sites.collectionKinds.contains .hashSet) = true ∧
      plan.rules.all (fun rule => ruleReady rule.rule) = true ∧
      plan.rules.all (fun rule =>
        RuleBinding.admittedFor rule.rule rule.binding.spec) = true ∧
      plan.equations.all (fun equation => setFreeEquation equation.authored) = true := by
    simpa only [check, Bool.and_eq_true] using checked
  exact List.all_eq_true.mp parts.2.2.1 rule member

theorem rules_admitted {plan : Plan} (certificate : Certificate plan) {rule : RulePlan}
    (member : rule ∈ plan.rules) :
    RuleBinding.admittedFor rule.rule rule.binding.spec = true := by
  have checked := certificate.checked
  have parts : (inheritedObligations plan).isEmpty = true ∧
      (!plan.permissions.sites.collectionKinds.contains .hashSet) = true ∧
      plan.rules.all (fun rule => ruleReady rule.rule) = true ∧
      plan.rules.all (fun rule =>
        RuleBinding.admittedFor rule.rule rule.binding.spec) = true ∧
      plan.equations.all (fun equation => setFreeEquation equation.authored) = true := by
    simpa only [check, Bool.and_eq_true] using checked
  exact List.all_eq_true.mp parts.2.2.2.1 rule member

theorem root_set_rule_unconditional {plan : Plan} (certificate : Certificate plan)
    {declaration : RulePlan} (member : declaration ∈ plan.rules)
    {schemas : List Pattern} {rest : Option String}
    (root : declaration.rule.left = .collection .hashSet schemas rest) :
    declaration.rule.premises = [] := by
  have ready := ruleReady_spec (rules_ready certificate member)
  rcases ready with ordinary | ⟨actualSchemas, actualRest, left, _, empty⟩
  · rw [setFreeRule, root, setFree] at ordinary
    contradiction
  · rw [root] at left
    cases Pattern.collection.inj left
    exact empty

theorem equations_set_free {plan : Plan} (certificate : Certificate plan)
    {equation : EquationPlan} (member : equation ∈ plan.equations) :
    setFreeEquation equation.authored = true := by
  have checked := certificate.checked
  have parts : (inheritedObligations plan).isEmpty = true ∧
      (!plan.permissions.sites.collectionKinds.contains .hashSet) = true ∧
      plan.rules.all (fun rule => ruleReady rule.rule) = true ∧
      plan.rules.all (fun rule =>
        RuleBinding.admittedFor rule.rule rule.binding.spec) = true ∧
      plan.equations.all (fun equation => setFreeEquation equation.authored) = true := by
    simpa only [check, Bool.and_eq_true] using checked
  exact List.all_eq_true.mp parts.2.2.2.2 equation member

/-- A source-derived request for the admitted root-collection matcher. The
selected declaration and its inferred binding specification remain intact. -/
def request? (plan : Plan) (_certificate : Certificate plan) (ordinal : Nat)
    (targets : List Pattern) : Option ScopedCollectionMachine.Request := do
  let declaration ← plan.rules[ordinal]?
  match declaration.rule.left with
  | .collection .vec _ _ => none
  | .collection kind schemas rest =>
      pure ⟨declaration.rule, declaration.binding.spec, 0, .left, [], 0, 0, [],
        schemas, rest, kind, arrange kind targets⟩
  | _ => none

theorem request?_selected {plan : Plan} {certificate : Certificate plan}
    {ordinal : Nat} {targets : List Pattern} {request : ScopedCollectionMachine.Request}
    (made : request? plan certificate ordinal targets = some request) :
    ∃ declaration, plan.rules[ordinal]? = some declaration ∧
      request.rule = declaration.rule ∧ request.spec = declaration.binding.spec ∧
      request.targets = arrange request.kind targets := by
  unfold request? at made
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at made
  obtain ⟨declaration, selected, made⟩ := made
  cases left : declaration.rule.left <;> simp [left] at made
  rename_i kind schemas rest
  cases kind with
  | vec => simp at made
  | hashBag | hashSet =>
      cases made
      exact ⟨declaration, selected, rfl, rfl, rfl⟩

theorem request?_unordered {plan : Plan} {certificate : Certificate plan}
    {ordinal : Nat} {targets : List Pattern} {request : ScopedCollectionMachine.Request}
    (made : request? plan certificate ordinal targets = some request) :
    request.kind ≠ .vec := by
  unfold request? at made
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at made
  obtain ⟨declaration, _, made⟩ := made
  cases left : declaration.rule.left <;> simp [left] at made
  rename_i kind schemas rest
  cases kind with
  | vec => simp at made
  | hashBag | hashSet =>
      cases made
      intro impossible
      cases impossible

theorem arrange_fixed (kind : CollType) (items : List Pattern) :
    arrange kind (arrange kind items) = arrange kind items := by
  cases kind with
  | vec => rfl
  | hashBag =>
      simp only [arrange_bag]
      exact PatternLexOrder.sortLex_eq_of_perm
        (PatternLexOrder.sortLex_perm items)
  | hashSet =>
      rw [arrange_set, arrange_set]
      have sorted : PatternLexOrder.sortLex
          (PatternLexOrder.sortLex items).dedup =
          (PatternLexOrder.sortLex items).dedup :=
        List.Perm.eq_of_pairwise'
          (PatternLexOrder.sortLex_pairwise _)
          ((PatternLexOrder.sortLex_pairwise items).sublist (List.dedup_sublist _))
          (PatternLexOrder.sortLex_perm _)
      rw [sorted, List.dedup_idem]

theorem request?_fixed {plan : Plan} {certificate : Certificate plan}
    {ordinal : Nat} {targets : List Pattern} {request : ScopedCollectionMachine.Request}
    (made : request? plan certificate ordinal targets = some request) :
    arrange request.kind request.targets = request.targets := by
  obtain ⟨_, _, _, _, targetEq⟩ := request?_selected made
  rw [targetEq]
  exact arrange_fixed request.kind targets

/-- Dispatch a concrete root collection only to rules declaring the same
collection kind. Source wrappers and open collection rests are rejected. -/
def requestForSource? (plan : Plan) (certificate : Certificate plan)
    (ordinal : Nat) : Pattern → Option ScopedCollectionMachine.Request
  | .collection actualKind targets none => do
      let request ← request? plan certificate ordinal targets
      if request.kind = actualKind then some request else none
  | _ => none

/-- Every selected root-collection declaration receives one source-derived
request, in plan order. -/
def requestsForSource (plan : Plan) (certificate : Certificate plan)
    (source : Pattern) : List (Nat × ScopedCollectionMachine.Request) :=
  (List.range plan.rules.length).filterMap fun ordinal =>
    (requestForSource? plan certificate ordinal source).map fun request => (ordinal, request)

theorem requestsForSource_selected {plan : Plan} {certificate : Certificate plan}
    {source : Pattern} {ordinal : Nat} {request : ScopedCollectionMachine.Request}
    (member : (ordinal, request) ∈ requestsForSource plan certificate source) :
    requestForSource? plan certificate ordinal source = some request := by
  simp only [requestsForSource, List.mem_filterMap] at member
  obtain ⟨candidate, _, produced⟩ := member
  cases made : requestForSource? plan certificate candidate source with
  | none => simp [made] at produced
  | some actual =>
      simp only [made, Option.map_some] at produced
      rcases produced with ⟨rfl, rfl⟩
      exact made

theorem requestForSource?_target {plan : Plan} {certificate : Certificate plan}
    {ordinal : Nat} {source : Pattern} {request : ScopedCollectionMachine.Request}
    (made : requestForSource? plan certificate ordinal source = some request) :
    ∃ targets, source = .collection request.kind targets none ∧
      request.targets = arrange request.kind targets := by
  cases source with
  | collection actualKind targets rest =>
      cases rest with
      | some => simp [requestForSource?] at made
      | none =>
          unfold requestForSource? at made
          cases generated : request? plan certificate ordinal targets with
          | none => simp [generated] at made
          | some actual =>
              by_cases same : actual.kind = actualKind
              · simp [generated, same] at made
                cases made
                obtain ⟨_, _, _, _, targetEq⟩ := request?_selected generated
                exact ⟨targets, by rw [same], targetEq⟩
              · simp [generated, same] at made
  | _ => simp [requestForSource?] at made

theorem requestForSource?_fixed {plan : Plan} {certificate : Certificate plan}
    {ordinal : Nat} {source : Pattern} {request : ScopedCollectionMachine.Request}
    (made : requestForSource? plan certificate ordinal source = some request) :
    arrange request.kind request.targets = request.targets := by
  obtain ⟨targets, _, targetEq⟩ := requestForSource?_target made
  rw [targetEq]
  exact arrange_fixed request.kind targets

theorem requestForSource?_requested {plan : Plan} {certificate : Certificate plan}
    {ordinal : Nat} {source : Pattern} {request : ScopedCollectionMachine.Request}
    (made : requestForSource? plan certificate ordinal source = some request) :
    ∃ targets, request? plan certificate ordinal targets = some request := by
  cases source with
  | collection actualKind targets rest =>
      cases rest with
      | some => simp [requestForSource?] at made
      | none =>
          unfold requestForSource? at made
          cases generated : request? plan certificate ordinal targets with
          | none => simp [generated] at made
          | some actual =>
              by_cases same : actual.kind = actualKind
              · simp [generated, same] at made
                cases made
                exact ⟨targets, generated⟩
              · simp [generated, same] at made
  | _ => simp [requestForSource?] at made

private def guardedSetRule : RewriteRule where
  name := "guarded-set-must-use-generic-premises"
  typeContext := [("X", .base "Item")]
  premises := [.relationQuery "allowed" [.fvar "X"]]
  left := .collection .hashSet [.fvar "X"] none
  right := .fvar "X"

private def unconditionalSetRule : RewriteRule :=
  { guardedSetRule with premises := [] }

example : ruleReady guardedSetRule = false := by decide
example : ruleReady unconditionalSetRule = true := by decide

end Mettapedia.OSLF.MeTTaIL.CollectionExecutionAdmission
