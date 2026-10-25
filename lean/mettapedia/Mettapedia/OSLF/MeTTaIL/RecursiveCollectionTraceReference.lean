import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine

/-!
# A trace reference for recursive collection matching

This structural enumeration is a proof-side reference for the retained task
machine, not a second runner. Each unordered node records the exact existing
allocator decisions, and sequential children concatenate their histories.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine

open Syntax RuleBinding ScopedRuleMatching CanonicalBags CollectionSelection
open EquationalScopedMatching

/-- Deterministic operations add no allocation event. -/
def bareAnswers (assignments : List Assignment) : List Answer :=
  assignments.map fun assignment => ⟨assignment, []⟩

/-- Sequential matching retains the first computation's events before the
second computation's events. Both receive their actual captured assignment. -/
def bindAnswers (first : List Answer) (next : Assignment → List Answer) : List Answer :=
  first.flatMap fun head => (next head.assignment).map fun tail =>
    ⟨tail.assignment, head.trace ++ tail.trace⟩

mutual
def referenceAt (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat) (initial : Assignment) :
    Pattern → Pattern → List Answer
  | .fvar name, target => bareAnswers (capture? rule spec ambient depth site path initial name target).toList
  | .bvar expected, .bvar actual => if expected = actual then [⟨initial, []⟩] else []
  | .apply label schemas, .apply actual targets =>
      if label = actual then referenceArguments rule spec ambient site path depth initial 0 schemas targets else []
  | .lambda _ body, .lambda _ target =>
      referenceAt rule spec ambient site (path ++ [0]) (depth + 1) initial body target
  | .multiLambda arity _ body, .multiLambda actual _ target =>
      if arity = actual then referenceAt rule spec ambient site (path ++ [0]) (depth + arity) initial body target
      else []
  | .subst body replacement, .subst targetBody targetReplacement =>
      bindAnswers (referenceAt rule spec ambient site (path ++ [0]) (depth + 1) initial body targetBody)
        (fun middle => referenceAt rule spec ambient site (path ++ [1]) depth middle replacement targetReplacement)
  | .collection kind schemas rest, .collection actual targets actualRest =>
      if kind = actual ∧ actualRest = none then
        if kind = .vec then
          match rest with
          | none => referenceArguments rule spec ambient site path depth initial 0 schemas targets
          | some name =>
              bindAnswers (referenceArguments rule spec ambient site path depth initial 0 schemas
                (targets.take schemas.length)) (fun middle =>
                  bareAnswers (captureRest? rule spec ambient depth site (path ++ [schemas.length])
                    middle name kind (targets.drop schemas.length)).toList)
        else
          (tracedAllocations (kind == .hashSet) schemas.length (arrange kind targets)).flatMap fun allocation =>
            (bindAnswers (referenceArguments rule spec ambient site path depth initial 0 schemas allocation.values)
              (fun middle => bareAnswers (finish literalBodyComparison rule spec ambient site path depth
                schemas.length rest kind middle (arrange kind allocation.residual)))).map fun answer =>
                  ⟨answer.assignment, ⟨path, kind, allocation.decisions⟩ :: answer.trace⟩
      else []
  | _, _ => []
termination_by schema _ => sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

def referenceArguments (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat) (initial : Assignment) (index : Nat) :
    List Pattern → List Pattern → List Answer
  | [], [] => [⟨initial, []⟩]
  | schema :: schemas, target :: targets =>
      bindAnswers (referenceAt rule spec ambient site (path ++ [index]) depth initial schema target)
        (fun middle => referenceArguments rule spec ambient site path depth middle (index + 1) schemas targets)
  | _, _ => []
termination_by schemas _ => sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec
end

theorem bareAnswers_projection (assignments : List Assignment) :
    (bareAnswers assignments).map Answer.assignment = assignments := by simp [bareAnswers, Function.comp_def]

theorem bindAnswers_projection (first : List Answer) (next : Assignment → List Answer) :
    (bindAnswers first next).map Answer.assignment =
      (first.map Answer.assignment).flatMap (fun middle => (next middle).map Answer.assignment) := by
  simp only [bindAnswers, List.map_flatMap, List.map_map, List.flatMap_map, Function.comp_def]

theorem bindAnswers_assoc (first : List Answer) (second third : Assignment → List Answer) :
    bindAnswers (bindAnswers first second) third =
      bindAnswers first (fun middle => bindAnswers (second middle) third) := by
  simp only [bindAnswers, List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def, List.append_assoc]

theorem mem_bareAnswers {answer : Answer} {assignments : List Assignment} :
    answer ∈ bareAnswers assignments ↔ answer.assignment ∈ assignments ∧ answer.trace = [] := by
  cases answer
  simp [bareAnswers]

theorem mem_bindAnswers {answer : Answer} {first : List Answer} {next : Assignment → List Answer} :
    answer ∈ bindAnswers first next ↔
      ∃ head ∈ first, ∃ tail ∈ next head.assignment,
        answer = ⟨tail.assignment, head.trace ++ tail.trace⟩ := by
  simp [bindAnswers, eq_comm]

mutual
/-- Reference receipts satisfy the existing independent allocation-history
judgment, including every nested node and binder path. -/
theorem referenceAt_sound {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial : Assignment}
    {schema target : Pattern} {answer : Answer}
    (member : answer ∈ referenceAt rule spec ambient site path depth initial schema target) :
    EquationalScopedReceipts.Matches literalBodyComparison rule spec ambient site path depth
      initial schema target answer.trace answer.assignment := by
  cases schema with
  | fvar name =>
    rw [referenceAt.eq_def] at member
    have found := mem_bareAnswers.mp member
    rw [found.2]
    exact .capture (by simpa only [captureWith?_literal] using Option.mem_toList.mp found.1)
  | bvar index =>
    cases target <;> simp only [referenceAt, List.not_mem_nil] at member
    split at member
    · rename_i same
      subst same
      have same := List.mem_singleton.mp member
      subst answer
      exact .bound
    · cases member
  | apply label schemas =>
    cases target <;> simp only [referenceAt, List.not_mem_nil] at member
    split at member
    · rename_i same
      subst same
      exact .constructor (referenceArguments_sound member)
    · cases member
  | lambda display body =>
    cases target <;> simp only [referenceAt, List.not_mem_nil] at member
    exact .lambda (referenceAt_sound member)
  | multiLambda arity displays body =>
    cases target <;> simp only [referenceAt, List.not_mem_nil] at member
    split at member
    · rename_i same
      subst same
      exact .multiLambda (referenceAt_sound member)
    · cases member
  | subst body replacement =>
    cases target <;> simp only [referenceAt, List.not_mem_nil] at member
    obtain ⟨head, first, tail, second, rfl⟩ := mem_bindAnswers.mp member
    exact .substitution (referenceAt_sound first) (referenceAt_sound second)
  | collection kind schemas rest =>
    cases target <;> simp only [referenceAt.eq_def, List.not_mem_nil] at member
    rename_i actual targets actualRest
    split at member
    · rename_i shape
      obtain ⟨rfl, rfl⟩ := shape
      by_cases vector : kind = .vec
      · subst kind
        simp only [↓reduceIte] at member
        cases rest with
        | none => exact .vector (referenceArguments_sound member)
        | some name =>
          obtain ⟨head, first, tail, second, rfl⟩ := mem_bindAnswers.mp member
          obtain ⟨captured, empty⟩ := mem_bareAnswers.mp second
          rw [empty, List.append_nil]
          exact .vectorRest (middle := head.assignment) (referenceArguments_sound first)
            (by simpa only [captureRestWith?_literal] using Option.mem_toList.mp captured)
      · simp only [vector, ↓reduceIte] at member
        obtain ⟨allocation, allocated, member⟩ := List.mem_flatMap.mp member
        obtain ⟨result, combined, rfl⟩ := List.mem_map.mp member
        obtain ⟨head, first, tail, second, rfl⟩ := mem_bindAnswers.mp combined
        obtain ⟨finished, empty⟩ := mem_bareAnswers.mp second
        simp only [empty, List.append_nil]
        exact .unordered vector allocated (referenceArguments_sound first)
          ((finish_exact ..).mp finished)
    · cases member
termination_by sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

theorem referenceArguments_sound {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial : Assignment}
    {schemas targets : List Pattern} {answer : Answer}
    (member : answer ∈ referenceArguments rule spec ambient site path depth initial index schemas targets) :
    EquationalScopedReceipts.Arguments literalBodyComparison rule spec ambient site path depth
      initial index schemas targets answer.trace answer.assignment := by
  cases schemas with
  | nil =>
    cases targets <;> simp only [referenceArguments, List.not_mem_nil] at member
    have same := List.mem_singleton.mp member
    subst answer
    exact .nil
  | cons schema schemas =>
    cases targets <;> simp only [referenceArguments, List.not_mem_nil] at member
    obtain ⟨head, first, tail, second, rfl⟩ := mem_bindAnswers.mp member
    exact .cons (referenceAt_sound first) (referenceArguments_sound second)
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec
end

mutual
/-- Every independently valid allocation history occurs in the reference. -/
theorem referenceAt_complete {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
    {schema target : Pattern} {trace : List EquationalScopedReceipts.Event}
    (matched : EquationalScopedReceipts.Matches literalBodyComparison rule spec ambient site path depth
      initial schema target trace final) :
    (⟨final, trace⟩ : Answer) ∈ referenceAt rule spec ambient site path depth initial schema target := by
  cases matched with
  | capture captured =>
    rw [referenceAt.eq_def]
    exact mem_bareAnswers.mpr ⟨Option.mem_toList.mpr (by
      simpa only [captureWith?_literal] using captured), rfl⟩
  | bound => simp [referenceAt]
  | constructor rows => simpa only [referenceAt, ↓reduceIte] using referenceArguments_complete rows
  | lambda body => simpa only [referenceAt] using referenceAt_complete body
  | multiLambda body => simpa only [referenceAt, ↓reduceIte] using referenceAt_complete body
  | substitution first second =>
    rw [referenceAt.eq_def]
    exact mem_bindAnswers.mpr ⟨_, referenceAt_complete first, _, referenceAt_complete second, rfl⟩
  | vector rows => simpa only [referenceAt.eq_def, true_and, ↓reduceIte] using referenceArguments_complete rows
  | vectorRest rows captured =>
    rw [referenceAt.eq_def]
    simp only [true_and, ↓reduceIte]
    apply mem_bindAnswers.mpr
    exact ⟨_, referenceArguments_complete rows, ⟨_, []⟩,
      mem_bareAnswers.mpr ⟨Option.mem_toList.mpr (by
        simpa only [captureRestWith?_literal] using captured), rfl⟩,
      by simp only [List.append_nil]⟩
  | unordered notVector allocated rows finished =>
    rw [referenceAt.eq_def]
    simp only [true_and, notVector, ↓reduceIte]
    apply List.mem_flatMap.mpr
    refine ⟨_, allocated, List.mem_map.mpr ⟨⟨_, _⟩, ?_, rfl⟩⟩
    exact mem_bindAnswers.mpr ⟨_, referenceArguments_complete rows, ⟨_, []⟩,
      mem_bareAnswers.mpr ⟨(finish_exact ..).mpr finished, rfl⟩,
      by simp only [List.append_nil]⟩
termination_by sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

theorem referenceArguments_complete {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
    {schemas targets : List Pattern} {trace : List EquationalScopedReceipts.Event}
    (matched : EquationalScopedReceipts.Arguments literalBodyComparison rule spec ambient site path depth
      initial index schemas targets trace final) :
    (⟨final, trace⟩ : Answer) ∈ referenceArguments rule spec ambient site path depth initial index schemas targets := by
  cases matched with
  | nil => simp [referenceArguments]
  | cons first rest =>
    rw [referenceArguments]
    exact mem_bindAnswers.mpr ⟨_, referenceAt_complete first, _, referenceArguments_complete rest, rfl⟩
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec
end

theorem referenceAt_exact {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial : Assignment}
    {schema target : Pattern} {answer : Answer} :
    answer ∈ referenceAt rule spec ambient site path depth initial schema target ↔
      EquationalScopedReceipts.Matches literalBodyComparison rule spec ambient site path depth
        initial schema target answer.trace answer.assignment :=
  ⟨referenceAt_sound, referenceAt_complete⟩

end Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine
