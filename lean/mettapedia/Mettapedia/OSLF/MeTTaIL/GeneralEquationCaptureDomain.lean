import Mettapedia.OSLF.MeTTaIL.GeneralEquationSupport

/-!
# Captured domains and balanced equation support

Every schema metavariable is actually captured by an independent scoped match.
A premise extension preserves those whole contextual values. For a balanced
equation the reduct refers only to those names, so new query outputs cannot
enlarge its term support or replace its original captures.
-/

set_option autoImplicit false
namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationCaptureDomain

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch
open GeneralEquationMeasures GeneralEquationAdmission GeneralEquationSupport
open Mettapedia.OSLF.Framework.GeneralFiniteTermUniverse

def Captures (assignment : ScopedRuleMatching.Assignment) (names : List String) : Prop :=
  ∀ name ∈ names, ∃ value, lookup assignment name = some value

theorem Captures.extend {initial final : ScopedRuleMatching.Assignment} {names : List String}
    (captured : Captures initial names) (extension : Extends initial final) : Captures final names := by
  intro name member
  obtain ⟨value, found⟩ := captured name member
  exact ⟨value, extension name value found⟩

theorem capture_captures {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : ScopedRuleMatching.Assignment}
    {name : String} {target : Pattern}
    (captured : capture? rule spec ambient depth site path initial name target = some final) :
    ∃ value, lookup final name = some value := by
  obtain ⟨_, _, value, _, _, _, found, _, _⟩ := capture_interpretation captured
  exact ⟨value, found⟩

mutual
  theorem matched_captures {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth : Nat}
      {initial final : ScopedRuleMatching.Assignment} {pattern target : Pattern}
      (matched : Matches rule spec ambient site path depth initial pattern target final) :
      Captures final pattern.freeFvarNames := by
    cases matched with
    | capture captured =>
        intro name member
        simp only [Pattern.freeFvarNames, List.mem_singleton] at member
        subst name
        exact capture_captures captured
    | bound => simp [Captures, Pattern.freeFvarNames]
    | constructor arguments => simpa only [Pattern.freeFvarNames] using matchedArguments_captures arguments
    | binder body => simpa only [Pattern.freeFvarNames] using matched_captures body
    | binders body => simpa only [Pattern.freeFvarNames] using matched_captures body
    | substitution body replacement =>
        have first := (matched_captures body).extend replacement.extends
        have second := matched_captures replacement
        intro name member
        simp only [Pattern.freeFvarNames, List.mem_append] at member
        exact member.elim (first name) (second name)
    | bag _ bag => simpa only [Pattern.freeFvarNames] using matchedBag_captures bag
    | vector arguments => simpa only [Pattern.freeFvarNames, Option.toList_none, List.append_nil] using matchedArguments_captures arguments
    | vectorRest arguments captured =>
        have first := (matchedArguments_captures arguments).extend (capture_extends captured)
        have second := capture_captures captured
        intro name member
        simp only [Pattern.freeFvarNames, Option.toList_some, List.mem_append, List.mem_singleton] at member
        rcases member with ordinary | rfl
        · exact first name ordinary
        · exact second
  termination_by sizeOf pattern

  theorem matchedArguments_captures {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth index : Nat}
      {initial final : ScopedRuleMatching.Assignment} {patterns targets : List Pattern}
      (matched : Arguments rule spec ambient site path depth initial index patterns targets final) :
      Captures final (patterns.flatMap Pattern.freeFvarNames) := by
    cases matched with
    | nil => simp [Captures]
    | cons head tail =>
        have first := (matched_captures head).extend tail.extends
        have second := matchedArguments_captures tail
        intro name member
        simp only [List.flatMap_cons, List.mem_append] at member
        exact member.elim (first name) (second name)
  termination_by sizeOf patterns

  theorem matchedBag_captures {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth index : Nat}
      {initial final : ScopedRuleMatching.Assignment} {patterns targets : List Pattern}
      {rest : Option String} {kind : CollType}
      (matched : Bag rule spec ambient site path depth initial index patterns rest kind targets final) :
      Captures final (patterns.flatMap Pattern.freeFvarNames ++ rest.toList) := by
    cases matched with
    | nil => simp [Captures]
    | rest captured =>
        intro name member
        simp only [List.flatMap_nil, Option.toList_some, List.nil_append, List.mem_singleton] at member
        subst name
        exact capture_captures captured
    | cons _ _ head tail =>
        have first := (matched_captures head).extend tail.extends
        have second := matchedBag_captures tail
        intro name member
        simp only [List.flatMap_cons, List.append_assoc, List.mem_append] at member
        exact member.elim (first name) (fun later => second name (List.mem_append.mpr later))
  termination_by sizeOf patterns
end

mutual
  theorem instantiate_lookup_congr (rule : RewriteRule) (spec : RuleBindingSpec)
      (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
      (initial final : ScopedRuleMatching.Assignment) (pattern : Pattern)
      (ready : checkSide rule spec site path depth pattern = true)
      (agree : ∀ name ∈ pattern.freeFvarNames, lookup initial name = lookup final name) :
      instantiateAt? rule spec ambient site path depth initial pattern =
        instantiateAt? rule spec ambient site path depth final pattern := by
    cases pattern with
    | fvar name =>
        simp only [instantiateAt?, instantiateWith?, agree name (by simp [Pattern.freeFvarNames])]
    | bvar index => simp only [instantiateAt?, instantiateWith?]
    | apply label arguments =>
        simp only [checkSide] at ready
        have same := instantiateArguments_lookup_congr rule spec ambient site path depth initial final
          0 arguments ready (by intro name member; exact agree name (by simpa only [Pattern.freeFvarNames] using member))
        simpa only [instantiateAt?, instantiateWith?, Option.bind_eq_bind] using congrArg
          (fun results => results.bind (fun values => some (Pattern.apply label values))) same
    | lambda display body =>
        simp only [checkSide] at ready
        have same := instantiate_lookup_congr rule spec ambient site (path ++ [0]) (depth + 1)
          initial final body ready (by simpa only [Pattern.freeFvarNames] using agree)
        simpa only [instantiateAt?, instantiateWith?, Option.bind_eq_bind] using congrArg
          (fun result => result.bind (fun value => some (Pattern.lambda display value))) same
    | multiLambda arity display body =>
        simp only [checkSide] at ready
        have same := instantiate_lookup_congr rule spec ambient site (path ++ [0]) (depth + arity)
          initial final body ready (by simpa only [Pattern.freeFvarNames] using agree)
        simpa only [instantiateAt?, instantiateWith?, Option.bind_eq_bind] using congrArg
          (fun result => result.bind (fun value => some (Pattern.multiLambda arity display value))) same
    | subst body replacement => simp only [checkSide, Bool.false_eq_true] at ready
    | collection kind elements rest =>
        cases rest with
        | some name => simp only [checkSide, Option.isNone_some, Bool.false_and, Bool.false_eq_true] at ready
        | none =>
            simp only [checkSide, Option.isNone_none, Bool.true_and] at ready
            have same := instantiateArguments_lookup_congr rule spec ambient site path depth initial final
              0 elements ready (by intro name member; exact agree name (by simpa only [Pattern.freeFvarNames, Option.toList_none, List.append_nil] using member))
            simpa only [instantiateAt?, instantiateWith?, Option.bind_eq_bind] using congrArg
              (fun result => result.bind (fun values => some (Pattern.collection kind values none))) same
  termination_by sizeOf pattern

  theorem instantiateArguments_lookup_congr (rule : RewriteRule) (spec : RuleBindingSpec)
      (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
      (initial final : ScopedRuleMatching.Assignment) (index : Nat) (patterns : List Pattern)
      (ready : checkArguments rule spec site path depth index patterns = true)
      (agree : ∀ name ∈ patterns.flatMap Pattern.freeFvarNames, lookup initial name = lookup final name) :
      instantiateArgsWith? Substitution.instantiateBVar rule spec ambient site path depth initial index patterns =
        instantiateArgsWith? Substitution.instantiateBVar rule spec ambient site path depth final index patterns := by
    cases patterns with
    | nil => simp only [instantiateArgsWith?]
    | cons first rest =>
        simp only [checkArguments, Bool.and_eq_true] at ready
        have firstSame := instantiate_lookup_congr rule spec ambient site (path ++ [index]) depth initial final first ready.1
          (by intro name member; exact agree name (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inl member))
        have restSame := instantiateArguments_lookup_congr rule spec ambient site path depth initial final (index + 1) rest ready.2
          (by intro name member; exact agree name (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inr member))
        unfold instantiateAt? at firstSame
        simp only [instantiateArgsWith?, firstSame, restSame]
  termination_by sizeOf patterns
end

/-- Balance makes premise-only bindings irrelevant to the equation target. -/
theorem balanced_reduct_supported {alphabet : Alphabet} {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient : Nat} {source target : Pattern} {captured completed : ScopedRuleMatching.Assignment}
    (accepted : checkRule rule spec = true) (support : Supported alphabet source)
    (template : Supported alphabet rule.right) (matched : captured ∈ matchRuleAt rule spec ambient source)
    (extension : Extends captured completed) (reduct : reduct? rule spec ambient completed = some target) :
    Supported alphabet target := by
  have ready := checkRule_sides rule spec accepted
  have captures := matched_captures (matchRuleAt_iff.mp matched)
  have balance : constantContribution rule.left = constantContribution rule.right ∧
      rule.left.freeFvarNames.Perm rule.right.freeFvarNames := by
    simpa only [balanced, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using ready.2.2.2
  have permutation := balance.2
  have agree : ∀ name ∈ rule.right.freeFvarNames, lookup captured name = lookup completed name := by
    intro name member
    obtain ⟨value, found⟩ := captures name (permutation.mem_iff.mpr member)
    rw [found, extension name value found]
  have same := instantiate_lookup_congr rule spec ambient .right [] 0 captured completed rule.right ready.2.2.1 agree
  have original : reduct? rule spec ambient captured = some target := same.trans reduct
  exact instantiate_supported alphabet rule spec ambient .right [] 0 captured rule.right target
    ready.2.2.1 template (matchRule_supported support matched) original

end Mettapedia.OSLF.MeTTaIL.GeneralEquationCaptureDomain
