import Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
import Mathlib.Data.List.Enum

/-!
# Independent scoped matching judgments

The judgments describe a tree match and its ordered assignment flow. They
retain each contextual input occurrence and every multiset selection. Their
definition does not enumerate executable matcher results. Capture constraints
use the binding specification's checked local spine interpretation.
-/

namespace Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

mutual
inductive Matches (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) :
    RulePatternSite → List Nat → Nat → Assignment → Pattern → Pattern →
      Assignment → Prop where
  | capture {site path depth initial name target final} :
      capture? rule spec ambient depth site path initial name target = some final →
      Matches rule spec ambient site path depth initial (.fvar name) target final
  | bound {site path depth initial index} :
      Matches rule spec ambient site path depth initial (.bvar index) (.bvar index) initial
  | constructor {site path depth initial label patterns targets final} :
      Arguments rule spec ambient site path depth initial 0 patterns targets final →
      Matches rule spec ambient site path depth initial
        (.apply label patterns) (.apply label targets) final
  | binder {site path depth initial display actualDisplay pattern target final} :
      Matches rule spec ambient site (path ++ [0]) (depth + 1) initial pattern target final →
      Matches rule spec ambient site path depth initial
        (.lambda display pattern) (.lambda actualDisplay target) final
  | binders {site path depth initial arity display actualDisplay pattern target final} :
      Matches rule spec ambient site (path ++ [0]) (depth + arity) initial pattern target final →
      Matches rule spec ambient site path depth initial
        (.multiLambda arity display pattern) (.multiLambda arity actualDisplay target) final
  | substitution {site path depth initial body targetBody replacement targetReplacement middle final} :
      Matches rule spec ambient site (path ++ [0]) (depth + 1) initial body targetBody middle →
      Matches rule spec ambient site (path ++ [1]) depth middle replacement targetReplacement final →
      Matches rule spec ambient site path depth initial
        (.subst body replacement) (.subst targetBody targetReplacement) final
  | bag {site path depth initial kind patterns rest targets final} :
      kind ≠ .vec →
      Bag rule spec ambient site path depth initial 0 patterns rest kind targets final →
      Matches rule spec ambient site path depth initial
        (.collection kind patterns rest) (.collection kind targets none) final
  | vector {site path depth initial patterns targets final} :
      Arguments rule spec ambient site path depth initial 0 patterns targets final →
      Matches rule spec ambient site path depth initial
        (.collection .vec patterns none) (.collection .vec targets none) final
  | vectorRest {site path depth initial patterns name targets middle final} :
      Arguments rule spec ambient site path depth initial 0 patterns
        (targets.take patterns.length) middle →
      captureRest? rule spec ambient depth site (path ++ [patterns.length])
        middle name .vec (targets.drop patterns.length) = some final →
      Matches rule spec ambient site path depth initial
        (.collection .vec patterns (some name)) (.collection .vec targets none) final

inductive Arguments (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) :
    RulePatternSite → List Nat → Nat → Assignment → Nat → List Pattern →
      List Pattern → Assignment → Prop where
  | nil {site path depth initial index} :
      Arguments rule spec ambient site path depth initial index [] [] initial
  | cons {site path depth initial index pattern patterns target targets middle final} :
      Matches rule spec ambient site (path ++ [index]) depth initial pattern target middle →
      Arguments rule spec ambient site path depth middle (index + 1) patterns targets final →
      Arguments rule spec ambient site path depth initial index
        (pattern :: patterns) (target :: targets) final

inductive Bag (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) :
    RulePatternSite → List Nat → Nat → Assignment → Nat → List Pattern →
      Option String → CollType → List Pattern → Assignment → Prop where
  | nil {site path depth initial index kind} :
      Bag rule spec ambient site path depth initial index [] none kind [] initial
  | rest {site path depth initial index name kind targets final} :
      captureRest? rule spec ambient depth site (path ++ [index]) initial name kind targets =
        some final →
      Bag rule spec ambient site path depth initial index [] (some name) kind targets final
  | cons {site path depth initial index pattern patterns rest kind targets middle final}
      (selected : Nat) (within : selected < targets.length) :
      Matches rule spec ambient site (path ++ [index]) depth initial pattern targets[selected] middle →
      Bag rule spec ambient site path depth middle (index + 1) patterns rest kind
        (targets.eraseIdx selected) final →
      Bag rule spec ambient site path depth initial index (pattern :: patterns) rest kind targets final
end

private theorem mem_zipIdx {α : Type*} {items : List α} {item : α} {index : Nat}
    (member : (item, index) ∈ items.zipIdx) :
    ∃ within : index < items.length, items[index] = item := by
  obtain ⟨selected, within, same⟩ := List.exists_mem_zipIdx'.mp
    ⟨_, member, rfl⟩
  have equality : selected = index := (Prod.ext_iff.mp same).2.symm
  subst selected
  exact ⟨within, (Prod.ext_iff.mp same).1.symm⟩

private theorem selected_mem {α : Type*} (items : List α) (index : Nat)
    (within : index < items.length) : (items[index], index) ∈ items.zipIdx := by
  have zipWithin : index < items.zipIdx.length := by simpa using within
  simpa using List.getElem_mem zipWithin

private theorem pattern_positive (pattern : Pattern) : 0 < sizeOf pattern := by
  cases pattern <;> simp_wf

private theorem list_cons_positive (pattern : Pattern) (patterns : List Pattern) :
    0 < sizeOf (pattern :: patterns) := by simp_wf

private theorem head_smaller (pattern : Pattern) (patterns : List Pattern) :
    sizeOf pattern < sizeOf (pattern :: patterns) := by simp_wf; omega

private theorem tail_smaller (pattern : Pattern) (patterns : List Pattern) :
    sizeOf patterns < sizeOf (pattern :: patterns) := by simp_wf

private theorem args_smaller (label : String) (patterns : List Pattern) :
    sizeOf patterns < sizeOf (Pattern.apply label patterns) := by simp_wf

private theorem body_smaller (display : Option String) (pattern : Pattern) :
    sizeOf pattern < sizeOf (Pattern.lambda display pattern) := by simp_wf

private theorem multiBody_smaller (arity : Nat) (display : List String) (pattern : Pattern) :
    sizeOf pattern < sizeOf (Pattern.multiLambda arity display pattern) := by simp_wf

private theorem elements_smaller (kind : CollType) (patterns : List Pattern) (rest : Option String) :
    sizeOf patterns < sizeOf (Pattern.collection kind patterns rest) := by simp_wf; omega

private theorem substitutionBody_smaller (body replacement : Pattern) :
    sizeOf body < sizeOf (Pattern.subst body replacement) := by simp_wf; omega

private theorem substitutionReplacement_smaller (body replacement : Pattern) :
    sizeOf replacement < sizeOf (Pattern.subst body replacement) := by simp_wf

private theorem sound_all (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (bound : Nat) :
    (∀ site path depth initial pattern target final, sizeOf pattern ≤ bound →
      final ∈ matchAt rule spec ambient site path depth initial pattern target →
      Matches rule spec ambient site path depth initial pattern target final) ∧
    (∀ site path depth initial index patterns targets final, sizeOf patterns ≤ bound →
      final ∈ matchArgsAt rule spec ambient site path depth initial index patterns targets →
      Arguments rule spec ambient site path depth initial index patterns targets final) ∧
    (∀ site path depth initial index patterns rest kind targets final, sizeOf patterns ≤ bound →
      final ∈ matchBagAt rule spec ambient site path depth initial index patterns rest kind targets →
      Bag rule spec ambient site path depth initial index patterns rest kind targets final) := by
  induction bound with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro site path depth initial pattern target final small member
        have positive := pattern_positive pattern
        omega
      · intro site path depth initial index patterns targets final small member
        cases patterns with
        | nil =>
            cases targets with
            | nil =>
                simp only [matchArgsAt, matchArgsAtWith, List.mem_singleton] at member
                subst final
                exact .nil
            | cons target targets => simp [matchArgsAt, matchArgsAtWith] at member
        | cons pattern patterns =>
            have positive := list_cons_positive pattern patterns
            omega
      · intro site path depth initial index patterns rest kind targets final small member
        cases patterns with
        | nil =>
            cases rest with
            | none =>
                simp only [matchBagAt, matchBagAtWith] at member
                split at member
                next empty =>
                  have emptyTargets : targets = [] := List.isEmpty_iff.mp empty
                  subst targets
                  simp only [List.mem_singleton] at member
                  subst final
                  exact .nil
                next => simp at member
            | some name =>
                exact .rest (by simpa [matchBagAt, matchBagAtWith] using member)
        | cons pattern patterns =>
            have positive := list_cons_positive pattern patterns
            omega
  | succ bound inductionHypothesis =>
      obtain ⟨ihMatch, ihArgs, ihBag⟩ := inductionHypothesis
      refine ⟨?_, ?_, ?_⟩
      · intro site path depth initial pattern target final small member
        match pattern, target with
        | .fvar name, target =>
            exact .capture (by simpa [matchAt_fvar] using member)
        | .bvar expected, .bvar actual =>
            simp only [matchAt, matchAtWith] at member
            split at member
            next equal =>
              have same : expected = actual := beq_iff_eq.mp equal
              subst actual
              simp only [List.mem_singleton] at member
              subst final
              exact .bound
            next => simp at member
        | .apply label patterns, .apply actualLabel targets =>
            simp only [matchAt, matchAtWith] at member
            split at member
            next equal =>
              have same : label = actualLabel := beq_iff_eq.mp equal
              subst actualLabel
              exact .constructor (ihArgs site path depth initial 0 patterns targets final
                (by have := args_smaller label patterns; omega) member)
            next => simp at member
        | .lambda display body, .lambda actualDisplay target =>
            unfold matchAt matchAtWith at member
            exact .binder (ihMatch site (path ++ [0]) (depth + 1) initial body target final
              (by have := body_smaller display body; omega) member)
        | .multiLambda arity display body, .multiLambda actualArity actualDisplay target =>
            simp only [matchAt, matchAtWith] at member
            split at member
            next equal =>
              have same : arity = actualArity := beq_iff_eq.mp equal
              subst actualArity
              exact .binders (ihMatch site (path ++ [0]) (depth + arity) initial body target final
                (by have := multiBody_smaller arity display body; omega) member)
            next => simp at member
        | .subst body replacement, .subst targetBody targetReplacement =>
            simp only [matchAt, matchAtWith, List.mem_flatMap] at member
            obtain ⟨middle, first, second⟩ := member
            exact .substitution
              (ihMatch site (path ++ [0]) (depth + 1) initial body targetBody middle
                (by have := substitutionBody_smaller body replacement; omega) first)
              (ihMatch site (path ++ [1]) depth middle replacement targetReplacement final
                (by have := substitutionReplacement_smaller body replacement; omega) second)
        | .collection kind patterns rest, .collection actualKind targets actualRest =>
            unfold matchAt matchAtWith at member
            split at member
            next accepted =>
              have conditions := Bool.and_eq_true_iff.mp accepted
              have same : kind = actualKind := beq_iff_eq.mp conditions.1
              have noRest : actualRest = none := Option.isNone_iff_eq_none.mp conditions.2
              subst actualKind actualRest
              cases kind with
              | vec =>
                  simp only [beq_self_eq_true, ↓reduceIte] at member
                  cases rest with
                  | none =>
                      exact .vector (ihArgs site path depth initial 0 patterns targets final
                        (by have := elements_smaller .vec patterns none; omega) member)
                  | some name =>
                      obtain ⟨middle, matched, captured⟩ := List.mem_filterMap.mp member
                      exact .vectorRest
                        (ihArgs site path depth initial 0 patterns (targets.take patterns.length) middle
                          (by have := elements_smaller .vec patterns (some name); omega) matched)
                        (by simpa only [captureRestWith?_literal] using captured)
              | hashBag =>
                  exact .bag (by decide) (ihBag site path depth initial 0 patterns rest .hashBag
                    targets final (by have := elements_smaller .hashBag patterns rest; omega) member)
              | hashSet =>
                  exact .bag (by decide) (ihBag site path depth initial 0 patterns rest .hashSet
                    targets final (by have := elements_smaller .hashSet patterns rest; omega) member)
            next => simp at member
        | .bvar _, .fvar _ | .bvar _, .apply _ _ | .bvar _, .lambda _ _
        | .bvar _, .multiLambda _ _ _ | .bvar _, .subst _ _ | .bvar _, .collection _ _ _
        | .apply _ _, .bvar _ | .apply _ _, .fvar _ | .apply _ _, .lambda _ _
        | .apply _ _, .multiLambda _ _ _ | .apply _ _, .subst _ _ | .apply _ _, .collection _ _ _
        | .lambda _ _, .bvar _ | .lambda _ _, .fvar _ | .lambda _ _, .apply _ _
        | .lambda _ _, .multiLambda _ _ _ | .lambda _ _, .subst _ _ | .lambda _ _, .collection _ _ _
        | .multiLambda _ _ _, .bvar _ | .multiLambda _ _ _, .fvar _
        | .multiLambda _ _ _, .apply _ _ | .multiLambda _ _ _, .lambda _ _
        | .multiLambda _ _ _, .subst _ _ | .multiLambda _ _ _, .collection _ _ _
        | .subst _ _, .bvar _ | .subst _ _, .fvar _ | .subst _ _, .apply _ _
        | .subst _ _, .lambda _ _ | .subst _ _, .multiLambda _ _ _ | .subst _ _, .collection _ _ _
        | .collection _ _ _, .bvar _ | .collection _ _ _, .fvar _ | .collection _ _ _, .apply _ _
        | .collection _ _ _, .lambda _ _ | .collection _ _ _, .multiLambda _ _ _
        | .collection _ _ _, .subst _ _ =>
            simp [matchAt, matchAtWith] at member
      · intro site path depth initial index patterns targets final small member
        match patterns, targets with
        | [], [] =>
            simp only [matchArgsAt, matchArgsAtWith, List.mem_singleton] at member
            subst final
            exact .nil
        | [], _ :: _ | _ :: _, [] => simp [matchArgsAt, matchArgsAtWith] at member
        | pattern :: patterns, target :: targets =>
            simp only [matchArgsAt, matchArgsAtWith, List.mem_flatMap] at member
            obtain ⟨middle, matched, continued⟩ := member
            exact .cons
              (ihMatch site (path ++ [index]) depth initial pattern target middle
                (by have := head_smaller pattern patterns; omega) matched)
              (ihArgs site path depth middle (index + 1) patterns targets final
                (by have := tail_smaller pattern patterns; omega) continued)
      · intro site path depth initial index patterns rest kind targets final small member
        cases patterns with
        | nil =>
            cases rest with
            | none =>
                simp only [matchBagAt, matchBagAtWith] at member
                split at member
                next empty =>
                  have emptyTargets : targets = [] := List.isEmpty_iff.mp empty
                  subst targets
                  simp only [List.mem_singleton] at member
                  subst final
                  exact .nil
                next => simp at member
            | some name =>
                exact .rest (by simpa [matchBagAt, matchBagAtWith] using member)
        | cons pattern patterns =>
            simp only [matchBagAt, matchBagAtWith, List.mem_flatMap] at member
            obtain ⟨⟨target, selected⟩, selectedMember, middle, matched, continued⟩ := member
            obtain ⟨within, same⟩ := mem_zipIdx selectedMember
            subst target
            exact .cons selected within
              (ihMatch site (path ++ [index]) depth initial pattern targets[selected] middle
                (by have := head_smaller pattern patterns; omega) matched)
              (ihBag site path depth middle (index + 1) patterns rest kind
                (targets.eraseIdx selected) final
                (by have := tail_smaller pattern patterns; omega) continued)

theorem matchAt_sound {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
    {pattern target : Pattern}
    (member : final ∈ matchAt rule spec ambient site path depth initial pattern target) :
    Matches rule spec ambient site path depth initial pattern target final :=
  (sound_all rule spec ambient (sizeOf pattern)).1 _ _ _ _ _ _ _ (Nat.le_refl _) member

theorem matchArgsAt_sound {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
    {patterns targets : List Pattern}
    (member : final ∈ matchArgsAt rule spec ambient site path depth initial index patterns targets) :
    Arguments rule spec ambient site path depth initial index patterns targets final :=
  (sound_all rule spec ambient (sizeOf patterns)).2.1 _ _ _ _ _ _ _ _ (Nat.le_refl _) member

theorem matchBagAt_sound {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
    {patterns targets : List Pattern} {rest : Option String} {kind : CollType}
    (member : final ∈ matchBagAt rule spec ambient site path depth initial index patterns rest kind targets) :
    Bag rule spec ambient site path depth initial index patterns rest kind targets final :=
  (sound_all rule spec ambient (sizeOf patterns)).2.2 _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _) member

mutual
  theorem Matches.complete {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
      {pattern target : Pattern}
      (matched : Matches rule spec ambient site path depth initial pattern target final) :
      final ∈ matchAt rule spec ambient site path depth initial pattern target := by
    cases matched with
    | capture captured => simpa only [matchAt_fvar, Option.mem_toList] using captured
    | bound => simp only [matchAt, matchAtWith, beq_self_eq_true, ↓reduceIte, List.mem_singleton]
    | constructor arguments =>
        simpa only [matchAt, matchAtWith, matchArgsAt, beq_self_eq_true, ↓reduceIte]
          using arguments.complete
    | binder body =>
        unfold matchAt matchAtWith
        simpa only [matchAt] using body.complete
    | binders body =>
        simpa only [matchAt, matchAtWith, beq_self_eq_true, ↓reduceIte] using body.complete
    | substitution body replacement =>
        simp only [matchAt, matchAtWith, List.mem_flatMap]
        exact ⟨_, body.complete, replacement.complete⟩
    | bag notVector bag =>
        unfold matchAt matchAtWith
        simp only [beq_self_eq_true, Option.isNone_none, Bool.and_self, beq_iff_eq,
          notVector, ↓reduceIte]
        exact bag.complete
    | vector arguments =>
        unfold matchAt matchAtWith
        simpa only [beq_self_eq_true, Option.isNone_none, Bool.and_self, ↓reduceIte, matchArgsAt]
          using arguments.complete
    | vectorRest arguments captured =>
        unfold matchAt matchAtWith
        simp only [beq_self_eq_true, Option.isNone_none, Bool.and_self, ↓reduceIte,
          List.mem_filterMap, captureRestWith?_literal]
        exact ⟨_, arguments.complete, captured⟩
  termination_by sizeOf pattern

  theorem Arguments.complete {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
      {patterns targets : List Pattern}
      (matched : Arguments rule spec ambient site path depth initial index patterns targets final) :
      final ∈ matchArgsAt rule spec ambient site path depth initial index patterns targets := by
    cases matched with
    | nil => simp only [matchArgsAt, matchArgsAtWith, List.mem_singleton]
    | cons head tail =>
        simp only [matchArgsAt, matchArgsAtWith, List.mem_flatMap]
        exact ⟨_, head.complete, tail.complete⟩
  termination_by sizeOf patterns

  theorem Bag.complete {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
      {patterns targets : List Pattern} {rest : Option String} {kind : CollType}
      (matched : Bag rule spec ambient site path depth initial index patterns rest kind targets final) :
      final ∈ matchBagAt rule spec ambient site path depth initial index patterns rest kind targets := by
    cases matched with
    | nil => simp only [matchBagAt, matchBagAtWith, List.isEmpty_nil, ↓reduceIte, List.mem_singleton]
    | rest captured =>
        simpa only [matchBagAt, matchBagAtWith, captureRestWith?_literal, Option.mem_toList] using captured
    | cons selected within head tail =>
        simp only [matchBagAt, matchBagAtWith, List.mem_flatMap]
        exact ⟨(_, selected), selected_mem targets selected within, _, head.complete, tail.complete⟩
  termination_by sizeOf patterns
end

theorem matchAt_iff {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
    {pattern target : Pattern} :
    final ∈ matchAt rule spec ambient site path depth initial pattern target ↔
      Matches rule spec ambient site path depth initial pattern target final :=
  ⟨matchAt_sound, Matches.complete⟩

theorem matchRuleAt_iff {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {final : Assignment} {target : Pattern} :
    final ∈ matchRuleAt rule spec ambient target ↔
      Matches rule spec ambient .left [] 0 [] rule.left target final :=
  matchAt_iff

/-- Matching may add values; it never changes a value already captured. -/
def Extends (initial final : Assignment) : Prop :=
  ∀ name value, lookup initial name = some value → lookup final name = some value

theorem Extends.refl (assignment : Assignment) : Extends assignment assignment := by
  intro name value found
  exact found

theorem Extends.trans {first second third : Assignment}
    (left : Extends first second) (right : Extends second third) : Extends first third := by
  intro name value found
  exact right name value (left name value found)

theorem assign_extends {initial final : Assignment} {name : String} {value : ContextualValue}
    (assigned : assign initial name value = some final) : Extends initial final := by
  unfold assign at assigned
  cases stored : lookup initial name with
  | none =>
      simp only [stored, Option.some.injEq] at assigned
      subst final
      intro previous previousValue found
      have different : name ≠ previous := by
        intro same
        subst previous
        rw [stored] at found
        contradiction
      have notEqual : (name == previous) = false := by simp [different]
      simpa only [lookup, List.find?_cons, notEqual] using found
  | some prior =>
      simp only [stored] at assigned
      split at assigned
      next =>
        cases Option.some.inj assigned
        exact Extends.refl initial
      next => contradiction

/-- Reconciliation of a repeated body keeps the first captured contextual
value for every declared comparison policy. -/
theorem assignWith_extends {compare : String → Pattern → Pattern → Bool}
    {initial final : Assignment} {name : String} {value : ContextualValue}
    (assigned : assignWith compare initial name value = some final) : Extends initial final := by
  unfold assignWith at assigned
  cases stored : lookup initial name with
  | none =>
      simp only [stored, Option.some.injEq] at assigned
      subst final
      intro previous previousValue found
      have different : name ≠ previous := by
        intro same
        subst previous
        rw [stored] at found
        contradiction
      have notEqual : (name == previous) = false := by simp [different]
      simpa only [lookup, List.find?_cons, notEqual] using found
  | some prior =>
      simp only [stored] at assigned
      split at assigned
      · cases Option.some.inj assigned
        exact Extends.refl initial
      · contradiction

theorem captureWith_extends {compare : String → Pattern → Pattern → Bool}
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : Assignment}
    {name : String} {target : Pattern}
    (captured : captureWith? compare rule spec ambient depth site path initial name target = some final) :
    Extends initial final := by
  simp only [captureWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at captured
  obtain ⟨dependencies, _, arguments, _, value, _, assigned⟩ := captured
  exact assignWith_extends assigned

theorem assign_lookup {initial final : Assignment} {name : String} {value : ContextualValue}
    (assigned : assign initial name value = some final) : lookup final name = some value := by
  unfold assign at assigned
  cases stored : lookup initial name with
  | none =>
      simp only [stored, Option.some.injEq] at assigned
      subst final
      simp only [lookup, List.find?_cons, beq_self_eq_true, Option.map_some]
  | some prior =>
      simp only [stored] at assigned
      split at assigned
      next same =>
        have equality : prior = value := beq_iff_eq.mp same
        subst prior
        cases Option.some.inj assigned
        exact stored
      next => contradiction

theorem capture_interpretation {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {name : String} {target : Pattern}
    (captured : capture? rule spec ambient depth site path initial name target = some final) :
    ∃ dependencies arguments value,
      dependencies? spec name = some dependencies ∧
      arguments? rule spec name site path = some arguments ∧
      recoverValue? dependencies ambient depth arguments target = some value ∧
      lookup final name = some value ∧
      instantiateValue? value ambient depth arguments = some target ∧ Extends initial final := by
  simp only [capture?, Option.bind_eq_bind, Option.bind_eq_some_iff] at captured
  obtain ⟨dependencies, declared, arguments, occurrence, value, recovered, assigned⟩ := captured
  exact ⟨dependencies, arguments, value, declared, occurrence, recovered,
    assign_lookup assigned,
    recoverValue?_forward dependencies ambient depth arguments target value recovered,
    assign_extends assigned⟩

theorem capture_extends {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {name : String} {target : Pattern}
    (captured : capture? rule spec ambient depth site path initial name target = some final) :
    Extends initial final := by
  obtain ⟨_, _, _, _, _, _, _, _, extension⟩ := capture_interpretation captured
  exact extension

mutual
  theorem Matches.extends {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
      {pattern target : Pattern}
      (matched : Matches rule spec ambient site path depth initial pattern target final) :
      Extends initial final := by
    cases matched with
    | capture captured => exact capture_extends captured
    | bound => exact Extends.refl _
    | constructor arguments => exact arguments.extends
    | binder body => exact body.extends
    | binders body => exact body.extends
    | substitution body replacement => exact body.extends.trans replacement.extends
    | bag _ bag => exact bag.extends
    | vector arguments => exact arguments.extends
    | vectorRest arguments captured => exact arguments.extends.trans (capture_extends captured)
  termination_by sizeOf pattern

  theorem Arguments.extends {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
      {patterns targets : List Pattern}
      (matched : Arguments rule spec ambient site path depth initial index patterns targets final) :
      Extends initial final := by
    cases matched with
    | nil => exact Extends.refl _
    | cons head tail => exact head.extends.trans tail.extends
  termination_by sizeOf patterns

  theorem Bag.extends {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
      {patterns targets : List Pattern} {rest : Option String} {kind : CollType}
      (matched : Bag rule spec ambient site path depth initial index patterns rest kind targets final) :
      Extends initial final := by
    cases matched with
    | nil => exact Extends.refl _
    | rest captured => exact capture_extends captured
    | cons _ _ head tail => exact head.extends.trans tail.extends
  termination_by sizeOf patterns
end

theorem matchAt_extends {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
    {pattern target : Pattern}
    (member : final ∈ matchAt rule spec ambient site path depth initial pattern target) :
    Extends initial final := (matchAt_sound member).extends

end Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch

/-! ## Free-name coverage of the original operations -/

namespace Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch

open Mettapedia.OSLF.MeTTaIL.Syntax
open RuleBinding
open ScopedRuleMatching

mutual
 theorem matched_free_within {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
    {schema target : Pattern} (matched : GeneralScopedMatch.Matches rule spec ambient site path depth initial schema target final)
    (footprint : List String) (before : assignmentFreeWithin footprint initial)
    (covered : ∀ name ∈ target.freeFvarNames, name ∈ footprint) : assignmentFreeWithin footprint final := by
  cases matched with
  | capture captured => exact capture_free_within footprint rule spec ambient depth site path initial final _ target before covered captured
  | bound => exact before
  | constructor arguments =>
      apply arguments_free_within arguments footprint before
      intro target member name occurs
      exact covered name (by simpa only [Pattern.freeFvarNames] using List.mem_flatMap.mpr ⟨target, member, occurs⟩)
  | binder body => exact matched_free_within body footprint before (by simpa only [Pattern.freeFvarNames] using covered)
  | binders body => exact matched_free_within body footprint before (by simpa only [Pattern.freeFvarNames] using covered)
  | substitution body replacement =>
      apply matched_free_within replacement footprint
      · apply matched_free_within body footprint before
        intro name occurs
        exact covered name (by simpa only [Pattern.freeFvarNames] using List.mem_append_left _ occurs)
      · intro name occurs
        exact covered name (by simpa only [Pattern.freeFvarNames] using List.mem_append_right _ occurs)
  | bag _ bag =>
      apply bag_free_within bag footprint before
      intro target member name occurs
      exact covered name (by simp only [Pattern.freeFvarNames, Option.toList_none, List.append_nil]; exact List.mem_flatMap.mpr ⟨target, member, occurs⟩)
  | vector arguments =>
      apply arguments_free_within arguments footprint before
      intro target member name occurs
      exact covered name (by simp only [Pattern.freeFvarNames, Option.toList_none, List.append_nil]; exact List.mem_flatMap.mpr ⟨target, member, occurs⟩)
  | vectorRest arguments captured =>
      apply capture_rest_free_within footprint rule spec ambient depth site _ _ final _ .vec _ _ _ captured
      · apply arguments_free_within arguments footprint before
        intro target member name occurs
        exact covered name (by simp only [Pattern.freeFvarNames, Option.toList_none, List.append_nil]; exact List.mem_flatMap.mpr ⟨target, List.mem_of_mem_take member, occurs⟩)
      · intro target member name occurs
        exact covered name (by simp only [Pattern.freeFvarNames, Option.toList_none, List.append_nil]; exact List.mem_flatMap.mpr ⟨target, List.mem_of_mem_drop member, occurs⟩)
 termination_by sizeOf schema

 theorem arguments_free_within {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
    {schemas targets : List Pattern} (matched : GeneralScopedMatch.Arguments rule spec ambient site path depth initial index schemas targets final)
    (footprint : List String) (before : assignmentFreeWithin footprint initial)
    (covered : patternsFreeWithin footprint targets) : assignmentFreeWithin footprint final := by
  cases matched with
  | nil => exact before
  | cons head tail =>
      apply arguments_free_within tail footprint
      · apply matched_free_within head footprint before
        exact covered _ (by simp)
      · intro target member name occurs
        exact covered target (List.mem_cons_of_mem _ member) name occurs
 termination_by sizeOf schemas

 theorem bag_free_within {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
    {schemas targets : List Pattern} {rest : Option String} {kind : CollType}
    (matched : GeneralScopedMatch.Bag rule spec ambient site path depth initial index schemas rest kind targets final)
    (footprint : List String) (before : assignmentFreeWithin footprint initial)
    (covered : patternsFreeWithin footprint targets) : assignmentFreeWithin footprint final := by
  cases matched with
  | nil => exact before
  | rest captured => exact capture_rest_free_within footprint rule spec ambient depth site _ initial final _ kind targets before covered captured
  | cons selected within head tail =>
      apply bag_free_within tail footprint
      · apply matched_free_within head footprint before
        exact covered _ (List.getElem_mem within)
      · intro target member name occurs
        exact covered target (List.mem_of_mem_eraseIdx member) name occurs
 termination_by sizeOf schemas
end

#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch.matched_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch.arguments_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch.bag_free_within

end Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch
