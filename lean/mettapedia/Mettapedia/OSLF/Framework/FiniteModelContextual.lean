import Mettapedia.OSLF.Framework.FiniteModels
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Finite-model certificates for the contextual semantics

MeTTaIL's own reduction relation (`ContextualStep.Step`) takes its contexts from the language: a rule
with a congruence premise `x ~> y` rewrites inside whatever its left side puts around `x`, including
under a binder (`Lam (λ. x) ~> Lam (λ. y) if x ~> y`). A certificate covers it with a conditional rule
check (`Certificate.contextualRuleCheck`): under every table, when the premise goes down the preorder
at every environment of its depth, the rule does. For a binder this is exactly the monotonicity of
the abstraction.

Every derivation then goes down the preorder, by induction on its depth, in every environment of the
bound variables around it (`Certificate.contextual_below`), so a state from which no goal element lies
below cannot reach the goals (`Certificate.cannotReachContextual_of_check`), or never reaches an accepted
value (`Certificate.cannotReachContextualAccepted_of_check`).

The semantics instantiates scope-correctly: a metavariable used under more binders than the left side
captured it under is lifted past them (`applyBindingsScoped`), so its value reads the outermost binders
around its use (`scopedValuation`, `eval_applyBindingsScoped`), and the check reads its tables the same
way (`outerValuation`). Premises other than congruences between metavariables are decided by the
language's evaluator; the verdicts hold for every evaluator that only adds bindings (`BaseExtends`), which
is every evaluator when all premises are congruences (`baseExtends_of_congruencesOnly`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FiniteModels

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchArgsRel MatchBagRel BindingsExtends matchPattern_sound
  mergeBindings_subsumed_left mergeBindings_subsumed_right)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (StepAt PremiseAt PremisesAt BasePremiseEvaluator)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)
open Mettapedia.OSLF.Framework.BackwardSearch
open Mettapedia.OSLF.Framework.DerivedModalities (ReductionSpan)
open Mettapedia.OSLF.Framework.HerbrandBridge (Goal)

/-! ## Rules with congruence premises -/

/-- A congruence premise between two metavariables: the one that steps and the one it steps to. -/
def congruencePair? : Premise → Option (String × String)
  | .congruence (.fvar source) (.fvar target) => some (source, target)
  | .scopedStep step =>
      match step.binders, step.source, step.target with
      | [], .fvar source, .fvar target => some (source, target)
      | _, _, _ => none
  | _ => none

/-- The metavariables of a rule's two sides, each at its first depth. -/
def contextualSpec (rule : RewriteRule) : List (String × ℕ) :=
  firstDepths (occurrences 0 rule.left ++ occurrences 0 rule.right)

/-- The depth of a metavariable in a rule. -/
def depthIn (rule : RewriteRule) (name : String) : Option ℕ :=
  ((contextualSpec rule).find? (·.1 == name)).map (·.2)

/-- Every congruence premise between metavariables relates two of the same depth, the first one on the
left side. Other premises are decided by the language's evaluator. -/
def premisesShape (rule : RewriteRule) : Bool :=
  rule.premises.all fun premise =>
    match congruencePair? premise with
    | some (source, target) =>
        (occurrences 0 rule.left).any (·.1 == source) && (depthIn rule source).isSome &&
          depthIn rule source == depthIn rule target
    | none => true

/-- **The scope the semantics instantiates with**: each metavariable of the left side sits at the depth
the scoped applier captures it at, and the right side uses a captured metavariable at least that deep,
and any other at one depth. -/
def scopeShape (rule : RewriteRule) : Bool :=
  (occurrences 0 rule.left).all (fun entry =>
      captureDepth entry.1 0 rule.left == some entry.2 && decide (entry ∈ contextualSpec rule)) &&
    (occurrences 0 rule.right).all fun entry =>
      match captureDepth entry.1 0 rule.left with
      | some captured => decide (captured ≤ entry.2)
      | none => depthIn rule entry.1 == some entry.2

/-- A valuation read through the outermost entries of each environment, as many as each metavariable's
depth. -/
def outerValuation {A : Type} (depth : String → ℕ) (valuation : Valuation A) : Valuation A := fun name env =>
  valuation name (env.drop (env.length - depth name))

variable {A : Type} [DecidableEq A]

namespace Certificate

variable (certificate : Certificate A)

/-- **A rule with congruence premises goes down the preorder**: under every table, read the way the
scoped instantiation reads it, when each congruence premise goes down at every environment of its
depth, the left side lies above the right side. -/
def contextualRuleCheck (rule : RewriteRule) : Bool :=
  restsCovered rule && premisesShape rule && scopeShape rule &&
    rule.left.isWellScopedAt 0 && rule.right.isWellScopedAt 0 &&
    (tables certificate.elements (contextualSpec rule)).all fun table =>
      let valuation := outerValuation (fun name => (depthIn rule name).getD 0)
        (tableValuation certificate.model certificate.elements table)
      !(rule.premises.all fun premise =>
          match congruencePair? premise with
          | some (source, target) =>
              (vectors certificate.elements ((depthIn rule source).getD 0)).all fun env =>
                certificate.below (valuation source env) (valuation target env)
          | none => true) ||
        certificate.below (eval certificate.model valuation [] rule.left)
          (eval certificate.model valuation [] rule.right)

/-- **Validity for the contextual semantics**: a preorder, left-commutative unordered collection joins, and every rule
checked with its premises. -/
def contextualValid (language : LanguageDef) : Bool :=
  certificate.preorderValid && language.rewrites.all certificate.contextualRuleCheck

end Certificate

/-! ## Evaluation in an outer environment -/

/-- A valuation read below an outer environment. -/
def shiftValuation (valuation : Valuation A) (outer : List A) : Valuation A := fun name env =>
  valuation name (env ++ outer)

variable (model : FiniteModel A)

omit [DecidableEq A] in
/-- **A pattern in scope evaluates the same below an outer environment**, with the valuation shifted. -/
theorem eval_shift (valuation : Valuation A) (outer : List A) (pattern : Pattern) :
    ∀ env : List A, pattern.isWellScopedAt env.length = true →
      eval model valuation (env ++ outer) pattern = eval model (shiftValuation valuation outer) env pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    intro env inScope
    simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at inScope
    simp only [eval, List.getD_eq_getElem?_getD, List.getElem?_append_left inScope]
  | hfvar name => intro _ _; rfl
  | happly label arguments ih =>
    intro env inScope
    simp only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] at inScope
    simp only [eval, evalList_eq_map]
    congr 1
    exact List.map_congr_left fun argument member => ih argument member env (inScope argument member)
  | hlambda name body ih =>
    intro env inScope
    simp only [eval]
    congr 1
    funext value
    exact ih (value :: env) (by simpa [Pattern.isWellScopedAt] using inScope)
  | hmultiLambda arity names body ih =>
    intro env inScope
    simp only [eval]
    congr 1
    funext values
    rw [← List.append_assoc]
    exact ih (List.ofFn values ++ env) (by simpa [Pattern.isWellScopedAt, Nat.add_comm] using inScope)
  | hsubst body replacement bodyIh replacementIh =>
    intro env inScope
    simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at inScope
    simp only [eval]
    rw [replacementIh env inScope.2]
    exact bodyIh (_ :: env) (by simpa using inScope.1)
  | hcollection kind elements rest ih =>
    intro env inScope
    simp only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] at inScope
    simp only [eval, evalList_eq_map]
    rw [List.map_congr_left fun element member => ih element member env (inScope element member)]
    cases rest <;> rfl

/-! ## Scoped instantiation -/

/-- The valuation a scoped instantiation gives below an outer environment of length `outer`: a
metavariable the left side captures `captured` binders deep reads its value through the outermost
`captured` binders around its use, as the scoped applier lifts it; any other reads its value where it
stands. -/
def scopedValuation (lhs : Pattern) (bindings : Bindings) (outer : ℕ) : Valuation A := fun name env =>
  match bindings.find? (·.1 == name) with
  | some (_, bound) =>
      match captureDepth name 0 lhs with
      | some captured => eval model (stateValuation model) (env.drop (env.length - outer - captured)) bound
      | none => eval model (stateValuation model) env bound
  | none => model.junk

omit [DecidableEq A] in
/-- **Scoped instantiation evaluates as the pattern under the scoped valuation**, in any environment
below an outer one. -/
theorem eval_applyBindingsScoped (lhs : Pattern) (bindings : Bindings) (outer : List A) (pattern : Pattern)
    (bound : RestsBound bindings pattern) :
    ∀ inner : List A, eval model (stateValuation model) (inner ++ outer)
        (applyBindingsScoped lhs bindings inner.length pattern) =
      eval model (scopedValuation model lhs bindings outer.length) (inner ++ outer) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro inner; simp [eval]
  | hfvar name =>
    intro inner
    simp only [applyBindingsScoped, eval, scopedValuation]
    cases found : bindings.find? (·.1 == name) with
    | none => simp [eval, stateValuation]
    | some entry =>
      obtain ⟨_, value⟩ := entry
      cases captured : captureDepth name 0 lhs with
      | none => simp
      | some depth =>
        simp only
        rw [eval_liftBVars (stateValuation_independent model), dropAt_zero]
        congr 2
        simp only [List.length_append]
        omega
  | happly label arguments ih =>
    intro inner
    simp only [applyBindingsScoped_apply, eval, evalList_eq_map, List.map_map]
    congr 1
    refine List.map_congr_left fun argument member => ih argument member (fun entry inside => bound entry ?_) inner
    simp only [restVars, restVarsList_eq, List.mem_flatMap]
    exact ⟨argument, member, inside⟩
  | hlambda name body ih =>
    intro inner
    simp only [applyBindingsScoped, eval]
    congr 1
    funext value
    exact ih (fun entry inside => bound entry (by simpa [restVars] using inside)) (value :: inner)
  | hmultiLambda arity names body ih =>
    intro inner
    simp only [applyBindingsScoped, eval]
    congr 1
    funext values
    have shifted := ih (fun entry inside => bound entry (by simpa [restVars] using inside)) (List.ofFn values ++ inner)
    rw [List.length_append, List.length_ofFn, List.append_assoc, Nat.add_comm] at shifted
    exact shifted
  | hsubst body replacement bodyIh replacementIh =>
    intro inner
    simp only [applyBindingsScoped, eval]
    rw [eval_instantiateBVar (stateValuation_independent model),
      replacementIh (fun entry inside => bound entry (by simp [restVars, inside])) inner]
    exact bodyIh (fun entry inside => bound entry (by simp [restVars, inside])) (_ :: inner)
  | hcollection kind elements rest ih =>
    intro inner
    have mapped : elements.map (fun element => eval model (stateValuation model) (inner ++ outer)
          (applyBindingsScoped lhs bindings inner.length element)) =
        elements.map (eval model (scopedValuation model lhs bindings outer.length) (inner ++ outer)) :=
      List.map_congr_left fun element member => ih element member (fun entry inside => bound entry (by
        simp only [restVars, restVarsList_eq, List.mem_append, List.mem_flatMap]
        exact Or.inl ⟨element, member, inside⟩)) inner
    cases rest with
    | none =>
      simp only [applyBindingsScoped, restSplice, applyBindingsScopedList_eq_map, List.append_nil, eval,
        evalList_eq_map, restValue, List.map_map, Function.comp_def]
      rw [mapped]
    | some name =>
      obtain ⟨restElements, found⟩ := bound (name, kind) (by simp [restVars])
      simp only [applyBindingsScoped, restSplice, found, beq_self_eq_true, ↓reduceIte,
        applyBindingsScopedList_eq_map, eval, evalList_eq_map, restValue, scopedValuation, List.map_append,
        List.foldr_append, List.map_map, Function.comp_def]
      rw [mapped]
      cases captured : captureDepth name 0 lhs with
      | none => simp
      | some depth =>
        simp only
        congr 1
        apply congrArg (List.foldr (model.collectionJoin kind) (model.collectionUnit kind))
        rw [List.map_map]
        refine List.map_congr_left fun element _ => ?_
        simp only [Function.comp_apply]
        rw [eval_liftBVars (stateValuation_independent model), dropAt_zero]
        congr 2
        simp only [List.length_append]
        omega

mutual
/-- **The depth a metavariable is captured at is one of its occurrences.** -/
theorem mem_occurrences_of_captureDepth (name : String) : ∀ (depth : ℕ) (pattern : Pattern) (captured : ℕ),
    captureDepth name depth pattern = some captured → (name, captured) ∈ occurrences depth pattern
  | depth, .fvar other, captured, found => by
    simp only [captureDepth] at found
    split at found
    · rename_i same
      simp only [Option.some.injEq] at found
      subst found
      simp only [beq_iff_eq] at same
      subst same
      simp [occurrences]
    · simp at found
  | _, .bvar _, _, found => by simp [captureDepth] at found
  | depth, .apply _ arguments, captured, found => by
    simp only [captureDepth] at found
    simpa [occurrences] using mem_occurrencesList_of_captureDepthList name depth arguments captured found
  | depth, .lambda _ body, captured, found => by
    simp only [captureDepth] at found
    simpa [occurrences] using mem_occurrences_of_captureDepth name (depth + 1) body captured found
  | depth, .multiLambda arity _ body, captured, found => by
    simp only [captureDepth] at found
    simpa [occurrences] using mem_occurrences_of_captureDepth name (depth + arity) body captured found
  | depth, .subst body replacement, captured, found => by
    simp only [captureDepth] at found
    simp only [occurrences, List.mem_append]
    split at found
    · rename_i inBody
      simp only [Option.some.injEq] at found
      subst found
      exact Or.inl (mem_occurrences_of_captureDepth name (depth + 1) body _ inBody)
    · exact Or.inr (mem_occurrences_of_captureDepth name depth replacement captured found)
  | depth, .collection _ elements rest, captured, found => by
    simp only [captureDepth] at found
    simp only [occurrences, List.mem_append]
    split at found
    · rename_i inElements
      simp only [Option.some.injEq] at found
      subst found
      exact Or.inl (mem_occurrencesList_of_captureDepthList name depth elements _ inElements)
    · right
      cases rest with
      | none => simp at found
      | some restName =>
        simp only at found
        split at found
        · rename_i same
          simp only [Option.some.injEq] at found
          subst found
          simp only [beq_iff_eq] at same
          subst same
          simp
        · simp at found

theorem mem_occurrencesList_of_captureDepthList (name : String) : ∀ (depth : ℕ) (patterns : List Pattern)
    (captured : ℕ), captureDepthList name depth patterns = some captured →
      (name, captured) ∈ occurrencesList depth patterns
  | _, [], _, found => by simp [captureDepthList] at found
  | depth, pattern :: patterns, captured, found => by
    simp only [captureDepthList] at found
    simp only [occurrencesList, List.mem_append]
    split at found
    · rename_i inHead
      simp only [Option.some.injEq] at found
      subst found
      exact Or.inl (mem_occurrences_of_captureDepth name depth pattern _ inHead)
    · exact Or.inr (mem_occurrencesList_of_captureDepthList name depth patterns captured found)
end

/-! ## What matching an object state provides -/

mutual
/-- **The values of a match of an object state are object patterns.** -/
theorem object_of_matchRel : ∀ {pattern state : Pattern} {bindings : Bindings}, MatchRel pattern state bindings →
    isObjectPattern state = true → ∀ entry ∈ bindings, isObjectPattern entry.2 = true
  | _, _, _, .fvar, object, entry, inside => by
    simp only [List.mem_singleton] at inside
    subst inside
    exact object
  | _, _, _, .bvar, _, entry, inside => by simp at inside
  | _, _, _, .apply arguments _, object, entry, inside =>
    objectList_of_matchArgsRel arguments (by simpa [isObjectPattern] using object) entry inside
  | _, _, _, .lambda body, object, entry, inside =>
    object_of_matchRel body (by simpa [isObjectPattern] using object) entry inside
  | _, _, _, .multiLambda body, object, entry, inside =>
    object_of_matchRel body (by simpa [isObjectPattern] using object) entry inside
  | _, _, _, .collection _ bag, object, entry, inside => by
    simp only [isObjectPattern, Bool.and_eq_true] at object
    exact objectBag_of_matchBagRel bag object.2 entry inside
  | _, _, _, .vector arguments, object, entry, inside => by
    simp only [isObjectPattern, Bool.and_eq_true] at object
    exact objectList_of_matchArgsRel arguments object.2 entry inside
  | _, _, _, .vectorRest prefixMatch merged, object, entry, inside => by
    simp only [isObjectPattern, Bool.and_eq_true] at object
    rcases mem_of_mergeBindings merged entry inside with inPrefix | isRest
    · exact objectList_of_matchArgsRel prefixMatch (list_of_objects fun pattern member =>
        objects_of_list object.2 pattern (List.mem_of_mem_take member)) entry inPrefix
    · simp only [List.mem_singleton] at isRest
      subst isRest
      simp only [isObjectPattern, Option.isNone_none, Bool.true_and]
      exact list_of_objects fun pattern member => objects_of_list object.2 pattern (List.mem_of_mem_drop member)
  | _, _, _, .subst _ _ _, object, _, _ => by simp [isObjectPattern] at object

theorem objectList_of_matchArgsRel : ∀ {patterns states : List Pattern} {bindings : Bindings},
    MatchArgsRel patterns states bindings → isObjectPatternList states = true →
      ∀ entry ∈ bindings, isObjectPattern entry.2 = true
  | _, _, _, .nil, _, entry, inside => by simp at inside
  | _, _, _, .cons head tail merged, objects, entry, inside => by
    simp only [isObjectPatternList, Bool.and_eq_true] at objects
    rcases mem_of_mergeBindings merged entry inside with inHead | inTail
    · exact object_of_matchRel head objects.1 entry inHead
    · exact objectList_of_matchArgsRel tail objects.2 entry inTail

theorem objectBag_of_matchBagRel :
    ∀ {patterns : List Pattern} {rest : Option String} {kind : CollType} {states : List Pattern} {bindings : Bindings},
      MatchBagRel patterns rest kind states bindings → isObjectPatternList states = true →
        ∀ entry ∈ bindings, isObjectPattern entry.2 = true
  | _, _, _, _, _, .nilNoRest, _, entry, inside => by simp at inside
  | _, _, _, _, _, .nilRest, objects, entry, inside => by
    simp only [List.mem_singleton] at inside
    subst inside
    simp [isObjectPattern, objects]
  | _, _, _, _, _, MatchBagRel.cons _ below head tail merged, objects, entry, inside => by
    rcases mem_of_mergeBindings merged entry inside with inHead | inTail
    · exact object_of_matchRel head (objects_of_list objects _ (List.getElem_mem below)) entry inHead
    · exact objectBag_of_matchBagRel tail (list_of_objects fun pattern member =>
        objects_of_list objects pattern (List.mem_of_mem_eraseIdx member)) entry inTail
end

mutual
/-- **A match binds every metavariable of the pattern.** -/
theorem covers_of_matchRel : ∀ {pattern state : Pattern} {bindings : Bindings}, MatchRel pattern state bindings →
    ∀ depth, ∀ entry ∈ occurrences depth pattern, ∃ value, bindings.find? (·.1 == entry.1) = some (entry.1, value)
  | _, state, _, @MatchRel.fvar name _, depth, entry, inside => by
    simp only [occurrences, List.mem_singleton] at inside
    subst inside
    exact ⟨state, find?_singleton _ _⟩
  | _, _, _, .bvar, _, _, inside => by simp [occurrences] at inside
  | _, _, _, .apply arguments _, depth, entry, inside =>
    coversList_of_matchArgsRel arguments depth entry (by simpa [occurrences] using inside)
  | _, _, _, .lambda body, depth, entry, inside =>
    covers_of_matchRel body (depth + 1) entry (by simpa [occurrences] using inside)
  | _, _, _, .multiLambda body, depth, entry, inside =>
    covers_of_matchRel body _ entry (by simpa [occurrences] using inside)
  | _, _, _, .collection _ bag, depth, entry, inside => coversBag_of_matchBagRel bag depth entry inside
  | _, _, _, .vector arguments, depth, entry, inside => by
    simp only [occurrences, List.append_nil] at inside
    exact coversList_of_matchArgsRel arguments depth entry inside
  | _, _, _, .vectorRest (rv := name) prefixMatch merged, depth, entry, inside => by
    simp only [occurrences, List.mem_append, List.mem_singleton] at inside
    rcases inside with inElements | rfl
    · obtain ⟨value, found⟩ := coversList_of_matchArgsRel prefixMatch depth entry inElements
      exact ⟨value, mergeBindings_subsumed_left merged found⟩
    · exact ⟨_, mergeBindings_subsumed_right merged (find?_singleton _ _)⟩
  | _, _, _, .subst body replacement merged, depth, entry, inside => by
    simp only [occurrences, List.mem_append] at inside
    rcases inside with inBody | inReplacement
    · obtain ⟨value, found⟩ := covers_of_matchRel body (depth + 1) entry inBody
      exact ⟨value, mergeBindings_subsumed_left merged found⟩
    · obtain ⟨value, found⟩ := covers_of_matchRel replacement depth entry inReplacement
      exact ⟨value, mergeBindings_subsumed_right merged found⟩

theorem coversList_of_matchArgsRel : ∀ {patterns states : List Pattern} {bindings : Bindings},
    MatchArgsRel patterns states bindings → ∀ depth, ∀ entry ∈ occurrencesList depth patterns,
      ∃ value, bindings.find? (·.1 == entry.1) = some (entry.1, value)
  | _, _, _, .nil, _, _, inside => by simp [occurrencesList] at inside
  | _, _, _, .cons head tail merged, depth, entry, inside => by
    simp only [occurrencesList, List.mem_append] at inside
    rcases inside with inHead | inTail
    · obtain ⟨value, found⟩ := covers_of_matchRel head depth entry inHead
      exact ⟨value, mergeBindings_subsumed_left merged found⟩
    · obtain ⟨value, found⟩ := coversList_of_matchArgsRel tail depth entry inTail
      exact ⟨value, mergeBindings_subsumed_right merged found⟩

theorem coversBag_of_matchBagRel :
    ∀ {patterns : List Pattern} {rest : Option String} {kind : CollType} {states : List Pattern} {bindings : Bindings},
      MatchBagRel patterns rest kind states bindings → ∀ depth, ∀ entry ∈ occurrences depth (.collection kind patterns rest),
        ∃ value, bindings.find? (·.1 == entry.1) = some (entry.1, value)
  | _, _, _, _, _, .nilNoRest, _, _, inside => by simp [occurrences, occurrencesList] at inside
  | _, _, _, _, _, .nilRest (rv := name), depth, entry, inside => by
    simp only [occurrences, occurrencesList, List.nil_append, List.mem_singleton] at inside
    subst inside
    exact ⟨_, find?_singleton _ _⟩
  | _, _, _, _, _, MatchBagRel.cons _ _ head tail merged, depth, entry, inside => by
    simp only [occurrences, occurrencesList, List.mem_append] at inside
    rcases inside with (inHead | inTail) | inRest
    · obtain ⟨value, found⟩ := covers_of_matchRel head depth entry inHead
      exact ⟨value, mergeBindings_subsumed_left merged found⟩
    · obtain ⟨value, found⟩ := coversBag_of_matchBagRel tail depth entry (by
        simp only [occurrences, List.mem_append]; exact Or.inl inTail)
      exact ⟨value, mergeBindings_subsumed_right merged found⟩
    · obtain ⟨value, found⟩ := coversBag_of_matchBagRel tail depth entry (by
        simp only [occurrences, List.mem_append]; exact Or.inr inRest)
      exact ⟨value, mergeBindings_subsumed_right merged found⟩
end

/-! ## Premises -/

/-- **The evaluator of the other premises only adds bindings**, at every premise of the language that
is not a congruence between metavariables. -/
def BaseExtends (base : BasePremiseEvaluator) (language : LanguageDef) : Prop :=
  ∀ rule ∈ language.rewrites, ∀ premise ∈ rule.premises, congruencePair? premise = none →
    ∀ bindings result, result ∈ base language bindings premise → BindingsExtends bindings result

/-- Every premise of the language is a congruence between metavariables. -/
def congruencesOnly (language : LanguageDef) : Bool :=
  language.rewrites.all fun rule => rule.premises.all fun premise => (congruencePair? premise).isSome

/-- **A language whose premises are all congruences needs nothing of the evaluator.** -/
theorem baseExtends_of_congruencesOnly {language : LanguageDef} (checked : congruencesOnly language = true)
    (base : BasePremiseEvaluator) : BaseExtends base language := by
  intro rule member premise inside none _ _ _
  simp only [congruencesOnly, List.all_eq_true] at checked
  have some := checked rule member premise inside
  rw [none] at some
  simp at some

/-- **The engine's evaluator only adds bindings**: a freshness premise keeps them, and a relation query
merges into them. -/
theorem engine_extends (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv) (language : LanguageDef) :
    BaseExtends (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises relations) language := by
  intro _ _ premise _ _ bindings result member
  cases premise with
  | freshness condition =>
    simp only [Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises] at member
    have same := Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv_freshness_mem member
    subst same
    exact fun _ _ found => found
  | relationQuery relation arguments =>
    simp only [Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises] at member
    obtain ⟨added, merge⟩ := Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv_relationQuery_mem member
    exact fun _ _ found => mergeBindings_subsumed_left merge found
  | congruence => simp [Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises] at member
  | scopedStep => simp [Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises,
      Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv] at member
  | forAll => simp [Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises,
      Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv] at member

section Premises

variable {base : BasePremiseEvaluator} {language : LanguageDef} {fuel : ℕ}

theorem extends_of_premiseAt {bindings result : Bindings} {premise : Premise}
    (fromBase : congruencePair? premise = none →
      ∀ bindings result, result ∈ base language bindings premise → BindingsExtends bindings result)
    (evidence : PremiseAt base language fuel bindings premise result) : BindingsExtends bindings result := by
  cases evidence with
  | freshness decided => exact fromBase (by simp [congruencePair?]) _ _ decided
  | relationQuery decided => exact fromBase (by simp [congruencePair?]) _ _ decided
  | forAll decided => exact fromBase (by simp [congruencePair?]) _ _ decided
  | congruence _ _ merged => exact fun _ _ found => mergeBindings_subsumed_left merged found
  | scopedRoot _ _ _ merged => exact fun _ _ found => mergeBindings_subsumed_left merged found

/-- **Premises only add bindings.** -/
theorem extends_of_premisesAt : ∀ {initial final : Bindings} {premises : List Premise},
    PremisesAt base language fuel initial premises final →
    (∀ premise ∈ premises, congruencePair? premise = none →
      ∀ bindings result, result ∈ base language bindings premise → BindingsExtends bindings result) →
    BindingsExtends initial final
  | _, _, _, .nil _, _ => fun _ _ found => found
  | _, _, _, .cons first rest, fromBase => fun name value found =>
    extends_of_premisesAt rest (fun premise member => fromBase premise (List.mem_cons_of_mem _ member)) name value
      (extends_of_premiseAt (fromBase _ List.mem_cons_self) first name value found)

theorem congruence_cases {premise : Premise} {source target : String}
    (pair : congruencePair? premise = some (source, target)) :
    premise = .congruence (.fvar source) (.fvar target) ∨
      ∃ step : ScopedStepPremise, premise = .scopedStep step ∧ step.binders = [] ∧ step.source = .fvar source ∧
        step.target = .fvar target := by
  cases premise with
  | congruence first second =>
    cases first <;> cases second <;> simp_all [congruencePair?]
  | scopedStep step =>
    right
    obtain ⟨binders, resultType, first, second⟩ := step
    cases binders <;> cases first <;> cases second <;> simp_all [congruencePair?]
  | _ => simp [congruencePair?] at pair

/-- **What a congruence premise provides**: the value of its first metavariable steps to the value of the
second. -/
theorem step_of_premisesAt : ∀ {initial final : Bindings} {premises : List Premise},
    PremisesAt base language fuel initial premises final →
    (∀ premise ∈ premises, congruencePair? premise = none →
      ∀ bindings result, result ∈ base language bindings premise → BindingsExtends bindings result) →
    ∀ premise ∈ premises, ∀ source target, congruencePair? premise = some (source, target) →
      ∀ value, initial.find? (·.1 == source) = some (source, value) →
        ∃ candidate, StepAt base language fuel value candidate ∧
          final.find? (·.1 == target) = some (target, candidate)
  | _, _, _, .nil _, _, _, member, _, _, _, _, _ => by simp at member
  | initial, final, _, .cons (middle := middle) first rest, fromBase, premise, member, source, target, pair, value,
      found => by
    have restExtends := extends_of_premisesAt rest fun other inside => fromBase other (List.mem_cons_of_mem _ inside)
    rcases List.mem_cons.mp member with rfl | later
    · have read : applyBindings initial (.fvar source) = value := by simp [applyBindings, found]
      rcases congruence_cases pair with rfl | ⟨step, rfl, _, stepSource, stepTarget⟩
      · cases first with
        | congruence stepped premiseMatch merged =>
          rw [read] at stepped
          simp only [matchPattern, List.mem_singleton] at premiseMatch
          subst premiseMatch
          exact ⟨_, stepped, restExtends _ _ (mergeBindings_subsumed_right merged (find?_singleton _ _))⟩
      · cases first with
        | scopedRoot _ stepped premiseMatch merged =>
          rw [stepSource, read] at stepped
          rw [stepTarget] at premiseMatch
          simp only [matchPattern, List.mem_singleton] at premiseMatch
          subst premiseMatch
          exact ⟨_, stepped, restExtends _ _ (mergeBindings_subsumed_right merged (find?_singleton _ _))⟩
    · exact step_of_premisesAt rest (fun other inside => fromBase other (List.mem_cons_of_mem _ inside)) premise later
        source target pair value (extends_of_premiseAt (fromBase _ List.mem_cons_self) first _ _ found)

end Premises

/-! ## Every contextual step goes down -/

namespace Certificate

variable {certificate : Certificate A} {language : LanguageDef} {base : BasePremiseEvaluator}

theorem contextual_preorder (checked : certificate.contextualValid language = true) : certificate.preorderValid = true := by
  simp only [contextualValid, Bool.and_eq_true] at checked
  exact checked.1

theorem contextual_rule_checked (checked : certificate.contextualValid language = true) {rule : RewriteRule}
    (member : rule ∈ language.rewrites) : certificate.contextualRuleCheck rule = true := by
  simp only [contextualValid, Bool.and_eq_true, List.all_eq_true] at checked
  exact checked.2 rule member

theorem mem_spec_of_depthIn {rule : RewriteRule} {name : String} {depth : ℕ} (found : depthIn rule name = some depth) :
    (name, depth) ∈ contextualSpec rule := by
  simp only [depthIn, Option.map_eq_some_iff] at found
  obtain ⟨entry, entryFound, rfl⟩ := found
  have same : entry.1 = name := by simpa using List.find?_some entryFound
  rw [← same]
  exact List.mem_of_find?_eq_some entryFound

theorem depthIn_of_mem_spec {rule : RewriteRule} {name : String} {depth : ℕ}
    (member : (name, depth) ∈ contextualSpec rule) : depthIn rule name = some depth := by
  have keys := firstDepths_keys (occurrences 0 rule.left ++ occurrences 0 rule.right)
  simp only [depthIn, contextualSpec] at member ⊢
  obtain ⟨entry, entryFound⟩ : ∃ entry, (firstDepths (occurrences 0 rule.left ++ occurrences 0 rule.right)).find?
      (·.1 == name) = some entry := by
    cases found : (firstDepths (occurrences 0 rule.left ++ occurrences 0 rule.right)).find? (·.1 == name) with
    | none => exact absurd (List.find?_eq_none.mp found (name, depth) member) (by simp)
    | some entry => exact ⟨entry, rfl⟩
  have entryMember := List.mem_of_find?_eq_some entryFound
  have sameName : entry.1 = name := by simpa using List.find?_some entryFound
  have sameEntry : entry = (name, depth) :=
    List.inj_on_of_nodup_map keys entryMember member (by simpa using sameName)
  rw [entryFound, sameEntry]
  rfl

/-- **Every contextual step from an object state goes down the preorder**, in every environment of the
bound variables around it, when the evaluator of the other premises only adds bindings. -/
theorem contextual_below (checked : certificate.contextualValid language = true) (fromBase : BaseExtends base language) :
    ∀ (fuel : ℕ) {source target : Pattern}, StepAt base language fuel source target → isObjectPattern source = true →
      ∀ outer : List A, certificate.below (eval certificate.model (stateValuation certificate.model) outer source)
        (eval certificate.model (stateValuation certificate.model) outer target) = true
  | 0, _, _, step, _, _ => by cases step
  | fuel + 1, source, target, step, object, outer => by
    cases step with
    | @rule _ _ _ rule initial final ruleMember matchMember premisesEvidence targetEq =>
      have ruleChecked := contextual_rule_checked checked ruleMember
      simp only [contextualRuleCheck, Bool.and_eq_true, List.all_eq_true] at ruleChecked
      obtain ⟨⟨⟨⟨⟨covered, shape⟩, scope⟩, leftScoped⟩, rightScoped⟩, tablesChecked⟩ := ruleChecked
      simp only [scopeShape, Bool.and_eq_true, List.all_eq_true] at scope
      obtain ⟨leftDepths, rightDepths⟩ := scope
      rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic] at matchMember
      have targetIs : applyBindingsScoped rule.left final 0 rule.right = target := by
        rw [← targetEq]
        simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule, applyRuleBindings]
      have fromRule := fun premise member => fromBase rule ruleMember premise member
      have extension := extends_of_premisesAt premisesEvidence fromRule
      have relation := matchPattern_sound matchMember
      have comm := preorder_commutes (contextual_preorder checked)
      have rightBound : RestsBound final rule.right := fun entry inside =>
        restsBound_of_matchRel relation final extension entry (by
          simp only [restsCovered, List.all_eq_true, decide_eq_true_eq] at covered
          exact covered entry inside)
      have sourceValue : eval certificate.model (stateValuation certificate.model) outer source =
          eval certificate.model (bindingValuation certificate.model final) outer rule.left := by
        rw [← eval_of_matchRel certificate.model comm relation object final extension outer]
        exact eval_applyBindings certificate.model final rule.left (restsBound_of_matchRel relation final extension) outer
      have targetValue : eval certificate.model (stateValuation certificate.model) outer target =
          eval certificate.model (scopedValuation certificate.model rule.left final outer.length) outer rule.right := by
        rw [← targetIs]
        exact eval_applyBindingsScoped certificate.model rule.left final outer rule.right rightBound []
      have shiftLeft := eval_shift certificate.model (bindingValuation certificate.model final) outer rule.left []
        leftScoped
      have shiftRight := eval_shift certificate.model
        (scopedValuation certificate.model rule.left final outer.length) outer rule.right [] rightScoped
      simp only [List.nil_append] at shiftLeft shiftRight
      rw [sourceValue, targetValue, shiftLeft, shiftRight]
      obtain ⟨table, tableMember, realizes⟩ := exists_table certificate.model certificate.elements certificate.complete
        (shiftValuation (bindingValuation certificate.model final) outer) (contextualSpec rule) (firstDepths_keys _)
      let depthOf := fun name => (depthIn rule name).getD 0
      let read := outerValuation depthOf (tableValuation certificate.model certificate.elements table)
      -- At an environment of a metavariable's own depth, the table reads its value.
      have atDepth : ∀ name depth, (name, depth) ∈ contextualSpec rule → ∀ env : List A, env.length = depth →
          read name env = bindingValuation certificate.model final name (env ++ outer) := by
        intro name depth member env length
        simp only [read, outerValuation, depthOf, depthIn_of_mem_spec member, Option.getD_some, length,
          Nat.sub_self, List.drop_zero]
        rw [realizes (name, depth) member env (by omega), List.take_of_length_le (by omega)]
        rfl
      have leftAgree : eval certificate.model (shiftValuation (bindingValuation certificate.model final) outer) [] rule.left =
          eval certificate.model read [] rule.left :=
        eval_congr certificate.model rule.left [] fun entry inside inner length => by
          have home := leftDepths entry inside
          simp only [beq_iff_eq, decide_eq_true_eq] at home
          rw [atDepth entry.1 entry.2 home.2 inner length]
          rfl
      have rightAgree : eval certificate.model (shiftValuation (scopedValuation certificate.model rule.left final outer.length) outer)
            [] rule.right = eval certificate.model read [] rule.right :=
        eval_congr certificate.model rule.right [] fun entry inside inner length => by
          have used := rightDepths entry inside
          simp only [shiftValuation, scopedValuation]
          cases captured : captureDepth entry.1 0 rule.left with
          | some depth =>
            simp only [captured, decide_eq_true_eq] at used
            have home : (entry.1, depth) ∈ contextualSpec rule := by
              have occurs := mem_occurrences_of_captureDepth entry.1 0 rule.left depth captured
              have checkedHome := leftDepths _ occurs
              simp only [decide_eq_true_eq] at checkedHome
              exact checkedHome.2
            have outerRead : read entry.1 inner =
                bindingValuation certificate.model final entry.1 (inner.drop (inner.length - depth) ++ outer) := by
              simp only [read, outerValuation, depthOf, depthIn_of_mem_spec home, Option.getD_some]
              rw [realizes (entry.1, depth) home _ (by simp; omega), List.take_of_length_le (by simp; omega)]
              rfl
            rw [outerRead]
            simp only [bindingValuation]
            cases found : final.find? (·.1 == entry.1) with
            | none => rfl
            | some pair =>
              obtain ⟨_, bound⟩ := pair
              simp only [List.length_append]
              rw [show inner.length + outer.length - outer.length - depth = inner.length - depth by omega,
                List.drop_append_of_le_length (by omega)]
          | none =>
            simp only [captured, beq_iff_eq] at used
            rw [atDepth entry.1 entry.2 (mem_spec_of_depthIn used) inner length]
            simp only [bindingValuation]
            cases found : final.find? (·.1 == entry.1) with
            | none => rfl
            | some pair => rfl
      have premisesHold : (rule.premises.all fun premise =>
          match congruencePair? premise with
          | some (source, target) =>
              (vectors certificate.elements ((depthIn rule source).getD 0)).all fun env =>
                certificate.below (read source env) (read target env)
          | none => true) = true := by
        rw [List.all_eq_true]
        intro premise member
        have one := List.all_eq_true.mp shape premise member
        cases pair : congruencePair? premise with
        | none => rfl
        | some names =>
          obtain ⟨first, second⟩ := names
          simp only [pair, Bool.and_eq_true, List.any_eq_true, beq_iff_eq, Option.isSome_iff_exists] at one
          obtain ⟨⟨⟨entryFirst, inLeft, sameName⟩, depth, depthFirst⟩, sameDepth⟩ := one
          rw [depthFirst, eq_comm] at sameDepth
          have depthSecond : depthIn rule second = some depth := by simpa using sameDepth
          simp only [depthFirst, Option.getD_some, List.all_eq_true]
          intro env envMember
          have envLength := (mem_vectors certificate.elements certificate.complete depth env).mp envMember
          obtain ⟨firstValue, firstFound⟩ := covers_of_matchRel relation 0 entryFirst inLeft
          rw [sameName] at firstFound
          obtain ⟨candidate, stepped, secondFound⟩ := step_of_premisesAt premisesEvidence fromRule premise member first
            second pair firstValue firstFound
          have firstObject := object_of_matchRel relation object (first, firstValue)
            (List.mem_of_find?_eq_some firstFound)
          have below := contextual_below checked fromBase fuel stepped firstObject (env ++ outer)
          rw [atDepth first depth (mem_spec_of_depthIn depthFirst) env envLength,
            atDepth second depth (mem_spec_of_depthIn depthSecond) env envLength]
          simpa [bindingValuation, extension first firstValue firstFound, secondFound] using below
      have check : (!(rule.premises.all fun premise =>
          match congruencePair? premise with
          | some (source, target) =>
              (vectors certificate.elements ((depthIn rule source).getD 0)).all fun env =>
                certificate.below (read source env) (read target env)
          | none => true) ||
            certificate.below (eval certificate.model read [] rule.left) (eval certificate.model read [] rule.right)) = true :=
        tablesChecked table tableMember
      rw [premisesHold, Bool.not_true, Bool.false_or] at check
      rw [leftAgree, rightAgree]
      exact check

end Certificate

/-! ## Verdicts over the contextual semantics -/

/-- MeTTaIL's contextual semantics of a language, as a span. -/
def contextualSpan (base : BasePremiseEvaluator) (language : LanguageDef) : ReductionSpan Pattern where
  Edge := {pair : Pattern × Pattern // Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base language pair.1 pair.2}
  source edge := edge.1.1
  target edge := edge.1.2

namespace Certificate

variable {certificate : Certificate A} {language : LanguageDef} {base : BasePremiseEvaluator}

/-- **The contextual semantics goes down**, when the evaluator of the other premises only adds bindings. -/
theorem contextualGoesDown (checked : certificate.contextualValid language = true)
    (fromBase : BaseExtends base language) : certificate.GoesDown (contextualSpan base language) := by
  intro event inScope
  obtain ⟨fuel, stepped⟩ := event.2
  exact contextual_below checked fromBase fuel stepped inScope.2 []

variable (certificate) in
/-- **Decide that a state cannot reach the goals under the contextual semantics**: the certificate is
valid for rules with congruence premises, every goal instance is accepted, and no accepted element lies
below the value of the state. -/
def cannotReachContextual (language : LanguageDef) (goals : List Pattern) (accept : A → Bool) (state : Pattern) : Bool :=
  certificate.contextualValid language && goals.all (certificate.goalCheck accept) &&
    certificate.apart accept (value certificate.model state)

/-- The verdict holds for every evaluator of the other premises that only adds bindings. -/
theorem cannotReachContextual_of_check {goals : List Pattern} {accept : A → Bool} {state : Pattern}
    (checked : certificate.cannotReachContextual language goals accept state = true) (base : BasePremiseEvaluator)
    (fromBase : BaseExtends base language) :
    ¬ Reaches (between (contextualSpan base language) ObjectState) (Goal goals) state := by
  simp only [cannotReachContextual, Bool.and_eq_true] at checked
  obtain ⟨⟨valid, goalsChecked⟩, apartChecked⟩ := checked
  exact certificate.not_reaches_of_apart (contextual_preorder valid) (contextualGoesDown valid fromBase)
    goalsChecked apartChecked

variable (certificate) in
/-- **Decide that a state never reaches an accepted value under the contextual semantics**: the accepted
elements are a native type the model selects. -/
def cannotReachContextualAccepted (language : LanguageDef) (accept : A → Bool) (state : Pattern) : Bool :=
  certificate.contextualValid language && certificate.apart accept (value certificate.model state)

theorem cannotReachContextualAccepted_of_check {accept : A → Bool} {state : Pattern}
    (checked : certificate.cannotReachContextualAccepted language accept state = true) (base : BasePremiseEvaluator)
    (fromBase : BaseExtends base language) :
    ¬ Reaches (between (contextualSpan base language) ObjectState)
      (fun reached => accept (value certificate.model reached) = true) state := by
  simp only [cannotReachContextualAccepted, Bool.and_eq_true] at checked
  exact certificate.not_reachesAccepted_of_apart (contextual_preorder checked.1) (contextualGoesDown checked.1 fromBase)
    checked.2

end Certificate

end Mettapedia.OSLF.Framework.FiniteModels
