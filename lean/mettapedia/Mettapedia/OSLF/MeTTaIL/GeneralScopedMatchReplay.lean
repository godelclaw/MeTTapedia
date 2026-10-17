import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineComparison

/-!
# Direct replay of scoped matching choices

Replay follows one supplied stream of residual collection selections. It
checks their literal source paths and threads the original contextual
assignment through the original capture operations. It does not enumerate
matcher answers or run the scoped matcher machine.

The source judgments are the existing `TracedMatches`, `TracedArguments` and
`TracedBag`. The prefix interface leaves unused choices available to the next
operation; the whole-trace interface refuses every unused choice.

Constructor labels and bound indices are compared literally. Binder display
names are ignored exactly as in the source relation. Context formation is a
separate source obligation: replay adds no new admission restriction to the
original traced matching judgments. Contextual capture, repeated-value
comparison and forward instantiation remain computations of the original
capture primitives, rather than additional supplied proof articles.
-/

namespace Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchReplay

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

/-- Thread an actual intermediate assignment and the remaining guidance. -/
def continueReplay (first : Option (Assignment × List BagChoice))
    (next : Assignment → List BagChoice → Option (Assignment × List BagChoice)) :
    Option (Assignment × List BagChoice) :=
  first.bind fun (middle, remaining) => next middle remaining

theorem continueReplay_eq_some_iff (first : Option (Assignment × List BagChoice))
    (next : Assignment → List BagChoice → Option (Assignment × List BagChoice))
    (final : Assignment) (remaining : List BagChoice) :
    continueReplay first next = some (final, remaining) ↔
      ∃ middle rest, first = some (middle, rest) ∧ next middle rest = some (final, remaining) := by
  cases first with
  | none => simp [continueReplay]
  | some pair => cases pair; simp [continueReplay]

mutual

/-- Replay one scoped schema, retaining any unused choice suffix. -/
def replayAt (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat) (initial : Assignment)
    (schema target : Pattern) (trace : List BagChoice) : Option (Assignment × List BagChoice) :=
  match schema, target with
  | .fvar name, target =>
      (capture? rule spec ambient depth site path initial name target).map (fun final => (final, trace))
  | .bvar expected, .bvar actual => if expected = actual then some (initial, trace) else none
  | .apply label schemas, .apply actualLabel targets =>
      if label = actualLabel then
        replayArguments rule spec ambient site path depth initial 0 schemas targets trace
      else none
  | .lambda _ body, .lambda _ targetBody =>
      replayAt rule spec ambient site (path ++ [0]) (depth + 1) initial body targetBody trace
  | .multiLambda arity _ body, .multiLambda actualArity _ targetBody =>
      if arity = actualArity then
        replayAt rule spec ambient site (path ++ [0]) (depth + arity) initial body targetBody trace
      else none
  | .subst body replacement, .subst targetBody targetReplacement =>
      continueReplay
        (replayAt rule spec ambient site (path ++ [0]) (depth + 1) initial body targetBody trace)
        (fun middle rest =>
          replayAt rule spec ambient site (path ++ [1]) depth middle replacement targetReplacement rest)
  | .collection kind schemas rest, .collection actualKind targets actualRest =>
      if kind = actualKind ∧ actualRest = none then
        if kind = .vec then
          match rest with
          | none => replayArguments rule spec ambient site path depth initial 0 schemas targets trace
          | some name =>
              continueReplay
                (replayArguments rule spec ambient site path depth initial 0 schemas
                  (targets.take schemas.length) trace)
                (fun middle remaining =>
                  (captureRest? rule spec ambient depth site (path ++ [schemas.length])
                    middle name .vec (targets.drop schemas.length)).map (fun final => (final, remaining)))
        else replayBag rule spec ambient site path depth initial 0 schemas rest kind targets trace
      else none
  | _, _ => none
termination_by sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

/-- Ordered arguments thread contextual assignments without collection choices. -/
def replayArguments (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat) (initial : Assignment)
    (index : Nat) (schemas targets : List Pattern) (trace : List BagChoice) :
    Option (Assignment × List BagChoice) :=
  match schemas, targets with
  | [], [] => some (initial, trace)
  | schema :: schemas, target :: targets =>
      continueReplay
        (replayAt rule spec ambient site (path ++ [index]) depth initial schema target trace)
        (fun middle rest =>
          replayArguments rule spec ambient site path depth middle (index + 1) schemas targets rest)
  | _, _ => none
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec

/-- Each bag choice names an occurrence of the current residual target list.
Equal target values at different positions remain distinct choices. -/
def replayBag (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat) (initial : Assignment)
    (index : Nat) (schemas : List Pattern) (rest : Option String) (kind : CollType)
    (targets : List Pattern) (trace : List BagChoice) : Option (Assignment × List BagChoice) :=
  match schemas, rest, targets, trace with
  | [], none, [], trace => some (initial, trace)
  | [], none, _ :: _, _ => none
  | [], some name, targets, trace =>
      (captureRest? rule spec ambient depth site (path ++ [index]) initial name kind targets).map
        (fun final => (final, trace))
  | schema :: schemas, rest, targets, choice :: trace =>
      if choice.path = path ++ [index] then
        match targets[choice.selected]? with
        | none => none
        | some target =>
            continueReplay
              (replayAt rule spec ambient site (path ++ [index]) depth initial schema target trace)
              (fun middle remaining =>
                replayBag rule spec ambient site path depth middle (index + 1) schemas rest kind
                  (targets.eraseIdx choice.selected) remaining)
      else none
  | _ :: _, _, _, [] => none
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec

end

/-- An unordered collection first checks the literal tag and closed target,
then consumes the source bag selections. -/
theorem replayAt_collection_unordered (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (initial : Assignment) (kind : CollType) (schemas targets : List Pattern)
    (rest : Option String) (trace : List BagChoice) (notVector : kind ≠ .vec) :
    replayAt rule spec ambient site path depth initial
      (.collection kind schemas rest) (.collection kind targets none) trace =
      replayBag rule spec ambient site path depth initial 0 schemas rest kind targets trace := by
  rw [replayAt.eq_def]
  simp [notVector]

mutual

/-- Successful replay constructs the original traced judgment for precisely
the consumed prefix, with the literal supplied suffix left over. -/
theorem replayAt_sound (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat) (initial : Assignment)
    (schema target : Pattern) (trace : List BagChoice)
    {final : Assignment} {remaining : List BagChoice}
    (replayed : replayAt rule spec ambient site path depth initial schema target trace =
      some (final, remaining)) :
    ∃ consumed, trace = consumed ++ remaining ∧
      TracedMatches rule spec ambient site path depth initial schema target consumed final := by
  match schema, target with
  | .fvar name, target =>
      simp only [replayAt, Option.map_eq_some_iff] at replayed
      obtain ⟨value, captured, same⟩ := replayed
      cases same
      exact ⟨[], rfl, .capture captured⟩
  | .bvar expected, .bvar actual =>
      by_cases same : expected = actual
      · subst actual
        simp only [replayAt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at replayed
        rcases replayed with ⟨rfl, rfl⟩
        exact ⟨[], rfl, .bound⟩
      · simp [replayAt, same] at replayed
  | .apply label schemas, .apply actualLabel targets =>
      by_cases same : label = actualLabel
      · subst actualLabel
        have arguments : replayArguments rule spec ambient site path depth initial 0 schemas targets trace =
            some (final, remaining) := by simpa only [replayAt, and_self, ↓reduceIte] using replayed
        obtain ⟨consumed, consumedEq, matched⟩ := replayArguments_sound _ _ _ _ _ _ _ _ _ _ _ arguments
        exact ⟨consumed, consumedEq, .constructor matched⟩
      · simp [replayAt, same] at replayed
  | .lambda display body, .lambda actualDisplay targetBody =>
      obtain ⟨consumed, consumedEq, matched⟩ := replayAt_sound rule spec ambient site
        (path ++ [0]) (depth + 1) initial body targetBody trace
        (by simpa only [replayAt] using replayed)
      exact ⟨consumed, consumedEq, .binder matched⟩
  | .multiLambda arity display body, .multiLambda actualArity actualDisplay targetBody =>
      by_cases same : arity = actualArity
      · subst actualArity
        obtain ⟨consumed, consumedEq, matched⟩ := replayAt_sound rule spec ambient site
          (path ++ [0]) (depth + arity) initial body targetBody trace
          (by simpa only [replayAt, and_self, ↓reduceIte] using replayed)
        exact ⟨consumed, consumedEq, .binders matched⟩
      · simp [replayAt, same] at replayed
  | .subst body replacement, .subst targetBody targetReplacement =>
      simp only [replayAt] at replayed
      obtain ⟨middle, rest, first, second⟩ := (continueReplay_eq_some_iff _ _ _ _).mp replayed
      obtain ⟨bodyTrace, bodyPrefix, bodyMatched⟩ :=
        replayAt_sound _ _ _ _ _ _ _ _ _ _ first
      obtain ⟨replacementTrace, replacementPrefix, replacementMatched⟩ :=
        replayAt_sound _ _ _ _ _ _ _ _ _ _ second
      refine ⟨bodyTrace ++ replacementTrace, ?_, .substitution bodyMatched replacementMatched⟩
      simp only [bodyPrefix, replacementPrefix, List.append_assoc]
  | .collection kind schemas rest, .collection actualKind targets actualRest =>
      by_cases same : kind = actualKind
      · subst actualKind
        cases actualRest with
        | some name =>
            rw [replayAt.eq_def] at replayed
            simp at replayed
        | none =>
            by_cases vector : kind = .vec
            · subst kind
              cases rest with
              | none =>
                  have arguments : replayArguments rule spec ambient site path depth initial 0
                      schemas targets trace = some (final, remaining) := by
                    simpa only [replayAt, and_self, ↓reduceIte] using replayed
                  obtain ⟨consumed, consumedEq, matched⟩ :=
                    replayArguments_sound _ _ _ _ _ _ _ _ _ _ _ arguments
                  exact ⟨consumed, consumedEq, .vector matched⟩
              | some name =>
                  simp only [replayAt, and_self, ↓reduceIte] at replayed
                  obtain ⟨middle, suffix, arguments, captured⟩ :=
                    (continueReplay_eq_some_iff _ _ _ _).mp replayed
                  simp only [Option.map_eq_some_iff] at captured
                  obtain ⟨value, captured, result⟩ := captured
                  cases result
                  obtain ⟨consumed, consumedEq, matched⟩ :=
                    replayArguments_sound _ _ _ _ _ _ _ _ _ _ _ arguments
                  exact ⟨consumed, consumedEq, .vectorRest matched captured⟩
            · rw [replayAt_collection_unordered _ _ _ _ _ _ _ _ _ _ _ _ vector] at replayed
              obtain ⟨consumed, consumedEq, matched⟩ :=
                replayBag_sound _ _ _ _ _ _ _ _ _ _ _ _ _ replayed
              exact ⟨consumed, consumedEq, .bag vector matched⟩
      · rw [replayAt.eq_def] at replayed
        simp [same] at replayed
  | .bvar _, .fvar _ | .bvar _, .apply _ _ | .bvar _, .lambda _ _
  | .bvar _, .multiLambda _ _ _ | .bvar _, .subst _ _ | .bvar _, .collection _ _ _
  | .apply _ _, .bvar _ | .apply _ _, .fvar _ | .apply _ _, .lambda _ _
  | .apply _ _, .multiLambda _ _ _ | .apply _ _, .subst _ _ | .apply _ _, .collection _ _ _
  | .lambda _ _, .bvar _ | .lambda _ _, .fvar _ | .lambda _ _, .apply _ _
  | .lambda _ _, .multiLambda _ _ _ | .lambda _ _, .subst _ _ | .lambda _ _, .collection _ _ _
  | .multiLambda _ _ _, .bvar _ | .multiLambda _ _ _, .fvar _ | .multiLambda _ _ _, .apply _ _
  | .multiLambda _ _ _, .lambda _ _ | .multiLambda _ _ _, .subst _ _
  | .multiLambda _ _ _, .collection _ _ _
  | .subst _ _, .bvar _ | .subst _ _, .fvar _ | .subst _ _, .apply _ _
  | .subst _ _, .lambda _ _ | .subst _ _, .multiLambda _ _ _ | .subst _ _, .collection _ _ _
  | .collection _ _ _, .bvar _ | .collection _ _ _, .fvar _ | .collection _ _ _, .apply _ _
  | .collection _ _ _, .lambda _ _ | .collection _ _ _, .multiLambda _ _ _
  | .collection _ _ _, .subst _ _ =>
      rw [replayAt.eq_def] at replayed
      simp at replayed
termination_by sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

theorem replayArguments_sound (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat) (initial : Assignment)
    (index : Nat) (schemas targets : List Pattern) (trace : List BagChoice)
    {final : Assignment} {remaining : List BagChoice}
    (replayed : replayArguments rule spec ambient site path depth initial index schemas targets trace =
      some (final, remaining)) :
    ∃ consumed, trace = consumed ++ remaining ∧
      TracedArguments rule spec ambient site path depth initial index schemas targets consumed final := by
  cases schemas with
  | nil =>
      cases targets with
      | nil =>
          simp only [replayArguments, Option.some.injEq, Prod.mk.injEq] at replayed
          rcases replayed with ⟨rfl, rfl⟩
          exact ⟨[], rfl, .nil⟩
      | cons => simp [replayArguments] at replayed
  | cons schema schemas =>
      cases targets with
      | nil => simp [replayArguments] at replayed
      | cons target targets =>
          simp only [replayArguments] at replayed
          obtain ⟨middle, rest, first, second⟩ := (continueReplay_eq_some_iff _ _ _ _).mp replayed
          obtain ⟨headTrace, headPrefix, headMatched⟩ :=
            replayAt_sound _ _ _ _ _ _ _ _ _ _ first
          obtain ⟨tailTrace, tailPrefix, tailMatched⟩ :=
            replayArguments_sound _ _ _ _ _ _ _ _ _ _ _ second
          refine ⟨headTrace ++ tailTrace, ?_, .cons headMatched tailMatched⟩
          simp only [headPrefix, tailPrefix, List.append_assoc]
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec

theorem replayBag_sound (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat) (initial : Assignment)
    (index : Nat) (schemas : List Pattern) (rest : Option String) (kind : CollType)
    (targets : List Pattern) (trace : List BagChoice)
    {final : Assignment} {remaining : List BagChoice}
    (replayed : replayBag rule spec ambient site path depth initial index schemas rest kind targets trace =
      some (final, remaining)) :
    ∃ consumed, trace = consumed ++ remaining ∧
      TracedBag rule spec ambient site path depth initial index schemas rest kind targets consumed final := by
  cases schemas with
  | nil =>
      cases rest with
      | none =>
          cases targets with
          | nil =>
              simp only [replayBag, Option.some.injEq, Prod.mk.injEq] at replayed
              rcases replayed with ⟨rfl, rfl⟩
              exact ⟨[], rfl, .nil⟩
          | cons => simp [replayBag] at replayed
      | some name =>
          simp only [replayBag, Option.map_eq_some_iff] at replayed
          obtain ⟨value, captured, same⟩ := replayed
          cases same
          exact ⟨[], rfl, .rest captured⟩
  | cons schema schemas =>
      cases trace with
      | nil => simp [replayBag] at replayed
      | cons choice trace =>
          rcases choice with ⟨choicePath, selected⟩
          by_cases samePath : choicePath = path ++ [index]
          · subst choicePath
            cases selectedCase : targets[selected]? with
            | none => simp [replayBag, selectedCase] at replayed
            | some target =>
                simp only [replayBag, ↓reduceIte, selectedCase] at replayed
                obtain ⟨middle, rest, first, second⟩ := (continueReplay_eq_some_iff _ _ _ _).mp replayed
                obtain ⟨within, sameTarget⟩ := List.getElem?_eq_some_iff.mp selectedCase
                subst target
                obtain ⟨headTrace, headPrefix, headMatched⟩ :=
                  replayAt_sound _ _ _ _ _ _ _ _ _ _ first
                obtain ⟨tailTrace, tailPrefix, tailMatched⟩ :=
                  replayBag_sound _ _ _ _ _ _ _ _ _ _ _ _ _ second
                refine ⟨{ path := path ++ [index], selected } :: (headTrace ++ tailTrace),
                  ?_, .cons selected within headMatched tailMatched⟩
                simp only [List.cons_append, headPrefix, tailPrefix, List.append_assoc]
          · simp [replayBag, samePath] at replayed
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec

end

/-- The very same traced source derivation replays before any suffix. -/
theorem replayAt_complete {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
    {schema target : Pattern} {trace : List BagChoice}
    (matched : TracedMatches rule spec ambient site path depth initial schema target trace final)
    (suffix : List BagChoice) :
    replayAt rule spec ambient site path depth initial schema target (trace ++ suffix) =
      some (final, suffix) := by
  revert suffix
  induction matched using TracedMatches.rec
    (motive_2 := fun path depth initial index schemas targets trace final _ =>
      ∀ suffix, replayArguments rule spec ambient site path depth initial index schemas targets
        (trace ++ suffix) = some (final, suffix))
    (motive_3 := fun path depth initial index schemas rest kind targets trace final _ =>
      ∀ suffix, replayBag rule spec ambient site path depth initial index schemas rest kind targets
        (trace ++ suffix) = some (final, suffix))
  all_goals intros
  all_goals simp_all [replayAt, replayArguments, replayBag, continueReplay, List.append_assoc]
  rw [replayAt.eq_def]
  simp_all

/-- Replay at the exact source site and binder context of the request. -/
def replayWithRest (request : Request) (trace : List BagChoice) :
    Option (Assignment × List BagChoice) :=
  replayAt request.rule request.spec request.ambient request.site request.path request.depth
    request.initial request.schema request.target trace

/-- A whole match must consume all supplied bag selections. -/
def replay (request : Request) (trace : List BagChoice) : Option Assignment := do
  let (final, remaining) ← replayWithRest request trace
  if remaining.isEmpty then some final else none

/-- Compare the actual replayed assignment with the literal claimed result. -/
def check (request : Request) (trace : List BagChoice) (final : Assignment) : Bool :=
  decide (replay request trace = some final)

theorem replay_eq_some_iff (request : Request) (trace : List BagChoice) (final : Assignment) :
    replay request trace = some final ↔ replayWithRest request trace = some (final, []) := by
  cases result : replayWithRest request trace with
  | none => simp [replay, result]
  | some pair =>
      rcases pair with ⟨actual, remaining⟩
      cases remaining with
      | nil => simp [replay, result]
      | cons => simp [replay, result]

/-- Whole-trace replay is exact for the original source judgment, including
the exact order and multiplicity of supplied residual choices. -/
theorem replay_exact (request : Request) (trace : List BagChoice) (final : Assignment) :
    replay request trace = some final ↔
      TracedMatches request.rule request.spec request.ambient request.site request.path
        request.depth request.initial request.schema request.target trace final := by
  rw [replay_eq_some_iff]
  constructor
  · intro accepted
    obtain ⟨consumed, consumedEq, matched⟩ := replayAt_sound _ _ _ _ _ _ _ _ _ _ accepted
    simp only [List.append_nil] at consumedEq
    cases consumedEq
    exact matched
  · intro matched
    exact (List.append_nil trace) ▸ replayAt_complete matched []

@[simp] theorem check_exact (request : Request) (trace : List BagChoice) (final : Assignment) :
    check request trace final = true ↔
      TracedMatches request.rule request.spec request.ambient request.site request.path
        request.depth request.initial request.schema request.target trace final := by
  simp only [check, decide_eq_true_eq, replay_exact]

/-- The prefix interface constructs original source evidence for every
consumed choice while retaining the exact unconsumed suffix. -/
theorem replayWithRest_sound (request : Request) (trace : List BagChoice)
    {final : Assignment} {remaining : List BagChoice}
    (accepted : replayWithRest request trace = some (final, remaining)) :
    ∃ consumed, trace = consumed ++ remaining ∧
      TracedMatches request.rule request.spec request.ambient request.site request.path
        request.depth request.initial request.schema request.target consumed final :=
  replayAt_sound _ _ _ _ _ _ _ _ _ _ accepted

/-- The same source evidence remains replayable before every continuation. -/
theorem replayWithRest_complete (request : Request) (trace : List BagChoice) (final : Assignment)
    (matched : TracedMatches request.rule request.spec request.ambient request.site request.path
      request.depth request.initial request.schema request.target trace final)
    (suffix : List BagChoice) :
    replayWithRest request (trace ++ suffix) = some (final, suffix) :=
  replayAt_complete matched suffix

theorem replayWithRest_exact (request : Request) (trace : List BagChoice)
    (final : Assignment) (remaining : List BagChoice) :
    replayWithRest request trace = some (final, remaining) ↔
      ∃ consumed, trace = consumed ++ remaining ∧
        TracedMatches request.rule request.spec request.ambient request.site request.path
          request.depth request.initial request.schema request.target consumed final := by
  constructor
  · exact replayWithRest_sound request trace
  · rintro ⟨consumed, rfl, matched⟩
    exact replayWithRest_complete request consumed final matched remaining

/-- Erasing supplied guidance recovers precisely the original scoped matches;
every such finite derivation has guidance accepted by direct replay. -/
theorem matches_iff_exists_guidance (request : Request) (final : Assignment) :
    GeneralScopedMatch.Matches request.rule request.spec request.ambient request.site request.path
      request.depth request.initial request.schema request.target final ↔
      ∃ trace, check request trace final = true := by
  rw [← traced_iff_matches]
  simp only [check_exact]

theorem check_answer_exact (request : Request) (answer : Answer) :
    check request answer.trace answer.assignment = true ↔ answer.Valid request :=
  check_exact request answer.trace answer.assignment

end Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchReplay
