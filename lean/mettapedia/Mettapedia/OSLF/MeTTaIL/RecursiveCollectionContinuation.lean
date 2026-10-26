import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionHandoff
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledFrontier
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledFootprint
import Mettapedia.OSLF.MeTTaIL.Complete.DeepRoot

/-!
# Retained continuations for prepared recursive collection matches

One allocation starts one existing scheduled post-match continuation. The
request retains the recursive allocation receipt and its ordinary source
witness. Resumption advances that continuation, without matching again.
Coverage preserves the completed assignment, premise history and target;
the ordinary trace is validation evidence, not another allocation occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.RecursiveCollectionContinuation

open Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted
open RecursiveCollectionHandoff
open StructuralDescent.Scheduled

structure Request where
  environment : Environment
  depth : Nat
  bound : List TypeExpr
  type : TypeExpr
  source : Pattern
  index : Nat
  rule : RewriteRule
  spec : RuleBindingSpec
  answer : RecursiveCollectionMachine.Answer
  prepared : Prepared
  declared : environment.language.rewrites[index]? = some rule
  specified : specification? environment index = some spec
  admitted : admittedFor rule spec = true
  sorted : OpenPatternWellSorted environment.language environment.free bound type source
  matching : prepared.Valid
    ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩ answer

abbrev Request.goal (request : Request) : Goal :=
  .root (request.depth + 1) request.bound request.type request.prepared.source request.index

def Request.context (request : Request) : Context :=
  ⟨request.index, request.rule, request.spec, request.bound, 0, 0⟩

theorem Request.sourceTyped (request : Request) :
    OpenPatternWellSorted request.environment.language request.environment.free
      request.bound request.type request.prepared.source :=
  request.matching.typed request.environment request.sorted

def Request.answers (request : Request) :
    List {answer : GeneralScopedMatchMachine.Answer // answer.Valid
      ⟨request.rule, request.spec, request.bound.length, .left, [], 0, [],
        request.rule.left, request.prepared.source⟩} :=
  [⟨request.prepared.ordinary, request.matching.matching⟩]

def Request.expansion (request : Request) :
    Scheduler.Expansion (Task request.environment request.goal)
      (Result request.environment request.goal) Obligation :=
  continueRootAnswer request.environment request.goal request.depth request.bound request.type
    request.prepared.source request.index request.rule request.spec request.declared request.specified
    request.admitted request.sourceTyped request.prepared.ordinary request.matching.matching
    (.done request.goal) []

abbrev State (request : Request) := StructuralDescent.Scheduled.State request.environment request.goal

def start (request : Request) : State request :=
  { agenda := request.expansion.tasks, answers := request.expansion.answers,
    unresolved := request.expansion.unresolved, work := 0 }

def run (request : Request) (work : Nat) (state : State request) : State request :=
  StructuralDescent.Scheduled.run request.environment request.goal work state

def read? (request : Request) (result : Result request.environment request.goal) :
    Option Complete.DeepRoot.Firing :=
  let firing := Complete.DeepRoot.read
    (request := ⟨request.environment, request.bound, request.type, request.prepared.source, request.index⟩) result
  if firing.captured == request.prepared.ordinary.assignment then some firing else none

def publication (request : Request) (state : State request) : List Complete.DeepRoot.Firing :=
  state.answers.filterMap (read? request)

theorem start_no_early_answers (request : Request) : (start request).answers = [] :=
  continueRootAnswer_answers ..

theorem run_add (request : Request) (first extra : Nat) (state : State request) :
    run request (first + extra) state = run request extra (run request first state) :=
  StructuralDescent.Scheduled.run_add ..

theorem publication_prefix (request : Request) (state : State request) (work : Nat) :
    publication request state <+: publication request (run request work state) := by
  obtain ⟨suffix, grown⟩ := StructuralDescent.Scheduled.receipts_prefix
    request.environment request.goal work state
  refine ⟨suffix.filterMap (read? request), ?_⟩
  change state.answers.filterMap (read? request) ++ suffix.filterMap (read? request) =
    (StructuralDescent.Scheduled.run request.environment request.goal work state).answers.filterMap (read? request)
  rw [grown, List.filterMap_append]

/-- Each allocation drains its own new suffix before publications from
different allocations are interleaved. -/
def fresh (request : Request) (state : State request) : List Complete.DeepRoot.Firing :=
  (publication request (run request 1 state)).drop (publication request state).length

theorem fresh_balance (request : Request) (state : State request) :
    publication request state ++ fresh request state = publication request (run request 1 state) := by
  have grown := publication_prefix request state 1
  unfold fresh
  calc
    _ = (publication request (run request 1 state)).take (publication request state).length ++
        (publication request (run request 1 state)).drop (publication request state).length :=
      congrArg (fun front => front ++
        (publication request (run request 1 state)).drop (publication request state).length)
        (List.prefix_iff_eq_take.mp grown)
    _ = _ := List.take_append_drop _ _

theorem source_free_within (request : Request) (footprint : List String)
    (inside : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint) :
    ∀ name ∈ request.prepared.source.freeFvarNames, name ∈ footprint := by
  intro name member
  apply inside name
  apply (CanonicalBags.canon_freeFvarNames request.source name).mp
  rw [request.matching.source]
  exact (CanonicalBags.canon_freeFvarNames request.prepared.source name).mpr member

theorem captures_free_within (request : Request) (footprint : List String)
    (inside : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint) :
    assignmentFreeWithin footprint request.prepared.ordinary.assignment :=
  GeneralScopedMatch.matched_free_within request.matching.matching.matching footprint
    (by intro entry member; cases member) (source_free_within request footprint inside)

/-- The source's finite free-name table suffices for the actual prepared
continuation. No completed premise result is assumed. -/
theorem start_free_within (request : Request) (footprint : List String)
    (inside : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint) :
    stateFreeWithin footprint request.environment request.goal (start request) := by
  have sourceWithin := source_free_within request footprint inside
  have captures := captures_free_within request footprint inside
  constructor
  · intro task member
    simp only [start, Request.expansion, continueRootAnswer] at member
    split at member
    · have selected := List.mem_singleton.mp member
      subst task
      exact ⟨⟨request.admitted, captures⟩, sourceWithin, captures, sourceWithin⟩
    · cases member
  · intro result member
    rw [start_no_early_answers] at member
    cases member

theorem publication_sound (request : Request) (state : State request)
    {firing : Complete.DeepRoot.Firing} (member : firing ∈ publication request state) :
    firing.Valid ⟨request.environment, request.bound, request.type, request.prepared.source, request.index⟩ ∧
      firing.captured = request.answer.assignment := by
  obtain ⟨result, _, read⟩ := List.mem_filterMap.mp member
  have valid := Complete.DeepRoot.read_valid
    (request := ⟨request.environment, request.bound, request.type, request.prepared.source, request.index⟩) result
  unfold read? at read
  dsimp only at read
  split at read
  · rename_i same
    cases read
    exact ⟨valid, (beq_iff_eq.mp same).trans request.matching.assignment⟩
  · cases read

theorem publication_premises (request : Request) (state : State request)
    {firing : Complete.DeepRoot.Firing} (member : firing ∈ publication request state) :
    PremisesHold request.environment request.context request.rule.premises
      request.prepared.ordinary.assignment firing.completed firing.history := by
  obtain ⟨valid, captured⟩ := publication_sound request state member
  have sameCapture := captured.trans request.matching.assignment.symm
  cases valid with
  | @fire bound type source target index rule spec trace captured completed events
      declared specified admitted sorted matched capturedTyped premises reduced targetTyped =>
    have ruleSame : rule = request.rule := Option.some.inj (declared.symm.trans request.declared)
    have specSame : spec = request.spec := Option.some.inj (specified.symm.trans request.specified)
    cases ruleSame
    cases specSame
    simpa only [Request.context, sameCapture] using premises

theorem eventually_settled (request : Request) :
    ∃ work, (run request work (start request)).agenda = [] :=
  continueRootAnswers_eventually_settled request.environment request.goal request.depth request.bound
    request.type request.prepared.source request.index request.rule request.spec request.declared
    request.specified request.admitted request.sourceTyped (.done request.goal)
    (doneTrees request.environment request.goal) request.answers

/-- The source firing may use another ordinary validation trace. The actual
prepared allocation starts exactly one continuation with the supplied
captures; it retains every completed premise history and target. -/
theorem source_coverage (request : Request)
    (trace : List GeneralScopedMatchMachine.BagChoice) (completed : Assignment)
    (history : List Event) (target : Pattern)
    (held : RootFiring request.environment request.bound request.type request.prepared.source
      request.index trace request.prepared.ordinary.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ request.depth) :
    ∃ work, (⟨request.prepared.ordinary.trace, request.prepared.ordinary.assignment,
      completed, history, target⟩ : Complete.DeepRoot.Firing) ∈
      publication request (run request work (start request)) := by
  cases held with
  | @fire bound type source endpoint index rule spec oldTrace captured final events
      declared specified admitted sorted matched capturedTyped premises reduced targetTyped =>
    have ruleSame : rule = request.rule := Option.some.inj (declared.symm.trans request.declared)
    have specSame : spec = request.spec := Option.some.inj (specified.symm.trans request.specified)
    cases ruleSame
    cases specSame
    let wanted : Result request.environment request.goal :=
      .root request.prepared.ordinary.trace request.prepared.ordinary.assignment completed history target
        (.fire request.declared request.specified request.admitted request.sourceTyped
          request.matching.matching capturedTyped premises reduced targetTyped)
    have meaning : EvaluatesTo
        (.rootBody request.depth request.bound request.type request.prepared.source request.index
          request.rule request.spec request.declared request.specified request.admitted request.sourceTyped
          request.prepared.ordinary.trace request.prepared.ordinary.assignment request.matching.matching
          capturedTyped (.done request.goal)) wanted := by
      refine ⟨.premises completed history premises, ?_, ?_⟩
      · simpa only [Interpreted.Result.ordered, decide_eq_true_eq] using bounded
      · exact ⟨target, reduced, targetTyped, rfl⟩
    have accepts := continueRootAnswers_covers request.environment request.goal request.depth request.bound
      request.type request.prepared.source request.index request.rule request.spec request.declared
      request.specified request.admitted request.sourceTyped (.done request.goal)
      request.answers ⟨request.prepared.ordinary, request.matching.matching⟩
      List.mem_cons_self capturedTyped wanted meaning
    obtain ⟨work, drained⟩ := eventually_settled request
    have published := continueRootAnswers_drained_contains request.environment request.goal request.depth
      request.bound request.type request.prepared.source request.index request.rule request.spec request.declared
      request.specified request.admitted request.sourceTyped (.done request.goal)
      request.answers work wanted accepts drained
    refine ⟨work, List.mem_filterMap.mpr ⟨wanted, published, ?_⟩⟩
    simp [read?, wanted, Complete.DeepRoot.read]


/-- Common captured-filtered readout for the selected matching execution. -/
def readIn? (matcher : MatchingExecution) (request : Request)
    (result : StructuralDescent.Scheduled.Interpreted.Result matcher request.environment request.goal) :
    Option (Complete.DeepRoot.Firing matcher.Choice) :=
  let firing := Complete.DeepRoot.readIn (request :=
    ⟨request.environment, request.bound, request.type, request.prepared.source, request.index⟩) matcher result
  if firing.captured == request.prepared.ordinary.assignment then some firing else none

def publicationIn (matcher : MatchingExecution) (request : Request)
    (state : StructuralDescent.Scheduled.State request.environment request.goal matcher) :
    List (Complete.DeepRoot.Firing matcher.Choice) := state.answers.filterMap (readIn? matcher request)

theorem readIn_ordinary (request : Request) (result : Result request.environment request.goal) :
    readIn? MatchingExecution.ordinary request result = read? request result := by
  cases result
  rfl

theorem publicationIn_ordinary (request : Request) (state : State request) :
    publicationIn MatchingExecution.ordinary request state = publication request state := by
  simp only [publicationIn, publication, readIn_ordinary]

theorem publicationIn_prefix (matcher : MatchingExecution) (request : Request)
    (state : StructuralDescent.Scheduled.State request.environment request.goal matcher) (work : Nat) :
    publicationIn matcher request state <+: publicationIn matcher request
      (StructuralDescent.Scheduled.run request.environment request.goal work state) := by
  obtain ⟨suffix, grown⟩ := StructuralDescent.Scheduled.receipts_prefix
    request.environment request.goal work state
  refine ⟨suffix.filterMap (readIn? matcher request), ?_⟩
  change state.answers.filterMap (readIn? matcher request) ++ suffix.filterMap (readIn? matcher request) =
    (StructuralDescent.Scheduled.run request.environment request.goal work state).answers.filterMap
      (readIn? matcher request)
  rw [grown, List.filterMap_append]

namespace Canonical

private theorem canonical_of_map_member {pattern : Pattern} {items : List Pattern}
    (member : pattern ∈ items.map CanonicalBags.canon) : CanonicalBags.canon pattern = pattern := by
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  exact CanonicalBags.canon_idempotent original

/-- A focused subterm of a canonical filled context is canonical, including
inside bags and sets where sorting and idempotence change physical positions. -/
theorem focus_canonical (context : DerivedContexts.OneHoleContext) (focus : Pattern) :
    CanonicalBags.canon (context.fill focus) = context.fill focus →
      CanonicalBags.canon focus = focus := by
  induction context generalizing focus with
  | hole => intro fixed; exact fixed
  | apply label before inner after ih =>
    intro fixed
    simp only [DerivedContexts.OneHoleContext.fill, CanonicalBags.canon] at fixed
    change Pattern.apply label ((before ++ inner.fill focus :: after).map CanonicalBags.canon) =
      Pattern.apply label (before ++ inner.fill focus :: after) at fixed
    apply ih focus
    apply canonical_of_map_member
    rw [(Pattern.apply.inj fixed).2]
    simp
  | lambda display inner ih =>
    intro fixed
    simp only [DerivedContexts.OneHoleContext.fill, CanonicalBags.canon] at fixed
    change Pattern.lambda display (CanonicalBags.canon (inner.fill focus)) =
      Pattern.lambda display (inner.fill focus) at fixed
    exact ih focus (Pattern.lambda.inj fixed).2
  | multiLambda arity displays inner ih =>
    intro fixed
    simp only [DerivedContexts.OneHoleContext.fill, CanonicalBags.canon] at fixed
    change Pattern.multiLambda arity displays (CanonicalBags.canon (inner.fill focus)) =
      Pattern.multiLambda arity displays (inner.fill focus) at fixed
    exact ih focus (Pattern.multiLambda.inj fixed).2.2
  | substBody inner replacement ih =>
    intro fixed
    simp only [DerivedContexts.OneHoleContext.fill, CanonicalBags.canon] at fixed
    change Pattern.subst (CanonicalBags.canon (inner.fill focus)) (CanonicalBags.canon replacement) =
      Pattern.subst (inner.fill focus) replacement at fixed
    exact ih focus (Pattern.subst.inj fixed).1
  | substReplacement body inner ih =>
    intro fixed
    simp only [DerivedContexts.OneHoleContext.fill, CanonicalBags.canon] at fixed
    change Pattern.subst (CanonicalBags.canon body) (CanonicalBags.canon (inner.fill focus)) =
      Pattern.subst body (inner.fill focus) at fixed
    exact ih focus (Pattern.subst.inj fixed).2
  | collection kind before inner after rest ih =>
    intro fixed
    simp only [DerivedContexts.OneHoleContext.fill, CanonicalBags.canon] at fixed
    change Pattern.collection kind (CanonicalBags.arrange kind
      ((before ++ inner.fill focus :: after).map CanonicalBags.canon)) rest =
      Pattern.collection kind (before ++ inner.fill focus :: after) rest at fixed
    apply ih focus
    apply canonical_of_map_member
    apply (CanonicalBags.arrange_mem _).mp
    rw [(Pattern.collection.inj fixed).2.1]
    simp

/-- The original allocation trace enters the canonical interpretation at the
prepared presentation. It is neither rerun nor replaced by an ordinary trace. -/
theorem prepared_seed {request : RecursiveCollectionMachine.Request}
    {answer : RecursiveCollectionMachine.Answer} {prepared : Prepared}
    (matching : prepared.Valid request answer)
    (canonical : CanonicalBags.canon request.target = request.target) :
    canonicalMatchingInterpretation.Matches {request with target := prepared.source}
      answer.trace answer.assignment := by
  apply canonical_matches_same_target matching.source
  change (matchingInterpretation literalBodyComparison).Matches
    (canonicalRequest request) answer.trace answer.assignment
  have unchanged : canonicalRequest request = request := by
    simp only [canonicalRequest, canonical]
  rw [unchanged]
  exact matching.allocation

/-- The prepared request enters the shared post-match continuation with the
same recursive allocation answer and the selected canonical premise machine. -/
def expansion (request : Request)
    (seed : canonicalMatchingInterpretation.Matches
      ⟨request.rule, request.spec, request.bound.length, .left, [], 0, [],
        request.rule.left, request.prepared.source⟩ request.answer.trace request.answer.assignment) :
    Scheduler.Expansion
      (StructuralDescent.Scheduled.Interpreted.Task canonicalMatchingExecution request.environment request.goal)
      (StructuralDescent.Scheduled.Interpreted.Result canonicalMatchingExecution request.environment request.goal)
      Obligation :=
  continueRootAnswer (matcher := canonicalMatchingExecution) request.environment request.goal
    request.depth request.bound request.type request.prepared.source request.index request.rule request.spec
    request.declared request.specified request.admitted request.sourceTyped request.answer seed
    (.done request.goal) []

theorem expansion_no_early_answers (request : Request)
    (seed : canonicalMatchingInterpretation.Matches
      ⟨request.rule, request.spec, request.bound.length, .left, [], 0, [],
        request.rule.left, request.prepared.source⟩ request.answer.trace request.answer.assignment) :
    (expansion request seed).answers = [] :=
  continueRootAnswer_answers (matcher := canonicalMatchingExecution) request.environment request.goal
    request.depth request.bound request.type request.prepared.source request.index request.rule request.spec
    request.declared request.specified request.admitted request.sourceTyped request.answer seed
    (.done request.goal) []

theorem expansion_no_early_obligations (request : Request)
    (seed : canonicalMatchingInterpretation.Matches
      ⟨request.rule, request.spec, request.bound.length, .left, [], 0, [],
        request.rule.left, request.prepared.source⟩ request.answer.trace request.answer.assignment) :
    (expansion request seed).unresolved = [] :=
  continueRootAnswer_unresolved (matcher := canonicalMatchingExecution) request.environment request.goal
    request.depth request.bound request.type request.prepared.source request.index request.rule request.spec
    request.declared request.specified request.admitted request.sourceTyped request.answer seed
    (.done request.goal) []

/-- The seed fixes the original allocation trace and captured assignment. -/
abbrev Seed (request : Request) : Prop :=
  canonicalMatchingInterpretation.Matches
    ⟨request.rule, request.spec, request.bound.length, .left, [], 0, [],
      request.rule.left, request.prepared.source⟩ request.answer.trace request.answer.assignment

abbrev State (request : Request) :=
  StructuralDescent.Scheduled.State request.environment request.goal canonicalMatchingExecution

abbrev Firing := Complete.DeepRoot.Firing canonicalMatchingExecution.Choice

/-- The selected shared scheduler starts after matching, with the retained seed. -/
def start (request : Request) (seed : Seed request) : State request :=
  { agenda := (expansion request seed).tasks, answers := (expansion request seed).answers,
    unresolved := (expansion request seed).unresolved, work := 0 }

def run (request : Request) (work : Nat) (state : State request) : State request :=
  StructuralDescent.Scheduled.run request.environment request.goal work state

/-- Read all matching choices and nested premise histories without changing their carrier. -/
def read? (request : Request)
    (result : StructuralDescent.Scheduled.Interpreted.Result canonicalMatchingExecution
      request.environment request.goal) : Option Firing :=
  let firing := Complete.DeepRoot.readIn (request :=
    ⟨request.environment, request.bound, request.type, request.prepared.source, request.index⟩)
    canonicalMatchingExecution result
  if firing.captured == request.answer.assignment then some firing else none

def publication (request : Request) (state : State request) : List Firing :=
  state.answers.filterMap (read? request)

theorem publicationIn_canonical (request : Request) (state : State request) :
    publicationIn canonicalMatchingExecution request state = publication request state := by
  unfold publicationIn publication readIn? read?
  rw [request.matching.assignment]

theorem start_no_early_answers (request : Request) (seed : Seed request) :
    (start request seed).answers = [] := expansion_no_early_answers request seed

theorem run_add (request : Request) (first extra : Nat) (state : State request) :
    run request (first + extra) state = run request extra (run request first state) :=
  StructuralDescent.Scheduled.run_add ..

theorem publication_prefix (request : Request) (state : State request) (work : Nat) :
    publication request state <+: publication request (run request work state) := by
  obtain ⟨suffix, grown⟩ := StructuralDescent.Scheduled.receipts_prefix
    request.environment request.goal work state
  refine ⟨suffix.filterMap (read? request), ?_⟩
  change state.answers.filterMap (read? request) ++ suffix.filterMap (read? request) =
    (StructuralDescent.Scheduled.run request.environment request.goal work state).answers.filterMap
      (read? request)
  rw [grown, List.filterMap_append]

/-- Publications are delivered only in their new chronological suffix. -/
def fresh (request : Request) (state : State request) : List Firing :=
  (publication request (run request 1 state)).drop (publication request state).length

theorem fresh_balance (request : Request) (state : State request) :
    publication request state ++ fresh request state = publication request (run request 1 state) := by
  have grown := publication_prefix request state 1
  unfold fresh
  calc
    _ = (publication request (run request 1 state)).take (publication request state).length ++
        (publication request (run request 1 state)).drop (publication request state).length :=
      congrArg (fun front => front ++
        (publication request (run request 1 state)).drop (publication request state).length)
        (List.prefix_iff_eq_take.mp grown)
    _ = _ := List.take_append_drop _ _

theorem publication_sound (request : Request) (state : State request)
    {firing : Firing} (member : firing ∈ publication request state) :
    firing.ValidIn canonicalMatchingInterpretation
      ⟨request.environment, request.bound, request.type, request.prepared.source, request.index⟩ ∧
      firing.captured = request.answer.assignment := by
  obtain ⟨result, _, read⟩ := List.mem_filterMap.mp member
  have valid := Complete.DeepRoot.readIn_valid
    (request := ⟨request.environment, request.bound, request.type, request.prepared.source, request.index⟩)
    canonicalMatchingExecution result
  unfold read? at read
  dsimp only at read
  split at read
  · rename_i same
    cases read
    exact ⟨valid, beq_iff_eq.mp same⟩
  · cases read

theorem publication_premises (request : Request) (state : State request)
    {firing : Firing} (member : firing ∈ publication request state) :
    GeneralPremise.Interpreted.PremisesHold canonicalMatchingInterpretation
      request.environment request.context request.rule.premises
      request.answer.assignment firing.completed firing.history := by
  obtain ⟨valid, capturesSame⟩ := publication_sound request state member
  cases valid with
  | @fire bound type source target index rule spec trace captured completed events
      declared specified admitted sorted matched capturedTyped premises reduced targetTyped =>
    have ruleSame : rule = request.rule := Option.some.inj (declared.symm.trans request.declared)
    have specSame : spec = request.spec := Option.some.inj (specified.symm.trans request.specified)
    cases ruleSame
    cases specSame
    simpa only [Request.context, capturesSame] using premises

/-- Equivalent prepared and authored sources have the same interpretation-indexed firing.
This is not a theorem about the ordinary reference relation. -/
theorem publication_original_source (request : Request) (state : State request)
    {firing : Firing} (member : firing ∈ publication request state) :
    firing.ValidIn canonicalMatchingInterpretation
      ⟨request.environment, request.bound, request.type, request.source, request.index⟩ :=
  canonical_firing_same_source request.matching.source.symm
    (publication_sound request state member).1

/-- The existing finite work tree is built for the one retained post-match task. -/
def startForest (request : Request) (seed : Seed request) :
    Scheduler.TaskForest (StructuralDescent.Scheduled.expand request.environment request.goal)
      (start request seed).agenda := by
  unfold start expansion continueRootAnswer
  dsimp only
  split
  · apply Scheduler.TaskForest.cons ?_ .nil
    apply treeEvaluate canonicalCursorCost
    intro result
    cases result with
    | premises completed events held =>
      apply Scheduler.TaskTree.branch
      simp only [StructuralDescent.Scheduled.expand, delivered]
      split
      · exact .nil
      · split
        · exact .cons ((doneTrees request.environment request.goal) _) .nil
        · exact .nil
  · exact .nil

/-- This finite finisher drains the retained depth-bounded continuation.
Its unresolved obligations remain in the returned state. -/
def finish (request : Request) (seed : Seed request) : State request :=
  run request (startForest request seed).cost (start request seed)

theorem finish_settled (request : Request) (seed : Seed request) :
    (finish request seed).agenda = [] :=
  Scheduler.finiteWork_drains (StructuralDescent.Scheduled.expand request.environment request.goal)
    (startForest request seed).cost _ (startForest request seed) (Nat.le_refl _)

theorem eventually_settled (request : Request) (seed : Seed request) :
    ∃ work, (run request work (start request seed)).agenda = [] :=
  ⟨(startForest request seed).cost, finish_settled request seed⟩

/-- The original seed trace is retained while every bounded premise history and
reduct of the selected interpretation is published by the finite finisher. -/
theorem finish_source_coverage (request : Request) (seed : Seed request)
    (trace : List EquationalScopedReceipts.Event) (completed : Assignment)
    (history : List (Event EquationalScopedReceipts.Event)) (target : Pattern)
    (held : GeneralPremise.Interpreted.RootFiring canonicalMatchingInterpretation
      request.environment request.bound request.type request.prepared.source request.index
      trace request.answer.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ request.depth) :
    (⟨request.answer.trace, request.answer.assignment, completed, history, target⟩ : Firing) ∈
      publication request (finish request seed) := by
  cases held with
  | @fire bound type source endpoint index rule spec oldTrace captured final events
      declared specified admitted sorted matched capturedTyped premises reduced targetTyped =>
    have ruleSame : rule = request.rule := Option.some.inj (declared.symm.trans request.declared)
    have specSame : spec = request.spec := Option.some.inj (specified.symm.trans request.specified)
    cases ruleSame
    cases specSame
    let wanted : StructuralDescent.Scheduled.Interpreted.Result canonicalMatchingExecution
        request.environment request.goal :=
      .root request.answer.trace request.answer.assignment completed history target
        (.fire request.declared request.specified request.admitted request.sourceTyped
          seed capturedTyped premises reduced targetTyped)
    have meaning : EvaluatesTo
        (StructuralDescent.Scheduled.Interpreted.Continuation.rootBody
          (matcher := canonicalMatchingExecution) request.depth request.bound request.type
          request.prepared.source request.index request.rule request.spec request.declared
          request.specified request.admitted request.sourceTyped request.answer.trace request.answer.assignment
          seed capturedTyped (.done request.goal)) wanted := by
      refine ⟨.premises completed history premises, ?_, ?_⟩
      · change decide (StructuralDescent.eventsDepth history ≤ request.depth) = true
        exact decide_eq_true bounded
      · exact ⟨target, reduced, targetTyped, rfl⟩
    have initial : StateAccepts canonicalCursorLaws (start request seed) wanted := by
      unfold start expansion continueRootAnswer
      dsimp only
      split
      · exact .inr ⟨_, List.mem_cons_self, meaning⟩
      · rename_i failed
        exact False.elim (failed (checkTypedAssignment_complete capturedTyped))
    have retained := StructuralDescent.Scheduled.run_covers canonicalCursorLaws
      canonical_answer_representation (startForest request seed).cost initial
    have present : wanted ∈ (finish request seed).answers := by
      rcases retained with present | ⟨task, present, _⟩
      · exact present
      · change task ∈ (finish request seed).agenda at present
        rw [finish_settled request seed] at present
        exact False.elim (List.not_mem_nil present)
    apply List.mem_filterMap.mpr
    refine ⟨wanted, present, ?_⟩
    change (if request.answer.assignment == request.answer.assignment then
      some (⟨request.answer.trace, request.answer.assignment, completed, history, target⟩ : Firing)
      else none) = some _
    simp

theorem source_coverage (request : Request) (seed : Seed request)
    (trace : List EquationalScopedReceipts.Event) (completed : Assignment)
    (history : List (Event EquationalScopedReceipts.Event)) (target : Pattern)
    (held : GeneralPremise.Interpreted.RootFiring canonicalMatchingInterpretation
      request.environment request.bound request.type request.prepared.source request.index
      trace request.answer.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ request.depth) :
    ∃ work, (⟨request.answer.trace, request.answer.assignment, completed, history, target⟩ : Firing) ∈
      publication request (run request work (start request seed)) :=
  ⟨(startForest request seed).cost,
    finish_source_coverage request seed trace completed history target held bounded⟩

#print axioms start_no_early_answers
#print axioms run_add
#print axioms publication_prefix
#print axioms fresh_balance
#print axioms publication_sound
#print axioms publication_premises
#print axioms publication_original_source
#print axioms finish_settled
#print axioms eventually_settled
#print axioms finish_source_coverage
#print axioms source_coverage

#print axioms focus_canonical
#print axioms prepared_seed
#print axioms expansion_no_early_answers
#print axioms expansion_no_early_obligations

end Canonical

/-- A retained root seed contains the actual selected match and its captures.
It supplies no completed premise result or precomputed scheduled state. -/
structure RootSeed (matcher : MatchingExecution) (request : Request) where
  answer : matcher.Answer
  valid : matcher.meaning.Matches
    ⟨request.rule, request.spec, request.bound.length, .left, [], 0, [],
      request.rule.left, request.prepared.source⟩ (matcher.trace answer) (matcher.assignment answer)
  captured : matcher.assignment answer = request.prepared.ordinary.assignment

def expansionWithSeed (matcher : MatchingExecution) (request : Request)
    (seed : RootSeed matcher request) :
    Scheduler.Expansion
      (StructuralDescent.Scheduled.Interpreted.Task matcher request.environment request.goal)
      (StructuralDescent.Scheduled.Interpreted.Result matcher request.environment request.goal)
      Obligation :=
  continueRootAnswer (matcher := matcher) request.environment request.goal request.depth request.bound
    request.type request.prepared.source request.index request.rule request.spec request.declared
    request.specified request.admitted request.sourceTyped seed.answer seed.valid (.done request.goal) []

/-- The existing scheduler begins immediately after the retained root match. -/
def startWithSeed (matcher : MatchingExecution) (request : Request)
    (seed : RootSeed matcher request) :
    StructuralDescent.Scheduled.State request.environment request.goal matcher :=
  { agenda := (expansionWithSeed matcher request seed).tasks,
    answers := (expansionWithSeed matcher request seed).answers,
    unresolved := (expansionWithSeed matcher request seed).unresolved, work := 0 }

theorem startWithSeed_no_early_answers (matcher : MatchingExecution) (request : Request)
    (seed : RootSeed matcher request) : (startWithSeed matcher request seed).answers = [] :=
  continueRootAnswer_answers ..

theorem startWithSeed_no_early_obligations (matcher : MatchingExecution) (request : Request)
    (seed : RootSeed matcher request) : (startWithSeed matcher request seed).unresolved = [] :=
  continueRootAnswer_unresolved ..

def ordinarySeed (request : Request) : RootSeed MatchingExecution.ordinary request :=
  ⟨request.prepared.ordinary, request.matching.matching, rfl⟩

/-- This seed retains literally the original allocation answer and trace. -/
def canonicalSeed (request : Request) (seed : Canonical.Seed request) :
    RootSeed canonicalMatchingExecution request :=
  ⟨request.answer, seed, request.matching.assignment.symm⟩

theorem startWithSeed_ordinary (request : Request) :
    startWithSeed MatchingExecution.ordinary request (ordinarySeed request) = start request := rfl

theorem startWithSeed_canonical (request : Request) (seed : Canonical.Seed request) :
    startWithSeed canonicalMatchingExecution request (canonicalSeed request seed) =
      Canonical.start request seed := rfl

theorem ordinarySeed_trace (request : Request) :
    MatchingExecution.ordinary.trace (ordinarySeed request).answer =
      request.prepared.ordinary.trace := rfl

theorem canonicalSeed_answer (request : Request) (seed : Canonical.Seed request) :
    (canonicalSeed request seed).answer = request.answer := rfl

#print axioms startWithSeed_no_early_answers
#print axioms startWithSeed_no_early_obligations
#print axioms startWithSeed_ordinary
#print axioms startWithSeed_canonical
#print axioms canonicalSeed_answer

end Mettapedia.OSLF.MeTTaIL.RecursiveCollectionContinuation


namespace Mettapedia.OSLF.MeTTaIL.RecursiveCollectionContinuation
open Syntax GeneralPremise StructuralDescent.Scheduled
open CanonicalCompare CanonicalCompare.AllNameSupport

theorem captures_names_covered (request : Request) (table footprint : List String)
    (declarations : ∀ rule ∈ request.environment.language.terms, rule.label ∈ table)
    (included : ∀ name ∈ footprint, name ∈ table)
    (inside : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint) :
    AssignmentCovered table request.prepared.ordinary.assignment := by
  have sourceCovered := TypedObjectAlphabet.wellSorted_covered request.sourceTyped declarations
    (fun name member => included name (source_free_within request footprint inside name member))
  exact matched_covered (by intro entry member; cases member) sourceCovered request.matching.matching.matching

/-- Every retained root seed starts in the existing scheduler with the original captures. -/
theorem startWithSeed_free_within (matcher : MatchingExecution) (request : Request)
    (seed : RootSeed matcher request) (footprint : List String)
    (inside : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint) :
    stateFreeWithin footprint request.environment request.goal (startWithSeed matcher request seed) := by
  have sourceWithin := source_free_within request footprint inside
  have captures := captures_free_within request footprint inside
  rw [← seed.captured] at captures
  constructor
  · intro task member
    simp only [startWithSeed, expansionWithSeed, continueRootAnswer] at member
    split at member
    · have selected := List.mem_singleton.mp member
      subst task
      exact ⟨⟨request.admitted, captures⟩, sourceWithin, captures, sourceWithin⟩
    · cases member
  · intro result member
    rw [startWithSeed_no_early_answers] at member
    cases member

/-- Coverage follows from the typed original match and declared source alphabet. -/
theorem startWithSeed_names_covered (matcher : MatchingExecution) (request : Request)
    (seed : RootSeed matcher request) (table footprint : List String)
    (declarations : ∀ rule ∈ request.environment.language.terms, rule.label ∈ table)
    (included : ∀ name ∈ footprint, name ∈ table)
    (templates : ∀ rule ∈ request.environment.language.rewrites, ∀ premise ∈ rule.premises,
      NameSupport.PremiseCovered table premise)
    (specifications : ∀ entry ∈ request.environment.specifications, SpecificationCovered table entry.2)
    (inside : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint) :
    NameSupport.StateCovered (table := table) request.environment request.goal
      (startWithSeed matcher request seed) := by
  have captures := captures_names_covered request table footprint declarations included inside
  rw [← seed.captured] at captures
  have spines := NameSupport.selected_specification_covered request.environment specifications request.specified
  have premises := templates request.rule (List.mem_of_getElem? request.declared)
  constructor
  · intro task member
    simp only [startWithSeed, expansionWithSeed, continueRootAnswer] at member
    split at member
    · have selected := List.mem_singleton.mp member
      subst task
      exact ⟨⟨captures, spines, premises⟩, captures, trivial⟩
    · cases member
  · intro result member
    rw [startWithSeed_no_early_answers] at member
    cases member

theorem Canonical.start_free_within (request : Request) (seed : Canonical.Seed request)
    (footprint : List String) (inside : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint) :
    stateFreeWithin footprint request.environment request.goal (Canonical.start request seed) := by
  simpa only [startWithSeed_canonical] using
    startWithSeed_free_within RecursiveCollectionHandoff.canonicalMatchingExecution request
      (canonicalSeed request seed) footprint inside

theorem Canonical.start_names_covered (request : Request) (seed : Canonical.Seed request)
    (table footprint : List String)
    (declarations : ∀ rule ∈ request.environment.language.terms, rule.label ∈ table)
    (included : ∀ name ∈ footprint, name ∈ table)
    (templates : ∀ rule ∈ request.environment.language.rewrites, ∀ premise ∈ rule.premises,
      NameSupport.PremiseCovered table premise)
    (specifications : ∀ entry ∈ request.environment.specifications, SpecificationCovered table entry.2)
    (inside : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint) :
    NameSupport.StateCovered (table := table) request.environment request.goal (Canonical.start request seed) := by
  simpa only [startWithSeed_canonical] using
    startWithSeed_names_covered RecursiveCollectionHandoff.canonicalMatchingExecution request
      (canonicalSeed request seed) table footprint declarations included templates specifications inside

/-- The finite source-derived alphabet suffices at the actual post-match start. -/
theorem Canonical.start_ready (request : Request) (seed : Canonical.Seed request) :
    let footprint := request.source.freeFvarNames ++ providerFreeNames request.environment.provider
    let names := NameSupport.environmentNameTable request.environment footprint
    stateFreeWithin footprint request.environment request.goal (Canonical.start request seed) ∧
      NameSupport.StateCovered (table := names) request.environment request.goal (Canonical.start request seed) := by
  dsimp only
  let footprint := request.source.freeFvarNames ++ providerFreeNames request.environment.provider
  have inside : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint :=
    fun name member => List.mem_append_left _ member
  constructor
  · exact Canonical.start_free_within request seed footprint inside
  · exact Canonical.start_names_covered request seed _ footprint
      (NameSupport.environment_table_declarations request.environment footprint)
      (NameSupport.environment_table_footprint request.environment footprint)
      (NameSupport.environment_table_templates request.environment footprint)
      (NameSupport.environment_table_specifications request.environment footprint) inside

/-- Running the retained seed preserves the same computable free-name and alphabet obligations. -/
theorem Canonical.run_ready (request : Request) (seed : Canonical.Seed request) (work : Nat)
    (unregistered : request.environment.provider.dynamicRelations = []) :
    let footprint := request.source.freeFvarNames ++ providerFreeNames request.environment.provider
    let names := NameSupport.environmentNameTable request.environment footprint
    stateFreeWithin footprint request.environment request.goal
      (Canonical.run request work (Canonical.start request seed)) ∧
      NameSupport.StateCovered (table := names) request.environment request.goal
        (Canonical.run request work (Canonical.start request seed)) := by
  dsimp only
  let footprint := request.source.freeFvarNames ++ providerFreeNames request.environment.provider
  have provider : ∀ name ∈ providerFreeNames request.environment.provider, name ∈ footprint :=
    fun name member => List.mem_append_right _ member
  have initial := Canonical.start_ready request seed
  have rows := provider_coverage_mono _ footprint request.environment.provider provider
    (provider_covered_by_own_names request.environment.provider)
  have dynamic := Query.DynamicOutputsFreeWithin.of_unregistered footprint request.environment unregistered
  constructor
  · exact StructuralDescent.Scheduled.run_free_within
      RecursiveCollectionHandoff.canonical_preservesFreeNames footprint request.environment request.goal
      rows dynamic work (Canonical.start request seed) initial.1
  · exact NameSupport.run_covered MatchingExecution.canonical_preservesNames
      RecursiveCollectionHandoff.canonical_preservesFreeNames request.environment request.goal
      (NameSupport.environment_table_declarations request.environment footprint)
      (NameSupport.environment_table_footprint request.environment footprint) rows dynamic
      (NameSupport.environment_table_templates request.environment footprint)
      (NameSupport.environment_table_specifications request.environment footprint)
      work (Canonical.start request seed) initial.1 initial.2

#print axioms captures_names_covered
#print axioms startWithSeed_free_within
#print axioms startWithSeed_names_covered
#print axioms Canonical.start_free_within
#print axioms Canonical.start_names_covered
#print axioms Canonical.start_ready
#print axioms Canonical.run_ready
end Mettapedia.OSLF.MeTTaIL.RecursiveCollectionContinuation
