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

end Mettapedia.OSLF.MeTTaIL.RecursiveCollectionContinuation
