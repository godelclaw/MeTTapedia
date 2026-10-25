import Mettapedia.OSLF.MeTTaIL.CollectionMatcherBackend
import Mettapedia.OSLF.MeTTaIL.Complete.Graph
import Mettapedia.OSLF.MeTTaIL.Complete.Presented

/-!
# Root collection search with retained typed continuations

The existing plan matcher supplies raw allocation receipts. Once its finite
frontier settles, each receipt starts the shared typed/premise continuation.
The continuation batch retains every origin and one chronological log. The
strategy implements the existing resumable-search interface.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionRootSearch

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax CollectionMatcherBackend
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Machines.ResumableSearchRunner (Search Status)

def rootRule (rule : RewriteRule) : Bool :=
  match rule.left with
  | .collection .hashBag _ _ | .collection .hashSet _ _ => true
  | _ => false

/-- Syntactic and structural admission conditions for this strategy. No
coverage theorem or execution result is supplied as a certificate field. -/
structure Profile (plan : GeneralExecutionAdmission.Plan) where
  collection : CollectionExecutionAdmission.Certificate plan
  rootOnly : plan.permissions.sites = .rootOnly
  noEquations : plan.equations = []
  rootRules : plan.rules.all (fun declaration => rootRule declaration.rule) = true
  structural : StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) = true
  finiteProvider : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = []

def profile? (plan : GeneralExecutionAdmission.Plan) : Option (Profile plan) := do
  let collection ← CollectionExecutionAdmission.admit? plan
  if rootOnly : plan.permissions.sites = .rootOnly then
    if noEquations : plan.equations = [] then
      if rootRules : plan.rules.all (fun declaration => rootRule declaration.rule) = true then
        if structural : StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) = true then
          if finiteProvider : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [] then
            some ⟨collection, rootOnly, noEquations, rootRules, structural, finiteProvider⟩
          else none
        else none
      else none
    else none
  else none

variable (plan : GeneralExecutionAdmission.Plan) (profile : Profile plan)

abbrev requests (source : Pattern) :=
  CollectionExecutionAdmission.requestsForSource plan profile.collection source

/-- The existing matcher state is retained; increasing work resumes it. -/
structure Matching (source : Pattern) where
  spent : Nat
  state : CollectionPlanMachine.State
  reached : state = CollectionPlanMachine.resume spent
    (CollectionPlanMachine.start (requests plan profile source))

variable {plan profile}

def Matching.begin (source : Pattern) : Matching plan profile source :=
  ⟨0, CollectionPlanMachine.start (requests plan profile source),
    (CollectionPlanMachine.resume_zero _).symm⟩

def Matching.resume {source : Pattern} (extra : Nat) (matching : Matching plan profile source) :
    Matching plan profile source :=
  ⟨matching.spent + extra, CollectionPlanMachine.resume extra matching.state, by
    rw [matching.reached, CollectionPlanMachine.resume_add]⟩

theorem Matching.resume_add {source : Pattern} (first extra : Nat)
    (matching : Matching plan profile source) :
    matching.resume (first + extra) = (matching.resume first).resume extra := by
  cases matching
  simp only [Matching.resume, Nat.add_assoc, CollectionPlanMachine.resume_add]

def rawPublication (state : CollectionPlanMachine.State) : List Retained.Match :=
  state.flatMap fun job => (ScopedCollectionMachine.publication job.state).map fun receipt =>
    ⟨job.ordinal, job.request, receipt⟩

theorem Matching.raw_authority {source : Pattern} (matching : Matching plan profile source)
    {matched : Retained.Match} (member : matched ∈ rawPublication matching.state) :
    MatchAuthority plan profile.collection source matched.ordinal matched.request matched.receipt := by
  rw [matching.reached] at member
  simp only [rawPublication, CollectionPlanMachine.resume, CollectionPlanMachine.start,
    List.flatMap_map, List.map_map, Function.comp_def, List.mem_flatMap, List.mem_map] at member
  obtain ⟨⟨ordinal, request⟩, origin, receipt, published, same⟩ := member
  cases same
  exact match_authority_of_origin plan profile.collection source origin
    (ScopedCollectionMachine.publication_sound request matching.spent published)

def Matching.matches {source : Pattern} (matching : Matching plan profile source) :
    List (Retained.CheckedMatch plan profile.collection source) :=
  (rawPublication matching.state).attach.map fun matched =>
    ⟨matched.val, matching.raw_authority matched.property⟩

theorem Matching.raw_complete {source : Pattern} (matching : Matching plan profile source)
    (complete : CollectionPlanMachine.complete matching.state = true)
    {matched : Retained.Match}
    (origin : (matched.ordinal, matched.request) ∈ requests plan profile source)
    (valid : ScopedCollectionMachine.Valid matched.request matched.receipt) :
    matched ∈ rawPublication matching.state := by
  rw [matching.reached] at complete ⊢
  have jobMember :
      (⟨matched.ordinal, matched.request,
        ScopedCollectionMachine.resume matched.request matching.spent
          (ScopedCollectionMachine.start matched.request)⟩ : CollectionPlanMachine.Job) ∈
      CollectionPlanMachine.resume matching.spent
        (CollectionPlanMachine.start (requests plan profile source)) := by
    apply List.mem_map.mpr
    refine ⟨⟨matched.ordinal, matched.request, ScopedCollectionMachine.start matched.request⟩, ?_, rfl⟩
    exact List.mem_map_of_mem origin
  have finished := List.all_eq_true.mp complete _ jobMember
  apply List.mem_flatMap.mpr
  refine ⟨_, jobMember, List.mem_map.mpr ⟨matched.receipt, ?_, ?_⟩⟩
  · exact (ScopedCollectionMachine.publication_exact matched.request matching.spent finished _).mpr valid
  · cases matched
    rfl

/-- An ordinary firing on an arranged carrier supplies a raw collection
receipt with exactly its captured assignment. No RHS is evaluated here. -/
theorem raw_receipt_of_ordinary
    (request : ScopedCollectionMachine.Request) (ready : RootReady request)
    (unordered : request.kind ≠ .vec)
    (fixed : CanonicalBags.arrange request.kind request.targets = request.targets)
    (captured : ScopedRuleMatching.Assignment)
    (matched : GeneralScopedMatch.Matches request.rule request.spec 0 .left [] 0 [] request.rule.left
      (.collection request.kind request.targets none) captured) :
    ∃ receipt : ScopedCollectionMachine.Receipt,
      ScopedCollectionMachine.Valid request receipt ∧ receipt.matching.assignment = captured := by
  have ordinary := matched
  rw [ready.schema] at ordinary
  have meaning := CollectionMatcherCompatibility.collection_matches_of_ordinary_on_fixed
    unordered fixed ordinary
  have member := (ScopedCollectionMatching.run_exact request.rule request.spec 0 .left [] 0 0
    [] captured request.schemas request.rest unordered (by
      intro setKind
      have distinct := CollectionSelection.canonical_set_distinct request.targets
      rw [setKind] at fixed
      rwa [fixed] at distinct)).mpr meaning
  obtain ⟨work, complete⟩ := ScopedCollectionMachine.eventually_complete request
    (ScopedCollectionMachine.start request)
  have values := ScopedCollectionMachine.completed_assignments request work complete
  have found : captured ∈ (ScopedCollectionMachine.publication
      (ScopedCollectionMachine.resume request work (ScopedCollectionMachine.start request))).map
        (fun receipt => receipt.matching.assignment) := by
    rw [values]
    simpa only [ready.ambient, ready.site, ready.path, ready.depth, ready.index, ready.initial] using member
  obtain ⟨receipt, published, same⟩ := List.mem_map.mp found
  exact ⟨receipt, ScopedCollectionMachine.publication_sound request work published, same⟩

theorem Matching.eventually_complete {source : Pattern} (matching : Matching plan profile source) :
    ∃ work, CollectionPlanMachine.complete (matching.resume work).state = true := by
  have finite : ∀ state : CollectionPlanMachine.State,
      ∃ work, CollectionPlanMachine.complete (CollectionPlanMachine.resume work state) = true := by
    intro state
    induction state with
    | nil => exact ⟨0, rfl⟩
    | cons job jobs ih =>
      obtain ⟨first, headFinished⟩ := ScopedCollectionMachine.eventually_complete job.request job.state
      obtain ⟨later, tailFinished⟩ := ih
      refine ⟨first + later, ?_⟩
      change (ScopedCollectionMachine.complete
        (ScopedCollectionMachine.resume job.request (first + later) job.state) &&
        CollectionPlanMachine.complete (CollectionPlanMachine.resume (first + later) jobs)) = true
      rw [ScopedCollectionMachine.resume_add,
        ScopedCollectionMachine.complete_resume job.request _ headFinished, headFinished]
      simp only [Bool.true_and]
      rw [Nat.add_comm first later, CollectionPlanMachine.resume_add]
      have stopped : CollectionPlanMachine.resume first (CollectionPlanMachine.resume later jobs) =
          CollectionPlanMachine.resume later jobs := by
        have every := List.all_eq_true.mp tailFinished
        calc
          _ = (CollectionPlanMachine.resume later jobs).map id := by
            apply List.map_congr_left
            intro current present
            have idle := every current present
            cases current
            simp only [ScopedCollectionMachine.complete_resume _ _ idle, id_eq]
          _ = _ := List.map_id _
      rw [stopped]
      exact tailFinished
  exact finite matching.state

variable (expected : TypeExpr)

inductive Phase (source : Pattern) where
  | rejected
  | matching
      (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
        (GeneralPlanEnvironment.environment plan).free [] expected source)
      (matcher : Matching plan profile source)
  | continuing
      (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
        (GeneralPlanEnvironment.environment plan).free [] expected source)
      (search : Retained.State plan profile.collection source expected)
      (balanced : search.Balanced)

structure Run where
  source : Pattern
  phase : Phase (plan := plan) (profile := profile) expected source

/-- The source packet retains the original matcher receipt, completed
assignment, premise origins and target. The ordinary validation witness
remains in the retained run rather than becoming another source occurrence. -/
structure Receipt where
  matched : Retained.Match
  completed : ScopedRuleMatching.Assignment
  history : List GeneralPremise.Event
  target : Pattern

def observe (publication : Retained.Publication) : Receipt :=
  ⟨publication.matched, publication.outcome.completed, publication.outcome.history,
    publication.outcome.target⟩

def Receipt.Valid (source : Pattern) (receipt : Receipt) : Prop :=
  MatchAuthority plan profile.collection source receipt.matched.ordinal
      receipt.matched.request receipt.matched.receipt ∧
    ∃ trace, GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] expected
      (CollectionMatcherCompatibility.ordinaryTarget receipt.matched.request receipt.matched.receipt)
      receipt.matched.ordinal trace receipt.matched.receipt.matching.assignment receipt.completed
      receipt.history receipt.target

theorem observe_valid {source : Pattern} {publication : Retained.Publication}
    (valid : publication.Valid plan profile.collection source expected) :
    (observe publication).Valid (profile := profile) expected source := by
  obtain ⟨authority, captured, held⟩ := valid
  exact ⟨authority, publication.outcome.trace, captured ▸ held⟩

theorem Receipt.source_typed {source : Pattern} {receipt : Receipt}
    (valid : receipt.Valid (profile := profile) expected source) :
    OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected source := by
  obtain ⟨authority, trace, held⟩ := valid
  have sorted : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected
      (CollectionMatcherCompatibility.ordinaryTarget receipt.matched.request receipt.matched.receipt) := by
    cases held with
    | fire _ _ _ sorted _ _ _ _ _ => exact sorted
  exact CanonicalBags.openPatternWellSorted_of_eqvGen
    (.symm _ _ authority.source_equivalent) sorted

def begin (source : Pattern) : Run (plan := plan) (profile := profile) expected :=
  if typed : checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected source = true then
    ⟨source, .matching (checkOpenPatternWellSorted_sound typed) (Matching.begin source)⟩
  else ⟨source, .rejected⟩

theorem begin_source (source : Pattern) : (begin (profile := profile) expected source).source = source := by
  unfold begin
  split <;> rfl

def depth (matched : Retained.Match) : Nat :=
  PatternTreeSize.nodes (CollectionMatcherCompatibility.ordinaryTarget matched.request matched.receipt)

def tick (run : Run (plan := plan) (profile := profile) expected) :
    Run (plan := plan) (profile := profile) expected :=
  match run with
  | ⟨source, .rejected⟩ => ⟨source, .rejected⟩
  | ⟨source, .matching typed matcher⟩ =>
      if CollectionPlanMachine.complete matcher.state then
        ⟨source, .continuing typed (Retained.State.initial matcher.matches typed depth)
          (Retained.State.begin_balanced _)⟩
      else ⟨source, .matching typed (matcher.resume 1)⟩
  | ⟨source, .continuing typed search balanced⟩ =>
      ⟨source, .continuing typed search.round (Retained.State.round_balanced balanced)⟩

def rounds : Nat → Run (plan := plan) (profile := profile) expected →
    Run (plan := plan) (profile := profile) expected
  | 0, run => run
  | work + 1, run => rounds work (tick expected run)

def publication (run : Run (plan := plan) (profile := profile) expected) : List Receipt :=
  match run.phase with
  | .continuing _ search _ => search.log.map observe
  | .rejected | .matching _ _ => []

def status (run : Run (plan := plan) (profile := profile) expected) : Status :=
  match run.phase with
  | .rejected => .blocked
  | .matching _ _ => .pending
  | .continuing _ search _ => if search.complete then .complete else .pending

def search : Search Pattern (Run (plan := plan) (profile := profile) expected) Receipt where
  run source work := rounds expected work (begin expected source)
  resume run work := rounds expected work run
  publication := publication expected
  status := status expected
  target result := CanonicalBags.canon result.target
  Valid source result := result.Valid (profile := profile) expected source

theorem rounds_add (first extra : Nat)
    (run : Run (plan := plan) (profile := profile) expected) :
    rounds expected (first + extra) run = rounds expected extra (rounds expected first run) := by
  induction first generalizing run with
  | zero => simp only [Nat.zero_add, rounds]
  | succ first ih => simpa only [Nat.succ_add, rounds] using ih (tick expected run)

theorem tick_source (run : Run (plan := plan) (profile := profile) expected) :
    (tick expected run).source = run.source := by
  obtain ⟨source, phase⟩ := run
  cases phase <;> simp only [tick]
  split <;> rfl

theorem rounds_source (work : Nat)
    (run : Run (plan := plan) (profile := profile) expected) :
    (rounds expected work run).source = run.source := by
  induction work generalizing run with
  | zero => rfl
  | succ work ih => exact (ih _).trans (tick_source expected run)

theorem tick_publication_prefix (run : Run (plan := plan) (profile := profile) expected) :
    publication expected run <+: publication expected (tick expected run) := by
  obtain ⟨source, phase⟩ := run
  cases phase with
  | rejected => exact List.prefix_refl _
  | matching typed matcher =>
    simp only [publication, tick]
    split <;> exact List.nil_prefix
  | continuing typed current balanced => exact (List.prefix_append _ _).map observe

theorem rounds_publication_prefix (work : Nat)
    (run : Run (plan := plan) (profile := profile) expected) :
    publication expected run <+: publication expected (rounds expected work run) := by
  induction work generalizing run with
  | zero => exact List.prefix_refl _
  | succ work ih => exact (tick_publication_prefix expected run).trans (ih _)

theorem publication_sound (run : Run (plan := plan) (profile := profile) expected)
    {result : Receipt} (member : result ∈ publication expected run) :
    result.Valid (profile := profile) expected run.source := by
  obtain ⟨source, phase⟩ := run
  cases phase with
  | rejected => cases member
  | matching => cases member
  | continuing typed current balanced =>
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨frame, _, present⟩ := List.mem_flatMap.mp (balanced.subset present)
    exact observe_valid expected (frame.publication_sound present)

theorem search_lawful : (search (plan := plan) (profile := profile) expected).Lawful where
  resume_run source first extra := (rounds_add expected first extra (begin expected source)).symm
  publication_prefix source first extra := by
    rw [show (search expected).run source (first + extra) =
      (search expected).resume ((search expected).run source first) extra from
      rounds_add expected first extra (begin expected source)]
    exact rounds_publication_prefix expected extra _
  sound source work result member := by
    have valid := publication_sound expected (rounds expected work (begin expected source)) member
    rw [rounds_source, begin_source] at valid
    exact valid

theorem begin_typed (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected source) :
    begin (profile := profile) expected source = ⟨source, .matching typed (Matching.begin source)⟩ := by
  simp only [begin, checkOpenPatternWellSorted_complete typed, ↓reduceDIte]

theorem rounds_continuing (work : Nat) {source : Pattern}
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected source)
    (current : Retained.State plan profile.collection source expected) (balanced : current.Balanced) :
    rounds expected work ⟨source, .continuing typed current balanced⟩ =
      ⟨source, .continuing typed (Retained.State.run work current)
        (Retained.State.run_balanced work balanced)⟩ := by
  induction work generalizing current with
  | zero => rfl
  | succ work ih => exact ih current.round (Retained.State.round_balanced balanced)

/-- The matching phase uses the existing finite matcher, with no provisional
RHS filter. Completion hands its actual raw frontier to the continuations. -/
theorem matching_enters_continuing {source : Pattern}
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected source)
    (matching : Matching plan profile source) :
    ∃ (work : Nat) (finished : Matching plan profile source),
      CollectionPlanMachine.complete finished.state = true ∧
      rounds expected work ⟨source, .matching typed matching⟩ =
        ⟨source, .continuing typed (Retained.State.initial finished.matches typed depth)
          (Retained.State.begin_balanced _)⟩ := by
  obtain ⟨budget, complete⟩ := matching.eventually_complete
  have enters : ∀ (budget : Nat) (matching : Matching plan profile source),
      CollectionPlanMachine.complete (matching.resume budget).state = true →
      ∃ (work : Nat) (finished : Matching plan profile source),
        CollectionPlanMachine.complete finished.state = true ∧
        rounds expected work ⟨source, .matching typed matching⟩ =
          ⟨source, .continuing typed (Retained.State.initial finished.matches typed depth)
            (Retained.State.begin_balanced _)⟩ := by
    intro budget
    induction budget with
    | zero =>
      intro matching complete
      have finished : CollectionPlanMachine.complete matching.state = true := by
        simpa only [Matching.resume, CollectionPlanMachine.resume_zero] using complete
      exact ⟨1, matching, finished, by simp only [rounds, tick, finished, ↓reduceIte]⟩
    | succ budget ih =>
      intro matching complete
      by_cases finished : CollectionPlanMachine.complete matching.state = true
      · exact ⟨1, matching, finished, by simp only [rounds, tick, finished, ↓reduceIte]⟩
      · have nextFinished : CollectionPlanMachine.complete ((matching.resume 1).resume budget).state = true := by
          rw [← Matching.resume_add, Nat.add_comm 1 budget]
          exact complete
        obtain ⟨work, actual, completeActual, entered⟩ := ih (matching.resume 1) nextFinished
        refine ⟨work + 1, actual, completeActual, ?_⟩
        simpa only [rounds, tick, finished, Bool.false_eq_true, ↓reduceIte] using entered
  exact enters budget matching complete

/-- Every independent raw-root source packet reaches the retained search.
This retains the raw allocation and premise origins while forgetting only
the auxiliary ordinary validation trace. Full presented-law comparison is
a separate obligation and is not a consequence of this theorem. -/
theorem source_coverage {source : Pattern} {receipt : Receipt}
    (valid : receipt.Valid (profile := profile) expected source) :
    ∃ work, receipt ∈ (search (profile := profile) expected).publication
      ((search (profile := profile) expected).run source work) := by
  have typed := Receipt.source_typed expected valid
  obtain ⟨enteredAt, finished, complete, entered⟩ :=
    matching_enters_continuing expected typed (Matching.begin source)
  have raw := finished.raw_complete complete valid.1.origin valid.1.valid
  have selected : (⟨receipt.matched, valid.1⟩ : Retained.CheckedMatch plan profile.collection source) ∈
      finished.matches := by
    apply List.mem_map.mpr
    exact ⟨⟨receipt.matched, raw⟩, List.mem_attach _ _, rfl⟩
  have initial : Retained.Frame.initial receipt.matched valid.1 typed (depth receipt.matched) ∈
      (Retained.State.initial finished.matches typed depth).frames := List.mem_map_of_mem selected
  obtain ⟨trace, held⟩ := valid.2
  have bound := StructuralDescent.firing_depth_bound (GeneralPlanEnvironment.environment plan)
    profile.structural _ [] expected
    ⟨receipt.matched.ordinal, trace, receipt.matched.receipt.matching.assignment,
      receipt.completed, receipt.history, receipt.target, held⟩
  have bounded : StructuralDescent.eventsDepth receipt.history ≤ depth receipt.matched := by
    change 1 + StructuralDescent.eventsDepth receipt.history ≤ depth receipt.matched at bound
    omega
  obtain ⟨work, chosenTrace, published⟩ := Retained.State.source_coverage _ receipt.matched valid.1
    typed (depth receipt.matched) initial trace receipt.completed receipt.history receipt.target held bounded
  refine ⟨enteredAt + work, ?_⟩
  change receipt ∈ publication expected (rounds expected (enteredAt + work) (begin expected source))
  rw [begin_typed expected source typed, rounds_add, entered]
  erw [rounds_continuing]
  exact List.mem_map.mpr ⟨_, published, by cases receipt; rfl⟩

/-- Every ordinary root firing at an arranged request source has a source
packet of this strategy with the same captures, premise history and result.
This is the reverse comparison at the actual canonical input, not yet a
transport theorem from arbitrary model-equal presentations. -/
theorem ordinary_root_source_packet {source : Pattern}
    (ordinal : Nat) (request : ScopedCollectionMachine.Request)
    (origin : (ordinal, request) ∈ requests plan profile source)
    (sourceEq : source = .collection request.kind request.targets none)
    (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : ScopedRuleMatching.Assignment) (history : List GeneralPremise.Event)
    (target : Pattern)
    (held : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] expected source
      ordinal trace captured completed history target) :
    ∃ receipt : Receipt, receipt.Valid (profile := profile) expected source ∧
      receipt.matched.receipt.matching.assignment = captured ∧
      receipt.completed = completed ∧ receipt.history = history ∧ receipt.target = target := by
  have selected := CollectionExecutionAdmission.requestsForSource_selected origin
  obtain ⟨targets, requested⟩ := CollectionExecutionAdmission.requestForSource?_requested selected
  obtain ⟨declaration, position, ruleEq, specEq, _⟩ :=
    CollectionExecutionAdmission.request?_selected requested
  have declaredExpected : (GeneralPlanEnvironment.environment plan).language.rewrites[ordinal]? =
      some request.rule := by
    simpa only [ruleEq] using GeneralPlanEnvironment.selected_rule plan position
  have specifiedExpected : GeneralPremise.specification? (GeneralPlanEnvironment.environment plan) ordinal =
      some request.spec := by
    simpa only [specEq] using GeneralPlanEnvironment.selected_specification plan position
  have ready := CollectionMatcherBackend.request_ready requested
  have unordered := CollectionExecutionAdmission.request?_unordered requested
  have fixed := CollectionExecutionAdmission.requestForSource?_fixed selected
  cases held with
  | @fire _ _ _ _ _ rule spec _ _ _ _ declared specified admitted sorted matched typed premises reduced targetTyped =>
    have ruleSame := Option.some.inj (declared.symm.trans declaredExpected)
    have specSame := Option.some.inj (specified.symm.trans specifiedExpected)
    subst rule
    subst spec
    have ordinary : GeneralScopedMatch.Matches request.rule request.spec 0 .left [] 0 []
        request.rule.left (.collection request.kind request.targets none) captured := by
      rw [← sourceEq]
      exact matched.matching
    obtain ⟨raw, validRaw, sameRaw⟩ := raw_receipt_of_ordinary request ready unordered fixed captured ordinary
    let authority := match_authority_of_origin plan profile.collection source origin validRaw
    obtain ⟨answer, _, same⟩ := CollectionMatcherCompatibility.ordinaryAnswers_complete
      ready.index unordered validRaw
    let rootAnswer := CollectionMatcherBackend.ordinaryRootAnswer request raw ready answer
    have sameAnswer : rootAnswer.val.assignment = captured := same.trans sameRaw
    have rematched : GeneralScopedMatchMachine.TracedMatches request.rule request.spec 0 .left [] 0 []
        request.rule.left (CollectionMatcherCompatibility.ordinaryTarget request raw)
        rootAnswer.val.trace captured := by
      rw [← sameAnswer]
      exact rootAnswer.property
    have transported : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] expected
        (CollectionMatcherCompatibility.ordinaryTarget request raw) ordinal rootAnswer.val.trace
        captured completed history target :=
      .fire authority.declared authority.specified authority.admitted (authority.source_typed sorted)
        rematched typed premises reduced targetTyped
    let receipt : Receipt := ⟨⟨ordinal, request, raw⟩, completed, history, target⟩
    refine ⟨receipt, ⟨authority, rootAnswer.val.trace, ?_⟩, sameRaw, rfl, rfl, rfl⟩
    simpa only [receipt, sameRaw] using transported

theorem ordinary_root_covered {source : Pattern}
    (ordinal : Nat) (request : ScopedCollectionMachine.Request)
    (origin : (ordinal, request) ∈ requests plan profile source)
    (sourceEq : source = .collection request.kind request.targets none)
    (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : ScopedRuleMatching.Assignment) (history : List GeneralPremise.Event)
    (target : Pattern)
    (held : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] expected source
      ordinal trace captured completed history target) :
    ∃ work receipt, receipt ∈ (search (profile := profile) expected).publication
      ((search (profile := profile) expected).run source work) ∧
      receipt.matched.receipt.matching.assignment = captured ∧ receipt.completed = completed ∧
      receipt.history = history ∧ receipt.target = target := by
  obtain ⟨receipt, valid, same, completedEq, historyEq, targetEq⟩ :=
    ordinary_root_source_packet expected ordinal request origin sourceEq trace captured completed history target held
  obtain ⟨work, published⟩ := source_coverage expected valid
  exact ⟨work, receipt, published, same, completedEq, historyEq, targetEq⟩

/-- A source packet authorizes an actual step of the existing presented
GSLT, including its model equality before matching and after the reduct. -/
theorem Receipt.presented_step {source : Pattern} {receipt : Receipt}
    (valid : receipt.Valid (profile := profile) expected source) :
    (Complete.Presented.gslt plan [] expected).Step source (CanonicalBags.canon receipt.target) := by
  obtain ⟨authority, trace, held⟩ := valid
  have selected := CollectionExecutionAdmission.requestsForSource_selected authority.origin
  obtain ⟨targets, requested⟩ := CollectionExecutionAdmission.requestForSource?_requested selected
  obtain ⟨declaration, position, _, _, _⟩ := CollectionExecutionAdmission.request?_selected requested
  have sourceTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected
      (CollectionMatcherCompatibility.ordinaryTarget receipt.matched.request receipt.matched.receipt) := by
    cases held with
    | fire _ _ _ sorted _ _ _ _ _ => exact sorted
  have targetTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected receipt.target := by
    cases held with
    | fire _ _ _ _ _ _ _ _ sorted => exact sorted
  let presented := CollectionMatcherCompatibility.ordinaryTarget receipt.matched.request receipt.matched.receipt
  let job : GeneralRuleJobs.Job :=
    ⟨receipt.matched.ordinal, declaration, GeneralTypedSites.SiteData.here [] expected presented⟩
  let primitive : GeneralRuleJobs.Receipt :=
    ⟨job, trace, receipt.matched.receipt.matching.assignment, receipt.completed,
      receipt.history, receipt.target, receipt.target⟩
  have licensed : job.Valid plan [] expected presented := by
    constructor
    · exact List.mk_mem_zipIdx_iff_getElem?.mpr position
    · exact .here (by rw [profile.rootOnly]; rfl) sourceTyped.2.2.1 sourceTyped.1
  have primitiveValid : primitive.Valid plan [] expected presented := by
    exact ⟨licensed, held, rfl, rfl, targetTyped⟩
  have same := CanonicalBags.eqvGen_canon_eq authority.source_equivalent
  have before : Complete.Presented.ModelEquiv plan [] expected source presented := by
    apply Relation.EqvGen.trans _ _ _ (Complete.Presented.canon_equiv plan [] expected source)
    rw [same]
    exact .symm _ _ (Complete.Presented.canon_equiv plan [] expected presented)
  exact ⟨presented, primitive, before, primitiveValid,
    Complete.Presented.canon_equiv plan [] expected receipt.target⟩

theorem run_presented_step (source : Pattern) (work : Nat) {receipt : Receipt}
    (published : receipt ∈ (search (profile := profile) expected).publication
      ((search (profile := profile) expected).run source work)) :
    (Complete.Presented.gslt plan [] expected).Step source (CanonicalBags.canon receipt.target) :=
  Receipt.presented_step expected ((search_lawful expected).sound source work receipt published)

private theorem retained_round_idle {source : Pattern}
    (current : Retained.State plan profile.collection source expected)
    (complete : current.complete = true) : current.round = current := by
  have each := List.all_eq_true.mp complete
  have advanced : current.frames.map (Retained.Frame.run 1) = current.frames := by
    calc
      _ = current.frames.map id := List.map_congr_left fun frame present =>
        Retained.Frame.run_idle frame (List.isEmpty_iff.mp (each frame present)) 1
      _ = _ := List.map_id _
  have fresh : current.frames.flatMap Retained.Frame.fresh = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro frame present
    rw [Retained.Frame.fresh,
      Retained.Frame.run_idle frame (List.isEmpty_iff.mp (each frame present)) 1,
      List.drop_length]
  cases current
  simp only [Retained.State.round, advanced, fresh, List.append_nil]

private theorem retained_run_idle {source : Pattern}
    (current : Retained.State plan profile.collection source expected)
    (complete : current.complete = true) (work : Nat) : Retained.State.run work current = current := by
  induction work with
  | zero => rfl
  | succ work ih => simpa only [Retained.State.run, retained_round_idle expected current complete] using ih

theorem search_stable : Complete.Settled.Stable (search (profile := profile) expected) := by
  intro run work complete
  obtain ⟨source, phase⟩ := run
  cases phase with
  | rejected => cases complete
  | matching => cases complete
  | continuing typed current balanced =>
    have done : current.complete = true := by
      change (if current.complete then Status.complete else .pending) = .complete at complete
      split at complete
      · assumption
      · cases complete
    have unchanged : rounds expected work ⟨source, .continuing typed current balanced⟩ =
        ⟨source, .continuing typed current balanced⟩ := by
      simp only [rounds_continuing, retained_run_idle expected current done]
    exact ⟨congrArg (publication expected) unchanged,
      (congrArg (status expected) unchanged).trans complete⟩

theorem eventually_complete (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      (GeneralPlanEnvironment.environment plan).free [] expected source) :
    ∃ work, (search (profile := profile) expected).status
      ((search (profile := profile) expected).run source work) = .complete := by
  obtain ⟨enteredAt, finished, _, entered⟩ := matching_enters_continuing expected typed (Matching.begin source)
  obtain ⟨work, complete⟩ := Retained.State.eventually_settled finished.matches typed depth
  refine ⟨enteredAt + work, ?_⟩
  change status expected (rounds expected (enteredAt + work) (begin expected source)) = .complete
  rw [begin_typed expected source typed, rounds_add, entered]
  erw [rounds_continuing]
  simp only [status, complete, ↓reduceIte]

end Mettapedia.OSLF.MeTTaIL.CollectionRootSearch
