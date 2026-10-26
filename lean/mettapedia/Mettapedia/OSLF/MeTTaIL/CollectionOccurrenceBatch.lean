import Mathlib.Data.Finset.Image
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceContinuation
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionTraceAccounting
import Mathlib.Data.List.Perm.Basic

/-!
# Retained conditional allocations at typed collection occurrences

Every frame owns its original occurrence, recursive allocation and scheduled
continuation. The chronological log drains each frame's own publication
suffix. Its permutation account preserves complete packets and multiplicity;
it identifies neither logical derivations nor repeated validation evidence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceBatch

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching GeneralPremise
open CollectionOccurrenceHandoff RecursiveCollectionHandoff

variable (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern)

structure Allocation where
  job : Job
  licensed : job.Valid plan bound expected source
  answer : RecursiveCollectionMachine.Answer
  prepared : Prepared
  matching : prepared.Valid job.request answer
  depth : Nat
  request : RecursiveCollectionContinuation.Request
  issued : CollectionOccurrenceContinuation.request? plan bound expected source job licensed
    answer prepared matching depth = some request

variable {plan bound expected source}
variable {matcher : MatchingExecution} {Choice : Type}

theorem Allocation.request_origin (allocation : Allocation plan bound expected source) :
    allocation.request.environment = GeneralPlanEnvironment.environment plan ∧
      allocation.request.prepared = allocation.prepared := by
  have issued := allocation.issued
  unfold CollectionOccurrenceContinuation.request? at issued
  dsimp only at issued
  split at issued
  · split at issued
    · have same := Option.some.inj issued
      rw [← same]
      exact ⟨rfl, rfl⟩
    · cases issued
  · cases issued

/-- Only published recursive matches enter preparation and the existing
local typing/admission checks. No premise outcome is supplied here. -/
def allocate? (job : Job) (licensed : job.Valid plan bound expected source)
    (work : Nat) (answer : RecursiveCollectionMachine.Answer)
    (published : answer ∈ (RecursiveCollectionMachine.run job.request work
      (RecursiveCollectionMachine.start job.request)).answers) (depth : Nat) :
    Option (Allocation plan bound expected source) :=
  match made : prepare job.request answer with
  | none => none
  | some prepared =>
    let matching := prepare_valid job.request answer
      (RecursiveCollectionMachine.published_trace_valid job.request work published) made
    match issued : CollectionOccurrenceContinuation.request? plan bound expected source
        job licensed answer prepared matching depth with
    | none => none
    | some request => some ⟨job, licensed, answer, prepared, matching, depth, request, issued⟩

structure Frame (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (matcher : MatchingExecution := MatchingExecution.ordinary) where
  allocation : Allocation plan bound expected source
  state : StructuralDescent.Scheduled.State allocation.request.environment allocation.request.goal matcher

structure Publication (Choice : Type := GeneralScopedMatchMachine.BagChoice) where
  job : Job
  answer : RecursiveCollectionMachine.Answer
  prepared : Prepared
  outcome : Complete.DeepRoot.Firing Choice

/-- Operational provenance before the ordinary receipt projection. Equal
ordinary receipts may come from different recursive allocations; their
allocation traces remain available independently of result aggregation. -/
def Publication.allocationOrigin (packet : Publication Choice) :
    Job × RecursiveCollectionMachine.Answer × List (GeneralPremise.Event Choice) :=
  (packet.job, packet.answer, packet.outcome.history)

def tag (allocation : Allocation plan bound expected source)
    (outcome : Complete.DeepRoot.Firing Choice) : Publication Choice :=
  ⟨allocation.job, allocation.answer, allocation.prepared, outcome⟩

def Frame.initial (allocation : Allocation plan bound expected source) :
    Frame plan bound expected source :=
  ⟨allocation, RecursiveCollectionContinuation.start allocation.request⟩

def Frame.run (work : Nat) (frame : Frame plan bound expected source matcher) :
    Frame plan bound expected source matcher :=
  { frame with state := (StructuralDescent.Scheduled.run frame.allocation.request.environment
      frame.allocation.request.goal work frame.state) }

def Frame.publication (frame : Frame plan bound expected source matcher) : List (Publication matcher.Choice) :=
  (RecursiveCollectionContinuation.publicationIn matcher frame.allocation.request frame.state).map
    (tag frame.allocation)

theorem Frame.initial_publication (allocation : Allocation plan bound expected source) :
    (Frame.initial allocation).publication = [] := by
  simp only [Frame.publication, Frame.initial, RecursiveCollectionContinuation.publicationIn_ordinary,
    RecursiveCollectionContinuation.publication,
    RecursiveCollectionContinuation.start_no_early_answers, List.filterMap_nil, List.map_nil]

theorem Frame.run_add (first extra : Nat) (frame : Frame plan bound expected source matcher) :
    Frame.run (first + extra) frame = Frame.run extra (Frame.run first frame) := by
  cases frame
  simp only [Frame.run, StructuralDescent.Scheduled.run_add]

theorem Frame.publication_prefix (frame : Frame plan bound expected source matcher) (work : Nat) :
    frame.publication <+: (Frame.run work frame).publication :=
  (RecursiveCollectionContinuation.publicationIn_prefix matcher frame.allocation.request frame.state work).map _

def Frame.fresh (frame : Frame plan bound expected source matcher) : List (Publication matcher.Choice) :=
  (Frame.run 1 frame).publication.drop frame.publication.length

theorem Frame.fresh_balance (frame : Frame plan bound expected source matcher) :
    frame.publication ++ frame.fresh = (Frame.run 1 frame).publication := by
  have grown := Frame.publication_prefix frame 1
  unfold Frame.fresh
  calc
    _ = (Frame.run 1 frame).publication.take frame.publication.length ++
        (Frame.run 1 frame).publication.drop frame.publication.length :=
      congrArg (fun front => front ++ (Frame.run 1 frame).publication.drop frame.publication.length)
        (List.prefix_iff_eq_take.mp grown)
    _ = _ := List.take_append_drop _ _

/-- A published packet retains its source allocation. Finishing it uses the
original rule-job operation, with the complete premise history. -/
def Publication.finish? (packet : Publication) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) : Option GeneralRuleJobs.Receipt :=
  CollectionOccurrenceContinuation.finish? plan bound expected packet.job packet.prepared packet.outcome

theorem Frame.publication_source_sound (frame : Frame plan bound expected source)
    {packet : Publication} (published : packet ∈ frame.publication)
    {receipt : GeneralRuleJobs.Receipt}
    (finished : packet.finish? plan bound expected = some receipt) :
    (Complete.Presented.gslt plan bound expected).Step source receipt.target := by
  obtain ⟨outcome, member, same⟩ := List.mem_map.mp published
  cases same
  rw [RecursiveCollectionContinuation.publicationIn_ordinary] at member
  exact CollectionOccurrenceContinuation.finish_source_step plan bound expected source
    frame.allocation.job frame.allocation.licensed frame.allocation.answer frame.allocation.prepared
    frame.allocation.matching frame.allocation.depth frame.allocation.issued frame.state member finished

theorem Frame.source_coverage (allocation : Allocation plan bound expected source)
    (trace : List GeneralScopedMatchMachine.BagChoice) (completed : Assignment)
    (history : List Event) (target : Pattern)
    (held : RootFiring allocation.request.environment allocation.request.bound allocation.request.type
      allocation.request.prepared.source allocation.request.index trace
      allocation.request.prepared.ordinary.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ allocation.request.depth) :
    ∃ work, tag allocation
        ⟨allocation.request.prepared.ordinary.trace, allocation.request.prepared.ordinary.assignment,
          completed, history, target⟩ ∈ (Frame.run work (Frame.initial allocation)).publication := by
  obtain ⟨work, published⟩ := RecursiveCollectionContinuation.source_coverage allocation.request
    trace completed history target held bounded
  refine ⟨work, ?_⟩
  simpa only [Frame.publication, Frame.run, Frame.initial, RecursiveCollectionContinuation.publicationIn_ordinary,
    RecursiveCollectionContinuation.run] using (List.mem_map_of_mem (f := tag allocation) published)

structure State (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (matcher : MatchingExecution := MatchingExecution.ordinary) where
  frames : List (Frame plan bound expected source matcher)
  log : List (Publication matcher.Choice)

def State.begin (allocations : List (Allocation plan bound expected source)) :
    State plan bound expected source :=
  ⟨allocations.map Frame.initial, []⟩

def State.round (state : State plan bound expected source matcher) : State plan bound expected source matcher :=
  ⟨state.frames.map (Frame.run 1), state.log ++ state.frames.flatMap Frame.fresh⟩

def State.run : Nat → State plan bound expected source matcher → State plan bound expected source matcher
  | 0, state => state
  | work + 1, state => State.run work state.round

def State.Balanced (state : State plan bound expected source matcher) : Prop :=
  state.log.Perm (state.frames.flatMap Frame.publication)

theorem State.begin_balanced (allocations : List (Allocation plan bound expected source)) :
    (State.begin allocations).Balanced := by
  have empty : (allocations.map Frame.initial).flatMap Frame.publication = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro frame member
    obtain ⟨allocation, _, rfl⟩ := List.mem_map.mp member
    exact Frame.initial_publication allocation
  change [].Perm ((allocations.map Frame.initial).flatMap Frame.publication)
  rw [empty]

theorem State.round_balanced {state : State plan bound expected source matcher}
    (balanced : state.Balanced) : state.round.Balanced := by
  apply (balanced.append_right _).trans
  apply (List.flatMap_append_perm state.frames Frame.publication Frame.fresh).trans
  change (state.frames.flatMap fun frame => frame.publication ++ frame.fresh).Perm
    ((state.frames.map (Frame.run 1)).flatMap Frame.publication)
  rw [List.flatMap_map]
  apply List.Perm.of_eq
  apply List.flatMap_congr
  intro frame _
  exact Frame.fresh_balance frame

theorem State.run_balanced (work : Nat) {state : State plan bound expected source matcher}
    (balanced : state.Balanced) : (State.run work state).Balanced := by
  induction work generalizing state with
  | zero => exact balanced
  | succ work ih => exact ih (State.round_balanced balanced)

theorem State.run_add (first extra : Nat) (state : State plan bound expected source matcher) :
    State.run (first + extra) state = State.run extra (State.run first state) := by
  induction first generalizing state with
  | zero => simp only [State.run, Nat.zero_add]
  | succ first ih => simpa only [State.run, Nat.succ_add] using ih state.round

theorem State.run_frames (work : Nat) (state : State plan bound expected source matcher) :
    (State.run work state).frames = state.frames.map (Frame.run work) := by
  induction work generalizing state with
  | zero =>
    have idle : (Frame.run 0 : Frame plan bound expected source matcher → _) = id := by
      funext frame
      cases frame
      rfl
    change state.frames = state.frames.map (Frame.run 0)
    rw [idle, List.map_id]
  | succ work ih =>
    simpa only [State.run, ih, State.round, List.map_map, Function.comp_def, Nat.add_comm 1 work] using
      congrArg (List.map · state.frames) (funext fun frame => Frame.run_add 1 work frame).symm

theorem State.log_prefix (work : Nat) (state : State plan bound expected source matcher) :
    state.log <+: (State.run work state).log := by
  induction work generalizing state with
  | zero => exact List.prefix_refl _
  | succ work ih => exact (List.prefix_append _ _).trans (ih state.round)

theorem State.publication_source_sound (work : Nat)
    (allocations : List (Allocation plan bound expected source))
    {packet : Publication} (published : packet ∈ (State.run work (State.begin allocations)).log)
    {receipt : GeneralRuleJobs.Receipt}
    (finished : packet.finish? plan bound expected = some receipt) :
    (Complete.Presented.gslt plan bound expected).Step source receipt.target := by
  have accounted := State.run_balanced work (State.begin_balanced allocations)
  obtain ⟨frame, _, present⟩ := List.mem_flatMap.mp (accounted.subset published)
  exact Frame.publication_source_sound frame present finished

theorem State.source_coverage (allocations : List (Allocation plan bound expected source))
    (allocation : Allocation plan bound expected source) (member : allocation ∈ allocations)
    (trace : List GeneralScopedMatchMachine.BagChoice) (completed : Assignment)
    (history : List Event) (target : Pattern)
    (held : RootFiring allocation.request.environment allocation.request.bound allocation.request.type
      allocation.request.prepared.source allocation.request.index trace
      allocation.request.prepared.ordinary.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ allocation.request.depth) :
    ∃ work, tag allocation
        ⟨allocation.request.prepared.ordinary.trace, allocation.request.prepared.ordinary.assignment,
          completed, history, target⟩ ∈ (State.run work (State.begin allocations)).log := by
  obtain ⟨work, present⟩ := Frame.source_coverage allocation trace completed history target held bounded
  have retained : Frame.run work (Frame.initial allocation) ∈
      (State.run work (State.begin allocations)).frames := by
    rw [State.run_frames]
    exact List.mem_map_of_mem (List.mem_map_of_mem member)
  exact ⟨work, (State.run_balanced work (State.begin_balanced allocations)).symm.subset
    (List.mem_flatMap.mpr ⟨_, retained, present⟩)⟩

/-- The ordinary specialization advances precisely the original continuation. -/
theorem Frame.run_ordinary (work : Nat) (frame : Frame plan bound expected source) :
    Frame.run work frame =
      { frame with state := RecursiveCollectionContinuation.run frame.allocation.request work frame.state } := rfl

theorem Frame.publication_ordinary (frame : Frame plan bound expected source) :
    frame.publication =
      (RecursiveCollectionContinuation.publication frame.allocation.request frame.state).map
        (tag frame.allocation) :=
  congrArg (List.map (tag frame.allocation))
    (RecursiveCollectionContinuation.publicationIn_ordinary frame.allocation.request frame.state)

theorem Allocation.request_answer (allocation : Allocation plan bound expected source) :
    allocation.request.answer = allocation.answer := by
  have issued := allocation.issued
  unfold CollectionOccurrenceContinuation.request? at issued
  dsimp only at issued
  split at issued
  · split at issued
    · have same := Option.some.inj issued
      rw [← same]
    · cases issued
  · cases issued

/-- The actual allocation record supplies its original canonical seed. -/
theorem Allocation.canonical_seed
    (allocation : Allocation plan bound expected (CanonicalBags.canon source)) :
    RecursiveCollectionContinuation.Canonical.Seed allocation.request :=
  CollectionOccurrenceContinuation.Canonical.request_seed allocation.job allocation.licensed
    allocation.answer allocation.prepared allocation.matching allocation.depth allocation.issued

/-- The same frame starts the selected canonical continuation after matching. -/
def Frame.initialCanonical
    (allocation : Allocation plan bound expected (CanonicalBags.canon source)) :
    Frame plan bound expected (CanonicalBags.canon source) RecursiveCollectionHandoff.canonicalMatchingExecution :=
  ⟨allocation, RecursiveCollectionContinuation.Canonical.start allocation.request allocation.canonical_seed⟩

theorem Frame.canonical_publication
    (frame : Frame plan bound expected source RecursiveCollectionHandoff.canonicalMatchingExecution) :
    frame.publication =
      (RecursiveCollectionContinuation.Canonical.publication frame.allocation.request frame.state).map
        (tag frame.allocation) :=
  congrArg (List.map (tag frame.allocation))
    (RecursiveCollectionContinuation.Canonical.publicationIn_canonical frame.allocation.request frame.state)

theorem Frame.initialCanonical_publication
    (allocation : Allocation plan bound expected (CanonicalBags.canon source)) :
    (Frame.initialCanonical allocation).publication = [] := by
  simp only [Frame.canonical_publication, Frame.initialCanonical,
    RecursiveCollectionContinuation.Canonical.publication,
    RecursiveCollectionContinuation.Canonical.start_no_early_answers, List.filterMap_nil, List.map_nil]

/-- The chosen canonical receipt uses the original allocation trace. The
complete outcome remains in the publication independently of that choice. -/
def Publication.finishCanonical? (packet : Publication EquationalScopedReceipts.Event)
    (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr) :
    Option (GeneralRuleJobs.Receipt EquationalScopedReceipts.Event) :=
  CollectionOccurrenceContinuation.Canonical.finish? plan bound expected packet.job packet.answer
    packet.prepared packet.outcome

theorem Frame.publication_canonical_valid
    (frame : Frame plan bound expected (CanonicalBags.canon source)
      RecursiveCollectionHandoff.canonicalMatchingExecution)
    {packet : Publication EquationalScopedReceipts.Event} (published : packet ∈ frame.publication)
    {receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event}
    (finished : packet.finishCanonical? plan bound expected = some receipt) :
    receipt.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation DynamicProvider.empty
      plan bound expected (packet.job.presentedSource packet.prepared) ∧
      CanonicalBags.Same source (packet.job.presentedSource packet.prepared) := by
  obtain ⟨outcome, member, same⟩ := List.mem_map.mp published
  cases same
  rw [RecursiveCollectionContinuation.Canonical.publicationIn_canonical] at member
  exact CollectionOccurrenceContinuation.Canonical.finish_original_source frame.allocation.job
    frame.allocation.licensed frame.allocation.answer frame.allocation.prepared frame.allocation.matching
    frame.allocation.depth frame.allocation.issued frame.state member finished

theorem Frame.source_coverageCanonical
    (allocation : Allocation plan bound expected (CanonicalBags.canon source))
    (trace : List EquationalScopedReceipts.Event) (completed : Assignment)
    (history : List (Event EquationalScopedReceipts.Event)) (target : Pattern)
    (held : GeneralPremise.Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation
      allocation.request.environment allocation.request.bound allocation.request.type
      allocation.request.prepared.source allocation.request.index trace
      allocation.request.answer.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ allocation.request.depth) :
    ∃ work, tag allocation
        ⟨allocation.request.answer.trace, allocation.request.answer.assignment, completed, history, target⟩ ∈
      (Frame.run work (Frame.initialCanonical allocation)).publication := by
  obtain ⟨work, published⟩ := RecursiveCollectionContinuation.Canonical.source_coverage allocation.request
    allocation.canonical_seed trace completed history target held bounded
  refine ⟨work, ?_⟩
  simp only [Frame.publication, Frame.run, Frame.initialCanonical,
    RecursiveCollectionContinuation.Canonical.publicationIn_canonical]
  exact List.mem_map_of_mem (f := tag allocation) published

def State.beginCanonical (allocations : List (Allocation plan bound expected (CanonicalBags.canon source))) :
    State plan bound expected (CanonicalBags.canon source) RecursiveCollectionHandoff.canonicalMatchingExecution :=
  ⟨allocations.map Frame.initialCanonical, []⟩

theorem State.beginCanonical_balanced
    (allocations : List (Allocation plan bound expected (CanonicalBags.canon source))) :
    (State.beginCanonical allocations).Balanced := by
  have empty : (allocations.map Frame.initialCanonical).flatMap Frame.publication = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro frame member
    obtain ⟨allocation, _, rfl⟩ := List.mem_map.mp member
    exact Frame.initialCanonical_publication allocation
  change [].Perm ((allocations.map Frame.initialCanonical).flatMap Frame.publication)
  rw [empty]

theorem State.publication_canonical_valid (work : Nat)
    (allocations : List (Allocation plan bound expected (CanonicalBags.canon source)))
    {packet : Publication EquationalScopedReceipts.Event}
    (published : packet ∈ (State.run work (State.beginCanonical allocations)).log)
    {receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event}
    (finished : packet.finishCanonical? plan bound expected = some receipt) :
    receipt.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation DynamicProvider.empty
      plan bound expected (packet.job.presentedSource packet.prepared) ∧
      CanonicalBags.Same source (packet.job.presentedSource packet.prepared) := by
  have accounted := State.run_balanced work (State.beginCanonical_balanced allocations)
  obtain ⟨frame, _, present⟩ := List.mem_flatMap.mp (accounted.subset published)
  exact Frame.publication_canonical_valid frame present finished

theorem State.source_coverageCanonical
    (allocations : List (Allocation plan bound expected (CanonicalBags.canon source)))
    (allocation : Allocation plan bound expected (CanonicalBags.canon source)) (member : allocation ∈ allocations)
    (trace : List EquationalScopedReceipts.Event) (completed : Assignment)
    (history : List (Event EquationalScopedReceipts.Event)) (target : Pattern)
    (held : GeneralPremise.Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation
      allocation.request.environment allocation.request.bound allocation.request.type
      allocation.request.prepared.source allocation.request.index trace
      allocation.request.answer.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ allocation.request.depth) :
    ∃ work, tag allocation
        ⟨allocation.request.answer.trace, allocation.request.answer.assignment, completed, history, target⟩ ∈
      (State.run work (State.beginCanonical allocations)).log := by
  obtain ⟨work, present⟩ := Frame.source_coverageCanonical allocation trace completed history target held bounded
  have retained : Frame.run work (Frame.initialCanonical allocation) ∈
      (State.run work (State.beginCanonical allocations)).frames := by
    rw [State.run_frames]
    exact List.mem_map_of_mem (List.mem_map_of_mem member)
  exact ⟨work, (State.run_balanced work (State.beginCanonical_balanced allocations)).symm.subset
    (List.mem_flatMap.mpr ⟨_, retained, present⟩)⟩

#print axioms Frame.run_ordinary
#print axioms Frame.publication_ordinary
#print axioms Allocation.canonical_seed
#print axioms Frame.run_add
#print axioms Frame.fresh_balance
#print axioms State.run_balanced
#print axioms State.run_add
#print axioms State.log_prefix
#print axioms State.publication_source_sound
#print axioms State.source_coverage
#print axioms Frame.publication_canonical_valid
#print axioms Frame.source_coverageCanonical
#print axioms State.beginCanonical_balanced
#print axioms State.publication_canonical_valid
#print axioms State.source_coverageCanonical

/-- Installation selects genuine retained root matches, never completed states. -/
abbrev SeedProfile (matcher : MatchingExecution) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) :=
  (allocation : Allocation plan bound expected source) →
    RecursiveCollectionContinuation.RootSeed matcher allocation.request

def ordinarySeedProfile (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) :
    SeedProfile MatchingExecution.ordinary plan bound expected source :=
  fun allocation => RecursiveCollectionContinuation.ordinarySeed allocation.request

def canonicalSeedProfile (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) :
    SeedProfile canonicalMatchingExecution plan bound expected (CanonicalBags.canon source) :=
  fun allocation => RecursiveCollectionContinuation.canonicalSeed allocation.request allocation.canonical_seed

def Frame.initialWith (profile : SeedProfile matcher plan bound expected source)
    (allocation : Allocation plan bound expected source) : Frame plan bound expected source matcher :=
  ⟨allocation, RecursiveCollectionContinuation.startWithSeed matcher allocation.request (profile allocation)⟩

theorem Frame.initialWith_ordinary (allocation : Allocation plan bound expected source) :
    Frame.initialWith (ordinarySeedProfile plan bound expected source) allocation =
      Frame.initial allocation := rfl

theorem Frame.initialWith_canonical
    (allocation : Allocation plan bound expected (CanonicalBags.canon source)) :
    Frame.initialWith (canonicalSeedProfile plan bound expected source) allocation =
      Frame.initialCanonical allocation := rfl

theorem Frame.initialWith_publication (profile : SeedProfile matcher plan bound expected source)
    (allocation : Allocation plan bound expected source) :
    (Frame.initialWith profile allocation).publication = [] := by
  simp only [Frame.publication, Frame.initialWith, RecursiveCollectionContinuation.publicationIn,
    RecursiveCollectionContinuation.startWithSeed_no_early_answers, List.filterMap_nil, List.map_nil]

def State.beginWith (profile : SeedProfile matcher plan bound expected source)
    (allocations : List (Allocation plan bound expected source)) :
    State plan bound expected source matcher :=
  ⟨allocations.map (Frame.initialWith profile), []⟩

theorem State.beginWith_ordinary (allocations : List (Allocation plan bound expected source)) :
    State.beginWith (ordinarySeedProfile plan bound expected source) allocations =
      State.begin allocations := rfl

theorem State.beginWith_canonical
    (allocations : List (Allocation plan bound expected (CanonicalBags.canon source))) :
    State.beginWith (canonicalSeedProfile plan bound expected source) allocations =
      State.beginCanonical allocations := rfl

theorem State.beginWith_balanced (profile : SeedProfile matcher plan bound expected source)
    (allocations : List (Allocation plan bound expected source)) :
    (State.beginWith profile allocations).Balanced := by
  have empty : (allocations.map (Frame.initialWith profile)).flatMap Frame.publication = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro frame member
    obtain ⟨allocation, _, rfl⟩ := List.mem_map.mp member
    exact Frame.initialWith_publication profile allocation
  change [].Perm ((allocations.map (Frame.initialWith profile)).flatMap Frame.publication)
  rw [empty]

#print axioms Frame.initialWith_ordinary
#print axioms Frame.initialWith_canonical
#print axioms Frame.initialWith_publication
#print axioms State.beginWith_balanced

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceBatch

/-! Prefix observations retain their complete committed packets.
These readouts make no enumeration-completion assertion. -/

namespace Mettapedia.OSLF.MeTTaIL.CollectionCommittedObservation

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax CanonicalBags
open CollectionOccurrenceBatch GeneralPremise

abbrev Committed (Choice : Type := GeneralScopedMatchMachine.BagChoice) :=
  Publication Choice × GeneralRuleJobs.Receipt Choice

def commit? (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (packet : Publication) : Option Committed :=
  (packet.finish? plan bound expected).map fun receipt => (packet, receipt)

def retained (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (packets : List Publication) : List Committed :=
  packets.filterMap (commit? plan bound expected)

theorem retained_append (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (first second : List Publication) :
    retained plan bound expected (first ++ second) =
      retained plan bound expected first ++ retained plan bound expected second :=
  List.filterMap_append

theorem retained_perm (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) {first second : List Publication} (same : first.Perm second) :
    (retained plan bound expected first).Perm (retained plan bound expected second) :=
  same.filterMap (commit? plan bound expected)

theorem retained_receipts (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (packets : List Publication) :
    (retained plan bound expected packets).map Prod.snd =
      packets.filterMap (fun packet => packet.finish? plan bound expected) := by
  simp only [retained, List.map_filterMap]
  apply List.filterMap_congr
  intro packet _
  simp only [commit?]
  cases packet.finish? plan bound expected <;> rfl

theorem rejected_packet_erases (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (packet : Publication)
    (rejected : packet.finish? plan bound expected = none) :
    retained plan bound expected [packet] = [] := by
  simp [retained, commit?, rejected]

theorem frame_source_same {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (frame : Frame plan bound expected source)
    {packet : Publication} (published : packet ∈ frame.publication) :
    Same source (packet.job.presentedSource packet.prepared) := by
  obtain ⟨outcome, member, same⟩ := List.mem_map.mp published
  cases same
  exact CollectionOccurrenceHandoff.Job.source_same frame.allocation.licensed frame.allocation.matching

theorem retained_source_same {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {state : State plan bound expected source}
    (balanced : state.Balanced) {committed : Committed}
    (published : committed ∈ retained plan bound expected state.log) :
    Same source (committed.1.job.presentedSource committed.1.prepared) := by
  obtain ⟨packet, logged, made⟩ := List.mem_filterMap.mp published
  unfold commit? at made
  cases finished : packet.finish? plan bound expected with
  | none => simp only [finished, Option.map_none] at made; cases made
  | some receipt =>
      simp only [finished, Option.map_some, Option.some.injEq] at made
      cases made
      obtain ⟨frame, _, member⟩ := List.mem_flatMap.mp (balanced.subset logged)
      exact frame_source_same frame member

/-- Declared identity acts on already committed complete packet/receipt pairs.
It is supplied by the observer and does not replace the retained source list. -/
def committedKeys {Choice Key : Type} [DecidableEq Key] (identity : Committed Choice → Key)
    (committed : List (Committed Choice)) : Finset Key := (committed.map identity).toFinset

def committedBag {Choice Key Value : Type} [DecidableEq Key] (identity : Committed Choice → Key)
    (value : Key → Value) (committed : List (Committed Choice)) : Multiset Value :=
  (committedKeys identity committed).val.map value

def committedFacts {Choice Key Fact : Type} [DecidableEq Key] [DecidableEq Fact]
    (identity : Committed Choice → Key) (fact : Key → Fact)
    (committed : List (Committed Choice)) : Finset Fact := (committedKeys identity committed).image fact

theorem committedKeys_append {Choice Key : Type} [DecidableEq Key] (identity : Committed Choice → Key)
    (first second : List (Committed Choice)) :
    committedKeys identity (first ++ second) = committedKeys identity first ∪ committedKeys identity second := by
  simp only [committedKeys, List.map_append, List.toFinset_append]

theorem committedKeys_perm {Choice Key : Type} [DecidableEq Key] (identity : Committed Choice → Key)
    {first second : List (Committed Choice)} (same : first.Perm second) :
    committedKeys identity first = committedKeys identity second := by
  ext key
  simpa only [committedKeys, List.mem_toFinset] using List.Perm.mem_iff (same.map identity)

theorem committed_observation_perm {Choice Key Fact Value : Type} [DecidableEq Key] [DecidableEq Fact]
    (identity : Committed Choice → Key) (fact : Key → Fact) (value : Key → Value)
    {first second : List (Committed Choice)} (same : first.Perm second) :
    committedBag identity value first = committedBag identity value second ∧
      committedFacts identity fact first = committedFacts identity fact second := by
  simp only [committedBag, committedFacts, committedKeys_perm identity same, and_self]

/-- Replay is harmless precisely when it supplies no new declared key.
This does not impose an identity or erase any original packet. -/
theorem committed_observation_replay {Choice Key Fact Value : Type} [DecidableEq Key] [DecidableEq Fact]
    (identity : Committed Choice → Key) (fact : Key → Fact) (value : Key → Value)
    (earlier replay : List (Committed Choice))
    (already : committedKeys identity replay ⊆ committedKeys identity earlier) :
    committedBag identity value (earlier ++ replay) = committedBag identity value earlier ∧
      committedFacts identity fact (earlier ++ replay) = committedFacts identity fact earlier := by
  have same : committedKeys identity (earlier ++ replay) = committedKeys identity earlier := by
    rw [committedKeys_append, Finset.union_eq_left.mpr already]
  simp only [committedBag, committedFacts, same, and_self]

/-- Every observed fact has an actual retained pair as its projection witness.
Soundness of a particular fact interpretation remains an observer obligation. -/
theorem committedFacts_mem {Choice Key Fact : Type} [DecidableEq Key] [DecidableEq Fact]
    (identity : Committed Choice → Key) (fact : Key → Fact) (committed : List (Committed Choice))
    (observed : Fact) :
    observed ∈ committedFacts identity fact committed ↔
      ∃ pair ∈ committed, fact (identity pair) = observed := by
  simp only [committedFacts, committedKeys, Finset.mem_image, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨key, ⟨pair, member, same⟩, read⟩
    exact ⟨pair, member, same ▸ read⟩
  · rintro ⟨pair, member, read⟩
    exact ⟨identity pair, ⟨pair, member, rfl⟩, read⟩

def declaredKeys {Key : Type} [DecidableEq Key] (identity : Committed → Key)
    (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (packets : List Publication) : Finset Key :=
  committedKeys identity (retained plan bound expected packets)

def declaredBag {Key Value : Type} [DecidableEq Key] (identity : Committed → Key)
    (value : Key → Value) (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (packets : List Publication) : Multiset Value :=
  (declaredKeys identity plan bound expected packets).val.map value

def declaredFacts {Key Fact : Type} [DecidableEq Key] [DecidableEq Fact]
    (identity : Committed → Key) (fact : Key → Fact) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (packets : List Publication) : Finset Fact :=
  (declaredKeys identity plan bound expected packets).image fact

theorem declaredBag_committed {Key Value : Type} [DecidableEq Key] (identity : Committed → Key)
    (value : Key → Value) (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (packets : List Publication) :
    declaredBag identity value plan bound expected packets =
      committedBag identity value (retained plan bound expected packets) := rfl

theorem declaredFacts_committed {Key Fact : Type} [DecidableEq Key] [DecidableEq Fact]
    (identity : Committed → Key) (fact : Key → Fact) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (packets : List Publication) :
    declaredFacts identity fact plan bound expected packets =
      committedFacts identity fact (retained plan bound expected packets) := rfl

theorem declaredKeys_perm {Key : Type} [DecidableEq Key] (identity : Committed → Key)
    (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    {first second : List Publication} (same : first.Perm second) :
    declaredKeys identity plan bound expected first = declaredKeys identity plan bound expected second := by
  ext key
  simpa only [declaredKeys, committedKeys, List.mem_toFinset] using
    List.Perm.mem_iff ((retained_perm plan bound expected same).map identity)

theorem declared_observation_balance {Key Fact Value : Type} [DecidableEq Key] [DecidableEq Fact]
    (identity : Committed → Key) (fact : Key → Fact) (value : Key → Value)
    {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {state : State plan bound expected source}
    (balanced : state.Balanced) :
    declaredBag identity value plan bound expected state.log =
        declaredBag identity value plan bound expected (state.frames.flatMap Frame.publication) ∧
      declaredFacts identity fact plan bound expected state.log =
        declaredFacts identity fact plan bound expected (state.frames.flatMap Frame.publication) := by
  simp only [declaredBag, declaredFacts, declaredKeys_perm identity plan bound expected balanced, and_self]

theorem declaredKeys_append {Key : Type} [DecidableEq Key] (identity : Committed → Key)
    (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (first second : List Publication) :
    declaredKeys identity plan bound expected (first ++ second) =
      declaredKeys identity plan bound expected first ∪ declaredKeys identity plan bound expected second := by
  simp only [declaredKeys, committedKeys, retained_append, List.map_append, List.toFinset_append]

theorem declared_replay_invariant {Key Fact Value : Type} [DecidableEq Key] [DecidableEq Fact]
    (identity : Committed → Key) (fact : Key → Fact) (value : Key → Value)
    (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (earlier replay : List Publication)
    (already : declaredKeys identity plan bound expected replay ⊆
      declaredKeys identity plan bound expected earlier) :
    declaredBag identity value plan bound expected (earlier ++ replay) =
        declaredBag identity value plan bound expected earlier ∧
      declaredFacts identity fact plan bound expected (earlier ++ replay) =
        declaredFacts identity fact plan bound expected earlier := by
  have same : declaredKeys identity plan bound expected (earlier ++ replay) =
      declaredKeys identity plan bound expected earlier := by
    rw [declaredKeys_append, Finset.union_eq_left.mpr already]
  simp only [declaredBag, declaredFacts, same, and_self]

theorem frame_commit_balance {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (frame : Frame plan bound expected source) :
    retained plan bound expected frame.publication ++ retained plan bound expected frame.fresh =
      retained plan bound expected (Frame.run 1 frame).publication := by
  rw [← retained_append, Frame.fresh_balance]

/-- The selected receipt finisher is explicit and every successful pair keeps
its entire source packet, including the actual outcome. -/
def commitWith? {Choice : Type} (finish : Publication Choice → Option (GeneralRuleJobs.Receipt Choice))
    (packet : Publication Choice) : Option (Committed Choice) :=
  (finish packet).map fun receipt => (packet, receipt)

def retainedWith {Choice : Type} (finish : Publication Choice → Option (GeneralRuleJobs.Receipt Choice))
    (packets : List (Publication Choice)) : List (Committed Choice) := packets.filterMap (commitWith? finish)

theorem retainedWith_append {Choice : Type}
    (finish : Publication Choice → Option (GeneralRuleJobs.Receipt Choice))
    (first second : List (Publication Choice)) :
    retainedWith finish (first ++ second) = retainedWith finish first ++ retainedWith finish second :=
  List.filterMap_append

theorem retainedWith_ordinary (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (packets : List Publication) :
    retainedWith (fun packet => packet.finish? plan bound expected) packets = retained plan bound expected packets := rfl

def retainedCanonical (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (packets : List (Publication EquationalScopedReceipts.Event)) :
    List (Committed EquationalScopedReceipts.Event) :=
  retainedWith (fun packet => packet.finishCanonical? plan bound expected) packets

theorem retainedCanonical_keeps_packet (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (packets : List (Publication EquationalScopedReceipts.Event))
    {committed : Committed EquationalScopedReceipts.Event}
    (member : committed ∈ retainedCanonical plan bound expected packets) :
    committed.1 ∈ packets ∧ committed.1.finishCanonical? plan bound expected = some committed.2 := by
  obtain ⟨packet, logged, made⟩ := List.mem_filterMap.mp member
  unfold commitWith? at made
  cases finished : packet.finishCanonical? plan bound expected with
  | none => simp only [finished, Option.map_none] at made; cases made
  | some receipt =>
    simp only [finished, Option.map_some, Option.some.injEq] at made
    cases made
    exact ⟨logged, finished⟩

theorem retainedCanonical_valid {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (work : Nat)
    (allocations : List (Allocation plan bound expected (canon source)))
    {committed : Committed EquationalScopedReceipts.Event}
    (member : committed ∈ retainedCanonical plan bound expected
      (State.run work (State.beginCanonical allocations)).log) :
    committed.2.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation DynamicProvider.empty
      plan bound expected (committed.1.job.presentedSource committed.1.prepared) ∧
      Same source (committed.1.job.presentedSource committed.1.prepared) := by
  obtain ⟨logged, finished⟩ := retainedCanonical_keeps_packet _ _ _ _ member
  exact State.publication_canonical_valid work allocations logged finished

#print axioms committedKeys_append
#print axioms committedKeys_perm
#print axioms committed_observation_perm
#print axioms committed_observation_replay
#print axioms committedFacts_mem
#print axioms declaredBag_committed
#print axioms declaredFacts_committed
#print axioms declared_observation_balance
#print axioms declared_replay_invariant

#print axioms retainedWith_ordinary
#print axioms retainedCanonical_keeps_packet
#print axioms retainedCanonical_valid

end Mettapedia.OSLF.MeTTaIL.CollectionCommittedObservation
