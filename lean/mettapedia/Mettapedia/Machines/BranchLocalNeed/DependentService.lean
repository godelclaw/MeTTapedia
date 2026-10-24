import Mettapedia.Machines.BranchLocalNeed.CacheLaws
import Mettapedia.Machines.BranchLocalNeed.ExecutionMachine
import Mettapedia.TypeTheory.DisplayedEvidenceNeed
import Mettapedia.Machines.BranchLocalNeed.LocalSteps
import Mettapedia.Machines.BranchLocalNeed.InferenceControl
import Mettapedia.GSLT.LanguageDef.NativeControlCursor

/-!
# Dependent services on the reference Need machine

A service produces a reply in the family indexed by its complete immutable
request. Its first force uses the existing owned Need machine to evaluate and
commit a packed reply. A consumer resumes through that same machine, checks
the packet index, and only then exposes the reply at the requested fibre.
Subsequent demands observe the existing cache without invoking the producer.

The client supplies the full raw request, including any authority, revision,
context, and query coordinates on which its meaning depends. No key-only
sharing or transport across unequal requests is introduced. A finite check's
accepted and refused candidate outcomes can both be data in its reply family;
refusing a candidate is not a refutation of a logical proposition.

The producer is a total deterministic local action, not an unbounded search
oracle. The exact transition counts describe the surrounding Need protocol,
not the native cost of producing a reply. No evaluator or type profile is
replaced by this instance.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.NeedDependentService

open NeedReference
open Mettapedia.TypeTheory.DisplayedEvidence

universe uRaw uExact

variable (family : Family.{uRaw, uExact})

/-- Reuse the existing displayed-evidence packet, including its exact index. -/
abbrev Packet := Mettapedia.TypeTheory.DisplayedEvidenceNeed.PackedEvidence family

/-- An operational request mismatch, not a logical refutation. -/
structure IndexMismatch where
  expected : family.Raw
  actual : family.Raw

abbrev Outcome := Produced (Packet family) Empty (IndexMismatch family)

/-- Project only after the complete request indices agree. -/
def project? [DecidableEq family.Raw] (expected : family.Raw)
    (packet : Packet family) : Option (family.Exact expected) :=
  if same : packet.1 = expected then
    some (cast (congrArg family.Exact same) packet.2)
  else none

@[simp] theorem project?_matching [DecidableEq family.Raw]
    (request : family.Raw) (reply : family.Exact request) :
    project? family request ⟨request, reply⟩ = some reply := by
  simp [project?]

theorem project?_mismatched [DecidableEq family.Raw]
    {expected actual : family.Raw} (different : actual ≠ expected)
    (reply : family.Exact actual) :
    project? family expected ⟨actual, reply⟩ = none := by
  simp [project?, different]

/-- Successful projection retains the exact dependent packet, not only its tag. -/
theorem project?_sound [DecidableEq family.Raw]
    {expected : family.Raw} {packet : Packet family} {reply : family.Exact expected}
    (projected : project? family expected packet = some reply) :
    packet = ⟨expected, reply⟩ := by
  rcases packet with ⟨actual, value⟩
  unfold project? at projected
  split at projected
  · rename_i same
    change actual = expected at same
    subst actual
    simp only [cast_eq, Option.some.injEq] at projected
    subst reply
    rfl
  · cases projected

/-- A resumed consumer validates the packet before returning its dependent reply. -/
def consumeOutcome [DecidableEq family.Raw] (expected : family.Raw) :
    Outcome family → Outcome family
  | .value packet =>
      match project? family expected packet with
      | some reply => .value ⟨expected, reply⟩
      | none => .retryableFault (.domain ⟨expected, packet.1⟩)
  | .stableFault impossible => nomatch impossible
  | .retryableFault reason => .retryableFault reason

@[simp] theorem consumeOutcome_matching [DecidableEq family.Raw]
    (request : family.Raw) (reply : family.Exact request) :
    consumeOutcome family request (.value ⟨request, reply⟩) =
      .value ⟨request, reply⟩ := by
  simp [consumeOutcome]

theorem consumeOutcome_mismatched [DecidableEq family.Raw]
    {expected actual : family.Raw} (different : actual ≠ expected)
    (reply : family.Exact actual) :
    consumeOutcome family expected (.value ⟨actual, reply⟩) =
      .retryableFault (.domain ⟨expected, actual⟩) := by
  simp [consumeOutcome, project?_mismatched family different reply]

inductive Rule where
  | produce
  deriving DecidableEq, Repr

/-- Service entry and consumption are states of the existing Need machine. -/
inductive Local where
  | produce (request : family.Raw)
  | demand (expected : family.Raw) (cell : CellId)
  | output (outcome : Outcome family)

abbrev ServiceWorld :=
  World family.Raw Rule (Packet family) Empty (IndexMismatch family) Empty

abbrev ServiceMachine :=
  Machine family.Raw (Local family) family.Raw Rule (Packet family) Empty
    (IndexMismatch family) Empty

/-- The only producer invocation is the local `produce` action. The core
machine owns allocation, the evaluating owner, commit, cache lookup and receipts. -/
def spec [DecidableEq family.Raw] (producer : (request : family.Raw) → family.Exact request) :
    Spec family.Raw (Local family) family.Raw Rule (Packet family) Empty
      (IndexMismatch family) Empty where
  alternatives request := [(.produce, .produce request)]
  action
    | .produce request => .done (.value ⟨request, producer request⟩)
    | .demand expected cell => .demand cell expected
    | .output outcome => .done outcome
  afterDemand expected outcome := .output (consumeOutcome family expected outcome)
  afterAllocation expected cell := .demand expected cell

/-- The exact world at the unique suspended-force successor. -/
def forceWorld (world : ServiceWorld family) (cell : CellId) (request : family.Raw) :
    ServiceWorld family :=
  let base := { world with nextEvaluator := world.nextEvaluator + 1 }
  recorded
    (recorded
      ((base.fork 0).setKnownCache cell ⟨request, .suspended⟩
        (.evaluating world.nextEvaluator))
      (.evaluate cell world.nextEvaluator))
    (.chooseRule cell .produce)

/-- The exact owner-matched commit-and-observe world. -/
def commitWorld (world : ServiceWorld family) (cell : CellId) (request : family.Raw)
    (owner : EvaluatorId) (packet : Packet family) : ServiceWorld family :=
  recorded (world.setKnownCache cell ⟨request, .evaluating owner⟩ (.value packet))
    (.observe cell (.value packet))

def producedWorld (producer : (request : family.Raw) → family.Exact request)
    (world : ServiceWorld family) (cell : CellId) (request : family.Raw) :
    ServiceWorld family :=
  commitWorld family (forceWorld family world cell request) cell request world.nextEvaluator
    ⟨request, producer request⟩

def freshForceWork (work : Work) : Work :=
  ((work.bump 1 1 2 0).bump 0 0 0 0).bump 1 1 1 0

def consumerFinishWork (work : Work) : Work :=
  ((work.bump 0 0 0 0).bump 0 0 0 0).bump 0 0 0 0

@[simp] theorem forceWorld_lookup (world : ServiceWorld family) (cell : CellId)
    (request : family.Raw) :
    (forceWorld family world cell request).heap.lookup cell =
      some ⟨request, .evaluating world.nextEvaluator⟩ := by
  simp only [forceWorld, NeedCacheLaws.recorded_heap, World.setKnownCache,
    Heap.setKnownCache_lookup_same]

@[simp] theorem producedWorld_lookup
    (producer : (request : family.Raw) → family.Exact request)
    (world : ServiceWorld family) (cell : CellId) (request : family.Raw) :
    (producedWorld family producer world cell request).heap.lookup cell =
      some ⟨request, .value ⟨request, producer request⟩⟩ := by
  simp only [producedWorld, commitWorld, NeedCacheLaws.recorded_heap,
    World.setKnownCache, Heap.setKnownCache_lookup_same]

section Runs

variable [DecidableEq family.Raw]
    (producer : (request : family.Raw) → family.Exact request)

theorem step_force_suspended {world : ServiceWorld family} {cell : CellId}
    {request : family.Raw} {stack : List (Frame family.Raw)} {work : Work}
    (suspended : world.heap.lookup cell = some ⟨request, .suspended⟩) :
    step (spec family producer) (⟨world, .force cell stack, work⟩ : ServiceMachine family) =
      [⟨forceWorld family world cell request,
        .run (.produce request) (.commit cell world.nextEvaluator :: stack),
        work.bump 1 1 2 0⟩] := by
  simp [step, spec, suspended, branchAlternatives, forceWorld, finished]

theorem step_produce (world : ServiceWorld family) (request : family.Raw)
    (stack : List (Frame family.Raw)) (work : Work) :
    step (spec family producer) (⟨world, .run (.produce request) stack, work⟩ :
      ServiceMachine family) =
      [⟨world, .returned (.value ⟨request, producer request⟩) stack,
        work.bump 0 0 0 0⟩] := rfl

theorem step_commit {world : ServiceWorld family} {cell : CellId} {request : family.Raw}
    {owner : EvaluatorId} {packet : Packet family} {stack : List (Frame family.Raw)}
    {work : Work} (owned : world.heap.lookup cell = some ⟨request, .evaluating owner⟩) :
    step (spec family producer)
      (⟨world, .returned (.value packet) (.commit cell owner :: stack), work⟩ :
        ServiceMachine family) =
      [⟨commitWorld family world cell request owner packet,
        .returned (.value packet) stack, work.bump 1 1 1 0⟩] := by
  simp [step, owned, commitWorld, finished]

/-- Every suspended service cell returns and caches the exact producer packet
in three actual machine transitions, under an arbitrary continuation stack. -/
theorem fresh_force_returns {world : ServiceWorld family} {cell : CellId}
    {request : family.Raw} (stack : List (Frame family.Raw)) (work : Work)
    (suspended : world.heap.lookup cell = some ⟨request, .suspended⟩) :
    UniqueSteps (spec family producer) 3
      (⟨world, .force cell stack, work⟩ : ServiceMachine family)
      ⟨producedWorld family producer world cell request,
        .returned (.value ⟨request, producer request⟩) stack, freshForceWork work⟩ := by
  apply UniqueSteps.cons (step_force_suspended family producer suspended)
  apply UniqueSteps.cons (step_produce family producer _ _ _ _)
  apply UniqueSteps.cons (step_commit family producer (forceWorld_lookup family world cell request))
  exact UniqueSteps.refl _

/-- Forcing an already cached reply observes it in one transition. In
particular the producer and its local action are not invoked. -/
theorem cached_force_returns {world : ServiceWorld family} {cell : CellId}
    {origin : family.Raw} {packet : Packet family}
    (stack : List (Frame family.Raw)) (work : Work)
    (cached : world.heap.lookup cell = some ⟨origin, .value packet⟩) :
    UniqueSteps (spec family producer) 1
      (⟨world, .force cell stack, work⟩ : ServiceMachine family)
      ⟨recorded world (.observe cell (.value packet)),
        .returned (.value packet) stack, work.bump 1 0 1 0⟩ := by
  apply UniqueSteps.cons
    (NeedCacheLaws.force_cached_value_step (spec family producer) _ rfl cached)
  exact UniqueSteps.refl _

/-- The consumer index check is executed by the machine's resume path. -/
theorem resume_and_halt (world : ServiceWorld family) (expected : family.Raw)
    (outcome : Outcome family) (work : Work) :
    UniqueSteps (spec family producer) 3
      (⟨world, .returned outcome [.resume expected], work⟩ : ServiceMachine family)
      ⟨world, .halted (consumeOutcome family expected outcome), consumerFinishWork work⟩ := by
  apply UniqueSteps.cons (by rfl)
  apply UniqueSteps.cons (by rfl)
  apply UniqueSteps.cons (by rfl)
  exact UniqueSteps.refl _

/-- A first demanded consumer checks, caches, projects and returns the reply. -/
theorem fresh_consumer_run {world : ServiceWorld family} {cell : CellId}
    {request : family.Raw} (work : Work)
    (suspended : world.heap.lookup cell = some ⟨request, .suspended⟩) :
    UniqueSteps (spec family producer) 7
      (⟨world, .run (.demand request cell) [], work⟩ : ServiceMachine family)
      ⟨producedWorld family producer world cell request,
        .halted (.value ⟨request, producer request⟩),
        consumerFinishWork (freshForceWork (work.bump 0 0 0 0))⟩ := by
  apply UniqueSteps.cons (by rfl)
  have forced := fresh_force_returns family producer [.resume request]
    (work.bump 0 0 0 0) suspended
  have resumed := resume_and_halt family producer
    (producedWorld family producer world cell request) request
    (.value ⟨request, producer request⟩) (freshForceWork (work.bump 0 0 0 0))
  simpa only [consumeOutcome_matching, finished] using
    UniqueSteps.trans (spec family producer) forced resumed

/-- All cached consumer outcomes are exact, including request-index failures. -/
theorem cached_consumer_run {world : ServiceWorld family} {cell : CellId}
    {origin : family.Raw} {packet : Packet family} (expected : family.Raw) (work : Work)
    (cached : world.heap.lookup cell = some ⟨origin, .value packet⟩) :
    UniqueSteps (spec family producer) 5
      (⟨world, .run (.demand expected cell) [], work⟩ : ServiceMachine family)
      ⟨recorded world (.observe cell (.value packet)),
        .halted (consumeOutcome family expected (.value packet)),
        consumerFinishWork ((work.bump 0 0 0 0).bump 1 0 1 0)⟩ := by
  apply UniqueSteps.cons (by rfl)
  apply UniqueSteps.trans (rightLength := 2) (spec family producer)
    (NeedCacheLaws.force_cached_value_resume (spec family producer) world cell expected []
      (work.bump 0 0 0 0) cached)
  apply UniqueSteps.cons (by rfl)
  apply UniqueSteps.cons (by rfl)
  exact UniqueSteps.refl _

/-- Exact frontier equality for a first consumer demand, not only reachability. -/
theorem fresh_consumer_runFrontier {world : ServiceWorld family} {cell : CellId}
    {request : family.Raw} (work : Work)
    (suspended : world.heap.lookup cell = some ⟨request, .suspended⟩) :
    runFrontier (spec family producer) 7
      [(⟨world, .run (.demand request cell) [], work⟩ : ServiceMachine family)] =
      [⟨producedWorld family producer world cell request,
        .halted (.value ⟨request, producer request⟩),
        consumerFinishWork (freshForceWork (work.bump 0 0 0 0))⟩] :=
  UniqueSteps.runFrontier_eq (spec family producer)
    (fresh_consumer_run family producer work suspended)

theorem cached_consumer_runFrontier {world : ServiceWorld family} {cell : CellId}
    {origin : family.Raw} {packet : Packet family} (expected : family.Raw) (work : Work)
    (cached : world.heap.lookup cell = some ⟨origin, .value packet⟩) :
    runFrontier (spec family producer) 5
      [(⟨world, .run (.demand expected cell) [], work⟩ : ServiceMachine family)] =
      [⟨recorded world (.observe cell (.value packet)),
        .halted (consumeOutcome family expected (.value packet)),
        consumerFinishWork ((work.bump 0 0 0 0).bump 1 0 1 0)⟩] :=
  UniqueSteps.runFrontier_eq (spec family producer)
    (cached_consumer_run family producer expected work cached)

/-- A cached packet from another complete request is not silently projected. -/
theorem mismatched_consumer_run {world : ServiceWorld family} {cell : CellId}
    {origin expected actual : family.Raw} (reply : family.Exact actual) (work : Work)
    (different : actual ≠ expected)
    (cached : world.heap.lookup cell = some ⟨origin, .value ⟨actual, reply⟩⟩) :
    runFrontier (spec family producer) 5
      [(⟨world, .run (.demand expected cell) [], work⟩ : ServiceMachine family)] =
      [⟨recorded world (.observe cell (.value ⟨actual, reply⟩)),
        .halted (.retryableFault (.domain ⟨expected, actual⟩)),
        consumerFinishWork ((work.bump 0 0 0 0).bump 1 0 1 0)⟩] := by
  simpa only [consumeOutcome_mismatched family different reply] using
    cached_consumer_runFrontier family producer expected work cached

/-- Completed packets remain unchanged through every subsequent execution. -/
theorem completed_packet_retained {length : Nat} {initial final : ServiceMachine family}
    (execution : Steps (spec family producer) length initial final)
    {cell : CellId} {origin : family.Raw} {packet : Packet family}
    (cached : initial.world.heap.lookup cell = some ⟨origin, .value packet⟩) :
    final.world.heap.lookup cell = some ⟨origin, .value packet⟩ :=
  NeedCacheLaws.steps_preserve_completed (spec family producer) execution cached (.value packet)

/-- The answer-only execution carrier inherits the exact service answer bag. -/
theorem answers_erasure (fuel : Nat) (machine : ServiceMachine family) :
    NeedExecution.answers (spec family producer) fuel
        (NeedExecution.eraseMachine machine) =
      answers (spec family producer) fuel machine :=
  NeedExecution.answers_commute (spec family producer) fuel machine

end Runs

/-- Cached consumption is independent of the producer function. This is the
saved-invocation boundary, not a constant-time native checking claim. -/
theorem cached_consumer_independent_of_producer [DecidableEq family.Raw]
    (first second : (request : family.Raw) → family.Exact request)
    {world : ServiceWorld family} {cell : CellId} {origin : family.Raw}
    {packet : Packet family} (expected : family.Raw) (work : Work)
    (cached : world.heap.lookup cell = some ⟨origin, .value packet⟩) :
    runFrontier (spec family first) 5
        [(⟨world, .run (.demand expected cell) [], work⟩ : ServiceMachine family)] =
      runFrontier (spec family second) 5
        [(⟨world, .run (.demand expected cell) [], work⟩ : ServiceMachine family)] := by
  rw [cached_consumer_runFrontier family first expected work cached,
    cached_consumer_runFrontier family second expected work cached]

#print axioms project?_sound
#print axioms project?_mismatched
#print axioms fresh_force_returns
#print axioms fresh_consumer_runFrontier
#print axioms cached_consumer_runFrontier
#print axioms mismatched_consumer_run
#print axioms completed_packet_retained
#print axioms answers_erasure
#print axioms cached_consumer_independent_of_producer

end Mettapedia.Machines.BranchLocalNeed.NeedDependentService

/-! ## Selected source alternatives

This finite admission view inspects the existing suspended-force operation.
It retains the actual source record, evaluator, return stack and physical
alternative ordinal. It does not evaluate a body or identify empty admission
with successful producer exhaustion. The indexed packet below is a finite
admission result, not the eventual answer set of a searched service.
-/
namespace Mettapedia.Machines.BranchLocalNeed.NeedDependentService.SourceBranch

open NeedReference
open Mettapedia.TypeTheory.DisplayedEvidence

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type}

abbrev SourceMachine := Machine Origin Local Resume Rule Value StableFault RetryableFault Effect

structure Selection (Origin Local Resume Rule Value StableFault : Type) where
  cell : CellId
  record : CellRecord Origin Value StableFault
  evaluator : EvaluatorId
  returns : List (Frame Resume)
  ordinal : Nat
  rule : Rule
  state : Local

variable (specification : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)

/-- The validity judgment mentions the independently defined source control,
lookup and alternative list, rather than an equality to an inspector result. -/
structure Admitted (source : SourceMachine (Origin := Origin) (Local := Local) (Resume := Resume)
    (Rule := Rule) (Value := Value) (StableFault := StableFault)
    (RetryableFault := RetryableFault) (Effect := Effect)) (ordinal : Nat)
    (selection : Selection Origin Local Resume Rule Value StableFault) : Prop where
  control : source.control = .force selection.cell selection.returns
  lookup : source.world.heap.lookup selection.cell = some selection.record
  suspended : selection.record.cache = .suspended
  evaluator : selection.evaluator = source.world.nextEvaluator
  position : selection.ordinal = ordinal
  alternative : (specification.alternatives selection.record.origin)[ordinal]? =
    some (selection.rule, selection.state)

def inspectAt (heap : Heap Origin Value StableFault) (evaluator : EvaluatorId)
    (control : Control Local Resume Value StableFault RetryableFault) (ordinal : Nat) :
    Option (Selection Origin Local Resume Rule Value StableFault) :=
  match control with
  | .force cell returns =>
      (heap.lookup cell).bind fun record => match record.cache with
      | .suspended => ((specification.alternatives record.origin)[ordinal]?).map fun (rule, state) =>
          ⟨cell, record, evaluator, returns, ordinal, rule, state⟩
      | _ => none
  | _ => none

def inspect (source : SourceMachine (Origin := Origin) (Local := Local) (Resume := Resume)
    (Rule := Rule) (Value := Value) (StableFault := StableFault)
    (RetryableFault := RetryableFault) (Effect := Effect)) (ordinal : Nat) :
    Option (Selection Origin Local Resume Rule Value StableFault) :=
  inspectAt specification source.world.heap source.world.nextEvaluator source.control ordinal

/-- Receipt selection changes no datum used by source admission. This view
reads actual control and heap; it does not fabricate a full source world. -/
def inspectCore (source : NeedExecution.CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (ordinal : Nat) : Option (Selection Origin Local Resume Rule Value StableFault) :=
  inspectAt specification source.world.heap source.world.nextEvaluator source.control ordinal

theorem inspectCore_project (keepReceipts : Bool)
    (source : SourceMachine (Origin := Origin) (Local := Local) (Resume := Resume)
      (Rule := Rule) (Value := Value) (StableFault := StableFault)
      (RetryableFault := RetryableFault) (Effect := Effect)) (ordinal : Nat) :
    inspectCore specification (NeedExecution.projectMachine keepReceipts source) ordinal =
      inspect specification source ordinal := rfl

/-- The executable reader constructs genuine source admission evidence. -/
theorem inspect_sound {source : SourceMachine (Origin := Origin) (Local := Local) (Resume := Resume)
    (Rule := Rule) (Value := Value) (StableFault := StableFault)
    (RetryableFault := RetryableFault) (Effect := Effect)} {ordinal : Nat}
    {selection : Selection Origin Local Resume Rule Value StableFault}
    (selected : inspect specification source ordinal = some selection) :
    Admitted specification source ordinal selection := by
  cases control : source.control with
  | run state returns => simp only [inspect, inspectAt, control] at selected; cases selected
  | returned outcome returns => simp only [inspect, inspectAt, control] at selected; cases selected
  | halted outcome => simp only [inspect, inspectAt, control] at selected; cases selected
  | force cell returns =>
      cases found : source.world.heap.lookup cell with
      | none => simp only [inspect, inspectAt, control, found, Option.bind_none] at selected; cases selected
      | some record =>
          cases cache : record.cache <;> simp only [inspect, inspectAt, control, found, Option.bind_some, cache] at selected
          case evaluating owner => cases selected
          case value value => cases selected
          case stableFault fault => cases selected
          case suspended =>
            cases alternative : (specification.alternatives record.origin)[ordinal]? with
            | none => simp only [alternative, Option.map_none] at selected; cases selected
            | some choice =>
                rcases choice with ⟨rule, state⟩
                simp only [alternative, Option.map_some, Option.some.injEq] at selected
                subst selection
                exact ⟨control, found, cache, rfl, rfl, alternative⟩

/-- Conversely every admitted physical alternative is recognized with its
full source record and exact continuation. -/
theorem inspect_complete {source : SourceMachine (Origin := Origin) (Local := Local) (Resume := Resume)
    (Rule := Rule) (Value := Value) (StableFault := StableFault)
    (RetryableFault := RetryableFault) (Effect := Effect)} {ordinal : Nat}
    {selection : Selection Origin Local Resume Rule Value StableFault}
    (admitted : Admitted specification source ordinal selection) :
    inspect specification source ordinal = some selection := by
  rcases selection with ⟨cell, record, evaluator, returns, position, rule, state⟩
  obtain ⟨control, found, cache, owner, place, alternative⟩ := admitted
  dsimp only at control found cache owner place alternative
  simp only [inspect, inspectAt, control, found, Option.bind_some, cache, alternative, Option.map_some]
  cases owner
  cases place
  rfl

/-- A selected alternative excludes the separate no-rule branch. The actual
Need instruction retains the entire ordered successor family, not only this
one selected member. -/
theorem admitted_step {source : SourceMachine (Origin := Origin) (Local := Local) (Resume := Resume)
    (Rule := Rule) (Value := Value) (StableFault := StableFault)
    (RetryableFault := RetryableFault) (Effect := Effect)} {ordinal : Nat}
    {selection : Selection Origin Local Resume Rule Value StableFault}
    (admitted : Admitted specification source ordinal selection) :
    NeedReference.step specification source =
      branchAlternatives source { source.world with nextEvaluator := source.world.nextEvaluator + 1 }
        selection.cell selection.record source.world.nextEvaluator selection.returns 0
        (specification.alternatives selection.record.origin) := by
  have nonempty : specification.alternatives selection.record.origin ≠ [] := by
    intro empty
    have selected := admitted.alternative
    rw [empty] at selected
    cases selected
  simp only [NeedReference.step, admitted.control, admitted.lookup, admitted.suspended]

/-- The selected physical branch installs the real cache owner and commit
frame. Its world includes the engine's evaluation and choice receipts. -/
def realize (source : SourceMachine (Origin := Origin) (Local := Local) (Resume := Resume)
    (Rule := Rule) (Value := Value) (StableFault := StableFault)
    (RetryableFault := RetryableFault) (Effect := Effect))
    (selection : Selection Origin Local Resume Rule Value StableFault) :
    SourceMachine (Origin := Origin) (Local := Local) (Resume := Resume) (Rule := Rule)
      (Value := Value) (StableFault := StableFault) (RetryableFault := RetryableFault) (Effect := Effect) :=
  let base := { source.world with nextEvaluator := source.world.nextEvaluator + 1 }
  let world := (base.fork selection.ordinal).setKnownCache selection.cell selection.record
    (.evaluating selection.evaluator)
  let world := recorded world (.evaluate selection.cell selection.evaluator)
  let world := recorded world (.chooseRule selection.cell selection.rule)
  finished source world (.run selection.state (.commit selection.cell selection.evaluator :: selection.returns)) 1 1 2 0

private theorem branch_at
    (source : SourceMachine (Origin := Origin) (Local := Local) (Resume := Resume)
      (Rule := Rule) (Value := Value) (StableFault := StableFault)
      (RetryableFault := RetryableFault) (Effect := Effect))
    (base : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault) (owner : EvaluatorId)
    (returns : List (Frame Resume)) (rule : Rule) (state : Local)
    (alternatives : List (Rule × Local)) (offset ordinal : Nat)
    (selected : alternatives[ordinal]? = some (rule, state)) :
    (branchAlternatives source base cell record owner returns offset alternatives)[ordinal]? =
      some (finished source
        (recorded (recorded ((base.fork (offset + ordinal)).setKnownCache cell record (.evaluating owner))
          (.evaluate cell owner)) (.chooseRule cell rule))
        (.run state (.commit cell owner :: returns)) 1 1 2 0) := by
  induction alternatives generalizing offset ordinal with
  | nil => simp only [List.getElem?_nil] at selected; cases selected
  | cons first rest ih =>
      cases ordinal with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
          subst first
          rfl
      | succ ordinal =>
          simp only [List.getElem?_cons_succ] at selected
          simp only [branchAlternatives, List.getElem?_cons_succ]
          have next := ih (offset + 1) ordinal selected
          have position : (offset + 1) + ordinal = offset + (ordinal + 1) := by omega
          simpa only [position] using next

/-- Exact positional readback links admission to the actual successor list.
It preserves the selected owner, full body and stack, rather than just the
existence of a body with an equal final answer. -/
theorem admitted_transition {source : SourceMachine (Origin := Origin) (Local := Local) (Resume := Resume)
    (Rule := Rule) (Value := Value) (StableFault := StableFault)
    (RetryableFault := RetryableFault) (Effect := Effect)} {ordinal : Nat}
    {selection : Selection Origin Local Resume Rule Value StableFault}
    (admitted : Admitted specification source ordinal selection) :
    (NeedReference.step specification source)[ordinal]? = some (realize source selection) := by
  rw [admitted_step specification admitted]
  simpa only [realize, admitted.evaluator, admitted.position, Nat.zero_add] using
    branch_at source { source.world with nextEvaluator := source.world.nextEvaluator + 1 }
      selection.cell selection.record source.world.nextEvaluator selection.returns selection.rule selection.state
      (specification.alternatives selection.record.origin) 0 ordinal admitted.alternative

/-- The source admission family keeps the complete request, including the
original source world and physical ordinal, in its index. -/
def family : Family where
  Raw := SourceMachine (Origin := Origin) (Local := Local) (Resume := Resume)
    (Rule := Rule) (Value := Value) (StableFault := StableFault)
    (RetryableFault := RetryableFault) (Effect := Effect) × Nat
  Exact request := Option { selected : Selection Origin Local Resume Rule Value StableFault //
    Admitted specification request.1 request.2 selected }

/-- A checked finite-admission reply is available without deciding equality
of arbitrary captured closures or worlds. -/
def checked (source : SourceMachine (Origin := Origin) (Local := Local) (Resume := Resume)
    (Rule := Rule) (Value := Value) (StableFault := StableFault)
    (RetryableFault := RetryableFault) (Effect := Effect)) (ordinal : Nat) :
    (family specification).Exact (source, ordinal) :=
  match selected : inspect specification source ordinal with
  | none => none
  | some selection => some ⟨selection, inspect_sound specification selected⟩

/-- Packing adds the real request index; successful unpacking never substitutes
another source world or another ordinal. -/
def packet (source : SourceMachine (Origin := Origin) (Local := Local) (Resume := Resume)
    (Rule := Rule) (Value := Value) (StableFault := StableFault)
    (RetryableFault := RetryableFault) (Effect := Effect)) (ordinal : Nat) :
    NeedDependentService.Packet (family specification) :=
  ⟨(source, ordinal), checked specification source ordinal⟩

end Mettapedia.Machines.BranchLocalNeed.NeedDependentService.SourceBranch

/-! ## Retained source inventories

One poll delegates to the existing occurrence controller. A yielded item keeps
its own selected-machine observation, while the provider state retains every
other branch world. Exhaustion is checked against the complete inventory.
This wrapper neither runs a body to completion nor computes cardinality.
-/
namespace Mettapedia.Machines.BranchLocalNeed.NeedDependentService.Retained

open NeedReference
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.LanguageDef

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect Observation : Type}

abbrev Machine := NeedReference.Machine Origin Local Resume Rule Value StableFault RetryableFault Effect
abbrev Node := WorkOccurrence (Machine (Origin := Origin) (Local := Local) (Resume := Resume)
  (Rule := Rule) (Value := Value) (StableFault := StableFault)
  (RetryableFault := RetryableFault) (Effect := Effect))
abbrev Answer := Produced Value StableFault RetryableFault
abbrev Inventory := Mettapedia.GSLT.Core.InferenceControl.Snapshot
  (Node (Origin := Origin) (Local := Local) (Resume := Resume) (Rule := Rule) (Value := Value)
    (StableFault := StableFault) (RetryableFault := RetryableFault) (Effect := Effect))
  (Answer (Value := Value) (StableFault := StableFault) (RetryableFault := RetryableFault) × WorldPath) Nat

variable (advance : Machine (Origin := Origin) (Local := Local) (Resume := Resume) (Rule := Rule)
  (Value := Value) (StableFault := StableFault) (RetryableFault := RetryableFault) (Effect := Effect) →
    List (Machine (Origin := Origin) (Local := Local) (Resume := Resume) (Rule := Rule)
      (Value := Value) (StableFault := StableFault) (RetryableFault := RetryableFault) (Effect := Effect)))

def system : BranchingSystem
    (Node (Origin := Origin) (Local := Local) (Resume := Resume) (Rule := Rule) (Value := Value)
      (StableFault := StableFault) (RetryableFault := RetryableFault) (Effect := Effect))
    (Answer (Value := Value) (StableFault := StableFault) (RetryableFault := RetryableFault) × WorldPath) :=
  WorkOccurrence.lift ⟨haltedOutcome, advance⟩

variable (controller : Controller
  (Node (Origin := Origin) (Local := Local) (Resume := Resume) (Rule := Rule) (Value := Value)
    (StableFault := StableFault) (RetryableFault := RetryableFault) (Effect := Effect))
  (Answer (Value := Value) (StableFault := StableFault) (RetryableFault := RetryableFault) × WorldPath) Nat)
  (observe : Machine (Origin := Origin) (Local := Local) (Resume := Resume) (Rule := Rule)
    (Value := Value) (StableFault := StableFault) (RetryableFault := RetryableFault) (Effect := Effect) → Observation)

/-- A source-specific world readout travels with the actual emitted branch.
The remaining inventory lives separately in the retained provider state. -/
def pull (inventory : Inventory (Origin := Origin) (Local := Local) (Resume := Resume) (Rule := Rule)
    (Value := Value) (StableFault := StableFault) (RetryableFault := RetryableFault) (Effect := Effect)) :
    HostCalls.Pull (Inventory (Origin := Origin) (Local := Local) (Resume := Resume) (Rule := Rule)
      (Value := Value) (StableFault := StableFault) (RetryableFault := RetryableFault) (Effect := Effect))
      (Answer (Value := Value) (StableFault := StableFault) (RetryableFault := RetryableFault) × WorldPath × Observation) :=
  match Mettapedia.GSLT.Core.InferenceControl.Snapshot.selected controller inventory with
  | none => .done
  | some node =>
      let reached := Mettapedia.GSLT.Core.InferenceControl.Snapshot.tick (system advance) controller inventory
      match haltedOutcome node.state with
      | none => .suspend reached
      | some outcome => .yield (outcome, node.trace, observe node.state) reached

def provider : Mettapedia.Machines.Cursor.Provider
    (NativeControlCursor.protocol
      (Answer (Value := Value) (StableFault := StableFault) (RetryableFault := RetryableFault) × WorldPath × Observation)) :=
  NativeControlCursor.provider (pull advance controller observe)

/-- Scheduler rearrangement preserves the complete occurrence inventory.
It therefore cannot manufacture a successful exhaustion reply. -/
theorem selected_none_iff (inventory : Inventory (Origin := Origin) (Local := Local) (Resume := Resume)
    (Rule := Rule) (Value := Value) (StableFault := StableFault)
    (RetryableFault := RetryableFault) (Effect := Effect)) :
    Mettapedia.GSLT.Core.InferenceControl.Snapshot.selected controller inventory = none ↔
      inventory.search.frontier = [] := by
  have sameLength := ((controller.scheduler inventory.memory).reorder_complete
    inventory.search.frontier).length_eq
  cases ordered : (controller.scheduler inventory.memory).reorder inventory.search.frontier with
  | nil =>
      have empty : inventory.search.frontier = [] := by
        rw [ordered] at sameLength
        exact List.length_eq_zero_iff.mp sameLength.symm
      change ((controller.scheduler inventory.memory).reorder inventory.search.frontier).head? = none ↔
        inventory.search.frontier = []
      rw [ordered]
      exact ⟨fun _ => empty, fun _ => rfl⟩
  | cons node rest =>
      have nonempty : inventory.search.frontier ≠ [] := by
        intro empty
        rw [ordered, empty] at sameLength
        simp only [List.length_cons, List.length_nil] at sameLength
        omega
      simp only [Mettapedia.GSLT.Core.InferenceControl.Snapshot.selected, selected, ordered,
        List.head?_cons, Option.some_ne_none, nonempty]

/-- An unfinished selected node suspends with its actual progressed inventory.
The full residual cannot be replaced by an empty successful collection. -/
theorem unfinished_poll (inventory : Inventory (Origin := Origin) (Local := Local) (Resume := Resume)
    (Rule := Rule) (Value := Value) (StableFault := StableFault)
    (RetryableFault := RetryableFault) (Effect := Effect))
    (node : Node (Origin := Origin) (Local := Local) (Resume := Resume) (Rule := Rule) (Value := Value)
      (StableFault := StableFault) (RetryableFault := RetryableFault) (Effect := Effect))
    (chosen : Mettapedia.GSLT.Core.InferenceControl.Snapshot.selected controller inventory = some node)
    (unfinished : haltedOutcome node.state = none) :
    pull advance controller observe inventory =
      .suspend (Mettapedia.GSLT.Core.InferenceControl.Snapshot.tick (system advance) controller inventory) := by
  simp only [pull, chosen, unfinished]

/-- A returned fault and a returned value have the same occurrence retention.
The chosen observation is read from that exact branch, not another world. -/
theorem returned_poll (inventory : Inventory (Origin := Origin) (Local := Local) (Resume := Resume)
    (Rule := Rule) (Value := Value) (StableFault := StableFault)
    (RetryableFault := RetryableFault) (Effect := Effect))
    (node : Node (Origin := Origin) (Local := Local) (Resume := Resume) (Rule := Rule) (Value := Value)
      (StableFault := StableFault) (RetryableFault := RetryableFault) (Effect := Effect))
    (outcome : Answer (Value := Value) (StableFault := StableFault) (RetryableFault := RetryableFault))
    (chosen : Mettapedia.GSLT.Core.InferenceControl.Snapshot.selected controller inventory = some node)
    (returned : haltedOutcome node.state = some outcome) :
    pull advance controller observe inventory =
      .yield (outcome, node.trace, observe node.state)
        (Mettapedia.GSLT.Core.InferenceControl.Snapshot.tick (system advance) controller inventory) := by
  simp only [pull, chosen, returned]

end Mettapedia.Machines.BranchLocalNeed.NeedDependentService.Retained
