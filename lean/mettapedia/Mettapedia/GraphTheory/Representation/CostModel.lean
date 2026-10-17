import Mettapedia.GraphTheory.Representation.Basic
import Mathlib.Control.Monad.Writer

/-!
# Resource algebra for graph representation choice

Meaning-preserving graph conversions can still be poor operational choices.
This module records time, reads, writes, allocation, and peak temporary space
without identifying any of them with wall-clock time.  The central decision is
whether paying once to change representation is repaid by a later workload.

The equations are exact accounting identities.  Big-O descriptions may be
derived from them after a physical realization supplies parameter bounds; they
are not installed as substitutes for those bounds.
-/

namespace Mettapedia.GraphTheory.Representation

set_option autoImplicit false

/-- Independently observable resource coordinates.  `peakTemporary` assumes
temporary storage is released at the end of an operation; retained outputs are
accounted for separately by the presentation's `storageCells`. -/
@[ext] structure Resources where
  time : Nat := 0
  reads : Nat := 0
  writes : Nat := 0
  allocated : Nat := 0
  peakTemporary : Nat := 0
deriving DecidableEq, Repr

namespace Resources

/-- Sequential composition.  Additive work accumulates, while disjoint
temporary lifetimes take their maximum rather than their sum. -/
def seq (first second : Resources) : Resources where
  time := first.time + second.time
  reads := first.reads + second.reads
  writes := first.writes + second.writes
  allocated := first.allocated + second.allocated
  peakTemporary := max first.peakTemporary second.peakTemporary

def zero : Resources := {}

@[simp] theorem zero_seq (cost : Resources) : zero.seq cost = cost := by
  cases cost
  simp [zero, seq]

@[simp] theorem seq_zero (cost : Resources) : cost.seq zero = cost := by
  cases cost
  simp [zero, seq]

theorem seq_assoc (first second third : Resources) :
    (first.seq second).seq third = first.seq (second.seq third) := by
  cases first
  cases second
  cases third
  simp [seq, Nat.add_assoc, max_assoc]

/-!
`Resources` is a writer account.  Sequential composition is its monoid
operation: additive coordinates accumulate and peak temporary storage takes
the maximum across non-overlapping operation lifetimes.
-/

instance : Mul Resources := ⟨seq⟩

instance : One Resources := ⟨zero⟩

/-- Already measured resource vectors commute. This does not license
reordering stateful operations, whose measured vectors may depend on order. -/
instance : CommMonoid Resources where
  mul := seq
  one := zero
  mul_assoc := seq_assoc
  one_mul := zero_seq
  mul_one := seq_zero
  mul_comm first second := by
    change seq first second = seq second first
    cases first
    cases second
    simp [seq, Nat.add_comm, max_comm]

@[simp] theorem mul_eq_seq (first second : Resources) :
    first * second = first.seq second := rfl

@[simp] theorem one_eq_zero : (1 : Resources) = zero := rfl

/-- Repeating one operation a known number of times. -/
def replicate (count : Nat) (cost : Resources) : Resources where
  time := count * cost.time
  reads := count * cost.reads
  writes := count * cost.writes
  allocated := count * cost.allocated
  peakTemporary := if count = 0 then 0 else cost.peakTemporary

@[simp] theorem replicate_zero (cost : Resources) : replicate 0 cost = zero := by
  cases cost
  simp [replicate, zero]

@[simp] theorem replicate_one (cost : Resources) : replicate 1 cost = cost := by
  cases cost
  simp [replicate]


/-- The closed-form repeated account agrees with the standard monoid power. -/
theorem replicate_eq_pow (count : Nat) (cost : Resources) :
    replicate count cost = cost ^ count := by
  induction count with
  | zero => exact replicate_zero cost
  | succ count ih =>
      rw [pow_succ, ← ih]
      apply Resources.ext <;>
        simp [replicate, seq, Nat.succ_mul, Nat.add_comm, mul_eq_seq]
      split_ifs <;> simp

/-- Workload concatenation is standard monoid multiplication. -/
theorem replicate_add (first second : Nat) (cost : Resources) :
    replicate (first + second) cost = (replicate first cost).seq (replicate second cost) := by
  simpa only [replicate_eq_pow, mul_eq_seq] using pow_add cost first second

end Resources

/-- A computed value with a resource account. -/
structure Accounted (Result : Type*) where
  value : Result
  resources : Resources

namespace Accounted

def pure {Result : Type*} (value : Result) : Accounted Result :=
  ⟨value, Resources.zero⟩

def bind {First Second : Type*} (first : Accounted First)
    (next : First → Accounted Second) : Accounted Second :=
  let second := next first.value
  ⟨second.value, first.resources.seq second.resources⟩

@[simp] theorem pure_bind {First Second : Type*} (value : First)
    (next : First → Accounted Second) :
    bind (pure value) next = next value := by
  simp [bind, pure]


/-- Returning an already computed value adds no resource usage. -/
@[simp] theorem bind_pure {Result : Type*} (computation : Accounted Result) :
    bind computation pure = computation := by
  cases computation
  simp [bind, pure]

/-- Account accumulation has the associativity required for program bracketing. -/
theorem bind_assoc {First Middle Last : Type*} (computation : Accounted First)
    (next : First → Accounted Middle) (last : Middle → Accounted Last) :
    bind (bind computation next) last = bind computation (fun value => bind (next value) last) := by
  simp [bind, Resources.seq_assoc]

/-- This account-value wrapper is the standard writer construction; both
value and complete resource vector are retained. -/
def writerEquiv (Result : Type) : Accounted Result ≃ Writer Resources Result where
  toFun computation := (computation.value, computation.resources)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv computation := by cases computation; rfl
  right_inv pair := by cases pair; rfl

@[simp] theorem writerEquiv_pure {Result : Type} (value : Result) :
    writerEquiv Result (pure value) = (Pure.pure value : Writer Resources Result) := rfl

/-- The equivalence preserves binding, including the entire vector account. -/
theorem writerEquiv_bind {First Second : Type} (computation : Accounted First)
    (next : First → Accounted Second) :
    writerEquiv Second (bind computation next) =
      (writerEquiv First computation >>= fun value => writerEquiv Second (next value)) := rfl

end Accounted

/-- A refinement augmented with a resource account for constructing its actual
target value.  Semantic correctness remains the underlying refinement law. -/
structure CostedRefinement {n : Nat} (source target : Presentation n)
    extends Refinement source target where
  resources : source.Carrier → Resources

namespace CostedRefinement

/-- A costed conversion computes its target and retains the full account. -/
def run {n : Nat} {source target : Presentation n}
    (conversion : CostedRefinement source target) (graph : source.Carrier) :
    Accounted target.Carrier :=
  ⟨conversion.map graph, conversion.resources graph⟩

@[ext] theorem ext {n : Nat} {source target : Presentation n}
    {first second : CostedRefinement source target}
    (maps : first.map = second.map) (accounts : first.resources = second.resources) :
    first = second := by
  cases first with
  | mk first firstResources =>
    cases second with
    | mk second secondResources =>
      have underlying : first = second := Refinement.ext maps
      cases underlying
      cases accounts
      rfl

def id {n : Nat} (presentation : Presentation n) :
    CostedRefinement presentation presentation where
  map := _root_.id
  commute := by simp
  resources := fun _ => Resources.zero

/-- Costed refinements compose in the same direction as semantic refinements.
The intermediate target is genuinely constructed and passed to the later
resource account. -/
def comp {n : Nat} {first middle last : Presentation n}
    (earlier : CostedRefinement first middle)
    (later : CostedRefinement middle last) :
    CostedRefinement first last where
  map := later.map ∘ earlier.map
  commute := by
    intro graph
    change last.denote (later.map (earlier.map graph)) = first.denote graph
    rw [later.commute, earlier.commute]
  resources := fun graph =>
    (earlier.resources graph).seq (later.resources (earlier.map graph))

@[simp] theorem run_id {n : Nat} (presentation : Presentation n)
    (graph : presentation.Carrier) :
    (id presentation).run graph = Accounted.pure graph := rfl

/-- Actual intermediate values determine later resource costs, exactly as
in the standard writer sequencing operation. -/
theorem run_comp {n : Nat} {first middle last : Presentation n}
    (earlier : CostedRefinement first middle) (later : CostedRefinement middle last)
    (graph : first.Carrier) :
    (earlier.comp later).run graph = Accounted.bind (earlier.run graph) later.run := rfl

@[simp] theorem id_comp {n : Nat} {source target : Presentation n}
    (conversion : CostedRefinement source target) :
    (id source).comp conversion = conversion := by
  apply ext
  · rfl
  · funext graph
    exact Resources.zero_seq _

@[simp] theorem comp_id {n : Nat} {source target : Presentation n}
    (conversion : CostedRefinement source target) :
    conversion.comp (id target) = conversion := by
  apply ext
  · rfl
  · funext graph
    exact Resources.seq_zero _

/-- Rebracketing conversions preserves both output and complete accounting. -/
theorem comp_assoc {n : Nat} {first second third last : Presentation n}
    (one : CostedRefinement first second) (two : CostedRefinement second third)
    (three : CostedRefinement third last) :
    (one.comp two).comp three = one.comp (two.comp three) := by
  apply ext
  · rfl
  · funext graph
    exact Resources.seq_assoc _ _ _

@[simp] theorem comp_time {n : Nat} {first middle last : Presentation n}
    (earlier : CostedRefinement first middle)
    (later : CostedRefinement middle last) (graph : first.Carrier) :
    ((earlier.comp later).resources graph).time =
      (earlier.resources graph).time +
        (later.resources (earlier.map graph)).time :=
  rfl

@[simp] theorem comp_peakTemporary {n : Nat}
    {first middle last : Presentation n}
    (earlier : CostedRefinement first middle)
    (later : CostedRefinement middle last) (graph : first.Carrier) :
    ((earlier.comp later).resources graph).peakTemporary =
      max (earlier.resources graph).peakTemporary
        (later.resources (earlier.map graph)).peakTemporary :=
  rfl

end CostedRefinement

/-! ## Persistent versus destructive memory regimes -/

/-- Absolute peak cells when the source must remain live while the target is
constructed. -/
def persistentPeak (sourceCells targetCells temporaryCells : Nat) : Nat :=
  sourceCells + targetCells + temporaryCells

/-- Absolute peak cells when construction may overwrite or release source
storage as it proceeds.  This is an ideal lower-envelope model; a concrete
algorithm must prove that it attains it. -/
def destructivePeak (sourceCells targetCells temporaryCells : Nat) : Nat :=
  max sourceCells targetCells + temporaryCells

theorem destructivePeak_le_persistentPeak
    (sourceCells targetCells temporaryCells : Nat) :
    destructivePeak sourceCells targetCells temporaryCells ≤
      persistentPeak sourceCells targetCells temporaryCells := by
  simp only [destructivePeak, persistentPeak]
  omega

theorem persistentPeak_exceeds_source_by_target
    (sourceCells targetCells temporaryCells : Nat) :
    sourceCells + targetCells ≤
      persistentPeak sourceCells targetCells temporaryCells := by
  simp [persistentPeak]

/-- An operation is structurally in-place only when it allocates no cells and
needs no temporary cells.  Low time alone cannot establish this property. -/
def IsInPlace (cost : Resources) : Prop :=
  cost.allocated = 0 ∧ cost.peakTemporary = 0

theorem sequential_inPlace {first second : Resources}
    (firstInPlace : IsInPlace first) (secondInPlace : IsInPlace second) :
    IsInPlace (first.seq second) := by
  rcases firstInPlace with ⟨firstAllocated, firstPeak⟩
  rcases secondInPlace with ⟨secondAllocated, secondPeak⟩
  simp [IsInPlace, Resources.seq, firstAllocated, secondAllocated,
    firstPeak, secondPeak]

/-! ## Stay-versus-migrate economics -/

/-- Total time for answering `queryCount` equally costed queries without
changing representation. -/
def stayTime (queryCount sourceQueryTime : Nat) : Nat :=
  queryCount * sourceQueryTime

/-- Total time for one translation followed by `queryCount` target queries. -/
def migrateTime (translationTime queryCount targetQueryTime : Nat) : Nat :=
  translationTime + queryCount * targetQueryTime

/-- Exact break-even theorem.  If every source query costs `saving` more than
the target query, migration wins precisely when accumulated savings exceed the
one-time translation cost. -/
theorem migrate_faster_iff_breakEven
    (translationTime queryCount targetQueryTime saving : Nat) :
    migrateTime translationTime queryCount targetQueryTime <
        stayTime queryCount (targetQueryTime + saving) ↔
      translationTime < queryCount * saving := by
  simp only [migrateTime, stayTime, Nat.mul_add]
  omega

theorem migrate_ties_iff_breakEven
    (translationTime queryCount targetQueryTime saving : Nat) :
    migrateTime translationTime queryCount targetQueryTime =
        stayTime queryCount (targetQueryTime + saving) ↔
      translationTime = queryCount * saving := by
  simp only [migrateTime, stayTime, Nat.mul_add]
  omega

/-- Negative control: with no per-query saving, a positive-cost migration is
strictly slower for every workload size. -/
theorem migration_without_saving_is_slower
    (translationTime queryCount queryTime : Nat)
    (positive : 0 < translationTime) :
    stayTime queryCount queryTime <
      migrateTime translationTime queryCount queryTime := by
  simp [stayTime, migrateTime, positive]

/-- A strategy is admissible only when its peak storage fits the budget. -/
def FitsSpace (budget peak : Nat) : Prop := peak ≤ budget

theorem persistent_migration_not_feasible
    {budget sourceCells targetCells temporaryCells : Nat}
    (tooLarge : budget < sourceCells + targetCells) :
    ¬ FitsSpace budget
      (persistentPeak sourceCells targetCells temporaryCells) := by
  intro fits
  exact Nat.not_le_of_lt tooLarge
    (le_trans (persistentPeak_exceeds_source_by_target _ _ _) fits)

/-! ## Finite average-case workloads -/

/-- A finite empirical or probabilistic workload.  Natural weights avoid
floating-point semantics; normalization is deferred until reporting. -/
structure WeightedSample (Query : Type*) where
  query : Query
  weight : Nat

def totalWeight {Query : Type*} (samples : List (WeightedSample Query)) : Nat :=
  (samples.map WeightedSample.weight).sum

/-- Unnormalized expected time numerator.  Dividing this by `totalWeight`
gives the arithmetic mean when the total weight is nonzero. -/
def weightedTime {Query : Type*} (cost : Query → Nat)
    (samples : List (WeightedSample Query)) : Nat :=
  (samples.map fun sample => sample.weight * cost sample.query).sum

theorem weightedTime_add {Query : Type*} (first second : Query → Nat)
    (samples : List (WeightedSample Query)) :
    weightedTime (fun query => first query + second query) samples =
      weightedTime first samples + weightedTime second samples := by
  induction samples with
  | nil => simp [weightedTime]
  | cons sample rest inductionHypothesis =>
      change sample.weight * (first sample.query + second sample.query) +
          weightedTime (fun query => first query + second query) rest =
        (sample.weight * first sample.query + weightedTime first rest) +
          (sample.weight * second sample.query + weightedTime second rest)
      rw [Nat.mul_add, inductionHypothesis]
      omega

/-- A representation that is pointwise no slower is also no slower on every
finite weighted average-case workload. -/
theorem weightedTime_mono {Query : Type*} {first second : Query → Nat}
    (pointwise : ∀ query, first query ≤ second query)
    (samples : List (WeightedSample Query)) :
    weightedTime first samples ≤ weightedTime second samples := by
  induction samples with
  | nil => simp [weightedTime]
  | cons sample rest inductionHypothesis =>
      simp only [weightedTime, List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (Nat.mul_le_mul_left sample.weight (pointwise sample.query))
        inductionHypothesis

/-! ## Strict materialization schedules -/

/-- A dense materialization asks for every ordered vertex pair. -/
def denseProbeCount (vertexCount : Nat) : Nat := vertexCount * vertexCount

/-- Exact upper envelope when every source edge query costs at most
`sourceQueryBound`.  This is a schedule count, not a claim about lazy function
evaluation or a physical cache. -/
def denseViaObserverWork (vertexCount sourceQueryBound : Nat) : Nat :=
  denseProbeCount vertexCount * sourceQueryBound

theorem denseViaObserverWork_zero_vertices (sourceQueryBound : Nat) :
    denseViaObserverWork 0 sourceQueryBound = 0 := by
  simp [denseViaObserverWork, denseProbeCount]

namespace Canary

/-- Ten queries saving three units each repay a translation costing twenty. -/
theorem migration_profitable : migrateTime 20 10 1 < stayTime 10 4 := by
  decide

/-- Two queries do not repay the same translation. -/
theorem migration_too_early : stayTime 2 4 < migrateTime 20 2 1 := by
  decide

/-- Persistent conversion can fail a memory budget even when the destructive
lower envelope fits. -/
theorem persistent_fails_destructive_fits :
    ¬ FitsSpace 12 (persistentPeak 8 7 0) ∧
      FitsSpace 12 (destructivePeak 8 7 0) := by
  constructor <;> simp [FitsSpace, persistentPeak, destructivePeak]


/-- A state-dependent account for doubling one stored natural number. -/
def doubleAccount (state : Nat) : Accounted Nat :=
  ⟨2 * state, { time := state }⟩

/-- A reset with a state-dependent account. -/
def resetAccount (state : Nat) : Accounted Nat :=
  ⟨0, { time := state }⟩

/-- Both schedules have the same extensional result, but their costs differ.
Commutativity of the account monoid therefore grants no program-reorder law. -/
theorem equal_results_different_accounts :
    (Accounted.bind (doubleAccount 1) resetAccount).value =
      (Accounted.bind (resetAccount 1) doubleAccount).value ∧
    (Accounted.bind (doubleAccount 1) resetAccount).resources.time ≠
      (Accounted.bind (resetAccount 1) doubleAccount).resources.time := by
  decide

end Canary


end Mettapedia.GraphTheory.Representation
