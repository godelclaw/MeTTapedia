import Mettapedia.Machines.ResourceCollectionSchedule

/-!
# Collecting for want of frame identities

A dead structure keeps the frame identities it refers to until a collection
reaches it, so the identities in use can exceed the live ones by whatever the
collections have not yet reached. A machine therefore reads the identity census
at the top of every step, a safe point outside any transition
(`petta_machine_identity_pressure`, `petta_machine_identity_pressure_relieved`,
`petta_machine_maybe_collect`):

* it records how many identities the step just finished minted, and keeps the
  largest such count;
* it lowers its threshold to the in-use count plus a quarter of it (at least the
  base reserve), when that is lower: the threshold is the least such value since
  the last pressure collection;
* the reserve is the base reserve or the largest step, whichever is more;
* when at least the threshold is in use and the headroom is below a quarter of
  the in-use count plus the reserve, it collects every generation, and the
  threshold becomes the count that collection left plus a quarter of it (at
  least the base reserve). Otherwise only the heap's own schedule collects.

The state splits the census by what a collection can release: live handles,
referenced from reachable structure; garbage handles, referenced only from
unreachable structure, which a collection of every generation releases; free
handles in this thread's cache, which the census counts as in use; and retired
handles, lost for good. A step mints, kills and drops identities in any order.
A mint takes a cached handle, else headroom, and is refused only when neither
is left.

* `safePoint_room`, `step_within_reserve`: with at most `B` live and `R`
  retired at a safe point, pressure collections of every generation, every step
  minting at most `K`, a base reserve `r > 0`, a cache of `C`,
  `A = B + C + max r ((B + C) / 4)` and `A + R + K ≤ L`, the safe point leaves
  room for a step as large as the reserve (up to `K`); such a step is never
  refused.
* `refusal_only_when_growing`: a refused step minted more than every earlier
  step and more than the base reserve. `no_refusal`: a run in which each such
  step has room when it comes never refuses. `no_refusal_within_reserve`: in
  particular a run whose every step mints at most the reserve, which such steps
  never raise above the base reserve.
* `pressure_collections_spaced`: between two pressure collections the in-use
  count has grown by a quarter (at least the base reserve) over the fewest in
  use since the earlier one. When they free nothing and nothing is freed
  between them, their counts grow geometrically (`collections_geometric`); with
  a reserve no more than a quarter of the counts, two such in a row are the
  last (`fruitless_pair_last`).
* Controls: the threshold falls again once handles are freed, so pressure
  collections resume after collections that could not reach the garbage; a
  step larger than every earlier one can still be refused, but once one has
  had room, steps of its size are covered; the conditions of each theorem are
  needed. The previous rule, which neither lowered its threshold nor adapted
  its reserve, refuses both the resumed run and the covered one.

The census formulas are those the frame store satisfies
(`MetavariableFrameStoreGrowth.census_in_use`, `census_headroom`). The model
counts handles: it does not trace reachability, which `ArenaHeldResources`
relates to the holds a reset releases, and it follows one thread's cache and
mint count.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IdentityPressureSchedule

/-! ## Census and schedule -/

/-- Handles `1 .. limit - 1` may be issued; a thread keeps at most `cache` free
handles; `reserve` is the base reserve. -/
structure Config where
  limit : Nat
  cache : Nat
  reserve : Nat
  deriving DecidableEq, Repr

/-- The runtime's parameters: every handle class, a 64-handle cache, a base
reserve of sixteen. -/
def runtime : Config := ⟨152043520, 64, 16⟩

/-- The census, split by what a collection can release; the machine's pressure
threshold; and the most identities one of its steps has minted. -/
structure State where
  live : Nat
  garbage : Nat
  cached : Nat
  retired : Nat
  pressureAfter : Nat
  peak : Nat
  deriving DecidableEq, Repr

def start : State := ⟨0, 0, 0, 0, 0, 0⟩

/-- `cetta_frame_identity_census_in_use`: referenced handles and the cache. -/
def State.inUse (s : State) : Nat := s.live + s.garbage + s.cached

/-- Handles holding a reference. -/
def State.held (s : State) : Nat := s.live + s.garbage

/-- `cetta_frame_identity_census_headroom`: never issued, or on the shared list. -/
def State.headroom (cfg : Config) (s : State) : Nat := cfg.limit - 1 - (s.inUse + s.retired)

/-- What this thread may still mint. -/
def State.available (cfg : Config) (s : State) : Nat := s.cached + s.headroom cfg

/-- `petta_machine_identity_after`: a count grown by a quarter, at least the
base reserve. -/
def grow (cfg : Config) (count : Nat) : Nat := count + max cfg.reserve (count / 4)

/-- The reserve: the most one step has minted, at least the base reserve. -/
def State.reserve (cfg : Config) (s : State) : Nat := max cfg.reserve s.peak

/-- The threshold lowered to the current count grown by a quarter, when that
is lower. -/
def State.lower (cfg : Config) (s : State) : State :=
  { s with pressureAfter := min s.pressureAfter (grow cfg s.inUse) }

/-- `petta_machine_identity_pressure`, applied after lowering. -/
def Pressured (cfg : Config) (s : State) : Prop :=
  s.pressureAfter ≤ s.inUse ∧ s.headroom cfg < s.inUse / 4 + s.reserve cfg

instance (cfg : Config) (s : State) : Decidable (Pressured cfg s) := by
  unfold Pressured; infer_instance

/-- `petta_machine_identity_pressure_relieved`. -/
def State.relieve (cfg : Config) (s : State) : State :=
  { s with pressureAfter := grow cfg s.inUse }

/-- A collection releases up to `freed` garbage handles; `retiring` of them
retire, and the rest fill the cache, then the shared list. -/
def State.collect (cfg : Config) (freed retiring : Nat) (s : State) : State :=
  { s with
    garbage := s.garbage - min freed s.garbage
    cached := min cfg.cache
      (s.cached + (min freed s.garbage - min retiring (min freed s.garbage)))
    retired := s.retired + min retiring (min freed s.garbage) }

/-- What a transition does to identities: a mint; a live hold becoming
unreachable; a live hold's last reference released directly, retiring the
handle or freeing it. -/
inductive Event
  | mint
  | die
  | drop (retire : Bool)
  deriving DecidableEq, Repr

/-- One event; `none` is a refused mint. -/
def Event.apply (cfg : Config) : Event → State → Option State
  | .mint, s =>
    if 0 < s.cached then some { s with cached := s.cached - 1, live := s.live + 1 }
    else if 0 < s.headroom cfg then some { s with live := s.live + 1 }
    else none
  | .die, s =>
    if 0 < s.live then some { s with live := s.live - 1, garbage := s.garbage + 1 }
    else some s
  | .drop retire, s =>
    if 0 < s.live then
      if retire then some { s with live := s.live - 1, retired := s.retired + 1 }
      else if s.cached < cfg.cache then
        some { s with live := s.live - 1, cached := s.cached + 1 }
      else some { s with live := s.live - 1 }
    else some s

def transition (cfg : Config) : List Event → State → Option State
  | [], s => some s
  | e :: rest, s => (e.apply cfg s).bind (transition cfg rest)

def mints : List Event → Nat
  | [] => 0
  | .mint :: rest => mints rest + 1
  | _ :: rest => mints rest

/-- One step's choices: what the heap's own schedule releases, what a pressure
collection releases, how many released handles retire, and the transition. -/
structure Choice where
  heapFreed : Nat
  pressureFreed : Nat
  retiring : Nat
  events : List Event
  deriving DecidableEq, Repr

/-- The top of the step loop: lower the threshold, then collect under pressure,
or let the heap's own schedule collect. -/
def safePoint (cfg : Config) (c : Choice) (s : State) : State :=
  if Pressured cfg (s.lower cfg) then
    ((s.lower cfg).collect cfg c.pressureFreed c.retiring).relieve cfg
  else (s.lower cfg).collect cfg c.heapFreed c.retiring

/-- The step's mint count, kept if it is the largest. -/
def State.record (s : State) (count : Nat) : State := { s with peak := max s.peak count }

def step (cfg : Config) (c : Choice) (s : State) : Option State :=
  (transition cfg c.events (safePoint cfg c s)).map fun after => after.record (mints c.events)

def run (cfg : Config) : List Choice → State → Option State
  | [], s => some s
  | c :: rest, s => (step cfg c s).bind (run cfg rest)

/-- The heap's own schedule alone, as when pressure collection is disabled. -/
def heapStep (cfg : Config) (c : Choice) (s : State) : Option State :=
  transition cfg c.events (s.collect cfg c.heapFreed c.retiring)

def heapRun (cfg : Config) : List Choice → State → Option State
  | [], s => some s
  | c :: rest, s => (heapStep cfg c s).bind (heapRun cfg rest)

theorem grow_mono (cfg : Config) {a b : Nat} (le : a ≤ b) : grow cfg a ≤ grow cfg b := by
  unfold grow; omega

theorem grow_min (cfg : Config) (a b : Nat) :
    min (grow cfg a) (grow cfg b) = grow cfg (min a b) := by
  unfold grow; omega

/-! ## The census stays consistent -/

/-- The cache within its capacity, and in-use plus retired handles within the
limit. Every operation keeps it. -/
structure Census (cfg : Config) (s : State) : Prop where
  cached_le : s.cached ≤ cfg.cache
  fits : s.inUse + s.retired ≤ cfg.limit - 1

theorem start_census (cfg : Config) : Census cfg start := ⟨Nat.zero_le _, Nat.zero_le _⟩

theorem available_eq {cfg : Config} {s : State} (census : Census cfg s) :
    s.available cfg + s.held + s.retired = cfg.limit - 1 := by
  have := census.fits
  simp only [State.available, State.headroom, State.held, State.inUse] at *
  omega

theorem lower_census {cfg : Config} {s : State} (census : Census cfg s) :
    Census cfg (s.lower cfg) := ⟨census.cached_le, census.fits⟩

theorem collect_census {cfg : Config} {s : State} (census : Census cfg s) (freed retiring : Nat) :
    Census cfg (s.collect cfg freed retiring) ∧ (s.collect cfg freed retiring).live = s.live ∧
      (s.collect cfg freed retiring).inUse ≤ s.inUse ∧
      (s.collect cfg freed retiring).held + (s.collect cfg freed retiring).retired ≤
        s.held + s.retired ∧
      s.retired ≤ (s.collect cfg freed retiring).retired ∧
      (s.collect cfg freed retiring).pressureAfter = s.pressureAfter ∧
      (s.collect cfg freed retiring).peak = s.peak := by
  have cachedLe := census.cached_le
  have fits := census.fits
  simp only [State.inUse] at fits
  refine ⟨⟨?_, ?_⟩, rfl, ?_, ?_, ?_, rfl, rfl⟩ <;>
    dsimp only [State.collect, State.inUse, State.held] <;> omega

/-- A collection that reaches all the garbage leaves none. -/
theorem collect_full {cfg : Config} {s : State} {freed retiring : Nat} (full : s.garbage ≤ freed) :
    (s.collect cfg freed retiring).garbage = 0 := by
  simp only [State.collect]; omega

/-- A mint is refused exactly when nothing is available. -/
theorem mint_none_iff (cfg : Config) (s : State) :
    Event.mint.apply cfg s = none ↔ s.available cfg = 0 := by
  simp only [Event.apply, State.available]
  split_ifs <;> simp <;> omega

theorem event_census {cfg : Config} {s after : State} (census : Census cfg s) (e : Event)
    (applied : e.apply cfg s = some after) :
    Census cfg after ∧ after.pressureAfter = s.pressureAfter ∧ after.peak = s.peak ∧
      s.retired ≤ after.retired ∧
      after.held + after.retired ≤ s.held + s.retired + mints [e] := by
  have cachedLe := census.cached_le
  have fits := census.fits
  simp only [State.inUse] at fits
  cases e with
  | mint =>
    simp only [Event.apply] at applied
    split_ifs at applied with cachedPos headroomPos <;>
      simp only [Option.some.injEq] at applied <;> subst applied <;>
      refine ⟨⟨?_, ?_⟩, rfl, rfl, ?_, ?_⟩ <;>
      dsimp only [State.held, State.inUse, State.headroom, mints] at * <;> omega
  | die =>
    simp only [Event.apply] at applied
    split_ifs at applied with livePos <;>
      simp only [Option.some.injEq] at applied <;> subst applied <;>
      refine ⟨⟨?_, ?_⟩, rfl, rfl, ?_, ?_⟩ <;>
      (try dsimp only [State.held, State.inUse, mints] at *) <;> omega
  | drop retire =>
    simp only [Event.apply] at applied
    split_ifs at applied <;>
      simp only [Option.some.injEq] at applied <;> subst applied <;>
      refine ⟨⟨?_, ?_⟩, rfl, rfl, ?_, ?_⟩ <;>
      (try dsimp only [State.held, State.inUse, mints] at *) <;> omega

/-- A transition whose mints fit what is available completes. -/
theorem transition_succeeds (cfg : Config) :
    ∀ (events : List Event) (s : State), Census cfg s →
      mints events + s.held + s.retired ≤ cfg.limit - 1 →
      ∃ after, transition cfg events s = some after := by
  intro events
  induction events with
  | nil => exact fun s _ _ => ⟨s, rfl⟩
  | cons e rest ih =>
    intro s census room
    have exact := available_eq census
    have applied : ∃ next, e.apply cfg s = some next := by
      cases hmint : e.apply cfg s with
      | some next => exact ⟨next, rfl⟩
      | none =>
        cases e with
        | mint =>
          have := (mint_none_iff cfg s).mp hmint
          simp only [mints] at room
          omega
        | die =>
          simp only [Event.apply] at hmint
          split_ifs at hmint
        | drop retire =>
          simp only [Event.apply] at hmint
          split_ifs at hmint
    obtain ⟨next, applied⟩ := applied
    obtain ⟨nextCensus, _, _, _, nextHeld⟩ := event_census census e applied
    have nextRoom : mints rest + next.held + next.retired ≤ cfg.limit - 1 := by
      cases e <;> simp only [mints] at room nextHeld <;> omega
    obtain ⟨after, finished⟩ := ih next nextCensus nextRoom
    exact ⟨after, by simp only [transition, applied, Option.bind_some, finished]⟩

/-- A transition that completes keeps the census, the threshold and the largest
step, and never undoes a retirement. -/
theorem transition_census (cfg : Config) :
    ∀ (events : List Event) (s after : State), Census cfg s →
      transition cfg events s = some after →
      Census cfg after ∧ after.pressureAfter = s.pressureAfter ∧ after.peak = s.peak ∧
        s.retired ≤ after.retired := by
  intro events
  induction events with
  | nil =>
    intro s after census finished
    simp only [transition, Option.some.injEq] at finished
    subst finished
    exact ⟨census, rfl, rfl, Nat.le_refl _⟩
  | cons e rest ih =>
    intro s after census finished
    simp only [transition] at finished
    cases applied : e.apply cfg s with
    | none => simp [applied] at finished
    | some next =>
      rw [applied, Option.bind_some] at finished
      obtain ⟨nextCensus, nextThreshold, nextPeak, nextRetired, _⟩ := event_census census e applied
      obtain ⟨afterCensus, afterThreshold, afterPeak, afterRetired⟩ :=
        ih next after nextCensus finished
      exact ⟨afterCensus, afterThreshold.trans nextThreshold, afterPeak.trans nextPeak,
        nextRetired.trans afterRetired⟩

theorem safePoint_census {cfg : Config} {s : State} (census : Census cfg s) (c : Choice) :
    Census cfg (safePoint cfg c s) ∧ (safePoint cfg c s).peak = s.peak ∧
      s.retired ≤ (safePoint cfg c s).retired := by
  have lowered := lower_census census
  unfold safePoint
  split_ifs
  · obtain ⟨collected, _, _, _, retired, _, peak⟩ :=
      collect_census lowered c.pressureFreed c.retiring
    exact ⟨⟨collected.cached_le, collected.fits⟩, peak, retired⟩
  · obtain ⟨collected, _, _, _, retired, _, peak⟩ := collect_census lowered c.heapFreed c.retiring
    exact ⟨collected, peak, retired⟩

/-- A completed step keeps the census, takes its threshold from the safe point,
records its mints, and never undoes a retirement. -/
theorem step_census {cfg : Config} {s after : State} {c : Choice} (census : Census cfg s)
    (stepped : step cfg c s = some after) :
    Census cfg after ∧ after.pressureAfter = (safePoint cfg c s).pressureAfter ∧
      after.peak = max s.peak (mints c.events) ∧ s.retired ≤ after.retired := by
  unfold step at stepped
  obtain ⟨finished, transitioned, rfl⟩ := Option.map_eq_some_iff.mp stepped
  obtain ⟨safeCensus, safePeak, safeRetired⟩ := safePoint_census census c
  obtain ⟨afterCensus, threshold, peak, retired⟩ :=
    transition_census cfg c.events _ _ safeCensus transitioned
  refine ⟨⟨afterCensus.cached_le, afterCensus.fits⟩, threshold, ?_, safeRetired.trans retired⟩
  simp only [State.record, peak, safePeak]

/-! ## Room for every step within the reserve -/

/-- The in-use count the rule lets accumulate before a collection: `bound` live
handles and a full cache, grown by a quarter. -/
def accrual (cfg : Config) (bound : Nat) : Nat := grow cfg (bound + cfg.cache)

/-- The census, and a threshold no higher than `accrual`. -/
structure Invariant (cfg : Config) (bound : Nat) (s : State) : Prop where
  census : Census cfg s
  threshold : s.pressureAfter ≤ accrual cfg bound

theorem start_invariant (cfg : Config) (bound : Nat) : Invariant cfg bound start :=
  ⟨start_census cfg, Nat.zero_le _⟩

/-- After the safe point the held and retired handles leave room for a step as
large as the reserve, up to `K`. Under pressure a full collection leaves only
live handles; below the threshold fewer than `accrual` are in use; and with
the headroom at least a quarter of the in-use count plus the reserve, the
reserve itself is available. -/
theorem safePoint_room (cfg : Config) {bound K retiredBound : Nat} (reserve_pos : 0 < cfg.reserve)
    (fit : accrual cfg bound + retiredBound + K ≤ cfg.limit)
    {s : State} {c : Choice} (invariant : Invariant cfg bound s) (live : s.live ≤ bound)
    (full : Pressured cfg (s.lower cfg) → s.garbage ≤ c.pressureFreed)
    (retired : (safePoint cfg c s).retired ≤ retiredBound) :
    (safePoint cfg c s).held + (safePoint cfg c s).retired + min (s.reserve cfg) K ≤
        cfg.limit - 1 ∧
      Census cfg (safePoint cfg c s) ∧
      (safePoint cfg c s).pressureAfter ≤ accrual cfg bound ∧
      (safePoint cfg c s).peak = s.peak := by
  have census := invariant.census
  have threshold := invariant.threshold
  have cachedLe := census.cached_le
  have fits := census.fits
  have lowered := lower_census census
  obtain ⟨safeCensus, safePeak, _⟩ := safePoint_census census c
  refine ⟨?_, safeCensus, ?_, safePeak⟩
  · unfold safePoint at retired ⊢
    split_ifs at retired ⊢ with pressured
    · have empty := collect_full (cfg := cfg) (retiring := c.retiring)
        (s := s.lower cfg) (full pressured)
      simp only [State.relieve, State.held, State.lower, State.reserve, State.collect]
        at retired empty ⊢
      unfold accrual grow at fit
      omega
    · unfold Pressured at pressured
      simp only [State.held, State.inUse, State.headroom, State.lower, State.collect,
        State.reserve, grow] at *
      unfold accrual grow at fit threshold
      omega
  · unfold safePoint
    split_ifs with pressured
    · have collectedCached :=
        (collect_census lowered c.pressureFreed c.retiring).1.cached_le
      have empty := collect_full (cfg := cfg) (retiring := c.retiring)
        (s := s.lower cfg) (full pressured)
      simp only [State.relieve, State.inUse, accrual, grow] at collectedCached empty ⊢
      simp only [State.collect, State.lower] at collectedCached empty ⊢
      omega
    · simp only [State.collect, State.lower]
      omega

/-- A step with room at its safe point completes and keeps the invariant. -/
theorem step_room (cfg : Config) {bound K retiredBound : Nat} (reserve_pos : 0 < cfg.reserve)
    (fit : accrual cfg bound + retiredBound + K ≤ cfg.limit)
    {s : State} {c : Choice} (invariant : Invariant cfg bound s) (live : s.live ≤ bound)
    (full : Pressured cfg (s.lower cfg) → s.garbage ≤ c.pressureFreed)
    (retired : (safePoint cfg c s).retired ≤ retiredBound)
    (room : mints c.events + (safePoint cfg c s).held + (safePoint cfg c s).retired ≤
      cfg.limit - 1) :
    ∃ after, step cfg c s = some after ∧ Invariant cfg bound after := by
  obtain ⟨_, safeCensus, safeThreshold, _⟩ :=
    safePoint_room cfg reserve_pos fit invariant live full retired
  obtain ⟨after, finished⟩ := transition_succeeds cfg c.events _ safeCensus room
  have stepped : step cfg c s = some (after.record (mints c.events)) := by
    simp only [step, finished, Option.map_some]
  obtain ⟨afterCensus, afterThreshold, _, _⟩ := step_census invariant.census stepped
  exact ⟨_, stepped, afterCensus, by rw [afterThreshold]; exact safeThreshold⟩

/-- A step minting no more than the reserve, and no more than `K`, is never
refused. -/
theorem step_within_reserve (cfg : Config) {bound K retiredBound : Nat}
    (reserve_pos : 0 < cfg.reserve) (fit : accrual cfg bound + retiredBound + K ≤ cfg.limit)
    {s : State} {c : Choice} (invariant : Invariant cfg bound s) (live : s.live ≤ bound)
    (full : Pressured cfg (s.lower cfg) → s.garbage ≤ c.pressureFreed)
    (retired : (safePoint cfg c s).retired ≤ retiredBound) (bounded : mints c.events ≤ K)
    (within : mints c.events ≤ s.reserve cfg) :
    ∃ after, step cfg c s = some after ∧ Invariant cfg bound after := by
  obtain ⟨room, _, _, _⟩ := safePoint_room cfg reserve_pos fit invariant live full retired
  have small : mints c.events ≤ min (s.reserve cfg) K := Nat.le_min.mpr ⟨within, bounded⟩
  exact step_room cfg reserve_pos fit invariant live full retired (by omega)

/-- A step that is refused minted more than every earlier step and more than
the base reserve. -/
theorem refusal_only_when_growing (cfg : Config) {bound K retiredBound : Nat}
    (reserve_pos : 0 < cfg.reserve) (fit : accrual cfg bound + retiredBound + K ≤ cfg.limit)
    {s : State} {c : Choice} (invariant : Invariant cfg bound s) (live : s.live ≤ bound)
    (full : Pressured cfg (s.lower cfg) → s.garbage ≤ c.pressureFreed)
    (retired : (safePoint cfg c s).retired ≤ retiredBound) (bounded : mints c.events ≤ K)
    (refused : step cfg c s = none) : s.reserve cfg < mints c.events := by
  by_contra within
  obtain ⟨_, stepped, _⟩ := step_within_reserve cfg reserve_pos fit invariant live full
    retired bounded (Nat.le_of_not_lt within)
  rw [stepped] at refused
  cases refused

/-- A run whose choices respect the hypotheses at every safe point it reaches,
and whose every step larger than the reserve has room when it comes. -/
def Obeys (cfg : Config) (bound K retiredBound : Nat) : List Choice → State → Prop
  | [], _ => True
  | c :: rest, s =>
    s.live ≤ bound ∧ mints c.events ≤ K ∧
      (Pressured cfg (s.lower cfg) → s.garbage ≤ c.pressureFreed) ∧
      (safePoint cfg c s).retired ≤ retiredBound ∧
      (s.reserve cfg < mints c.events →
        mints c.events + (safePoint cfg c s).held + (safePoint cfg c s).retired ≤
          cfg.limit - 1) ∧
      ∀ after, step cfg c s = some after → Obeys cfg bound K retiredBound rest after

/-- No mint is ever refused in a run that obeys the hypotheses: steps within
the reserve need nothing more, and each larger one has room when it comes. -/
theorem no_refusal (cfg : Config) {bound K retiredBound : Nat} (reserve_pos : 0 < cfg.reserve)
    (fit : accrual cfg bound + retiredBound + K ≤ cfg.limit) :
    ∀ (choices : List Choice) (s : State), Invariant cfg bound s →
      Obeys cfg bound K retiredBound choices s → (run cfg choices s).isSome := by
  intro choices
  induction choices with
  | nil => exact fun _ _ _ => rfl
  | cons c rest ih =>
    intro s invariant obeys
    obtain ⟨live, bounded, full, retired, growing, later⟩ := obeys
    have stepped : ∃ after, step cfg c s = some after ∧ Invariant cfg bound after := by
      by_cases within : mints c.events ≤ s.reserve cfg
      · exact step_within_reserve cfg reserve_pos fit invariant live full retired bounded within
      · exact step_room (K := K) cfg reserve_pos fit invariant live full retired
          (growing (Nat.lt_of_not_le within))
    obtain ⟨after, stepped, afterInvariant⟩ := stepped
    simp only [run, stepped, Option.bind_some]
    exact ih after afterInvariant (later after stepped)

theorem no_refusal_from_start (cfg : Config) {bound K retiredBound : Nat}
    (reserve_pos : 0 < cfg.reserve) (fit : accrual cfg bound + retiredBound + K ≤ cfg.limit)
    {choices : List Choice} (obeys : Obeys cfg bound K retiredBound choices start) :
    (run cfg choices start).isSome :=
  no_refusal cfg reserve_pos fit choices start (start_invariant cfg bound) obeys

/-- A run whose every step mints no more than its reserve. -/
def WithinReserve (cfg : Config) (bound retiredBound : Nat) : List Choice → State → Prop
  | [], _ => True
  | c :: rest, s =>
    s.live ≤ bound ∧ mints c.events ≤ s.reserve cfg ∧
      (Pressured cfg (s.lower cfg) → s.garbage ≤ c.pressureFreed) ∧
      (safePoint cfg c s).retired ≤ retiredBound ∧
      ∀ after, step cfg c s = some after → WithinReserve cfg bound retiredBound rest after

/-- Steps within the reserve never raise it above the base reserve, and a run
of them never refuses once `accrual + R` and the base reserve fit the limit. -/
theorem no_refusal_within_reserve (cfg : Config) {bound retiredBound : Nat}
    (reserve_pos : 0 < cfg.reserve)
    (fit : accrual cfg bound + retiredBound + cfg.reserve ≤ cfg.limit) :
    ∀ (choices : List Choice) (s : State), Invariant cfg bound s → s.peak ≤ cfg.reserve →
      WithinReserve cfg bound retiredBound choices s → (run cfg choices s).isSome := by
  intro choices
  induction choices with
  | nil => exact fun _ _ _ _ => rfl
  | cons c rest ih =>
    intro s invariant peakLe within
    obtain ⟨live, small, full, retired, later⟩ := within
    have bounded : mints c.events ≤ cfg.reserve := by
      simp only [State.reserve] at small
      omega
    obtain ⟨after, stepped, afterInvariant⟩ := step_within_reserve cfg reserve_pos fit
      invariant live full retired bounded small
    simp only [run, stepped, Option.bind_some]
    refine ih after afterInvariant ?_ (later after stepped)
    rw [(step_census invariant.census stepped).2.2.1]
    exact max_le peakLe bounded

/-! ## How far apart pressure collections are -/

/-- A pressure collection: the in-use count before and after it, the fewest in
use since the previous one (this count, for the first), the retired count, and
the reserve when it ran. -/
structure Collection where
  before : Nat
  after : Nat
  low : Nat
  retired : Nat
  reserve : Nat
  deriving DecidableEq, Repr

/-- The fewest in use since the previous pressure collection, if there was one. -/
def lowWith (fewest : Option Nat) (count : Nat) : Nat := (fewest.map (min · count)).getD count

/-- The pressure collections of a run, in order; `fewest` is the least in-use
count since the previous one, if any. -/
def pressureLog (cfg : Config) : Option Nat → List Choice → State → List Collection
  | _, [], _ => []
  | fewest, c :: rest, s =>
    if Pressured cfg (s.lower cfg) then
      ⟨s.inUse, ((s.lower cfg).collect cfg c.pressureFreed c.retiring).inUse,
        lowWith fewest s.inUse, s.retired, s.reserve cfg⟩ ::
        match step cfg c s with
        | some after =>
          pressureLog cfg (some ((s.lower cfg).collect cfg c.pressureFreed c.retiring).inUse)
            rest after
        | none => []
    else
      match step cfg c s with
      | some after => pressureLog cfg (fewest.map (min · s.inUse)) rest after
      | none => []

/-- The threshold is the least count since the last pressure collection, grown
by a quarter. -/
def Tracks (cfg : Config) (fewest : Option Nat) (s : State) : Prop :=
  ∀ low, fewest = some low → s.pressureAfter = grow cfg low

/-- A pressure collection waits until a quarter more (at least the base
reserve) is in use than the fewest since the earlier one; retirements are
never undone. -/
def Spaced (cfg : Config) (earlier later : Collection) : Prop :=
  later.low ≤ earlier.after ∧ grow cfg later.low ≤ later.before ∧
    earlier.retired ≤ later.retired

/-- Every pressure collection ran with little headroom, within the census, and
released rather than added; between two of them the in-use count grew by a
quarter over the fewest in use since the earlier one. -/
theorem pressure_collections_spaced (cfg : Config) :
    ∀ (choices : List Choice) (fewest : Option Nat) (s : State), Census cfg s →
      Tracks cfg fewest s →
      (pressureLog cfg fewest choices s).IsChain (Spaced cfg) ∧
        (∀ first ∈ (pressureLog cfg fewest choices s).head?,
          (∀ low, fewest = some low → first.low ≤ low ∧ grow cfg first.low ≤ first.before) ∧
            s.retired ≤ first.retired) ∧
        ∀ entry ∈ pressureLog cfg fewest choices s, entry.after ≤ entry.before ∧
          entry.before + entry.retired ≤ cfg.limit - 1 ∧
          cfg.limit - 1 - (entry.before + entry.retired) < entry.before / 4 + entry.reserve := by
  intro choices
  induction choices with
  | nil => intro _ s _ _; simp [pressureLog]
  | cons c rest ih =>
    intro fewest s census tracks
    have fits := census.fits
    have lowered := lower_census census
    obtain ⟨_, _, lessInUse, _, _, _, _⟩ := collect_census lowered c.pressureFreed c.retiring
    by_cases pressured : Pressured cfg (s.lower cfg)
    · have threshold : ∀ after, step cfg c s = some after →
          after.pressureAfter =
            grow cfg ((s.lower cfg).collect cfg c.pressureFreed c.retiring).inUse := by
        intro after stepped
        rw [(step_census census stepped).2.1]
        unfold safePoint
        rw [if_pos pressured]
        rfl
      have here : ((s.lower cfg).collect cfg c.pressureFreed c.retiring).inUse ≤ s.inUse ∧
          s.inUse + s.retired ≤ cfg.limit - 1 ∧
          cfg.limit - 1 - (s.inUse + s.retired) < s.inUse / 4 + s.reserve cfg :=
        ⟨lessInUse, fits, pressured.2⟩
      have headHere : ∀ low, fewest = some low →
          lowWith fewest s.inUse ≤ low ∧ grow cfg (lowWith fewest s.inUse) ≤ s.inUse := by
        intro low known
        subst known
        have trigger : grow cfg (min low s.inUse) ≤ s.inUse := by
          have := pressured.1
          simp only [State.lower, tracks low rfl, grow_min] at this
          exact this
        exact ⟨by simp [lowWith], by simpa [lowWith] using trigger⟩
      simp only [pressureLog, if_pos pressured]
      cases stepped : step cfg c s with
      | none =>
        dsimp only
        simp only [List.isChain_singleton, List.head?_cons, Option.mem_def, Option.some.injEq,
          forall_eq', List.mem_singleton, forall_eq, true_and]
        exact ⟨⟨headHere, Nat.le_refl _⟩, here⟩
      | some after =>
        dsimp only
        have afterCensus := (step_census census stepped).1
        obtain ⟨chain, head, entries⟩ :=
          ih (some ((s.lower cfg).collect cfg c.pressureFreed c.retiring).inUse) after afterCensus
            (by
              intro low known
              simp only [Option.some.injEq] at known
              subst known
              exact threshold after stepped)
        refine ⟨?_, ?_, ?_⟩
        · cases log : pressureLog cfg
              (some ((s.lower cfg).collect cfg c.pressureFreed c.retiring).inUse) rest after with
          | nil => exact List.isChain_singleton _
          | cons next more =>
            rw [log] at chain head
            obtain ⟨spacing, retiredLater⟩ := head next rfl
            obtain ⟨lowLe, grown⟩ := spacing _ rfl
            exact List.IsChain.cons_cons
              ⟨lowLe, grown, (step_census census stepped).2.2.2.trans retiredLater⟩ chain
        · intro first member
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at member
          subst member
          exact ⟨headHere, Nat.le_refl _⟩
        · intro entry member
          rcases List.mem_cons.mp member with rfl | later
          · exact here
          · exact entries entry later
    · simp only [pressureLog, if_neg pressured]
      cases stepped : step cfg c s with
      | none => simp
      | some after =>
        dsimp only
        have afterCensus := (step_census census stepped).1
        have afterThreshold : after.pressureAfter = (s.lower cfg).pressureAfter := by
          rw [(step_census census stepped).2.1]
          unfold safePoint
          rw [if_neg pressured]
          exact (collect_census lowered c.heapFreed c.retiring).2.2.2.2.2.1
        obtain ⟨chain, head, entries⟩ := ih (fewest.map (min · s.inUse)) after afterCensus (by
          intro low known
          cases fewest with
          | none => cases known
          | some earlier =>
            simp only [Option.map_some, Option.some.injEq] at known
            subst known
            rw [afterThreshold]
            simp only [State.lower, tracks earlier rfl, grow_min])
        refine ⟨chain, ?_, entries⟩
        intro first member
        obtain ⟨spacing, retiredLater⟩ := head first member
        refine ⟨fun low known => ?_, (step_census census stepped).2.2.2.trans retiredLater⟩
        subst known
        obtain ⟨lowLe, grown⟩ := spacing _ rfl
        exact ⟨Nat.le_trans lowLe (Nat.min_le_left _ _), grown⟩

/-- Every pressure collection of the run frees nothing. -/
def Fruitless (cfg : Config) : List Choice → State → Prop
  | [], _ => True
  | c :: rest, s => (Pressured cfg (s.lower cfg) → min c.pressureFreed s.garbage = 0) ∧
      ∀ after, step cfg c s = some after → Fruitless cfg rest after

theorem fruitless_log (cfg : Config) :
    ∀ (choices : List Choice) (fewest : Option Nat) (s : State), Census cfg s →
      Fruitless cfg choices s →
      ∀ entry ∈ pressureLog cfg fewest choices s, entry.after = entry.before := by
  intro choices
  induction choices with
  | nil => intro _ s _ _; simp [pressureLog]
  | cons c rest ih =>
    intro fewest s census fruitless entry member
    obtain ⟨nothing, later⟩ := fruitless
    simp only [pressureLog] at member
    split_ifs at member with pressured
    · rcases List.mem_cons.mp member with rfl | there
      · have := nothing pressured
        have := census.cached_le
        simp only [State.collect, State.inUse, State.lower]
        omega
      · cases stepped : step cfg c s with
        | none => rw [stepped] at there; simp at there
        | some after =>
          rw [stepped] at there
          exact ih _ after (step_census census stepped).1 (later after stepped) entry there
    · cases stepped : step cfg c s with
      | none => rw [stepped] at member; simp at member
      | some after =>
        rw [stepped] at member
        exact ih _ after (step_census census stepped).1 (later after stepped) entry member

/-- Two consecutive pressure collections that free nothing are the last ones
when no handle is freed between them and the one after, and the reserve at the
first is at most a quarter of the second's count (or the base reserve): the
first ran with less headroom than a quarter of its count plus that reserve,
and the threshold two collections on lies beyond what the limit allows. -/
theorem fruitless_pair_last (cfg : Config) (choices : List Choice) (fewest : Option Nat)
    (s : State) (census : Census cfg s) (tracks : Tracks cfg fewest s)
    {first second third : Collection} {before after : List Collection}
    (log : pressureLog cfg fewest choices s = before ++ first :: second :: third :: after)
    (firstFruitless : first.after = first.before) (secondFruitless : second.after = second.before)
    (steadySecond : second.low = first.after) (steadyThird : third.low = second.after)
    (smallReserve : first.reserve ≤ max cfg.reserve (second.before / 4)) : False := by
  obtain ⟨chain, _, entries⟩ := pressure_collections_spaced cfg choices fewest s census tracks
  rw [log] at chain entries
  have link := List.isChain_iff_forall_rel_of_append_cons_cons.mp chain
  have one : Spaced cfg first second := link (l₁ := before) (l₂ := third :: after) rfl
  have two : Spaced cfg second third :=
    link (l₁ := before ++ [first]) (l₂ := after) (by simp)
  have firstEntry := entries first (by simp)
  have thirdEntry := entries third (by simp)
  unfold Spaced at one two
  rw [steadySecond, firstFruitless] at one
  rw [steadyThird, secondFruitless] at two
  unfold grow at one two
  omega

private theorem grows_fifth {reserve a b : Nat} (grows : a + max reserve (a / 4) ≤ b) :
    5 * (a - 3) ≤ 4 * (b - 3) := by
  omega

private theorem chain_tail_geometric {reserve : Nat} :
    ∀ (a : Nat) (rest : List Nat),
      (a :: rest).IsChain (fun u v => u + max reserve (u / 4) ≤ v) →
      5 ^ rest.length * (a - 3) ≤
        4 ^ rest.length * ((a :: rest).getLast (List.cons_ne_nil _ _) - 3) := by
  intro a rest
  induction rest generalizing a with
  | nil => intro _; simp
  | cons b more ih =>
    intro chain
    rw [List.isChain_cons_cons] at chain
    have step := grows_fifth chain.1
    have tail := ih b chain.2
    rw [List.getLast_cons_cons]
    simp only [List.length_cons, pow_succ]
    calc 5 ^ more.length * 5 * (a - 3) = 5 ^ more.length * (5 * (a - 3)) := by ring
      _ ≤ 5 ^ more.length * (4 * (b - 3)) := Nat.mul_le_mul_left _ step
      _ = 4 * (5 ^ more.length * (b - 3)) := by ring
      _ ≤ 4 * (4 ^ more.length * ((b :: more).getLast (List.cons_ne_nil _ _) - 3)) :=
          Nat.mul_le_mul_left _ tail
      _ = 4 ^ more.length * 4 * ((b :: more).getLast (List.cons_ne_nil _ _) - 3) := by ring

/-- Counts that each grow by at least the reserve and a quarter: after the first
five, their number is logarithmic in their bound. -/
theorem chain_geometric {reserve bound : Nat} (reserve_pos : 0 < reserve) {counts : List Nat}
    (chain : counts.IsChain (fun u v => u + max reserve (u / 4) ≤ v))
    (bounded : ∀ u ∈ counts, u ≤ bound) (many : 5 ≤ counts.length) :
    5 ^ (counts.length - 5) ≤ 4 ^ (counts.length - 5) * bound := by
  match counts, many with
  | u0 :: u1 :: u2 :: u3 :: u4 :: rest, _ =>
    simp only [List.isChain_cons_cons] at chain
    obtain ⟨g0, g1, g2, g3, tail⟩ := chain
    have fourth : 4 ≤ u4 := by omega
    have geometric := chain_tail_geometric u4 rest tail
    have last : (u4 :: rest).getLast (List.cons_ne_nil _ _) ≤ bound :=
      bounded _ (by simp [List.getLast_mem])
    simp only [List.length_cons]
    have shift : rest.length + 1 + 1 + 1 + 1 + 1 - 5 = rest.length := by omega
    rw [shift]
    calc 5 ^ rest.length ≤ 5 ^ rest.length * (u4 - 3) :=
          Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ 4 ^ rest.length * ((u4 :: rest).getLast (List.cons_ne_nil _ _) - 3) := geometric
      _ ≤ 4 ^ rest.length * bound := Nat.mul_le_mul_left _ (by omega)

private theorem isChain_and {α : Type} {R S : α → α → Prop} :
    ∀ {items : List α}, items.IsChain R → items.IsChain S → items.IsChain fun a b => R a b ∧ S a b
  | [], _, _ => List.IsChain.nil
  | [_], _, _ => List.isChain_singleton _
  | _ :: _ :: _, first, second => by
    rw [List.isChain_cons_cons] at first second ⊢
    exact ⟨⟨first.1, second.1⟩, isChain_and first.2 second.2⟩

/-- When pressure collections free nothing and no handle is freed between them,
each runs with a quarter more in use than the previous one, so their number is
logarithmic in the limit. -/
theorem collections_geometric (cfg : Config) {choices : List Choice} {fewest : Option Nat}
    {s : State} (census : Census cfg s) (tracks : Tracks cfg fewest s)
    (fruitless : ∀ entry ∈ pressureLog cfg fewest choices s, entry.after = entry.before)
    (steady : (pressureLog cfg fewest choices s).IsChain fun earlier later =>
      later.low = earlier.after) :
    ((pressureLog cfg fewest choices s).map Collection.before).IsChain
        (fun u v => grow cfg u ≤ v) ∧
      (0 < cfg.reserve → 5 ≤ (pressureLog cfg fewest choices s).length →
        5 ^ ((pressureLog cfg fewest choices s).length - 5) ≤
          4 ^ ((pressureLog cfg fewest choices s).length - 5) * (cfg.limit - 1)) := by
  obtain ⟨chain, _, entries⟩ := pressure_collections_spaced cfg choices fewest s census tracks
  have counts : ((pressureLog cfg fewest choices s).map Collection.before).IsChain
      (fun u v => grow cfg u ≤ v) := by
    rw [List.isChain_map]
    refine (isChain_and chain steady).imp_of_mem_imp ?_
    intro earlier later earlierMember _ both
    obtain ⟨⟨_, grown, _⟩, sameLow⟩ := both
    rw [sameLow, fruitless earlier earlierMember] at grown
    exact grown
  refine ⟨counts, fun reserve_pos many => ?_⟩
  have := chain_geometric (bound := cfg.limit - 1) reserve_pos counts (by
      intro u member
      obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
      have := (entries entry entryMember).2.1
      omega)
    (by rw [List.length_map]; exact many)
  rwa [List.length_map] at this

/-! ## The previous rule, for comparison -/

namespace Previous

/-- The previous rule: a fixed reserve, and a threshold that moves only at a
pressure collection. -/
def Pressured (cfg : Config) (s : State) : Prop :=
  s.pressureAfter ≤ s.inUse ∧ s.headroom cfg < s.inUse / 4 + cfg.reserve

instance (cfg : Config) (s : State) : Decidable (Pressured cfg s) := by
  unfold Pressured; infer_instance

def safePoint (cfg : Config) (c : Choice) (s : State) : State :=
  if Pressured cfg s then (s.collect cfg c.pressureFreed c.retiring).relieve cfg
  else s.collect cfg c.heapFreed c.retiring

def step (cfg : Config) (c : Choice) (s : State) : Option State :=
  transition cfg c.events (safePoint cfg c s)

def run (cfg : Config) : List Choice → State → Option State
  | [], s => some s
  | c :: rest, s => (step cfg c s).bind (run cfg rest)

end Previous

/-! ## Checking concrete runs -/

/-- The hypotheses of `no_refusal`, checked along a concrete run up to its end
or its first refusal. -/
def obeysCheck (cfg : Config) (bound K retiredBound : Nat) : List Choice → State → Bool
  | [], _ => true
  | c :: rest, s =>
    decide (s.live ≤ bound) && decide (mints c.events ≤ K) &&
      (!decide (Pressured cfg (s.lower cfg)) || decide (s.garbage ≤ c.pressureFreed)) &&
      decide ((safePoint cfg c s).retired ≤ retiredBound) &&
      (!decide (s.reserve cfg < mints c.events) ||
        decide (mints c.events + (safePoint cfg c s).held + (safePoint cfg c s).retired ≤
          cfg.limit - 1)) &&
      match step cfg c s with
      | some after => obeysCheck cfg bound K retiredBound rest after
      | none => true

theorem obeysCheck_sound (cfg : Config) (bound K retiredBound : Nat) :
    ∀ (choices : List Choice) (s : State), obeysCheck cfg bound K retiredBound choices s = true →
      Obeys cfg bound K retiredBound choices s := by
  intro choices
  induction choices with
  | nil => intro _ _; trivial
  | cons c rest ih =>
    intro s checked
    simp only [obeysCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not] at checked
    obtain ⟨⟨⟨⟨⟨live, bounded⟩, full⟩, retired⟩, growing⟩, later⟩ := checked
    refine ⟨live, bounded, fun pressured => ?_, retired, fun larger => ?_,
      fun after stepped => ?_⟩
    · rcases full with notPressured | enough
      · exact absurd pressured notPressured
      · exact enough
    · rcases growing with notLarger | room
      · exact absurd larger notLarger
      · exact room
    · rw [stepped] at later
      exact ih after later

theorem run_append (cfg : Config) (first second : List Choice) (s : State) :
    run cfg (first ++ second) s = (run cfg first s).bind (run cfg second) := by
  induction first generalizing s with
  | nil => simp [run]
  | cons c rest ih =>
    simp only [List.cons_append, run]
    cases step cfg c s <;> simp [ih]

theorem heapRun_append (cfg : Config) (first second : List Choice) (s : State) :
    heapRun cfg (first ++ second) s = (heapRun cfg first s).bind (heapRun cfg second) := by
  induction first generalizing s with
  | nil => simp [heapRun]
  | cons c rest ih =>
    simp only [List.cons_append, heapRun]
    cases heapStep cfg c s <;> simp [ih]

/-! ## Controls -/

namespace Controls

/-- A step minting one identity that dies at once: the heap's own schedule
first releases `heapFreed`, and a pressure collection reaches everything. -/
def churn (cfg : Config) (heapFreed : Nat) : Choice := ⟨heapFreed, cfg.limit, 0, [.mint, .die]⟩

/-- A step minting one identity that stays live. -/
def keep (cfg : Config) : Choice := ⟨0, cfg.limit, 0, [.mint]⟩

/-- A step minting `count` identities that all die at once. -/
def burst (cfg : Config) (count : Nat) : Choice :=
  ⟨0, cfg.limit, 0, List.replicate count .mint ++ List.replicate count .die⟩

/-- A churn step whose pressure collection declines: the garbage is held by a
choice the collector cannot move. -/
def declined : Choice := ⟨0, 0, 0, [.mint, .die]⟩

/-! ### An allocation-threshold heap schedule alone -/

/-- What the threshold policy of `ResourceCollectionSchedule` releases at the
safe point before request `n`: everything if the previous request collected,
else nothing. -/
def thresholdFreed (cfg : Config) (headroom n : Nat) : Nat :=
  if (ResourceCollectionSchedule.run headroom n).collections =
      (ResourceCollectionSchedule.run headroom (n - 1)).collections then 0 else cfg.limit

/-- `n` churn steps under that schedule. -/
def thresholdChurn (cfg : Config) (headroom n : Nat) : List Choice :=
  (List.range n).map fun m => churn cfg (thresholdFreed cfg headroom m)

theorem thresholdFreed_early {cfg : Config} {headroom n : Nat} (early : n < headroom) :
    thresholdFreed cfg headroom n = 0 := by
  unfold thresholdFreed
  rw [if_pos]
  rw [(ResourceCollectionSchedule.Controls.no_collection_before_full early).1,
    (ResourceCollectionSchedule.Controls.no_collection_before_full
      (show n - 1 < headroom by omega)).1]

/-- A heap schedule that collects only after as many allocations as there are
handles keeps every dead structure's identity until none is left: the run is
refused. -/
theorem heap_threshold_refuses (cfg : Config) {headroom : Nat} (positive : 0 < cfg.limit)
    (wide : cfg.limit ≤ headroom) :
    heapRun cfg (thresholdChurn cfg headroom cfg.limit) start = none := by
  have early : ∀ j, j ≤ cfg.limit - 1 →
      heapRun cfg (thresholdChurn cfg headroom j) start = some ⟨0, j, 0, 0, 0, 0⟩ := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro bound
      unfold thresholdChurn at ih ⊢
      rw [List.range_succ, List.map_append, heapRun_append, ih (by omega)]
      simp only [List.map_cons, List.map_nil, Option.bind_some]
      rw [thresholdFreed_early (by omega)]
      have room : j < cfg.limit - 1 := by omega
      simp [heapRun, heapStep, transition, Event.apply, State.collect, State.headroom,
        State.inUse, churn, room]
  have last : cfg.limit = (cfg.limit - 1) + 1 := by omega
  rw [last]
  unfold thresholdChurn
  rw [List.range_succ, List.map_append, heapRun_append]
  have before := early (cfg.limit - 1) (Nat.le_refl _)
  unfold thresholdChurn at before
  rw [before]
  simp only [List.map_cons, List.map_nil, Option.bind_some]
  rw [thresholdFreed_early (by omega)]
  simp [heapRun, heapStep, transition, Event.apply, State.collect, State.headroom, State.inUse,
    churn]

private theorem mint_live {cfg : Config} {t u : State} (applied : Event.mint.apply cfg t = some u) :
    u.live = t.live + 1 ∧ u.retired = t.retired := by
  simp only [Event.apply] at applied
  split_ifs at applied <;> simp only [Option.some.injEq] at applied <;> subst applied <;>
    exact ⟨rfl, rfl⟩

theorem churn_step {cfg : Config} {s after : State} {heapFreed : Nat}
    (live : s.live = 0) (retired : s.retired = 0)
    (stepped : step cfg (churn cfg heapFreed) s = some after) :
    after.live = 0 ∧ after.retired = 0 := by
  have safeLive : (safePoint cfg (churn cfg heapFreed) s).live = 0 ∧
      (safePoint cfg (churn cfg heapFreed) s).retired = 0 := by
    unfold safePoint
    split_ifs <;> simp [State.relieve, State.collect, State.lower, churn, live, retired]
  unfold step at stepped
  obtain ⟨finished, transitioned, rfl⟩ := Option.map_eq_some_iff.mp stepped
  simp only [churn, transition] at transitioned
  cases minted : Event.mint.apply cfg (safePoint cfg (churn cfg heapFreed) s) with
  | none =>
    simp only [churn] at minted
    simp [minted] at transitioned
  | some u =>
    simp only [churn] at minted safeLive
    rw [minted, Option.bind_some] at transitioned
    obtain ⟨uLive, uRetired⟩ := mint_live minted
    simp only [Event.apply, uLive, safeLive.1] at transitioned
    simp only [Nat.lt_add_one, if_true, Option.bind_some, Option.some.injEq] at transitioned
    subst transitioned
    exact ⟨by simp [State.record], by simp [State.record, uRetired, safeLive.2]⟩

theorem churn_obeys (cfg : Config) (reserve_pos : 0 < cfg.reserve) :
    ∀ (choices : List Choice), (∀ c ∈ choices, ∃ heapFreed, c = churn cfg heapFreed) →
      ∀ s, Census cfg s → s.live = 0 → s.retired = 0 →
        Obeys cfg 0 1 0 choices s := by
  intro choices
  induction choices with
  | nil => intro _ _ _ _ _; trivial
  | cons c rest ih =>
    intro shaped s census live retired
    obtain ⟨heapFreed, rfl⟩ := shaped c (List.mem_cons_self ..)
    have fits := census.fits
    refine ⟨by omega, by simp [churn, mints], fun _ => ?_, ?_, fun larger => ?_,
      fun after stepped => ?_⟩
    · simp only [churn, State.inUse] at fits ⊢
      omega
    · unfold safePoint
      split_ifs <;> simp [State.relieve, State.collect, State.lower, churn, retired]
    · simp only [churn, mints, State.reserve] at larger
      omega
    · obtain ⟨afterLive, afterRetired⟩ := churn_step live retired stepped
      exact ih (fun c member => shaped c (List.mem_cons_of_mem _ member)) after
        (step_census census stepped).1 afterLive afterRetired

/-- With the pressure rule, the same run never refuses, however long. -/
theorem pressure_rule_completes (cfg : Config) (headroom n : Nat) (reserve_pos : 0 < cfg.reserve)
    (fit : accrual cfg 0 + 1 ≤ cfg.limit) :
    (run cfg (thresholdChurn cfg headroom n) start).isSome := by
  refine no_refusal_from_start cfg (bound := 0) (K := 1) (retiredBound := 0)
    reserve_pos (by simpa using fit) ?_
  refine churn_obeys cfg reserve_pos _ ?_ start (start_census cfg) rfl rfl
  intro c member
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp member
  exact ⟨_, rfl⟩

/-- The runtime's parameters: the heap schedule alone refuses a run of dead
structures holding one identity each, which the pressure rule completes at
every length. -/
theorem without_pressure_refuses :
    heapRun runtime (thresholdChurn runtime runtime.limit runtime.limit) start = none ∧
      ∀ n, (run runtime (thresholdChurn runtime runtime.limit n) start).isSome :=
  ⟨heap_threshold_refuses runtime (by decide) (Nat.le_refl _),
    fun n => pressure_rule_completes runtime _ n (by decide) (by decide)⟩

/-! ### A step larger than every earlier one -/

/-- Twenty single mints whose identities die leave little headroom; a step
minting ten, more than any before and than the base reserve, is then refused,
although the bound holds for steps of ten. -/
theorem growth_step_refused :
    obeysCheck ⟨30, 0, 2⟩ 0 10 0 (List.replicate 20 (churn ⟨30, 0, 2⟩ 0)) start = true ∧
      (run ⟨30, 0, 2⟩ (List.replicate 20 (churn ⟨30, 0, 2⟩ 0)) start).map
        (fun s => (s.reserve ⟨30, 0, 2⟩, (safePoint ⟨30, 0, 2⟩ (burst ⟨30, 0, 2⟩ 10) s).available
          ⟨30, 0, 2⟩)) = some (2, 9) ∧
      run ⟨30, 0, 2⟩ (List.replicate 20 (churn ⟨30, 0, 2⟩ 0) ++ [burst ⟨30, 0, 2⟩ 10]) start =
        none ∧
      accrual ⟨30, 0, 2⟩ 0 + 0 + 10 ≤ 30 := by decide +kernel

/-- The first step of ten comes with room; afterwards the reserve is ten, and
the next one, near the same in-use count, is covered: the bound applies. The
previous rule, whose reserve did not adapt, refuses that second step. -/
theorem growth_with_room_covered :
    (run ⟨30, 0, 2⟩
      ([burst ⟨30, 0, 2⟩ 10] ++ List.replicate 10 (churn ⟨30, 0, 2⟩ 0) ++ [burst ⟨30, 0, 2⟩ 10])
      start).isSome ∧
      Previous.run ⟨30, 0, 2⟩
        ([burst ⟨30, 0, 2⟩ 10] ++ List.replicate 10 (churn ⟨30, 0, 2⟩ 0) ++
          [burst ⟨30, 0, 2⟩ 10]) start = none := by
  refine ⟨no_refusal_from_start ⟨30, 0, 2⟩ (bound := 0) (K := 10) (retiredBound := 0)
    (by decide) (by decide) (obeysCheck_sound _ _ _ _ _ _ (by decide +kernel)),
    by decide +kernel⟩

/-! ### Collections that could not reach the garbage -/

/-- Pressure collections that decline, the garbage never freed: the threshold
stays beyond what the limit allows and the run is refused. -/
theorem declined_never_freed_refuses :
    run ⟨86, 64, 16⟩ (List.replicate 4 (keep ⟨86, 64, 16⟩) ++ List.replicate 400 declined)
      start = none := by decide +kernel

/-- Two pressure collections decline, raising the threshold to 90 with at most
85 handles; then the heap's own schedule frees the garbage, the threshold falls
to 85, and full pressure collections resume: the run completes. The previous
rule, whose threshold never fell, refuses it. -/
theorem rearmed_after_release :
    (run ⟨86, 64, 16⟩ (List.replicate 4 (keep ⟨86, 64, 16⟩) ++ List.replicate 69 declined ++
      [⟨86, 0, 0, [.mint, .die]⟩] ++ List.replicate 300 (churn ⟨86, 64, 16⟩ 0)) start).isSome ∧
      (pressureLog ⟨86, 64, 16⟩ none (List.replicate 4 (keep ⟨86, 64, 16⟩) ++
        List.replicate 69 declined ++ [⟨86, 0, 0, [.mint, .die]⟩] ++
        List.replicate 300 (churn ⟨86, 64, 16⟩ 0)) start).take 3 =
        [⟨56, 56, 56, 0, 16⟩, ⟨72, 72, 56, 0, 16⟩, ⟨85, 68, 68, 0, 16⟩] ∧
      grow ⟨86, 64, 16⟩ 72 = 90 ∧ grow ⟨86, 64, 16⟩ 68 = 85 ∧
      Previous.run ⟨86, 64, 16⟩ (List.replicate 4 (keep ⟨86, 64, 16⟩) ++
        List.replicate 69 declined ++ [⟨86, 0, 0, [.mint, .die]⟩] ++
        List.replicate 300 (churn ⟨86, 64, 16⟩ 0)) start = none := by decide +kernel

/-! ### The hypotheses are needed -/

/-- More live handles than the bound: every step keeps its identity, collections
free nothing, and the rule refuses too, when every handle is live. -/
theorem live_above_bound_refuses :
    run ⟨100, 64, 16⟩ (List.replicate 100 (keep ⟨100, 64, 16⟩)) start = none ∧
      (run ⟨100, 64, 16⟩ (List.replicate 99 (keep ⟨100, 64, 16⟩)) start).map
        (fun s => (s.live, s.garbage, s.cached, s.retired)) = some (99, 0, 0, 0) ∧
      accrual ⟨100, 64, 16⟩ 4 + 0 + 1 ≤ 100 := by decide +kernel

/-- One handle below `accrual + retired + K`: a run obeying every other
hypothesis is refused, and at the bound the same run completes. -/
theorem fit_exact :
    accrual ⟨5, 0, 2⟩ 1 + 0 + 2 = 5 ∧
      obeysCheck ⟨4, 0, 2⟩ 1 2 0 ([keep ⟨4, 0, 2⟩, churn ⟨4, 0, 2⟩ 0, churn ⟨4, 0, 2⟩ 0] ++
        List.replicate 11 (burst ⟨4, 0, 2⟩ 2)) start = true ∧
      run ⟨4, 0, 2⟩ ([keep ⟨4, 0, 2⟩, churn ⟨4, 0, 2⟩ 0, churn ⟨4, 0, 2⟩ 0] ++
        List.replicate 11 (burst ⟨4, 0, 2⟩ 2)) start = none ∧
      (run ⟨5, 0, 2⟩ ([keep ⟨5, 0, 2⟩, churn ⟨5, 0, 2⟩ 0, churn ⟨5, 0, 2⟩ 0] ++
        List.replicate 11 (burst ⟨5, 0, 2⟩ 2)) start).isSome := by decide +kernel

/-- The cache is in use for the census: with the runtime's cache and reserve,
four live handles and one mint a step, a run obeying every other hypothesis is
refused under a limit that a bound without the cache allows. -/
theorem cache_counts_in_use :
    accrual ⟨85, 64, 16⟩ 4 = 85 ∧ 4 + max 16 (4 / 4) + 0 + 1 ≤ 85 ∧
      obeysCheck ⟨85, 64, 16⟩ 4 1 0
        (List.replicate 4 (keep ⟨85, 64, 16⟩) ++ List.replicate 250 (churn ⟨85, 64, 16⟩ 0))
        start = true ∧
      run ⟨85, 64, 16⟩
        (List.replicate 4 (keep ⟨85, 64, 16⟩) ++ List.replicate 250 (churn ⟨85, 64, 16⟩ 0))
        start = none := by decide +kernel

/-- One handle more, at `accrual + K`, the bound applies to that run. -/
theorem cache_bound_applies :
    (run ⟨86, 64, 16⟩
      (List.replicate 4 (keep ⟨86, 64, 16⟩) ++ List.replicate 250 (churn ⟨86, 64, 16⟩ 0))
      start).isSome :=
  no_refusal_from_start ⟨86, 64, 16⟩ (bound := 4) (K := 1) (retiredBound := 0) (by decide)
    (by decide) (obeysCheck_sound _ _ _ _ _ _ (by decide +kernel))

/-! ### How many pressure collections -/

/-- One step of six hundred raises the reserve; its identities are released at
once, and single mints that stay live follow. Every pressure collection then
frees nothing and nothing is freed between them: there are six, each a quarter
beyond the previous one, more than two because the reserve exceeds a quarter
of the counts, and as few as `collections_geometric` requires. -/
theorem steady_fruitless_collections :
    pressureLog ⟨1000, 0, 16⟩ none
      (⟨0, 1000, 0, List.replicate 600 .mint ++ List.replicate 600 (.drop false)⟩ ::
        List.replicate 990 (keep ⟨1000, 0, 16⟩)) start =
      [⟨320, 320, 320, 0, 600⟩, ⟨400, 400, 320, 0, 600⟩, ⟨500, 500, 400, 0, 600⟩,
        ⟨625, 625, 500, 0, 600⟩, ⟨781, 781, 625, 0, 600⟩, ⟨976, 976, 781, 0, 600⟩] ∧
      5 ^ (6 - 5) ≤ 4 ^ (6 - 5) * (1000 - 1) := by decide +kernel

/-- Collections that free garbage are not few: a churn run completes with
twenty-four of them, beyond the logarithmic count. -/
theorem productive_collections_not_logarithmic :
    (run ⟨40, 0, 1⟩ (List.replicate 800 (churn ⟨40, 0, 1⟩ 0)) start).isSome ∧
      (pressureLog ⟨40, 0, 1⟩ none (List.replicate 800 (churn ⟨40, 0, 1⟩ 0)) start).length = 24 ∧
      ¬ 5 ^ (24 - 5) ≤ 4 ^ (24 - 5) * (40 - 1) := by decide +kernel

end Controls

end Mettapedia.Machines.IdentityPressureSchedule
