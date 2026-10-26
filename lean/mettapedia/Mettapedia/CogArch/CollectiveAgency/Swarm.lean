import Mettapedia.CogArch.CollectiveAgency.Lifecycle
import Mettapedia.GSLT.Causality.ResourceInstancePermission

/-!
# Swarms sharing physical space

A move consumes the agent's position and a free destination, producing the
new position and a free origin. Every cell and every agent has conserved
mass one. Collision freedom applies at this checked resource boundary;
unrestricted actuators can violate it. Membership withdrawal does not remove
a physical body or create a free cell.

The presentation reuses resource interactions, permissions and occurrence
paths. Independent moves commute at their endpoint while retaining different
orders. Safety does not imply that a desired rearrangement is reachable.
-/

set_option autoImplicit false

namespace Mettapedia.CogArch.CollectiveAgency.Swarm

open Mettapedia.GSLT.Causality.ResourceInteraction

inductive Token (A Cell : Type*) where
  | at (agent : A) (cell : Cell)
  | free (cell : Cell)
  deriving DecidableEq

structure Move (A Cell : Type*) where
  agent : A
  origin : Cell
  destination : Cell
  deriving DecidableEq

variable {A Cell : Type*} [DecidableEq A] [DecidableEq Cell]

def system (edge : Cell → Cell → Prop) : System (Token A Cell) where
  Site := PUnit
  Instance _ := {m : Move A Cell // edge m.origin m.destination}
  consume m := {.at m.val.agent m.val.origin, .free m.val.destination}
  read _ := 0
  produce m := {.at m.val.agent m.val.destination, .free m.val.origin}

def mass {T : Type*} (weight : T → Nat) (marking : Multiset T) : Nat := (marking.map weight).sum

def cellWeight (cell : Cell) : Token A Cell → Nat
  | .at _ c | .free c => if c = cell then 1 else 0

def agentWeight (agent : A) : Token A Cell → Nat
  | .at a _ => if a = agent then 1 else 0
  | .free _ => 0

def WellFormed (marking : Multiset (Token A Cell)) : Prop :=
  (∀ cell, mass (cellWeight cell) marking = 1) ∧
  (∀ agent, mass (agentWeight agent) marking = 1)

theorem mass_mono {T : Type*} (weight : T → Nat) {small large : Multiset T}
    (included : small ≤ large) : mass weight small ≤ mass weight large := by
  obtain ⟨rest, rfl⟩ := Multiset.le_iff_exists_add.mp included
  simp only [mass, Multiset.map_add, Multiset.sum_add]
  exact Nat.le_add_right _ _

theorem mass_one_excludes_pair {T : Type*} [DecidableEq T] (weight : T → Nat)
    (marking : Multiset T) (x y : T) (different : x ≠ y)
    (one : mass weight marking = 1) (wx : weight x = 1) (wy : weight y = 1)
    (presentX : x ∈ marking) (presentY : y ∈ marking) : False := by
  obtain ⟨rest, split⟩ := Multiset.le_iff_exists_add.mp (Multiset.singleton_le.mpr presentX)
  have inRest : y ∈ rest := by
    rw [split] at presentY
    simpa [different.symm] using presentY
  have bound := mass_mono weight (Multiset.singleton_le.mpr inRest)
  have total : mass weight marking = 1 + mass weight rest := by
    simp [split, mass, wx]
  have atLeast : 1 ≤ mass weight rest := by simpa [mass, wy] using bound
  omega

theorem no_collision (marking : Multiset (Token A Cell)) (safe : WellFormed marking)
    (a b : A) (cell : Cell) (different : a ≠ b)
    (pa : Token.at a cell ∈ marking) (pb : Token.at b cell ∈ marking) : False := by
  apply mass_one_excludes_pair (cellWeight cell) marking (.at a cell) (.at b cell)
    (by simpa using different) (safe.1 cell) (by simp [cellWeight]) (by simp [cellWeight]) pa pb

theorem no_duplicate_body (marking : Multiset (Token A Cell)) (safe : WellFormed marking)
    (a : A) (first second : Cell) (different : first ≠ second)
    (pa : Token.at a first ∈ marking) (pb : Token.at a second ∈ marking) : False := by
  apply mass_one_excludes_pair (agentWeight a) marking (.at a first) (.at a second)
    (by simpa using different) (safe.2 a) (by simp [agentWeight]) (by simp [agentWeight]) pa pb

theorem fire_mass (edge : Cell → Cell → Prop) (marking : Multiset (Token A Cell))
    (move : (system (A := A) edge).Instance PUnit.unit) (enabled : (system edge).Enables marking move)
    (weight : Token A Cell → Nat)
    (balanced : mass weight ((system edge).consume move) = mass weight ((system edge).produce move)) :
    mass weight ((system edge).fire marking move) = mass weight marking := by
  have h := congrArg (mass weight) ((system edge).fire_balance move enabled)
  simp only [mass, Multiset.map_add, Multiset.sum_add] at h balanced ⊢
  omega

theorem fire_wellFormed (edge : Cell → Cell → Prop) (marking : Multiset (Token A Cell))
    (move : (system (A := A) edge).Instance PUnit.unit) (enabled : (system edge).Enables marking move)
    (safe : WellFormed marking) : WellFormed ((system edge).fire marking move) := by
  constructor
  · intro cell
    rw [fire_mass edge marking move enabled (cellWeight cell)]
    · exact safe.1 cell
    · simp [system, mass, cellWeight, add_comm]
  · intro agent
    rw [fire_mass edge marking move enabled (agentWeight agent)]
    · exact safe.2 agent
    · simp [system, mass, agentWeight]

theorem run_wellFormed (edge : Cell → Cell → Prop) (entries : List (system (A := A) edge).Entry)
    {start finish : Multiset (Token A Cell)} (run : (system edge).Fires entries start finish)
    (safe : WellFormed start) : WellFormed finish := by
  induction entries generalizing start with
  | nil => exact run ▸ safe
  | cons entry rest ih =>
    obtain ⟨enabled, remaining⟩ := run
    cases entry with
    | mk site move =>
      cases site
      exact ih remaining (fire_wellFormed edge start move enabled safe)

/-- Permission checks augment the physical availability check. -/
def authorizedSystem {Task Resource Fact : Type*} [DecidableEq Task] [DecidableEq Fact]
    (edge : Cell → Cell → Prop) (coalition : Lifecycle.Body A Task Resource Fact)
    (actuator : A → Resource) (epoch : Nat) :=
  permittedSystem (system (A := A) edge)
    (fun move => Lifecycle.Authorized coalition move.val.agent epoch (actuator move.val.agent))

structure Deployment (A Task Resource Fact Cell : Type*) where
  team : Lifecycle.Machine A Task Resource Fact
  marking : Multiset (Token A Cell)
  halted : Finset A

/-- Local cessation requires no network acknowledgement. It does not claim
that other replicas have already recorded membership release. -/
def localStop {Task Resource Fact : Type*} (s : Deployment A Task Resource Fact Cell) (actor : A) :
    Deployment A Task Resource Fact Cell := { s with halted := insert actor s.halted }

/-- Checked actuation observes the current team state and physical marking
at application time. A cached grant or a free-space prediction is insufficient. -/
def moveChecked {Task Resource Fact : Type*}
    (edge : Cell → Cell → Prop) (actuator : A → Resource)
    (s : Deployment A Task Resource Fact Cell) (epoch : Nat)
    (move : (system (A := A) edge).Instance PUnit.unit) : Option (Deployment A Task Resource Fact Cell) :=
  if move.val.agent ∈ s.halted then none
  else if Lifecycle.Authorized s.team.body move.val.agent epoch (actuator move.val.agent) then
    if (system edge).consume move + (system edge).read move ≤ s.marking
    then some { s with marking := (system edge).fire s.marking move }
    else none
  else none

theorem moveChecked_iff {Task Resource Fact : Type*}
    (edge : Cell → Cell → Prop) (actuator : A → Resource)
    (s : Deployment A Task Resource Fact Cell) (epoch : Nat)
    (move : (system (A := A) edge).Instance PUnit.unit) :
    (∃ t, moveChecked edge actuator s epoch move = some t) ↔
      move.val.agent ∉ s.halted ∧
      Lifecycle.Authorized s.team.body move.val.agent epoch (actuator move.val.agent) ∧
        (system edge).Enables s.marking move := by
  simp only [moveChecked, System.Enables]
  split_ifs <;> simp_all

theorem checked_move_safe {Task Resource Fact : Type*}
    (edge : Cell → Cell → Prop) (actuator : A → Resource)
    (s t : Deployment A Task Resource Fact Cell) (epoch : Nat)
    (move : (system (A := A) edge).Instance PUnit.unit)
    (safe : WellFormed s.marking) (admitted : moveChecked edge actuator s epoch move = some t) :
    WellFormed t.marking ∧ t.team = s.team := by
  unfold moveChecked at admitted
  split_ifs at admitted
  cases admitted
  exact ⟨fire_wellFormed edge s.marking move (by assumption) safe, rfl⟩

theorem local_stop_blocks_actuation {Task Resource Fact : Type*}
    (edge : Cell → Cell → Prop) (actuator : A → Resource)
    (s : Deployment A Task Resource Fact Cell) (epoch : Nat)
    (move : (system (A := A) edge).Instance PUnit.unit) :
    moveChecked edge actuator (localStop s move.val.agent) epoch move = none := by
  simp [moveChecked, localStop]

omit [DecidableEq Cell] in
theorem local_stop_not_global_release {Task Resource Fact : Type*}
    (s : Deployment A Task Resource Fact Cell) (actor : A) :
    (localStop s actor).team = s.team ∧ (localStop s actor).marking = s.marking := ⟨rfl, rfl⟩

/-- Protocol commands, including withdrawal and dissolution, do not make
physical positions disappear. The caller still passes through authentication. -/
def protocolStep {Task Resource Fact : Type*} [DecidableEq Task] [DecidableEq Resource]
    [DecidableEq Fact] [Fintype Task] (profile : Lifecycle.ExitProfile)
    (principal : A) (s : Deployment A Task Resource Fact Cell)
    (request : Lifecycle.Request A Task Resource Fact) : Deployment A Task Resource Fact Cell :=
  { s with team := Lifecycle.submit profile principal s.team request }

omit [DecidableEq Cell] in
theorem protocol_preserves_bodies {Task Resource Fact : Type*} [DecidableEq Task]
    [DecidableEq Resource] [DecidableEq Fact] [Fintype Task] (profile : Lifecycle.ExitProfile)
    (principal : A) (s : Deployment A Task Resource Fact Cell)
    (request : Lifecycle.Request A Task Resource Fact) :
    (protocolStep profile principal s request).marking = s.marking := rfl

theorem independent_moves_commute (edge : Cell → Cell → Prop)
    (marking : Multiset (Token A Cell)) (first second : (system (A := A) edge).Instance PUnit.unit)
    (independent : (system edge).Concurrent marking first second) :
    (system edge).fire ((system edge).fire marking first) second =
      (system edge).fire ((system edge).fire marking second) first :=
  (system edge).fire_comm independent

/-! ## A corridor: safety does not imply rearrangement -/

/-- Unit-distance motion of either of two agents, into a cell not occupied
by the other. This coordinate presentation includes both movement directions. -/
inductive CorridorStep : Nat × Nat → Nat × Nat → Prop where
  | left {x y target : Nat} : (x + 1 = target ∨ target + 1 = x) → target ≠ y →
      CorridorStep (x, y) (target, y)
  | right {x y target : Nat} : (y + 1 = target ∨ target + 1 = y) → target ≠ x →
      CorridorStep (x, y) (x, target)

theorem corridor_order {s t : Nat × Nat} (ordered : s.1 < s.2) (move : CorridorStep s t) :
    t.1 < t.2 := by
  cases move with
  | left adjacent free => rcases adjacent with h | h <;> omega
  | right adjacent free => rcases adjacent with h | h <;> omega

theorem corridor_path_order {s t : Nat × Nat} (ordered : s.1 < s.2)
    (path : Relation.ReflTransGen CorridorStep s t) : t.1 < t.2 := by
  induction path with
  | refl => exact ordered
  | tail _ move ih => exact corridor_order ih move

theorem corridor_cannot_swap (x y : Nat) (ordered : x < y) :
    ¬ Relation.ReflTransGen CorridorStep (x, y) (y, x) := by
  intro path
  have backwards := corridor_path_order ordered path
  omega

namespace Controls

def triangle (x y : Fin 3) : Prop := x ≠ y
instance : DecidableRel triangle := fun x y => inferInstanceAs (Decidable (x ≠ y))
abbrev Triangle := system (A := Bool) triangle
def m0 : Multiset (Token Bool (Fin 3)) := {.at false 0, .at true 1, .free 2}
def m1 : Multiset (Token Bool (Fin 3)) := {.at false 2, .at true 1, .free 0}
def m2 : Multiset (Token Bool (Fin 3)) := {.at false 2, .at true 0, .free 1}
def m3 : Multiset (Token Bool (Fin 3)) := {.at false 1, .at true 0, .free 2}
def a02 : Triangle.Instance PUnit.unit := ⟨⟨false, 0, 2⟩, by decide⟩
def b10 : Triangle.Instance PUnit.unit := ⟨⟨true, 1, 0⟩, by decide⟩
def a21 : Triangle.Instance PUnit.unit := ⟨⟨false, 2, 1⟩, by decide⟩

theorem triangle_rearrangement :
    Triangle.Fires [⟨PUnit.unit, a02⟩, ⟨PUnit.unit, b10⟩, ⟨PUnit.unit, a21⟩] m0 m3 := by
  simp only [System.Fires, System.Enables]
  decide

theorem triangle_start_safe : WellFormed m0 := by
  unfold WellFormed
  constructor <;> decide

theorem triangle_finish_safe : WellFormed m3 :=
  run_wellFormed triangle _ triangle_rearrangement triangle_start_safe

theorem triangle_occurrence_path :
    ∃ path : Mettapedia.GSLT.Causality.OccurrenceHistory.OccurrencePath Triangle.presentation m0 m3,
      Triangle.pathEntries path = [⟨PUnit.unit, a02⟩, ⟨PUnit.unit, b10⟩, ⟨PUnit.unit, a21⟩] :=
  Triangle.exists_path_of_fires _ triangle_rearrangement

/-- A second move cannot consume the same free cell after the first. -/
def b12 : Triangle.Instance PUnit.unit := ⟨⟨true, 1, 2⟩, by decide⟩

theorem shared_destination_conflict :
    Triangle.Enables m0 a02 ∧ Triangle.Enables m0 b12 ∧
    ¬ Triangle.Enables (Triangle.fire m0 a02) b12 := by
  unfold System.Enables
  decide

def square (x y : Fin 4) : Prop := x ≠ y
instance : DecidableRel square := fun x y => inferInstanceAs (Decidable (x ≠ y))
abbrev Square := system (A := Bool) square
def separateStart : Multiset (Token Bool (Fin 4)) :=
  {.at false 0, .at true 2, .free 1, .free 3}
def separateEnd : Multiset (Token Bool (Fin 4)) :=
  {.at false 1, .at true 3, .free 0, .free 2}
def leftMove : Square.Instance PUnit.unit := ⟨⟨false, 0, 1⟩, by decide⟩
def rightMove : Square.Instance PUnit.unit := ⟨⟨true, 2, 3⟩, by decide⟩

theorem independent_orders :
    Square.Fires [⟨PUnit.unit, leftMove⟩, ⟨PUnit.unit, rightMove⟩] separateStart separateEnd ∧
    Square.Fires [⟨PUnit.unit, rightMove⟩, ⟨PUnit.unit, leftMove⟩] separateStart separateEnd := by
  simp only [System.Fires, System.Enables]
  decide

theorem same_endpoint_distinct_histories :
    ∃ first second : Mettapedia.GSLT.Causality.OccurrenceHistory.OccurrencePath
      Square.presentation separateStart separateEnd,
      Square.pathEntries first ≠ Square.pathEntries second := by
  obtain ⟨first, a⟩ := Square.exists_path_of_fires _ independent_orders.1
  obtain ⟨second, b⟩ := Square.exists_path_of_fires _ independent_orders.2
  refine ⟨first, second, ?_⟩
  rw [a, b]
  intro equal
  have impossible : (false : Bool) = true :=
    congrArg (fun entry : Square.Entry => entry.2.val.agent) (List.cons.inj equal).1
  cases impossible

theorem unrestricted_actuator_breaks_safety :
    ¬ WellFormed ({Token.at false (0 : Fin 3), .at true 0, .free 1, .free 2} :
      Multiset (Token Bool (Fin 3))) := by
  intro safe
  exact no_collision _ safe false true 0 (by decide) (by decide) (by decide)

end Controls

end Mettapedia.CogArch.CollectiveAgency.Swarm
