import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs.Determinacy
import Mettapedia.Logic.EvidenceKinds.Race

/-!
# Correct without confluence

A program need not be determinate to be correct. Correctness means that **every execution meets a
specification that allows several outcomes**: a property of the stores where runs stop
(`maximal_meets_spec`). The proof is an invariant of the reachable stores together with what being
stopped implies; no confluence is used.

## A first-come server

Two clients ask for one seat (`Controls.server`). The first to commit gets it; the other is told
the seat is gone, by a predicate query that sees no seat. The specification: exactly one client
wins and the other is refused (`Controls.Fair`).

* **Every maximal run meets the specification** (`Controls.server_just_works`).
* **The server is not determinate** (`Controls.server_two_outcomes`): two schedules give two
  winners. By `Determinacy` this is forced: the seat's name is not safe, since both clients hold
  `receive` there (`Controls.seat_not_safe`).

## A race publishes a sound result, whoever wins

The server is the race of `Logic.EvidenceKinds.Race`: the goal is the seat and the racers are the
clients, each with the dependency set of its proof. In every maximal run the winner closes the goal,
and the set it publishes is sound in every model in which the racers' proofs are
(`Controls.race_publishes_sound`, by `EvidenceKinds.published_sound`), although which set is
published depends on the schedule (`EvidenceKinds.Controls.published_depends_on_schedule`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes

universe uO uR

section Specs

variable {O : Type uO} [DecidableEq O] {R : Type uR} {label : O → R} {sys : Commit O R → Prop}

/-- An invariant preserved by every enabled commit holds at the end of every run. -/
theorem IsRun.preserves {invariant : Finset O → Prop}
    (preserved : ∀ t c, invariant t → sys c → Enabled label t c → invariant (fire t c))
    {store : Finset O} {run : List (Commit O R)} (isRun : IsRun label sys store run)
    (holds : invariant store) : invariant (fireList store run) := by
  induction run generalizing store with
  | nil => exact holds
  | cons c rest ih =>
      obtain ⟨member, enabled, isRest⟩ := isRun_cons_iff.mp isRun
      exact ih isRest (preserved store c holds member enabled)

/-- **Correct without confluence.** If an invariant holds at the start and is preserved by every
enabled commit, and the specification holds wherever the invariant holds and nothing is enabled,
then every maximal run ends where the specification holds, whichever outcome the schedule picks. -/
theorem maximal_meets_spec {invariant spec : Finset O → Prop} {store : Finset O}
    (initially : invariant store)
    (preserved : ∀ t c, invariant t → sys c → Enabled label t c → invariant (fire t c))
    (stopped : ∀ t, invariant t → Terminal label sys t → spec t) {run : List (Commit O R)}
    (maximal : Maximal label sys store run) : spec (fireList store run) :=
  stopped _ (IsRun.preserves preserved maximal.1 initially) maximal.2

end Specs

namespace Controls

open Mettapedia.Logic.EvidenceKinds

/-- The seat and everything else. -/
inductive Place where
  | seat
  | other
  deriving DecidableEq, Repr

/-- Occurrence `0` is the seat. -/
def placeOf (o : ℕ) : Place := if o = 0 then .seat else .other

/-- The region of the seat. -/
def isSeat : Place → Bool
  | .seat => true
  | .other => false

/-- Client `i` (request `i`) takes the seat and wins (identity `10 + i`). -/
def grant (i : ℕ) : Commit ℕ Place := ⟨{0, i}, ∅, {10 + i}, []⟩

/-- Client `i` is refused (identity `20 + i`) when no seat is present. -/
def refuse (i : ℕ) : Commit ℕ Place := ⟨{i}, ∅, {20 + i}, [⟨isSeat, ∅⟩]⟩

/-- The commits of the server. -/
def serverCommits : List (Commit ℕ Place) := [grant 1, grant 2, refuse 1, refuse 2]

/-- The first-come server for two clients. -/
def server : Commit ℕ Place → Prop := fun c => c ∈ serverCommits

/-- The stores the server can reach from the seat and two requests. -/
def reachable : List (Finset ℕ) := [{0, 1, 2}, {2, 11}, {1, 12}, {11, 22}, {12, 21}]

/-- **The specification**: exactly one client wins and the other is refused. -/
def Fair (t : Finset ℕ) : Prop :=
  (11 ∈ t ∧ 22 ∈ t ∧ 12 ∉ t ∧ 21 ∉ t) ∨ (12 ∈ t ∧ 21 ∈ t ∧ 11 ∉ t ∧ 22 ∉ t)

instance (t : Finset ℕ) : Decidable (Fair t) := by unfold Fair; infer_instance

theorem reachable_closed :
    ∀ t ∈ reachable, ∀ c ∈ serverCommits, Enabled placeOf t c → fire t c ∈ reachable := by
  decide

theorem reachable_stopped :
    ∀ t ∈ reachable, (∀ c ∈ serverCommits, ¬ Enabled placeOf t c) → Fair t := by
  decide

/-- **The server just works**: every maximal run ends with exactly one winner and one refusal. -/
theorem server_just_works {run : List (Commit ℕ Place)} (maximal : Maximal placeOf server {0, 1, 2} run) :
    Fair (fireList {0, 1, 2} run) :=
  maximal_meets_spec (invariant := fun t => t ∈ reachable) (by decide)
    (fun t c inReach member enabled => reachable_closed t inReach c member enabled)
    (fun t inReach terminal => reachable_stopped t inReach fun c member => terminal c member)
    maximal

theorem server_terminal_one : Terminal placeOf server {11, 22} := by
  intro c member
  simp only [server, serverCommits, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

theorem server_terminal_two : Terminal placeOf server {12, 21} := by
  intro c member
  simp only [server, serverCommits, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

/-- **The server is not determinate**: two maximal runs give two winners. -/
theorem server_two_outcomes :
    Maximal placeOf server {0, 1, 2} [grant 1, refuse 2] ∧
      Maximal placeOf server {0, 1, 2} [grant 2, refuse 1] ∧
      fireList ({0, 1, 2} : Finset ℕ) [grant 1, refuse 2] ≠ fireList ({0, 1, 2} : Finset ℕ) [grant 2, refuse 1] := by
  refine ⟨⟨⟨.cons (by decide) (.cons (by decide) (.nil _)), by simp [server, serverCommits]⟩, ?_⟩,
    ⟨⟨.cons (by decide) (.cons (by decide) (.nil _)), by simp [server, serverCommits]⟩, ?_⟩, by decide⟩
  · rw [show fireList ({0, 1, 2} : Finset ℕ) [grant 1, refuse 2] = {11, 22} by decide]
    exact server_terminal_one
  · rw [show fireList ({0, 1, 2} : Finset ℕ) [grant 2, refuse 1] = {12, 21} by decide]
    exact server_terminal_two

/-- The names of the server: the seat, and everything else. Both clients hold `receive` at the
seat. -/
def clientRights : Bool → Rights Place
  | _, .seat, .receive => true
  | _, .other, _ => true
  | _, _, _ => false

/-- **Why it cannot be determinate**: the seat's name is not safe; both clients hold `receive`
there. -/
theorem seat_not_safe : ¬ SafeAt clientRights .seat := fun safe => by
  have := safe false true (by decide) .receive .receive rfl rfl
  simp [conflicts] at this

/-! ### The race -/

/-- **A race publishes a sound result, whoever wins.** Client `1` and client `2` race for the goal
(the seat), with dependency sets `deps₁` and `deps₂`. In every maximal run the winner closes the goal
and publishes its set, which is sound in every model in which both racers' proofs are. -/
theorem race_publishes_sound {World Dep : Type} {holdsAtom : World → Dep → Prop}
    {claim : World → Prop} {deps₁ deps₂ : Finset Dep} (sound₁ : Sound holdsAtom claim deps₁)
    (sound₂ : Sound holdsAtom claim deps₂) {run : List (Commit ℕ Place)}
    (maximal : Maximal placeOf server {0, 1, 2} run) :
    ∃ closing : Closing [deps₁, deps₂], 10 + (closing.val + 1) ∈ fireList {0, 1, 2} run ∧
      Sound holdsAtom claim (published closing) := by
  have sounds : ∀ deps ∈ [deps₁, deps₂], Sound holdsAtom claim deps := by
    intro deps member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact sound₁
    · exact sound₂
  rcases server_just_works maximal with ⟨one, _⟩ | ⟨two, _⟩
  · exact ⟨⟨0, by simp⟩, one, published_sound sounds _⟩
  · exact ⟨⟨1, by simp⟩, two, published_sound sounds _⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs
