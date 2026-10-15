import Mettapedia.Machines.Cursor.SharedFactor
import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Mettapedia.GSLT.Distinction.SimulationComposition
import Mettapedia.GSLT.Dynamics.MemoizationObserver
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Shared answer factors in the common resumable machine interface

The flat specification and indexed factor implementation both inhabit the
existing productive machine. They preserve every finite observation and its
decoded residual, including exhaustion, genuine completion, cancelled readers,
waiting for a producer and invalid cursors. Waiting does not execute a host
effect. An owner may handle that request using the existing service interface.

This connects a regional delivery machine to the shared contract. It does not
identify eager, logic-programming and call-by-need evaluation strategies.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.SharedFactorMachine

open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.Dynamics.OrderedDemand (Observation)

variable {Input Value : Type} {clients : Nat}

abbrev Checked (Input Value : Type) (clients : Nat) :=
  { state : SharedFactor.State Input Value clients // state.view.Valid state.backing }

def reposition (state : Checked Input Value clients) (client : Fin clients) (position : Option Nat) :
    Checked Input Value clients :=
  ⟨SharedFactor.setPosition state.val client position, state.property⟩

def compactReader (lower : Nat) (state : Checked Input Value clients)
    (before : lower ≤ state.val.view.start) : Checked Input Value clients :=
  ⟨SharedFactor.trimBefore lower state.val,
    SharedFactor.trimBefore_valid lower state.val state.property before⟩

/-- The verdict distinguishes exhaustion of the producer from consumer
cancellation. A waiting producer suspends with the complete reader state. -/
def indexed (client : Fin clients) :
    Machine (Checked Input Value clients) (Nat × (Input × Value)) Bool Unit where
  step state := match SharedFactor.peek state.val client with
    | .answer position value => some (.publish [(position, value)]
        (reposition state client (some (position + 1))))
    | .paused => some (.call () state)
    | .completed => some (.finish true)
    | .cancelled => some (.finish false)
    | .invalid => none

def flat (client : Fin clients) :
    Machine (SharedOccurrenceLog.State (Input × Value) clients) (Nat × (Input × Value)) Bool Unit where
  step state := match SharedOccurrenceLog.peek state client with
    | .answer position value => some (.publish [(position, value)]
        (SharedOccurrenceLog.setPosition state client (some (position + 1))))
    | .paused => some (.call () state)
    | .completed => some (.finish true)
    | .cancelled => some (.finish false)
    | .invalid => none

def readback (outcome : Outcome (Checked Input Value clients) Bool Unit) :
    Outcome (SharedOccurrenceLog.State (Input × Value) clients) Bool Unit :=
  match outcome with
  | .finished result => .finished result
  | .faulted => .faulted
  | .suspended request saved => .suspended request (SharedFactor.decode saved.val)
  | .stuck state => .stuck (SharedFactor.decode state.val)
  | .exhausted state => .exhausted (SharedFactor.decode state.val)

/-- The actual indexed machine and independent flat machine agree for every
finite budget, with the same ordered occurrences and complete decoded outcome. -/
theorem run_readback (fuel : Nat) (state : Checked Input Value clients) (client : Fin clients) :
    ((indexed client).run fuel state).1 =
      ((flat client).run fuel (SharedFactor.decode state.val)).1 ∧
    readback ((indexed client).run fuel state).2 =
      ((flat client).run fuel (SharedFactor.decode state.val)).2 := by
  induction fuel generalizing state with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
      have same := SharedFactor.peek_decode state.val client state.property
      cases reply : SharedFactor.peek state.val client with
      | answer position value =>
          have next := ih (reposition state client (some (position + 1)))
          simp only [Machine.run, indexed, reply, flat, ← same,
            reposition, SharedFactor.decode_setPosition, List.singleton_append] at next ⊢
          exact ⟨congrArg (List.cons (position, value)) next.1, next.2⟩
      | paused => simp only [Machine.run, indexed, reply, flat, ← same, readback]; trivial
      | completed => simp only [Machine.run, indexed, reply, flat, ← same, readback]; trivial
      | cancelled => simp only [Machine.run, indexed, reply, flat, ← same, readback]; trivial
      | invalid => simp only [Machine.run, indexed, reply, flat, ← same, readback]; trivial

/-- Exact finite observations include terminal, suspended and incomplete
statuses. The retained state is related separately by `run_readback`. -/
theorem observe_readback (fuel : Nat) (state : Checked Input Value clients)
    (client : Fin clients) :
    (indexed client).observe fuel state =
      (flat client).observe fuel (SharedFactor.decode state.val) := by
  obtain ⟨events, outcome⟩ := run_readback fuel state client
  have status : ∀ saved : Outcome (Checked Input Value clients) Bool Unit,
      (readback saved).status = saved.status := by
    intro saved
    cases saved <;> rfl
  exact congrArg₂ Observation.mk events
    (by simpa only [Machine.observe, status] using congrArg Outcome.status outcome)

/-- Migrating a suffix preserves every finite observation, including a
consumer paused partway through it. Migration does not reset its bookmark. -/
theorem compactReader_observe (lower fuel : Nat) (state : Checked Input Value clients)
    (before : lower ≤ state.val.view.start) (client : Fin clients) :
    (indexed client).observe fuel (compactReader lower state before) =
      (indexed client).observe fuel state := by
  rw [observe_readback, observe_readback]
  exact congrArg ((flat client).observe fuel)
    (SharedFactor.trimBefore_decode lower state.val state.property before)

/-- The decoder is an actual unit-bound simulation in the shared machine
theory. It transfers requests with their saved reader positions. -/
theorem decoder_simulation (client : Fin clients) :
    CostSimulation (indexed (Input := Input) (Value := Value) client) (flat client)
      (fun state decoded => SharedFactor.decode state.val = decoded) 1 where
  silent := by
    rintro state decoded next rfl stepped
    cases reply : SharedFactor.peek state.val client <;>
      simp [indexed, reply] at stepped
  publish := by
    rintro state decoded events next rfl stepped
    have same := SharedFactor.peek_decode state.val client state.property
    cases reply : SharedFactor.peek state.val client <;>
      simp [indexed, reply] at stepped
    rcases stepped with ⟨rfl, rfl⟩
    refine ⟨1, le_rfl, _, ?_, rfl⟩
    simp [Machine.run, flat, ← same, reply, reposition, SharedFactor.decode_setPosition]
  finish := by
    rintro state decoded verdict rfl stepped
    have same := SharedFactor.peek_decode state.val client state.property
    cases reply : SharedFactor.peek state.val client <;>
      simp [indexed, reply] at stepped
    all_goals subst verdict; exact ⟨1, le_rfl, by simp [Machine.run, flat, ← same, reply]⟩
  fail := by
    rintro state decoded events rfl stepped
    cases reply : SharedFactor.peek state.val client <;>
      simp [indexed, reply] at stepped
  call := by
    rintro state decoded request saved rfl stepped
    have same := SharedFactor.peek_decode state.val client state.property
    cases reply : SharedFactor.peek state.val client <;>
      simp [indexed, reply] at stepped
    rcases stepped with ⟨rfl, rfl⟩
    exact ⟨1, le_rfl, SharedFactor.decode state.val,
      by simp [Machine.run, flat, ← same, reply], rfl⟩

/-- A qualified regional stage can compose with other stages in the existing
theory. Completion is reflected by exact observations at the same budget. -/
def decoderStage (client : Fin clients) :
    Stage (indexed (Input := Input) (Value := Value) client) (flat client) where
  related := fun state decoded => SharedFactor.decode state.val = decoded
  cost := 1
  forward := decoder_simulation client
  reflects := by
    rintro state decoded rfl fuel _
    exact ⟨fuel, observe_readback fuel state client⟩

/-- Composition retains the following stage's cost because decoding matches
one indexed transition with one specified transition. -/
theorem stitched_cost {Target : Type}
    {target : Machine Target (Nat × (Input × Value)) Bool Unit}
    (client : Fin clients) (following : Stage (flat client) target) :
    ((decoderStage client).comp following).cost = following.cost := by
  simp [Stage.comp, decoderStage]

/-- Pausing consumes a budget without reloading the source or repeating any
already published occurrence. The shared runner's exact law applies directly. -/
theorem resume_exact (first second : Nat) (state : Checked Input Value clients) (client : Fin clients) :
    (indexed client).run (first + second) state =
      (indexed client).continueRun second ((indexed client).run first state) :=
  Machine.run_add _ first second state

theorem run_events_eq_drain (fuel : Nat) (state : Checked Input Value clients) (client : Fin clients) :
    ((indexed client).run fuel state).1 = (SharedFactor.drain fuel state.val client).1 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases reply : SharedFactor.peek state.val client with
      | answer position value =>
          simp only [Machine.run, indexed, reply,
            SharedFactor.drain_answer _ _ _ _ _ reply, List.singleton_append]
          exact congrArg (List.cons (position, value))
            (ih (reposition state client (some (position + 1))))
      | paused | completed | cancelled | invalid =>
          have stopped : ∀ position value,
              SharedFactor.peek state.val client ≠ .answer position value := by simp [reply]
          simp only [Machine.run, indexed, reply, SharedFactor.drain_stopped _ _ _ stopped]

/-- Every occurrence requested by this reader is delivered once, up to the
budget. Payload equality never affects the count. -/
theorem delivery_count (fuel : Nat) (state : Checked Input Value clients)
    (client : Fin clients) (position : Nat) (present : state.val.positions client = some position) :
    ((indexed client).run fuel state).1.length =
      min fuel (state.val.view.stop - state.val.view.start - position) := by
  rw [run_events_eq_drain]
  have decode := congrArg Prod.fst (SharedFactor.drain_decode fuel state.val client state.property)
  have specification := (SharedOccurrenceLog.drain_spec fuel (SharedFactor.decode state.val)
    client position present (Nat.zero_le _)).1
  rw [decode, specification]
  simp only [SharedFactor.decode, Nat.sub_zero, List.length_take,
    SharedOccurrenceLog.numberFrom_length, List.length_drop,
    SharedFactor.length_records _ _ state.property]

/-- A regional primitive plan: an answer takes a bounds check, indexed read,
publication and acknowledgment. Terminal/waiting inspection costs one. -/
def price (client : Fin clients) (state : Checked Input Value clients) : Nat :=
  match SharedFactor.peek state.val client with
  | .answer _ _ => 4
  | _ => 1

theorem spent_le_deliveries (fuel : Nat) (state : Checked Input Value clients) (client : Fin clients) :
    (indexed client).spent (price client) fuel state ≤
      4 * ((indexed client).run fuel state).1.length + 1 := by
  induction fuel generalizing state with
  | zero => simp only [Machine.spent, Machine.run, List.length_nil]; omega
  | succ fuel ih =>
      cases reply : SharedFactor.peek state.val client with
      | answer position value =>
          have bound := ih (reposition state client (some (position + 1)))
          simp only [Machine.spent, Machine.run, indexed, reply, price,
            List.singleton_append, List.length_cons] at bound ⊢
          omega
      | paused | completed | cancelled | invalid =>
          simp only [Machine.spent, Machine.run, indexed, reply, price, List.length_nil]
          omega

/-- Every published occurrence incurs its four delivery primitives, even
when equal payloads share storage. Internal scheduling cannot erase output. -/
theorem deliveries_le_spent (fuel : Nat) (state : Checked Input Value clients)
    (client : Fin clients) :
    4 * ((indexed client).run fuel state).1.length ≤
      (indexed client).spent (price client) fuel state := by
  induction fuel generalizing state with
  | zero => simp only [Machine.spent, Machine.run, List.length_nil]; omega
  | succ fuel ih =>
      cases reply : SharedFactor.peek state.val client with
      | answer position value =>
          have bound := ih (reposition state client (some (position + 1)))
          simp only [Machine.spent, Machine.run, indexed, reply, price,
            List.singleton_append, List.length_cons] at bound ⊢
          omega
      | paused | completed | cancelled | invalid =>
          simp only [Machine.spent, Machine.run, indexed, reply, price, List.length_nil]
          omega

theorem spent_resume_exact (first second : Nat) (state : Checked Input Value clients)
    (client : Fin clients) :
    (indexed client).spent (price client) (first + second) state =
      (indexed client).spent (price client) first state +
        (indexed client).spentAfter (price client) second ((indexed client).run first state).2 :=
  Machine.spent_add _ _ first second state

private def sample : Checked Nat Nat 2 :=
  ⟨⟨#[7, 7, 9], ⟨41, 0, 3, true⟩, fun _ => some 0⟩, by constructor <;> decide⟩

theorem repeated_payloads_are_distinct_occurrences :
    ((indexed 0).run 4 sample).1 = [(0, (41, 7)), (1, (41, 7)), (2, (41, 9))] := by decide

theorem waiting_retains_residual :
    (indexed 0).run 1 (⟨⟨#[], ⟨0, 0, 0, false⟩, fun _ => some 0⟩,
      by constructor <;> decide⟩ : Checked Nat Nat 1) =
      ([], .suspended () ⟨⟨#[], ⟨0, 0, 0, false⟩, fun _ => some 0⟩, by constructor <;> decide⟩) := rfl

theorem restart_repeats_delivered_occurrence :
    ((indexed 0).run 1 sample).1 ++ ((indexed 0).run 1 sample).1 ≠
      ((indexed 0).run 2 sample).1 := by decide

/-! ## Observation boundaries and retained distinctions -/

/-- The retained occurrence state serves every finite delivery observation.
This is a semantic readout; it does not prescribe an enumerating runtime key. -/
theorem decoded_observation_factors (fuel : Nat) (client : Fin clients) :
    Mettapedia.GSLT.Core.NonFactorization.Factors
      (fun state : Checked Input Value clients => SharedFactor.decode state.val)
      ((indexed client).observe fuel) := by
  refine ⟨(flat client).observe fuel, ?_⟩
  intro state
  exact (observe_readback fuel state client).symm

/-- Any equal decoded residuals have equal finite observations, including
completion and suspension. Equality of an already delivered prefix is weaker. -/
theorem decoded_observation_sound (fuel : Nat) (client : Fin clients) :
    Mettapedia.GSLT.Dynamics.MemoizationObserver.SoundKey
      (fun state : Checked Input Value clients => SharedFactor.decode state.val)
      ((indexed client).observe fuel) :=
  (decoded_observation_factors fuel client).constantOnFibers

private def prefixLeft : Checked Nat Nat 1 :=
  ⟨⟨#[7, 8], ⟨41, 0, 2, true⟩, fun _ => some 0⟩, by constructor <;> decide⟩

private def prefixRight : Checked Nat Nat 1 :=
  ⟨⟨#[7, 9], ⟨41, 0, 2, true⟩, fun _ => some 0⟩, by constructor <;> decide⟩

/-- Two computations have the same first delivery and different unread work.
A prefix observation cannot identify their resumable computations. -/
def prefixFiber : Mettapedia.GSLT.Core.NonFactorization.NonTrivialFiber
    (fun state : Checked Nat Nat 1 => ((indexed 0).run 1 state).1)
    ((indexed 0).observe 2) where
  left := prefixLeft
  right := prefixRight
  sameShadow := by decide
  differentValue := by decide

theorem prefix_cannot_key_future :
    ¬ Mettapedia.GSLT.Dynamics.MemoizationObserver.SoundKey
      (fun state : Checked Nat Nat 1 => ((indexed 0).run 1 state).1)
      ((indexed 0).observe 2) :=
  prefixFiber.not_constantOnFibers

private def layoutSample : Checked Nat Nat 1 :=
  ⟨⟨#[7, 8, 9], ⟨41, 2, 3, true⟩, fun _ => some 0⟩, by constructor <;> decide⟩

/-- Compaction preserves the full delivery readback while changing allocation
size. A storage-layout observer requires more retained information than that
readback supplies. -/
def layoutFiber : Mettapedia.GSLT.Core.NonFactorization.NonTrivialFiber
    (fun state : Checked Nat Nat 1 => SharedFactor.decode state.val)
    (fun state => state.val.backing.size) where
  left := layoutSample
  right := compactReader 2 layoutSample (by decide)
  sameShadow := (SharedFactor.trimBefore_decode 2 layoutSample.val
    layoutSample.property (by decide)).symm
  differentValue := by decide

theorem layout_does_not_factor_through_delivery :
    ¬ Mettapedia.GSLT.Core.NonFactorization.Factors
      (fun state : Checked Nat Nat 1 => SharedFactor.decode state.val)
      (fun state => state.val.backing.size) :=
  layoutFiber.not_factors

end Mettapedia.Machines.Cursor.SharedFactorMachine
