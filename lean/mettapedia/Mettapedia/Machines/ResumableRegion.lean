import Mettapedia.Machines.MachineRefinement

/-!
# Bounded execution retaining its residual machine state

A finite region returns both its exact residual and the number of transitions
taken. Splitting a run does not restart it or repeat a debit. Exhausting the
region budget is not a final-state certificate. A final state may be a normal
completion or a stuck state; its observation belongs to the particular machine.

This extends `MachineCore`, independently of eager or demand-driven control.
Its unit transition count is not a claim about physical work, semantic fuel in
another language, or the latency of an individual transition.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.MachineCore

variable {Term OtherTerm : Type}

def runSlice (machine : MachineCore Term) : Nat → machine.State → machine.State × Nat
  | 0, state => (state, 0)
  | fuel + 1, state =>
      match machine.step state with
      | none => (state, 0)
      | some next =>
          let remaining := runSlice machine fuel next
          (remaining.1, remaining.2 + 1)

/-- A bounded region reaches its retained endpoint by actual machine steps. -/
theorem runSlice_steps (machine : MachineCore Term) (fuel : Nat)
    (state : machine.State) : machine.Steps state (runSlice machine fuel state).1 := by
  induction fuel generalizing state with
  | zero => exact Relation.ReflTransGen.refl
  | succ fuel ih =>
      cases advanced : machine.step state with
      | none =>
          simpa only [runSlice, advanced] using
            (Relation.ReflTransGen.refl : machine.Steps state state)
      | some next =>
          have step : machine.StepRel state next := advanced
          simpa only [runSlice, advanced] using
            Relation.ReflTransGen.head step (ih next)

theorem runSlice_of_final (machine : MachineCore Term) (state : machine.State)
    (final : machine.step state = none) (fuel : Nat) :
    runSlice machine fuel state = (state, 0) := by
  cases fuel <;> simp [runSlice, final]

/-- Exact residual composition, with additive accounting only for transitions
actually performed. The second slice starts at the first slice's endpoint. -/
theorem runSlice_add (machine : MachineCore Term) (first second : Nat)
    (state : machine.State) :
    runSlice machine (first + second) state =
      let earlier := runSlice machine first state
      let later := runSlice machine second earlier.1
      (later.1, earlier.2 + later.2) := by
  induction first generalizing state with
  | zero => simp [runSlice]
  | succ first ih =>
      cases transition : machine.step state with
      | none => simp [Nat.succ_add, runSlice, transition,
          runSlice_of_final machine state transition]
      | some next =>
          simp only [Nat.succ_add, runSlice, transition]
          rw [ih]

theorem runSlice_used_le (machine : MachineCore Term) (fuel : Nat)
    (state : machine.State) :
    (runSlice machine fuel state).2 ≤ fuel := by
  induction fuel generalizing state with
  | zero => simp [runSlice]
  | succ fuel ih =>
      cases transition : machine.step state with
      | none => simp [runSlice, transition]
      | some next => simpa [runSlice, transition] using Nat.add_le_add_right (ih next) 1

/-- A retained invocation carries its incoming debit into the next slice.
The entire machine state is retained, independently of its representation. -/
def paidSlice (machine : MachineCore Term) (fuel : Nat)
    (packet : Nat × machine.State) : Nat × machine.State :=
  let result := runSlice machine fuel packet.2
  (packet.1 + result.2, result.1)

@[simp] theorem paidSlice_zero (machine : MachineCore Term)
    (packet : Nat × machine.State) : paidSlice machine 0 packet = packet := by
  simp [paidSlice, runSlice]

theorem paidSlice_add (machine : MachineCore Term) (first second : Nat)
    (packet : Nat × machine.State) :
    paidSlice machine (first + second) packet =
      paidSlice machine second (paidSlice machine first packet) := by
  have combined := runSlice_add machine first second packet.2
  have paid := congrArg (fun result : machine.State × Nat =>
    (packet.1 + result.2, result.1)) combined
  simpa only [paidSlice, Nat.add_assoc] using paid

theorem paidSlice_debit_bounds (machine : MachineCore Term) (fuel : Nat)
    (packet : Nat × machine.State) :
    packet.1 ≤ (paidSlice machine fuel packet).1 ∧
      (paidSlice machine fuel packet).1 ≤ packet.1 + fuel := by
  have bounded := runSlice_used_le machine fuel packet.2
  dsimp only [paidSlice]
  omega

theorem paidSlice_of_final (machine : MachineCore Term) (state : machine.State)
    (final : machine.step state = none) (fuel incoming : Nat) :
    paidSlice machine fuel (incoming, state) = (incoming, state) := by
  simp [paidSlice, runSlice_of_final machine state final]

/-- The actual debit replays exactly the retained endpoint and debit, even
when the supplied allowance extends beyond a final state. -/
theorem runSlice_replay_used (machine : MachineCore Term) (fuel : Nat)
    (state : machine.State) :
    runSlice machine (runSlice machine fuel state).2 state =
      runSlice machine fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases transition : machine.step state with
      | none => simp only [runSlice, transition]
      | some next =>
          simp only [runSlice, transition]
          rw [ih]

/-- Stopping strictly before the supplied budget certifies no further step.
Using the whole budget alone cannot establish that conclusion. -/
theorem runSlice_under_budget_final (machine : MachineCore Term) (fuel : Nat)
    (state : machine.State) (early : (runSlice machine fuel state).2 < fuel) :
    machine.step (runSlice machine fuel state).1 = none := by
  induction fuel generalizing state with
  | zero => simp [runSlice] at early
  | succ fuel ih =>
      cases transition : machine.step state with
      | none => simp [runSlice, transition]
      | some next =>
          simp only [runSlice, transition] at early ⊢
          exact ih next (by omega)

/-- A decoder reflecting both successors and finality transports bounded
resumption and its transition count. Native fusion needs a region-level law
instead of this stronger single-step premise. -/
theorem runSlice_decode (source : MachineCore Term) (target : MachineCore OtherTerm)
    (decode : target.State → source.State)
    (step_exact : ∀ state,
      (target.step state).map decode = source.step (decode state))
    (fuel : Nat) (state : target.State) :
    (decode (runSlice target fuel state).1, (runSlice target fuel state).2) =
      runSlice source fuel (decode state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      have exactStep := step_exact state
      cases transition : target.step state with
      | none =>
          simp only [transition, Option.map_none] at exactStep
          simp [runSlice, transition, ← exactStep]
      | some next =>
          simp only [transition, Option.map_some] at exactStep
          simp only [runSlice, transition, ← exactStep]
          have exactRun := ih next
          have states := congrArg Prod.fst exactRun
          have counts := congrArg Prod.snd exactRun
          exact Prod.ext states (congrArg (· + 1) counts)


/-- A zero-or-one step readback preserves the actual bounded endpoint. Its
source debit may be smaller than the implementation debit. -/
theorem runSlice_decode_stuttering (source : MachineCore Term)
    (target : MachineCore OtherTerm) (decode : target.State → source.State)
    (readStep : ∀ state next, target.step state = some next →
      decode next = decode state ∨ source.step (decode state) = some (decode next))
    (fuel : Nat) (state : target.State) :
    ∃ used, used ≤ (runSlice target fuel state).2 ∧
      runSlice source used (decode state) =
        (decode (runSlice target fuel state).1, used) := by
  induction fuel generalizing state with
  | zero => exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ fuel ih =>
      cases transition : target.step state with
      | none => exact ⟨0, by simp [runSlice, transition], by simp [runSlice, transition]⟩
      | some next =>
          obtain ⟨used, bound, exactRun⟩ := ih next
          rcases readStep state next transition with unchanged | advanced
          · refine ⟨used, ?_, ?_⟩
            · simp only [runSlice, transition]
              omega
            · simpa only [runSlice, transition, unchanged] using exactRun
          · refine ⟨used + 1, ?_, ?_⟩
            · simp only [runSlice, transition]
              omega
            · simp only [runSlice, advanced, transition]
              rw [exactRun]

/-- Composing genuine finite implementations of source steps preserves every
bounded source endpoint. Only transitions actually taken are charged; a source
that stops early does not compel extra implementation steps. -/
theorem runSlice_realizes (source : MachineCore Term)
    (target : MachineCore OtherTerm) (decode : target.State → source.State)
    (realizeStep : ∀ state next, source.step (decode state) = some next →
      ∃ ticks, 0 < ticks ∧ (runSlice target ticks state).2 = ticks ∧
        decode (runSlice target ticks state).1 = next)
    (fuel : Nat) (state : target.State) :
    ∃ ticks, (runSlice source fuel (decode state)).2 ≤ ticks ∧
      (runSlice target ticks state).2 = ticks ∧
      decode (runSlice target ticks state).1 =
        (runSlice source fuel (decode state)).1 := by
  induction fuel generalizing state with
  | zero => exact ⟨0, Nat.le_refl 0, rfl, rfl⟩
  | succ fuel ih =>
      cases transition : source.step (decode state) with
      | none => exact ⟨0, by simp [runSlice, transition], rfl,
          by simp [runSlice, transition]⟩
      | some next =>
          obtain ⟨first, positive, firstPaid, firstEndpoint⟩ :=
            realizeStep state next transition
          obtain ⟨later, laterBound, laterPaid, laterEndpoint⟩ :=
            ih (runSlice target first state).1
          simp only [firstEndpoint] at laterBound laterEndpoint
          refine ⟨first + later, ?_, ?_, ?_⟩
          · simp only [runSlice, transition]
            omega
          · rw [runSlice_add]
            change (runSlice target first state).2 +
              (runSlice target later (runSlice target first state).1).2 = first + later
            rw [firstPaid, laterPaid]
          · rw [runSlice_add]
            simpa only [runSlice, transition] using laterEndpoint

end Mettapedia.Machines.MachineCore
