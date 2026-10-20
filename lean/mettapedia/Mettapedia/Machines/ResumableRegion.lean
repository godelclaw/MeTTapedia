import Mettapedia.Machines.MachineRefinement
import Mettapedia.GSLT.Contracts.RunAccounts
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

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

/-- A local observation law composes over the retained primitive execution. -/
theorem runSlice_preserves {View : Type*} (machine : MachineCore Term)
    (view : machine.State → View)
    (localLaw : ∀ before after, machine.step before = some after → view after = view before)
    (fuel : Nat) (state : machine.State) :
    view (runSlice machine fuel state).1 = view state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases advanced : machine.step state with
      | none => simp [runSlice, advanced]
      | some next =>
          simpa only [runSlice, advanced] using (ih next).trans (localLaw state next advanced)

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

/-- A stuttering implementation realizes the next source step within its
remaining maintenance rank plus one. A decreasing rank is required only for
administrative steps; genuine source transitions may replenish it. Finality
reflection excludes an implementation that silently stops during maintenance.
Native allocation refusal must be an explicit source outcome or lie outside
the admitted service domain, rather than masquerading as source exhaustion. -/
theorem runSlice_realizes_step_of_rank (source : MachineCore Term)
    (target : MachineCore OtherTerm) (decode : target.State → source.State)
    (rank : target.State → Nat)
    (readStep : ∀ state next, target.step state = some next →
      (decode next = decode state ∧ rank next < rank state) ∨
        source.step (decode state) = some (decode next))
    (reflectFinal : ∀ state, target.step state = none → source.step (decode state) = none)
    (state : target.State) (next : source.State)
    (advanced : source.step (decode state) = some next) :
    ∃ ticks, 0 < ticks ∧ ticks ≤ rank state + 1 ∧
      (runSlice target ticks state).2 = ticks ∧
      decode (runSlice target ticks state).1 = next := by
  generalize rankState : rank state = remaining
  induction remaining using Nat.strong_induction_on generalizing state with
  | h remaining ih =>
      cases transition : target.step state with
      | none =>
          have stopped := reflectFinal state transition
          rw [advanced] at stopped
          cases stopped
      | some later =>
          rcases readStep state later transition with ⟨unchanged, decreases⟩ | moved
          · have laterAdvanced : source.step (decode later) = some next := by
              simpa only [unchanged] using advanced
            obtain ⟨ticks, positive, bounded, paid, endpoint⟩ :=
              ih (rank later) (by omega) later laterAdvanced rfl
            refine ⟨ticks + 1, by omega, by omega, ?_, ?_⟩
            · simp only [runSlice, transition, paid]
            · simpa only [runSlice, transition] using endpoint
          · have endpoint : decode later = next := Option.some.inj (moved.symm.trans advanced)
            refine ⟨1, by omega, by omega, ?_, ?_⟩
            · simp only [runSlice, transition]
            · simpa only [runSlice, transition] using endpoint

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

/-- A finite maintenance rank discharges the finite-step premise of the
existing region-realization theorem. This does not impose termination on
the source machine: every finite source prefix has a finite implementation. -/
theorem runSlice_realizes_of_rank (source : MachineCore Term)
    (target : MachineCore OtherTerm) (decode : target.State → source.State)
    (rank : target.State → Nat)
    (readStep : ∀ state next, target.step state = some next →
      (decode next = decode state ∧ rank next < rank state) ∨
        source.step (decode state) = some (decode next))
    (reflectFinal : ∀ state, target.step state = none → source.step (decode state) = none)
    (fuel : Nat) (state : target.State) :
    ∃ ticks, (runSlice source fuel (decode state)).2 ≤ ticks ∧
      (runSlice target ticks state).2 = ticks ∧
      decode (runSlice target ticks state).1 =
        (runSlice source fuel (decode state)).1 := by
  apply runSlice_realizes source target decode _ fuel state
  intro before after advanced
  obtain ⟨ticks, positive, _, paid, endpoint⟩ :=
    runSlice_realizes_step_of_rank source target decode rank readStep reflectFinal
      before after advanced
  exact ⟨ticks, positive, paid, endpoint⟩

namespace MaintenanceControls

/-- One visible completion, independently of any maintenance representation. -/
def source : MachineCore Bool where
  State := Bool
  load := id
  step state := if state then some false else none

/-- The positive control performs a finite countdown before that completion. -/
def countdown : MachineCore Nat where
  State := Nat
  load := id
  step
    | 0 => none
    | remaining + 1 => some remaining

def decode (state : Nat) : Bool := state != 0

theorem countdown_readStep (state next : Nat)
    (advanced : countdown.step state = some next) :
    (decode next = decode state ∧ next.pred < state.pred) ∨
      source.step (decode state) = some (decode next) := by
  cases state with
  | zero => simp [countdown] at advanced
  | succ remaining =>
      have equal : remaining = next := Option.some.inj advanced
      subst next
      cases remaining with
      | zero => right; rfl
      | succ remaining =>
          left
          exact ⟨rfl, by simp only [Nat.add_one, Nat.pred_succ]; omega⟩

theorem countdown_reflectFinal (state : Nat) (stopped : countdown.step state = none) :
    source.step (decode state) = none := by
  cases state with
  | zero => rfl
  | succ remaining => simp [countdown] at stopped

theorem finite_maintenance_realizes_completion (remaining : Nat) :
    ∃ ticks, 0 < ticks ∧ ticks ≤ remaining + 1 ∧
      (runSlice countdown ticks (remaining + 1)).2 = ticks ∧
      decode (runSlice countdown ticks (remaining + 1)).1 = false := by
  obtain ⟨ticks, positive, bounded, paid, endpoint⟩ :=
    runSlice_realizes_step_of_rank source countdown decode Nat.pred
      countdown_readStep countdown_reflectFinal (remaining + 1) false rfl
  exact ⟨ticks, positive, bounded, paid, endpoint⟩

/-- Preserving the decoded state alone admits endless internal maintenance. -/
def forever : MachineCore Bool where
  State := Bool
  load := id
  step := some

theorem unranked_stuttering_never_completes (fuel : Nat) :
    runSlice forever fuel true = (true, fuel) ∧ source.step true = some false := by
  constructor
  · induction fuel with
    | zero => rfl
    | succ fuel ih =>
        change ((runSlice forever fuel true).1, (runSlice forever fuel true).2 + 1) = _
        rw [ih]
        rfl
  · rfl

theorem forever_has_no_progress_rank :
    ¬ ∃ rank : Bool → Nat, ∀ state next, forever.step state = some next →
      (next = state ∧ rank next < rank state) ∨ source.step state = some next := by
  rintro ⟨rank, progress⟩
  rcases progress true true rfl with ⟨_, decreases⟩ | advanced
  · exact (Nat.lt_irrefl _) decreases
  · cases advanced

end MaintenanceControls

/-! ## Optional accounts of the actual primitive path

The ordinary slice above is unchanged. This mathematical observation labels
its actual transitions through the maintained `RunAccount`. A terminal probe,
result inspection, callback adaptation and other host work are outside this
transition account and require their own bounds.
-/

abbrev stepQuiver (machine : MachineCore Term) : Quiver machine.State :=
  ⟨fun before after => PLift (machine.StepRel before after)⟩

/-- The path contains exactly the transitions taken by the ordinary slice.
It is not stored by `runSlice` or required by an unrecorded implementation. -/
def slicePath (machine : MachineCore Term) : (fuel : Nat) → (state : machine.State) →
    letI := stepQuiver machine
    Σ endpoint : machine.State, Quiver.Path state endpoint
  | 0, state => by
      letI := stepQuiver machine
      exact ⟨state, .nil⟩
  | fuel + 1, state => by
      letI := stepQuiver machine
      exact match advanced : machine.step state with
        | none => ⟨state, .nil⟩
        | some next =>
            let rest := slicePath machine fuel next
            let edge : state ⟶ next := ⟨advanced⟩
            ⟨rest.1, edge.toPath.comp rest.2⟩

theorem slicePath_endpoint (machine : MachineCore Term) (fuel : Nat) (state : machine.State) :
    (slicePath machine fuel state).1 = (runSlice machine fuel state).1 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      rw [slicePath]
      split
      · rename_i advanced
        simp only [runSlice, advanced]
      · rename_i next advanced
        simpa only [runSlice, advanced] using ih next

def stepAccount {Cost : Type*} [AddMonoid Cost] (machine : MachineCore Term)
    (price : machine.State → Cost) :
    letI := stepQuiver machine
    Mettapedia.Effects.RunAccount (_root_.CategoryTheory.Paths machine.State)
      (Multiplicative Cost) := by
  letI := stepQuiver machine
  exact Mettapedia.GSLT.Contracts.Accounts.pathAccount
    (fun {before _} _ => Multiplicative.ofAdd (price before))

/-- A readout of the existing account, rather than a second cost accumulator. -/
def sliceCost {Cost : Type*} [AddMonoid Cost] (machine : MachineCore Term)
    (price : machine.State → Cost) (fuel : Nat) (state : machine.State) : Cost := by
  letI := stepQuiver machine
  exact Multiplicative.toAdd ((stepAccount machine price).of (slicePath machine fuel state).2)

@[simp] theorem sliceCost_zero {Cost : Type*} [AddMonoid Cost]
    (machine : MachineCore Term) (price : machine.State → Cost) (state : machine.State) :
    sliceCost machine price 0 state = 0 := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem sliceCost_succ {Cost : Type*} [AddMonoid Cost]
    (machine : MachineCore Term) (price : machine.State → Cost) (fuel : Nat)
    (state : machine.State) :
    sliceCost machine price (fuel + 1) state =
      match machine.step state with
      | none => 0
      | some next => price state + sliceCost machine price fuel next := by
  let _ := stepQuiver machine
  unfold sliceCost
  rw [slicePath]
  split
  · rename_i stopped
    simp [stepAccount, stopped]
  · rename_i next advanced
    conv_rhs => rw [advanced]
    erw [(stepAccount machine price).of_comp]
    simp [stepAccount, Quiver.Hom.toPath,
      Mettapedia.GSLT.Contracts.Accounts.pathAccount_cons,
      Mettapedia.GSLT.Contracts.Accounts.pathAccount_nil]

theorem sliceCost_of_final {Cost : Type*} [AddMonoid Cost]
    (machine : MachineCore Term) (price : machine.State → Cost) (state : machine.State)
    (final : machine.step state = none) (fuel : Nat) :
    sliceCost machine price fuel state = 0 := by
  cases fuel <;> simp [sliceCost_succ, final]

/-- Ordered additive accounts compose at the retained endpoint. Already paid
primitive work is neither restarted nor charged again after suspension. -/
theorem sliceCost_add {Cost : Type*} [AddMonoid Cost]
    (machine : MachineCore Term) (price : machine.State → Cost) (first second : Nat)
    (state : machine.State) :
    sliceCost machine price (first + second) state =
      sliceCost machine price first state +
        sliceCost machine price second (runSlice machine first state).1 := by
  induction first generalizing state with
  | zero => simp [runSlice]
  | succ first ih =>
      cases advanced : machine.step state with
      | none => simp [Nat.succ_add, sliceCost_succ, advanced, runSlice,
          sliceCost_of_final machine price state advanced]
      | some next =>
          simp only [Nat.succ_add, sliceCost_succ, advanced, runSlice, ih]
          rw [add_assoc]

theorem sliceCost_const {Cost : Type*} [AddMonoid Cost] (machine : MachineCore Term)
    (price : Cost) (fuel : Nat) (state : machine.State) :
    sliceCost machine (fun _ => price) fuel state = (runSlice machine fuel state).2 • price := by
  induction fuel generalizing state with
  | zero => simp [runSlice]
  | succ fuel ih =>
      cases advanced : machine.step state with
      | none => simp [sliceCost_succ, runSlice, advanced]
      | some next => simp [sliceCost_succ, runSlice, advanced, ih, succ_nsmul']

theorem sliceCost_unit (machine : MachineCore Term) (fuel : Nat) (state : machine.State) :
    sliceCost machine (fun _ => (1 : Nat)) fuel state = (runSlice machine fuel state).2 := by
  simpa using sliceCost_const machine (1 : Nat) fuel state

/-- Local prices bound the actual transitions, including slices which stop
early. The statement does not bound any one primitive by its invocation count. -/
theorem sliceCost_le_used {Cost : Type*} [AddCommMonoid Cost] [Preorder Cost]
    [IsOrderedAddMonoid Cost] (machine : MachineCore Term) (price : machine.State → Cost)
    (bound : Cost) (localBound : ∀ state, price state ≤ bound) (fuel : Nat)
    (state : machine.State) :
    sliceCost machine price fuel state ≤ (runSlice machine fuel state).2 • bound := by
  induction fuel generalizing state with
  | zero => simp [runSlice]
  | succ fuel ih =>
      cases advanced : machine.step state with
      | none => simp [sliceCost_succ, runSlice, advanced]
      | some next =>
          simpa only [sliceCost_succ, runSlice, advanced, add_nsmul, one_nsmul,
            add_comm] using add_le_add (localBound state) (ih next)

theorem sliceCost_le_budget {Cost : Type*} [AddCommMonoid Cost] [Preorder Cost]
    [IsOrderedAddMonoid Cost] (machine : MachineCore Term) (price : machine.State → Cost)
    (bound : Cost) (nonnegative : 0 ≤ bound) (localBound : ∀ state, price state ≤ bound)
    (fuel : Nat) (state : machine.State) :
    sliceCost machine price fuel state ≤ fuel • bound :=
  (sliceCost_le_used machine price bound localBound fuel state).trans
    (nsmul_le_nsmul_left nonnegative (runSlice_used_le machine fuel state))

/-- Add an optional primitive account to the existing paid residual. The
first component remains the maintained exact transition debit and state. -/
def accountedPaidSlice {Cost : Type*} [AddMonoid Cost] (machine : MachineCore Term)
    (price : machine.State → Cost) (fuel : Nat) (packet : (Nat × machine.State) × Cost) :
    (Nat × machine.State) × Cost :=
  (paidSlice machine fuel packet.1, packet.2 + sliceCost machine price fuel packet.1.2)

theorem accountedPaidSlice_add {Cost : Type*} [AddMonoid Cost]
    (machine : MachineCore Term) (price : machine.State → Cost) (first second : Nat)
    (packet : (Nat × machine.State) × Cost) :
    accountedPaidSlice machine price (first + second) packet =
      accountedPaidSlice machine price second (accountedPaidSlice machine price first packet) := by
  apply Prod.ext
  · exact paidSlice_add machine first second packet.1
  · simp only [accountedPaidSlice, sliceCost_add, paidSlice, add_assoc]

theorem accountedPaidSlice_cost_bound {Cost : Type*} [AddCommMonoid Cost] [Preorder Cost]
    [IsOrderedAddMonoid Cost] (machine : MachineCore Term) (price : machine.State → Cost)
    (bound : Cost) (nonnegative : 0 ≤ bound) (localBound : ∀ state, price state ≤ bound)
    (fuel : Nat) (packet : (Nat × machine.State) × Cost) :
    (accountedPaidSlice machine price fuel packet).2 ≤ packet.2 + fuel • bound :=
  add_le_add (le_refl packet.2)
    (sliceCost_le_budget machine price bound nonnegative localBound fuel packet.1.2)

namespace Attempts

/-- Each source `step` call is an observer transition, including a call that
returns `none`. Once stopped, the observer performs no further source call.
This observes work independently of the source's successful-transition debit. -/
abbrev observer (machine : MachineCore Term) : MachineCore Term where
  State := Bool × machine.State
  load input := (false, machine.load input)
  step packet := if packet.1 then none else
    some (match machine.step packet.2 with
      | none => (true, packet.2)
      | some next => (false, next))

theorem stopped (machine : MachineCore Term) (fuel : Nat) (state : machine.State) :
    runSlice (observer machine) fuel (true, state) = ((true, state), 0) :=
  runSlice_of_final (observer machine) (true, state) rfl fuel

/-- The observer has the exact ordinary endpoint. Its one possible extra
transition is the early stopping check, rather than a semantic source step. -/
theorem run_exact (machine : MachineCore Term) (fuel : Nat) (state : machine.State) :
    runSlice (observer machine) fuel (false, state) =
      ((decide ((runSlice machine fuel state).2 < fuel), (runSlice machine fuel state).1),
        (runSlice machine fuel state).2 +
          if (runSlice machine fuel state).2 < fuel then 1 else 0) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases advanced : machine.step state with
      | none => simp [runSlice, observer, advanced, stopped]
      | some next =>
          simp only [runSlice, observer, Bool.false_eq_true, ↓reduceIte, advanced]
          rw [ih]
          simp only [Nat.add_lt_add_iff_right]
          split_ifs <;> simp_all [Nat.add_comm]

/-- Mathematical call observations, independently collected from the source
operation. An unrecorded runtime need not construct or retain this list. -/
def trace (machine : MachineCore Term) : Nat → machine.State → List (machine.State × Option machine.State)
  | 0, _ => []
  | fuel + 1, state =>
      let result := machine.step state
      (state, result) :: match result with
      | none => []
      | some next => trace machine fuel next

theorem trace_valid (machine : MachineCore Term) (fuel : Nat) (state : machine.State)
    (call : machine.State × Option machine.State) (member : call ∈ trace machine fuel state) :
    call.2 = machine.step call.1 := by
  induction fuel generalizing state with
  | zero => cases member
  | succ fuel ih =>
      simp only [trace, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · cases advanced : machine.step state with
        | none => simp [advanced] at member
        | some next => exact ih next (by simpa only [advanced] using member)

theorem trace_length (machine : MachineCore Term) (fuel : Nat) (state : machine.State) :
    (trace machine fuel state).length = (runSlice (observer machine) fuel (false, state)).2 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases advanced : machine.step state with
      | none => simp [trace, runSlice, observer, advanced, stopped]
      | some next => simpa [trace, runSlice, observer, advanced] using ih next

theorem trace_length_exact (machine : MachineCore Term) (fuel : Nat) (state : machine.State) :
    (trace machine fuel state).length = (runSlice machine fuel state).2 +
      if (runSlice machine fuel state).2 < fuel then 1 else 0 := by
  rw [trace_length, run_exact]

theorem trace_successes (machine : MachineCore Term) (fuel : Nat) (state : machine.State) :
    ((trace machine fuel state).filter fun call => call.2.isSome).length =
      (runSlice machine fuel state).2 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases advanced : machine.step state with
      | none => simp [trace, runSlice, advanced]
      | some next => simpa [trace, runSlice, advanced] using ih next

theorem trace_of_final (machine : MachineCore Term) (fuel : Nat) (state : machine.State)
    (final : machine.step state = none) :
    trace machine fuel state = if fuel = 0 then [] else [(state, none)] := by
  cases fuel <;> simp [trace, final]

/-- Splitting after an already observed stop repeats that terminal probe
when the second invocation has positive allowance. Source endpoints and
successful debits still compose exactly. -/
theorem trace_split (machine : MachineCore Term) (first second : Nat) (state : machine.State) :
    trace machine first state ++ trace machine second (runSlice machine first state).1 =
      trace machine (first + second) state ++
        if (runSlice machine first state).2 < first ∧ 0 < second then
          [((runSlice machine first state).1, none)] else [] := by
  induction first generalizing state with
  | zero => simp [trace, runSlice]
  | succ first ih =>
      cases advanced : machine.step state with
      | none => cases second <;> simp [trace, runSlice, advanced]
      | some next =>
          simpa [Nat.succ_add, trace, runSlice, advanced, List.append_assoc] using
            congrArg (List.cons (state, some next)) (ih next)

/-- Prices are read from the maintained `RunAccount` of the observer path.
Calls returning `none` are real accounted transitions of this observer. -/
def cost {Cost : Type*} [AddMonoid Cost] (machine : MachineCore Term)
    (price : machine.State → Cost) (fuel : Nat) (state : machine.State) : Cost :=
  sliceCost (observer machine) (fun packet => price packet.2) fuel (false, state)

theorem cost_stopped {Cost : Type*} [AddMonoid Cost] (machine : MachineCore Term)
    (price : machine.State → Cost) (fuel : Nat) (state : machine.State) :
    sliceCost (observer machine) (fun packet => price packet.2) fuel (true, state) = 0 :=
  sliceCost_of_final (observer machine) _ (true, state) rfl fuel

theorem cost_exact {Cost : Type*} [AddMonoid Cost] (machine : MachineCore Term)
    (price : machine.State → Cost) (fuel : Nat) (state : machine.State) :
    cost machine price fuel state = sliceCost machine price fuel state +
      if (runSlice machine fuel state).2 < fuel then price (runSlice machine fuel state).1 else 0 := by
  induction fuel generalizing state with
  | zero => simp [cost, runSlice]
  | succ fuel ih =>
      cases advanced : machine.step state with
      | none => simp [cost, sliceCost_succ, runSlice, observer, advanced, cost_stopped]
      | some next =>
          simp only [cost, sliceCost_succ, runSlice, observer, Bool.false_eq_true,
            ↓reduceIte, advanced] at ih ⊢
          rw [ih]
          simp [add_assoc]

theorem cost_const {Cost : Type*} [AddMonoid Cost] (machine : MachineCore Term)
    (price : Cost) (fuel : Nat) (state : machine.State) :
    cost machine (fun _ => price) fuel state = (trace machine fuel state).length • price := by
  rw [cost, sliceCost_const, trace_length]

theorem cost_le {Cost : Type*} [AddCommMonoid Cost] [Preorder Cost] [IsOrderedAddMonoid Cost]
    (machine : MachineCore Term) (price : machine.State → Cost) (bound : Cost)
    (nonnegative : 0 ≤ bound) (localBound : ∀ state, price state ≤ bound)
    (fuel : Nat) (state : machine.State) : cost machine price fuel state ≤ fuel • bound :=
  sliceCost_le_budget (observer machine) _ bound nonnegative
    (fun packet => localBound packet.2) fuel (false, state)

theorem cost_split {Cost : Type*} [AddMonoid Cost] (machine : MachineCore Term)
    (price : machine.State → Cost) (first second : Nat) (state : machine.State) :
    cost machine price first state + cost machine price second (runSlice machine first state).1 =
      cost machine price (first + second) state +
        if (runSlice machine first state).2 < first ∧ 0 < second then
          price (runSlice machine first state).1 else 0 := by
  have combined := sliceCost_add (observer machine) (fun packet => price packet.2)
    first second (false, state)
  rw [run_exact] at combined
  by_cases early : (runSlice machine first state).2 < first
  · have final := runSlice_under_budget_final machine first state early
    simp only [early, decide_true, cost_stopped, add_zero] at combined
    have later := cost_exact machine price second (runSlice machine first state).1
    rw [runSlice_of_final machine _ final, sliceCost_of_final machine price _ final] at later
    cases second with
    | zero => simp [cost, early]
    | succ second =>
        have appended := congrArg (fun extra => cost machine price first state + extra) later
        simpa [cost, early, combined] using appended
  · simpa only [cost, early, decide_false, false_and, ↓reduceIte, add_zero] using combined.symm

end Attempts

#print axioms sliceCost_add
#print axioms sliceCost_unit
#print axioms sliceCost_le_budget
#print axioms accountedPaidSlice_add
#print axioms accountedPaidSlice_cost_bound
#print axioms runSlice_realizes_step_of_rank
#print axioms runSlice_realizes_of_rank
#print axioms MaintenanceControls.finite_maintenance_realizes_completion
#print axioms MaintenanceControls.unranked_stuttering_never_completes
#print axioms MaintenanceControls.forever_has_no_progress_rank
#print axioms Attempts.run_exact
#print axioms Attempts.trace_valid
#print axioms Attempts.trace_length_exact
#print axioms Attempts.trace_successes
#print axioms Attempts.trace_split
#print axioms Attempts.cost_exact
#print axioms Attempts.cost_le
#print axioms Attempts.cost_split

end Mettapedia.Machines.MachineCore
