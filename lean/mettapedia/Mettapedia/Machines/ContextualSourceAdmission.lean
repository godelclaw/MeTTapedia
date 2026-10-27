import Mettapedia.Machines.ContextualCBPV

/-!
# Joint physical and source admission of contextual execution

The reference counts down a physical window around the metered contextual
machine. The native realization counts admitted transitions up to a limit,
checks that limit before word-sized source debit, and then executes the
retained contextual transition. A missing window is unbounded. This models
the active diagnostic window or controller quantum, not a language fuel.

Decoding retains the complete contextual state: bindings, effects, pending
workers, return frames, alternatives and publications. The bounded refinement
connects unit-transition resumption to explicit source accounting. It does not
assign charges to arbitrary source syntax or verify native pointer storage;
the complete C elaboration and worker-internal charge laws remain obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ContextualSourceAdmission

open ContextualCBPV

variable (Value Call Effect Fault Delay Suspension Context World Worker : Type)

abbrev Meter := Metered (Value := Value) (Call := Call) (Effect := Effect)
  (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
  (Context := Context) (World := World) (Worker := Worker)

structure Native where
  meter : Meter Value Call Effect Fault Delay Suspension Context World Worker
  permitted : Nat

structure Reference where
  meter : Meter Value Call Effect Fault Delay Suspension Context World Worker
  physical : Option Nat

variable {Value Call Effect Fault Delay Suspension Context World Worker}

def room : Option Nat → Bool
  | none => true
  | some remaining => 0 < remaining

def remaining (limit : Option Nat) (used : Nat) : Option Nat :=
  limit.map (· - used)

def decode (limit : Option Nat)
    (state : Native Value Call Effect Fault Delay Suspension Context World Worker) :
    Reference Value Call Effect Fault Delay Suspension Context World Worker :=
  ⟨state.meter, remaining limit state.permitted⟩

/-- The reference performs no source transition when its physical window is empty. -/
def referenceStep (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (state : Reference Value Call Effect Fault Delay Suspension Context World Worker) :
    Option (Reference Value Call Effect Fault Delay Suspension Context World Worker) :=
  if room state.physical then
    (meteredStep sem state.meter).map fun next => ⟨next, state.physical.map (· - 1)⟩
  else none

/-- Native admission reads the physical counter before the semantic ledger. -/
def nativeStep (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (maximum : Nat) (limit : Option Nat)
    (state : Native Value Call Effect Fault Delay Suspension Context World Worker) :=
  if limit.all (state.permitted < ·) then
    (EpisodeAccounting.nativeChargedStep sem maximum state.meter).map fun next =>
      (⟨next, if limit.isSome then state.permitted + 1 else state.permitted⟩ :
        Native Value Call Effect Fault Delay Suspension Context World Worker)
  else none

theorem native_step_refines
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (maximum : Nat) (limit : Option Nat)
    (state : Native Value Call Effect Fault Delay Suspension Context World Worker)
    (inRange : state.meter.state.spent + state.meter.remaining ≤ maximum) :
    (nativeStep sem maximum limit state).map (decode limit) =
      referenceStep sem (decode limit state) := by
  cases limit with
  | none =>
      simp [nativeStep, referenceStep, decode, remaining, room,
        EpisodeAccounting.charged_step_refines sem maximum state.meter inRange,
        Option.map_map, Function.comp_def]
  | some limit =>
      by_cases available : state.permitted < limit
      · have positive : 0 < limit - state.permitted := by omega
        have next : limit - (state.permitted + 1) = limit - state.permitted - 1 := by omega
        simp [nativeStep, referenceStep, decode, remaining, room, available, positive, next,
          EpisodeAccounting.charged_step_refines sem maximum state.meter inRange,
          Option.map_map, Function.comp_def]
      · have empty : limit - state.permitted = 0 := by omega
        simp [nativeStep, referenceStep, decode, remaining, room, available, empty]

theorem reference_step_meter
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (before after : Reference Value Call Effect Fault Delay Suspension Context World Worker)
    (advanced : referenceStep sem before = some after) :
    meteredStep sem before.meter = some after.meter := by
  unfold referenceStep at advanced
  split at advanced
  · obtain ⟨next, moved, equal⟩ := Option.map_eq_some_iff.mp advanced
    subst after
    exact moved
  · simp at advanced

theorem native_preserves_source_total
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (maximum : Nat) (limit : Option Nat)
    (before after : Native Value Call Effect Fault Delay Suspension Context World Worker)
    (inRange : before.meter.state.spent + before.meter.remaining ≤ maximum)
    (advanced : nativeStep sem maximum limit before = some after) :
    after.meter.state.spent + after.meter.remaining =
      before.meter.state.spent + before.meter.remaining := by
  have exactStep := native_step_refines sem maximum limit before inRange
  rw [advanced] at exactStep
  have moved := reference_step_meter sem _ _ exactStep.symm
  exact semantic_purse_conserved sem before.meter after.meter moved

def nativeCore (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker)) (maximum : Nat) (limit : Option Nat) :
    MachineCore (Native Value Call Effect Fault Delay Suspension Context World Worker) :=
  ⟨Native Value Call Effect Fault Delay Suspension Context World Worker, id,
    nativeStep sem maximum limit⟩

def referenceCore (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker)) :
    MachineCore (Reference Value Call Effect Fault Delay Suspension Context World Worker) :=
  ⟨Reference Value Call Effect Fault Delay Suspension Context World Worker, id, referenceStep sem⟩

/-- Every physical slice preserves the complete charged kernel residual,
including source refusal before an effect and earlier committed effects. -/
theorem slice_refines
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (maximum allowance : Nat) (limit : Option Nat)
    (state : Native Value Call Effect Fault Delay Suspension Context World Worker)
    (inRange : state.meter.state.spent + state.meter.remaining ≤ maximum) :
    (decode limit ((nativeCore sem maximum limit).runSlice allowance state).1,
      ((nativeCore sem maximum limit).runSlice allowance state).2) =
      (referenceCore sem).runSlice allowance (decode limit state) := by
  induction allowance generalizing state with
  | zero => rfl
  | succ allowance ih =>
      have exactStep := native_step_refines sem maximum limit state inRange
      cases advanced : nativeStep sem maximum limit state with
      | none =>
          simp only [advanced, Option.map_none] at exactStep
          simp [MachineCore.runSlice, nativeCore, referenceCore, advanced, ← exactStep]
      | some next =>
          have conserved := native_preserves_source_total sem maximum limit state next inRange advanced
          have later := ih next (by omega)
          simp only [advanced, Option.map_some] at exactStep
          simpa only [MachineCore.runSlice, nativeCore, referenceCore, advanced, ← exactStep]
            using congrArg (fun result => (result.1, result.2 + 1)) later

theorem split_resume
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (maximum first later : Nat) (limit : Option Nat)
    (state : Native Value Call Effect Fault Delay Suspension Context World Worker) :
    (nativeCore sem maximum limit).runSlice (first + later) state =
      let earlier := (nativeCore sem maximum limit).runSlice first state
      let suffix := (nativeCore sem maximum limit).runSlice later earlier.1
      (suffix.1, earlier.2 + suffix.2) :=
  MachineCore.runSlice_add (nativeCore sem maximum limit) first later state

/-- Extending a window retains the kernel state; it does not reload a call. -/
theorem refill_decode (limit extra : Nat)
    (state : Native Value Call Effect Fault Delay Suspension Context World Worker)
    (bounded : state.permitted ≤ limit) :
    decode (some (limit + extra)) state =
      {decode (some limit) state with physical := some (limit - state.permitted + extra)} := by
  have equal : limit + extra - state.permitted = limit - state.permitted + extra := by omega
  simp only [decode, remaining, Option.map_some, equal]

namespace Controls

open ContextualCBPV.Controls

abbrev TestNative := Native Datum Unit Nat Nat Unit Nat Nat Nat
  (NativeCallReturn.Cursor Datum Nat Unit Nat)

def initialState (used credit : Nat) (code : TestCode) : TestNative :=
  ⟨⟨ContextualCBPV.initial 0 4 code, credit⟩, used⟩

theorem physical_refusal_does_not_spend :
    nativeStep semantics 100 (some 1) (initialState 1 8 (.source 9 3 (.native 1))) = none := by
  rfl

/-- The old ordering can mutate the purse even though physical work is denied. -/
theorem debit_before_refusal_changes_purse :
    EpisodeAccounting.nativeDebit 100 3 ⟨8, 0⟩ = some ⟨5, 3⟩ ∧
    (initialState 1 8 (.source 9 3 (.native 1))).meter.remaining = 8 := by
  exact ⟨rfl, rfl⟩

theorem zero_source_debit_still_needs_physical_room :
    ((nativeCore semantics 100 (some 2)).runSlice 10
      (initialState 0 0 (.source 9 0 (.native 1)))).1.permitted = 2 ∧
    ((nativeCore semantics 100 (some 2)).runSlice 10
      (initialState 0 0 (.source 9 0 (.native 1)))).1.meter.state.world = 1 ∧
    ((nativeCore semantics 100 (some 2)).runSlice 10
      (initialState 0 0 (.source 9 0 (.native 1)))).1.meter.state.spent = 0 := by
  decide

theorem source_refusal_does_not_admit_physical_work :
    ((nativeCore semantics 100 (some 4)).runSlice 10
      (initialState 0 1 (.source 9 3 (.native 1)))).1.permitted = 0 ∧
    ((nativeCore semantics 100 (some 4)).runSlice 10
      (initialState 0 1 (.source 9 3 (.native 1)))).1.meter.state.world = 0 := by
  decide

def paused := ((nativeCore semantics 100 (some 2)).runSlice 40
  (initialState 0 8 (.source 9 3 (.native 1)))).1

theorem resumed_effect_is_not_reentered :
    let after := ((nativeCore semantics 100 (some 20)).runSlice 40 paused).1
    after.meter.state.world = 1 ∧ after.meter.state.nativeEntries = 1 ∧
      after.meter.state.sourceTrace = [9] ∧ after.meter.remaining = 5 ∧
      after.meter.state.published = [(4, .value .completed (.number 4))] := by
  decide

end Controls
end Mettapedia.Machines.ContextualSourceAdmission

#print axioms Mettapedia.Machines.ContextualSourceAdmission.native_step_refines
#print axioms Mettapedia.Machines.ContextualSourceAdmission.native_preserves_source_total
#print axioms Mettapedia.Machines.ContextualSourceAdmission.slice_refines
#print axioms Mettapedia.Machines.ContextualSourceAdmission.split_resume
#print axioms Mettapedia.Machines.ContextualSourceAdmission.refill_decode
#print axioms Mettapedia.Machines.ContextualSourceAdmission.Controls.physical_refusal_does_not_spend
#print axioms Mettapedia.Machines.ContextualSourceAdmission.Controls.debit_before_refusal_changes_purse
#print axioms Mettapedia.Machines.ContextualSourceAdmission.Controls.zero_source_debit_still_needs_physical_room
#print axioms Mettapedia.Machines.ContextualSourceAdmission.Controls.source_refusal_does_not_admit_physical_work
#print axioms Mettapedia.Machines.ContextualSourceAdmission.Controls.resumed_effect_is_not_reentered
