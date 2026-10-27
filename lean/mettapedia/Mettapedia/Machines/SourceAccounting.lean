import Mettapedia.Machines.ContextualCBPV
import Mathlib.Data.Nat.Pairing

/-!
# Source receipts and charged residual execution

Declaration/query roots distinguish occurrences even when code is shared.
Positions number the elaborated occurrence list before normalization. Zero is
reserved for derived work, whose canonical native transition costs one.

The source machine consumes charged jobs. The compiled machine reads immutable
instructions through a retained program counter and uses bounded-word debit.
Their refinement preserves the complete world, receipt trace, remaining credit
and residual jobs for every physical slice. It does not equate source credit
with the number of scheduler transitions.

This is an accounting refinement for a retained instruction schedule. The C
elaborator's complete syntax traversal, pointer lifetimes, dynamic call stacks
and specialized regions still require their concrete correspondence laws.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SourceAccounting

open ContextualCBPV.EpisodeAccounting

structure Origin where
  root : Nat
  position : Nat
  deriving DecidableEq, Repr

def Origin.encode (origin : Origin) : Nat := Nat.pair origin.root origin.position

theorem distinct_roots (first second position : Nat) (different : first ≠ second) :
    Origin.encode ⟨first, position⟩ ≠ Origin.encode ⟨second, position⟩ := by
  simp [Origin.encode, Nat.pair_eq_pair, different]

/-- Iterative numbering's recursive specification, independent of node contents. -/
def numberFrom {A : Type} (position : Nat) : List A → List (Nat × A)
  | [] => []
  | node :: rest => (position, node) :: numberFrom (position + 1) rest

theorem numbered_positions {A : Type} (nodes : List A) (position : Nat) :
    (numberFrom position nodes).map Prod.fst = List.range' position nodes.length := by
  induction nodes generalizing position with
  | nil => rfl
  | cons node rest ih => simp [numberFrom, ih, List.range'_succ]

theorem numbered_positions_distinct {A : Type} (nodes : List A) (position : Nat) :
    ((numberFrom position nodes).map Prod.fst).Nodup := by
  rw [numbered_positions]
  exact List.nodup_range'

/-- Removing inert nodes keeps surviving source positions, including gaps. -/
theorem retained_positions {A : Type} (nodes : List A) (position : Nat)
    (keep : Nat × A → Bool) :
    (((numberFrom position nodes).filter keep).map Prod.fst).Sublist
      (List.range' position nodes.length) := by
  rw [← numbered_positions nodes position]
  exact List.Sublist.map Prod.fst List.filter_sublist

variable {World : Type}

structure Instruction (World : Type) where
  position : Nat
  debit : Nat
  execute : World → World

def Instruction.charge (instruction : Instruction World) : Nat :=
  if instruction.position = 0 then 1 else instruction.debit

structure Job (World : Type) where
  origin : Origin
  cost : Nat
  execute : World → World

structure Source (World : Type) where
  pending : List (Job World)
  world : World
  purse : Purse
  trace : List Origin

/-- Source semantics tests credit before changing either the world or residual. -/
def sourceStep (state : Source World) : Option (Source World) :=
  match state.pending with
  | [] => none
  | job :: rest =>
      if job.cost ≤ state.purse.remaining then
        some ⟨rest, job.execute state.world,
          ⟨state.purse.remaining - job.cost, state.purse.spent + job.cost⟩,
          state.trace ++ [job.origin]⟩
      else none

structure Compiled (World : Type) where
  root : Nat
  code : List (Instruction World)
  pc : Nat
  world : World
  purse : Purse
  trace : List Origin

def compiledStep (maximum : Nat) (state : Compiled World) : Option (Compiled World) :=
  match state.code.drop state.pc with
  | [] => none
  | instruction :: _ =>
      (nativeDebit maximum instruction.charge state.purse).map fun paid =>
        {state with
          pc := state.pc + 1
          world := instruction.execute state.world
          purse := paid
          trace := state.trace ++ [⟨state.root, instruction.position⟩]}

def decode (state : Compiled World) : Source World :=
  ⟨(state.code.drop state.pc).map fun instruction =>
      ⟨⟨state.root, instruction.position⟩, instruction.charge, instruction.execute⟩,
    state.world, state.purse, state.trace⟩

theorem drop_next {A : Type} (code : List A) (pc : Nat) (first : A) (rest : List A)
    (pending : code.drop pc = first :: rest) : code.drop (pc + 1) = rest := by
  have tail := congrArg (List.drop 1) pending
  simpa [List.drop_drop, Nat.add_comm] using tail

/-- Admission, action, exact residual, and all observations commute with decoding. -/
theorem charged_step_refines (maximum : Nat) (state : Compiled World)
    (inRange : state.purse.spent + state.purse.remaining ≤ maximum) :
    sourceStep (decode state) = (compiledStep maximum state).map decode := by
  cases pending : state.code.drop state.pc with
  | nil => simp [sourceStep, compiledStep, decode, pending]
  | cons instruction rest =>
      have tail := drop_next state.code state.pc instruction rest pending
      simp only [compiledStep, pending, native_debit_refines maximum _ _ inRange]
      by_cases enough : instruction.charge ≤ state.purse.remaining
      · simp [sourceStep, decode, pending, debit, enough, tail]
      · simp [sourceStep, decode, pending, debit, enough]

/-- A successful compiled debit preserves the bounded-word invariant. -/
theorem compiled_in_range (maximum : Nat) (before after : Compiled World)
    (inRange : before.purse.spent + before.purse.remaining ≤ maximum)
    (advanced : compiledStep maximum before = some after) :
    after.purse.spent + after.purse.remaining ≤ maximum := by
  unfold compiledStep at advanced
  split at advanced
  · simp at advanced
  · rename_i instruction rest pending
    rw [native_debit_refines maximum _ _ inRange] at advanced
    unfold debit at advanced
    split at advanced
    · simp only [Option.map_some, Option.some.injEq] at advanced
      cases advanced
      dsimp
      omega
    · simp at advanced

/-- Physical slices stop at refusal with the same complete source residual. -/
def sourceCore : MachineCore (Source World) :=
  ⟨Source World, id, sourceStep⟩

def compiledCore (maximum : Nat) : MachineCore (Compiled World) :=
  ⟨Compiled World, id, compiledStep maximum⟩

theorem slice_refines (maximum allowance : Nat) (state : Compiled World)
    (inRange : state.purse.spent + state.purse.remaining ≤ maximum) :
    (sourceCore.runSlice allowance (decode state)).1 =
      decode ((compiledCore maximum).runSlice allowance state).1 ∧
    (sourceCore.runSlice allowance (decode state)).2 =
      ((compiledCore maximum).runSlice allowance state).2 := by
  induction allowance generalizing state with
  | zero => exact ⟨rfl, rfl⟩
  | succ allowance ih =>
      have localLaw := charged_step_refines maximum state inRange
      cases advanced : compiledStep maximum state with
      | none =>
          simp only [advanced, Option.map_none] at localLaw
          simp [MachineCore.runSlice, sourceCore, compiledCore, localLaw, advanced]
      | some next =>
          simp only [advanced, Option.map_some] at localLaw
          have later := ih next (compiled_in_range maximum state next inRange advanced)
          simpa only [MachineCore.runSlice, sourceCore, compiledCore, localLaw, advanced]
            using ⟨later.1, congrArg (· + 1) later.2⟩

/-- A split physical allowance preserves charged source execution exactly. -/
theorem split_resume (maximum first later : Nat) (state : Compiled World) :
    (compiledCore maximum).runSlice (first + later) state =
      let earlier := (compiledCore maximum).runSlice first state
      let suffix := (compiledCore maximum).runSlice later earlier.1
      (suffix.1, earlier.2 + suffix.2) :=
  MachineCore.runSlice_add (compiledCore maximum) first later state

namespace Controls

def event (position debit value : Nat) : Instruction (List Nat) :=
  ⟨position, debit, fun world => world ++ [value]⟩

def initial (code : List (Instruction (List Nat))) (budget : Nat) : Compiled (List Nat) :=
  ⟨17, code, 0, [], ⟨budget, 0⟩, []⟩

theorem zero_charge_keeps_physical_step :
    ((compiledCore 10).runSlice 1 (initial [event 1 0 7] 0)).2 = 1 ∧
    ((compiledCore 10).runSlice 1 (initial [event 1 0 7] 0)).1.world = [7] := by decide

theorem aggregate_charge_changes_prefix :
    ((compiledCore 10).runSlice 2 (initial [event 1 1 7, event 2 1 8] 1)).1.world = [7] ∧
    ((compiledCore 10).runSlice 2 (initial [event 1 2 7] 1)).1.world = [] := by decide

theorem unannotated_is_not_free :
    ((compiledCore 10).runSlice 1 (initial [event 0 0 7] 0)).2 = 0 := by decide

theorem renumbering_after_pruning_changes_origin :
    ((numberFrom 1 [7, 8]).filter fun node => node.2 == 8).map Prod.fst = [2] ∧
    (numberFrom 1 ([7, 8].filter (· == 8))).map Prod.fst = [1] := by decide

end Controls
end Mettapedia.Machines.SourceAccounting

#print axioms Mettapedia.Machines.SourceAccounting.distinct_roots
#print axioms Mettapedia.Machines.SourceAccounting.numbered_positions
#print axioms Mettapedia.Machines.SourceAccounting.numbered_positions_distinct
#print axioms Mettapedia.Machines.SourceAccounting.retained_positions
#print axioms Mettapedia.Machines.SourceAccounting.charged_step_refines
#print axioms Mettapedia.Machines.SourceAccounting.compiled_in_range
#print axioms Mettapedia.Machines.SourceAccounting.slice_refines
#print axioms Mettapedia.Machines.SourceAccounting.split_resume
#print axioms Mettapedia.Machines.SourceAccounting.Controls.zero_charge_keeps_physical_step
#print axioms Mettapedia.Machines.SourceAccounting.Controls.aggregate_charge_changes_prefix
#print axioms Mettapedia.Machines.SourceAccounting.Controls.unannotated_is_not_free
#print axioms Mettapedia.Machines.SourceAccounting.Controls.renumbering_after_pruning_changes_origin
