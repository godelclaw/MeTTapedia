import Mettapedia.Machines.ContextualCBPV
import Mathlib.Data.List.Nodup
import Mettapedia.Languages.MeTTa.PeTTa.PartialApplicationExpansion

/-!
# Contextual entry from borrowed invocation fields

Ordinary calls and completed partial applications share the native invocation
field reader. The source entry uses a flat ordered argument list; the lowering
reads captured and supplied arrays, resolving each lexical identity in the
current logical world. Resolution does not interpret completed values.

After entry the two contextual machines have the same actual computation and
continuation. This transports subsequent choices, effects, faults and pending
native work through the common kernel. Raw syntax observation on refusal stays
with the dialect adapter. Native lifetimes, admission predicates and the C
transition/fuel correspondence remain separate obligations.

Source argument sequencing additionally compares recursive written-order
semantics with reverse worklist assembly. The resulting kernel law preserves
complete packets and every metered slice; concrete source-demand admission and
the native worklist correspondence remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ContextualInvocation

section General

variable {Argument Observed Value Effect Fault Delay Suspension Context World Worker : Type}

abbrev Input := NativeCallReturn.Arguments.Input

inductive Call (Argument : Type) where
  | expanded (head : Argument) (arguments : List Argument)
  | borrowed (input : Input Argument)

abbrev Code := ContextualCBPV.Code Value (Call Argument) Effect Fault Delay Suspension
abbrev Semantics := ContextualCBPV.Semantics Value (Call Argument) Effect Fault Delay
  Suspension Context World Worker
abbrev State := ContextualCBPV.State Value (Call Argument) Effect Fault Delay
  Suspension Context World Worker

/-- A failed lookup rejects the entrance before the callee can execute.
The observation function reads values and lexical coordinates, never code. -/
def resolveBorrowed (resolve : Argument → Option Observed) (input : Input Argument) :
    Option (List Observed) :=
  (input.gather resolve 0 input.arity).bind (List.mapM id)

private theorem sequence_map (resolve : Argument → Option Observed)
    (arguments : List Argument) :
    (arguments.map resolve).mapM id = arguments.mapM resolve := by
  induction arguments with
  | nil => rfl
  | cons first rest ih => simp [List.mapM_cons, ih]

theorem resolution_refines (resolve : Argument → Option Observed)
    (input : Input Argument) :
    resolveBorrowed resolve input = input.arguments.mapM resolve := by
  rw [resolveBorrowed, NativeCallReturn.Arguments.Input.gather_full]
  exact sequence_map resolve input.arguments

section Entry

variable (base : Semantics (Argument := Argument) (Value := Value)
      (Effect := Effect) (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (resolve : World → Context → Argument → Option Observed)
    (enter : World → Context → Argument → List Observed → Context × Code
      (Argument := Argument) (Value := Value) (Effect := Effect) (Fault := Fault)
      (Delay := Delay) (Suspension := Suspension))
    (fallback : World → Context → Argument → List Argument → Context × Code
      (Argument := Argument) (Value := Value) (Effect := Effect) (Fault := Fault)
      (Delay := Delay) (Suspension := Suspension))

/-- Lookup returns code rather than executing it. The fallback receives the
original fields only when it needs the language's authored interpretation. -/
def withCalls :
    Semantics (Argument := Argument) (Value := Value) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker) :=
  {base with enter := fun world context call =>
    match call with
    | .expanded head arguments =>
        match arguments.mapM (resolve world context) with
        | none => fallback world context head arguments
        | some values => enter world context head values
    | .borrowed input =>
        match resolveBorrowed (resolve world context) input with
        | none => fallback world context input.head input.arguments
        | some values => enter world context input.head values}

theorem entry_refines
    (world : World) (context : Context) (input : Input Argument) :
    (withCalls base resolve enter fallback).enter world context (.borrowed input) =
      (withCalls base resolve enter fallback).enter world context
        (.expanded input.head input.arguments) := by
  simp [withCalls, resolution_refines]

/-- Preserve the whole post-entry state, with arbitrary older continuations,
choice alternatives, publication history and source charges. -/
theorem step_refines
    (state : State (Argument := Argument) (Value := Value) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (context : Context) (input : Input Argument) :
    ContextualCBPV.step (withCalls base resolve enter fallback)
      {state with focus := ⟨.compute context (.invoke (.borrowed input)), state.focus.frames⟩} =
    ContextualCBPV.step (withCalls base resolve enter fallback)
      {state with focus := ⟨.compute context
        (.invoke (.expanded input.head input.arguments)), state.focus.frames⟩} := by
  simp [ContextualCBPV.step, ContextualCBPV.advance, ContextualCBPV.debit,
    ContextualCBPV.origin, entry_refines]

/-- Removing a syntax reconstruction cannot introduce a source charge.
The explicit occurrence and debit remain attached to the common invocation. -/
theorem charged_entry_refines
    (state : State (Argument := Argument) (Value := Value) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (context : Context) (input : Input Argument) (occurrence debit : Nat) :
    let sem := withCalls base resolve enter fallback
    (ContextualCBPV.step sem
      {state with focus := ⟨.compute context
        (.source occurrence debit (.invoke (.borrowed input))), state.focus.frames⟩}).bind
          (ContextualCBPV.step sem) =
    (ContextualCBPV.step sem
      {state with focus := ⟨.compute context
        (.source occurrence debit (.invoke (.expanded input.head input.arguments))),
          state.focus.frames⟩}).bind (ContextualCBPV.step sem) := by
  simp [ContextualCBPV.step, ContextualCBPV.advance, ContextualCBPV.debit,
    ContextualCBPV.origin, entry_refines]

/-- Every later slice resumes the same code, contexts, native cursor and
pending alternatives. It does not reconstruct or reload either entrance. -/
theorem resume_after_entry
    (state : State (Argument := Argument) (Value := Value) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (context : Context) (input : Input Argument) (allowance : Nat) :
    let sem := withCalls base resolve enter fallback
    let resume := fun next => (ContextualCBPV.core sem state.world context).runSlice allowance next
    (ContextualCBPV.step sem
      {state with focus := ⟨.compute context (.invoke (.borrowed input)), state.focus.frames⟩}).map resume =
    (ContextualCBPV.step sem
      {state with focus := ⟨.compute context
        (.invoke (.expanded input.head input.arguments)), state.focus.frames⟩}).map resume := by
  dsimp only
  rw [step_refines]

end Entry

/-- This is the same certified partial carrier used by the existing expansion
semantics. Transport changes its representation rather than its callable or
argument order. -/
def partialInput
    (carrier : Languages.MeTTa.PeTTa.PartialApplicationExpansion.Partial Argument)
    (supplied : List Argument) : Input Argument :=
  ⟨carrier.base, carrier.bound.toArray, supplied.toArray⟩

theorem partial_readback
    (carrier : Languages.MeTTa.PeTTa.PartialApplicationExpansion.Partial Argument)
    (supplied : List Argument) :
    (partialInput carrier supplied).head :: (partialInput carrier supplied).arguments =
      Languages.MeTTa.PeTTa.PartialApplicationExpansion.expand carrier supplied := by
  simp [partialInput, NativeCallReturn.Arguments.Input.arguments,
    Languages.MeTTa.PeTTa.PartialApplicationExpansion.expand]

end General

namespace FreshReadback

/-- Private preparation may consume arbitrary names between observable fresh
allocations. The next unused counter is retained, independently of readback.
Natural names model successful allocation; machine-width exhaustion, native
encodings and pointer ownership require their own correspondence. -/
def allocate (next : Nat) : List Nat → List Nat × Nat
  | [] => ([], next)
  | skipped :: rest =>
      let name := next + skipped
      let later := allocate (name + 1) rest
      (name :: later.1, later.2)

theorem allocate_length (next : Nat) (skips : List Nat) :
    (allocate next skips).1.length = skips.length := by
  induction skips generalizing next with
  | nil => rfl
  | cons skipped rest ih => simp [allocate, ih]

theorem allocate_fresh (next : Nat) (skips : List Nat) :
    ∀ name ∈ (allocate next skips).1, next ≤ name := by
  induction skips generalizing next with
  | nil => simp [allocate]
  | cons skipped rest ih =>
      intro name member
      simp only [allocate, List.mem_cons] at member
      rcases member with rfl | later
      · omega
      · have bound := ih (next + skipped + 1) name later
        omega

theorem allocate_distinct (next : Nat) (skips : List Nat) :
    (allocate next skips).1.Nodup := by
  induction skips generalizing next with
  | nil => simp [allocate]
  | cons skipped rest ih =>
      simp only [allocate, List.nodup_cons]
      constructor
      · intro member
        have bound := allocate_fresh (next + skipped + 1) rest
          (next + skipped) member
        omega
      · exact ih _

/-- A resumed allocation uses the retained counter, so the earlier support
is neither regenerated nor mistaken for later fresh names. -/
theorem allocate_append (next : Nat) (first later : List Nat) :
    allocate next (first ++ later) =
      let earlier := allocate next first
      let remaining := allocate earlier.2 later
      (earlier.1 ++ remaining.1, remaining.2) := by
  induction first generalizing next with
  | nil => rfl
  | cons skipped rest ih => simp [allocate, ih]

theorem allocate_next (next : Nat) (skips : List Nat) :
    (allocate next skips).2 = next + skips.sum + skips.length := by
  induction skips generalizing next with
  | nil => simp [allocate]
  | cons skipped rest ih => simp [allocate, ih]; omega

/-- The source contract chooses distinct private names outside the protected
public range. It does not specify an allocator's counter increments. -/
structure Choice (publicBound count : Nat) where
  names : List Nat
  length : names.length = count
  distinct : names.Nodup
  fresh : ∀ name ∈ names, publicBound ≤ name

/-- The counter implementation satisfies the independent fresh-choice
contract for every schedule of unobserved preparation allocations. -/
def allocationChoice (publicBound : Nat) (skips : List Nat) :
    Choice publicBound skips.length where
  names := (allocate publicBound skips).1
  length := allocate_length publicBound skips
  distinct := allocate_distinct publicBound skips
  fresh := allocate_fresh publicBound skips

abbrev Ref (publicBound count : Nat) := Fin publicBound ⊕ Fin count
abbrev Token (Name : Type) := String ⊕ Name

def encode {publicBound count : Nat} (choice : Choice publicBound count) :
    Ref publicBound count → Nat
  | .inl publicName => publicName.val
  | .inr privateName => choice.names.get
      ⟨privateName.val, by rw [choice.length]; exact privateName.isLt⟩

theorem encode_injective {publicBound count : Nat}
    (choice : Choice publicBound count) : Function.Injective (encode choice) := by
  intro left right equal
  cases left with
  | inl a =>
      cases right with
      | inl b => exact congrArg Sum.inl (Fin.ext equal)
      | inr b =>
          have bound := choice.fresh _ (List.get_mem choice.names
            ⟨b.val, by rw [choice.length]; exact b.isLt⟩)
          simp only [encode] at equal
          omega
  | inr a =>
      cases right with
      | inl b =>
          have bound := choice.fresh _ (List.get_mem choice.names
            ⟨a.val, by rw [choice.length]; exact a.isLt⟩)
          simp only [encode] at equal
          omega
      | inr b =>
          have same := choice.distinct.get_inj_iff.mp equal
          exact congrArg Sum.inr (Fin.ext (congrArg (fun x : Fin choice.names.length => x.val) same))

/-- Readback searches the published private support. Unknown names fail;
ordinary literal text is never searched for name-like substrings. -/
def decode {publicBound count : Nat} (choice : Choice publicBound count)
    (name : Nat) : Option (Ref publicBound count) :=
  if publicName : name < publicBound then some (.inl ⟨name, publicName⟩)
  else if privateName : name ∈ choice.names then
    some (.inr ⟨choice.names.idxOf name, by
      have bound := List.idxOf_lt_length_iff.mpr privateName
      simpa only [choice.length] using bound⟩)
  else none

theorem decode_encode {publicBound count : Nat}
    (choice : Choice publicBound count) (name : Ref publicBound count) :
    decode choice (encode choice name) = some name := by
  cases name with
  | inl publicName => simp [decode, encode, publicName.isLt]
  | inr privateName =>
      have member := List.get_mem choice.names
        ⟨privateName.val, by rw [choice.length]; exact privateName.isLt⟩
      have bound := choice.fresh _ member
      simp only [decode, encode, show ¬choice.names.get
        ⟨privateName.val, by rw [choice.length]; exact privateName.isLt⟩ < publicBound
        from by omega, ↓reduceDIte, member]
      congr 3
      exact choice.distinct.idxOf_getElem privateName.val (by rw [choice.length]; exact privateName.isLt)

def instantiate {publicBound count : Nat} (choice : Choice publicBound count)
    (tokens : List (Token (Ref publicBound count))) : List (Token Nat) :=
  tokens.map (Sum.map id (encode choice))

def readback {publicBound count : Nat} (choice : Choice publicBound count)
    (tokens : List (Token Nat)) : Option (List (Token (Ref publicBound count))) :=
  tokens.mapM fun token => match token with
    | .inl text => some (.inl text)
    | .inr name => (decode choice name).map Sum.inr

/-- Lookup-based readback recovers the complete structured observation:
public identity, private aliasing, multiplicity, order and literal bytes. -/
theorem readback_refines {publicBound count : Nat}
    (choice : Choice publicBound count)
    (tokens : List (Token (Ref publicBound count))) :
    readback choice (instantiate choice tokens) = some tokens := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      cases token <;> simp [readback, instantiate, List.mapM_cons, decode_encode] at ih ⊢
      all_goals simp [ih]

/-- Two lawful naming choices preserve every same/different-variable test.
They need not publish the same numeric spelling. -/
theorem choices_preserve_aliasing {publicBound count : Nat}
    (left right : Choice publicBound count) (a b : Ref publicBound count) :
    (encode left a = encode left b) ↔ (encode right a = encode right b) := by
  rw [(encode_injective left).eq_iff, (encode_injective right).eq_iff]

def format (spell : Nat → String) (tokens : List (Token Nat)) : String :=
  String.join (tokens.map fun token => match token with
    | .inl text => text
    | .inr name => spell name)

theorem literal_format_is_exact (spell : Nat → String) (text : String) :
    format spell [.inl text] = text := by simp [format]

/-- Different hidden allocation schedules are both lawful yet visibly print
different private numbers. This is not equality of arbitrary string data. -/
example :
    let left := allocationChoice 5 [0, 0]
    let right := allocationChoice 5 [7, 2]
    encode left (.inr ⟨0, by decide⟩) ≠ encode right (.inr ⟨0, by decide⟩) ∧
    format toString [.inr (encode left (.inr ⟨0, by decide⟩))] ≠
      format toString [.inr (encode right (.inr ⟨0, by decide⟩))] := by decide

example : ¬([5, 5] : List Nat).Nodup := by decide
example : readback (allocationChoice 5 [0, 0]) [.inr 7] = none := by decide
example :
    format toString [.inl "$x#5", .inl " ", .inr 12] = "$x#5 12" := by decide

end FreshReadback

namespace ArgumentSequence

variable {Value Call Effect Fault Delay Suspension : Type}

local notation "Code" => ContextualCBPV.Code Value Call Effect Fault Delay Suspension
local notation "Packet" => NativeCallReturn.Packet Value Fault Delay

/-- Source arguments execute in written order. Their complete packets, including
conditional obligations, reach the call continuation. Raised control is handled
by the contextual kernel before this value continuation can run. -/
def reference : List Code → (List Packet → Code) → Code
  | [], finish => finish []
  | producer :: rest, finish =>
      .sequence producer (fun packet => reference rest (fun values => finish (packet :: values)))

private def push (resume : List Packet → Code) (producer : Code) : List Packet → Code :=
  fun reversed => .sequence producer (fun packet => resume (packet :: reversed))

/-- A newest-first worklist is assembled backwards. Completed packets accumulate
by cons; their order is restored only at the invocation continuation. This is a
lowering of argument sequencing, not permission to evaluate held source syntax. -/
def lower (sources : List Code) (finish : List Packet → Code) : Code :=
  (sources.reverse.foldl push (fun reversed => finish reversed.reverse)) []

private theorem folded_refines (sources : List Code) (finish : List Packet → Code)
    (reversed : List Packet) :
    (sources.reverse.foldl push (fun values => finish values.reverse)) reversed =
      reference sources (fun values => finish (reversed.reverse ++ values)) := by
  induction sources generalizing reversed with
  | nil => simp [reference]
  | cons first rest ih =>
      simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
        push, reference]
      congr 1
      funext packet
      rw [ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Independent recursive source sequencing and reverse worklist assembly
produce the same contextual computation, with the same packet order. -/
theorem lowering_refines (sources : List Code) (finish : List Packet → Code) :
    lower sources finish = reference sources finish := by
  simpa [lower] using folded_refines sources finish []

/-- The assembly law preserves every finite physical slice at every source
purse, including an already active caller's frames, alternatives and history.
This says nothing about the as-yet separate native instruction correspondence. -/
theorem metered_refines {Context World Worker : Type}
    (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension Context World Worker)
    (state : ContextualCBPV.State Value Call Effect Fault Delay Suspension Context World Worker)
    (context : Context) (sources : List Code) (finish : List Packet → Code)
    (sourceFuel physicalSteps : Nat) :
    let machine := ContextualCBPV.meteredCore sem state.world context sourceFuel
    machine.runSlice physicalSteps
        ⟨{state with focus := ⟨.compute context (lower sources finish), state.focus.frames⟩}, sourceFuel⟩ =
      machine.runSlice physicalSteps
        ⟨{state with focus := ⟨.compute context (reference sources finish), state.focus.frames⟩}, sourceFuel⟩ := by
  rw [lowering_refines]

end ArgumentSequence

namespace ArgumentWorklist

/-- Elaboration's readiness and lexical coordinates. A completed error-shaped
value requires a check only when the dialect's argument policy requests it. -/
structure Operand (Scope : Type) where
  index : Nat
  scope : Scope
  demanded : Bool
  returnedError : Bool
  deriving DecidableEq, Repr

inductive Goal (Scope Continuation : Type) where
  | compute (scope : Scope) (index : Nat)
  | check (index : Nat)
  | resume (continuation : Continuation)
  deriving DecidableEq, Repr

variable {Scope Continuation : Type}

/-- The source states computation before its optional completion check. -/
def operandProgram (strict : Bool) (operand : Operand Scope) : List (Goal Scope Continuation) :=
  (if operand.demanded then [.compute operand.scope operand.index] else []) ++
    (if strict && (operand.demanded || operand.returnedError)
      then [.check operand.index] else [])

def source (strict : Bool) (operands : List (Operand Scope))
    (continuation : Continuation) (older : List (Goal Scope Continuation)) :=
  operands.flatMap (operandProgram strict) ++ .resume continuation :: older

/-- Physical push order is check, then computation. Each push places work at
its execution end of the stack; the actual continuation remains below both. -/
def push (strict : Bool) (pending : List (Goal Scope Continuation)) (operand : Operand Scope) :=
  let pending := if strict && (operand.demanded || operand.returnedError)
    then .check operand.index :: pending else pending
  if operand.demanded then .compute operand.scope operand.index :: pending else pending

def lower (strict : Bool) (operands : List (Operand Scope))
    (continuation : Continuation) (older : List (Goal Scope Continuation)) :=
  operands.reverse.foldl (push strict) (.resume continuation :: older)

theorem push_program (strict : Bool) (pending : List (Goal Scope Continuation))
    (operand : Operand Scope) :
    push strict pending operand = operandProgram strict operand ++ pending := by
  rcases operand with ⟨index, scope, demanded, returnedError⟩
  cases strict <;> cases demanded <;> cases returnedError <;> rfl

private theorem fold_program (strict : Bool) (operands : List (Operand Scope))
    (pending : List (Goal Scope Continuation)) :
    operands.reverse.foldl (push strict) pending =
      operands.flatMap (operandProgram strict) ++ pending := by
  induction operands with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.reverse_cons, List.foldl_append, List.foldl_cons,
        List.foldl_nil, ih, push_program, List.flatMap_cons, List.append_assoc]

/-- The executable schedule agrees with independently written source order,
including ready operands, guard placement, lexical scope and older work. -/
theorem lowering_refines (strict : Bool) (operands : List (Operand Scope))
    (continuation : Continuation) (older : List (Goal Scope Continuation)) :
    lower strict operands continuation older = source strict operands continuation older := by
  exact fold_program strict operands (.resume continuation :: older)

/-- Charge emitted source visits without erasing the actual pending suffix.
This models schedule accounting, not the separate native instruction relation. -/
def chargePrefix (charge : Goal Scope Continuation → Nat) :
    Nat → List (Goal Scope Continuation) →
      List (Goal Scope Continuation) × List (Goal Scope Continuation) × Nat
  | fuel, [] => ([], [], fuel)
  | fuel, first :: rest =>
      if charge first ≤ fuel then
        let later := chargePrefix charge (fuel - charge first) rest
        (first :: later.1, later.2.1, later.2.2)
      else ([], first :: rest, fuel)

theorem prefix_partition (charge : Goal Scope Continuation → Nat)
    (fuel : Nat) (goals : List (Goal Scope Continuation)) :
    (chargePrefix charge fuel goals).1 ++ (chargePrefix charge fuel goals).2.1 = goals := by
  induction goals generalizing fuel with
  | nil => rfl
  | cons first rest ih =>
      by_cases enough : charge first ≤ fuel
      · simpa only [chargePrefix, if_pos enough, List.cons_append, List.cons.injEq, true_and]
          using ih (fuel - charge first)
      · simp only [chargePrefix, if_neg enough, List.nil_append]

theorem prefix_conserves (charge : Goal Scope Continuation → Nat)
    (fuel : Nat) (goals : List (Goal Scope Continuation)) :
    ((chargePrefix charge fuel goals).1.map charge).sum + (chargePrefix charge fuel goals).2.2 = fuel := by
  induction goals generalizing fuel with
  | nil => simp only [chargePrefix, List.map_nil, List.sum_nil, Nat.zero_add]
  | cons first rest ih =>
      by_cases enough : charge first ≤ fuel
      · simp only [chargePrefix, if_pos enough, List.map_cons, List.sum_cons]
        have remainder := ih (fuel - charge first)
        omega
      · simp only [chargePrefix, if_neg enough, List.map_nil, List.sum_nil, Nat.zero_add]

theorem budgeted_lowering (charge : Goal Scope Continuation → Nat)
    (strict : Bool) (operands : List (Operand Scope)) (continuation : Continuation)
    (older : List (Goal Scope Continuation)) (fuel : Nat) :
    chargePrefix charge fuel (lower strict operands continuation older) =
      chargePrefix charge fuel (source strict operands continuation older) := by
  rw [lowering_refines]

/-- Held arguments have no computation goal. A completed language error still
has the selected check, before continuation entry. -/
theorem held_error_checks_before_entry :
    lower true [⟨1, 11, true, false⟩, ⟨2, 29, false, true⟩] 7 [] =
      [.compute 11 1, .check 1, .check 2, .resume 7] := rfl

/-- Dropping a lexical coordinate changes the executable work, even when all
source indices and readiness decisions agree. -/
theorem scope_erasure_changes_work :
    lower false [⟨1, 11, true, false⟩] 7 [] ≠
      lower false [⟨1, 29, true, false⟩] 7 [] := by decide

/-- A ready error-shaped value alone grants no permission to evaluate it or
convert it to control. That decision is supplied by dialect elaboration. -/
theorem error_policy_is_explicit :
    lower false [⟨1, 11, false, true⟩] 7 [] = [.resume 7] ∧
      lower true [⟨1, 11, false, true⟩] 7 [] = [.check 1, .resume 7] := by decide

namespace Contextual

variable {Value Call Effect Fault Delay Suspension : Type}
local notation "Code" => ContextualCBPV.Code Value Call Effect Fault Delay Suspension

/-- Each emitted visit is interpreted in the existing contextual core. The
adapters supply source computations, completion checks and continuation entry. -/
def interpret (compute : Scope → Nat → Code) (check : Nat → Code)
    (resume : Continuation → Code) (goals : List (Goal Scope Continuation))
    (finish : Code) : Code :=
  goals.foldr (fun goal rest => .sequence (match goal with
    | .compute scope index => compute scope index
    | .check index => check index
    | .resume continuation => resume continuation) (fun _ => rest)) finish

/-- Direct elaboration states the operand's computation before its optional
check, without constructing or reading a physical goal list. -/
def operand (compute : Scope → Nat → Code) (check : Nat → Code)
    (strict : Bool) (slot : Operand Scope) (rest : Code) : Code :=
  let rest := if strict && (slot.demanded || slot.returnedError)
    then .sequence (check slot.index) (fun _ => rest) else rest
  if slot.demanded then .sequence (compute slot.scope slot.index) (fun _ => rest) else rest

def elaborate (compute : Scope → Nat → Code) (check : Nat → Code)
    (resume : Continuation → Code) (strict : Bool) (slots : List (Operand Scope))
    (continuation : Continuation) (older : List (Goal Scope Continuation)) (finish : Code) : Code :=
  slots.foldr (operand compute check strict)
    (interpret compute check resume (.resume continuation :: older) finish)

theorem interpret_append (compute : Scope → Nat → Code) (check : Nat → Code)
    (resume : Continuation → Code) (first rest : List (Goal Scope Continuation))
    (finish : Code) :
    interpret compute check resume (first ++ rest) finish =
      interpret compute check resume first (interpret compute check resume rest finish) := by
  simp only [interpret, List.foldr_append]

theorem operand_refines (compute : Scope → Nat → Code) (check : Nat → Code)
    (resume : Continuation → Code) (strict : Bool) (slot : Operand Scope) (finish : Code) :
    interpret compute check resume (operandProgram strict slot) finish =
      operand compute check strict slot finish := by
  rcases slot with ⟨index, scope, demanded, returnedError⟩
  cases strict <;> cases demanded <;> cases returnedError <;> rfl

theorem elaboration_refines (compute : Scope → Nat → Code) (check : Nat → Code)
    (resume : Continuation → Code) (strict : Bool) (slots : List (Operand Scope))
    (continuation : Continuation) (older : List (Goal Scope Continuation)) (finish : Code) :
    interpret compute check resume (lower strict slots continuation older) finish =
      elaborate compute check resume strict slots continuation older finish := by
  rw [lowering_refines]
  unfold source elaborate
  induction slots with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.flatMap_cons, List.append_assoc, interpret_append, List.foldr_cons,
        operand_refines, ih]

/-- This join preserves the complete contextual residual at every source purse
and every model transition allowance. Native charge correspondence and the
particular dialect's check elaboration remain separate obligations. -/
theorem metered_refines {Context World Worker : Type}
    (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension Context World Worker)
    (state : ContextualCBPV.State Value Call Effect Fault Delay Suspension Context World Worker)
    (context : Context) (compute : Scope → Nat → Code) (check : Nat → Code)
    (resume : Continuation → Code) (strict : Bool) (slots : List (Operand Scope))
    (continuation : Continuation) (older : List (Goal Scope Continuation)) (finish : Code)
    (sourceFuel physicalSteps : Nat) :
    let machine := ContextualCBPV.meteredCore sem state.world context sourceFuel
    machine.runSlice physicalSteps
        ⟨{state with focus := ⟨.compute context
          (interpret compute check resume (lower strict slots continuation older) finish),
          state.focus.frames⟩}, sourceFuel⟩ =
      machine.runSlice physicalSteps
        ⟨{state with focus := ⟨.compute context
          (elaborate compute check resume strict slots continuation older finish),
          state.focus.frames⟩}, sourceFuel⟩ := by
  rw [elaboration_refines]

end Contextual

end ArgumentWorklist

namespace Preparation

inductive Step where
  | installType | compute | checkReturn | checkType | bindValue
  deriving DecidableEq, Repr

structure Plan where
  installType : Bool
  compute : Bool
  checkReturn : Bool
  checkType : Bool
  bindValue : Bool
  deriving DecidableEq, Repr

/-- The source states the semantic stages in execution order. -/
def source (plan : Plan) : List Step :=
  (if plan.installType then [.installType] else []) ++
  (if plan.compute then [.compute] else []) ++
  (if plan.checkReturn then [.checkReturn] else []) ++
  (if plan.checkType then [.checkType] else []) ++
  (if plan.bindValue then [.bindValue] else [])

/-- Compact program metadata uses the generated preparation positions. -/
def encode (plan : Plan) : Nat :=
  (if plan.installType then 1 else 0) + (if plan.compute then 2 else 0) +
  (if plan.checkReturn then 4 else 0) + (if plan.checkType then 8 else 0) +
  (if plan.bindValue then 16 else 0)

def reverseStages : List (Nat × Step) :=
  [(4, .bindValue), (3, .checkType), (2, .checkReturn), (1, .compute), (0, .installType)]

def lower (bits : Nat) (older : List Step) : List Step :=
  reverseStages.foldl (fun pending stage =>
    if bits.testBit stage.1 then stage.2 :: pending else pending) older

theorem lower_refines (plan : Plan) (older : List Step) :
    lower (encode plan) older = source plan ++ older := by
  rcases plan with ⟨install, compute, returned, checked, bound⟩
  cases install <;> cases compute <;> cases returned <;> cases checked <;> cases bound <;> rfl

theorem encoding_bounded (plan : Plan) : encode plan < 32 := by
  rcases plan with ⟨install, compute, returned, checked, bound⟩
  cases install <;> cases compute <;> cases returned <;> cases checked <;> cases bound <;> decide

inductive Demand where
  | raw | translated | guarded
  deriving DecidableEq, Repr

def argumentPlan (demand : Demand) (binder obligations contracts formalVariable : Bool) : Plan :=
  let guard := demand == .guarded
  ⟨guard && obligations, demand != .raw, false,
    guard && !(contracts && formalVariable), binder⟩

/-- Direct dialect elaboration, independently of the bit representation. -/
def argumentSource (demand : Demand) (binder obligations contracts formalVariable : Bool) : List Step :=
  let tail := if binder then [.bindValue] else []
  match demand with
  | .raw => tail
  | .translated => .compute :: tail
  | .guarded =>
      (if obligations then [.installType] else []) ++ [.compute] ++
        (if contracts && formalVariable then [] else [.checkType]) ++ tail

theorem argument_refines (demand : Demand) (binder obligations contracts formalVariable : Bool)
    (older : List Step) :
    lower (encode (argumentPlan demand binder obligations contracts formalVariable)) older =
      argumentSource demand binder obligations contracts formalVariable ++ older := by
  rw [lower_refines]
  cases demand <;> cases binder <;> cases obligations <;> cases contracts <;>
    cases formalVariable <;> rfl

def resultPlan (guardResult isPartial resultVariable contracts obligations delayed : Bool) : Plan :=
  let checked := guardResult && !(contracts && (isPartial || resultVariable))
  ⟨checked && obligations, true, false, checked, delayed⟩

def resultSource (guardResult isPartial resultVariable contracts obligations delayed : Bool) : List Step :=
  if guardResult && !(contracts && (isPartial || resultVariable)) then
    (if obligations then [.installType] else []) ++ [.compute, .checkType] ++
      (if delayed then [.bindValue] else [])
  else [.compute] ++ (if delayed then [.bindValue] else [])

theorem result_refines (guardResult isPartial resultVariable contracts obligations delayed : Bool)
    (older : List Step) :
    lower (encode (resultPlan guardResult isPartial resultVariable contracts obligations delayed)) older =
      resultSource guardResult isPartial resultVariable contracts obligations delayed ++ older := by
  rw [lower_refines]
  cases guardResult <;> cases isPartial <;> cases resultVariable <;> cases contracts <;>
    cases obligations <;> cases delayed <;> rfl

/-- Argument programs precede the result program already installed as the
call continuation. The assembler reads the arguments backwards. -/
def lowerCall (arguments : List Plan) (result : Plan) (older : List Step) : List Step :=
  arguments.reverse.foldl (fun pending plan => lower (encode plan) pending)
    (lower (encode result) older)

private theorem argumentFold (arguments : List Plan) (pending : List Step) :
    arguments.reverse.foldl (fun rest plan => lower (encode plan) rest) pending =
      arguments.flatMap source ++ pending := by
  induction arguments with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih, lower_refines]
      simp only [List.flatMap_cons, List.append_assoc]

theorem call_refines (arguments : List Plan) (result : Plan) (older : List Step) :
    lowerCall arguments result older =
      arguments.flatMap source ++ source result ++ older := by
  unfold lowerCall
  rw [argumentFold, lower_refines]
  exact (List.append_assoc _ _ _).symm

section Contextual

variable {Value Call Effect Fault Delay Suspension Context World Worker : Type}
local notation "Code" => ContextualCBPV.Code Value Call Effect Fault Delay Suspension

/-- The adapter realizes each stage using the existing binding, type,
computation and return services. Packet writes and native source charges
are realization obligations, beyond this schedule interpretation. -/
def interpret (stage : Step → Code) (steps : List Step) (finish : Code) : Code :=
  steps.foldr (fun step rest => .sequence (stage step) (fun _ => rest)) finish

theorem contextual_refines
    (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension Context World Worker)
    (state : ContextualCBPV.State Value Call Effect Fault Delay Suspension Context World Worker)
    (context : Context) (stage : Step → Code) (arguments : List Plan) (result : Plan)
    (older : List Step) (finish : Code) (sourceFuel physicalSteps : Nat) :
    let machine := ContextualCBPV.meteredCore sem state.world context sourceFuel
    machine.runSlice physicalSteps
        ⟨{state with focus := ⟨.compute context
          (interpret stage (lowerCall arguments result older) finish), state.focus.frames⟩}, sourceFuel⟩ =
      machine.runSlice physicalSteps
        ⟨{state with focus := ⟨.compute context
          (interpret stage (arguments.flatMap source ++ source result ++ older) finish),
          state.focus.frames⟩}, sourceFuel⟩ := by
  rw [call_refines]

end Contextual

/-- A telescope binder follows the argument's completed check. Installation
precedes computation even when the post-guard on a formal variable is omitted. -/
theorem dependent_order :
    argumentSource .guarded true true false false =
      [.installType, .compute, .checkType, .bindValue] ∧
    argumentSource .guarded true true true true =
      [.installType, .compute, .bindValue] := by decide

/-- Moving a postcondition before the body is a different schedule. -/
theorem result_check_is_after_body :
    resultSource true false false false true true =
      [.installType, .compute, .checkType, .bindValue] ∧
    resultSource true false false false true true ≠
      [.installType, .checkType, .compute, .bindValue] := by decide

end Preparation

namespace Controls

inductive Scalar where
  | number (n : Nat)
  | code (n : Nat)
  deriving DecidableEq, Repr

inductive Value where
  | number (n : Nat)
  | code (n : Nat)
  | tuple (fields : List Scalar)
  deriving DecidableEq, Repr

inductive Argument where
  | symbol (name : Nat)
  | variable (scope name : Nat)
  | datum (value : Scalar)
  deriving DecidableEq, Repr

abbrev Context := Nat × Nat
abbrev Cursor := NativeCallReturn.Cursor Value String Unit Context
abbrev Engine := Semantics (Argument := Argument) (Value := Value)
  (Effect := Nat) (Fault := String) (Delay := Unit) (Suspension := Nat)
  (Context := Context) (World := Nat) (Worker := Cursor)

def resolve (_ : Nat) (context : Context) : Argument → Option Scalar
  | .symbol name => some (.number name)
  | .variable 0 0 => some (.number context.1)
  | .variable 1 0 => some (.number context.2)
  | .variable _ _ => none
  | .datum value => some value

def base : Engine where
  enter := fun _ context _ => (context, .failure)
  suspend := fun _ reference => .code reference
  force := fun context value => match value with
    | .code effect => (context, .native effect)
    | _ => (context, .returned value)
  native := fun context world effect =>
    (world + effect, ⟨.one (.value .completed (.number world)), context, 0⟩)
  pull := fun world cursor => (world, NativeCallReturn.read cursor)
  resume := fun _ current => current

def lookup (_ : Nat) (context : Context) (head : Argument) (values : List Scalar) :
    Context × Code (Argument := Argument) (Value := Value) (Effect := Nat)
      (Fault := String) (Delay := Unit) (Suspension := Nat) :=
  (context, match head with
    | .symbol 10 => .sequence (.native 1) (fun _ =>
        .choice (.returned (.tuple values)) (.returned (.tuple values)))
    | _ => .failure)

def fallback (_ : Nat) (context : Context) (_ : Argument) (_ : List Argument) :
    Context × Code (Argument := Argument) (Value := Value) (Effect := Nat)
      (Fault := String) (Delay := Unit) (Suspension := Nat) :=
  (context, .raised "unresolved")

def input : Input Argument :=
  ⟨.symbol 10, #[.variable 0 0, .datum (.code 17)], #[.variable 1 0]⟩

def runInput (input : Input Argument) (resolver : Nat → Context → Argument → Option Scalar) (context : Context) :
    State (Argument := Argument) (Value := Value) (Effect := Nat)
      (Fault := String) (Delay := Unit) (Suspension := Nat)
      (Context := Context) (World := Nat) (Worker := Cursor) :=
  let sem := withCalls base resolver lookup fallback
  ((ContextualCBPV.core sem 0 context).runSlice 128
    (ContextualCBPV.initial 0 context (.invoke (.borrowed input)))).1


def run (resolver : Nat → Context → Argument → Option Scalar) (context : Context) :=
  runInput input resolver context

theorem scoped_values_and_duplicates :
    (run resolve (11, 29)).published =
      [((11, 29), .value .completed (.tuple [.number 11, .code 17, .number 29])),
       ((11, 29), .value .completed (.tuple [.number 11, .code 17, .number 29]))] := by
  decide

/-- Code-shaped input remains data. Only the callee's one native computation
enters; the stored code would contribute a different effect if forced. -/
theorem values_are_not_forced :
    (run resolve (11, 29)).world = 1 ∧ (run resolve (11, 29)).nativeEntries = 1 := by
  decide

theorem current_context_is_observed :
    (run resolve (11, 29)).published ≠ (run resolve (101, 103)).published := by
  decide

def eraseScope (world : Nat) (context : Context) : Argument → Option Scalar
  | .variable _ name => resolve world context (.variable 0 name)
  | value => resolve world context value

theorem erasing_scope_loses_argument_identity :
    (run resolve (11, 29)).published ≠ (run eraseScope (11, 29)).published := by
  decide

/-- A missing lexical coordinate never enters the callee's native work. -/
theorem unresolved_argument_does_not_enter :
    let bad : Input Argument := ⟨.symbol 10, #[.variable 2 0], #[]⟩
    (runInput bad resolve (11, 29)).world = 0 ∧
      (runInput bad resolve (11, 29)).nativeEntries = 0 ∧
      (runInput bad resolve (11, 29)).focus.control = .unhandled "unresolved" := by
  exact ⟨rfl, rfl, rfl⟩

def sequenceSemantics : Engine :=
  {base with native := fun context world effect =>
    (world * 10 + effect, ⟨.one (.value .completed (.number effect)), context, 0⟩)}

private def sequenceRun (code : Code (Argument := Argument) (Value := Value)
    (Effect := Nat) (Fault := String) (Delay := Unit) (Suspension := Nat)) :=
  ((ContextualCBPV.core sequenceSemantics 0 (0, 0)).runSlice 128
    (ContextualCBPV.initial 0 (0, 0) code)).1

private def countArguments (packets : List (NativeCallReturn.Packet Value String Unit)) :
    Code (Argument := Argument) (Value := Value) (Effect := Nat)
      (Fault := String) (Delay := Unit) (Suspension := Nat) :=
  .returned (.number packets.length)

theorem argument_effects_keep_source_order :
    (sequenceRun (ArgumentSequence.lower [.native 1, .native 2] countArguments)).world = 12 ∧
      (sequenceRun (ArgumentSequence.lower [.native 2, .native 1] countArguments)).world = 21 := by
  decide

theorem completed_argument_is_not_forced :
    let result := sequenceRun
      (ArgumentSequence.lower [.returned (.code 9), .native 2] countArguments)
    result.world = 2 ∧ result.nativeEntries = 1 ∧
      result.published = [((0, 0), .value .completed (.number 2))] := by
  decide

theorem failed_argument_stops_remaining_work :
    let result := sequenceRun
      (ArgumentSequence.lower [.native 1, .failure, .native 2] (fun _ => .native 9))
    result.world = 1 ∧ result.nativeEntries = 1 ∧ result.published = [] := by
  decide

theorem raised_argument_reaches_caller_handler :
    let result := sequenceRun (.handle
      (ArgumentSequence.lower [.native 1, .raised "argument fault", .native 2]
        (fun _ => .native 9)) (fun _ => .returned (.number 8)))
    result.world = 1 ∧ result.nativeEntries = 1 ∧
      result.published = [((0, 0), .value .completed (.number 8))] := by
  decide

theorem duplicate_arguments_retain_separate_continuations :
    let result := sequenceRun (ArgumentSequence.lower
      [.choice (.returned (.number 1)) (.returned (.number 1)), .native 2] countArguments)
    result.world = 22 ∧ result.nativeEntries = 2 ∧
      result.published = [((0, 0), .value .completed (.number 2)),
        ((0, 0), .value .completed (.number 2))] := by
  decide

/-- The callee's delimiter starts after its arguments. Moving that delimiter
outside argument sequencing wrongly protects a caller alternative from cut. -/
theorem argument_commit_belongs_to_caller_scope :
    let arguments := [.commit (.number 0)]
    let finish := fun (_ : List (NativeCallReturn.Packet Value String Unit)) =>
      ContextualCBPV.Computation.scope (.returned (.number 1))
    (sequenceRun (.choice (ArgumentSequence.lower arguments finish)
      (.returned (.number 9)))).published = [((0, 0), .value .completed (.number 1))] ∧
    (sequenceRun (.choice (.scope (ArgumentSequence.lower arguments finish))
      (.returned (.number 9)))).published = [((0, 0), .value .completed (.number 1)),
        ((0, 0), .value .completed (.number 9))] := by
  decide

end Controls

end Mettapedia.Machines.ContextualInvocation

#print axioms Mettapedia.Machines.ContextualInvocation.resolution_refines
#print axioms Mettapedia.Machines.ContextualInvocation.entry_refines
#print axioms Mettapedia.Machines.ContextualInvocation.step_refines
#print axioms Mettapedia.Machines.ContextualInvocation.partial_readback

#print axioms Mettapedia.Machines.ContextualInvocation.charged_entry_refines
#print axioms Mettapedia.Machines.ContextualInvocation.resume_after_entry
#print axioms Mettapedia.Machines.ContextualInvocation.Controls.scoped_values_and_duplicates
#print axioms Mettapedia.Machines.ContextualInvocation.Controls.values_are_not_forced
#print axioms Mettapedia.Machines.ContextualInvocation.Controls.current_context_is_observed
#print axioms Mettapedia.Machines.ContextualInvocation.Controls.erasing_scope_loses_argument_identity

#print axioms Mettapedia.Machines.ContextualInvocation.Controls.unresolved_argument_does_not_enter
#print axioms Mettapedia.Machines.ContextualInvocation.ArgumentSequence.lowering_refines
#print axioms Mettapedia.Machines.ContextualInvocation.ArgumentSequence.metered_refines
#print axioms Mettapedia.Machines.ContextualInvocation.Controls.argument_effects_keep_source_order
#print axioms Mettapedia.Machines.ContextualInvocation.Controls.completed_argument_is_not_forced
#print axioms Mettapedia.Machines.ContextualInvocation.Controls.failed_argument_stops_remaining_work
#print axioms Mettapedia.Machines.ContextualInvocation.Controls.raised_argument_reaches_caller_handler
#print axioms Mettapedia.Machines.ContextualInvocation.Controls.duplicate_arguments_retain_separate_continuations
#print axioms Mettapedia.Machines.ContextualInvocation.Controls.argument_commit_belongs_to_caller_scope

#print axioms Mettapedia.Machines.ContextualInvocation.FreshReadback.allocate_length

#print axioms Mettapedia.Machines.ContextualInvocation.FreshReadback.allocate_fresh

#print axioms Mettapedia.Machines.ContextualInvocation.FreshReadback.allocate_distinct
#print axioms Mettapedia.Machines.ContextualInvocation.FreshReadback.allocate_append
#print axioms Mettapedia.Machines.ContextualInvocation.FreshReadback.allocate_next

#print axioms Mettapedia.Machines.ContextualInvocation.FreshReadback.encode_injective

#print axioms Mettapedia.Machines.ContextualInvocation.FreshReadback.decode_encode

#print axioms Mettapedia.Machines.ContextualInvocation.FreshReadback.readback_refines

#print axioms Mettapedia.Machines.ContextualInvocation.FreshReadback.choices_preserve_aliasing

#print axioms Mettapedia.Machines.ContextualInvocation.FreshReadback.literal_format_is_exact

#print axioms Mettapedia.Machines.ContextualInvocation.ArgumentWorklist.push_program
#print axioms Mettapedia.Machines.ContextualInvocation.ArgumentWorklist.lowering_refines
#print axioms Mettapedia.Machines.ContextualInvocation.ArgumentWorklist.prefix_partition
#print axioms Mettapedia.Machines.ContextualInvocation.ArgumentWorklist.prefix_conserves
#print axioms Mettapedia.Machines.ContextualInvocation.ArgumentWorklist.budgeted_lowering
#print axioms Mettapedia.Machines.ContextualInvocation.ArgumentWorklist.held_error_checks_before_entry
#print axioms Mettapedia.Machines.ContextualInvocation.ArgumentWorklist.scope_erasure_changes_work
#print axioms Mettapedia.Machines.ContextualInvocation.ArgumentWorklist.error_policy_is_explicit

#print axioms Mettapedia.Machines.ContextualInvocation.ArgumentWorklist.Contextual.interpret_append
#print axioms Mettapedia.Machines.ContextualInvocation.ArgumentWorklist.Contextual.operand_refines
#print axioms Mettapedia.Machines.ContextualInvocation.ArgumentWorklist.Contextual.elaboration_refines
#print axioms Mettapedia.Machines.ContextualInvocation.ArgumentWorklist.Contextual.metered_refines

#print axioms Mettapedia.Machines.ContextualInvocation.Preparation.lower_refines
#print axioms Mettapedia.Machines.ContextualInvocation.Preparation.encoding_bounded
#print axioms Mettapedia.Machines.ContextualInvocation.Preparation.argument_refines
#print axioms Mettapedia.Machines.ContextualInvocation.Preparation.result_refines
#print axioms Mettapedia.Machines.ContextualInvocation.Preparation.call_refines
#print axioms Mettapedia.Machines.ContextualInvocation.Preparation.contextual_refines
#print axioms Mettapedia.Machines.ContextualInvocation.Preparation.dependent_order
#print axioms Mettapedia.Machines.ContextualInvocation.Preparation.result_check_is_after_body
