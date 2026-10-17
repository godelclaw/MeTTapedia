import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mettapedia.GSLT.LanguageDef.PatternSpanExecution
import Mettapedia.Computability.BinaryWordAddition
import Mettapedia.Computability.BinaryWordComparison
import Mettapedia.Computability.WordHomomorphismMachine
import Mathlib.Data.Fintype.Sum

/-!
# Scope checks on structural pattern traversal

A structural visitor records bound-index checks, entry into a binder block,
return to the enclosing context, and metadata refusal. This layer retains the
original argument-admission judgment: local closure and canonical binder
metadata. Natural-valued trace fields are semantic payloads; physical execution
uses their complete binary words on stacks.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.PatternScopeExecution
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

inductive Event where
  | bound (index : Nat)
  | enter (arity : Nat)
  | leave
  | refuse
  deriving DecidableEq, Repr

structure Context where
  depth : Nat
  saved : List Nat
  accepted : Bool
  deriving DecidableEq, Repr

def step : Event → Context → Option Context
  | .bound index, state => some { state with accepted := state.accepted && decide (index < state.depth) }
  | .enter arity, state => some ⟨state.depth + arity, state.depth :: state.saved, state.accepted⟩
  | .leave, ⟨_, [], _⟩ => none
  | .leave, ⟨_, depth :: saved, accepted⟩ => some ⟨depth, saved, accepted⟩
  | .refuse, state => some { state with accepted := false }

def walk : List Event → Context → Option Context
  | [], state => some state
  | event :: events, state => do
      let next ← step event state
      walk events next

theorem walk_append (first second : List Event) (state : Context) :
    walk (first ++ second) state = (walk first state).bind (walk second) := by
  induction first generalizing state with
  | nil => rfl
  | cons event events ih =>
      cases h : step event state <;> simp [walk, h, ih]

theorem walk_namedRefusals (names : List String) (state : Context) :
    walk (names.map fun _ => Event.refuse) state =
      some { state with accepted := state.accepted && names.isEmpty } := by
  induction names generalizing state with
  | nil => simp [walk]
  | cons name names ih =>
      simp only [List.map_cons, walk, step, Option.bind_eq_bind, Option.bind_some, ih,
        List.isEmpty_cons, Bool.and_false, Bool.false_and]

mutual
  def events : Pattern → List Event
    | .bvar index => [.bound index]
    | .fvar _ => [.refuse]
    | .apply _ arguments => listEvents arguments
    | .lambda binder body =>
        (if binder.isNone then [] else [.refuse]) ++ .enter 1 :: events body ++ [.leave]
    | .multiLambda arity names body =>
        .enter arity :: (names.map (fun _ => .refuse) ++ events body ++ [.leave])
    | .subst body replacement => .enter 1 :: events body ++ .leave :: events replacement
    | .collection _ elements rest =>
        (if rest.isNone then [] else [.refuse]) ++ listEvents elements
  def listEvents : List Pattern → List Event
    | [] => []
    | pattern :: patterns => events pattern ++ listEvents patterns
end

mutual
  /-- Every binder return restores the supplied context, including an arbitrary
  pre-existing continuation stack. Refusal is retained through the traversal. -/
  theorem walk_events (pattern : Pattern) (state : Context) :
      walk (events pattern) state = some { state with accepted := state.accepted && argumentValidAt state.depth pattern } := by
    cases pattern with
    | bvar index => simp [events, walk, step, argumentValidAt,
        Pattern.isGroundAt, Pattern.hasCanonicalBinderMetadata]
    | fvar name => simp [events, walk, step, argumentValidAt,
        Pattern.isGroundAt, Pattern.hasCanonicalBinderMetadata]
    | apply name arguments =>
        simpa [events, argumentValidAt, Pattern.isGroundAt,
          Pattern.hasCanonicalBinderMetadata] using walk_listEvents arguments state
    | lambda binder body =>
        cases binder <;>
          simp [events, walk_append, walk, step, walk_events body, argumentValidAt,
            Pattern.isGroundAt, Pattern.hasCanonicalBinderMetadata]
    | multiLambda arity names body =>
        simp only [events, walk, step, Option.bind_some, walk_append,
          walk_namedRefusals, walk_events body]
        simp [argumentValidAt, Pattern.isGroundAt,
          Pattern.hasCanonicalBinderMetadata, Bool.and_assoc, Bool.and_left_comm]
    | subst body replacement =>
        simp [events, walk_append, walk, step, walk_events body, walk_events replacement,
          argumentValidAt, Pattern.isGroundAt, Pattern.hasCanonicalBinderMetadata,
          Bool.and_assoc, Bool.and_left_comm]
    | collection kind elements rest =>
        cases rest <;>
          simp [events, walk, step, walk_listEvents elements, argumentValidAt,
            Pattern.isGroundAt, Pattern.hasCanonicalBinderMetadata, Bool.and_comm]
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem walk_listEvents (patterns : List Pattern) (state : Context) :
      walk (listEvents patterns) state = some { state with accepted := state.accepted && (Pattern.isGroundListAt state.depth patterns && Pattern.hasCanonicalBinderMetadataList patterns) } := by
    cases patterns with
    | nil => simp [listEvents, walk, Pattern.isGroundListAt,
        Pattern.hasCanonicalBinderMetadataList]
    | cons pattern patterns =>
        simp [listEvents, walk_append, walk_events pattern, walk_listEvents patterns,
          argumentValidAt, Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadataList,
          Bool.and_assoc, Bool.and_left_comm]
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- Complete traversal accepts exactly the original source argument check. -/
theorem admission_exact (depth : Nat) (pattern : Pattern) :
    walk (events pattern) ⟨depth, [], true⟩ =
      some ⟨depth, [], argumentValidAt depth pattern⟩ := by
  simpa using walk_events pattern ⟨depth, [], true⟩

/-- An unmatched return refuses rather than silently inventing a context. -/
theorem unmatched_leave (depth : Nat) (accepted : Bool) :
    walk [.leave] ⟨depth, [], accepted⟩ = none := rfl

/-- Subsequent well-formed work cannot erase an earlier refusal. -/
theorem refusal_persists (depth : Nat) (saved : List Nat) (pattern : Pattern) :
    walk (events pattern) ⟨depth, saved, false⟩ = some ⟨depth, saved, false⟩ := by
  simpa using walk_events pattern ⟨depth, saved, false⟩

namespace Binary
open Turing StateTransition Polynomial Turing.TM2.Stmt
open Mettapedia.Computability
open BinaryStackArithmetic (naturalBits)

/-- Binary payload symbols and five control boundaries. -/
abbrev Symbol := Sum Bool (Fin 5)

def wire : Event → List Symbol
  | .bound index => .inr 0 :: (naturalBits index).map Sum.inl ++ [.inr 4]
  | .enter arity => .inr 1 :: (naturalBits arity).map Sum.inl ++ [.inr 4]
  | .leave => [.inr 2]
  | .refuse => [.inr 3]

def encode (events : List Event) : List Symbol := events.flatMap wire

@[simp] theorem encode_nil : encode [] = [] := rfl
@[simp] theorem encode_cons (event : Event) (rest : List Event) :
    encode (event :: rest) = wire event ++ encode rest := rfl
theorem encode_append (first second : List Event) :
    encode (first ++ second) = encode first ++ encode second := List.flatMap_append

inductive Stack where
  | input | number | depth | scratch | saved | result
  deriving DecidableEq, Fintype
inductive Phase where
  | next | number | restoreNumber | compare | restoreComparison
  | saveDepth | restoreDepth | add | trim | restoreSum | leaveClear | leaveRestore
  | finishDepth | rejectInput | rejectNumber | rejectDepth | rejectScratch | rejectSaved
  deriving DecidableEq, Fintype
abbrev Cells : Stack → Type
  | .input => Symbol
  | .saved | .result => Option Bool
  | _ => Bool
instance (stack : Stack) : Fintype (Cells stack) := by cases stack <;> infer_instance
structure Registers where
  accepted : Bool
  enter : Bool
  symbol : Option Symbol
  first : Option Bool
  second : Option Bool
  flag : Bool
  deriving DecidableEq

instance : Fintype Registers := Fintype.ofEquiv
    (Bool × Bool × Option Symbol × Option Bool × Option Bool × Bool)
    { toFun := fun state => ⟨state.1, state.2.1, state.2.2.1,
        state.2.2.2.1, state.2.2.2.2.1, state.2.2.2.2.2⟩
      invFun := fun state => (state.accepted, state.enter, state.symbol,
        state.first, state.second, state.flag)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def ready (accepted : Bool) : Registers := ⟨accepted, false, none, none, none, false⟩

def program (phase : Phase) : TM2.Stmt Cells Phase Registers := match phase with
  | .next => pop .input (fun state symbol => { state with symbol := symbol })
      (branch (fun state => state.symbol.isNone)
        (peek .saved (fun state symbol => { state with second := symbol.join, flag := symbol.isSome })
          (branch (fun state => !state.flag)
            (goto fun _ => .finishDepth) (goto fun _ => .rejectDepth)))
        (branch (fun state => decide (state.symbol = some (.inr 0)))
          (load (fun state => { (ready state.accepted) with enter := false }) (goto fun _ => .number))
          (branch (fun state => decide (state.symbol = some (.inr 1)))
            (load (fun state => { (ready state.accepted) with enter := true }) (goto fun _ => .number))
            (branch (fun state => decide (state.symbol = some (.inr 2)))
              (load (fun state => ready state.accepted) (goto fun _ => .leaveClear))
              (branch (fun state => decide (state.symbol = some (.inr 3)))
                (load (fun _ => ready false) (goto fun _ => .next))
                (goto fun _ => .rejectInput))))))
  | .number => pop .input (fun state symbol => { state with symbol := symbol })
      (branch (fun state => decide (state.symbol = some (.inr 4)))
        (goto fun _ => .restoreNumber)
        (branch (fun state => decide (state.symbol = some (.inl false)))
          (push .scratch (fun _ => false) (goto fun _ => .number))
          (branch (fun state => decide (state.symbol = some (.inl true)))
            (push .scratch (fun _ => true) (goto fun _ => .number))
            (goto fun _ => .rejectInput))))
  | .restoreNumber => pop .scratch (fun state bit => { state with first := bit })
      (branch (fun state => state.first.isSome)
        (push .number (fun state => state.first.getD false) (goto fun _ => .restoreNumber))
        (branch Registers.enter
          (push .saved (fun _ => none) (goto fun _ => .saveDepth))
          (load (fun state => { state with flag := false }) (goto fun _ => .compare))))
  | .compare => pop .number (fun state bit => { state with first := bit })
      (pop .depth (fun state bit => { state with second := bit })
        (branch (fun state => state.first.isNone && state.second.isNone)
          (load (fun state => { state with accepted := state.accepted && state.flag })
            (goto fun _ => .restoreComparison))
          (branch (fun state => state.second.isSome)
            (push .scratch (fun state => state.second.getD false)
              (load (fun state => { state with flag := (BinaryWordComparison.updateLess state.flag (state.first.getD false) (state.second.getD false)) }) (goto fun _ => .compare)))
            (load (fun state => { state with flag := (BinaryWordComparison.updateLess state.flag (state.first.getD false) false) }) (goto fun _ => .compare)))))
  | .restoreComparison => pop .scratch (fun state bit => { state with first := bit })
      (branch (fun state => state.first.isSome)
        (push .depth (fun state => state.first.getD false) (goto fun _ => .restoreComparison))
        (load (fun state => ready state.accepted) (goto fun _ => .next)))
  | .saveDepth => pop .depth (fun state bit => { state with first := bit })
      (branch (fun state => state.first.isSome)
        (push .saved (fun state => state.first)
          (push .scratch (fun state => state.first.getD false) (goto fun _ => .saveDepth)))
        (goto fun _ => .restoreDepth))
  | .restoreDepth => pop .scratch (fun state bit => { state with first := bit })
      (branch (fun state => state.first.isSome)
        (push .depth (fun state => state.first.getD false) (goto fun _ => .restoreDepth))
        (load (fun state => { state with flag := false }) (goto fun _ => .add)))
  | .add => pop .number (fun state bit => { state with first := bit })
      (pop .depth (fun state bit => { state with second := bit })
        (branch (fun state => state.first.isNone && state.second.isNone)
          (branch Registers.flag
            (push .scratch (fun _ => true)
              (load (fun state => ready state.accepted) (goto fun _ => .trim)))
            (load (fun state => ready state.accepted) (goto fun _ => .trim)))
          (push .scratch (fun state => BinaryWordAddition.sumBit
              (state.first.getD false) (state.second.getD false) state.flag)
            (load (fun state => { state with flag := (BinaryWordAddition.nextCarry (state.first.getD false) (state.second.getD false) state.flag) }) (goto fun _ => .add)))))
  | .trim => pop .scratch (fun state bit => { state with first := bit })
      (branch (fun state => state.first == some false) (goto fun _ => .trim)
        (branch (fun state => state.first == some true)
          (push .depth (fun _ => true) (goto fun _ => .restoreSum))
          (load (fun state => ready state.accepted) (goto fun _ => .next))))
  | .restoreSum => pop .scratch (fun state bit => { state with first := bit })
      (branch (fun state => state.first.isSome)
        (push .depth (fun state => state.first.getD false) (goto fun _ => .restoreSum))
        (load (fun state => ready state.accepted) (goto fun _ => .next)))
  | .leaveClear => pop .depth (fun state bit => { state with first := bit })
      (branch (fun state => state.first.isSome) (goto fun _ => .leaveClear) (goto fun _ => .leaveRestore))
  | .leaveRestore => pop .saved (fun state bit => { state with symbol := (bit.map fun value => value.elim (.inr 4) Sum.inl) })
      (branch (fun state => decide (state.symbol = some (.inr 4)))
        (load (fun state => ready state.accepted) (goto fun _ => .next))
        (branch (fun state => decide (state.symbol = some (.inl false)))
          (push .depth (fun _ => false) (goto fun _ => .leaveRestore))
          (branch (fun state => decide (state.symbol = some (.inl true)))
            (push .depth (fun _ => true) (goto fun _ => .leaveRestore))
            (goto fun _ => .rejectInput))))
  | .finishDepth => pop .depth (fun state bit => { state with first := bit })
      (branch (fun state => state.first.isSome) (goto fun _ => .finishDepth)
        (push .result (fun state => some state.accepted) (load (fun _ => ready true) halt)))
  | .rejectInput => pop .input (fun state symbol => { state with symbol := symbol })
      (branch (fun state => state.symbol.isSome) (goto fun _ => .rejectInput) (goto fun _ => .rejectNumber))
  | .rejectNumber => pop .number (fun state bit => { state with first := bit })
      (branch (fun state => state.first.isSome) (goto fun _ => .rejectNumber) (goto fun _ => .rejectDepth))
  | .rejectDepth => pop .depth (fun state bit => { state with first := bit })
      (branch (fun state => state.first.isSome) (goto fun _ => .rejectDepth) (goto fun _ => .rejectScratch))
  | .rejectScratch => pop .scratch (fun state bit => { state with first := bit })
      (branch (fun state => state.first.isSome) (goto fun _ => .rejectScratch) (goto fun _ => .rejectSaved))
  | .rejectSaved => pop .saved (fun state bit => { state with symbol := (bit.map fun value => value.elim (.inr 4) Sum.inl) })
      (branch (fun state => state.symbol.isSome) (goto fun _ => .rejectSaved)
        (push .result (fun _ => none) (load (fun _ => ready true) halt)))

def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := Cells
  Λ := Phase
  main := .next
  σ := Registers
  initialState := ready true
  m := program

def config (phase : Option Phase) (state : Registers) (input : List Symbol)
    (number depth scratch : List Bool) (saved result : List (Option Bool)) : machine.Cfg where
  l := phase
  var := state
  stk key := match (show Stack from key) with
    | .input => input | .number => number | .depth => depth | .scratch => scratch
    | .saved => saved | .result => result

local macro "scope_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, program, config, TM2.step, TM2.stepAux, Function.update]
  all_goals first
    | rfl
    | (congr 2; funext key; cases key <;> simp [Function.update])))

theorem compare_nil_nil (state : Registers) (input : List Symbol) (scratch : List Bool)
    (saved result : List (Option Bool)) :
    TM2.step program (config (some .compare) state input [] [] scratch saved result) =
      some (config (some .restoreComparison)
        { state with first := none, second := none, accepted := state.accepted && state.flag }
        input [] [] scratch saved result) := by scope_step

theorem compare_nil_cons (state : Registers) (bit : Bool) (rest scratch : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .compare) state input [] (bit :: rest) scratch saved result) =
      some (config (some .compare) { state with first := none, second := some bit, flag := BinaryWordComparison.updateLess state.flag false bit }
        input [] rest (bit :: scratch) saved result) := by scope_step

theorem compare_cons_nil (state : Registers) (bit : Bool) (rest scratch : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .compare) state input (bit :: rest) [] scratch saved result) =
      some (config (some .compare) { state with first := some bit, second := none, flag := BinaryWordComparison.updateLess state.flag bit false }
        input rest [] scratch saved result) := by scope_step

theorem compare_cons_cons (state : Registers) (left right : Bool)
    (lefts rights scratch : List Bool) (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .compare) state input (left :: lefts) (right :: rights) scratch saved result) =
      some (config (some .compare) { state with first := some left, second := some right, flag := BinaryWordComparison.updateLess state.flag left right }
        input lefts rights (right :: scratch) saved result) := by scope_step

/-- Comparing an index consumes its bits, retains the complete enclosing
binary depth, and records the existing numerical comparison. -/
noncomputable def compareRun (state : Registers) (left right scratch : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .compare) state input left right scratch saved result)
      (some (config (some .restoreComparison) { state with first := none, second := none, flag := BinaryWordComparison.lessFrom state.flag left right, accepted := state.accepted && BinaryWordComparison.lessFrom state.flag left right }
        input [] [] (right.reverse ++ scratch) saved result))
      (max left.length right.length + 1) := by
  induction left generalizing right state scratch with
  | nil =>
      induction right generalizing state scratch with
      | nil => simpa [BinaryWordComparison.lessFrom] using
          StackMachineComposition.oneStep (compare_nil_nil state input scratch saved result)
      | cons bit rest ih =>
          have first := StackMachineComposition.oneStep
            (compare_nil_cons state bit rest scratch input saved result)
          have after := ih { state with first := none, second := some bit, flag := BinaryWordComparison.updateLess state.flag false bit } (bit :: scratch)
          simpa [BinaryWordComparison.lessFrom, List.reverse_cons, List.append_assoc] using
            EvalsToInTime.trans _ _ _ _ _ _ first after
  | cons bit left ih =>
      cases right with
      | nil =>
          have first := StackMachineComposition.oneStep
            (compare_cons_nil state bit left scratch input saved result)
          have after := ih { state with first := some bit, second := none, flag := BinaryWordComparison.updateLess state.flag bit false } [] scratch
          simpa [BinaryWordComparison.lessFrom] using
            EvalsToInTime.trans _ _ _ _ _ _ first after
      | cons other right =>
          have first := StackMachineComposition.oneStep
            (compare_cons_cons state bit other left right scratch input saved result)
          have after := ih { state with first := some bit, second := some other, flag := BinaryWordComparison.updateLess state.flag bit other } right (other :: scratch)
          simpa [BinaryWordComparison.lessFrom, List.reverse_cons, List.append_assoc,
            Nat.succ_max_succ] using EvalsToInTime.trans _ _ _ _ _ _ first after

theorem number_bit (state : Registers) (bit : Bool) (input : List Symbol)
    (number depth scratch : List Bool) (saved result : List (Option Bool)) :
    TM2.step program (config (some .number) state (.inl bit :: input) number depth scratch saved result) =
      some (config (some .number) { state with symbol := some (.inl bit) }
        input number depth (bit :: scratch) saved result) := by
  cases bit <;> scope_step

theorem number_end (state : Registers) (input : List Symbol)
    (number depth scratch : List Bool) (saved result : List (Option Bool)) :
    TM2.step program (config (some .number) state (.inr 4 :: input) number depth scratch saved result) =
      some (config (some .restoreNumber) { state with symbol := some (.inr 4) }
        input number depth scratch saved result) := by scope_step

/-- Numeric field capture visits every supplied bit and retains the unused
input suffix. Its framing terminator is consumed as an actual transition. -/
noncomputable def numberRun (state : Registers) (bits : List Bool) (input : List Symbol)
    (number depth scratch : List Bool) (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .number) state (bits.map Sum.inl ++ .inr 4 :: input) number depth scratch saved result)
      (some (config (some .restoreNumber) { state with symbol := some (.inr 4) }
        input number depth (bits.reverse ++ scratch) saved result)) (bits.length + 1) := by
  induction bits generalizing state scratch with
  | nil => simpa using StackMachineComposition.oneStep (number_end state input number depth scratch saved result)
  | cons bit bits ih =>
      have first := StackMachineComposition.oneStep (number_bit state bit
        (bits.map Sum.inl ++ .inr 4 :: input) number depth scratch saved result)
      have after := ih { state with symbol := some (.inl bit) } (bit :: scratch)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first after

theorem restoreComparison_cons (state : Registers) (bit : Bool) (rest depth number : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .restoreComparison) state input number depth (bit :: rest) saved result) =
      some (config (some .restoreComparison) { state with first := some bit }
        input number (bit :: depth) rest saved result) := by scope_step

theorem restoreComparison_nil (state : Registers) (depth number : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .restoreComparison) state input number depth [] saved result) =
      some (config (some .next) (ready state.accepted) input number depth [] saved result) := by scope_step

noncomputable def restoreComparisonRun (state : Registers) (scratch depth number : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .restoreComparison) state input number depth scratch saved result)
      (some (config (some .next) (ready state.accepted) input number
        (scratch.reverse ++ depth) [] saved result)) (scratch.length + 1) := by
  induction scratch generalizing state depth with
  | nil => simpa using StackMachineComposition.oneStep (restoreComparison_nil state depth number input saved result)
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep (restoreComparison_cons state bit rest depth number input saved result)
      have after := ih { state with first := some bit } (bit :: depth)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first after

theorem restoreNumber_cons (state : Registers) (bit : Bool)
    (rest number depth : List Bool) (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .restoreNumber) state input number depth (bit :: rest) saved result) =
      some (config (some .restoreNumber) { state with first := some bit }
        input (bit :: number) depth rest saved result) := by scope_step

theorem restoreNumber_nil (state : Registers) (number depth : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .restoreNumber) state input number depth [] saved result) =
      some (config (some (if state.enter then .saveDepth else .compare))
        { state with first := none, flag := if state.enter then state.flag else false }
        input number depth [] (if state.enter then none :: saved else saved) result) := by
  cases state with
  | mk accepted enter symbol first second flag => cases enter <;> scope_step

/-- Reversal restores the exact captured numeric word; binder entry additionally
pushes its physical continuation boundary. -/
noncomputable def restoreNumberRun (state : Registers) (scratch number depth : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .restoreNumber) state input number depth scratch saved result)
      (some (config (some (if state.enter then .saveDepth else .compare))
        { state with first := none, flag := if state.enter then state.flag else false }
        input (scratch.reverse ++ number) depth []
        (if state.enter then none :: saved else saved) result)) (scratch.length + 1) := by
  induction scratch generalizing state number with
  | nil => simpa using StackMachineComposition.oneStep (restoreNumber_nil state number depth input saved result)
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep (restoreNumber_cons state bit rest number depth input saved result)
      have after := ih { state with first := some bit } (bit :: number)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first after

/-- Complete bound checking restores the exact binary context word and is
exactly numerical strict inequality, including arbitrarily large indices. -/
noncomputable def boundStateRun (state : Registers) (flag : state.flag = false)
    (index depth : Nat) (input : List Symbol)
    (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .compare) state input (naturalBits index) (naturalBits depth) [] saved result)
      (some (config (some .next) (ready (state.accepted && decide (index < depth)))
        input [] (naturalBits depth) [] saved result))
      (max (naturalBits index).length (naturalBits depth).length + (naturalBits depth).length + 2) := by
  have compared := compareRun state (naturalBits index) (naturalBits depth) [] input saved result
  simp only [List.append_nil] at compared
  have restored := restoreComparisonRun
    { state with first := none, second := none, flag := BinaryWordComparison.lessFrom state.flag (naturalBits index) (naturalBits depth), accepted := state.accepted && BinaryWordComparison.lessFrom state.flag (naturalBits index) (naturalBits depth) }
    (naturalBits depth).reverse [] [] input saved result
  simp only [List.reverse_reverse, List.append_nil] at restored
  have exactLess : BinaryWordComparison.lessFrom false (naturalBits index) (naturalBits depth) =
      decide (index < depth) := BinaryWordComparison.less_naturalBits index depth
  have run := EvalsToInTime.trans _ _ _ _ _ _ compared restored
  simp only [flag, exactLess, List.length_reverse] at run
  convert run using 1
  omega

noncomputable def boundRun (accepted : Bool) (index depth : Nat) (input : List Symbol)
    (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .compare) (ready accepted) input (naturalBits index) (naturalBits depth) [] saved result)
      (some (config (some .next) (ready (accepted && decide (index < depth)))
        input [] (naturalBits depth) [] saved result))
      (max (naturalBits index).length (naturalBits depth).length + (naturalBits depth).length + 2) :=
  boundStateRun (ready accepted) rfl index depth input saved result

theorem saveDepth_cons (state : Registers) (bit : Bool) (rest number scratch : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .saveDepth) state input number (bit :: rest) scratch saved result) =
      some (config (some .saveDepth) { state with first := some bit }
        input number rest (bit :: scratch) (some bit :: saved) result) := by scope_step

theorem saveDepth_nil (state : Registers) (number scratch : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .saveDepth) state input number [] scratch saved result) =
      some (config (some .restoreDepth) { state with first := none }
        input number [] scratch saved result) := by scope_step

/-- Saving a depth copies every bit into both the saved frame and restoration
scratch, without consuming the next source event. -/
noncomputable def saveDepthRun (state : Registers) (depth number scratch : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .saveDepth) state input number depth scratch saved result)
      (some (config (some .restoreDepth) { state with first := none }
        input number [] (depth.reverse ++ scratch)
        (depth.reverse.map some ++ saved) result)) (depth.length + 1) := by
  induction depth generalizing state scratch saved with
  | nil => simpa using StackMachineComposition.oneStep (saveDepth_nil state number scratch input saved result)
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep (saveDepth_cons state bit rest number scratch input saved result)
      have after := ih { state with first := some bit } (bit :: scratch) (some bit :: saved)
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        EvalsToInTime.trans _ _ _ _ _ _ first after

theorem restoreDepth_cons (state : Registers) (bit : Bool) (rest depth number : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .restoreDepth) state input number depth (bit :: rest) saved result) =
      some (config (some .restoreDepth) { state with first := some bit }
        input number (bit :: depth) rest saved result) := by scope_step

theorem restoreDepth_nil (state : Registers) (depth number : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .restoreDepth) state input number depth [] saved result) =
      some (config (some .add) { state with first := none, flag := false }
        input number depth [] saved result) := by scope_step

noncomputable def restoreDepthRun (state : Registers) (scratch depth number : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .restoreDepth) state input number depth scratch saved result)
      (some (config (some .add) { state with first := none, flag := false }
        input number (scratch.reverse ++ depth) [] saved result)) (scratch.length + 1) := by
  induction scratch generalizing state depth with
  | nil => simpa using StackMachineComposition.oneStep (restoreDepth_nil state depth number input saved result)
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep (restoreDepth_cons state bit rest depth number input saved result)
      have after := ih { state with first := some bit } (bit :: depth)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first after

theorem leaveClear_cons (state : Registers) (bit : Bool) (rest number scratch : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .leaveClear) state input number (bit :: rest) scratch saved result) =
      some (config (some .leaveClear) { state with first := some bit }
        input number rest scratch saved result) := by scope_step

theorem leaveClear_nil (state : Registers) (number scratch : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .leaveClear) state input number [] scratch saved result) =
      some (config (some .leaveRestore) { state with first := none }
        input number [] scratch saved result) := by scope_step

noncomputable def leaveClearRun (state : Registers) (depth number scratch : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .leaveClear) state input number depth scratch saved result)
      (some (config (some .leaveRestore) { state with first := none }
        input number [] scratch saved result)) (depth.length + 1) := by
  induction depth generalizing state with
  | nil => simpa using StackMachineComposition.oneStep (leaveClear_nil state number scratch input saved result)
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep (leaveClear_cons state bit rest number scratch input saved result)
      have after := ih { state with first := some bit }
      simpa using EvalsToInTime.trans _ _ _ _ _ _ first after

theorem leaveRestore_cons (state : Registers) (bit : Bool) (saved : List (Option Bool))
    (number depth scratch : List Bool) (input : List Symbol) (result : List (Option Bool)) :
    TM2.step program (config (some .leaveRestore) state input number depth scratch (some bit :: saved) result) =
      some (config (some .leaveRestore) { state with symbol := some (.inl bit) }
        input number (bit :: depth) scratch saved result) := by cases bit <;> scope_step

theorem leaveRestore_boundary (state : Registers) (saved : List (Option Bool))
    (number depth scratch : List Bool) (input : List Symbol) (result : List (Option Bool)) :
    TM2.step program (config (some .leaveRestore) state input number depth scratch (none :: saved) result) =
      some (config (some .next) (ready state.accepted) input number depth scratch saved result) := by scope_step

/-- A saved frame is popped only through its actual delimiter. Zero depth has
an empty word and still owns a delimiter, so it cannot be confused with no frame. -/
noncomputable def leaveRestoreRun (state : Registers) (bits depth number scratch : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .leaveRestore) state input number depth scratch
        (bits.map some ++ none :: saved) result)
      (some (config (some .next) (ready state.accepted)
        input number (bits.reverse ++ depth) scratch saved result)) (bits.length + 1) := by
  induction bits generalizing state depth with
  | nil => simpa using StackMachineComposition.oneStep (leaveRestore_boundary state saved number depth scratch input result)
  | cons bit bits ih =>
      have first := StackMachineComposition.oneStep (leaveRestore_cons state bit
        (bits.map some ++ none :: saved) number depth scratch input result)
      have after := ih { state with symbol := some (.inl bit) } (bit :: depth)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first after

theorem add_nil_nil (state : Registers) (scratch : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .add) state input [] [] scratch saved result) =
      some (config (some .trim) (ready state.accepted) input [] []
        (if state.flag then true :: scratch else scratch) saved result) := by
  cases state with
  | mk accepted enter symbol first second flag => cases flag <;> scope_step

theorem add_nil_cons (state : Registers) (bit : Bool) (rest scratch : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .add) state input [] (bit :: rest) scratch saved result) =
      some (config (some .add) { state with first := none, second := some bit, flag := BinaryWordAddition.nextCarry false bit state.flag }
        input [] rest (BinaryWordAddition.sumBit false bit state.flag :: scratch) saved result) := by scope_step

theorem add_cons_nil (state : Registers) (bit : Bool) (rest scratch : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .add) state input (bit :: rest) [] scratch saved result) =
      some (config (some .add) { state with first := some bit, second := none, flag := BinaryWordAddition.nextCarry bit false state.flag }
        input rest [] (BinaryWordAddition.sumBit bit false state.flag :: scratch) saved result) := by scope_step

theorem add_cons_cons (state : Registers) (left right : Bool)
    (lefts rights scratch : List Bool) (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .add) state input (left :: lefts) (right :: rights) scratch saved result) =
      some (config (some .add) { state with first := some left, second := some right, flag := BinaryWordAddition.nextCarry left right state.flag }
        input lefts rights (BinaryWordAddition.sumBit left right state.flag :: scratch) saved result) := by scope_step

/-- Binder-depth addition uses the original per-bit arithmetic functions. Its
carry and bit scratch are dead on entry to normalization and are reset there. -/
noncomputable def addRun (state : Registers) (left right scratch : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .add) state input left right scratch saved result)
      (some (config (some .trim) (ready state.accepted) input [] []
        ((BinaryWordAddition.addWords state.flag left right).reverse ++ scratch) saved result))
      (left.length + right.length + 1) := by
  induction left generalizing right state scratch with
  | nil =>
      induction right generalizing state scratch with
      | nil =>
          have first := StackMachineComposition.oneStep (add_nil_nil state scratch input saved result)
          cases h : state.flag <;> simpa [BinaryWordAddition.addWords, h] using first
      | cons bit rest ih =>
          have first := StackMachineComposition.oneStep (add_nil_cons state bit rest scratch input saved result)
          have after := ih { state with first := none, second := some bit, flag := BinaryWordAddition.nextCarry false bit state.flag }
            (BinaryWordAddition.sumBit false bit state.flag :: scratch)
          simpa [BinaryWordAddition.addWords, List.reverse_cons, List.append_assoc] using
            EvalsToInTime.trans _ _ _ _ _ _ first after
  | cons bit left ih =>
      cases right with
      | nil =>
          have first := StackMachineComposition.oneStep (add_cons_nil state bit left scratch input saved result)
          have after := ih { state with first := some bit, second := none, flag := BinaryWordAddition.nextCarry bit false state.flag } []
            (BinaryWordAddition.sumBit bit false state.flag :: scratch)
          simpa [BinaryWordAddition.addWords, List.reverse_cons, List.append_assoc] using
            EvalsToInTime.trans _ _ _ _ _ _ first after
      | cons other right =>
          have first := StackMachineComposition.oneStep (add_cons_cons state bit other left right scratch input saved result)
          have after := ih { state with first := some bit, second := some other, flag := BinaryWordAddition.nextCarry bit other state.flag } right
            (BinaryWordAddition.sumBit bit other state.flag :: scratch)
          have joined := EvalsToInTime.trans _ _ _ _ _ _ first after
          have shaped : EvalsToInTime (TM2.step program)
              (config (some .add) state input (bit :: left) (other :: right) scratch saved result)
              (some (config (some .trim) (ready state.accepted) input [] []
                ((BinaryWordAddition.addWords state.flag (bit :: left) (other :: right)).reverse ++ scratch) saved result))
              (1 + (left.length + right.length + 1)) := by
            simpa [BinaryWordAddition.addWords, List.reverse_cons, List.append_assoc, Nat.add_comm] using joined
          exact ⟨shaped.toEvalsTo, shaped.steps_le_m.trans (by simp only [List.length_cons]; omega)⟩

theorem restoreSum_cons (state : Registers) (bit : Bool) (rest depth : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .restoreSum) state input [] depth (bit :: rest) saved result) =
      some (config (some .restoreSum) { state with first := some bit }
        input [] (bit :: depth) rest saved result) := by scope_step

theorem restoreSum_nil (state : Registers) (depth : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .restoreSum) state input [] depth [] saved result) =
      some (config (some .next) (ready state.accepted) input [] depth [] saved result) := by scope_step

noncomputable def restoreSumRun (state : Registers) (scratch depth : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .restoreSum) state input [] depth scratch saved result)
      (some (config (some .next) (ready state.accepted)
        input [] (scratch.reverse ++ depth) [] saved result)) (scratch.length + 1) := by
  induction scratch generalizing state depth with
  | nil => simpa using StackMachineComposition.oneStep (restoreSum_nil state depth input saved result)
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep (restoreSum_cons state bit rest depth input saved result)
      have after := ih { state with first := some bit } (bit :: depth)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first after

theorem trim_false (state : Registers) (rest : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .trim) state input [] [] (false :: rest) saved result) =
      some (config (some .trim) { state with first := some false }
        input [] [] rest saved result) := by scope_step

theorem trim_true (state : Registers) (rest : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .trim) state input [] [] (true :: rest) saved result) =
      some (config (some .restoreSum) { state with first := some true }
        input [] [true] rest saved result) := by scope_step

theorem trim_nil (state : Registers) (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .trim) state input [] [] [] saved result) =
      some (config (some .next) (ready state.accepted) input [] [] [] saved result) := by scope_step

noncomputable def trimRun (state : Registers) (scratch : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .trim) state input [] [] scratch saved result)
      (some (config (some .next) (ready state.accepted)
        input [] (BinaryWordAddition.trim scratch).reverse [] saved result)) (scratch.length + 1) := by
  induction scratch generalizing state with
  | nil => simpa [BinaryWordAddition.trim] using StackMachineComposition.oneStep (trim_nil state input saved result)
  | cons bit rest ih =>
      cases bit with
      | false =>
          have first := StackMachineComposition.oneStep (trim_false state rest input saved result)
          have after := ih { state with first := some false }
          simpa [BinaryWordAddition.trim] using EvalsToInTime.trans _ _ _ _ _ _ first after
      | true =>
          have first := StackMachineComposition.oneStep (trim_true state rest input saved result)
          have after := restoreSumRun { state with first := some true } rest [true] input saved result
          simpa [BinaryWordAddition.trim, List.reverse_cons] using EvalsToInTime.trans _ _ _ _ _ _ first after

noncomputable def additionRun (state : Registers) (flag : state.flag = false)
    (arity depth : Nat) (input : List Symbol) (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .add) state input (naturalBits arity) (naturalBits depth) [] saved result)
      (some (config (some .next) (ready state.accepted)
        input [] (naturalBits (depth + arity)) [] saved result))
      (2 * ((naturalBits arity).length + (naturalBits depth).length) + 3) := by
  have added := addRun state (naturalBits arity) (naturalBits depth) [] input saved result
  simp only [flag, List.append_nil] at added
  have trimmed := trimRun (ready state.accepted)
    (BinaryWordAddition.addWords false (naturalBits arity) (naturalBits depth)).reverse input saved result
  have joined := EvalsToInTime.trans _ _ _ _ _ _ added trimmed
  have output : (BinaryWordAddition.trim
        (BinaryWordAddition.addWords false (naturalBits arity) (naturalBits depth)).reverse).reverse =
      naturalBits (depth + arity) := by
    rw [BinaryWordAddition.trim_reverse, List.reverse_reverse, BinaryWordAddition.addition_exact,
      BinaryStackArithmetic.naturalBits_value, BinaryStackArithmetic.naturalBits_value, Nat.add_comm]
  rw [output] at joined
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by
    have size := BinaryWordAddition.addWords_length (naturalBits arity) (naturalBits depth) false
    simp only [List.length_reverse] at *
    omega)⟩

local macro "scope_ready_step" : tactic => `(tactic| (
  simp [ready, wire, machine, program, config, TM2.step, TM2.stepAux, Function.update]
  all_goals first
    | rfl
    | (funext key; cases key <;> simp [Function.update])))

theorem next_bound (accepted : Bool) (index : Nat) (depth : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .next) (ready accepted)
      (wire (.bound index) ++ input) [] depth [] saved result) =
      some (config (some .number) (ready accepted)
        ((naturalBits index).map Sum.inl ++ .inr 4 :: input) [] depth [] saved result) := by
  scope_ready_step

theorem next_enter (accepted : Bool) (arity : Nat) (depth : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .next) (ready accepted)
      (wire (.enter arity) ++ input) [] depth [] saved result) =
      some (config (some .number) { (ready accepted) with enter := true }
        ((naturalBits arity).map Sum.inl ++ .inr 4 :: input) [] depth [] saved result) := by
  scope_ready_step

theorem next_leave (accepted : Bool) (depth : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .next) (ready accepted)
      (wire .leave ++ input) [] depth [] saved result) =
      some (config (some .leaveClear) (ready accepted) input [] depth [] saved result) := by
  scope_ready_step

theorem next_refuse (accepted : Bool) (depth : List Bool)
    (input : List Symbol) (saved result : List (Option Bool)) :
    TM2.step program (config (some .next) (ready accepted)
      (wire .refuse ++ input) [] depth [] saved result) =
      some (config (some .next) (ready false) input [] depth [] saved result) := by
  scope_ready_step

/-- A complete bound event executes header, binary capture, reversal,
comparison and depth restoration. No numeric operation is a semantic callback. -/
noncomputable def boundEventRun (accepted : Bool) (index depth : Nat)
    (input : List Symbol) (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .next) (ready accepted) (wire (.bound index) ++ input)
        [] (naturalBits depth) [] saved result)
      (some (config (some .next) (ready (accepted && decide (index < depth)))
        input [] (naturalBits depth) [] saved result))
      (2 * (naturalBits index).length + max (naturalBits index).length (naturalBits depth).length +
        (naturalBits depth).length + 5) := by
  have header := StackMachineComposition.oneStep (next_bound accepted index (naturalBits depth) input saved result)
  have captured := numberRun (ready accepted) (naturalBits index) input [] (naturalBits depth) [] saved result
  simp only [List.append_nil] at captured
  let capturedState : Registers := { (ready accepted) with symbol := some (.inr 4) }
  have restored := restoreNumberRun capturedState (naturalBits index).reverse [] (naturalBits depth) input saved result
  simp only [capturedState, ready, Bool.false_eq_true, ↓reduceIte,
    List.reverse_reverse, List.append_nil] at restored
  have checked := boundStateRun { (ready accepted) with symbol := some (.inr 4), first := none, flag := false }
    rfl index depth input saved result
  have first := EvalsToInTime.trans _ _ _ _ _ _ header captured
  have second := EvalsToInTime.trans _ _ _ _ _ _ first restored
  have whole := EvalsToInTime.trans _ _ _ _ _ _ second checked
  exact ⟨whole.toEvalsTo, whole.steps_le_m.trans (by simp only [List.length_reverse]; omega)⟩

/-- Binder entry executes physical save, canonical binary addition and
normalization, retaining the exact old frame and the unused event suffix. -/
noncomputable def enterEventRun (accepted : Bool) (arity depth : Nat)
    (input : List Symbol) (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .next) (ready accepted) (wire (.enter arity) ++ input)
        [] (naturalBits depth) [] saved result)
      (some (config (some .next) (ready accepted)
        input [] (naturalBits (depth + arity)) []
        ((naturalBits depth).reverse.map some ++ none :: saved) result))
      (4 * ((naturalBits arity).length + (naturalBits depth).length) + 8) := by
  let initial : Registers := { (ready accepted) with enter := true }
  let capturedState : Registers := { initial with symbol := some (.inr 4) }
  have header := StackMachineComposition.oneStep (next_enter accepted arity (naturalBits depth) input saved result)
  have captured := numberRun initial (naturalBits arity) input [] (naturalBits depth) [] saved result
  simp only [List.append_nil] at captured
  have restored := restoreNumberRun capturedState (naturalBits arity).reverse [] (naturalBits depth) input saved result
  simp only [initial, capturedState, ready, ↓reduceIte,
    List.reverse_reverse, List.append_nil] at restored
  let savedState : Registers := { capturedState with first := none, flag := capturedState.flag }
  have savedDepth := saveDepthRun savedState (naturalBits depth) (naturalBits arity) [] input (none :: saved) result
  simp only [List.append_nil] at savedDepth
  have restoredDepth := restoreDepthRun { savedState with first := none }
    (naturalBits depth).reverse [] (naturalBits arity) input
    ((naturalBits depth).reverse.map some ++ none :: saved) result
  simp only [List.reverse_reverse, List.append_nil] at restoredDepth
  have added := additionRun { savedState with first := none, flag := false } rfl arity depth input
    ((naturalBits depth).reverse.map some ++ none :: saved) result
  have first := EvalsToInTime.trans _ _ _ _ _ _ header captured
  have second := EvalsToInTime.trans _ _ _ _ _ _ first restored
  have third := EvalsToInTime.trans _ _ _ _ _ _ second savedDepth
  have fourth := EvalsToInTime.trans _ _ _ _ _ _ third restoredDepth
  have whole := EvalsToInTime.trans _ _ _ _ _ _ fourth added
  exact ⟨whole.toEvalsTo, whole.steps_le_m.trans (by simp only [List.length_reverse]; omega)⟩

noncomputable def leaveEventRun (accepted : Bool) (depth oldDepth : Nat)
    (input : List Symbol) (saved result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .next) (ready accepted) (wire .leave ++ input)
        [] (naturalBits depth) [] ((naturalBits oldDepth).reverse.map some ++ none :: saved) result)
      (some (config (some .next) (ready accepted)
        input [] (naturalBits oldDepth) [] saved result))
      ((naturalBits depth).length + (naturalBits oldDepth).length + 3) := by
  have header := StackMachineComposition.oneStep (next_leave accepted (naturalBits depth) input
    ((naturalBits oldDepth).reverse.map some ++ none :: saved) result)
  have cleared := leaveClearRun (ready accepted) (naturalBits depth) [] [] input
    ((naturalBits oldDepth).reverse.map some ++ none :: saved) result
  have restored := leaveRestoreRun { (ready accepted) with first := none }
    (naturalBits oldDepth).reverse [] [] [] input saved result
  simp only [List.reverse_reverse, List.append_nil] at restored
  have whole := EvalsToInTime.trans _ _ _ _ _ _ (EvalsToInTime.trans _ _ _ _ _ _ header cleared) restored
  exact ⟨whole.toEvalsTo, whole.steps_le_m.trans (by simp only [List.length_reverse]; omega)⟩

def savedWire : List Nat → List (Option Bool)
  | [] => []
  | depth :: saved => (naturalBits depth).reverse.map some ++ none :: savedWire saved

/-- The original semantic context is represented entirely by the existing
machine's depth and saved stacks. -/
def atNext (state : Context) (input : List Symbol) (result : List (Option Bool)) : machine.Cfg :=
  config (some .next) (ready state.accepted) input [] (naturalBits state.depth) []
    (savedWire state.saved) result

def eventCost (event : Event) (state : Context) : Nat := match event with
  | .bound index => 2 * (naturalBits index).length +
      max (naturalBits index).length (naturalBits state.depth).length +
      (naturalBits state.depth).length + 5
  | .enter arity => 4 * ((naturalBits arity).length + (naturalBits state.depth).length) + 8
  | .leave => (naturalBits state.depth).length +
      (naturalBits (state.saved.headD 0)).length + 3
  | .refuse => 1

/-- Every successful original context operation is physically realized at its
recorded cost, preserving the complete unread event suffix. -/
noncomputable def eventRun (event : Event) (state next : Context)
    (accepted : step event state = some next) (input : List Symbol)
    (result : List (Option Bool)) :
    EvalsToInTime (TM2.step program) (atNext state (wire event ++ input) result)
      (some (atNext next input result)) (eventCost event state) := by
  cases event with
  | bound index =>
      simp only [step, Option.some.injEq] at accepted
      subst next
      exact boundEventRun state.accepted index state.depth input (savedWire state.saved) result
  | enter arity =>
      simp only [step, Option.some.injEq] at accepted
      subst next
      exact enterEventRun state.accepted arity state.depth input (savedWire state.saved) result
  | leave =>
      cases state with
      | mk depth saved flag =>
          cases saved with
          | nil => simp [step] at accepted
          | cons oldDepth saved =>
              simp only [step, Option.some.injEq] at accepted
              subst next
              exact leaveEventRun flag depth oldDepth input (savedWire saved) result
  | refuse =>
      simp only [step, Option.some.injEq] at accepted
      subst next
      exact StackMachineComposition.oneStep (next_refuse state.accepted
        (naturalBits state.depth) input (savedWire state.saved) result)

def traceCost : List Event → Context → Nat
  | [], _ => 0
  | event :: events, state =>
      eventCost event state + (match step event state with
        | none => 0
        | some next => traceCost events next)

/-- Composition follows the original context transition function. The clock is
derived from the executed event operations; it is not an independent annotation. -/
noncomputable def eventsRun (source : List Event) (state next : Context)
    (accepted : walk source state = some next) (input : List Symbol)
    (result : List (Option Bool)) :
    EvalsToInTime (TM2.step program) (atNext state (encode source ++ input) result)
      (some (atNext next input result)) (traceCost source state) := by
  induction source generalizing state with
  | nil =>
      simp only [walk, Option.some.injEq] at accepted
      subst state
      exact EvalsToInTime.refl _ _
  | cons event source ih =>
      cases transition : step event state with
      | none => simp [walk, transition] at accepted
      | some middle =>
          have remainder : walk source middle = some next := by simpa [walk, transition] using accepted
          have first := eventRun event state middle transition (encode source ++ input) result
          have after := ih middle remainder
          simpa only [encode_cons, List.append_assoc, traceCost, transition, Nat.add_comm] using
            EvalsToInTime.trans _ _ _ _ _ _ first after

theorem next_end (accepted : Bool) (depth : List Bool) (result : List (Option Bool)) :
    TM2.step program (config (some .next) (ready accepted) [] [] depth [] [] result) =
      some (config (some .finishDepth) (ready accepted) [] [] depth [] [] result) := by
  scope_ready_step

theorem finishDepth_cons (state : Registers) (bit : Bool) (rest : List Bool)
    (result : List (Option Bool)) :
    TM2.step program (config (some .finishDepth) state [] [] (bit :: rest) [] [] result) =
      some (config (some .finishDepth) { state with first := some bit } [] [] rest [] [] result) := by scope_step

theorem finishDepth_nil (state : Registers) (result : List (Option Bool)) :
    TM2.step program (config (some .finishDepth) state [] [] [] [] [] result) =
      some (config none (ready true) [] [] [] [] [] (some state.accepted :: result)) := by scope_step

noncomputable def finishDepthRun (state : Registers) (depth : List Bool)
    (result : List (Option Bool)) :
    EvalsToInTime (TM2.step program)
      (config (some .finishDepth) state [] [] depth [] [] result)
      (some (config none (ready true) [] [] [] [] [] (some state.accepted :: result)))
      (depth.length + 1) := by
  induction depth generalizing state with
  | nil => simpa using StackMachineComposition.oneStep (finishDepth_nil state result)
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep (finishDepth_cons state bit rest result)
      have after := ih { state with first := some bit }
      simpa using EvalsToInTime.trans _ _ _ _ _ _ first after

/-- The finite consumer returns exactly the original source check, including
negative judgments, and resets every physical stack and control field. -/
noncomputable def admissionRun (depth : Nat) (pattern : Pattern) :
    EvalsToInTime (TM2.step program)
      (atNext ⟨depth, [], true⟩ (encode (events pattern)) [])
      (some (config none (ready true) [] [] [] [] [] [some (argumentValidAt depth pattern)]))
      (traceCost (events pattern) ⟨depth, [], true⟩ + (naturalBits depth).length + 2) := by
  have walked := eventsRun (events pattern) ⟨depth, [], true⟩
    ⟨depth, [], argumentValidAt depth pattern⟩ (admission_exact depth pattern) [] []
  simp only [List.append_nil] at walked
  have ending := StackMachineComposition.oneStep
    (next_end (argumentValidAt depth pattern) (naturalBits depth) [])
  have finished := finishDepthRun (ready (argumentValidAt depth pattern)) (naturalBits depth) []
  have whole := EvalsToInTime.trans _ _ _ _ _ _ (EvalsToInTime.trans _ _ _ _ _ _ walked ending) finished
  exact ⟨whole.toEvalsTo, whole.steps_le_m.trans (by omega)⟩

theorem normalized_length (word : List Bool) :
    (BinaryWordAddition.normalize word).length ≤ word.length := by
  induction word with
  | nil => rfl
  | cons bit rest ih =>
      simp only [BinaryWordAddition.normalize, List.length_cons]
      split <;> simp only [List.length_nil, List.length_cons] <;> omega

theorem added_depth_length (depth arity : Nat) :
    (naturalBits (depth + arity)).length ≤
      (naturalBits depth).length + (naturalBits arity).length + 1 := by
  have normalized := normalized_length
    (BinaryWordAddition.addWords false (naturalBits depth) (naturalBits arity))
  rw [BinaryWordAddition.addition_exact, BinaryStackArithmetic.naturalBits_value,
    BinaryStackArithmetic.naturalBits_value] at normalized
  exact normalized.trans (BinaryWordAddition.addWords_length (naturalBits depth) (naturalBits arity) false)

/-- All live and saved binary depths stay within the supplied bit budget. -/
def Within (state : Context) (budget : Nat) : Prop :=
  (naturalBits state.depth).length ≤ budget ∧
    ∀ depth ∈ state.saved, (naturalBits depth).length ≤ budget

theorem wire_nonempty (event : Event) : 1 ≤ (wire event).length := by
  cases event <;> simp [wire]

theorem eventCost_bound (event : Event) (state : Context) (budget : Nat)
    (within : Within state budget) :
    eventCost event state ≤ 8 * (budget + (wire event).length + 1) := by
  obtain ⟨depthBound, savedBound⟩ := within
  cases event with
  | bound index =>
      simp only [eventCost, wire, List.length_cons, List.length_append,
        List.length_map]
      have maximum := Nat.max_le.mpr ⟨Nat.le_add_right (naturalBits index).length budget,
        depthBound.trans (by omega : budget ≤ (naturalBits index).length + budget)⟩
      omega
  | enter arity =>
      simp only [eventCost, wire, List.length_cons, List.length_append,
        List.length_map]
      omega
  | leave =>
      cases saved : state.saved with
      | nil =>
          simp only [eventCost, wire, saved, List.headD_nil, List.length_singleton,
            show (naturalBits 0).length = 0 from rfl]
          omega
      | cons oldDepth saved =>
          have oldBound := savedBound oldDepth (by simp [saved])
          simp [eventCost, wire, saved]
          omega
  | refuse => simp only [eventCost, wire, List.length_singleton]; omega

theorem step_within (event : Event) (state next : Context) (budget : Nat)
    (transition : step event state = some next) (within : Within state budget) :
    Within next (budget + (wire event).length) := by
  obtain ⟨depthBound, savedBound⟩ := within
  cases event with
  | bound index =>
      simp only [step, Option.some.injEq] at transition
      subst next
      exact ⟨depthBound.trans (Nat.le_add_right _ _), fun depth member =>
        (savedBound depth member).trans (Nat.le_add_right _ _)⟩
  | enter arity =>
      simp only [step, Option.some.injEq] at transition
      subst next
      refine ⟨?_, ?_⟩
      · have added := added_depth_length state.depth arity
        simp only [wire, List.length_cons, List.length_append,
          List.length_map]
        omega
      · intro depth member
        rcases List.mem_cons.mp member with same | member
        · subst depth; exact depthBound.trans (Nat.le_add_right _ _)
        · exact (savedBound depth member).trans (Nat.le_add_right _ _)
  | leave =>
      cases state with
      | mk depth saved accepted =>
          cases saved with
          | nil => simp [step] at transition
          | cons oldDepth saved =>
              simp only [step, Option.some.injEq] at transition
              subst next
              exact ⟨(savedBound oldDepth (List.mem_cons_self)).trans (Nat.le_add_right _ _),
                fun depth member => (savedBound depth (List.mem_cons_of_mem _ member)).trans (Nat.le_add_right _ _)⟩
  | refuse =>
      simp only [step, Option.some.injEq] at transition
      subst next
      exact ⟨depthBound.trans (Nat.le_add_right _ _), fun depth member =>
        (savedBound depth member).trans (Nat.le_add_right _ _)⟩

theorem traceCost_bound (source : List Event) (state : Context) (budget : Nat)
    (within : Within state budget) :
    traceCost source state ≤ 8 * (budget + (encode source).length + 1) * source.length := by
  induction source generalizing state budget with
  | nil => simp [traceCost]
  | cons event source ih =>
      have firstBound := eventCost_bound event state budget within
      cases transition : step event state with
      | none =>
          simp only [traceCost, transition, Nat.add_zero, encode_cons,
            List.length_append, List.length_cons]
          calc
            eventCost event state ≤ 8 * (budget + (wire event).length + 1) := firstBound
            _ ≤ 8 * (budget + ((wire event).length + (encode source).length) + 1) := by omega
            _ ≤ 8 * (budget + ((wire event).length + (encode source).length) + 1) * (source.length + 1) := by
              exact Nat.le_mul_of_pos_right _ (by omega)
      | some next =>
          have after := ih next (budget + (wire event).length) (step_within event state next budget transition within)
          simp only [traceCost, transition, encode_cons, List.length_append, List.length_cons]
          have expanded := Nat.mul_add (8 * (budget + (wire event).length + (encode source).length + 1)) source.length 1
          nlinarith

theorem events_length_le_encoded (source : List Event) : source.length ≤ (encode source).length := by
  induction source with
  | nil => rfl
  | cons event source ih =>
      have positive := wire_nonempty event
      simp only [List.length_cons, encode_cons, List.length_append]
      omega

theorem admission_clock_bound (depth : Nat) (pattern : Pattern) :
    traceCost (events pattern) ⟨depth, [], true⟩ + (naturalBits depth).length + 2 ≤
      10 * ((naturalBits depth).length + (encode (events pattern)).length + 1)^2 := by
  have bounded := traceCost_bound (events pattern) ⟨depth, [], true⟩
    (naturalBits depth).length ⟨Nat.le_refl _, by simp⟩
  have count := events_length_le_encoded (events pattern)
  have enlarged := Nat.mul_le_mul_left (8 * ((naturalBits depth).length + (encode (events pattern)).length + 1)) count
  nlinarith

/-- The attached operational clock is quadratic in complete bit payloads,
rather than the numerical magnitude of binder arities or indices. -/
noncomputable def admissionPolynomialRun (depth : Nat) (pattern : Pattern) :
    EvalsToInTime (TM2.step program)
      (atNext ⟨depth, [], true⟩ (encode (events pattern)) [])
      (some (config none (ready true) [] [] [] [] [] [some (argumentValidAt depth pattern)]))
      (10 * ((naturalBits depth).length + (encode (events pattern)).length + 1)^2) :=
  let run := admissionRun depth pattern
  ⟨run.toEvalsTo, run.steps_le_m.trans (admission_clock_bound depth pattern)⟩

/-- A static view of the shared structural visitor's events. Full numeric
payloads are copied bit for bit; names and constructor boundaries carry no
additional scope operation. -/
def scopeSymbol : PatternSpanExecution.Event → List Symbol
  | .numberStart .boundIndex => [.inr 0]
  | .numberStart .binderArity => [.inr 1]
  | .bit _ bit => [.inl bit]
  | .numberEnd _ => [.inr 4]
  | .enterOne => wire (.enter 1)
  | .leave => [.inr 2]
  | .metadataPresent _ | .namedBinder | .freeVariable => [.inr 3]
  | _ => []

def project (source : List PatternSpanExecution.Event) : List Symbol := source.flatMap scopeSymbol

@[simp] theorem project_nil : project [] = [] := rfl
@[simp] theorem project_cons (event : PatternSpanExecution.Event)
    (rest : List PatternSpanExecution.Event) :
    project (event :: rest) = scopeSymbol event ++ project rest := rfl

theorem project_append (first second : List PatternSpanExecution.Event) :
    project (first ++ second) = project first ++ project second := List.flatMap_append

theorem project_number (role : PatternSpanExecution.NumberRole) (value : Nat) :
    project (PatternSpanExecution.numberEvents role value) =
      (naturalBits value).map Sum.inl ++ [.inr 4] := by
  have bits : (Nat.digits 2 value).map (fun digit => Sum.inl (digit != 0) : Nat → Symbol) =
      (naturalBits value).map Sum.inl := by
    rw [naturalBits, List.map_map]
    apply List.map_congr_left
    intro digit member
    have bound := Nat.digits_lt_base (by decide : 1 < 2) member
    by_cases zero : digit = 0
    · subst digit; rfl
    · have one : digit = 1 := by omega
      subst digit; rfl
  cases role <;>
    simpa only [project, PatternSpanExecution.numberEvents, scopeSymbol,
      List.flatMap_append, List.flatMap_map, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, ← List.map_eq_flatMap] using congrArg (· ++ [.inr 4]) bits

theorem project_options (role : PatternSpanExecution.OptionRole) (name : Option String) :
    project (PatternSpanExecution.optionEvents role name) =
      if name.isNone then [] else [.inr 3] := by
  cases name <;> cases role <;> rfl

theorem project_names (names : List String) :
    project (PatternSpanExecution.nameEvents names) =
      encode (names.map fun _ => Event.refuse) := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      simpa only [PatternSpanExecution.nameEvents, project_cons, scopeSymbol,
        List.nil_append, List.singleton_append, List.map_cons,
        encode_cons, wire] using congrArg ((Sum.inr 3 : Symbol) :: ·) ih

mutual
  /-- The shared parser trace feeds exactly the scope operations of the original
  Pattern, preserving arities, indices, metadata refusals and binder returns. -/
  theorem project_events (pattern : Pattern) :
      project (PatternSpanExecution.events pattern) = encode (events pattern) := by
    cases pattern with
    | bvar index => simp [PatternSpanExecution.events, project_append, project_number,
        events, wire, scopeSymbol]
    | fvar name => rfl
    | apply name arguments =>
        simpa [PatternSpanExecution.events, project_append, events, scopeSymbol]
          using project_listEvents arguments
    | lambda binder body =>
        cases binder <;>
        simp [PatternSpanExecution.events, project_append, project_options,
          project_events body, events, encode_append, wire, scopeSymbol, List.append_assoc]
    | multiLambda arity names body =>
        simp [PatternSpanExecution.events, project_append, project_number, project_names,
          project_events body, events, encode_append, wire, scopeSymbol, List.append_assoc]
    | subst body replacement =>
        simp [PatternSpanExecution.events, project_append, project_events body,
          project_events replacement, events, encode_append, wire, scopeSymbol, List.append_assoc]
    | collection kind elements rest =>
        cases kind <;> cases rest <;>
          simp [PatternSpanExecution.events, PatternSpanExecution.kindEvent, project_append,
            project_options, project_listEvents elements, events, wire,
            scopeSymbol, List.append_assoc]
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem project_listEvents (patterns : List Pattern) :
      project (PatternSpanExecution.listEvents patterns) = encode (listEvents patterns) := by
    cases patterns with
    | nil => rfl
    | cons pattern patterns =>
        simp [PatternSpanExecution.listEvents, project_append, project_events pattern,
          project_listEvents patterns, listEvents, encode_append]
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

end Binary

/- A byte-preserving adapter around the original structural visitor. Only its
real halt is redirected: retained prefix/tail bytes are cleared, then the event
stack is physically reversed into the output stack. -/
namespace VisitorAdapter
open Turing StateTransition Polynomial Turing.TM2.Stmt
open Mettapedia.Computability
open Mettapedia.OSLF.Binding.WireCodec.Binary
open PatternSpanExecution

inductive Phase where
  | visit (phase : Execution.Phase)
  | clearInput | clearReceipt | reverseEvents
  deriving DecidableEq, Fintype
abbrev Cells := StackMachineRegisters.withStackAlphabet Execution.StackAlphabet PatternSpanExecution.Event
instance (key : Option Execution.Stack) : Fintype (Cells key) := by
  cases key with
  | none => change Fintype PatternSpanExecution.Event; infer_instance
  | some key => cases key <;> infer_instance
abbrev Control := Execution.Control × Unit
def initial : Control := (Execution.initial, ())

def program : Phase → TM2.Stmt Cells Phase Control
  | .visit phase => StackMachineRegisters.withStack id
      (StackMachineRegisters.returning Phase.visit (fun (_ : Unit) => .clearInput) (Execution.program phase))
  | .clearInput => pop (some .input) (fun state symbol => ({state.1 with symbol := symbol}, ()))
      (branch (fun state => state.1.symbol.isSome) (goto fun _ => .clearInput) (goto fun _ => .clearReceipt))
  | .clearReceipt => pop (some .result) (fun state symbol => ({state.1 with symbol := symbol}, ()))
      (branch (fun state => state.1.symbol.isSome) (goto fun _ => .clearReceipt) (goto fun _ => .reverseEvents))
  | .reverseEvents => pop (some .events) (fun state event => ({state.1 with event := event}, ()))
      (branch (fun state => state.1.event.isSome)
        (push none (fun state => state.1.event.getD .finish) (goto fun _ => .reverseEvents))
        (load (fun _ => initial) halt))

def machine : FinTM2 where
  K := Option Execution.Stack
  k₀ := some .input
  k₁ := none
  Γ := Cells
  Λ := Phase
  main := .visit .start
  σ := Control
  initialState := initial
  m := program

abbrev Cfg := TM2.Cfg Cells Phase Control

def embed (output : List PatternSpanExecution.Event) (source : Execution.Cfg) : Cfg :=
  StackMachineRegisters.withStackConfig id output
    (StackMachineRegisters.returningConfig Phase.visit (fun (_ : Unit) => .clearInput) () source)

theorem visitor_step (output : List PatternSpanExecution.Event) (before after : Execution.Cfg)
    (executed : Execution.step before = some after) :
    TM2.step program (embed output before) = some (embed output after) := by
  cases before with
  | mk phase state contents =>
      cases phase with
      | none => simp [Execution.step, TM2.step] at executed
      | some phase =>
          simp only [Execution.step, TM2.step] at executed
          have identified := Option.some.inj executed
          subst after
          simp only [embed, StackMachineRegisters.withStackConfig,
            StackMachineRegisters.returningConfig, Option.elim_some, Option.map_some,
            TM2.step, id_eq, program]
          rw [StackMachineRegisters.stepAux_withStack,
            StackMachineRegisters.stepAux_returning]
          rfl

def config (phase : Option Phase) (state : Control) (input receipt : List Alphabet)
    (events output : List PatternSpanExecution.Event) : Cfg where
  l := phase
  var := state
  stk key := match key with
    | none => output
    | some .input => input
    | some .result => receipt
    | some .events => events
    | _ => []

local macro "adapter_step" : tactic => `(tactic| (
  simp [program, config, TM2.step, TM2.stepAux, Function.update]
  all_goals first | rfl | (funext key; cases key with
    | none => simp [Function.update]
    | some key => cases key <;> simp [Function.update])))

theorem clearInput_cons (state : Control) (head : Alphabet) (tail receipt : List Alphabet)
    (events output : List PatternSpanExecution.Event) :
    TM2.step program (config (some .clearInput) state (head :: tail) receipt events output) =
      some (config (some .clearInput) ({state.1 with symbol := some head}, ()) tail receipt events output) := by adapter_step
theorem clearInput_nil (state : Control) (receipt : List Alphabet)
    (events output : List PatternSpanExecution.Event) :
    TM2.step program (config (some .clearInput) state [] receipt events output) =
      some (config (some .clearReceipt) ({state.1 with symbol := none}, ()) [] receipt events output) := by adapter_step

noncomputable def clearInputRun (state : Control) (input receipt : List Alphabet)
    (events output : List PatternSpanExecution.Event) :
    EvalsToInTime (TM2.step program) (config (some .clearInput) state input receipt events output)
      (some (config (some .clearReceipt) ({state.1 with symbol := none}, ()) [] receipt events output))
      (input.length + 1) := by
  induction input generalizing state with
  | nil => simpa using StackMachineComposition.oneStep (clearInput_nil state receipt events output)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (clearInput_cons state head tail receipt events output)
      simpa using EvalsToInTime.trans _ _ _ _ _ _ first (ih ({state.1 with symbol := some head}, ()))

theorem clearReceipt_cons (state : Control) (head : Alphabet) (tail : List Alphabet)
    (events output : List PatternSpanExecution.Event) :
    TM2.step program (config (some .clearReceipt) state [] (head :: tail) events output) =
      some (config (some .clearReceipt) ({state.1 with symbol := some head}, ()) [] tail events output) := by adapter_step
theorem clearReceipt_nil (state : Control) (events output : List PatternSpanExecution.Event) :
    TM2.step program (config (some .clearReceipt) state [] [] events output) =
      some (config (some .reverseEvents) ({state.1 with symbol := none}, ()) [] [] events output) := by adapter_step

noncomputable def clearReceiptRun (state : Control) (receipt : List Alphabet)
    (events output : List PatternSpanExecution.Event) :
    EvalsToInTime (TM2.step program) (config (some .clearReceipt) state [] receipt events output)
      (some (config (some .reverseEvents) ({state.1 with symbol := none}, ()) [] [] events output))
      (receipt.length + 1) := by
  induction receipt generalizing state with
  | nil => simpa using StackMachineComposition.oneStep (clearReceipt_nil state events output)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (clearReceipt_cons state head tail events output)
      simpa using EvalsToInTime.trans _ _ _ _ _ _ first (ih ({state.1 with symbol := some head}, ()))

theorem reverseEvents_cons (state : Control) (event : PatternSpanExecution.Event)
    (events output : List PatternSpanExecution.Event) :
    TM2.step program (config (some .reverseEvents) state [] [] (event :: events) output) =
      some (config (some .reverseEvents) ({state.1 with event := some event}, ()) [] [] events (event :: output)) := by adapter_step
theorem reverseEvents_nil (state : Control) (output : List PatternSpanExecution.Event) :
    TM2.step program (config (some .reverseEvents) state [] [] [] output) =
      some (config none initial [] [] [] output) := by adapter_step

noncomputable def reverseEventsRun (state : Control) (events output : List PatternSpanExecution.Event) :
    EvalsToInTime (TM2.step program) (config (some .reverseEvents) state [] [] events output)
      (some (config none initial [] [] [] (events.reverse ++ output))) (events.length + 1) := by
  induction events generalizing state output with
  | nil => simpa using StackMachineComposition.oneStep (reverseEvents_nil state output)
  | cons event events ih =>
      have first := StackMachineComposition.oneStep (reverseEvents_cons state event events output)
      have after := ih ({state.1 with event := some event}, ()) (event :: output)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first after

theorem embed_complete (input receipt : List Alphabet)
    (events output : List PatternSpanExecution.Event) :
    embed output (Execution.config none Execution.initial input [] [] [] [] events receipt) =
      config (some .clearInput) initial input receipt events output := by
  simp only [embed, StackMachineRegisters.withStackConfig, StackMachineRegisters.returningConfig,
    Option.elim_none, Option.map_some, id_eq, Execution.config, config, initial]
  congr 1
  funext key
  cases key with
  | none => rfl
  | some key => cases key <;> rfl

theorem init_eq (pattern : Pattern) :
    initList machine (encodeWith CertificateDataEncoding.patternCodec pattern) =
      embed [] (Execution.startConfig (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern)) := by
  rw [Execution.original_pattern_wire]
  simp only [initList, machine, embed, StackMachineRegisters.withStackConfig,
    StackMachineRegisters.returningConfig, Execution.startConfig, Execution.config, initial]
  congr 1
  funext key
  cases key with
  | none => rfl
  | some key => cases key <;> simp [StackMachineRegisters.withStackContents]

theorem halt_eq (output : List PatternSpanExecution.Event) :
    haltList machine output = config none initial [] [] [] output := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key with
  | none => simp
  | some key => cases key <;> simp

/-- Every original Pattern-codec image is physically visited and emits its
forward event trace, with all byte receipts and continuation scratch cleared. -/
noncomputable def outputs (pattern : Pattern) :
    TM2OutputsInTime machine (encodeWith CertificateDataEncoding.patternCodec pattern)
      (some (PatternSpanExecution.events pattern))
      (28 * (encodeWith CertificateDataEncoding.patternCodec pattern).length + 11) := by
  let original := Classical.choice (Execution.pattern_execution_linear pattern [])
  have visited := StackMachineComposition.lift_execution Execution.step (TM2.step program)
    (embed []) (visitor_step []) original
  simp only [List.append_nil] at visited
  rw [embed_complete] at visited
  have clearInput := clearInputRun initial (Execution.tokenWire [])
    (Execution.tokenWire (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern))
    (PatternSpanExecution.events pattern).reverse []
  have clearReceipt := clearReceiptRun ({Execution.initial with symbol := none}, ())
    (Execution.tokenWire (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern))
    (PatternSpanExecution.events pattern).reverse []
  have reversed := reverseEventsRun ({Execution.initial with symbol := none}, ())
    (PatternSpanExecution.events pattern).reverse []
  simp only [List.reverse_reverse, List.append_nil] at reversed
  have whole := EvalsToInTime.trans _ _ _ _ _ _
    (EvalsToInTime.trans _ _ _ _ _ _ (EvalsToInTime.trans _ _ _ _ _ _ visited clearInput) clearReceipt) reversed
  change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
  rw [init_eq, halt_eq]
  refine ⟨whole.toEvalsTo, whole.steps_le_m.trans ?_⟩
  have count := Execution.pattern_events_length_le pattern
  have length : (Execution.tokenWire (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern)).length =
      (encodeWith CertificateDataEncoding.patternCodec pattern).length := rfl
  have framing := Execution.tokenWire_eq (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern)
  simp only [List.length_reverse]
  have emptyLength : (Execution.tokenWire []).length = 2 := rfl
  rw [emptyLength]
  have fieldsSize : (Execution.fields (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern)).length ≤
      (encodeWith CertificateDataEncoding.patternCodec pattern).length := by
    rw [← length, framing, List.length_append]
    omega
  omega

end VisitorAdapter

namespace Binary

open Turing StateTransition Polynomial
open Mettapedia.Computability.BinaryStackArithmetic (naturalBits)

theorem scopeSymbol_length (event : PatternSpanExecution.Event) : (scopeSymbol event).length ≤ 3 := by
  cases event <;> simp [scopeSymbol, wire, naturalBits]
  all_goals split <;> simp

theorem project_length (source : List PatternSpanExecution.Event) :
    (project source).length ≤ 3 * source.length := by
  induction source with
  | nil => rfl
  | cons event source ih =>
      have head := scopeSymbol_length event
      simp only [project_cons, List.length_append, List.length_cons]
      omega

theorem machine_step : machine.step = TM2.step program := rfl

theorem init_eq (source : List Symbol) :
    initList machine source = atNext ⟨0, [], true⟩ source [] := by
  simp only [initList, machine, atNext, config, savedWire]
  congr 1
  funext key
  cases key <;> simp [naturalBits]

theorem halt_eq (accepted : Bool) :
    haltList machine [some accepted] = config none (ready true) [] [] [] [] [] [some accepted] := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key <;> simp

/-- Scope checking consumes exactly the projected shared visitor events. -/
noncomputable def outputs (pattern : Pattern) :
    TM2OutputsInTime machine (project (PatternSpanExecution.events pattern))
      (some [some (argumentValidAt 0 pattern)])
      (10 * ((project (PatternSpanExecution.events pattern)).length + 1)^2) := by
  change EvalsToInTime (TM2.step program) (initList machine _) (some (haltList machine _)) _
  rw [init_eq, halt_eq, project_events]
  simpa only [show (naturalBits 0).length = 0 from rfl, Nat.zero_add] using admissionPolynomialRun 0 pattern

end Binary

namespace OriginalAdmission
open Turing StateTransition Polynomial Turing.TM2.Stmt
open Mettapedia.Computability
open Mettapedia.OSLF.Binding.WireCodec.Binary

local instance : Inhabited PatternSpanExecution.Event := ⟨.finish⟩
local instance : Fintype (VisitorAdapter.machine.Γ VisitorAdapter.machine.k₁) := by
  change Fintype PatternSpanExecution.Event; infer_instance
local instance : Inhabited (VisitorAdapter.machine.Γ VisitorAdapter.machine.k₁) := by
  change Inhabited PatternSpanExecution.Event; infer_instance

/-- The first handoff executes original byte traversal and static event
projection, with the actual intermediate word transfer included. -/
def projectedMachine : FinTM2 := StackMachineComposition.machine VisitorAdapter.machine
  (WordHomomorphismMachine.machine Binary.scopeSymbol) (Equiv.refl _)

local instance : Fintype (projectedMachine.Γ projectedMachine.k₁) := by
  change Fintype Binary.Symbol; infer_instance
local instance : Inhabited (projectedMachine.Γ projectedMachine.k₁) := by
  change Inhabited Binary.Symbol; infer_instance

/-- Original bytes, projected scope bits and admission are executed by one
finite-stack machine assembled through proved physical handoffs. -/
def machine : FinTM2 := StackMachineComposition.machine projectedMachine Binary.machine (Equiv.refl _)

/-- The original composed transition table, exposed independently of its finite
type witnesses. No register-space enumeration is needed to execute a step. -/
def projectedProgram : projectedMachine.Λ → TM2.Stmt projectedMachine.Γ projectedMachine.Λ projectedMachine.σ
  | .inl phase => StackMachineRegisters.embedStatement (fun key => some (.inl key)) Sum.inl
      (fun state => state.1) (fun state value => (value, state.2)) (fun _ => rfl)
      (goto fun _ => .inr (.inl false)) (VisitorAdapter.program phase)
  | .inr (.inr phase) => StackMachineRegisters.embedStatement (fun key => some (.inr key))
      (fun label => .inr (.inr label)) (fun state => state.2.1)
      (fun state value => (state.1, value, state.2.2)) (fun _ => rfl) .halt
      (WordHomomorphismMachine.program Binary.scopeSymbol phase)
  | .inr (.inl false) => pop (some (.inl none)) (fun state value => (state.1, state.2.1, value))
      (branch (fun state => state.2.2.isSome)
        (push none (fun state => state.2.2.getD .finish) (goto fun _ => .inr (.inl false)))
        (load (fun state => (state.1, state.2.1, none)) (goto fun _ => .inr (.inl true))))
  | .inr (.inl true) => pop none (fun state value => (state.1, state.2.1, value))
      (branch (fun state => state.2.2.isSome)
        (push (some (.inr .input)) (fun state => state.2.2.getD .finish) (goto fun _ => .inr (.inl true)))
        (load (fun state => (state.1, state.2.1, none)) (goto fun _ => .inr (.inr .read))))

theorem projectedProgram_eq : projectedProgram = projectedMachine.m := by
  funext phase
  cases phase with
  | inl phase =>
      exact (StackMachineComposition.liftFirst_eq_embedStatement VisitorAdapter.machine
        (WordHomomorphismMachine.machine Binary.scopeSymbol) (VisitorAdapter.program phase)).symm
  | inr phase =>
      cases phase with
      | inl bit => cases bit <;> rfl
      | inr phase =>
          exact (StackMachineComposition.liftSecond_eq_embedStatement VisitorAdapter.machine
            (WordHomomorphismMachine.machine Binary.scopeSymbol)
            (WordHomomorphismMachine.program Binary.scopeSymbol phase)).symm

def program : machine.Λ → TM2.Stmt machine.Γ machine.Λ machine.σ
  | .inl phase => StackMachineRegisters.embedStatement (fun key => some (.inl key)) Sum.inl
      (fun state => state.1) (fun state value => (value, state.2)) (fun _ => rfl)
      (goto fun _ => .inr (.inl false)) (projectedProgram phase)
  | .inr (.inr phase) => StackMachineRegisters.embedStatement (fun key => some (.inr key))
      (fun label => .inr (.inr label)) (fun state => state.2.1)
      (fun state value => (state.1, value, state.2.2)) (fun _ => rfl) .halt (Binary.program phase)
  | .inr (.inl false) => pop (some (.inl (some (.inr .result))))
      (fun state value => (state.1, state.2.1, value))
      (branch (fun state => state.2.2.isSome)
        (push none (fun state => state.2.2.getD default) (goto fun _ => .inr (.inl false)))
        (load (fun state => (state.1, state.2.1, none)) (goto fun _ => .inr (.inl true))))
  | .inr (.inl true) => pop none (fun state value => (state.1, state.2.1, value))
      (branch (fun state => state.2.2.isSome)
        (push (some (.inr .input)) (fun state => state.2.2.getD default) (goto fun _ => .inr (.inl true)))
        (load (fun state => (state.1, state.2.1, none)) (goto fun _ => .inr (.inr .next))))

theorem program_eq : program = machine.m := by
  funext phase
  cases phase with
  | inl phase =>
      simp only [program, projectedProgram_eq]
      exact (StackMachineComposition.liftFirst_eq_embedStatement projectedMachine Binary.machine
        (projectedMachine.m phase)).symm
  | inr phase =>
      cases phase with
      | inl bit => cases bit <;> rfl
      | inr phase =>
          exact (StackMachineComposition.liftSecond_eq_embedStatement projectedMachine Binary.machine
            (Binary.program phase)).symm
theorem machine_step : machine.step = TM2.step program := by
  rw [program_eq]
  rfl

def initialConfig (input : List Alphabet) : machine.Cfg where
  l := some (.inl (.inl (.visit .start)))
  var := ((VisitorAdapter.initial, (none, none), none), Binary.ready true, none)
  stk key := match key with
    | some (.inl (some (.inl (some .input)))) => input
    | _ => []

theorem initialConfig_eq (input : List Alphabet) : initialConfig input = initList machine input := by
  simp only [initialConfig, initList, machine, projectedMachine, StackMachineComposition.machine,
    StackMachineComposition.leftKey, VisitorAdapter.machine, WordHomomorphismMachine.machine, Binary.machine]
  congr 1
  funext key
  cases key with
  | none => simp
  | some key =>
      cases key with
      | inr key => cases key <;> simp
      | inl key =>
          cases key with
          | none => simp
          | some key =>
              cases key with
              | inr key => cases key <;> simp
              | inl key =>
                  cases key with
                  | none => simp
                  | some key => cases key <;> simp

/-- Executable key equality is computed on the concrete physical stack keys.
It does not evaluate the packaged machine's finite-state witnesses. -/
def keyEquality : DecidableEq machine.K :=
  (inferInstance : DecidableEq (Option ((Option ((Option PatternSpanExecution.Execution.Stack) ⊕
    WordHomomorphismMachine.Stack)) ⊕ Binary.Stack)))

/-- Execute the proved transition table without enumerating machine states. -/
def step : machine.Cfg → Option machine.Cfg :=
  @TM2.step machine.K machine.Γ machine.Λ machine.σ keyEquality program

theorem step_eq : step = machine.step := by
  unfold step
  rw [show keyEquality = machine.kDecidableEq from Subsingleton.elim _ _]
  rw [program_eq]
  rfl

theorem events_length_bound (pattern : Pattern) :
    (PatternSpanExecution.events pattern).length ≤
      10 * (encodeWith CertificateDataEncoding.patternCodec pattern).length + 1 := by
  have count := PatternSpanExecution.Execution.pattern_events_length_le pattern
  have framing := PatternSpanExecution.Execution.tokenWire_eq
    (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern)
  have original := PatternSpanExecution.Execution.original_pattern_wire pattern
  have fieldsBound : (PatternSpanExecution.Execution.fields
        (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern)).length ≤
      (encodeWith CertificateDataEncoding.patternCodec pattern).length := by
    rw [original, framing, List.length_append]
    omega
  omega

/-- Admission on the original full Pattern codec has an attached quadratic
execution bound. UTF-8 names and all binary numeric fields are included in its
input length, while the output is exactly the original argument judgment. -/
noncomputable def outputs (pattern : Pattern) :
    TM2OutputsInTime machine (encodeWith CertificateDataEncoding.patternCodec pattern)
      (some [some (argumentValidAt 0 pattern)])
      (20000 * ((encodeWith CertificateDataEncoding.patternCodec pattern).length + 1)^2) := by
  let input := encodeWith CertificateDataEncoding.patternCodec pattern
  let events := PatternSpanExecution.events pattern
  let projected := Binary.project events
  have mapped := StackMachineComposition.outputs VisitorAdapter.machine
    (WordHomomorphismMachine.machine Binary.scopeSymbol) (Equiv.refl _) input events projected
    (28 * input.length + 11) (2 * events.length + 2 * projected.length + 2)
    (VisitorAdapter.outputs pattern)
    (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine Binary.scopeSymbol)
        (events.map id) (some projected) _
      rw [List.map_id]
      exact WordHomomorphismMachine.outputs Binary.scopeSymbol events)
  have joined := StackMachineComposition.outputs projectedMachine Binary.machine (Equiv.refl _)
    input projected [some (argumentValidAt 0 pattern)]
    (28 * input.length + 11 + 2 * events.length + 2 + (2 * events.length + 2 * projected.length + 2))
    (10 * (projected.length + 1)^2) mapped
    (by
      change TM2OutputsInTime Binary.machine (projected.map id) (some [some (argumentValidAt 0 pattern)]) _
      rw [List.map_id]
      exact Binary.outputs pattern)
  refine ⟨joined.toEvalsTo, joined.steps_le_m.trans ?_⟩
  have eventsSize : events.length ≤ 10 * input.length + 1 := events_length_bound pattern
  have scopeSize : projected.length ≤ 3 * events.length := Binary.project_length events
  nlinarith

end OriginalAdmission

end Mettapedia.GSLT.LanguageDef.PatternScopeExecution
