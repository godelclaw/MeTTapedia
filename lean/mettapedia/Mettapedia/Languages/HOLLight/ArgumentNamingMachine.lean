import Mettapedia.Languages.HOLLight.ArgumentRenderingMachine
import Mettapedia.GSLT.LanguageDef.CertificateDataTraversal

/-!
# Executed naming of original HOL data arguments

A finite prefix machine traverses the original raw term bytes. Application
markers are changed to their original named-source markers; constant symbol
provenance and type annotations are copied by a separate generic data walk.
Their embedded source syntax is retained exactly, including binders.

The complete execution costs at most three times the raw byte length plus
four. It produces the original checkedSource representative for every rendered
source argument, with empty work stacks. Its input is already the raw HOL
operand; source admission/rendering and the surrounding driver have separate
clocks. Arbitrary HOL lambda spines are outside this operand fragment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.ArgumentNamingMachine
open Turing StateTransition Polynomial Turing.TM2.Stmt
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability
open Mettapedia.GSLT.LanguageDef

/-- Only the term spine is restricted. Symbol provenance and type annotations
remain arbitrary original values, with all their embedded syntax retained. -/
inductive Applicative : DBTerm → SourceTerm → Prop
  | const (symbol : Const) (annotation : Ty) : Applicative (.const symbol annotation) (.const symbol annotation)
  | app {function argument : DBTerm} {first second : SourceTerm} :
      Applicative function first → Applicative argument second →
      Applicative (.app function argument) (.app first second)

theorem named_exact {term : DBTerm} {source : SourceTerm}
    (shape : Applicative term source) (binders : List SourceVar) :
    PrimitiveTransport.named? term binders = some source := by
  induction shape with
  | const => rfl
  | app left right ihLeft ihRight => simp [PrimitiveTransport.named?, ihLeft, ihRight]

inductive Stack where
  | input | pending | output | result
  deriving DecidableEq, Fintype
inductive Phase where
  | start | next | termPair | termAtom | termFirst | termSecond | termEnd | appPair
  | dataHeader | dataNumber | checkTail | reverse | rejectInput | rejectPending | rejectOutput
  deriving DecidableEq, Fintype

abbrev Register := Option Alphabet

def copyRead (afterPhase : Phase) : TM2.Stmt (fun _ : Stack => Alphabet) Phase Register :=
  push .output (fun state => state.getD 2) (goto fun _ => afterPhase)
def expect (symbol : Alphabet) (afterPhase : Phase) : TM2.Stmt (fun _ : Stack => Alphabet) Phase Register :=
  pop .input (fun _ value => value) (branch (fun state => state == some symbol)
    (copyRead afterPhase) (goto fun _ => .rejectInput))

def program : Phase → TM2.Stmt (fun _ : Stack => Alphabet) Phase Register
  | .start => push .pending (fun _ => 1) (goto fun _ => .next)
  | .next => pop .pending (fun _ value => value)
      (branch Option.isNone (goto fun _ => .checkTail)
        (branch (fun state => state == some 1) (goto fun _ => .termPair) (goto fun _ => .dataHeader)))
  | .termPair => expect 4 .termAtom
  | .termAtom => expect 3 .termFirst
  | .termFirst => pop .input (fun _ value => value)
      (branch (fun state => state == some 2)
        (push .output (fun _ => 2) (push .pending (fun _ => 0) (goto fun _ => .next)))
        (branch (fun state => state == some 1)
          (push .output (fun _ => 0) (goto fun _ => .termSecond)) (goto fun _ => .rejectInput)))
  | .termSecond => expect 1 .termEnd
  | .termEnd => expect 2 .appPair
  | .appPair => pop .input (fun _ value => value)
      (branch (fun state => state == some 4)
        (push .output (fun _ => 4) (push .pending (fun _ => 1)
          (push .pending (fun _ => 1) (goto fun _ => .next)))) (goto fun _ => .rejectInput))
  | .dataHeader => pop .input (fun _ value => value)
      (branch (fun state => state == some 4)
        (push .output (fun _ => 4) (push .pending (fun _ => 0)
          (push .pending (fun _ => 0) (goto fun _ => .next))))
        (branch (fun state => state == some 3) (copyRead .dataNumber) (goto fun _ => .rejectInput)))
  | .dataNumber => pop .input (fun _ value => value)
      (branch (fun state => state == some 2) (copyRead .next)
        (branch SharedReferenceExecution.isBit (copyRead .dataNumber) (goto fun _ => .rejectInput)))
  | .checkTail => pop .input (fun _ value => value)
      (branch Option.isNone (goto fun _ => .reverse) (goto fun _ => .rejectInput))
  | .reverse => pop .output (fun _ value => value)
      (branch Option.isSome (push .result (fun state => state.getD 2) (goto fun _ => .reverse))
        (load (fun _ => none) halt))
  | .rejectInput => pop .input (fun _ value => value)
      (branch Option.isSome (goto fun _ => .rejectInput) (goto fun _ => .rejectPending))
  | .rejectPending => pop .pending (fun _ value => value)
      (branch Option.isSome (goto fun _ => .rejectPending) (goto fun _ => .rejectOutput))
  | .rejectOutput => pop .output (fun _ value => value)
      (branch Option.isSome (goto fun _ => .rejectOutput) (load (fun _ => none) halt))

def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ _ := Alphabet
  Λ := Phase
  main := .start
  σ := Register
  initialState := none
  m := program

def config (phase : Option Phase) (state : Register)
    (input pending output result : List Alphabet) : machine.Cfg where
  l := phase
  var := state
  stk key := match (show Stack from key) with
    | .input => input | .pending => pending | .output => output | .result => result

local macro "check_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, program, expect, copyRead, config, TM2.step, TM2.stepAux, Function.update] <;>
  congr 2 <;> funext key <;> cases key <;> simp [Function.update]))

theorem next_term (state : Register) (input pending output result : List Alphabet) :
    machine.step (config (some .next) state input (1 :: pending) output result) =
    some (config (some .termPair) (some 1) input pending output result) := by check_step

theorem next_data (state : Register) (input pending output result : List Alphabet) :
    machine.step (config (some .next) state input (0 :: pending) output result) =
    some (config (some .dataHeader) (some 0) input pending output result) := by check_step

theorem pair_read (state : Register) (input pending output result : List Alphabet) :
    machine.step (config (some .termPair) state (4 :: input) pending output result) =
    some (config (some .termAtom) (some 4) input pending (4 :: output) result) := by check_step

theorem atom_read (state : Register) (input pending output result : List Alphabet) :
    machine.step (config (some .termAtom) state (3 :: input) pending output result) =
    some (config (some .termFirst) (some 3) input pending (3 :: output) result) := by check_step

theorem const_read (state : Register) (input pending output result : List Alphabet) :
    machine.step (config (some .termFirst) state (2 :: input) pending output result) =
    some (config (some .next) (some 2) input (0 :: pending) (2 :: output) result) := by check_step

theorem app_first (state : Register) (input pending output result : List Alphabet) :
    machine.step (config (some .termFirst) state (1 :: input) pending output result) =
    some (config (some .termSecond) (some 1) input pending (0 :: output) result) := by check_step

theorem app_second (state : Register) (input pending output result : List Alphabet) :
    machine.step (config (some .termSecond) state (1 :: input) pending output result) =
    some (config (some .termEnd) (some 1) input pending (1 :: output) result) := by check_step

theorem app_end (state : Register) (input pending output result : List Alphabet) :
    machine.step (config (some .termEnd) state (2 :: input) pending output result) =
    some (config (some .appPair) (some 2) input pending (2 :: output) result) := by check_step

theorem app_pair (state : Register) (input pending output result : List Alphabet) :
    machine.step (config (some .appPair) state (4 :: input) pending output result) =
    some (config (some .next) (some 4) input (1 :: 1 :: pending) (4 :: output) result) := by check_step

theorem data_pair (state : Register) (input pending output result : List Alphabet) :
    machine.step (config (some .dataHeader) state (4 :: input) pending output result) =
    some (config (some .next) (some 4) input (0 :: 0 :: pending) (4 :: output) result) := by check_step

theorem data_atom (state : Register) (input pending output result : List Alphabet) :
    machine.step (config (some .dataHeader) state (3 :: input) pending output result) =
    some (config (some .dataNumber) (some 3) input pending (3 :: output) result) := by check_step

theorem data_bit (state : Register) (value : Bool) (input pending output result : List Alphabet) :
    machine.step (config (some .dataNumber) state (SharedReferenceExecution.bit value :: input) pending output result) =
    some (config (some .dataNumber) (some (SharedReferenceExecution.bit value)) input pending
      (SharedReferenceExecution.bit value :: output) result) := by
  cases value <;> simp [SharedReferenceExecution.bit, SharedReferenceExecution.isBit, FinTM2.step,
    machine, program, copyRead, config, TM2.step, TM2.stepAux, Function.update] <;>
    funext key <;> cases key <;> simp [Function.update]

theorem data_end (state : Register) (input pending output result : List Alphabet) :
    machine.step (config (some .dataNumber) state (2 :: input) pending output result) =
    some (config (some .next) (some 2) input pending (2 :: output) result) := by check_step

def number_run (bits : List Bool) (input pending output result : List Alphabet) (state : Register) :
    EvalsToInTime machine.step
      (config (some .dataNumber) state (SharedReferenceExecution.field bits ++ 2 :: input) pending output result)
      (some (config (some .next) (some 2) input pending
        (2 :: (SharedReferenceExecution.field bits).reverse ++ output) result)) (bits.length + 1) := by
  induction bits generalizing state output with
  | nil => simpa [SharedReferenceExecution.field] using StackMachineComposition.oneStep (data_end state input pending output result)
  | cons bit rest ih =>
      have first := StackMachineComposition.oneStep (data_bit state bit
        (SharedReferenceExecution.field rest ++ 2 :: input) pending output result)
      have later := ih (SharedReferenceExecution.bit bit :: output) (some (SharedReferenceExecution.bit bit))
      simpa [SharedReferenceExecution.field, List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first later

def dataCost : Data → Nat
  | .atom value => (Nat.digits 2 value).length + 3
  | .pair first second => 2 + dataCost first + dataCost second

noncomputable def dataRun (value : Data) (input pending output result : List Alphabet) (state : Register) :
    EvalsToInTime machine.step
      (config (some .next) state (encodeData value ++ input) (0 :: pending) output result)
      (some (config (some .next) (some 2) input pending ((encodeData value).reverse ++ output) result))
      (dataCost value) := by
  induction value generalizing input pending output state with
  | atom value =>
      have enter := StackMachineComposition.oneStep (next_data state (3 :: natural value ++ input) pending output result)
      have header := StackMachineComposition.oneStep (data_atom (some 0) (natural value ++ input) pending output result)
      have number := number_run (SharedReferenceExecution.naturalKey value) input pending (3 :: output) result (some 3)
      have inputSame : SharedReferenceExecution.field (SharedReferenceExecution.naturalKey value) ++ 2 :: input =
          natural value ++ input := by
        rw [← SharedReferenceExecution.field_naturalKey]
        simp [List.append_assoc]
      have outputSame : 2 :: (SharedReferenceExecution.field (SharedReferenceExecution.naturalKey value)).reverse ++ 3 :: output =
          (3 :: natural value).reverse ++ output := by
        rw [← SharedReferenceExecution.field_naturalKey]
        simp [List.reverse_append, List.append_assoc]
      rw [inputSame, outputSame] at number
      have first := EvalsToInTime.trans _ 1 1 _ _ _ enter header
      have all := EvalsToInTime.trans _ 2 _ _ _ _ first number
      convert all using 1
      all_goals simp only [encodeData, writeData, dataCost, SharedReferenceExecution.naturalKey, List.length_map, List.reverse_cons, List.append_assoc, List.singleton_append, List.append_nil]
  | pair first second ihFirst ihSecond =>
      have enter := StackMachineComposition.oneStep (next_data state
        (4 :: encodeData first ++ encodeData second ++ input) pending output result)
      have header := StackMachineComposition.oneStep (data_pair (some 0)
        (encodeData first ++ encodeData second ++ input) pending output result)
      have left := ihFirst (encodeData second ++ input) (0 :: pending) (4 :: output) (some 4)
      have right := ihSecond input pending ((encodeData first).reverse ++ 4 :: output) (some 2)
      have a := EvalsToInTime.trans _ 1 1 _ _ _ enter header
      have b := EvalsToInTime.trans _ 2 _ _ _ _ a (by simpa [List.append_assoc] using left)
      have all := EvalsToInTime.trans _ _ _ _ _ _ b right
      convert all using 1
      all_goals simp [encodeData_pair, dataCost, List.reverse_append, List.reverse_cons, List.append_assoc]
      omega

def termCost : DBTerm → Nat
  | .const symbol annotation => 4 + dataCost (.pair (putConst symbol) (putTy annotation))
  | .app function argument => 7 + termCost function + termCost argument
  | _ => 0

theorem termRuns {term : DBTerm} {source : SourceTerm} (shape : Applicative term source)
    (input pending output result : List Alphabet) (state : Register) :
    Nonempty (EvalsToInTime machine.step
      (config (some .next) state (encodeWith dbTermCodec term ++ input) (1 :: pending) output result)
      (some (config (some .next) (some 2) input pending
        ((encodeWith sourceTermCodec source).reverse ++ output) result)) (termCost term)) := by
  induction shape generalizing input pending output state with
  | const symbol annotation =>
      let payload := encodeData (.pair (putConst symbol) (putTy annotation))
      have a := StackMachineComposition.oneStep (next_term state (4 :: 3 :: 2 :: payload ++ input) pending output result)
      have b := StackMachineComposition.oneStep (pair_read (some 1) (3 :: 2 :: payload ++ input) pending output result)
      have c := StackMachineComposition.oneStep (atom_read (some 4) (2 :: payload ++ input) pending (4 :: output) result)
      have d := StackMachineComposition.oneStep (const_read (some 3) (payload ++ input) pending (3 :: 4 :: output) result)
      have e := dataRun (.pair (putConst symbol) (putTy annotation)) input pending (2 :: 3 :: 4 :: output) result (some 2)
      have ab := EvalsToInTime.trans _ 1 1 _ _ _ a b
      have abc := EvalsToInTime.trans _ 2 1 _ _ _ ab c
      have abcd := EvalsToInTime.trans _ 3 1 _ _ _ abc d
      have all := EvalsToInTime.trans _ 4 _ _ _ _ abcd e
      have zero : natural 0 = [2] := rfl
      refine ⟨?_⟩
      convert all using 1
      all_goals simp only [encodeWith, dbTermCodec, sourceTermCodec, putTerm, putSourceTerm, encodeData_pair,
        encodeData_atom, zero, termCost, payload, List.reverse_append, List.reverse_cons,
        List.cons_append, List.nil_append, List.append_assoc]
      omega
  | @app function argument first second left right ihLeft ihRight =>
      let firstWord := encodeWith dbTermCodec function
      let secondWord := encodeWith dbTermCodec argument
      have a := StackMachineComposition.oneStep (next_term state (4 :: 3 :: 1 :: 1 :: 2 :: 4 :: firstWord ++ secondWord ++ input) pending output result)
      have b := StackMachineComposition.oneStep (pair_read (some 1) (3 :: 1 :: 1 :: 2 :: 4 :: firstWord ++ secondWord ++ input) pending output result)
      have c := StackMachineComposition.oneStep (atom_read (some 4) (1 :: 1 :: 2 :: 4 :: firstWord ++ secondWord ++ input) pending (4 :: output) result)
      have d := StackMachineComposition.oneStep (app_first (some 3) (1 :: 2 :: 4 :: firstWord ++ secondWord ++ input) pending (3 :: 4 :: output) result)
      have e := StackMachineComposition.oneStep (app_second (some 1) (2 :: 4 :: firstWord ++ secondWord ++ input) pending (0 :: 3 :: 4 :: output) result)
      have f := StackMachineComposition.oneStep (app_end (some 1) (4 :: firstWord ++ secondWord ++ input) pending (1 :: 0 :: 3 :: 4 :: output) result)
      have g := StackMachineComposition.oneStep (app_pair (some 2) (firstWord ++ secondWord ++ input) pending (2 :: 1 :: 0 :: 3 :: 4 :: output) result)
      have ab := EvalsToInTime.trans _ 1 1 _ _ _ a b
      have abc := EvalsToInTime.trans _ 2 1 _ _ _ ab c
      have abcd := EvalsToInTime.trans _ 3 1 _ _ _ abc d
      have abcde := EvalsToInTime.trans _ 4 1 _ _ _ abcd e
      have abcdef := EvalsToInTime.trans _ 5 1 _ _ _ abcde f
      have front := EvalsToInTime.trans _ 6 1 _ _ _ abcdef g
      have l := Classical.choice (ihLeft (secondWord ++ input) (1 :: pending) (4 :: 2 :: 1 :: 0 :: 3 :: 4 :: output) (some 4))
      have r := Classical.choice (ihRight input pending ((encodeWith sourceTermCodec first).reverse ++ 4 :: 2 :: 1 :: 0 :: 3 :: 4 :: output) (some 2))
      have fl := EvalsToInTime.trans _ 7 _ _ _ _ front (by simpa [firstWord, secondWord, List.append_assoc] using l)
      have all := EvalsToInTime.trans _ _ _ _ _ _ fl r
      have three : natural 3 = [1, 1, 2] := rfl
      have two : natural 2 = [0, 1, 2] := rfl
      refine ⟨?_⟩
      convert all using 1
      all_goals simp only [encodeWith, dbTermCodec, sourceTermCodec, putTerm, putSourceTerm, encodeData_pair,
        encodeData_atom, three, two, termCost, firstWord, secondWord,
        List.cons_append, List.reverse_cons, List.reverse_append,
        List.nil_append, List.append_assoc]
      omega

noncomputable def termRun {term : DBTerm} {source : SourceTerm} (shape : Applicative term source)
    (input pending output result : List Alphabet) (state : Register) :=
  Classical.choice (termRuns shape input pending output result state)

theorem dataCost_le (value : Data) : dataCost value ≤ 2 * dataWeight value := by
  induction value with
  | atom value => simp only [dataCost, dataWeight]; omega
  | pair first second ihFirst ihSecond => simp only [dataCost, dataWeight]; omega

theorem encoded_length (value : Data) : (encodeData value).length = dataWeight value := by
  simpa [encodeData] using writeData_length value []

theorem termCost_le {term : DBTerm} {source : SourceTerm} (shape : Applicative term source) :
    termCost term ≤ 2 * (encodeWith dbTermCodec term).length := by
  induction shape with
  | const symbol annotation =>
      have bound := dataCost_le (.pair (putConst symbol) (putTy annotation))
      have zero : natural 0 = [2] := rfl
      simp only [termCost, encodeWith, dbTermCodec, putTerm, encodeData_pair, encodeData_atom,
        zero, List.length_cons, List.length_nil, List.length_append, encoded_length, dataWeight] at *
      omega
  | app left right ihLeft ihRight =>
      have three : natural 3 = [1, 1, 2] := rfl
      simp only [termCost, encodeWith, dbTermCodec, putTerm, encodeData_pair, encodeData_atom,
        three, List.length_cons, List.length_nil, List.length_append] at *
      omega

theorem wire_length {term : DBTerm} {source : SourceTerm} (shape : Applicative term source) :
    (encodeWith sourceTermCodec source).length = (encodeWith dbTermCodec term).length := by
  induction shape with
  | const => rfl
  | app left right ihLeft ihRight =>
      have three : natural 3 = [1, 1, 2] := rfl
      have two : natural 2 = [0, 1, 2] := rfl
      simp only [encodeWith, dbTermCodec, sourceTermCodec, putTerm, putSourceTerm, encodeData_pair,
        encodeData_atom, three, two, List.length_cons, List.length_nil, List.length_append] at *
      omega

theorem start (input : List Alphabet) :
    machine.step (config (some .start) none input [] [] []) =
    some (config (some .next) none input [1] [] []) := by check_step

theorem next_empty (state : Register) (input output : List Alphabet) :
    machine.step (config (some .next) state input [] output []) =
    some (config (some .checkTail) none input [] output []) := by check_step

theorem tail_empty (output : List Alphabet) :
    machine.step (config (some .checkTail) none [] [] output []) =
    some (config (some .reverse) none [] [] output []) := by check_step

theorem reverse_cons (state : Register) (symbol : Alphabet) (output result : List Alphabet) :
    machine.step (config (some .reverse) state [] [] (symbol :: output) result) =
    some (config (some .reverse) (some symbol) [] [] output (symbol :: result)) := by check_step

theorem reverse_nil (state : Register) (result : List Alphabet) :
    machine.step (config (some .reverse) state [] [] [] result) =
    some (config none none [] [] [] result) := by check_step

def reverseRun (output result : List Alphabet) (state : Register) :
    EvalsToInTime machine.step (config (some .reverse) state [] [] output result)
      (some (config none none [] [] [] (output.reverse ++ result))) (output.length + 1) := by
  induction output generalizing state result with
  | nil => simpa using StackMachineComposition.oneStep (reverse_nil state result)
  | cons symbol rest ih =>
      have first := StackMachineComposition.oneStep (reverse_cons state symbol rest result)
      have later := ih (symbol :: result) (some symbol)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ 1 _ _ _ _ first later

theorem init_eq (input : List Alphabet) : initList machine input = config (some .start) none input [] [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key <;> simp

theorem halt_eq (output : List Alphabet) : haltList machine output = config none none [] [] [] output := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key <;> simp

noncomputable def outputs {term : DBTerm} {source : SourceTerm} (shape : Applicative term source) :
    TM2OutputsInTime machine (encodeWith dbTermCodec term) (some (encodeWith sourceTermCodec source))
      (3 * ((encodeWith dbTermCodec term).length + 1) + 1) := by
  have begin := StackMachineComposition.oneStep (start (encodeWith dbTermCodec term))
  have walked := termRun shape [] [] [] [] none
  have final := StackMachineComposition.oneStep (next_empty (some 2) [] (encodeWith sourceTermCodec source).reverse)
  have endCheck := StackMachineComposition.oneStep (tail_empty (encodeWith sourceTermCodec source).reverse)
  have reverse := reverseRun (encodeWith sourceTermCodec source).reverse [] none
  have first := EvalsToInTime.trans _ 1 _ _ _ _ begin (by simpa using walked)
  have second := EvalsToInTime.trans _ _ 1 _ _ _ first final
  have third := EvalsToInTime.trans _ _ 1 _ _ _ second endCheck
  have all := EvalsToInTime.trans _ _ _ _ _ _ third reverse
  have exactRun : TM2OutputsInTime machine (encodeWith dbTermCodec term) (some (encodeWith sourceTermCodec source))
      (termCost term + (encodeWith sourceTermCodec source).length + 4) := by
    change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
    rw [init_eq, halt_eq]
    convert all using 1
    all_goals simp only [List.reverse_reverse, List.append_nil, List.length_reverse]
    omega
  apply WordEqualityMachine.within exactRun
  have clock := termCost_le shape
  rw [wire_length shape]
  omega

open ArgumentRenderingMachine
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.HOLLight.InferenceStorageBounds

/-- The original left-associated constructor spine preserves argument order. -/
theorem applyTerms_shape {head : DBTerm} {source : SourceTerm} (headShape : Applicative head source)
    (arguments : List DBTerm) (children : ∀ child ∈ arguments, ∃ namedChild, Applicative child namedChild) :
    ∃ result, Applicative (applyTerms head arguments) result := by
  induction arguments generalizing head source with
  | nil => exact ⟨source, headShape⟩
  | cons child rest ih =>
      obtain ⟨namedChild, childShape⟩ := children child (by simp)
      exact ih (.app headShape childShape) (fun item member => children item (by simp [member]))

/-- Every source-data argument has an applicative target spine. Opaque source
binders remain inside constant payloads and are never renamed by this pass. -/
theorem dataTerm_shape (pattern : Pattern) : ∃ source, Applicative (dataTerm pattern) source := by
  cases pattern with
  | apply name arguments =>
      rw [dataTerm]
      apply applyTerms_shape (.const _ _)
      intro argument member
      obtain ⟨child, sourceMember, rfl⟩ := List.mem_map.mp member
      exact dataTerm_shape child
  | _ => simp only [dataTerm, literalTerm]; exact ⟨_, .const _ _⟩
termination_by sizeOf pattern
decreasing_by
  have smaller := List.sizeOf_lt_of_mem sourceMember
  simp only [Pattern.apply.sizeOf_spec]
  omega

theorem rendered_shape (pattern : Pattern) :
    Applicative (renderedArgument pattern).term (PrimitiveTransport.checkedSource (renderedArgument pattern)).source := by
  rw [renderedArgument_term, Named.checkedSource_argument]
  obtain ⟨source, shape⟩ := dataTerm_shape pattern
  have original := Named.argument_exact pattern []
  rw [named_exact shape []] at original
  cases Option.some.inj original
  exact shape

noncomputable def argumentOutputs (pattern : Pattern) :
    TM2OutputsInTime machine (encodeWith dbTermCodec (renderedArgument pattern).term)
      (some (encodeWith sourceTermCodec (PrimitiveTransport.checkedSource (renderedArgument pattern)).source))
      (3 * ((encodeWith dbTermCodec (renderedArgument pattern).term).length + 1) + 1) :=
  outputs (rendered_shape pattern)

/-- The physical input here is the original rendered raw operand. Admission
and source-pattern rendering are earlier separately charged subroutines. -/
noncomputable def realization : TM2ComputableInPolyTime
    (fun pattern : Pattern => encodeWith dbTermCodec (renderedArgument pattern).term)
    (encodeWith sourceTermCodec)
    (fun pattern => (PrimitiveTransport.checkedSource (renderedArgument pattern)).source) where
  tm := machine
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := C 3 * (X + C 1) + C 1
  outputsFun pattern := by
    change TM2OutputsInTime machine ((encodeWith dbTermCodec (renderedArgument pattern).term).map id)
      (some ((encodeWith sourceTermCodec (PrimitiveTransport.checkedSource (renderedArgument pattern)).source).map id)) _
    simp only [List.map_id_fun]
    simpa only [eval_add, eval_mul, eval_C, eval_X, id_eq] using argumentOutputs pattern

theorem output_decodes (pattern : Pattern) :
    decodeWith sourceTermCodec (encodeWith sourceTermCodec (PrimitiveTransport.checkedSource (renderedArgument pattern)).source) =
      some (PrimitiveTransport.checkedSource (renderedArgument pattern)).source :=
  decodeWith_encodeWith sourceTermCodec _

theorem arbitrary_run_decodes {pattern : Pattern} {word : List Alphabet}
    (run : TM2Outputs machine (encodeWith dbTermCodec (renderedArgument pattern).term) (some word)) :
    decodeWith sourceTermCodec word = some (PrimitiveTransport.checkedSource (renderedArgument pattern)).source := by
  have same := StackMachineComposition.outputs_unique run (argumentOutputs pattern).toTM2Outputs
  rw [same]
  exact output_decodes pattern

namespace Controls

theorem higher_order_spine_excluded (domain : Ty) (body : DBTerm) (source : SourceTerm) :
    ¬ Applicative (.abs domain body) source := by intro shape; cases shape

theorem bound_spine_excluded (index : Nat) (source : SourceTerm) :
    ¬ Applicative (.bound index) source := by intro shape; cases shape

theorem source_binder_is_data :
    Applicative (renderedArgument (.lambda none (.bvar 0))).term
      (PrimitiveTransport.checkedSource (renderedArgument (.lambda none (.bvar 0)))).source := rendered_shape _

theorem original_defined_payload (name : Name) (definition : SourceTerm) (annotation : Ty) :
    Applicative (.const ⟨name, .defined definition⟩ annotation)
      (.const ⟨name, .defined definition⟩ annotation) := .const _ _

end Controls

end Mettapedia.Languages.HOLLight.ArgumentNamingMachine
