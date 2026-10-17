import Mettapedia.Computability.FiniteWordClassifier
import Mettapedia.Computability.FramedWordDecoding
import Mettapedia.OSLF.Syntax.BindingWireBinary

/-!
# Physical framing of binary lists over an authored dictionary

The original binary list spine and every complete element byte are read directly.
Exact codec words are prefix-free, so the fixed dictionary recognizes each head
without a run-time arity or a catalog of subsets. Ordered repeated occurrences
are retained. Unknown words, malformed list markers and trailing bytes drain
all scratch and return refusal. The compact descriptor includes the authored
words; no enumerated-control-table size claim is made.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Computability.AuthoredListFraming
open Turing StateTransition Turing.TM2.Stmt
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open FiniteWordClassifier

/-- The original data parser has enough fuel at structural size. -/
theorem readData_writeData_size (value : Data) (tail : List Alphabet) (fuel : Nat)
    (enough : sizeOf value < fuel) : readData fuel (writeData value tail) = some (value,tail) := by
  induction value generalizing fuel tail with
  | atom value =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [writeData,readData,readNatural_natural]
  | pair first second ihFirst ihSecond =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have firstEnough : sizeOf first < fuel := by simp only [Data.pair.sizeOf_spec] at enough; omega
      have secondEnough : sizeOf second < fuel := by simp only [Data.pair.sizeOf_spec] at enough; omega
      simp [writeData,readData,ihFirst _ _ firstEnough,ihSecond _ _ secondEnough]

/-- Prefix equality of original encoded data leaves no unconsumed suffix. -/
theorem data_prefix_free (first second : Data) (tail : List Alphabet)
    (same : encodeData first ++ tail = encodeData second) : first = second ∧ tail = [] := by
  let fuel := sizeOf first + sizeOf second + 1
  have left := readData_writeData_size first tail fuel (by dsimp [fuel]; omega)
  have right := readData_writeData_size second [] fuel (by dsimp [fuel]; omega)
  rw [writeData_append] at left
  change readData fuel (encodeData first ++ tail) = _ at left
  change readData fuel (encodeData second) = _ at right
  rw [same,right] at left
  exact ⟨(Prod.mk.inj (Option.some.inj left)).1.symm,(Prod.mk.inj (Option.some.inj left)).2.symm⟩

variable {n : Nat}
def words (dictionary : Fin n → Data) : Fin n → List Alphabet := fun index => encodeData (dictionary index)

theorem word_nonempty (value : Data) : encodeData value ≠ [] := by
  cases value <;> simp [encodeData,writeData]

theorem strict_prefix_unfinished (dictionary : Fin n → Data) (value : Data)
    (consumed rest : List Alphabet) (same : consumed ++ rest = encodeData value) (restNonempty : rest ≠ []) :
    finish (words dictionary) (walkState (words dictionary) consumed (initial (words dictionary))) = none := by
  rw [finish_walk]
  cases found : classify (words dictionary) consumed with
  | none => rfl
  | some index =>
    have matched := classify_sound (words dictionary) consumed index found
    rw [matched] at same
    have terminal := (data_prefix_free (dictionary index) value rest same).2
    exact False.elim (restNonempty terminal)

inductive Stack where
  | input | temporary | result
  deriving DecidableEq,Fintype
inductive Phase where
  | spine | word | nilEnd | tail | reverse | rejectInput | rejectTemporary
  deriving DecidableEq,Fintype
abbrev Cells : Stack → Type
  | .input => Alphabet
  | .temporary | .result => Option Alphabet
abbrev Registers (dictionary : Fin n → Data) := Residuals (words dictionary) × Option Alphabet × Option (Option Alphabet)

def registers (dictionary : Fin n → Data) : Registers dictionary := (initial (words dictionary),none,none)

def program (dictionary : Fin n → Data) (phase : Phase) : TM2.Stmt Cells Phase (Registers dictionary) :=
  match phase with
  | .spine => pop .input (fun state cell => (state.1,cell,state.2.2))
      (branch (fun state => state.2.1 == some 4)
        (load (fun _ => registers dictionary) (goto fun _ => .word))
        (branch (fun state => state.2.1 == some 3) (goto fun _ => .nilEnd) (goto fun _ => .rejectInput)))
  | .word => branch (fun state => (finish (words dictionary) state.1).isSome)
      (push .temporary (fun _ => none) (load (fun _ => registers dictionary) (goto fun _ => .spine)))
      (pop .input (fun state cell => (state.1,cell,state.2.2))
        (branch (fun state => state.2.1.isSome)
          (push .temporary (fun state => some (state.2.1.getD 0))
            (load (fun state => (advanceAll (words dictionary) state.1 (state.2.1.getD 0),state.2))
              (goto fun _ => .word))) (goto fun _ => .rejectTemporary)))
  | .nilEnd => pop .input (fun state cell => (state.1,cell,state.2.2))
      (branch (fun state => state.2.1 == some 2) (goto fun _ => .tail) (goto fun _ => .rejectInput))
  | .tail => pop .input (fun state cell => (state.1,cell,state.2.2))
      (branch (fun state => state.2.1.isNone) (goto fun _ => .reverse) (goto fun _ => .rejectInput))
  | .reverse => pop .temporary (fun state cell => (state.1,state.2.1,cell))
      (branch (fun state => state.2.2.isSome)
        (push .result (fun state => state.2.2.getD none) (goto fun _ => .reverse))
        (push .result (fun _ => some 1) (load (fun _ => registers dictionary) halt)))
  | .rejectInput => pop .input (fun state cell => (state.1,cell,state.2.2))
      (branch (fun state => state.2.1.isSome) (goto fun _ => .rejectInput) (goto fun _ => .rejectTemporary))
  | .rejectTemporary => pop .temporary (fun state cell => (state.1,state.2.1,cell))
      (branch (fun state => state.2.2.isSome) (goto fun _ => .rejectTemporary)
        (push .result (fun _ => some 0) (load (fun _ => registers dictionary) halt)))

@[implicit_reducible] def machine (dictionary : Fin n → Data) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := Cells
  Λ := Phase
  main := .spine
  σ := Registers dictionary
  initialState := registers dictionary
  m := program dictionary

def config (dictionary : Fin n → Data) (label : Option Phase) (state : Registers dictionary)
    (input : List Alphabet) (temporary result : List (Option Alphabet)) : (machine dictionary).Cfg where
  l := label
  var := state
  stk key := match key with
    | .input => input | .temporary => temporary | .result => result

local macro "scanner_step" : tactic => `(tactic| (
  simp_all [FinTM2.step,machine,program,config,TM2.step,TM2.stepAux,Function.update]
  all_goals first | rfl | (congr 2; funext key; cases key <;> simp [Function.update])))

theorem walkState_append (dictionary : Fin n → Data) (left right : List Alphabet)
    (state : Residuals (words dictionary)) :
    walkState (words dictionary) (left ++ right) state =
      walkState (words dictionary) right (walkState (words dictionary) left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons symbol rest ih => simpa only [walkState,List.cons_append] using ih (advanceAll (words dictionary) state symbol)

theorem word_symbol (dictionary : Fin n → Data) (cursors : Residuals (words dictionary))
    (cell : Option Alphabet) (head : Alphabet) (rest : List Alphabet)
    (temporary result : List (Option Alphabet))
    (unfinished : finish (words dictionary) cursors = none) :
    (machine dictionary).step (config dictionary (some .word) (cursors,cell,none)
      (head::rest) temporary result) = some (config dictionary (some .word)
        (advanceAll (words dictionary) cursors head,some head,none) rest (some head::temporary) result) := by
  scanner_step

theorem word_close (dictionary : Fin n → Data) (state : Registers dictionary)
    (input : List Alphabet) (temporary result : List (Option Alphabet))
    (complete : (finish (words dictionary) state.1).isSome = true) :
    (machine dictionary).step (config dictionary (some .word) state input temporary result) =
      some (config dictionary (some .spine) (registers dictionary) input (none::temporary) result) := by
  scanner_step

theorem whole_complete (dictionary : Fin n → Data) (value : Data)
    (known : ∃ index, dictionary index = value) :
    (finish (words dictionary) (walkState (words dictionary) (encodeData value)
      (initial (words dictionary)))).isSome = true := by
  rw [finish_walk]
  cases found : classify (words dictionary) (encodeData value) with
  | none =>
    rcases known with ⟨index,same⟩
    have refused := (classify_none_iff (words dictionary) (encodeData value)).mp found index
    exact False.elim (refused (by rw [words,same]))
  | some index => rfl

/-- Each complete head is copied byte for byte before its physical delimiter is added. -/
noncomputable def wordRun (dictionary : Fin n → Data) (value : Data)
    (known : ∃ index, dictionary index = value)
    (rest : List Alphabet) (consumed : List Alphabet) (same : consumed ++ rest = encodeData value)
    (tail : List Alphabet) (temporary result : List (Option Alphabet)) (cell : Option Alphabet) :
    EvalsToInTime (machine dictionary).step
      (config dictionary (some .word)
        (walkState (words dictionary) consumed (initial (words dictionary)),cell,none)
        (rest ++ tail) temporary result)
      (some (config dictionary (some .spine) (registers dictionary) tail
        (none :: (rest.reverse.map some ++ temporary)) result)) (rest.length+1) := by
  induction rest generalizing consumed temporary cell with
  | nil =>
    have equal : consumed = encodeData value := by simpa using same
    have completed := whole_complete dictionary value known
    rw [← equal] at completed
    simpa only [List.nil_append,List.reverse_nil,List.map_nil,List.length_nil,Nat.zero_add] using
      StackMachineComposition.oneStep (word_close dictionary _ tail temporary result completed)
  | cons head rest ih =>
    have unfinished := strict_prefix_unfinished dictionary value consumed (head::rest) same (by simp)
    have first := StackMachineComposition.oneStep
      (word_symbol dictionary _ cell head (rest++tail) temporary result unfinished)
    have aligned : (consumed ++ [head]) ++ rest = encodeData value := by simpa [List.append_assoc] using same
    have next := ih (consumed++[head]) aligned (some head::temporary) (some head)
    simp only [walkState_append,walkState] at next
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first next
    simpa [List.reverse_cons,List.map_append,List.append_assoc] using joined

def dataCodec : Codec Data := ⟨id,some,fun _ => rfl⟩
def listWire (values : List Data) : List Alphabet := encodeWith (Codec.list dataCodec) values

def framed (values : List Data) : List (Option Alphabet) :=
  WordTemplateMachine.Indexed.frame (values.map encodeData)

def scanClock (values : List Data) : Nat :=
  (values.map (fun value => (encodeData value).length+2)).sum+2

theorem spine_cons (dictionary : Fin n → Data) (state : Registers dictionary)
    (input : List Alphabet) (temporary result : List (Option Alphabet)) :
    (machine dictionary).step (config dictionary (some .spine) state (4::input) temporary result) =
      some (config dictionary (some .word) (registers dictionary) input temporary result) := by scanner_step

theorem spine_nil (dictionary : Fin n → Data) (state : Registers dictionary)
    (input : List Alphabet) (temporary result : List (Option Alphabet)) :
    (machine dictionary).step (config dictionary (some .spine) state (3::2::input) temporary result) =
      some (config dictionary (some .nilEnd) (state.1,some 3,state.2.2) (2::input) temporary result) := by scanner_step

theorem nil_end (dictionary : Fin n → Data) (state : Registers dictionary)
    (input : List Alphabet) (temporary result : List (Option Alphabet)) :
    (machine dictionary).step (config dictionary (some .nilEnd) state (2::input) temporary result) =
      some (config dictionary (some .tail) (state.1,some 2,state.2.2) input temporary result) := by scanner_step

/-- Original binary list traversal retains the input's order and duplicate occurrences. -/
noncomputable def spineRun (dictionary : Fin n → Data) (values : List Data)
    (known : ∀ value ∈ values, ∃ index, dictionary index = value)
    (input : List Alphabet) (temporary result : List (Option Alphabet)) :
    EvalsToInTime (machine dictionary).step
      (config dictionary (some .spine) (registers dictionary) (listWire values++input) temporary result)
      (some (config dictionary (some .tail) (initial (words dictionary),some 2,none) input
        ((framed values).reverse ++ temporary) result)) (scanClock values) := by
  induction values generalizing temporary with
  | nil =>
    have first := StackMachineComposition.oneStep (spine_nil dictionary (registers dictionary) input temporary result)
    have next := StackMachineComposition.oneStep (nil_end dictionary (initial (words dictionary),some 3,none) input temporary result)
    simpa [listWire,encodeWith,Codec.list,Codec.putList,encodeData,writeData,natural,
      framed,WordTemplateMachine.Indexed.frame,scanClock,registers] using
      EvalsToInTime.trans _ _ _ _ _ _ first next
  | cons value values ih =>
    have first := StackMachineComposition.oneStep
      (spine_cons dictionary (registers dictionary) (encodeData value ++ (listWire values++input)) temporary result)
    have copied := wordRun dictionary value (known value (by simp)) (encodeData value) [] (by simp)
      (listWire values++input) temporary result none
    have next := ih (fun value member => known value (List.mem_cons_of_mem _ member))
      (none::((encodeData value).reverse.map some++temporary))
    have joined := EvalsToInTime.trans _ _ _ _ _ _ (EvalsToInTime.trans _ _ _ _ _ _ first copied) next
    convert joined using 1 <;> simp [listWire,encodeWith,Codec.list,Codec.putList,encodeData_pair,dataCodec,
      framed,WordTemplateMachine.Indexed.frame,List.reverse_append,List.map_reverse,
      List.append_assoc,scanClock,registers]
    omega

theorem tail_empty (dictionary : Fin n → Data) (state : Registers dictionary)
    (temporary result : List (Option Alphabet)) :
    (machine dictionary).step (config dictionary (some .tail) state [] temporary result) =
      some (config dictionary (some .reverse) (state.1,none,state.2.2) [] temporary result) := by scanner_step

theorem reverse_cons (dictionary : Fin n → Data) (state : Registers dictionary)
    (head : Option Alphabet) (rest result : List (Option Alphabet)) :
    (machine dictionary).step (config dictionary (some .reverse) state [] (head::rest) result) =
      some (config dictionary (some .reverse) (state.1,state.2.1,some head) [] rest (head::result)) := by scanner_step

theorem reverse_nil (dictionary : Fin n → Data) (state : Registers dictionary)
    (result : List (Option Alphabet)) :
    (machine dictionary).step (config dictionary (some .reverse) state [] [] result) =
      some (config dictionary none (registers dictionary) [] [] (some 1::result)) := by scanner_step

noncomputable def reverseRun (dictionary : Fin n → Data) (temporary result : List (Option Alphabet))
    (state : Registers dictionary) :
    EvalsToInTime (machine dictionary).step (config dictionary (some .reverse) state [] temporary result)
      (some (config dictionary none (registers dictionary) [] [] (some 1::temporary.reverse++result)))
      (temporary.length+1) := by
  induction temporary generalizing state result with
  | nil => simpa using StackMachineComposition.oneStep (reverse_nil dictionary state result)
  | cons head rest ih =>
    have first := StackMachineComposition.oneStep (reverse_cons dictionary state head rest result)
    have next := ih (head::result) (state.1,state.2.1,some head)
    simpa [List.reverse_cons,List.append_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first next

theorem init_eq (dictionary : Fin n → Data) (input : List Alphabet) :
    initList (machine dictionary) input = config dictionary (some .spine) (registers dictionary) input [] [] := by
  simp only [initList,machine,config]
  congr 1; funext key; cases key <;> simp

theorem halt_eq (dictionary : Fin n → Data) (out : List (Option Alphabet)) :
    haltList (machine dictionary) out = config dictionary none (registers dictionary) [] [] out := by
  simp only [haltList,machine,config]
  congr 1; funext key; cases key <;> simp

/-- Successful framing executes all original bytes and clears every finite register and scratch stack. -/
noncomputable def outputs (dictionary : Fin n → Data) (values : List Data)
    (known : ∀ value ∈ values, ∃ index, dictionary index = value) :
    TM2OutputsInTime (machine dictionary) (listWire values) (some (some 1::framed values))
      (scanClock values+(framed values).length+2) := by
  have source := spineRun dictionary values known [] [] []
  simp only [List.append_nil] at source
  have tail := StackMachineComposition.oneStep (tail_empty dictionary (initial (words dictionary),some 2,none) (framed values).reverse [])
  have reverse := reverseRun dictionary (framed values).reverse [] (initial (words dictionary),none,none)
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at reverse
  have joined := EvalsToInTime.trans _ _ _ _ _ _ (EvalsToInTime.trans _ _ _ _ _ _ source tail) reverse
  change EvalsToInTime _ (initList _ _) (some (haltList _ _)) _
  rw [init_eq,halt_eq]
  exact ⟨joined.toEvalsTo,joined.steps_le_m.trans (by omega)⟩


/-- Framing a codec list uses its unchanged original binary writer. -/
theorem listWire_codec {Value : Type} (codec : Codec Value) (values : List Value) :
    listWire (values.map codec.put) = encodeWith (Codec.list codec) values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [List.map_cons,listWire,encodeWith,Codec.list,Codec.putList,dataCodec] at ih ⊢
    rw [encodeData_pair,encodeData_pair]
    exact congrArg (fun rest => 4::encodeData (codec.put value)++rest) ih

theorem clock_bound (values : List Data) :
    scanClock values+(framed values).length+2 ≤ 3*(listWire values).length+2 := by
  induction values with
  | nil => change 4 ≤ 8; omega
  | cons value values ih =>
    have source : (listWire (value::values)).length = 1+(encodeData value).length+(listWire values).length := by
      simp only [listWire,encodeWith,Codec.list,Codec.putList,dataCodec,encodeData_pair,
        List.length_cons,List.length_append,id_eq]
      omega
    have frames : (framed (value::values)).length = (encodeData value).length+1+(framed values).length := by
      simp [framed,WordTemplateMachine.Indexed.frame]
      omega
    rw [source,frames]
    simp only [scanClock,List.map_cons,List.sum_cons] at ih ⊢
    omega

/-- A linear clock charges every source byte, list marker and restored frame. -/
noncomputable def codecOutputs {Value : Type} (codec : Codec Value) (dictionary : Fin n → Data)
    (values : List Value) (known : ∀ value ∈ values, ∃ index, dictionary index = codec.put value) :
    TM2OutputsInTime (machine dictionary) (encodeWith (Codec.list codec) values)
      (some (some 1::WordTemplateMachine.Indexed.frame (values.map (encodeWith codec))))
      (3*(encodeWith (Codec.list codec) values).length+2) := by
  have ran := outputs dictionary (values.map codec.put) (by
    intro value member
    rcases List.mem_map.mp member with ⟨original,member,same⟩
    exact same ▸ known original member)
  have frameExact : framed (values.map codec.put) =
      WordTemplateMachine.Indexed.frame (values.map (encodeWith codec)) := by
    simp only [framed,List.map_map]
    rfl
  have bound := clock_bound (values.map codec.put)
  rw [listWire_codec,frameExact] at ran bound
  exact WordEqualityMachine.within ran bound

/-- Direct instruction execution uses the original mathematical transition function. -/
theorem machine_step (dictionary : Fin n → Data) :
    (machine dictionary).step = TM2.step (program dictionary) := rfl

end Mettapedia.Computability.AuthoredListFraming
