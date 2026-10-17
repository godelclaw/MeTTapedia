import Mettapedia.Computability.BinaryStackArithmetic
import Mettapedia.Computability.WordEqualityMachine

/-!
# Addition of binary words by finite stack control

Inputs contain two least-significant-bit-first words separated by a delimiter
outside the bit alphabet. Carry propagation, high-zero removal, restoration
and refused-input cleanup operate on physical stacks. Successful outputs use
only bit symbols; a delimiter in the output is an explicit refusal.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.BinaryWordAddition
open Turing StateTransition Polynomial Turing.TM2.Stmt
open BinaryStackArithmetic (naturalBits value bitValue)
open StackMachineComposition (oneStep)

def sumBit (left right carry : Bool) : Bool := (left != right) != carry

def nextCarry (left right carry : Bool) : Bool :=
  (left && right) || (carry && (left || right))

theorem digit_sum (left right carry : Bool) :
    bitValue left + bitValue right + bitValue carry =
      bitValue (sumBit left right carry) + 2 * bitValue (nextCarry left right carry) := by
  cases left <;> cases right <;> cases carry <;> decide

def addWords (carry : Bool) (left right : List Bool) : List Bool :=
  match left, right with
  | [], [] => if carry then [true] else []
  | left :: lefts, [] => sumBit left false carry :: addWords (nextCarry left false carry) lefts []
  | [], right :: rights => sumBit false right carry :: addWords (nextCarry false right carry) [] rights
  | left :: lefts, right :: rights =>
      sumBit left right carry :: addWords (nextCarry left right carry) lefts rights
termination_by left.length + right.length

def normalize : List Bool → List Bool
  | [] => []
  | bit :: rest =>
      let tail := normalize rest
      if tail.isEmpty && !bit then [] else bit :: tail

def trim : List Bool → List Bool
  | [] => []
  | false :: rest => trim rest
  | true :: rest => true :: rest

theorem value_cons (bit : Bool) (rest : List Bool) :
    value (bit :: rest) = bitValue bit + 2 * value rest := by
  simp only [value, List.map_cons, Nat.ofDigits_cons]

theorem addWords_value (left right : List Bool) (carry : Bool) :
    value (addWords carry left right) = value left + value right + bitValue carry := by
  induction left generalizing right carry with
  | nil =>
      induction right generalizing carry with
      | nil => cases carry <;> simp [addWords, value, bitValue]
      | cons bit right ih =>
          rw [addWords, value_cons, ih, value_cons]
          have digit := digit_sum false bit carry
          have nilValue : value [] = 0 := rfl
          have falseValue : bitValue false = 0 := rfl
          simp only [nilValue, falseValue] at digit ⊢
          omega
  | cons bit left ih =>
      cases right with
      | nil =>
          rw [addWords, value_cons, ih, value_cons]
          have digit := digit_sum bit false carry
          have nilValue : value [] = 0 := rfl
          have falseValue : bitValue false = 0 := rfl
          simp only [nilValue, falseValue] at digit ⊢
          omega
      | cons other right =>
          rw [addWords, value_cons, ih, value_cons, value_cons]
          have digit := digit_sum bit other carry
          omega

theorem addWords_length (left right : List Bool) (carry : Bool) :
    (addWords carry left right).length ≤ left.length + right.length + 1 := by
  induction left generalizing right carry with
  | nil =>
      induction right generalizing carry with
      | nil => cases carry <;> simp [addWords]
      | cons bit right ih => simp only [addWords, List.length_cons]; have h := ih (nextCarry false bit carry); omega
  | cons bit left ih =>
      cases right with
      | nil => simp only [addWords, List.length_cons, List.length_nil]; have h := ih [] (nextCarry bit false carry); simp only [List.length_nil] at h; omega
      | cons other right => simp only [addWords, List.length_cons]; have h := ih right (nextCarry bit other carry); omega

theorem trim_append (first second : List Bool) :
    trim (first ++ second) = if (trim first).isEmpty then trim second else trim first ++ second := by
  induction first with
  | nil => simp [trim]
  | cons bit first ih => cases bit <;> simp [trim, ih]

theorem trim_reverse (word : List Bool) : trim word.reverse = (normalize word).reverse := by
  induction word with
  | nil => rfl
  | cons bit rest ih =>
      simp only [List.reverse_cons, trim_append, ih, normalize]
      cases h : normalize rest with
      | nil => cases bit <;> simp [trim]
      | cons head tail => cases bit <;> simp

theorem naturalBits_digit (bit : Bool) (n : Nat) (positive : bitValue bit + 2 * n ≠ 0) :
    naturalBits (bitValue bit + 2 * n) = bit :: naturalBits n := by
  cases bit with
  | false =>
      have nonzero : n ≠ 0 := by simp only [bitValue, Bool.false_eq_true, ↓reduceIte] at positive; omega
      change (Nat.digits 2 (0 + 2 * n)).map _ = _
      rw [Nat.digits_add 2 (by decide) 0 n (by decide) (Or.inr nonzero)]
      rfl
  | true =>
      change (Nat.digits 2 (1 + 2 * n)).map _ = _
      rw [Nat.digits_add 2 (by decide) 1 n (by decide) (Or.inl (by decide))]
      rfl

theorem normalize_naturalBits (word : List Bool) : normalize word = naturalBits (value word) := by
  induction word with
  | nil => simp [normalize, value, naturalBits]
  | cons bit rest ih =>
      have empty_iff : (naturalBits (value rest)).isEmpty = true ↔ value rest = 0 := by
        constructor
        · intro empty
          have equality : naturalBits (value rest) = [] := List.isEmpty_iff.mp empty
          have h := BinaryStackArithmetic.naturalBits_value (value rest)
          rw [equality] at h
          simpa [value] using h.symm
        · intro zero; simp [zero, naturalBits]
      cases bit with
      | false =>
          by_cases zero : value rest = 0
          · simp [normalize, ih, zero, value_cons, bitValue, naturalBits]
          · have nonempty : (naturalBits (value rest)).isEmpty = false := by
              cases h : (naturalBits (value rest)).isEmpty
              · rfl
              · exact (zero (empty_iff.mp h)).elim
            rw [normalize, ih]
            simp only [nonempty, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
            rw [value_cons]
            exact (naturalBits_digit false (value rest) (by simp only [bitValue]; omega)).symm
      | true =>
          rw [normalize, ih]
          simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          rw [value_cons]
          exact (naturalBits_digit true (value rest) (by simp [bitValue])).symm

theorem addition_exact (left right : List Bool) :
    normalize (addWords false left right) = naturalBits (value left + value right) := by
  rw [normalize_naturalBits, addWords_value]
  simp [bitValue]

/-- Removing high zeroes never enlarges the physically stored word. -/
theorem normalize_length (word : List Bool) : (normalize word).length ≤ word.length := by
  induction word with
  | nil => rfl
  | cons bit rest ih =>
      simp only [normalize, List.length_cons]
      split
      · simp
      · simp only [List.length_cons]
        omega

/-- Canonical addition charges binary payload lengths, including the final
carry, independently of the numbers represented by those payloads. -/
theorem naturalBits_add_length (left right : Nat) :
    (naturalBits (left + right)).length ≤
      (naturalBits left).length + (naturalBits right).length + 1 := by
  have exactWord := addition_exact (naturalBits left) (naturalBits right)
  simp only [BinaryStackArithmetic.naturalBits_value] at exactWord
  rw [← exactWord]
  exact (normalize_length _).trans (addWords_length _ _ _)

inductive Stack where
  | input | temporary | left | digits | result
  deriving DecidableEq, Fintype

inductive Phase where
  | scan | restoreLeft | add | trim | restore
  | rejectInput | rejectTemporary | rejectLeft | rejectDigits | rejectResult
  deriving DecidableEq, Fintype

abbrev State := Bool × Option (Option Bool) × Option Bool
abbrev Cells : Stack → Type
  | .input | .result => Option Bool
  | _ => Bool

instance (stack : Stack) : Fintype (Cells stack) := by cases stack <;> infer_instance
instance (stack : Stack) : Inhabited (Cells stack) := by cases stack <;> infer_instance

def initial : State := (false, none, none)

def packet (left right : List Bool) : List (Option Bool) := left.map some ++ none :: right.map some

def program (phase : Phase) : TM2.Stmt Cells Phase State := match phase with
  | .scan => pop .input (fun state symbol => (state.1, symbol, state.2.2))
      (branch (fun state => state.2.1 == some none)
        (goto fun _ => .restoreLeft)
        (branch (fun state => state.2.1.isSome)
          (push .temporary (fun state => (state.2.1.getD none).getD false) (goto fun _ => .scan))
          (goto fun _ => .rejectInput)))
  | .restoreLeft => pop .temporary (fun state symbol => (state.1, state.2.1, symbol))
      (branch (fun state => state.2.2.isSome)
        (push .left (fun state => state.2.2.getD false) (goto fun _ => .restoreLeft))
        (goto fun _ => .add))
  | .add => pop .input (fun state symbol => (state.1, symbol, state.2.2))
      (branch (fun state => state.2.1 == some none)
        (goto fun _ => .rejectInput)
        (pop .left (fun state symbol => (state.1, state.2.1, symbol))
          (branch (fun state => state.2.1.isNone && state.2.2.isNone)
            (branch Prod.fst
              (push .digits (fun _ => true) (load (fun _ => initial) (goto fun _ => .trim)))
              (load (fun _ => initial) (goto fun _ => .trim)))
            (push .digits (fun state => sumBit (state.2.2.getD false)
                ((state.2.1.getD none).getD false) state.1)
              (load (fun state => (nextCarry (state.2.2.getD false)
                  ((state.2.1.getD none).getD false) state.1, none, none)) (goto fun _ => .add))))))
  | .trim => pop .digits (fun state symbol => (state.1, state.2.1, symbol))
      (branch (fun state => state.2.2 == some false)
        (goto fun _ => .trim)
        (branch (fun state => state.2.2 == some true)
          (push .result (fun _ => some true) (goto fun _ => .restore))
          (load (fun _ => initial) halt)))
  | .restore => pop .digits (fun state symbol => (state.1, state.2.1, symbol))
      (branch (fun state => state.2.2.isSome)
        (push .result (fun state => some (state.2.2.getD false)) (goto fun _ => .restore))
        (load (fun _ => initial) halt))
  | .rejectInput => pop .input (fun state symbol => (state.1, symbol, state.2.2))
      (branch (fun state => state.2.1.isSome) (goto fun _ => .rejectInput) (goto fun _ => .rejectTemporary))
  | .rejectTemporary => pop .temporary (fun state symbol => (state.1, state.2.1, symbol))
      (branch (fun state => state.2.2.isSome) (goto fun _ => .rejectTemporary) (goto fun _ => .rejectLeft))
  | .rejectLeft => pop .left (fun state symbol => (state.1, state.2.1, symbol))
      (branch (fun state => state.2.2.isSome) (goto fun _ => .rejectLeft) (goto fun _ => .rejectDigits))
  | .rejectDigits => pop .digits (fun state symbol => (state.1, state.2.1, symbol))
      (branch (fun state => state.2.2.isSome) (goto fun _ => .rejectDigits) (goto fun _ => .rejectResult))
  | .rejectResult => pop .result (fun state symbol => (state.1, symbol, state.2.2))
      (branch (fun state => state.2.1.isSome) (goto fun _ => .rejectResult)
        (push .result (fun _ => none) (load (fun _ => initial) halt)))

def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := Cells
  Λ := Phase
  main := .scan
  σ := State
  initialState := initial
  m := program

def config (phase : Option Phase) (state : State)
    (input : List (Option Bool)) (temporary left digits : List Bool) (result : List (Option Bool)) : machine.Cfg where
  l := phase
  var := state
  stk key := match (show Stack from key) with
    | .input => input | .temporary => temporary | .left => left | .digits => digits | .result => result

local macro "check_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux, initial] <;>
  (funext key; cases key <;> simp [Function.update])))

theorem scan_bit (state : State) (bit : Bool) (tail : List (Option Bool))
    (temporary left digits : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .scan) state (some bit :: tail) temporary left digits result) =
      some (config (some .scan) (state.1, some (some bit), state.2.2) tail
        (bit :: temporary) left digits result) := by check_step

theorem scan_delimiter (state : State) (input : List (Option Bool))
    (temporary left digits : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .scan) state (none :: input) temporary left digits result) =
      some (config (some .restoreLeft) (state.1, some none, state.2.2) input temporary left digits result) := by check_step

theorem restore_left_cons (state : State) (bit : Bool) (input : List (Option Bool))
    (tail left digits : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .restoreLeft) state input (bit :: tail) left digits result) =
      some (config (some .restoreLeft) (state.1, state.2.1, some bit) input tail (bit :: left) digits result) := by check_step

theorem restore_left_nil (state : State) (input : List (Option Bool))
    (left digits : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .restoreLeft) state input [] left digits result) =
      some (config (some .add) (state.1, state.2.1, none) input [] left digits result) := by check_step

theorem add_pair (state : State) (left right : Bool) (lefts rights digits : List Bool)
    (result : List (Option Bool)) :
    machine.step (config (some .add) state (some right :: rights.map some) [] (left :: lefts) digits result) =
      some (config (some .add) (nextCarry left right state.1, none, none) (rights.map some) [] lefts
        (sumBit left right state.1 :: digits) result) := by check_step

theorem add_left (state : State) (left : Bool) (lefts digits : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .add) state [] [] (left :: lefts) digits result) =
      some (config (some .add) (nextCarry left false state.1, none, none) [] [] lefts
        (sumBit left false state.1 :: digits) result) := by check_step

theorem add_right (state : State) (right : Bool) (rights digits : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .add) state (some right :: rights.map some) [] [] digits result) =
      some (config (some .add) (nextCarry false right state.1, none, none) (rights.map some) [] []
        (sumBit false right state.1 :: digits) result) := by check_step

theorem add_end (state : State) (digits : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .add) state [] [] [] digits result) =
      some (config (some .trim) initial [] [] [] (if state.1 then true :: digits else digits) result) := by
  rcases state with ⟨carry, last⟩
  cases carry <;> check_step

theorem trim_false (state : State) (digits : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .trim) state [] [] [] (false :: digits) result) =
      some (config (some .trim) (state.1, state.2.1, some false) [] [] [] digits result) := by check_step

theorem trim_true (state : State) (digits : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .trim) state [] [] [] (true :: digits) result) =
      some (config (some .restore) (state.1, state.2.1, some true) [] [] [] digits (some true :: result)) := by check_step

theorem trim_nil (state : State) (result : List (Option Bool)) :
    machine.step (config (some .trim) state [] [] [] [] result) =
      some (config none initial [] [] [] [] result) := by check_step

theorem restore_cons (state : State) (bit : Bool) (tail : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .restore) state [] [] [] (bit :: tail) result) =
      some (config (some .restore) (state.1, state.2.1, some bit) [] [] [] tail (some bit :: result)) := by check_step

theorem restore_nil (state : State) (result : List (Option Bool)) :
    machine.step (config (some .restore) state [] [] [] [] result) =
      some (config none initial [] [] [] [] result) := by check_step

/-- Scan one original bit field and consume exactly its delimiter. -/
def scanRun (left : List Bool) (input : List (Option Bool)) (state : State)
    (temporary stored digits : List Bool) (result : List (Option Bool)) :
    EvalsToInTime machine.step
      (config (some .scan) state (left.map some ++ none :: input) temporary stored digits result)
      (some (config (some .restoreLeft) (state.1, some none, state.2.2) input
        (left.reverse ++ temporary) stored digits result)) (left.length + 1) := by
  induction left generalizing state temporary with
  | nil => simpa using oneStep (scan_delimiter state input temporary stored digits result)
  | cons bit left ih =>
      have first := oneStep (scan_bit state bit (left.map some ++ none :: input) temporary stored digits result)
      have tail := ih (state.1, some (some bit), state.2.2) (bit :: temporary)
      simpa [List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (left.length + 1) _ _ _ first tail

def restoreLeftRun (temporary : List Bool) (input : List (Option Bool)) (state : State)
    (left digits : List Bool) (result : List (Option Bool)) :
    EvalsToInTime machine.step
      (config (some .restoreLeft) state input temporary left digits result)
      (some (config (some .add) (state.1, state.2.1, none) input [] (temporary.reverse ++ left) digits result))
      (temporary.length + 1) := by
  induction temporary generalizing state left with
  | nil => simpa using oneStep (restore_left_nil state input left digits result)
  | cons bit tail ih =>
      have first := oneStep (restore_left_cons state bit input tail left digits result)
      have rest := ih (state.1, state.2.1, some bit) (bit :: left)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def addRun (left right : List Bool) (state : State) (digits : List Bool) (result : List (Option Bool)) :
    EvalsToInTime machine.step
      (config (some .add) state (right.map some) [] left digits result)
      (some (config (some .trim) initial [] [] [] ((addWords state.1 left right).reverse ++ digits) result))
      (left.length + right.length + 1) := by
  induction left generalizing right state digits with
  | nil =>
      induction right generalizing state digits with
      | nil =>
          have step := oneStep (add_end state digits result)
          cases h : state.1 <;> simpa [addWords, h] using step
      | cons bit right ih =>
          have first := oneStep (add_right state bit right digits result)
          have rest := ih (nextCarry false bit state.1, none, none) (sumBit false bit state.1 :: digits)
          simp only [List.length_nil, Nat.zero_add] at rest
          simpa [addWords, List.reverse_cons, List.append_assoc] using
            EvalsToInTime.trans _ 1 (right.length + 1) _ _ _ first rest
  | cons bit left ih =>
      cases right with
      | nil =>
          have first := oneStep (add_left state bit left digits result)
          have rest := ih [] (nextCarry bit false state.1, none, none) (sumBit bit false state.1 :: digits)
          simpa [addWords, List.reverse_cons, List.append_assoc] using
            EvalsToInTime.trans _ 1 (left.length + 1) _ _ _ first rest
      | cons other right =>
          have first := oneStep (add_pair state bit other left right digits result)
          have rest := ih right (nextCarry bit other state.1, none, none) (sumBit bit other state.1 :: digits)
          have joined := EvalsToInTime.trans _ 1 (left.length + right.length + 1) _ _ _ first rest
          have shaped : EvalsToInTime machine.step
              (config (some .add) state ((other :: right).map some) [] (bit :: left) digits result)
              (some (config (some .trim) initial [] [] []
                ((addWords state.1 (bit :: left) (other :: right)).reverse ++ digits) result))
              (1 + (left.length + right.length + 1)) := by
            simpa [addWords, List.reverse_cons, List.append_assoc, Nat.add_comm] using joined
          exact ⟨shaped.toEvalsTo, shaped.steps_le_m.trans (by simp only [List.length_cons]; omega)⟩

def restoreRun (digits : List Bool) (state : State) (result : List (Option Bool)) :
    EvalsToInTime machine.step
      (config (some .restore) state [] [] [] digits result)
      (some (config none initial [] [] [] [] (digits.reverse.map some ++ result))) (digits.length + 1) := by
  induction digits generalizing state result with
  | nil => simpa using oneStep (restore_nil state result)
  | cons bit tail ih =>
      have first := oneStep (restore_cons state bit tail result)
      have rest := ih (state.1, state.2.1, some bit) (some bit :: result)
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def trimRun (digits : List Bool) (state : State) (result : List (Option Bool)) :
    EvalsToInTime machine.step
      (config (some .trim) state [] [] [] digits result)
      (some (config none initial [] [] [] [] ((trim digits).reverse.map some ++ result))) (digits.length + 1) := by
  induction digits generalizing state with
  | nil => simpa [trim] using oneStep (trim_nil state result)
  | cons bit tail ih =>
      cases bit with
      | false =>
          have first := oneStep (trim_false state tail result)
          have rest := ih (state.1, state.2.1, some false)
          simpa [trim] using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
      | true =>
          have first := oneStep (trim_true state tail result)
          have rest := restoreRun tail (state.1, state.2.1, some true) (some true :: result)
          simpa [trim, List.reverse_cons, List.map_append, List.append_assoc] using
            EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

theorem init_eq (input : List (Option Bool)) : initList machine input = config (some .scan) initial input [] [] [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key <;> rfl

theorem halt_eq (result : List (Option Bool)) : haltList machine result = config none initial [] [] [] [] result := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key <;> simp

/-- Every valid pair of bit words is normalized by the actual machine. -/
def outputs (left right : List Bool) :
    TM2OutputsInTime machine (packet left right)
      (some ((naturalBits (value left + value right)).map some))
      (5 * (packet left right).length + 8) := by
  have scanned := scanRun left (right.map some) initial [] [] [] []
  have restored := restoreLeftRun left.reverse (right.map some) (false, some none, none) [] [] []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at restored scanned
  have added := addRun left right (false, some none, none) [] []
  simp only [List.append_nil] at added
  have normalized := trimRun (addWords false left right).reverse initial []
  simp only [trim_reverse, List.reverse_reverse, List.append_nil, addition_exact] at normalized
  have a := EvalsToInTime.trans _ (left.length + 1) (left.length + 1) _ _ _ scanned restored
  have b := EvalsToInTime.trans _ (left.length + 1 + (left.length + 1))
    (left.length + right.length + 1) _ _ _ a added
  have c := EvalsToInTime.trans _ (left.length + right.length + 1 + (left.length + 1 + (left.length + 1)))
    ((addWords false left right).reverse.length + 1) _ _ _ b normalized
  change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
  rw [init_eq, halt_eq]
  have size := addWords_length left right false
  refine ⟨c.toEvalsTo, c.steps_le_m.trans ?_⟩
  simp only [packet, List.length_append, List.length_map, List.length_cons, List.length_reverse]
  omega

def encodedInput (input : Nat × Nat) : List (Option Bool) := packet (naturalBits input.1) (naturalBits input.2)

def naturalOutputs (left right : Nat) :
    TM2OutputsInTime machine (encodedInput (left, right)) (some ((naturalBits (left + right)).map some))
      (5 * (encodedInput (left, right)).length + 8) := by
  simpa only [encodedInput, BinaryStackArithmetic.naturalBits_value] using outputs (naturalBits left) (naturalBits right)

noncomputable def realization : TM2ComputableInPolyTime encodedInput
    (fun n => (naturalBits n).map some) (fun input => input.1 + input.2) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C 5 * X + C 8
  outputsFun input := by
    change TM2OutputsInTime machine ((encodedInput input).map id)
      (some (((naturalBits (input.1 + input.2)).map some).map id)) _
    simpa only [List.map_id, eval_add, eval_mul, eval_C, eval_X] using naturalOutputs input.1 input.2

theorem reject_input_cons (state : State) (bit : Option Bool) (tail : List (Option Bool)) (temporary : List Bool) (left : List Bool) (digits : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .rejectInput) state (bit :: tail) temporary left digits result) =
      some (config (some .rejectInput) (state.1, some bit, state.2.2) tail temporary left digits result) := by check_step

theorem reject_input_nil (state : State) (temporary : List Bool) (left : List Bool) (digits : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .rejectInput) state [] temporary left digits result) =
      some (config (some .rejectTemporary) (state.1, none, state.2.2) [] temporary left digits result) := by check_step

theorem reject_temporary_cons (state : State) (bit : Bool) (tail : List Bool) (left : List Bool) (digits : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .rejectTemporary) state [] (bit :: tail) left digits result) =
      some (config (some .rejectTemporary) (state.1, state.2.1, some bit) [] tail left digits result) := by check_step

theorem reject_temporary_nil (state : State) (left : List Bool) (digits : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .rejectTemporary) state [] [] left digits result) =
      some (config (some .rejectLeft) (state.1, state.2.1, none) [] [] left digits result) := by check_step

theorem reject_left_cons (state : State) (bit : Bool) (tail : List Bool) (digits : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .rejectLeft) state [] [] (bit :: tail) digits result) =
      some (config (some .rejectLeft) (state.1, state.2.1, some bit) [] [] tail digits result) := by check_step

theorem reject_left_nil (state : State) (digits : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .rejectLeft) state [] [] [] digits result) =
      some (config (some .rejectDigits) (state.1, state.2.1, none) [] [] [] digits result) := by check_step

theorem reject_digits_cons (state : State) (bit : Bool) (tail : List Bool) (result : List (Option Bool)) :
    machine.step (config (some .rejectDigits) state [] [] [] (bit :: tail) result) =
      some (config (some .rejectDigits) (state.1, state.2.1, some bit) [] [] [] tail result) := by check_step

theorem reject_digits_nil (state : State) (result : List (Option Bool)) :
    machine.step (config (some .rejectDigits) state [] [] [] [] result) =
      some (config (some .rejectResult) (state.1, state.2.1, none) [] [] [] [] result) := by check_step

theorem reject_result_cons (state : State) (bit : Option Bool) (tail : List (Option Bool))  :
    machine.step (config (some .rejectResult) state [] [] [] [] (bit :: tail)) =
      some (config (some .rejectResult) (state.1, some bit, state.2.2) [] [] [] [] tail) := by check_step

theorem reject_result_nil (state : State)  :
    machine.step (config (some .rejectResult) state [] [] [] [] []) =
      some (config none initial [] [] [] [] [none]) := by check_step

def rejectResultRun (state : State) (result : List (Option Bool))  :
    EvalsToInTime machine.step (config (some .rejectResult) state [] [] [] [] result)
      (some (config none initial [] [] [] [] [none])) (result.length + 1) := by
  induction result generalizing state with
  | nil =>
      have first := oneStep (reject_result_nil state )
      simpa using first
  | cons bit tail ih =>
      have first := oneStep (reject_result_cons state bit tail )
      have rest := ih (state.1, some bit, state.2.2)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ 1
        (tail.length + 1) _ _ _ first rest

def rejectDigitsRun (state : State) (digits : List Bool) (result : List (Option Bool)) :
    EvalsToInTime machine.step (config (some .rejectDigits) state [] [] [] digits result)
      (some (config none initial [] [] [] [] [none])) (digits.length + result.length + 2) := by
  induction digits generalizing state with
  | nil =>
      have first := oneStep (reject_digits_nil state result)
      have tail := rejectResultRun (state.1, state.2.1, none) result
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ 1 (result.length + 1) _ _ _ first tail
  | cons bit tail ih =>
      have first := oneStep (reject_digits_cons state bit tail result)
      have rest := ih (state.1, state.2.1, some bit)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ 1
        (tail.length + result.length + 2) _ _ _ first rest

def rejectLeftRun (state : State) (left : List Bool) (digits : List Bool) (result : List (Option Bool)) :
    EvalsToInTime machine.step (config (some .rejectLeft) state [] [] left digits result)
      (some (config none initial [] [] [] [] [none])) (left.length + digits.length + result.length + 3) := by
  induction left generalizing state with
  | nil =>
      have first := oneStep (reject_left_nil state digits result)
      have tail := rejectDigitsRun (state.1, state.2.1, none) digits result
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ 1 (digits.length + result.length + 2) _ _ _ first tail
  | cons bit tail ih =>
      have first := oneStep (reject_left_cons state bit tail digits result)
      have rest := ih (state.1, state.2.1, some bit)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ 1
        (tail.length + digits.length + result.length + 3) _ _ _ first rest

def rejectTemporaryRun (state : State) (temporary : List Bool) (left : List Bool) (digits : List Bool) (result : List (Option Bool)) :
    EvalsToInTime machine.step (config (some .rejectTemporary) state [] temporary left digits result)
      (some (config none initial [] [] [] [] [none])) (temporary.length + left.length + digits.length + result.length + 4) := by
  induction temporary generalizing state with
  | nil =>
      have first := oneStep (reject_temporary_nil state left digits result)
      have tail := rejectLeftRun (state.1, state.2.1, none) left digits result
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ 1 (left.length + digits.length + result.length + 3) _ _ _ first tail
  | cons bit tail ih =>
      have first := oneStep (reject_temporary_cons state bit tail left digits result)
      have rest := ih (state.1, state.2.1, some bit)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ 1
        (tail.length + left.length + digits.length + result.length + 4) _ _ _ first rest

def rejectInputRun (state : State) (input : List (Option Bool)) (temporary : List Bool) (left : List Bool) (digits : List Bool) (result : List (Option Bool)) :
    EvalsToInTime machine.step (config (some .rejectInput) state input temporary left digits result)
      (some (config none initial [] [] [] [] [none])) (input.length + temporary.length + left.length + digits.length + result.length + 5) := by
  induction input generalizing state with
  | nil =>
      have first := oneStep (reject_input_nil state temporary left digits result)
      have tail := rejectTemporaryRun (state.1, none, state.2.2) temporary left digits result
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ 1 (temporary.length + left.length + digits.length + result.length + 4) _ _ _ first tail
  | cons bit tail ih =>
      have first := oneStep (reject_input_cons state bit tail temporary left digits result)
      have rest := ih (state.1, some bit, state.2.2)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ 1
        (tail.length + temporary.length + left.length + digits.length + result.length + 5) _ _ _ first rest

theorem scan_missing (state : State) (temporary : List Bool) :
    machine.step (config (some .scan) state [] temporary [] [] []) =
      some (config (some .rejectInput) (state.1, none, state.2.2) [] temporary [] [] []) := by check_step

def missingRun (word : List Bool) (state : State) (temporary : List Bool) :
    EvalsToInTime machine.step (config (some .scan) state (word.map some) temporary [] [] [])
      (some (config (some .rejectInput) (state.1, none, state.2.2) []
        (word.reverse ++ temporary) [] [] [])) (word.length + 1) := by
  induction word generalizing state temporary with
  | nil => simpa using oneStep (scan_missing state temporary)
  | cons bit word ih =>
      have first := oneStep (scan_bit state bit (word.map some) temporary [] [] [])
      have rest := ih (state.1, some (some bit), state.2.2) (bit :: temporary)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ 1 (word.length + 1) _ _ _ first rest

def missingDelimiterOutputs (word : List Bool) :
    TM2OutputsInTime machine (word.map some) (some [none]) (5 * word.length + 8) := by
  have first := missingRun word initial []
  simp only [List.append_nil] at first
  have rest := rejectInputRun (false, none, none) [] word.reverse [] [] []
  have joined := EvalsToInTime.trans _ (word.length + 1) (0 + word.reverse.length + 0 + 0 + 0 + 5) _ _ _ first rest
  change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
  rw [init_eq, halt_eq]
  refine ⟨joined.toEvalsTo, joined.steps_le_m.trans ?_⟩
  simp only [List.length_reverse]
  omega

theorem add_delimiter (state : State) (input : List (Option Bool)) (left digits : List Bool) :
    machine.step (config (some .add) state (none :: input) [] left digits []) =
      some (config (some .rejectInput) (state.1, some none, state.2.2) input [] left digits []) := by check_step

theorem add_pair_tail (state : State) (left right : Bool) (input : List (Option Bool)) (lefts digits : List Bool) :
    machine.step (config (some .add) state (some right :: input) [] (left :: lefts) digits []) =
      some (config (some .add) (nextCarry left right state.1, none, none) input [] lefts
        (sumBit left right state.1 :: digits) []) := by check_step

theorem add_right_tail (state : State) (right : Bool) (input : List (Option Bool)) (digits : List Bool) :
    machine.step (config (some .add) state (some right :: input) [] [] digits []) =
      some (config (some .add) (nextCarry false right state.1, none, none) input [] []
        (sumBit false right state.1 :: digits) []) := by check_step

/-- Before a second delimiter is seen, only finite carry and actual bit-stack
operations are performed. The bounds retain all produced scratch digits. -/
noncomputable def delimiterPrefixRun (right : List Bool) (left : List Bool) (input : List (Option Bool))
    (state : State) (digits : List Bool) :
    Σ finalState : State, Σ finalLeft : List Bool, Σ finalDigits : List Bool,
      { _run : EvalsToInTime machine.step
        (config (some .add) state (right.map some ++ none :: input) [] left digits [])
        (some (config (some .rejectInput) finalState input [] finalLeft finalDigits [])) (right.length + 1) //
      finalLeft.length ≤ left.length ∧ finalDigits.length ≤ digits.length + right.length } := by
  induction right generalizing left state digits with
  | nil => exact ⟨(state.1, some none, state.2.2), left, digits,
      by simpa using oneStep (add_delimiter state input left digits), by omega, by simp⟩
  | cons bit right ih =>
      cases left with
      | nil =>
          have first := oneStep (add_right_tail state bit (right.map some ++ none :: input) digits)
          obtain ⟨finalState, finalLeft, finalDigits, rest, boundLeft, boundDigits⟩ :=
            ih [] (nextCarry false bit state.1, none, none) (sumBit false bit state.1 :: digits)
          refine ⟨finalState, finalLeft, finalDigits, ?_, boundLeft, ?_⟩
          · simpa using EvalsToInTime.trans _ 1 (right.length + 1) _ _ _ first rest
          · simp only [List.length_cons] at *; omega
      | cons other left =>
          have first := oneStep (add_pair_tail state other bit (right.map some ++ none :: input) left digits)
          obtain ⟨finalState, finalLeft, finalDigits, rest, boundLeft, boundDigits⟩ :=
            ih left (nextCarry other bit state.1, none, none) (sumBit other bit state.1 :: digits)
          refine ⟨finalState, finalLeft, finalDigits, ?_, ?_, ?_⟩
          · simpa using EvalsToInTime.trans _ 1 (right.length + 1) _ _ _ first rest
          · simp only [List.length_cons]; omega
          · simp only [List.length_cons] at *; omega

noncomputable def repeatedDelimiterOutputs (left right : List Bool) (input : List (Option Bool)) :
    TM2OutputsInTime machine (left.map some ++ none :: right.map some ++ none :: input) (some [none])
      (5 * (left.map some ++ none :: right.map some ++ none :: input).length + 8) := by
  have scanned := scanRun left (right.map some ++ none :: input) initial [] [] [] []
  have restored := restoreLeftRun left.reverse (right.map some ++ none :: input) (false, some none, none) [] [] []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at scanned restored
  obtain ⟨finalState, finalLeft, finalDigits, prefixRun, boundLeft, boundDigits⟩ :=
    delimiterPrefixRun right left input (false, some none, none) []
  have cleared := rejectInputRun finalState input [] finalLeft finalDigits []
  have a := EvalsToInTime.trans _ (left.length + 1) (left.length + 1) _ _ _ scanned restored
  have b := EvalsToInTime.trans _ (left.length + 1 + (left.length + 1)) (right.length + 1) _ _ _ a prefixRun
  have c := EvalsToInTime.trans _ (right.length + 1 + (left.length + 1 + (left.length + 1)))
    (input.length + 0 + finalLeft.length + finalDigits.length + 0 + 5) _ _ _ b cleared
  change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
  rw [init_eq, halt_eq]
  simp only [List.append_assoc, List.cons_append]
  refine ⟨c.toEvalsTo, c.steps_le_m.trans ?_⟩
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at *
  omega

/-- Successful results contain only bits. Refusal has a symbol outside that
alphabet, including when the successful sum is zero and its word is empty. -/
def resultWire : Option Nat → List (Option Bool)
  | none => [none]
  | some n => (naturalBits n).map some

/-- Framing uses the shared delimiter classifier. Additional delimiters remain
visible in the second field and are refused by the physical carry pass. -/
def rawResult (input : List (Option Bool)) : Option Nat :=
  match (WordEqualityMachine.splitPacket input).2 with
  | none => none
  | some right =>
    match (WordEqualityMachine.splitPacket right).2 with
    | none => some (value (WordEqualityMachine.splitPacket input).1 +
        value (WordEqualityMachine.splitPacket right).1)
    | some _ => none

theorem rawResult_packet (left right : List Bool) :
    rawResult (packet left right) = some (value left + value right) := by
  simp [rawResult, packet, WordEqualityMachine.splitPacket_words,
    WordEqualityMachine.splitPacket_missing]

theorem rawResult_missing (word : List Bool) : rawResult (word.map some) = none := by
  simp [rawResult, WordEqualityMachine.splitPacket_missing]

theorem rawResult_repeated (left right : List Bool) (tail : List (Option Bool)) :
    rawResult (left.map some ++ none :: right.map some ++ none :: tail) = none := by
  simp only [List.append_assoc, List.cons_append, rawResult,
    WordEqualityMachine.splitPacket_words]

/-- Every raw packet halts with the stated result and all scratch stacks cleared.
Both missing and repeated delimiters consume the complete physical input. -/
noncomputable def rawOutputs (input : List (Option Bool)) :
    TM2OutputsInTime machine input (some (resultWire (rawResult input)))
      (5 * input.length + 8) := by
  have front := WordEqualityMachine.splitPacket_framing input
  cases first : (WordEqualityMachine.splitPacket input).2 with
  | none =>
    simp only [first, List.append_nil] at front
    have executed := missingDelimiterOutputs (WordEqualityMachine.splitPacket input).1
    rw [← front] at executed
    have lengths : (WordEqualityMachine.splitPacket input).1.length = input.length := by
      simpa only [List.length_map] using (congrArg List.length front).symm
    simpa only [rawResult, first, resultWire, lengths] using executed
  | some right =>
    simp only [first] at front
    have back := WordEqualityMachine.splitPacket_framing right
    cases second : (WordEqualityMachine.splitPacket right).2 with
    | none =>
      simp only [second, List.append_nil] at back
      have exactPacket : input = packet (WordEqualityMachine.splitPacket input).1
          (WordEqualityMachine.splitPacket right).1 := by
        exact front.trans (congrArg
          (fun field => (WordEqualityMachine.splitPacket input).1.map some ++ none :: field) back)
      have executed := outputs (WordEqualityMachine.splitPacket input).1
        (WordEqualityMachine.splitPacket right).1
      rw [← exactPacket] at executed
      simpa only [rawResult, first, second, resultWire] using executed
    | some tail =>
      simp only [second] at back
      have executed := repeatedDelimiterOutputs (WordEqualityMachine.splitPacket input).1
        (WordEqualityMachine.splitPacket right).1 tail
      have exactInput : input = (WordEqualityMachine.splitPacket input).1.map some ++
          none :: (WordEqualityMachine.splitPacket right).1.map some ++ none :: tail := by
        simpa only [List.append_assoc, List.cons_append] using front.trans (congrArg
          (fun field => (WordEqualityMachine.splitPacket input).1.map some ++ none :: field) back)
      rw [← exactInput] at executed
      simpa only [rawResult, first, second, resultWire] using executed

noncomputable def rawComputable : TM2ComputableInPolyTime
    (fun input : List (Option Bool) => input) resultWire rawResult where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C 5 * X + C 8
  outputsFun input := by
    change TM2OutputsInTime machine (input.map id)
      (some ((resultWire (rawResult input)).map id)) _
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using rawOutputs input

namespace Controls

theorem zero_sum : rawResult [none] = some 0 := rfl

theorem zero_word : resultWire (some 0) = [] := rfl

theorem missing_zero_refused : rawResult [] = none := rfl

theorem repeated_zero_refused : rawResult [none, none] = none := rfl

theorem long_carry : rawResult (packet (List.replicate 32 true) [true]) = some (2 ^ 32) := by
  decide

theorem high_zeros_normalized :
    resultWire (rawResult (packet [true, false, false] [true, false])) = [some false, some true] := rfl

end Controls

end Mettapedia.Computability.BinaryWordAddition
