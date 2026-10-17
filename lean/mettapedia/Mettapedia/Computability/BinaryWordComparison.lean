import Mettapedia.Computability.BinaryStackArithmetic
import Mettapedia.Computability.WordEqualityMachine

/-!
# Comparison of complete binary natural words

The finite machine compares two delimiter-framed, least-significant-bit-first
words. Higher differing bits overwrite lower-bit comparisons. It scans the
actual input bits and keeps all variable-sized values on stacks.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.BinaryWordComparison
open Turing StateTransition Polynomial Turing.TM2.Stmt
open BinaryStackArithmetic (bitValue value naturalBits naturalBits_value)
open StackMachineComposition (oneStep)

def updateLess (previous left right : Bool) : Bool :=
  if left = right then previous else !left && right

def lessFrom (previous : Bool) : List Bool → List Bool → Bool
  | [], [] => previous
  | [], right :: rest => lessFrom (updateLess previous false right) [] rest
  | left :: rest, [] => lessFrom (updateLess previous left false) rest []
  | left :: tail, right :: rest => lessFrom (updateLess previous left right) tail rest
termination_by left right => left.length + right.length

@[simp] theorem value_nil : value [] = 0 := rfl
@[simp] theorem value_cons (bit : Bool) (rest : List Bool) :
    value (bit :: rest) = bitValue bit + 2 * value rest := by
  simp only [value, List.map_cons, Nat.ofDigits_cons]

/-- Last differing physical bits have the original numerical ordering; equal
words retain the supplied finite comparison flag. -/
theorem lessFrom_true (left right : List Bool) (previous : Bool) :
    lessFrom previous left right = true ↔
      value left < value right ∨ value left = value right ∧ previous = true := by
  induction left generalizing right previous with
  | nil =>
    induction right generalizing previous with
    | nil => simp [lessFrom]
    | cons right rest ih =>
      rw [lessFrom, ih]
      cases right <;> cases previous <;> simp [updateLess, bitValue, value_cons] <;> omega
  | cons left tail ih =>
    cases right with
    | nil =>
      rw [lessFrom, ih]
      cases left <;> cases previous <;> simp [updateLess, bitValue, value_cons]
    | cons right rest =>
      rw [lessFrom, ih]
      cases left <;> cases right <;> cases previous <;>
        simp [updateLess, bitValue, value_cons] <;> omega

def less (left right : List Bool) : Bool := lessFrom false left right

theorem less_value (left right : List Bool) :
    less left right = decide (value left < value right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [less, lessFrom_true, Bool.false_eq_true, and_false, or_false, decide_eq_true_eq]

theorem less_naturalBits (left right : Nat) :
    less (naturalBits left) (naturalBits right) = decide (left < right) := by
  rw [less_value, naturalBits_value, naturalBits_value]

inductive Stack where
  | input | temporary | left | result
  deriving DecidableEq, Fintype

inductive Phase where
  | scan | restore | compare | rejectInput | rejectTemporary | rejectLeft
  deriving DecidableEq, Fintype

abbrev Cells : Stack → Type := fun _ => Option Bool
abbrev State := Option (Option Bool) × Bool

def packet (left right : List Bool) : List (Option Bool) :=
  left.map some ++ none :: right.map some

/-- The machine returns a Boolean slot on framed input and the outside
symbol on malformed framing. Refusal is distinct from successful false. -/
def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := Cells
  Λ := Phase
  main := .scan
  σ := State
  initialState := (none, false)
  m phase := match phase with
    | .scan => pop .input (fun state symbol => (symbol, state.2))
      (branch (fun state => state.1 == some none)
        (goto fun _ => .restore)
        (branch (fun state => state.1.isSome)
          (push .temporary (fun state => state.1.getD none) (goto fun _ => .scan))
          (goto fun _ => .rejectTemporary)))
    | .restore => pop .temporary (fun state symbol => (symbol, state.2))
      (branch (fun state => state.1.isSome)
        (push .left (fun state => state.1.getD none) (goto fun _ => .restore))
        (goto fun _ => .compare))
    | .compare => pop .input (fun state symbol => (symbol, state.2))
      (branch (fun state => state.1 == some none)
        (goto fun _ => .rejectInput)
        (pop .left (fun state symbol =>
            if state.1.isSome || symbol.isSome then
              (some (some false), updateLess state.2
                ((symbol.getD none).getD false) ((state.1.getD none).getD false))
            else (none, state.2))
          (branch (fun state => state.1.isSome)
            (goto fun _ => .compare)
            (push .result (fun state => some state.2)
              (load (fun _ => (none, false)) halt)))))
    | .rejectInput => pop .input (fun state symbol => (symbol, state.2))
      (branch (fun state => state.1.isSome)
        (goto fun _ => .rejectInput) (goto fun _ => .rejectTemporary))
    | .rejectTemporary => pop .temporary (fun state symbol => (symbol, state.2))
      (branch (fun state => state.1.isSome)
        (goto fun _ => .rejectTemporary) (goto fun _ => .rejectLeft))
    | .rejectLeft => pop .left (fun state symbol => (symbol, state.2))
      (branch (fun state => state.1.isSome)
        (goto fun _ => .rejectLeft)
        (push .result (fun _ => none) (load (fun _ => (none, false)) halt)))

def config (phase : Option Phase) (state : State)
    (input temporary left result : List (Option Bool)) : machine.Cfg where
  l := phase
  var := state
  stk key := match (show Stack from key) with
    | .input => input | .temporary => temporary | .left => left | .result => result

local macro "check_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  all_goals first
    | (funext key; cases key <;> simp [Function.update])
    | (congr 2; funext key; cases key <;> simp [Function.update])))

theorem scan_symbol (state : State) (head : Bool)
    (tail temporary left result : List (Option Bool)) :
    machine.step (config (some .scan) state (some head :: tail) temporary left result) =
      some (config (some .scan) (some (some head), state.2) tail (some head :: temporary) left result) := by
  check_step

theorem scan_delimiter (state : State) (tail temporary left result : List (Option Bool)) :
    machine.step (config (some .scan) state (none :: tail) temporary left result) =
      some (config (some .restore) (some none, state.2) tail temporary left result) := by
  check_step

theorem scan_nil (state : State) (temporary left result : List (Option Bool)) :
    machine.step (config (some .scan) state [] temporary left result) =
      some (config (some .rejectTemporary) (none, state.2) [] temporary left result) := by
  check_step

theorem restore_cons (state : State) (head : Option Bool)
    (input tail left result : List (Option Bool)) :
    machine.step (config (some .restore) state input (head :: tail) left result) =
      some (config (some .restore) (some head, state.2) input tail (head :: left) result) := by
  check_step

theorem restore_nil (state : State) (input left result : List (Option Bool)) :
    machine.step (config (some .restore) state input [] left result) =
      some (config (some .compare) (none, state.2) input [] left result) := by
  check_step

theorem compare_pair (state : State) (left right : Bool)
    (leftTail rightTail result : List (Option Bool)) :
    machine.step (config (some .compare) state (some right :: rightTail) [] (some left :: leftTail) result) =
      some (config (some .compare) (some (some false), updateLess state.2 left right)
        rightTail [] leftTail result) := by
  check_step

theorem compare_right (state : State) (right : Bool)
    (tail result : List (Option Bool)) :
    machine.step (config (some .compare) state (some right :: tail) [] [] result) =
      some (config (some .compare) (some (some false), updateLess state.2 false right) tail [] [] result) := by
  check_step

theorem compare_left (state : State) (left : Bool)
    (tail result : List (Option Bool)) :
    machine.step (config (some .compare) state [] [] (some left :: tail) result) =
      some (config (some .compare) (some (some false), updateLess state.2 left false) [] [] tail result) := by
  check_step

theorem compare_end (state : State) (result : List (Option Bool)) :
    machine.step (config (some .compare) state [] [] [] result) =
      some (config none (none, false) [] [] [] (some state.2 :: result)) := by
  check_step

def scanRun (left : List Bool) (right : List (Option Bool)) (state : State)
    (temporary stored result : List (Option Bool)) :
    EvalsToInTime machine.step
      (config (some .scan) state (left.map some ++ none :: right) temporary stored result)
      (some (config (some .restore) (some none, state.2) right
        ((left.map some).reverse ++ temporary) stored result)) (left.length + 1) := by
  induction left generalizing state temporary with
  | nil => simpa using oneStep (scan_delimiter state right temporary stored result)
  | cons head tail ih =>
    have first := oneStep (scan_symbol state head (tail.map some ++ none :: right) temporary stored result)
    have rest := ih (some (some head), state.2) (some head :: temporary)
    simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def restoreRun (temporary input left result : List (Option Bool)) (state : State) :
    EvalsToInTime machine.step (config (some .restore) state input temporary left result)
      (some (config (some .compare) (none, state.2) input [] (temporary.reverse ++ left) result))
      (temporary.length + 1) := by
  induction temporary generalizing state left with
  | nil => simpa using oneStep (restore_nil state input left result)
  | cons head tail ih =>
    have first := oneStep (restore_cons state head input tail left result)
    have rest := ih (head :: left) (some head, state.2)
    simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def compareRun (left right : List Bool) (state : State) (result : List (Option Bool)) :
    EvalsToInTime machine.step (config (some .compare) state (right.map some) [] (left.map some) result)
      (some (config none (none, false) [] [] [] (some (lessFrom state.2 left right) :: result)))
      (left.length + right.length + 1) := by
  induction left generalizing right state with
  | nil =>
    induction right generalizing state with
    | nil => simpa [lessFrom] using oneStep (compare_end state result)
    | cons right rest ih =>
      have first := oneStep (compare_right state right (rest.map some) result)
      have next := ih (some (some false), updateLess state.2 false right)
      simp only [List.map_nil, List.length_nil, Nat.zero_add] at next
      simpa [lessFrom] using EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first next
  | cons left tail ih =>
    cases right with
    | nil =>
      have first := oneStep (compare_left state left (tail.map some) result)
      have next := ih [] (some (some false), updateLess state.2 left false)
      simpa [lessFrom] using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first next
    | cons right rest =>
      have first := oneStep (compare_pair state left right (tail.map some) (rest.map some) result)
      have next := ih rest (some (some false), updateLess state.2 left right)
      have joined := EvalsToInTime.trans _ 1 (tail.length + rest.length + 1) _ _ _ first next
      have bound : (tail.length + rest.length + 1) + 1 ≤
          (left :: tail).length + (right :: rest).length + 1 := by simp only [List.length_cons]; omega
      have enlarged : EvalsToInTime machine.step _ _
          ((left :: tail).length + (right :: rest).length + 1) :=
        ⟨joined.toEvalsTo, joined.steps_le_m.trans bound⟩
      simpa only [List.map_cons, lessFrom] using enlarged

theorem init_eq (input : List (Option Bool)) :
    initList machine input = config (some .scan) (none, false) input [] [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key <;> simp

theorem halt_eq (output : List (Option Bool)) :
    haltList machine output = config none (none, false) [] [] [] output := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key <;> simp

/-- The clock charges first-word scan/restoration and every actual paired-bit
transition. The size is the physical packet, not the represented numbers. -/
def outputs (left right : List Bool) :
    TM2OutputsInTime machine (packet left right) (some [some (less left right)])
      (3 * (packet left right).length + 3) := by
  have scanned := scanRun left (right.map some) (none, false) [] [] []
  simp only [List.append_nil] at scanned
  have restored := restoreRun (left.map some).reverse (right.map some) [] [] (some none, false)
  simp only [List.reverse_reverse, List.append_nil] at restored
  have compared := compareRun left right (none, false) []
  have front := EvalsToInTime.trans _ (left.length + 1) ((left.map some).reverse.length + 1) _ _ _ scanned restored
  have joined := EvalsToInTime.trans _ (((left.map some).reverse.length + 1) + (left.length + 1))
    (left.length + right.length + 1) _ _ _ front compared
  change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
  rw [init_eq, halt_eq]
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by simp [packet]; omega)⟩

/-- Malformed right fields are refused before their delimiter can become a
numerical bit. The source uses the shared finite framing classifier. -/
def rawLessFrom (previous : Bool) : List Bool → List (Option Bool) → Option Bool
  | [], [] => some previous
  | [], some right :: rest => rawLessFrom (updateLess previous false right) [] rest
  | left :: tail, [] => rawLessFrom (updateLess previous left false) tail []
  | left :: tail, some right :: rest => rawLessFrom (updateLess previous left right) tail rest
  | _, none :: _ => none
termination_by left right => left.length + right.length

theorem rawLessFrom_words (left right : List Bool) (previous : Bool) :
    rawLessFrom previous left (right.map some) = some (lessFrom previous left right) := by
  induction left generalizing right previous with
  | nil =>
    induction right generalizing previous with
    | nil => simp only [List.map_nil, rawLessFrom, lessFrom]
    | cons head tail ih => simpa only [List.map_cons, rawLessFrom, lessFrom] using ih (updateLess previous false head)
  | cons head tail ih =>
    cases right with
    | nil => simpa only [List.map_nil, rawLessFrom, lessFrom] using ih [] (updateLess previous head false)
    | cons other rest => simpa only [List.map_cons, rawLessFrom, lessFrom] using ih rest (updateLess previous head other)

theorem compare_delimiter (state : State) (tail left result : List (Option Bool)) :
    machine.step (config (some .compare) state (none :: tail) [] left result) =
      some (config (some .rejectInput) (some none, state.2) tail [] left result) := by
  check_step

theorem reject_input_cons (state : State) (head : Option Bool)
    (tail temporary left result : List (Option Bool)) :
    machine.step (config (some .rejectInput) state (head :: tail) temporary left result) =
      some (config (some .rejectInput) (some head, state.2) tail temporary left result) := by
  check_step

theorem reject_input_nil (state : State) (temporary left result : List (Option Bool)) :
    machine.step (config (some .rejectInput) state [] temporary left result) =
      some (config (some .rejectTemporary) (none, state.2) [] temporary left result) := by
  check_step

theorem reject_temporary_cons (state : State) (head : Option Bool)
    (tail left result : List (Option Bool)) :
    machine.step (config (some .rejectTemporary) state [] (head :: tail) left result) =
      some (config (some .rejectTemporary) (some head, state.2) [] tail left result) := by
  check_step

theorem reject_temporary_nil (state : State) (left result : List (Option Bool)) :
    machine.step (config (some .rejectTemporary) state [] [] left result) =
      some (config (some .rejectLeft) (none, state.2) [] [] left result) := by
  check_step

theorem reject_left_cons (state : State) (head : Option Bool) (tail result : List (Option Bool)) :
    machine.step (config (some .rejectLeft) state [] [] (head :: tail) result) =
      some (config (some .rejectLeft) (some head, state.2) [] [] tail result) := by
  check_step

theorem reject_left_nil (state : State) (result : List (Option Bool)) :
    machine.step (config (some .rejectLeft) state [] [] [] result) =
      some (config none (none, false) [] [] [] (none :: result)) := by
  check_step

def rejectLeftRun (left result : List (Option Bool)) (state : State) :
    EvalsToInTime machine.step (config (some .rejectLeft) state [] [] left result)
      (some (config none (none, false) [] [] [] (none :: result))) (left.length + 1) := by
  induction left generalizing state with
  | nil => simpa using oneStep (reject_left_nil state result)
  | cons head tail ih =>
    have first := oneStep (reject_left_cons state head tail result)
    have next := ih (some head, state.2)
    simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first next

def rejectTemporaryRun (temporary left result : List (Option Bool)) (state : State) :
    EvalsToInTime machine.step (config (some .rejectTemporary) state [] temporary left result)
      (some (config none (none, false) [] [] [] (none :: result)))
      (temporary.length + left.length + 2) := by
  induction temporary generalizing state with
  | nil =>
    have first := oneStep (reject_temporary_nil state left result)
    have next := rejectLeftRun left result (none, state.2)
    have joined := EvalsToInTime.trans _ 1 (left.length + 1) _ _ _ first next
    exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by simp only [List.length_nil, Nat.zero_add]; omega)⟩
  | cons head tail ih =>
    have first := oneStep (reject_temporary_cons state head tail left result)
    have next := ih (some head, state.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      EvalsToInTime.trans _ 1 (tail.length + left.length + 2) _ _ _ first next

def rejectInputRun (input temporary left result : List (Option Bool)) (state : State) :
    EvalsToInTime machine.step (config (some .rejectInput) state input temporary left result)
      (some (config none (none, false) [] [] [] (none :: result)))
      (input.length + temporary.length + left.length + 3) := by
  induction input generalizing state with
  | nil =>
    have first := oneStep (reject_input_nil state temporary left result)
    have next := rejectTemporaryRun temporary left result (none, state.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      EvalsToInTime.trans _ 1 (temporary.length + left.length + 2) _ _ _ first next
  | cons head tail ih =>
    have first := oneStep (reject_input_cons state head tail temporary left result)
    have next := ih (some head, state.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      EvalsToInTime.trans _ 1 (tail.length + temporary.length + left.length + 3) _ _ _ first next

def rawCompareRun (left : List Bool) (right : List (Option Bool)) (state : State)
    (result : List (Option Bool)) :
    EvalsToInTime machine.step (config (some .compare) state right [] (left.map some) result)
      (some (config none (none, false) [] [] [] (rawLessFrom state.2 left right :: result)))
      (left.length + right.length + 4) := by
  induction left generalizing right state with
  | nil =>
    induction right generalizing state with
    | nil =>
      simp only [rawLessFrom, List.map_nil, List.length_nil]
      have done := oneStep (compare_end state result)
      exact ⟨done.toEvalsTo, done.steps_le_m.trans (by omega)⟩
    | cons head rest ih =>
      cases head with
      | none =>
        have first := oneStep (compare_delimiter state rest [] result)
        have next := rejectInputRun rest [] [] result (some none, state.2)
        simp only [rawLessFrom, List.map_nil, List.length_nil, List.length_cons]
        have joined := EvalsToInTime.trans _ 1 (rest.length + 0 + 0 + 3) _ _ _ first next
        exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by omega)⟩
      | some bit =>
        have first := oneStep (compare_right state bit rest result)
        have next := ih (some (some false), updateLess state.2 false bit)
        simp only [List.map_nil, List.length_nil, Nat.zero_add] at next
        simpa only [List.map_nil, List.length_nil, Nat.zero_add, rawLessFrom,
          List.length_cons, Nat.add_assoc] using EvalsToInTime.trans _ 1 (rest.length + 4) _ _ _ first next
  | cons bit tail ih =>
    cases right with
    | nil =>
      have first := oneStep (compare_left state bit (tail.map some) result)
      have next := ih [] (some (some false), updateLess state.2 bit false)
      simp only [List.length_nil, Nat.add_zero] at next
      simpa only [List.length_cons, List.length_nil, List.map_cons, rawLessFrom,
        Nat.add_zero, Nat.add_assoc] using EvalsToInTime.trans _ 1 (tail.length + 4) _ _ _ first next
    | cons head rest =>
      cases head with
      | none =>
        have first := oneStep (compare_delimiter state rest (some bit :: tail.map some) result)
        have next := rejectInputRun rest [] (some bit :: tail.map some) result (some none, state.2)
        have joined := EvalsToInTime.trans _ 1 (rest.length + 0 + (some bit :: tail.map some).length + 3) _ _ _ first next
        have cleaned : EvalsToInTime machine.step _ _ ((bit :: tail).length + (none :: rest).length + 4) :=
          ⟨joined.toEvalsTo, joined.steps_le_m.trans (by simp only [List.length_cons, List.length_map]; omega)⟩
        simpa only [List.map_cons, rawLessFrom] using cleaned
      | some other =>
        have first := oneStep (compare_pair state bit other (tail.map some) rest result)
        have next := ih rest (some (some false), updateLess state.2 bit other)
        have joined := EvalsToInTime.trans _ 1 (tail.length + rest.length + 4) _ _ _ first next
        have enlarged : EvalsToInTime machine.step _ _ ((bit :: tail).length + (some other :: rest).length + 4) :=
          ⟨joined.toEvalsTo, joined.steps_le_m.trans (by simp only [List.length_cons]; omega)⟩
        simpa only [List.map_cons, rawLessFrom] using enlarged

def framedRawOutputs (left : List Bool) (right : List (Option Bool)) :
    TM2OutputsInTime machine (left.map some ++ none :: right)
      (some [rawLessFrom false left right]) (3 * (left.map some ++ none :: right).length + 4) := by
  have scanned := scanRun left right (none, false) [] [] []
  simp only [List.append_nil] at scanned
  have restored := restoreRun (left.map some).reverse right [] [] (some none, false)
  simp only [List.reverse_reverse, List.append_nil] at restored
  have compared := rawCompareRun left right (none, false) []
  have front := EvalsToInTime.trans _ (left.length + 1) ((left.map some).reverse.length + 1) _ _ _ scanned restored
  have joined := EvalsToInTime.trans _ (((left.map some).reverse.length + 1) + (left.length + 1))
    (left.length + right.length + 4) _ _ _ front compared
  change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
  rw [init_eq, halt_eq]
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by simp only [List.length_append,
    List.length_map, List.length_cons, List.length_reverse]; omega)⟩

def missingDelimiterScan (word : List Bool) (temporary left result : List (Option Bool)) (state : State) :
    EvalsToInTime machine.step (config (some .scan) state (word.map some) temporary left result)
      (some (config (some .rejectTemporary) (none, state.2) [] ((word.map some).reverse ++ temporary) left result))
      (word.length + 1) := by
  induction word generalizing state temporary with
  | nil => simpa using oneStep (scan_nil state temporary left result)
  | cons head tail ih =>
    have first := oneStep (scan_symbol state head (tail.map some) temporary left result)
    have next := ih (some head :: temporary) (some (some head), state.2)
    simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first next

def missingDelimiterOutputs (word : List Bool) :
    TM2OutputsInTime machine (word.map some) (some [none]) (3 * word.length + 4) := by
  have scanned := missingDelimiterScan word [] [] [] (none, false)
  simp only [List.append_nil] at scanned
  have cleaned := rejectTemporaryRun (word.map some).reverse [] [] (none, false)
  have joined := EvalsToInTime.trans _ (word.length + 1)
    ((word.map some).reverse.length + 0 + 2) _ _ _ scanned cleaned
  change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
  rw [init_eq, halt_eq]
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by
    simp only [List.length_reverse, List.length_map, Nat.add_zero]
    omega)⟩

def rawResult (input : List (Option Bool)) : Option Bool :=
  match (WordEqualityMachine.splitPacket input).2 with
  | none => none
  | some right => rawLessFrom false (WordEqualityMachine.splitPacket input).1 right

theorem rawResult_packet (left right : List Bool) :
    rawResult (packet left right) = some (less left right) := by
  rw [rawResult]
  simp only [packet, WordEqualityMachine.splitPacket_words, rawLessFrom_words, less]

theorem rawResult_missing (word : List Bool) : rawResult (word.map some) = none := by
  simp only [rawResult, WordEqualityMachine.splitPacket_missing]

theorem rawLessFrom_has_delimiter (left : List Bool) (right : List (Option Bool))
    (previous : Bool) (malformed : none ∈ right) : rawLessFrom previous left right = none := by
  induction right generalizing left previous with
  | nil => simp only [List.not_mem_nil] at malformed
  | cons head rest ih =>
    cases head with
    | none => cases left <;> simp only [rawLessFrom]
    | some bit =>
      have remaining : none ∈ rest := by simpa using malformed
      cases left with
      | nil => simpa only [rawLessFrom] using ih [] (updateLess previous false bit) remaining
      | cons first tail => simpa only [rawLessFrom] using ih tail (updateLess previous first bit) remaining

theorem rawResult_extra_delimiter (left before : List Bool) (after : List (Option Bool)) :
    rawResult (left.map some ++ none :: (before.map some ++ none :: after)) = none := by
  rw [rawResult]
  simp only [WordEqualityMachine.splitPacket_words]
  exact rawLessFrom_has_delimiter left _ false (by simp)

/-- Every physical input halts, including missing/additional delimiters, with
all temporary fields consumed. Its clock counts actual cleanup transitions. -/
def rawOutputs (input : List (Option Bool)) :
    TM2OutputsInTime machine input (some [rawResult input]) (3 * input.length + 4) := by
  have framing := WordEqualityMachine.splitPacket_framing input
  cases right : (WordEqualityMachine.splitPacket input).2 with
  | none =>
    simp only [right, List.append_nil] at framing
    have lengths : (WordEqualityMachine.splitPacket input).1.length = input.length := by
      simpa only [List.length_map] using (congrArg List.length framing).symm
    have output := missingDelimiterOutputs (WordEqualityMachine.splitPacket input).1
    rw [← framing, lengths] at output
    simpa only [rawResult, right] using output
  | some rest =>
    simp only [right] at framing
    have output := framedRawOutputs (WordEqualityMachine.splitPacket input).1 rest
    rw [← framing] at output
    simpa only [rawResult, right] using output

noncomputable def rawComputable : TM2ComputableInPolyTime
    (fun input : List (Option Bool) => input) (fun result : Option Bool => [result]) rawResult where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C 3 * X + C 4
  outputsFun input := by
    change TM2OutputsInTime machine (input.map id) (some ([rawResult input].map id)) _
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using rawOutputs input

noncomputable def computable : TM2ComputableInPolyTime
    (fun words : List Bool × List Bool => packet words.1 words.2)
    (fun bit : Bool => [some bit]) (fun words => less words.1 words.2) where
  tm := machine
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl (Option Bool)
  time := C 3 * X + C 3
  outputsFun words := by
    change TM2OutputsInTime machine ((packet words.1 words.2).map id)
      (some ([some (less words.1 words.2)].map id)) _
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using outputs words.1 words.2

noncomputable def naturalComputable : TM2ComputableInPolyTime
    (fun values : Nat × Nat => packet (naturalBits values.1) (naturalBits values.2))
    (fun bit : Bool => [some bit]) (fun values => decide (values.1 < values.2)) where
  tm := machine
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl (Option Bool)
  time := C 3 * X + C 3
  outputsFun values := by
    change TM2OutputsInTime machine ((packet (naturalBits values.1) (naturalBits values.2)).map id)
      (some ([some (decide (values.1 < values.2))].map id)) _
    simpa only [less_naturalBits, List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using outputs (naturalBits values.1) (naturalBits values.2)

end Mettapedia.Computability.BinaryWordComparison
