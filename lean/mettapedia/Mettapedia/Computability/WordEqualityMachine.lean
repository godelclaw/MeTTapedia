import Mettapedia.Computability.StackMachineComposition

/-!
# Equality of complete finite-alphabet words

Two words are framed by a delimiter outside the data alphabet. The machine
scans and restores the first word, compares every symbol of the second, and
clears its internal stacks before returning a Boolean. Symbols and control
registers are finite; dynamic words remain on stacks.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.WordEqualityMachine
open Turing StateTransition Polynomial
open Turing.TM2.Stmt

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ]

inductive Stack where
  | input | temporary | left | result
  deriving DecidableEq, Fintype

inductive Phase where
  | scan | restore | compare | drain
  deriving DecidableEq, Fintype

abbrev Symbol (Γ : Type) := Option Γ

abbrev Alphabet (Γ : Type) : Stack → Type
  | .result => Bool
  | _ => Symbol Γ

def packet (left right : List Γ) : List (Symbol Γ) :=
  left.map some ++ none :: right.map some

def symbolMatch : Option (Symbol Γ) → Option (Symbol Γ) → Bool
  | some (some left), some (some right) => decide (left = right)
  | _, _ => false

def machine (Γ : Type) [Fintype Γ] [DecidableEq Γ] : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := Alphabet Γ
  Λ := Phase
  main := .scan
  σ := Option (Symbol Γ) × Bool
  initialState := (none, true)
  m phase := match phase with
    | .scan => pop .input (fun state value => (value, state.2))
        (branch (fun state => state.1 = some none)
          (goto fun _ => .restore)
          (branch (fun state => state.1.isSome)
            (push .temporary (fun state => state.1.getD none) (goto fun _ => .scan))
            (load (fun _ => (none, false)) (goto fun _ => .restore))))
    | .restore => pop .temporary (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome)
          (push .left (fun state => state.1.getD none) (goto fun _ => .restore))
          (goto fun _ => .compare))
    | .compare => pop .input (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome)
          (pop .left (fun state value => (none, state.2 && symbolMatch state.1 value))
            (goto fun _ => .compare))
          (goto fun _ => .drain))
    | .drain => pop .left (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome)
          (load (fun _ => (none, false)) (goto fun _ => .drain))
          (push .result (fun state => state.2) (load (fun _ => (none, true)) halt)))

def config (phase : Option Phase) (state : Option (Symbol Γ) × Bool)
    (input temporary left : List (Symbol Γ)) (result : List Bool) : (machine Γ).Cfg where
  l := phase
  var := state
  stk key := match (show Stack from key) with
    | .input => input | .temporary => temporary | .left => left | .result => result

local macro "check_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  all_goals first
    | (funext key; cases key <;> simp [Function.update])
    | (congr 2; funext key; cases key <;> simp [Function.update])))

theorem scan_symbol (state : Option (Symbol Γ) × Bool) (head : Γ)
    (tail temporary left : List (Symbol Γ)) (result : List Bool) :
    (machine Γ).step (config (some .scan) state (some head :: tail) temporary left result) =
      some (config (some .scan) (some (some head), state.2) tail (some head :: temporary) left result) := by
  check_step

theorem scan_delimiter (state : Option (Symbol Γ) × Bool)
    (tail temporary left : List (Symbol Γ)) (result : List Bool) :
    (machine Γ).step (config (some .scan) state (none :: tail) temporary left result) =
      some (config (some .restore) (some none, state.2) tail temporary left result) := by
  check_step

theorem scan_nil (state : Option (Symbol Γ) × Bool)
    (temporary left : List (Symbol Γ)) (result : List Bool) :
    (machine Γ).step (config (some .scan) state [] temporary left result) =
      some (config (some .restore) (none, false) [] temporary left result) := by
  check_step

theorem restore_cons (state : Option (Symbol Γ) × Bool) (head : Symbol Γ)
    (input tail left : List (Symbol Γ)) (result : List Bool) :
    (machine Γ).step (config (some .restore) state input (head :: tail) left result) =
      some (config (some .restore) (some head, state.2) input tail (head :: left) result) := by
  check_step

theorem restore_nil (state : Option (Symbol Γ) × Bool)
    (input left : List (Symbol Γ)) (result : List Bool) :
    (machine Γ).step (config (some .restore) state input [] left result) =
      some (config (some .compare) (none, state.2) input [] left result) := by
  check_step

theorem compare_cons_cons (state : Option (Symbol Γ) × Bool) (right : Symbol Γ) (left : Γ)
    (rightTail leftTail : List (Symbol Γ)) (result : List Bool) :
    (machine Γ).step (config (some .compare) state (right :: rightTail) [] (some left :: leftTail) result) =
      some (config (some .compare) (none, state.2 && decide (right = some left)) rightTail [] leftTail result) := by
  have match_eq : symbolMatch (some right) (some (some left)) = decide (right = some left) := by
    cases right <;> simp [symbolMatch]
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux, match_eq]
  funext key
  cases key <;> simp [Function.update]

theorem compare_cons_nil (state : Option (Symbol Γ) × Bool) (right : Symbol Γ)
    (tail : List (Symbol Γ)) (result : List Bool) :
    (machine Γ).step (config (some .compare) state (right :: tail) [] [] result) =
      some (config (some .compare) (none, false) tail [] [] result) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux, symbolMatch]
  funext key
  cases key <;> simp [Function.update]

theorem compare_nil (state : Option (Symbol Γ) × Bool) (left : List (Symbol Γ)) (result : List Bool) :
    (machine Γ).step (config (some .compare) state [] [] left result) =
      some (config (some .drain) (none, state.2) [] [] left result) := by
  check_step

theorem drain_cons (state : Option (Symbol Γ) × Bool) (head : Symbol Γ)
    (tail : List (Symbol Γ)) (result : List Bool) :
    (machine Γ).step (config (some .drain) state [] [] (head :: tail) result) =
      some (config (some .drain) (none, false) [] [] tail result) := by
  check_step

theorem drain_nil (state : Option (Symbol Γ) × Bool) (result : List Bool) :
    (machine Γ).step (config (some .drain) state [] [] [] result) =
      some (config none (none, true) [] [] [] (state.2 :: result)) := by
  check_step

def within {State : Type} {step : State → Option State} {before : State} {after : Option State}
    {bound enlarged : Nat} (run : EvalsToInTime step before after bound) (le : bound ≤ enlarged) :
    EvalsToInTime step before after enlarged :=
  ⟨run.toEvalsTo, run.steps_le_m.trans le⟩

def scanRun (left : List Γ) (right : List (Symbol Γ)) (state : Option (Symbol Γ) × Bool)
    (temporary stored : List (Symbol Γ)) (result : List Bool) :
    EvalsToInTime (machine Γ).step
      (config (some .scan) state (left.map some ++ none :: right) temporary stored result)
      (some (config (some .restore) (some none, state.2) right
        ((left.map some).reverse ++ temporary) stored result)) (left.length + 1) := by
  induction left generalizing state temporary with
  | nil => simpa using StackMachineComposition.oneStep (scan_delimiter state right temporary stored result)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep (scan_symbol state head
      (tail.map some ++ none :: right) temporary stored result)
    have rest := ih (some (some head), state.2) (some head :: temporary)
    simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def restoreRun (temporary input left : List (Symbol Γ)) (state : Option (Symbol Γ) × Bool) (result : List Bool) :
    EvalsToInTime (machine Γ).step
      (config (some .restore) state input temporary left result)
      (some (config (some .compare) (none, state.2) input [] (temporary.reverse ++ left) result))
      (temporary.length + 1) := by
  induction temporary generalizing state left with
  | nil => simpa using StackMachineComposition.oneStep (restore_nil state input left result)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep (restore_cons state head input tail left result)
    have rest := ih (head :: left) (some head, state.2)
    simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def drainRun (left : List (Symbol Γ)) (state : Option (Symbol Γ) × Bool) (result : List Bool) :
    EvalsToInTime (machine Γ).step
      (config (some .drain) state [] [] left result)
      (some (config none (none, true) [] [] [] ((state.2 && decide (left = [])) :: result)))
      (left.length + 1) := by
  induction left generalizing state with
  | nil => simpa using StackMachineComposition.oneStep (drain_nil state result)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep (drain_cons state head tail result)
    have rest := ih (none, false)
    simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def compareRun (left : List Γ) (right : List (Symbol Γ))
    (state : Option (Symbol Γ) × Bool) (result : List Bool) :
    EvalsToInTime (machine Γ).step
      (config (some .compare) state right [] (left.map some) result)
      (some (config none (none, true) [] [] [] ((state.2 && decide (left.map some = right)) :: result)))
      (left.length + right.length + 2) := by
  induction right generalizing left state with
  | nil =>
    have first := StackMachineComposition.oneStep (compare_nil state (left.map some) result)
    have rest := drainRun (left.map some) (none, state.2) result
    simpa using EvalsToInTime.trans _ 1 ((left.map some).length + 1) _ _ _ first rest
  | cons head tail ih =>
    cases left with
    | nil =>
      have first := StackMachineComposition.oneStep (compare_cons_nil state head tail result)
      have rest := ih [] (none, false)
      simpa using EvalsToInTime.trans _ 1 (0 + tail.length + 2) _ _ _ first rest
    | cons first rest =>
      have begin := StackMachineComposition.oneStep (compare_cons_cons state head first tail (rest.map some) result)
      have later := ih rest (none, state.2 && decide (head = some first))
      have joined := EvalsToInTime.trans _ 1 (rest.length + tail.length + 2) _ _ _ begin later
      have bound : rest.length + tail.length + 2 + 1 ≤ (first :: rest).length + (head :: tail).length + 2 := by simp; omega
      have enlarged := within joined bound
      simpa [Bool.and_assoc, eq_comm] using enlarged


private theorem init_eq (input : List (Symbol Γ)) :
    initList (machine Γ) input = config (some .scan) (none, true) input [] [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key <;> simp

private theorem halt_eq (value : Bool) :
    haltList (machine Γ) [value] = config none (none, true) [] [] [] [value] := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key <;> simp

/-- Every symbol of a framed second field is compared. A delimiter inside
that field is unequal to every data symbol, and therefore refuses the packet. -/
def framedOutputs (left : List Γ) (right : List (Symbol Γ)) :
    TM2OutputsInTime (machine Γ) (left.map some ++ none :: right)
      (some [decide (left.map some = right)]) (3 * left.length + right.length + 4) := by
  have scanned := scanRun left right (none, true) [] [] []
  simp only [List.append_nil] at scanned
  have restored := restoreRun (left.map some).reverse right [] (some none, true) []
  simp only [List.reverse_reverse, List.append_nil] at restored
  have compared := compareRun left right (none, true) []
  have first := EvalsToInTime.trans _ (left.length + 1)
    ((left.map some).reverse.length + 1) _ _ _ scanned restored
  have joined := EvalsToInTime.trans _
    (((left.map some).reverse.length + 1) + (left.length + 1))
    (left.length + right.length + 2) _ _ _ first compared
  change EvalsToInTime _ (initList (machine Γ) _)
    (some (haltList (machine Γ) _)) _
  rw [init_eq, halt_eq]
  simpa [Nat.succ_mul, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

/-- Full word equality is realized without decoding the words into registers. -/
def outputs (left right : List Γ) :
    TM2OutputsInTime (machine Γ) (packet left right) (some [decide (left = right)])
      (3 * left.length + right.length + 4) := by
  have exactField : left.map some = right.map some ↔ left = right :=
    (List.map_injective_iff.mpr (Option.some_injective Γ)).eq_iff
  simpa [packet, exactField] using framedOutputs left (right.map some)

omit [Fintype Γ] [DecidableEq Γ] in
theorem packet_length (left right : List Γ) :
    (packet left right).length = left.length + right.length + 1 := by simp [packet]; omega

noncomputable def computable : TM2ComputableInPolyTime
    (fun words : List Γ × List Γ => packet words.1 words.2)
    (fun result : Bool => [result])
    (fun words : List Γ × List Γ => decide (words.1 = words.2)) where
  tm := machine Γ
  inputAlphabet := Equiv.refl (Symbol Γ)
  outputAlphabet := Equiv.refl Bool
  time := C 3 * X + C 1
  outputsFun words := by
    change TM2OutputsInTime (machine Γ) ((packet words.1 words.2).map id)
      (some ([decide (words.1 = words.2)].map id)) _
    simp only [List.map_id_fun]
    apply within (outputs words.1 words.2)
    simp only [eval_add, eval_mul, eval_C, eval_X, packet_length]
    omega

def missingDelimiterScan (word : List Γ) (temporary left : List (Symbol Γ))
    (state : Option (Symbol Γ) × Bool) (result : List Bool) :
    EvalsToInTime (machine Γ).step
      (config (some .scan) state (word.map some) temporary left result)
      (some (config (some .restore) (none, false) [] ((word.map some).reverse ++ temporary) left result))
      (word.length + 1) := by
  induction word generalizing state temporary with
  | nil => simpa using StackMachineComposition.oneStep (scan_nil state temporary left result)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep (scan_symbol state head (tail.map some) temporary left result)
    have rest := ih (some head :: temporary) (some (some head), state.2)
    simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

/-- Missing delimiters are refused after scanning and clearing every symbol. -/
def missingDelimiterOutputs (word : List Γ) :
    TM2OutputsInTime (machine Γ) (word.map some) (some [false]) (3 * word.length + 4) := by
  have scanned := missingDelimiterScan word [] [] (none, true) []
  simp only [List.append_nil] at scanned
  have restored := restoreRun (word.map some).reverse [] [] (none, false) []
  simp only [List.reverse_reverse, List.append_nil] at restored
  have compared := compareRun word [] (none, false) []
  have first := EvalsToInTime.trans _ (word.length + 1)
    ((word.map some).reverse.length + 1) _ _ _ scanned restored
  have joined := EvalsToInTime.trans _
    (((word.map some).reverse.length + 1) + (word.length + 1))
    (word.length + 0 + 2) _ _ _ first compared
  change EvalsToInTime _ (initList (machine Γ) _)
    (some (haltList (machine Γ) _)) _
  rw [init_eq, halt_eq]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add, Nat.succ_mul] using joined

/-- Finite framing classification. The right-hand field retains the original
symbols, including malformed additional delimiters. -/
def splitPacket : List (Symbol Γ) → List Γ × Option (List (Symbol Γ))
  | [] => ([], none)
  | none :: rest => ([], some rest)
  | some head :: rest =>
    let fields := splitPacket rest
    (head :: fields.1, fields.2)

omit [Fintype Γ] [DecidableEq Γ] in
theorem splitPacket_words (left : List Γ) (right : List (Symbol Γ)) :
    splitPacket (left.map some ++ none :: right) = (left, some right) := by
  induction left with
  | nil => rfl
  | cons head tail ih => simpa [splitPacket] using congrArg (fun fields : List Γ × Option (List (Symbol Γ)) => (head :: fields.1, fields.2)) ih

omit [Fintype Γ] [DecidableEq Γ] in
theorem splitPacket_missing (word : List Γ) : splitPacket (word.map some) = (word, none) := by
  induction word with
  | nil => rfl
  | cons head tail ih => simp [splitPacket, ih]

omit [Fintype Γ] [DecidableEq Γ] in
theorem splitPacket_framing (word : List (Symbol Γ)) :
    word = (splitPacket word).1.map some ++
      (match (splitPacket word).2 with | none => [] | some rest => none :: rest) := by
  induction word with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | none => rfl
    | some value => simpa [splitPacket] using congrArg (some value :: ·) ih

def result (word : List (Symbol Γ)) : Bool :=
  match (splitPacket word).2 with
  | none => false
  | some right => decide ((splitPacket word).1.map some = right)

omit [Fintype Γ] in
theorem result_packet (left right : List Γ) : result (packet left right) = decide (left = right) := by
  have exactField : left.map some = right.map some ↔ left = right :=
    (List.map_injective_iff.mpr (Option.some_injective Γ)).eq_iff
  simp [result, packet, splitPacket_words, exactField]

omit [Fintype Γ] in
theorem result_missing (word : List Γ) : result (word.map some) = false := by
  simp [result, splitPacket_missing]

omit [Fintype Γ] in
theorem result_extra_delimiter (left before : List Γ) (after : List (Symbol Γ)) :
    result (left.map some ++ none :: before.map some ++ none :: after) = false := by
  have different : left.map some ≠ before.map some ++ none :: after := by
    intro same
    have contains : (none : Symbol Γ) ∈ before.map some ++ none :: after := by simp
    rw [← same] at contains
    simp at contains
  simp [result, splitPacket_words, different]

/-- All raw packets halt within a linear bound, including missing and repeated
field delimiters. This theorem charges the actual input symbols on refusal. -/
def rawOutputs (word : List (Symbol Γ)) :
    TM2OutputsInTime (machine Γ) word (some [result word]) (3 * word.length + 4) := by
  have framing := splitPacket_framing word
  cases right : (splitPacket word).2 with
  | none =>
    have exactWord : word = (splitPacket word).1.map some := by simpa [right] using framing
    have exactResult : result word = false := by simp [result, right]
    have lengths : word.length = (splitPacket word).1.length := by
      simpa only [List.length_map] using congrArg List.length exactWord
    rw [exactResult]
    have executed := missingDelimiterOutputs (splitPacket word).1
    rw [← exactWord] at executed
    change EvalsToInTime (machine Γ).step (initList (machine Γ) word)
      (some (haltList (machine Γ) [false])) _ at executed ⊢
    exact within executed (by omega)
  | some tail =>
    have exactWord : word = (splitPacket word).1.map some ++ none :: tail := by simpa [right] using framing
    have exactResult : result word = decide ((splitPacket word).1.map some = tail) := by simp [result, right]
    have lengths : word.length = (splitPacket word).1.length + (tail.length + 1) := by
      simpa only [List.length_map, List.length_append, List.length_cons] using congrArg List.length exactWord
    rw [exactResult]
    have executed := framedOutputs (splitPacket word).1 tail
    rw [← exactWord] at executed
    change EvalsToInTime (machine Γ).step (initList (machine Γ) word)
      (some (haltList (machine Γ) [decide ((splitPacket word).1.map some = tail)])) _ at executed ⊢
    exact within executed (by omega)

noncomputable def rawComputable : TM2ComputableInPolyTime
    (id : List (Symbol Γ) → List (Symbol Γ)) (fun value : Bool => [value]) result where
  tm := machine Γ
  inputAlphabet := Equiv.refl (Symbol Γ)
  outputAlphabet := Equiv.refl Bool
  time := C 3 * X + C 4
  outputsFun word := by
    change TM2OutputsInTime (machine Γ) ((id word).map id)
      (some ([result word].map id)) _
    simpa only [List.map_id_fun, id_eq, eval_add, eval_mul, eval_C, eval_X] using rawOutputs word


omit [Fintype Γ] in
theorem result_true_iff (word : List (Symbol Γ)) :
    result word = true ↔ ∃ data : List Γ, word = packet data data := by
  constructor
  · intro accepted
    have framing := splitPacket_framing word
    cases right : (splitPacket word).2 with
    | none => simp [result, right] at accepted
    | some tail =>
      have exactFields : (splitPacket word).1.map some = tail := by
        simpa [result, right] using accepted
      refine ⟨(splitPacket word).1, ?_⟩
      simpa [packet, right, ← exactFields] using framing
  · rintro ⟨data, rfl⟩
    simp [result_packet]

noncomputable def sameOutputs (word : List Γ) :
    TM2OutputsInTime (machine Γ) (packet word word) (some [true])
      (3 * (packet word word).length + 1) := by
  have checked := computable.outputsFun (word, word)
  change TM2OutputsInTime (machine Γ) ((packet word word).map id)
    (some ([decide (word = word)].map id)) ((C 3 * X + C 1).eval (packet word word).length) at checked
  simpa only [List.map_id_fun, id_eq, decide_true, eval_add, eval_mul, eval_C, eval_X] using checked

noncomputable def differentOutputs (left right : List Γ) (different : left ≠ right) :
    TM2OutputsInTime (machine Γ) (packet left right) (some [false])
      (3 * (packet left right).length + 1) := by
  have checked := computable.outputsFun (left, right)
  change TM2OutputsInTime (machine Γ) ((packet left right).map id)
    (some ([decide (left = right)].map id)) ((C 3 * X + C 1).eval (packet left right).length) at checked
  simpa only [List.map_id_fun, id_eq, different, decide_false, eval_add, eval_mul, eval_C, eval_X] using checked

noncomputable def extraDelimiterOutputs (left before : List Γ) (after : List (Symbol Γ)) :
    TM2OutputsInTime (machine Γ) (left.map some ++ none :: before.map some ++ none :: after)
      (some [false]) (3 * (left.map some ++ none :: before.map some ++ none :: after).length + 4) := by
  simpa only [result_extra_delimiter] using rawOutputs
    (left.map some ++ none :: before.map some ++ none :: after)

end Mettapedia.Computability.WordEqualityMachine
