import Mettapedia.Computability.StackMachineComposition
import Mettapedia.Computability.StackMachineRegisters
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Binary arithmetic by finite stack machines

Natural fields use least-significant-bit-first words. Increment scans each
physical bit, propagates a finite carry, and restores the output order through
one temporary stack. Its execution bound includes carry extension.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.BinaryStackArithmetic
open Turing StateTransition Turing.TM2.Stmt
open StackMachineComposition (oneStep)

def increment : List Bool → List Bool
  | [] => [true]
  | false :: rest => true :: rest
  | true :: rest => false :: increment rest

def carryWord (carry : Bool) (word : List Bool) : List Bool :=
  if carry then increment word else word

def bitValue (bit : Bool) : Nat := if bit then 1 else 0

def value (word : List Bool) : Nat := Nat.ofDigits 2 (word.map bitValue)

/-- Canonical binary natural fields, with no leading high zero. -/
def naturalBits (n : Nat) : List Bool := (Nat.digits 2 n).map (fun digit => decide (digit = 1))

theorem naturalBits_digits (n : Nat) : (naturalBits n).map bitValue = Nat.digits 2 n := by
  simp only [naturalBits, List.map_map]
  calc
    _ = (Nat.digits 2 n).map id := by
      apply List.map_congr_left
      intro digit member
      have bound := Nat.digits_lt_base (by decide : 1 < 2) member
      have alternatives : digit = 0 ∨ digit = 1 := by omega
      rcases alternatives with rfl | rfl <;> simp [bitValue]
    _ = _ := List.map_id _

theorem naturalBits_value (n : Nat) : value (naturalBits n) = n := by
  rw [value, naturalBits_digits, Nat.ofDigits_digits]

theorem increment_naturalBits (n : Nat) : increment (naturalBits n) = naturalBits (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases zero : n = 0
      · subst n
        simp [naturalBits, increment]
      have positive : 0 < n := Nat.pos_of_ne_zero zero
      have smaller : n / 2 < n := Nat.div_lt_self positive (by decide)
      have decomposition := Nat.mod_add_div n 2
      rcases Nat.mod_two_eq_zero_or_one n with even | odd
      · have quotientPositive : n / 2 ≠ 0 := by omega
        have original : n = 0 + 2 * (n / 2) := by omega
        have successor : n + 1 = 1 + 2 * (n / 2) := by omega
        have before : naturalBits n = false :: naturalBits (n / 2) := by
          unfold naturalBits
          conv_lhs => rw [original, Nat.digits_add 2 (by decide) 0 (n / 2)
            (by decide) (Or.inr quotientPositive)]
          rfl
        have after : naturalBits (n + 1) = true :: naturalBits (n / 2) := by
          unfold naturalBits
          rw [successor, Nat.digits_add 2 (by decide) 1 (n / 2)
            (by decide) (Or.inl (by decide))]
          rfl
        rw [before, after, increment]
      · have original : n = 1 + 2 * (n / 2) := by omega
        have successor : n + 1 = 0 + 2 * (n / 2 + 1) := by omega
        have before : naturalBits n = true :: naturalBits (n / 2) := by
          unfold naturalBits
          conv_lhs => rw [original, Nat.digits_add 2 (by decide) 1 (n / 2)
            (by decide) (Or.inl (by decide))]
          rfl
        have after : naturalBits (n + 1) = false :: naturalBits (n / 2 + 1) := by
          unfold naturalBits
          rw [successor, Nat.digits_add 2 (by decide) 0 (n / 2 + 1)
            (by decide) (Or.inr (by omega))]
          rfl
        rw [before, after, increment, ih (n / 2) smaller]

theorem increment_value (word : List Bool) : value (increment word) = value word + 1 := by
  induction word with
  | nil => simp [increment, value, bitValue]
  | cons bit rest ih =>
      cases bit
      · simp [increment, value, bitValue, Nat.ofDigits_cons, Nat.add_comm]
      · simp [increment, value, bitValue, Nat.ofDigits_cons] at ih ⊢
        omega

theorem increment_length (word : List Bool) : (increment word).length ≤ word.length + 1 := by
  induction word with
  | nil => simp [increment]
  | cons bit rest ih =>
      cases bit
      · simp [increment]
      · simpa [increment] using Nat.succ_le_succ ih

theorem carryWord_length (carry : Bool) (word : List Bool) :
    (carryWord carry word).length ≤ word.length + 1 := by
  cases carry
  · simp [carryWord]
  · exact increment_length word

/-- The state stores only one carry and the last physical bit. -/
def machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ _ := Bool
  Λ := Bool
  main := false
  σ := Bool × Option Bool
  initialState := (true, none)
  m phase := if phase then
    pop true (fun state symbol => (state.1, symbol))
      (branch (fun state => state.2.isSome)
        (push false (fun state => state.2.getD false) (goto fun _ => true))
        (load (fun _ => (true, none)) halt))
    else
    pop false (fun state symbol => (state.1, symbol))
      (branch (fun state => state.2.isSome)
        (push true (fun state => if state.1 then !(state.2.getD false) else state.2.getD false)
          (load (fun state => (state.1 && state.2.getD false, none)) (goto fun _ => false)))
        (branch Prod.fst
          (push true (fun _ => true) (load (fun _ => (true, none)) (goto fun _ => true)))
          (load (fun _ => (true, none)) (goto fun _ => true))))

def config (phase : Option Bool) (carry : Bool) (last : Option Bool)
    (input temporary : List Bool) : machine.Cfg where
  l := phase
  var := (carry, last)
  stk key := if (show Bool from key) then temporary else input

theorem scan_cons (carry : Bool) (last : Option Bool) (bit : Bool)
    (rest temporary : List Bool) :
    machine.step (config (some false) carry last (bit :: rest) temporary) =
      some (config (some false) (carry && bit) none rest
        ((if carry then !bit else bit) :: temporary)) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem scan_nil (carry : Bool) (last : Option Bool) (temporary : List Bool) :
    machine.step (config (some false) carry last [] temporary) =
      some (config (some true) true none [] (if carry then true :: temporary else temporary)) := by
  cases carry <;> simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  all_goals
    funext key
    cases key <;> simp [Function.update]

theorem restore_cons (carry : Bool) (last : Option Bool) (bit : Bool)
    (input rest : List Bool) :
    machine.step (config (some true) carry last input (bit :: rest)) =
      some (config (some true) carry (some bit) (bit :: input) rest) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem restore_nil (carry : Bool) (last : Option Bool) (input : List Bool) :
    machine.step (config (some true) carry last input []) =
      some (config none true none input []) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]

/-- Carry propagation is measured by actual bit transitions, including the
end-of-word transition that may append a high bit. -/
def scan_run (word temporary : List Bool) (carry : Bool) (last : Option Bool) :
    EvalsToInTime machine.step (config (some false) carry last word temporary)
      (some (config (some true) true none [] ((carryWord carry word).reverse ++ temporary)))
      (word.length + 1) := by
  induction word generalizing temporary carry last with
  | nil =>
      have step := oneStep (scan_nil carry last temporary)
      cases carry <;> simpa [carryWord, increment] using step
  | cons bit rest ih =>
      have started := oneStep (scan_cons carry last bit rest temporary)
      have continued := ih ((if carry then !bit else bit) :: temporary) (carry && bit) none
      have joined := EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ started continued
      cases carry <;> cases bit <;> simpa [carryWord, increment] using joined

/-- Restoration consumes the entire temporary word and restores the original
least-significant-bit-first order. -/
def restore_run (temporary input : List Bool) (carry : Bool) (last : Option Bool) :
    EvalsToInTime machine.step (config (some true) carry last input temporary)
      (some (config none true none (temporary.reverse ++ input) []))
      (temporary.length + 1) := by
  induction temporary generalizing input last with
  | nil => simpa using oneStep (restore_nil carry last input)
  | cons bit rest ih =>
      have started := oneStep (restore_cons carry last bit input rest)
      have continued := ih (bit :: input) (some bit)
      have joined := EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ started continued
      simpa using joined

theorem init_eq (word : List Bool) : initList machine word = config (some false) true none word [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key <;> simp

theorem halt_eq (word : List Bool) : haltList machine word = config none true none word [] := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key <;> simp

/-- The real binary incrementer uses at most twice the input bit length plus
three transitions, irrespective of the represented natural's magnitude. -/
def outputs (word : List Bool) :
    TM2OutputsInTime machine word (some (increment word)) (2 * word.length + 3) := by
  have scanned := scan_run word [] true none
  simp only [carryWord, List.append_nil] at scanned
  have restored := restore_run (increment word).reverse [] true none
  have joined := EvalsToInTime.trans _ (word.length + 1)
    ((increment word).reverse.length + 1) _ _ _ scanned restored
  change EvalsToInTime _ (initList machine word) (some (haltList machine (increment word))) _
  rw [init_eq, halt_eq]
  have timeBound : (increment word).reverse.length + 1 + (word.length + 1) ≤
      2 * word.length + 3 := by
    have lengthBound := increment_length word
    simp only [List.length_reverse]
    omega
  have bounded : EvalsToInTime machine.step
      (config (some false) true none word []) (some (config none true none (increment word) []))
      (2 * word.length + 3) :=
    { steps := joined.steps
      evals_in_steps := by simpa using joined.evals_in_steps
      steps_le_m := joined.steps_le_m.trans timeBound }
  exact bounded

/-- Chronological natural addresses advance by bit operations, including a
carry through every low bit; the clock depends on the encoded address length. -/
def naturalOutputs (n : Nat) : TM2OutputsInTime machine (naturalBits n)
    (some (naturalBits (n + 1))) (2 * (naturalBits n).length + 3) := by
  simpa only [increment_naturalBits] using outputs (naturalBits n)

/-- A polynomial clock attached to the implemented word operation. -/
noncomputable def computable : TM2ComputableInPolyTime
    (fun word : List Bool => word) (fun word : List Bool => word) increment where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun word := by
    change TM2OutputsInTime machine (word.map id) (some ((increment word).map id)) _
    simp only [List.map_id_fun]
    simpa using outputs word

/-- The same implementation computes successor on canonical encoded naturals,
without iterating up to their represented value. -/
noncomputable def naturalComputable : TM2ComputableInPolyTime
    naturalBits naturalBits Nat.succ where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun n := by
    change TM2OutputsInTime machine ((naturalBits n).map id)
      (some ((naturalBits (Nat.succ n)).map id)) _
    simp only [List.map_id_fun]
    simpa using naturalOutputs n

namespace MarkerCounting
open Mettapedia.Computability Polynomial
open Turing.TM2.Stmt

/-- The caller's physical child markers remain distinct from the original
binary incrementer's two bit stacks. -/
abbrev Cells := StackMachineRegisters.withStackAlphabet (fun _ : Bool => Bool) Unit
instance (key : Option Bool) : Fintype (Cells key) := by
  cases key <;> infer_instance

inductive Phase where
  | count | increment (phase : Bool)
  deriving DecidableEq, Fintype
abbrev Control := (Bool × Option Bool) × Option Unit

def initial : Control := ((true, none), none)

/-- Each admitted child invokes the existing bitwise increment program. No
represented-number iteration or dynamic integer register is introduced. -/
def program : Phase → TM2.Stmt Cells Phase Control
  | .count => pop none (fun state marker => (state.1, marker))
      (branch (fun state => state.2.isSome)
        (load (fun state => ((true, none), state.2)) (goto fun _ => .increment false))
        (load (fun _ => initial) halt))
  | .increment phase => StackMachineRegisters.withStack id
      (StackMachineRegisters.returning Phase.increment (fun (_ : Option Unit) => .count)
        (BinaryStackArithmetic.machine.m phase))

abbrev Cfg := TM2.Cfg Cells Phase Control

def step : Cfg → Option Cfg := TM2.step program

def machine : FinTM2 where
  K := Option Bool
  k₀ := none
  k₁ := some false
  Γ := Cells
  Λ := Phase
  main := .count
  σ := Control
  initialState := initial
  m := program

theorem machine_step : machine.step = step := rfl

def config (phase : Option Phase) (state : Control) (markers : List Unit)
    (bits temporary : List Bool) : Cfg where
  l := phase
  var := state
  stk key := match key with
    | none => markers
    | some false => bits
    | some true => temporary

def embed (markers : List Unit) (lastMarker : Option Unit)
    (source : BinaryStackArithmetic.machine.Cfg) : Cfg :=
  StackMachineRegisters.withStackConfig id markers
    (StackMachineRegisters.returningConfig Phase.increment
      (fun (_ : Option Unit) => .count) lastMarker source)

/-- The embedded incrementer executes exactly its original transition. -/
theorem increment_step (markers : List Unit) (lastMarker : Option Unit)
    (before after : BinaryStackArithmetic.machine.Cfg)
    (executed : BinaryStackArithmetic.machine.step before = some after) :
    step (embed markers lastMarker before) = some (embed markers lastMarker after) := by
  cases before with
  | mk phase state contents =>
      cases phase with
      | none => simp [FinTM2.step, BinaryStackArithmetic.machine, TM2.step] at executed
      | some phase =>
          simp only [FinTM2.step, TM2.step] at executed
          have identified := Option.some.inj executed
          subst after
          simp only [step, embed, StackMachineRegisters.withStackConfig,
            StackMachineRegisters.returningConfig, Option.elim_some, Option.map_some,
            TM2.step, id_eq, program]
          rw [StackMachineRegisters.stepAux_withStack,
            StackMachineRegisters.stepAux_returning]
          rfl

theorem embed_config (markers : List Unit) (lastMarker : Option Unit)
    (phase : Option Bool) (carry : Bool) (last : Option Bool) (bits temporary : List Bool) :
    embed markers lastMarker (BinaryStackArithmetic.config phase carry last bits temporary) =
      config (some (phase.elim .count Phase.increment)) ((carry, last), lastMarker) markers bits temporary := by
  simp only [embed, StackMachineRegisters.withStackConfig, StackMachineRegisters.returningConfig,
    BinaryStackArithmetic.config, config]
  congr 1
  funext key
  cases key with
  | none => rfl
  | some key => cases key <;> rfl

noncomputable def scanRun (markers : List Unit) (lastMarker : Option Unit)
    (word temporary : List Bool) (carry : Bool) (last : Option Bool) :
    EvalsToInTime step
      (embed markers lastMarker (BinaryStackArithmetic.config (some false) carry last word temporary))
      (some (embed markers lastMarker (BinaryStackArithmetic.config (some true) true none []
        ((BinaryStackArithmetic.carryWord carry word).reverse ++ temporary))))
      (word.length + 1) := by
  exact StackMachineComposition.lift_execution BinaryStackArithmetic.machine.step step
    (embed markers lastMarker) (increment_step markers lastMarker)
    (BinaryStackArithmetic.scan_run word temporary carry last)

noncomputable def restoreRun (markers : List Unit) (lastMarker : Option Unit)
    (temporary bits : List Bool) (carry : Bool) (last : Option Bool) :
    EvalsToInTime step
      (embed markers lastMarker (BinaryStackArithmetic.config (some true) carry last bits temporary))
      (some (embed markers lastMarker (BinaryStackArithmetic.config none true none
        (temporary.reverse ++ bits) []))) (temporary.length + 1) := by
  exact StackMachineComposition.lift_execution BinaryStackArithmetic.machine.step step
    (embed markers lastMarker) (increment_step markers lastMarker)
    (BinaryStackArithmetic.restore_run temporary bits carry last)

noncomputable def incrementRun (markers : List Unit) (lastMarker : Option Unit) (value : Nat) :
    EvalsToInTime step
      (config (some (.increment false)) ((true, none), lastMarker) markers
        (BinaryStackArithmetic.naturalBits value) [])
      (some (config (some .count) ((true, none), lastMarker) markers
        (BinaryStackArithmetic.naturalBits (value + 1)) []))
      (2 * (BinaryStackArithmetic.naturalBits value).length + 3) := by
  have scan := scanRun markers lastMarker (BinaryStackArithmetic.naturalBits value) [] true none
  simp only [BinaryStackArithmetic.carryWord, List.append_nil] at scan
  have restore := restoreRun markers lastMarker
    (BinaryStackArithmetic.increment (BinaryStackArithmetic.naturalBits value)).reverse [] true none
  have joined := EvalsToInTime.trans _ _ _ _ _ _ scan restore
  rw [BinaryStackArithmetic.increment_naturalBits] at joined
  simp only [List.reverse_reverse, List.append_nil, embed_config, Option.elim_some,
    Option.elim_none, List.length_reverse] at joined
  have growth := BinaryStackArithmetic.increment_length (BinaryStackArithmetic.naturalBits value)
  rw [BinaryStackArithmetic.increment_naturalBits] at growth
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by omega)⟩

theorem count_cons (state : Control) (markers : List Unit) (bits temporary : List Bool) :
    step (config (some .count) state (() :: markers) bits temporary) =
      some (config (some (.increment false)) ((true, none), some ()) markers bits temporary) := by
  simp [step, program, config, TM2.step, TM2.stepAux]
  funext key
  cases key with
  | none => simp [Function.update]
  | some key => cases key <;> simp [Function.update]

theorem count_nil (state : Control) (bits temporary : List Bool) :
    step (config (some .count) state [] bits temporary) =
      some (config none initial [] bits temporary) := by
  simp [step, program, config, TM2.step, TM2.stepAux]

noncomputable def countRun (markers : List Unit) (value : Nat) (lastMarker : Option Unit) :
    EvalsToInTime step
      (config (some .count) ((true, none), lastMarker) markers
        (BinaryStackArithmetic.naturalBits value) [])
      (some (config none initial []
        (BinaryStackArithmetic.naturalBits (value + markers.length)) []))
      (markers.length * (2 * (value + markers.length) + 4) + 1) := by
  induction markers generalizing value lastMarker with
  | nil => simpa only [List.length_nil, Nat.add_zero, Nat.zero_mul, Nat.zero_add] using
      StackMachineComposition.oneStep (count_nil ((true, none), lastMarker) (BinaryStackArithmetic.naturalBits value) [])
  | cons marker markers ih =>
      cases marker
      have start := StackMachineComposition.oneStep
        (count_cons ((true, none), lastMarker) markers (BinaryStackArithmetic.naturalBits value) [])
      have incremented := incrementRun markers (some ()) value
      have rest := ih (value + 1) (some ())
      have joined := EvalsToInTime.trans _ _ _ _ _ _ start incremented
      have joined := EvalsToInTime.trans _ _ _ _ _ _ joined rest
      have digits : (BinaryStackArithmetic.naturalBits value).length ≤ value := by
        rw [BinaryStackArithmetic.naturalBits, List.length_map]
        apply (Nat.digits_length_le_iff (by decide : 1 < 2) value).mpr
        exact Nat.lt_two_pow_self
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (show EvalsToInTime step _ _
          ((markers.length + 1) * (2 * (value + (markers.length + 1)) + 4) + 1) from
          ⟨joined.toEvalsTo, joined.steps_le_m.trans (by nlinarith)⟩)

/-- Constructor arity is computed from the physically retained child
occurrences, including duplicates. The clock counts each bit increment. -/
noncomputable def outputs (count : Nat) : TM2OutputsInTime machine (List.replicate count ())
    (some (BinaryStackArithmetic.naturalBits count)) (count * (2 * count + 4) + 1) := by
  have run := countRun (List.replicate count ()) 0 none
  have inputEq : initList machine (List.replicate count ()) =
      config (some .count) initial (List.replicate count ()) [] [] := by
    simp only [initList, machine, config]
    congr 1
    funext key
    cases key with
    | none => rfl
    | some key => cases key <;> rfl
  have outputEq : haltList machine (BinaryStackArithmetic.naturalBits count) =
      config none initial [] (BinaryStackArithmetic.naturalBits count) [] := by
    simp only [haltList, machine, config]
    congr 1
    funext key
    cases key with
    | none => rfl
    | some key => cases key <;> rfl
  change EvalsToInTime step (initList machine (List.replicate count ()))
    (some (haltList machine (BinaryStackArithmetic.naturalBits count))) _
  rw [inputEq, outputEq]
  simpa only [BinaryStackArithmetic.naturalBits, Nat.digits_zero, List.map_nil,
    List.length_replicate, Nat.zero_add, initial] using run

noncomputable def realization : TM2ComputableInPolyTime
    (fun count : Nat => List.replicate count ()) BinaryStackArithmetic.naturalBits id where
  tm := machine
  inputAlphabet := Equiv.refl Unit
  outputAlphabet := Equiv.refl Bool
  time := X * (C 2 * X + C 4) + C 1
  outputsFun count := by
    change TM2OutputsInTime machine ((List.replicate count ()).map id)
      (some ((BinaryStackArithmetic.naturalBits count).map id)) _
    simp only [List.map_id_fun]
    simpa only [id_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, List.length_replicate] using outputs count

end MarkerCounting

end Mettapedia.Computability.BinaryStackArithmetic
