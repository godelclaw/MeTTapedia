import Mettapedia.Computability.WordTemplateMachine

/-!
# Removing a fixed suffix from delimiter-framed words

A two-symbol finite buffer delays output until a field delimiter arrives.
Every field must end in the supplied fixed suffix. The machine copies the
remaining original symbols in order, retains every field delimiter, and
returns a distinct success or refusal tag. Dynamic fields live on stacks.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.FramedWordSuffixRemoval
open Turing StateTransition Turing.TM2.Stmt

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ]

abbrev Symbol := Option Γ
abbrev Output := Option Γ ⊕ Bool
abbrev State := Option (Option Γ) × Option Γ × Option Γ × Option (Output (Γ := Γ))

inductive Stack where
  | input | output | result
  deriving DecidableEq, Fintype

def Alphabet : Stack → Type
  | .input => Symbol (Γ := Γ)
  | .output | .result => Output (Γ := Γ)

instance (key : Stack) : Fintype (Alphabet (Γ := Γ) key) := by
  cases key <;> dsimp [Alphabet] <;> infer_instance

inductive Phase where
  | read | reverse | finish | rejectInput | rejectOutput | refuse
  deriving DecidableEq, Fintype

def initial : State (Γ := Γ) := (none, none, none, none)

def program (first last : Γ) : Phase → TM2.Stmt (Alphabet (Γ := Γ)) Phase (State (Γ := Γ))
  | .read => pop .input (fun state cell => (cell, state.2))
      (branch (fun state => state.1.isNone)
        (branch (fun state => state.2.1.isNone && state.2.2.1.isNone)
          (goto fun _ => .reverse) (goto fun _ => .rejectInput))
        (branch (fun state => (state.1.getD none).isSome)
          (branch (fun state => state.2.1.isNone)
            (load (fun state => (none, state.1.getD none, none, none)) (goto fun _ => .read))
            (branch (fun state => state.2.2.1.isNone)
              (load (fun state => (none, state.2.1, state.1.getD none, none)) (goto fun _ => .read))
              (push .output (fun state => .inl state.2.1)
                (load (fun state => (none, state.2.2.1, state.1.getD none, none)) (goto fun _ => .read)))))
          (branch (fun state => decide (state.2.1 = some first ∧ state.2.2.1 = some last))
            (push .output (fun _ => .inl none) (load (fun _ => initial) (goto fun _ => .read)))
            (goto fun _ => .rejectInput))))
  | .reverse => pop .output (fun state cell => (state.1, state.2.1, state.2.2.1, cell))
      (branch (fun state => state.2.2.2.isSome)
        (push .result (fun state => state.2.2.2.getD (.inr false)) (goto fun _ => .reverse))
        (goto fun _ => .finish))
  | .finish => push .result (fun _ => .inr true) (load (fun _ => initial) halt)
  | .rejectInput => pop .input (fun state cell => (cell, state.2))
      (branch (fun state => state.1.isSome) (goto fun _ => .rejectInput) (goto fun _ => .rejectOutput))
  | .rejectOutput => pop .output (fun state cell => (state.1, state.2.1, state.2.2.1, cell))
      (branch (fun state => state.2.2.2.isSome) (goto fun _ => .rejectOutput) (goto fun _ => .refuse))
  | .refuse => push .result (fun _ => .inr false) (load (fun _ => initial) halt)

def machine (first last : Γ) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := Alphabet
  Γk₀Fin := inferInstance
  Λ := Phase
  main := .read
  σ := State
  initialState := initial
  m := program first last

def config (first last : Γ) (phase : Option Phase) (state : State (Γ := Γ))
    (input : List (Symbol (Γ := Γ))) (output result : List (Output (Γ := Γ))) :
    (machine first last).Cfg where
  l := phase
  var := state
  stk := fun key => match key with
    | .input => input
    | .output => output
    | .result => result

theorem first_symbol (first last value : Γ) (input : List (Symbol (Γ := Γ)))
    (output result : List (Output (Γ := Γ))) :
    (machine first last).step (config first last (some .read) initial (some value :: input) output result) =
      some (config first last (some .read) (none, some value, none, none) input output result) := by
  simp [FinTM2.step, machine, program, config, initial, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem second_symbol (first last a value : Γ) (input : List (Symbol (Γ := Γ)))
    (output result : List (Output (Γ := Γ))) :
    (machine first last).step (config first last (some .read) (none, some a, none, none)
      (some value :: input) output result) =
      some (config first last (some .read) (none, some a, some value, none) input output result) := by
  simp [FinTM2.step, machine, program, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem buffered_symbol (first last a b value : Γ) (input : List (Symbol (Γ := Γ)))
    (output result : List (Output (Γ := Γ))) :
    (machine first last).step (config first last (some .read) (none, some a, some b, none)
      (some value :: input) output result) =
      some (config first last (some .read) (none, some b, some value, none)
        input (.inl (some a) :: output) result) := by
  simp [FinTM2.step, machine, program, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem delimiter (first last : Γ) (input : List (Symbol (Γ := Γ)))
    (output result : List (Output (Γ := Γ))) :
    (machine first last).step (config first last (some .read) (none, some first, some last, none)
      (none :: input) output result) =
      some (config first last (some .read) initial input (.inl none :: output) result) := by
  simp [FinTM2.step, machine, program, config, initial, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem input_end (first last : Γ) (output result : List (Output (Γ := Γ))) :
    (machine first last).step (config first last (some .read) initial [] output result) =
      some (config first last (some .reverse) initial [] output result) := by
  simp [FinTM2.step, machine, program, config, initial, TM2.step, TM2.stepAux]

theorem reverse_symbol (first last : Γ) (state : State (Γ := Γ))
    (value : Output (Γ := Γ)) (output result : List (Output (Γ := Γ))) :
    (machine first last).step (config first last (some .reverse) state [] (value :: output) result) =
      some (config first last (some .reverse) (state.1, state.2.1, state.2.2.1, some value)
        [] output (value :: result)) := by
  simp [FinTM2.step, machine, program, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem reverse_end (first last : Γ) (state : State (Γ := Γ))
    (result : List (Output (Γ := Γ))) :
    (machine first last).step (config first last (some .reverse) state [] [] result) =
      some (config first last (some .finish) (state.1, state.2.1, state.2.2.1, none) [] [] result) := by
  simp [FinTM2.step, machine, program, config, TM2.step, TM2.stepAux]

theorem finish (first last : Γ) (state : State (Γ := Γ))
    (result : List (Output (Γ := Γ))) :
    (machine first last).step (config first last (some .finish) state [] [] result) =
      some (config first last none initial [] [] (.inr true :: result)) := by
  simp [FinTM2.step, machine, program, config, initial, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

def buffer_run (first last a b : Γ) (body : List Γ)
    (input : List (Symbol (Γ := Γ))) (output result : List (Output (Γ := Γ))) :
    EvalsToInTime (machine first last).step
      (config first last (some .read) (none, some a, some b, none)
        ((body ++ [first, last]).map some ++ none :: input) output result)
      (some (config first last (some .read) initial input
        (.inl none :: ((a :: b :: body).map (fun value => .inl (some value))).reverse ++ output) result))
      (body.length + 3) := by
  induction body generalizing a b output with
  | nil =>
      have one := StackMachineComposition.oneStep (buffered_symbol first last a b first
        (some last :: none :: input) output result)
      have two := StackMachineComposition.oneStep (buffered_symbol first last b first last
        (none :: input) (.inl (some a) :: output) result)
      have three := StackMachineComposition.oneStep (delimiter first last input
        (.inl (some b) :: .inl (some a) :: output) result)
      have front := EvalsToInTime.trans _ 1 1 _ _ _ one two
      have all := EvalsToInTime.trans _ 2 1 _ _ _ front three
      simpa only [List.nil_append, List.map_cons, List.map_nil, List.nil_append,
        List.reverse_cons, List.reverse_nil, List.singleton_append,
        List.cons_append, List.length_nil] using all
  | cons value body ih =>
      have one := StackMachineComposition.oneStep (buffered_symbol first last a b value
        ((body ++ [first, last]).map some ++ none :: input) output result)
      have later := ih b value (.inl (some a) :: output)
      have all := EvalsToInTime.trans _ 1 (body.length + 3) _ _ _ one later
      simpa only [List.cons_append, List.map_cons, List.reverse_cons,
        List.append_assoc, List.singleton_append, List.nil_append, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

def field_run (first last : Γ) (body : List Γ)
    (input : List (Symbol (Γ := Γ))) (output result : List (Output (Γ := Γ))) :
    EvalsToInTime (machine first last).step
      (config first last (some .read) initial
        ((body ++ [first, last]).map some ++ none :: input) output result)
      (some (config first last (some .read) initial input
        (.inl none :: (body.map (fun value => .inl (some value))).reverse ++ output) result))
      (body.length + 3) := by
  cases body with
  | nil =>
      have one := StackMachineComposition.oneStep (first_symbol first last first
        (some last :: none :: input) output result)
      have two := StackMachineComposition.oneStep (second_symbol first last first last
        (none :: input) output result)
      have three := StackMachineComposition.oneStep (delimiter first last input output result)
      have front := EvalsToInTime.trans _ 1 1 _ _ _ one two
      have all := EvalsToInTime.trans _ 2 1 _ _ _ front three
      simpa using all
  | cons a body =>
      cases body with
      | nil =>
          have one := StackMachineComposition.oneStep (first_symbol first last a
            (some first :: some last :: none :: input) output result)
          have two := StackMachineComposition.oneStep (second_symbol first last a first
            (some last :: none :: input) output result)
          have three := StackMachineComposition.oneStep (buffered_symbol first last a first last
            (none :: input) output result)
          have four := StackMachineComposition.oneStep (delimiter first last input
            (.inl (some a) :: output) result)
          have front := EvalsToInTime.trans _ 1 1 _ _ _ one two
          have middle := EvalsToInTime.trans _ 2 1 _ _ _ front three
          have all := EvalsToInTime.trans _ 3 1 _ _ _ middle four
          simpa using all
      | cons b body =>
          have one := StackMachineComposition.oneStep (first_symbol first last a
            (some b :: ((body ++ [first, last]).map some ++ none :: input)) output result)
          have two := StackMachineComposition.oneStep (second_symbol first last a b
            ((body ++ [first, last]).map some ++ none :: input) output result)
          have front := EvalsToInTime.trans _ 1 1 _ _ _ one two
          have later := buffer_run first last a b body input output result
          have all := EvalsToInTime.trans _ 2 (body.length + 3) _ _ _ front later
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

def source (first last : Γ) (bodies : List (List Γ)) : List (Symbol (Γ := Γ)) :=
  WordTemplateMachine.Indexed.frame (bodies.map (fun body => body ++ [first, last]))

def copied (bodies : List (List Γ)) : List (Output (Γ := Γ)) :=
  (WordTemplateMachine.Indexed.frame bodies).map Sum.inl

def cost : List (List Γ) → Nat
  | [] => 0
  | body :: bodies => body.length + 3 + cost bodies

omit [Fintype Γ] [DecidableEq Γ] in
theorem source_cons (first last : Γ) (body : List Γ) (bodies : List (List Γ)) :
    source first last (body :: bodies) =
      (body ++ [first, last]).map some ++ none :: source first last bodies := by
  simp [source, WordTemplateMachine.Indexed.frame]

omit [Fintype Γ] [DecidableEq Γ] in
theorem copied_cons (body : List Γ) (bodies : List (List Γ)) :
    copied (body :: bodies) =
      (body.map (fun value => .inl (some value))) ++ .inl none :: copied bodies := by
  simp [copied, WordTemplateMachine.Indexed.frame, List.map_append, List.map_map,
    Function.comp_def]

def scan_run (first last : Γ) (bodies : List (List Γ))
    (input : List (Symbol (Γ := Γ))) (output result : List (Output (Γ := Γ))) :
    EvalsToInTime (machine first last).step
      (config first last (some .read) initial (source first last bodies ++ input) output result)
      (some (config first last (some .read) initial input ((copied bodies).reverse ++ output) result))
      (cost bodies) := by
  induction bodies generalizing output with
  | nil => simpa [source, copied, cost, WordTemplateMachine.Indexed.frame] using
      (EvalsToInTime.refl (machine first last).step
        (config first last (some .read) initial input output result))
  | cons body bodies ih =>
      have firstRun := field_run first last body (source first last bodies ++ input) output result
      have later := ih (.inl none :: (body.map (fun value => .inl (some value))).reverse ++ output)
      have all := EvalsToInTime.trans _ (body.length + 3) (cost bodies) _ _ _ firstRun later
      simpa only [source_cons, copied_cons, cost, List.append_assoc, List.cons_append,
        List.reverse_append, List.reverse_cons, List.singleton_append, List.nil_append,
        Nat.add_comm] using all

def reverse_run (first last : Γ) (state : State (Γ := Γ))
    (output result : List (Output (Γ := Γ))) :
    EvalsToInTime (machine first last).step
      (config first last (some .reverse) state [] output result)
      (some (config first last none initial [] [] (.inr true :: output.reverse ++ result)))
      (output.length + 2) := by
  induction output generalizing state result with
  | nil =>
      have one := StackMachineComposition.oneStep (reverse_end first last state result)
      have two := StackMachineComposition.oneStep (finish first last
        (state.1, state.2.1, state.2.2.1, none) result)
      simpa using EvalsToInTime.trans _ 1 1 _ _ _ one two
  | cons value output ih =>
      have one := StackMachineComposition.oneStep (reverse_symbol first last state value output result)
      have later := ih (state.1, state.2.1, state.2.2.1, some value) (value :: result)
      have all := EvalsToInTime.trans _ 1 (output.length + 2) _ _ _ one later
      simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

omit [Fintype Γ] [DecidableEq Γ] in
theorem source_length (first last : Γ) (bodies : List (List Γ)) :
    (source first last bodies).length = cost bodies := by
  induction bodies with
  | nil => rfl
  | cons body bodies ih => simp only [source_cons, cost, List.length_append,
      List.length_map, List.length_cons, List.length_nil, ih]; omega

omit [Fintype Γ] [DecidableEq Γ] in
theorem copied_length_le (first last : Γ) (bodies : List (List Γ)) :
    (copied bodies).length ≤ (source first last bodies).length := by
  induction bodies with
  | nil => rfl
  | cons body bodies ih => simp only [source_cons, copied_cons, List.length_append,
      List.length_map, List.length_cons, List.length_nil] at *; omega

private theorem init_eq (first last : Γ) (input : List (Symbol (Γ := Γ))) :
    initList (machine first last) input = config first last (some .read) initial input [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key <;> simp

private theorem halt_eq (first last : Γ) (result : List (Output (Γ := Γ))) :
    haltList (machine first last) result = config first last none initial [] [] result := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key <;> simp

/-- The clock counts the delayed field scan, delimiters, output reversal and
status emission. Every dynamic symbol is copied without reinterpretation. -/
def outputs (first last : Γ) (bodies : List (List Γ)) :
    TM2OutputsInTime (machine first last) (source first last bodies)
      (some (.inr true :: copied bodies)) (2 * (source first last bodies).length + 3) := by
  have scanned := scan_run first last bodies [] [] []
  simp only [List.append_nil] at scanned
  have ended := StackMachineComposition.oneStep (input_end first last (copied bodies).reverse [])
  have front := EvalsToInTime.trans _ (cost bodies) 1 _ _ _ scanned ended
  have later := reverse_run first last initial (copied bodies).reverse []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at later
  have all := EvalsToInTime.trans _ (1 + cost bodies) ((copied bodies).length + 2) _ _ _ front later
  change EvalsToInTime _ (initList _ _) (some (haltList _ _)) _
  rw [init_eq, halt_eq]
  refine ⟨all.toEvalsTo, all.steps_le_m.trans ?_⟩
  have bound := copied_length_le first last bodies
  rw [source_length]
  rw [source_length] at bound
  omega

noncomputable def realization (first last : Γ) : TM2ComputableInPolyTime
    (source first last) (fun result : List (Output (Γ := Γ)) => result)
    (fun bodies => .inr true :: copied bodies) where
  tm := machine first last
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun bodies := by
    change TM2OutputsInTime (machine first last) ((source first last bodies).map id)
      (some ((.inr true :: copied bodies).map id)) _
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using outputs first last bodies

end Mettapedia.Computability.FramedWordSuffixRemoval
