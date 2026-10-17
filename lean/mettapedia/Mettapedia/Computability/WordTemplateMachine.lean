import Mettapedia.Computability.StackMachineComposition

/-!
# Finite-control word-template instantiation

A fixed template consists of literal alphabet symbols and holes. Each hole
copies the complete supplied word, retaining its order and restoring it for
later holes. The dynamic word lives only on stacks. Control registers and
program labels are finite, including when holes repeat.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.WordTemplateMachine

open Turing StateTransition
open Turing.TM2.Stmt

variable {Γ : Type}

abbrev Template (Γ : Type) := List (Option Γ)

def instantiate (template : Template Γ) (word : List Γ) : List Γ :=
  template.flatMap fun token => match token with | none => word | some symbol => [symbol]

@[simp] theorem instantiate_nil (word : List Γ) : instantiate ([] : Template Γ) word = [] := rfl
@[simp] theorem instantiate_literal (symbol : Γ) (rest : Template Γ) (word : List Γ) :
    instantiate (some symbol :: rest) word = symbol :: instantiate rest word := by simp [instantiate]
@[simp] theorem instantiate_hole (rest : Template Γ) (word : List Γ) :
    instantiate (none :: rest) word = word ++ instantiate rest word := by simp [instantiate]

@[simp] theorem instantiate_append (first second : Template Γ) (word : List Γ) :
    instantiate (first ++ second) word = instantiate first word ++ instantiate second word := by
  simp [instantiate]

@[simp] theorem instantiate_literals (symbols word : List Γ) :
    instantiate (symbols.map some) word = symbols := by
  induction symbols with
  | nil => simp
  | cons symbol rest ih => simpa using congrArg (List.cons symbol) ih

theorem instantiate_length (template : Template Γ) (word : List Γ) :
    (instantiate template word).length ≤ template.length * (word.length + 1) := by
  induction template with
  | nil => simp
  | cons token rest ih =>
      cases token <;> simp only [instantiate_hole, instantiate_literal, List.length_append, List.length_cons]
      all_goals nlinarith

inductive Stack where
  | input | temporary | output
  deriving DecidableEq, Fintype

inductive Phase (length : Nat) where
  | emit (index : Fin (length + 1))
  | copy (index : Fin (length + 1))
  | restore (index : Fin (length + 1))
  | drain | finish
  deriving DecidableEq, Fintype

def advance {length : Nat} (index : Fin (length + 1)) : Fin (length + 1) :=
  ⟨min (index.val + 1) length, by have := Nat.min_le_right (index.val + 1) length; omega⟩

theorem advance_value {length : Nat} (index : Fin (length + 1)) (before : index.val < length) :
    (advance index).val = index.val + 1 := by simp [advance, Nat.min_eq_left (by omega : index.val + 1 ≤ length)]

variable [Fintype Γ] [Inhabited Γ]

/-- The shared transition body is executable without constructing bundled
finite-enumeration witnesses. The machine below uses this exact body. -/
def program (template : Template Γ) (phase : Phase template.length) :
    TM2.Stmt (fun (_ : Stack) => Γ) (Phase template.length) (Option Γ) :=
  match phase with
    | .emit index => match template[index.val]? with
      | none => goto fun _ => .drain
      | some (some symbol) => push .output (fun _ => symbol) (goto fun _ => .emit (advance index))
      | some none => goto fun _ => .copy index
    | .copy index => pop .input (fun _ value => value)
        (branch Option.isSome
          (push .temporary (fun state => state.getD default)
            (push .output (fun state => state.getD default) (goto fun _ => .copy index)))
          (goto fun _ => .restore index))
    | .restore index => pop .temporary (fun _ value => value)
        (branch Option.isSome
          (push .input (fun state => state.getD default) (goto fun _ => .restore index))
          (goto fun _ => .emit (advance index)))
    | .drain => pop .input (fun _ value => value)
        (branch Option.isSome (goto fun _ => .drain) (goto fun _ => .finish))
    | .finish => pop .output (fun _ value => value)
        (branch Option.isSome
          (push .input (fun state => state.getD default) (goto fun _ => .finish)) halt)

/-- Each statement inspects or transfers one alphabet symbol. No register
contains the dynamic argument or an unbounded integer. -/
def machine (template : Template Γ) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .input
  Γ _ := Γ
  Λ := Phase template.length
  main := .emit ⟨0, by omega⟩
  σ := Option Γ
  initialState := none
  m := program template

theorem machine_step (template : Template Γ) :
    (machine template).step = TM2.step (program template) := rfl

def config (template : Template Γ) (phase : Option (Phase template.length)) (state : Option Γ)
    (input temporary output : List Γ) : (machine template).Cfg where
  l := phase
  var := state
  stk stack := match (show Stack from stack) with
    | .input => input
    | .temporary => temporary
    | .output => output

theorem emit_literal (template : Template Γ) (index : Fin (template.length + 1))
    (symbol : Γ) (stored : template[index.val]? = some (some symbol))
    (state : Option Γ) (input temporary output : List Γ) :
    (machine template).step (config template (some (.emit index)) state input temporary output) =
      some (config template (some (.emit (advance index))) state input temporary (symbol :: output)) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux, stored]
  funext stack
  cases stack <;> simp [Function.update]

theorem emit_hole (template : Template Γ) (index : Fin (template.length + 1))
    (stored : template[index.val]? = some none) (state : Option Γ) (input temporary output : List Γ) :
    (machine template).step (config template (some (.emit index)) state input temporary output) =
      some (config template (some (.copy index)) state input temporary output) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux, stored]

theorem emit_end (template : Template Γ) (index : Fin (template.length + 1))
    (stored : template[index.val]? = none) (state : Option Γ) (input temporary output : List Γ) :
    (machine template).step (config template (some (.emit index)) state input temporary output) =
      some (config template (some .drain) state input temporary output) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux, stored]

theorem copy_cons (template : Template Γ) (index : Fin (template.length + 1))
    (state : Option Γ) (head : Γ) (tail temporary output : List Γ) :
    (machine template).step (config template (some (.copy index)) state (head :: tail) temporary output) =
      some (config template (some (.copy index)) (some head) tail (head :: temporary) (head :: output)) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]
  funext stack
  cases stack <;> simp [Function.update]

theorem copy_nil (template : Template Γ) (index : Fin (template.length + 1))
    (state : Option Γ) (temporary output : List Γ) :
    (machine template).step (config template (some (.copy index)) state [] temporary output) =
      some (config template (some (.restore index)) none [] temporary output) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]

theorem restore_cons (template : Template Γ) (index : Fin (template.length + 1))
    (state : Option Γ) (head : Γ) (input tail output : List Γ) :
    (machine template).step (config template (some (.restore index)) state input (head :: tail) output) =
      some (config template (some (.restore index)) (some head) (head :: input) tail output) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]
  funext stack
  cases stack <;> simp [Function.update]

theorem restore_nil (template : Template Γ) (index : Fin (template.length + 1))
    (state : Option Γ) (input output : List Γ) :
    (machine template).step (config template (some (.restore index)) state input [] output) =
      some (config template (some (.emit (advance index))) none input [] output) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]


theorem drain_cons (template : Template Γ) (state : Option Γ) (head : Γ) (tail output : List Γ) :
    (machine template).step (config template (some .drain) state (head :: tail) [] output) =
      some (config template (some .drain) (some head) tail [] output) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]
  funext stack
  cases stack <;> simp [Function.update]

theorem drain_nil (template : Template Γ) (state : Option Γ) (output : List Γ) :
    (machine template).step (config template (some .drain) state [] [] output) =
      some (config template (some .finish) none [] [] output) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]

theorem finish_cons (template : Template Γ) (state : Option Γ) (head : Γ) (input tail : List Γ) :
    (machine template).step (config template (some .finish) state input [] (head :: tail)) =
      some (config template (some .finish) (some head) (head :: input) [] tail) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]
  funext stack
  cases stack <;> simp [Function.update]

theorem finish_nil (template : Template Γ) (state : Option Γ) (input : List Γ) :
    (machine template).step (config template (some .finish) state input [] []) =
      some (config template none none input [] []) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]

/-- Copying retains an independent reversed argument for restoring the next
hole, while adding its symbols to the output in physical reverse order. -/
def copy_run (template : Template Γ) (index : Fin (template.length + 1))
    (word temporary output : List Γ) (state : Option Γ) :
    EvalsToInTime (machine template).step
      (config template (some (.copy index)) state word temporary output)
      (some (config template (some (.restore index)) none []
        (word.reverse ++ temporary) (word.reverse ++ output))) (word.length + 1) := by
  induction word generalizing temporary output state with
  | nil => simpa using StackMachineComposition.oneStep (copy_nil template index state temporary output)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (copy_cons template index state head tail temporary output)
      have rest := ih (head :: temporary) (head :: output) (some head)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

/-- The temporary stack restores the original complete argument before the
next template instruction. -/
def restore_run (template : Template Γ) (index : Fin (template.length + 1))
    (temporary input output : List Γ) (state : Option Γ) :
    EvalsToInTime (machine template).step
      (config template (some (.restore index)) state input temporary output)
      (some (config template (some (.emit (advance index))) none (temporary.reverse ++ input) [] output))
      (temporary.length + 1) := by
  induction temporary generalizing input state with
  | nil => simpa using StackMachineComposition.oneStep (restore_nil template index state input output)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (restore_cons template index state head input tail output)
      have rest := ih (head :: input) (some head)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def copy_restore_run (template : Template Γ) (index : Fin (template.length + 1))
    (word output : List Γ) (state : Option Γ) :
    EvalsToInTime (machine template).step
      (config template (some (.copy index)) state word [] output)
      (some (config template (some (.emit (advance index))) none word [] (word.reverse ++ output)))
      (2 * word.length + 2) := by
  have copied := copy_run template index word [] output state
  simp only [List.append_nil] at copied
  have restored := restore_run template index word.reverse [] (word.reverse ++ output) none
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ (word.length + 1) (word.reverse.length + 1) _ _ _ copied restored

def drain_run (template : Template Γ) (input output : List Γ) (state : Option Γ) :
    EvalsToInTime (machine template).step
      (config template (some .drain) state input [] output)
      (some (config template (some .finish) none [] [] output)) (input.length + 1) := by
  induction input generalizing state with
  | nil => simpa using StackMachineComposition.oneStep (drain_nil template state output)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (drain_cons template state head tail output)
      have rest := ih (some head)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def finish_run (template : Template Γ) (output input : List Γ) (state : Option Γ) :
    EvalsToInTime (machine template).step
      (config template (some .finish) state input [] output)
      (some (config template none none (output.reverse ++ input) [] [])) (output.length + 1) := by
  induction output generalizing input state with
  | nil => simpa using StackMachineComposition.oneStep (finish_nil template state input)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (finish_cons template state head input tail)
      have rest := ih (head :: input) (some head)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

omit [Fintype Γ] [Inhabited Γ] in
private theorem suffix_index (template preceding rest : Template Γ) (layout : template = preceding ++ rest) :
    preceding.length < template.length + 1 := by rw [layout, List.length_append]; omega

/-- The authored template's finite control runs all its remaining instructions.
Order is restored only after every literal and hole has been processed. -/
def emit_run (template preceding rest : Template Γ) (layout : template = preceding ++ rest)
    (word output : List Γ) (state : Option Γ) :
    Σ finalState, EvalsToInTime (machine template).step
      (config template (some (.emit ⟨preceding.length, suffix_index template preceding rest layout⟩)) state word [] output)
      (some (config template (some .drain) finalState word [] ((instantiate rest word).reverse ++ output)))
      ((2 * word.length + 3) * rest.length + 1) := by
  induction rest generalizing preceding output state with
  | nil =>
      have stored : template[preceding.length]? = none := by rw [layout]; simp
      refine ⟨state, ?_⟩
      simpa using StackMachineComposition.oneStep (emit_end template _ stored state word [] output)
  | cons token rest ih =>
      let index : Fin (template.length + 1) := ⟨preceding.length, suffix_index template preceding (token :: rest) layout⟩
      let nextPrefix := preceding ++ [token]
      have nextLayout : template = nextPrefix ++ rest := by simpa [nextPrefix, List.append_assoc] using layout
      have before : index.val < template.length := by
        simp only [index, layout, List.length_append, List.length_cons]
        omega
      have nextIndex : advance index =
          ⟨nextPrefix.length, suffix_index template nextPrefix rest nextLayout⟩ := by
        apply Fin.ext
        rw [advance_value index before]
        simp [index, nextPrefix]
      have stored : template[index.val]? = some token := by simp [index, layout]
      cases token with
      | some symbol =>
          obtain ⟨finalState, remaining⟩ := ih nextPrefix nextLayout (symbol :: output) state
          rw [← nextIndex] at remaining
          have first := StackMachineComposition.oneStep (emit_literal template index symbol stored state word [] output)
          have joined := EvalsToInTime.trans _ 1 ((2 * word.length + 3) * rest.length + 1) _ _ _ first remaining
          refine ⟨finalState, ?_⟩
          have enlarged : ((2 * word.length + 3) * rest.length + 1) + 1 ≤
              (2 * word.length + 3) * (rest.length + 1) + 1 := by
            simp only [Nat.mul_add, Nat.mul_one]
            omega
          have bounded := (show EvalsToInTime _ _ _ ((2 * word.length + 3) * (rest.length + 1) + 1)
            from ⟨joined.toEvalsTo, joined.steps_le_m.trans enlarged⟩)
          simpa [index, List.append_assoc] using bounded
      | none =>
          obtain ⟨finalState, remaining⟩ := ih nextPrefix nextLayout (word.reverse ++ output) none
          rw [← nextIndex] at remaining
          have first := StackMachineComposition.oneStep (emit_hole template index stored state word [] output)
          have copied := copy_restore_run template index word output state
          have front := EvalsToInTime.trans _ 1 (2 * word.length + 2) _ _ _ first copied
          have joined := EvalsToInTime.trans _ ((2 * word.length + 2) + 1)
            ((2 * word.length + 3) * rest.length + 1) _ _ _ front remaining
          refine ⟨finalState, ?_⟩
          have sameBudget : ((2 * word.length + 3) * rest.length + 1) + ((2 * word.length + 2) + 1) =
              (2 * word.length + 3) * (rest.length + 1) + 1 := by ring
          rw [sameBudget] at joined
          simpa [index, List.append_assoc] using joined


theorem init_eq (template : Template Γ) (word : List Γ) :
    initList (machine template) word = config template (some (.emit ⟨0, by omega⟩)) none word [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext stack
  cases stack <;> simp

theorem halt_eq (template : Template Γ) (word : List Γ) :
    haltList (machine template) word = config template none none word [] [] := by
  simp only [haltList, machine, config]
  congr 1
  funext stack
  cases stack <;> simp

/-- The finite machine realizes every fixed word template, preserving order
and repeated copies, with a linear clock derived from its actual execution. -/
def outputs (template : Template Γ) (word : List Γ) :
    TM2OutputsInTime (machine template) word (some (instantiate template word))
      (4 * (template.length + 1) * (word.length + 1)) := by
  obtain ⟨finalState, emitted⟩ := emit_run template [] template (by simp) word [] none
  simp only [List.length_nil, List.append_nil] at emitted
  have drained := drain_run template word (instantiate template word).reverse finalState
  have finished := finish_run template (instantiate template word).reverse [] none
  simp only [List.reverse_reverse, List.append_nil] at finished
  have front := EvalsToInTime.trans _ ((2 * word.length + 3) * template.length + 1)
    (word.length + 1) _ _ _ emitted drained
  have joined := EvalsToInTime.trans _ ((word.length + 1) + ((2 * word.length + 3) * template.length + 1))
    ((instantiate template word).reverse.length + 1) _ _ _ front finished
  have size := instantiate_length template word
  have included : ((instantiate template word).reverse.length + 1) +
      ((word.length + 1) + ((2 * word.length + 3) * template.length + 1)) ≤ 4 * (template.length + 1) * (word.length + 1) := by
    simp only [List.length_reverse]
    nlinarith
  change EvalsToInTime _ (initList (machine template) word)
    (some (haltList (machine template) (instantiate template word))) _
  rw [init_eq, halt_eq]
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans included⟩

open Polynomial

/-- Each finite template supplies a genuine polynomial-time realization; the
coefficient depends on that fixed authored template. -/
noncomputable def computable (template : Template Γ) : TM2ComputableInPolyTime
    (fun word : List Γ => word) (fun word : List Γ => word) (instantiate template) where
  tm := machine template
  inputAlphabet := Equiv.refl Γ
  outputAlphabet := Equiv.refl Γ
  time := C (4 * (template.length + 1)) * (X + C 1)
  outputsFun word := by
    change TM2OutputsInTime (machine template) (word.map id) (some ((instantiate template word).map id)) _
    simp only [List.map_id_fun]
    simpa using outputs template word

namespace Indexed

variable {arity : Nat}

/-- Indexed holes select independently supplied words; repeated indices retain
separate physical copies in the output. -/
abbrev Template (Γ : Type) (arity : Nat) := List (Γ ⊕ Fin arity)

def instantiate (template : Template Γ arity) (words : Fin arity → List Γ) : List Γ :=
  template.flatMap fun token => match token with | .inl symbol => [symbol] | .inr index => words index

omit [Fintype Γ] [Inhabited Γ] in
@[simp] theorem instantiate_nil (words : Fin arity → List Γ) :
    instantiate ([] : Template Γ arity) words = [] := rfl

omit [Fintype Γ] [Inhabited Γ] in
@[simp] theorem instantiate_literal (symbol : Γ) (rest : Template Γ arity)
    (words : Fin arity → List Γ) :
    instantiate (.inl symbol :: rest) words = symbol :: instantiate rest words := by
  simp [instantiate]

omit [Fintype Γ] [Inhabited Γ] in
@[simp] theorem instantiate_hole (index : Fin arity) (rest : Template Γ arity)
    (words : Fin arity → List Γ) :
    instantiate (.inr index :: rest) words = words index ++ instantiate rest words := by
  simp [instantiate]

omit [Fintype Γ] [Inhabited Γ] in
@[simp] theorem instantiate_append (first second : Template Γ arity) (words : Fin arity → List Γ) :
    instantiate (first ++ second) words = instantiate first words ++ instantiate second words := by
  simp [instantiate]

omit [Fintype Γ] [Inhabited Γ] in
@[simp] theorem instantiate_literals (symbols : List Γ) (words : Fin arity → List Γ) :
    instantiate (symbols.map Sum.inl) words = symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol rest ih => simpa [instantiate] using congrArg (List.cons symbol) ih

/-- A separator is outside the argument alphabet, so argument symbols cannot
be confused with tuple boundaries. -/
def frame (words : List (List Γ)) : List (Option Γ) :=
  words.flatMap fun word => word.map some ++ [none]

def argumentWire (words : Fin arity → List Γ) : List (Option Γ) :=
  frame ((List.finRange arity).map words)

omit [Fintype Γ] [Inhabited Γ] in
theorem frame_length (words : List (List Γ)) :
    (frame words).length = (words.map List.length).sum + words.length := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
      change ((word.map some ++ [none]) ++ frame rest).length = _
      simp only [List.length_append, List.length_map,
        List.map_cons, List.sum_cons, List.length_cons, List.length_nil]
      rw [ih]
      omega

omit [Fintype Γ] [Inhabited Γ] in
theorem argumentWire_length (words : Fin arity → List Γ) :
    (argumentWire words).length =
      ((List.finRange arity).map fun index => (words index).length).sum + arity := by
  simpa [argumentWire, List.map_map, Function.comp_def] using
    frame_length ((List.finRange arity).map words)

/-- The field cursor is finite and saturates after the authored arity. -/
def select (target : Fin arity) (cursor : Fin (arity + 1)) : List (Option Γ) → List Γ
  | [] => []
  | none :: rest => select target (advance cursor) rest
  | some symbol :: rest =>
      if cursor.val = target.val then symbol :: select target cursor rest else select target cursor rest

def instantiateWire (template : Template Γ arity) (input : List (Option Γ)) : List Γ :=
  instantiate template fun index => select index ⟨0, by omega⟩ input

omit [Fintype Γ] [Inhabited Γ] in
@[simp] theorem instantiateWire_nil (input : List (Option Γ)) : instantiateWire ([] : Template Γ arity) input = [] := rfl

omit [Fintype Γ] [Inhabited Γ] in
@[simp] theorem instantiateWire_literal (symbol : Γ) (rest : Template Γ arity) (input : List (Option Γ)) :
    instantiateWire (.inl symbol :: rest) input = symbol :: instantiateWire rest input := by
  simp [instantiateWire, instantiate]

omit [Fintype Γ] [Inhabited Γ] in
@[simp] theorem instantiateWire_hole (index : Fin arity) (rest : Template Γ arity) (input : List (Option Γ)) :
    instantiateWire (.inr index :: rest) input = select index ⟨0, by omega⟩ input ++ instantiateWire rest input := by
  simp [instantiateWire, instantiate]

omit [Fintype Γ] [Inhabited Γ] in
theorem select_length (target : Fin arity) (cursor : Fin (arity + 1)) (input : List (Option Γ)) :
    (select target cursor input).length ≤ input.length := by
  induction input generalizing cursor with
  | nil => simp [select]
  | cons token rest ih =>
      cases token <;> simp only [select]
      · exact (ih (advance cursor)).trans (by simp)
      · split <;> simp only [List.length_cons] <;> have := ih cursor <;> omega

omit [Fintype Γ] [Inhabited Γ] in
theorem select_word (target : Fin arity) (cursor : Fin (arity + 1)) (word : List Γ) (rest : List (Option Γ)) :
    select target cursor (word.map some ++ rest) =
      (if cursor.val = target.val then word else []) ++ select target cursor rest := by
  induction word with
  | nil => simp
  | cons symbol tail ih =>
      by_cases same : cursor.val = target.val <;> simp [select, same, ih]

omit [Fintype Γ] [Inhabited Γ] in
theorem select_frame (target : Fin arity) (cursor : Fin (arity + 1)) (words : List (List Γ))
    (room : cursor.val + words.length ≤ arity) :
    select target cursor (frame words) =
      if cursor.val ≤ target.val then (words[target.val - cursor.val]?).getD [] else [] := by
  induction words generalizing cursor with
  | nil => simp [frame, select]
  | cons word rest ih =>
      have before : cursor.val < arity := by simp only [List.length_cons] at room; omega
      have next := advance_value cursor before
      have restRoom : (advance cursor).val + rest.length ≤ arity := by
        rw [next]
        simp only [List.length_cons] at room
        omega
      simp only [frame, List.flatMap_cons, List.append_assoc, select_word]
      change (if cursor.val = target.val then word else []) ++ select target (advance cursor) (frame rest) = _
      rw [ih (advance cursor) restRoom, next]
      by_cases same : cursor.val = target.val
      · simp [same]
      · by_cases follows : cursor.val < target.val
        · have difference : target.val - cursor.val = (target.val - (cursor.val + 1)) + 1 := by omega
          simp [same, show cursor.val ≤ target.val by omega,
            show cursor.val + 1 ≤ target.val by omega, difference]
        · simp [same, show ¬cursor.val ≤ target.val by omega,
            show ¬cursor.val + 1 ≤ target.val by omega]

omit [Fintype Γ] [Inhabited Γ] in
theorem select_argument (words : Fin arity → List Γ) (index : Fin arity) :
    select index ⟨0, by omega⟩ (argumentWire words) = words index := by
  have exactField := select_frame index ⟨0, by omega⟩ ((List.finRange arity).map words) (by simp)
  have bound : index.val < ((List.finRange arity).map words).length := by simp
  simpa [argumentWire, List.getElem?_eq_getElem bound] using exactField

omit [Fintype Γ] [Inhabited Γ] in
theorem instantiateWire_argumentWire (template : Template Γ arity) (words : Fin arity → List Γ) :
    instantiateWire template (argumentWire words) = instantiate template words := by
  unfold instantiateWire
  congr 1
  funext index
  exact select_argument words index

omit [Fintype Γ] [Inhabited Γ] in
theorem instantiateWire_length (template : Template Γ arity) (input : List (Option Γ)) :
    (instantiateWire template input).length ≤ template.length * (input.length + 1) := by
  induction template with
  | nil => simp [instantiateWire, instantiate]
  | cons token rest ih =>
      cases token with
      | inl symbol =>
          simp only [instantiateWire, instantiate, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at *
          nlinarith
      | inr index =>
          have selected := select_length index ⟨0, by omega⟩ input
          simp only [instantiateWire, instantiate, List.flatMap_cons, List.length_append, List.length_cons] at *
          nlinarith

inductive Stack where
  | input | temporary | output | result
  deriving DecidableEq, Fintype

def Alphabet (Γ : Type) : Stack → Type
  | .input | .temporary => Option Γ
  | .output | .result => Γ

instance (stack : Stack) : Fintype (Alphabet Γ stack) := by
  cases stack <;> dsimp [Alphabet] <;> infer_instance

instance (stack : Stack) : Inhabited (Alphabet Γ stack) := by
  cases stack <;> dsimp [Alphabet] <;> infer_instance

inductive Phase (arity length : Nat) where
  | emit (index : Fin (length + 1))
  | copy (index : Fin (length + 1)) (target : Fin arity) (cursor : Fin (arity + 1))
  | restore (index : Fin (length + 1))
  | drain | finish
  deriving DecidableEq, Fintype

/-- The original indexed transition body depends only on its fixed
instruction lookup. Dynamic argument words remain on the original stacks. -/
def instructionProgram (length : Nat) (instruction : Nat → Option (Γ ⊕ Fin arity))
    (phase : Phase arity length) : TM2.Stmt (Alphabet Γ) (Phase arity length) (Option (Option Γ)) := match phase with
    | .emit index => match instruction index.val with
      | none => goto fun _ => .drain
      | some (.inl symbol) => push .output (fun _ => symbol) (goto fun _ => .emit (advance index))
      | some (.inr target) => goto fun _ => .copy index target ⟨0, by omega⟩
    | .copy index target cursor => pop .input (fun _ value => value)
        (branch Option.isSome
          (push .temporary (fun state => state.getD none)
            (branch (fun state => (state.getD none).isSome)
              (branch (fun _ => decide (cursor.val = target.val))
                (push .output (fun state => (state.getD none).getD default)
                  (goto fun _ => .copy index target cursor))
                (goto fun _ => .copy index target cursor))
              (goto fun _ => .copy index target (advance cursor))))
          (goto fun _ => .restore index))
    | .restore index => pop .temporary (fun _ value => value)
        (branch Option.isSome
          (push .input (fun state => state.getD none) (goto fun _ => .restore index))
          (goto fun _ => .emit (advance index)))
    | .drain => pop .input (fun _ value => value)
        (branch Option.isSome (goto fun _ => .drain) (goto fun _ => .finish))
    | .finish => pop .output (fun _ value => value.map some)
        (branch Option.isSome
          (push .result (fun state => (state.getD none).getD default) (goto fun _ => .finish)) halt)


/-- The original list-facing finite program. -/
def program (template : Template Γ arity) : Phase arity template.length →
    TM2.Stmt (Alphabet Γ) (Phase arity template.length) (Option (Option Γ)) :=
  instructionProgram template.length (fun index => template[index]?)

/-- An eagerly supplied instruction table realizes the very same finite
control. The caller can materialize this fixed table once before execution. -/
def arrayProgram (length : Nat) (instructions : Array (Γ ⊕ Fin arity)) : Phase arity length →
    TM2.Stmt (Alphabet Γ) (Phase arity length) (Option (Option Γ)) :=
  instructionProgram length (fun index => instructions[index]?)

omit [Fintype Γ] in
theorem arrayProgram_eq_program (template : Template Γ arity) :
    arrayProgram template.length template.toArray = program template := by
  have lookupSame : (fun (index : Nat) => template.toArray[index]?) =
      (fun (index : Nat) => template[index]?) := by
    funext index
    exact List.getElem?_toArray
  simp only [arrayProgram, program, lookupSame]


/-- Indexed selection scans and restores the real framed input. The only
register is a finite optional symbol; argument values live entirely on stacks. -/
def machine (template : Template Γ arity) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := Alphabet Γ
  Λ := Phase arity template.length
  main := .emit ⟨0, by omega⟩
  σ := Option (Option Γ)
  initialState := none
  m := program template

theorem machine_step (template : Template Γ arity) (state : (machine template).Cfg) :
    (machine template).step state = TM2.step (program template) state := rfl

def config (template : Template Γ arity) (phase : Option (Phase arity template.length))
    (state : Option (Option Γ)) (input temporary : List (Option Γ)) (output result : List Γ) : (machine template).Cfg where
  l := phase
  var := state
  stk stack := match stack with
    | .input => input
    | .temporary => temporary
    | .output => output
    | .result => result

theorem emit_literal (template : Template Γ arity) (index : Fin (template.length + 1))
    (symbol : Γ) (stored : template[index.val]? = some (.inl symbol))
    (state : Option (Option Γ)) (input temporary : List (Option Γ)) (output result : List Γ) :
    (machine template).step (config template (some (.emit index)) state input temporary output result) =
      some (config template (some (.emit (advance index))) state input temporary (symbol :: output) result) := by
  simp [FinTM2.step, machine, program, instructionProgram, config, Turing.TM2.step, Turing.TM2.stepAux, stored]
  funext stack
  cases stack <;> simp [Function.update]

theorem emit_hole (template : Template Γ arity) (index : Fin (template.length + 1))
    (target : Fin arity) (stored : template[index.val]? = some (.inr target))
    (state : Option (Option Γ)) (input temporary : List (Option Γ)) (output result : List Γ) :
    (machine template).step (config template (some (.emit index)) state input temporary output result) =
      some (config template (some (.copy index target ⟨0, by omega⟩)) state input temporary output result) := by
  simp [FinTM2.step, machine, program, instructionProgram, config, Turing.TM2.step, Turing.TM2.stepAux, stored]

theorem emit_end (template : Template Γ arity) (index : Fin (template.length + 1))
    (stored : template[index.val]? = none) (state : Option (Option Γ))
    (input temporary : List (Option Γ)) (output result : List Γ) :
    (machine template).step (config template (some (.emit index)) state input temporary output result) =
      some (config template (some .drain) state input temporary output result) := by
  simp [FinTM2.step, machine, program, instructionProgram, config, Turing.TM2.step, Turing.TM2.stepAux, stored]

theorem copy_symbol (template : Template Γ arity) (index : Fin (template.length + 1))
    (target : Fin arity) (cursor : Fin (arity + 1)) (state : Option (Option Γ))
    (symbol : Γ) (tail temporary : List (Option Γ)) (output result : List Γ) :
    (machine template).step (config template (some (.copy index target cursor)) state (some symbol :: tail) temporary output result) =
      some (config template (some (.copy index target cursor)) (some (some symbol)) tail (some symbol :: temporary)
        (if cursor.val = target.val then symbol :: output else output) result) := by
  by_cases selected : cursor.val = target.val
  all_goals simp [FinTM2.step, machine, program, instructionProgram, config, Turing.TM2.step, Turing.TM2.stepAux, selected]
  all_goals funext stack; cases stack <;> simp [Function.update]

theorem copy_separator (template : Template Γ arity) (index : Fin (template.length + 1))
    (target : Fin arity) (cursor : Fin (arity + 1)) (state : Option (Option Γ))
    (tail temporary : List (Option Γ)) (output result : List Γ) :
    (machine template).step (config template (some (.copy index target cursor)) state (none :: tail) temporary output result) =
      some (config template (some (.copy index target (advance cursor))) (some none) tail (none :: temporary) output result) := by
  simp [FinTM2.step, machine, program, instructionProgram, config, Turing.TM2.step, Turing.TM2.stepAux]
  funext stack
  cases stack <;> simp [Function.update]

theorem copy_nil (template : Template Γ arity) (index : Fin (template.length + 1))
    (target : Fin arity) (cursor : Fin (arity + 1)) (state : Option (Option Γ))
    (temporary : List (Option Γ)) (output result : List Γ) :
    (machine template).step (config template (some (.copy index target cursor)) state [] temporary output result) =
      some (config template (some (.restore index)) none [] temporary output result) := by
  simp [FinTM2.step, machine, program, instructionProgram, config, Turing.TM2.step, Turing.TM2.stepAux]

theorem restore_cons (template : Template Γ arity) (index : Fin (template.length + 1))
    (state : Option (Option Γ)) (head : Option Γ) (input tail : List (Option Γ)) (output result : List Γ) :
    (machine template).step (config template (some (.restore index)) state input (head :: tail) output result) =
      some (config template (some (.restore index)) (some head) (head :: input) tail output result) := by
  simp [FinTM2.step, machine, program, instructionProgram, config, Turing.TM2.step, Turing.TM2.stepAux]
  funext stack
  cases stack <;> simp [Function.update]

theorem restore_nil (template : Template Γ arity) (index : Fin (template.length + 1))
    (state : Option (Option Γ)) (input : List (Option Γ)) (output result : List Γ) :
    (machine template).step (config template (some (.restore index)) state input [] output result) =
      some (config template (some (.emit (advance index))) none input [] output result) := by
  simp [FinTM2.step, machine, program, instructionProgram, config, Turing.TM2.step, Turing.TM2.stepAux]

theorem drain_cons (template : Template Γ arity) (state : Option (Option Γ))
    (head : Option Γ) (tail : List (Option Γ)) (output result : List Γ) :
    (machine template).step (config template (some .drain) state (head :: tail) [] output result) =
      some (config template (some .drain) (some head) tail [] output result) := by
  simp [FinTM2.step, machine, program, instructionProgram, config, Turing.TM2.step, Turing.TM2.stepAux]
  funext stack
  cases stack <;> simp [Function.update]

theorem drain_nil (template : Template Γ arity) (state : Option (Option Γ)) (output result : List Γ) :
    (machine template).step (config template (some .drain) state [] [] output result) =
      some (config template (some .finish) none [] [] output result) := by
  simp [FinTM2.step, machine, program, instructionProgram, config, Turing.TM2.step, Turing.TM2.stepAux]

theorem finish_cons (template : Template Γ arity) (state : Option (Option Γ))
    (head : Γ) (tail result : List Γ) :
    (machine template).step (config template (some .finish) state [] [] (head :: tail) result) =
      some (config template (some .finish) (some (some head)) [] [] tail (head :: result)) := by
  simp [FinTM2.step, machine, program, instructionProgram, config, Turing.TM2.step, Turing.TM2.stepAux]
  funext stack
  cases stack <;> simp [Function.update]

theorem finish_nil (template : Template Γ arity) (state : Option (Option Γ)) (result : List Γ) :
    (machine template).step (config template (some .finish) state [] [] [] result) =
      some (config template none none [] [] [] result) := by
  simp [FinTM2.step, machine, program, instructionProgram, config, Turing.TM2.step, Turing.TM2.stepAux]

/-- Every input symbol is physically scanned, including separators and fields
that do not match the selected index. -/
def copy_run (template : Template Γ arity) (index : Fin (template.length + 1))
    (target : Fin arity) (cursor : Fin (arity + 1))
    (input temporary : List (Option Γ)) (output result : List Γ) (state : Option (Option Γ)) :
    EvalsToInTime (machine template).step
      (config template (some (.copy index target cursor)) state input temporary output result)
      (some (config template (some (.restore index)) none [] (input.reverse ++ temporary)
        ((select target cursor input).reverse ++ output) result)) (input.length + 1) := by
  induction input generalizing temporary output cursor state with
  | nil => simpa [select] using StackMachineComposition.oneStep (copy_nil template index target cursor state temporary output result)
  | cons token rest ih =>
      cases token with
      | none =>
          have first := StackMachineComposition.oneStep (copy_separator template index target cursor state rest temporary output result)
          have tail := ih (advance cursor) (none :: temporary) output (some none)
          simpa [select] using EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first tail
      | some symbol =>
          have first := StackMachineComposition.oneStep (copy_symbol template index target cursor state symbol rest temporary output result)
          have tail := ih cursor (some symbol :: temporary) (if cursor.val = target.val then symbol :: output else output)
            (some (some symbol))
          by_cases selected : cursor.val = target.val
          all_goals simpa [select, selected] using EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first tail

def restore_run (template : Template Γ arity) (index : Fin (template.length + 1))
    (temporary input : List (Option Γ)) (output result : List Γ) (state : Option (Option Γ)) :
    EvalsToInTime (machine template).step
      (config template (some (.restore index)) state input temporary output result)
      (some (config template (some (.emit (advance index))) none (temporary.reverse ++ input) [] output result))
      (temporary.length + 1) := by
  induction temporary generalizing input state with
  | nil => simpa using StackMachineComposition.oneStep (restore_nil template index state input output result)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (restore_cons template index state head input tail output result)
      have rest := ih (head :: input) (some head)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

/-- Selection never consumes or rewrites the independently supplied arguments. -/
def copy_restore_run (template : Template Γ arity) (index : Fin (template.length + 1))
    (target : Fin arity) (input : List (Option Γ)) (output result : List Γ) (state : Option (Option Γ)) :
    EvalsToInTime (machine template).step
      (config template (some (.copy index target ⟨0, by omega⟩)) state input [] output result)
      (some (config template (some (.emit (advance index))) none input []
        ((select target ⟨0, by omega⟩ input).reverse ++ output) result)) (2 * input.length + 2) := by
  have copied := copy_run template index target ⟨0, by omega⟩ input [] output result state
  simp only [List.append_nil] at copied
  have restored := restore_run template index input.reverse [] ((select target ⟨0, by omega⟩ input).reverse ++ output) result none
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    EvalsToInTime.trans _ (input.length + 1) (input.reverse.length + 1) _ _ _ copied restored

def drain_run (template : Template Γ arity) (input : List (Option Γ)) (output result : List Γ) (state : Option (Option Γ)) :
    EvalsToInTime (machine template).step
      (config template (some .drain) state input [] output result)
      (some (config template (some .finish) none [] [] output result)) (input.length + 1) := by
  induction input generalizing state with
  | nil => simpa using StackMachineComposition.oneStep (drain_nil template state output result)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (drain_cons template state head tail output result)
      have rest := ih (some head)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def finish_run (template : Template Γ arity) (output result : List Γ) (state : Option (Option Γ)) :
    EvalsToInTime (machine template).step
      (config template (some .finish) state [] [] output result)
      (some (config template none none [] [] [] (output.reverse ++ result))) (output.length + 1) := by
  induction output generalizing result state with
  | nil => simpa using StackMachineComposition.oneStep (finish_nil template state result)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (finish_cons template state head tail result)
      have rest := ih (head :: result) (some (some head))
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

omit [Fintype Γ] [Inhabited Γ] in
private theorem suffix_index (template preceding rest : Template Γ arity) (layout : template = preceding ++ rest) :
    preceding.length < template.length + 1 := by rw [layout, List.length_append]; omega

/-- The indexed authored control processes every literal and selected hole;
each selected field is obtained by a complete physical input scan. -/
def emit_run (template preceding rest : Template Γ arity) (layout : template = preceding ++ rest)
    (input : List (Option Γ)) (output result : List Γ) (state : Option (Option Γ)) :
    Σ finalState, EvalsToInTime (machine template).step
      (config template (some (.emit ⟨preceding.length, suffix_index template preceding rest layout⟩)) state input [] output result)
      (some (config template (some .drain) finalState input [] ((instantiateWire rest input).reverse ++ output) result))
      ((2 * input.length + 3) * rest.length + 1) := by
  induction rest generalizing preceding output state with
  | nil =>
      have stored : template[preceding.length]? = none := by rw [layout]; simp
      refine ⟨state, ?_⟩
      simpa using StackMachineComposition.oneStep (emit_end template _ stored state input [] output result)
  | cons token rest ih =>
      let index : Fin (template.length + 1) := ⟨preceding.length, suffix_index template preceding (token :: rest) layout⟩
      let nextPrefix := preceding ++ [token]
      have nextLayout : template = nextPrefix ++ rest := by simpa [nextPrefix, List.append_assoc] using layout
      have before : index.val < template.length := by
        simp only [index, layout, List.length_append, List.length_cons]
        omega
      have nextIndex : advance index = ⟨nextPrefix.length, suffix_index template nextPrefix rest nextLayout⟩ := by
        apply Fin.ext
        rw [advance_value index before]
        simp [index, nextPrefix]
      have stored : template[index.val]? = some token := by simp [index, layout]
      cases token with
      | inl symbol =>
          obtain ⟨finalState, remaining⟩ := ih nextPrefix nextLayout (symbol :: output) state
          rw [← nextIndex] at remaining
          have first := StackMachineComposition.oneStep (emit_literal template index symbol stored state input [] output result)
          have joined := EvalsToInTime.trans _ 1 ((2 * input.length + 3) * rest.length + 1) _ _ _ first remaining
          refine ⟨finalState, ?_⟩
          have enlarged : ((2 * input.length + 3) * rest.length + 1) + 1 ≤
              (2 * input.length + 3) * (rest.length + 1) + 1 := by
            simp only [Nat.mul_add, Nat.mul_one]
            omega
          have bounded := (show EvalsToInTime _ _ _ ((2 * input.length + 3) * (rest.length + 1) + 1)
            from ⟨joined.toEvalsTo, joined.steps_le_m.trans enlarged⟩)
          simpa [index, List.append_assoc] using bounded
      | inr target =>
          obtain ⟨finalState, remaining⟩ := ih nextPrefix nextLayout ((select target ⟨0, by omega⟩ input).reverse ++ output) none
          rw [← nextIndex] at remaining
          have first := StackMachineComposition.oneStep (emit_hole template index target stored state input [] output result)
          have copied := copy_restore_run template index target input output result state
          have front := EvalsToInTime.trans _ 1 (2 * input.length + 2) _ _ _ first copied
          have joined := EvalsToInTime.trans _ ((2 * input.length + 2) + 1)
            ((2 * input.length + 3) * rest.length + 1) _ _ _ front remaining
          refine ⟨finalState, ?_⟩
          have sameBudget : ((2 * input.length + 3) * rest.length + 1) + ((2 * input.length + 2) + 1) =
              (2 * input.length + 3) * (rest.length + 1) + 1 := by ring
          rw [sameBudget] at joined
          simpa [index, List.append_assoc] using joined

private theorem init_eq (template : Template Γ arity) (input : List (Option Γ)) :
    initList (machine template) input = config template (some (.emit ⟨0, by omega⟩)) none input [] [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext stack
  cases stack <;> simp

private theorem halt_eq (template : Template Γ arity) (result : List Γ) :
    haltList (machine template) result = config template none none [] [] [] result := by
  simp only [haltList, machine, config]
  congr 1
  funext stack
  cases stack <;> simp

/-- The polynomial clock counts real selection scans, restorations, final
input disposal and output reversal; it is not a supplied complexity callback. -/
def outputsWire (template : Template Γ arity) (input : List (Option Γ)) :
    TM2OutputsInTime (machine template) input (some (instantiateWire template input))
      (4 * (template.length + 1) * (input.length + 1)) := by
  obtain ⟨finalState, emitted⟩ := emit_run template [] template (by simp) input [] [] none
  simp only [List.length_nil, List.append_nil] at emitted
  have drained := drain_run template input (instantiateWire template input).reverse [] finalState
  have finished := finish_run template (instantiateWire template input).reverse [] none
  simp only [List.reverse_reverse, List.append_nil] at finished
  have front := EvalsToInTime.trans _ ((2 * input.length + 3) * template.length + 1)
    (input.length + 1) _ _ _ emitted drained
  have joined := EvalsToInTime.trans _ ((input.length + 1) + ((2 * input.length + 3) * template.length + 1))
    ((instantiateWire template input).reverse.length + 1) _ _ _ front finished
  have size := instantiateWire_length template input
  have included : ((instantiateWire template input).reverse.length + 1) +
      ((input.length + 1) + ((2 * input.length + 3) * template.length + 1)) ≤
        4 * (template.length + 1) * (input.length + 1) := by
    simp only [List.length_reverse]
    nlinarith
  change EvalsToInTime _ (initList (machine template) input)
    (some (haltList (machine template) (instantiateWire template input))) _
  rw [init_eq, halt_eq]
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans included⟩

/-- On independently supplied argument values, the total word operation emits
exactly the original indexed template interpretation. -/
def outputs (template : Template Γ arity) (words : Fin arity → List Γ) :
    TM2OutputsInTime (machine template) (argumentWire words) (some (instantiate template words))
      (4 * (template.length + 1) * ((argumentWire words).length + 1)) := by
  rw [← instantiateWire_argumentWire template words]
  exact outputsWire template (argumentWire words)

noncomputable def computable (template : Template Γ arity) : TM2ComputableInPolyTime
    argumentWire (fun word : List Γ => word) (instantiate template) where
  tm := machine template
  inputAlphabet := Equiv.refl (Option Γ)
  outputAlphabet := Equiv.refl Γ
  time := C (4 * (template.length + 1)) * (X + C 1)
  outputsFun words := by
    change TM2OutputsInTime (machine template) ((argumentWire words).map id)
      (some ((instantiate template words).map id)) _
    simp only [List.map_id_fun]
    simpa using outputs template words

/-- The same copier has a linear execution account for every physical input,
including packets that omit or repeat argument delimiters. -/
noncomputable def wireComputable (template : Template Γ arity) : TM2ComputableInPolyTime
    id id (instantiateWire template) where
  tm := machine template
  inputAlphabet := Equiv.refl (Option Γ)
  outputAlphabet := Equiv.refl Γ
  time := C (4 * (template.length + 1)) * (X + C 1)
  outputsFun input := by
    change TM2OutputsInTime (machine template) (input.map id)
      (some ((instantiateWire template input).map id)) _
    simp only [List.map_id_fun]
    simpa using outputsWire template input

end Indexed

namespace Wrapping

/-- Repeated one-hole wrapping retains a single copy of the central word.
The input supplies one physical marker for each wrapper, rather than a binary
number whose value would require exponentially many output nodes. -/
def wrapped (opening center suffix : List Γ) (count : Nat) : List Γ :=
  (List.replicate count opening).flatten ++ center ++ (List.replicate count suffix).flatten

inductive Stack where
  | input | closing | output | result
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input | .closing => Unit
  | .output | .result => Γ

inductive Kind where
  | opening | center | suffix
  deriving DecidableEq, Fintype

def word (opening center suffix : List Γ) : Kind → List Γ
  | .opening => opening | .center => center | .suffix => suffix

def limit (opening center suffix : List Γ) : Nat := opening.length + center.length + suffix.length

omit [Fintype Γ] [Inhabited Γ] in
theorem word_length_le (opening center suffix : List Γ) (kind : Kind) :
    (word opening center suffix kind).length ≤ limit opening center suffix := by
  cases kind <;> simp only [word, limit] <;> omega

inductive Phase (length : Nat) where
  | read | emit (kind : Kind) (index : Fin (length + 1)) | close | reverse
  deriving DecidableEq, Fintype

abbrev State := Bool × Option Γ

def after {length : Nat} : Kind → Phase length
  | .opening => .read | .center | .suffix => .close

/-- Opening and closing markers stay on physical stacks. Only the static
word position, current finite phase and alphabet symbol inhabit registers. -/
def machine (opening center suffix : List Γ) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := Alphabet (Γ := Γ)
  Λ := Phase (limit opening center suffix)
  main := .read
  σ := State (Γ := Γ)
  initialState := (false, none)
  m phase := match phase with
    | .read => pop .input (fun state marker => (marker.isSome, state.2))
        (branch (fun state => state.1)
          (push .closing (fun _ => ()) (goto fun _ => .emit .opening ⟨0, by omega⟩))
          (goto fun _ => .emit .center ⟨0, by omega⟩))
    | .emit kind index => match (word opening center suffix kind)[index.val]? with
      | some symbol => push .output (fun _ => symbol) (goto fun _ => .emit kind (advance index))
      | none => goto fun _ => after kind
    | .close => pop .closing (fun state marker => (marker.isSome, state.2))
        (branch (fun state => state.1) (goto fun _ => .emit .suffix ⟨0, by omega⟩)
          (goto fun _ => .reverse))
    | .reverse => pop .output (fun state symbol => (state.1, symbol))
        (branch (fun state => state.2.isSome)
          (push .result (fun state => state.2.getD default) (goto fun _ => .reverse)) halt)

def config (opening center suffix : List Γ) (phase : Option (Phase (limit opening center suffix)))
    (state : State (Γ := Γ)) (input closing : List Unit) (output result : List Γ) :
    (machine opening center suffix).Cfg where
  l := phase
  var := state
  stk stack := match stack with
    | .input => input | .closing => closing | .output => output | .result => result

local macro "wrapping_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]
  funext stack
  cases stack <;> simp [Function.update]))

theorem read_cons (opening center suffix : List Γ) (state : State (Γ := Γ))
    (input closing : List Unit) (output result : List Γ) :
    (machine opening center suffix).step (config opening center suffix (some .read) state
      (() :: input) closing output result) =
      some (config opening center suffix (some (.emit .opening ⟨0, by omega⟩))
        (true, state.2) input (() :: closing) output result) := by wrapping_step

theorem read_nil (opening center suffix : List Γ) (state : State (Γ := Γ))
    (closing : List Unit) (output result : List Γ) :
    (machine opening center suffix).step (config opening center suffix (some .read) state
      [] closing output result) =
      some (config opening center suffix (some (.emit .center ⟨0, by omega⟩))
        (false, state.2) [] closing output result) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]

theorem emit_symbol (opening center suffix : List Γ) (kind : Kind)
    (index : Fin (limit opening center suffix + 1)) (symbol : Γ)
    (stored : (word opening center suffix kind)[index.val]? = some symbol)
    (state : State (Γ := Γ)) (input closing : List Unit) (output result : List Γ) :
    (machine opening center suffix).step (config opening center suffix (some (.emit kind index))
      state input closing output result) =
      some (config opening center suffix (some (.emit kind (advance index)))
        state input closing (symbol :: output) result) := by
  simp [FinTM2.step, machine, config, stored, Turing.TM2.step, Turing.TM2.stepAux]
  funext stack
  cases stack <;> simp [Function.update]

theorem emit_end (opening center suffix : List Γ) (kind : Kind)
    (index : Fin (limit opening center suffix + 1))
    (stored : (word opening center suffix kind)[index.val]? = none)
    (state : State (Γ := Γ)) (input closing : List Unit) (output result : List Γ) :
    (machine opening center suffix).step (config opening center suffix (some (.emit kind index))
      state input closing output result) =
      some (config opening center suffix (some (after kind)) state input closing output result) := by
  simp [FinTM2.step, machine, config, stored, Turing.TM2.step, Turing.TM2.stepAux]

theorem close_cons (opening center suffix : List Γ) (state : State (Γ := Γ))
    (input closing : List Unit) (output result : List Γ) :
    (machine opening center suffix).step (config opening center suffix (some .close) state
      input (() :: closing) output result) =
      some (config opening center suffix (some (.emit .suffix ⟨0, by omega⟩))
        (true, state.2) input closing output result) := by wrapping_step

theorem close_nil (opening center suffix : List Γ) (state : State (Γ := Γ))
    (input : List Unit) (output result : List Γ) :
    (machine opening center suffix).step (config opening center suffix (some .close) state
      input [] output result) =
      some (config opening center suffix (some .reverse) (false, state.2) input [] output result) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]

theorem reverse_cons (opening center suffix : List Γ) (state : State (Γ := Γ))
    (input closing : List Unit) (head : Γ) (tail result : List Γ) :
    (machine opening center suffix).step (config opening center suffix (some .reverse) state
      input closing (head :: tail) result) =
      some (config opening center suffix (some .reverse) (state.1, some head)
        input closing tail (head :: result)) := by wrapping_step

theorem reverse_nil (opening center suffix : List Γ) (state : State (Γ := Γ))
    (input closing : List Unit) (result : List Γ) :
    (machine opening center suffix).step (config opening center suffix (some .reverse) state
      input closing [] result) =
      some (config opening center suffix none (state.1, none) input closing [] result) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]

omit [Fintype Γ] [Inhabited Γ] in
private theorem suffix_index (opening center suffix : List Γ) (kind : Kind)
    (preceding rest : List Γ) (layout : word opening center suffix kind = preceding ++ rest) :
    preceding.length < limit opening center suffix + 1 := by
  have bound := word_length_le opening center suffix kind
  rw [layout, List.length_append] at bound
  omega

/-- All constant-word emission goes through the same finite position loop. -/
def emit_run (opening center suffix : List Γ) (kind : Kind)
    (preceding rest : List Γ) (layout : word opening center suffix kind = preceding ++ rest)
    (state : State (Γ := Γ)) (input closing : List Unit) (output result : List Γ) :
    EvalsToInTime (machine opening center suffix).step
      (config opening center suffix (some (.emit kind
        ⟨preceding.length, suffix_index opening center suffix kind preceding rest layout⟩))
        state input closing output result)
      (some (config opening center suffix (some (after kind)) state input closing
        (rest.reverse ++ output) result)) (rest.length + 1) := by
  induction rest generalizing preceding output with
  | nil =>
      have stored : (word opening center suffix kind)[preceding.length]? = none := by rw [layout]; simp
      simpa using StackMachineComposition.oneStep
        (emit_end opening center suffix kind _ stored state input closing output result)
  | cons symbol rest ih =>
      let index : Fin (limit opening center suffix + 1) :=
        ⟨preceding.length, suffix_index opening center suffix kind preceding (symbol :: rest) layout⟩
      let nextPrefix := preceding ++ [symbol]
      have nextLayout : word opening center suffix kind = nextPrefix ++ rest := by
        simpa only [nextPrefix, List.append_assoc, List.singleton_append] using layout
      have before : index.val < limit opening center suffix := by
        have bound := word_length_le opening center suffix kind
        rw [layout, List.length_append, List.length_cons] at bound
        dsimp only [index]
        omega
      have nextIndex : advance index =
          ⟨nextPrefix.length, suffix_index opening center suffix kind nextPrefix rest nextLayout⟩ := by
        apply Fin.ext
        rw [advance_value index before]
        simp [index, nextPrefix]
      have stored : (word opening center suffix kind)[index.val]? = some symbol := by simp [index, layout]
      have remaining := ih nextPrefix nextLayout (symbol :: output)
      rw [← nextIndex] at remaining
      have first := StackMachineComposition.oneStep
        (emit_symbol opening center suffix kind index symbol stored state input closing output result)
      simpa only [index, List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first remaining

/-- One marker opens one wrapper and saves one pending closer. -/
def read_run (opening center suffix : List Γ) (input closing : List Unit)
    (output result : List Γ) (state : State (Γ := Γ)) :
    EvalsToInTime (machine opening center suffix).step
      (config opening center suffix (some .read) state input closing output result)
      (some (config opening center suffix (some (.emit .center ⟨0, by omega⟩))
        (false, state.2) [] (input.reverse ++ closing)
        ((List.replicate input.length opening).flatten.reverse ++ output) result))
      (input.length * (opening.length + 2) + 1) := by
  induction input generalizing closing output state with
  | nil =>
      simpa using StackMachineComposition.oneStep
        (read_nil opening center suffix state closing output result)
  | cons marker input ih =>
      cases marker
      have first := StackMachineComposition.oneStep
        (read_cons opening center suffix state input closing output result)
      have emitted := emit_run opening center suffix .opening [] opening rfl
        (true, state.2) input (() :: closing) output result
      have rest := ih (() :: closing) (opening.reverse ++ output) (true, state.2)
      have front := EvalsToInTime.trans _ 1 (opening.length + 1) _ _ _ first emitted
      have joined := EvalsToInTime.trans _ (opening.length + 1 + 1)
        (input.length * (opening.length + 2) + 1) _ _ _ front rest
      simpa [List.length_cons, List.reverse_cons, List.replicate_succ,
        List.flatten_cons, List.reverse_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add, Nat.add_mul, after] using joined

/-- Saved closers are consumed explicitly before reversing the output. -/
def close_run (opening center suffix : List Γ) (closing : List Unit)
    (input : List Unit) (output result : List Γ) (state : State (Γ := Γ)) :
    EvalsToInTime (machine opening center suffix).step
      (config opening center suffix (some .close) state input closing output result)
      (some (config opening center suffix (some .reverse) (false, state.2) input []
        ((List.replicate closing.length suffix).flatten.reverse ++ output) result))
      (closing.length * (suffix.length + 2) + 1) := by
  induction closing generalizing output state with
  | nil =>
      simpa using StackMachineComposition.oneStep
        (close_nil opening center suffix state input output result)
  | cons marker closing ih =>
      cases marker
      have first := StackMachineComposition.oneStep
        (close_cons opening center suffix state input closing output result)
      have emitted := emit_run opening center suffix .suffix [] suffix rfl
        (true, state.2) input closing output result
      have rest := ih (suffix.reverse ++ output) (true, state.2)
      have front := EvalsToInTime.trans _ 1 (suffix.length + 1) _ _ _ first emitted
      have joined := EvalsToInTime.trans _ (suffix.length + 1 + 1)
        (closing.length * (suffix.length + 2) + 1) _ _ _ front rest
      simpa [List.length_cons, List.replicate_succ, List.flatten_cons,
        List.reverse_append, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, Nat.mul_add, Nat.add_mul, after] using joined

def reverse_run (opening center suffix : List Γ) (output result : List Γ)
    (state : State (Γ := Γ)) :
    EvalsToInTime (machine opening center suffix).step
      (config opening center suffix (some .reverse) state [] [] output result)
      (some (config opening center suffix none (state.1, none) [] [] []
        (output.reverse ++ result))) (output.length + 1) := by
  induction output generalizing result state with
  | nil =>
      simpa using StackMachineComposition.oneStep
        (reverse_nil opening center suffix state [] [] result)
  | cons head output ih =>
      have first := StackMachineComposition.oneStep
        (reverse_cons opening center suffix state [] [] head output result)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (output.length + 1) _ _ _ first
          (ih (head :: result) (state.1, some head))

private theorem init_eq (opening center suffix : List Γ) (input : List Unit) :
    initList (machine opening center suffix) input =
      config opening center suffix (some .read) (false, none) input [] [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext stack
  cases stack <;> simp

private theorem halt_eq (opening center suffix : List Γ) (output : List Γ) :
    haltList (machine opening center suffix) output =
      config opening center suffix none (false, none) [] [] [] output := by
  simp only [haltList, machine, config]
  congr 1
  funext stack
  cases stack <;> simp

/-- The emitted word charges every opening, central and closing symbol. -/
def outputs (opening center suffix : List Γ) (count : Nat) :
    TM2OutputsInTime (machine opening center suffix) (List.replicate count ())
      (some (wrapped opening center suffix count))
      (count * (opening.length + suffix.length + 4) + center.length +
        (wrapped opening center suffix count).length + 4) := by
  have first := read_run opening center suffix (List.replicate count ()) [] [] [] (false, none)
  simp only [List.length_replicate, List.reverse_replicate, List.append_nil] at first
  have middle := emit_run opening center suffix .center [] center rfl
    (false, none) [] (List.replicate count ())
    (List.replicate count opening).flatten.reverse []
  have closed := close_run opening center suffix (List.replicate count ()) []
    (center.reverse ++ (List.replicate count opening).flatten.reverse) [] (false, none)
  simp only [List.length_replicate] at closed
  have before := EvalsToInTime.trans _ (count * (opening.length + 2) + 1)
    (center.length + 1) _ _ _ first middle
  have ready := EvalsToInTime.trans _
    (center.length + 1 + (count * (opening.length + 2) + 1))
    (count * (suffix.length + 2) + 1) _ _ _ before closed
  have readyLayout : (List.replicate count suffix).flatten.reverse ++
      (center.reverse ++ (List.replicate count opening).flatten.reverse) =
      (wrapped opening center suffix count).reverse := by
    simp only [wrapped, List.reverse_append, List.append_assoc]
  rw [readyLayout] at ready
  have final := reverse_run opening center suffix (wrapped opening center suffix count).reverse []
    (false, none)
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil] at final
  have joined := EvalsToInTime.trans _
    ((count * (suffix.length + 2) + 1) +
      (center.length + 1 + (count * (opening.length + 2) + 1)))
    ((wrapped opening center suffix count).length + 1) _ _ _ ready final
  change EvalsToInTime _ (initList (machine opening center suffix) (List.replicate count ()))
    (some (haltList (machine opening center suffix) (wrapped opening center suffix count))) _
  rw [init_eq, halt_eq]
  convert joined using 1
  ring

omit [Fintype Γ] [Inhabited Γ] in
theorem wrapped_zero (opening center suffix : List Γ) : wrapped opening center suffix 0 = center := by
  simp [wrapped]

omit [Fintype Γ] [Inhabited Γ] in
theorem wrapped_succ (opening center suffix : List Γ) (count : Nat) :
    wrapped opening center suffix (count + 1) = opening ++ wrapped opening center suffix count ++ suffix := by
  rw [wrapped, List.replicate_succ (a := opening), List.replicate_succ' (a := suffix)]
  simp only [List.flatten_cons, List.flatten_append, List.flatten_nil,
    List.append_nil, wrapped, List.append_assoc]

omit [Fintype Γ] [Inhabited Γ] in
theorem wrapped_length (opening center suffix : List Γ) (count : Nat) :
    (wrapped opening center suffix count).length =
      count * (opening.length + suffix.length) + center.length := by
  induction count with
  | zero => simp [wrapped_zero]
  | succ count ih =>
      rw [wrapped_succ, List.length_append, List.length_append, ih]
      ring

/-- This polynomial is measured against physically supplied markers. The
machine never decodes a represented number and expands it without charge. -/
noncomputable def computable (opening center suffix : List Γ) :
    TM2ComputableInPolyTime (fun count : Nat => List.replicate count ())
      (fun output : List Γ => output) (wrapped opening center suffix) where
  tm := machine opening center suffix
  inputAlphabet := Equiv.refl Unit
  outputAlphabet := Equiv.refl Γ
  time := C (2 * (opening.length + suffix.length + 2)) * X + C (2 * center.length + 4)
  outputsFun count := by
    change TM2OutputsInTime (machine opening center suffix)
      ((List.replicate count ()).map id)
      (some ((wrapped opening center suffix count).map id)) _
    simp only [List.map_id_fun, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, id_eq, List.length_replicate]
    have result := outputs opening center suffix count
    rw [wrapped_length] at result
    convert result using 1
    ring

end Wrapping

end Mettapedia.Computability.WordTemplateMachine
