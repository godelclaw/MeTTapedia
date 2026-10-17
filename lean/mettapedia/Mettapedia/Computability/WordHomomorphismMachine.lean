import Mettapedia.Computability.WordTemplateMachine

/-!
# Executed finite-alphabet word homomorphisms

Each input symbol selects a fixed output word. The selected symbol and output
position live in finite registers and labels; input and accumulated output
remain on stacks. Every emitted symbol and the final reversal are charged.
Empty images delete symbols, and arbitrary finite images retain their order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.WordHomomorphismMachine

open Turing StateTransition Polynomial
open Turing.TM2.Stmt
open scoped BigOperators

variable {A B : Type} [Fintype A] [Fintype B] [Inhabited B]

/-- The finite table supplies an explicit bound on every symbol image. -/
def capacity (images : A → List B) : Nat := ∑ symbol : A, (images symbol).length

omit [Fintype B] [Inhabited B] in
theorem image_length_le (images : A → List B) (symbol : A) :
    (images symbol).length ≤ capacity images := by
  unfold capacity
  exact Finset.single_le_sum (f := fun value : A => (images value).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ symbol)

inductive Stack where
  | input | output | result
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => A
  | .output | .result => B

inductive Phase (limit : Nat) where
  | read | emit (index : Fin (limit + 1)) | reverse
  deriving DecidableEq, Fintype

abbrev State := Option A × Option B

private def selected (images : A → List B) (index : Nat) (state : State (A := A) (B := B)) : Option B :=
  (state.1.map fun symbol => (images symbol)[index]?).join

/-- The finite transition table operates directly on symbols and counters.
It does not construct a machine's finite-state enumeration during execution. -/
def program (images : A → List B) (phase : Phase (capacity images)) :
    TM2.Stmt (Alphabet (A := A) (B := B)) (Phase (capacity images)) (State (A := A) (B := B)) :=
  match phase with
    | .read => pop .input (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome)
          (goto fun _ => .emit ⟨0, by omega⟩) (goto fun _ => .reverse))
    | .emit index => branch (fun state => (selected images index.val state).isSome)
        (push .output (fun state => (selected images index.val state).getD default)
          (goto fun _ => .emit (WordTemplateMachine.advance index)))
        (goto fun _ => .read)
    | .reverse => pop .output (fun state value => (state.1, value))
        (branch (fun state => state.2.isSome)
          (push .result (fun state => state.2.getD default) (goto fun _ => .reverse)) halt)


/-- The table is compiled into the finite transition function. No input word,
output word or unbounded index is stored in the machine register. -/
def machine (images : A → List B) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := Alphabet (A := A) (B := B)
  Λ := Phase (capacity images)
  main := .read
  σ := State (A := A) (B := B)
  initialState := (none, none)
  m := program images

theorem machine_step (images : A → List B) :
    (machine images).step = TM2.step (program images) := rfl

def config (images : A → List B) (phase : Option (Phase (capacity images)))
    (state : State (A := A) (B := B)) (input : List A) (output result : List B) :
    (machine images).Cfg where
  l := phase
  var := state
  stk stack := match stack with | .input => input | .output => output | .result => result

theorem read_cons (images : A → List B) (state : State (A := A) (B := B))
    (head : A) (tail : List A) (output result : List B) :
    (machine images).step (config images (some .read) state (head :: tail) output result) =
      some (config images (some (.emit ⟨0, by omega⟩)) (some head, state.2) tail output result) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]
  funext stack
  cases stack <;> simp [Function.update]

theorem read_nil (images : A → List B) (state : State (A := A) (B := B)) (output result : List B) :
    (machine images).step (config images (some .read) state [] output result) =
      some (config images (some .reverse) (none, state.2) [] output result) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]

theorem emit_symbol (images : A → List B) (symbol : A) (index : Fin (capacity images + 1))
    (value : B) (stored : (images symbol)[index.val]? = some value)
    (state : Option B) (input : List A) (output result : List B) :
    (machine images).step (config images (some (.emit index)) (some symbol, state) input output result) =
      some (config images (some (.emit (WordTemplateMachine.advance index)))
        (some symbol, state) input (value :: output) result) := by
  simp [FinTM2.step, machine, program, config, selected, stored, Turing.TM2.step, Turing.TM2.stepAux]
  funext stack
  cases stack <;> simp [Function.update]

theorem emit_end (images : A → List B) (symbol : A) (index : Fin (capacity images + 1))
    (stored : (images symbol)[index.val]? = none)
    (state : Option B) (input : List A) (output result : List B) :
    (machine images).step (config images (some (.emit index)) (some symbol, state) input output result) =
      some (config images (some .read) (some symbol, state) input output result) := by
  simp [FinTM2.step, machine, program, config, selected, stored, Turing.TM2.step, Turing.TM2.stepAux]

theorem reverse_cons (images : A → List B) (state : State (A := A) (B := B))
    (input : List A) (head : B) (tail result : List B) :
    (machine images).step (config images (some .reverse) state input (head :: tail) result) =
      some (config images (some .reverse) (state.1, some head) input tail (head :: result)) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]
  funext stack
  cases stack <;> simp [Function.update]

theorem reverse_nil (images : A → List B) (state : State (A := A) (B := B))
    (input : List A) (result : List B) :
    (machine images).step (config images (some .reverse) state input [] result) =
      some (config images none (state.1, none) input [] result) := by
  simp [FinTM2.step, machine, program, config, Turing.TM2.step, Turing.TM2.stepAux]

omit [Fintype B] [Inhabited B] in
private theorem suffix_index (images : A → List B) (symbol : A) (preceding rest : List B)
    (layout : images symbol = preceding ++ rest) : preceding.length < capacity images + 1 := by
  have bound := image_length_le images symbol
  rw [layout, List.length_append] at bound
  omega

/-- Emission visits the finite position of every selected output symbol. -/
def emit_run (images : A → List B) (symbol : A) (preceding rest : List B)
    (layout : images symbol = preceding ++ rest) (state : Option B)
    (input : List A) (output result : List B) :
    EvalsToInTime (machine images).step
      (config images (some (.emit ⟨preceding.length, suffix_index images symbol preceding rest layout⟩))
        (some symbol, state) input output result)
      (some (config images (some .read) (some symbol, state) input (rest.reverse ++ output) result))
      (rest.length + 1) := by
  induction rest generalizing preceding output with
  | nil =>
    have stored : (images symbol)[preceding.length]? = none := by rw [layout]; simp
    simpa using StackMachineComposition.oneStep (emit_end images symbol _ stored state input output result)
  | cons value rest ih =>
    let index : Fin (capacity images + 1) :=
      ⟨preceding.length, suffix_index images symbol preceding (value :: rest) layout⟩
    let nextPrefix := preceding ++ [value]
    have nextLayout : images symbol = nextPrefix ++ rest := by
      simpa only [nextPrefix, List.append_assoc, List.singleton_append] using layout
    have before : index.val < capacity images := by
      have bound := image_length_le images symbol
      rw [layout, List.length_append, List.length_cons] at bound
      dsimp only [index]
      omega
    have nextIndex : WordTemplateMachine.advance index =
        ⟨nextPrefix.length, suffix_index images symbol nextPrefix rest nextLayout⟩ := by
      apply Fin.ext
      rw [WordTemplateMachine.advance_value index before]
      simp [index, nextPrefix]
    have stored : (images symbol)[index.val]? = some value := by simp [index, layout]
    have remaining := ih nextPrefix nextLayout (value :: output)
    rw [← nextIndex] at remaining
    have first := StackMachineComposition.oneStep
      (emit_symbol images symbol index value stored state input output result)
    simpa only [index, List.length_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, Nat.add_assoc] using
      EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first remaining

/-- The input pass leaves the complete output in reverse physical order. -/
def read_run (images : A → List B) (input : List A) (output result : List B)
    (state : State (A := A) (B := B)) :
    EvalsToInTime (machine images).step
      (config images (some .read) state input output result)
      (some (config images (some .reverse) (none, state.2) []
        ((input.flatMap images).reverse ++ output) result))
      (2 * input.length + (input.flatMap images).length + 1) := by
  induction input generalizing output state with
  | nil => simpa using StackMachineComposition.oneStep (read_nil images state output result)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep (read_cons images state head tail output result)
    have emitted := emit_run images head [] (images head) (by simp) state.2 tail output result
    have remaining := ih ((images head).reverse ++ output) (some head, state.2)
    have front := EvalsToInTime.trans _ 1 ((images head).length + 1) _ _ _ first emitted
    have joined := EvalsToInTime.trans _ ((images head).length + 1 + 1)
      (2 * tail.length + (tail.flatMap images).length + 1) _ _ _ front remaining
    simpa [List.flatMap_cons, List.reverse_append, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using joined

def reverse_run (images : A → List B) (output result : List B)
    (state : State (A := A) (B := B)) :
    EvalsToInTime (machine images).step
      (config images (some .reverse) state [] output result)
      (some (config images none (state.1, none) [] [] (output.reverse ++ result)))
      (output.length + 1) := by
  induction output generalizing result state with
  | nil => simpa using StackMachineComposition.oneStep (reverse_nil images state [] result)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep (reverse_cons images state [] head tail result)
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first (ih (head :: result) (state.1, some head))

private theorem init_eq (images : A → List B) (word : List A) :
    initList (machine images) word = config images (some .read) (none, none) word [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext stack
  cases stack <;> simp

private theorem halt_eq (images : A → List B) (word : List B) :
    haltList (machine images) word = config images none (none, none) [] [] word := by
  simp only [haltList, machine, config]
  congr 1
  funext stack
  cases stack <;> simp

/-- Execution charges input traversal, every emitted symbol and reversal. -/
def outputs (images : A → List B) (word : List A) :
    TM2OutputsInTime (machine images) word (some (word.flatMap images))
      (2 * word.length + 2 * (word.flatMap images).length + 2) := by
  have read := read_run images word [] [] (none, none)
  simp only [List.append_nil] at read
  have reversed := reverse_run images (word.flatMap images).reverse [] (none, none)
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil] at reversed
  change EvalsToInTime _ (initList (machine images) word)
    (some (haltList (machine images) (word.flatMap images))) _
  rw [init_eq images word, halt_eq images (word.flatMap images)]
  have joined := EvalsToInTime.trans _ (2 * word.length + (word.flatMap images).length + 1)
    ((word.flatMap images).length + 1) _ _ _ read reversed
  convert joined using 1
  ring

omit [Fintype B] [Inhabited B] in
theorem output_length_le (images : A → List B) (word : List A) :
    (word.flatMap images).length ≤ capacity images * word.length := by
  induction word with
  | nil => simp
  | cons head tail ih =>
    have bound := image_length_le images head
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- The polynomial clock is proved from the concrete transition count and
the fixed finite image table, including empty input and empty symbol images. -/
noncomputable def realization (images : A → List B) :
    TM2ComputableInPolyTime id id (fun word : List A => word.flatMap images) where
  tm := machine images
  inputAlphabet := Equiv.refl A
  outputAlphabet := Equiv.refl B
  time := C (2 + 2 * capacity images) * X + C 2
  outputsFun word := by
    change TM2OutputsInTime (machine images) (word.map id) (some ((word.flatMap images).map id)) _
    simp only [List.map_id_fun]
    have run := outputs images word
    refine ⟨run.toEvalsTo, run.steps_le_m.trans ?_⟩
    have lengthBound := output_length_le images word
    simp only [id_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    nlinarith

end Mettapedia.Computability.WordHomomorphismMachine
