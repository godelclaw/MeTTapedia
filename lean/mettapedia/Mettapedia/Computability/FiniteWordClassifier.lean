import Mettapedia.Computability.StackMachineComposition
import Mathlib.Data.List.TakeDrop

/-!
# Finite dictionaries over complete words

Each static word has a finite residual cursor. Every dynamic input symbol
advances all still-possible cursors, without retaining unbounded input data in
control registers. Classification chooses the first matching authored entry;
the dynamic word is restored in the output.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Computability.FiniteWordClassifier
open Turing StateTransition Polynomial
open Turing.TM2.Stmt
variable {Γ : Type} [DecidableEq Γ]

abbrev Cursor (word : List Γ) := Option (Fin (word.length + 1))

def initialCursor (word : List Γ) : Cursor word := some ⟨0, by omega⟩

def advance (word : List Γ) (cursor : Cursor word) (symbol : Γ) : Cursor word :=
  cursor.bind fun position =>
    if matched : word[position.val]? = some symbol then
      some ⟨position.val + 1, by
        obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp matched
        omega⟩
    else none

def remaining (word : List Γ) (cursor : Cursor word) : Option (List Γ) :=
  cursor.map fun position => word.drop position.val

def eat (symbol : Γ) (rest : Option (List Γ)) : Option (List Γ) :=
  rest.bind fun word => if word.head? = some symbol then some word.tail else none

def consume : List Γ → Option (List Γ) → Option (List Γ)
  | [], rest => rest
  | symbol :: tail, rest => consume tail (eat symbol rest)

def ready (word : List Γ) (cursor : Cursor word) : Bool :=
  match cursor with
  | none => false
  | some position => position.val == word.length

def walkCursor (word : List Γ) : List Γ → Cursor word → Cursor word
  | [], cursor => cursor
  | symbol :: tail, cursor => walkCursor word tail (advance word cursor symbol)

omit [DecidableEq Γ] in
theorem remaining_initial (word : List Γ) : remaining word (initialCursor word) = some word := by
  simp [remaining, initialCursor]

theorem remaining_advance (word : List Γ) (cursor : Cursor word) (symbol : Γ) :
    remaining word (advance word cursor symbol) = eat symbol (remaining word cursor) := by
  cases cursor with
  | none => simp [advance, remaining, eat]
  | some position =>
      by_cases matched : word[position.val]? = some symbol
      · simp [advance, remaining, eat, matched, List.head?_drop, List.tail_drop]
      · simp [advance, remaining, eat, matched, List.head?_drop]

theorem remaining_walk (word input : List Γ) (cursor : Cursor word) :
    remaining word (walkCursor word input cursor) = consume input (remaining word cursor) := by
  induction input generalizing cursor with
  | nil => rfl
  | cons symbol tail ih => simp only [walkCursor, consume, ih, remaining_advance]

theorem consume_none (input : List Γ) : consume input (none : Option (List Γ)) = none := by
  induction input with
  | nil => rfl
  | cons symbol tail ih => simpa [consume, eat] using ih

theorem consume_empty_iff (input word : List Γ) : consume input (some word) = some [] ↔ input = word := by
  induction input generalizing word with
  | nil => simp [consume]
  | cons symbol tail ih =>
      cases word with
      | nil => simp [consume, eat, consume_none]
      | cons head rest =>
          by_cases same : head = symbol
          · subst head; simp [consume, eat, ih]
          · simp [consume, eat, same, consume_none, List.cons.injEq, Ne.symm same]

omit [DecidableEq Γ] in
theorem ready_iff (word : List Γ) (cursor : Cursor word) :
    ready word cursor = true ↔ remaining word cursor = some [] := by
  cases cursor with
  | none => simp [ready, remaining]
  | some position =>
      simp only [ready, beq_iff_eq, remaining, Option.map_some, Option.some.injEq]
      constructor
      · intro same; rw [same]; simp
      · intro empty
        have size := congrArg List.length empty
        simp only [List.length_drop, List.length_nil] at size
        have bound := position.isLt
        omega

theorem walked_ready_iff (word input : List Γ) :
    ready word (walkCursor word input (initialCursor word)) = true ↔ input = word := by
  rw [ready_iff, remaining_walk, remaining_initial, consume_empty_iff]

variable {n : Nat}
abbrev Residuals (words : Fin n → List Γ) := ∀ index, Cursor (words index)

def initial (words : Fin n → List Γ) : Residuals words := fun index => initialCursor (words index)

def advanceAll (words : Fin n → List Γ) (state : Residuals words) (symbol : Γ) : Residuals words :=
  fun index => advance (words index) (state index) symbol

def walkState (words : Fin n → List Γ) : List Γ → Residuals words → Residuals words
  | [], state => state
  | symbol :: tail, state => walkState words tail (advanceAll words state symbol)

def finish (words : Fin n → List Γ) (state : Residuals words) : Option (Fin n) :=
  (List.finRange n).find? fun index => ready (words index) (state index)

/-- The independent reference searches complete authored words in order. -/
def classify (words : Fin n → List Γ) (input : List Γ) : Option (Fin n) :=
  (List.finRange n).find? fun index => input == words index

theorem walkState_get (words : Fin n → List Γ) (input : List Γ) (state : Residuals words) (index : Fin n) :
    walkState words input state index = walkCursor (words index) input (state index) := by
  induction input generalizing state with
  | nil => rfl
  | cons symbol tail ih => simpa only [walkState, walkCursor, advanceAll] using ih (advanceAll words state symbol)

theorem finish_walk (words : Fin n → List Γ) (input : List Γ) :
    finish words (walkState words input (initial words)) = classify words input := by
  unfold finish classify
  congr 1
  funext index
  apply Bool.eq_iff_iff.mpr
  rw [walkState_get]
  simp only [initial]
  rw [walked_ready_iff]
  simp only [beq_iff_eq]

inductive Stack where
  | input | temporary | result
  deriving DecidableEq, Fintype
inductive Phase where
  | scan | restore
  deriving DecidableEq, Fintype

abbrev Alphabet (Γ : Type) (n : Nat) : Stack → Type
  | .input => Γ
  | .temporary => Γ
  | .result => Sum Γ (Option (Fin n))

abbrev Control (words : Fin n → List Γ) := Residuals words × Option Γ × Option (Fin n)

variable [Fintype Γ] [Inhabited Γ]

def program (words : Fin n → List Γ) (phase : Phase) :
    TM2.Stmt (Alphabet Γ n) Phase (Control words) := match phase with
  | .scan => pop .input (fun state value => (state.1, value, state.2.2))
      (branch (fun state => state.2.1.isSome)
        (push .temporary (fun state => state.2.1.getD default)
          (load (fun state => (advanceAll words state.1 (state.2.1.getD default), state.2.1, state.2.2))
            (goto fun _ => .scan)))
        (load (fun state => (state.1, none, finish words state.1)) (goto fun _ => .restore)))
  | .restore => pop .temporary (fun state value => (state.1, value, state.2.2))
      (branch (fun state => state.2.1.isSome)
        (push .result (fun state => .inl (state.2.1.getD default)) (goto fun _ => .restore))
        (push .result (fun state => .inr state.2.2) (load (fun _ => (initial words, none, none)) halt)))


def machine (words : Fin n → List Γ) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := Alphabet Γ n
  Λ := Phase
  main := .scan
  σ := Control words
  initialState := (initial words, none, none)
  m := program words

/-- The bundled finite machine and the executable statement body use exactly
 the same transition operation; no finite-state enumeration is needed to run it. -/
theorem machine_step (words : Fin n → List Γ) :
    (machine words).step = TM2.step (program words) := rfl

def config (words : Fin n → List Γ) (phase : Option Phase) (cursors : Residuals words)
    (symbol : Option Γ) (tag : Option (Fin n)) (input temporary : List Γ)
    (result : List (Sum Γ (Option (Fin n)))) : (machine words).Cfg where
  l := phase
  var := (cursors, symbol, tag)
  stk key := match (show Stack from key) with
    | .input => input | .temporary => temporary | .result => result

local macro "classifier_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, program, config, TM2.step, TM2.stepAux, Function.update]
  all_goals first
    | rfl
    | (congr 2; funext key; cases key <;> simp [Function.update])))

theorem scan_cons (words : Fin n → List Γ) (cursors : Residuals words) (symbol : Option Γ)
    (tag : Option (Fin n)) (head : Γ) (tail temporary : List Γ) (result : List (Sum Γ (Option (Fin n)))) :
    (machine words).step (config words (some .scan) cursors symbol tag (head :: tail) temporary result) =
      some (config words (some .scan) (advanceAll words cursors head) (some head) tag tail (head :: temporary) result) := by
  classifier_step

theorem scan_nil (words : Fin n → List Γ) (cursors : Residuals words) (symbol : Option Γ)
    (tag : Option (Fin n)) (temporary : List Γ) (result : List (Sum Γ (Option (Fin n)))) :
    (machine words).step (config words (some .scan) cursors symbol tag [] temporary result) =
      some (config words (some .restore) cursors none (finish words cursors) [] temporary result) := by classifier_step

theorem restore_cons (words : Fin n → List Γ) (cursors : Residuals words) (symbol : Option Γ)
    (tag : Option (Fin n)) (head : Γ) (input temporary : List Γ) (result : List (Sum Γ (Option (Fin n)))) :
    (machine words).step (config words (some .restore) cursors symbol tag input (head :: temporary) result) =
      some (config words (some .restore) cursors (some head) tag input temporary (.inl head :: result)) := by classifier_step

theorem restore_nil (words : Fin n → List Γ) (cursors : Residuals words) (symbol : Option Γ)
    (tag : Option (Fin n)) (input : List Γ) (result : List (Sum Γ (Option (Fin n)))) :
    (machine words).step (config words (some .restore) cursors symbol tag input [] result) =
      some (config words none (initial words) none none input [] (.inr tag :: result)) := by classifier_step

noncomputable def scanRun (words : Fin n → List Γ) (input temporary : List Γ)
    (result : List (Sum Γ (Option (Fin n)))) (cursors : Residuals words)
    (symbol : Option Γ) (tag : Option (Fin n)) :
    EvalsToInTime (machine words).step
      (config words (some .scan) cursors symbol tag input temporary result)
      (some (config words (some .restore) (walkState words input cursors) none
        (finish words (walkState words input cursors)) [] (input.reverse ++ temporary) result)) (input.length + 1) := by
  induction input generalizing cursors symbol temporary with
  | nil => simpa only [walkState, List.reverse_nil, List.nil_append, List.length_nil, Nat.zero_add] using
      StackMachineComposition.oneStep (scan_nil words cursors symbol tag temporary result)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (scan_cons words cursors symbol tag head tail temporary result)
      have rest := ih (head :: temporary) (advanceAll words cursors head) (some head)
      simpa [walkState, List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first rest

noncomputable def restoreRun (words : Fin n → List Γ) (temporary input : List Γ)
    (result : List (Sum Γ (Option (Fin n)))) (cursors : Residuals words)
    (symbol : Option Γ) (tag : Option (Fin n)) :
    EvalsToInTime (machine words).step
      (config words (some .restore) cursors symbol tag input temporary result)
      (some (config words none (initial words) none none input []
        (.inr tag :: temporary.reverse.map Sum.inl ++ result))) (temporary.length + 1) := by
  induction temporary generalizing symbol result with
  | nil => simpa using StackMachineComposition.oneStep (restore_nil words cursors symbol tag input result)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (restore_cons words cursors symbol tag head input tail result)
      have rest := ih (.inl head :: result) (some head)
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first rest

theorem init_eq (words : Fin n → List Γ) (input : List Γ) :
    initList (machine words) input = config words (some .scan) (initial words) none none input [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key <;> simp

theorem halt_eq (words : Fin n → List Γ) (output : List (Sum Γ (Option (Fin n)))) :
    haltList (machine words) output = config words none (initial words) none none [] [] output := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key <;> simp

/-- Classification and restoration are actual physical stack operations. The
clock includes every dynamic input symbol and both empty-stack boundaries. -/
noncomputable def outputs (words : Fin n → List Γ) (input : List Γ) :
    TM2OutputsInTime (machine words) input (some (.inr (classify words input) :: input.map Sum.inl))
      (2 * input.length + 2) := by
  have scan := scanRun words input [] [] (initial words) none none
  simp only [List.append_nil] at scan
  have restore := restoreRun words input.reverse [] [] (walkState words input (initial words)) none
    (finish words (walkState words input (initial words)))
  simp only [List.reverse_reverse, List.append_nil, finish_walk] at restore
  rw [finish_walk] at scan
  have run := EvalsToInTime.trans _ _ _ _ _ _ scan restore
  change EvalsToInTime _ (initList (machine words) input)
    (some (haltList (machine words) (.inr (classify words input) :: input.map Sum.inl))) _
  rw [init_eq, halt_eq]
  convert run using 1
  simp only [List.length_reverse]
  omega

omit [Fintype Γ] [Inhabited Γ] in
theorem classify_sound (words : Fin n → List Γ) (input : List Γ) (index : Fin n)
    (accepted : classify words input = some index) : input = words index := by
  simpa only [beq_iff_eq] using List.find?_some accepted

omit [Fintype Γ] [Inhabited Γ] in
theorem classify_none_iff (words : Fin n → List Γ) (input : List Γ) :
    classify words input = none ↔ ∀ index, input ≠ words index := by
  simp [classify, List.find?_eq_none]

noncomputable def computable (words : Fin n → List Γ) : TM2ComputableInPolyTime
    (fun input : List Γ => input) (fun output : List (Sum Γ (Option (Fin n))) => output)
    (fun input => .inr (classify words input) :: input.map Sum.inl) where
  tm := machine words
  inputAlphabet := Equiv.refl Γ
  outputAlphabet := Equiv.refl (Sum Γ (Option (Fin n)))
  time := C 2 * X + C 2
  outputsFun input := by
    change TM2OutputsInTime (machine words) (input.map id)
      (some ((.inr (classify words input) :: input.map Sum.inl).map id)) _
    simp only [List.map_id_fun, id_eq]
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using outputs words input


namespace Union

/-- Membership is retained in finite flags for the fixed authored dictionary.
Complete input words are validated by the same residual classifier. -/
structure State (words : Fin n → List Γ) where
  cursors : Residuals words
  seen : Fin n → Bool
  valid : Bool
  dirty : Bool
  cell : Option (Option Γ)
  deriving Fintype

def initial (words : Fin n → List Γ) : State words :=
  ⟨FiniteWordClassifier.initial words, fun _ => false, true, false, none⟩

def closeWord (words : Fin n → List Γ) (state : State words) : State words :=
  let selected := finish words state.cursors
  { state with
    cursors := FiniteWordClassifier.initial words
    seen := fun index => state.seen index || decide (selected = some index)
    valid := state.valid && selected.isSome
    dirty := false }

def consumeCell (words : Fin n → List Γ) (state : State words) (cell : Option Γ) : State words :=
  match cell with
  | some symbol => { state with
      cursors := advanceAll words state.cursors symbol
      dirty := true
      cell := some cell }
  | none => closeWord words { state with cell := some none }

def walk (words : Fin n → List Γ) : List (Option Γ) → State words → State words
  | [], state => state
  | cell :: rest, state => walk words rest (consumeCell words state cell)

def frame (values : List (List Γ)) : List (Option Γ) :=
  values.flatMap fun word => word.map some ++ [none]

/-- Canonical output follows dictionary order. Repeated input words update
one flag, while an unrecognized word makes the whole union refuse. -/
def emitWire (words : Fin n → List Γ) (seen : Fin n → Bool) (index : Nat) : List (Option Γ) :=
  if inside : index < n then
    (if seen ⟨index,inside⟩ then (words ⟨index,inside⟩).map some ++ [none] else []) ++
      emitWire words seen (index + 1)
  else []
termination_by n - index

def emitCost (words : Fin n → List Γ) (seen : Fin n → Bool) (index : Nat) : Nat :=
  if inside : index < n then
    (if seen ⟨index,inside⟩ then (words ⟨index,inside⟩).length + 2 else 1) +
      emitCost words seen (index + 1)
  else 1
termination_by n - index

def result (words : Fin n → List Γ) (failure success : Γ) (input : List (Option Γ)) : List (Option Γ) :=
  let final := walk words input (initial words)
  if final.valid && !final.dirty then some success :: emitWire words final.seen 0 else [some failure]

inductive Stack where
  | input | temporary | result
  deriving DecidableEq, Fintype

inductive Phase (words : Fin n → List Γ) where
  | scan | finish
  | emit (index : Fin (n + 1))
  | word (index : Fin n) (position : Fin ((words index).length + 1))
  | reverse
  deriving DecidableEq, Fintype

abbrev Cells (_ : Stack) := Option Γ

/-- Only the fixed dictionary and finite cursors occur in control. Dynamic
payload symbols are consumed directly from the physical input stack. -/
def program (words : Fin n → List Γ) (failure success : Γ) (phase : Phase words) :
    TM2.Stmt (Cells (Γ := Γ)) (Phase words) (State words) := match phase with
  | .scan => pop .input (fun state value => { state with cell := value })
      (branch (fun state => state.cell.isSome)
        (load (fun state => consumeCell words state (state.cell.getD none)) (goto fun _ => .scan))
        (goto fun _ => .finish))
  | .finish => branch (fun state => state.valid && !state.dirty)
      (goto fun _ => .emit ⟨0, by omega⟩)
      (push .result (fun _ => some failure) (load (fun _ => initial words) halt))
  | .emit index =>
      if inside : index.val < n then
        branch (fun state => state.seen ⟨index.val,inside⟩)
          (goto fun _ => .word ⟨index.val,inside⟩ ⟨0, by omega⟩)
          (goto fun _ => .emit ⟨index.val + 1, by omega⟩)
      else goto fun _ => .reverse
  | .word index position =>
      if inside : position.val < (words index).length then
        push .temporary (fun _ => some ((words index)[position.val]))
          (goto fun _ => .word index ⟨position.val + 1, by omega⟩)
      else push .temporary (fun _ => none)
        (goto fun _ => .emit ⟨index.val + 1, by omega⟩)
  | .reverse => pop .temporary (fun state value => { state with cell := value })
      (branch (fun state => state.cell.isSome)
        (push .result (fun state => state.cell.getD none) (goto fun _ => .reverse))
        (push .result (fun _ => some success) (load (fun _ => initial words) halt)))

@[implicit_reducible] def machine (words : Fin n → List Γ) (failure success : Γ) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := Cells
  Λ := Phase words
  main := .scan
  σ := State words
  initialState := initial words
  m := program words failure success

def config (words : Fin n → List Γ) (failure success : Γ) (phase : Option (Phase words))
    (state : State words) (input temporary output : List (Option Γ)) : (machine words failure success).Cfg where
  l := phase
  var := state
  stk key := match key with
    | .input => input
    | .temporary => temporary
    | .result => output

local macro "union_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, program, config, consumeCell, closeWord, Turing.TM2.step, Turing.TM2.stepAux, *] <;>
  (funext key; cases key <;> simp [Function.update])))

omit [Inhabited Γ] in
theorem scan_cons (words : Fin n → List Γ) (failure success : Γ) (state : State words)
    (cell : Option Γ) (rest temporary output : List (Option Γ)) :
    (machine words failure success).step (config words failure success (some .scan) state (cell :: rest) temporary output) =
      some (config words failure success (some .scan) (consumeCell words state cell) rest temporary output) := by
  cases cell <;> union_step

omit [Inhabited Γ] in
theorem scan_nil (words : Fin n → List Γ) (failure success : Γ) (state : State words)
    (temporary output : List (Option Γ)) :
    (machine words failure success).step (config words failure success (some .scan) state [] temporary output) =
      some (config words failure success (some .finish) {state with cell := none} [] temporary output) := by union_step

omit [Inhabited Γ] in
theorem finish_accept (words : Fin n → List Γ) (failure success : Γ) (state : State words)
    (accepted : (state.valid && !state.dirty) = true) (temporary output : List (Option Γ)) :
    (machine words failure success).step (config words failure success (some .finish) state [] temporary output) =
      some (config words failure success (some (.emit ⟨0, by omega⟩)) state [] temporary output) := by
  union_step

omit [Inhabited Γ] in
theorem finish_refuse (words : Fin n → List Γ) (failure success : Γ) (state : State words)
    (refused : (state.valid && !state.dirty) = false) (temporary output : List (Option Γ)) :
    (machine words failure success).step (config words failure success (some .finish) state [] temporary output) =
      some (config words failure success none (initial words) [] temporary (some failure :: output)) := by
  cases valid : state.valid <;> cases dirty : state.dirty <;>
    simp [valid, dirty] at refused <;> union_step


omit [Inhabited Γ] in
theorem emit_selected (words : Fin n → List Γ) (failure success : Γ) (state : State words)
    (index : Fin (n + 1)) (inside : index.val < n)
    (selected : state.seen ⟨index.val,inside⟩ = true) (temporary output : List (Option Γ)) :
    (machine words failure success).step (config words failure success (some (.emit index)) state [] temporary output) =
      some (config words failure success (some (.word ⟨index.val,inside⟩ ⟨0, by omega⟩)) state [] temporary output) := by
  union_step

omit [Inhabited Γ] in
theorem emit_skipped (words : Fin n → List Γ) (failure success : Γ) (state : State words)
    (index : Fin (n + 1)) (inside : index.val < n)
    (selected : state.seen ⟨index.val,inside⟩ = false) (temporary output : List (Option Γ)) :
    (machine words failure success).step (config words failure success (some (.emit index)) state [] temporary output) =
      some (config words failure success (some (.emit ⟨index.val + 1, by omega⟩)) state [] temporary output) := by
  union_step

omit [Inhabited Γ] in
theorem emit_end (words : Fin n → List Γ) (failure success : Γ) (state : State words)
    (index : Fin (n + 1)) (ended : ¬ index.val < n) (temporary output : List (Option Γ)) :
    (machine words failure success).step (config words failure success (some (.emit index)) state [] temporary output) =
      some (config words failure success (some .reverse) state [] temporary output) := by
  union_step

omit [Inhabited Γ] in
theorem word_cons (words : Fin n → List Γ) (failure success : Γ) (state : State words)
    (index : Fin n) (position : Fin ((words index).length + 1))
    (inside : position.val < (words index).length) (temporary output : List (Option Γ)) :
    (machine words failure success).step (config words failure success (some (.word index position)) state [] temporary output) =
      some (config words failure success (some (.word index ⟨position.val + 1, by omega⟩)) state []
        (some ((words index)[position.val]) :: temporary) output) := by
  union_step

omit [Inhabited Γ] in
theorem word_end (words : Fin n → List Γ) (failure success : Γ) (state : State words)
    (index : Fin n) (position : Fin ((words index).length + 1))
    (ended : ¬ position.val < (words index).length) (temporary output : List (Option Γ)) :
    (machine words failure success).step (config words failure success (some (.word index position)) state [] temporary output) =
      some (config words failure success (some (.emit ⟨index.val + 1, by omega⟩)) state []
        (none :: temporary) output) := by
  union_step

omit [Inhabited Γ] in
theorem reverse_cons (words : Fin n → List Γ) (failure success : Γ) (state : State words)
    (head : Option Γ) (temporary output : List (Option Γ)) :
    (machine words failure success).step (config words failure success (some .reverse) state [] (head :: temporary) output) =
      some (config words failure success (some .reverse) {state with cell := some head} []
        temporary (head :: output)) := by union_step

omit [Inhabited Γ] in
theorem reverse_nil (words : Fin n → List Γ) (failure success : Γ) (state : State words)
    (output : List (Option Γ)) :
    (machine words failure success).step (config words failure success (some .reverse) state [] [] output) =
      some (config words failure success none (initial words) [] [] (some success :: output)) := by union_step

/-- Scanning charges all supplied symbols, even after a failed membership
check; the delimiter cursor is reset after every completed occurrence. -/
noncomputable def scanRun (words : Fin n → List Γ) (failure success : Γ)
    (input temporary output : List (Option Γ)) (state : State words) :
    EvalsToInTime (machine words failure success).step
      (config words failure success (some .scan) state input temporary output)
      (some (config words failure success (some .finish)
        {walk words input state with cell := none} [] temporary output)) (input.length + 1) := by
  induction input generalizing state with
  | nil => exact StackMachineComposition.oneStep (scan_nil words failure success state temporary output)
  | cons cell rest ih =>
      have first := StackMachineComposition.oneStep (scan_cons words failure success state cell rest temporary output)
      have next := ih (consumeCell words state cell)
      simpa only [walk, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ _ _ _ _ _ first next

noncomputable def wordRun (words : Fin n → List Γ) (failure success : Γ) (state : State words)
    (index : Fin n) (position : Fin ((words index).length + 1)) (temporary output : List (Option Γ)) :
    EvalsToInTime (machine words failure success).step
      (config words failure success (some (.word index position)) state [] temporary output)
      (some (config words failure success (some (.emit ⟨index.val + 1, by omega⟩)) state []
        ((none :: (((words index).drop position.val).map some).reverse) ++ temporary) output))
      ((words index).length - position.val + 1) := by
  by_cases inside : position.val < (words index).length
  · have first := StackMachineComposition.oneStep
      (word_cons words failure success state index position inside temporary output)
    have next := wordRun words failure success state index ⟨position.val + 1, by omega⟩
      (some ((words index)[position.val]) :: temporary) output
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first next
    dsimp only at joined
    rw [List.drop_eq_getElem_cons inside]
    convert joined using 1
    · simp only [List.map_cons, List.reverse_cons, List.cons_append, List.append_assoc, List.nil_append]
    · omega
  · have same : position.val = (words index).length := by omega
    simpa only [same, List.drop_length, List.map_nil, List.reverse_nil, List.cons_append,
      List.nil_append, Nat.sub_self, Nat.zero_add] using
      StackMachineComposition.oneStep (word_end words failure success state index position inside temporary output)
termination_by (words index).length - position.val

noncomputable def reverseRun (words : Fin n → List Γ) (failure success : Γ) (state : State words)
    (temporary output : List (Option Γ)) :
    EvalsToInTime (machine words failure success).step
      (config words failure success (some .reverse) state [] temporary output)
      (some (config words failure success none (initial words) [] []
        (some success :: (temporary.reverse ++ output)))) (temporary.length + 1) := by
  induction temporary generalizing state output with
  | nil => simpa using StackMachineComposition.oneStep (reverse_nil words failure success state output)
  | cons head rest ih =>
      have first := StackMachineComposition.oneStep (reverse_cons words failure success state head rest output)
      have next := ih {state with cell := some head} (head :: output)
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ _ _ _ _ _ first next


/-- Every selected dictionary word is emitted once in dictionary order.
The physical temporary stack is reversed before the status is added. -/
noncomputable def emitRun (words : Fin n → List Γ) (failure success : Γ) (state : State words)
    (index : Fin (n + 1)) (temporary output : List (Option Γ)) :
    EvalsToInTime (machine words failure success).step
      (config words failure success (some (.emit index)) state [] temporary output)
      (some (config words failure success (some .reverse) state []
        ((emitWire words state.seen index.val).reverse ++ temporary) output))
      (emitCost words state.seen index.val) := by
  by_cases inside : index.val < n
  · let entry : Fin n := ⟨index.val,inside⟩
    cases selected : state.seen ⟨index.val,inside⟩ with
    | false =>
        have first := StackMachineComposition.oneStep
          (emit_skipped words failure success state index inside selected temporary output)
        have next := emitRun words failure success state ⟨index.val + 1, by omega⟩ temporary output
        have joined := EvalsToInTime.trans _ _ _ _ _ _ first next
        rw [emitWire,emitCost]
        simpa only [dif_pos inside, selected, Bool.false_eq_true, ↓reduceIte, List.nil_append,
          Fin.val_mk, Nat.add_comm] using joined
    | true =>
        have first := StackMachineComposition.oneStep
          (emit_selected words failure success state index inside selected temporary output)
        have copied := wordRun words failure success state entry ⟨0, by omega⟩ temporary output
        have next := emitRun words failure success state ⟨index.val + 1, by omega⟩
          ((none :: ((words entry).map some).reverse) ++ temporary) output
        have joined := EvalsToInTime.trans _ _ _ _ _ _
          (EvalsToInTime.trans _ _ _ _ _ _ first copied) next
        rw [emitWire,emitCost]
        convert joined using 1 <;>
          simp [inside, selected, entry, List.reverse_append, List.append_assoc]
        omega
  · rw [emitWire,emitCost]
    simpa only [dif_neg inside,List.nil_append,List.reverse_nil] using
      StackMachineComposition.oneStep (emit_end words failure success state index inside temporary output)
termination_by n - index.val

omit [Inhabited Γ] in
theorem init_eq (words : Fin n → List Γ) (failure success : Γ) (input : List (Option Γ)) :
    initList (machine words failure success) input = config words failure success (some .scan) (initial words) input [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key <;> simp

omit [Inhabited Γ] in
theorem halt_eq (words : Fin n → List Γ) (failure success : Γ) (output : List (Option Γ)) :
    haltList (machine words failure success) output = config words failure success none (initial words) [] [] output := by
  simp only [haltList,machine,config]
  congr 1
  funext key
  cases key <;> simp

/-- All framed packets execute, including unknown words and unfinished final
words. The successful clock includes dictionary emission and output reversal. -/
noncomputable def outputsExact (words : Fin n → List Γ) (failure success : Γ) (input : List (Option Γ)) :
    TM2OutputsInTime (machine words failure success) input (some (result words failure success input))
      (input.length + 3 + emitCost words (walk words input (initial words)).seen 0 +
        (emitWire words (walk words input (initial words)).seen 0).length) := by
  let final : State words := {walk words input (initial words) with cell := none}
  have scanned := scanRun words failure success input [] [] (initial words)
  cases accepted : (final.valid && !final.dirty) with
  | false =>
      have refused := StackMachineComposition.oneStep (finish_refuse words failure success final accepted [] [])
      have run := EvalsToInTime.trans _ _ _ _ _ _ scanned refused
      change EvalsToInTime _ (initList (machine words failure success) input)
        (some (haltList (machine words failure success) (result words failure success input))) _
      rw [init_eq,halt_eq]
      have expected : result words failure success input = [some failure] := by
        simp only [result, show ((walk words input (initial words)).valid &&
          !(walk words input (initial words)).dirty) = false from accepted, Bool.false_eq_true, ↓reduceIte]
      rw [expected]
      exact ⟨run.toEvalsTo, le_trans run.steps_le_m (by omega)⟩
  | true =>
      have admitted := StackMachineComposition.oneStep (finish_accept words failure success final accepted [] [])
      have emitted := emitRun words failure success final ⟨0, by omega⟩ [] []
      have reversed := reverseRun words failure success final
        (emitWire words final.seen 0).reverse []
      simp only [List.append_nil] at emitted reversed
      simp only [List.reverse_reverse] at reversed
      have run := EvalsToInTime.trans _ _ _ _ _ _
        (EvalsToInTime.trans _ _ _ _ _ _ (EvalsToInTime.trans _ _ _ _ _ _ scanned admitted) emitted) reversed
      change EvalsToInTime _ (initList (machine words failure success) input)
        (some (haltList (machine words failure success) (result words failure success input))) _
      rw [init_eq,halt_eq]
      have expected : result words failure success input = some success :: emitWire words final.seen 0 := by
        simp only [result, show ((walk words input (initial words)).valid &&
          !(walk words input (initial words)).dirty) = true from accepted, ↓reduceIte]
        rfl
      rw [expected]
      convert run using 1
      simp only [List.length_reverse]
      dsimp only [final]
      omega


def basisBytes (words : Fin n → List Γ) : Nat := ∑ index : Fin n, (words index).length

omit [DecidableEq Γ] [Fintype Γ] [Inhabited Γ] in
theorem word_length_le (words : Fin n → List Γ) (index : Fin n) : (words index).length ≤ basisBytes words := by
  exact Finset.single_le_sum (fun entry _ => Nat.zero_le ((words entry).length)) (Finset.mem_univ index)

omit [DecidableEq Γ] [Fintype Γ] [Inhabited Γ] in
theorem emitWire_length_le (words : Fin n → List Γ) (seen : Fin n → Bool) (index : Nat) :
    (emitWire words seen index).length ≤ (n - index) * (basisBytes words + 1) := by
  rw [emitWire]
  by_cases inside : index < n
  · simp only [dif_pos inside,List.length_append]
    have later := emitWire_length_le words seen (index + 1)
    have headBound : (if seen ⟨index,inside⟩ then (words ⟨index,inside⟩).map some ++ [none] else []).length ≤
        basisBytes words + 1 := by
      split
      · simpa only [List.length_append,List.length_map,List.length_singleton] using
          Nat.add_le_add_right (word_length_le words ⟨index,inside⟩) 1
      · simp
    have difference : n - index = (n - (index + 1)) + 1 := by omega
    calc
      _ ≤ (basisBytes words + 1) + ((n - (index + 1)) * (basisBytes words + 1)) := Nat.add_le_add headBound later
      _ = (n - index) * (basisBytes words + 1) := by rw [difference,Nat.add_mul]; omega
  · simp only [dif_neg inside,List.length_nil]; omega
termination_by n - index

omit [DecidableEq Γ] [Fintype Γ] [Inhabited Γ] in
theorem emitCost_le (words : Fin n → List Γ) (seen : Fin n → Bool) (index : Nat) :
    emitCost words seen index ≤ (n - index) * (basisBytes words + 2) + 1 := by
  rw [emitCost]
  by_cases inside : index < n
  · simp only [dif_pos inside]
    have later := emitCost_le words seen (index + 1)
    have headBound : (if seen ⟨index,inside⟩ then (words ⟨index,inside⟩).length + 2 else 1) ≤
        basisBytes words + 2 := by
      split
      · exact Nat.add_le_add_right (word_length_le words ⟨index,inside⟩) 2
      · omega
    have difference : n - index = (n - (index + 1)) + 1 := by omega
    calc
      _ ≤ (basisBytes words + 2) + ((n - (index + 1)) * (basisBytes words + 2) + 1) := Nat.add_le_add headBound later
      _ = (n - index) * (basisBytes words + 2) + 1 := by rw [difference,Nat.add_mul]; omega
  · simp only [dif_neg inside]; omega
termination_by n - index

/-- The all-input bound includes malformed framing, complete-word membership
checks, canonical dictionary-order emission and physical scratch cleanup. -/
noncomputable def outputs (words : Fin n → List Γ) (failure success : Γ) (input : List (Option Γ)) :
    TM2OutputsInTime (machine words failure success) input (some (result words failure success input))
      (input.length + 2 * (n * (basisBytes words + 2)) + 4) := by
  have ran := outputsExact words failure success input
  have cost := emitCost_le words (walk words input (initial words)).seen 0
  have output := emitWire_length_le words (walk words input (initial words)).seen 0
  simp only [Nat.sub_zero] at cost output
  have upper : n * (basisBytes words + 1) ≤ n * (basisBytes words + 2) :=
    Nat.mul_le_mul_left n (by omega)
  exact ⟨ran.toEvalsTo, le_trans ran.steps_le_m (by omega)⟩

/-- Polynomial realizability is witnessed by this same finite-alphabet
machine, with an attached linear clock for the fixed authored dictionary. -/
noncomputable def computable (words : Fin n → List Γ) (failure success : Γ) : TM2ComputableInPolyTime id id
    (result words failure success) where
  tm := machine words failure success
  inputAlphabet := Equiv.refl (Option Γ)
  outputAlphabet := Equiv.refl (Option Γ)
  time := X + C (2 * (n * (basisBytes words + 2)) + 4)
  outputsFun input := by
    change TM2OutputsInTime (machine words failure success) (input.map id)
      (some ((result words failure success input).map id)) _
    simp only [List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
    simpa only [Nat.add_assoc] using outputs words failure success input


omit [Fintype Γ] [Inhabited Γ] in
theorem walk_append (words : Fin n → List Γ) (first second : List (Option Γ)) (state : State words) :
    walk words (first ++ second) state = walk words second (walk words first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons cell rest ih => simpa only [List.cons_append,walk] using ih (consumeCell words state cell)

omit [Fintype Γ] [Inhabited Γ] in
/-- A completed physical frame performs the original complete-word lookup,
then retains its membership flag and resets the cursor for the next word. -/
theorem walk_delimited (words : Fin n → List Γ) (word : List Γ) (state : State words) :
    walk words (word.map some ++ [none]) state =
      {state with
        cursors := FiniteWordClassifier.initial words
        seen := fun index => state.seen index || decide (finish words (walkState words word state.cursors) = some index)
        valid := state.valid && (finish words (walkState words word state.cursors)).isSome
        dirty := false
        cell := some none} := by
  induction word generalizing state with
  | nil => rfl
  | cons symbol rest ih =>
      simpa only [List.map_cons,List.cons_append,walk,consumeCell,walkState] using
        ih {state with cursors := advanceAll words state.cursors symbol, dirty := true, cell := some (some symbol)}

def includeWord (words : Fin n → List Γ) (word : List Γ) (state : State words) : State words :=
  {state with
    cursors := FiniteWordClassifier.initial words
    seen := fun index => state.seen index || decide (classify words word = some index)
    valid := state.valid && (classify words word).isSome
    dirty := false
    cell := some none}

def foldWords (words : Fin n → List Γ) : List (List Γ) → State words → State words
  | [], state => state
  | word :: rest, state => foldWords words rest (includeWord words word state)

omit [Fintype Γ] [Inhabited Γ] in
theorem walk_frame (words : Fin n → List Γ) (values : List (List Γ)) (state : State words)
    (fresh : state.cursors = FiniteWordClassifier.initial words) :
    walk words (frame values) state = foldWords words values state := by
  induction values generalizing state with
  | nil => rfl
  | cons word rest ih =>
      change walk words ((word.map some ++ [none]) ++ frame rest) state =
        foldWords words rest (includeWord words word state)
      rw [walk_append,walk_delimited,fresh,finish_walk]
      exact ih (includeWord words word state) rfl

omit [Fintype Γ] [Inhabited Γ] in
theorem foldWords_valid (words : Fin n → List Γ) (values : List (List Γ)) (state : State words) :
    (foldWords words values state).valid = (state.valid && values.all (fun word => (classify words word).isSome)) := by
  induction values generalizing state with
  | nil => simp [foldWords]
  | cons word rest ih => simp only [foldWords,ih,includeWord,List.all_cons,Bool.and_assoc]

omit [Fintype Γ] [Inhabited Γ] in
theorem foldWords_dirty (words : Fin n → List Γ) (values : List (List Γ)) (state : State words)
    (clean : state.dirty = false) : (foldWords words values state).dirty = false := by
  induction values generalizing state with
  | nil => exact clean
  | cons word rest ih => exact ih (includeWord words word state) rfl

omit [Fintype Γ] [Inhabited Γ] in
theorem foldWords_seen (words : Fin n → List Γ) (values : List (List Γ)) (state : State words) (index : Fin n) :
    (foldWords words values state).seen index = true ↔
      state.seen index = true ∨ ∃ word ∈ values, classify words word = some index := by
  induction values generalizing state with
  | nil => simp [foldWords]
  | cons word rest ih =>
      simp only [foldWords,ih,includeWord,Bool.or_eq_true,decide_eq_true_eq,List.mem_cons]
      aesop

omit [Fintype Γ] [Inhabited Γ] in
/-- Every framed occurrence must belong to the authored dictionary. Output
membership is a set union; authored dictionary order determines serialization. -/
theorem result_frame (words : Fin n → List Γ) (failure success : Γ) (values : List (List Γ)) :
    result words failure success (frame values) =
      if values.all (fun word => (classify words word).isSome) then
        some success :: emitWire words (foldWords words values (initial words)).seen 0
      else [some failure] := by
  have clean := foldWords_dirty words values (initial words) rfl
  unfold result
  rw [walk_frame words values (initial words) rfl]
  dsimp only
  rw [foldWords_valid,clean]
  simp [initial]

omit [Fintype Γ] [Inhabited Γ] in
theorem classify_self (words : Fin n → List Γ) (distinct : Function.Injective words) (index : Fin n) :
    classify words (words index) = some index := by
  cases found : classify words (words index) with
  | none => exact False.elim ((classify_none_iff words (words index)).mp found index rfl)
  | some selected =>
      have same := distinct (classify_sound words (words index) selected found)
      subst selected
      rfl

omit [Fintype Γ] [Inhabited Γ] in
theorem seen_frame_iff (words : Fin n → List Γ) (distinct : Function.Injective words)
    (values : List (List Γ)) (index : Fin n) :
    (walk words (frame values) (initial words)).seen index = true ↔ words index ∈ values := by
  rw [walk_frame words values (initial words) rfl,foldWords_seen]
  simp only [initial,Bool.false_eq_true,false_or]
  constructor
  · rintro ⟨word,member,found⟩
    exact (classify_sound words word index found) ▸ member
  · intro member
    exact ⟨words index,member,classify_self words distinct index⟩

end Union

end Mettapedia.Computability.FiniteWordClassifier
