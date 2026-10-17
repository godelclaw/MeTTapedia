import Mettapedia.Computability.FramedWordDecoding
import Mettapedia.Computability.StackMachineComposition
import Mettapedia.Computability.WordEqualityMachine

/-!
# Physical pairing of two ordered framed streams

Two independently tagged streams are copied into physical stacks. Each field
of the first stream is paired with the corresponding field of the second.
The result retains empty fields, order and repeated occurrences. A missing
success tag or unequal field count refuses and clears the entire work arena.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Computability.FramedWordPairing
open Turing StateTransition Turing.TM2.Stmt
open WordTemplateMachine
variable {Γ : Type} [Fintype Γ] [DecidableEq Γ]
abbrev Cell := Option (Option Γ) ⊕ Bool
abbrev Register := Option (Cell (Γ := Γ))
inductive Stack where
  | input | first | second | temporary | accumulator | result
  deriving DecidableEq, Fintype
inductive Phase where
  | tag (side : Bool) | copy (side : Bool) | restore (side : Bool)
  | checkEnd | firstStart | firstField | secondField | secondEnd | reverse
  | reject (key : Stack) | refuse
  deriving DecidableEq, Fintype

def streamKey (side : Bool) : Stack := if side then .second else .first

def nextStack : Stack → Option Stack
  | .input => some .first | .first => some .second | .second => some .temporary
  | .temporary => some .accumulator | .accumulator => some .result | .result => none

def fieldCell (value : Option Γ) : Cell (Γ := Γ) := .inl (some value)
def outerDelimiter : Cell (Γ := Γ) := .inl none

def isField : Register (Γ := Γ) → Bool
  | some (.inl (some _)) => true | _ => false

def isByte : Register (Γ := Γ) → Bool
  | some (.inl (some (some _))) => true | _ => false

def statement (accepted : Γ) : Phase → TM2.Stmt (fun _ : Stack => Cell (Γ := Γ)) Phase (Register (Γ := Γ))
  | .tag side => pop .input (fun _ cell => cell)
      (branch (fun cell => decide (cell = some (fieldCell (some accepted))))
        (goto fun _ => .copy side) (goto fun _ => .reject .input))
  | .copy side => pop .input (fun _ cell => cell)
      (branch isField (push .temporary (fun cell => cell.getD (.inr false)) (goto fun _ => .copy side))
        (branch (fun cell => decide (cell = some outerDelimiter)) (goto fun _ => .restore side)
          (goto fun _ => .reject .input)))
  | .restore side => pop .temporary (fun _ cell => cell)
      (branch (fun cell => cell.isSome)
        (push (streamKey side) (fun cell => cell.getD (.inr false)) (goto fun _ => .restore side))
        (goto fun _ => if side then .checkEnd else .tag true))
  | .checkEnd => pop .input (fun _ cell => cell)
      (branch (fun cell => cell.isNone) (goto fun _ => .firstStart) (goto fun _ => .reject .input))
  | .firstStart => pop .first (fun _ cell => cell)
      (branch (fun cell => cell.isNone) (goto fun _ => .secondEnd)
        (branch isByte (push .accumulator (fun cell => cell.getD (.inr false)) (goto fun _ => .firstField))
          (branch (fun cell => decide (cell = some (fieldCell none)))
            (push .accumulator (fun _ => fieldCell none) (goto fun _ => .secondField))
            (goto fun _ => .reject .input))))
  | .firstField => pop .first (fun _ cell => cell)
      (branch isByte (push .accumulator (fun cell => cell.getD (.inr false)) (goto fun _ => .firstField))
        (branch (fun cell => decide (cell = some (fieldCell none)))
          (push .accumulator (fun _ => fieldCell none) (goto fun _ => .secondField))
          (goto fun _ => .reject .input)))
  | .secondField => pop .second (fun _ cell => cell)
      (branch isByte (push .accumulator (fun cell => cell.getD (.inr false)) (goto fun _ => .secondField))
        (branch (fun cell => decide (cell = some (fieldCell none)))
          (push .accumulator (fun _ => fieldCell none)
            (push .accumulator (fun _ => outerDelimiter) (goto fun _ => .firstStart)))
          (goto fun _ => .reject .input)))
  | .secondEnd => pop .second (fun _ cell => cell)
      (branch (fun cell => cell.isNone) (goto fun _ => .reverse) (goto fun _ => .reject .input))
  | .reverse => pop .accumulator (fun _ cell => cell)
      (branch (fun cell => cell.isSome)
        (push .result (fun cell => cell.getD (.inr false)) (goto fun _ => .reverse))
        (push .result (fun _ => .inr true) (load (fun _ => none) halt)))
  | .reject key => pop key (fun _ cell => cell)
      (branch (fun cell => cell.isSome) (goto fun _ => .reject key)
        (goto fun _ => (nextStack key).elim .refuse Phase.reject))
  | .refuse => push .result (fun _ => .inr false) (load (fun _ => none) halt)

def machine (accepted : Γ) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := fun _ => Cell (Γ := Γ)
  Γk₀Fin := inferInstance
  Λ := Phase
  main := .tag false
  σ := Register
  initialState := none
  m := statement accepted

def config (accepted : Γ) (phase : Option Phase) (state : Register (Γ := Γ))
    (input first second temporary accumulator result : List (Cell (Γ := Γ))) : (machine accepted).Cfg where
  l := phase
  var := state
  stk key := match key with
    | .input => input | .first => first | .second => second | .temporary => temporary
    | .accumulator => accumulator | .result => result

def stream (words : List (List Γ)) : List (Cell (Γ := Γ)) := (Indexed.frame words).map fieldCell

def job (first second : List Γ) : List (Cell (Γ := Γ)) :=
  (Indexed.frame [first,second]).map fieldCell ++ [outerDelimiter]

def jobs (first second : List (List Γ)) : List (Cell (Γ := Γ)) :=
  (first.zip second).flatMap fun pair => job pair.1 pair.2

def input (accepted refused : Γ) (first second : Option (List (List Γ))) : List (Cell (Γ := Γ)) :=
  let tagged := fun value : Option (List (List Γ)) => value.elim [some refused]
    (fun words => some accepted :: Indexed.frame words)
  (Indexed.frame [tagged first,tagged second]).map Sum.inl

def output (first second : Option (List (List Γ))) : List (Cell (Γ := Γ)) :=
  match first,second with
  | some left,some right => if left.length = right.length then .inr true :: jobs left right else [.inr false]
  | _,_ => [.inr false]

local macro "pair_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, statement, config, streamKey, fieldCell, outerDelimiter,
    isField, isByte, nextStack, TM2.step, TM2.stepAux]
  all_goals first
    | rfl
    | (funext key; cases key <;> simp [Function.update])
    | (congr 1; funext key; cases key <;> simp [Function.update])))

theorem tag_step (accepted : Γ) (side : Bool) (state : Register (Γ := Γ))
    (input first second temporary accumulator result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some (.tag side)) state
      (fieldCell (some accepted) :: input) first second temporary accumulator result) =
    some (config accepted (some (.copy side)) (some (fieldCell (some accepted)))
      input first second temporary accumulator result) := by pair_step

theorem copy_step (accepted : Γ) (side : Bool) (state : Register (Γ := Γ)) (value : Option Γ)
    (input first second temporary accumulator result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some (.copy side)) state
      (fieldCell value :: input) first second temporary accumulator result) =
    some (config accepted (some (.copy side)) (some (fieldCell value))
      input first second (fieldCell value :: temporary) accumulator result) := by pair_step

theorem copy_end (accepted : Γ) (side : Bool) (state : Register (Γ := Γ))
    (input first second temporary accumulator result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some (.copy side)) state
      (outerDelimiter :: input) first second temporary accumulator result) =
    some (config accepted (some (.restore side)) (some outerDelimiter)
      input first second temporary accumulator result) := by pair_step

theorem restore_step (accepted : Γ) (side : Bool) (state : Register (Γ := Γ)) (value : Cell (Γ := Γ))
    (input first second temporary accumulator result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some (.restore side)) state
      input first second (value :: temporary) accumulator result) =
    some (config accepted (some (.restore side)) (some value) input
      (if side then first else value :: first) (if side then value :: second else second)
      temporary accumulator result) := by cases side <;> pair_step

theorem restore_end (accepted : Γ) (side : Bool) (state : Register (Γ := Γ))
    (input first second accumulator result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some (.restore side)) state
      input first second [] accumulator result) =
    some (config accepted (some (if side then .checkEnd else .tag true)) none
      input first second [] accumulator result) := by cases side <;> pair_step

theorem check_end (accepted : Γ) (state : Register (Γ := Γ))
    (first second accumulator result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some .checkEnd) state [] first second [] accumulator result) =
    some (config accepted (some .firstStart) none [] first second [] accumulator result) := by pair_step

def copyRun (accepted : Γ) (side : Bool) (word : List (Option Γ))
    (state : Register (Γ := Γ)) (input first second temporary accumulator result : List (Cell (Γ := Γ))) :
    EvalsToInTime (machine accepted).step
      (config accepted (some (.copy side)) state
        (word.map fieldCell ++ outerDelimiter :: input) first second temporary accumulator result)
      (some (config accepted (some (.restore side)) (some outerDelimiter)
        input first second ((word.map fieldCell).reverse ++ temporary) accumulator result)) (word.length + 1) := by
  induction word generalizing state temporary with
  | nil => simpa using StackMachineComposition.oneStep (copy_end accepted side state input first second temporary accumulator result)
  | cons value word ih =>
    have one := StackMachineComposition.oneStep (copy_step accepted side state value
      (word.map fieldCell ++ outerDelimiter :: input) first second temporary accumulator result)
    have rest := ih (some (fieldCell value)) (fieldCell value :: temporary)
    have joined := EvalsToInTime.trans _ 1 (word.length + 1) _ _ _ one rest
    simpa only [List.map_cons, List.cons_append, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.nil_append, List.cons_append, List.append_nil, List.length_cons, List.nil_append, List.cons_append, List.append_nil, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

def restoreRun (accepted : Γ) (side : Bool) (word : List (Cell (Γ := Γ)))
    (state : Register (Γ := Γ)) (input first second accumulator result : List (Cell (Γ := Γ))) :
    EvalsToInTime (machine accepted).step
      (config accepted (some (.restore side)) state input first second word accumulator result)
      (some (config accepted (some (if side then .checkEnd else .tag true)) none input
        (if side then first else word.reverse ++ first)
        (if side then word.reverse ++ second else second) [] accumulator result)) (word.length + 1) := by
  induction word generalizing state first second with
  | nil => simpa using StackMachineComposition.oneStep (restore_end accepted side state input first second accumulator result)
  | cons value word ih =>
    have one := StackMachineComposition.oneStep (restore_step accepted side state value input first second word accumulator result)
    have rest := ih (some value) (if side then first else value :: first) (if side then value :: second else second)
    have joined := EvalsToInTime.trans _ 1 (word.length + 1) _ _ _ one rest
    cases side <;> simpa only [Bool.false_eq_true, ↓reduceIte, List.reverse_cons,
      List.append_assoc, List.singleton_append, List.nil_append, List.cons_append, List.append_nil, List.length_cons, ite_true,
      List.nil_append, List.cons_append, List.append_nil, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

theorem first_byte (accepted value : Γ) (start : Bool) (state : Register (Γ := Γ))
    (first second accumulator result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some (if start then .firstStart else .firstField))
      state [] (fieldCell (some value) :: first) second [] accumulator result) =
    some (config accepted (some .firstField) (some (fieldCell (some value)))
      [] first second [] (fieldCell (some value) :: accumulator) result) := by cases start <;> pair_step

theorem first_delimiter (accepted : Γ) (start : Bool) (state : Register (Γ := Γ))
    (first second accumulator result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some (if start then .firstStart else .firstField))
      state [] (fieldCell none :: first) second [] accumulator result) =
    some (config accepted (some .secondField) (some (fieldCell none))
      [] first second [] (fieldCell none :: accumulator) result) := by cases start <;> pair_step

theorem second_byte (accepted value : Γ) (state : Register (Γ := Γ))
    (first second accumulator result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some .secondField) state
      [] first (fieldCell (some value) :: second) [] accumulator result) =
    some (config accepted (some .secondField) (some (fieldCell (some value)))
      [] first second [] (fieldCell (some value) :: accumulator) result) := by pair_step

theorem second_delimiter (accepted : Γ) (state : Register (Γ := Γ))
    (first second accumulator result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some .secondField) state
      [] first (fieldCell none :: second) [] accumulator result) =
    some (config accepted (some .firstStart) (some (fieldCell none))
      [] first second [] (outerDelimiter :: fieldCell none :: accumulator) result) := by pair_step

theorem first_empty (accepted : Γ) (state : Register (Γ := Γ))
    (second accumulator result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some .firstStart) state [] [] second [] accumulator result) =
    some (config accepted (some .secondEnd) none [] [] second [] accumulator result) := by pair_step

theorem second_empty (accepted : Γ) (state : Register (Γ := Γ))
    (accumulator result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some .secondEnd) state [] [] [] [] accumulator result) =
    some (config accepted (some .reverse) none [] [] [] [] accumulator result) := by pair_step

theorem reverse_byte (accepted : Γ) (state : Register (Γ := Γ)) (value : Cell (Γ := Γ))
    (accumulator result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some .reverse) state [] [] [] [] (value :: accumulator) result) =
    some (config accepted (some .reverse) (some value) [] [] [] [] accumulator (value :: result)) := by pair_step

theorem reverse_empty (accepted : Γ) (state : Register (Γ := Γ))
    (result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some .reverse) state [] [] [] [] [] result) =
    some (config accepted none none [] [] [] [] [] (.inr true :: result)) := by pair_step

def firstRun (accepted : Γ) (start : Bool) (word : List Γ) (state : Register (Γ := Γ))
    (first second accumulator result : List (Cell (Γ := Γ))) :
    EvalsToInTime (machine accepted).step
      (config accepted (some (if start then .firstStart else .firstField)) state []
        ((word.map (fun value => fieldCell (some value))) ++ fieldCell none :: first)
        second [] accumulator result)
      (some (config accepted (some .secondField) (some (fieldCell none)) [] first second []
        (fieldCell none :: (word.map (fun value => fieldCell (some value))).reverse ++ accumulator) result))
      (word.length + 1) := by
  induction word generalizing start state accumulator with
  | nil => simpa using StackMachineComposition.oneStep (first_delimiter accepted start state first second accumulator result)
  | cons value word ih =>
    have one := StackMachineComposition.oneStep (first_byte accepted value start state
      (word.map (fun value => fieldCell (some value)) ++ fieldCell none :: first) second accumulator result)
    have rest := ih false (some (fieldCell (some value))) (fieldCell (some value) :: accumulator)
    have joined := EvalsToInTime.trans _ 1 (word.length + 1) _ _ _ one rest
    simpa only [List.map_cons, List.cons_append, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.nil_append, List.cons_append, List.append_nil, List.length_cons, Bool.false_eq_true, ↓reduceIte,
      List.nil_append, List.cons_append, List.append_nil, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

def secondRun (accepted : Γ) (word : List Γ) (state : Register (Γ := Γ))
    (first second accumulator result : List (Cell (Γ := Γ))) :
    EvalsToInTime (machine accepted).step
      (config accepted (some .secondField) state [] first
        (word.map (fun value => fieldCell (some value)) ++ fieldCell none :: second) [] accumulator result)
      (some (config accepted (some .firstStart) (some (fieldCell none)) [] first second []
        (outerDelimiter :: fieldCell none :: (word.map (fun value => fieldCell (some value))).reverse ++ accumulator) result))
      (word.length + 1) := by
  induction word generalizing state accumulator with
  | nil => simpa using StackMachineComposition.oneStep (second_delimiter accepted state first second accumulator result)
  | cons value word ih =>
    have one := StackMachineComposition.oneStep (second_byte accepted value state first
      (word.map (fun value => fieldCell (some value)) ++ fieldCell none :: second) accumulator result)
    have rest := ih (some (fieldCell (some value))) (fieldCell (some value) :: accumulator)
    have joined := EvalsToInTime.trans _ 1 (word.length + 1) _ _ _ one rest
    simpa only [List.map_cons, List.cons_append, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.nil_append, List.cons_append, List.append_nil, List.length_cons, List.nil_append, List.cons_append, List.append_nil, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

omit [Fintype Γ] [DecidableEq Γ] in
theorem stream_cons (word : List Γ) (words : List (List Γ)) :
    stream (word :: words) = word.map (fun value => fieldCell (some value)) ++ fieldCell none :: stream words := by
  simp [stream, Indexed.frame, List.map_append, List.map_map, Function.comp_def]

omit [Fintype Γ] [DecidableEq Γ] in
theorem job_eq (left right : List Γ) : job left right =
    left.map (fun value => fieldCell (some value)) ++ fieldCell none ::
      right.map (fun value => fieldCell (some value)) ++ [fieldCell none,outerDelimiter] := by
  simp [job, Indexed.frame, List.map_append, List.map_map, Function.comp_def, List.append_assoc]

omit [Fintype Γ] [DecidableEq Γ] in
theorem jobs_cons (left right : List Γ) (first second : List (List Γ)) :
    jobs (left :: first) (right :: second) = job left right ++ jobs first second := by
  simp [jobs]

def jobsRun (accepted : Γ) (first second : List (List Γ)) (same : first.length = second.length)
    (state : Register (Γ := Γ)) (accumulator result : List (Cell (Γ := Γ))) :
    EvalsToInTime (machine accepted).step
      (config accepted (some .firstStart) state [] (stream first) (stream second) [] accumulator result)
      (some (config accepted (some .reverse) none [] [] [] [] ((jobs first second).reverse ++ accumulator) result))
      ((stream first).length + (stream second).length + 2) := by
  induction first generalizing second state accumulator with
  | nil =>
    have empty : second = [] := List.eq_nil_iff_length_eq_zero.mpr (by simpa using same.symm)
    subst second
    have one := StackMachineComposition.oneStep (first_empty accepted state [] accumulator result)
    have two := StackMachineComposition.oneStep (second_empty accepted none accumulator result)
    simpa [stream, jobs, Indexed.frame] using EvalsToInTime.trans _ 1 1 _ _ _ one two
  | cons left first ih =>
    cases second with
    | nil => simp at same
    | cons right second =>
      have smaller : first.length = second.length := by simpa using same
      have one := firstRun accepted true left state (stream first) (stream (right :: second)) accumulator result
      rw [stream_cons] at one
      have two := secondRun accepted right (some (fieldCell none)) (stream first) (stream second)
        (fieldCell none :: (left.map (fun value => fieldCell (some value))).reverse ++ accumulator) result
      have later := ih second smaller (some (fieldCell none))
        (outerDelimiter :: fieldCell none :: (right.map (fun value => fieldCell (some value))).reverse ++
          fieldCell none :: (left.map (fun value => fieldCell (some value))).reverse ++ accumulator)
      simp only [List.cons_append, List.append_assoc] at one two later
      have front := EvalsToInTime.trans _ (left.length + 1) (right.length + 1) _ _ _ one two
      have all := EvalsToInTime.trans _ _ _ _ _ _ front later
      convert all using 1
      all_goals simp [stream_cons, job_eq, jobs_cons, List.append_assoc, List.cons_append]
      all_goals omega

def reverseRun (accepted : Γ) (word : List (Cell (Γ := Γ))) (state : Register (Γ := Γ))
    (result : List (Cell (Γ := Γ))) :
    EvalsToInTime (machine accepted).step
      (config accepted (some .reverse) state [] [] [] [] word result)
      (some (config accepted none none [] [] [] [] [] (.inr true :: word.reverse ++ result))) (word.length + 1) := by
  induction word generalizing state result with
  | nil => simpa using StackMachineComposition.oneStep (reverse_empty accepted state result)
  | cons value word ih =>
    have one := StackMachineComposition.oneStep (reverse_byte accepted state value word result)
    have later := ih (some value) (value :: result)
    have all := EvalsToInTime.trans _ 1 (word.length + 1) _ _ _ one later
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append, List.cons_append, List.append_nil, List.length_cons,
      List.cons_append, List.nil_append, List.append_nil, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all
def taggedRun (accepted : Γ) (side : Bool) (word : List (Option Γ)) (state : Register (Γ := Γ))
    (input first second accumulator result : List (Cell (Γ := Γ))) :
    EvalsToInTime (machine accepted).step
      (config accepted (some (.tag side)) state
        (fieldCell (some accepted) :: word.map fieldCell ++ outerDelimiter :: input)
        first second [] accumulator result)
      (some (config accepted (some (if side then .checkEnd else .tag true)) none input
        (if side then first else word.map fieldCell ++ first)
        (if side then word.map fieldCell ++ second else second) [] accumulator result)) (2 * word.length + 3) := by
  have one := StackMachineComposition.oneStep (tag_step accepted side state
    (word.map fieldCell ++ outerDelimiter :: input) first second [] accumulator result)
  have copied := copyRun accepted side word (some (fieldCell (some accepted))) input first second [] accumulator result
  have restored := restoreRun accepted side (word.map fieldCell).reverse (some outerDelimiter) input first second accumulator result
  simp only [List.length_reverse, List.length_map, List.reverse_reverse, List.append_nil] at copied restored
  have front := EvalsToInTime.trans _ 1 (word.length + 1) _ _ _ one copied
  have all := EvalsToInTime.trans _ _ (word.length + 1) _ _ _ front restored
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, two_mul, List.cons_append, Nat.reduceAdd] using all

omit [Fintype Γ] [DecidableEq Γ] in
theorem input_positive (accepted refused : Γ) (first second : List (List Γ)) :
    input accepted refused (some first) (some second) =
      fieldCell (some accepted) :: stream first ++ outerDelimiter ::
        fieldCell (some accepted) :: stream second ++ [outerDelimiter] := by
  simp [input, stream, Indexed.frame, List.map_append, List.map_map, Function.comp_def,
    fieldCell, outerDelimiter, List.append_assoc]
  rfl

def prepareRun (accepted refused : Γ) (first second : List (List Γ)) :
    EvalsToInTime (machine accepted).step
      (config accepted (some (.tag false)) none (input accepted refused (some first) (some second)) [] [] [] [] [])
      (some (config accepted (some .firstStart) none [] (stream first) (stream second) [] [] []))
      (2 * (stream first).length + 2 * (stream second).length + 7) := by
  have one := taggedRun accepted false (Indexed.frame first) none
    (fieldCell (some accepted) :: stream second ++ [outerDelimiter]) [] [] [] []
  have two := taggedRun accepted true (Indexed.frame second) none [] (stream first) [] [] []
  have three := StackMachineComposition.oneStep (check_end accepted none (stream first) (stream second) [] [])
  simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append] at one two
  have front := EvalsToInTime.trans _ _ _ _ _ _ one two
  have all := EvalsToInTime.trans _ _ 1 _ _ _ front three
  rw [input_positive]
  convert all using 1
  all_goals simp [stream, List.append_assoc, List.cons_append]
  all_goals omega

omit [Fintype Γ] [DecidableEq Γ] in
theorem stream_length (words : List (List Γ)) : (stream words).length = (Indexed.frame words).length := by
  simp [stream]

omit [Fintype Γ] [DecidableEq Γ] in
theorem jobs_length (first second : List (List Γ)) (same : first.length = second.length) :
    (jobs first second).length = (stream first).length + (stream second).length + first.length := by
  induction first generalizing second with
  | nil =>
    have empty : second = [] := List.eq_nil_iff_length_eq_zero.mpr (by simpa using same.symm)
    subst second
    simp [jobs, stream, Indexed.frame]
  | cons left first ih =>
    cases second with
    | nil => simp at same
    | cons right second =>
      rw [jobs_cons, job_eq, List.length_append, ih second (by simpa using same)]
      simp only [stream_cons, List.length_append, List.length_cons, List.length_map, List.length_nil]
      omega

omit [Fintype Γ] [DecidableEq Γ] in
theorem input_length (accepted refused : Γ) (first second : List (List Γ)) :
    (input accepted refused (some first) (some second)).length =
      (stream first).length + (stream second).length + 4 := by
  rw [input_positive]
  simp only [List.length_cons, List.length_append, List.length_nil]
  omega

theorem init_eq (accepted : Γ) (word : List (Cell (Γ := Γ))) :
    initList (machine accepted) word = config accepted (some (.tag false)) none word [] [] [] [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key <;> rfl

theorem halt_eq (accepted : Γ) (word : List (Cell (Γ := Γ))) :
    haltList (machine accepted) word = config accepted none none [] [] [] [] [] word := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key <;> rfl

def positiveOutputs (accepted refused : Γ) (first second : List (List Γ)) (same : first.length = second.length) :
    TM2OutputsInTime (machine accepted) (input accepted refused (some first) (some second))
      (some (.inr true :: jobs first second))
      (7 * (input accepted refused (some first) (some second)).length + 20) := by
  have prepared := prepareRun accepted refused first second
  have paired := jobsRun accepted first second same none [] []
  have reversed := reverseRun accepted (jobs first second).reverse none []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at paired reversed
  have front := EvalsToInTime.trans _ _ _ _ _ _ prepared paired
  have all := EvalsToInTime.trans _ _ _ _ _ _ front reversed
  change EvalsToInTime _ (initList _ _) (some (haltList _ _)) _
  rw [init_eq, halt_eq]
  apply WordEqualityMachine.within all
  rw [input_length, jobs_length first second same]
  have count : first.length ≤ (stream first).length := by
    rw [stream_length, Indexed.frame_length]
    omega
  omega

def rawConfig (accepted : Γ) (phase : Option Phase) (state : Register (Γ := Γ))
    (contents : Stack → List (Cell (Γ := Γ))) : (machine accepted).Cfg := ⟨phase,state,contents⟩

theorem reject_byte (accepted : Γ) (key : Stack) (state : Register (Γ := Γ)) (value : Cell (Γ := Γ))
    (word : List (Cell (Γ := Γ))) (contents : Stack → List (Cell (Γ := Γ))) :
    (machine accepted).step (rawConfig accepted (some (.reject key)) state (Function.update contents key (value :: word))) =
      some (rawConfig accepted (some (.reject key)) (some value) (Function.update contents key word)) := by
  simp [FinTM2.step, machine, statement, rawConfig, TM2.step, TM2.stepAux]

theorem reject_empty (accepted : Γ) (key : Stack) (state : Register (Γ := Γ))
    (contents : Stack → List (Cell (Γ := Γ))) :
    (machine accepted).step (rawConfig accepted (some (.reject key)) state (Function.update contents key [])) =
      some (rawConfig accepted (some ((nextStack key).elim .refuse Phase.reject)) none (Function.update contents key [])) := by
  simp [FinTM2.step, machine, statement, rawConfig, TM2.step, TM2.stepAux]

def rejectFieldRun (accepted : Γ) (key : Stack) (word : List (Cell (Γ := Γ))) (state : Register (Γ := Γ))
    (contents : Stack → List (Cell (Γ := Γ))) :
    EvalsToInTime (machine accepted).step
      (rawConfig accepted (some (.reject key)) state (Function.update contents key word))
      (some (rawConfig accepted (some ((nextStack key).elim .refuse Phase.reject)) none (Function.update contents key [])))
      (word.length + 1) := by
  induction word generalizing state with
  | nil => simpa using StackMachineComposition.oneStep (reject_empty accepted key state contents)
  | cons value word ih =>
    have one := StackMachineComposition.oneStep (reject_byte accepted key state value word contents)
    have later := ih (some value)
    simpa only [List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      EvalsToInTime.trans _ 1 (word.length + 1) _ _ _ one later

def clearRun (accepted : Γ) (key : Stack) (state : Register (Γ := Γ))
    (contents : Stack → List (Cell (Γ := Γ))) :
    EvalsToInTime (machine accepted).step (rawConfig accepted (some (.reject key)) state contents)
      (some (rawConfig accepted (some ((nextStack key).elim .refuse Phase.reject)) none (Function.update contents key [])))
      ((contents key).length + 1) := by
  have ran := rejectFieldRun accepted key (contents key) state contents
  have same : Function.update contents key (contents key) = contents := by
    funext other
    by_cases equal : other = key
    · subst other; simp
    · simp [Function.update, equal]
  rw [same] at ran
  exact ran

def arenaSize (contents : Stack → List (Cell (Γ := Γ))) : Nat :=
  (contents .input).length + (contents .first).length + (contents .second).length +
    (contents .temporary).length + (contents .accumulator).length + (contents .result).length

def clearAllRun (accepted : Γ) (state : Register (Γ := Γ)) (contents : Stack → List (Cell (Γ := Γ))) :
    EvalsToInTime (machine accepted).step (rawConfig accepted (some (.reject .input)) state contents)
      (some (rawConfig accepted (some .refuse) none (fun _ => []))) (arenaSize contents + 6) := by
  let a := Function.update contents .input []
  let b := Function.update a .first []
  let c := Function.update b .second []
  let d := Function.update c .temporary []
  let e := Function.update d .accumulator []
  let f := Function.update e .result []
  have r1 := clearRun accepted .input state contents
  have r2 := clearRun accepted .first none a
  have r3 := clearRun accepted .second none b
  have r4 := clearRun accepted .temporary none c
  have r5 := clearRun accepted .accumulator none d
  have r6 := clearRun accepted .result none e
  simp only [nextStack, Option.elim_some, Option.elim_none] at r1 r2 r3 r4 r5 r6
  have j2 := EvalsToInTime.trans _ _ _ _ _ _ r1 r2
  have j3 := EvalsToInTime.trans _ _ _ _ _ _ j2 r3
  have j4 := EvalsToInTime.trans _ _ _ _ _ _ j3 r4
  have j5 := EvalsToInTime.trans _ _ _ _ _ _ j4 r5
  have all := EvalsToInTime.trans _ _ _ _ _ _ j5 r6
  have emptied : f = fun _ => [] := by funext key; cases key <;> simp [f,e,d,c,b,a,Function.update]
  change EvalsToInTime _ _ (some (rawConfig accepted (some .refuse) none f)) _ at all
  rw [emptied] at all
  convert all using 1
  simp [arenaSize,a,b,c,d,e,Function.update]
  omega

theorem refuse_step (accepted : Γ) :
    (machine accepted).step (rawConfig accepted (some .refuse) none (fun _ => [])) =
      some (config accepted none none [] [] [] [] [] [.inr false]) := by
  simp [FinTM2.step, machine, statement, rawConfig, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

def refusalRun (accepted : Γ) (state : Register (Γ := Γ))
    (input first second temporary accumulator result : List (Cell (Γ := Γ))) :
    EvalsToInTime (machine accepted).step
      (config accepted (some (.reject .input)) state input first second temporary accumulator result)
      (some (config accepted none none [] [] [] [] [] [.inr false]))
      (input.length + first.length + second.length + temporary.length + accumulator.length + result.length + 7) := by
  have first := clearAllRun accepted state (config accepted (some (.reject .input)) state
    input first second temporary accumulator result).stk
  have last := StackMachineComposition.oneStep (refuse_step accepted)
  have all := EvalsToInTime.trans _ _ 1 _ _ _ first last
  simpa only [rawConfig, config, arenaSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

theorem tag_refused (accepted refused : Γ) (different : refused ≠ accepted) (side : Bool)
    (state : Register (Γ := Γ)) (input first second temporary accumulator result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some (.tag side)) state
      (fieldCell (some refused) :: input) first second temporary accumulator result) =
      some (config accepted (some (.reject .input)) (some (fieldCell (some refused)))
        input first second temporary accumulator result) := by
  simp [FinTM2.step, machine, statement, config, fieldCell, TM2.step, TM2.stepAux, different]
  funext key
  cases key <;> simp [Function.update]
def firstRefusedOutputs (accepted refused : Γ) (different : refused ≠ accepted)
    (second : Option (List (List Γ))) :
    TM2OutputsInTime (machine accepted) (input accepted refused none second) (some [.inr false])
      (7 * (input accepted refused none second).length + 20) := by
  let tail := (Indexed.frame [second.elim [some refused]
    (fun words => some accepted :: Indexed.frame words)]).map (Sum.inl (β := Bool))
  have encoded : input accepted refused none second = fieldCell (some refused) :: outerDelimiter :: tail := by
    cases second <;> simp [input,tail,Indexed.frame,List.map_append,fieldCell,outerDelimiter]
  have one := StackMachineComposition.oneStep (tag_refused accepted refused different false none
    (outerDelimiter :: tail) [] [] [] [] [])
  have refusedRun := refusalRun accepted (some (fieldCell (some refused))) (outerDelimiter :: tail) [] [] [] [] []
  have all := EvalsToInTime.trans _ 1 _ _ _ _ one refusedRun
  change EvalsToInTime _ (initList _ _) (some (haltList _ _)) _
  rw [init_eq,halt_eq,encoded]
  apply WordEqualityMachine.within all
  simp only [List.length_cons,List.length_nil]
  omega

def secondRefusedOutputs (accepted refused : Γ) (different : refused ≠ accepted)
    (first : List (List Γ)) :
    TM2OutputsInTime (machine accepted) (input accepted refused (some first) none) (some [.inr false])
      (7 * (input accepted refused (some first) none).length + 20) := by
  have encoded : input accepted refused (some first) none =
      fieldCell (some accepted) :: stream first ++ [outerDelimiter,fieldCell (some refused),outerDelimiter] := by
    simp [input,stream,Indexed.frame,List.map_append,List.map_map,Function.comp_def,fieldCell,outerDelimiter,List.append_assoc]
  have prepared := taggedRun accepted false (Indexed.frame first) none
    [fieldCell (some refused),outerDelimiter] [] [] [] []
  simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at prepared
  have one := StackMachineComposition.oneStep (tag_refused accepted refused different true none [outerDelimiter]
    (stream first) [] [] [] [])
  have refusedRun := refusalRun accepted (some (fieldCell (some refused))) [outerDelimiter] (stream first) [] [] [] []
  have front := EvalsToInTime.trans _ _ 1 _ _ _ prepared one
  have all := EvalsToInTime.trans _ _ _ _ _ _ front refusedRun
  change EvalsToInTime _ (initList _ _) (some (haltList _ _)) _
  rw [init_eq,halt_eq,encoded]
  apply WordEqualityMachine.within all
  simp only [List.length_cons,List.length_nil,List.length_append,stream_length]
  omega

theorem second_extra (accepted : Γ) (state : Register (Γ := Γ)) (value : Cell (Γ := Γ))
    (second accumulator result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some .secondEnd) state [] [] (value :: second) [] accumulator result) =
      some (config accepted (some (.reject .input)) (some value) [] [] second [] accumulator result) := by pair_step

theorem second_missing (accepted : Γ) (state : Register (Γ := Γ))
    (first accumulator result : List (Cell (Γ := Γ))) :
    (machine accepted).step (config accepted (some .secondField) state [] first [] [] accumulator result) =
      some (config accepted (some (.reject .input)) none [] first [] [] accumulator result) := by pair_step

omit [Fintype Γ] [DecidableEq Γ] in
theorem jobs_nil_right (first : List (List Γ)) : jobs first [] = [] := by simp [jobs]

omit [Fintype Γ] [DecidableEq Γ] in
theorem jobs_length_le (first second : List (List Γ)) :
    (jobs first second).length ≤ 2 * ((stream first).length + (stream second).length) := by
  induction first generalizing second with
  | nil => simp [jobs]
  | cons left first ih =>
    cases second with
    | nil => simp [jobs]
    | cons right second =>
      rw [jobs_cons,job_eq]
      have later := ih second
      simp only [stream_cons,List.length_append,List.length_cons,List.length_map,List.length_nil] at *
      omega

def mismatchRun (accepted : Γ) (first second : List (List Γ)) (different : first.length ≠ second.length)
    (state : Register (Γ := Γ)) (accumulator : List (Cell (Γ := Γ))) :
    EvalsToInTime (machine accepted).step
      (config accepted (some .firstStart) state [] (stream first) (stream second) [] accumulator [])
      (some (config accepted none none [] [] [] [] [] [.inr false]))
      (2 * ((stream first).length + (stream second).length) + (jobs first second).length + accumulator.length + 10) := by
  induction first generalizing second state accumulator with
  | nil =>
    cases second with
    | nil => exact (different rfl).elim
    | cons right second =>
      rw [show stream ([] : List (List Γ)) = [] from rfl,stream_cons]
      have one := StackMachineComposition.oneStep (first_empty accepted state (stream (right :: second)) accumulator [])
      cases right with
      | nil =>
        have two := StackMachineComposition.oneStep (second_extra accepted none (fieldCell none) (stream second) accumulator [])
        have rest := refusalRun accepted (some (fieldCell none)) [] [] (stream second) [] accumulator []
        simp only [stream_cons,List.map_nil,List.nil_append] at one
        have front := EvalsToInTime.trans _ 1 1 _ _ _ one two
        have all := EvalsToInTime.trans _ _ _ _ _ _ front rest
        simp only [List.map_nil,List.nil_append] at ⊢
        apply WordEqualityMachine.within all
        simp [stream,jobs,Indexed.frame]
        omega
      | cons value right =>
        let tail := right.map (fun value => fieldCell (some value)) ++ fieldCell none :: stream second
        have two := StackMachineComposition.oneStep (second_extra accepted none (fieldCell (some value)) tail accumulator [])
        have rest := refusalRun accepted (some (fieldCell (some value))) [] [] tail [] accumulator []
        simp only [stream_cons,List.map_cons,List.cons_append] at one
        have front := EvalsToInTime.trans _ 1 1 _ _ _ one two
        have all := EvalsToInTime.trans _ _ _ _ _ _ front rest
        simp only [List.map_cons,List.cons_append] at ⊢
        apply WordEqualityMachine.within all
        simp [tail,stream,jobs,Indexed.frame]
        omega
  | cons left first ih =>
    cases second with
    | nil =>
      have one := firstRun accepted true left state (stream first) [] accumulator []
      have two := StackMachineComposition.oneStep (second_missing accepted (some (fieldCell none)) (stream first)
        (fieldCell none :: (left.map (fun value => fieldCell (some value))).reverse ++ accumulator) [])
      have rest := refusalRun accepted none [] (stream first) [] []
        (fieldCell none :: (left.map (fun value => fieldCell (some value))).reverse ++ accumulator) []
      have front := EvalsToInTime.trans _ _ 1 _ _ _ one two
      have all := EvalsToInTime.trans _ _ _ _ _ _ front rest
      rw [stream_cons]
      change EvalsToInTime _
        (config accepted (some .firstStart) state []
          (left.map (fun value => fieldCell (some value)) ++ fieldCell none :: stream first) [] [] accumulator []) _ _
      apply WordEqualityMachine.within all
      simp [jobs]
      omega
    | cons right second =>
      have smaller : first.length ≠ second.length := by simpa using different
      have one := firstRun accepted true left state (stream first) (stream (right :: second)) accumulator []
      rw [stream_cons] at one
      have two := secondRun accepted right (some (fieldCell none)) (stream first) (stream second)
        (fieldCell none :: (left.map (fun value => fieldCell (some value))).reverse ++ accumulator) []
      have later := ih second smaller (some (fieldCell none))
        (outerDelimiter :: fieldCell none :: (right.map (fun value => fieldCell (some value))).reverse ++
          fieldCell none :: (left.map (fun value => fieldCell (some value))).reverse ++ accumulator)
      simp only [List.cons_append,List.append_assoc] at one two later
      have front := EvalsToInTime.trans _ _ _ _ _ _ one two
      have all := EvalsToInTime.trans _ _ _ _ _ _ front later
      rw [stream_cons,stream_cons]
      apply WordEqualityMachine.within all
      rw [jobs_cons,job_eq]
      simp only [List.length_append,List.length_cons,List.length_map,List.length_reverse,List.length_nil]
      omega

def mismatchOutputs (accepted refused : Γ) (first second : List (List Γ)) (different : first.length ≠ second.length) :
    TM2OutputsInTime (machine accepted) (input accepted refused (some first) (some second)) (some [.inr false])
      (12 * (input accepted refused (some first) (some second)).length + 30) := by
  have prepared := prepareRun accepted refused first second
  have rejected := mismatchRun accepted first second different none []
  have all := EvalsToInTime.trans _ _ _ _ _ _ prepared rejected
  change EvalsToInTime _ (initList _ _) (some (haltList _ _)) _
  rw [init_eq,halt_eq]
  apply WordEqualityMachine.within all
  rw [input_length]
  have size := jobs_length_le first second
  simp only [List.length_nil]
  omega

/-- Every pair of independently framed status results is handled. Both statuses
and exact field counts are checked; an empty success is distinct from refusal. -/
def outputs (accepted refused : Γ) (different : refused ≠ accepted)
    (first second : Option (List (List Γ))) :
    TM2OutputsInTime (machine accepted) (input accepted refused first second) (some (output first second))
      (12 * (input accepted refused first second).length + 30) := by
  cases first with
  | none =>
    exact WordEqualityMachine.within (firstRefusedOutputs accepted refused different second) (by omega)
  | some first =>
    cases second with
    | none =>
      exact WordEqualityMachine.within (secondRefusedOutputs accepted refused different first) (by omega)
    | some second =>
      by_cases same : first.length = second.length
      · simpa only [output,if_pos same,TM2OutputsInTime,Option.map_some] using WordEqualityMachine.within
          (positiveOutputs accepted refused first second same) (by omega)
      · simpa only [output,if_neg same] using mismatchOutputs accepted refused first second same

/-- Independent result decoding sees only the returned physical word. -/
def peel : List (Cell (Γ := Γ)) → Option (List (Option (Option Γ)))
  | [] => some []
  | .inl cell :: rest => (peel rest).map (cell :: ·)
  | .inr _ :: _ => none

def readJob (word : List (Option Γ)) : Option (List Γ × List Γ) :=
  match Indexed.decodeFrames word with
  | some [first,second] => some (first,second)
  | _ => none

def readRows : List (List (Option Γ)) → Option (List (List Γ × List Γ))
  | [] => some []
  | row :: rest => do
    let pair ← readJob row
    let pairs ← readRows rest
    pure (pair :: pairs)

def readOutput : List (Cell (Γ := Γ)) → Option (List (List Γ × List Γ))
  | .inr true :: rest => do
    let physical ← peel rest
    let rows ← Indexed.decodeFrames physical
    readRows rows
  | _ => none

omit [Fintype Γ] [DecidableEq Γ] in
theorem peel_exact (word : List (Option (Option Γ))) : peel (word.map Sum.inl) = some word := by
  induction word with
  | nil => rfl
  | cons cell word ih => simp [peel,ih]

omit [Fintype Γ] [DecidableEq Γ] in
theorem job_frame (first second : List Γ) :
    job first second = ((Indexed.frame [first,second]).map some ++ [none]).map Sum.inl := by
  simp [job,List.map_append,List.map_map,Function.comp_def,outerDelimiter]
  intros
  rfl

omit [Fintype Γ] [DecidableEq Γ] in
theorem jobs_frame (first second : List (List Γ)) :
    jobs first second = (Indexed.frame ((first.zip second).map fun pair => Indexed.frame [pair.1,pair.2])).map Sum.inl := by
  induction first generalizing second with
  | nil => rfl
  | cons left first ih =>
    cases second with
    | nil => simp [jobs,Indexed.frame]
    | cons right second =>
      rw [jobs_cons,job_frame,ih second]
      simp [Indexed.frame,List.map_append]

omit [Fintype Γ] [DecidableEq Γ] in
theorem readRows_exact (pairs : List (List Γ × List Γ)) :
    readRows (pairs.map fun pair => Indexed.frame [pair.1,pair.2]) = some pairs := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
    simp [readRows,readJob,Indexed.decodeFrames_frame,ih]

omit [Fintype Γ] [DecidableEq Γ] in
theorem readOutput_positive (first second : List (List Γ)) :
    readOutput (.inr true :: jobs first second) = some (first.zip second) := by
  rw [jobs_frame]
  simp only [readOutput,peel_exact,bind,Option.bind,Indexed.decodeFrames_frame]
  exact readRows_exact _

omit [Fintype Γ] [DecidableEq Γ] in
theorem readOutput_refused : readOutput ([.inr false] : List (Cell (Γ := Γ))) = none := rfl

omit [Fintype Γ] [DecidableEq Γ] in
theorem output_readout (first second : Option (List (List Γ))) :
    readOutput (output first second) = (do
      let left ← first
      let right ← second
      if left.length = right.length then pure (left.zip right) else none) := by
  cases first <;> cases second <;> simp [output,readOutput_refused]
  split <;> simp_all [readOutput_positive,readOutput_refused]

theorem run_readout (accepted refused : Γ) (different : refused ≠ accepted)
    (first second : Option (List (List Γ))) {word : List (Cell (Γ := Γ))}
    (finished : TM2Outputs (machine accepted) (input accepted refused first second) (some word)) :
    word = output first second :=
  StackMachineComposition.outputs_unique finished (outputs accepted refused different first second).toEvalsTo

noncomputable def realization (accepted refused : Γ) (different : refused ≠ accepted) :
    TM2ComputableInPolyTime
      (fun value : Option (List (List Γ)) × Option (List (List Γ)) => input accepted refused value.1 value.2)
      id (fun value => output value.1 value.2) where
  tm := machine accepted
  inputAlphabet := Equiv.refl (Cell (Γ := Γ))
  outputAlphabet := Equiv.refl (Cell (Γ := Γ))
  time := Polynomial.C 12 * Polynomial.X + Polynomial.C 30
  outputsFun value := by
    change TM2OutputsInTime (machine accepted) ((input accepted refused value.1 value.2).map id)
      (some ((output value.1 value.2).map id)) _
    simp only [List.map_id,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    exact outputs accepted refused different value.1 value.2

namespace Controls

theorem repeated_order : readOutput (output (some [[true],[false],[true]]) (some [[false],[],[false]])) =
    some [([true],[false]),([false],[]),([true],[false])] := by decide

theorem empty_success : readOutput (output (some ([] : List (List Bool))) (some [])) = some [] := by decide

theorem empty_refusal : readOutput (output (none : Option (List (List Bool))) (some [])) = none := by decide

theorem missing_child : readOutput (output (some [[true],[false]]) (some [[true]])) = none := by decide

theorem extra_child : readOutput (output (some [[true]]) (some [[true],[]])) = none := by decide

theorem malformed_job : readJob ([some true] : List (Option Bool)) = none := by decide

end Controls
end Mettapedia.Computability.FramedWordPairing
