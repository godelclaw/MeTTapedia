import Mettapedia.Logic.ProofSearch.FiniteCertificateExecution
import Mettapedia.Computability.FramedWordMapping

/-!
# Returning the first accepted finite certificate

The independent checker is called through the existing retained-word protocol.
Its result tag and the complete original candidate are then collected by the
existing framed mapper. A finite selector returns the first accepted original
word and drains the remaining physical input. An accepted empty certificate has
a success tag and remains distinct from an exhausted search.

The enumeration uses the original `wordsUpTo` order and a physical unary depth
budget. Every candidate is checked before selection: this construction makes
no early-stop or polynomial-in-depth claim.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.ProofSearch.FirstCertificateExecution

open Turing StateTransition Turing.TM2.Stmt
open Mettapedia.Computability
open Mettapedia.Computability.StackMachineComposition (oneStep)

namespace Selection

variable {Letter : Type} [Fintype Letter] [Inhabited Letter]

inductive Stack where
  | input | temporary | output
  deriving DecidableEq, Fintype

abbrev Alphabet (Letter : Type) : Stack → Type
  | .input => Option (Letter ⊕ Bool)
  | .temporary => Letter
  | .output => Letter ⊕ Bool

inductive Phase where
  | seek | skip | capture | drain | restore | rejectTemporary | rejectInput
  deriving DecidableEq, Fintype

abbrev State (Letter : Type) := Option (Option (Letter ⊕ Bool)) × Option Letter

private def letter (state : State Letter) : Letter :=
  match state.1 with
  | some (some (.inl value)) => value
  | _ => default

def statement (phase : Phase) : TM2.Stmt (Alphabet Letter) Phase (State Letter) :=
  match phase with
  | .seek => pop .input (fun state cell => (cell, state.2))
      (branch (fun state => state.1.isNone)
        (push .output (fun _ => .inr false) (load (fun _ => (none, none)) halt))
        (branch (fun state => match state.1 with
          | some (some (.inr true)) => true | _ => false)
          (goto fun _ => .capture) (goto fun _ => .skip)))
  | .skip => pop .input (fun state cell => (cell, state.2))
      (branch (fun state => state.1.isNone)
        (push .output (fun _ => .inr false) (load (fun _ => (none, none)) halt))
        (branch (fun state => (state.1.getD none).isNone)
          (goto fun _ => .seek) (goto fun _ => .skip)))
  | .capture => pop .input (fun state cell => (cell, state.2))
      (branch (fun state => match state.1 with
          | some (some (.inl _)) => true | _ => false)
        (push .temporary letter (goto fun _ => .capture))
        (branch (fun state => match state.1 with
          | some none => true | _ => false)
          (goto fun _ => .drain) (goto fun _ => .rejectTemporary)))
  | .drain => pop .input (fun state cell => (cell, state.2))
      (branch (fun state => state.1.isSome)
        (goto fun _ => .drain) (goto fun _ => .restore))
  | .restore => pop .temporary (fun state cell => (state.1, cell))
      (branch (fun state => state.2.isSome)
        (push .output (fun state => .inl (state.2.getD default)) (goto fun _ => .restore))
        (push .output (fun _ => .inr true) (load (fun _ => (none, none)) halt)))
  | .rejectTemporary => pop .temporary (fun state cell => (state.1, cell))
      (branch (fun state => state.2.isSome)
        (goto fun _ => .rejectTemporary) (goto fun _ => .rejectInput))
  | .rejectInput => pop .input (fun state cell => (cell, state.2))
      (branch (fun state => state.1.isSome)
        (goto fun _ => .rejectInput)
        (push .output (fun _ => .inr false) (load (fun _ => (none, none)) halt)))

def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet Letter
  Λ := Phase
  main := .seek
  σ := State Letter
  initialState := (none, none)
  m := statement

attribute [local implicit_reducible] machine statement FinTM2.Cfg FinTM2.Stmt

def config (phase : Option Phase) (state : State Letter)
    (input : List (Option (Letter ⊕ Bool))) (temporary : List Letter)
    (output : List (Letter ⊕ Bool)) : (machine (Letter := Letter)).Cfg where
  l := phase
  var := state
  stk key := match key with
    | .input => input | .temporary => temporary | .output => output

local macro "selection_step" : tactic => `(tactic| (
  simp_all [FinTM2.step, machine, statement, config, letter, TM2.step, TM2.stepAux]
  all_goals first
    | rfl
    | (congr 2; funext key; cases key <;> simp [Function.update])))

theorem seek_accepted (state : State Letter) (input : List (Option (Letter ⊕ Bool))) :
    (machine (Letter := Letter)).step (config (some .seek) state (some (.inr true) :: input) [] []) =
      some (config (some .capture) (some (some (.inr true)), state.2) input [] []) := by
  selection_step

theorem seek_refused (state : State Letter) (input : List (Option (Letter ⊕ Bool))) :
    (machine (Letter := Letter)).step (config (some .seek) state (some (.inr false) :: input) [] []) =
      some (config (some .skip) (some (some (.inr false)), state.2) input [] []) := by
  selection_step

theorem seek_empty (state : State Letter) :
    (machine (Letter := Letter)).step (config (some .seek) state [] [] []) =
      some (config none (none, none) [] [] [.inr false]) := by selection_step

theorem skip_letter (state : State Letter) (head : Letter) (input : List (Option (Letter ⊕ Bool))) :
    (machine (Letter := Letter)).step (config (some .skip) state (some (.inl head) :: input) [] []) =
      some (config (some .skip) (some (some (.inl head)), state.2) input [] []) := by selection_step

theorem skip_delimiter (state : State Letter) (input : List (Option (Letter ⊕ Bool))) :
    (machine (Letter := Letter)).step (config (some .skip) state (none :: input) [] []) =
      some (config (some .seek) (some none, state.2) input [] []) := by selection_step

theorem capture_letter (state : State Letter) (head : Letter)
    (input : List (Option (Letter ⊕ Bool))) (temporary : List Letter) :
    (machine (Letter := Letter)).step (config (some .capture) state
      (some (.inl head) :: input) temporary []) =
      some (config (some .capture) (some (some (.inl head)), state.2) input (head :: temporary) []) := by
  selection_step

theorem capture_delimiter (state : State Letter) (input : List (Option (Letter ⊕ Bool)))
    (temporary : List Letter) :
    (machine (Letter := Letter)).step (config (some .capture) state (none :: input) temporary []) =
      some (config (some .drain) (some none, state.2) input temporary []) := by selection_step

theorem drain_cons (state : State Letter) (head : Option (Letter ⊕ Bool))
    (input : List (Option (Letter ⊕ Bool))) (temporary : List Letter) :
    (machine (Letter := Letter)).step (config (some .drain) state (head :: input) temporary []) =
      some (config (some .drain) (some head, state.2) input temporary []) := by selection_step

theorem drain_nil (state : State Letter) (temporary : List Letter) :
    (machine (Letter := Letter)).step (config (some .drain) state [] temporary []) =
      some (config (some .restore) (none, state.2) [] temporary []) := by selection_step

theorem restore_cons (state : State Letter) (head : Letter) (temporary : List Letter)
    (output : List (Letter ⊕ Bool)) :
    (machine (Letter := Letter)).step (config (some .restore) state [] (head :: temporary) output) =
      some (config (some .restore) (state.1, some head) [] temporary (.inl head :: output)) := by
  selection_step

theorem restore_nil (state : State Letter) (output : List (Letter ⊕ Bool)) :
    (machine (Letter := Letter)).step (config (some .restore) state [] [] output) =
      some (config none (none, none) [] [] (.inr true :: output)) := by selection_step

def letters (word : List Letter) : List (Option (Letter ⊕ Bool)) := word.map (some ∘ Sum.inl)

def field (accepted : Bool) (word : List Letter) : List (Option (Letter ⊕ Bool)) :=
  some (.inr accepted) :: letters word ++ [none]

def result : Option (List Letter) → List (Letter ⊕ Bool)
  | none => [.inr false]
  | some word => .inr true :: word.map Sum.inl

def skip_run (state : State Letter) (word : List Letter) (input : List (Option (Letter ⊕ Bool))) :
    EvalsToInTime (machine (Letter := Letter)).step
      (config (some .skip) state (letters word ++ none :: input) [] [])
      (some (config (some .seek) (some none, state.2) input [] [])) (word.length + 1) := by
  induction word generalizing state with
  | nil => exact oneStep (skip_delimiter state input)
  | cons head tail ih =>
      have first := oneStep (skip_letter state head (letters tail ++ none :: input))
      have rest := ih (some (some (.inl head)), state.2)
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
      simpa [letters] using joined

def capture_run (state : State Letter) (word temporary : List Letter)
    (input : List (Option (Letter ⊕ Bool))) :
    EvalsToInTime (machine (Letter := Letter)).step
      (config (some .capture) state (letters word ++ none :: input) temporary [])
      (some (config (some .drain) (some none, state.2) input (word.reverse ++ temporary) []))
      (word.length + 1) := by
  induction word generalizing state temporary with
  | nil => exact oneStep (capture_delimiter state input temporary)
  | cons head tail ih =>
      have first := oneStep (capture_letter state head (letters tail ++ none :: input) temporary)
      have rest := ih (some (some (.inl head)), state.2) (head :: temporary)
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
      simpa [letters, List.reverse_cons, List.append_assoc] using joined

def drain_run (state : State Letter) (input : List (Option (Letter ⊕ Bool))) (temporary : List Letter) :
    EvalsToInTime (machine (Letter := Letter)).step (config (some .drain) state input temporary [])
      (some (config (some .restore) (none, state.2) [] temporary [])) (input.length + 1) := by
  induction input generalizing state with
  | nil => exact oneStep (drain_nil state temporary)
  | cons head tail ih =>
      have first := oneStep (drain_cons state head tail temporary)
      have rest := ih (some head, state.2)
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
      simpa using joined

def restore_run (state : State Letter) (temporary : List Letter) (output : List (Letter ⊕ Bool)) :
    EvalsToInTime (machine (Letter := Letter)).step (config (some .restore) state [] temporary output)
      (some (config none (none, none) [] [] (.inr true :: temporary.reverse.map Sum.inl ++ output)))
      (temporary.length + 1) := by
  induction temporary generalizing state output with
  | nil => exact oneStep (restore_nil state output)
  | cons head tail ih =>
      have first := oneStep (restore_cons state head tail output)
      have rest := ih (state.1, some head) (.inl head :: output)
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using joined

def taggedWords {Value : Type} (encode : Value → List Letter) (accepts : Value → Bool)
    (values : List Value) : List (Option (Letter ⊕ Bool)) :=
  values.flatMap (fun value => field (accepts value) (encode value))

def selectionClock {Value : Type} (encode : Value → List Letter) (accepts : Value → Bool) :
    List Value → Nat
  | [] => 1
  | value :: tail => if accepts value then
      2 * (encode value).length + (taggedWords encode accepts tail).length + 4
    else (encode value).length + 2 + selectionClock encode accepts tail

def selection_run {Value : Type} (encode : Value → List Letter) (accepts : Value → Bool)
    (values : List Value) (state : State Letter) :
    EvalsToInTime (machine (Letter := Letter)).step
      (config (some .seek) state (taggedWords encode accepts values) [] [])
      (some (config none (none, none) [] [] (result ((values.find? accepts).map encode))))
      (selectionClock encode accepts values) := by
  induction values generalizing state with
  | nil => exact oneStep (seek_empty state)
  | cons value tail ih =>
      cases accepted : accepts value with
      | false =>
          have first := oneStep (seek_refused state
            (letters (encode value) ++ none :: taggedWords encode accepts tail))
          have skipped := skip_run (some (some (.inr false)), state.2) (encode value)
            (taggedWords encode accepts tail)
          have rest := ih (some none, state.2)
          have a := EvalsToInTime.trans _ _ _ _ _ _ first skipped
          have b := EvalsToInTime.trans _ _ _ _ _ _ a rest
          simpa [taggedWords, field, List.append_assoc, selectionClock, accepted,
            List.find?_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b
      | true =>
          have first := oneStep (seek_accepted state
            (letters (encode value) ++ none :: taggedWords encode accepts tail))
          have captured := capture_run (some (some (.inr true)), state.2) (encode value) []
            (taggedWords encode accepts tail)
          simp only [List.append_nil] at captured
          have drained := drain_run (some none, state.2) (taggedWords encode accepts tail) (encode value).reverse
          have restored := restore_run (none, state.2) (encode value).reverse []
          simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at restored
          have a := EvalsToInTime.trans _ _ _ _ _ _ first captured
          have b := EvalsToInTime.trans _ _ _ _ _ _ a drained
          have c := EvalsToInTime.trans _ _ _ _ _ _ b restored
          convert c using 1 <;>
            simp [taggedWords, field, result, List.append_assoc, selectionClock, accepted]
          all_goals omega

omit [Fintype Letter] [Inhabited Letter] in
theorem selectionClock_written {Value : Type} (encode : Value → List Letter) (accepts : Value → Bool)
    (values : List Value) :
    selectionClock encode accepts values ≤ 2 * (taggedWords encode accepts values).length + 1 := by
  induction values with
  | nil => simp [selectionClock, taggedWords]
  | cons value tail ih =>
      cases accepted : accepts value <;>
        simp only [selectionClock, accepted, Bool.false_eq_true, ↓reduceIte, taggedWords,
          List.flatMap_cons, List.length_append, field, List.length_cons, letters, List.length_map] at * <;> omega

theorem init_eq (input : List (Option (Letter ⊕ Bool))) :
    initList (machine (Letter := Letter)) input = config (some .seek) (none, none) input [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key <;> simp

theorem halt_eq (output : List (Letter ⊕ Bool)) :
    haltList (machine (Letter := Letter)) output = config none (none, none) [] [] output := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key <;> simp

def outputs {Value : Type} (encode : Value → List Letter) (accepts : Value → Bool) (values : List Value) :
    TM2OutputsInTime (machine (Letter := Letter)) (taggedWords encode accepts values)
      (some (result ((values.find? accepts).map encode)))
      (2 * (taggedWords encode accepts values).length + 1) := by
  have ran := selection_run encode accepts values (none, none)
  change EvalsToInTime _ (initList (machine (Letter := Letter)) _) (some (haltList (machine (Letter := Letter)) _)) _
  rw [init_eq, halt_eq]
  exact ⟨ran.toEvalsTo, ran.steps_le_m.trans (selectionClock_written encode accepts values)⟩

theorem finiteAlphabet (key : (machine (Letter := Letter)).K) :
    Finite ((machine (Letter := Letter)).Γ key) := by
  cases key with
  | input => exact inferInstanceAs (Finite (Option (Letter ⊕ Bool)))
  | temporary => exact inferInstanceAs (Finite Letter)
  | output => exact inferInstanceAs (Finite (Letter ⊕ Bool))

end Selection

namespace Checking

open Mettapedia.GSLT.LanguageDef.KernelAuthority

variable {Claim : Type} (program : FinTM2)
  (inputAlphabet : program.Γ program.k₀ ≃ Bool)
  (outputAlphabet : program.Γ program.k₁ ≃ Bool)
  [Inhabited (program.Γ program.k₀)] [Fintype (program.Γ program.k₁)]

local instance : Fintype (program.Γ program.k₀) := program.Γk₀Fin

def encodeCertificate (certificate : List (Fin 2)) : List (program.Γ program.k₀) :=
  FiniteCertificateExecution.Checking.encodeCertificate program inputAlphabet certificate

def retainedProgram : FinTM2 := RetainedWordExecution.machine program outputAlphabet

local instance : Fintype ((retainedProgram program outputAlphabet).Γ
    (retainedProgram program outputAlphabet).k₁) := inferInstanceAs (Fintype (program.Γ program.k₀ ⊕ Bool))
local instance : Inhabited ((retainedProgram program outputAlphabet).Γ
    (retainedProgram program outputAlphabet).k₀) := inferInstanceAs (Inhabited (program.Γ program.k₀))
local instance : Inhabited ((retainedProgram program outputAlphabet).Γ
    (retainedProgram program outputAlphabet).k₁) := ⟨.inr false⟩

def mappedProgram : FinTM2 := FramedWordMapping.machine (retainedProgram program outputAlphabet)

local instance : Fintype ((mappedProgram program outputAlphabet).Γ
    (mappedProgram program outputAlphabet).k₁) :=
  inferInstanceAs (Fintype (Option (program.Γ program.k₀ ⊕ Bool)))
local instance : Inhabited ((mappedProgram program outputAlphabet).Γ
    (mappedProgram program outputAlphabet).k₁) := ⟨none⟩

def decisionProgram : FinTM2 := StackMachineComposition.machine
  (mappedProgram program outputAlphabet) (Selection.machine (Letter := program.Γ program.k₀))
  (Equiv.refl (Option (program.Γ program.k₀ ⊕ Bool)))

def bridge : FiniteCertificateExecution.machine.Γ FiniteCertificateExecution.machine.k₁ ≃
    (decisionProgram program outputAlphabet).Γ (decisionProgram program outputAlphabet).k₀ :=
  Equiv.optionCongr inputAlphabet.symm

local instance : Fintype (FiniteCertificateExecution.machine.Γ FiniteCertificateExecution.machine.k₁) :=
  inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited (FiniteCertificateExecution.machine.Γ FiniteCertificateExecution.machine.k₁) := ⟨none⟩

def searchMachine : FinTM2 := StackMachineComposition.machine FiniteCertificateExecution.machine
  (decisionProgram program outputAlphabet) (bridge program inputAlphabet outputAlphabet)

def emitted (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (certificate : List (Fin 2)) : List (program.Γ program.k₀ ⊕ Bool) :=
  .inr (checker.check claim certificate) :: (encodeCertificate program inputAlphabet certificate).map Sum.inl

def retainedClock (clock : List (Fin 2) → Nat) (certificate : List (Fin 2)) : Nat :=
  clock certificate + 3 * (encodeCertificate program inputAlphabet certificate).length + 5

def mappedWire (checker : Checker Claim (List (Fin 2))) (claim : Claim) (bound : Nat) :
    List (Option (program.Γ program.k₀ ⊕ Bool)) :=
  WordTemplateMachine.Indexed.frame ((CertificateBounds.wordsUpTo 2 bound).map
    (emitted program inputAlphabet checker claim))

def mappingClock (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (clock : List (Fin 2) → Nat) (bound : Nat) : Nat :=
  FramedWordMapping.totalClock (retainedProgram program outputAlphabet)
    (encodeCertificate program inputAlphabet) (emitted program inputAlphabet checker claim)
    (retainedClock program inputAlphabet clock) (CertificateBounds.wordsUpTo 2 bound)

def searchTime (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (clock : List (Fin 2) → Nat) (bound : Nat) : Nat :=
  FiniteCertificateExecution.enumerationTime bound +
    2 * (FiniteCertificateExecution.wire (FiniteCertificateExecution.words bound)).length +
    mappingClock program inputAlphabet outputAlphabet checker claim clock bound +
    4 * (mappedWire program inputAlphabet checker claim bound).length + 5

theorem enumeration_frame (bound : Nat) :
    (FiniteCertificateExecution.wire (FiniteCertificateExecution.words bound)).map
      (bridge program inputAlphabet outputAlphabet) =
      WordTemplateMachine.Indexed.frame ((CertificateBounds.wordsUpTo 2 bound).map
        (encodeCertificate program inputAlphabet)) := by
  simp only [FiniteCertificateExecution.wire, FiniteCertificateExecution.words, List.flatMap_map,
    List.map_flatMap, FiniteCertificateExecution.row, List.map_append, List.map_cons, List.map_nil,
    bridge, WordTemplateMachine.Indexed.frame, List.map_map, Function.comp_def,
    encodeCertificate, FiniteCertificateExecution.Checking.encodeCertificate]
  congr 1

omit [Inhabited (program.Γ program.k₀)] [Fintype (program.Γ program.k₁)] in
theorem mappedWire_tagged (checker : Checker Claim (List (Fin 2))) (claim : Claim) (bound : Nat) :
    mappedWire program inputAlphabet checker claim bound =
      Selection.taggedWords (encodeCertificate program inputAlphabet) (checker.check claim)
        (CertificateBounds.wordsUpTo 2 bound) := by
  simp only [mappedWire, WordTemplateMachine.Indexed.frame, List.flatMap_map,
    emitted, List.map_cons, List.map_map, Function.comp_def, Selection.taggedWords,
    Selection.field, Selection.letters, List.cons_append]

omit [Inhabited (program.Γ program.k₀)] [Fintype (program.Γ program.k₁)] in
theorem first_result (checker : Checker Claim (List (Fin 2))) (claim : Claim) (bound : Nat) :
    ((CertificateBounds.wordsUpTo 2 bound).find? (checker.check claim)).map
      (encodeCertificate program inputAlphabet) =
    (CertificateBounds.boundedSearch checker claim bound).map (encodeCertificate program inputAlphabet) := by
  rw [CertificateBounds.boundedSearch, CertificateBounds.finiteSearch_eq_find?]

noncomputable def retainedRun (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (clock : List (Fin 2) → Nat)
    (runs : ∀ certificate, TM2OutputsInTime program (encodeCertificate program inputAlphabet certificate)
      (some [outputAlphabet.symm (checker.check claim certificate)]) (clock certificate))
    (certificate : List (Fin 2)) :
    TM2OutputsInTime (retainedProgram program outputAlphabet) (encodeCertificate program inputAlphabet certificate)
      (some (emitted program inputAlphabet checker claim certificate))
      (retainedClock program inputAlphabet clock certificate) := by
  simpa only [retainedProgram, emitted, retainedClock, Equiv.apply_symm_apply,
    List.length_nil, Nat.add_zero] using
    RetainedWordExecution.outputs program outputAlphabet
      (encodeCertificate program inputAlphabet certificate)
      (outputAlphabet.symm (checker.check claim certificate)) [] (clock certificate) (runs certificate)

noncomputable def mapped_outputs (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (clock : List (Fin 2) → Nat)
    (runs : ∀ certificate, TM2OutputsInTime program (encodeCertificate program inputAlphabet certificate)
      (some [outputAlphabet.symm (checker.check claim certificate)]) (clock certificate)) (bound : Nat) :
    TM2OutputsInTime (mappedProgram program outputAlphabet)
      (WordTemplateMachine.Indexed.frame ((CertificateBounds.wordsUpTo 2 bound).map
        (encodeCertificate program inputAlphabet)))
      (some (mappedWire program inputAlphabet checker claim bound))
      (mappingClock program inputAlphabet outputAlphabet checker claim clock bound) := by
  exact FramedWordMapping.outputs (retainedProgram program outputAlphabet)
    (encodeCertificate program inputAlphabet) (emitted program inputAlphabet checker claim)
    (retainedClock program inputAlphabet clock) (retainedRun program inputAlphabet outputAlphabet checker claim clock runs)
    (CertificateBounds.wordsUpTo 2 bound)

/-- The concrete finite program returns the original first accepted certificate.
Every retention, per-candidate checker execution, emitted field, handoff and
final cleanup is included in the bound. -/
noncomputable def search_outputs (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (clock : List (Fin 2) → Nat)
    (runs : ∀ certificate, TM2OutputsInTime program (encodeCertificate program inputAlphabet certificate)
      (some [outputAlphabet.symm (checker.check claim certificate)]) (clock certificate)) (bound : Nat) :
    TM2OutputsInTime (searchMachine program inputAlphabet outputAlphabet) (List.replicate bound none)
      (some (Selection.result ((CertificateBounds.boundedSearch checker claim bound).map
        (encodeCertificate program inputAlphabet))))
      (searchTime program inputAlphabet outputAlphabet checker claim clock bound) := by
  have mapped := mapped_outputs program inputAlphabet outputAlphabet checker claim clock runs bound
  have selected := Selection.outputs (encodeCertificate program inputAlphabet) (checker.check claim)
    (CertificateBounds.wordsUpTo 2 bound)
  rw [← mappedWire_tagged program inputAlphabet checker claim bound, first_result program inputAlphabet checker claim bound] at selected
  have handed : (mappedWire program inputAlphabet checker claim bound).map
      (Equiv.refl (Option (program.Γ program.k₀ ⊕ Bool))) =
      mappedWire program inputAlphabet checker claim bound := by
    exact List.map_id _
  rw [← handed] at selected
  simp only [List.length_map] at selected
  have decision := StackMachineComposition.outputs (mappedProgram program outputAlphabet)
    (Selection.machine (Letter := program.Γ program.k₀)) (Equiv.refl (Option (program.Γ program.k₀ ⊕ Bool)))
    _ _ _ _ _ mapped selected
  rw [← enumeration_frame program inputAlphabet outputAlphabet bound] at decision
  have all := StackMachineComposition.outputs FiniteCertificateExecution.machine
    (decisionProgram program outputAlphabet) (bridge program inputAlphabet outputAlphabet)
    _ _ _ _ _ (FiniteCertificateExecution.outputs bound) decision
  convert all using 1
  all_goals first | rfl | (dsimp only [searchTime]; omega)

theorem retainedProgram_finiteAlphabet (originalFinite : ∀ key, Finite (program.Γ key)) :
    ∀ key, Finite ((retainedProgram program outputAlphabet).Γ key) := by
  intro key
  cases key with
  | none => exact inferInstanceAs (Finite (program.Γ program.k₀ ⊕ Bool))
  | some key => cases key with
    | none => exact inferInstanceAs (Finite (program.Γ program.k₀))
    | some key => cases key with
      | none => exact inferInstanceAs (Finite (program.Γ program.k₀))
      | some key => exact originalFinite key

theorem searchMachine_finiteAlphabet (originalFinite : ∀ key, Finite (program.Γ key)) :
    ∀ key, Finite ((searchMachine program inputAlphabet outputAlphabet).Γ key) := by
  have retainedFinite := retainedProgram_finiteAlphabet program outputAlphabet originalFinite
  have mappedFinite := FramedWordMapping.finiteAlphabet (retainedProgram program outputAlphabet) retainedFinite
  have decisionFinite : ∀ key, Finite ((decisionProgram program outputAlphabet).Γ key) := by
    intro key
    cases key with
    | none => exact inferInstanceAs (Finite (Option (program.Γ program.k₀ ⊕ Bool)))
    | some key => cases key with
      | inl key => exact mappedFinite key
      | inr key => exact Selection.finiteAlphabet key
  intro key
  cases key with
  | none => exact inferInstanceAs (Finite (Option Bool))
  | some key => cases key with
    | inl _ => exact inferInstanceAs (Finite (Option Bool))
    | inr key => exact decisionFinite key

/-- Reaching an intermediate state is distinct from either successful search
or exhaustive refusal. The threshold is the original physical run length. -/
theorem search_halts_iff (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (clock : List (Fin 2) → Nat)
    (runs : ∀ certificate, TM2OutputsInTime program (encodeCertificate program inputAlphabet certificate)
      (some [outputAlphabet.symm (checker.check claim certificate)]) (clock certificate))
    (bound budget : Nat) :
    (ExecutedBudgets.probe (searchMachine program inputAlphabet outputAlphabet).step
      (initList (searchMachine program inputAlphabet outputAlphabet) (List.replicate bound none)) budget).halted = true ↔
      (search_outputs program inputAlphabet outputAlphabet checker claim clock runs bound).steps ≤ budget := by
  exact ExecutedBudgets.probe_halts_iff (searchMachine program inputAlphabet outputAlphabet).step
    (initList (searchMachine program inputAlphabet outputAlphabet) (List.replicate bound none)) _
    (search_outputs program inputAlphabet outputAlphabet checker claim clock runs bound).toEvalsTo rfl budget

/-- With enough budget the observer returns the complete original certificate
packet, including its success or exhaustive-refusal tag. -/
theorem search_with_budget (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (clock : List (Fin 2) → Nat)
    (runs : ∀ certificate, TM2OutputsInTime program (encodeCertificate program inputAlphabet certificate)
      (some [outputAlphabet.symm (checker.check claim certificate)]) (clock certificate))
    (bound budget : Nat)
    (enough : searchTime program inputAlphabet outputAlphabet checker claim clock bound ≤ budget) :
    let observed := ExecutedBudgets.probe (searchMachine program inputAlphabet outputAlphabet).step
      (initList (searchMachine program inputAlphabet outputAlphabet) (List.replicate bound none)) budget
    observed.halted = true ∧
      observed.state.stk (searchMachine program inputAlphabet outputAlphabet).k₁ =
        Selection.result ((CertificateBounds.boundedSearch checker claim bound).map
          (encodeCertificate program inputAlphabet)) := by
  let ran := search_outputs program inputAlphabet outputAlphabet checker claim clock runs bound
  have execution : EvalsToInTime (searchMachine program inputAlphabet outputAlphabet).step
      (initList (searchMachine program inputAlphabet outputAlphabet) (List.replicate bound none))
      (some (haltList (searchMachine program inputAlphabet outputAlphabet)
        (Selection.result ((CertificateBounds.boundedSearch checker claim bound).map
          (encodeCertificate program inputAlphabet))))) budget :=
    ⟨ran.toEvalsTo, ran.steps_le_m.trans enough⟩
  have observed := ExecutedBudgets.probe_complete _ _ _ budget execution rfl
  dsimp only
  rw [observed]
  simp [haltList]

end Checking

namespace Readout

open Mettapedia.GSLT.LanguageDef.KernelAuthority

variable {Letter Claim : Type} (alphabet : Letter ≃ Bool)

def certificate : List (Letter ⊕ Bool) → Option (List (Fin 2))
  | .inr true :: tail => tail.mapM (fun symbol => match symbol with
      | .inl letter => some (finTwoEquiv.symm (alphabet letter))
      | .inr _ => none)
  | _ => none

theorem mapped_certificate (word : List (Fin 2)) :
    certificate alphabet (.inr true :: (word.map (alphabet.symm ∘ finTwoEquiv)).map Sum.inl) = some word := by
  induction word with
  | nil => rfl
  | cons head tail ih =>
      simp [certificate, List.mapM_cons] at ih ⊢
      rw [ih]
      rfl

theorem original_result (answer : Option (List (Fin 2))) :
    certificate alphabet (Selection.result (answer.map (fun word => word.map (alphabet.symm ∘ finTwoEquiv)))) = answer := by
  cases answer with
  | none => rfl
  | some word => exact mapped_certificate alphabet word

/-- The readout recovers the same checked proof; no separate acceptance
judgment is introduced by the finite implementation. -/
theorem accepted_scope (checker : Checker Claim (List (Fin 2))) (meaning : Claim → Prop)
    (sound : checker.Sound meaning) (claim : Claim) (bound : Nat) (word : List (Fin 2))
    (found : certificate alphabet (Selection.result ((CertificateBounds.boundedSearch checker claim bound).map
      (fun original => original.map (alphabet.symm ∘ finTwoEquiv)))) = some word) :
    word.length ≤ bound ∧ checker.check claim word = true ∧ meaning claim := by
  rw [original_result] at found
  have accepted := CertificateBounds.boundedSearch_eq_some_sound checker claim bound found
  exact ⟨accepted.1, accepted.2, sound claim word accepted.2⟩

end Readout

end Mettapedia.Logic.ProofSearch.FirstCertificateExecution
