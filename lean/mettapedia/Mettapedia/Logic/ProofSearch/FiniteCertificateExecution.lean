import Mettapedia.Logic.ProofSearch.CertificateBounds
import Mettapedia.Logic.ProofSearch.ExecutedBudgets
import Mettapedia.Computability.FramedWordValidation
import Mettapedia.Computability.WordHomomorphismMachine

/-!
# Executed finite certificate enumeration

The binary certificate fragment uses the original finite word enumeration,
transported through `finTwoEquiv`. Its physical enumerator performs a bounded
depth-first traversal in that same order. A unary depth budget, the current
word and pending work remain on stacks; registers contain only finite symbols.
Every word is framed by a delimiter outside the binary alphabet.

Copying words, advancing branches, cleaning the original depth budget and
restoring the complete output order are original counted transitions. The
subsequent original framed-word loop checks every candidate, including refused
ones. The joined observation is bounded existence; returning the first checked
certificate is a further operation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.ProofSearch.FiniteCertificateExecution

open Turing StateTransition Turing.TM2.Stmt
open Mettapedia.Computability.StackMachineComposition (oneStep)

/-- The existing enumeration, with the original finite binary alphabet. -/
def words (bound : Nat) : List (List Bool) :=
  (CertificateBounds.wordsUpTo 2 bound).map (List.map finTwoEquiv)

theorem words_zero : words 0 = [[]] := rfl

theorem words_succ (bound : Nat) : words (bound + 1) =
    [] :: ((words bound).map (false :: ·) ++ (words bound).map (true :: ·)) := by
  have zero : finTwoEquiv (0 : Fin 2) = false := rfl
  have one : finTwoEquiv (1 : Fin 2) = true := rfl
  simp [words, CertificateBounds.wordsUpTo_succ, CertificateBounds.extendWords,
    List.finRange_succ, List.map_map, Function.comp_def, zero, one]

theorem mem_words (bound : Nat) (word : List Bool) : word ∈ words bound ↔ word.length ≤ bound := by
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨original, present, rfl⟩
    simpa using (CertificateBounds.mem_wordsUpTo 2 bound original).mp present
  · intro short
    let original := word.map finTwoEquiv.symm
    have present : original ∈ CertificateBounds.wordsUpTo 2 bound :=
      (CertificateBounds.mem_wordsUpTo 2 bound original).mpr (by simpa [original] using short)
    apply List.mem_map.mpr
    refine ⟨original, present, ?_⟩
    simp [original, List.map_map]

def row (word : List Bool) : List (Option Bool) := word.map some ++ [none]

def wire (certificates : List (List Bool)) : List (Option Bool) := certificates.flatMap row

def subtreeWords (bound : Nat) (stem : List Bool) : List (List Bool) :=
  (words bound).map (stem ++ ·)

theorem subtreeWords_nil (bound : Nat) : subtreeWords bound [] = words bound := by
  change (words bound).map id = words bound
  exact List.map_id _

theorem subtreeWords_zero (stem : List Bool) : subtreeWords 0 stem = [stem] := by
  simp [subtreeWords, words_zero]

theorem subtreeWords_succ (bound : Nat) (stem : List Bool) :
    subtreeWords (bound + 1) stem = stem ::
      (subtreeWords bound (stem ++ [false]) ++ subtreeWords bound (stem ++ [true])) := by
  simp [subtreeWords, words_succ, List.map_map, Function.comp_def, List.append_assoc]

inductive Stack where
  | allowance | path | copy | results | output
  deriving DecidableEq, Fintype

inductive Phase where
  | emit | restore | descend | advance | drain | finish
  deriving DecidableEq, Fintype

/-- Finite control walks the original preorder, retaining every physical
candidate. Delimiters are ordinary stack symbols, not checker outcomes. -/
def machine : FinTM2 where
  K := Stack
  k₀ := .allowance
  k₁ := .output
  Γ _ := Option Bool
  Λ := Phase
  main := .emit
  σ := Option (Option Bool)
  initialState := none
  m phase := match phase with
    | .emit => pop .path (fun _ value => value)
        (branch Option.isSome
          (push .copy (fun value => value.getD none) (goto fun _ => .emit))
          (load (fun _ => none) (goto fun _ => .restore)))
    | .restore => pop .copy (fun _ value => value)
        (branch Option.isSome
          (push .path (fun value => value.getD none)
            (push .results (fun value => value.getD none) (goto fun _ => .restore)))
          (push .results (fun _ => none) (load (fun _ => none) (goto fun _ => .descend))))
    | .descend => pop .allowance (fun _ value => value)
        (branch Option.isSome
          (push .path (fun _ => some false) (load (fun _ => none) (goto fun _ => .emit)))
          (load (fun _ => none) (goto fun _ => .advance)))
    | .advance => pop .path (fun _ value => value)
        (branch (fun value => value == some (some false))
          (push .path (fun _ => some true) (load (fun _ => none) (goto fun _ => .emit)))
          (branch Option.isSome
            (push .allowance (fun _ => none) (load (fun _ => none) (goto fun _ => .advance)))
            (load (fun _ => none) (goto fun _ => .drain))))
    | .drain => pop .allowance (fun _ value => value)
        (branch Option.isSome (goto fun _ => .drain)
          (load (fun _ => none) (goto fun _ => .finish)))
    | .finish => pop .results (fun _ value => value)
        (branch Option.isSome
          (push .output (fun value => value.getD none) (goto fun _ => .finish))
          (load (fun _ => none) halt))

def config (phase : Option Phase) (last : Option (Option Bool))
    (allowance path copy results output : List (Option Bool)) : machine.Cfg where
  l := phase
  var := last
  stk stack := match stack with
    | .allowance => allowance
    | .path => path
    | .copy => copy
    | .results => results
    | .output => output

theorem emit_cons (last : Option (Option Bool)) (head : Option Bool)
    (allowance path copy results output : List (Option Bool)) :
    machine.step (config (some .emit) last allowance (head :: path) copy results output) =
      some (config (some .emit) (some head) allowance path (head :: copy) results output) := by
  simp [FinTM2.step, machine, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem emit_nil (last : Option (Option Bool))
    (allowance copy results output : List (Option Bool)) :
    machine.step (config (some .emit) last allowance [] copy results output) =
      some (config (some .restore) none allowance [] copy results output) := by
  simp [FinTM2.step, machine, config, TM2.step, TM2.stepAux]

theorem restore_cons (last : Option (Option Bool)) (head : Option Bool)
    (allowance path copy results output : List (Option Bool)) :
    machine.step (config (some .restore) last allowance path (head :: copy) results output) =
      some (config (some .restore) (some head) allowance (head :: path) copy (head :: results) output) := by
  simp [FinTM2.step, machine, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem restore_nil (last : Option (Option Bool))
    (allowance path results output : List (Option Bool)) :
    machine.step (config (some .restore) last allowance path [] results output) =
      some (config (some .descend) none allowance path [] (none :: results) output) := by
  simp [FinTM2.step, machine, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem descend_cons (last : Option (Option Bool)) (head : Option Bool)
    (allowance path results output : List (Option Bool)) :
    machine.step (config (some .descend) last (head :: allowance) path [] results output) =
      some (config (some .emit) none allowance (some false :: path) [] results output) := by
  simp [FinTM2.step, machine, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem descend_nil (last : Option (Option Bool))
    (path results output : List (Option Bool)) :
    machine.step (config (some .descend) last [] path [] results output) =
      some (config (some .advance) none [] path [] results output) := by
  simp [FinTM2.step, machine, config, TM2.step, TM2.stepAux]

theorem advance_false (last : Option (Option Bool))
    (allowance path results output : List (Option Bool)) :
    machine.step (config (some .advance) last allowance (some false :: path) [] results output) =
      some (config (some .emit) none allowance (some true :: path) [] results output) := by
  simp [FinTM2.step, machine, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem advance_true (last : Option (Option Bool))
    (allowance path results output : List (Option Bool)) :
    machine.step (config (some .advance) last allowance (some true :: path) [] results output) =
      some (config (some .advance) none (none :: allowance) path [] results output) := by
  simp [FinTM2.step, machine, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem advance_nil (last : Option (Option Bool))
    (allowance results output : List (Option Bool)) :
    machine.step (config (some .advance) last allowance [] [] results output) =
      some (config (some .drain) none allowance [] [] results output) := by
  simp [FinTM2.step, machine, config, TM2.step, TM2.stepAux]

theorem drain_cons (last : Option (Option Bool)) (head : Option Bool)
    (allowance results output : List (Option Bool)) :
    machine.step (config (some .drain) last (head :: allowance) [] [] results output) =
      some (config (some .drain) (some head) allowance [] [] results output) := by
  simp [FinTM2.step, machine, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem drain_nil (last : Option (Option Bool)) (results output : List (Option Bool)) :
    machine.step (config (some .drain) last [] [] [] results output) =
      some (config (some .finish) none [] [] [] results output) := by
  simp [FinTM2.step, machine, config, TM2.step, TM2.stepAux]

theorem finish_cons (last : Option (Option Bool)) (head : Option Bool)
    (results output : List (Option Bool)) :
    machine.step (config (some .finish) last [] [] [] (head :: results) output) =
      some (config (some .finish) (some head) [] [] [] results (head :: output)) := by
  simp [FinTM2.step, machine, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem finish_nil (last : Option (Option Bool)) (output : List (Option Bool)) :
    machine.step (config (some .finish) last [] [] [] [] output) =
      some (config none none [] [] [] [] output) := by
  simp [FinTM2.step, machine, config, TM2.step, TM2.stepAux]

def emit_run (last : Option (Option Bool))
    (allowance path copy results output : List (Option Bool)) :
    EvalsToInTime machine.step (config (some .emit) last allowance path copy results output)
      (some (config (some .restore) none allowance [] (path.reverse ++ copy) results output))
      (path.length + 1) := by
  induction path generalizing last copy with
  | nil => simpa using oneStep (emit_nil last allowance copy results output)
  | cons head tail ih =>
      have first := oneStep (emit_cons last head allowance tail copy results output)
      have rest := ih (some head) (head :: copy)
      have joined := EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
      simpa [List.reverse_cons, List.append_assoc] using joined

def restore_run (last : Option (Option Bool))
    (allowance path copy results output : List (Option Bool)) :
    EvalsToInTime machine.step (config (some .restore) last allowance path copy results output)
      (some (config (some .descend) none allowance (copy.reverse ++ path) []
        (none :: (copy.reverse ++ results)) output))
      (copy.length + 1) := by
  induction copy generalizing last path results with
  | nil => simpa using oneStep (restore_nil last allowance path results output)
  | cons head tail ih =>
      have first := oneStep (restore_cons last head allowance path tail results output)
      have rest := ih (some head) (head :: path) (head :: results)
      have joined := EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
      simpa [List.reverse_cons, List.append_assoc] using joined

/-- One candidate is really copied and its original order restored before
the traversal continues; the growing output keeps all earlier rows. -/
def emission_run (stem : List Bool) (allowance results output : List (Option Bool)) :
    EvalsToInTime machine.step
      (config (some .emit) none allowance (stem.map some).reverse [] results output)
      (some (config (some .descend) none allowance (stem.map some).reverse []
        ((row stem).reverse ++ results) output)) (2 * stem.length + 2) := by
  have first := emit_run none allowance (stem.map some).reverse [] results output
  simp only [List.reverse_reverse, List.append_nil] at first
  have rest := restore_run none allowance [] (stem.map some) results output
  have joined := EvalsToInTime.trans _ ((stem.map some).reverse.length + 1)
    ((stem.map some).length + 1) _ _ _ first rest
  simpa [row, List.reverse_append, List.append_assoc, two_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using joined

def subtreeTime : Nat → Nat → Nat
  | 0, length => 2 * length + 3
  | bound + 1, length => 2 * length + 5 + 2 * subtreeTime bound (length + 1)

/-- The actual finite control visits each subtree in the original authored
enumeration order, with its complete counted copy and branch operations. -/
def subtree_run (bound : Nat) (stem : List Bool) (results output : List (Option Bool)) :
    EvalsToInTime machine.step
      (config (some .emit) none (List.replicate bound none) (stem.map some).reverse [] results output)
      (some (config (some .advance) none (List.replicate bound none) (stem.map some).reverse []
        ((wire (subtreeWords bound stem)).reverse ++ results) output)) (subtreeTime bound stem.length) := by
  induction bound generalizing stem results with
  | zero =>
      have first := emission_run stem [] results output
      have rest := oneStep (descend_nil none (stem.map some).reverse ((row stem).reverse ++ results) output)
      have joined := EvalsToInTime.trans _ (2 * stem.length + 2) 1 _ _ _ first rest
      have clock : 1 + (2 * stem.length + 2) = 2 * stem.length + 3 := by omega
      rw [clock] at joined
      simpa [subtreeTime, subtreeWords_zero, wire, Nat.add_assoc] using joined
  | succ bound ih =>
      have emitted := emission_run stem (List.replicate (bound + 1) none) results output
      have descended := oneStep (descend_cons none none (List.replicate bound none)
        (stem.map some).reverse ((row stem).reverse ++ results) output)
      have left := ih (stem ++ [false]) ((row stem).reverse ++ results)
      have right := ih (stem ++ [true])
        ((wire (subtreeWords bound (stem ++ [false]))).reverse ++ ((row stem).reverse ++ results))
      have switched := oneStep (advance_false none (List.replicate bound none) (stem.map some).reverse
        ((wire (subtreeWords bound (stem ++ [false]))).reverse ++ ((row stem).reverse ++ results)) output)
      have ascended := oneStep (advance_true none (List.replicate bound none) (stem.map some).reverse
        ((wire (subtreeWords bound (stem ++ [true]))).reverse ++
          ((wire (subtreeWords bound (stem ++ [false]))).reverse ++ ((row stem).reverse ++ results))) output)
      simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
        List.length_append, List.length_singleton] at left right
      simp only [List.replicate_succ] at emitted
      have a := EvalsToInTime.trans _ (2 * stem.length + 2) 1 _ _ _ emitted descended
      have b := EvalsToInTime.trans _ _ (subtreeTime bound (stem.length + 1)) _ _ _ a left
      have c := EvalsToInTime.trans _ _ 1 _ _ _ b switched
      have d := EvalsToInTime.trans _ _ (subtreeTime bound (stem.length + 1)) _ _ _ c right
      have joined := EvalsToInTime.trans _ _ 1 _ _ _ d ascended
      have clock : 1 + (subtreeTime bound (stem.length + 1) +
          (1 + (subtreeTime bound (stem.length + 1) + (1 + (2 * stem.length + 2))))) =
          2 * stem.length + 5 + 2 * subtreeTime bound (stem.length + 1) := by omega
      rw [clock] at joined
      simpa [subtreeTime, subtreeWords_succ, wire, List.flatMap_append, List.reverse_append,
        List.append_assoc, List.replicate_succ, two_mul, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using joined

def drain_run (last : Option (Option Bool)) (allowance results output : List (Option Bool)) :
    EvalsToInTime machine.step (config (some .drain) last allowance [] [] results output)
      (some (config (some .finish) none [] [] [] results output)) (allowance.length + 1) := by
  induction allowance generalizing last with
  | nil => simpa using oneStep (drain_nil last results output)
  | cons head tail ih =>
      have first := oneStep (drain_cons last head tail results output)
      have rest := ih (some head)
      have joined := EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
      simpa using joined

def finish_run (last : Option (Option Bool)) (results output : List (Option Bool)) :
    EvalsToInTime machine.step (config (some .finish) last [] [] [] results output)
      (some (config none none [] [] [] [] (results.reverse ++ output))) (results.length + 1) := by
  induction results generalizing last output with
  | nil => simpa using oneStep (finish_nil last output)
  | cons head tail ih =>
      have first := oneStep (finish_cons last head tail output)
      have rest := ih (some head) (head :: output)
      have joined := EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
      simpa [List.reverse_cons, List.append_assoc] using joined

def enumerationTime (bound : Nat) : Nat :=
  subtreeTime bound 0 + bound + (wire (words bound)).length + 3

theorem init_eq (bound : Nat) : initList machine (List.replicate bound none) =
    config (some .emit) none (List.replicate bound none) [] [] [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key <;> simp

theorem halt_eq (output : List (Option Bool)) : haltList machine output =
    config none none [] [] [] [] output := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key <;> simp

/-- The actual finite machine emits exactly the original bounded binary
certificate space. Its halt clears the entire physical depth budget and all
pending path/copy/output scratch; no candidate list is supplied for free. -/
def outputs (bound : Nat) : TM2OutputsInTime machine (List.replicate bound none)
    (some (wire (words bound))) (enumerationTime bound) := by
  have walked := subtree_run bound [] [] []
  simp only [subtreeWords_nil, List.map_nil,
    List.reverse_nil, List.append_nil, List.length_nil] at walked
  have leaving := oneStep (advance_nil none (List.replicate bound none) (wire (words bound)).reverse [])
  have drained := drain_run none (List.replicate bound none) (wire (words bound)).reverse []
  have finished := finish_run none (wire (words bound)).reverse []
  simp only [List.length_replicate] at drained
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil] at finished
  have a := EvalsToInTime.trans _ (subtreeTime bound 0) 1 _ _ _ walked leaving
  have b := EvalsToInTime.trans _ _ (bound + 1) _ _ _ a drained
  have joined := EvalsToInTime.trans _ _ ((wire (words bound)).length + 1) _ _ _ b finished
  change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
  rw [init_eq, halt_eq]
  convert joined using 1
  simp only [enumerationTime]
  omega

theorem subtreeTime_written (bound : Nat) (stem : List Bool) :
    subtreeTime bound stem.length + 1 ≤ 4 * (wire (subtreeWords bound stem)).length := by
  induction bound generalizing stem with
  | zero =>
      simp only [subtreeTime, subtreeWords_zero, wire, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, row, List.length_append, List.length_map, List.length_singleton]
      omega
  | succ bound ih =>
      have left := ih (stem ++ [false])
      have right := ih (stem ++ [true])
      simp only [List.length_append, List.length_singleton] at left right
      simp only [subtreeTime, subtreeWords_succ, wire, List.flatMap_cons, List.flatMap_append,
        row, List.length_append, List.length_map, List.length_singleton] at *
      omega

/-- Enumeration is bounded by the complete materialized output, including
all candidate delimiters, plus clearing the original unary depth budget.
This is not a polynomial bound in the depth: that output is exponential. -/
theorem enumerationTime_written (bound : Nat) :
    enumerationTime bound ≤ 5 * (wire (words bound)).length + bound + 3 := by
  have written := subtreeTime_written bound []
  simp only [subtreeWords_nil, List.length_nil] at written
  simp only [enumerationTime]
  omega

namespace Checking

open Mettapedia.Computability
open Mettapedia.GSLT.LanguageDef.KernelAuthority

variable {Claim : Type} (program : FinTM2)
  (inputAlphabet : program.Γ program.k₀ ≃ Bool)
  (outputAlphabet : program.Γ program.k₁ ≃ Bool)
  [Inhabited (program.Γ program.k₀)] [Fintype (program.Γ program.k₁)]

local instance : Fintype (FiniteCertificateExecution.machine.Γ FiniteCertificateExecution.machine.k₁) :=
  inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited (FiniteCertificateExecution.machine.Γ FiniteCertificateExecution.machine.k₁) :=
  ⟨none⟩

/-- Complete original candidate words are mapped to the supplied original
checker's input alphabet; no term or certificate lives in finite registers. -/
def encodeCertificate (certificate : List (Fin 2)) : List (program.Γ program.k₀) :=
  (certificate.map finTwoEquiv).map inputAlphabet.symm

def refusedLoop : FinTM2 :=
  FramedWordValidation.machine program (fun symbol => !(outputAlphabet symbol))

def loopTime (clock : List (Fin 2) → Nat) (bound : Nat) : Nat :=
  FramedWordValidation.totalClock program (encodeCertificate program inputAlphabet) clock
    (CertificateBounds.wordsUpTo 2 bound)

def verdictImages (symbol : Option Bool) : List Bool := [!symbol.getD false]

def verdictMachine : FinTM2 := WordHomomorphismMachine.machine verdictImages

local instance : Fintype ((refusedLoop program outputAlphabet).Γ
    (refusedLoop program outputAlphabet).k₁) := inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited ((refusedLoop program outputAlphabet).Γ
    (refusedLoop program outputAlphabet).k₁) := ⟨none⟩

/-- The original all-field loop checks every candidate, including refusals;
one further executed word map converts "all refused" into "some accepted". -/
def decisionLoop : FinTM2 := StackMachineComposition.machine
  (refusedLoop program outputAlphabet) verdictMachine (Equiv.refl (Option Bool))

def bridge : FiniteCertificateExecution.machine.Γ FiniteCertificateExecution.machine.k₁ ≃
    (decisionLoop program outputAlphabet).Γ (decisionLoop program outputAlphabet).k₀ :=
  Equiv.optionCongr inputAlphabet.symm

/-- A single original machine generates its candidate space, transfers the
complete framed output and performs the original checker on each field. -/
def searchMachine : FinTM2 := StackMachineComposition.machine
  FiniteCertificateExecution.machine (decisionLoop program outputAlphabet)
  (bridge program inputAlphabet outputAlphabet)

def searchTime (clock : List (Fin 2) → Nat) (bound : Nat) : Nat :=
  enumerationTime bound + 2 * (wire (words bound)).length + loopTime program inputAlphabet clock bound + 12

theorem frame_exact (bound : Nat) :
    (wire (words bound)).map (bridge program inputAlphabet outputAlphabet) =
      FramedWordValidation.frameWords program (encodeCertificate program inputAlphabet)
        (CertificateBounds.wordsUpTo 2 bound) := by
  simp only [wire, words, List.flatMap_map, List.map_flatMap, row, List.map_append,
    List.map_cons, List.map_nil, bridge, FramedWordValidation.frameWords,
    WordTemplateMachine.Indexed.frame, List.map_map, Function.comp_def, encodeCertificate]
  congr 1

omit [Inhabited (program.Γ program.k₀)] [Fintype (program.Γ program.k₁)] in
theorem responses_exact (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (certificates : List (List (Fin 2))) :
    FramedWordValidation.responses program (fun symbol => !(outputAlphabet symbol))
      (fun certificate => outputAlphabet.symm (checker.check claim certificate)) certificates =
        !(certificates.any (checker.check claim)) := by
  induction certificates with
  | nil => rfl
  | cons certificate rest ih =>
      simp only [FramedWordValidation.responses, List.any_cons, Equiv.apply_symm_apply, ih]
      cases checker.check claim certificate <;> cases rest.any (checker.check claim) <;> rfl

/-- The supplied checker runs are actual original transitions, not a freely
assigned per-candidate score. All rejected trials execute before this result. -/
noncomputable def decision_outputs (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (clock : List (Fin 2) → Nat)
    (runs : ∀ certificate, TM2OutputsInTime program (encodeCertificate program inputAlphabet certificate)
      (some [outputAlphabet.symm (checker.check claim certificate)]) (clock certificate))
    (bound : Nat) :
    TM2OutputsInTime (decisionLoop program outputAlphabet)
      (FramedWordValidation.frameWords program (encodeCertificate program inputAlphabet)
        (CertificateBounds.wordsUpTo 2 bound))
      (some [(CertificateBounds.boundedSearch checker claim bound).isSome])
      (loopTime program inputAlphabet clock bound + 10) := by
  let candidates := CertificateBounds.wordsUpTo 2 bound
  have checked := FramedWordValidation.outputs program (fun symbol => !(outputAlphabet symbol))
    (encodeCertificate program inputAlphabet)
    (fun certificate => outputAlphabet.symm (checker.check claim certificate)) clock runs candidates
  rw [responses_exact program outputAlphabet checker claim candidates] at checked
  have last := WordHomomorphismMachine.outputs verdictImages [some (!(candidates.any (checker.check claim)))]
  simp only [verdictImages, List.flatMap_cons, List.flatMap_nil, Option.getD_some, Bool.not_not,
    List.append_nil, List.length_cons, List.length_nil] at last
  have handed : ([some (!(candidates.any (checker.check claim)))].map (Equiv.refl (Option Bool))) =
      [some (!(candidates.any (checker.check claim)))] := rfl
  rw [← handed] at last
  have joined := StackMachineComposition.outputs (refusedLoop program outputAlphabet) verdictMachine
    (Equiv.refl (Option Bool)) _ _ _ _ _ checked last
  have verdict : (CertificateBounds.boundedSearch checker claim bound).isSome =
      candidates.any (checker.check claim) := by
    rw [CertificateBounds.boundedSearch, CertificateBounds.finiteSearch_eq_find?, List.isSome_find?]
  rw [← verdict] at joined
  convert joined using 1 <;> rfl

/-- The complete bounded-existence computation, including serialization of
every generated word, both physical handoffs, every checker invocation and
all result reads/cleanup. This returns a Boolean existence verdict, not the
first accepted certificate. -/
noncomputable def search_outputs (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (clock : List (Fin 2) → Nat)
    (runs : ∀ certificate, TM2OutputsInTime program (encodeCertificate program inputAlphabet certificate)
      (some [outputAlphabet.symm (checker.check claim certificate)]) (clock certificate))
    (bound : Nat) :
    TM2OutputsInTime (searchMachine program inputAlphabet outputAlphabet) (List.replicate bound none)
      (some [(CertificateBounds.boundedSearch checker claim bound).isSome])
      (searchTime program inputAlphabet clock bound) := by
  have generated := FiniteCertificateExecution.outputs bound
  have checked := decision_outputs program inputAlphabet outputAlphabet checker claim clock runs bound
  rw [← frame_exact program inputAlphabet outputAlphabet bound] at checked
  have joined := StackMachineComposition.outputs FiniteCertificateExecution.machine
    (decisionLoop program outputAlphabet) (bridge program inputAlphabet outputAlphabet)
    _ _ _ _ _ generated checked
  convert joined using 1
  all_goals first | rfl | (dsimp only [searchTime]; omega)

/-- Finite input does not silently make a checker's other stack alphabets
finite. This precise hypothesis propagates through the actual whole machine. -/
theorem refusedLoop_finiteAlphabet (originalFinite : ∀ key, Finite (program.Γ key)) :
    ∀ key, Finite ((refusedLoop program outputAlphabet).Γ key) := by
  intro key
  change Finite (FramedWordValidation.Alphabet program key)
  cases key with
  | none => exact inferInstanceAs (Finite (Option (program.Γ program.k₀)))
  | some key => cases key with
    | none => exact inferInstanceAs (Finite (program.Γ program.k₀))
    | some key => cases key with
      | none => exact inferInstanceAs (Finite (Option Bool))
      | some key => exact originalFinite key

theorem decisionLoop_finiteAlphabet (originalFinite : ∀ key, Finite (program.Γ key)) :
    ∀ key, Finite ((decisionLoop program outputAlphabet).Γ key) := by
  intro key
  change Finite (StackMachineComposition.Alphabet (refusedLoop program outputAlphabet) verdictMachine key)
  cases key with
  | none => exact inferInstanceAs (Finite (Option Bool))
  | some key => cases key with
    | inl key => exact refusedLoop_finiteAlphabet program outputAlphabet originalFinite key
    | inr key => cases key with
      | input => exact inferInstanceAs (Finite (Option Bool))
      | output => exact inferInstanceAs (Finite Bool)
      | result => exact inferInstanceAs (Finite Bool)

theorem searchMachine_finiteAlphabet (originalFinite : ∀ key, Finite (program.Γ key)) :
    ∀ key, Finite ((searchMachine program inputAlphabet outputAlphabet).Γ key) := by
  intro key
  change Finite (StackMachineComposition.Alphabet FiniteCertificateExecution.machine
    (decisionLoop program outputAlphabet) key)
  cases key with
  | none => exact inferInstanceAs (Finite (Option Bool))
  | some key => cases key with
    | inl key => exact inferInstanceAs (Finite (Option Bool))
    | inr key => exact decisionLoop_finiteAlphabet program outputAlphabet originalFinite key

theorem search_observation_iff (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (clock : List (Fin 2) → Nat)
    (runs : ∀ certificate, TM2OutputsInTime program (encodeCertificate program inputAlphabet certificate)
      (some [outputAlphabet.symm (checker.check claim certificate)]) (clock certificate))
    (bound budget : Nat) (verdict : Bool) :
    ExecutedBudgets.observe (searchMachine program inputAlphabet outputAlphabet) (Equiv.refl Bool)
      (List.replicate bound none) budget = some verdict ↔
      (CertificateBounds.boundedSearch checker claim bound).isSome = verdict ∧
        (search_outputs program inputAlphabet outputAlphabet checker claim clock runs bound).steps ≤ budget := by
  let execution : TM2Outputs (searchMachine program inputAlphabet outputAlphabet)
      (List.replicate bound none)
      (some ([(CertificateBounds.boundedSearch checker claim bound).isSome].map (Equiv.refl Bool).symm)) :=
    (search_outputs program inputAlphabet outputAlphabet checker claim clock runs bound).toTM2Outputs
  simpa only [execution, TM2OutputsInTime.toTM2Outputs] using
    ExecutedBudgets.observation_eq_some_iff (searchMachine program inputAlphabet outputAlphabet)
    (Equiv.refl Bool) (List.replicate bound none)
    (CertificateBounds.boundedSearch checker claim bound).isSome verdict execution budget

/-- Paying the whole serialized enumeration and checker-loop clock produces
a completed verdict. A smaller budget can instead leave the machine running. -/
theorem search_with_budget (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (clock : List (Fin 2) → Nat)
    (runs : ∀ certificate, TM2OutputsInTime program (encodeCertificate program inputAlphabet certificate)
      (some [outputAlphabet.symm (checker.check claim certificate)]) (clock certificate))
    (bound budget : Nat) (enough : searchTime program inputAlphabet clock bound ≤ budget) :
    ExecutedBudgets.observe (searchMachine program inputAlphabet outputAlphabet) (Equiv.refl Bool)
      (List.replicate bound none) budget =
        some (CertificateBounds.boundedSearch checker claim bound).isSome := by
  rw [search_observation_iff]
  exact ⟨rfl, (search_outputs program inputAlphabet outputAlphabet checker claim clock runs bound).steps_le_m.trans enough⟩

theorem search_scope (checker : Checker Claim (List (Fin 2))) (claim : Claim)
    (clock : List (Fin 2) → Nat)
    (runs : ∀ certificate, TM2OutputsInTime program (encodeCertificate program inputAlphabet certificate)
      (some [outputAlphabet.symm (checker.check claim certificate)]) (clock certificate))
    {Meaning : Claim → Prop} (sound : checker.Sound Meaning) (bound budget : Nat)
    (accepted : ExecutedBudgets.observe (searchMachine program inputAlphabet outputAlphabet) (Equiv.refl Bool)
      (List.replicate bound none) budget = some true) : Meaning claim := by
  have checked := (search_observation_iff program inputAlphabet outputAlphabet checker claim clock runs
    bound budget true).mp accepted
  rcases (CertificateBounds.boundedSearch_isSome_iff checker claim bound).mp checked.1 with
    ⟨certificate, _, valid⟩
  exact sound claim certificate valid

omit [Inhabited (program.Γ program.k₀)] [Fintype (program.Γ program.k₁)] in
theorem searchTime_written (clock : List (Fin 2) → Nat) (bound : Nat) :
    searchTime program inputAlphabet clock bound ≤
      7 * (wire (words bound)).length + bound + loopTime program inputAlphabet clock bound + 15 := by
  have written := enumerationTime_written bound
  simp only [searchTime]
  omega

end Checking

end Mettapedia.Logic.ProofSearch.FiniteCertificateExecution
