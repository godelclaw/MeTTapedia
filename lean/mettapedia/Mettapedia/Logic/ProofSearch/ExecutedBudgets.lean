import Mettapedia.Logic.ProofSearch.SearchTransport
import Mettapedia.GSLT.LanguageDef.ResourceComputation

/-!
# Finite-budget observations of executed proof-search routes

The observer follows the original transition function and retains the actual
configuration and transition count. A halted result, a refused certificate and
a still-running computation are distinct. The returned count is justified by
the original `EvalsToInTime` relation, rather than supplied as a search score.

The whole-route theorem joins a witnessed candidate producer, an implemented
packet compiler and an independent checker through both physical word handoffs.
Producing a refused candidate is charged in exactly the same way as success.
The producer may be partial on other inputs, and exhausting this budget does
not refute theoremhood. No implementation or cost bound for a universal
interpreter, a route scheduler or exhaustive certificate enumeration is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ProofSearch.ExecutedBudgets

open Turing StateTransition
open Mettapedia.Computability
open Mettapedia.GSLT.LanguageDef
open SemanticEvidence ResourceTranslation

/-- A finite observation retains the original state, rather than replacing
unfinished work with a negative checking result. -/
structure Observation (Config : Type) where
  state : Config
  spent : Nat
  halted : Bool

/-- Execute at most `budget` original transitions, stopping at a halt. The
terminal test does not invent another transition or a checking verdict. This
is an executable semantic observer, not an implementation of a universal TM. -/
def probe {Config : Type} (step : Config → Option Config) (state : Config) :
    Nat → Observation Config
  | 0 => ⟨state, 0, (step state).isNone⟩
  | budget + 1 =>
      match step state with
      | none => ⟨state, 0, true⟩
      | some next =>
          let result := probe step next budget
          ⟨result.state, result.spent + 1, result.halted⟩

/-- The TM2 observer tests the original halt label directly, so a zero-budget
observation never speculatively executes another original statement. Passing
the instruction body also keeps finite-state enumeration outside execution. -/
def programProbe {Key Label Registers : Type} {Alphabet : Key → Type} [DecidableEq Key]
    (program : Label → TM2.Stmt Alphabet Label Registers)
    (state : TM2.Cfg Alphabet Label Registers) : Nat → Observation (TM2.Cfg Alphabet Label Registers)
  | 0 => ⟨state, 0, state.l.isNone⟩
  | budget + 1 =>
      match state.l with
      | none => ⟨state, 0, true⟩
      | some label =>
          let result := programProbe program (TM2.stepAux (program label) state.var state.stk) budget
          ⟨result.state, result.spent + 1, result.halted⟩

/-- Native observation executes exactly the original instruction table and
agrees with the transition-level observer, including its transition count. -/
theorem programProbe_eq {Key Label Registers : Type} {Alphabet : Key → Type} [DecidableEq Key]
    (program : Label → TM2.Stmt Alphabet Label Registers)
    (state : TM2.Cfg Alphabet Label Registers) (budget : Nat) :
    programProbe program state budget = probe (TM2.step program) state budget := by
  induction budget generalizing state with
  | zero => cases state with | mk label registers storage => cases label <;> rfl
  | succ budget ih =>
      cases state with | mk label registers storage =>
        cases label <;> simp only [programProbe, probe, TM2.step, ih]

/-- Every reported transition count is an original finite execution. A live
result has spent the entire requested transition budget. -/
theorem probe_sound {Config : Type} (step : Config → Option Config)
    (state : Config) (budget : Nat) :
    (probe step state budget).spent ≤ budget ∧
    (fun current : Option Config => current.bind step)^[
      (probe step state budget).spent] (some state) =
        some (probe step state budget).state ∧
    (probe step state budget).halted = (step (probe step state budget).state).isNone ∧
    ((probe step state budget).halted = false → (probe step state budget).spent = budget) := by
  induction budget generalizing state with
  | zero => simp [probe]
  | succ budget ih =>
      cases next : step state with
      | none => simp [probe, next]
      | some nextState =>
          rcases ih nextState with ⟨bound, execution, halted, exhausted⟩
          simp only [probe, next]
          refine ⟨by omega, ?_, halted, fun live => by have := exhausted live; omega⟩
          rw [Function.iterate_succ_apply, Option.bind_some, next]
          exact execution

def probe_run {Config : Type} (step : Config → Option Config) (state : Config) (budget : Nat) :
    EvalsToInTime step state (some (probe step state budget).state) budget where
  steps := (probe step state budget).spent
  evals_in_steps := (probe_sound step state budget).2.1
  steps_le_m := (probe_sound step state budget).1

private theorem probe_at_halt {Config : Type} (step : Config → Option Config)
    (state : Config) (halted : step state = none) (budget : Nat) :
    probe step state budget = ⟨state, 0, true⟩ := by
  cases budget <;> simp [probe, halted]

private theorem probe_of_iteration {Config : Type} (step : Config → Option Config)
    (steps : Nat) (state final : Config)
    (execution : (fun current : Option Config => current.bind step)^[steps] (some state) = some final)
    (halted : step final = none) (budget : Nat) (enough : steps ≤ budget) :
    probe step state budget = ⟨final, steps, true⟩ := by
  induction steps generalizing state budget with
  | zero =>
      have same : state = final := Option.some.inj execution
      subst state
      exact probe_at_halt step final halted budget
  | succ steps ih =>
      cases budget with
      | zero => omega
      | succ budget =>
          cases next : step state with
          | none =>
              rw [Function.iterate_succ_apply, Option.bind_some, next] at execution
              have stopped : (fun current : Option Config => current.bind step)^[steps] none = none :=
                Function.iterate_fixed (by rfl) steps
              rw [stopped] at execution
              contradiction
          | some nextState =>
              rw [Function.iterate_succ_apply, Option.bind_some, next] at execution
              have rest := ih nextState execution budget (by omega)
              simp only [probe, next, rest]

/-- Every original halting execution within the budget is observed, with its
exact count. Termination is required; reaching an intermediate state is not a
completed checking result. -/
theorem probe_complete {Config : Type} (step : Config → Option Config)
    (state final : Config) (budget : Nat)
    (execution : EvalsToInTime step state (some final) budget) (halted : step final = none) :
    probe step state budget = ⟨final, execution.steps, true⟩ :=
  probe_of_iteration step execution.steps state final execution.evals_in_steps halted budget
    execution.steps_le_m

/-- Two original halting executions have the same transition count. A proof
may supply a loose bound, but it cannot supply a different physical run. -/
theorem halting_steps_unique {Config : Type} (step : Config → Option Config)
    (state first second : Config)
    (firstRun : EvalsTo step state (some first)) (secondRun : EvalsTo step state (some second))
    (firstHalt : step first = none) (secondHalt : step second = none) :
    first = second ∧ firstRun.steps = secondRun.steps := by
  have firstObserved := probe_of_iteration step firstRun.steps state first
    firstRun.evals_in_steps firstHalt (max firstRun.steps secondRun.steps) (Nat.le_max_left _ _)
  have secondObserved := probe_of_iteration step secondRun.steps state second
    secondRun.evals_in_steps secondHalt (max firstRun.steps secondRun.steps) (Nat.le_max_right _ _)
  have same := firstObserved.symm.trans secondObserved
  exact ⟨congrArg Observation.state same, congrArg Observation.spent same⟩

theorem probe_halts_iff {Config : Type} (step : Config → Option Config)
    (state final : Config) (execution : EvalsTo step state (some final))
    (halted : step final = none) (budget : Nat) :
    (probe step state budget).halted = true ↔ execution.steps ≤ budget := by
  constructor
  · intro observed
    have sound := probe_sound step state budget
    have terminal : step (probe step state budget).state = none := by
      rw [sound.2.2.1] at observed
      exact Option.isNone_iff_eq_none.mp observed
    have same := halting_steps_unique step state _ final
      (probe_run step state budget).toEvalsTo execution terminal halted
    exact same.2 ▸ sound.1
  · intro enough
    rw [probe_of_iteration step execution.steps state final execution.evals_in_steps halted budget enough]

/-- A completed observation survives every larger budget without spending the
additional budget. -/
theorem probe_halt_mono {Config : Type} (step : Config → Option Config)
    (state : Config) (small large : Nat) (increase : small ≤ large)
    (halted : (probe step state small).halted = true) :
    probe step state large = probe step state small := by
  have sound := probe_sound step state small
  have terminal : step (probe step state small).state = none := by
    rw [sound.2.2.1] at halted
    exact Option.isNone_iff_eq_none.mp halted
  have observed := probe_of_iteration step (probe step state small).spent state _
    sound.2.1 terminal large (sound.1.trans increase)
  rw [observed]
  cases smallObserved : probe step state small with
  | mk final spent status => simp_all

/-- Read a Boolean verdict only from a halted original machine. A live state
or a malformed output word is not reported as refusal. -/
def observe (machine : FinTM2) (outputAlphabet : machine.Γ machine.k₁ ≃ Bool)
    (input : List (machine.Γ machine.k₀)) (budget : Nat) : Option Bool :=
  let result := probe machine.step (initList machine input) budget
  if result.halted then
    match (result.state.stk machine.k₁).map outputAlphabet with
    | [verdict] => some verdict
    | _ => none
  else none

/-- A known checker run characterizes every budget, including budgets too
small to finish. The threshold is the run's actual count, not its loose bound. -/
theorem observation_of_run (machine : FinTM2) (outputAlphabet : machine.Γ machine.k₁ ≃ Bool)
    (input : List (machine.Γ machine.k₀)) (verdict : Bool)
    (execution : TM2Outputs machine input (some ([verdict].map outputAlphabet.symm)))
    (budget : Nat) : observe machine outputAlphabet input budget =
      if execution.steps ≤ budget then some verdict else none := by
  have halted : machine.step (haltList machine ([verdict].map outputAlphabet.symm)) = none := rfl
  by_cases enough : execution.steps ≤ budget
  · have completed := probe_of_iteration machine.step execution.steps (initList machine input)
      (haltList machine ([verdict].map outputAlphabet.symm)) execution.evals_in_steps halted budget enough
    simp only [observe, completed, ↓reduceIte]
    simp [haltList, enough]
  · have stopped := probe_halts_iff machine.step (initList machine input) _ execution halted budget
    have live : (probe machine.step (initList machine input) budget).halted = false := by
      cases status : (probe machine.step (initList machine input) budget).halted
      · rfl
      · exact (enough (stopped.mp status)).elim
    simp only [observe, live, Bool.false_eq_true, ↓reduceIte, if_neg enough]

theorem observation_eq_some_iff (machine : FinTM2)
    (outputAlphabet : machine.Γ machine.k₁ ≃ Bool) (input : List (machine.Γ machine.k₀))
    (verdict observed : Bool)
    (execution : TM2Outputs machine input (some ([verdict].map outputAlphabet.symm)))
    (budget : Nat) : observe machine outputAlphabet input budget = some observed ↔
      verdict = observed ∧ execution.steps ≤ budget := by
  rw [observation_of_run machine outputAlphabet input verdict execution budget]
  by_cases enough : execution.steps ≤ budget <;> simp [enough]

variable {SK TK Γ Δ : Type} [Fintype Γ] [Fintype Δ] [Inhabited Γ] [Inhabited Δ]
    {S : TheoryFamily SK} {T : TheoryFamily TK}
    {SA : AuthorityContract S} {TA : AuthorityContract T}
    {se : Computability.Encoding (Packet SA) Γ}
    {te : Computability.Encoding (Packet TA) Δ}

/-- The original discovery/translation/checking machine, with no new checker
or route authority. Its two intermediate words are physically transferred. -/
noncomputable def pipeline (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (compiler : ExecutedTranslation SA TA se te) (exactReplay : compiler.toTranslation.Exact)
    (checker : CheckerExecution TA te) : FinTM2 :=
  SearchExecution.searchThenCheck producer producerOutput (compiler.thenCheck exactReplay checker)

/-- A bit-level finite-machine reading requires finite alphabets on the
producer's scratch stacks too, rather than just on its input stack. -/
theorem pipeline_finiteAlphabet (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (compiler : ExecutedTranslation SA TA se te) (exactReplay : compiler.toTranslation.Exact)
    (checker : CheckerExecution TA te) (producerFinite : ∀ key, Finite (producer.Γ key)) :
    ∀ key, Finite ((pipeline producer producerOutput compiler exactReplay checker).Γ key) := by
  intro key
  change Finite (StackMachineComposition.Alphabet producer (compiler.thenCheck exactReplay checker).tm key)
  cases key with
  | none => exact producerFinite _
  | some key => cases key with
    | inl key => exact producerFinite key
    | inr key => exact (compiler.thenCheck exactReplay checker).finiteAlphabet key

set_option backward.isDefEq.respectTransparency false in
noncomputable def pipeline_run (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (compiler : ExecutedTranslation SA TA se te) (exactReplay : compiler.toTranslation.Exact)
    (checker : CheckerExecution TA te) (input : List (producer.Γ producer.k₀))
    (packet : Packet SA) (discovery : Nat)
    (produced : TM2OutputsInTime producer input
      (some ((se.encode packet).map producerOutput.symm)) discovery) :
    TM2OutputsInTime (pipeline producer producerOutput compiler exactReplay checker) input
      (some ([checkPacket SA packet].map checker.outputAlphabet.symm))
      (discovery + 2 * (se.encode packet).length + 2 + compiler.time packet +
        2 * (te.encode (compiler.packet packet)).length + 2 + checker.time (compiler.packet packet)) := by
  have joined := SearchExecution.searchThenCheck_outputs producer producerOutput
    (compiler.thenCheck exactReplay checker) input packet discovery produced
  convert joined using 1 <;> first | rfl | simp only [ExecutedTranslation.thenCheck]; omega

/-- Every budget is characterized by the completed route's actual execution,
not by an oracle supplying a route's profile. This also covers refusal. -/
theorem pipeline_observation_iff (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (compiler : ExecutedTranslation SA TA se te) (exactReplay : compiler.toTranslation.Exact)
    (checker : CheckerExecution TA te) (input : List (producer.Γ producer.k₀))
    (packet : Packet SA) (discovery : Nat)
    (produced : TM2OutputsInTime producer input
      (some ((se.encode packet).map producerOutput.symm)) discovery)
    (verdict : Bool) (budget : Nat) :
    observe (pipeline producer producerOutput compiler exactReplay checker)
      checker.outputAlphabet input budget = some verdict ↔
    checkPacket SA packet = verdict ∧
      (pipeline_run producer producerOutput compiler exactReplay checker input packet discovery produced).steps ≤
        budget :=
  observation_eq_some_iff (pipeline producer producerOutput compiler exactReplay checker)
    checker.outputAlphabet input (checkPacket SA packet) verdict
    (pipeline_run producer producerOutput compiler exactReplay checker input packet discovery produced).toTM2Outputs
    budget

/-- Paying discovery, translation, checking and both complete-word transfers
is sufficient for a completed verdict. A refused packet incurs the same costs. -/
theorem pipeline_observed_with_budget (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (compiler : ExecutedTranslation SA TA se te) (exactReplay : compiler.toTranslation.Exact)
    (checker : CheckerExecution TA te) (input : List (producer.Γ producer.k₀))
    (packet : Packet SA) (discovery : Nat)
    (produced : TM2OutputsInTime producer input
      (some ((se.encode packet).map producerOutput.symm)) discovery)
    (budget : Nat) (enough : discovery + 2 * (se.encode packet).length + 2 + compiler.time packet +
      2 * (te.encode (compiler.packet packet)).length + 2 + checker.time (compiler.packet packet) ≤ budget) :
    observe (pipeline producer producerOutput compiler exactReplay checker)
      checker.outputAlphabet input budget = some (checkPacket SA packet) := by
  rw [pipeline_observation_iff]
  exact ⟨rfl, (pipeline_run producer producerOutput compiler exactReplay checker input packet discovery
    produced).steps_le_m.trans enough⟩

theorem pipeline_acceptance_scope (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (compiler : ExecutedTranslation SA TA se te) (exactReplay : compiler.toTranslation.Exact)
    (checker : CheckerExecution TA te) (input : List (producer.Γ producer.k₀))
    (packet : Packet SA) (discovery : Nat)
    (produced : TM2OutputsInTime producer input
      (some ((se.encode packet).map producerOutput.symm)) discovery)
    (budget : Nat)
    (accepted : observe (pipeline producer producerOutput compiler exactReplay checker)
      checker.outputAlphabet input budget = some true) : S.Scope packet.1 packet.2.1 := by
  have checked := (pipeline_observation_iff producer producerOutput compiler exactReplay checker
    input packet discovery produced true budget).mp accepted
  exact (SA.scopeAuthority _).sound _ _ checked.1

/-- Explicit discovery/translation/checking budgets already bound both
intermediate packet lengths through the actual machines' writing capacity. -/
theorem pipeline_budget_from_runs (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (compiler : ExecutedTranslation SA TA se te) (exactReplay : compiler.toTranslation.Exact)
    (checker : CheckerExecution TA te) (input : List (producer.Γ producer.k₀))
    (packet : Packet SA) (discovery : Nat)
    (produced : TM2OutputsInTime producer input
      (some ((se.encode packet).map producerOutput.symm)) discovery)
    (inputLimit discoveryLimit translationLimit checkingLimit budget : Nat)
    (inputBound : input.length ≤ inputLimit) (discoveryBound : discovery ≤ discoveryLimit)
    (translationBound : compiler.time packet ≤ translationLimit)
    (checkingBound : checker.time (compiler.packet packet) ≤ checkingLimit)
    (enough : discoveryLimit + 4 * (inputLimit +
        StackMachineSpaceGrowth.machinePushBound producer * discoveryLimit) +
      2 * StackMachineSpaceGrowth.machinePushBound compiler.tm * translationLimit +
      translationLimit + checkingLimit + 4 ≤ budget) :
    observe (pipeline producer producerOutput compiler exactReplay checker)
      checker.outputAlphabet input budget = some (checkPacket SA packet) := by
  apply pipeline_observed_with_budget producer producerOutput compiler exactReplay checker input packet
    discovery produced budget
  have written : (se.encode packet).length ≤ input.length +
      StackMachineSpaceGrowth.machinePushBound producer * discovery := by
    simpa only [List.length_map] using StackMachineSpaceGrowth.output_length_le producer produced
  have sourceGrowth := Nat.mul_le_mul_left (StackMachineSpaceGrowth.machinePushBound producer) discoveryBound
  have targetGrowth := Nat.mul_le_mul_left (StackMachineSpaceGrowth.machinePushBound compiler.tm) translationBound
  have targetWritten := compiler.output_length_le packet
  rw [Nat.mul_assoc] at enough
  omega

end Mettapedia.Logic.ProofSearch.ExecutedBudgets
