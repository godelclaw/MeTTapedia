import Mettapedia.Languages.HOLLight.QuantifierArgumentEmission
import Lean
/-!
# Executable instruction table for naming followed by SPEC emission

The table uses the original symbol-processing programs and physical stack
addresses. Fixed structural reduction removes finite-type enumeration from
runtime arguments. The instruction table, initial state and transition
function equal the machines used in the complete naming/emission clock.
The final template is held in an array with its length supplied once.
-/

set_option autoImplicit false
set_option allowUnsafeReducibility true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace Mettapedia.Languages.HOLLight.QuantifierArgumentEmission.Program
open Turing Mettapedia.Computability
open Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec.Binary
attribute [local reducible] selectedMachine preparedMachine ArgumentNamingMachine.machine
  Indexed.machine StackMachineComposition.machine RetainedWordExecution.WithOutput.machine
  WordHomomorphismMachine.machine WordTemplateMachine.machine
  StackMachineComposition.leftKey StackMachineComposition.rightKey
  RetainedWordExecution.WithOutput.Framed.untag

open Lean Elab Tactic Meta in
elab "reduce_spec_program " expression:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let expression ← Elab.Term.elabTerm expression (← goal.getType)
    let reduced ← withTransparency .reducible (reduce expression)
    goal.assign reduced
  replaceMainGoal []

def selectedBody : selectedMachine.Λ → selectedMachine.Stmt :=
  StackMachineComposition.Programs.body Indexed.Stack.result ArgumentNamingMachine.Stack.input
    ArgumentNamingMachine.Phase.start (0 : Alphabet) id
    (Indexed.arrayProgram 1 (#[.inr 0] : Array (Alphabet ⊕ Fin 2))) ArgumentNamingMachine.program

theorem selectedBody_exact : selectedBody = selectedMachine.m := by
  change StackMachineComposition.Programs.body _ _ _ _ _
    (Indexed.arrayProgram selector.length selector.toArray) _ = _
  rw [Indexed.arrayProgram_eq_program]
  exact StackMachineComposition.body_eq (Indexed.machine selector) ArgumentNamingMachine.machine (Equiv.refl _)

local instance : Fintype (selectedMachine.Γ selectedMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (selectedMachine.Γ selectedMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Inhabited (selectedMachine.Γ selectedMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
abbrev retained := RetainedWordExecution.WithOutput.machine selectedMachine

local instance : Fintype (retained.Γ retained.k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Alphabet))
local instance : Inhabited (retained.Γ retained.k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Alphabet))

def selectedRegisters : selectedMachine.σ := by reduce_spec_program selectedMachine.initialState

def retainedBody : retained.Λ → retained.Stmt :=
  RetainedWordExecution.WithOutput.Programs.statement (Γ := selectedMachine.Γ) (some (.inl Indexed.Stack.input))
    (some (.inr ArgumentNamingMachine.Stack.result)) none (0 : Alphabet)
    selectedRegisters (.inl (.emit ⟨0, by decide⟩)) selectedBody

theorem retainedBody_exact : retainedBody = retained.m := by
  unfold retainedBody
  rw [selectedBody_exact]
  rfl

abbrev tagged := RetainedWordExecution.WithOutput.Framed.taggedMachine selectedMachine
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)

local instance : Fintype (tagged.Γ tagged.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (tagged.Γ tagged.k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def retainedDefault : retained.Γ retained.k₁ := by reduce_spec_program default

abbrev mapping := WordHomomorphismMachine.machine
  (RetainedWordExecution.WithOutput.Framed.untag selectedMachine
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))
def mappingBody : mapping.Λ → mapping.Stmt := by reduce_spec_program mapping.m

theorem mappingBody_exact : mappingBody = mapping.m := rfl

def taggedBody : tagged.Λ → tagged.Stmt :=
  StackMachineComposition.Programs.body (none : retained.K) WordHomomorphismMachine.Stack.input
    WordHomomorphismMachine.Phase.read retainedDefault id retainedBody mappingBody

theorem taggedBody_exact : taggedBody = tagged.m := by
  unfold taggedBody
  rw [retainedBody_exact, mappingBody_exact]
  exact StackMachineComposition.body_eq retained mapping (Equiv.refl _)

def preparedBody : preparedMachine.Λ → preparedMachine.Stmt :=
  StackMachineComposition.Programs.body (some (.inr WordHomomorphismMachine.Stack.result) : tagged.K)
    WordTemplateMachine.Stack.input (.emit ⟨0, by decide⟩) none id taggedBody
    (WordTemplateMachine.program ([none, some none] : WordTemplateMachine.Template (Option Alphabet)))

theorem preparedBody_exact : preparedBody = preparedMachine.m := by
  unfold preparedBody
  rw [taggedBody_exact]
  exact StackMachineComposition.body_eq tagged
    (WordTemplateMachine.machine ([none, some none] : WordTemplateMachine.Template (Option Alphabet))) (Equiv.refl _)

abbrev Config (length : Nat) := TM2.Cfg
  (StackMachineComposition.Programs.Cells (FirstAlphabet := preparedMachine.Γ)
    (SecondAlphabet := Indexed.Alphabet Alphabet) preparedMachine.k₁)
  (StackMachineComposition.Programs.Labels preparedMachine.Λ (Indexed.Phase 3 length))
  (StackMachineComposition.Programs.Registers (FirstState := preparedMachine.σ)
    (SecondState := Option (Option Alphabet)) (FirstAlphabet := preparedMachine.Γ) preparedMachine.k₁)

def preparedResult : preparedMachine.K := by reduce_spec_program preparedMachine.k₁

def body (length : Nat) (table : Array (Alphabet ⊕ Fin 3)) :=
  StackMachineComposition.Programs.body preparedResult Indexed.Stack.input (.emit ⟨0, Nat.zero_lt_succ _⟩)
    (none : Option Alphabet) id preparedBody (Indexed.arrayProgram length table)

local instance : Fintype (preparedMachine.Γ preparedMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (preparedMachine.Γ preparedMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
abbrev target (template : Indexed.Template Alphabet 3) := StackMachineComposition.machine
  preparedMachine (Indexed.machine template) (Equiv.refl (Option Alphabet))

theorem body_exact (template : Indexed.Template Alphabet 3) :
    body template.length template.toArray = (target template).m := by
  unfold body
  rw [preparedBody_exact, Indexed.arrayProgram_eq_program]
  exact StackMachineComposition.body_eq preparedMachine (Indexed.machine template) (Equiv.refl _)

abbrev Key := Option (preparedMachine.K ⊕ Indexed.Stack)

private def optionEquality {A : Type} (equality : DecidableEq A) : DecidableEq (Option A) :=
  @Option.instDecidableEq A equality
private def sumEquality {A B : Type} (left : DecidableEq A) (right : DecidableEq B) : DecidableEq (A ⊕ B) :=
  fun x y => @instDecidableEqSum A B left right x y

def keyEquality : DecidableEq Key :=
  let selected := optionEquality (sumEquality Indexed.instDecidableEqStack ArgumentNamingMachine.instDecidableEqStack)
  let retained := optionEquality (optionEquality (optionEquality (optionEquality selected)))
  let tagged := optionEquality (sumEquality retained WordHomomorphismMachine.instDecidableEqStack)
  let prepared := optionEquality (sumEquality tagged WordTemplateMachine.instDecidableEqStack)
  optionEquality (sumEquality prepared Indexed.instDecidableEqStack)
local instance : DecidableEq Key := keyEquality

def step (length : Nat) (table : Array (Alphabet ⊕ Fin 3)) : Config length → Option (Config length) :=
  @TM2.step Key _ _ _ keyEquality (body length table)

theorem step_exact (template : Indexed.Template Alphabet 3) :
    step template.length template.toArray = (target template).step := by
  unfold step
  rw [show keyEquality = (target template).kDecidableEq from Subsingleton.elim _ _, body_exact]
  rfl

def inputKey : Key := by reduce_spec_program some (Sum.inl preparedMachine.k₀)
def resultKey : Key := some (.inr Indexed.Stack.result)
def preparedRegisters : preparedMachine.σ := by reduce_spec_program preparedMachine.initialState
def preparedMain : preparedMachine.Λ := by reduce_spec_program preparedMachine.main

def initial (length : Nat) (word : List (Option Alphabet)) : Config length where
  l := some (.inl preparedMain)
  var := (preparedRegisters, none, none)
  stk := Function.update (fun _ => []) inputKey word

theorem initial_exact (template : Indexed.Template Alphabet 3) (word : List (Option Alphabet)) :
    initial template.length word = initList (target template) word := by
  simp only [initial, initList]
  congr 1
  funext key
  have address : inputKey = (target template).k₀ := rfl
  simp only [Function.update, address]
  by_cases same : key = (target template).k₀
  · subst key; simp
  · simp [same]

end Mettapedia.Languages.HOLLight.QuantifierArgumentEmission.Program
