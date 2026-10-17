import Mettapedia.Languages.HOLLight.RuleInstantiationExecution
import Mettapedia.Languages.HOLLight.ClaimCheckingMachine
import Mettapedia.Computability.StackMachineSpaceGrowth

/-!
# Executed source-node admission in the direct HOL compiler

The supplied rule instance and requested source judgment are independent
physical fields. The original local instantiator computes the full ordered
premises and conclusion. A product selector reads that computed conclusion,
and a complete-word comparison checks it against the original requested goal.
Missing rules, invalid arguments and a changed requested conclusion refuse.
The full original packet and computed fields are retained for the subsequent
child traversal and HOL emission; this stage does not inspect child proofs.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.RuleNodeAdmission
open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
abbrev Alphabet := Binary.Alphabet
abbrev sourceWire := RuleInstantiationExecution.inputWire
def goalWire (goal : Pattern) := encodeWith CertificateDataEncoding.patternCodec goal
def fields (ruleInstance : RuleInstance) (goal : Pattern) : Fin 2 → List Alphabet := ![sourceWire ruleInstance, goalWire goal]
def inputWire (ruleInstance : RuleInstance) (goal : Pattern) := Indexed.argumentWire (fields ruleInstance goal)
def selector : Indexed.Template Alphabet 2 := [.inr 0]

local instance : Fintype ((Indexed.machine selector).Γ (Indexed.machine selector).k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((Indexed.machine selector).Γ (Indexed.machine selector).k₁) := inferInstanceAs (Inhabited Alphabet)
def selectedMachine (definition : CalculusLanguageDef) := StackMachineComposition.machine
  (Indexed.machine selector) (RuleInstantiationExecution.machine definition) (Equiv.refl Alphabet)
local instance (definition : CalculusLanguageDef) : Inhabited
    ((selectedMachine definition).Γ (selectedMachine definition).k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance (definition : CalculusLanguageDef) : Fintype
    ((selectedMachine definition).Γ (selectedMachine definition).k₁) := inferInstanceAs (Fintype Alphabet)
local instance (definition : CalculusLanguageDef) : Inhabited
    ((selectedMachine definition).Γ (selectedMachine definition).k₁) := inferInstanceAs (Inhabited Alphabet)
def retainedMachine (definition : CalculusLanguageDef) := RetainedWordExecution.WithOutput.Framed.machine
  (selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
def retainedFields (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) : Fin 3 → List Alphabet :=
  ![sourceWire ruleInstance, goalWire goal, RuleInstantiationExecution.output definition ruleInstance]
def retainedWire (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) :=
  Indexed.argumentWire (retainedFields definition ruleInstance goal)

theorem input_length (ruleInstance : RuleInstance) (goal : Pattern) :
    (inputWire ruleInstance goal).length = (sourceWire ruleInstance).length + (goalWire goal).length + 2 := by
  simp [inputWire, fields, Indexed.argumentWire, Indexed.frame, List.finRange_succ, Nat.add_assoc]

theorem retained_framing (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) :
    retainedWire definition ruleInstance goal = inputWire ruleInstance goal ++
      (RuleInstantiationExecution.output definition ruleInstance).map some ++ [none] := by
  simp [retainedWire, retainedFields, inputWire, fields, Indexed.argumentWire, Indexed.frame,
    List.finRange_succ, List.append_assoc]

def payloadCoefficient (definition : CalculusLanguageDef) :=
  2 + StackMachineSpaceGrowth.machinePushBound (CertificateSchemaInstantiation.Authored.machine definition) *
    (55 * CertificateSchemaInstantiation.Authored.planBudget definition + 40)

/-- Emitted storage is bounded from the instantiator's actual instruction
pushes and its actual linear run, including the refusal word. -/
theorem response_length (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) :
    (RuleInstantiationExecution.output definition ruleInstance).length ≤
      payloadCoefficient definition.1 * ((sourceWire ruleInstance).length + 1) := by
  dsimp only [RuleInstantiationExecution.output]
  rw [← RuleInstantiationExecution.guardedOutput_eq definition firstOrder]
  unfold RuleInstantiationExecution.guardedOutput
  split
  · have bound := StackMachineSpaceGrowth.output_length_le (CertificateSchemaInstantiation.Authored.machine definition.1)
      (CertificateSchemaInstantiation.Authored.outputs definition.1 ruleInstance)
    unfold payloadCoefficient
    simp only [sourceWire, RuleInstantiationExecution.inputWire] at *
    nlinarith
  · simp only [List.length_cons, List.length_nil]
    have positive : 2 ≤ payloadCoefficient definition.1 := by unfold payloadCoefficient; omega
    have scaled := Nat.mul_le_mul_left (payloadCoefficient definition.1)
      (show 1 ≤ (sourceWire ruleInstance).length + 1 by omega)
    simp only [Nat.mul_one] at scaled
    omega

noncomputable def selectedOutputs (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) :
    TM2OutputsInTime (selectedMachine definition.1) (inputWire ruleInstance goal)
      (some (RuleInstantiationExecution.output definition ruleInstance))
      ((RuleInstantiationExecution.coefficient definition.1 + 20) * ((inputWire ruleInstance goal).length + 1)^2) := by
  have selected := Indexed.outputs selector (fields ruleInstance goal)
  have same : Indexed.instantiate selector (fields ruleInstance goal) = sourceWire ruleInstance := by simp [selector, fields]
  rw [same] at selected
  have joined := StackMachineComposition.outputs (Indexed.machine selector) (RuleInstantiationExecution.machine definition.1)
    (Equiv.refl Alphabet) (inputWire ruleInstance goal) (sourceWire ruleInstance)
    (RuleInstantiationExecution.output definition ruleInstance) _ _ selected (by
      change TM2OutputsInTime (RuleInstantiationExecution.machine definition.1) ((sourceWire ruleInstance).map id) _ _
      simpa only [List.map_id] using RuleInstantiationExecution.outputs definition firstOrder ruleInstance)
  apply WordEqualityMachine.within joined
  have size := input_length ruleInstance goal
  have square := Nat.pow_le_pow_left (show (sourceWire ruleInstance).length + 1 ≤ (inputWire ruleInstance goal).length + 1 by omega) 2
  have linear : (inputWire ruleInstance goal).length + 1 ≤ ((inputWire ruleInstance goal).length + 1)^2 := le_self_pow (by omega) (by decide)
  simp only [selector, List.length_cons, List.length_nil, sourceWire, inputWire] at *
  nlinarith

def retainedCoefficient (definition : CalculusLanguageDef) :=
  RuleInstantiationExecution.coefficient definition + 80 + 22 * payloadCoefficient definition
noncomputable def retainedOutputs (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) :
    TM2OutputsInTime (retainedMachine definition.1) (inputWire ruleInstance goal)
      (some (retainedWire definition ruleInstance goal))
      (retainedCoefficient definition.1 * ((inputWire ruleInstance goal).length + 1)^2) := by
  have retained := RetainedWordExecution.WithOutput.Framed.outputs (selectedMachine definition.1)
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (inputWire ruleInstance goal)
    (RuleInstantiationExecution.output definition ruleInstance) _ (selectedOutputs definition firstOrder ruleInstance goal)
  have same : RetainedWordExecution.WithOutput.Framed.outputWord (selectedMachine definition.1)
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (inputWire ruleInstance goal)
      (RuleInstantiationExecution.output definition ruleInstance) = retainedWire definition ruleInstance goal := by
    change (inputWire ruleInstance goal).map id ++ (RuleInstantiationExecution.output definition ruleInstance).map some ++ [none] = _
    rw [List.map_id, retained_framing]
  rw [same] at retained
  apply WordEqualityMachine.within retained
  have inputSize := input_length ruleInstance goal
  have outputSize := response_length definition firstOrder ruleInstance
  have linear : (inputWire ruleInstance goal).length + 1 ≤ ((inputWire ruleInstance goal).length + 1)^2 := le_self_pow (by omega) (by decide)
  unfold retainedCoefficient
  nlinarith

abbrev conclusionField := CertificateDataTraversal.ProductField.machine true
def conclusionMachine := StackMachineComposition.Dispatch.machine conclusionField RuleInstantiationExecution.accept [(0 : Alphabet)]
def conclusionResponse (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) : List Alphabet :=
  match instantiateRule? definition ruleInstance with
  | none => [0]
  | some result => 1 :: goalWire result.2

noncomputable def conclusionOutputs (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime conclusionMachine (RuleInstantiationExecution.output definition ruleInstance)
      (some (conclusionResponse definition ruleInstance))
      (6 * ((RuleInstantiationExecution.output definition ruleInstance).length + 1)) := by
  cases instantiated : instantiateRule? definition ruleInstance with
  | none =>
    have refused := StackMachineComposition.Dispatch.outputs_refused conclusionField RuleInstantiationExecution.accept [(0 : Alphabet)]
      (0 : Alphabet) [] (by decide)
    have run : TM2OutputsInTime conclusionMachine (RuleInstantiationExecution.output definition ruleInstance)
        (some (conclusionResponse definition ruleInstance)) 2 := by
      simpa [conclusionMachine, RuleInstantiationExecution.output, conclusionResponse, instantiated,
        CertificateArgumentFraming.Execution.resultWire] using refused
    exact WordEqualityMachine.within run (by omega)
  | some result =>
    have selected := (CertificateDataTraversal.ProductField.selectSecondCodec
      (Codec.list CertificateDataEncoding.patternCodec) CertificateDataEncoding.patternCodec).outputsFun result
    dsimp only [CertificateDataTraversal.ProductField.selectSecondCodec,
      CertificateDataTraversal.ProductField.computable, CertificateDataTraversal.ProductField.successEncoding] at selected
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at selected
    change TM2OutputsInTime conclusionField ((encodeWith CertificateSchemaInstantiation.fieldsCodec result).map id)
      (some (((1 : Alphabet) :: goalWire result.2).map id))
      (4 * (encodeWith CertificateSchemaInstantiation.fieldsCodec result).length + 3) at selected
    simp only [List.map_id] at selected
    have accepted := StackMachineComposition.Dispatch.outputs_success conclusionField RuleInstantiationExecution.accept [(0 : Alphabet)]
      (1 : Alphabet) (encodeWith CertificateSchemaInstantiation.fieldsCodec result)
      ((1 : Alphabet) :: goalWire result.2) _ (by decide) selected
    have run : TM2OutputsInTime conclusionMachine (RuleInstantiationExecution.output definition ruleInstance)
        (some (conclusionResponse definition ruleInstance))
        (4 * (encodeWith CertificateSchemaInstantiation.fieldsCodec result).length + 4) := by
      simpa only [conclusionMachine, RuleInstantiationExecution.output, conclusionResponse, instantiated,
        Option.map_some, CertificateArgumentFraming.Execution.resultWire] using accepted
    apply WordEqualityMachine.within run
    simp only [RuleInstantiationExecution.output, instantiated, Option.map_some,
      CertificateArgumentFraming.Execution.resultWire, List.length_cons]
    omega

theorem conclusion_length (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) :
    (conclusionResponse definition ruleInstance).length ≤ (RuleInstantiationExecution.output definition ruleInstance).length := by
  cases instantiated : instantiateRule? definition ruleInstance with
  | none => simp [conclusionResponse, RuleInstantiationExecution.output, instantiated, CertificateArgumentFraming.Execution.resultWire]
  | some result =>
    have bound := CertificateDataTraversal.ProductField.selected_length_le true
      ((Codec.list CertificateDataEncoding.patternCodec).put result.1) (CertificateDataEncoding.patternCodec.put result.2)
    have fieldsBound : (goalWire result.2).length ≤ (encodeWith CertificateSchemaInstantiation.fieldsCodec result).length := bound
    simpa only [conclusionResponse, RuleInstantiationExecution.output, instantiated, Option.map_some,
      CertificateArgumentFraming.Execution.resultWire, List.length_cons] using Nat.add_le_add_right fieldsBound 1

def conclusionSelector : Indexed.Template Alphabet 3 := [.inr 2]
local instance : Fintype ((Indexed.machine conclusionSelector).Γ (Indexed.machine conclusionSelector).k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((Indexed.machine conclusionSelector).Γ (Indexed.machine conclusionSelector).k₁) := inferInstanceAs (Inhabited Alphabet)
def selectedConclusionMachine := StackMachineComposition.machine (Indexed.machine conclusionSelector) conclusionMachine (Equiv.refl Alphabet)

noncomputable def selectedConclusionOutputs (definition : ValidatedCalculusLanguageDef)
    (ruleInstance : RuleInstance) (goal : Pattern) :
    TM2OutputsInTime selectedConclusionMachine (retainedWire definition ruleInstance goal)
      (some (conclusionResponse definition ruleInstance)) (20 * ((retainedWire definition ruleInstance goal).length + 1)) := by
  have selected := Indexed.outputs conclusionSelector (retainedFields definition ruleInstance goal)
  have same : Indexed.instantiate conclusionSelector (retainedFields definition ruleInstance goal) =
      RuleInstantiationExecution.output definition ruleInstance := by simp [conclusionSelector, retainedFields]
  rw [same] at selected
  have joined := StackMachineComposition.outputs (Indexed.machine conclusionSelector) conclusionMachine (Equiv.refl Alphabet)
    (retainedWire definition ruleInstance goal) (RuleInstantiationExecution.output definition ruleInstance)
    (conclusionResponse definition ruleInstance) _ _ selected (by
      change TM2OutputsInTime conclusionMachine ((RuleInstantiationExecution.output definition ruleInstance).map id) _ _
      simpa only [List.map_id] using conclusionOutputs definition ruleInstance)
  apply WordEqualityMachine.within joined
  have size : (RuleInstantiationExecution.output definition ruleInstance).length ≤ (retainedWire definition ruleInstance goal).length := by
    rw [retained_framing]
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  simp only [conclusionSelector, List.length_cons, List.length_nil, retainedWire] at *
  nlinarith

local instance : Inhabited (selectedConclusionMachine.Γ selectedConclusionMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype (selectedConclusionMachine.Γ selectedConclusionMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (selectedConclusionMachine.Γ selectedConclusionMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
def projectedMachine := RetainedWordExecution.WithOutput.Framed.machine selectedConclusionMachine
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
def projectedFields (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) : Fin 4 → List Alphabet :=
  ![sourceWire ruleInstance, goalWire goal, RuleInstantiationExecution.output definition ruleInstance,
    conclusionResponse definition ruleInstance]
def projectedWire (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) :=
  Indexed.argumentWire (projectedFields definition ruleInstance goal)

theorem projected_framing (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) :
    projectedWire definition ruleInstance goal = retainedWire definition ruleInstance goal ++
      (conclusionResponse definition ruleInstance).map some ++ [none] := by
  simp [projectedWire, projectedFields, retainedWire, retainedFields, Indexed.argumentWire, Indexed.frame,
    List.finRange_succ, List.append_assoc]

noncomputable def projectedOutputs (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) :
    TM2OutputsInTime projectedMachine (retainedWire definition ruleInstance goal)
      (some (projectedWire definition ruleInstance goal)) (70 * ((retainedWire definition ruleInstance goal).length + 1)) := by
  have retained := RetainedWordExecution.WithOutput.Framed.outputs selectedConclusionMachine
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (retainedWire definition ruleInstance goal)
    (conclusionResponse definition ruleInstance) _ (selectedConclusionOutputs definition ruleInstance goal)
  have same : RetainedWordExecution.WithOutput.Framed.outputWord selectedConclusionMachine
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (retainedWire definition ruleInstance goal)
      (conclusionResponse definition ruleInstance) = projectedWire definition ruleInstance goal := by
    change (retainedWire definition ruleInstance goal).map id ++ (conclusionResponse definition ruleInstance).map some ++ [none] = _
    rw [List.map_id, projected_framing]
  rw [same] at retained
  apply WordEqualityMachine.within retained
  have projection := conclusion_length definition ruleInstance
  have parts : (RuleInstantiationExecution.output definition ruleInstance).length ≤ (retainedWire definition ruleInstance goal).length := by
    rw [retained_framing]
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  nlinarith

def result (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) : Bool :=
  (instantiateRule? definition ruleInstance).any (fun fields => decide (fields.2 = goal))

theorem compared_result (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) :
    decide (((1 : Alphabet) :: goalWire goal) = conclusionResponse definition ruleInstance) = result definition ruleInstance goal := by
  cases instantiated : instantiateRule? definition ruleInstance with
  | none => simp [conclusionResponse, instantiated, result]
  | some fields =>
    apply Bool.eq_iff_iff.mpr
    simp only [conclusionResponse, instantiated, result, Option.any_some, decide_eq_true_eq, List.cons.injEq, true_and]
    constructor
    · intro same
      exact (Binary.encodeWith_injective CertificateDataEncoding.patternCodec same).symm
    · intro same
      subst goal
      rfl

namespace Comparison
open Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.EncodedTable.ReferenceCheck (liftSymbol lift_frame lifted_length)
def fields (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) : Fin 4 → List (Option Alphabet) :=
  fun index => (projectedFields definition ruleInstance goal index).map some
def wire (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) := Indexed.argumentWire (fields definition ruleInstance goal)
def selector : Indexed.Template (Option Alphabet) 4 := [.inl (some 1), .inr 1, .inl none, .inr 3]
theorem lift_exact (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) :
    (projectedWire definition ruleInstance goal).flatMap liftSymbol = wire definition ruleInstance goal := by
  unfold projectedWire Indexed.argumentWire
  rw [lift_frame]
  simp only [List.map_map, Function.comp_def]
  rfl
theorem selector_exact (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) :
    Indexed.instantiate selector (fields definition ruleInstance goal) =
      WordEqualityMachine.packet (1 :: goalWire goal) (conclusionResponse definition ruleInstance) := by
  simp [selector, fields, projectedFields, WordEqualityMachine.packet]
local instance : Fintype ((Indexed.machine selector).Γ (Indexed.machine selector).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((Indexed.machine selector).Γ (Indexed.machine selector).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def compareMachine := StackMachineComposition.machine (Indexed.machine selector) (WordEqualityMachine.machine Alphabet) (Equiv.refl (Option Alphabet))
local instance : Fintype ((WordHomomorphismMachine.machine liftSymbol).Γ (WordHomomorphismMachine.machine liftSymbol).k₁) := inferInstanceAs (Fintype (Option (Option Alphabet)))
local instance : Inhabited ((WordHomomorphismMachine.machine liftSymbol).Γ (WordHomomorphismMachine.machine liftSymbol).k₁) := inferInstanceAs (Inhabited (Option (Option Alphabet)))
def machine := StackMachineComposition.machine (WordHomomorphismMachine.machine liftSymbol) compareMachine (Equiv.refl (Option (Option Alphabet)))
def clock (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) :=
  26 * ((projectedWire definition ruleInstance goal).length + 1) +
    5 * (1 + (goalWire goal).length) + 3 * (conclusionResponse definition ruleInstance).length + 8

noncomputable def outputs (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) :
    TM2OutputsInTime machine (projectedWire definition ruleInstance goal) (some [result definition ruleInstance goal])
      (clock definition ruleInstance goal) := by
  have lifted := WordHomomorphismMachine.outputs liftSymbol (projectedWire definition ruleInstance goal)
  have length := lifted_length (projectedWire definition ruleInstance goal)
  rw [lift_exact] at lifted length
  have selected := Indexed.outputs selector (fields definition ruleInstance goal)
  rw [selector_exact] at selected
  have compared := WordEqualityMachine.outputs ((1 : Alphabet) :: goalWire goal) (conclusionResponse definition ruleInstance)
  rw [compared_result] at compared
  have second := StackMachineComposition.outputs (Indexed.machine selector) (WordEqualityMachine.machine Alphabet)
    (Equiv.refl (Option Alphabet)) (wire definition ruleInstance goal)
    (WordEqualityMachine.packet (1 :: goalWire goal) (conclusionResponse definition ruleInstance))
    [result definition ruleInstance goal] _ _ selected (by
      change TM2OutputsInTime (WordEqualityMachine.machine Alphabet)
        ((WordEqualityMachine.packet (1 :: goalWire goal) (conclusionResponse definition ruleInstance)).map id) _ _
      simpa only [List.map_id] using compared)
  have joined := StackMachineComposition.outputs (WordHomomorphismMachine.machine liftSymbol) compareMachine
    (Equiv.refl (Option (Option Alphabet))) (projectedWire definition ruleInstance goal) (wire definition ruleInstance goal)
    [result definition ruleInstance goal] _ _ lifted (by
      change TM2OutputsInTime compareMachine ((wire definition ruleInstance goal).map id) _ _
      simpa only [List.map_id, compareMachine] using second)
  apply WordEqualityMachine.within joined
  have packetSize := WordEqualityMachine.packet_length ((1 : Alphabet) :: goalWire goal) (conclusionResponse definition ruleInstance)
  simp only [selector, List.length_cons, List.length_nil, wire] at *
  unfold clock
  omega
end Comparison

local instance (definition : CalculusLanguageDef) : Fintype
    ((retainedMachine definition).Γ (retainedMachine definition).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (definition : CalculusLanguageDef) : Inhabited
    ((retainedMachine definition).Γ (retainedMachine definition).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def preparedMachine (definition : CalculusLanguageDef) := StackMachineComposition.machine (retainedMachine definition)
  projectedMachine (Equiv.refl (Option Alphabet))
local instance (definition : CalculusLanguageDef) : Fintype
    ((preparedMachine definition).Γ (preparedMachine definition).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (definition : CalculusLanguageDef) : Inhabited
    ((preparedMachine definition).Γ (preparedMachine definition).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def machine (definition : CalculusLanguageDef) := StackMachineComposition.machine (preparedMachine definition)
  Comparison.machine (Equiv.refl (Option Alphabet))
def clock (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) :=
  retainedCoefficient definition.1 * ((inputWire ruleInstance goal).length + 1)^2 +
    2 * (retainedWire definition ruleInstance goal).length + 2 +
    70 * ((retainedWire definition ruleInstance goal).length + 1) +
    2 * (projectedWire definition ruleInstance goal).length + 2 + Comparison.clock definition ruleInstance goal
def coefficient (definition : CalculusLanguageDef) := retainedCoefficient definition + 200 * (payloadCoefficient definition + 2)

noncomputable def outputs (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) :
    TM2OutputsInTime (machine definition.1) (inputWire ruleInstance goal) (some [result definition ruleInstance goal])
      (clock definition ruleInstance goal) := by
  have first := StackMachineComposition.outputs (retainedMachine definition.1) projectedMachine (Equiv.refl (Option Alphabet))
    (inputWire ruleInstance goal) (retainedWire definition ruleInstance goal) (projectedWire definition ruleInstance goal)
    _ _ (retainedOutputs definition firstOrder ruleInstance goal) (by
      change TM2OutputsInTime projectedMachine ((retainedWire definition ruleInstance goal).map id) _ _
      simpa only [List.map_id] using projectedOutputs definition ruleInstance goal)
  exact StackMachineComposition.outputs (preparedMachine definition.1) Comparison.machine (Equiv.refl (Option Alphabet))
    (inputWire ruleInstance goal) (projectedWire definition ruleInstance goal) [result definition ruleInstance goal]
    _ _ first (by
      change TM2OutputsInTime Comparison.machine ((projectedWire definition ruleInstance goal).map id) _ _
      simpa only [List.map_id] using Comparison.outputs definition ruleInstance goal)

theorem packet_lengths (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) :
    (retainedWire definition ruleInstance goal).length ≤
      (payloadCoefficient definition.1 + 2) * ((inputWire ruleInstance goal).length + 1) ∧
    (projectedWire definition ruleInstance goal).length ≤
      (2 * payloadCoefficient definition.1 + 3) * ((inputWire ruleInstance goal).length + 1) := by
  have parts := input_length ruleInstance goal
  have response := response_length definition firstOrder ruleInstance
  have conclusion := conclusion_length definition ruleInstance
  rw [projected_framing, retained_framing]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  constructor <;> nlinarith

theorem clock_polynomial (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) :
    clock definition ruleInstance goal ≤ coefficient definition.1 * ((inputWire ruleInstance goal).length + 1)^2 := by
  obtain ⟨retained, projected⟩ := packet_lengths definition firstOrder ruleInstance goal
  have parts := input_length ruleInstance goal
  have response := response_length definition firstOrder ruleInstance
  have conclusion := conclusion_length definition ruleInstance
  have linear : (inputWire ruleInstance goal).length + 1 ≤ ((inputWire ruleInstance goal).length + 1)^2 := le_self_pow (by omega) (by decide)
  have charged := Nat.mul_le_mul_left (payloadCoefficient definition.1) linear
  unfold clock Comparison.clock coefficient
  nlinarith

/-- The original node's local admission, all packet retention and both
independent source-judgment fields are charged to one quadratic clock. -/
noncomputable def polynomialOutputs (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) :
    TM2OutputsInTime (machine definition.1) (inputWire ruleInstance goal) (some [result definition ruleInstance goal])
      (coefficient definition.1 * ((inputWire ruleInstance goal).length + 1)^2) :=
  WordEqualityMachine.within (outputs definition firstOrder ruleInstance goal) (clock_polynomial definition firstOrder ruleInstance goal)

theorem result_accepted_iff (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) :
    result definition ruleInstance goal = true ↔ ∃ premises,
      instantiateRule? definition ruleInstance = some (premises, goal) := by
  cases instantiated : instantiateRule? definition ruleInstance with
  | none => simp [result, instantiated]
  | some fields =>
    cases fields with
    | mk premises conclusion => simp [result, instantiated]

theorem run_readout (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) {word : List Bool}
    (finished : TM2Outputs (machine definition.1) (inputWire ruleInstance goal) (some word)) :
    word = [result definition ruleInstance goal] :=
  StackMachineComposition.outputs_unique finished (outputs definition firstOrder ruleInstance goal).toEvalsTo

theorem run_source_application (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern)
    (finished : TM2Outputs (machine definition.1) (inputWire ruleInstance goal) (some [true])) :
    ∃ premises, RuleApplication definition ruleInstance premises goal := by
  have accepted : result definition ruleInstance goal = true := (List.cons.inj (run_readout definition firstOrder ruleInstance goal finished)).1.symm
  obtain ⟨premises, instantiated⟩ := (result_accepted_iff definition ruleInstance goal).mp accepted
  exact ⟨premises, instantiateRule?_eq_some_iff_application.mp instantiated⟩

abbrev Input := RuleInstance × Pattern
def encodeInput (input : Input) := inputWire input.1 input.2
def evaluate (definition : ValidatedCalculusLanguageDef) (input : Input) := result definition input.1 input.2
noncomputable def realization (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1) :
    TM2ComputableInPolyTime encodeInput (fun accepted : Bool => [accepted]) (evaluate definition) where
  tm := machine definition.1
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C (coefficient definition.1) * (Polynomial.X + Polynomial.C 1)^2
  outputsFun input := by
    change TM2OutputsInTime (machine definition.1) ((encodeInput input).map id)
      (some (([evaluate definition input]).map id)) _
    simp only [List.map_id, encodeInput, evaluate, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
    exact polynomialOutputs definition firstOrder input.1 input.2

local instance : Inhabited (Comparison.machine.Γ Comparison.machine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype (Comparison.machine.Γ Comparison.machine.k₁) := inferInstanceAs (Fintype Bool)
local instance : Inhabited (Comparison.machine.Γ Comparison.machine.k₁) := inferInstanceAs (Inhabited Bool)
def retainedComparisonMachine := RetainedWordExecution.machine Comparison.machine (fun accepted => accepted)
def jobMachine (definition : CalculusLanguageDef) := StackMachineComposition.machine (preparedMachine definition)
  retainedComparisonMachine (Equiv.refl (Option Alphabet))
def jobOutput (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) : List (Option Alphabet ⊕ Bool) :=
  .inr (result definition ruleInstance goal) :: (projectedWire definition ruleInstance goal).map Sum.inl

/-- The completed job retains both supplied fields and the physically computed
ordered judgment payload; child traversal need not recompute instantiation. -/
noncomputable def jobOutputs (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) :
    TM2OutputsInTime (jobMachine definition.1) (inputWire ruleInstance goal)
      (some (jobOutput definition ruleInstance goal))
      ((coefficient definition.1 + 20 * (payloadCoefficient definition.1 + 1)) * ((inputWire ruleInstance goal).length + 1)^2) := by
  have first := StackMachineComposition.outputs (retainedMachine definition.1) projectedMachine (Equiv.refl (Option Alphabet))
    (inputWire ruleInstance goal) (retainedWire definition ruleInstance goal) (projectedWire definition ruleInstance goal)
    _ _ (retainedOutputs definition firstOrder ruleInstance goal) (by
      change TM2OutputsInTime projectedMachine ((retainedWire definition ruleInstance goal).map id) _ _
      simpa only [List.map_id] using projectedOutputs definition ruleInstance goal)
  have saved := RetainedWordExecution.outputs Comparison.machine (fun accepted => accepted)
    (projectedWire definition ruleInstance goal) (result definition ruleInstance goal) [] _
    (Comparison.outputs definition ruleInstance goal)
  have joined := StackMachineComposition.outputs (preparedMachine definition.1) retainedComparisonMachine (Equiv.refl (Option Alphabet))
    (inputWire ruleInstance goal) (projectedWire definition ruleInstance goal) (jobOutput definition ruleInstance goal)
    _ _ first (by
      change TM2OutputsInTime retainedComparisonMachine ((projectedWire definition ruleInstance goal).map id) _ _
      simpa only [List.map_id, jobOutput, retainedComparisonMachine] using saved)
  apply WordEqualityMachine.within joined
  have original := clock_polynomial definition firstOrder ruleInstance goal
  obtain ⟨_, projected⟩ := packet_lengths definition firstOrder ruleInstance goal
  have linear : (inputWire ruleInstance goal).length + 1 ≤ ((inputWire ruleInstance goal).length + 1)^2 := le_self_pow (by omega) (by decide)
  have charged := Nat.mul_le_mul_left (payloadCoefficient definition.1) linear
  simp only [List.length_nil]
  unfold clock at original
  nlinarith

theorem job_run_readout (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) {word : List (Option Alphabet ⊕ Bool)}
    (finished : TM2Outputs (jobMachine definition.1) (inputWire ruleInstance goal) (some word)) :
    word = jobOutput definition ruleInstance goal :=
  StackMachineComposition.outputs_unique finished (jobOutputs definition firstOrder ruleInstance goal).toEvalsTo

namespace Controls
open Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayPresentation
theorem matching_nullary_goal : result mpValidated ⟨⟨"a"⟩, []⟩ (judgmentP formulaA) = true := by
  simp [result, RuleInstantiationExecution.Controls.nullary_rule]
theorem changed_nullary_goal : result mpValidated ⟨⟨"a"⟩, []⟩ (judgmentP formulaB) = false := by
  simp only [result, RuleInstantiationExecution.Controls.nullary_rule, Option.any_some]
  decide +kernel
theorem matching_modus_ponens_goal : result mpValidated ⟨⟨"m"⟩, [formulaA, formulaB]⟩ (judgmentP formulaB) = true := by
  simp [result, RuleInstantiationExecution.Controls.ordered_modus_ponens]
theorem changed_modus_ponens_goal : result mpValidated ⟨⟨"m"⟩, [formulaA, formulaB]⟩ (judgmentP formulaA) = false := by
  simp only [result, RuleInstantiationExecution.Controls.ordered_modus_ponens, Option.any_some]
  decide +kernel
theorem repeated_argument_goal : result mpValidated ⟨⟨"m"⟩, [formulaA, formulaA]⟩ (judgmentP formulaA) = true := by
  simp [result, RuleInstantiationExecution.Controls.repeated_arguments]
theorem unknown_rule_refused : result mpValidated ⟨⟨"absent"⟩, []⟩ (judgmentP formulaA) = false := by
  simp [result, RuleInstantiationExecution.Controls.absent_rule_refused]
theorem missing_argument_refused : result mpValidated ⟨⟨"m"⟩, [formulaA]⟩ (judgmentP formulaB) = false := by
  simp [result, RuleInstantiationExecution.Controls.missing_argument_refused]
theorem escaping_argument_refused : result FirstOrder.InferenceTranslation.Controls.dataCalculus
    ⟨⟨"data"⟩, [.lambda none (.bvar 1)]⟩ (judgmentP (.lambda none (.bvar 1))) = false := by
  simp [result, RuleInstantiationExecution.Controls.escaping_argument_refused]
end Controls

end Mettapedia.Languages.HOLLight.RuleNodeAdmission
