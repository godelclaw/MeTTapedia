import Mettapedia.Languages.HOLLight.OriginalChildJobs
import Mettapedia.Languages.HOLLight.RuleNodeAdmission
import Mettapedia.Computability.FramedFieldSelection

/-!
# Executed child jobs from the actual source rule instance

An original rule-instance, requested goal and child-proof list form the input.
The original source rule admission and complete requested-goal comparison run
before child preparation. The machine computes the original instantiated
premises, extracts their full list bytes, and pairs them with the submitted
children. No premise list or child judgment is supplied by the caller.

The finite calculus and local premise arity are compiled parameters. A whole
rule dispatcher must select that arity from the original authored row. This
stage prepares original child jobs and does not check the children themselves.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.NodeChildrenExecution
open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
abbrev Alphabet := Binary.Alphabet
abbrev PairCell := OriginalChildJobs.PairCell
local instance : Inhabited PairCell := ⟨.inr false⟩
attribute [local implicit_reducible] StackMachineComposition.machine StackMachineComposition.Dispatch.machine
  RetainedWordExecution.machine RetainedWordExecution.WithOutput.machine
  WordHomomorphismMachine.machine Indexed.machine Indexed.Alphabet
  FramedFieldSelection.machine OriginalChildJobs.machine
  RuleNodeAdmission.machine RuleInstantiationExecution.machine

def childWire (children : List RawOpenProof) := encodeWith (Codec.list CertificateDataEncoding.proofCodec) children
def fields (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) : Fin 3 → List Alphabet :=
  ![RuleInstantiationExecution.inputWire ruleInstance,RuleNodeAdmission.goalWire goal,childWire children]
def inputWire (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :=
  Indexed.argumentWire (fields ruleInstance goal children)
def nodeSelector : List (Fin 3) := [0,1]
local instance : Fintype ((FramedFieldSelection.machine (Γ := Alphabet) nodeSelector).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) nodeSelector).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((FramedFieldSelection.machine (Γ := Alphabet) nodeSelector).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) nodeSelector).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def selectedNodeMachine (definition : CalculusLanguageDef) := StackMachineComposition.machine
  (FramedFieldSelection.machine nodeSelector) (RuleNodeAdmission.machine definition) (Equiv.refl (Option Alphabet))
attribute [local implicit_reducible] selectedNodeMachine
local instance (definition : CalculusLanguageDef) : Fintype ((selectedNodeMachine definition).Γ (selectedNodeMachine definition).k₁) := inferInstanceAs (Fintype Bool)
local instance (definition : CalculusLanguageDef) : Inhabited ((selectedNodeMachine definition).Γ (selectedNodeMachine definition).k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance (definition : CalculusLanguageDef) : Inhabited ((selectedNodeMachine definition).Γ (selectedNodeMachine definition).k₁) := inferInstanceAs (Inhabited Bool)
def savedNodeMachine (definition : CalculusLanguageDef) := RetainedWordExecution.machine (selectedNodeMachine definition) (fun accepted => accepted)
attribute [local implicit_reducible] savedNodeMachine
local instance (definition : CalculusLanguageDef) : Fintype ((savedNodeMachine definition).Γ (savedNodeMachine definition).k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Bool))
local instance (definition : CalculusLanguageDef) : Inhabited ((savedNodeMachine definition).Γ (savedNodeMachine definition).k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Bool))
def statusCell : Option Alphabet ⊕ Bool → List (Option Alphabet)
  | .inl value => [value]
  | .inr accepted => [some (if accepted then 1 else 0)]
def testedNodeMachine (definition : CalculusLanguageDef) := StackMachineComposition.machine (savedNodeMachine definition)
  (WordHomomorphismMachine.machine statusCell) (Equiv.refl (Option Alphabet ⊕ Bool))

def instanceSelector : Indexed.Template Alphabet 3 := [.inr 0]
local instance : Fintype ((Indexed.machine instanceSelector).Γ (Indexed.machine instanceSelector).k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((Indexed.machine instanceSelector).Γ (Indexed.machine instanceSelector).k₁) := inferInstanceAs (Inhabited Alphabet)
def selectedInstantiationMachine (definition : CalculusLanguageDef) := StackMachineComposition.machine
  (Indexed.machine instanceSelector) (RuleInstantiationExecution.machine definition) (Equiv.refl Alphabet)
attribute [local implicit_reducible] selectedInstantiationMachine
local instance (definition : CalculusLanguageDef) : Fintype ((selectedInstantiationMachine definition).Γ (selectedInstantiationMachine definition).k₁) := inferInstanceAs (Fintype Alphabet)
local instance (definition : CalculusLanguageDef) : Inhabited ((selectedInstantiationMachine definition).Γ (selectedInstantiationMachine definition).k₁) := inferInstanceAs (Inhabited Alphabet)
abbrev premiseField := CertificateDataTraversal.ProductField.machine false
def premiseMachine := StackMachineComposition.Dispatch.machine premiseField RuleInstantiationExecution.accept [(0 : Alphabet)]
def selectedPremiseMachine (definition : CalculusLanguageDef) := StackMachineComposition.machine (selectedInstantiationMachine definition)
  premiseMachine (Equiv.refl Alphabet)
attribute [local implicit_reducible] selectedPremiseMachine
local instance (definition : CalculusLanguageDef) : Fintype ((selectedPremiseMachine definition).Γ (selectedPremiseMachine definition).k₁) := inferInstanceAs (Fintype Alphabet)
local instance (definition : CalculusLanguageDef) : Inhabited ((selectedPremiseMachine definition).Γ (selectedPremiseMachine definition).k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance (definition : CalculusLanguageDef) : Inhabited ((selectedPremiseMachine definition).Γ (selectedPremiseMachine definition).k₁) := inferInstanceAs (Inhabited Alphabet)
def retainedPremiseMachine (definition : CalculusLanguageDef) := RetainedWordExecution.WithOutput.Framed.machine
  (selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)

def responseSelector : Indexed.Template Alphabet 4 := [.inr 3]
def rawIdentity := WordHomomorphismMachine.machine (fun value : Alphabet => [value])
def stripMachine := StackMachineComposition.Dispatch.machine rawIdentity RuleInstantiationExecution.accept [(0 : Alphabet)]
local instance : Fintype ((Indexed.machine responseSelector).Γ (Indexed.machine responseSelector).k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((Indexed.machine responseSelector).Γ (Indexed.machine responseSelector).k₁) := inferInstanceAs (Inhabited Alphabet)
def selectedStripMachine := StackMachineComposition.machine (Indexed.machine responseSelector) stripMachine (Equiv.refl Alphabet)
attribute [local implicit_reducible] selectedStripMachine
local instance : Fintype (selectedStripMachine.Γ selectedStripMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (selectedStripMachine.Γ selectedStripMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Inhabited (selectedStripMachine.Γ selectedStripMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
def retainedStripMachine := RetainedWordExecution.WithOutput.Framed.machine selectedStripMachine
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
attribute [local implicit_reducible] retainedPremiseMachine retainedStripMachine
local instance (definition : CalculusLanguageDef) : Fintype ((retainedPremiseMachine definition).Γ (retainedPremiseMachine definition).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (definition : CalculusLanguageDef) : Inhabited ((retainedPremiseMachine definition).Γ (retainedPremiseMachine definition).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype (retainedStripMachine.Γ retainedStripMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (retainedStripMachine.Γ retainedStripMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def childSelector : List (Fin 5) := [4,2]
def preparedPremiseMachine (definition : CalculusLanguageDef) := StackMachineComposition.machine (retainedPremiseMachine definition)
  retainedStripMachine (Equiv.refl (Option Alphabet))
attribute [local implicit_reducible] preparedPremiseMachine
local instance (definition : CalculusLanguageDef) : Fintype ((preparedPremiseMachine definition).Γ (preparedPremiseMachine definition).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (definition : CalculusLanguageDef) : Inhabited ((preparedPremiseMachine definition).Γ (preparedPremiseMachine definition).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype ((FramedFieldSelection.machine (Γ := Alphabet) childSelector).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) childSelector).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((FramedFieldSelection.machine (Γ := Alphabet) childSelector).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) childSelector).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def selectedChildrenMachine (arity : Nat) := StackMachineComposition.machine
  (FramedFieldSelection.machine childSelector) (OriginalChildJobs.machine arity) (Equiv.refl (Option Alphabet))
attribute [local implicit_reducible] selectedChildrenMachine
def payloadMachine (definition : CalculusLanguageDef) (arity : Nat) := StackMachineComposition.machine (preparedPremiseMachine definition)
  (selectedChildrenMachine arity) (Equiv.refl (Option Alphabet))
attribute [local implicit_reducible] payloadMachine
local instance (definition : CalculusLanguageDef) (arity : Nat) : Fintype ((payloadMachine definition arity).Γ (payloadMachine definition arity).k₁) := inferInstanceAs (Fintype PairCell)
local instance (definition : CalculusLanguageDef) (arity : Nat) : Inhabited ((payloadMachine definition arity).Γ (payloadMachine definition arity).k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance (definition : CalculusLanguageDef) (arity : Nat) : Inhabited ((payloadMachine definition arity).Γ (payloadMachine definition arity).k₁) := inferInstanceAs (Inhabited PairCell)
def accepted (symbol : Option Alphabet) := decide (symbol = some 1)
def guardedMachine (definition : CalculusLanguageDef) (arity : Nat) := StackMachineComposition.Dispatch.machine
  (payloadMachine definition arity) accepted [(.inr false : PairCell)]
attribute [local implicit_reducible] testedNodeMachine
local instance (definition : CalculusLanguageDef) : Fintype ((testedNodeMachine definition).Γ (testedNodeMachine definition).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (definition : CalculusLanguageDef) : Inhabited ((testedNodeMachine definition).Γ (testedNodeMachine definition).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def machine (definition : CalculusLanguageDef) (arity : Nat) := StackMachineComposition.machine (testedNodeMachine definition)
  (guardedMachine definition arity) (Equiv.refl (Option Alphabet))

def nodeClock (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :=
  28 * ((inputWire ruleInstance goal children).length + 1) +
    2 * (RuleNodeAdmission.inputWire ruleInstance goal).length + 2 +
    RuleNodeAdmission.coefficient definition * ((RuleNodeAdmission.inputWire ruleInstance goal).length + 1)^2

noncomputable def selectedNodeOutputs (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :
    TM2OutputsInTime (selectedNodeMachine definition.1) (inputWire ruleInstance goal children)
      (some [RuleNodeAdmission.result definition ruleInstance goal]) (nodeClock definition.1 ruleInstance goal children) := by
  have selected := FramedFieldSelection.outputs nodeSelector (fields ruleInstance goal children)
  have same : Indexed.frame (nodeSelector.map (fields ruleInstance goal children)) = RuleNodeAdmission.inputWire ruleInstance goal := by
    simp [nodeSelector,fields,RuleNodeAdmission.inputWire,RuleNodeAdmission.fields,Indexed.argumentWire,Indexed.frame,List.finRange_succ]
  rw [same] at selected
  have ran := StackMachineComposition.outputs (FramedFieldSelection.machine nodeSelector) (RuleNodeAdmission.machine definition.1)
    (Equiv.refl (Option Alphabet)) (inputWire ruleInstance goal children) (RuleNodeAdmission.inputWire ruleInstance goal)
    [RuleNodeAdmission.result definition ruleInstance goal] _ _ selected (by
      change TM2OutputsInTime (RuleNodeAdmission.machine definition.1) ((RuleNodeAdmission.inputWire ruleInstance goal).map id) _ _
      simpa only [List.map_id] using RuleNodeAdmission.polynomialOutputs definition firstOrder ruleInstance goal)
  simpa [nodeClock,nodeSelector,inputWire,selectedNodeMachine] using ran

def testedWire (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :=
  some (if RuleNodeAdmission.result definition ruleInstance goal then (1 : Alphabet) else 0) :: inputWire ruleInstance goal children

def testedClock (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :=
  nodeClock definition ruleInstance goal children + 9 * ((inputWire ruleInstance goal children).length + 1) + 20

noncomputable def testedOutputs (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :
    TM2OutputsInTime (testedNodeMachine definition.1) (inputWire ruleInstance goal children)
      (some (testedWire definition ruleInstance goal children)) (testedClock definition.1 ruleInstance goal children) := by
  have retained := RetainedWordExecution.outputs (selectedNodeMachine definition.1) (fun accepted => accepted)
    (inputWire ruleInstance goal children) (RuleNodeAdmission.result definition ruleInstance goal) [] _
    (selectedNodeOutputs definition firstOrder ruleInstance goal children)
  let saved := (.inr (RuleNodeAdmission.result definition ruleInstance goal) ::
    (inputWire ruleInstance goal children).map Sum.inl : List (Option Alphabet ⊕ Bool))
  have projected := WordHomomorphismMachine.outputs statusCell saved
  have same : saved.flatMap statusCell = testedWire definition ruleInstance goal children := by
    simp only [saved,testedWire,List.flatMap_cons,statusCell,List.singleton_append,List.flatMap_map]
    congr 1
    induction inputWire ruleInstance goal children <;> simp_all
  rw [same] at projected
  have ran := StackMachineComposition.outputs (savedNodeMachine definition.1) (WordHomomorphismMachine.machine statusCell)
    (Equiv.refl (Option Alphabet ⊕ Bool)) (inputWire ruleInstance goal children) saved
    (testedWire definition ruleInstance goal children) _ _ retained (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine statusCell) (saved.map id) _ _
      simpa only [List.map_id] using projected)
  apply WordEqualityMachine.within ran
  simp only [testedClock,saved,testedWire,List.length_cons,List.length_map,List.length_nil]
  omega

def premiseResponse (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) :=
  match instantiateRule? definition ruleInstance with
  | none => [(0 : Alphabet)]
  | some result => 1 :: encodeWith (Codec.list CertificateDataEncoding.patternCodec) result.1

noncomputable def premiseOutputs (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime premiseMachine (RuleInstantiationExecution.output definition ruleInstance)
      (some (premiseResponse definition ruleInstance)) (6 * ((RuleInstantiationExecution.output definition ruleInstance).length + 1)) := by
  cases instantiated : instantiateRule? definition ruleInstance with
  | none =>
    have refused := StackMachineComposition.Dispatch.outputs_refused premiseField RuleInstantiationExecution.accept [(0 : Alphabet)]
      (0 : Alphabet) [] (by decide)
    have run : TM2OutputsInTime premiseMachine (RuleInstantiationExecution.output definition ruleInstance)
        (some (premiseResponse definition ruleInstance)) 2 := by
      simpa [premiseMachine,RuleInstantiationExecution.output,premiseResponse,instantiated,
        CertificateArgumentFraming.Execution.resultWire] using refused
    exact WordEqualityMachine.within run (by omega)
  | some result =>
    have selected := (CertificateDataTraversal.ProductField.selectFirstCodec
      (Codec.list CertificateDataEncoding.patternCodec) CertificateDataEncoding.patternCodec).outputsFun result
    dsimp only [CertificateDataTraversal.ProductField.selectFirstCodec,CertificateDataTraversal.ProductField.computable,
      CertificateDataTraversal.ProductField.successEncoding] at selected
    simp only [eval_add,eval_mul,eval_C,eval_X] at selected
    change TM2OutputsInTime premiseField ((encodeWith CertificateSchemaInstantiation.fieldsCodec result).map id)
      (some (((1 : Alphabet) :: encodeWith (Codec.list CertificateDataEncoding.patternCodec) result.1).map id))
      (4 * (encodeWith CertificateSchemaInstantiation.fieldsCodec result).length + 3) at selected
    simp only [List.map_id] at selected
    have acceptedRun := StackMachineComposition.Dispatch.outputs_success premiseField RuleInstantiationExecution.accept [(0 : Alphabet)]
      (1 : Alphabet) (encodeWith CertificateSchemaInstantiation.fieldsCodec result)
      ((1 : Alphabet) :: encodeWith (Codec.list CertificateDataEncoding.patternCodec) result.1) _ (by decide) selected
    have run : TM2OutputsInTime premiseMachine (RuleInstantiationExecution.output definition ruleInstance)
        (some (premiseResponse definition ruleInstance)) (4 * (encodeWith CertificateSchemaInstantiation.fieldsCodec result).length + 4) := by
      simpa only [premiseMachine,RuleInstantiationExecution.output,premiseResponse,instantiated,Option.map_some,
        CertificateArgumentFraming.Execution.resultWire] using acceptedRun
    apply WordEqualityMachine.within run
    simp only [RuleInstantiationExecution.output,instantiated,Option.map_some,CertificateArgumentFraming.Execution.resultWire,List.length_cons]
    omega

def instantiationClock (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :=
  8 * ((inputWire ruleInstance goal children).length + 1) + 2 * (RuleInstantiationExecution.inputWire ruleInstance).length + 2 +
    RuleInstantiationExecution.coefficient definition * ((RuleInstantiationExecution.inputWire ruleInstance).length + 1)^2
noncomputable def selectedInstantiationOutputs (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :
    TM2OutputsInTime (selectedInstantiationMachine definition.1) (inputWire ruleInstance goal children)
      (some (RuleInstantiationExecution.output definition ruleInstance)) (instantiationClock definition.1 ruleInstance goal children) := by
  have selected := Indexed.outputs instanceSelector (fields ruleInstance goal children)
  have same : Indexed.instantiate instanceSelector (fields ruleInstance goal children) = RuleInstantiationExecution.inputWire ruleInstance := by
    simp [instanceSelector,Indexed.instantiate,fields]
  rw [same] at selected
  have ran := StackMachineComposition.outputs (Indexed.machine instanceSelector) (RuleInstantiationExecution.machine definition.1)
    (Equiv.refl Alphabet) (inputWire ruleInstance goal children) (RuleInstantiationExecution.inputWire ruleInstance)
    (RuleInstantiationExecution.output definition ruleInstance) _ _ selected (by
      change TM2OutputsInTime (RuleInstantiationExecution.machine definition.1) ((RuleInstantiationExecution.inputWire ruleInstance).map id) _ _
      simpa only [List.map_id] using RuleInstantiationExecution.outputs definition firstOrder ruleInstance)
  simpa [selectedInstantiationMachine,instantiationClock,instanceSelector,inputWire] using ran

def premiseClock (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :=
  instantiationClock definition.1 ruleInstance goal children + 2 * (RuleInstantiationExecution.output definition ruleInstance).length + 2 +
    6 * ((RuleInstantiationExecution.output definition ruleInstance).length + 1)
noncomputable def selectedPremiseOutputs (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :
    TM2OutputsInTime (selectedPremiseMachine definition.1) (inputWire ruleInstance goal children)
      (some (premiseResponse definition ruleInstance)) (premiseClock definition ruleInstance goal children) := by
  have ran := StackMachineComposition.outputs (selectedInstantiationMachine definition.1) premiseMachine (Equiv.refl Alphabet)
    (inputWire ruleInstance goal children) (RuleInstantiationExecution.output definition ruleInstance) (premiseResponse definition ruleInstance)
    _ _ (selectedInstantiationOutputs definition firstOrder ruleInstance goal children) (by
      change TM2OutputsInTime premiseMachine ((RuleInstantiationExecution.output definition ruleInstance).map id) _ _
      simpa only [List.map_id] using premiseOutputs definition ruleInstance)
  exact ran

def retainedFields (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) : Fin 4 → List Alphabet :=
  ![RuleInstantiationExecution.inputWire ruleInstance,RuleNodeAdmission.goalWire goal,childWire children,premiseResponse definition ruleInstance]
def retainedWire (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :=
  Indexed.argumentWire (retainedFields definition ruleInstance goal children)
theorem retained_framing (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :
    retainedWire definition ruleInstance goal children = inputWire ruleInstance goal children ++
      (premiseResponse definition ruleInstance).map some ++ [none] := by
  simp [retainedWire,retainedFields,inputWire,fields,Indexed.argumentWire,Indexed.frame,List.finRange_succ,List.append_assoc]
def retainedClock (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :=
  premiseClock definition ruleInstance goal children + 23 * (inputWire ruleInstance goal children).length +
    22 * (premiseResponse definition ruleInstance).length + 23
noncomputable def retainedOutputs (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :
    TM2OutputsInTime (retainedPremiseMachine definition.1) (inputWire ruleInstance goal children)
      (some (retainedWire definition ruleInstance goal children)) (retainedClock definition ruleInstance goal children) := by
  have ran := RetainedWordExecution.WithOutput.Framed.outputs (selectedPremiseMachine definition.1)
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (inputWire ruleInstance goal children)
    (premiseResponse definition ruleInstance) _ (selectedPremiseOutputs definition firstOrder ruleInstance goal children)
  have same : RetainedWordExecution.WithOutput.Framed.outputWord (selectedPremiseMachine definition.1)
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (inputWire ruleInstance goal children)
      (premiseResponse definition ruleInstance) = retainedWire definition ruleInstance goal children := by
    change (inputWire ruleInstance goal children).map id ++ (premiseResponse definition ruleInstance).map some ++ [none] = _
    rw [List.map_id,retained_framing]
  rw [same] at ran
  exact ran

def goalListWire (premises : List Pattern) := encodeWith (Codec.list CertificateDataEncoding.patternCodec) premises
def stripClock (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern)
    (children : List RawOpenProof) (premises : List Pattern) :=
  8 * ((retainedWire definition ruleInstance goal children).length + 1) +
    2 * (premiseResponse definition ruleInstance).length + 2 + 4 * (goalListWire premises).length + 3

noncomputable def selectedStripOutputs (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern)
    (children : List RawOpenProof) (premises : List Pattern)
    (instantiated : instantiateRule? definition ruleInstance = some (premises,goal)) :
    TM2OutputsInTime selectedStripMachine (retainedWire definition ruleInstance goal children)
      (some (goalListWire premises)) (stripClock definition ruleInstance goal children premises) := by
  have selected := Indexed.outputs responseSelector (retainedFields definition ruleInstance goal children)
  have same : Indexed.instantiate responseSelector (retainedFields definition ruleInstance goal children) =
      premiseResponse definition ruleInstance := by simp [responseSelector,Indexed.instantiate,retainedFields]
  rw [same] at selected
  have body := WordHomomorphismMachine.outputs (fun value : Alphabet => [value]) (goalListWire premises)
  have flat : (goalListWire premises).flatMap (fun value => [value]) = goalListWire premises := by simp
  rw [flat] at body
  have stripped := StackMachineComposition.Dispatch.outputs_success rawIdentity RuleInstantiationExecution.accept [(0 : Alphabet)]
    (1 : Alphabet) (goalListWire premises) (goalListWire premises) _ (by decide) body
  have response : premiseResponse definition ruleInstance = 1 :: goalListWire premises := by
    simp [premiseResponse,instantiated,goalListWire]
  have run : TM2OutputsInTime stripMachine (premiseResponse definition ruleInstance) (some (goalListWire premises))
      (4 * (goalListWire premises).length + 3) := by
    rw [response]
    convert stripped using 1
    all_goals simp [rawIdentity,stripMachine]
    all_goals omega
  have joined := StackMachineComposition.outputs (Indexed.machine responseSelector) stripMachine (Equiv.refl Alphabet)
    (retainedWire definition ruleInstance goal children) (premiseResponse definition ruleInstance) (goalListWire premises)
    _ _ selected (by
      change TM2OutputsInTime stripMachine ((premiseResponse definition ruleInstance).map id) _ _
      simpa only [List.map_id] using run)
  simpa [selectedStripMachine,stripClock,responseSelector,retainedWire,Nat.add_assoc] using joined

def preparedFields (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern)
    (children : List RawOpenProof) (premises : List Pattern) : Fin 5 → List Alphabet :=
  ![RuleInstantiationExecution.inputWire ruleInstance,RuleNodeAdmission.goalWire goal,childWire children,
    premiseResponse definition ruleInstance,goalListWire premises]
def preparedWire (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern)
    (children : List RawOpenProof) (premises : List Pattern) := Indexed.argumentWire (preparedFields definition ruleInstance goal children premises)
theorem prepared_framing (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern)
    (children : List RawOpenProof) (premises : List Pattern) :
    preparedWire definition ruleInstance goal children premises = retainedWire definition ruleInstance goal children ++
      (goalListWire premises).map some ++ [none] := by
  simp [preparedWire,preparedFields,retainedWire,retainedFields,Indexed.argumentWire,Indexed.frame,List.finRange_succ,List.append_assoc]
def stripRetainedClock (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern)
    (children : List RawOpenProof) (premises : List Pattern) :=
  stripClock definition ruleInstance goal children premises + 23 * (retainedWire definition ruleInstance goal children).length +
    22 * (goalListWire premises).length + 23
noncomputable def stripRetainedOutputs (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern)
    (children : List RawOpenProof) (premises : List Pattern)
    (instantiated : instantiateRule? definition ruleInstance = some (premises,goal)) :
    TM2OutputsInTime retainedStripMachine (retainedWire definition ruleInstance goal children)
      (some (preparedWire definition ruleInstance goal children premises)) (stripRetainedClock definition ruleInstance goal children premises) := by
  have ran := RetainedWordExecution.WithOutput.Framed.outputs selectedStripMachine
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (retainedWire definition ruleInstance goal children)
    (goalListWire premises) _ (selectedStripOutputs definition ruleInstance goal children premises instantiated)
  have same : RetainedWordExecution.WithOutput.Framed.outputWord selectedStripMachine
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (retainedWire definition ruleInstance goal children)
      (goalListWire premises) = preparedWire definition ruleInstance goal children premises := by
    change (retainedWire definition ruleInstance goal children).map id ++ (goalListWire premises).map some ++ [none] = _
    rw [List.map_id,prepared_framing]
  rw [same] at ran
  exact ran

def preparedClock (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern)
    (children : List RawOpenProof) (premises : List Pattern) :=
  retainedClock definition ruleInstance goal children + 2 * (retainedWire definition ruleInstance goal children).length + 2 +
    stripRetainedClock definition ruleInstance goal children premises
noncomputable def preparedOutputs (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) (premises : List Pattern)
    (instantiated : instantiateRule? definition ruleInstance = some (premises,goal)) :
    TM2OutputsInTime (preparedPremiseMachine definition.1) (inputWire ruleInstance goal children)
      (some (preparedWire definition ruleInstance goal children premises)) (preparedClock definition ruleInstance goal children premises) := by
  have ran := StackMachineComposition.outputs (retainedPremiseMachine definition.1) retainedStripMachine (Equiv.refl (Option Alphabet))
    (inputWire ruleInstance goal children) (retainedWire definition ruleInstance goal children)
    (preparedWire definition ruleInstance goal children premises) _ _ (retainedOutputs definition firstOrder ruleInstance goal children) (by
      change TM2OutputsInTime retainedStripMachine ((retainedWire definition ruleInstance goal children).map id) _ _
      simpa only [List.map_id] using stripRetainedOutputs definition ruleInstance goal children premises instantiated)
  exact ran

def childrenClock (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern)
    (children : List RawOpenProof) (premises : List Pattern) :=
  28 * ((preparedWire definition ruleInstance goal children premises).length + 1) +
    33 * (OriginalChildJobs.inputWire premises children).length + 48
noncomputable def childrenOutputs (definition : ValidatedCalculusLanguageDef) (arity : Nat)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) (premises : List Pattern) :
    TM2OutputsInTime (selectedChildrenMachine arity) (preparedWire definition ruleInstance goal children premises)
      (some (OriginalChildJobs.outputWire arity premises children)) (childrenClock definition ruleInstance goal children premises) := by
  have selected := FramedFieldSelection.outputs childSelector (preparedFields definition ruleInstance goal children premises)
  have same : Indexed.frame (childSelector.map (preparedFields definition ruleInstance goal children premises)) =
      OriginalChildJobs.inputWire premises children := by
    simp [childSelector,preparedFields,OriginalChildJobs.inputWire,OriginalChildJobs.encodeField,goalListWire,childWire]
  rw [same] at selected
  have ran := StackMachineComposition.outputs (FramedFieldSelection.machine childSelector) (OriginalChildJobs.machine arity)
    (Equiv.refl (Option Alphabet)) (preparedWire definition ruleInstance goal children premises)
    (OriginalChildJobs.inputWire premises children) (OriginalChildJobs.outputWire arity premises children) _ _ selected (by
      change TM2OutputsInTime (OriginalChildJobs.machine arity) ((OriginalChildJobs.inputWire premises children).map id) _ _
      simpa only [List.map_id] using OriginalChildJobs.outputs arity premises children)
  convert ran using 1
  · rfl
  · simp [childrenClock,childSelector,preparedWire]
    omega

def payloadClock (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern)
    (children : List RawOpenProof) (premises : List Pattern) :=
  preparedClock definition ruleInstance goal children premises +
    2 * (preparedWire definition ruleInstance goal children premises).length + 2 +
    childrenClock definition ruleInstance goal children premises
noncomputable def payloadOutputs (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1) (arity : Nat)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) (premises : List Pattern)
    (instantiated : instantiateRule? definition ruleInstance = some (premises,goal)) :
    TM2OutputsInTime (payloadMachine definition.1 arity) (inputWire ruleInstance goal children)
      (some (OriginalChildJobs.outputWire arity premises children)) (payloadClock definition ruleInstance goal children premises) := by
  have ran := StackMachineComposition.outputs (preparedPremiseMachine definition.1) (selectedChildrenMachine arity)
    (Equiv.refl (Option Alphabet)) (inputWire ruleInstance goal children)
    (preparedWire definition ruleInstance goal children premises) (OriginalChildJobs.outputWire arity premises children)
    _ _ (preparedOutputs definition firstOrder ruleInstance goal children premises instantiated) (by
      change TM2OutputsInTime (selectedChildrenMachine arity) ((preparedWire definition ruleInstance goal children premises).map id) _ _
      simpa only [List.map_id] using childrenOutputs definition arity ruleInstance goal children premises)
  exact ran

def resultWire (definition : ValidatedCalculusLanguageDef) (arity : Nat)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) : List PairCell :=
  if RuleNodeAdmission.result definition ruleInstance goal then
    match instantiateRule? definition ruleInstance with
    | none => [.inr false]
    | some result => OriginalChildJobs.outputWire arity result.1 children
  else [.inr false]

def guardedClock (definition : ValidatedCalculusLanguageDef)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :=
  if RuleNodeAdmission.result definition ruleInstance goal then
    match instantiateRule? definition ruleInstance with
    | none => (inputWire ruleInstance goal children).length + 2
    | some result => payloadClock definition ruleInstance goal children result.1 + 1
  else (inputWire ruleInstance goal children).length + 2

def clock (definition : ValidatedCalculusLanguageDef)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :=
  testedClock definition.1 ruleInstance goal children + 2 * (testedWire definition ruleInstance goal children).length + 2 +
    guardedClock definition ruleInstance goal children

noncomputable def guardedOutputs (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (arity : Nat) (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :
    TM2OutputsInTime (guardedMachine definition.1 arity) (testedWire definition ruleInstance goal children)
      (some (resultWire definition arity ruleInstance goal children)) (guardedClock definition ruleInstance goal children) := by
  cases admitted : RuleNodeAdmission.result definition ruleInstance goal with
  | false =>
    have refused := StackMachineComposition.Dispatch.outputs_refused (payloadMachine definition.1 arity) accepted [(.inr false : PairCell)]
      (some (0 : Alphabet)) (inputWire ruleInstance goal children) (by decide)
    simpa only [guardedMachine,testedWire,resultWire,guardedClock,admitted,Bool.false_eq_true,↓reduceIte] using refused
  | true =>
    cases instantiated : instantiateRule? definition ruleInstance with
    | none => simp [RuleNodeAdmission.result,instantiated] at admitted
    | some pair =>
      rcases pair with ⟨premises,conclusion⟩
      have same : conclusion = goal := by simpa [RuleNodeAdmission.result,instantiated] using admitted
      subst conclusion
      have run := payloadOutputs definition firstOrder arity ruleInstance goal children premises instantiated
      have joined := StackMachineComposition.Dispatch.outputs_success (payloadMachine definition.1 arity) accepted [(.inr false : PairCell)]
        (some (1 : Alphabet)) (inputWire ruleInstance goal children) (OriginalChildJobs.outputWire arity premises children)
        _ (by decide) run
      simpa only [guardedMachine,testedWire,resultWire,guardedClock,admitted,↓reduceIte,instantiated] using joined

/-- Full original node-request images execute all guards and either return
computed original jobs or a distinct refusal. No source judgment is a runtime
callback or input to this machine. -/
noncomputable def outputs (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (arity : Nat) (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :
    TM2OutputsInTime (machine definition.1 arity) (inputWire ruleInstance goal children)
      (some (resultWire definition arity ruleInstance goal children)) (clock definition ruleInstance goal children) := by
  have run := StackMachineComposition.outputs (testedNodeMachine definition.1) (guardedMachine definition.1 arity)
    (Equiv.refl (Option Alphabet)) (inputWire ruleInstance goal children) (testedWire definition ruleInstance goal children)
    (resultWire definition arity ruleInstance goal children) _ _ (testedOutputs definition firstOrder ruleInstance goal children) (by
      change TM2OutputsInTime (guardedMachine definition.1 arity) ((testedWire definition ruleInstance goal children).map id) _ _
      simpa only [List.map_id] using guardedOutputs definition firstOrder arity ruleInstance goal children)
  exact run

/-- Independent original pair-codec readout of the physically produced jobs. -/
theorem result_readout (definition : ValidatedCalculusLanguageDef) (arity : Nat)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :
    OriginalChildJobs.readOutput (resultWire definition arity ruleInstance goal children) =
      (match instantiateRule? definition ruleInstance with
      | none => none
      | some result => if result.2 = goal ∧ result.1.length = arity ∧ children.length = arity
          then some (result.1.zip children) else none) := by
  cases instantiated : instantiateRule? definition ruleInstance with
  | none => simp [resultWire,RuleNodeAdmission.result,instantiated,OriginalChildJobs.readOutput,FramedWordPairing.readOutput]
  | some pair =>
    rcases pair with ⟨premises,conclusion⟩
    by_cases same : conclusion = goal
    · subst conclusion
      simp only [resultWire,RuleNodeAdmission.result,instantiated,Option.any_some,decide_true,↓reduceIte]
      rw [OriginalChildJobs.readOutput_exact]
      simp
    · simp [resultWire,RuleNodeAdmission.result,instantiated,same,OriginalChildJobs.readOutput,FramedWordPairing.readOutput]

theorem run_readout (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1) (arity : Nat)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) {word : List PairCell}
    (finished : TM2Outputs (machine definition.1 arity) (inputWire ruleInstance goal children) (some word)) :
    word = resultWire definition arity ruleInstance goal children :=
  StackMachineComposition.outputs_unique finished (outputs definition firstOrder arity ruleInstance goal children).toEvalsTo

theorem run_source_application (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1) (arity : Nat)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) {word : List PairCell}
    {jobs : List (Pattern × RawOpenProof)}
    (finished : TM2Outputs (machine definition.1 arity) (inputWire ruleInstance goal children) (some word))
    (decoded : OriginalChildJobs.readOutput word = some jobs) :
    ∃ premises, RuleApplication definition ruleInstance premises goal ∧
      premises.length = arity ∧ children.length = arity ∧ jobs = premises.zip children := by
  rw [run_readout definition firstOrder arity ruleInstance goal children finished,result_readout] at decoded
  cases instantiated : instantiateRule? definition ruleInstance with
  | none => simp [instantiated] at decoded
  | some pair =>
    rcases pair with ⟨premises,conclusion⟩
    simp only [instantiated] at decoded
    split at decoded
    · rename_i admitted
      rcases admitted with ⟨rfl,premiseCount,childCount⟩
      exact ⟨premises,instantiateRule?_eq_some_iff_application.mp instantiated,premiseCount,childCount,Option.some.inj decoded |>.symm⟩
    · cases decoded

theorem input_length (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :
    (inputWire ruleInstance goal children).length = (RuleInstantiationExecution.inputWire ruleInstance).length +
      (RuleNodeAdmission.goalWire goal).length + (childWire children).length + 3 := by
  simp [inputWire,fields,Indexed.argumentWire,Indexed.frame,List.finRange_succ,Nat.add_assoc]

theorem premise_response_length (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) :
    (premiseResponse definition ruleInstance).length ≤ (RuleInstantiationExecution.output definition ruleInstance).length := by
  cases instantiated : instantiateRule? definition ruleInstance with
  | none => simp [premiseResponse,RuleInstantiationExecution.output,instantiated,
      CertificateArgumentFraming.Execution.resultWire]
  | some pair =>
    simp only [premiseResponse,RuleInstantiationExecution.output,instantiated,Option.map_some,
      CertificateArgumentFraming.Execution.resultWire,List.length_cons]
    simp only [CertificateSchemaInstantiation.fieldsCodec,Binary.encodeWith,Codec.prod,encodeData_pair,
      List.length_cons,List.length_append]
    omega

theorem packet_lengths (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) (premises : List Pattern)
    (instantiated : instantiateRule? definition ruleInstance = some (premises,goal)) :
    (RuleInstantiationExecution.output definition ruleInstance).length ≤
        RuleNodeAdmission.payloadCoefficient definition.1 * ((inputWire ruleInstance goal children).length + 1) ∧
      (premiseResponse definition ruleInstance).length ≤
        RuleNodeAdmission.payloadCoefficient definition.1 * ((inputWire ruleInstance goal children).length + 1) ∧
      (goalListWire premises).length ≤
        RuleNodeAdmission.payloadCoefficient definition.1 * ((inputWire ruleInstance goal children).length + 1) ∧
      (retainedWire definition ruleInstance goal children).length ≤
        (RuleNodeAdmission.payloadCoefficient definition.1 + 1) * ((inputWire ruleInstance goal children).length + 1) ∧
      (preparedWire definition ruleInstance goal children premises).length ≤
        (2 * RuleNodeAdmission.payloadCoefficient definition.1 + 2) * ((inputWire ruleInstance goal children).length + 1) ∧
      (OriginalChildJobs.inputWire premises children).length ≤
        (RuleNodeAdmission.payloadCoefficient definition.1 + 2) * ((inputWire ruleInstance goal children).length + 1) := by
  have inputSize := input_length ruleInstance goal children
  have sourceSize : (RuleNodeAdmission.sourceWire ruleInstance).length + 1 ≤
      (inputWire ruleInstance goal children).length + 1 := by
    simp only [RuleNodeAdmission.sourceWire,RuleInstantiationExecution.inputWire] at inputSize ⊢
    omega
  have response := (RuleNodeAdmission.response_length definition firstOrder ruleInstance).trans
    (Nat.mul_le_mul_left _ sourceSize)
  have premise := (premise_response_length definition ruleInstance).trans response
  have goals : (goalListWire premises).length ≤ (premiseResponse definition ruleInstance).length := by
    simp [goalListWire,premiseResponse,instantiated]
  have retained : (retainedWire definition ruleInstance goal children).length =
      (inputWire ruleInstance goal children).length + (premiseResponse definition ruleInstance).length + 1 := by
    rw [retained_framing]; simp [Nat.add_assoc]
  have prepared : (preparedWire definition ruleInstance goal children premises).length =
      (retainedWire definition ruleInstance goal children).length + (goalListWire premises).length + 1 := by
    rw [prepared_framing]; simp [Nat.add_assoc]
  have childSize : (OriginalChildJobs.inputWire premises children).length =
      (goalListWire premises).length + (childWire children).length + 2 := by
    simpa [OriginalChildJobs.encodeField,goalListWire,childWire] using OriginalChildJobs.input_length premises children
  refine ⟨response,premise,goals.trans premise,?_,?_,?_⟩ <;> nlinarith

theorem tested_clock_bound (definition : CalculusLanguageDef) (ruleInstance : RuleInstance)
    (goal : Pattern) (children : List RawOpenProof) :
    testedClock definition ruleInstance goal children ≤
      (RuleNodeAdmission.coefficient definition + 59) * ((inputWire ruleInstance goal children).length + 1)^2 := by
  have inputSize := input_length ruleInstance goal children
  have nodeSize := RuleNodeAdmission.input_length ruleInstance goal
  have nodeBound : (RuleNodeAdmission.inputWire ruleInstance goal).length + 1 ≤
      (inputWire ruleInstance goal children).length + 1 := by
    simp only [RuleNodeAdmission.sourceWire,RuleInstantiationExecution.inputWire] at nodeSize inputSize
    omega
  have square := Nat.mul_le_mul_left (RuleNodeAdmission.coefficient definition) (Nat.pow_le_pow_left nodeBound 2)
  have linear : (inputWire ruleInstance goal children).length + 1 ≤
      ((inputWire ruleInstance goal children).length + 1)^2 := le_self_pow (by omega) (by decide)
  unfold testedClock nodeClock
  nlinarith

theorem payload_clock_bound (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) (premises : List Pattern)
    (instantiated : instantiateRule? definition ruleInstance = some (premises,goal)) :
    payloadClock definition ruleInstance goal children premises ≤
      (RuleInstantiationExecution.coefficient definition.1 + 316 +
        184 * RuleNodeAdmission.payloadCoefficient definition.1) * ((inputWire ruleInstance goal children).length + 1)^2 := by
  let n := (inputWire ruleInstance goal children).length + 1
  let p := RuleNodeAdmission.payloadCoefficient definition.1
  let i := RuleInstantiationExecution.coefficient definition.1
  obtain ⟨response,premise,goals,retained,prepared,childSize⟩ :=
    packet_lengths definition firstOrder ruleInstance goal children premises instantiated
  change _ ≤ p * n at response premise goals
  change _ ≤ (p+1)*n at retained
  change _ ≤ (2*p+2)*n at prepared
  change _ ≤ (p+2)*n at childSize
  have inputSize := input_length ruleInstance goal children
  have sourceBound : (RuleInstantiationExecution.inputWire ruleInstance).length + 1 ≤ n := by dsimp [n]; omega
  have square := Nat.mul_le_mul_left i (Nat.pow_le_pow_left sourceBound 2)
  have positive : 1 ≤ n := by dsimp [n]; omega
  have linear : n ≤ n^2 := le_self_pow positive (by decide)
  have inputBound : (inputWire ruleInstance goal children).length + 1 = n := rfl
  have instantiation : instantiationClock definition.1 ruleInstance goal children ≤ i*n^2+10*n := by
    unfold instantiationClock
    change 8*n + 2*(RuleInstantiationExecution.inputWire ruleInstance).length + 2 +
      i*((RuleInstantiationExecution.inputWire ruleInstance).length+1)^2 ≤ _
    nlinarith only [square,sourceBound]
  have selected : premiseClock definition ruleInstance goal children ≤ i*n^2+(18+8*p)*n := by
    unfold premiseClock; nlinarith only [instantiation,response,positive]
  have saved : retainedClock definition ruleInstance goal children ≤ i*n^2+(41+30*p)*n := by
    unfold retainedClock; nlinarith only [selected,premise,inputBound]
  have stripped : stripClock definition ruleInstance goal children premises ≤ (14*p+21)*n := by
    unfold stripClock; nlinarith only [retained,premise,goals,positive]
  have stripSaved : stripRetainedClock definition ruleInstance goal children premises ≤ (59*p+67)*n := by
    unfold stripRetainedClock; nlinarith only [stripped,retained,goals,positive]
  have preparedTime : preparedClock definition ruleInstance goal children premises ≤ i*n^2+(112+91*p)*n := by
    unfold preparedClock; nlinarith only [saved,retained,stripSaved,positive]
  have childrenTime : childrenClock definition ruleInstance goal children premises ≤ (89*p+198)*n := by
    unfold childrenClock; nlinarith only [prepared,childSize,positive]
  have body : payloadClock definition ruleInstance goal children premises ≤ i*n^2+(316+184*p)*n := by
    unfold payloadClock; nlinarith only [preparedTime,prepared,childrenTime,positive]
  have scaled := Nat.mul_le_mul_left (316+184*p) linear
  change _ ≤ (i+316+184*p)*n^2
  nlinarith only [body,scaled]

/-- The coefficient charges the actual rule-instantiation storage and both
guarded executions; the bound includes the complete refusal branch. -/
def coefficient (definition : CalculusLanguageDef) := RuleNodeAdmission.coefficient definition +
  RuleInstantiationExecution.coefficient definition + 400 * (RuleNodeAdmission.payloadCoefficient definition + 1)

theorem clock_polynomial (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :
    clock definition ruleInstance goal children ≤ coefficient definition.1 * ((inputWire ruleInstance goal children).length + 1)^2 := by
  have tested := tested_clock_bound definition.1 ruleInstance goal children
  have length : (testedWire definition ruleInstance goal children).length = (inputWire ruleInstance goal children).length + 1 := by
    simp [testedWire]
  have linear : (inputWire ruleInstance goal children).length + 1 ≤
      ((inputWire ruleInstance goal children).length + 1)^2 := le_self_pow (by omega) (by decide)
  have positive : 1 ≤ ((inputWire ruleInstance goal children).length + 1)^2 := le_trans (by omega) linear
  cases admitted : RuleNodeAdmission.result definition ruleInstance goal with
  | false =>
    simp only [clock,guardedClock,admitted,Bool.false_eq_true,↓reduceIte,length]
    unfold coefficient
    nlinarith
  | true =>
    cases instantiated : instantiateRule? definition ruleInstance with
    | none => simp [RuleNodeAdmission.result,instantiated] at admitted
    | some pair =>
      rcases pair with ⟨premises,conclusion⟩
      have same : conclusion = goal := by simpa [RuleNodeAdmission.result,instantiated] using admitted
      subst conclusion
      have payload := payload_clock_bound definition firstOrder ruleInstance goal children premises instantiated
      simp only [clock,guardedClock,admitted,↓reduceIte,instantiated,length]
      unfold coefficient
      nlinarith

noncomputable def polynomialOutputs (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (arity : Nat) (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :
    TM2OutputsInTime (machine definition.1 arity) (inputWire ruleInstance goal children)
      (some (resultWire definition arity ruleInstance goal children))
      (coefficient definition.1 * ((inputWire ruleInstance goal children).length + 1)^2) :=
  WordEqualityMachine.within (outputs definition firstOrder arity ruleInstance goal children)
    (clock_polynomial definition firstOrder ruleInstance goal children)

abbrev Input := RuleInstance × Pattern × List RawOpenProof
def encodeInput (input : Input) := inputWire input.1 input.2.1 input.2.2
def evaluate (definition : ValidatedCalculusLanguageDef) (arity : Nat) (input : Input) :=
  resultWire definition arity input.1 input.2.1 input.2.2
noncomputable def realization (definition : ValidatedCalculusLanguageDef) (firstOrder : FirstOrderCalculus definition.1)
    (arity : Nat) : TM2ComputableInPolyTime encodeInput id (evaluate definition arity) where
  tm := machine definition.1 arity
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl PairCell
  time := Polynomial.C (coefficient definition.1) * (Polynomial.X + Polynomial.C 1)^2
  outputsFun input := by
    change TM2OutputsInTime (machine definition.1 arity) ((encodeInput input).map id)
      (some ((evaluate definition arity input).map id)) _
    simp only [List.map_id,encodeInput,evaluate,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X]
    exact polynomialOutputs definition firstOrder arity input.1 input.2.1 input.2.2

namespace Controls
open Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayPresentation

theorem nullary_jobs : OriginalChildJobs.readOutput
    (resultWire mpValidated 0 ⟨⟨"a"⟩, []⟩ (judgmentP formulaA) []) = some [] := by
  rw [result_readout]
  simp [RuleInstantiationExecution.Controls.nullary_rule]

theorem ordered_jobs : OriginalChildJobs.readOutput
    (resultWire mpValidated 2 ⟨⟨"m"⟩, [formulaA,formulaB]⟩ (judgmentP formulaB)
      [.premise 7,.premise 3]) = some
        [(judgmentP formulaA,.premise 7),(judgmentP (implication formulaA formulaB),.premise 3)] := by
  rw [result_readout]
  simp [RuleInstantiationExecution.Controls.ordered_modus_ponens]

theorem repeated_children_preserved : OriginalChildJobs.readOutput
    (resultWire mpValidated 2 ⟨⟨"m"⟩, [formulaA,formulaB]⟩ (judgmentP formulaB)
      [.premise 4,.premise 4]) = some
        [(judgmentP formulaA,.premise 4),(judgmentP (implication formulaA formulaB),.premise 4)] := by
  rw [result_readout]
  simp [RuleInstantiationExecution.Controls.ordered_modus_ponens]

theorem changed_goal_refused : resultWire mpValidated 0 ⟨⟨"a"⟩, []⟩ (judgmentP formulaB) [] = [.inr false] := by
  simp [resultWire,RuleNodeAdmission.Controls.changed_nullary_goal]

theorem missing_child_refused : OriginalChildJobs.readOutput
    (resultWire mpValidated 2 ⟨⟨"m"⟩, [formulaA,formulaB]⟩ (judgmentP formulaB) [.premise 7]) = none := by
  rw [result_readout]
  simp [RuleInstantiationExecution.Controls.ordered_modus_ponens]

theorem extra_nullary_child_refused : OriginalChildJobs.readOutput
    (resultWire mpValidated 0 ⟨⟨"a"⟩, []⟩ (judgmentP formulaA) [.premise 0]) = none := by
  rw [result_readout]
  simp [RuleInstantiationExecution.Controls.nullary_rule]

theorem absent_row_refused : resultWire mpValidated 0 ⟨⟨"absent"⟩, []⟩ (judgmentP formulaA) [] = [.inr false] := by
  simp [resultWire,RuleNodeAdmission.Controls.unknown_rule_refused]

theorem escaping_argument_refused : resultWire FirstOrder.InferenceTranslation.Controls.dataCalculus 0
    ⟨⟨"data"⟩, [.lambda none (.bvar 1)]⟩ (judgmentP (.lambda none (.bvar 1))) [] = [.inr false] := by
  simp [resultWire,RuleNodeAdmission.Controls.escaping_argument_refused]
end Controls

end Mettapedia.Languages.HOLLight.NodeChildrenExecution

