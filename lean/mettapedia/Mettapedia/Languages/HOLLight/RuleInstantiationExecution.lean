import Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation
import Mettapedia.Languages.HOLLight.InferenceCompiler

/-!
# Executed local source-rule instantiation for the direct HOL compiler

The physical source rule-instance packet is retained while the original
rule lookup, arity and argument-scope checks run. Only an admitted packet
reaches the existing authored-schema machine. The resulting ordered premises
and conclusion are the original source instantiation, including repetitions.

The finite authored calculus is compiled into control and literal template
data. It is fixed for an invocation family. Its complete template budget
appears in the polynomial coefficient. The input domain contains every original
rule-instance codec image; arbitrary byte admission is a separate operation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.RuleInstantiationExecution
open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.ScopedApplication
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
abbrev Alphabet := Binary.Alphabet

def inputWire (ruleInstance : RuleInstance) := encodeWith CertificateDataEncoding.instanceCodec ruleInstance
def project : Alphabet ⊕ Bool → List Alphabet
  | .inl symbol => [symbol]
  | .inr accepted => [if accepted then 1 else 0]
def testedWire (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :=
  (if scopeResult definition ruleInstance then (1 : Alphabet) else 0) :: inputWire ruleInstance

theorem saved_project (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    (savedOutput definition ruleInstance).flatMap project = testedWire definition ruleInstance := by
  simp only [savedOutput, project, List.flatMap_cons, List.singleton_append, List.flatMap_map, testedWire]
  simp only [List.flatMap_singleton', inputWire]

local instance (definition : CalculusLanguageDef) : Fintype
    ((savedMachine definition).Γ (savedMachine definition).k₁) := inferInstanceAs (Fintype (Alphabet ⊕ Bool))
local instance (definition : CalculusLanguageDef) : Inhabited
    ((savedMachine definition).Γ (savedMachine definition).k₁) := inferInstanceAs (Inhabited (Alphabet ⊕ Bool))
def testedMachine (definition : CalculusLanguageDef) : FinTM2 :=
  StackMachineComposition.machine (savedMachine definition) (WordHomomorphismMachine.machine project)
    (Equiv.refl (Alphabet ⊕ Bool))

noncomputable def testedOutputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (testedMachine definition) (inputWire ruleInstance)
      (some (testedWire definition ruleInstance)) (20140 * ((inputWire ruleInstance).length + 1)^2) := by
  have projected := WordHomomorphismMachine.outputs project (savedOutput definition ruleInstance)
  rw [saved_project] at projected
  have joined := StackMachineComposition.outputs (savedMachine definition) (WordHomomorphismMachine.machine project)
    (Equiv.refl (Alphabet ⊕ Bool)) (inputWire ruleInstance) (savedOutput definition ruleInstance)
    (testedWire definition ruleInstance) _ _ (savedOutputs definition ruleInstance) (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine project)
        ((savedOutput definition ruleInstance).map id) _ _
      simpa only [List.map_id] using projected)
  apply WordEqualityMachine.within joined
  have linear : (inputWire ruleInstance).length + 1 ≤ ((inputWire ruleInstance).length + 1)^2 :=
    le_self_pow (by omega) (by decide)
  simp only [savedOutput, testedWire, List.length_cons, List.length_map, inputWire] at *
  nlinarith

local instance (definition : CalculusLanguageDef) : Inhabited
    ((CertificateSchemaInstantiation.Authored.machine definition).Γ
      (CertificateSchemaInstantiation.Authored.machine definition).k₀) := inferInstanceAs (Inhabited Alphabet)
local instance (definition : CalculusLanguageDef) : Fintype
    ((CertificateSchemaInstantiation.Authored.machine definition).Γ
      (CertificateSchemaInstantiation.Authored.machine definition).k₁) := inferInstanceAs (Fintype Alphabet)
local instance (definition : CalculusLanguageDef) : Inhabited
    ((CertificateSchemaInstantiation.Authored.machine definition).Γ
      (CertificateSchemaInstantiation.Authored.machine definition).k₁) := inferInstanceAs (Inhabited Alphabet)
def accept (symbol : Alphabet) := symbol == 1
def guardedMachine (definition : CalculusLanguageDef) : FinTM2 :=
  StackMachineComposition.Dispatch.machine (CertificateSchemaInstantiation.Authored.machine definition) accept [(0 : Alphabet)]
def guardedOutput (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :=
  if scopeResult definition ruleInstance then CertificateSchemaInstantiation.Authored.output definition ruleInstance else [0]
def coefficient (definition : CalculusLanguageDef) := 55 * CertificateSchemaInstantiation.Authored.planBudget definition + 21000

noncomputable def guardedOutputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (guardedMachine definition) (testedWire definition ruleInstance)
      (some (guardedOutput definition ruleInstance))
      ((55 * CertificateSchemaInstantiation.Authored.planBudget definition + 50) * ((inputWire ruleInstance).length + 1)) := by
  cases admitted : scopeResult definition ruleInstance with
  | false =>
    have refused := StackMachineComposition.Dispatch.outputs_refused
      (CertificateSchemaInstantiation.Authored.machine definition) accept [(0 : Alphabet)]
      (0 : Alphabet) (inputWire ruleInstance) (by decide)
    have run : TM2OutputsInTime (guardedMachine definition) (testedWire definition ruleInstance)
        (some (guardedOutput definition ruleInstance)) ((inputWire ruleInstance).length + 2) := by
      simpa only [guardedMachine, testedWire, guardedOutput, admitted,
        Bool.false_eq_true, ↓reduceIte] using refused
    apply WordEqualityMachine.within run
    nlinarith
  | true =>
    have executed := StackMachineComposition.Dispatch.outputs_success
      (CertificateSchemaInstantiation.Authored.machine definition) accept [(0 : Alphabet)]
      (1 : Alphabet) (inputWire ruleInstance) (CertificateSchemaInstantiation.Authored.output definition ruleInstance)
      _ (by decide) (CertificateSchemaInstantiation.Authored.outputs definition ruleInstance)
    have run : TM2OutputsInTime (guardedMachine definition) (testedWire definition ruleInstance)
        (some (guardedOutput definition ruleInstance))
        ((55 * CertificateSchemaInstantiation.Authored.planBudget definition + 40) * ((inputWire ruleInstance).length + 1) + 1) := by
      simpa only [guardedMachine, testedWire, guardedOutput, admitted,
        ↓reduceIte, inputWire] using executed
    apply WordEqualityMachine.within run
    simp only [inputWire]
    nlinarith

local instance (definition : CalculusLanguageDef) : Fintype
    ((testedMachine definition).Γ (testedMachine definition).k₁) := inferInstanceAs (Fintype Alphabet)
local instance (definition : CalculusLanguageDef) : Inhabited
    ((testedMachine definition).Γ (testedMachine definition).k₁) := inferInstanceAs (Inhabited Alphabet)
def machine (definition : CalculusLanguageDef) := StackMachineComposition.machine
  (testedMachine definition) (guardedMachine definition) (Equiv.refl Alphabet)

attribute [local implicit_reducible] machine testedMachine guardedMachine
  StackMachineComposition.machine StackMachineComposition.Dispatch.machine

noncomputable def guardedWholeOutputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (machine definition) (inputWire ruleInstance) (some (guardedOutput definition ruleInstance))
      (coefficient definition * ((inputWire ruleInstance).length + 1)^2) := by
  have joined := StackMachineComposition.outputs (testedMachine definition) (guardedMachine definition)
    (Equiv.refl Alphabet) (inputWire ruleInstance) (testedWire definition ruleInstance)
    (guardedOutput definition ruleInstance) _ _ (testedOutputs definition ruleInstance) (by
      change TM2OutputsInTime (guardedMachine definition) ((testedWire definition ruleInstance).map id) _ _
      simpa only [List.map_id] using guardedOutputs definition ruleInstance)
  apply WordEqualityMachine.within joined
  have linear : (inputWire ruleInstance).length + 1 ≤ ((inputWire ruleInstance).length + 1)^2 :=
    le_self_pow (by omega) (by decide)
  simp only [testedWire, List.length_cons]
  unfold coefficient
  nlinarith

theorem zero_depth {definition : CalculusLanguageDef} (firstOrder : FirstOrderCalculus definition) :
    ∀ index : Fin definition.rules.length,
      ∀ formal ∈ (CertificateRuleAdmission.row definition index).metavariables, formal.2 = 0 := by
  intro index
  exact firstOrder.arities _ (List.getElem_mem index.isLt)

/-- The physical gate discharges the original scope and arity obligations.
First-order schema admissibility and absent side conditions come from the
authored calculus, not from a per-instance correctness callback. -/
theorem guardedOutput_eq (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (ruleInstance : RuleInstance) :
    guardedOutput definition.1 ruleInstance = CertificateArgumentFraming.Execution.resultWire
      ((instantiateRule? definition ruleInstance).map (encodeWith CertificateSchemaInstantiation.fieldsCodec)) := by
  cases admitted : scopeResult definition.1 ruleInstance with
  | false =>
    have missing : instantiateRule? definition ruleInstance = none := by
      cases instantiated : instantiateRule? definition ruleInstance with
      | none => rfl
      | some fields =>
        have admitted' := scopeResult_of_application (zero_depth firstOrder) instantiated
        simp [admitted] at admitted'
    simp [guardedOutput, admitted, missing, CertificateArgumentFraming.Execution.resultWire]
  | true =>
    obtain ⟨rule, lookup, arguments⟩ := (scopeResult_iff definition.1 (zero_depth firstOrder) ruleInstance).mp admitted
    have member : rule ∈ definition.1.rules := List.mem_of_find?_eq_some
      (by simpa only [CalculusLanguageDef.lookupRule?] using lookup)
    have formals := FirstOrder.InferenceTranslation.inferenceRule_formals (firstOrder.arities rule member)
    have converted : FirstOrder.InferenceTranslation.inferenceRule rule ∈
        FirstOrder.InferenceTranslation.inferenceRules definition.1 := List.mem_map.mpr ⟨rule, member, rfl⟩
    have package := FirstOrder.InferenceTranslation.inferenceRules_package firstOrder
    have premiseFragment := package.premisesFragment _ converted
    have conclusionFragment := package.conclusionFragment _ converted
    rw [formals] at premiseFragment conclusionFragment
    have fields : rule.metavariables = (rule.metavariables.map Prod.fst).map (fun name => (name, 0)) := formals.symm
    have conditions : RuleSchema.sideConditionsHold rule ruleInstance.arguments = true := by
      simp [RuleSchema.sideConditionsHold, firstOrder.noSideConditions rule member]
    simpa only [guardedOutput, admitted, ↓reduceIte] using CertificateSchemaInstantiation.Authored.output_of_rule
      lookup fields premiseFragment conclusionFragment (firstOrder.distinctNames rule member) arguments conditions

def output (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance) :=
  CertificateArgumentFraming.Execution.resultWire
    ((instantiateRule? definition ruleInstance).map (encodeWith CertificateSchemaInstantiation.fieldsCodec))

/-- One finite machine executes exact original local instantiation on every
rule-instance codec image, including missing rules and invalid arguments. -/
noncomputable def outputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (ruleInstance : RuleInstance) :
    TM2OutputsInTime (machine definition.1) (inputWire ruleInstance) (some (output definition ruleInstance))
      (coefficient definition.1 * ((inputWire ruleInstance).length + 1)^2) := by
  dsimp only [output]
  rw [← guardedOutput_eq definition firstOrder ruleInstance]
  exact guardedWholeOutputs definition.1 ruleInstance

def encodeOutput (value : Option (List Pattern × Pattern)) :=
  CertificateArgumentFraming.Execution.resultWire (value.map (encodeWith CertificateSchemaInstantiation.fieldsCodec))

noncomputable def realization (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) :
    TM2ComputableInPolyTime inputWire encodeOutput (instantiateRule? definition) where
  tm := machine definition.1
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := Polynomial.C (coefficient definition.1) * (Polynomial.X + Polynomial.C 1)^2
  outputsFun ruleInstance := by
    change TM2OutputsInTime (machine definition.1) ((inputWire ruleInstance).map id)
      (some ((encodeOutput (instantiateRule? definition ruleInstance)).map id)) _
    simp only [List.map_id, encodeOutput, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
    exact outputs definition firstOrder ruleInstance

def readOutput : List Alphabet → Option (Option (List Pattern × Pattern))
  | [0] => some none
  | 1 :: payload => (decodeWith CertificateSchemaInstantiation.fieldsCodec payload).map some
  | _ => none

theorem readOutput_encodeOutput (value : Option (List Pattern × Pattern)) :
    readOutput (encodeOutput value) = some value := by
  cases value with
  | none => rfl
  | some fields =>
    change (decodeWith CertificateSchemaInstantiation.fieldsCodec
      (encodeWith CertificateSchemaInstantiation.fieldsCodec fields)).map some = some (some fields)
    rw [decodeWith_encodeWith]
    rfl

theorem run_readout (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (ruleInstance : RuleInstance)
    {word : List Alphabet} (finished : TM2Outputs (machine definition.1) (inputWire ruleInstance) (some word)) :
    word = encodeOutput (instantiateRule? definition ruleInstance) :=
  StackMachineComposition.outputs_unique finished (outputs definition firstOrder ruleInstance).toEvalsTo

theorem run_decodes (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (ruleInstance : RuleInstance)
    {word : List Alphabet} (finished : TM2Outputs (machine definition.1) (inputWire ruleInstance) (some word)) :
    readOutput word = some (instantiateRule? definition ruleInstance) := by
  rw [run_readout definition firstOrder ruleInstance finished, readOutput_encodeOutput]

/-- A successful actual run produces exactly a declarative source rule
application, with its complete ordered premises and original conclusion. -/
theorem run_source_application (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (ruleInstance : RuleInstance)
    (premises : List Pattern) (conclusion : Pattern)
    {word : List Alphabet} (finished : TM2Outputs (machine definition.1) (inputWire ruleInstance) (some word))
    (decoded : readOutput word = some (some (premises, conclusion))) :
    RuleApplication definition ruleInstance premises conclusion := by
  have exactResult := run_decodes definition firstOrder ruleInstance finished
  have same := Option.some.inj (exactResult.symm.trans decoded)
  exact instantiateRule?_eq_some_iff_application.mp same

theorem run_refusal_iff (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (ruleInstance : RuleInstance)
    {word : List Alphabet} (finished : TM2Outputs (machine definition.1) (inputWire ruleInstance) (some word)) :
    readOutput word = some none ↔ instantiateRule? definition ruleInstance = none := by
  rw [run_decodes definition firstOrder ruleInstance finished, Option.some.injEq]

namespace Controls
open Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayPresentation

theorem nullary_rule : instantiateRule? mpValidated ⟨⟨"a"⟩, []⟩ = some ([], judgmentP formulaA) := by
  decide +kernel
theorem ordered_modus_ponens : instantiateRule? mpValidated ⟨⟨"m"⟩, [formulaA, formulaB]⟩ =
    some ([judgmentP formulaA, judgmentP (implication formulaA formulaB)], judgmentP formulaB) := by
  decide +kernel
theorem repeated_arguments : instantiateRule? mpValidated ⟨⟨"m"⟩, [formulaA, formulaA]⟩ =
    some ([judgmentP formulaA, judgmentP (implication formulaA formulaA)], judgmentP formulaA) := by
  decide +kernel
theorem opaque_binder_argument :
    instantiateRule? FirstOrder.InferenceTranslation.Controls.dataCalculus ⟨⟨"data"⟩, [.lambda none (.bvar 0)]⟩ =
      some ([], judgmentP (.lambda none (.bvar 0))) := by decide +kernel
theorem absent_rule_refused : instantiateRule? mpValidated ⟨⟨"absent"⟩, []⟩ = none := by decide +kernel
theorem missing_argument_refused : instantiateRule? mpValidated ⟨⟨"m"⟩, [formulaA]⟩ = none := by decide +kernel
theorem excess_argument_refused : instantiateRule? mpValidated ⟨⟨"a"⟩, [formulaA]⟩ = none := by decide +kernel
theorem escaping_argument_refused :
    instantiateRule? FirstOrder.InferenceTranslation.Controls.dataCalculus ⟨⟨"data"⟩, [.lambda none (.bvar 1)]⟩ = none :=
  by decide +kernel
theorem named_binder_refused :
    instantiateRule? FirstOrder.InferenceTranslation.Controls.dataCalculus ⟨⟨"data"⟩, [.lambda (some "x") (.bvar 0)]⟩ = none :=
  by decide +kernel
end Controls

end Mettapedia.Languages.HOLLight.RuleInstantiationExecution
