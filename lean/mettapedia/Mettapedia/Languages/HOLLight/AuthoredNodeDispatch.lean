import Mettapedia.Languages.HOLLight.NodeChildrenExecution
import Mettapedia.Languages.HOLLight.RuleNodeAdmission
import Mettapedia.Computability.CommonArenaDispatch

/-!
# Executed authored-row dispatch on a complete original node packet

The original instance field executes the original rule-name dictionary.
The selected row tag precedes every byte of the retained original instance,
requested goal and submitted child list. Row selection preserves the first
matching authored occurrence, including duplicate names.

For the finite compiled calculus, each selected row executes the original
node machine at that row's premise count. Source rule admission, requested
goal comparison and computed premises retain their original guards. The
quadratic bound includes row lookup, packet retention, physical handoffs and
refusal cleanup. The resulting jobs feed subsequent child-proof validation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.AuthoredNodeDispatch
open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

abbrev Alphabet := Binary.Alphabet
abbrev Row (definition : CalculusLanguageDef) := Fin definition.rules.length

def premiseArity (definition : CalculusLanguageDef) (index : Row definition) : Nat :=
  (CertificateRuleAdmission.row definition index).premises.length

/-- The original successful application fixes the actual authored premise
count. Argument arity and premise arity are distinct source quantities. -/
theorem instantiated_premise_count {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    (accepted : instantiateRule? definition ruleInstance = some (premises, conclusion)) :
    ∃ index : Row definition.1,
      CertificateRuleAdmission.selected definition.1 ruleInstance = some index ∧
      premiseArity definition.1 index = premises.length := by
  obtain ⟨rule, lookup, _, _, instantiated, _⟩ :=
    instantiateRule?_eq_some_iff_application.mp accepted
  have selected := CertificateRuleAdmission.selected_lookup definition.1 ruleInstance
  cases found : CertificateRuleAdmission.selected definition.1 ruleInstance with
  | none => simp only [found, Option.map_none, lookup] at selected; cases selected
  | some index =>
    have same : CertificateRuleAdmission.row definition.1 index = rule := by
      simpa only [found, Option.map_some, lookup, Option.some.injEq] using selected
    refine ⟨index, rfl, ?_⟩
    rw [premiseArity, same]
    exact InstantiatesListAt.length_eq instantiated

theorem selected_premise_count {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    {index : Row definition.1}
    (selected : CertificateRuleAdmission.selected definition.1 ruleInstance = some index)
    (accepted : instantiateRule? definition ruleInstance = some (premises, conclusion)) :
    premiseArity definition.1 index = premises.length := by
  obtain ⟨actual, found, counted⟩ := instantiated_premise_count accepted
  have same : actual = index := Option.some.inj (found.symm.trans selected)
  simpa only [same] using counted

theorem absent_row_refuses {definition : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance}
    (missing : CertificateRuleAdmission.selected definition.1 ruleInstance = none) :
    instantiateRule? definition ruleInstance = none := by
  have absent : definition.1.lookupRule? ruleInstance.ruleId = none := by
    rw [← CertificateRuleAdmission.selected_lookup, missing]
    rfl
  simp only [instantiateRule?, absent]

namespace Selection

def fields (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) : Fin 3 → List Alphabet :=
  ![RuleInstantiationExecution.inputWire ruleInstance, RuleNodeAdmission.goalWire goal,
    encodeWith (Codec.list CertificateDataEncoding.proofCodec) children]

def inputWire (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :=
  Indexed.argumentWire (fields ruleInstance goal children)

def instanceSelector : Indexed.Template Alphabet 3 := [.inr 0]

attribute [local implicit_reducible] Indexed.machine StackMachineComposition.machine
  CertificateRuleAdmission.machine RetainedWordExecution.machine

local instance : Fintype ((Indexed.machine instanceSelector).Γ (Indexed.machine instanceSelector).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((Indexed.machine instanceSelector).Γ (Indexed.machine instanceSelector).k₁) :=
  inferInstanceAs (Inhabited Alphabet)

def selectedMachine (definition : CalculusLanguageDef) := StackMachineComposition.machine
  (Indexed.machine instanceSelector) (CertificateRuleAdmission.machine definition) (Equiv.refl Alphabet)

attribute [local implicit_reducible] selectedMachine
local instance (definition : CalculusLanguageDef) : Fintype ((selectedMachine definition).Γ (selectedMachine definition).k₁) :=
  inferInstanceAs (Fintype (Alphabet ⊕ Option (Row definition)))
local instance (definition : CalculusLanguageDef) : Inhabited ((selectedMachine definition).Γ (selectedMachine definition).k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def machine (definition : CalculusLanguageDef) := RetainedWordExecution.machine
  (selectedMachine definition) (CertificateRuleAdmission.ScopedApplication.readSelected definition)

def output (definition : CalculusLanguageDef) (ruleInstance : RuleInstance) (goal : Pattern)
    (children : List RawOpenProof) : List (Option Alphabet ⊕ Option (Row definition)) :=
  .inr (CertificateRuleAdmission.selected definition ruleInstance) ::
    (inputWire ruleInstance goal children).map Sum.inl

def selectionClock (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :=
  8 * ((inputWire ruleInstance goal children).length + 1) +
    14 * (RuleInstantiationExecution.inputWire ruleInstance).length + 17

def clock (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :=
  selectionClock ruleInstance goal children + 3 * (inputWire ruleInstance goal children).length +
    (RuleInstantiationExecution.inputWire ruleInstance).length + 5

noncomputable def selectedOutputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance)
    (goal : Pattern) (children : List RawOpenProof) :
    TM2OutputsInTime (selectedMachine definition) (inputWire ruleInstance goal children)
      (some (CertificateRuleAdmission.output definition ruleInstance)) (selectionClock ruleInstance goal children) := by
  have selected := Indexed.outputs instanceSelector (fields ruleInstance goal children)
  have same : Indexed.instantiate instanceSelector (fields ruleInstance goal children) =
      RuleInstantiationExecution.inputWire ruleInstance := by
    simp [instanceSelector, fields, Indexed.instantiate]
  rw [same] at selected
  have ran := StackMachineComposition.outputs (Indexed.machine instanceSelector)
    (CertificateRuleAdmission.machine definition) (Equiv.refl Alphabet)
    (inputWire ruleInstance goal children) (RuleInstantiationExecution.inputWire ruleInstance)
    (CertificateRuleAdmission.output definition ruleInstance) _ _ selected (by
      change TM2OutputsInTime (CertificateRuleAdmission.machine definition)
        ((RuleInstantiationExecution.inputWire ruleInstance).map id) _ _
      simpa only [List.map_id, RuleInstantiationExecution.inputWire] using
        CertificateRuleAdmission.outputs definition ruleInstance)
  apply WordEqualityMachine.within ran
  simp only [selectionClock, instanceSelector, List.length_cons, List.length_nil,
    RuleInstantiationExecution.inputWire, inputWire]
  omega

noncomputable def outputs (definition : CalculusLanguageDef) (ruleInstance : RuleInstance)
    (goal : Pattern) (children : List RawOpenProof) :
    TM2OutputsInTime (machine definition) (inputWire ruleInstance goal children)
      (some (output definition ruleInstance goal children)) (clock ruleInstance goal children) := by
  have retained := RetainedWordExecution.outputs (selectedMachine definition)
    (CertificateRuleAdmission.ScopedApplication.readSelected definition)
    (inputWire ruleInstance goal children) (.inr (CertificateRuleAdmission.selected definition ruleInstance))
    ((RuleInstantiationExecution.inputWire ruleInstance).map Sum.inl)
    (selectionClock ruleInstance goal children) (selectedOutputs definition ruleInstance goal children)
  simpa only [machine, output, CertificateRuleAdmission.ScopedApplication.readSelected,
    clock, List.length_map] using retained

theorem output_length (definition : CalculusLanguageDef) (ruleInstance : RuleInstance)
    (goal : Pattern) (children : List RawOpenProof) :
    (output definition ruleInstance goal children).length = (inputWire ruleInstance goal children).length + 1 := by
  simp [output]

theorem input_length (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :
    (inputWire ruleInstance goal children).length =
      (RuleInstantiationExecution.inputWire ruleInstance).length +
      (RuleNodeAdmission.goalWire goal).length +
      (encodeWith (Codec.list CertificateDataEncoding.proofCodec) children).length + 3 := by
  simp [inputWire, fields, Indexed.argumentWire, Indexed.frame, List.finRange_succ]
  omega

theorem clock_linear (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :
    clock ruleInstance goal children ≤ 26 * (inputWire ruleInstance goal children).length + 30 := by
  have size := input_length ruleInstance goal children
  unfold clock selectionClock
  omega

end Selection
end Mettapedia.Languages.HOLLight.AuthoredNodeDispatch

namespace Mettapedia.Languages.HOLLight.AuthoredNodeDispatch
open Turing Polynomial
open Mettapedia.Computability
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.MM0.Translation.CalculusSimulation

abbrev Base (definition : CalculusLanguageDef) := NodeChildrenExecution.machine definition 0
abbrev PairCell := OriginalChildJobs.PairCell

theorem input_exact (ruleInstance : RuleInstance) (goal : Pattern) (children : List RawOpenProof) :
    Selection.inputWire ruleInstance goal children =
      NodeChildrenExecution.inputWire ruleInstance goal children := rfl

theorem familyCellTypes (definition : CalculusLanguageDef) (index : Row definition) (key : (Base definition).K) :
    (NodeChildrenExecution.machine definition (premiseArity definition index)).Γ key =
      (Base definition).Γ key := rfl

def family (definition : CalculusLanguageDef) : CommonArenaDispatch.Family (Base definition) (Row definition) where
  alphabet index := (NodeChildrenExecution.machine definition (premiseArity definition index)).Γ
  cellTypes := familyCellTypes definition
  Label index := (NodeChildrenExecution.machine definition (premiseArity definition index)).Λ
  labelFinite index := (NodeChildrenExecution.machine definition (premiseArity definition index)).ΛFin
  main index := (NodeChildrenExecution.machine definition (premiseArity definition index)).main
  body index := (NodeChildrenExecution.machine definition (premiseArity definition index)).m

local instance (definition : CalculusLanguageDef) : Inhabited ((Base definition).Γ (Base definition).k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def dispatcher (definition : CalculusLanguageDef) := CommonArenaDispatch.machine
  (Base definition) (family definition) (none : Option Alphabet) (Sum.inr false : PairCell)

attribute [local implicit_reducible] dispatcher Selection.machine RetainedWordExecution.machine
  StackMachineComposition.machine NodeChildrenExecution.machine

local instance (definition : CalculusLanguageDef) : Fintype ((Selection.machine definition).Γ (Selection.machine definition).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet ⊕ Option (Row definition)))
local instance (definition : CalculusLanguageDef) : Inhabited ((Selection.machine definition).Γ (Selection.machine definition).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet ⊕ Option (Row definition)))

def machine (definition : CalculusLanguageDef) := StackMachineComposition.machine
  (Selection.machine definition) (dispatcher definition) (Equiv.refl (Option Alphabet ⊕ Option (Row definition)))

def resultWire (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance)
    (goal : Pattern) (children : List RawOpenProof) : List PairCell :=
  match CertificateRuleAdmission.selected definition.1 ruleInstance with
  | none => [Sum.inr false]
  | some index => NodeChildrenExecution.resultWire definition (premiseArity definition.1 index)
      ruleInstance goal children

def clock (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance)
    (goal : Pattern) (children : List RawOpenProof) :=
  Selection.clock ruleInstance goal children +
    4 * (Selection.inputWire ruleInstance goal children).length +
    NodeChildrenExecution.clock definition ruleInstance goal children + 8

noncomputable def dispatchedOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (ruleInstance : RuleInstance)
    (goal : Pattern) (children : List RawOpenProof) :
    TM2OutputsInTime (dispatcher definition.1) (Selection.output definition.1 ruleInstance goal children)
      (some (resultWire definition ruleInstance goal children))
      (2 * (Selection.inputWire ruleInstance goal children).length +
        NodeChildrenExecution.clock definition ruleInstance goal children + 4) := by
  cases chosen : CertificateRuleAdmission.selected definition.1 ruleInstance with
  | none =>
    have refused := CommonArenaDispatch.outputs_absent (Base definition.1) (family definition.1)
      (none : Option Alphabet) (Sum.inr false : PairCell)
      (Selection.inputWire ruleInstance goal children)
    have ran : TM2OutputsInTime (dispatcher definition.1)
        (Selection.output definition.1 ruleInstance goal children)
        (some (resultWire definition ruleInstance goal children))
        ((Selection.inputWire ruleInstance goal children).length + 3) := by
      simpa only [Selection.output, chosen, resultWire, dispatcher] using refused
    exact WordEqualityMachine.within ran (by omega)
  | some index =>
    have source := NodeChildrenExecution.outputs definition firstOrder (premiseArity definition.1 index)
      ruleInstance goal children
    have executed : TM2OutputsInTime ((family definition.1).toMachine index)
        ((Selection.inputWire ruleInstance goal children).map
          (CommonArenaDispatch.cellTypes (Base definition.1) (family definition.1) index (Base definition.1).k₀).mpr)
        (some ((NodeChildrenExecution.resultWire definition (premiseArity definition.1 index)
          ruleInstance goal children).map
          (CommonArenaDispatch.cellTypes (Base definition.1) (family definition.1) index (Base definition.1).k₁).mpr))
        (NodeChildrenExecution.clock definition ruleInstance goal children) := by
      change TM2OutputsInTime (NodeChildrenExecution.machine definition.1 (premiseArity definition.1 index))
        ((Selection.inputWire ruleInstance goal children).map id)
        (some ((NodeChildrenExecution.resultWire definition (premiseArity definition.1 index)
          ruleInstance goal children).map id)) _
      simpa only [List.map_id, input_exact] using source
    have joined := CommonArenaDispatch.outputs_selected (Base definition.1) (family definition.1)
      (none : Option Alphabet) (Sum.inr false : PairCell) index
      (Selection.inputWire ruleInstance goal children)
      (NodeChildrenExecution.resultWire definition (premiseArity definition.1 index) ruleInstance goal children)
      _ executed
    simpa only [Selection.output, resultWire, chosen, dispatcher] using joined

noncomputable def outputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (ruleInstance : RuleInstance)
    (goal : Pattern) (children : List RawOpenProof) :
    TM2OutputsInTime (machine definition.1) (Selection.inputWire ruleInstance goal children)
      (some (resultWire definition ruleInstance goal children)) (clock definition ruleInstance goal children) := by
  have joined := StackMachineComposition.outputs (Selection.machine definition.1) (dispatcher definition.1)
    (Equiv.refl (Option Alphabet ⊕ Option (Row definition.1)))
    (Selection.inputWire ruleInstance goal children) (Selection.output definition.1 ruleInstance goal children)
    (resultWire definition ruleInstance goal children) _ _ (Selection.outputs definition.1 ruleInstance goal children) (by
      change TM2OutputsInTime (dispatcher definition.1) ((Selection.output definition.1 ruleInstance goal children).map id) _ _
      simpa only [List.map_id] using dispatchedOutputs definition firstOrder ruleInstance goal children)
  apply WordEqualityMachine.within joined
  rw [Selection.output_length]
  unfold clock
  omega

theorem result_readout (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance)
    (goal : Pattern) (children : List RawOpenProof) :
    OriginalChildJobs.readOutput (resultWire definition ruleInstance goal children) =
      match instantiateRule? definition ruleInstance with
      | none => none
      | some result => if result.2 = goal ∧ children.length = result.1.length
          then some (result.1.zip children) else none := by
  cases chosen : CertificateRuleAdmission.selected definition.1 ruleInstance with
  | none =>
    have absent := absent_row_refuses chosen
    simp only [resultWire, chosen, absent, OriginalChildJobs.readOutput,
      FramedWordPairing.readOutput_refused, bind, Option.bind]
  | some index =>
    simp only [resultWire, chosen]
    rw [NodeChildrenExecution.result_readout]
    cases instantiated : instantiateRule? definition ruleInstance with
    | none => rfl
    | some pair =>
      rcases pair with ⟨premises, conclusion⟩
      have count := selected_premise_count chosen instantiated
      simp only [count, true_and]

theorem run_readout (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (ruleInstance : RuleInstance)
    (goal : Pattern) (children : List RawOpenProof) {word : List PairCell}
    (finished : TM2Outputs (machine definition.1) (Selection.inputWire ruleInstance goal children) (some word)) :
    word = resultWire definition ruleInstance goal children :=
  StackMachineComposition.outputs_unique finished (outputs definition firstOrder ruleInstance goal children).toEvalsTo

theorem result_success (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance)
    (goal : Pattern) (children : List RawOpenProof) (premises : List Pattern)
    (applied : RuleApplication definition ruleInstance premises goal)
    (childCount : children.length = premises.length) :
    OriginalChildJobs.readOutput (resultWire definition ruleInstance goal children) =
      some (premises.zip children) := by
  have instantiated := instantiateRule?_eq_some_iff_application.mpr applied
  rw [result_readout, instantiated]
  simp only [childCount, and_self, ↓reduceIte]

theorem wrong_child_count_refuses (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance)
    (goal : Pattern) (children : List RawOpenProof) (premises : List Pattern) (conclusion : Pattern)
    (instantiated : instantiateRule? definition ruleInstance = some (premises, conclusion))
    (wrong : children.length ≠ premises.length) :
    OriginalChildJobs.readOutput (resultWire definition ruleInstance goal children) = none := by
  rw [result_readout, instantiated]
  simp only [wrong, and_false, ↓reduceIte]

theorem wrong_goal_refuses (definition : ValidatedCalculusLanguageDef) (ruleInstance : RuleInstance)
    (goal : Pattern) (children : List RawOpenProof) (premises : List Pattern) (conclusion : Pattern)
    (instantiated : instantiateRule? definition ruleInstance = some (premises, conclusion))
    (wrong : conclusion ≠ goal) :
    OriginalChildJobs.readOutput (resultWire definition ruleInstance goal children) = none := by
  rw [result_readout, instantiated]
  simp only [wrong, false_and, ↓reduceIte]

theorem run_source_application (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (ruleInstance : RuleInstance)
    (goal : Pattern) (children : List RawOpenProof) {word : List PairCell}
    {jobs : List (Pattern × RawOpenProof)}
    (finished : TM2Outputs (machine definition.1) (Selection.inputWire ruleInstance goal children) (some word))
    (decoded : OriginalChildJobs.readOutput word = some jobs) :
    ∃ premises, RuleApplication definition ruleInstance premises goal ∧
      children.length = premises.length ∧ jobs = premises.zip children := by
  rw [run_readout definition firstOrder ruleInstance goal children finished, result_readout] at decoded
  cases instantiated : instantiateRule? definition ruleInstance with
  | none => simp [instantiated] at decoded
  | some pair =>
    rcases pair with ⟨premises, conclusion⟩
    simp only [instantiated] at decoded
    split at decoded
    · rename_i admitted
      rcases admitted with ⟨rfl, childCount⟩
      exact ⟨premises, instantiateRule?_eq_some_iff_application.mp instantiated,
        childCount, (Option.some.inj decoded).symm⟩
    · cases decoded

def coefficient (definition : CalculusLanguageDef) := NodeChildrenExecution.coefficient definition + 38

theorem clock_polynomial (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (ruleInstance : RuleInstance)
    (goal : Pattern) (children : List RawOpenProof) :
    clock definition ruleInstance goal children ≤ coefficient definition.1 *
      ((Selection.inputWire ruleInstance goal children).length + 1)^2 := by
  have selection := Selection.clock_linear ruleInstance goal children
  have node := NodeChildrenExecution.clock_polynomial definition firstOrder ruleInstance goal children
  rw [← input_exact] at node
  have linear : (Selection.inputWire ruleInstance goal children).length + 1 ≤
      ((Selection.inputWire ruleInstance goal children).length + 1)^2 := le_self_pow (by omega) (by decide)
  unfold clock coefficient
  nlinarith

noncomputable def polynomialOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (ruleInstance : RuleInstance)
    (goal : Pattern) (children : List RawOpenProof) :
    TM2OutputsInTime (machine definition.1) (Selection.inputWire ruleInstance goal children)
      (some (resultWire definition ruleInstance goal children))
      (coefficient definition.1 * ((Selection.inputWire ruleInstance goal children).length + 1)^2) :=
  WordEqualityMachine.within (outputs definition firstOrder ruleInstance goal children)
    (clock_polynomial definition firstOrder ruleInstance goal children)

abbrev Input := RuleInstance × Pattern × List RawOpenProof
def encodeInput (input : Input) := Selection.inputWire input.1 input.2.1 input.2.2
def evaluate (definition : ValidatedCalculusLanguageDef) (input : Input) :=
  resultWire definition input.1 input.2.1 input.2.2

noncomputable def realization (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) :
    TM2ComputableInPolyTime encodeInput id (evaluate definition) where
  tm := machine definition.1
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl PairCell
  time := Polynomial.C (coefficient definition.1) * (Polynomial.X + Polynomial.C 1)^2
  outputsFun input := by
    change TM2OutputsInTime (machine definition.1) ((encodeInput input).map id)
      (some ((evaluate definition input).map id)) _
    simp only [List.map_id, encodeInput, evaluate, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
    exact polynomialOutputs definition firstOrder input.1 input.2.1 input.2.2

namespace Controls
open Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayPresentation

theorem nullary_jobs : OriginalChildJobs.readOutput
    (resultWire mpValidated ⟨⟨"a"⟩, []⟩ (judgmentP formulaA) []) = some [] := by
  rw [result_readout]
  simp [RuleInstantiationExecution.Controls.nullary_rule]

theorem ordered_jobs : OriginalChildJobs.readOutput
    (resultWire mpValidated ⟨⟨"m"⟩, [formulaA, formulaB]⟩ (judgmentP formulaB)
      [.premise 7, .premise 3]) = some
        [(judgmentP formulaA, .premise 7), (judgmentP (implication formulaA formulaB), .premise 3)] := by
  rw [result_readout]
  simp [RuleInstantiationExecution.Controls.ordered_modus_ponens]

theorem repeated_children_preserved : OriginalChildJobs.readOutput
    (resultWire mpValidated ⟨⟨"m"⟩, [formulaA, formulaB]⟩ (judgmentP formulaB)
      [.premise 4, .premise 4]) = some
        [(judgmentP formulaA, .premise 4), (judgmentP (implication formulaA formulaB), .premise 4)] := by
  rw [result_readout]
  simp [RuleInstantiationExecution.Controls.ordered_modus_ponens]

theorem nested_child_bodies_preserved : OriginalChildJobs.readOutput
    (resultWire mpValidated ⟨⟨"m"⟩, [formulaA, formulaB]⟩ (judgmentP formulaB)
      [.node ⟨⟨"untrusted"⟩, [formulaA]⟩ [.premise 99], .premise 3]) = some
        [(judgmentP formulaA, .node ⟨⟨"untrusted"⟩, [formulaA]⟩ [.premise 99]),
          (judgmentP (implication formulaA formulaB), .premise 3)] := by
  rw [result_readout]
  simp [RuleInstantiationExecution.Controls.ordered_modus_ponens]

theorem missing_child_refused : OriginalChildJobs.readOutput
    (resultWire mpValidated ⟨⟨"m"⟩, [formulaA, formulaB]⟩ (judgmentP formulaB) [.premise 7]) = none := by
  rw [result_readout]
  simp [RuleInstantiationExecution.Controls.ordered_modus_ponens]

theorem extra_nullary_child_refused : OriginalChildJobs.readOutput
    (resultWire mpValidated ⟨⟨"a"⟩, []⟩ (judgmentP formulaA) [.premise 0]) = none := by
  rw [result_readout]
  simp [RuleInstantiationExecution.Controls.nullary_rule]

theorem changed_goal_refused : OriginalChildJobs.readOutput
    (resultWire mpValidated ⟨⟨"a"⟩, []⟩ (judgmentP formulaB) []) = none := by
  rw [result_readout]
  simp [RuleInstantiationExecution.Controls.nullary_rule]
  decide +kernel

theorem absent_row_refused : OriginalChildJobs.readOutput
    (resultWire mpValidated ⟨⟨"absent"⟩, []⟩ (judgmentP formulaA) []) = none := by
  rw [result_readout]
  simp [RuleInstantiationExecution.Controls.absent_rule_refused]

theorem escaping_argument_refused : OriginalChildJobs.readOutput
    (resultWire FirstOrder.InferenceTranslation.Controls.dataCalculus
      ⟨⟨"data"⟩, [.lambda none (.bvar 1)]⟩ (judgmentP (.lambda none (.bvar 1))) []) = none := by
  rw [result_readout]
  simp [RuleInstantiationExecution.Controls.escaping_argument_refused]

end Controls

end Mettapedia.Languages.HOLLight.AuthoredNodeDispatch
