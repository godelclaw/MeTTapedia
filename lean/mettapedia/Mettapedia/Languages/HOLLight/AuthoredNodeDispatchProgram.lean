import Mettapedia.Languages.HOLLight.AuthoredNodeDispatch
import Mettapedia.Languages.HOLLight.ClaimCheckingProgram
import Mettapedia.Languages.HOLLight.OriginalChildJobsProgram
import Mettapedia.Computability.RetainedWordProgram

/-!
# Original authored-node instruction interface

The table and literal physical endpoints expose the complete original
row-selection and node-admission execution. Equality to the original machine
preserves its transitions, source guards, refusal paths and counted clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option allowUnsafeReducibility true
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.AuthoredNodeDispatch.Program
open Turing
open Mettapedia.Computability
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Binding.WireCodec.Binary

attribute [local reducible]
  Mettapedia.Languages.HOLLight.AuthoredNodeDispatch.Selection.selectedMachine
  Mettapedia.Languages.HOLLight.AuthoredNodeDispatch.Selection.machine
  Mettapedia.Languages.HOLLight.AuthoredNodeDispatch.family
  Mettapedia.Languages.HOLLight.AuthoredNodeDispatch.dispatcher
  Mettapedia.Languages.HOLLight.AuthoredNodeDispatch.machine
  Mettapedia.Languages.HOLLight.NodeChildrenExecution.selectedNodeMachine
  Mettapedia.Languages.HOLLight.NodeChildrenExecution.savedNodeMachine
  Mettapedia.Languages.HOLLight.NodeChildrenExecution.testedNodeMachine
  Mettapedia.Languages.HOLLight.NodeChildrenExecution.selectedInstantiationMachine
  Mettapedia.Languages.HOLLight.NodeChildrenExecution.premiseMachine
  Mettapedia.Languages.HOLLight.NodeChildrenExecution.selectedPremiseMachine
  Mettapedia.Languages.HOLLight.NodeChildrenExecution.retainedPremiseMachine
  Mettapedia.Languages.HOLLight.NodeChildrenExecution.rawIdentity
  Mettapedia.Languages.HOLLight.NodeChildrenExecution.stripMachine
  Mettapedia.Languages.HOLLight.NodeChildrenExecution.selectedStripMachine
  Mettapedia.Languages.HOLLight.NodeChildrenExecution.retainedStripMachine
  Mettapedia.Languages.HOLLight.NodeChildrenExecution.preparedPremiseMachine
  Mettapedia.Languages.HOLLight.NodeChildrenExecution.selectedChildrenMachine
  Mettapedia.Languages.HOLLight.NodeChildrenExecution.payloadMachine
  Mettapedia.Languages.HOLLight.NodeChildrenExecution.guardedMachine
  Mettapedia.Languages.HOLLight.NodeChildrenExecution.machine
  Mettapedia.Languages.HOLLight.RuleNodeAdmission.selectedMachine
  Mettapedia.Languages.HOLLight.RuleNodeAdmission.retainedMachine
  Mettapedia.Languages.HOLLight.RuleNodeAdmission.conclusionMachine
  Mettapedia.Languages.HOLLight.RuleNodeAdmission.selectedConclusionMachine
  Mettapedia.Languages.HOLLight.RuleNodeAdmission.projectedMachine
  Mettapedia.Languages.HOLLight.RuleNodeAdmission.Comparison.compareMachine
  Mettapedia.Languages.HOLLight.RuleNodeAdmission.Comparison.machine
  Mettapedia.Languages.HOLLight.RuleNodeAdmission.preparedMachine
  Mettapedia.Languages.HOLLight.RuleNodeAdmission.machine
  Mettapedia.Languages.HOLLight.RuleNodeAdmission.retainedComparisonMachine
  Mettapedia.Languages.HOLLight.RuleNodeAdmission.jobMachine
  Mettapedia.Languages.HOLLight.RuleInstantiationExecution.testedMachine
  Mettapedia.Languages.HOLLight.RuleInstantiationExecution.guardedMachine
  Mettapedia.Languages.HOLLight.RuleInstantiationExecution.machine
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.dictionary
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.classifier
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.nameMachine
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.machine
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.argumentMachine
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.UniformArity.family
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.UniformArity.machine
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.admissionMachine
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.ArgumentScope.machine
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.ScopedApplication.scopeDispatcher
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.ScopedApplication.scopeMachine
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.ScopedApplication.savedMachine
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.ScopedApplication.relookupMachine
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.ScopedApplication.selectedMachine
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.ScopedApplication.machine
  Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.stripMachine
  Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.stripAtArityMachine
  Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.normalizedMachine
  Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.copier
  Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.copyDispatcher
  Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.machine
  Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.Authored.localMachine
  Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.Authored.family
  Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.Authored.dispatcher
  Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.Authored.machine
  StackMachineComposition.machine
  StackMachineComposition.Dispatch.machine
  StackMachineComposition.Dispatch.lift
  StackMachineComposition.leftKey
  StackMachineComposition.rightKey
  CommonArenaDispatch.machine
  CommonArenaDispatch.program
  CommonArenaDispatch.body
  CommonArenaDispatch.Programs.body
  CommonArenaDispatch.Programs.embedded
  CommonArenaDispatch.Family.toMachine
  CommonArenaDispatch.readByte
  RetainedWordExecution.machine
  RetainedWordExecution.statement
  RetainedWordExecution.body
  RetainedWordExecution.WithOutput.machine
  RetainedWordExecution.WithOutput.statement
  RetainedWordExecution.WithOutput.body
  RetainedWordExecution.WithOutput.Framed.machine
  RetainedWordExecution.WithOutput.Framed.untag
  WordHomomorphismMachine.machine
  WordTemplateMachine.machine
  WordTemplateMachine.Indexed.machine
  WordTemplateMachine.Indexed.Alphabet
  WordEqualityMachine.machine
  CertificateSchemaInstantiation.stripDispatcher
  FramedFieldSelection.machine
  FramedWordSuffixRemoval.machine
  FramedWordMapping.machine
  FramedWordMapping.statement
  FramedWordMapping.body
  FramedWordMapping.initial
  OriginalChildJobs.machine
  OriginalChildJobs.preparedMachine
  OriginalChildJobs.framingMachine
  FramedWordPairing.machine
  CertificateArgumentFraming.Execution.machine
  CertificateArgumentFraming.Execution.parserBody
  CertificateDataTraversal.ProductField.machine
  CertificateDataTraversal.PrefixField.machine
  CertificateDataTraversal.machine
  FramedWordValidation.retainedMachine
  FramedWordValidation.machine
  FramedWordValidation.statement
  FramedWordValidation.body
  PatternScopeExecution.OriginalAdmission.machine
  PatternScopeExecution.OriginalAdmission.projectedMachine
  PatternScopeExecution.VisitorAdapter.machine
  PatternScopeExecution.Binary.machine
  PatternSpanExecution.Execution.machine
  FiniteWordClassifier.machine

abbrev target (definition : CalculusLanguageDef) := AuthoredNodeDispatch.machine definition

private theorem dispatchLift_eq (program : FinTM2) (statement : program.Stmt) :
    StackMachineComposition.Dispatch.lift program statement =
      StackMachineRegisters.extend StackMachineComposition.Dispatch.Phase.run statement := by
  induction statement <;> simp_all only [StackMachineComposition.Dispatch.lift, StackMachineRegisters.extend]

open Lean Elab Tactic Meta in
elab "extract_authored_program " expression:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let original ← Elab.Term.elabTerm expression none
    let mut rules : SimpTheorems := {}
    for name in [``StackMachineComposition.liftFirst_eq_embedStatement,
        ``StackMachineComposition.liftSecond_eq_embedStatement, ``dispatchLift_eq] do
      rules ← rules.addConst name
    for name in [
        ``CertificateSchemaInstantiation.stripDispatcher,
        ``Mettapedia.Languages.HOLLight.AuthoredNodeDispatch.Selection.selectedMachine,
        ``Mettapedia.Languages.HOLLight.AuthoredNodeDispatch.Selection.machine,
        ``Mettapedia.Languages.HOLLight.AuthoredNodeDispatch.family,
        ``Mettapedia.Languages.HOLLight.AuthoredNodeDispatch.dispatcher,
        ``Mettapedia.Languages.HOLLight.AuthoredNodeDispatch.machine,
        ``Mettapedia.Languages.HOLLight.NodeChildrenExecution.selectedNodeMachine,
        ``Mettapedia.Languages.HOLLight.NodeChildrenExecution.savedNodeMachine,
        ``Mettapedia.Languages.HOLLight.NodeChildrenExecution.testedNodeMachine,
        ``Mettapedia.Languages.HOLLight.NodeChildrenExecution.selectedInstantiationMachine,
        ``Mettapedia.Languages.HOLLight.NodeChildrenExecution.premiseMachine,
        ``Mettapedia.Languages.HOLLight.NodeChildrenExecution.selectedPremiseMachine,
        ``Mettapedia.Languages.HOLLight.NodeChildrenExecution.retainedPremiseMachine,
        ``Mettapedia.Languages.HOLLight.NodeChildrenExecution.rawIdentity,
        ``Mettapedia.Languages.HOLLight.NodeChildrenExecution.stripMachine,
        ``Mettapedia.Languages.HOLLight.NodeChildrenExecution.selectedStripMachine,
        ``Mettapedia.Languages.HOLLight.NodeChildrenExecution.retainedStripMachine,
        ``Mettapedia.Languages.HOLLight.NodeChildrenExecution.preparedPremiseMachine,
        ``Mettapedia.Languages.HOLLight.NodeChildrenExecution.selectedChildrenMachine,
        ``Mettapedia.Languages.HOLLight.NodeChildrenExecution.payloadMachine,
        ``Mettapedia.Languages.HOLLight.NodeChildrenExecution.guardedMachine,
        ``Mettapedia.Languages.HOLLight.NodeChildrenExecution.machine,
        ``Mettapedia.Languages.HOLLight.RuleNodeAdmission.selectedMachine,
        ``Mettapedia.Languages.HOLLight.RuleNodeAdmission.retainedMachine,
        ``Mettapedia.Languages.HOLLight.RuleNodeAdmission.conclusionMachine,
        ``Mettapedia.Languages.HOLLight.RuleNodeAdmission.selectedConclusionMachine,
        ``Mettapedia.Languages.HOLLight.RuleNodeAdmission.projectedMachine,
        ``Mettapedia.Languages.HOLLight.RuleNodeAdmission.Comparison.compareMachine,
        ``Mettapedia.Languages.HOLLight.RuleNodeAdmission.Comparison.machine,
        ``Mettapedia.Languages.HOLLight.RuleNodeAdmission.preparedMachine,
        ``Mettapedia.Languages.HOLLight.RuleNodeAdmission.machine,
        ``Mettapedia.Languages.HOLLight.RuleNodeAdmission.retainedComparisonMachine,
        ``Mettapedia.Languages.HOLLight.RuleNodeAdmission.jobMachine,
        ``Mettapedia.Languages.HOLLight.RuleInstantiationExecution.testedMachine,
        ``Mettapedia.Languages.HOLLight.RuleInstantiationExecution.guardedMachine,
        ``Mettapedia.Languages.HOLLight.RuleInstantiationExecution.machine,
        ``Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.dictionary,
        ``Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.classifier,
        ``Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.nameMachine,
        ``Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.machine,
        ``Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.argumentMachine,
        ``Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.UniformArity.family,
        ``Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.UniformArity.machine,
        ``Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.admissionMachine,
        ``Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.ArgumentScope.machine,
        ``Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.ScopedApplication.scopeDispatcher,
        ``Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.ScopedApplication.scopeMachine,
        ``Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.ScopedApplication.savedMachine,
        ``Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.ScopedApplication.relookupMachine,
        ``Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.ScopedApplication.selectedMachine,
        ``Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.ScopedApplication.machine,
        ``Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.stripMachine,
        ``Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.stripAtArityMachine,
        ``Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.normalizedMachine,
        ``Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.copier,
        ``Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.copyDispatcher,
        ``Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.machine,
        ``Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.Authored.localMachine,
        ``Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.Authored.family,
        ``Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.Authored.dispatcher,
        ``Mettapedia.GSLT.LanguageDef.CertificateSchemaInstantiation.Authored.machine,
        ``StackMachineComposition.machine,
        ``StackMachineComposition.Dispatch.machine,
        ``StackMachineComposition.Dispatch.lift,
        ``StackMachineComposition.leftKey,
        ``StackMachineComposition.rightKey,
        ``CommonArenaDispatch.machine,
        ``CommonArenaDispatch.program,
        ``CommonArenaDispatch.body,
        ``CommonArenaDispatch.Programs.body,
        ``CommonArenaDispatch.Programs.embedded,
        ``CommonArenaDispatch.Family.toMachine,
        ``CommonArenaDispatch.readByte,
        ``RetainedWordExecution.machine,
        ``RetainedWordExecution.statement,
        ``RetainedWordExecution.body,
        ``RetainedWordExecution.WithOutput.machine,
        ``RetainedWordExecution.WithOutput.statement,
        ``RetainedWordExecution.WithOutput.body,
        ``RetainedWordExecution.WithOutput.Framed.machine,
        ``RetainedWordExecution.WithOutput.Framed.untag,
        ``WordHomomorphismMachine.machine,
        ``WordTemplateMachine.machine,
        ``WordTemplateMachine.Indexed.machine,
        ``WordTemplateMachine.Indexed.Alphabet,
        ``WordEqualityMachine.machine,
        ``FramedFieldSelection.machine,
        ``FramedWordSuffixRemoval.machine,
        ``FramedWordMapping.machine,
        ``FramedWordMapping.statement,
        ``FramedWordMapping.body,
        ``FramedWordMapping.initial,
        ``OriginalChildJobs.machine,
        ``OriginalChildJobs.preparedMachine,
        ``OriginalChildJobs.framingMachine,
        ``FramedWordPairing.machine,
        ``CertificateArgumentFraming.Execution.machine,
        ``CertificateArgumentFraming.Execution.parserBody,
        ``CertificateDataTraversal.ProductField.machine,
        ``CertificateDataTraversal.PrefixField.machine,
        ``CertificateDataTraversal.machine,
        ``FramedWordValidation.retainedMachine,
        ``FramedWordValidation.machine,
        ``FramedWordValidation.statement,
        ``FramedWordValidation.body,
        ``PatternScopeExecution.OriginalAdmission.machine,
        ``PatternScopeExecution.OriginalAdmission.projectedMachine,
        ``PatternScopeExecution.VisitorAdapter.machine,
        ``PatternScopeExecution.Binary.machine,
        ``PatternSpanExecution.Execution.machine,
        ``FiniteWordClassifier.machine] do
      rules := rules.addDeclToUnfoldCore name
    let ctx ← Simp.mkContext { zeta := false } (simpTheorems := #[rules])
      (congrTheorems := ← getSimpCongrTheorems)
    let (simplified, _) ← simp original ctx
    let value := simplified.expr
    let proof ← mkEqSymm (← simplified.getProof)
    let goalType ← whnf (← goal.getType)
    let args := goalType.getAppArgs
    goal.assign (← mkAppOptM ``Subtype.mk #[some (args.getD 0 (.bvar 0)),
      some (args.getD 1 (.bvar 0)), some value, some proof])
  replaceMainGoal []

open Lean Elab Tactic Meta in
elab "authored_program_literal_endpoints " expression:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let expression ← Elab.Term.elabTerm expression (← goal.getType)
    let literal ← Meta.transform expression (pre := fun term => do
      let endpoint := match term with
        | .proj ``FinTM2 field _ => [3,4,7,10].contains field
        | _ => match term.getAppFn.constName? with
          | some name => [``FinTM2.k₀,``FinTM2.k₁,``FinTM2.main,``FinTM2.initialState].contains name
          | none => false
      if endpoint then return .done (← withTransparency .reducible (reduce term))
      else return .continue)
    goal.assign literal
  replaceMainGoal []

def schemaCoreTable {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity) :
    { instructions : (CertificateSchemaInstantiation.machine template).Λ →
        (CertificateSchemaInstantiation.machine template).Stmt //
      instructions = (CertificateSchemaInstantiation.machine template).m } := by
  extract_authored_program (CertificateSchemaInstantiation.machine template).m


def schemaCoreBody {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity) :=
  (schemaCoreTable template).val

theorem schemaCoreBody_exact {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity) :
    schemaCoreBody template = (CertificateSchemaInstantiation.machine template).m :=
  (schemaCoreTable template).property

local instance {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity) :
    Inhabited ((CertificateSchemaInstantiation.machine template).Γ (CertificateSchemaInstantiation.machine template).k₀) :=
  inferInstanceAs (Inhabited Alphabet)

def schemaDispatchBody {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity)
    (enabled : Bool) : (StackMachineComposition.Dispatch.machine (CertificateSchemaInstantiation.machine template)
      (CertificateSchemaInstantiation.Authored.accepts enabled) [(0 : Alphabet)]).Λ →
      (StackMachineComposition.Dispatch.machine (CertificateSchemaInstantiation.machine template)
      (CertificateSchemaInstantiation.Authored.accepts enabled) [(0 : Alphabet)]).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Dispatch.Programs.body
    (CertificateSchemaInstantiation.machine template).k₀ (CertificateSchemaInstantiation.machine template).k₁
    (CertificateSchemaInstantiation.machine template).initialState (CertificateSchemaInstantiation.machine template).main
    (CertificateSchemaInstantiation.Authored.accepts enabled) [(0 : Alphabet)] (schemaCoreBody template))

theorem schemaDispatchBody_exact {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity)
    (enabled : Bool) : schemaDispatchBody template enabled =
      (StackMachineComposition.Dispatch.machine (CertificateSchemaInstantiation.machine template)
      (CertificateSchemaInstantiation.Authored.accepts enabled) [(0 : Alphabet)]).m := by
  unfold schemaDispatchBody
  rw [schemaCoreBody_exact]
  exact (StackMachineComposition.Dispatch.Programs.body_eq _ _ _).symm


def productFieldTable (second : Bool) :
    { instructions : (CertificateDataTraversal.ProductField.machine second).Λ →
        (CertificateDataTraversal.ProductField.machine second).Stmt //
      instructions = (CertificateDataTraversal.ProductField.machine second).m } := by
  extract_authored_program (CertificateDataTraversal.ProductField.machine second).m

def productFieldBody (second : Bool) := (productFieldTable second).val

theorem productFieldBody_exact (second : Bool) :
    productFieldBody second = (CertificateDataTraversal.ProductField.machine second).m :=
  (productFieldTable second).property

local instance : Inhabited ((CertificateDataTraversal.ProductField.machine true).Γ
    (CertificateDataTraversal.ProductField.machine true).k₁) := inferInstanceAs (Inhabited Alphabet)

def schemaLocalBody {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity)
    (enabled : Bool) : (CertificateSchemaInstantiation.Authored.localMachine template enabled).Λ →
      (CertificateSchemaInstantiation.Authored.localMachine template enabled).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (CertificateDataTraversal.ProductField.machine true).k₁
    (CertificateSchemaInstantiation.machine template).k₀ StackMachineComposition.Dispatch.Phase.read
    (0 : Alphabet) id (productFieldBody true) (schemaDispatchBody template enabled))

theorem schemaLocalBody_exact {arity : Nat} (template : WordTemplateMachine.Indexed.Template Alphabet arity)
    (enabled : Bool) : schemaLocalBody template enabled =
      (CertificateSchemaInstantiation.Authored.localMachine template enabled).m := by
  unfold schemaLocalBody
  rw [productFieldBody_exact, schemaDispatchBody_exact]
  exact StackMachineComposition.body_eq (CertificateDataTraversal.ProductField.machine true)
    (StackMachineComposition.Dispatch.machine (CertificateSchemaInstantiation.machine template)
      (CertificateSchemaInstantiation.Authored.accepts enabled) [(0 : Alphabet)]) (Equiv.refl Alphabet)


def schemaMains (definition : CalculusLanguageDef) :
    ∀ index, (CertificateSchemaInstantiation.Authored.family definition).Label index := by
  authored_program_literal_endpoints (fun index =>
    (CertificateSchemaInstantiation.Authored.localMachine
      (CertificateSchemaInstantiation.Authored.plan (CertificateRuleAdmission.row definition index))
      (CertificateSchemaInstantiation.Authored.compiled (CertificateRuleAdmission.row definition index)).isSome).main)

def schemaInitial : CertificateSchemaInstantiation.Authored.Base.σ := by
  normalize_rule_program CertificateSchemaInstantiation.Authored.Base.initialState

def schemaDispatcherBody (definition : CalculusLanguageDef) :
    (CertificateSchemaInstantiation.Authored.dispatcher definition).Λ →
      (CertificateSchemaInstantiation.Authored.dispatcher definition).Stmt := by
  authored_program_literal_endpoints (CommonArenaDispatch.Programs.body
    CertificateSchemaInstantiation.Authored.Base (CertificateSchemaInstantiation.Authored.family definition)
    (CommonArenaDispatch.baseKey CertificateSchemaInstantiation.Authored.Base
      CertificateSchemaInstantiation.Authored.Base.k₀)
    (CommonArenaDispatch.baseKey CertificateSchemaInstantiation.Authored.Base
      CertificateSchemaInstantiation.Authored.Base.k₁)
    rfl rfl schemaInitial (schemaMains definition)
    (fun index => schemaLocalBody
      (CertificateSchemaInstantiation.Authored.plan (CertificateRuleAdmission.row definition index))
      (CertificateSchemaInstantiation.Authored.compiled (CertificateRuleAdmission.row definition index)).isSome)
    (0 : Alphabet) (0 : Alphabet))

theorem schemaDispatcherBody_exact (definition : CalculusLanguageDef) :
    schemaDispatcherBody definition = (CertificateSchemaInstantiation.Authored.dispatcher definition).m := by
  have source : (fun index => schemaLocalBody
      (CertificateSchemaInstantiation.Authored.plan (CertificateRuleAdmission.row definition index))
      (CertificateSchemaInstantiation.Authored.compiled (CertificateRuleAdmission.row definition index)).isSome) =
      (CertificateSchemaInstantiation.Authored.family definition).body := by
    funext index
    exact schemaLocalBody_exact _ _
  unfold schemaDispatcherBody
  rw [source]
  rfl

def lookupTable (definition : CalculusLanguageDef) :
    { instructions : (CertificateRuleAdmission.machine definition).Λ →
        (CertificateRuleAdmission.machine definition).Stmt //
      instructions = (CertificateRuleAdmission.machine definition).m } := by
  extract_authored_program (CertificateRuleAdmission.machine definition).m

def lookupBody (definition : CalculusLanguageDef) := (lookupTable definition).val

theorem lookupBody_exact (definition : CalculusLanguageDef) :
    lookupBody definition = (CertificateRuleAdmission.machine definition).m :=
  (lookupTable definition).property

local instance (definition : CalculusLanguageDef) : Fintype ((CertificateRuleAdmission.machine definition).Γ
    (CertificateRuleAdmission.machine definition).k₁) := inferInstanceAs (Fintype (Alphabet ⊕ Option (Fin definition.rules.length)))
local instance (definition : CalculusLanguageDef) : Inhabited ((CertificateRuleAdmission.machine definition).Γ
    (CertificateRuleAdmission.machine definition).k₁) := inferInstanceAs (Inhabited (Alphabet ⊕ Option (Fin definition.rules.length)))

def schemaAuthoredBody (definition : CalculusLanguageDef) :
    (CertificateSchemaInstantiation.Authored.machine definition).Λ → (CertificateSchemaInstantiation.Authored.machine definition).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (CertificateRuleAdmission.machine definition).k₁ (CertificateSchemaInstantiation.Authored.dispatcher definition).k₀
    (CertificateSchemaInstantiation.Authored.dispatcher definition).main
    (default : Alphabet ⊕ Option (Fin definition.rules.length)) id
    (lookupBody definition) (schemaDispatcherBody definition))

theorem schemaAuthoredBody_exact (definition : CalculusLanguageDef) :
    schemaAuthoredBody definition = (CertificateSchemaInstantiation.Authored.machine definition).m := by
  unfold schemaAuthoredBody
  rw [lookupBody_exact, schemaDispatcherBody_exact]
  exact StackMachineComposition.body_eq (CertificateRuleAdmission.machine definition)
    (CertificateSchemaInstantiation.Authored.dispatcher definition) (Equiv.refl _)

local instance (definition : CalculusLanguageDef) : Fintype ((CertificateRuleAdmission.ScopedApplication.scopeMachine definition).Γ
    (CertificateRuleAdmission.ScopedApplication.scopeMachine definition).k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Bool))
local instance (definition : CalculusLanguageDef) : Inhabited ((CertificateRuleAdmission.ScopedApplication.scopeMachine definition).Γ
    (CertificateRuleAdmission.ScopedApplication.scopeMachine definition).k₀) := inferInstanceAs (Inhabited Alphabet)

def savedScopeBody (definition : CalculusLanguageDef) :
    (CertificateRuleAdmission.ScopedApplication.savedMachine definition).Λ → (CertificateRuleAdmission.ScopedApplication.savedMachine definition).Stmt := by
  authored_program_literal_endpoints (RetainedWordExecution.Programs.body
    (CertificateRuleAdmission.ScopedApplication.scopeMachine definition).k₀
    (CertificateRuleAdmission.ScopedApplication.scopeMachine definition).k₁
    (CertificateRuleAdmission.ScopedApplication.scopeMachine definition).initialState
    (CertificateRuleAdmission.ScopedApplication.scopeMachine definition).main
    (0 : Alphabet) false CertificateRuleAdmission.ScopedApplication.readScope
    (RuleArgumentRendering.Program.scopeBody definition))

theorem savedScopeBody_exact (definition : CalculusLanguageDef) :
    savedScopeBody definition = (CertificateRuleAdmission.ScopedApplication.savedMachine definition).m := by
  unfold savedScopeBody
  rw [RuleArgumentRendering.Program.scopeBody_exact]
  exact RetainedWordExecution.Programs.body_eq _ _

local instance (definition : CalculusLanguageDef) : Fintype ((CertificateRuleAdmission.ScopedApplication.savedMachine definition).Γ
    (CertificateRuleAdmission.ScopedApplication.savedMachine definition).k₁) := inferInstanceAs (Fintype (Alphabet ⊕ Bool))
local instance (definition : CalculusLanguageDef) : Inhabited ((CertificateRuleAdmission.ScopedApplication.savedMachine definition).Γ
    (CertificateRuleAdmission.ScopedApplication.savedMachine definition).k₁) := inferInstanceAs (Inhabited (Alphabet ⊕ Bool))

def testedScopeBody (definition : CalculusLanguageDef) :
    (RuleInstantiationExecution.testedMachine definition).Λ → (RuleInstantiationExecution.testedMachine definition).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (CertificateRuleAdmission.ScopedApplication.savedMachine definition).k₁ WordHomomorphismMachine.Stack.input
    WordHomomorphismMachine.Phase.read (default : Alphabet ⊕ Bool) id
    (savedScopeBody definition) (WordHomomorphismMachine.program RuleInstantiationExecution.project))

theorem testedScopeBody_exact (definition : CalculusLanguageDef) :
    testedScopeBody definition = (RuleInstantiationExecution.testedMachine definition).m := by
  unfold testedScopeBody
  rw [savedScopeBody_exact]
  exact StackMachineComposition.body_eq (CertificateRuleAdmission.ScopedApplication.savedMachine definition)
    (WordHomomorphismMachine.machine RuleInstantiationExecution.project) (Equiv.refl _)

local instance (definition : CalculusLanguageDef) : Inhabited ((CertificateSchemaInstantiation.Authored.machine definition).Γ
    (CertificateSchemaInstantiation.Authored.machine definition).k₀) := inferInstanceAs (Inhabited Alphabet)

def guardedSchemaBody (definition : CalculusLanguageDef) :
    (RuleInstantiationExecution.guardedMachine definition).Λ → (RuleInstantiationExecution.guardedMachine definition).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Dispatch.Programs.body
    (CertificateSchemaInstantiation.Authored.machine definition).k₀ (CertificateSchemaInstantiation.Authored.machine definition).k₁
    (CertificateSchemaInstantiation.Authored.machine definition).initialState (CertificateSchemaInstantiation.Authored.machine definition).main
    RuleInstantiationExecution.accept [(0 : Alphabet)] (schemaAuthoredBody definition))

theorem guardedSchemaBody_exact (definition : CalculusLanguageDef) :
    guardedSchemaBody definition = (RuleInstantiationExecution.guardedMachine definition).m := by
  unfold guardedSchemaBody
  rw [schemaAuthoredBody_exact]
  exact (StackMachineComposition.Dispatch.Programs.body_eq _ _ _).symm

local instance (definition : CalculusLanguageDef) : Fintype ((RuleInstantiationExecution.testedMachine definition).Γ
    (RuleInstantiationExecution.testedMachine definition).k₁) := inferInstanceAs (Fintype Alphabet)
local instance (definition : CalculusLanguageDef) : Inhabited ((RuleInstantiationExecution.testedMachine definition).Γ
    (RuleInstantiationExecution.testedMachine definition).k₁) := inferInstanceAs (Inhabited Alphabet)

def instantiationBody (definition : CalculusLanguageDef) :
    (RuleInstantiationExecution.machine definition).Λ → (RuleInstantiationExecution.machine definition).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (RuleInstantiationExecution.testedMachine definition).k₁ (RuleInstantiationExecution.guardedMachine definition).k₀
    (RuleInstantiationExecution.guardedMachine definition).main (0 : Alphabet) id
    (testedScopeBody definition) (guardedSchemaBody definition))

theorem instantiationBody_exact (definition : CalculusLanguageDef) :
    instantiationBody definition = (RuleInstantiationExecution.machine definition).m := by
  unfold instantiationBody
  rw [testedScopeBody_exact, guardedSchemaBody_exact]
  exact StackMachineComposition.body_eq (RuleInstantiationExecution.testedMachine definition)
    (RuleInstantiationExecution.guardedMachine definition) (Equiv.refl _)

def framedUntag : Option Alphabet ⊕ Alphabet → List (Option Alphabet)
  | .inl value => [value]
  | .inr value => [some value]

attribute [local reducible] framedUntag

def homomorphicBody {A B : Type} [Fintype A] [Fintype B] [Inhabited B]
    {original images : A → List B} (same : original = images) :
    (WordHomomorphismMachine.machine original).Λ → (WordHomomorphismMachine.machine original).Stmt :=
  same.symm ▸ WordHomomorphismMachine.program images

theorem homomorphicBody_exact {A B : Type} [Fintype A] [Fintype B] [Inhabited B]
    {original images : A → List B} (same : original = images) :
    homomorphicBody same = (WordHomomorphismMachine.machine original).m := by
  cases same
  rfl

def nodeSelectorBodyTable  : { instructions : (WordTemplateMachine.Indexed.machine RuleNodeAdmission.selector).Λ → (WordTemplateMachine.Indexed.machine RuleNodeAdmission.selector).Stmt // instructions = (WordTemplateMachine.Indexed.machine RuleNodeAdmission.selector).m } := by
  extract_authored_program (WordTemplateMachine.Indexed.machine RuleNodeAdmission.selector).m

def nodeSelectorBody  := (nodeSelectorBodyTable ).val

theorem nodeSelectorBody_exact  : nodeSelectorBody  = (WordTemplateMachine.Indexed.machine RuleNodeAdmission.selector).m := (nodeSelectorBodyTable ).property

local instance : Fintype ((WordTemplateMachine.Indexed.machine RuleNodeAdmission.selector).Γ (WordTemplateMachine.Indexed.machine RuleNodeAdmission.selector).k₁) := inferInstanceAs (Fintype Alphabet)

local instance : Inhabited ((WordTemplateMachine.Indexed.machine RuleNodeAdmission.selector).Γ (WordTemplateMachine.Indexed.machine RuleNodeAdmission.selector).k₁) := inferInstanceAs (Inhabited Alphabet)

def selectedRuleBody (definition : CalculusLanguageDef) : (RuleNodeAdmission.selectedMachine definition).Λ → (RuleNodeAdmission.selectedMachine definition).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (WordTemplateMachine.Indexed.machine RuleNodeAdmission.selector).k₁ (RuleInstantiationExecution.machine definition).k₀ (RuleInstantiationExecution.machine definition).main (default : Alphabet) id
    nodeSelectorBody (instantiationBody definition))

theorem selectedRuleBody_exact (definition : CalculusLanguageDef) : selectedRuleBody definition = (RuleNodeAdmission.selectedMachine definition).m := by
  unfold selectedRuleBody
  rw [nodeSelectorBody_exact, instantiationBody_exact]
  exact StackMachineComposition.body_eq (WordTemplateMachine.Indexed.machine RuleNodeAdmission.selector) (RuleInstantiationExecution.machine definition) (Equiv.refl _)

local instance (definition : CalculusLanguageDef) : Fintype ((RuleNodeAdmission.selectedMachine definition).Γ (RuleNodeAdmission.selectedMachine definition).k₁) := inferInstanceAs (Fintype Alphabet)

local instance (definition : CalculusLanguageDef) : Inhabited ((RuleNodeAdmission.selectedMachine definition).Γ (RuleNodeAdmission.selectedMachine definition).k₁) := inferInstanceAs (Inhabited Alphabet)

local instance (definition : CalculusLanguageDef) : Inhabited ((RuleNodeAdmission.selectedMachine definition).Γ (RuleNodeAdmission.selectedMachine definition).k₀) := inferInstanceAs (Inhabited (Option Alphabet))

def retainedRuleBodySaved (definition : CalculusLanguageDef) : (RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedMachine definition)).Λ →
    (RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedMachine definition)).Stmt := by
  authored_program_literal_endpoints (RetainedWordExecution.WithOutput.Programs.statement
    (RuleNodeAdmission.selectedMachine definition).k₀ (RuleNodeAdmission.selectedMachine definition).k₁ (none : Option Alphabet) (0 : Alphabet)
    (RuleNodeAdmission.selectedMachine definition).initialState (RuleNodeAdmission.selectedMachine definition).main (selectedRuleBody definition))

theorem retainedRuleBodySaved_exact (definition : CalculusLanguageDef) : retainedRuleBodySaved definition = (RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedMachine definition)).m := by
  unfold retainedRuleBodySaved
  rw [selectedRuleBody_exact]
  rfl

local instance (definition : CalculusLanguageDef) : Fintype ((RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedMachine definition)).Γ (RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedMachine definition)).k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Alphabet))

local instance (definition : CalculusLanguageDef) : Inhabited ((RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedMachine definition)).Γ (RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedMachine definition)).k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Alphabet))

theorem retainedRuleBodyImages_exact (definition : CalculusLanguageDef) : (RetainedWordExecution.WithOutput.Framed.untag (RuleNodeAdmission.selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)) = framedUntag := by
  funext value
  cases value <;> rfl

def retainedRuleBodyUntag (definition : CalculusLanguageDef) : (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (RuleNodeAdmission.selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).Λ → (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (RuleNodeAdmission.selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).Stmt :=
  homomorphicBody (retainedRuleBodyImages_exact definition)

theorem retainedRuleBodyUntag_exact (definition : CalculusLanguageDef) : retainedRuleBodyUntag definition = (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (RuleNodeAdmission.selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).m :=
  homomorphicBody_exact (retainedRuleBodyImages_exact definition)

def retainedRuleBodyTagged (definition : CalculusLanguageDef) : (RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Λ → (RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedMachine definition)).k₁ (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (RuleNodeAdmission.selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).k₀ (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (RuleNodeAdmission.selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).main (default : (Option Alphabet ⊕ Alphabet)) id
    (retainedRuleBodySaved definition) (retainedRuleBodyUntag definition))

theorem retainedRuleBodyTagged_exact (definition : CalculusLanguageDef) : retainedRuleBodyTagged definition = (RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).m := by
  unfold retainedRuleBodyTagged
  rw [retainedRuleBodySaved_exact, retainedRuleBodyUntag_exact]
  exact StackMachineComposition.body_eq (RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedMachine definition)) (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (RuleNodeAdmission.selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))) (Equiv.refl _)

local instance (definition : CalculusLanguageDef) : Fintype ((RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Γ (RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁) := inferInstanceAs (Fintype (Option Alphabet))

local instance (definition : CalculusLanguageDef) : Inhabited ((RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Γ (RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def retainedRuleBody (definition : CalculusLanguageDef) : (RuleNodeAdmission.retainedMachine definition).Λ → (RuleNodeAdmission.retainedMachine definition).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).k₀ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).main (default : (Option Alphabet)) id
    (retainedRuleBodyTagged definition) (WordTemplateMachine.program (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))))

theorem retainedRuleBody_exact (definition : CalculusLanguageDef) : retainedRuleBody definition = (RuleNodeAdmission.retainedMachine definition).m := by
  unfold retainedRuleBody
  rw [retainedRuleBodyTagged_exact]
  exact StackMachineComposition.body_eq (RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)) (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))) (Equiv.refl _)

def conclusionBody  : (RuleNodeAdmission.conclusionMachine).Λ → (RuleNodeAdmission.conclusionMachine).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Dispatch.Programs.body
    (CertificateDataTraversal.ProductField.machine true).k₀ (CertificateDataTraversal.ProductField.machine true).k₁ (CertificateDataTraversal.ProductField.machine true).initialState (CertificateDataTraversal.ProductField.machine true).main
    RuleInstantiationExecution.accept [(0 : Alphabet)] (productFieldBody true))

theorem conclusionBody_exact  : conclusionBody  = (RuleNodeAdmission.conclusionMachine).m := by
  unfold conclusionBody
  rw [productFieldBody_exact]
  exact (StackMachineComposition.Dispatch.Programs.body_eq _ _ _).symm

def conclusionSelectorBodyTable  : { instructions : (WordTemplateMachine.Indexed.machine RuleNodeAdmission.conclusionSelector).Λ → (WordTemplateMachine.Indexed.machine RuleNodeAdmission.conclusionSelector).Stmt // instructions = (WordTemplateMachine.Indexed.machine RuleNodeAdmission.conclusionSelector).m } := by
  extract_authored_program (WordTemplateMachine.Indexed.machine RuleNodeAdmission.conclusionSelector).m

def conclusionSelectorBody  := (conclusionSelectorBodyTable ).val

theorem conclusionSelectorBody_exact  : conclusionSelectorBody  = (WordTemplateMachine.Indexed.machine RuleNodeAdmission.conclusionSelector).m := (conclusionSelectorBodyTable ).property

local instance  : Fintype ((WordTemplateMachine.Indexed.machine RuleNodeAdmission.conclusionSelector).Γ (WordTemplateMachine.Indexed.machine RuleNodeAdmission.conclusionSelector).k₁) := inferInstanceAs (Fintype Alphabet)

local instance  : Inhabited ((WordTemplateMachine.Indexed.machine RuleNodeAdmission.conclusionSelector).Γ (WordTemplateMachine.Indexed.machine RuleNodeAdmission.conclusionSelector).k₁) := inferInstanceAs (Inhabited Alphabet)

def selectedConclusionBody  : (RuleNodeAdmission.selectedConclusionMachine).Λ → (RuleNodeAdmission.selectedConclusionMachine).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (WordTemplateMachine.Indexed.machine RuleNodeAdmission.conclusionSelector).k₁ (RuleNodeAdmission.conclusionMachine).k₀ (RuleNodeAdmission.conclusionMachine).main (default : Alphabet) id
    conclusionSelectorBody conclusionBody)

theorem selectedConclusionBody_exact  : selectedConclusionBody  = (RuleNodeAdmission.selectedConclusionMachine).m := by
  unfold selectedConclusionBody
  rw [conclusionSelectorBody_exact, conclusionBody_exact]
  exact StackMachineComposition.body_eq (WordTemplateMachine.Indexed.machine RuleNodeAdmission.conclusionSelector) (RuleNodeAdmission.conclusionMachine) (Equiv.refl _)

local instance  : Fintype ((RuleNodeAdmission.selectedConclusionMachine).Γ (RuleNodeAdmission.selectedConclusionMachine).k₁) := inferInstanceAs (Fintype Alphabet)

local instance  : Inhabited ((RuleNodeAdmission.selectedConclusionMachine).Γ (RuleNodeAdmission.selectedConclusionMachine).k₁) := inferInstanceAs (Inhabited Alphabet)

local instance  : Inhabited ((RuleNodeAdmission.selectedConclusionMachine).Γ (RuleNodeAdmission.selectedConclusionMachine).k₀) := inferInstanceAs (Inhabited (Option Alphabet))

def projectedRuleBodySaved  : (RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedConclusionMachine)).Λ →
    (RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedConclusionMachine)).Stmt := by
  authored_program_literal_endpoints (RetainedWordExecution.WithOutput.Programs.statement
    (RuleNodeAdmission.selectedConclusionMachine).k₀ (RuleNodeAdmission.selectedConclusionMachine).k₁ (none : Option Alphabet) (0 : Alphabet)
    (RuleNodeAdmission.selectedConclusionMachine).initialState (RuleNodeAdmission.selectedConclusionMachine).main selectedConclusionBody)

theorem projectedRuleBodySaved_exact  : projectedRuleBodySaved  = (RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedConclusionMachine)).m := by
  unfold projectedRuleBodySaved
  rw [selectedConclusionBody_exact]
  rfl

local instance  : Fintype ((RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedConclusionMachine)).Γ (RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedConclusionMachine)).k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Alphabet))

local instance  : Inhabited ((RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedConclusionMachine)).Γ (RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedConclusionMachine)).k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Alphabet))

theorem projectedRuleBodyImages_exact  : (RetainedWordExecution.WithOutput.Framed.untag (RuleNodeAdmission.selectedConclusionMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)) = framedUntag := by
  funext value
  cases value <;> rfl

def projectedRuleBodyUntag  : (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (RuleNodeAdmission.selectedConclusionMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).Λ → (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (RuleNodeAdmission.selectedConclusionMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).Stmt :=
  homomorphicBody (projectedRuleBodyImages_exact )

theorem projectedRuleBodyUntag_exact  : projectedRuleBodyUntag  = (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (RuleNodeAdmission.selectedConclusionMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).m :=
  homomorphicBody_exact (projectedRuleBodyImages_exact )

def projectedRuleBodyTagged  : (RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedConclusionMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Λ → (RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedConclusionMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedConclusionMachine)).k₁ (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (RuleNodeAdmission.selectedConclusionMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).k₀ (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (RuleNodeAdmission.selectedConclusionMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).main (default : (Option Alphabet ⊕ Alphabet)) id
    (projectedRuleBodySaved ) (projectedRuleBodyUntag ))

theorem projectedRuleBodyTagged_exact  : projectedRuleBodyTagged  = (RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedConclusionMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).m := by
  unfold projectedRuleBodyTagged
  rw [projectedRuleBodySaved_exact, projectedRuleBodyUntag_exact]
  exact StackMachineComposition.body_eq (RetainedWordExecution.WithOutput.machine (RuleNodeAdmission.selectedConclusionMachine)) (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (RuleNodeAdmission.selectedConclusionMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))) (Equiv.refl _)

local instance  : Fintype ((RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedConclusionMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Γ (RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedConclusionMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁) := inferInstanceAs (Fintype (Option Alphabet))

local instance  : Inhabited ((RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedConclusionMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Γ (RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedConclusionMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def projectedRuleBody  : (RuleNodeAdmission.projectedMachine).Λ → (RuleNodeAdmission.projectedMachine).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedConclusionMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).k₀ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).main (default : (Option Alphabet)) id
    (projectedRuleBodyTagged ) (WordTemplateMachine.program (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))))

theorem projectedRuleBody_exact  : projectedRuleBody  = (RuleNodeAdmission.projectedMachine).m := by
  unfold projectedRuleBody
  rw [projectedRuleBodyTagged_exact]
  exact StackMachineComposition.body_eq (RetainedWordExecution.WithOutput.Framed.taggedMachine (RuleNodeAdmission.selectedConclusionMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)) (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))) (Equiv.refl _)

def comparisonSelectorBodyTable  : { instructions : (WordTemplateMachine.Indexed.machine RuleNodeAdmission.Comparison.selector).Λ → (WordTemplateMachine.Indexed.machine RuleNodeAdmission.Comparison.selector).Stmt // instructions = (WordTemplateMachine.Indexed.machine RuleNodeAdmission.Comparison.selector).m } := by
  extract_authored_program (WordTemplateMachine.Indexed.machine RuleNodeAdmission.Comparison.selector).m

def comparisonSelectorBody  := (comparisonSelectorBodyTable ).val

theorem comparisonSelectorBody_exact  : comparisonSelectorBody  = (WordTemplateMachine.Indexed.machine RuleNodeAdmission.Comparison.selector).m := (comparisonSelectorBodyTable ).property

def equalityBodyTable  : { instructions : (WordEqualityMachine.machine Alphabet).Λ → (WordEqualityMachine.machine Alphabet).Stmt // instructions = (WordEqualityMachine.machine Alphabet).m } := by
  extract_authored_program (WordEqualityMachine.machine Alphabet).m

def equalityBody  := (equalityBodyTable ).val

theorem equalityBody_exact  : equalityBody  = (WordEqualityMachine.machine Alphabet).m := (equalityBodyTable ).property

local instance  : Fintype ((WordTemplateMachine.Indexed.machine RuleNodeAdmission.Comparison.selector).Γ (WordTemplateMachine.Indexed.machine RuleNodeAdmission.Comparison.selector).k₁) := inferInstanceAs (Fintype (Option Alphabet))

local instance  : Inhabited ((WordTemplateMachine.Indexed.machine RuleNodeAdmission.Comparison.selector).Γ (WordTemplateMachine.Indexed.machine RuleNodeAdmission.Comparison.selector).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def compareBody  : (RuleNodeAdmission.Comparison.compareMachine).Λ → (RuleNodeAdmission.Comparison.compareMachine).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (WordTemplateMachine.Indexed.machine RuleNodeAdmission.Comparison.selector).k₁ (WordEqualityMachine.machine Alphabet).k₀ (WordEqualityMachine.machine Alphabet).main (default : (Option Alphabet)) id
    comparisonSelectorBody equalityBody)

theorem compareBody_exact  : compareBody  = (RuleNodeAdmission.Comparison.compareMachine).m := by
  unfold compareBody
  rw [comparisonSelectorBody_exact, equalityBody_exact]
  exact StackMachineComposition.body_eq (WordTemplateMachine.Indexed.machine RuleNodeAdmission.Comparison.selector) (WordEqualityMachine.machine Alphabet) (Equiv.refl _)

local instance  : Fintype ((WordHomomorphismMachine.machine Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.EncodedTable.ReferenceCheck.liftSymbol).Γ (WordHomomorphismMachine.machine Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.EncodedTable.ReferenceCheck.liftSymbol).k₁) := inferInstanceAs (Fintype (Option (Option Alphabet)))

local instance  : Inhabited ((WordHomomorphismMachine.machine Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.EncodedTable.ReferenceCheck.liftSymbol).Γ (WordHomomorphismMachine.machine Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.EncodedTable.ReferenceCheck.liftSymbol).k₁) := inferInstanceAs (Inhabited (Option (Option Alphabet)))

def comparisonBody  : (RuleNodeAdmission.Comparison.machine).Λ → (RuleNodeAdmission.Comparison.machine).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (WordHomomorphismMachine.machine Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.EncodedTable.ReferenceCheck.liftSymbol).k₁ (RuleNodeAdmission.Comparison.compareMachine).k₀ (RuleNodeAdmission.Comparison.compareMachine).main (default : (Option (Option Alphabet))) id
    (WordHomomorphismMachine.program Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.EncodedTable.ReferenceCheck.liftSymbol) compareBody)

theorem comparisonBody_exact  : comparisonBody  = (RuleNodeAdmission.Comparison.machine).m := by
  unfold comparisonBody
  rw [compareBody_exact]
  exact StackMachineComposition.body_eq (WordHomomorphismMachine.machine Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.EncodedTable.ReferenceCheck.liftSymbol) (RuleNodeAdmission.Comparison.compareMachine) (Equiv.refl _)

local instance (definition : CalculusLanguageDef) : Fintype ((RuleNodeAdmission.retainedMachine definition).Γ (RuleNodeAdmission.retainedMachine definition).k₁) := inferInstanceAs (Fintype (Option Alphabet))

local instance (definition : CalculusLanguageDef) : Inhabited ((RuleNodeAdmission.retainedMachine definition).Γ (RuleNodeAdmission.retainedMachine definition).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def preparedRuleBody (definition : CalculusLanguageDef) : (RuleNodeAdmission.preparedMachine definition).Λ → (RuleNodeAdmission.preparedMachine definition).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (RuleNodeAdmission.retainedMachine definition).k₁ (RuleNodeAdmission.projectedMachine).k₀ (RuleNodeAdmission.projectedMachine).main (default : (Option Alphabet)) id
    (retainedRuleBody definition) projectedRuleBody)

theorem preparedRuleBody_exact (definition : CalculusLanguageDef) : preparedRuleBody definition = (RuleNodeAdmission.preparedMachine definition).m := by
  unfold preparedRuleBody
  rw [retainedRuleBody_exact, projectedRuleBody_exact]
  exact StackMachineComposition.body_eq (RuleNodeAdmission.retainedMachine definition) (RuleNodeAdmission.projectedMachine) (Equiv.refl _)

local instance (definition : CalculusLanguageDef) : Fintype ((RuleNodeAdmission.preparedMachine definition).Γ (RuleNodeAdmission.preparedMachine definition).k₁) := inferInstanceAs (Fintype (Option Alphabet))

local instance (definition : CalculusLanguageDef) : Inhabited ((RuleNodeAdmission.preparedMachine definition).Γ (RuleNodeAdmission.preparedMachine definition).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def ruleAdmissionBody (definition : CalculusLanguageDef) : (RuleNodeAdmission.machine definition).Λ → (RuleNodeAdmission.machine definition).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (RuleNodeAdmission.preparedMachine definition).k₁ (RuleNodeAdmission.Comparison.machine).k₀ (RuleNodeAdmission.Comparison.machine).main (default : (Option Alphabet)) id
    (preparedRuleBody definition) comparisonBody)

theorem ruleAdmissionBody_exact (definition : CalculusLanguageDef) : ruleAdmissionBody definition = (RuleNodeAdmission.machine definition).m := by
  unfold ruleAdmissionBody
  rw [preparedRuleBody_exact, comparisonBody_exact]
  exact StackMachineComposition.body_eq (RuleNodeAdmission.preparedMachine definition) (RuleNodeAdmission.Comparison.machine) (Equiv.refl _)

def nodeFieldBodyTable  : { instructions : (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.nodeSelector).Λ → (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.nodeSelector).Stmt // instructions = (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.nodeSelector).m } := by
  extract_authored_program (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.nodeSelector).m

def nodeFieldBody  := (nodeFieldBodyTable ).val

theorem nodeFieldBody_exact  : nodeFieldBody  = (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.nodeSelector).m := (nodeFieldBodyTable ).property

local instance  : Fintype ((FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.nodeSelector).Γ (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.nodeSelector).k₁) := inferInstanceAs (Fintype (Option Alphabet))

local instance  : Inhabited ((FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.nodeSelector).Γ (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.nodeSelector).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def selectedNodeBody (definition : CalculusLanguageDef) : (NodeChildrenExecution.selectedNodeMachine definition).Λ → (NodeChildrenExecution.selectedNodeMachine definition).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.nodeSelector).k₁ (RuleNodeAdmission.machine definition).k₀ (RuleNodeAdmission.machine definition).main (default : (Option Alphabet)) id
    nodeFieldBody (ruleAdmissionBody definition))

theorem selectedNodeBody_exact (definition : CalculusLanguageDef) : selectedNodeBody definition = (NodeChildrenExecution.selectedNodeMachine definition).m := by
  unfold selectedNodeBody
  rw [nodeFieldBody_exact, ruleAdmissionBody_exact]
  exact StackMachineComposition.body_eq (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.nodeSelector) (RuleNodeAdmission.machine definition) (Equiv.refl _)

local instance (definition : CalculusLanguageDef) : Fintype ((NodeChildrenExecution.selectedNodeMachine definition).Γ (NodeChildrenExecution.selectedNodeMachine definition).k₁) := inferInstanceAs (Fintype Bool)

local instance (definition : CalculusLanguageDef) : Inhabited ((NodeChildrenExecution.selectedNodeMachine definition).Γ (NodeChildrenExecution.selectedNodeMachine definition).k₁) := inferInstanceAs (Inhabited Bool)

local instance (definition : CalculusLanguageDef) : Inhabited ((NodeChildrenExecution.selectedNodeMachine definition).Γ
    (NodeChildrenExecution.selectedNodeMachine definition).k₀) := inferInstanceAs (Inhabited (Option Alphabet))

def savedNodeBody (definition : CalculusLanguageDef) : (NodeChildrenExecution.savedNodeMachine definition).Λ →
    (NodeChildrenExecution.savedNodeMachine definition).Stmt := by
  authored_program_literal_endpoints (RetainedWordExecution.Programs.body
    (NodeChildrenExecution.selectedNodeMachine definition).k₀ (NodeChildrenExecution.selectedNodeMachine definition).k₁
    (NodeChildrenExecution.selectedNodeMachine definition).initialState (NodeChildrenExecution.selectedNodeMachine definition).main
    (none : Option Alphabet) false id (selectedNodeBody definition))

theorem savedNodeBody_exact (definition : CalculusLanguageDef) : savedNodeBody definition =
    (NodeChildrenExecution.savedNodeMachine definition).m := by
  unfold savedNodeBody
  rw [selectedNodeBody_exact]
  exact RetainedWordExecution.Programs.body_eq _ _

local instance (definition : CalculusLanguageDef) : Fintype ((NodeChildrenExecution.savedNodeMachine definition).Γ (NodeChildrenExecution.savedNodeMachine definition).k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Bool))

local instance (definition : CalculusLanguageDef) : Inhabited ((NodeChildrenExecution.savedNodeMachine definition).Γ (NodeChildrenExecution.savedNodeMachine definition).k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Bool))

def testedNodeBody (definition : CalculusLanguageDef) : (NodeChildrenExecution.testedNodeMachine definition).Λ → (NodeChildrenExecution.testedNodeMachine definition).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (NodeChildrenExecution.savedNodeMachine definition).k₁ (WordHomomorphismMachine.machine NodeChildrenExecution.statusCell).k₀ (WordHomomorphismMachine.machine NodeChildrenExecution.statusCell).main (default : (Option Alphabet ⊕ Bool)) id
    (savedNodeBody definition) (WordHomomorphismMachine.program NodeChildrenExecution.statusCell))

theorem testedNodeBody_exact (definition : CalculusLanguageDef) : testedNodeBody definition = (NodeChildrenExecution.testedNodeMachine definition).m := by
  unfold testedNodeBody
  rw [savedNodeBody_exact]
  exact StackMachineComposition.body_eq (NodeChildrenExecution.savedNodeMachine definition) (WordHomomorphismMachine.machine NodeChildrenExecution.statusCell) (Equiv.refl _)

def instanceSelectorBodyTable  : { instructions : (WordTemplateMachine.Indexed.machine NodeChildrenExecution.instanceSelector).Λ → (WordTemplateMachine.Indexed.machine NodeChildrenExecution.instanceSelector).Stmt // instructions = (WordTemplateMachine.Indexed.machine NodeChildrenExecution.instanceSelector).m } := by
  extract_authored_program (WordTemplateMachine.Indexed.machine NodeChildrenExecution.instanceSelector).m

def instanceSelectorBody  := (instanceSelectorBodyTable ).val

theorem instanceSelectorBody_exact  : instanceSelectorBody  = (WordTemplateMachine.Indexed.machine NodeChildrenExecution.instanceSelector).m := (instanceSelectorBodyTable ).property

local instance  : Fintype ((WordTemplateMachine.Indexed.machine NodeChildrenExecution.instanceSelector).Γ (WordTemplateMachine.Indexed.machine NodeChildrenExecution.instanceSelector).k₁) := inferInstanceAs (Fintype Alphabet)

local instance  : Inhabited ((WordTemplateMachine.Indexed.machine NodeChildrenExecution.instanceSelector).Γ (WordTemplateMachine.Indexed.machine NodeChildrenExecution.instanceSelector).k₁) := inferInstanceAs (Inhabited Alphabet)

def selectedInstantiationBody (definition : CalculusLanguageDef) : (NodeChildrenExecution.selectedInstantiationMachine definition).Λ → (NodeChildrenExecution.selectedInstantiationMachine definition).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (WordTemplateMachine.Indexed.machine NodeChildrenExecution.instanceSelector).k₁ (RuleInstantiationExecution.machine definition).k₀ (RuleInstantiationExecution.machine definition).main (default : Alphabet) id
    instanceSelectorBody (instantiationBody definition))

theorem selectedInstantiationBody_exact (definition : CalculusLanguageDef) : selectedInstantiationBody definition = (NodeChildrenExecution.selectedInstantiationMachine definition).m := by
  unfold selectedInstantiationBody
  rw [instanceSelectorBody_exact, instantiationBody_exact]
  exact StackMachineComposition.body_eq (WordTemplateMachine.Indexed.machine NodeChildrenExecution.instanceSelector) (RuleInstantiationExecution.machine definition) (Equiv.refl _)

def premiseBody  : (NodeChildrenExecution.premiseMachine).Λ → (NodeChildrenExecution.premiseMachine).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Dispatch.Programs.body
    (CertificateDataTraversal.ProductField.machine false).k₀ (CertificateDataTraversal.ProductField.machine false).k₁ (CertificateDataTraversal.ProductField.machine false).initialState (CertificateDataTraversal.ProductField.machine false).main
    RuleInstantiationExecution.accept [(0 : Alphabet)] (productFieldBody false))

theorem premiseBody_exact  : premiseBody  = (NodeChildrenExecution.premiseMachine).m := by
  unfold premiseBody
  rw [productFieldBody_exact]
  exact (StackMachineComposition.Dispatch.Programs.body_eq _ _ _).symm

local instance (definition : CalculusLanguageDef) : Fintype ((NodeChildrenExecution.selectedInstantiationMachine definition).Γ (NodeChildrenExecution.selectedInstantiationMachine definition).k₁) := inferInstanceAs (Fintype Alphabet)

local instance (definition : CalculusLanguageDef) : Inhabited ((NodeChildrenExecution.selectedInstantiationMachine definition).Γ (NodeChildrenExecution.selectedInstantiationMachine definition).k₁) := inferInstanceAs (Inhabited Alphabet)

def selectedPremiseBody (definition : CalculusLanguageDef) : (NodeChildrenExecution.selectedPremiseMachine definition).Λ → (NodeChildrenExecution.selectedPremiseMachine definition).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (NodeChildrenExecution.selectedInstantiationMachine definition).k₁ (NodeChildrenExecution.premiseMachine).k₀ (NodeChildrenExecution.premiseMachine).main (default : Alphabet) id
    (selectedInstantiationBody definition) premiseBody)

theorem selectedPremiseBody_exact (definition : CalculusLanguageDef) : selectedPremiseBody definition = (NodeChildrenExecution.selectedPremiseMachine definition).m := by
  unfold selectedPremiseBody
  rw [selectedInstantiationBody_exact, premiseBody_exact]
  exact StackMachineComposition.body_eq (NodeChildrenExecution.selectedInstantiationMachine definition) (NodeChildrenExecution.premiseMachine) (Equiv.refl _)

local instance (definition : CalculusLanguageDef) : Fintype ((NodeChildrenExecution.selectedPremiseMachine definition).Γ (NodeChildrenExecution.selectedPremiseMachine definition).k₁) := inferInstanceAs (Fintype Alphabet)

local instance (definition : CalculusLanguageDef) : Inhabited ((NodeChildrenExecution.selectedPremiseMachine definition).Γ (NodeChildrenExecution.selectedPremiseMachine definition).k₁) := inferInstanceAs (Inhabited Alphabet)

local instance (definition : CalculusLanguageDef) : Inhabited ((NodeChildrenExecution.selectedPremiseMachine definition).Γ (NodeChildrenExecution.selectedPremiseMachine definition).k₀) := inferInstanceAs (Inhabited (Option Alphabet))

def retainedPremiseBodySaved (definition : CalculusLanguageDef) : (RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedPremiseMachine definition)).Λ →
    (RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedPremiseMachine definition)).Stmt := by
  authored_program_literal_endpoints (RetainedWordExecution.WithOutput.Programs.statement
    (NodeChildrenExecution.selectedPremiseMachine definition).k₀ (NodeChildrenExecution.selectedPremiseMachine definition).k₁ (none : Option Alphabet) (0 : Alphabet)
    (NodeChildrenExecution.selectedPremiseMachine definition).initialState (NodeChildrenExecution.selectedPremiseMachine definition).main (selectedPremiseBody definition))

theorem retainedPremiseBodySaved_exact (definition : CalculusLanguageDef) : retainedPremiseBodySaved definition = (RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedPremiseMachine definition)).m := by
  unfold retainedPremiseBodySaved
  rw [selectedPremiseBody_exact]
  rfl

theorem retainedPremiseBodyImages_exact (definition : CalculusLanguageDef) : (RetainedWordExecution.WithOutput.Framed.untag (NodeChildrenExecution.selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)) = framedUntag := by
  funext value
  cases value <;> rfl

def retainedPremiseBodyUntag (definition : CalculusLanguageDef) : (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (NodeChildrenExecution.selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).Λ → (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (NodeChildrenExecution.selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).Stmt := homomorphicBody (retainedPremiseBodyImages_exact definition)

theorem retainedPremiseBodyUntag_exact (definition : CalculusLanguageDef) : retainedPremiseBodyUntag definition = (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (NodeChildrenExecution.selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).m := homomorphicBody_exact (retainedPremiseBodyImages_exact definition)

local instance (definition : CalculusLanguageDef) : Fintype ((RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedPremiseMachine definition)).Γ (RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedPremiseMachine definition)).k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Alphabet))

local instance (definition : CalculusLanguageDef) : Inhabited ((RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedPremiseMachine definition)).Γ (RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedPremiseMachine definition)).k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Alphabet))

def retainedPremiseBodyTagged (definition : CalculusLanguageDef) : (RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Λ → (RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedPremiseMachine definition)).k₁ (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (NodeChildrenExecution.selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).k₀ (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (NodeChildrenExecution.selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).main (default : (Option Alphabet ⊕ Alphabet)) id
    (retainedPremiseBodySaved definition) (retainedPremiseBodyUntag definition))

theorem retainedPremiseBodyTagged_exact (definition : CalculusLanguageDef) : retainedPremiseBodyTagged definition = (RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).m := by
  unfold retainedPremiseBodyTagged
  rw [retainedPremiseBodySaved_exact, retainedPremiseBodyUntag_exact]
  exact StackMachineComposition.body_eq (RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedPremiseMachine definition)) (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (NodeChildrenExecution.selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))) (Equiv.refl _)

local instance (definition : CalculusLanguageDef) : Fintype ((RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Γ (RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁) := inferInstanceAs (Fintype (Option Alphabet))

local instance (definition : CalculusLanguageDef) : Inhabited ((RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Γ (RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def retainedPremiseBody (definition : CalculusLanguageDef) : (NodeChildrenExecution.retainedPremiseMachine definition).Λ → (NodeChildrenExecution.retainedPremiseMachine definition).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).k₀ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).main (default : (Option Alphabet)) id
    (retainedPremiseBodyTagged definition) (WordTemplateMachine.program (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))))

theorem retainedPremiseBody_exact (definition : CalculusLanguageDef) : retainedPremiseBody definition = (NodeChildrenExecution.retainedPremiseMachine definition).m := by
  unfold retainedPremiseBody
  rw [retainedPremiseBodyTagged_exact]
  exact StackMachineComposition.body_eq (RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedPremiseMachine definition) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)) (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))) (Equiv.refl _)

def identityBody : NodeChildrenExecution.rawIdentity.Λ → NodeChildrenExecution.rawIdentity.Stmt :=
  WordHomomorphismMachine.program (fun value : Alphabet => [value])

theorem identityBody_exact : identityBody = NodeChildrenExecution.rawIdentity.m := rfl

def stripBody  : (NodeChildrenExecution.stripMachine).Λ → (NodeChildrenExecution.stripMachine).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Dispatch.Programs.body
    (NodeChildrenExecution.rawIdentity).k₀ (NodeChildrenExecution.rawIdentity).k₁ (NodeChildrenExecution.rawIdentity).initialState (NodeChildrenExecution.rawIdentity).main
    RuleInstantiationExecution.accept [(0 : Alphabet)] identityBody)

theorem stripBody_exact  : stripBody  = (NodeChildrenExecution.stripMachine).m := by
  unfold stripBody
  rw [identityBody_exact]
  exact (StackMachineComposition.Dispatch.Programs.body_eq _ _ _).symm

def responseSelectorBodyTable  : { instructions : (WordTemplateMachine.Indexed.machine NodeChildrenExecution.responseSelector).Λ → (WordTemplateMachine.Indexed.machine NodeChildrenExecution.responseSelector).Stmt // instructions = (WordTemplateMachine.Indexed.machine NodeChildrenExecution.responseSelector).m } := by
  extract_authored_program (WordTemplateMachine.Indexed.machine NodeChildrenExecution.responseSelector).m

def responseSelectorBody  := (responseSelectorBodyTable ).val

theorem responseSelectorBody_exact  : responseSelectorBody  = (WordTemplateMachine.Indexed.machine NodeChildrenExecution.responseSelector).m := (responseSelectorBodyTable ).property

local instance  : Fintype ((WordTemplateMachine.Indexed.machine NodeChildrenExecution.responseSelector).Γ (WordTemplateMachine.Indexed.machine NodeChildrenExecution.responseSelector).k₁) := inferInstanceAs (Fintype Alphabet)

local instance  : Inhabited ((WordTemplateMachine.Indexed.machine NodeChildrenExecution.responseSelector).Γ (WordTemplateMachine.Indexed.machine NodeChildrenExecution.responseSelector).k₁) := inferInstanceAs (Inhabited Alphabet)

def selectedStripBody  : (NodeChildrenExecution.selectedStripMachine).Λ → (NodeChildrenExecution.selectedStripMachine).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (WordTemplateMachine.Indexed.machine NodeChildrenExecution.responseSelector).k₁ (NodeChildrenExecution.stripMachine).k₀ (NodeChildrenExecution.stripMachine).main (default : Alphabet) id
    responseSelectorBody stripBody)

theorem selectedStripBody_exact  : selectedStripBody  = (NodeChildrenExecution.selectedStripMachine).m := by
  unfold selectedStripBody
  rw [responseSelectorBody_exact, stripBody_exact]
  exact StackMachineComposition.body_eq (WordTemplateMachine.Indexed.machine NodeChildrenExecution.responseSelector) (NodeChildrenExecution.stripMachine) (Equiv.refl _)

local instance  : Fintype ((NodeChildrenExecution.selectedStripMachine).Γ (NodeChildrenExecution.selectedStripMachine).k₁) := inferInstanceAs (Fintype Alphabet)

local instance  : Inhabited ((NodeChildrenExecution.selectedStripMachine).Γ (NodeChildrenExecution.selectedStripMachine).k₁) := inferInstanceAs (Inhabited Alphabet)

local instance  : Inhabited ((NodeChildrenExecution.selectedStripMachine).Γ (NodeChildrenExecution.selectedStripMachine).k₀) := inferInstanceAs (Inhabited (Option Alphabet))

def retainedStripBodySaved  : (RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedStripMachine)).Λ →
    (RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedStripMachine)).Stmt := by
  authored_program_literal_endpoints (RetainedWordExecution.WithOutput.Programs.statement
    (NodeChildrenExecution.selectedStripMachine).k₀ (NodeChildrenExecution.selectedStripMachine).k₁ (none : Option Alphabet) (0 : Alphabet)
    (NodeChildrenExecution.selectedStripMachine).initialState (NodeChildrenExecution.selectedStripMachine).main selectedStripBody)

theorem retainedStripBodySaved_exact  : retainedStripBodySaved  = (RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedStripMachine)).m := by
  unfold retainedStripBodySaved
  rw [selectedStripBody_exact]
  rfl

theorem retainedStripBodyImages_exact  : (RetainedWordExecution.WithOutput.Framed.untag (NodeChildrenExecution.selectedStripMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)) = framedUntag := by
  funext value
  cases value <;> rfl

def retainedStripBodyUntag  : (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (NodeChildrenExecution.selectedStripMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).Λ → (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (NodeChildrenExecution.selectedStripMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).Stmt := homomorphicBody (retainedStripBodyImages_exact )

theorem retainedStripBodyUntag_exact  : retainedStripBodyUntag  = (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (NodeChildrenExecution.selectedStripMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).m := homomorphicBody_exact (retainedStripBodyImages_exact )

local instance  : Fintype ((RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedStripMachine)).Γ (RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedStripMachine)).k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Alphabet))

local instance  : Inhabited ((RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedStripMachine)).Γ (RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedStripMachine)).k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Alphabet))

def retainedStripBodyTagged  : (RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedStripMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Λ → (RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedStripMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedStripMachine)).k₁ (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (NodeChildrenExecution.selectedStripMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).k₀ (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (NodeChildrenExecution.selectedStripMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).main (default : (Option Alphabet ⊕ Alphabet)) id
    (retainedStripBodySaved ) (retainedStripBodyUntag ))

theorem retainedStripBodyTagged_exact  : retainedStripBodyTagged  = (RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedStripMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).m := by
  unfold retainedStripBodyTagged
  rw [retainedStripBodySaved_exact, retainedStripBodyUntag_exact]
  exact StackMachineComposition.body_eq (RetainedWordExecution.WithOutput.machine (NodeChildrenExecution.selectedStripMachine)) (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (NodeChildrenExecution.selectedStripMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))) (Equiv.refl _)

local instance  : Fintype ((RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedStripMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Γ (RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedStripMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁) := inferInstanceAs (Fintype (Option Alphabet))

local instance  : Inhabited ((RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedStripMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Γ (RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedStripMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def retainedStripBody  : (NodeChildrenExecution.retainedStripMachine).Λ → (NodeChildrenExecution.retainedStripMachine).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedStripMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).k₀ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).main (default : (Option Alphabet)) id
    (retainedStripBodyTagged ) (WordTemplateMachine.program (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))))

theorem retainedStripBody_exact  : retainedStripBody  = (NodeChildrenExecution.retainedStripMachine).m := by
  unfold retainedStripBody
  rw [retainedStripBodyTagged_exact]
  exact StackMachineComposition.body_eq (RetainedWordExecution.WithOutput.Framed.taggedMachine (NodeChildrenExecution.selectedStripMachine) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)) (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))) (Equiv.refl _)

local instance (definition : CalculusLanguageDef) : Fintype ((NodeChildrenExecution.retainedPremiseMachine definition).Γ (NodeChildrenExecution.retainedPremiseMachine definition).k₁) := inferInstanceAs (Fintype (Option Alphabet))

local instance (definition : CalculusLanguageDef) : Inhabited ((NodeChildrenExecution.retainedPremiseMachine definition).Γ (NodeChildrenExecution.retainedPremiseMachine definition).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def preparedPremiseBody (definition : CalculusLanguageDef) : (NodeChildrenExecution.preparedPremiseMachine definition).Λ → (NodeChildrenExecution.preparedPremiseMachine definition).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (NodeChildrenExecution.retainedPremiseMachine definition).k₁ (NodeChildrenExecution.retainedStripMachine).k₀ (NodeChildrenExecution.retainedStripMachine).main (default : (Option Alphabet)) id
    (retainedPremiseBody definition) retainedStripBody)

theorem preparedPremiseBody_exact (definition : CalculusLanguageDef) : preparedPremiseBody definition = (NodeChildrenExecution.preparedPremiseMachine definition).m := by
  unfold preparedPremiseBody
  rw [retainedPremiseBody_exact, retainedStripBody_exact]
  exact StackMachineComposition.body_eq (NodeChildrenExecution.retainedPremiseMachine definition) (NodeChildrenExecution.retainedStripMachine) (Equiv.refl _)

def childSelectorBodyTable  : { instructions : (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.childSelector).Λ → (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.childSelector).Stmt // instructions = (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.childSelector).m } := by
  extract_authored_program (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.childSelector).m

def childSelectorBody  := (childSelectorBodyTable ).val

theorem childSelectorBody_exact  : childSelectorBody  = (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.childSelector).m := (childSelectorBodyTable ).property

local instance  : Fintype ((FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.childSelector).Γ (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.childSelector).k₁) := inferInstanceAs (Fintype (Option Alphabet))

local instance  : Inhabited ((FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.childSelector).Γ (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.childSelector).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def selectedChildrenBody (arity : Nat) : (NodeChildrenExecution.selectedChildrenMachine arity).Λ → (NodeChildrenExecution.selectedChildrenMachine arity).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.childSelector).k₁ (OriginalChildJobs.machine arity).k₀ (OriginalChildJobs.machine arity).main (default : (Option Alphabet)) id
    childSelectorBody (OriginalChildJobs.Program.body arity))

theorem selectedChildrenBody_exact (arity : Nat) : selectedChildrenBody arity = (NodeChildrenExecution.selectedChildrenMachine arity).m := by
  unfold selectedChildrenBody
  rw [childSelectorBody_exact, OriginalChildJobs.Program.body_exact]
  exact StackMachineComposition.body_eq (FramedFieldSelection.machine (Γ := Alphabet) NodeChildrenExecution.childSelector) (OriginalChildJobs.machine arity) (Equiv.refl _)

local instance (definition : CalculusLanguageDef)  : Fintype ((NodeChildrenExecution.preparedPremiseMachine definition).Γ (NodeChildrenExecution.preparedPremiseMachine definition).k₁) := inferInstanceAs (Fintype (Option Alphabet))

local instance (definition : CalculusLanguageDef)  : Inhabited ((NodeChildrenExecution.preparedPremiseMachine definition).Γ (NodeChildrenExecution.preparedPremiseMachine definition).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def payloadBody (definition : CalculusLanguageDef) (arity : Nat) : (NodeChildrenExecution.payloadMachine definition arity).Λ → (NodeChildrenExecution.payloadMachine definition arity).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (NodeChildrenExecution.preparedPremiseMachine definition).k₁ (NodeChildrenExecution.selectedChildrenMachine arity).k₀ (NodeChildrenExecution.selectedChildrenMachine arity).main (default : (Option Alphabet)) id
    (preparedPremiseBody definition) (selectedChildrenBody arity))

theorem payloadBody_exact (definition : CalculusLanguageDef) (arity : Nat) : payloadBody definition arity = (NodeChildrenExecution.payloadMachine definition arity).m := by
  unfold payloadBody
  rw [preparedPremiseBody_exact, selectedChildrenBody_exact]
  exact StackMachineComposition.body_eq (NodeChildrenExecution.preparedPremiseMachine definition) (NodeChildrenExecution.selectedChildrenMachine arity) (Equiv.refl _)

local instance : Inhabited OriginalChildJobs.PairCell := ⟨.inr false⟩
local instance (definition : CalculusLanguageDef) (arity : Nat) : Inhabited ((NodeChildrenExecution.payloadMachine definition arity).Γ
    (NodeChildrenExecution.payloadMachine definition arity).k₀) := inferInstanceAs (Inhabited (Option Alphabet))

def guardedNodeBody (definition : CalculusLanguageDef) (arity : Nat) : (NodeChildrenExecution.guardedMachine definition arity).Λ → (NodeChildrenExecution.guardedMachine definition arity).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Dispatch.Programs.body
    (NodeChildrenExecution.payloadMachine definition arity).k₀ (NodeChildrenExecution.payloadMachine definition arity).k₁ (NodeChildrenExecution.payloadMachine definition arity).initialState (NodeChildrenExecution.payloadMachine definition arity).main
    NodeChildrenExecution.accepted [(.inr false : OriginalChildJobs.PairCell)] (payloadBody definition arity))

theorem guardedNodeBody_exact (definition : CalculusLanguageDef) (arity : Nat) : guardedNodeBody definition arity = (NodeChildrenExecution.guardedMachine definition arity).m := by
  unfold guardedNodeBody
  rw [payloadBody_exact]
  exact (StackMachineComposition.Dispatch.Programs.body_eq _ _ _).symm

local instance (definition : CalculusLanguageDef)  : Fintype ((NodeChildrenExecution.testedNodeMachine definition).Γ (NodeChildrenExecution.testedNodeMachine definition).k₁) := inferInstanceAs (Fintype (Option Alphabet))

local instance (definition : CalculusLanguageDef)  : Inhabited ((NodeChildrenExecution.testedNodeMachine definition).Γ (NodeChildrenExecution.testedNodeMachine definition).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def nodeBody (definition : CalculusLanguageDef) (arity : Nat) : (NodeChildrenExecution.machine definition arity).Λ → (NodeChildrenExecution.machine definition arity).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (NodeChildrenExecution.testedNodeMachine definition).k₁ (NodeChildrenExecution.guardedMachine definition arity).k₀ (NodeChildrenExecution.guardedMachine definition arity).main (default : (Option Alphabet)) id
    (testedNodeBody definition) (guardedNodeBody definition arity))

theorem nodeBody_exact (definition : CalculusLanguageDef) (arity : Nat) : nodeBody definition arity = (NodeChildrenExecution.machine definition arity).m := by
  unfold nodeBody
  rw [testedNodeBody_exact, guardedNodeBody_exact]
  exact StackMachineComposition.body_eq (NodeChildrenExecution.testedNodeMachine definition) (NodeChildrenExecution.guardedMachine definition arity) (Equiv.refl _)

def selectionSelectorBodyTable  : { instructions : (WordTemplateMachine.Indexed.machine AuthoredNodeDispatch.Selection.instanceSelector).Λ → (WordTemplateMachine.Indexed.machine AuthoredNodeDispatch.Selection.instanceSelector).Stmt // instructions = (WordTemplateMachine.Indexed.machine AuthoredNodeDispatch.Selection.instanceSelector).m } := by
  extract_authored_program (WordTemplateMachine.Indexed.machine AuthoredNodeDispatch.Selection.instanceSelector).m

def selectionSelectorBody  := (selectionSelectorBodyTable ).val

theorem selectionSelectorBody_exact  : selectionSelectorBody  = (WordTemplateMachine.Indexed.machine AuthoredNodeDispatch.Selection.instanceSelector).m := (selectionSelectorBodyTable ).property

local instance  : Fintype ((WordTemplateMachine.Indexed.machine AuthoredNodeDispatch.Selection.instanceSelector).Γ (WordTemplateMachine.Indexed.machine AuthoredNodeDispatch.Selection.instanceSelector).k₁) := inferInstanceAs (Fintype Alphabet)

local instance  : Inhabited ((WordTemplateMachine.Indexed.machine AuthoredNodeDispatch.Selection.instanceSelector).Γ (WordTemplateMachine.Indexed.machine AuthoredNodeDispatch.Selection.instanceSelector).k₁) := inferInstanceAs (Inhabited Alphabet)

def selectedLookupBody (definition : CalculusLanguageDef) : (AuthoredNodeDispatch.Selection.selectedMachine definition).Λ → (AuthoredNodeDispatch.Selection.selectedMachine definition).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (WordTemplateMachine.Indexed.machine AuthoredNodeDispatch.Selection.instanceSelector).k₁ (CertificateRuleAdmission.machine definition).k₀ (CertificateRuleAdmission.machine definition).main (default : Alphabet) id
    selectionSelectorBody (lookupBody definition))

theorem selectedLookupBody_exact (definition : CalculusLanguageDef) : selectedLookupBody definition = (AuthoredNodeDispatch.Selection.selectedMachine definition).m := by
  unfold selectedLookupBody
  rw [selectionSelectorBody_exact, lookupBody_exact]
  exact StackMachineComposition.body_eq (WordTemplateMachine.Indexed.machine AuthoredNodeDispatch.Selection.instanceSelector) (CertificateRuleAdmission.machine definition) (Equiv.refl _)

local instance (definition : CalculusLanguageDef) : Fintype ((AuthoredNodeDispatch.Selection.selectedMachine definition).Γ (AuthoredNodeDispatch.Selection.selectedMachine definition).k₁) := inferInstanceAs (Fintype (Alphabet ⊕ Option (Row definition)))

local instance (definition : CalculusLanguageDef) : Inhabited ((AuthoredNodeDispatch.Selection.selectedMachine definition).Γ (AuthoredNodeDispatch.Selection.selectedMachine definition).k₁) := inferInstanceAs (Inhabited (Alphabet ⊕ Option (Row definition)))

local instance (definition : CalculusLanguageDef) : Inhabited ((AuthoredNodeDispatch.Selection.selectedMachine definition).Γ
    (AuthoredNodeDispatch.Selection.selectedMachine definition).k₀) := inferInstanceAs (Inhabited (Option Alphabet))

def selectionBody (definition : CalculusLanguageDef) : (AuthoredNodeDispatch.Selection.machine definition).Λ →
    (AuthoredNodeDispatch.Selection.machine definition).Stmt := by
  authored_program_literal_endpoints (RetainedWordExecution.Programs.body
    (AuthoredNodeDispatch.Selection.selectedMachine definition).k₀ (AuthoredNodeDispatch.Selection.selectedMachine definition).k₁
    (AuthoredNodeDispatch.Selection.selectedMachine definition).initialState (AuthoredNodeDispatch.Selection.selectedMachine definition).main
    (none : Option Alphabet) (none : Option (Row definition))
    (CertificateRuleAdmission.ScopedApplication.readSelected definition) (selectedLookupBody definition))

theorem selectionBody_exact (definition : CalculusLanguageDef) : selectionBody definition =
    (AuthoredNodeDispatch.Selection.machine definition).m := by
  unfold selectionBody
  rw [selectedLookupBody_exact]
  exact RetainedWordExecution.Programs.body_eq _ _

def nodeMains (definition : CalculusLanguageDef) : ∀ index, (family definition).Label index := by
  authored_program_literal_endpoints (fun index => (NodeChildrenExecution.machine definition (premiseArity definition index)).main)

def nodeInitial (definition : CalculusLanguageDef) : (Base definition).σ := by
  authored_program_literal_endpoints (Base definition).initialState

theorem nodeInitial_exact (definition : CalculusLanguageDef) : nodeInitial definition = (Base definition).initialState := rfl

def dispatcherBody (definition : CalculusLanguageDef) : (AuthoredNodeDispatch.dispatcher definition).Λ →
    (AuthoredNodeDispatch.dispatcher definition).Stmt := by
  authored_program_literal_endpoints (CommonArenaDispatch.Programs.body (Base definition) (family definition)
    (CommonArenaDispatch.baseKey (Base definition) (Base definition).k₀)
    (CommonArenaDispatch.baseKey (Base definition) (Base definition).k₁)
    rfl rfl (nodeInitial definition) (nodeMains definition)
    (fun index => nodeBody definition (premiseArity definition index))
    (none : Option Alphabet) (.inr false : PairCell))

theorem dispatcherBody_exact (definition : CalculusLanguageDef) : dispatcherBody definition =
    (AuthoredNodeDispatch.dispatcher definition).m := by
  have source : (fun index => nodeBody definition (premiseArity definition index)) = (family definition).body := by
    funext index
    exact nodeBody_exact _ _
  unfold dispatcherBody
  rw [source]
  rfl

local instance (definition : CalculusLanguageDef) : Fintype ((AuthoredNodeDispatch.Selection.machine definition).Γ (AuthoredNodeDispatch.Selection.machine definition).k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Option (Row definition)))

local instance (definition : CalculusLanguageDef) : Inhabited ((AuthoredNodeDispatch.Selection.machine definition).Γ (AuthoredNodeDispatch.Selection.machine definition).k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Option (Row definition)))

def body (definition : CalculusLanguageDef) : (target definition).Λ → (target definition).Stmt := by
  authored_program_literal_endpoints (StackMachineComposition.Programs.body
    (AuthoredNodeDispatch.Selection.machine definition).k₁ (AuthoredNodeDispatch.dispatcher definition).k₀ (AuthoredNodeDispatch.dispatcher definition).main (default : (Option Alphabet ⊕ Option (Row definition))) id
    (selectionBody definition) (dispatcherBody definition))

theorem body_exact (definition : CalculusLanguageDef) : body definition = (target definition).m := by
  unfold body
  rw [selectionBody_exact, dispatcherBody_exact]
  exact StackMachineComposition.body_eq (AuthoredNodeDispatch.Selection.machine definition) (AuthoredNodeDispatch.dispatcher definition) (Equiv.refl _)

def keyEquality (definition : CalculusLanguageDef) : DecidableEq (target definition).K := by
  claim_program_key_equality

local instance (definition : CalculusLanguageDef) : DecidableEq (target definition).K := keyEquality definition

def registerEquality (definition : CalculusLanguageDef) : DecidableEq (target definition).σ := by
  claim_program_key_equality

def step (definition : CalculusLanguageDef) : (target definition).Cfg → Option (target definition).Cfg :=
  @TM2.step (target definition).K (target definition).Γ (target definition).Λ (target definition).σ
    (keyEquality definition) (body definition)

theorem step_exact (definition : CalculusLanguageDef) : step definition = (target definition).step := by
  unfold step
  rw [show keyEquality definition = (target definition).kDecidableEq from Subsingleton.elim _ _, body_exact]
  rfl

def inputKey (definition : CalculusLanguageDef) : (target definition).K := by
  authored_program_literal_endpoints (target definition).k₀

def resultKey (definition : CalculusLanguageDef) : (target definition).K := by
  authored_program_literal_endpoints (target definition).k₁

def mainLabel (definition : CalculusLanguageDef) : (target definition).Λ := by
  authored_program_literal_endpoints (target definition).main

def registers (definition : CalculusLanguageDef) : (target definition).σ := by
  authored_program_literal_endpoints (target definition).initialState

theorem inputKey_exact (definition : CalculusLanguageDef) : inputKey definition = (target definition).k₀ := rfl
theorem resultKey_exact (definition : CalculusLanguageDef) : resultKey definition = (target definition).k₁ := rfl
theorem mainLabel_exact (definition : CalculusLanguageDef) : mainLabel definition = (target definition).main := rfl
theorem registers_exact (definition : CalculusLanguageDef) : registers definition = (target definition).initialState := rfl

def initial (definition : CalculusLanguageDef) (word : List (Option Alphabet)) : (target definition).Cfg where
  l := some (mainLabel definition)
  var := registers definition
  stk key := if same : key = inputKey definition then by cases same; exact word else []

theorem initial_exact (definition : CalculusLanguageDef) (word : List (Option Alphabet)) :
    initial definition word = initList (target definition) word := by
  simp only [initial, initList]
  congr 1
  funext key
  by_cases same : key = inputKey definition
  · subst key
    have original : inputKey definition = (target definition).k₀ := rfl
    simp only [dif_pos original]
    rfl
  · have original : key ≠ (target definition).k₀ := same
    simp only [dif_neg same, dif_neg original]

private def optionKeys {A : Type} (keys : List A) : List (Option A) := none :: keys.map some
private theorem optionKeys_complete {A : Type} (keys : List A) (complete : ∀ key, key ∈ keys) :
    ∀ key, key ∈ optionKeys keys := by
  intro key
  cases key with
  | none => exact List.mem_cons_self
  | some value => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨value, complete value, rfl⟩)

private def sumKeys {A B : Type} (first : List A) (second : List B) : List (A ⊕ B) :=
  first.map Sum.inl ++ second.map Sum.inr
private theorem sumKeys_complete {A B : Type} (first : List A) (second : List B)
    (firstComplete : ∀ key, key ∈ first) (secondComplete : ∀ key, key ∈ second) :
    ∀ key, key ∈ sumKeys first second := by
  intro key
  cases key with
  | inl value => exact List.mem_append_left _ (List.mem_map.mpr ⟨value, firstComplete value, rfl⟩)
  | inr value => exact List.mem_append_right _ (List.mem_map.mpr ⟨value, secondComplete value, rfl⟩)

private def allKeyDecision {A : Type} [Fintype A] [DecidableEq A] (keys : List A) :
    Decidable (∀ key, key ∈ keys) := by
  letI : BEq A := ⟨fun first second => decide (first = second)⟩
  letI : LawfulBEq A := { eq_of_beq := of_decide_eq_true, rfl := by intro value; exact decide_eq_true rfl }
  exact Fintype.decidableForallFintype

open Lean Elab Tactic Meta in
private partial def leafKeyValues (type : Expr) : MetaM (Array Expr) := do
  let type ← withTransparency .reducible (whnf type)
  let some name := type.getAppFn.constName? | throwError "Unsupported key type {type}"
  let info ← getConstInfoInduct name
  unless info.numIndices == 0 do throwError "Indexed key type {type} needs explicit keys"
  let mut values := #[]
  for name in info.ctors do
    let constructor ← mkAppOptM name (type.getAppArgs.map some)
    let rec finish (constructor : Expr) : MetaM (Array Expr) := do
      let constructorType ← withTransparency .reducible (whnf (← inferType constructor))
      match constructorType with
      | .forallE _ field _ _ =>
        let mut result := #[]
        for value in ← leafKeyValues field do
          result := result ++ (← finish (mkApp constructor value))
        pure result
      | _ =>
        unless ← isDefEq constructorType type do throwError "Mismatched key constructor {name}"
        pure #[constructor]
    values := values ++ (← finish constructor)
  pure values

open Lean Elab Tactic Meta in
private partial def keyUniverseExpression (type : Expr) : MetaM (Expr × Expr) := do
  let type ← withTransparency .reducible (whnf type)
  match type.getAppFn.constName?, type.getAppArgs.toList with
  | some ``Option, [child] =>
    let (values, complete) ← keyUniverseExpression child
    let keys ← mkAppM ``optionKeys #[values]
    let proof ← mkAppM ``optionKeys_complete #[values, complete]
    pure (keys, proof)
  | some ``Sum, [first, second] =>
    let (left, leftComplete) ← keyUniverseExpression first
    let (right, rightComplete) ← keyUniverseExpression second
    let keys ← mkAppM ``sumKeys #[left, right]
    let proof ← mkAppM ``sumKeys_complete #[left, right, leftComplete, rightComplete]
    pure (keys, proof)
  | _, _ =>
    let keys ← mkListLit type (← leafKeyValues type).toList
    let proposition ← withLocalDeclD `key type fun key => do
      mkForallFVars #[key] (← mkAppM ``List.Mem #[key, keys])
    let decision ← mkAppM ``allKeyDecision #[keys]
    let decided ← mkAppOptM ``Decidable.decide #[some proposition, some decision]
    let decisionTrue ← mkEq decided (mkConst ``Bool.true)
    let reflexive ← mkEqRefl (mkConst ``Bool.true)
    let proof ← mkAppOptM ``of_decide_eq_true #[some proposition, some decision,
      some (mkExpectedPropHint reflexive decisionTrue)]
    pure (keys, proof)

open Lean Elab Tactic Meta in
elab "authored_key_universe" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let targetType ← goal.getType
    let listType := targetType.getAppArgs.toList.head!
    let keyType := listType.getAppArgs.toList.head!
    let (keys, complete) ← keyUniverseExpression keyType
    goal.assign (← mkAppOptM ``Subtype.mk #[some listType, some (targetType.getAppArgs.toList.tail.head!), some keys, some complete])
  replaceMainGoal []

def keyUniverse (definition : CalculusLanguageDef) :
    { keys : List (target definition).K // ∀ key, key ∈ keys } := by
  authored_key_universe

def keys (definition : CalculusLanguageDef) := (keyUniverse definition).val
theorem all_keys (definition : CalculusLanguageDef) : ∀ key : (target definition).K, key ∈ keys definition :=
  (keyUniverse definition).property

end Mettapedia.Languages.HOLLight.AuthoredNodeDispatch.Program
