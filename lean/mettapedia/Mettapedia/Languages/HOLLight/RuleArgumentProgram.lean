import Mettapedia.Languages.HOLLight.RuleArgumentRendering
import Mettapedia.Languages.HOLLight.ArgumentListProgram
import Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission
import Lean
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 1024
set_option allowUnsafeReducibility true
set_option backward.isDefEq.respectTransparency false
open Turing
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef InferenceChecker InferenceExtension
open Mettapedia.Computability
open Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission
/-!
# Executable table for original rule admission and argument rendering

The original authored-rule machine is exposed as instructions, physical stack
addresses and registers. Proof-producing simplification replaces mathematical
machine wrappers by their established structural embeddings. The resulting
table, initial configuration and transition function are checked against the
original machine, retaining its steps, refusal behavior and clock.
-/
namespace Mettapedia.Languages.HOLLight.RuleArgumentRendering.Program
attribute [local reducible] StackMachineComposition.Dispatch.emit
attribute [local implicit_reducible] CertificateRuleAdmission.admissionMachine CertificateRuleAdmission.machine RetainedWordExecution.machine
attribute [local reducible] ScopedApplication.machine ScopedApplication.savedMachine
 ScopedApplication.scopeMachine ScopedApplication.scopeDispatcher ScopedApplication.selectedMachine
 ScopedApplication.relookupMachine ArgumentScope.machine FramedWordValidation.retainedMachine
 FramedWordValidation.machine FramedWordValidation.statement FramedWordValidation.body
 PatternScopeExecution.OriginalAdmission.machine PatternScopeExecution.OriginalAdmission.projectedMachine
 PatternScopeExecution.VisitorAdapter.machine PatternScopeExecution.Binary.machine
 PatternSpanExecution.Execution.machine WordHomomorphismMachine.machine

attribute [local reducible] Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.admissionMachine
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.UniformArity.machine
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.UniformArity.body
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.UniformArity.program
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.argumentMachine
  Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming.Execution.machine
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.machine
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.nameMachine
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.classifier
  Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission.dictionary
  Mettapedia.Computability.RetainedWordExecution.machine
  Mettapedia.Computability.RetainedWordExecution.statement
  Mettapedia.Computability.RetainedWordExecution.body
  Mettapedia.Computability.StackMachineComposition.machine
  Mettapedia.Computability.StackMachineComposition.Dispatch.machine
  Mettapedia.Computability.FiniteWordClassifier.machine
  Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.machine

open Mettapedia.Languages.HOLLight
attribute [local reducible] RuleArgumentRendering.machine RuleArgumentRendering.projectedMachine
  CommonArenaDispatch.machine ArgumentListRendering.dispatched ArgumentListRendering.successMachine
  ArgumentVectorRendering.machine AdmittedArgumentRendering.machine AdmittedArgumentRendering.admittedMachine
  AdmittedArgumentRendering.renderingMachine AdmittedArgumentRendering.savedMachine
  FramedWordMapping.machine WordTemplateMachine.machine
  ArgumentRenderingMachine.Full.machine ArgumentRenderingMachine.Routing.Pipeline.machine
  ArgumentRenderingMachine.Routing.Traversal.machine ArgumentRenderingMachine.Execution.machine


attribute [local reducible] StackMachineComposition.liftFirst StackMachineComposition.liftSecond
  StackMachineComposition.Dispatch.lift
  CommonArenaDispatch.program CommonArenaDispatch.Programs.body CommonArenaDispatch.Programs.embedded
  CommonArenaDispatch.readByte

attribute [local reducible] StackMachineComposition.leftKey StackMachineComposition.rightKey
attribute [local reducible] UniformArity.family FramedWordMapping.initial

open Lean Elab Tactic Meta in
elab "normalize_rule_program " expression:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let expression ← Elab.Term.elabTerm expression (← goal.getType)
    let reduced ← withTransparency .reducible (reduce expression)
    goal.assign reduced
  replaceMainGoal []

private theorem dispatchLift_eq (program : FinTM2) (statement : program.Stmt) :
    StackMachineComposition.Dispatch.lift program statement =
      StackMachineRegisters.extend StackMachineComposition.Dispatch.Phase.run statement := by
  induction statement <;> simp_all only [StackMachineComposition.Dispatch.lift, StackMachineRegisters.extend]

open Lean Elab Tactic Meta in
elab "extract_rule_program " expression:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let expression ← Elab.Term.elabTerm expression none
    let reduced ← withTransparency .reducible (reduce expression)
    let mut rules : SimpTheorems := {}
    for name in [``StackMachineComposition.liftFirst_eq_embedStatement,
        ``StackMachineComposition.liftSecond_eq_embedStatement, ``dispatchLift_eq] do
      rules ← rules.addConst name
    let ctx ← Simp.mkContext { zeta := false } (simpTheorems := #[rules])
      (congrTheorems := ← getSimpCongrTheorems)
    let mut value := reduced
    let mut forward ← mkEqRefl reduced
    let mut stable := false
    for _ in [:32] do
      let (simplified, _) ← simp value ctx
      forward ← mkEqTrans forward (← simplified.getProof)
      let next ← withTransparency .reducible (reduce simplified.expr)
      if next == value then
        stable := true
        break
      value := next
    unless stable do throwError "Instruction extraction did not reach a fixed point"
    let proof ← mkEqSymm forward
    let goalType ← whnf (← goal.getType)
    let args := goalType.getAppArgs
    let pair ← mkAppOptM ``Subtype.mk #[some (args.getD 0 (.bvar 0)), some (args.getD 1 (.bvar 0)), some value, some proof]
    goal.assign pair
  replaceMainGoal []

def admissionTable (definition : CalculusLanguageDef) :
    { table : (admissionMachine definition).Λ → (admissionMachine definition).Stmt //
      table = (admissionMachine definition).m } := by
  extract_rule_program (admissionMachine definition).m

def admissionBody (definition : CalculusLanguageDef) := (admissionTable definition).val

theorem admissionBody_exact (definition : CalculusLanguageDef) :
    admissionBody definition = (admissionMachine definition).m := (admissionTable definition).property

def dispatcherTable : { table : ScopedApplication.scopeDispatcher.Λ →
    ScopedApplication.scopeDispatcher.Stmt // table = ScopedApplication.scopeDispatcher.m } := by
  extract_rule_program ScopedApplication.scopeDispatcher.m

def dispatcherBody := dispatcherTable.val

theorem dispatcherBody_exact : dispatcherBody = ScopedApplication.scopeDispatcher.m := dispatcherTable.property

local instance (definition : CalculusLanguageDef) : Fintype
    ((admissionMachine definition).Γ (admissionMachine definition).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (definition : CalculusLanguageDef) : Inhabited
    ((admissionMachine definition).Γ (admissionMachine definition).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def scopeBody (definition : CalculusLanguageDef) :
    (ScopedApplication.scopeMachine definition).Λ → (ScopedApplication.scopeMachine definition).Stmt := by
 normalize_rule_program (StackMachineComposition.Programs.body
  (FirstAlphabet := (admissionMachine definition).Γ)
  (SecondAlphabet := ScopedApplication.scopeDispatcher.Γ)
  (admissionMachine definition).k₁ ScopedApplication.scopeDispatcher.k₀
  ScopedApplication.scopeDispatcher.main (none : Option Alphabet) id
  (admissionBody definition) dispatcherBody)

theorem scopeBody_exact (definition : CalculusLanguageDef) :
 scopeBody definition = (ScopedApplication.scopeMachine definition).m := by
 unfold scopeBody
 rw [admissionBody_exact, dispatcherBody_exact]
 exact @StackMachineComposition.body_eq (admissionMachine definition)
  ScopedApplication.scopeDispatcher (inferInstanceAs (Fintype (Option Alphabet)))
    (inferInstanceAs (Inhabited (Option Alphabet))) (Equiv.refl _)


open Mettapedia.Languages.HOLLight
abbrev target (definition : CalculusLanguageDef) := RuleArgumentRendering.machine definition

local instance (definition : CalculusLanguageDef) : Fintype ((ScopedApplication.scopeMachine definition).Γ
    (ScopedApplication.scopeMachine definition).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet ⊕ Bool))
local instance (definition : CalculusLanguageDef) : Inhabited ((ScopedApplication.scopeMachine definition).Γ
    (ScopedApplication.scopeMachine definition).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet ⊕ Bool))



def firstBody (definition : CalculusLanguageDef) : (RuleArgumentRendering.projectedMachine definition).Λ →
    (RuleArgumentRendering.projectedMachine definition).Stmt := by
  normalize_rule_program (StackMachineComposition.Programs.body
    (ScopedApplication.scopeMachine definition).k₁
    WordHomomorphismMachine.Stack.input WordHomomorphismMachine.Phase.read
    (default : Option Alphabet ⊕ Bool) id
    (scopeBody definition)
    (WordHomomorphismMachine.program RuleArgumentRendering.project))

theorem firstBody_exact (definition : CalculusLanguageDef) : firstBody definition =
    (RuleArgumentRendering.projectedMachine definition).m := by
  unfold firstBody
  rw [scopeBody_exact]
  exact StackMachineComposition.body_eq
    (ScopedApplication.scopeMachine definition)
    (WordHomomorphismMachine.machine RuleArgumentRendering.project) (Equiv.refl _)

local instance (definition : CalculusLanguageDef) : Fintype ((RuleArgumentRendering.projectedMachine definition).Γ
    (RuleArgumentRendering.projectedMachine definition).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (definition : CalculusLanguageDef) : Inhabited ((RuleArgumentRendering.projectedMachine definition).Γ
    (RuleArgumentRendering.projectedMachine definition).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def body (definition : CalculusLanguageDef) : (target definition).Λ → (target definition).Stmt := by
  normalize_rule_program (StackMachineComposition.Programs.body
    (RuleArgumentRendering.projectedMachine definition).k₁
    ArgumentListRendering.Program.successInput StackMachineComposition.Dispatch.Phase.read
    (none : Option Alphabet) id (firstBody definition) ArgumentListRendering.Program.dispatch)

theorem body_exact (definition : CalculusLanguageDef) : body definition = (target definition).m := by
  unfold body
  rw [firstBody_exact definition, ← ArgumentListRendering.Program.dispatch_eq]
  exact StackMachineComposition.body_eq
    (RuleArgumentRendering.projectedMachine definition)
    ArgumentListRendering.dispatched (Equiv.refl _)

def optionEquality {α : Type} (eq : DecidableEq α) : DecidableEq (Option α) :=
  @Option.instDecidableEq α eq

def sumEquality {α β : Type} (first : DecidableEq α) (second : DecidableEq β) : DecidableEq (α ⊕ β) :=
  fun x y => @instDecidableEqSum α β first second x y

def admissionEquality (definition : CalculusLanguageDef) : DecidableEq (admissionMachine definition).K :=
  optionEquality (sumEquality
    (optionEquality (optionEquality (optionEquality (optionEquality (sumEquality
      (optionEquality CertificateDataTraversal.instDecidableEqStack)
      Mettapedia.Computability.FiniteWordClassifier.instDecidableEqStack)))))
    (optionEquality (optionEquality (optionEquality (sumEquality
      (optionEquality CertificateDataTraversal.instDecidableEqStack)
      (optionEquality (optionEquality (optionEquality CertificateDataTraversal.instDecidableEqStack))))))))
def patternScopeEquality : DecidableEq PatternScopeExecution.OriginalAdmission.machine.K :=
  optionEquality (sumEquality
    (optionEquality (sumEquality (optionEquality PatternSpanExecution.Execution.instDecidableEqStack)
      WordHomomorphismMachine.instDecidableEqStack)) PatternScopeExecution.Binary.instDecidableEqStack)
def scopeEquality (definition : CalculusLanguageDef) : DecidableEq (ScopedApplication.scopeMachine definition).K :=
  optionEquality (sumEquality (admissionEquality definition)
    (optionEquality (optionEquality (optionEquality (optionEquality (optionEquality
      (optionEquality patternScopeEquality)))))))
def keyEquality (definition : CalculusLanguageDef) : DecidableEq (target definition).K :=
  optionEquality (sumEquality
    (optionEquality (sumEquality (scopeEquality definition) WordHomomorphismMachine.instDecidableEqStack))
    (optionEquality (sumEquality ArgumentVectorRendering.Program.keyEquality WordTemplateMachine.instDecidableEqStack)))
local instance (definition : CalculusLanguageDef) : DecidableEq (target definition).K := keyEquality definition

def step (definition : CalculusLanguageDef) := @TM2.step (target definition).K (target definition).Γ (target definition).Λ (target definition).σ (keyEquality definition) (body definition)

theorem step_exact (definition : CalculusLanguageDef) : step definition = (target definition).step := by
  unfold step
  rw [show keyEquality definition = (target definition).kDecidableEq from Subsingleton.elim _ _, body_exact definition]
  rfl

def inputKey (definition : CalculusLanguageDef) : (target definition).K := by normalize_rule_program (target definition).k₀
def resultKey (definition : CalculusLanguageDef) : (target definition).K := by normalize_rule_program (target definition).k₁
def registers (definition : CalculusLanguageDef) : (target definition).σ := by normalize_rule_program (target definition).initialState
def mainLabel (definition : CalculusLanguageDef) : (target definition).Λ := by normalize_rule_program (target definition).main

def initial (definition : CalculusLanguageDef) (word : List Alphabet) : (target definition).Cfg where
  l := some (mainLabel definition)
  var := registers definition
  stk := Function.update (fun _ => []) (inputKey definition) word

theorem initial_exact (definition : CalculusLanguageDef) (word : List Alphabet) : initial definition word = initList (target definition) word := by
  simp only [initial, initList]
  congr 1
  funext key
  by_cases same : key = inputKey definition
  · subst key; simp [Function.update, inputKey, StackMachineComposition.leftKey]
  · simp [Function.update, inputKey, StackMachineComposition.leftKey] at same ⊢
    simp [same]

end Mettapedia.Languages.HOLLight.RuleArgumentRendering.Program
