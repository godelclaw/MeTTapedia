import Mettapedia.Languages.HOLLight.ClaimCheckingMachine
import Mettapedia.Languages.HOLLight.RuleArgumentProgram

/-!
# Computed instructions for original source-claim checking

The executable interfaces retain the original machine's stack alphabet,
labels, registers and transition semantics. Computed endpoint literals avoid
runtime evaluation of bundled finiteness metadata; every recovered block has
checked equality to its original instruction table.

The counted evaluator records actual original-machine transitions. Numeric
fuel and snapshot period are caller parameters; snapshots preserve the entire
configuration exactly.
-/
set_option autoImplicit false
set_option Elab.async false
set_option allowUnsafeReducibility true

namespace Mettapedia.Languages.HOLLight.ClaimCheckingProgram
open Turing
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.HOLLight Mettapedia.Languages.OpenTheory
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open ClaimCheckingMachine
@[instance_reducible] def alphabet0Finite : Fintype (Alphabet) := inferInstance
@[instance_reducible] def alphabet0Default : Inhabited (Alphabet) := inferInstance
@[instance_reducible] def alphabet1Finite : Fintype (Option Alphabet) := inferInstance
@[instance_reducible] def alphabet1Default : Inhabited (Option Alphabet) := inferInstance
@[instance_reducible] def alphabet2Finite : Fintype (Option (Option Alphabet)) := inferInstance
@[instance_reducible] def alphabet2Default : Inhabited (Option (Option Alphabet)) := inferInstance
@[instance_reducible] def alphabet3Finite : Fintype (Option Alphabet ⊕ Alphabet) := inferInstance
@[instance_reducible] def alphabet3Default : Inhabited (Option Alphabet ⊕ Alphabet) := inferInstance
@[instance_reducible] def alphabet4Finite : Fintype (Option Alphabet ⊕ Bool) := inferInstance
@[instance_reducible] def alphabet4Default : Inhabited (Option Alphabet ⊕ Bool) := inferInstance
@[instance_reducible] def alphabet5Finite : Fintype (Option Bool) := inferInstance
@[instance_reducible] def alphabet5Default : Inhabited (Option Bool) := inferInstance

attribute [local reducible] FinTM2.Cfg ClaimCheckingMachine.machine guardedMachine successMachine preparedMachine
 claimedMachine selectedClaimMachine claimMachine sequentMachine selectedSequentMachine projectedMachine
 Comparison.machine Comparison.compareMachine
 SourceQuantifierEmission.renderMachine SourceQuantifierEmission.rawMachine
 SourceQuantifierEmission.stripStatus SourceQuantifierEmission.rawIdentity
 SourceQuantifierEmission.selectedScopeMachine SourceQuantifierEmission.savedScopeMachine
 SourceQuantifierEmission.admissionMachine
 StackMachineComposition.machine StackMachineComposition.Dispatch.machine
 StackMachineComposition.liftFirst StackMachineComposition.liftSecond StackMachineComposition.Dispatch.lift
 RetainedWordExecution.machine RetainedWordExecution.statement RetainedWordExecution.body
 RetainedWordExecution.WithOutput.machine RetainedWordExecution.WithOutput.statement
 RetainedWordExecution.WithOutput.body
 WordHomomorphismMachine.machine WordTemplateMachine.machine Indexed.machine Indexed.Alphabet WordEqualityMachine.machine
 Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.machine
 Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.PrefixField.machine
 Mettapedia.GSLT.LanguageDef.PatternScopeExecution.OriginalAdmission.machine
 Mettapedia.GSLT.LanguageDef.PatternScopeExecution.OriginalAdmission.projectedMachine
 Mettapedia.GSLT.LanguageDef.PatternScopeExecution.VisitorAdapter.machine
 Mettapedia.GSLT.LanguageDef.PatternScopeExecution.Binary.machine
 Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.machine
 ArgumentRenderingMachine.Full.machine ArgumentRenderingMachine.Routing.Pipeline.machine
 ArgumentRenderingMachine.Routing.Traversal.machine ArgumentRenderingMachine.Routing.machine
 Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Hooks.Execution.machine ArgumentRenderingMachine.Execution.machine
 RetainedWordExecution.WithOutput.Framed.untag
 StackMachineComposition.leftKey StackMachineComposition.rightKey

open Lean Elab Tactic Meta in
elab "claim_program_whnf_table " expression:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let expression ← Elab.Term.elabTerm expression (← goal.getType)
    let reduced ← withTransparency .reducible (whnf expression)
    goal.assign reduced
  replaceMainGoal []

open Lean Elab Tactic Meta in
elab "claim_program_literal_endpoints " expression:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let expression ← Elab.Term.elabTerm expression (← goal.getType)
    let literal ← Meta.transform expression (pre := fun term => do
      let endpoint := match term with
        | .proj ``FinTM2 field _ => [3,4,7,10].contains field
        | _ => match term.getAppFn.constName? with
          | some name => [``FinTM2.k₀,``FinTM2.k₁,``FinTM2.main,``FinTM2.initialState,
              ``RetainedWordExecution.WithOutput.Framed.untag].contains name
          | none => false
      if endpoint then return .done (← withTransparency .reducible (reduce term))
      else return .continue)
    goal.assign literal
  replaceMainGoal []

open Lean Elab Tactic Meta in
private partial def concreteKeyEquality (type : Expr) : MetaM Expr := do
  let type ← withTransparency .all (whnf type)
  match type.getAppFn.constName?, type.getAppArgs.toList with
  | some ``Option, [child] =>
    mkAppOptM ``Option.instDecidableEq #[some child, some (← concreteKeyEquality child)]
  | some ``Sum, [first, second] =>
    mkAppOptM ``instDecidableEqSum #[some first, some second,
      some (← concreteKeyEquality first), some (← concreteKeyEquality second)]
  | some ``Prod, [first, second] =>
    mkAppOptM `instDecidableEqProd #[some first, some second,
      some (← concreteKeyEquality first), some (← concreteKeyEquality second)]
  | _, _ => synthInstance (← mkAppM ``DecidableEq #[type])

open Lean Elab Tactic Meta in
elab "claim_program_key_equality" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let type ← goal.getType
    let keyType := type.getAppArgs.back!
    goal.assign (← concreteKeyEquality keyType)
  replaceMainGoal []

private theorem composition_exact (first second : FinTM2)
    [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)]
    (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    {firstBody : first.Λ → first.Stmt} {secondBody : second.Λ → second.Stmt}
    (firstSame : firstBody = first.m) (secondSame : secondBody = second.m) :
    StackMachineComposition.Programs.body first.k₁ second.k₀ second.main default bridge firstBody secondBody =
      (StackMachineComposition.machine first second bridge).m := by
  cases firstSame
  cases secondSame
  exact StackMachineComposition.body_eq first second bridge

abbrev target := ClaimCheckingMachine.machine

def stripBodyTable : { instructions : (SourceQuantifierEmission.stripStatus).Λ → (SourceQuantifierEmission.stripStatus).Stmt // instructions = (SourceQuantifierEmission.stripStatus).m } := by
  extract_rule_program (SourceQuantifierEmission.stripStatus).m
def stripBody := stripBodyTable.val
theorem stripBody_exact : stripBody = (SourceQuantifierEmission.stripStatus).m := stripBodyTable.property

def firstFieldBodyTable : { instructions : (SourceQuantifierEmission.firstField).Λ → (SourceQuantifierEmission.firstField).Stmt // instructions = (SourceQuantifierEmission.firstField).m } := by
  extract_rule_program (SourceQuantifierEmission.firstField).m
def firstFieldBody := firstFieldBodyTable.val
theorem firstFieldBody_exact : firstFieldBody = (SourceQuantifierEmission.firstField).m := firstFieldBodyTable.property

def secondFieldBodyTable : { instructions : (sequentField).Λ → (sequentField).Stmt // instructions = (sequentField).m } := by
  extract_rule_program (sequentField).m
def secondFieldBody := secondFieldBodyTable.val
theorem secondFieldBody_exact : secondFieldBody = (sequentField).m := secondFieldBodyTable.property

local instance : Fintype ((SourceQuantifierEmission.firstField).Γ (SourceQuantifierEmission.firstField).k₁) := alphabet0Finite
local instance : Inhabited ((SourceQuantifierEmission.firstField).Γ (SourceQuantifierEmission.firstField).k₁) := alphabet0Default
def rawBody : (SourceQuantifierEmission.rawMachine).Λ → (SourceQuantifierEmission.rawMachine).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (SourceQuantifierEmission.firstField).k₁ (SourceQuantifierEmission.stripStatus).k₀ (SourceQuantifierEmission.stripStatus).main (default : Alphabet) id
    (firstFieldBody) (stripBody))
theorem rawBody_exact : rawBody = (SourceQuantifierEmission.rawMachine).m := composition_exact SourceQuantifierEmission.firstField SourceQuantifierEmission.stripStatus (Equiv.refl _) firstFieldBody_exact stripBody_exact

local instance : Fintype ((ArgumentRenderingMachine.Full.machine).Γ (ArgumentRenderingMachine.Full.machine).k₁) := alphabet0Finite
local instance : Inhabited ((ArgumentRenderingMachine.Full.machine).Γ (ArgumentRenderingMachine.Full.machine).k₁) := alphabet0Default
def renderBody : (SourceQuantifierEmission.renderMachine).Λ → (SourceQuantifierEmission.renderMachine).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (ArgumentRenderingMachine.Full.machine).k₁ (SourceQuantifierEmission.rawMachine).k₀ (SourceQuantifierEmission.rawMachine).main (default : Alphabet) id
    (ArgumentRenderingMachine.Full.program) (rawBody))
theorem renderBody_exact : renderBody = (SourceQuantifierEmission.renderMachine).m := composition_exact ArgumentRenderingMachine.Full.machine SourceQuantifierEmission.rawMachine (Equiv.refl _) ArgumentRenderingMachine.Full.program_eq.symm rawBody_exact

local instance : Fintype ((SourceQuantifierEmission.renderMachine).Γ (SourceQuantifierEmission.renderMachine).k₁) := alphabet0Finite
local instance : Inhabited ((SourceQuantifierEmission.renderMachine).Γ (SourceQuantifierEmission.renderMachine).k₁) := alphabet0Default
def claimBody : (claimMachine).Λ → (claimMachine).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (SourceQuantifierEmission.renderMachine).k₁ (WordTemplateMachine.machine claimTemplate).k₀ (WordTemplateMachine.machine claimTemplate).main (default : Alphabet) id
    (renderBody) (WordTemplateMachine.program claimTemplate))
theorem claimBody_exact : claimBody = (claimMachine).m := composition_exact SourceQuantifierEmission.renderMachine (WordTemplateMachine.machine claimTemplate) (Equiv.refl _) renderBody_exact rfl

local instance : Fintype ((sequentField).Γ (sequentField).k₁) := alphabet0Finite
local instance : Inhabited ((sequentField).Γ (sequentField).k₁) := alphabet0Default
def sequentBody : (sequentMachine).Λ → (sequentMachine).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (sequentField).k₁ (SourceQuantifierEmission.stripStatus).k₀ (SourceQuantifierEmission.stripStatus).main (default : Alphabet) id
    (secondFieldBody) (stripBody))
theorem sequentBody_exact : sequentBody = (sequentMachine).m := composition_exact sequentField SourceQuantifierEmission.stripStatus (Equiv.refl _) secondFieldBody_exact stripBody_exact

def claimSelectorBodyTable : { instructions : (Indexed.machine claimSelector).Λ → (Indexed.machine claimSelector).Stmt // instructions = (Indexed.machine claimSelector).m } := by
  extract_rule_program (Indexed.machine claimSelector).m
def claimSelectorBody := claimSelectorBodyTable.val
theorem claimSelectorBody_exact : claimSelectorBody = (Indexed.machine claimSelector).m := claimSelectorBodyTable.property

local instance : Fintype ((Indexed.machine claimSelector).Γ (Indexed.machine claimSelector).k₁) := alphabet0Finite
local instance : Inhabited ((Indexed.machine claimSelector).Γ (Indexed.machine claimSelector).k₁) := alphabet0Default
def selectedClaimBody : (selectedClaimMachine).Λ → (selectedClaimMachine).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (Indexed.machine claimSelector).k₁ (claimMachine).k₀ (claimMachine).main (default : Alphabet) id
    (claimSelectorBody) (claimBody))
theorem selectedClaimBody_exact : selectedClaimBody = (selectedClaimMachine).m := composition_exact (Indexed.machine claimSelector) claimMachine (Equiv.refl _) claimSelectorBody_exact claimBody_exact

def sequentSelectorBodyTable : { instructions : (Indexed.machine sequentSelector).Λ → (Indexed.machine sequentSelector).Stmt // instructions = (Indexed.machine sequentSelector).m } := by
  extract_rule_program (Indexed.machine sequentSelector).m
def sequentSelectorBody := sequentSelectorBodyTable.val
theorem sequentSelectorBody_exact : sequentSelectorBody = (Indexed.machine sequentSelector).m := sequentSelectorBodyTable.property

local instance : Fintype ((Indexed.machine sequentSelector).Γ (Indexed.machine sequentSelector).k₁) := alphabet0Finite
local instance : Inhabited ((Indexed.machine sequentSelector).Γ (Indexed.machine sequentSelector).k₁) := alphabet0Default
def selectedSequentBody : (selectedSequentMachine).Λ → (selectedSequentMachine).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (Indexed.machine sequentSelector).k₁ (sequentMachine).k₀ (sequentMachine).main (default : Alphabet) id
    (sequentSelectorBody) (sequentBody))
theorem selectedSequentBody_exact : selectedSequentBody = (selectedSequentMachine).m := composition_exact (Indexed.machine sequentSelector) sequentMachine (Equiv.refl _) sequentSelectorBody_exact sequentBody_exact

abbrev claimedRetained := RetainedWordExecution.WithOutput.machine selectedClaimMachine
local instance : Inhabited ((selectedClaimMachine).Γ (selectedClaimMachine).k₀) := alphabet1Default
local instance : Inhabited ((selectedClaimMachine).Γ (selectedClaimMachine).k₁) := alphabet0Default
local instance : Fintype ((selectedClaimMachine).Γ (selectedClaimMachine).k₁) := alphabet0Finite
def claimedRetainedBody : claimedRetained.Λ → claimedRetained.Stmt := by
  claim_program_literal_endpoints (RetainedWordExecution.WithOutput.Programs.statement
    (selectedClaimMachine).k₀ (selectedClaimMachine).k₁ (none : Option Alphabet) (0 : Alphabet)
    (selectedClaimMachine).initialState (selectedClaimMachine).main selectedClaimBody)
theorem claimedRetainedBody_exact : claimedRetainedBody = claimedRetained.m := by
  unfold claimedRetainedBody
  rw [selectedClaimBody_exact]
  rfl
abbrev claimedUntag := WordHomomorphismMachine.machine
  (RetainedWordExecution.WithOutput.Framed.untag selectedClaimMachine (Equiv.refl _) (Equiv.refl _))
abbrev claimedTagged := RetainedWordExecution.WithOutput.Framed.taggedMachine selectedClaimMachine (Equiv.refl _) (Equiv.refl _)

local instance : Fintype ((claimedRetained).Γ (claimedRetained).k₁) := alphabet3Finite
local instance : Inhabited ((claimedRetained).Γ (claimedRetained).k₁) := alphabet3Default
def claimedTaggedBody : (claimedTagged).Λ → (claimedTagged).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (claimedRetained).k₁ (claimedUntag).k₀ (claimedUntag).main (default : Option Alphabet ⊕ Alphabet) id
    (claimedRetainedBody) (WordHomomorphismMachine.program (RetainedWordExecution.WithOutput.Framed.untag selectedClaimMachine (Equiv.refl _) (Equiv.refl _))))
theorem claimedTaggedBody_exact : claimedTaggedBody = (claimedTagged).m := composition_exact claimedRetained claimedUntag (Equiv.refl _) claimedRetainedBody_exact rfl

local instance : Fintype ((claimedTagged).Γ (claimedTagged).k₁) := alphabet1Finite
local instance : Inhabited ((claimedTagged).Γ (claimedTagged).k₁) := alphabet1Default
def claimedBody : (claimedMachine).Λ → (claimedMachine).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (claimedTagged).k₁ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).k₀ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).main (default : Option Alphabet) id
    (claimedTaggedBody) (WordTemplateMachine.program (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))))
theorem claimedBody_exact : claimedBody = (claimedMachine).m := composition_exact claimedTagged (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))) (Equiv.refl _) claimedTaggedBody_exact rfl

abbrev projectedRetained := RetainedWordExecution.WithOutput.machine selectedSequentMachine
local instance : Inhabited ((selectedSequentMachine).Γ (selectedSequentMachine).k₀) := alphabet1Default
local instance : Inhabited ((selectedSequentMachine).Γ (selectedSequentMachine).k₁) := alphabet0Default
local instance : Fintype ((selectedSequentMachine).Γ (selectedSequentMachine).k₁) := alphabet0Finite
def projectedRetainedBody : projectedRetained.Λ → projectedRetained.Stmt := by
  claim_program_literal_endpoints (RetainedWordExecution.WithOutput.Programs.statement
    (selectedSequentMachine).k₀ (selectedSequentMachine).k₁ (none : Option Alphabet) (0 : Alphabet)
    (selectedSequentMachine).initialState (selectedSequentMachine).main selectedSequentBody)
theorem projectedRetainedBody_exact : projectedRetainedBody = projectedRetained.m := by
  unfold projectedRetainedBody
  rw [selectedSequentBody_exact]
  rfl
abbrev projectedUntag := WordHomomorphismMachine.machine
  (RetainedWordExecution.WithOutput.Framed.untag selectedSequentMachine (Equiv.refl _) (Equiv.refl _))
abbrev projectedTagged := RetainedWordExecution.WithOutput.Framed.taggedMachine selectedSequentMachine (Equiv.refl _) (Equiv.refl _)

local instance : Fintype ((projectedRetained).Γ (projectedRetained).k₁) := alphabet3Finite
local instance : Inhabited ((projectedRetained).Γ (projectedRetained).k₁) := alphabet3Default
def projectedTaggedBody : (projectedTagged).Λ → (projectedTagged).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (projectedRetained).k₁ (projectedUntag).k₀ (projectedUntag).main (default : Option Alphabet ⊕ Alphabet) id
    (projectedRetainedBody) (WordHomomorphismMachine.program (RetainedWordExecution.WithOutput.Framed.untag selectedSequentMachine (Equiv.refl _) (Equiv.refl _))))
theorem projectedTaggedBody_exact : projectedTaggedBody = (projectedTagged).m := composition_exact projectedRetained projectedUntag (Equiv.refl _) projectedRetainedBody_exact rfl

local instance : Fintype ((projectedTagged).Γ (projectedTagged).k₁) := alphabet1Finite
local instance : Inhabited ((projectedTagged).Γ (projectedTagged).k₁) := alphabet1Default
def projectedBody : (projectedMachine).Λ → (projectedMachine).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (projectedTagged).k₁ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).k₀ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).main (default : Option Alphabet) id
    (projectedTaggedBody) (WordTemplateMachine.program (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))))
theorem projectedBody_exact : projectedBody = (projectedMachine).m := composition_exact projectedTagged (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))) (Equiv.refl _) projectedTaggedBody_exact rfl

def compareSelectorBodyTable : { instructions : (Indexed.machine Comparison.selector).Λ → (Indexed.machine Comparison.selector).Stmt // instructions = (Indexed.machine Comparison.selector).m } := by
  extract_rule_program (Indexed.machine Comparison.selector).m
def compareSelectorBody := compareSelectorBodyTable.val
theorem compareSelectorBody_exact : compareSelectorBody = (Indexed.machine Comparison.selector).m := compareSelectorBodyTable.property

def equalityBody : (WordEqualityMachine.machine Alphabet).Λ → (WordEqualityMachine.machine Alphabet).Stmt := by
  claim_program_whnf_table (WordEqualityMachine.machine Alphabet).m
theorem equalityBody_exact : equalityBody = (WordEqualityMachine.machine Alphabet).m := rfl

local instance : Fintype ((Indexed.machine Comparison.selector).Γ (Indexed.machine Comparison.selector).k₁) := alphabet1Finite
local instance : Inhabited ((Indexed.machine Comparison.selector).Γ (Indexed.machine Comparison.selector).k₁) := alphabet1Default
def compareBody : (Comparison.compareMachine).Λ → (Comparison.compareMachine).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (Indexed.machine Comparison.selector).k₁ (WordEqualityMachine.machine Alphabet).k₀ (WordEqualityMachine.machine Alphabet).main (default : Option Alphabet) id
    (compareSelectorBody) (equalityBody))
theorem compareBody_exact : compareBody = (Comparison.compareMachine).m := composition_exact (Indexed.machine Comparison.selector) (WordEqualityMachine.machine Alphabet) (Equiv.refl _) compareSelectorBody_exact equalityBody_exact

abbrev liftSymbol := Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.EncodedTable.ReferenceCheck.liftSymbol

local instance : Fintype ((WordHomomorphismMachine.machine liftSymbol).Γ (WordHomomorphismMachine.machine liftSymbol).k₁) := alphabet2Finite
local instance : Inhabited ((WordHomomorphismMachine.machine liftSymbol).Γ (WordHomomorphismMachine.machine liftSymbol).k₁) := alphabet2Default
def comparisonBody : (Comparison.machine).Λ → (Comparison.machine).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (WordHomomorphismMachine.machine liftSymbol).k₁ (Comparison.compareMachine).k₀ (Comparison.compareMachine).main (default : Option (Option Alphabet)) id
    (WordHomomorphismMachine.program liftSymbol) (compareBody))
theorem comparisonBody_exact : comparisonBody = (Comparison.machine).m := composition_exact (WordHomomorphismMachine.machine liftSymbol) Comparison.compareMachine (Equiv.refl _) rfl compareBody_exact

local instance : Fintype ((claimedMachine).Γ (claimedMachine).k₁) := alphabet1Finite
local instance : Inhabited ((claimedMachine).Γ (claimedMachine).k₁) := alphabet1Default
def preparedBody : (preparedMachine).Λ → (preparedMachine).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (claimedMachine).k₁ (projectedMachine).k₀ (projectedMachine).main (default : Option Alphabet) id
    (claimedBody) (projectedBody))
theorem preparedBody_exact : preparedBody = (preparedMachine).m := composition_exact claimedMachine projectedMachine (Equiv.refl _) claimedBody_exact projectedBody_exact

local instance : Fintype ((preparedMachine).Γ (preparedMachine).k₁) := alphabet1Finite
local instance : Inhabited ((preparedMachine).Γ (preparedMachine).k₁) := alphabet1Default
def successBody (label : successMachine.Λ) : successMachine.Stmt :=
  StackMachineComposition.Programs.body (FirstAlphabet := preparedMachine.Γ) (SecondAlphabet := Comparison.machine.Γ)
    (some (.inr (some (.inr WordTemplateMachine.Stack.input))))
    (some (.inl WordHomomorphismMachine.Stack.input))
    (.inl WordHomomorphismMachine.Phase.read) (none : Option Alphabet) id preparedBody comparisonBody label
theorem successBody_exact : successBody = (successMachine).m := composition_exact preparedMachine Comparison.machine (Equiv.refl _) preparedBody_exact comparisonBody_exact

def scopeSelectorBodyTable : { instructions : (Indexed.machine SourceQuantifierEmission.selector).Λ → (Indexed.machine SourceQuantifierEmission.selector).Stmt // instructions = (Indexed.machine SourceQuantifierEmission.selector).m } := by
  extract_rule_program (Indexed.machine SourceQuantifierEmission.selector).m
def scopeSelectorBody := scopeSelectorBodyTable.val
theorem scopeSelectorBody_exact : scopeSelectorBody = (Indexed.machine SourceQuantifierEmission.selector).m := scopeSelectorBodyTable.property

local instance : Fintype ((Indexed.machine SourceQuantifierEmission.selector).Γ (Indexed.machine SourceQuantifierEmission.selector).k₁) := alphabet0Finite
local instance : Inhabited ((Indexed.machine SourceQuantifierEmission.selector).Γ (Indexed.machine SourceQuantifierEmission.selector).k₁) := alphabet0Default
def scopeBody : (SourceQuantifierEmission.selectedScopeMachine).Λ → (SourceQuantifierEmission.selectedScopeMachine).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (Indexed.machine SourceQuantifierEmission.selector).k₁ (SourceQuantifierEmission.scopeMachine).k₀ (SourceQuantifierEmission.scopeMachine).main (default : Alphabet) id
    (scopeSelectorBody) (Mettapedia.GSLT.LanguageDef.PatternScopeExecution.OriginalAdmission.program))
theorem scopeBody_exact : scopeBody = (SourceQuantifierEmission.selectedScopeMachine).m := composition_exact (Indexed.machine SourceQuantifierEmission.selector) SourceQuantifierEmission.scopeMachine (Equiv.refl _) scopeSelectorBody_exact Mettapedia.GSLT.LanguageDef.PatternScopeExecution.OriginalAdmission.program_eq

def savedScopeBody : SourceQuantifierEmission.savedScopeMachine.Λ → SourceQuantifierEmission.savedScopeMachine.Stmt := by
  claim_program_literal_endpoints (RetainedWordExecution.Programs.body
    SourceQuantifierEmission.selectedScopeMachine.k₀ SourceQuantifierEmission.selectedScopeMachine.k₁
    SourceQuantifierEmission.selectedScopeMachine.initialState SourceQuantifierEmission.selectedScopeMachine.main
    (none : Option Alphabet) false AdmittedArgumentRendering.readResult scopeBody)
local instance : Inhabited (SourceQuantifierEmission.selectedScopeMachine.Γ SourceQuantifierEmission.selectedScopeMachine.k₀) := alphabet1Default
local instance : Fintype (SourceQuantifierEmission.selectedScopeMachine.Γ SourceQuantifierEmission.selectedScopeMachine.k₁) := alphabet5Finite
theorem savedScopeBody_exact : savedScopeBody = SourceQuantifierEmission.savedScopeMachine.m := by
  unfold savedScopeBody
  rw [scopeBody_exact]
  exact RetainedWordExecution.Programs.body_eq _ _

local instance : Fintype ((SourceQuantifierEmission.savedScopeMachine).Γ (SourceQuantifierEmission.savedScopeMachine).k₁) := alphabet4Finite
local instance : Inhabited ((SourceQuantifierEmission.savedScopeMachine).Γ (SourceQuantifierEmission.savedScopeMachine).k₁) := alphabet4Default
def admissionBody : (SourceQuantifierEmission.admissionMachine).Λ → (SourceQuantifierEmission.admissionMachine).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (SourceQuantifierEmission.savedScopeMachine).k₁ (WordHomomorphismMachine.machine SourceQuantifierEmission.project).k₀ (WordHomomorphismMachine.machine SourceQuantifierEmission.project).main (default : Option Alphabet ⊕ Bool) id
    (savedScopeBody) (WordHomomorphismMachine.program SourceQuantifierEmission.project))
theorem admissionBody_exact : admissionBody = (SourceQuantifierEmission.admissionMachine).m := composition_exact SourceQuantifierEmission.savedScopeMachine (WordHomomorphismMachine.machine SourceQuantifierEmission.project) (Equiv.refl _) savedScopeBody_exact rfl

def guardedBody (phase : guardedMachine.Λ) : guardedMachine.Stmt := by
  claim_program_literal_endpoints (match phase with
  | .run label => StackMachineRegisters.extend StackMachineComposition.Dispatch.Phase.run (successBody label)
  | .read => TM2.Stmt.pop successMachine.k₀ (fun state value => (state.1, value))
      (TM2.Stmt.branch (fun state => state.2.any SourceQuantifierEmission.accept)
        (TM2.Stmt.load (fun state => (state.1, none)) (TM2.Stmt.goto fun _ => .run successMachine.main))
        (TM2.Stmt.goto fun _ => .discard))
  | .discard => TM2.Stmt.pop successMachine.k₀ (fun state value => (state.1, value))
      (TM2.Stmt.branch (fun state => state.2.isSome) (TM2.Stmt.goto fun _ => .discard)
        (TM2.Stmt.push successMachine.k₁ (fun _ => false)
          (TM2.Stmt.load (fun _ => (successMachine.initialState, none)) TM2.Stmt.halt))))
private theorem dispatch_lift (statement : successMachine.Stmt) :
    StackMachineComposition.Dispatch.lift successMachine statement =
      StackMachineRegisters.extend StackMachineComposition.Dispatch.Phase.run statement := by
  induction statement <;> simp_all only [StackMachineComposition.Dispatch.lift, StackMachineRegisters.extend]
theorem guardedBody_exact : guardedBody = guardedMachine.m := by
  funext phase
  cases phase with
  | read => rfl
  | discard => rfl
  | run label =>
    change StackMachineRegisters.extend StackMachineComposition.Dispatch.Phase.run (successBody label) =
      StackMachineComposition.Dispatch.lift successMachine (successMachine.m label)
    exact (congrArg (StackMachineRegisters.extend StackMachineComposition.Dispatch.Phase.run)
      (congrFun successBody_exact label)).trans (dispatch_lift _).symm

local instance : Fintype ((SourceQuantifierEmission.admissionMachine).Γ (SourceQuantifierEmission.admissionMachine).k₁) := alphabet1Finite
local instance : Inhabited ((SourceQuantifierEmission.admissionMachine).Γ (SourceQuantifierEmission.admissionMachine).k₁) := alphabet1Default
def body : (target).Λ → (target).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (SourceQuantifierEmission.admissionMachine).k₁ (guardedMachine).k₀ (guardedMachine).main (default : Option Alphabet) id
    (admissionBody) (guardedBody))
theorem body_exact : body = (target).m := composition_exact SourceQuantifierEmission.admissionMachine guardedMachine (Equiv.refl _) admissionBody_exact guardedBody_exact

def keyEquality : DecidableEq target.K := by
  claim_program_key_equality

local instance : DecidableEq target.K := keyEquality

deriving instance DecidableEq for Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.Control
deriving instance DecidableEq for ArgumentRenderingMachine.Constructor.HeadFromMarkers.Control
deriving instance DecidableEq for ArgumentRenderingMachine.Constructor.Completion.Control
deriving instance DecidableEq for ArgumentRenderingMachine.Execution.Control

def registerEquality : DecidableEq target.σ := by
  claim_program_key_equality

def step := @TM2.step target.K target.Γ target.Λ target.σ keyEquality body

theorem step_exact : step = target.step := by
  unfold step
  rw [show keyEquality = target.kDecidableEq from Subsingleton.elim _ _, body_exact]
  rfl

def inputKey : target.K := by normalize_rule_program target.k₀
def resultKey : target.K := by normalize_rule_program target.k₁
def registers : target.σ := by normalize_rule_program target.initialState
def mainLabel : target.Λ := by normalize_rule_program target.main

def initial (word : List (Option Alphabet)) : target.Cfg where
  l := some mainLabel
  var := registers
  stk key := if same : key = inputKey then by cases same; exact word else []

theorem initial_exact (word : List (Option Alphabet)) : initial word = initList target word := by
  simp only [initial, initList]
  congr 1
  funext key
  by_cases same : key = inputKey
  · subst key
    have original : inputKey = target.k₀ := rfl
    simp only [dif_pos original]
    rfl
  · have original : key ≠ target.k₀ := same
    simp only [dif_neg same, dif_neg original]

open Lean Elab Tactic Meta in
private partial def concreteKeyValues (type : Expr) : MetaM (Array Expr) := do
  let type ← withTransparency .reducible (whnf type)
  match type.getAppFn.constName?, type.getAppArgs.toList with
  | some ``Option, [child] =>
    let children ← concreteKeyValues child
    let first ← mkAppOptM ``Option.none #[some child]
    let rest ← children.mapM fun value => mkAppOptM ``Option.some #[some child, some value]
    pure (#[first] ++ rest)
  | some ``Sum, [first, second] =>
    let left ← (← concreteKeyValues first).mapM fun value =>
      mkAppOptM ``Sum.inl #[some first, some second, some value]
    let right ← (← concreteKeyValues second).mapM fun value =>
      mkAppOptM ``Sum.inr #[some first, some second, some value]
    pure (left ++ right)
  | some name, arguments =>
    let info ← getConstInfoInduct name
    unless info.numIndices == 0 do throwError "Indexed key type {type} needs an explicit enumeration"
    let mut values := #[]
    for name in info.ctors do
      let constructor ← mkAppOptM name (arguments.toArray.map some)
      let rec finish (constructor : Expr) : MetaM (Array Expr) := do
        let constructorType ← withTransparency .reducible (whnf (← inferType constructor))
        match constructorType with
        | .forallE _ field _ _ =>
          let mut result := #[]
          for value in ← concreteKeyValues field do
            result := result ++ (← finish (mkApp constructor value))
          pure result
        | _ =>
          unless ← isDefEq constructorType type do throwError "Mismatched key constructor {name}"
          pure #[constructor]
      values := values ++ (← finish constructor)
    pure values
  | _, _ => throwError "Unsupported key type {type}"

open Lean Elab Tactic Meta in
elab "claim_program_keys" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let type ← goal.getType
    let keyType := type.getAppArgs.back!
    goal.assign (← mkListLit keyType (← concreteKeyValues keyType).toList)
  replaceMainGoal []

def keys : List target.K := by claim_program_keys

local instance : BEq target.K := ⟨fun a b => decide (a = b)⟩
local instance : LawfulBEq target.K where
  eq_of_beq h := of_decide_eq_true h
  rfl := by intro a; exact decide_eq_true rfl
noncomputable local instance : Fintype target.K := target.kFin

theorem all_keys : ∀ key : target.K, key ∈ keys := by
  decide +kernel

theorem keys_nodup : keys.Nodup := by
  decide +kernel


open StackMachineRegisters.StackSnapshot

def refresh (state : target.Cfg) : target.Cfg :=
  let cells := snapshot target.Γ state.stk keys
  {state with stk := fun key => lookup target.Γ cells key}

theorem refresh_exact (state : target.Cfg) : refresh state = state := by
  cases state with
  | mk label savedRegisters contents =>
    dsimp only [refresh]
    congr 1
    funext key
    exact lookup_snapshot target.Γ contents keys key (all_keys key)


def periodicRefresh (period used : Nat) (state : target.Cfg) : target.Cfg :=
  if used % period == 0 then refresh state else state

theorem periodicRefresh_exact (period used : Nat) (state : target.Cfg) :
    periodicRefresh period used state = state := by
  unfold periodicRefresh
  split <;> simp only [refresh_exact]

def run (period : Nat) : Nat → Nat → target.Cfg → Option (Nat × target.Cfg)
  | 0, _, _ => none
  | fuel+1, used, state =>
    if state.l.isNone then some (used,state)
    else match step state with
      | none => none
      | some next => run period fuel (used+1) (periodicRefresh period (used+1) next)


theorem run_actual (period fuel used : Nat) (before : target.Cfg)
    {count : Nat} {after : target.Cfg}
    (completed : run period fuel used before = some (count,after)) :
    used ≤ count ∧
      (∃ path : StateTransition.EvalsToInTime target.step before (some after) (count-used),
        path.steps = count-used) ∧
      after.l = none := by
  induction fuel generalizing used before with
  | zero => cases completed
  | succ fuel ih =>
    simp only [run] at completed
    split at completed
    · rename_i halted
      have pair := Option.some.inj completed
      have countSame := congrArg Prod.fst pair
      have stateSame := congrArg Prod.snd pair
      change used = count at countSame
      change before = after at stateSame
      subst count
      subst after
      refine ⟨le_rfl,?_,Option.isNone_iff_eq_none.mp halted⟩
      rw [Nat.sub_self]
      exact ⟨StateTransition.EvalsToInTime.refl target.step before,rfl⟩
    · cases advanced : step before with
      | none => simp only [advanced,reduceCtorEq] at completed
      | some next =>
        simp only [advanced] at completed
        rw [periodicRefresh_exact] at completed
        rcases ih (used+1) next completed with ⟨countBound,⟨tail,tailCount⟩,halted⟩
        have original : target.step before = some next := by
          rw [← step_exact]
          exact advanced
        let first : StateTransition.EvalsToInTime target.step before (some next) 1 :=
          ⟨⟨1,by change (some before).bind target.step = some next; exact original⟩,le_rfl⟩
        have relative : count-used = (count-(used+1))+1 := by omega
        refine ⟨by omega,?_,halted⟩
        rw [relative]
        refine ⟨StateTransition.EvalsToInTime.trans target.step 1 (count-(used+1))
          before next (some after) first tail,?_⟩
        change tail.steps+first.steps = (count-(used+1))+1
        rw [tailCount]


end Mettapedia.Languages.HOLLight.ClaimCheckingProgram
