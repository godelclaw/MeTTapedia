import Mettapedia.Languages.HOLLight.DynamicModusPonensProgram
import Mettapedia.Computability.TreeStackSnapshot

/-!
# Exact changing-MP execution with materialized snapshots

The original instruction view and counted transitions are unchanged. Cached
stack and finite-register rows are retained as data before constructing each
refreshed configuration. The executor supplies the snapshot period, which
changes no formal machine step bound.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
namespace Mettapedia.Languages.HOLLight.DynamicModusPonensTreeProgram
open Turing Lean Elab Tactic Meta
open Mettapedia.Computability.TreeStackSnapshot

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine Mettapedia.Languages.HOLLight.DynamicModusPonensEmission
attribute [local reducible] FinTM2.Cfg
 DynamicModusPonensEmission.machine routedMachine supportsMachine theoremFieldsMachine
 retainedUnionMachine selectedUnionMachine unionBody unionStrip retainedAxiomMachine selectedAxiomMachine axiomMachine
 selector
 AuthoredAxiomUnion.machine AuthoredAxiomUnion.preparedMachine AuthoredAxiomUnion.core AuthoredAxiomUnion.scanner
 AuthoredAxiomUnion.assembler AuthoredAxiomUnion.strippedFramer AuthoredAxiomUnion.rawIdentity
 AuthoredListFraming.machine FiniteWordClassifier.Union.machine
 FramedFieldSelection.machine
 StackMachineComposition.machine StackMachineComposition.Dispatch.machine
 StackMachineComposition.liftFirst StackMachineComposition.liftSecond StackMachineComposition.Dispatch.lift
 StackMachineComposition.leftKey StackMachineComposition.rightKey
 RetainedWordExecution.WithOutput.Framed.machine RetainedWordExecution.WithOutput.Framed.taggedMachine
 RetainedWordExecution.WithOutput.Framed.untag
 RetainedWordExecution.WithOutput.machine RetainedWordExecution.WithOutput.statement RetainedWordExecution.WithOutput.body
 FramedWordMapping.machine FramedWordMapping.statement FramedWordMapping.body FramedWordMapping.initial
 WordHomomorphismMachine.machine WordTemplateMachine.machine Indexed.machine Indexed.Alphabet
 SourceQuantifierEmission.stripStatus SourceQuantifierEmission.rawIdentity
 Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.machine
 Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.PrefixField.machine
 Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming.ListAssembly.machine


abbrev target (basis : AuthoredAxiomUnion.Basis) := DynamicModusPonensProgram.target basis

def cachedStacks (basis : AuthoredAxiomUnion.Basis) (values : ∀ key, List ((target basis).Γ key)) :
    Snapshot (target basis).K (fun key => List ((target basis).Γ key)) := by typed_tree_cache values

theorem cachedStacks_exact (basis : AuthoredAxiomUnion.Basis) (values : ∀ key, List ((target basis).Γ key)) :
    (cachedStacks basis values).read=values := by
  unfold cachedStacks
  repeat' first
    | exact leaf_identity _ _ _
    | apply option_identity; intro branchValues
    | apply sum_identity <;> intro branchValues

private partial def makeRegisters (type value : Expr) : MetaM Expr := do
  let type ← withTransparency .all (whnf type)
  match type with
  | .forallE _ indexType _ _ =>
    let indexType ← withTransparency .all (whnf indexType)
    unless indexType.isAppOf ``Fin do throwError "Expected finite numeric register index"
    let defaults ← withLocalDeclD `index indexType fun index => do
      let cellType ← withTransparency .all (whnf (← inferType (mkApp value index)))
      let fallback ← match cellType.getAppFn.constName? with
        | some ``Option => mkAppOptM ``Option.none #[some cellType.getAppArgs.back!]
        | some ``Bool => pure (mkConst ``Bool.false)
        | _ => throwError "Unsupported register cell: {cellType}"
      mkLambdaFVars #[index] fallback
    let cached ← mkAppM ``functionCache #[defaults,value]
    mkAppM ``Snapshot.read #[cached]
  | _ =>
    match type.getAppFn.constName?,type.getAppArgs.toList with
    | some ``Prod,[_,_] =>
      let a := Expr.proj ``Prod 0 value
      let b := Expr.proj ``Prod 1 value
      mkAppM ``Prod.mk #[(← makeRegisters (← inferType a) a),(← makeRegisters (← inferType b) b)]
    | some ``Mettapedia.Computability.FiniteWordClassifier.Union.State,_ =>
      let a := Expr.proj ``Mettapedia.Computability.FiniteWordClassifier.Union.State 0 value
      let b := Expr.proj ``Mettapedia.Computability.FiniteWordClassifier.Union.State 1 value
      mkAppM ``Mettapedia.Computability.FiniteWordClassifier.Union.State.mk #[(← makeRegisters (← inferType a) a),(← makeRegisters (← inferType b) b),
        Expr.proj ``Mettapedia.Computability.FiniteWordClassifier.Union.State 2 value,
        Expr.proj ``Mettapedia.Computability.FiniteWordClassifier.Union.State 3 value,
        Expr.proj ``Mettapedia.Computability.FiniteWordClassifier.Union.State 4 value]
    | _,_ => pure value

elab "materialized_registers " expression:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let value ← Term.elabTerm expression (← goal.getType)
    goal.assign (← makeRegisters (← inferType value) value)
  replaceMainGoal []

def refreshRegisters (basis : AuthoredAxiomUnion.Basis) (values : (target basis).σ) : (target basis).σ := by materialized_registers values

theorem refreshRegisters_exact (basis : AuthoredAxiomUnion.Basis) (values : (target basis).σ) :
    refreshRegisters basis values=values := by
  simp only [refreshRegisters,function_identity]

def refresh (basis : AuthoredAxiomUnion.Basis) (state : (target basis).Cfg) : (target basis).Cfg :=
  let cached := cachedStacks basis state.stk
  ⟨state.l,refreshRegisters basis state.var,cached.read⟩

theorem refresh_exact (basis : AuthoredAxiomUnion.Basis) (state : (target basis).Cfg) : refresh basis state=state := by
  dsimp only [refresh]
  rw [refreshRegisters_exact,cachedStacks_exact]

def periodicRefresh (basis : AuthoredAxiomUnion.Basis) (period used : Nat) (state : (target basis).Cfg) : (target basis).Cfg :=
  if used % period == 0 then refresh basis state else state

theorem periodicRefresh_exact (basis : AuthoredAxiomUnion.Basis) (period used : Nat) (state : (target basis).Cfg) :
    periodicRefresh basis period used state=state := by
  unfold periodicRefresh
  split <;> simp only [refresh_exact]

def run (basis : AuthoredAxiomUnion.Basis) (period : Nat) : Nat → Nat → (target basis).Cfg → Option (Nat × (target basis).Cfg)
  | 0,_,_ => none
  | fuel+1,used,state =>
    if state.l.isNone then some (used,state)
    else match DynamicModusPonensProgram.step basis state with
      | none => none
      | some next => run basis period fuel (used+1) (periodicRefresh basis period (used+1) next)

theorem run_exact (basis : AuthoredAxiomUnion.Basis) (period fuel used : Nat) (before : (target basis).Cfg) :
    run basis period fuel used before = DynamicModusPonensProgram.run basis period fuel used before := by
  induction fuel generalizing used before with
  | zero => rfl
  | succ fuel ih =>
    simp only [run,DynamicModusPonensProgram.run]
    split
    · rfl
    · cases advanced : DynamicModusPonensProgram.step basis before with
      | none => rfl
      | some next =>
        dsimp only
        rw [periodicRefresh_exact,DynamicModusPonensProgram.periodicRefresh_exact,ih]

theorem run_actual (basis : AuthoredAxiomUnion.Basis) (period fuel used : Nat) (before : (target basis).Cfg)
    {count : Nat} {after : (target basis).Cfg}
    (completed : run basis period fuel used before = some (count,after)) :
    used ≤ count ∧
      (∃ path : StateTransition.EvalsToInTime (target basis).step before (some after) (count-used),
        path.steps = count-used) ∧ after.l=none := by
  rw [run_exact] at completed
  exact DynamicModusPonensProgram.run_actual basis period fuel used before completed

end Mettapedia.Languages.HOLLight.DynamicModusPonensTreeProgram
