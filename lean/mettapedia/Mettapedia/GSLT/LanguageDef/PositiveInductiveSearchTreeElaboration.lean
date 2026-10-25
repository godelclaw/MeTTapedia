import Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeGuest
import Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeGuestControls
import Mettapedia.GSLT.LanguageDef.IndexedInductiveOperationSource
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestPlans
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.IntrinsicNativeListMapComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation

/-!
# Source folds through the registered List SearchTree eliminator

The branch eliminator supplies a List of child/result pairs together with
source-correspondence evidence. Ordinary fold clauses instead consume a
List of recursive results. The adapter uses the intrinsic List eliminator
to project the second component of each pair. It does not reinterpret the
source children as recursive results or discard the dependent check.

The finite source-expression reader and independent formation-sensitive
replay remain separate. The computation statements concern the selected
declarations, not admission of arbitrary raw nested iota equations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeElaboration

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeIndexedFamilies
open RussellTarski
open SchemaElaboration
open PositiveInductiveSearchTreeGuest
open IntrinsicNativeListMapComputation (mapped)
open TypedEquality.Normalization (defaultTm)

variable {n m : Nat}

def constantMotive (result : Tower.Tm n) : Tower.Tm n :=
  .lam (rename wk result)

/-- Project results by a real List-eliminator program. The input retains its
complete child/result relation; this operation exposes its result view. -/
def bundleResults (tree result bundle : Tower.Tm n) : Tower.Tm n :=
  mapped (packedType tree (constantMotive result)) result
    (.lam (.snd (.var 0))) (.fst bundle)

def solvedMethod (function : Tower.Tm n) : Tower.Tm n :=
  .lam (.app (rename wk function) (.var 0))

/-- The source method takes children and results; the dependent method takes
children and their proof-relevant bundle. -/
def branchMethod (tree result node : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.app (weaken2 node)
    (bundleResults (weaken2 tree) (weaken2 result) (.var 0))))

def fold (answer result leaf node input : Tower.Tm n) : Tower.Tm n :=
  eliminateApp answer (constantMotive result) (solvedMethod leaf)
    (branchMethod (treeApp answer) result node) input

def foldType : Tower.Tm 0 :=
  .pi (sortTm level) (.pi (sortTm level)
    (.pi (arrow (.var 1) (.var 0))
      (.pi (arrow (Intrinsic.listApp (.var 1)) (.var 1))
        (.pi (treeApp (.var 3)) (.var 3)))))

def foldTerm : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (.lam
    (fold (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))))))

theorem fold_checked : endpointAccepted .nil foldTerm foldType = true := by
  decide +kernel

/-- The actual term, including both List traversals and the dependent branch
adapter, passes the existing independent typing replay. -/
theorem fold_typed :
    FormationSensitive.Judgment inventoryRules .nil foldTerm foldType :=
  endpointAccepted_sound fold_checked

/-! ## The result view of the actual recursive bundle -/

abbrev Reduces (left right : Tower.Tm n) :=
  IntrinsicNativeListMapComputation.Reduces level left right

private theorem reducesFst {left right : Tower.Tm n} (path : Reduces left right) :
    Reduces (.fst left) (.fst right) := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec
    (IntrinsicNativeListMapComputation.reduction level n)
    (fun left right _ => Reduces (.fst left) (.fst right))
    (fun _ => .refl _) (fun {_ _ _} step _ ih => .step (.congFst step) ih)
    left right path

private def executableRules : Rules Tower.Head :=
  { IntrinsicMaps.listRulesAt level with headEq := fun _ _ => False }

private theorem reducesOfTypedClosure {left right : Tower.Tm n}
    (path : TypedEquality.Reduces executableRules left right) : Reduces left right := by
  induction path with
  | refl => exact .refl _
  | tail _ step ih => exact ih.trans (.step step (.refl _))

private theorem betaThree (body : Tower.Tm (n + 3)) (first second third : Tower.Tm n) :
    Reduces (.app (.app (.app (.lam (.lam (.lam body))) first) second) third)
      (subst (consSub third (consSub second (consSub first ids))) body) := by
  have path := TypedEquality.Normalization.lams_beta (R := executableRules)
    3 body [first, second, third] rfl
  have assignments : TypedEquality.Normalization.extendSub ids
      (fun index => [first, second, third].getD index defaultTm) 3 =
      consSub third (consSub second (consSub first ids)) := rfl
  rw [assignments] at path
  exact reducesOfTypedClosure path

/-- Applying the actual closed program reaches the eliminator body used by
the bundle-computation theorem, using only beta steps. -/
theorem foldTerm_beta (answer result leaf node input : Tower.Tm n) :
    Reduces
      (TypedEquality.Normalization.appSpine (liftClosed foldTerm)
        [answer, result, leaf, node, input])
      (fold answer result leaf node input) := by
  apply reducesOfTypedClosure
  open TypedEquality.Normalization in
  have path := lams_beta (R := executableRules) 5
    (rename (liftRen (liftRen (liftRen (liftRen (liftRen Fin.elim0)))))
      (fold (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)))
    [answer, result, leaf, node, input] rfl
  rw [subst_rename] at path
  let assignment : Sub Tower.Head 5 n :=
    consSub input (consSub node (consSub leaf (consSub result (consSub answer Fin.elim0))))
  have sameAssignment : (fun index =>
      TypedEquality.Normalization.extendSub ids
        (fun j => [answer, result, leaf, node, input].getD j defaultTm) 5
        (liftRen (liftRen (liftRen (liftRen (liftRen Fin.elim0)))) index)) = assignment := by
    funext index
    fin_cases index <;> rfl
  rw [sameAssignment] at path
  convert path using 1
  · rfl
  · simp [assignment, consSub, fold, constantMotive, solvedMethod,
      branchMethod, bundleResults, IntrinsicNativeListMapComputation.mapped,
      IntrinsicNativeListMapComputation.motive, IntrinsicNativeListMapComputation.branch,
      weaken1, weaken2, packedType, eliminateApp, treeApp, Intrinsic.eliminateApp,
      Intrinsic.consApp, Intrinsic.nilApp, Intrinsic.listApp, subst, rename,
      wk, liftSub, Fin.cases, Fin.induction, Fin.induction.go, rename_comp]
    dsimp [liftRen, Fin.cases, Fin.induction, Fin.induction.go]
    simp [rename_comp]

private theorem finOne (n : Nat) : (1 : Fin (n + 2)) = (0 : Fin (n + 1)).succ := by
  apply Fin.ext
  change 1 % (n + 2) = 0 + 1
  exact Nat.mod_eq_of_lt (by omega)

private theorem finTwo (n : Nat) : (2 : Fin (n + 3)) = (0 : Fin (n + 1)).succ.succ := by
  apply Fin.ext
  change 2 % (n + 3) = 0 + 1 + 1
  exact Nat.mod_eq_of_lt (by omega)

private theorem substVariables (rho : Ren n m) (term : Tower.Tm n) :
    subst (fun index => .var (rho index)) term = rename rho term :=
  subst_renSub rho term

def packedChild (answer motive solvedCase branchCase child : Tower.Tm n) : Tower.Tm n :=
  .pair child (eliminateApp answer motive solvedCase branchCase child)

def consBundleResult
    (answer motive solvedCase branchCase head tail bundle : Tower.Tm n) : Tower.Tm n :=
  let tree := treeApp answer
  let packed := packedType tree motive
  let relation := packedRelation tree
  let item := packedChild answer motive solvedCase branchCase head
  .pair (Intrinsic.consApp packed item (.fst bundle))
    (IntrinsicRelator.consRelApp tree packed relation head item tail
      (.fst bundle) (.refl head) (.snd bundle))

theorem consBundleCase_beta
    (answer motive solvedCase branchCase head tail bundle : Tower.Tm n) :
    Reduces (.app (.app (.app
      (consBundleCase answer motive solvedCase branchCase) head) tail) bundle)
      (consBundleResult answer motive solvedCase branchCase head tail bundle) := by
  unfold consBundleCase
  convert betaThree _ head tail bundle using 1
  simp [consBundleResult, packedChild, weaken1, weaken2, weaken3,
    subst_rename, consSub, ids, subst, rename, eliminateApp, treeApp, wk,
    liftSub, finOne, finTwo, substVariables,
    packedType, packedRelation, Intrinsic.consApp, IntrinsicRelator.consRelApp,
    -Fin.succ_zero_eq_one, -Fin.succ_one_eq_two,
    -Fin.succ_zero_eq_one', -Fin.succ_one_eq_two']

/-- The proof-relevant recursion traverses the source children in their
original order. Its first projection contains the exact child/call pairs. -/
theorem liftChildren_fst_encode
    (answer motive solvedCase branchCase : Tower.Tm n) (children : List (Tower.Tm n)) :
    Reduces (.fst (liftChildren answer motive solvedCase branchCase
      (IntrinsicNativeListMapComputation.encode (treeApp answer) children)))
      (IntrinsicNativeListMapComputation.encode (packedType (treeApp answer) motive)
        (children.map (packedChild answer motive solvedCase branchCase))) := by
  induction children with
  | nil =>
      exact .step (.congFst (.root (.declared ⟨.nil _ _ _ _⟩)))
        (.step (.betaSigmaFst _ _) (.refl _))
  | cons head tail ih =>
      have unfoldList : Reduces
          (liftChildren answer motive solvedCase branchCase
            (IntrinsicNativeListMapComputation.encode (treeApp answer) (head :: tail)))
          (.app (.app (.app (consBundleCase answer motive solvedCase branchCase) head)
            (IntrinsicNativeListMapComputation.encode (treeApp answer) tail))
            (liftChildren answer motive solvedCase branchCase
              (IntrinsicNativeListMapComputation.encode (treeApp answer) tail))) :=
        .step (.root (.declared ⟨.cons _ _ _ _ _ _⟩)) (.refl _)
      refine (reducesFst (unfoldList.trans (consBundleCase_beta _ _ _ _ _ _ _))).trans ?_
      refine Mettapedia.GSLT.GSLT.MultiStep.step (.betaSigmaFst _ _) ?_
      exact ih.appArg _

def recursiveFunction (answer motive solvedCase branchCase : Tower.Tm n) : Tower.Tm n :=
  .lam (eliminateApp (rename wk answer) (rename wk motive)
    (rename wk solvedCase) (rename wk branchCase) (.var 0))

/-- Both source `map` and the dependent bundle adapter reach the same exact
result List. Recursive child computations remain object-level calls. -/
theorem bundleResults_common_output
    (answer result solvedCase branchCase : Tower.Tm n) (children : List (Tower.Tm n)) :
    let motive := constantMotive result
    let output := IntrinsicNativeListMapComputation.encode result
      (children.map (eliminateApp answer motive solvedCase branchCase))
    Reduces (bundleResults (treeApp answer) result
      (liftChildren answer motive solvedCase branchCase
        (IntrinsicNativeListMapComputation.encode (treeApp answer) children))) output ∧
    Reduces (mapped (treeApp answer) result
      (recursiveFunction answer motive solvedCase branchCase)
      (IntrinsicNativeListMapComputation.encode (treeApp answer) children)) output := by
  dsimp only
  constructor
  · have view := liftChildren_fst_encode answer (constantMotive result) solvedCase branchCase children
    refine (view.appArg _).trans ?_
    refine (IntrinsicNativeListMapComputation.mapped_encode level _ _ _ _).trans ?_
    have pointwise := IntrinsicNativeListMapComputation.encode_pointwise level result
      (fun child => .app (.lam (.snd (.var 0)))
        (packedChild answer (constantMotive result) solvedCase branchCase child))
      (eliminateApp answer (constantMotive result) solvedCase branchCase) children
      (fun child _ => .step (.betaPi _ _) (.step (.betaSigmaSnd _ _) (.refl _)))
    simpa only [List.map_map, Function.comp_def] using pointwise
  · refine (IntrinsicNativeListMapComputation.mapped_encode level _ _ _ children).trans ?_
    apply IntrinsicNativeListMapComputation.encode_pointwise
    intro child _
    simpa only [recursiveFunction, eliminateApp, inst0, subst,
      subst_rename, subst0_succ, subst0_zero, wk,
      show (fun index : Fin n => Tm.var index) = (ids : Sub Tower.Head n n) from rfl,
      subst_ids] using
      IntrinsicNativeListMapComputation.Reduces.beta level
        (eliminateApp (rename wk answer) (rename wk (constantMotive result))
          (rename wk solvedCase) (rename wk branchCase) (.var 0)) child

/-! ## Authored clauses and independent typed replay -/

open Mettapedia.OSLF.MeTTaIL.Syntax
open IndexedInductive.CaseElaboration IndexedInductive.OperationSource

section SourceReader

open ModuleSource.Commands

#module_file "../../../../../metta/gslt/module/IndexedSearchTreeFold.module"
#module_roundtrip AgentSearch

end SourceReader

def selfName : DeclName := `Authored.SearchTree.fold

def sourceCall (answer result leaf node child : Tower.Tm n) : Tower.Tm n :=
  Declaration.IndexedFamily.applyArgs (.const selfName) [answer, result, leaf, node, child]

/-- The explicitly selected source-library operation `MapFold` expands to
the existing intrinsic List map with the authored recursive function. -/
def sourceMap (answer result leaf node children : Tower.Tm n) : Tower.Tm n :=
  mapped (treeApp answer) result
    (.lam (sourceCall (rename wk answer) (rename wk result)
      (rename wk leaf) (rename wk node) (.var 0))) children

theorem sourceMap_substitute (substitution : Sub Tower.Head n m)
    (answer result leaf node children : Tower.Tm n) :
    subst substitution (sourceMap answer result leaf node children) =
      sourceMap (subst substitution answer) (subst substitution result)
        (subst substitution leaf) (subst substitution node) (subst substitution children) := by
  have shift3 (term : Tower.Tm n) :
      subst (liftSub (liftSub (liftSub substitution)))
          (rename (fun i => i.succ.succ.succ) term) =
        rename (fun i => i.succ.succ.succ) (subst substitution term) :=
    subst_weaken3 substitution term
  simp [sourceMap, IntrinsicNativeListMapComputation.mapped,
    IntrinsicNativeListMapComputation.motive, IntrinsicNativeListMapComputation.branch,
    Intrinsic.eliminateApp, Intrinsic.nilApp, Intrinsic.consApp, Intrinsic.listApp,
    shift3, subst, sourceCall, Declaration.IndexedFamily.applyArgs, treeApp]

/-- Calls are instantiated at the actual recursive fields by the generic
code scan. Every registered nested field here is the source List operation. -/
def sourceCallSyntax : IndexedPositiveContainerGuestPlans.CallSyntax
    ModuleSource.PositiveInductiveLoweringControls.Search.interface
    (Mettapedia.TypeTheory.IndexedPositiveContainer.Unindexed.liftRegistry
      ModuleSource.PositiveInductiveLoweringControls.Search.registry
      ModuleSource.PositiveInductiveLoweringControls.Search.interface) Tower.Head 4 where
  direct outer _ _ child := sourceCall (outer 3) (outer 2) (outer 1) (outer 0) child
  nested _ _ _ outer _ _ _ children :=
    sourceMap (outer 3) (outer 2) (outer 1) (outer 0) children
  direct_substitute := by
    intros
    simp [sourceCall, Declaration.IndexedFamily.applyArgs, subst]
  nested_substitute := by
    intros
    exact sourceMap_substitute _ _ _ _ _ _

def sourceSymbols : List (Symbol Tower.Head) :=
  [⟨"Apply", 2, .app (.var 1) (.var 0)⟩,
   ⟨"solved", 2, solvedApp (.var 1) (.var 0)⟩,
   ⟨"branch", 2, branchApp (.var 1) (.var 0)⟩,
   ⟨"Fold", 5, sourceCall (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)⟩,
   ⟨"MapFold", 5, sourceMap (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)⟩]

/-- Derive all field and call positions from the admitted code, including
interleaved data, direct and registered-List fields. The whole source-program
reader below still selects the established SearchTree family and headers. -/
def sourcePlan
    (constructor : ModuleSource.PositiveInductiveLowering.ResolvedConstructor
      (registry := ModuleSource.PositiveInductiveLoweringControls.Search.registry)
      (I := ModuleSource.PositiveInductiveLoweringControls.Search.interface)
      (parameterCount := 1) []) : Option (BranchPlan Tower.Head 4) :=
  some (IndexedPositiveContainerGuestPlans.plan sourceCallSyntax constructor.name
    constructor.body.eraseIndexed)

def sourceHeader (plan : BranchPlan Tower.Head 4) : Header 4 :=
  Header.fromPlan plan "Fold" [3]

def applyMethod (method argument : Tower.Tm n) : Tower.Tm n :=
  match method with
  | .lam body => inst0 argument body
  | _ => .app method argument

theorem applyMethod_reduces {R : Rules Tower.Head} (method argument : Tower.Tm n) :
    TypedEquality.Reduces R (.app method argument) (applyMethod method argument) := by
  cases method <;> try exact .refl
  exact .single (.betaPi _ _)

/-- Adapt a source branch that expects a List of results to the actual
proof-relevant dependent branch ABI. Opening the generated method performs
only ordinary beta steps and permits independent bidirectional replay. -/
def adaptBranch (tree result method : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (applyMethod (applyMethod (weaken2 method) (.var 1))
    (bundleResults (weaken2 tree) (weaken2 result) (.var 0))))

def emitFold (solved branch : Tower.Tm 4) : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (.lam
    (eliminateApp (.var 4) (constantMotive (.var 3)) (rename wk solved)
      (rename wk (adaptBranch (treeApp (.var 3)) (.var 2) branch)) (.var 0))))))

structure Proposed where
  plans : List (BranchPlan Tower.Head 4)
  clauses : List (Clause Tower.Head 4)
  methods : List (Tower.Tm 4)
  function : Tower.Tm 0

/-- The declaration check pins this selected source library. Successful
source production alone grants no typing or inference authority. -/
def propose (source : ModuleSource.Module) : Option Proposed := do
  let selected ← selectModule source
  if selected.families ≠ [ModuleSource.PositiveInductiveLoweringControls.Search.textualFamily] then none else
    match ModuleSource.PositiveInductiveLowering.lowerModule
        ModuleSource.PositiveInductiveLoweringControls.Search.codec selected.declarations with
    | none => none
    | some resolved => do
        let plans ← (resolved.family.constructors.map sourcePlan).mapM id
        if plans.length ≠ selected.rules.length then none else do
          let clauses ← (plans.zip selected.rules).mapM fun (plan, rule) =>
            (readRule sourceSymbols 64 (sourceHeader plan) rule).map (·.toClause)
          let methods ← compilePlans plans selfName clauses
          match methods with
          | [solved, branch] => some ⟨plans, clauses, methods, emitFold solved branch⟩
          | _ => none

def proposedFunction : Option (Tower.Tm 0) := (propose AgentSearch.module).map (·.function)

def sourceMethods : List (Tower.Tm 4) :=
  [solvedMethod (.var 1), .lam (.lam (.app (.var 2) (.var 0)))]

theorem methods_emitted : (propose AgentSearch.module).map (·.methods) = some sourceMethods := by
  decide +kernel

theorem source_declarations_exact :
    (selectModule AgentSearch.module).map (·.declarations) =
      some ModuleSource.PositiveInductiveLoweringControls.Search.textualModule := by
  rfl

theorem function_emitted : proposedFunction = some
    (emitFold (solvedMethod (.var 1)) (.lam (.lam (.app (.var 2) (.var 0))))) := by
  decide +kernel

theorem emitted_checked : endpointAccepted .nil
    (emitFold (solvedMethod (.var 1)) (.lam (.lam (.app (.var 2) (.var 0))))) foldType = true := by
  decide +kernel

/-- A source-produced function is checked including its emitted adapter;
the independently authored direct fold is not substituted for this term. -/
theorem source_typed (term : Tower.Tm 0) (emitted : proposedFunction = some term) :
    FormationSensitive.Judgment inventoryRules .nil term foldType := by
  rw [function_emitted] at emitted
  cases Option.some.inj emitted
  exact endpointAccepted_sound emitted_checked

theorem source_application (term : Tower.Tm 0) (emitted : proposedFunction = some term)
    (answer result leaf node input : Tower.Tm n) :
    Reduces
      (TypedEquality.Normalization.appSpine (liftClosed term)
        [answer, result, leaf, node, input])
      (PositiveInductiveSearchTreeElaboration.fold answer result leaf node input) := by
  rw [function_emitted] at emitted
  cases Option.some.inj emitted
  exact foldTerm_beta answer result leaf node input

theorem authored_fold_typed :
    FormationSensitive.Judgment inventoryRules .nil
      (emitFold (solvedMethod (.var 1)) (.lam (.lam (.app (.var 2) (.var 0))))) foldType :=
  source_typed _ function_emitted

theorem authored_fold_application (answer result leaf node input : Tower.Tm n) :
    Reduces (TypedEquality.Normalization.appSpine
      (liftClosed (emitFold (solvedMethod (.var 1)) (.lam (.lam (.app (.var 2) (.var 0))))))
      [answer, result, leaf, node, input])
      (PositiveInductiveSearchTreeElaboration.fold answer result leaf node input) :=
  source_application _ function_emitted answer result leaf node input

def selectedPlans : List (BranchPlan Tower.Head 4) :=
  ((propose AgentSearch.module).map (·.plans)).getD []

def selectedClauses : List (Clause Tower.Head 4) :=
  ((propose AgentSearch.module).map (·.clauses)).getD []

theorem selected_plans_derived : selectedPlans =
    [⟨"solved", 1, []⟩, ⟨"branch", 1,
      [sourceMap (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)]⟩] := by
  decide +kernel

theorem selected_compilation :
    compilePlans selectedPlans selfName selectedClauses = some sourceMethods := by
  decide +kernel

/-- Every actual emitted source method reconstructs its submitted clause,
in the constructor order obtained from the admitted source block. -/
theorem source_methods_reconstruct :
    sourceMethods.length = selectedPlans.length ∧
    List.Forall₂ (fun pair compiled => ∃ source,
      adaptFields pair.1.name pair.1.fields pair.2 = some source ∧
      TypedEquality.Reduces inventoryRules
        (TypedEquality.Normalization.appSpine
          (rename (TypedEquality.Normalization.wkN pair.1.fields) compiled)
          (TypedEquality.Normalization.fieldVars 4 pair.1.fields ++ pair.1.recursiveCalls)) source)
      (selectedPlans.zip selectedClauses) sourceMethods :=
  compilePlans_reduces selectedPlans selfName selectedClauses sourceMethods selected_compilation

def checkProposal (source : ModuleSource.Module) : Bool :=
  match propose source with
  | none => false
  | some proposed => endpointAccepted .nil proposed.function foldType

theorem checkProposal_sound (source : ModuleSource.Module) (checked : checkProposal source = true) :
    ∃ proposed, propose source = some proposed ∧
      FormationSensitive.Judgment inventoryRules .nil proposed.function foldType := by
  cases emitted : propose source with
  | none => simp [checkProposal, emitted] at checked
  | some proposed =>
      exact ⟨proposed, rfl, endpointAccepted_sound (by
        simpa only [checkProposal, emitted] using checked)⟩

def changedRules (change : List RewriteRule → List RewriteRule) : Option ModuleSource.Module :=
  (selectModule AgentSearch.module).map fun selected =>
    { selected with rules := change selected.rules }.assemble

def changedProposal (change : List RewriteRule → List RewriteRule) : Bool :=
  match changedRules change with
  | none => false
  | some source => checkProposal source

def changedProducer (change : List RewriteRule → List RewriteRule) : Bool :=
  match changedRules change with
  | none => false
  | some source => (propose source).isSome

def replaceBranch (body : Pattern) (rules : List RewriteRule) : List RewriteRule :=
  rules.mapIdx fun index rule => if index = 1 then { rule with right := body } else rule

def sourceChildrenAsResults : Pattern :=
  .apply "Apply" [.fvar "node", .fvar "children"]

def wrongRecursiveInput : Pattern :=
  .apply "Apply" [.fvar "node", .apply "MapFold"
    [.fvar "A", .fvar "B", .fvar "leaf", .fvar "node", .fvar "leaf"]]

def unbundledCall : Pattern :=
  .apply "Fold" [.fvar "A", .fvar "B", .fvar "leaf", .fvar "node", .fvar "children"]

def verdicts : List (String × Bool) :=
  [("authored nested fold compiles and checks", checkProposal AgentSearch.module),
   ("nested source methods preserve exact constructor order", sourceMethods.length == 2),
   ("missing source clause refuses", !(changedProposal (·.take 1))),
   ("extra source clause refuses", !(changedProposal (fun rows => rows ++ rows.take 1))),
   ("reordered source clauses refuse", !(changedProposal List.reverse)),
   ("wrong nested recursive input refuses", !(changedProducer (replaceBranch wrongRecursiveInput))),
   ("unbundled recursive call refuses", !(changedProducer (replaceBranch unbundledCall))),
   ("ordinary producer can emit children-as-results", changedProducer (replaceBranch sourceChildrenAsResults)),
   ("independent typing refuses children-as-results", !(changedProposal (replaceBranch sourceChildrenAsResults))),
   ("unbound source name refuses", !(changedProposal (replaceBranch (.fvar "unknown")))),
   ("unresolved imports refuse", !(checkProposal
     { AgentSearch.module with imports := [⟨"Other.module", "other"⟩] }))]

theorem all_verdicts : verdicts.all (·.2) = true := by
  decide +kernel


/-! ## The authored name denotes its checked transparent body -/

namespace Definitions

open Declaration

abbrev body : Tower.Tm 0 :=
  emitFold (solvedMethod (.var 1)) (.lam (.lam (.app (.var 2) (.var 0))))

def signature : Signature Tower.Head :=
  Signature.ofList [(selfName, ⟨foldType, some body⟩)]

abbrev rules := extendRules inventoryRules signature

theorem fresh : inventoryRules.constantType selfName = none := by decide +kernel

theorem typeFormation : endpointAccepted .nil foldType (sortTm (.succ level)) = true := by
  decide +kernel

theorem typeLookup (name : DeclName) : signature.typeOf? name =
    if name = selfName then some foldType else none := by
  by_cases same : name = selfName <;>
    simp [signature, Signature.ofList, Signature.typeOf?, Signature.insert, Signature.empty, same]

theorem valueLookup (name : DeclName) : signature.valueOf? name =
    if name = selfName then some body else none := by
  by_cases same : name = selfName <;>
    simp [signature, Signature.ofList, Signature.valueOf?, Signature.insert, Signature.empty, same]

theorem bodyTyped : FormationSensitive.Judgment rules .nil body foldType :=
  authored_fold_typed.includeSignature signature

/-- Freshness, declaration-type formation and the actual compiled body are
checked before the authored name receives transparent unfolding. -/
theorem formed : signature.Formed inventoryRules where
  fresh := by
    intro name entry known
    by_cases same : name = selfName
    · simpa only [same] using fresh
    · simp [signature, Signature.ofList, Signature.insert, Signature.empty, same] at known
  types := by
    intro name type known
    rw [typeLookup] at known
    split at known
    · cases Option.some.inj known
      exact ⟨.sort (.succ level), .sort _,
        ((endpointAccepted_sound typeFormation).includeSignature signature).toRaw⟩
    · cases known
  values := by
    intro name type value known valueKnown
    rw [typeLookup] at known
    rw [valueLookup] at valueKnown
    split at known
    · rename_i same
      simp only [same, ↓reduceIte] at valueKnown
      cases Option.some.inj known
      cases Option.some.inj valueKnown
      exact bodyTyped.toRaw
    · cases known
  noSelfDelta := by
    intro name value known
    rw [valueLookup] at known
    split at known
    · cases Option.some.inj known
      intro impossible
      cases impossible
    · cases known


theorem valueSelf : signature.valueOf? selfName = some body := by
  simp [valueLookup]

theorem constantSelf : rules.constantType selfName = some foldType := by
  apply combinedType_of_signature inventoryRules signature fresh
  simp [typeLookup]

/-- Unfolding retains the displayed type, including the original
conversion and cumulativity tail; global subject reduction is not assumed. -/
theorem typedUnfolding {n : Nat} {context : Tower.Ctx n} {displayed : Tower.Tm n}
    (typed : FormationSensitive.Judgment rules context (.const selfName) displayed) :
    StepCore rules.computation rules.headEq (.const selfName : Tower.Tm n) (liftClosed body) ∧
      FormationSensitive.Judgment rules context (liftClosed body) displayed :=
  typed.delta valueSelf constantSelf bodyTyped.typing

theorem constant_typed : FormationSensitive.Judgment rules .nil
    (.const selfName) (liftClosed foldType) :=
  ⟨.nil, .const constantSelf
    ((endpointAccepted_sound typeFormation).typing.includeSignature signature) (.sort _)⟩

theorem unfolding_witness :
    StepCore rules.computation rules.headEq (.const selfName : Tower.Tm 0) (liftClosed body) ∧
      FormationSensitive.Judgment rules .nil (liftClosed body) (liftClosed foldType) :=
  typedUnfolding constant_typed

private theorem listRoot {n : Nat} {left right : Tower.Tm n}
    (step : (NativeIndexedFamilies.IntrinsicMaps.listRulesAt level).computation.step left right) :
    rules.computation.step left right := by
  apply RootStep.inherited
  apply RootStep.inherited
  cases step with
  | inherited impossible => exact impossible.elim
  | @delta name value lookup =>
      change (NativeIndexedFamilies.IntrinsicMaps.listSignatureAt level).valueOf? name = some value at lookup
      simp [NativeIndexedFamilies.IntrinsicMaps.listSignatureAt,
        LevelInstance.signature, NativeIndexedFamilies.Intrinsic.rawSignature_valueOf_none] at lookup
  | declared retained =>
      obtain ⟨evidence⟩ := retained
      exact RootStep.declared ⟨.list evidence⟩

theorem liftListPath {n : Nat} {left right : Tower.Tm n}
    (path : Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeElaboration.Reduces left right) :
    TypedEquality.Reduces rules left right := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec
    (IntrinsicNativeListMapComputation.reduction level n)
    (fun left right _ => TypedEquality.Reduces rules left right)
    (fun _ => .refl) ?_ left right path
  intro left middle right edge rest ih
  apply Relation.ReflTransGen.head _ ih
  have mapped := edge.mapHead
    (targetEq := rules.headEq) (targetRoot := rules.computation) (fun head => head)
    (fun impossible => impossible.elim)
    (by intro k a b step; simpa only [Tm.mapHead_id] using listRoot step)
  rw [Tm.mapHead_id left, Tm.mapHead_id middle] at mapped
  exact mapped

theorem namedApplication {n : Nat} (answer result leaf node input : Tower.Tm n) :
    TypedEquality.Reduces rules (sourceCall answer result leaf node input)
      (Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeElaboration.fold answer result leaf node input) := by
  have delta : TypedEquality.Reduces rules (.const selfName : Tower.Tm n) (liftClosed body) :=
    .single (.root (.delta valueSelf))
  exact (TypedEquality.Normalization.Reduces.appSpine_left delta
    [answer, result, leaf, node, input]).trans
    (liftListPath (source_application body function_emitted answer result leaf node input))


private theorem encodePointwise {n : Nat} (element : Tower.Tm n)
    (first second : Tower.Tm n → Tower.Tm n) (values : List (Tower.Tm n))
    (pointwise : ∀ value ∈ values, TypedEquality.Reduces rules (first value) (second value)) :
    TypedEquality.Reduces rules
      (IntrinsicNativeListMapComputation.encode element (values.map first))
      (IntrinsicNativeListMapComputation.encode element (values.map second)) := by
  induction values with
  | nil => exact .refl
  | cons head tail ih =>
      have headPath := TypedEquality.Normalization.Reduces.congr
        (f := fun term => NativeIndexedFamilies.Intrinsic.consApp element term
          (IntrinsicNativeListMapComputation.encode element (tail.map first)))
        (fun step => .congAppFun (.congAppArg step)) (pointwise head List.mem_cons_self)
      have tailPath := TypedEquality.Normalization.Reduces.congr
        (f := NativeIndexedFamilies.Intrinsic.consApp element (second head))
        (fun step => .congAppArg step)
        (ih (fun value member => pointwise value (List.mem_cons_of_mem _ member)))
      exact headPath.trans tailPath

theorem namedMap {n : Nat} (answer result leaf node : Tower.Tm n)
    (children : List (Tower.Tm n)) :
    TypedEquality.Reduces rules
      (sourceMap answer result leaf node (IntrinsicNativeListMapComputation.encode (treeApp answer) children))
      (IntrinsicNativeListMapComputation.encode result
        (children.map (Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeElaboration.fold answer result leaf node))) := by
  refine (liftListPath (IntrinsicNativeListMapComputation.mapped_encode level _ _ _ children)).trans ?_
  apply encodePointwise
  intro child _
  have opening : TypedEquality.Reduces rules
      (.app (.lam (sourceCall (rename wk answer) (rename wk result)
        (rename wk leaf) (rename wk node) (.var 0))) child)
      (sourceCall answer result leaf node child) := by
    simpa only [sourceCall, Declaration.IndexedFamily.applyArgs, inst0, subst,
      subst_rename, subst0_succ, subst0_zero, wk,
      show (fun index : Fin n => Tm.var index) = (ids : Sub Tower.Head n n) from rfl,
      subst_ids] using (Relation.ReflTransGen.single (StepCore.betaPi
        (root := rules.computation) (headEq := rules.headEq)
        (sourceCall (rename wk answer) (rename wk result)
          (rename wk leaf) (rename wk node) (.var 0)) child))
  exact opening.trans (namedApplication answer result leaf node child)

/-- The source helper uses the actual published name. Both result views
reach the same ordered object-level calls after its delta/beta expansion. -/
theorem namedBundleCommonOutput {n : Nat} (answer result leaf node : Tower.Tm n)
    (children : List (Tower.Tm n)) :
    let output := IntrinsicNativeListMapComputation.encode result
      (children.map (Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeElaboration.fold answer result leaf node))
    TypedEquality.Reduces rules
      (bundleResults (treeApp answer) result
        (liftChildren answer (constantMotive result) (solvedMethod leaf)
          (branchMethod (treeApp answer) result node)
          (IntrinsicNativeListMapComputation.encode (treeApp answer) children))) output ∧
    TypedEquality.Reduces rules
      (sourceMap answer result leaf node
        (IntrinsicNativeListMapComputation.encode (treeApp answer) children)) output := by
  exact ⟨liftListPath (bundleResults_common_output answer result (solvedMethod leaf)
    (branchMethod (treeApp answer) result node) children).1,
    namedMap answer result leaf node children⟩

theorem body_no_recursive_name :
    selfName ∉ ConstantExpansion.constantNames body := by decide +kernel

def shadowSignature : Signature Tower.Head :=
  Signature.ofList [(treeName, ⟨foldType, some body⟩)]

theorem shadow_refused : ¬ shadowSignature.Formed inventoryRules := by
  intro admitted
  have selected : shadowSignature.entries treeName = some ⟨foldType, some body⟩ := by
    simp [shadowSignature, Signature.ofList, Signature.insert]
  have absent := admitted.fresh selected
  have present : inventoryRules.constantType treeName = some familyType := by decide +kernel
  rw [present] at absent
  cases absent

def selfSignature : Signature Tower.Head :=
  Signature.ofList [(selfName, ⟨foldType, some (.const selfName)⟩)]

theorem self_refused : ¬ selfSignature.Formed inventoryRules := by
  intro admitted
  have selected : selfSignature.valueOf? selfName = some (.const selfName) := by
    simp [selfSignature, Signature.ofList, Signature.valueOf?, Signature.insert]
  exact admitted.noSelfDelta selected rfl

def verdicts : List (String × Bool) :=
  [("authored fold name is fresh", (inventoryRules.constantType selfName).isNone),
   ("published fold type is exact", signature.typeOf? selfName == some foldType),
   ("published fold body is exact", signature.valueOf? selfName == some body),
   ("published body retains no recursive source constant",
      !(ConstantExpansion.constantNames body).contains selfName),
   ("unrelated definition name is absent", (signature.valueOf? treeName).isNone),
   ("existing family name cannot be reused", (inventoryRules.constantType treeName).isSome),
   ("wrong definition body fails independent replay",
      !(endpointAccepted .nil (.lam (.var 0)) foldType))]

theorem all_verdicts : verdicts.all (·.2) = true := by decide +kernel

#print axioms shadow_refused
#print axioms self_refused

#print axioms namedMap
#print axioms namedBundleCommonOutput

#print axioms formed
#print axioms typedUnfolding
#print axioms namedApplication

end Definitions


/-! ## The authored fold instantiates an explicit typed branch receipt -/

namespace Branch

def contextAB : Tower.Ctx 2 := .snoc contextA (sortTm level)
def contextABF : Tower.Ctx 3 := .snoc contextAB (arrow (.var 1) (.var 0))
def contextABFN : Tower.Ctx 4 := .snoc contextABF
  (arrow (Intrinsic.listApp (.var 1)) (.var 1))
def context : Tower.Ctx 5 := .snoc contextABFN (Intrinsic.listApp (treeApp (.var 3)))

def assignment : Sub Tower.Head 5 5 :=
  consSub (.var 0)
    (consSub (branchMethod (treeApp (.var 4)) (.var 3) (.var 1))
      (consSub (solvedMethod (.var 2))
        (consSub (constantMotive (.var 3)) (consSub (.var 4) Fin.elim0))))

def slotChecked (index : Fin 5) : Bool :=
  endpointAccepted context (assignment index)
    (subst assignment (Ctx.lookup branchContext index))

theorem slots : ∀ index, slotChecked index = true := by
  intro index
  fin_cases index <;> decide +kernel

theorem contextMorphism : FormationSensitive.CtxMor inventoryRules branchContext context assignment := by
  intro index
  exact (endpointAccepted_sound (slots index)).typing

theorem formed_endpoints :
    FormationSensitive.Judgment inventoryRules context
      (subst assignment branchLeft) (subst assignment branchIotaType) ∧
    FormationSensitive.Judgment inventoryRules context
      (subst assignment branchRight) (subst assignment branchIotaType) := by
  have targetFormation := (endpointAccepted_sound (slots 0)).context
  exact ⟨(branch_rows_formed.1).substitute targetFormation contextMorphism,
    (branch_rows_formed.2).substitute targetFormation contextMorphism⟩


theorem guestMorphism : Presentation.CtxMor
    Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeGuest.rules branchContext context assignment := by
  intro index
  exact (liftJudgment (endpointAccepted_sound (slots index))).toRaw

noncomputable def transportedReceipt := branchReceipt_substitute assignment guestMorphism

theorem result_formed : endpointAccepted context (.var 3) (sortTm level) = true := by decide +kernel

theorem result_conversion : Conv inventoryRules.headEq
    (subst assignment branchIotaType) (.var 3) inventoryRules.computation := by
  change Conv inventoryRules.headEq
    (.app (.lam (.var 4)) (branchApp (.var 4) (.var 0))) (.var 3) inventoryRules.computation
  exact Relation.EqvGen.rel _ _ (.betaPi _ _)

theorem result_endpoints :
    FormationSensitive.Judgment inventoryRules context (subst assignment branchLeft) (.var 3) ∧
    FormationSensitive.Judgment inventoryRules context (subst assignment branchRight) (.var 3) := by
  have formedResult := endpointAccepted_sound result_formed
  exact ⟨⟨formed_endpoints.1.context, .conv formed_endpoints.1.typing
      formedResult.typing (.sort _) result_conversion⟩,
    ⟨formed_endpoints.2.context, .conv formed_endpoints.2.typing
      formedResult.typing (.sort _) result_conversion⟩⟩

noncomputable def receipt : Declaration.ComputationAuthority.ProofRelevantStepReceipt
    baseRules Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeGuest.signature
    iotaComputation context (subst assignment branchLeft) (subst assignment branchRight) (.var 3) where
  sourceTyping := (liftJudgment result_endpoints.1).toRaw
  targetTyping := (liftJudgment result_endpoints.2).toRaw
  evidence := transportedReceipt.evidence

theorem left_is_fold : subst assignment branchLeft =
    Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeElaboration.fold
      (.var 4) (.var 3) (.var 2) (.var 1) (branchApp (.var 4) (.var 0)) := rfl

def badMethod : Tower.Tm 5 := .lam (.lam (.app (.var 3) (.var 1)))

theorem children_as_results_refused : endpointAccepted context badMethod
    (subst assignment (Ctx.lookup branchContext 1)) = false := by decide +kernel


def verdicts : List (String × Bool) :=
  [("fold branch child List checks", slotChecked 0),
   ("fold branch method checks", slotChecked 1),
   ("fold solved method checks", slotChecked 2),
   ("fold constant motive checks", slotChecked 3),
   ("fold payload type checks", slotChecked 4),
   ("fold branch refuses source children as results",
      !(endpointAccepted context badMethod (subst assignment (Ctx.lookup branchContext 1))))]

theorem all_verdicts : verdicts.all (·.2) = true := by
  simp [verdicts, slots, children_as_results_refused]

#print axioms contextMorphism
#print axioms result_endpoints
#print axioms receipt
#print axioms all_verdicts

end Branch

#print axioms fold_typed
#print axioms foldTerm_beta
#print axioms bundleResults_common_output
#print axioms source_typed
#print axioms source_application
#print axioms source_methods_reconstruct
#print axioms checkProposal_sound
#print axioms all_verdicts

end Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeElaboration
