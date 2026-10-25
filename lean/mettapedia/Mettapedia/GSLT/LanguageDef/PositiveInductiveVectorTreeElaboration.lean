import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuestControls
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeResultFoldEvidence
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestPlans
import Mettapedia.GSLT.LanguageDef.IndexedInductiveOperationSource
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

/-!
# Authored VectorTree clauses at their complete dependent method interface

The source reader retains the earlier length and all constructor fields. Its
nested operation expands to the admitted VectorTree eliminator's complete
Vector-position induction bundle. The compiled methods and their generated
dependent types meet at independent formation-sensitive replay.

This is a consumer of the existing eliminator. It introduces no datatype,
new eliminator, unlicensed raw Tree iota equation or accepted native kernel.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeElaboration

open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedPositiveContainerGuestTypes
open IndexedPositiveContainerGuestPlans
open IndexedInductive.CaseElaboration
open IndexedInductive.OperationSource

abbrev I := VectorControl.interface
abbrev registry := VectorControl.registry

def operations : CallSyntax I registry Tower.Head 3 where
  direct outer _ _ child :=
    PositiveInductiveVectorTreeGuest.eliminateApp (outer 2) (outer 1) (outer 0) child
  nested := by
    intro context n name entry registered outer output index environment children
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    exact PositiveInductiveVectorTreeGuest.liftChildren (outer 2) (outer 1) (outer 0)
      (IndexedPositiveContainerGuestControls.Vectors.lengthTerm output environment) children
  direct_substitute := by
    intros
    simp [PositiveInductiveVectorTreeGuest.eliminateApp, subst]
  nested_substitute := by
    intro context n m name entry registered outer output index environment children substitution
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    change VectorControl.LengthExpr context at output
    change subst substitution
        (PositiveInductiveVectorTreeGuest.liftChildren (outer 2) (outer 1) (outer 0)
          (IndexedPositiveContainerGuestControls.Vectors.lengthTerm output environment) children) =
      PositiveInductiveVectorTreeGuest.liftChildren (subst substitution (outer 2))
        (subst substitution (outer 1)) (subst substitution (outer 0))
        (IndexedPositiveContainerGuestControls.Vectors.lengthTerm output
          (IndexedInductive.Guest.mapEnv (subst substitution) environment))
        (subst substitution children)
    rw [PositiveInductiveVectorTreeGuest.subst_liftChildren]
    congr 1
    exact IndexedPositiveContainerGuestControls.Vectors.lengthTerm_substitute output environment substitution


section SourceReader
open ModuleSource.Commands
#module_file "../../../../../metta/gslt/module/IndexedVectorTreeFold.module"
#module_roundtrip AgentVectorSearch
end SourceReader

def sourceSymbols : List (Symbol Tower.Head) :=
  [⟨"Apply", 2, .app (.var 1) (.var 0)⟩,
   ⟨"Apply3", 4, .app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)⟩,
   ⟨"Fold", 4, PositiveInductiveVectorTreeGuest.eliminateApp (.var 3) (.var 2) (.var 1) (.var 0)⟩,
   ⟨"AllFold", 5, PositiveInductiveVectorTreeGuest.liftChildren (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)⟩]

def sourcePlan (constructor : ModuleSource.IndexedPositiveVectorLowering.ResolvedConstructor) : BranchPlan Tower.Head 3 :=
  plan operations constructor.name constructor.body.erase

def sourceHeader (generated : BranchPlan Tower.Head 3) : Header 3 :=
  Header.fromPlan generated "Fold" []

def selectedInventory : Option ModuleSource.IndexedPositiveVectorLowering.ResolvedModule := do
  let selected ← selectModule AgentVectorSearch.module
  ModuleSource.IndexedPositiveVectorLowering.lowerModule selected.declarations

def selectedPlans : List (BranchPlan Tower.Head 3) :=
  ((selectedInventory.map (fun resolved => resolved.family.constructors.map sourcePlan))).getD []

def selectedRules : List Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule :=
  ((selectModule AgentVectorSearch.module).map (·.rules)).getD []

theorem source_declarations_exact :
    (selectModule AgentVectorSearch.module).map (·.declarations) =
      some ModuleSource.IndexedPositiveVectorLowering.Controls.textualModule := by
  rfl

theorem source_inventory_exact : selectedInventory =
    some ModuleSource.IndexedPositiveVectorLowering.Controls.resolvedModule :=
  ModuleSource.IndexedPositiveVectorLowering.Controls.module_roundtrip

local instance : DecidableRel PositiveInductiveVectorTreeGuest.inventoryRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred PositiveInductiveVectorTreeGuest.inventoryRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (PositiveInductiveVectorTreeGuest.inventoryRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel PositiveInductiveVectorTreeGuest.inventoryRules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel PositiveInductiveVectorTreeGuest.inventoryRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def checked (constructor : ModuleSource.IndexedPositiveVectorLowering.ResolvedConstructor)
    (rule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule) :=
  elaborateClause PositiveInductiveVectorTreeGuest.inventoryRules PositiveInductiveVectorTreeGuest.inventoryDecoder operations IndexedPositiveContainerGuestControls.Vectors.indexing IndexedPositiveContainerGuestControls.Vectors.containers
    constructor.body.erase IndexedPositiveContainerGuestControls.Vectors.types (.var 2) constructor.name "Fold" [] sourceSymbols
    64 PositiveInductiveVectorTreeGuest.eliminateName rule PositiveInductiveVectorTreeGuest.inventoryChoices 256 PositiveInductiveVectorTreeGuest.contextPZB

def solvedRule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule :=
  selectedRules.get ⟨0, by decide +kernel⟩
def branchRule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule :=
  selectedRules.get ⟨1, by decide +kernel⟩

def solvedMethod : Tower.Tm 3 := .lam (.app (.var 2) (.var 0))
def branchMethod : Tower.Tm 3 :=
  .lam (.lam (.lam (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0))))

def compiled : Option (List (Tower.Tm 3)) := do
  if selectedPlans.length ≠ selectedRules.length then none else do
    let clauses ← (selectedPlans.zip selectedRules).mapM fun (generated, rule) =>
      (readRule sourceSymbols 64 (sourceHeader generated) rule).map (·.toClause)
    compilePlans selectedPlans PositiveInductiveVectorTreeGuest.eliminateName clauses

theorem methods_emitted : compiled = some [solvedMethod, branchMethod] := by
  decide +kernel

theorem solved_checked : (checked ModuleSource.IndexedPositiveVectorLowering.Controls.solved solvedRule).isSome = true := by
  decide +kernel

theorem branch_checked : (checked ModuleSource.IndexedPositiveVectorLowering.Controls.branch branchRule).isSome = true := by
  decide +kernel

/-- The exact generated dependent interfaces are compared with the separately
qualified declaration library, including every original field and bundle. -/
theorem generated_solved_type :
    methodType IndexedPositiveContainerGuestControls.Vectors.indexing IndexedPositiveContainerGuestControls.Vectors.containers ModuleSource.IndexedPositiveVectorLowering.Controls.solved.body.erase IndexedPositiveContainerGuestControls.Vectors.types
      (.var 2 : Tower.Tm 3) "solved" =
      rename (fun i : Fin 1 => (i.succ.succ : Fin 3)) PositiveInductiveVectorTreeGuest.solvedCaseType := by
  decide +kernel

theorem generated_branch_type :
    methodType IndexedPositiveContainerGuestControls.Vectors.indexing IndexedPositiveContainerGuestControls.Vectors.containers ModuleSource.IndexedPositiveVectorLowering.Controls.branch.body.erase IndexedPositiveContainerGuestControls.Vectors.types
      (.var 2 : Tower.Tm 3) "branch" = rename wk PositiveInductiveVectorTreeGuest.branchCaseType := by
  decide +kernel


open PositiveInductiveVectorTreeGuest (inventoryRules inventoryDecoder inventoryChoices
  contextPZB branchContext branchLeft branchRight branchIotaType endpointAccepted endpointAccepted_sound)

def generatedType (constructor : ModuleSource.IndexedPositiveVectorLowering.ResolvedConstructor) : Tower.Tm 3 :=
  methodType IndexedPositiveContainerGuestControls.Vectors.indexing
    IndexedPositiveContainerGuestControls.Vectors.containers constructor.body.erase
    IndexedPositiveContainerGuestControls.Vectors.types (.var 2) constructor.name

theorem checked_sound (constructor : ModuleSource.IndexedPositiveVectorLowering.ResolvedConstructor)
    (rule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule)
    (result : Tower.Tm 3 × FormationSensitiveElaboration.Submission Tower.Head inventoryDecoder.Code 3)
    (accepted : checked constructor rule = some result) :
    FormationSensitive.Judgment inventoryRules contextPZB result.1 (generatedType constructor) ∧
      compileRule sourceSymbols 64 PositiveInductiveVectorTreeGuest.eliminateName
        (sourceHeader (sourcePlan constructor)) (sourcePlan constructor).recursiveCalls rule = some result.1 :=
  elaborateClause_sound inventoryRules inventoryDecoder operations
    IndexedPositiveContainerGuestControls.Vectors.indexing
    IndexedPositiveContainerGuestControls.Vectors.containers constructor.body.erase
    IndexedPositiveContainerGuestControls.Vectors.types (.var 2) constructor.name "Fold" []
    sourceSymbols 64 PositiveInductiveVectorTreeGuest.eliminateName rule inventoryChoices 256 contextPZB result accepted

/-- A closed witness of the computed successful source request. The service
itself is `checked`; this chosen result is used only as a logical witness. -/
noncomputable def branchResult :
    Tower.Tm 3 × FormationSensitiveElaboration.Submission Tower.Head inventoryDecoder.Code 3 :=
  Classical.choose (Option.isSome_iff_exists.mp branch_checked)

theorem branchResult_produced :
    checked ModuleSource.IndexedPositiveVectorLowering.Controls.branch branchRule = some branchResult :=
  Classical.choose_spec (Option.isSome_iff_exists.mp branch_checked)

theorem branch_sound_witness :
    FormationSensitive.Judgment inventoryRules contextPZB branchResult.1
        (generatedType ModuleSource.IndexedPositiveVectorLowering.Controls.branch) ∧
      compileRule sourceSymbols 64 PositiveInductiveVectorTreeGuest.eliminateName
        (sourceHeader (sourcePlan ModuleSource.IndexedPositiveVectorLowering.Controls.branch))
        (sourcePlan ModuleSource.IndexedPositiveVectorLowering.Controls.branch).recursiveCalls
        branchRule = some branchResult.1 :=
  checked_sound _ _ branchResult branchResult_produced

theorem solved_compiled :
    compileRule sourceSymbols 64 PositiveInductiveVectorTreeGuest.eliminateName
      (sourceHeader (sourcePlan ModuleSource.IndexedPositiveVectorLowering.Controls.solved))
      (sourcePlan ModuleSource.IndexedPositiveVectorLowering.Controls.solved).recursiveCalls solvedRule =
        some solvedMethod := by
  decide +kernel

theorem branch_compiled :
    compileRule sourceSymbols 64 PositiveInductiveVectorTreeGuest.eliminateName
      (sourceHeader (sourcePlan ModuleSource.IndexedPositiveVectorLowering.Controls.branch))
      (sourcePlan ModuleSource.IndexedPositiveVectorLowering.Controls.branch).recursiveCalls branchRule =
        some branchMethod := by
  decide +kernel

theorem solved_typed :
    FormationSensitive.Judgment inventoryRules contextPZB solvedMethod
      (generatedType ModuleSource.IndexedPositiveVectorLowering.Controls.solved) := by
  obtain ⟨result, accepted⟩ := Option.isSome_iff_exists.mp solved_checked
  have qualified := checked_sound _ _ result accepted
  have same : result.1 = solvedMethod := Option.some.inj (qualified.2.symm.trans solved_compiled)
  simpa only [same] using qualified.1

theorem branch_typed :
    FormationSensitive.Judgment inventoryRules contextPZB branchMethod
      (generatedType ModuleSource.IndexedPositiveVectorLowering.Controls.branch) := by
  obtain ⟨result, accepted⟩ := Option.isSome_iff_exists.mp branch_checked
  have qualified := checked_sound _ _ result accepted
  have same : result.1 = branchMethod := Option.some.inj (qualified.2.symm.trans branch_compiled)
  simpa only [same] using qualified.1

def readBranch := readRule sourceSymbols 64
  (sourceHeader (sourcePlan ModuleSource.IndexedPositiveVectorLowering.Controls.branch)) branchRule

/-- This term is obtained from the actual authored right-hand side. The
checked comparison below ensures the default is never used. -/
def sourceBranchRight : Tower.Tm 5 :=
  (readBranch.map (·.body)).getD TypedEquality.Normalization.defaultTm

theorem branch_read_exact : sourceBranchRight = branchRight := by
  decide +kernel

def branchApplication : Tower.Tm 5 :=
  TypedEquality.Normalization.appSpine
    (rename (TypedEquality.Normalization.wkN 2) branchMethod)
    [(.var 1), (.var 0), PositiveInductiveVectorTreeGuest.branchBundle]

theorem branch_beta : TypedEquality.Reduces inventoryRules branchApplication sourceBranchRight := by
  obtain ⟨read, produced, _left, _body, reduction⟩ :=
    compileRule_reconstructs (R := inventoryRules) sourceSymbols 64
      PositiveInductiveVectorTreeGuest.eliminateName
      (sourceHeader (sourcePlan ModuleSource.IndexedPositiveVectorLowering.Controls.branch))
      (sourcePlan ModuleSource.IndexedPositiveVectorLowering.Controls.branch).recursiveCalls branchRule
      branchMethod branch_compiled
  have same : read.body = sourceBranchRight := by
    rw [sourceBranchRight, readBranch, produced]
    rfl
  exact same ▸ reduction

/-- Applications of an unannotated method use its reconstructed typing,
rather than requiring the bidirectional producer to infer that lambda. -/
theorem branch_application_typed :
    FormationSensitive.Judgment inventoryRules branchContext branchApplication branchIotaType := by
  have first := branch_typed.typing.weaken (extension := NativeNaturalVectorFamilies.natTm)
  have second := first.weaken
    (extension := NativeNaturalVectorFamilies.vecApp PositiveInductiveVectorTreeGuest.treeTm (.var 0))
  have lifted : FormationSensitive.Typing inventoryRules branchContext
      (rename (TypedEquality.Normalization.wkN 2) branchMethod)
      (rename (TypedEquality.Normalization.wkN 2)
        (generatedType ModuleSource.IndexedPositiveVectorLowering.Controls.branch)) := by
    have shift : (fun i : Fin 3 => (wk (wk i) : Fin 5)) =
        TypedEquality.Normalization.wkN 2 := by
      funext i
      apply Fin.ext
      rfl
    simpa only [PositiveInductiveVectorTreeGuest.branchContext,
      PositiveInductiveVectorTreeGuest.branchContextN, rename_comp, shift] using second
  have typeExact : generatedType ModuleSource.IndexedPositiveVectorLowering.Controls.branch =
      rename wk PositiveInductiveVectorTreeGuest.branchCaseType := generated_branch_type
  rw [typeExact] at lifted
  have arity : FormationSensitive.Typing inventoryRules branchContext (.var 1)
      NativeNaturalVectorFamilies.natTm := by
    exact .var 1
  have children : FormationSensitive.Typing inventoryRules branchContext (.var 0)
      (NativeNaturalVectorFamilies.vecApp PositiveInductiveVectorTreeGuest.treeTm (.var 1)) := by
    exact .var 0
  have firstApplied := FormationSensitive.Typing.appElim lifted arity
  have secondApplied := FormationSensitive.Typing.appElim firstApplied children
  have applied := FormationSensitive.Typing.appElim secondApplied
    PositiveInductiveVectorTreeGuest.branch_bundle_formed.typing
  exact ⟨PositiveInductiveVectorTreeGuest.branch_rows_formed.1.context, applied⟩

theorem branch_endpoints_typed :
    FormationSensitive.Judgment inventoryRules branchContext branchApplication branchIotaType ∧
      FormationSensitive.Judgment inventoryRules branchContext sourceBranchRight branchIotaType := by
  refine ⟨branch_application_typed, ?_⟩
  rw [branch_read_exact]
  exact PositiveInductiveVectorTreeGuest.branch_rows_formed.2

/-- The actual parsed branch target receives the existing VectorTree
proof-relevant receipt. This transport adds no raw-iota computation authority. -/
noncomputable def sourceBranchReceipt : Declaration.ComputationAuthority.ProofRelevantStepReceipt
    PositiveInductiveVectorTreeGuest.baseRules PositiveInductiveVectorTreeGuest.signature
    PositiveInductiveVectorTreeGuest.iotaComputation branchContext branchLeft sourceBranchRight branchIotaType := by
  rw [branch_read_exact]
  exact PositiveInductiveVectorTreeGuest.branchReceipt

def unbundledRule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule :=
  { branchRule with right := (.apply "Apply3"
      [.fvar "B", .fvar "arity", .fvar "children", .fvar "children"]) }

theorem unbundled_compiles :
    (compileRule sourceSymbols 64 PositiveInductiveVectorTreeGuest.eliminateName
      (sourceHeader (sourcePlan ModuleSource.IndexedPositiveVectorLowering.Controls.branch))
      (sourcePlan ModuleSource.IndexedPositiveVectorLowering.Controls.branch).recursiveCalls unbundledRule).isSome = true := by
  decide +kernel

theorem unbundled_refused :
    (checked ModuleSource.IndexedPositiveVectorLowering.Controls.branch unbundledRule).isNone = true := by
  decide +kernel


def verdicts : List (String × Bool) :=
  [("authored Vector methods preserve source and IH order", compiled == some [solvedMethod, branchMethod]),
   ("authored Vector solved method checks", (checked ModuleSource.IndexedPositiveVectorLowering.Controls.solved solvedRule).isSome),
   ("authored Vector dependent branch method checks", (checked ModuleSource.IndexedPositiveVectorLowering.Controls.branch branchRule).isSome),
   ("generated solved interface matches the admitted declaration",
      generatedType ModuleSource.IndexedPositiveVectorLowering.Controls.solved ==
        rename (fun i : Fin 1 => (i.succ.succ : Fin 3)) PositiveInductiveVectorTreeGuest.solvedCaseType),
   ("generated dependent branch interface retains the complete bundle",
      generatedType ModuleSource.IndexedPositiveVectorLowering.Controls.branch ==
        rename wk PositiveInductiveVectorTreeGuest.branchCaseType),
   ("parsed Vector branch retains the licensed receipt target", sourceBranchRight == branchRight),
   ("unbundled source survives raw compilation",
      (compileRule sourceSymbols 64 PositiveInductiveVectorTreeGuest.eliminateName
        (sourceHeader (sourcePlan ModuleSource.IndexedPositiveVectorLowering.Controls.branch))
        (sourcePlan ModuleSource.IndexedPositiveVectorLowering.Controls.branch).recursiveCalls unbundledRule).isSome),
   ("unbundled source refuses dependent checking",
      (checked ModuleSource.IndexedPositiveVectorLowering.Controls.branch unbundledRule).isNone)]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  have solvedExact : generatedType ModuleSource.IndexedPositiveVectorLowering.Controls.solved =
      rename (fun i : Fin 1 => (i.succ.succ : Fin 3)) PositiveInductiveVectorTreeGuest.solvedCaseType :=
    generated_solved_type
  have branchExact : generatedType ModuleSource.IndexedPositiveVectorLowering.Controls.branch =
      rename wk PositiveInductiveVectorTreeGuest.branchCaseType := generated_branch_type
  simp [verdicts, methods_emitted, solved_checked, branch_checked, solvedExact, branchExact,
    branch_read_exact, unbundled_compiles, unbundled_refused]

end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeElaboration

/-!
## Constant-motive source folds with source-ordered Vector results

An ordinary checked projection definition turns the exact dependent bundle
into a Vector of recursive results. The actual parsed branch is specialized
through a checked context substitution, retaining arity, children and its
original proof-relevant iota witness. Canonical-spine computation and typed
endpoints are separate from arbitrary open-container interpretation and
universal raw-iota preservation.
-/
namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.ResultFold
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

local instance : DecidableRel checkingRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred checkingRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (checkingRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel checkingRules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel checkingRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def slotReplay (index : Fin 5) : Bool :=
  FormationSensitiveElaboration.replay checkingRules checkingDecoder context
    (assignment index) (subst assignment (Ctx.lookup branchContext index)) (slotSubmission index)

private theorem slot0_checked : slotReplay 0 = true := by decide +kernel

private theorem slot1_checked : slotReplay 1 = true := by decide +kernel

private theorem slot2_checked : slotReplay 2 = true := by decide +kernel

private theorem slot3_checked : slotReplay 3 = true := by decide +kernel

private theorem slot4_checked : slotReplay 4 = true := by decide +kernel

theorem slots_checked (index : Fin 5) : slotReplay index = true := by
  fin_cases index
  · exact slot0_checked
  · exact slot1_checked
  · exact slot2_checked
  · exact slot3_checked
  · exact slot4_checked

theorem fold_replayed : FormationSensitiveElaboration.replay checkingRules checkingDecoder
    .nil foldTerm foldType foldSubmission = true := by decide +kernel

def projectedTarget : Tower.Tm 5 :=
  .app (.app (.app (.var 2) (.var 1)) (.var 0))
    (childrenResults (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))

theorem target_replayed : FormationSensitiveElaboration.replay checkingRules checkingDecoder
    context projectedTarget (.var 4) targetSubmission = true := by decide +kernel

theorem slot_judgment (index : Fin 5) : FormationSensitive.Judgment checkingRules context
    (assignment index) (subst assignment (Ctx.lookup branchContext index)) :=
  FormationSensitiveElaboration.replay_sound checkingRules checkingDecoder (slots_checked index)

theorem fold_typed : FormationSensitive.Judgment checkingRules .nil foldTerm foldType :=
  FormationSensitiveElaboration.replay_sound checkingRules checkingDecoder fold_replayed

theorem target_typed : FormationSensitive.Judgment checkingRules context projectedTarget (.var 4) :=
  FormationSensitiveElaboration.replay_sound checkingRules checkingDecoder target_replayed

theorem contextMorphism : FormationSensitive.CtxMor checkingRules branchContext context assignment :=
  fun index => (slot_judgment index).typing

theorem formed_endpoints :
    FormationSensitive.Judgment checkingRules context (subst assignment branchLeft) (subst assignment branchIotaType) ∧
    FormationSensitive.Judgment checkingRules context (subst assignment branchRight) (subst assignment branchIotaType) := by
  have formed := (slot_judgment 0).context
  exact ⟨⟨formed, (branch_rows_formed.1.typing.monoSignature prior_extends).substitute contextMorphism⟩,
    ⟨formed, (branch_rows_formed.2.typing.monoSignature prior_extends).substitute contextMorphism⟩⟩

theorem result_conversion : Conv checkingRules.headEq (subst assignment branchIotaType)
    (.var 4) checkingRules.computation := by
  change Conv checkingRules.headEq
    (.app (.lam (.var 5)) (branchApp (.var 1) (.var 0))) (.var 4) checkingRules.computation
  exact Relation.EqvGen.rel _ _ (.betaPi _ _)

theorem result_endpoints :
    FormationSensitive.Judgment checkingRules context (subst assignment branchLeft) (.var 4) ∧
    FormationSensitive.Judgment checkingRules context (subst assignment branchRight) (.var 4) := by
  have resultFormed : FormationSensitive.Typing checkingRules context (.var 4) (sortTm level) := .var 4
  exact ⟨⟨formed_endpoints.1.context, .conv formed_endpoints.1.typing resultFormed (.sort _) result_conversion⟩,
    ⟨formed_endpoints.2.context, .conv formed_endpoints.2.typing resultFormed (.sort _) result_conversion⟩⟩

noncomputable def sourceReceipt : ComputationAuthority.ProofRelevantStepReceipt
    baseRules executionSignature iotaComputation context (subst assignment branchLeft)
    (subst assignment PositiveInductiveVectorTreeElaboration.sourceBranchRight) (.var 4) := by
  rw [PositiveInductiveVectorTreeElaboration.branch_read_exact]
  exact {
    sourceTyping := (result_endpoints.1.typing.monoSignature checking_extends_execution).toRaw
    targetTyping := (result_endpoints.2.typing.monoSignature checking_extends_execution).toRaw
    evidence := IotaEvidence.substitute branchReceipt.evidence assignment }

open NativeNaturalVectorFamilies

theorem subst_projection {n m : Nat} (sigma : Sub Tower.Head n m)
    (result arity children bundle : Tower.Tm n) :
    subst sigma (projection result arity children bundle) =
      projection (subst sigma result) (subst sigma arity) (subst sigma children) (subst sigma bundle) := by
  simp [projection, subst]

theorem subst_solvedMethod {n m : Nat} (sigma : Sub Tower.Head n m) (leaf : Tower.Tm n) :
    subst sigma (solvedMethod leaf) = solvedMethod (subst sigma leaf) := by
  simp [solvedMethod, subst]

theorem subst_branchMethod {n m : Nat} (sigma : Sub Tower.Head n m) (result node : Tower.Tm n) :
    subst sigma (branchMethod result node) = branchMethod (subst sigma result) (subst sigma node) := by
  change subst sigma (.lam (.lam (.lam (.app (.app (.app (weaken3 node) (.var 2)) (.var 1))
    (projection (weaken3 result) (.var 2) (.var 1) (.var 0)))))) = _
  simp [subst, weaken3, subst_projection]
  rfl

theorem subst_fold {n m : Nat} (sigma : Sub Tower.Head n m)
    (result leaf node input : Tower.Tm n) :
    subst sigma (fold result leaf node input) =
      fold (subst sigma result) (subst sigma leaf) (subst sigma node) (subst sigma input) := by
  simp [fold, eliminateApp, subst, NativeVectorAll.ResultView.subst_predicate,
    subst_solvedMethod, subst_branchMethod]

theorem left_is_fold : subst assignment branchLeft =
    fold (.var 4) (.var 3) (.var 2) (branchApp (.var 1) (.var 0)) := rfl

theorem parsed_right_is_application :
    subst assignment PositiveInductiveVectorTreeElaboration.sourceBranchRight =
      .app (.app (.app (branchMethod (.var 4) (.var 2)) (.var 1)) (.var 0))
        (childrenBundle (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)) := by
  rw [PositiveInductiveVectorTreeElaboration.branch_read_exact]
  simp only [branchRight, subst]
  rfl

open TypedEquality.Normalization

theorem branchMethod_beta (R : Rules Tower.Head) {n : Nat} (result node arity children bundle : Tower.Tm n) :
    TypedEquality.Reduces R
      (.app (.app (.app (branchMethod result node) arity) children) bundle)
      (.app (.app (.app node arity) children)
        (projection result arity children bundle)) := by
  let body : Tower.Tm (n + 3) :=
    .app (.app (.app (weaken3 node) (.var 2)) (.var 1))
      (projection (weaken3 result) (.var 2) (.var 1) (.var 0))
  let sigma : Sub Tower.Head (n + 3) n := consSub bundle (consSub children (consSub arity ids))
  have beta := lams_beta (R := R) 3 body [arity, children, bundle] rfl
  have assigned : extendSub ids (fun j => [arity, children, bundle].getD j defaultTm) 3 = sigma := rfl
  rw [assigned] at beta
  have outer (term : Tower.Tm n) : subst sigma (weaken3 term) = term := by
    unfold weaken3 NativeVectorAll.weaken2
    rw [subst_rename, subst_rename]
    change subst ids term = term
    exact subst_ids term
  have target : subst sigma body =
      .app (.app (.app node arity) children)
        (projection result arity children bundle) := by
    change Tm.app (.app (.app (subst sigma (weaken3 node)) arity) children)
      (subst sigma (projection (weaken3 result) (.var 2) (.var 1) (.var 0))) = _
    rw [subst_projection, outer, outer]
    rfl
  rw [target] at beta
  exact beta

theorem parsed_branch_beta (R : Rules Tower.Head) : TypedEquality.Reduces R
    (subst assignment PositiveInductiveVectorTreeElaboration.sourceBranchRight)
    (.app (.app (.app (.var 2) (.var 1)) (.var 0))
      (childrenResults (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))) := by
  rw [parsed_right_is_application]
  exact branchMethod_beta R _ _ _ _ _



theorem projection_value : executionSignature.valueOf? projectionName =
    some NativeVectorAll.ResultView.program := by
  change checkingSignature.valueOf? projectionName = _
  simp [valueLookup]

theorem projection_steps {n : Nat} (result arity children bundle : Tower.Tm n) :
    TypedEquality.Reduces rules (projection result arity children bundle)
      (NativeVectorAll.ResultView.project treeTm result arity children bundle) := by
  have delta : TypedEquality.Reduces rules (.const projectionName : Tower.Tm n)
      (liftClosed NativeVectorAll.ResultView.program) := .single (.root (.delta projection_value))
  exact (TypedEquality.Normalization.Reduces.appSpine_left delta
    [treeTm, result, arity, children, bundle]).trans
    (NativeVectorAll.ResultView.program_beta rules treeTm result arity children bundle)

theorem liftVectorPath {n : Nat} {left right : Tower.Tm n}
    (path : NativeVectorAll.CanonicalAdequacy.Steps left right) :
    TypedEquality.Reduces rules left right := by
  induction path with
  | refl => exact .refl
  | tail prior step ih => exact .tail ih (StepCore.includeSignature baseRules executionSignature step)

private theorem encodePointwise {n : Nat} (result : Tower.Tm n)
    (first second : Tower.Tm n → Tower.Tm n) (values : List (Tower.Tm n))
    (pointwise : ∀ value ∈ values, TypedEquality.Reduces rules (first value) (second value)) :
    TypedEquality.Reduces rules
      (NativeVectorAll.CanonicalAdequacy.encodeVector result (values.map first))
      (NativeVectorAll.CanonicalAdequacy.encodeVector result (values.map second)) := by
  induction values with
  | nil => exact .refl
  | cons head tail ih =>
      have headPath := TypedEquality.Normalization.Reduces.congr
        (f := fun term => vconsApp result (NativeVectorAll.CanonicalAdequacy.numeral tail.length) term
          (NativeVectorAll.CanonicalAdequacy.encodeVector result (tail.map first)))
        (fun step => .congAppFun (.congAppArg step)) (pointwise head List.mem_cons_self)
      have tailPath := TypedEquality.Normalization.Reduces.congr
        (f := vconsApp result (NativeVectorAll.CanonicalAdequacy.numeral tail.length) (second head))
        (fun step => .congAppArg step)
        (ih (fun value member => pointwise value (List.mem_cons_of_mem _ member)))
      simpa only [List.map_cons, NativeVectorAll.CanonicalAdequacy.encodeVector,
        List.length_map] using headPath.trans tailPath

theorem recursiveWitness_beta {n : Nat} (result leaf node child : Tower.Tm n) :
    TypedEquality.Reduces rules
      (.app (recursiveWitness (NativeVectorAll.ResultView.predicate result)
        (solvedMethod leaf) (branchMethod result node)) child)
      (fold result leaf node child) := by
  let body := eliminateApp (rename wk (NativeVectorAll.ResultView.predicate result))
    (rename wk (solvedMethod leaf)) (rename wk (branchMethod result node)) (.var 0)
  have beta : TypedEquality.Reduces rules (.app (.lam body) child) (inst0 child body) :=
    .single (.betaPi body child)
  have target : inst0 child body = fold result leaf node child := by
    simp only [body, inst0, eliminateApp, subst, subst_rename]
    change eliminateApp (subst ids (NativeVectorAll.ResultView.predicate result))
      (subst ids (solvedMethod leaf)) (subst ids (branchMethod result node)) child = _
    simp only [subst_ids]
    rfl
  rw [target] at beta
  exact beta

/-- A finite source vector yields one recursive result at every original
position, including repeated children. The children themselves may be open terms. -/
theorem childrenResults_canonical {n : Nat} (result leaf node : Tower.Tm n)
    (values : List (Tower.Tm n)) :
    TypedEquality.Reduces rules
      (childrenResults result leaf node (NativeVectorAll.CanonicalAdequacy.numeral values.length)
        (NativeVectorAll.CanonicalAdequacy.encodeVector treeTm values))
      (NativeVectorAll.CanonicalAdequacy.encodeVector result
        (values.map (fold result leaf node))) := by
  let witness := recursiveWitness (NativeVectorAll.ResultView.predicate result)
    (solvedMethod leaf) (branchMethod result node)
  have bundlePath := liftVectorPath (NativeVectorAll.CanonicalAdequacy.allEvidence_steps
    treeTm (NativeVectorAll.ResultView.predicate result) witness values)
  refine (projection_steps result _ _ _).trans ?_
  refine (TypedEquality.Normalization.Reduces.congr
    (f := NativeVectorAll.ResultView.project treeTm result
      (NativeVectorAll.CanonicalAdequacy.numeral values.length)
      (NativeVectorAll.CanonicalAdequacy.encodeVector treeTm values))
    (fun step => .congAppArg step) bundlePath).trans ?_
  refine (liftVectorPath (NativeVectorAll.ResultView.canonical_steps treeTm result witness values)).trans ?_
  apply encodePointwise
  intro child _
  exact recursiveWitness_beta result leaf node child


/-- The existing solved equation followed by the leaf adapter's beta step. -/
theorem fold_solved_steps {n : Nat} (result leaf node answer : Tower.Tm n) :
    TypedEquality.Reduces rules (fold result leaf node (solvedApp answer)) (.app leaf answer) := by
  refine Relation.ReflTransGen.head (.root (.declared ⟨IotaEvidence.solved
    (NativeVectorAll.ResultView.predicate result) (solvedMethod leaf)
    (branchMethod result node) answer⟩)) ?_
  have beta : TypedEquality.Reduces rules (.app (solvedMethod leaf) answer)
      (inst0 answer (.app (rename wk leaf) (.var 0))) := .single (.betaPi _ _)
  have target : inst0 answer (.app (rename wk leaf) (.var 0)) = .app leaf answer := by
    simp only [inst0, subst, subst_rename]
    change Tm.app (subst ids leaf) answer = _
    rw [subst_ids]
  rw [target] at beta
  exact beta

/-- The branch uses the old declared equation and the checked result adapter. -/
theorem fold_branch_steps {n : Nat} (result leaf node arity children : Tower.Tm n) :
    TypedEquality.Reduces rules (fold result leaf node (branchApp arity children))
      (.app (.app (.app node arity) children) (childrenResults result leaf node arity children)) := by
  refine Relation.ReflTransGen.head (.root (.declared ⟨IotaEvidence.branch
    (NativeVectorAll.ResultView.predicate result) (solvedMethod leaf)
    (branchMethod result node) arity children⟩)) ?_
  exact branchMethod_beta rules _ _ _ _ _

theorem fold_branch_canonical {n : Nat} (result leaf node : Tower.Tm n)
    (values : List (Tower.Tm n)) :
    TypedEquality.Reduces rules
      (fold result leaf node (branchApp (NativeVectorAll.CanonicalAdequacy.numeral values.length)
        (NativeVectorAll.CanonicalAdequacy.encodeVector treeTm values)))
      (.app (.app (.app node (NativeVectorAll.CanonicalAdequacy.numeral values.length))
        (NativeVectorAll.CanonicalAdequacy.encodeVector treeTm values))
        (NativeVectorAll.CanonicalAdequacy.encodeVector result
          (values.map (fold result leaf node)))) :=
  (fold_branch_steps result leaf node _ _).trans
    (TypedEquality.Normalization.Reduces.congr
      (fun step => .congAppArg step) (childrenResults_canonical result leaf node values))

theorem program_application (R : Rules Tower.Head) {n : Nat}
    (result leaf node input : Tower.Tm n) :
    TypedEquality.Reduces R (appSpine (liftClosed foldTerm) [result, leaf, node, input])
      (fold result leaf node input) := by
  let body : Tower.Tm (n + 4) := fold (.var 3) (.var 2) (.var 1) (.var 0)
  let sigma : Sub Tower.Head (n + 4) n := consSub input (consSub node (consSub leaf (consSub result ids)))
  have beta := lams_beta (R := R) 4 body [result, leaf, node, input] rfl
  have assigned : extendSub ids (fun j => [result, leaf, node, input].getD j defaultTm) 4 = sigma := rfl
  rw [assigned] at beta
  have target : subst sigma body = fold result leaf node input := by
    rw [show body = fold (.var 3) (.var 2) (.var 1) (.var 0) from rfl, subst_fold]
    rfl
  rw [target] at beta
  exact beta



theorem source_step : StepCore rules.computation rules.headEq
    (subst assignment branchLeft)
    (subst assignment PositiveInductiveVectorTreeElaboration.sourceBranchRight) :=
  .root (.declared ⟨sourceReceipt.evidence⟩)

theorem source_path : TypedEquality.Reduces rules
    (subst assignment branchLeft) projectedTarget :=
  Relation.ReflTransGen.head source_step (parsed_branch_beta rules)

theorem source_target_typed :
    FormationSensitive.Judgment rules context (subst assignment branchLeft) (.var 4) ∧
      FormationSensitive.Judgment rules context projectedTarget (.var 4) :=
  by
    constructor
    · simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
        result_endpoints.1.mapHead (extensionMorphism baseRules checking_extends_execution)
    · simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
        target_typed.mapHead (extensionMorphism baseRules checking_extends_execution)

theorem wrongBranch_refused : accepted context wrongBranchMethod
    (subst assignment (Ctx.lookup branchContext 2)) = false := by decide +kernel

def verdicts : List (String × Bool) :=
  [("VectorTree result fold replays at its whole polymorphic type", FormationSensitiveElaboration.replay
      checkingRules checkingDecoder .nil foldTerm foldType foldSubmission),
   ("VectorTree result adapter context replays all five slots", (List.finRange 5).all slotReplay),
   ("parsed VectorTree result target replays", FormationSensitiveElaboration.replay
      checkingRules checkingDecoder context projectedTarget (.var 4) targetSubmission),
   ("VectorTree original children cannot replace recursive results", !(accepted context wrongBranchMethod
      (subst assignment (Ctx.lookup branchContext 2))))]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp [verdicts, fold_replayed, target_replayed, slots_checked, wrongBranch_refused]



theorem projection_type : rules.constantType projectionName =
    some NativeVectorAll.ResultView.programType := by
  change combinedType baseRules executionSignature projectionName = _
  apply combinedType_of_signature baseRules executionSignature
  · decide +kernel
  · change checkingSignature.typeOf? projectionName = _
    simp [typeLookup]

/-- Delta unfolding retains the caller's displayed type. -/
theorem projection_typedUnfolding {n : Nat} {ambient : Tower.Ctx n} {displayed : Tower.Tm n}
    (typed : FormationSensitive.Judgment rules ambient (.const projectionName) displayed) :
    StepCore rules.computation rules.headEq (.const projectionName : Tower.Tm n)
        (liftClosed NativeVectorAll.ResultView.program) ∧
      FormationSensitive.Judgment rules ambient
        (liftClosed NativeVectorAll.ResultView.program) displayed := by
  have body : FormationSensitive.Judgment rules .nil NativeVectorAll.ResultView.program
      NativeVectorAll.ResultView.programType := by
    simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
      body_typed.mapHead (extensionMorphism baseRules checking_extends_execution)
  exact typed.delta projection_value projection_type body.typing

theorem projection_typed : FormationSensitive.Judgment rules .nil (.const projectionName)
    NativeVectorAll.ResultView.programType := by
  have body : FormationSensitive.Judgment rules .nil NativeVectorAll.ResultView.program
      NativeVectorAll.ResultView.programType := by
    simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
      body_typed.mapHead (extensionMorphism baseRules checking_extends_execution)
  obtain ⟨level, isUniverse, formed⟩ := body.regularity (universes.includeSignature executionSignature)
  exact ⟨.nil, .const projection_type formed.typing isUniverse⟩

theorem unfolding_witness :
    StepCore rules.computation rules.headEq (.const projectionName : Tower.Tm 0)
        (liftClosed NativeVectorAll.ResultView.program) ∧
      FormationSensitive.Judgment rules .nil (liftClosed NativeVectorAll.ResultView.program)
        NativeVectorAll.ResultView.programType := projection_typedUnfolding projection_typed

theorem canonical_witness :
    TypedEquality.Reduces rules
      (childrenResults (.var 3) (.var 2) (.var 1)
        (NativeVectorAll.CanonicalAdequacy.numeral 3)
        (NativeVectorAll.CanonicalAdequacy.encodeVector treeTm
          [solvedApp (.var 0), branchApp zeroTm (vnilApp treeTm), solvedApp (.var 0)]))
      (NativeVectorAll.CanonicalAdequacy.encodeVector (.var 3)
        [fold (.var 3) (.var 2) (.var 1) (solvedApp (.var 0)),
          fold (.var 3) (.var 2) (.var 1) (branchApp zeroTm (vnilApp treeTm)),
          fold (.var 3) (.var 2) (.var 1) (solvedApp (.var 0))] : Tower.Tm 4) :=
  by
    simpa only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] using
      childrenResults_canonical (n := 4) (.var 3) (.var 2) (.var 1)
        [solvedApp (.var 0), branchApp zeroTm (vnilApp treeTm), solvedApp (.var 0)]

#print axioms contextMorphism
#print axioms fold_typed
#print axioms sourceReceipt
#print axioms source_path
#print axioms source_target_typed
#print axioms wrongBranch_refused
#print axioms all_verdicts
#print axioms projection_typedUnfolding
#print axioms unfolding_witness
#print axioms canonical_witness
end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest.ResultFold
