import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeSolvedChecks
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllResultsChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeRegularity
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeBranchChecks
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveIndexedContainerBundleRealization

/-!
# Qualified VectorTree receipts and provider comparisons

Declaration admission and constructor checks are qualified independently.
Their existing judgments meet here in the proof-relevant iota receipts and
complete textual-provider inventory.
-/

set_option autoImplicit false
set_option Elab.async false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest

open Presentation Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

def endpointVerdicts : List (String × Bool) :=
  [("VectorTree solved source forms",
      endpointAccepted solvedContext solvedLeft solvedIotaType),
   ("VectorTree solved target forms",
      endpointAccepted solvedContext solvedRight solvedIotaType),
   ("VectorTree branch source forms",
      endpointAccepted branchContext branchLeft branchIotaType),
   ("VectorTree exact Vector bundle forms",
      endpointAccepted branchContext branchBundle branchBundleType),
   ("VectorTree branch target forms",
      endpointAccepted branchContext branchRight branchIotaType),
   ("VectorTree branch refuses an unbundled child Vector",
      !(endpointAccepted branchContext
        (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0))
        branchIotaType))]

theorem endpointVerdicts_eq_true : endpointVerdicts.all Prod.snd = true := by
  simp [endpointVerdicts, solvedLeftAccepted, solvedRightAccepted,
    branchLeftAccepted, branchBundleAccepted, branchRightAccepted,
    unbundledBranchRefused]

theorem solved_rows_formed :
    FormationSensitive.Judgment inventoryRules solvedContext
        solvedLeft solvedIotaType ∧
      FormationSensitive.Judgment inventoryRules solvedContext
        solvedRight solvedIotaType :=
  ⟨endpointAccepted_sound solvedLeftAccepted,
    endpointAccepted_sound solvedRightAccepted⟩

theorem branch_bundle_formed :
    FormationSensitive.Judgment inventoryRules branchContext
      branchBundle branchBundleType :=
  endpointAccepted_sound branchBundleAccepted

theorem branch_rows_formed :
    FormationSensitive.Judgment inventoryRules branchContext
        branchLeft branchIotaType ∧
      FormationSensitive.Judgment inventoryRules branchContext
        branchRight branchIotaType :=
  ⟨endpointAccepted_sound branchLeftAccepted,
    endpointAccepted_sound branchRightAccepted⟩

theorem signature_formed : signature.Formed baseRules where
  fresh := inventory_formed.fresh
  types := by
    intro name type selected
    obtain ⟨u, isUniverse, typed⟩ := inventory_formed.types selected
    refine ⟨u, isUniverse, ?_⟩
    simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
      typed.mapHead (extensionMorphism baseRules inventory_extends_signature)
  values := by
    intro name type value typeSelected valueSelected
    have typed := inventory_formed.values typeSelected valueSelected
    simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
      typed.mapHead (extensionMorphism baseRules inventory_extends_signature)
  noSelfDelta := fun selected => inventory_formed.noSelfDelta selected

noncomputable def solvedReceipt : ProofRelevantStepReceipt baseRules signature
    iotaComputation solvedContext solvedLeft solvedRight solvedIotaType where
  sourceTyping := (liftJudgment solved_rows_formed.1).toRaw
  targetTyping := (liftJudgment solved_rows_formed.2).toRaw
  evidence := .solved (.var 3) (.var 2) (.var 1) (.var 0)

noncomputable def branchReceipt : ProofRelevantStepReceipt baseRules signature
    iotaComputation branchContext branchLeft branchRight branchIotaType where
  sourceTyping := (liftJudgment branch_rows_formed.1).toRaw
  targetTyping := (liftJudgment branch_rows_formed.2).toRaw
  evidence := .branch (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

noncomputable def solvedSchema : IndexedFamily.IotaSchema baseRules signature
    iotaComputation 4 where
  context := solvedContext
  left := solvedLeft
  right := solvedRight
  type := solvedIotaType
  receipt := solvedReceipt

noncomputable def branchSchema : IndexedFamily.IotaSchema baseRules signature
    iotaComputation 5 where
  context := branchContext
  left := branchLeft
  right := branchRight
  type := branchIotaType
  receipt := branchReceipt

noncomputable def branchReceipt_substitute {m : Nat}
    {targetContext : Tower.Ctx m} (sigma : Sub Tower.Head 5 m)
    (typed : CtxMor rules branchContext targetContext sigma) :
    ProofRelevantStepReceipt baseRules signature iotaComputation targetContext
      (subst sigma branchLeft) (subst sigma branchRight)
      (subst sigma branchIotaType) :=
  branchReceipt.substitute sigma typed

/-! ## Provider routing over the complete textual constructor inventory -/

namespace ProviderInventory

open Mettapedia.TypeTheory.IndexedPositiveContainer
open FormationSensitiveIndexedContainerBundleRealization
open FormationSensitiveIndexedContainerBundleRealization.MixedControl

/-- The ordered semantic codes come from the same resolved textual family as
the generated declaration entries. -/
def codes : List (Code VectorControl.interface VectorControl.registry 0 []) :=
  ModuleSource.IndexedPositiveVectorLowering.Controls.family.constructors.map
    (fun constructor => constructor.body.erase)

theorem codes_eq :
    codes = [ModuleSource.IndexedPositiveVectorLowering.Controls.solved.body.erase,
      ModuleSource.IndexedPositiveVectorLowering.Controls.branch.body.erase] := rfl

noncomputable def solvedRequest :
    FormationSensitiveIndexedContainerBundleRealization.Code.ConstructorRequest (Element := Element)
      ModuleSource.IndexedPositiveVectorLowering.Controls.solved.body.erase where
  environment := PUnit.unit
  index := ()
  shape := ⟨false, ⟨⟨rfl⟩⟩⟩
  children position := PEmpty.elim position

noncomputable def branchRequest :
    FormationSensitiveIndexedContainerBundleRealization.Code.ConstructorRequest (Element := Element)
      ModuleSource.IndexedPositiveVectorLowering.Controls.branch.body.erase where
  environment := PUnit.unit
  index := ()
  shape := VectorControl.shapeAt 2
  children := by
    intro position
    cases position with
    | inl vectorPosition => exact vectorChildren vectorPosition
    | inr impossible => exact PEmpty.elim impossible

/-- One shape/children request for each retained constructor occurrence. -/
noncomputable def requests :
    FormationSensitiveIndexedContainerBundleRealization.Code.InventoryRequests (Element := Element) codes := by
  intro occurrence
  refine Fin.cases ?_ (fun tail => ?_) occurrence
  · change FormationSensitiveIndexedContainerBundleRealization.Code.ConstructorRequest (Element := Element)
      ModuleSource.IndexedPositiveVectorLowering.Controls.solved.body.erase
    exact solvedRequest
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) tail
    change FormationSensitiveIndexedContainerBundleRealization.Code.ConstructorRequest (Element := Element)
      ModuleSource.IndexedPositiveVectorLowering.Controls.branch.body.erase
    exact branchRequest

noncomputable def accepted :=
  FormationSensitiveIndexedContainerBundleRealization.Code.realizeInventory? pairAlgebra qualified unitMotive completeProviders
    codes requests

def solvedOccurrence : Fin codes.length := ⟨0, by decide⟩
def branchOccurrence : Fin codes.length := ⟨1, by decide⟩

theorem solved_provider_accepted :
    (accepted solvedOccurrence).isSome = true := by
  rfl

theorem branch_provider_accepted :
    (accepted branchOccurrence).isSome = true := by
  rfl

noncomputable def missingNested :=
  FormationSensitiveIndexedContainerBundleRealization.Code.realizeInventory? pairAlgebra qualified unitMotive
    missingNestedProviders codes requests

/-- The constructor without a nested leaf remains realizable, while the
textual Vector branch retains the missing-provider refusal. -/
theorem missingNested_verdicts :
    (missingNested solvedOccurrence).isSome = true ∧
      missingNested branchOccurrence = none := by
  exact ⟨rfl, rfl⟩

end ProviderInventory

#print axioms inventoryAccepted_eq_true
#print axioms inventory_formed
#print axioms endpointVerdicts_eq_true
#print axioms branch_bundle_formed
#print axioms signature_formed
#print axioms solvedReceipt
#print axioms branchReceipt
#print axioms branchReceipt_substitute
#print axioms ProviderInventory.codes_eq
#print axioms ProviderInventory.solved_provider_accepted
#print axioms ProviderInventory.branch_provider_accepted
#print axioms ProviderInventory.missingNested_verdicts

end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest

namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest
namespace ResultFold
open Presentation Presentation.Declaration
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

theorem old_lookup_absent : inventorySignature.entries projectionName = none := by
  rfl

theorem projection_fresh : inventoryRules.constantType projectionName = none := by
  decide +kernel

theorem prior_extends : inventorySignature.Extends checkingSignature :=
  Signature.ofList_extends_append PositiveInductiveVectorTreeGuest.entries _

theorem entryLookup (name : DeclName) : checkingSignature.entries name =
    if name = projectionName then
      some ⟨NativeVectorAll.ResultView.programType, some NativeVectorAll.ResultView.program⟩
    else inventorySignature.entries name := by
  change (Signature.ofList (PositiveInductiveVectorTreeGuest.entries ++ _)).entries name = _
  rw [Signature.entries_ofList_append]
  change (inventorySignature.entries name).orElse (fun _ =>
    if name = projectionName then
      some ⟨NativeVectorAll.ResultView.programType, some NativeVectorAll.ResultView.program⟩ else none) = _
  by_cases same : name = projectionName
  · subst name
    rw [old_lookup_absent]
    rfl
  · simp [same]


theorem typeLookup (name : DeclName) : checkingSignature.typeOf? name =
    if name = projectionName then some NativeVectorAll.ResultView.programType
    else inventorySignature.typeOf? name := by
  by_cases same : name = projectionName <;> simp [Signature.typeOf?, entryLookup, same]

theorem old_value_none (name : DeclName) : inventorySignature.valueOf? name = none := by
  cases selected : inventorySignature.entries name with
  | none => simp [Signature.valueOf?, selected]
  | some entry =>
      have member := Signature.entries_ofList_mem PositiveInductiveVectorTreeGuest.entries selected
      have emptyValues : ∀ item ∈ PositiveInductiveVectorTreeGuest.entries, item.2.value? = none := by
        intro item present
        simp only [PositiveInductiveVectorTreeGuest.entries, List.mem_cons, List.not_mem_nil, or_false] at present
        rcases present with rfl | rfl | rfl | rfl | rfl <;> rfl
      simp only [Signature.valueOf?, selected, Option.bind_some]
      exact emptyValues (name, entry) member


theorem valueLookup (name : DeclName) : checkingSignature.valueOf? name =
    if name = projectionName then some NativeVectorAll.ResultView.program else none := by
  by_cases same : name = projectionName
  · simp [Signature.valueOf?, entryLookup, same]
  · simpa only [Signature.valueOf?, entryLookup, same, if_false] using old_value_none name

theorem universes : FormationSensitive.UniverseRegularity baseRules :=
  FormationSensitive.towerUniverseRegularity.includeSignature NativeVectorAll.signature

theorem body_typed : FormationSensitive.Judgment checkingRules .nil NativeVectorAll.ResultView.program
    NativeVectorAll.ResultView.programType :=
  NativeVectorAll.ResultView.program_formed.includeSignature checkingSignature

theorem checking_formed : checkingSignature.Formed baseRules where
  fresh := by
    intro name entry known
    rw [entryLookup] at known
    split at known
    · have baseNone : baseRules.constantType projectionName = none := by decide +kernel
      simpa only [‹name = projectionName›] using baseNone
    · exact inventory_formed.fresh known
  types := by
    intro name type known
    rw [typeLookup] at known
    split at known
    · cases Option.some.inj known
      obtain ⟨level, isUniverse, formed⟩ := NativeVectorAll.ResultView.program_formed.regularity universes
      exact ⟨level, isUniverse, (formed.includeSignature checkingSignature).toRaw⟩
    · obtain ⟨level, isUniverse, typed⟩ := inventory_formed.types known
      exact ⟨level, isUniverse, by
        simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
          typed.mapHead (extensionMorphism baseRules prior_extends)⟩
  values := by
    intro name type value typed selected
    rw [valueLookup] at selected
    split at selected
    · rename_i same
      rw [typeLookup, if_pos same] at typed
      cases Option.some.inj typed
      cases Option.some.inj selected
      exact body_typed.toRaw
    · cases selected
  noSelfDelta := by
    intro name value selected
    rw [valueLookup] at selected
    split at selected
    · cases Option.some.inj selected
      intro impossible
      cases impossible
    · cases selected

theorem checking_extends_execution : checkingSignature.Extends executionSignature where
  entries := fun known => known
  computation := by
    intro n left right impossible
    change False at impossible
    exact impossible.elim

theorem guest_extends_execution : PositiveInductiveVectorTreeGuest.signature.Extends executionSignature where
  entries := by
    intro name entry known
    exact prior_extends.entries known
  computation := fun step => step

theorem execution_formed : executionSignature.Formed baseRules where
  fresh := checking_formed.fresh
  types := by
    intro name type known
    obtain ⟨level, isUniverse, typed⟩ := checking_formed.types known
    exact ⟨level, isUniverse, by
      simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
        typed.mapHead (extensionMorphism baseRules checking_extends_execution)⟩
  values := by
    intro name type value typed selected
    simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
      (checking_formed.values typed selected).mapHead
        (extensionMorphism baseRules checking_extends_execution)
  noSelfDelta := checking_formed.noSelfDelta

#print axioms checking_formed
#print axioms execution_formed
end ResultFold
end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest
