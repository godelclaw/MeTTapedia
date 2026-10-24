import Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeGuest

/-!
# Executable controls and typed receipts for the registered-List SearchTree guest

The producer is untrusted.  Every positive row is replayed by the existing
formation-sensitive checker before it is turned into a proof-relevant iota
receipt.  The negative row removes the List-position bundle.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeGuest

open Presentation Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

def endpointVerdicts : List (String × Bool) :=
  [("solved source forms", endpointAccepted solvedContext solvedLeft solvedIotaType),
   ("solved target forms", endpointAccepted solvedContext solvedRight solvedIotaType),
   ("nested branch source forms", endpointAccepted branchContext branchLeft branchIotaType),
   ("nested child bundle forms", endpointAccepted branchContext
      (liftChildren (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
      (bundleType (treeApp (.var 4)) (.var 3) (.var 0))),
   ("nested branch target forms", endpointAccepted branchContext branchRight branchIotaType),
   ("branch refuses one unbundled recursive result",
      !(endpointAccepted branchContext
        (.app (.app (.var 1) (.var 0)) (.var 0)) branchIotaType))]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem solvedLeftAccepted :
    endpointAccepted solvedContext solvedLeft solvedIotaType = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem solvedRightAccepted :
    endpointAccepted solvedContext solvedRight solvedIotaType = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem branchLeftAccepted :
    endpointAccepted branchContext branchLeft branchIotaType = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem branchBundleAccepted :
    endpointAccepted branchContext
      (liftChildren (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
      (bundleType (treeApp (.var 4)) (.var 3) (.var 0)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem branchRightAccepted :
    endpointAccepted branchContext branchRight branchIotaType = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem unbundledBranchRefused :
    endpointAccepted branchContext
      (.app (.app (.var 1) (.var 0)) (.var 0)) branchIotaType = false := by
  decide +kernel

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
      (liftChildren (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
      (bundleType (treeApp (.var 4)) (.var 3) (.var 0)) :=
  endpointAccepted_sound branchBundleAccepted

theorem branch_rows_formed :
    FormationSensitive.Judgment inventoryRules branchContext
        branchLeft branchIotaType ∧
      FormationSensitive.Judgment inventoryRules branchContext
        branchRight branchIotaType :=
  ⟨endpointAccepted_sound branchLeftAccepted,
    endpointAccepted_sound branchRightAccepted⟩

noncomputable def solvedReceipt : ProofRelevantStepReceipt baseRules signature
    iotaComputation solvedContext solvedLeft solvedRight solvedIotaType where
  sourceTyping := (liftJudgment solved_rows_formed.1).toRaw
  targetTyping := (liftJudgment solved_rows_formed.2).toRaw
  evidence := .solved (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

noncomputable def branchReceipt : ProofRelevantStepReceipt baseRules signature
    iotaComputation branchContext branchLeft branchRight branchIotaType where
  sourceTyping := (liftJudgment branch_rows_formed.1).toRaw
  targetTyping := (liftJudgment branch_rows_formed.2).toRaw
  evidence := .branch (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

noncomputable def solvedSchema : IndexedFamily.IotaSchema baseRules signature
    iotaComputation 5 where
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

/-- Typed substitution transports the complete nested branch receipt,
including the List-position bundle and the retained branch witness. -/
noncomputable def branchReceipt_substitute {m : Nat} {targetContext : Tower.Ctx m}
    (substitution : Sub Tower.Head 5 m)
    (typed : CtxMor rules branchContext targetContext substitution) :
    ProofRelevantStepReceipt baseRules signature iotaComputation targetContext
      (subst substitution branchLeft) (subst substitution branchRight)
      (subst substitution branchIotaType) :=
  branchReceipt.substitute substitution typed

#print axioms endpointVerdicts_eq_true
#print axioms solved_rows_formed
#print axioms branch_bundle_formed
#print axioms branch_rows_formed
#print axioms solvedReceipt
#print axioms branchReceipt
#print axioms branchReceipt_substitute

end Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeGuest
