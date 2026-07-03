import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818LengthTwoMMRealAudit

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMMRealFiberBridge

/-!
# Length-two `mirror,mirror` real audit assembly base
-/

theorem mmLengthTwoStatesFromLeft_all_compatible (left : TauState) :
    (lengthTwoStatesFromLeft mmWord left).all (compatibleChainStates mmWord) = true := by
  rw [List.all_eq_true]
  intro states hmem
  unfold lengthTwoStatesFromLeft at hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨right, hright, rfl⟩
  rw [List.mem_filter] at hright
  rcases hright with ⟨_, hcomp⟩
  simpa [compatibleChainStates, mmWord, tauOrientAt, chainStateAt, listGetD] using hcomp

theorem mmAllChainStates_compatible :
    (allChainStates mmWord).all (compatibleChainStates mmWord) = true := by
  rw [mmAllChainStates_lengthTwo_eq]
  rw [List.all_eq_true]
  intro states hmem
  rw [bindList_mem] at hmem
  rcases hmem with ⟨left, _, hstates⟩
  have h := mmLengthTwoStatesFromLeft_all_compatible left
  rw [List.all_eq_true] at h
  exact h states hstates

theorem mmEmptyFiberConnected_of_extract_nil {key : List LColor}
    (h : lengthTwoFiberExtractLeftStateList mmWord key allTauStates = []) :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) key) = true := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts key]
  rw [h]
  rfl

theorem mmColorAssignments_eq_fiberKeys :
    colorAssignments4 = [mmFiber0Key, mmFiber1Key, mmFiber2Key, mmFiber3Key, mmFiber4Key, mmFiber5Key, mmFiber6Key, mmFiber7Key, mmFiber8Key, mmFiber9Key, mmFiber10Key, mmFiber11Key, mmFiber12Key, mmFiber13Key, mmFiber14Key, mmFiber15Key, mmFiber16Key, mmFiber17Key, mmFiber18Key, mmFiber19Key, mmFiber20Key, mmFiber21Key, mmFiber22Key, mmFiber23Key, mmFiber24Key, mmFiber25Key, mmFiber26Key, mmFiber27Key, mmFiber28Key, mmFiber29Key, mmFiber30Key, mmFiber31Key, mmFiber32Key, mmFiber33Key, mmFiber34Key, mmFiber35Key, mmFiber36Key, mmFiber37Key, mmFiber38Key, mmFiber39Key, mmFiber40Key, mmFiber41Key, mmFiber42Key, mmFiber43Key, mmFiber44Key, mmFiber45Key, mmFiber46Key, mmFiber47Key, mmFiber48Key, mmFiber49Key, mmFiber50Key, mmFiber51Key, mmFiber52Key, mmFiber53Key, mmFiber54Key, mmFiber55Key, mmFiber56Key, mmFiber57Key, mmFiber58Key, mmFiber59Key, mmFiber60Key, mmFiber61Key, mmFiber62Key, mmFiber63Key, mmFiber64Key, mmFiber65Key, mmFiber66Key, mmFiber67Key, mmFiber68Key, mmFiber69Key, mmFiber70Key, mmFiber71Key, mmFiber72Key, mmFiber73Key, mmFiber74Key, mmFiber75Key, mmFiber76Key, mmFiber77Key, mmFiber78Key, mmFiber79Key, mmFiber80Key] := by
  decide

end GoertzelLemma818LengthTwoMMRealAudit

end Mettapedia.GraphTheory.FourColor
