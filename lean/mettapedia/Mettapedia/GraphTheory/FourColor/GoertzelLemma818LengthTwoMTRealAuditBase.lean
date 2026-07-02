import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818LengthTwoMTRealAudit

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMTRealFiberBridge

/-!
# Length-two `mirror,normal` real audit assembly base
-/

theorem mtLengthTwoStatesFromLeft_all_compatible (left : TauState) :
    (lengthTwoStatesFromLeft mtWord left).all (compatibleChainStates mtWord) = true := by
  rw [List.all_eq_true]
  intro states hmem
  unfold lengthTwoStatesFromLeft at hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨right, hright, rfl⟩
  rw [List.mem_filter] at hright
  rcases hright with ⟨_, hcomp⟩
  simpa [compatibleChainStates, mtWord, tauOrientAt, chainStateAt, listGetD] using hcomp

theorem mtAllChainStates_compatible :
    (allChainStates mtWord).all (compatibleChainStates mtWord) = true := by
  rw [mtAllChainStates_lengthTwo_eq]
  rw [List.all_eq_true]
  intro states hmem
  rw [bindList_mem] at hmem
  rcases hmem with ⟨left, _, hstates⟩
  have h := mtLengthTwoStatesFromLeft_all_compatible left
  rw [List.all_eq_true] at h
  exact h states hstates

theorem mtEmptyFiberConnected_of_extract_nil {key : List LColor}
    (h : lengthTwoFiberExtractLeftStateList mtWord key allTauStates = []) :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) key) = true := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts key]
  rw [h]
  rfl

theorem mtColorAssignments_eq_fiberKeys :
    colorAssignments4 = [mtFiber0Key, mtFiber1Key, mtFiber2Key, mtFiber3Key, mtFiber4Key, mtFiber5Key, mtFiber6Key, mtFiber7Key, mtFiber8Key, mtFiber9Key, mtFiber10Key, mtFiber11Key, mtFiber12Key, mtFiber13Key, mtFiber14Key, mtFiber15Key, mtFiber16Key, mtFiber17Key, mtFiber18Key, mtFiber19Key, mtFiber20Key, mtFiber21Key, mtFiber22Key, mtFiber23Key, mtFiber24Key, mtFiber25Key, mtFiber26Key, mtFiber27Key, mtFiber28Key, mtFiber29Key, mtFiber30Key, mtFiber31Key, mtFiber32Key, mtFiber33Key, mtFiber34Key, mtFiber35Key, mtFiber36Key, mtFiber37Key, mtFiber38Key, mtFiber39Key, mtFiber40Key, mtFiber41Key, mtFiber42Key, mtFiber43Key, mtFiber44Key, mtFiber45Key, mtFiber46Key, mtFiber47Key, mtFiber48Key, mtFiber49Key, mtFiber50Key, mtFiber51Key, mtFiber52Key, mtFiber53Key, mtFiber54Key, mtFiber55Key, mtFiber56Key, mtFiber57Key, mtFiber58Key, mtFiber59Key, mtFiber60Key, mtFiber61Key, mtFiber62Key, mtFiber63Key, mtFiber64Key, mtFiber65Key, mtFiber66Key, mtFiber67Key, mtFiber68Key, mtFiber69Key, mtFiber70Key, mtFiber71Key, mtFiber72Key, mtFiber73Key, mtFiber74Key, mtFiber75Key, mtFiber76Key, mtFiber77Key, mtFiber78Key, mtFiber79Key, mtFiber80Key] := by
  decide

end GoertzelLemma818LengthTwoMTRealAudit

end Mettapedia.GraphTheory.FourColor
