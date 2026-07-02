import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818LengthTwoTMRealAudit

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoTMRealFiberBridge

/-!
# Length-two `normal,mirror` real audit assembly base

This module contains the structural compatibility and shared empty-fiber hooks
used to assemble the real `chainLKRInAudit` theorem for `tmWord` without
raising Lean recursion limits.
-/

theorem tmLengthTwoStatesFromLeft_all_compatible (left : TauState) :
    (lengthTwoStatesFromLeft tmWord left).all (compatibleChainStates tmWord) = true := by
  rw [List.all_eq_true]
  intro states hmem
  unfold lengthTwoStatesFromLeft at hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨right, hright, rfl⟩
  rw [List.mem_filter] at hright
  rcases hright with ⟨_, hcomp⟩
  simpa [compatibleChainStates, tmWord, tauOrientAt, chainStateAt, listGetD] using hcomp

theorem tmAllChainStates_compatible :
    (allChainStates tmWord).all (compatibleChainStates tmWord) = true := by
  rw [tmAllChainStates_lengthTwo_eq]
  rw [List.all_eq_true]
  intro states hmem
  rw [bindList_mem] at hmem
  rcases hmem with ⟨left, _, hstates⟩
  have h := tmLengthTwoStatesFromLeft_all_compatible left
  rw [List.all_eq_true] at h
  exact h states hstates

theorem tmEmptyFiberConnected_of_extract_nil {key : List LColor}
    (h : lengthTwoFiberExtractLeftStateList tmWord key allTauStates = []) :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) key) = true := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts key]
  rw [h]
  rfl

theorem tmColorAssignments_eq_fiberKeys :
    colorAssignments4 = [tmFiber0Key, tmFiber1Key, tmFiber2Key, tmFiber3Key, tmFiber4Key, tmFiber5Key, tmFiber6Key, tmFiber7Key, tmFiber8Key, tmFiber9Key, tmFiber10Key, tmFiber11Key, tmFiber12Key, tmFiber13Key, tmFiber14Key, tmFiber15Key, tmFiber16Key, tmFiber17Key, tmFiber18Key, tmFiber19Key, tmFiber20Key, tmFiber21Key, tmFiber22Key, tmFiber23Key, tmFiber24Key, tmFiber25Key, tmFiber26Key, tmFiber27Key, tmFiber28Key, tmFiber29Key, tmFiber30Key, tmFiber31Key, tmFiber32Key, tmFiber33Key, tmFiber34Key, tmFiber35Key, tmFiber36Key, tmFiber37Key, tmFiber38Key, tmFiber39Key, tmFiber40Key, tmFiber41Key, tmFiber42Key, tmFiber43Key, tmFiber44Key, tmFiber45Key, tmFiber46Key, tmFiber47Key, tmFiber48Key, tmFiber49Key, tmFiber50Key, tmFiber51Key, tmFiber52Key, tmFiber53Key, tmFiber54Key, tmFiber55Key, tmFiber56Key, tmFiber57Key, tmFiber58Key, tmFiber59Key, tmFiber60Key, tmFiber61Key, tmFiber62Key, tmFiber63Key, tmFiber64Key, tmFiber65Key, tmFiber66Key, tmFiber67Key, tmFiber68Key, tmFiber69Key, tmFiber70Key, tmFiber71Key, tmFiber72Key, tmFiber73Key, tmFiber74Key, tmFiber75Key, tmFiber76Key, tmFiber77Key, tmFiber78Key, tmFiber79Key, tmFiber80Key] := by
  decide

end GoertzelLemma818LengthTwoTMRealAudit

end Mettapedia.GraphTheory.FourColor
