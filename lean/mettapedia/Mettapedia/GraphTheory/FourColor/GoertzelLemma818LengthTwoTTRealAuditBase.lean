import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoRealFiberBridgePrototype

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818LengthTwoTTRealAudit

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype

/-!
# Length-two `tau,tau` real audit assembly base

This module contains the structural compatibility and shared empty-fiber hooks
used to assemble the real `chainLKRInAudit` theorem for the two-gadget
`tau,tau` word without raising Lean recursion limits.
-/

theorem ttLengthTwoStatesFromLeft_all_compatible (left : TauState) :
    (lengthTwoStatesFromLeft ttWord left).all (compatibleChainStates ttWord) = true := by
  rw [List.all_eq_true]
  intro states hmem
  unfold lengthTwoStatesFromLeft at hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨right, hright, rfl⟩
  rw [List.mem_filter] at hright
  rcases hright with ⟨_, hcomp⟩
  simpa [compatibleChainStates, ttWord, tauOrientAt, chainStateAt, listGetD] using hcomp

theorem ttAllChainStates_compatible :
    (allChainStates ttWord).all (compatibleChainStates ttWord) = true := by
  rw [ttAllChainStates_lengthTwo_eq]
  rw [List.all_eq_true]
  intro states hmem
  rw [bindList_mem] at hmem
  rcases hmem with ⟨left, _, hstates⟩
  have h := ttLengthTwoStatesFromLeft_all_compatible left
  rw [List.all_eq_true] at h
  exact h states hstates

theorem ttEmptyFiberConnected_of_extract_nil {key : List LColor}
    (h : lengthTwoFiberExtractLeftStateList ttWord key allTauStates = []) :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) key) = true := by
  rw [chainFiberFrom_tt_lengthTwo_eq_extracts key]
  rw [h]
  rfl

theorem ttColorAssignments_eq_fiberKeys :
    colorAssignments4 = [ttFiber0Key, ttFiber1Key, ttFiber2Key, ttFiber3Key, ttFiber4Key, ttFiber5Key, ttFiber6Key, ttFiber7Key, ttFiber8Key, ttFiber9Key, ttFiber10Key, ttFiber11Key, ttFiber12Key, ttFiber13Key, ttFiber14Key, ttFiber15Key, ttFiber16Key, ttFiber17Key, ttFiber18Key, ttFiber19Key, ttFiber20Key, ttFiber21Key, ttFiber22Key, ttFiber23Key, ttFiber24Key, ttFiber25Key, ttFiber26Key, ttFiber27Key, ttFiber28Key, ttFiber29Key, ttFiber30Key, ttFiber31Key, ttFiber32Key, ttFiber33Key, ttFiber34Key, ttFiber35Key, ttFiber36Key, ttFiber37Key, ttFiber38Key, ttFiber39Key, ttFiber40Key, ttFiber41Key, ttFiber42Key, ttFiber43Key, ttFiber44Key, ttFiber45Key, ttFiber46Key, ttFiber47Key, ttFiber48Key, ttFiber49Key, ttFiber50Key, ttFiber51Key, ttFiber52Key, ttFiber53Key, ttFiber54Key, ttFiber55Key, ttFiber56Key, ttFiber57Key, ttFiber58Key, ttFiber59Key, ttFiber60Key, ttFiber61Key, ttFiber62Key, ttFiber63Key, ttFiber64Key, ttFiber65Key, ttFiber66Key, ttFiber67Key, ttFiber68Key, ttFiber69Key, ttFiber70Key, ttFiber71Key, ttFiber72Key, ttFiber73Key, ttFiber74Key, ttFiber75Key, ttFiber76Key, ttFiber77Key, ttFiber78Key, ttFiber79Key, ttFiber80Key] := by
  decide

end GoertzelLemma818LengthTwoTTRealAudit

end Mettapedia.GraphTheory.FourColor
