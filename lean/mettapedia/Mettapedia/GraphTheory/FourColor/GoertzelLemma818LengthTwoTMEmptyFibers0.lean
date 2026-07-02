import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealAuditBase

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818LengthTwoTMRealAudit

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype

/-!
# Empty `normal,mirror` length-two fibers, group 0

This generated module proves that its assigned fixed-input fibers extract to the
empty real fiber, then packages each as a `chainFiberConnected` theorem.
-/

theorem tmFiber0ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber0Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber0RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber0Key) = true := by
  exact tmEmptyFiberConnected_of_extract_nil tmFiber0ExtractAllLefts_eq_nil

theorem tmFiber1ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber1Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber1RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber1Key) = true := by
  exact tmEmptyFiberConnected_of_extract_nil tmFiber1ExtractAllLefts_eq_nil

theorem tmFiber2ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber2Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber2RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber2Key) = true := by
  exact tmEmptyFiberConnected_of_extract_nil tmFiber2ExtractAllLefts_eq_nil

theorem tmFiber12ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber12Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber12RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber12Key) = true := by
  exact tmEmptyFiberConnected_of_extract_nil tmFiber12ExtractAllLefts_eq_nil

theorem tmFiber13ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber13Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber13RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber13Key) = true := by
  exact tmEmptyFiberConnected_of_extract_nil tmFiber13ExtractAllLefts_eq_nil

theorem tmFiber14ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber14Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber14RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber14Key) = true := by
  exact tmEmptyFiberConnected_of_extract_nil tmFiber14ExtractAllLefts_eq_nil

theorem tmFiber15ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber15Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber15RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber15Key) = true := by
  exact tmEmptyFiberConnected_of_extract_nil tmFiber15ExtractAllLefts_eq_nil

theorem tmFiber16ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber16Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber16RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber16Key) = true := by
  exact tmEmptyFiberConnected_of_extract_nil tmFiber16ExtractAllLefts_eq_nil

theorem tmFiber17ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber17Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber17RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber17Key) = true := by
  exact tmEmptyFiberConnected_of_extract_nil tmFiber17ExtractAllLefts_eq_nil

end GoertzelLemma818LengthTwoTMRealAudit

end Mettapedia.GraphTheory.FourColor
