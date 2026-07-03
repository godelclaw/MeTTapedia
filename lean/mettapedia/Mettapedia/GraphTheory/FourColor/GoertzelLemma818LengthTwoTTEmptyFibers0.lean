import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTTRealAuditBase

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818LengthTwoTTRealAudit

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype

/-!
# Empty `tau,tau` length-two fibers, group 0

This generated module proves that its assigned fixed-input fibers extract to the
empty real fiber, then packages each as a `chainFiberConnected` theorem.
-/

theorem ttFiber0ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber0Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber0RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber0Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber0ExtractAllLefts_eq_nil

theorem ttFiber1ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber1Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber1RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber1Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber1ExtractAllLefts_eq_nil

theorem ttFiber2ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber2Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber2RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber2Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber2ExtractAllLefts_eq_nil

theorem ttFiber12ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber12Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber12RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber12Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber12ExtractAllLefts_eq_nil

theorem ttFiber13ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber13Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber13RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber13Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber13ExtractAllLefts_eq_nil

theorem ttFiber14ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber14Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber14RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber14Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber14ExtractAllLefts_eq_nil

theorem ttFiber15ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber15Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber15RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber15Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber15ExtractAllLefts_eq_nil

theorem ttFiber16ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber16Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber16RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber16Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber16ExtractAllLefts_eq_nil

theorem ttFiber17ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber17Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber17RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber17Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber17ExtractAllLefts_eq_nil

end GoertzelLemma818LengthTwoTTRealAudit

end Mettapedia.GraphTheory.FourColor
