import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTTRealAuditBase

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818LengthTwoTTRealAudit

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype

/-!
# Empty `tau,tau` length-two fibers, group 2

This generated module proves that its assigned fixed-input fibers extract to the
empty real fiber, then packages each as a `chainFiberConnected` theorem.
-/

theorem ttFiber33ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber33Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber33RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber33Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber33ExtractAllLefts_eq_nil

theorem ttFiber34ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber34Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber34RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber34Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber34ExtractAllLefts_eq_nil

theorem ttFiber35ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber35Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber35RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber35Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber35ExtractAllLefts_eq_nil

theorem ttFiber39ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber39Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber39RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber39Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber39ExtractAllLefts_eq_nil

theorem ttFiber40ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber40Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber40RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber40Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber40ExtractAllLefts_eq_nil

theorem ttFiber41ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber41Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber41RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber41Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber41ExtractAllLefts_eq_nil

theorem ttFiber45ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber45Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber45RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber45Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber45ExtractAllLefts_eq_nil

theorem ttFiber46ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber46Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber46RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber46Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber46ExtractAllLefts_eq_nil

theorem ttFiber47ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber47Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber47RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber47Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber47ExtractAllLefts_eq_nil

end GoertzelLemma818LengthTwoTTRealAudit

end Mettapedia.GraphTheory.FourColor
