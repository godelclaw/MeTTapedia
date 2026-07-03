import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTTRealAuditBase

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818LengthTwoTTRealAudit

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype

/-!
# Empty `tau,tau` length-two fibers, group 4

This generated module proves that its assigned fixed-input fibers extract to the
empty real fiber, then packages each as a `chainFiberConnected` theorem.
-/

theorem ttFiber63ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber63Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber63RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber63Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber63ExtractAllLefts_eq_nil

theorem ttFiber64ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber64Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber64RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber64Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber64ExtractAllLefts_eq_nil

theorem ttFiber65ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber65Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber65RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber65Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber65ExtractAllLefts_eq_nil

theorem ttFiber66ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber66Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber66RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber66Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber66ExtractAllLefts_eq_nil

theorem ttFiber67ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber67Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber67RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber67Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber67ExtractAllLefts_eq_nil

theorem ttFiber68ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber68Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber68RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber68Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber68ExtractAllLefts_eq_nil

theorem ttFiber78ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber78Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber78RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber78Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber78ExtractAllLefts_eq_nil

theorem ttFiber79ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber79Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber79RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber79Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber79ExtractAllLefts_eq_nil

theorem ttFiber80ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber80Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber80RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber80Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber80ExtractAllLefts_eq_nil

end GoertzelLemma818LengthTwoTTRealAudit

end Mettapedia.GraphTheory.FourColor
