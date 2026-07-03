import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTTRealAuditBase

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818LengthTwoTTRealAudit

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype

/-!
# Empty `tau,tau` length-two fibers, group 1

This generated module proves that its assigned fixed-input fibers extract to the
empty real fiber, then packages each as a `chainFiberConnected` theorem.
-/

theorem ttFiber21ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber21Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber21RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber21Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber21ExtractAllLefts_eq_nil

theorem ttFiber22ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber22Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber22RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber22Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber22ExtractAllLefts_eq_nil

theorem ttFiber23ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber23Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber23RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber23Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber23ExtractAllLefts_eq_nil

theorem ttFiber24ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber24Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber24RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber24Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber24ExtractAllLefts_eq_nil

theorem ttFiber25ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber25Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber25RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber25Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber25ExtractAllLefts_eq_nil

theorem ttFiber26ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber26Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber26RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber26Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber26ExtractAllLefts_eq_nil

theorem ttFiber27ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber27Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber27RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber27Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber27ExtractAllLefts_eq_nil

theorem ttFiber28ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber28Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber28RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber28Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber28ExtractAllLefts_eq_nil

theorem ttFiber29ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber29Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem ttFiber29RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber29Key) = true := by
  exact ttEmptyFiberConnected_of_extract_nil ttFiber29ExtractAllLefts_eq_nil

end GoertzelLemma818LengthTwoTTRealAudit

end Mettapedia.GraphTheory.FourColor
