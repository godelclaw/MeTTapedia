import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealAuditBase

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818LengthTwoMTRealAudit

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMTRealFiberBridge

/-!
# Empty real-fiber checks for `mirror,normal`, group 0
-/

theorem mtFiber0ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber0Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber0RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber0Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber0ExtractAllLefts_eq_nil

theorem mtFiber1ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber1Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber1RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber1Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber1ExtractAllLefts_eq_nil

theorem mtFiber2ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber2Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber2RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber2Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber2ExtractAllLefts_eq_nil

theorem mtFiber5ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber5Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber5RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber5Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber5ExtractAllLefts_eq_nil

theorem mtFiber7ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber7Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber7RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber7Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber7ExtractAllLefts_eq_nil

theorem mtFiber11ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber11Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber11RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber11Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber11ExtractAllLefts_eq_nil

theorem mtFiber12ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber12Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber12RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber12Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber12ExtractAllLefts_eq_nil

theorem mtFiber13ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber13Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber13RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber13Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber13ExtractAllLefts_eq_nil

theorem mtFiber14ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber14Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber14RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber14Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber14ExtractAllLefts_eq_nil

end GoertzelLemma818LengthTwoMTRealAudit

end Mettapedia.GraphTheory.FourColor
