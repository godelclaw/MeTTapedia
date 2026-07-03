import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealAuditBase

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818LengthTwoMTRealAudit

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMTRealFiberBridge

/-!
# Empty real-fiber checks for `mirror,normal`, group 2
-/

theorem mtFiber32ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber32Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber32RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber32Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber32ExtractAllLefts_eq_nil

theorem mtFiber34ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber34Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber34RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber34Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber34ExtractAllLefts_eq_nil

theorem mtFiber38ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber38Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber38RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber38Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber38ExtractAllLefts_eq_nil

theorem mtFiber39ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber39Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber39RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber39Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber39ExtractAllLefts_eq_nil

theorem mtFiber40ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber40Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber40RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber40Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber40ExtractAllLefts_eq_nil

theorem mtFiber41ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber41Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber41RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber41Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber41ExtractAllLefts_eq_nil

theorem mtFiber42ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber42Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber42RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber42Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber42ExtractAllLefts_eq_nil

theorem mtFiber46ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber46Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber46RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber46Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber46ExtractAllLefts_eq_nil

theorem mtFiber48ExtractAllLefts_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber48Key allTauStates = [] := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber48RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber48Key) = true := by
  exact mtEmptyFiberConnected_of_extract_nil mtFiber48ExtractAllLefts_eq_nil

end GoertzelLemma818LengthTwoMTRealAudit

end Mettapedia.GraphTheory.FourColor
