import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTShape16Bridge1
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for small `mirror,normal` length-two fibers, group 1
-/

namespace GoertzelLemma818LengthTwoMTRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMTBridge

theorem mtFiber17ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber17Key allTauStates = mtFiber17DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber17RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber17Key = mtFiber17DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber17Key]
  exact mtFiber17ExtractAllLefts_eq_direct

theorem mtFiber17RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber17Key) = true := by
  rw [mtFiber17RealFiber_eq_direct]
  exact mtFiber17DirectConnected

theorem mtFiber18ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber18Key allTauStates = mtFiber18DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber18RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber18Key = mtFiber18DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber18Key]
  exact mtFiber18ExtractAllLefts_eq_direct

theorem mtFiber18RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber18Key) = true := by
  rw [mtFiber18RealFiber_eq_direct]
  exact mtFiber18DirectConnected

theorem mtFiber22ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber22Key allTauStates = mtFiber22DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber22RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber22Key = mtFiber22DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber22Key]
  exact mtFiber22ExtractAllLefts_eq_direct

theorem mtFiber22RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber22Key) = true := by
  rw [mtFiber22RealFiber_eq_direct]
  exact mtFiber22DirectConnected

theorem mtFiber23ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber23Key allTauStates = mtFiber23DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber23RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber23Key = mtFiber23DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber23Key]
  exact mtFiber23ExtractAllLefts_eq_direct

theorem mtFiber23RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber23Key) = true := by
  rw [mtFiber23RealFiber_eq_direct]
  exact mtFiber23DirectConnected

end GoertzelLemma818LengthTwoMTRealFiberBridge

end Mettapedia.GraphTheory.FourColor
