import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTShape16Bridge0
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for small `mirror,normal` length-two fibers, group 0
-/

namespace GoertzelLemma818LengthTwoMTRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMTBridge

theorem mtFiber3ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber3Key allTauStates = mtFiber3DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber3RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber3Key = mtFiber3DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber3Key]
  exact mtFiber3ExtractAllLefts_eq_direct

theorem mtFiber3RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber3Key) = true := by
  rw [mtFiber3RealFiber_eq_direct]
  exact mtFiber3DirectConnected

theorem mtFiber6ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber6Key allTauStates = mtFiber6DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber6RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber6Key = mtFiber6DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber6Key]
  exact mtFiber6ExtractAllLefts_eq_direct

theorem mtFiber6RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber6Key) = true := by
  rw [mtFiber6RealFiber_eq_direct]
  exact mtFiber6DirectConnected

theorem mtFiber9ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber9Key allTauStates = mtFiber9DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber9RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber9Key = mtFiber9DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber9Key]
  exact mtFiber9ExtractAllLefts_eq_direct

theorem mtFiber9RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber9Key) = true := by
  rw [mtFiber9RealFiber_eq_direct]
  exact mtFiber9DirectConnected

theorem mtFiber16ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber16Key allTauStates = mtFiber16DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber16RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber16Key = mtFiber16DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber16Key]
  exact mtFiber16ExtractAllLefts_eq_direct

theorem mtFiber16RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber16Key) = true := by
  rw [mtFiber16RealFiber_eq_direct]
  exact mtFiber16DirectConnected

end GoertzelLemma818LengthTwoMTRealFiberBridge

end Mettapedia.GraphTheory.FourColor
