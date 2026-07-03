import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTShape16Bridge4
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for small `mirror,normal` length-two fibers, group 4
-/

namespace GoertzelLemma818LengthTwoMTRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMTBridge

theorem mtFiber57ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber57Key allTauStates = mtFiber57DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber57RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber57Key = mtFiber57DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber57Key]
  exact mtFiber57ExtractAllLefts_eq_direct

theorem mtFiber57RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber57Key) = true := by
  rw [mtFiber57RealFiber_eq_direct]
  exact mtFiber57DirectConnected

theorem mtFiber58ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber58Key allTauStates = mtFiber58DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber58RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber58Key = mtFiber58DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber58Key]
  exact mtFiber58ExtractAllLefts_eq_direct

theorem mtFiber58RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber58Key) = true := by
  rw [mtFiber58RealFiber_eq_direct]
  exact mtFiber58DirectConnected

theorem mtFiber62ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber62Key allTauStates = mtFiber62DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber62RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber62Key = mtFiber62DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber62Key]
  exact mtFiber62ExtractAllLefts_eq_direct

theorem mtFiber62RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber62Key) = true := by
  rw [mtFiber62RealFiber_eq_direct]
  exact mtFiber62DirectConnected

theorem mtFiber63ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber63Key allTauStates = mtFiber63DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber63RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber63Key = mtFiber63DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber63Key]
  exact mtFiber63ExtractAllLefts_eq_direct

theorem mtFiber63RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber63Key) = true := by
  rw [mtFiber63RealFiber_eq_direct]
  exact mtFiber63DirectConnected

end GoertzelLemma818LengthTwoMTRealFiberBridge

end Mettapedia.GraphTheory.FourColor
