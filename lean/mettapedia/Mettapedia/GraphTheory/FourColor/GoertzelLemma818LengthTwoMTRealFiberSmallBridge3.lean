import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTShape16Bridge3
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for small `mirror,normal` length-two fibers, group 3
-/

namespace GoertzelLemma818LengthTwoMTRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMTBridge

theorem mtFiber43ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber43Key allTauStates = mtFiber43DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber43RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber43Key = mtFiber43DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber43Key]
  exact mtFiber43ExtractAllLefts_eq_direct

theorem mtFiber43RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber43Key) = true := by
  rw [mtFiber43RealFiber_eq_direct]
  exact mtFiber43DirectConnected

theorem mtFiber45ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber45Key allTauStates = mtFiber45DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber45RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber45Key = mtFiber45DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber45Key]
  exact mtFiber45ExtractAllLefts_eq_direct

theorem mtFiber45RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber45Key) = true := by
  rw [mtFiber45RealFiber_eq_direct]
  exact mtFiber45DirectConnected

theorem mtFiber47ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber47Key allTauStates = mtFiber47DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber47RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber47Key = mtFiber47DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber47Key]
  exact mtFiber47ExtractAllLefts_eq_direct

theorem mtFiber47RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber47Key) = true := by
  rw [mtFiber47RealFiber_eq_direct]
  exact mtFiber47DirectConnected

theorem mtFiber49ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber49Key allTauStates = mtFiber49DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber49RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber49Key = mtFiber49DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber49Key]
  exact mtFiber49ExtractAllLefts_eq_direct

theorem mtFiber49RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber49Key) = true := by
  rw [mtFiber49RealFiber_eq_direct]
  exact mtFiber49DirectConnected

end GoertzelLemma818LengthTwoMTRealFiberBridge

end Mettapedia.GraphTheory.FourColor
