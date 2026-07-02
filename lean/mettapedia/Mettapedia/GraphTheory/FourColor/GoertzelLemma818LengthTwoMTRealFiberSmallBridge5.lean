import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTShape16Bridge5
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for small `mirror,normal` length-two fibers, group 5
-/

namespace GoertzelLemma818LengthTwoMTRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMTBridge

theorem mtFiber64ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber64Key allTauStates = mtFiber64DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber64RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber64Key = mtFiber64DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber64Key]
  exact mtFiber64ExtractAllLefts_eq_direct

theorem mtFiber64RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber64Key) = true := by
  rw [mtFiber64RealFiber_eq_direct]
  exact mtFiber64DirectConnected

theorem mtFiber71ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber71Key allTauStates = mtFiber71DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber71RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber71Key = mtFiber71DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber71Key]
  exact mtFiber71ExtractAllLefts_eq_direct

theorem mtFiber71RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber71Key) = true := by
  rw [mtFiber71RealFiber_eq_direct]
  exact mtFiber71DirectConnected

theorem mtFiber74ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber74Key allTauStates = mtFiber74DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber74RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber74Key = mtFiber74DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber74Key]
  exact mtFiber74ExtractAllLefts_eq_direct

theorem mtFiber74RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber74Key) = true := by
  rw [mtFiber74RealFiber_eq_direct]
  exact mtFiber74DirectConnected

theorem mtFiber77ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber77Key allTauStates = mtFiber77DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber77RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber77Key = mtFiber77DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber77Key]
  exact mtFiber77ExtractAllLefts_eq_direct

theorem mtFiber77RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber77Key) = true := by
  rw [mtFiber77RealFiber_eq_direct]
  exact mtFiber77DirectConnected

end GoertzelLemma818LengthTwoMTRealFiberBridge

end Mettapedia.GraphTheory.FourColor
