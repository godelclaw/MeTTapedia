import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTShape16Bridge2
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for small `mirror,normal` length-two fibers, group 2
-/

namespace GoertzelLemma818LengthTwoMTRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMTBridge

theorem mtFiber31ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber31Key allTauStates = mtFiber31DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber31RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber31Key = mtFiber31DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber31Key]
  exact mtFiber31ExtractAllLefts_eq_direct

theorem mtFiber31RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber31Key) = true := by
  rw [mtFiber31RealFiber_eq_direct]
  exact mtFiber31DirectConnected

theorem mtFiber33ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber33Key allTauStates = mtFiber33DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber33RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber33Key = mtFiber33DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber33Key]
  exact mtFiber33ExtractAllLefts_eq_direct

theorem mtFiber33RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber33Key) = true := by
  rw [mtFiber33RealFiber_eq_direct]
  exact mtFiber33DirectConnected

theorem mtFiber35ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber35Key allTauStates = mtFiber35DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber35RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber35Key = mtFiber35DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber35Key]
  exact mtFiber35ExtractAllLefts_eq_direct

theorem mtFiber35RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber35Key) = true := by
  rw [mtFiber35RealFiber_eq_direct]
  exact mtFiber35DirectConnected

theorem mtFiber37ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber37Key allTauStates = mtFiber37DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mtFiber37RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber37Key = mtFiber37DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber37Key]
  exact mtFiber37ExtractAllLefts_eq_direct

theorem mtFiber37RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber37Key) = true := by
  rw [mtFiber37RealFiber_eq_direct]
  exact mtFiber37DirectConnected

end GoertzelLemma818LengthTwoMTRealFiberBridge

end Mettapedia.GraphTheory.FourColor
