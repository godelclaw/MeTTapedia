import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMShape8Bridge5
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for small `mirror,mirror` length-two fibers, group 5
-/

namespace GoertzelLemma818LengthTwoMMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMMBridge

theorem mmFiber64ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber64Key allTauStates = mmFiber64DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber64RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber64Key = mmFiber64DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber64Key]
  exact mmFiber64ExtractAllLefts_eq_direct

theorem mmFiber64RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber64Key) = true := by
  rw [mmFiber64RealFiber_eq_direct]
  exact mmFiber64DirectConnected

theorem mmFiber71ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber71Key allTauStates = mmFiber71DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber71RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber71Key = mmFiber71DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber71Key]
  exact mmFiber71ExtractAllLefts_eq_direct

theorem mmFiber71RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber71Key) = true := by
  rw [mmFiber71RealFiber_eq_direct]
  exact mmFiber71DirectConnected

theorem mmFiber74ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber74Key allTauStates = mmFiber74DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber74RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber74Key = mmFiber74DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber74Key]
  exact mmFiber74ExtractAllLefts_eq_direct

theorem mmFiber74RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber74Key) = true := by
  rw [mmFiber74RealFiber_eq_direct]
  exact mmFiber74DirectConnected

theorem mmFiber77ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber77Key allTauStates = mmFiber77DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber77RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber77Key = mmFiber77DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber77Key]
  exact mmFiber77ExtractAllLefts_eq_direct

theorem mmFiber77RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber77Key) = true := by
  rw [mmFiber77RealFiber_eq_direct]
  exact mmFiber77DirectConnected

end GoertzelLemma818LengthTwoMMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
