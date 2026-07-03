import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMShape8Bridge3
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for small `mirror,mirror` length-two fibers, group 3
-/

namespace GoertzelLemma818LengthTwoMMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMMBridge

theorem mmFiber43ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber43Key allTauStates = mmFiber43DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber43RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber43Key = mmFiber43DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber43Key]
  exact mmFiber43ExtractAllLefts_eq_direct

theorem mmFiber43RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber43Key) = true := by
  rw [mmFiber43RealFiber_eq_direct]
  exact mmFiber43DirectConnected

theorem mmFiber45ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber45Key allTauStates = mmFiber45DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber45RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber45Key = mmFiber45DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber45Key]
  exact mmFiber45ExtractAllLefts_eq_direct

theorem mmFiber45RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber45Key) = true := by
  rw [mmFiber45RealFiber_eq_direct]
  exact mmFiber45DirectConnected

theorem mmFiber47ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber47Key allTauStates = mmFiber47DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber47RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber47Key = mmFiber47DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber47Key]
  exact mmFiber47ExtractAllLefts_eq_direct

theorem mmFiber47RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber47Key) = true := by
  rw [mmFiber47RealFiber_eq_direct]
  exact mmFiber47DirectConnected

theorem mmFiber49ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber49Key allTauStates = mmFiber49DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber49RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber49Key = mmFiber49DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber49Key]
  exact mmFiber49ExtractAllLefts_eq_direct

theorem mmFiber49RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber49Key) = true := by
  rw [mmFiber49RealFiber_eq_direct]
  exact mmFiber49DirectConnected

end GoertzelLemma818LengthTwoMMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
