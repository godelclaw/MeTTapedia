import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMShape8Bridge4
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for small `mirror,mirror` length-two fibers, group 4
-/

namespace GoertzelLemma818LengthTwoMMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMMBridge

theorem mmFiber57ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber57Key allTauStates = mmFiber57DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber57RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber57Key = mmFiber57DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber57Key]
  exact mmFiber57ExtractAllLefts_eq_direct

theorem mmFiber57RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber57Key) = true := by
  rw [mmFiber57RealFiber_eq_direct]
  exact mmFiber57DirectConnected

theorem mmFiber58ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber58Key allTauStates = mmFiber58DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber58RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber58Key = mmFiber58DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber58Key]
  exact mmFiber58ExtractAllLefts_eq_direct

theorem mmFiber58RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber58Key) = true := by
  rw [mmFiber58RealFiber_eq_direct]
  exact mmFiber58DirectConnected

theorem mmFiber62ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber62Key allTauStates = mmFiber62DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber62RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber62Key = mmFiber62DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber62Key]
  exact mmFiber62ExtractAllLefts_eq_direct

theorem mmFiber62RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber62Key) = true := by
  rw [mmFiber62RealFiber_eq_direct]
  exact mmFiber62DirectConnected

theorem mmFiber63ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber63Key allTauStates = mmFiber63DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber63RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber63Key = mmFiber63DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber63Key]
  exact mmFiber63ExtractAllLefts_eq_direct

theorem mmFiber63RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber63Key) = true := by
  rw [mmFiber63RealFiber_eq_direct]
  exact mmFiber63DirectConnected

end GoertzelLemma818LengthTwoMMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
