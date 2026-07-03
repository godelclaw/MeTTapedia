import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMShape8Bridge0
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for small `mirror,mirror` length-two fibers, group 0
-/

namespace GoertzelLemma818LengthTwoMMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMMBridge

theorem mmFiber3ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber3Key allTauStates = mmFiber3DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber3RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber3Key = mmFiber3DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber3Key]
  exact mmFiber3ExtractAllLefts_eq_direct

theorem mmFiber3RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber3Key) = true := by
  rw [mmFiber3RealFiber_eq_direct]
  exact mmFiber3DirectConnected

theorem mmFiber6ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber6Key allTauStates = mmFiber6DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber6RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber6Key = mmFiber6DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber6Key]
  exact mmFiber6ExtractAllLefts_eq_direct

theorem mmFiber6RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber6Key) = true := by
  rw [mmFiber6RealFiber_eq_direct]
  exact mmFiber6DirectConnected

theorem mmFiber9ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber9Key allTauStates = mmFiber9DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber9RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber9Key = mmFiber9DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber9Key]
  exact mmFiber9ExtractAllLefts_eq_direct

theorem mmFiber9RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber9Key) = true := by
  rw [mmFiber9RealFiber_eq_direct]
  exact mmFiber9DirectConnected

theorem mmFiber16ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber16Key allTauStates = mmFiber16DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber16RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber16Key = mmFiber16DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber16Key]
  exact mmFiber16ExtractAllLefts_eq_direct

theorem mmFiber16RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber16Key) = true := by
  rw [mmFiber16RealFiber_eq_direct]
  exact mmFiber16DirectConnected

end GoertzelLemma818LengthTwoMMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
