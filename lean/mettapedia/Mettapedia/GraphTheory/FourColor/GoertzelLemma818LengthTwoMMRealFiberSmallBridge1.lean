import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMShape8Bridge1
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for small `mirror,mirror` length-two fibers, group 1
-/

namespace GoertzelLemma818LengthTwoMMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMMBridge

theorem mmFiber17ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber17Key allTauStates = mmFiber17DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber17RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber17Key = mmFiber17DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber17Key]
  exact mmFiber17ExtractAllLefts_eq_direct

theorem mmFiber17RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber17Key) = true := by
  rw [mmFiber17RealFiber_eq_direct]
  exact mmFiber17DirectConnected

theorem mmFiber18ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber18Key allTauStates = mmFiber18DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber18RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber18Key = mmFiber18DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber18Key]
  exact mmFiber18ExtractAllLefts_eq_direct

theorem mmFiber18RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber18Key) = true := by
  rw [mmFiber18RealFiber_eq_direct]
  exact mmFiber18DirectConnected

theorem mmFiber22ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber22Key allTauStates = mmFiber22DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber22RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber22Key = mmFiber22DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber22Key]
  exact mmFiber22ExtractAllLefts_eq_direct

theorem mmFiber22RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber22Key) = true := by
  rw [mmFiber22RealFiber_eq_direct]
  exact mmFiber22DirectConnected

theorem mmFiber23ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber23Key allTauStates = mmFiber23DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber23RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber23Key = mmFiber23DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber23Key]
  exact mmFiber23ExtractAllLefts_eq_direct

theorem mmFiber23RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber23Key) = true := by
  rw [mmFiber23RealFiber_eq_direct]
  exact mmFiber23DirectConnected

end GoertzelLemma818LengthTwoMMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
