import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMShape8Bridge2
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for small `mirror,mirror` length-two fibers, group 2
-/

namespace GoertzelLemma818LengthTwoMMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMMBridge

theorem mmFiber31ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber31Key allTauStates = mmFiber31DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber31RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber31Key = mmFiber31DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber31Key]
  exact mmFiber31ExtractAllLefts_eq_direct

theorem mmFiber31RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber31Key) = true := by
  rw [mmFiber31RealFiber_eq_direct]
  exact mmFiber31DirectConnected

theorem mmFiber33ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber33Key allTauStates = mmFiber33DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber33RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber33Key = mmFiber33DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber33Key]
  exact mmFiber33ExtractAllLefts_eq_direct

theorem mmFiber33RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber33Key) = true := by
  rw [mmFiber33RealFiber_eq_direct]
  exact mmFiber33DirectConnected

theorem mmFiber35ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber35Key allTauStates = mmFiber35DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber35RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber35Key = mmFiber35DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber35Key]
  exact mmFiber35ExtractAllLefts_eq_direct

theorem mmFiber35RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber35Key) = true := by
  rw [mmFiber35RealFiber_eq_direct]
  exact mmFiber35DirectConnected

theorem mmFiber37ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber37Key allTauStates = mmFiber37DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem mmFiber37RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber37Key = mmFiber37DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber37Key]
  exact mmFiber37ExtractAllLefts_eq_direct

theorem mmFiber37RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber37Key) = true := by
  rw [mmFiber37RealFiber_eq_direct]
  exact mmFiber37DirectConnected

end GoertzelLemma818LengthTwoMMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
