import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMShape16Bridge2
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for size-16 `normal,mirror` length-two fibers, group 2

This generated module identifies four generated direct fiber lists with their
actual `chainFiberFrom tmWord (allChainStates tmWord)` real fibers.
-/

namespace GoertzelLemma818LengthTwoTMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoTMShape16Bridge

theorem tmFiber31ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber31Key allTauStates = tmFiber31DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber31RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber31Key = tmFiber31DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber31Key]
  exact tmFiber31ExtractAllLefts_eq_direct

theorem tmFiber31RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber31Key) = true := by
  rw [tmFiber31RealFiber_eq_direct]
  exact tmFiber31DirectConnected

theorem tmFiber32ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber32Key allTauStates = tmFiber32DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber32RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber32Key = tmFiber32DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber32Key]
  exact tmFiber32ExtractAllLefts_eq_direct

theorem tmFiber32RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber32Key) = true := by
  rw [tmFiber32RealFiber_eq_direct]
  exact tmFiber32DirectConnected

theorem tmFiber37ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber37Key allTauStates = tmFiber37DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber37RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber37Key = tmFiber37DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber37Key]
  exact tmFiber37ExtractAllLefts_eq_direct

theorem tmFiber37RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber37Key) = true := by
  rw [tmFiber37RealFiber_eq_direct]
  exact tmFiber37DirectConnected

theorem tmFiber38ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber38Key allTauStates = tmFiber38DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber38RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber38Key = tmFiber38DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber38Key]
  exact tmFiber38ExtractAllLefts_eq_direct

theorem tmFiber38RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber38Key) = true := by
  rw [tmFiber38RealFiber_eq_direct]
  exact tmFiber38DirectConnected

end GoertzelLemma818LengthTwoTMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
