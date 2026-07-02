import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMShape16Bridge1
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for size-16 `normal,mirror` length-two fibers, group 1

This generated module identifies four generated direct fiber lists with their
actual `chainFiberFrom tmWord (allChainStates tmWord)` real fibers.
-/

namespace GoertzelLemma818LengthTwoTMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoTMShape16Bridge

theorem tmFiber9ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber9Key allTauStates = tmFiber9DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber9RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber9Key = tmFiber9DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber9Key]
  exact tmFiber9ExtractAllLefts_eq_direct

theorem tmFiber9RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber9Key) = true := by
  rw [tmFiber9RealFiber_eq_direct]
  exact tmFiber9DirectConnected

theorem tmFiber11ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber11Key allTauStates = tmFiber11DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber11RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber11Key = tmFiber11DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber11Key]
  exact tmFiber11ExtractAllLefts_eq_direct

theorem tmFiber11RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber11Key) = true := by
  rw [tmFiber11RealFiber_eq_direct]
  exact tmFiber11DirectConnected

theorem tmFiber18ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber18Key allTauStates = tmFiber18DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber18RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber18Key = tmFiber18DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber18Key]
  exact tmFiber18ExtractAllLefts_eq_direct

theorem tmFiber18RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber18Key) = true := by
  rw [tmFiber18RealFiber_eq_direct]
  exact tmFiber18DirectConnected

theorem tmFiber19ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber19Key allTauStates = tmFiber19DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber19RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber19Key = tmFiber19DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber19Key]
  exact tmFiber19ExtractAllLefts_eq_direct

theorem tmFiber19RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber19Key) = true := by
  rw [tmFiber19RealFiber_eq_direct]
  exact tmFiber19DirectConnected

end GoertzelLemma818LengthTwoTMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
