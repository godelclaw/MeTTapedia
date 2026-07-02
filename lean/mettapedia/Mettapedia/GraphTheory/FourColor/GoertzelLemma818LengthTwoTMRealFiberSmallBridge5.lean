import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMShape16Bridge5
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for size-16 `normal,mirror` length-two fibers, group 5

This generated module identifies four generated direct fiber lists with their
actual `chainFiberFrom tmWord (allChainStates tmWord)` real fibers.
-/

namespace GoertzelLemma818LengthTwoTMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoTMShape16Bridge

theorem tmFiber73ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber73Key allTauStates = tmFiber73DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber73RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber73Key = tmFiber73DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber73Key]
  exact tmFiber73ExtractAllLefts_eq_direct

theorem tmFiber73RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber73Key) = true := by
  rw [tmFiber73RealFiber_eq_direct]
  exact tmFiber73DirectConnected

theorem tmFiber74ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber74Key allTauStates = tmFiber74DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber74RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber74Key = tmFiber74DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber74Key]
  exact tmFiber74ExtractAllLefts_eq_direct

theorem tmFiber74RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber74Key) = true := by
  rw [tmFiber74RealFiber_eq_direct]
  exact tmFiber74DirectConnected

theorem tmFiber75ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber75Key allTauStates = tmFiber75DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber75RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber75Key = tmFiber75DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber75Key]
  exact tmFiber75ExtractAllLefts_eq_direct

theorem tmFiber75RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber75Key) = true := by
  rw [tmFiber75RealFiber_eq_direct]
  exact tmFiber75DirectConnected

theorem tmFiber77ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber77Key allTauStates = tmFiber77DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber77RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber77Key = tmFiber77DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber77Key]
  exact tmFiber77ExtractAllLefts_eq_direct

theorem tmFiber77RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber77Key) = true := by
  rw [tmFiber77RealFiber_eq_direct]
  exact tmFiber77DirectConnected

end GoertzelLemma818LengthTwoTMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
