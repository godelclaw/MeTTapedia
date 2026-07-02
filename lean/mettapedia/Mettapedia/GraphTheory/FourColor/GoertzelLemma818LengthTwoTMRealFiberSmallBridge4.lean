import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMShape16Bridge4
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for size-16 `normal,mirror` length-two fibers, group 4

This generated module identifies four generated direct fiber lists with their
actual `chainFiberFrom tmWord (allChainStates tmWord)` real fibers.
-/

namespace GoertzelLemma818LengthTwoTMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoTMShape16Bridge

theorem tmFiber61ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber61Key allTauStates = tmFiber61DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber61RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber61Key = tmFiber61DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber61Key]
  exact tmFiber61ExtractAllLefts_eq_direct

theorem tmFiber61RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber61Key) = true := by
  rw [tmFiber61RealFiber_eq_direct]
  exact tmFiber61DirectConnected

theorem tmFiber62ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber62Key allTauStates = tmFiber62DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber62RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber62Key = tmFiber62DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber62Key]
  exact tmFiber62ExtractAllLefts_eq_direct

theorem tmFiber62RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber62Key) = true := by
  rw [tmFiber62RealFiber_eq_direct]
  exact tmFiber62DirectConnected

theorem tmFiber69ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber69Key allTauStates = tmFiber69DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber69RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber69Key = tmFiber69DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber69Key]
  exact tmFiber69ExtractAllLefts_eq_direct

theorem tmFiber69RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber69Key) = true := by
  rw [tmFiber69RealFiber_eq_direct]
  exact tmFiber69DirectConnected

theorem tmFiber71ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber71Key allTauStates = tmFiber71DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber71RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber71Key = tmFiber71DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber71Key]
  exact tmFiber71ExtractAllLefts_eq_direct

theorem tmFiber71RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber71Key) = true := by
  rw [tmFiber71RealFiber_eq_direct]
  exact tmFiber71DirectConnected

end GoertzelLemma818LengthTwoTMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
