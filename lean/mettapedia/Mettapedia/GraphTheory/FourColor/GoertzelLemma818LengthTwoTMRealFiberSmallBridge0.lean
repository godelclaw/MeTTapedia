import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMShape16Bridge0
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for size-16 `normal,mirror` length-two fibers, group 0

This generated module identifies four generated direct fiber lists with their
actual `chainFiberFrom tmWord (allChainStates tmWord)` real fibers.
-/

namespace GoertzelLemma818LengthTwoTMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoTMShape16Bridge

theorem tmFiber3ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber3Key allTauStates = tmFiber3DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber3RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber3Key = tmFiber3DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber3Key]
  exact tmFiber3ExtractAllLefts_eq_direct

theorem tmFiber3RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber3Key) = true := by
  rw [tmFiber3RealFiber_eq_direct]
  exact tmFiber3DirectConnected

theorem tmFiber5ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber5Key allTauStates = tmFiber5DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber5RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber5Key = tmFiber5DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber5Key]
  exact tmFiber5ExtractAllLefts_eq_direct

theorem tmFiber5RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber5Key) = true := by
  rw [tmFiber5RealFiber_eq_direct]
  exact tmFiber5DirectConnected

theorem tmFiber6ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber6Key allTauStates = tmFiber6DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber6RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber6Key = tmFiber6DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber6Key]
  exact tmFiber6ExtractAllLefts_eq_direct

theorem tmFiber6RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber6Key) = true := by
  rw [tmFiber6RealFiber_eq_direct]
  exact tmFiber6DirectConnected

theorem tmFiber7ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber7Key allTauStates = tmFiber7DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber7RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber7Key = tmFiber7DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber7Key]
  exact tmFiber7ExtractAllLefts_eq_direct

theorem tmFiber7RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber7Key) = true := by
  rw [tmFiber7RealFiber_eq_direct]
  exact tmFiber7DirectConnected

end GoertzelLemma818LengthTwoTMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
