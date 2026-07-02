import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMShape16Bridge3
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for size-16 `normal,mirror` length-two fibers, group 3

This generated module identifies four generated direct fiber lists with their
actual `chainFiberFrom tmWord (allChainStates tmWord)` real fibers.
-/

namespace GoertzelLemma818LengthTwoTMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoTMShape16Bridge

theorem tmFiber42ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber42Key allTauStates = tmFiber42DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber42RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber42Key = tmFiber42DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber42Key]
  exact tmFiber42ExtractAllLefts_eq_direct

theorem tmFiber42RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber42Key) = true := by
  rw [tmFiber42RealFiber_eq_direct]
  exact tmFiber42DirectConnected

theorem tmFiber43ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber43Key allTauStates = tmFiber43DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber43RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber43Key = tmFiber43DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber43Key]
  exact tmFiber43ExtractAllLefts_eq_direct

theorem tmFiber43RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber43Key) = true := by
  rw [tmFiber43RealFiber_eq_direct]
  exact tmFiber43DirectConnected

theorem tmFiber48ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber48Key allTauStates = tmFiber48DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber48RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber48Key = tmFiber48DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber48Key]
  exact tmFiber48ExtractAllLefts_eq_direct

theorem tmFiber48RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber48Key) = true := by
  rw [tmFiber48RealFiber_eq_direct]
  exact tmFiber48DirectConnected

theorem tmFiber49ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber49Key allTauStates = tmFiber49DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  decide

theorem tmFiber49RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber49Key = tmFiber49DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber49Key]
  exact tmFiber49ExtractAllLefts_eq_direct

theorem tmFiber49RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber49Key) = true := by
  rw [tmFiber49RealFiber_eq_direct]
  exact tmFiber49DirectConnected

end GoertzelLemma818LengthTwoTMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
