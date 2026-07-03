import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiber30Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiber36Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiber60Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiber72Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for one-pass size-64 `normal,mirror` length-two fibers

This generated module identifies four generated direct fiber lists with their
actual `chainFiberFrom tmWord (allChainStates tmWord)` real fibers, using
per-left-chunk extraction lemmas to stay within default recursion limits.
-/

namespace GoertzelLemma818LengthTwoTMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoTMLargeFiberBridge

theorem tmFiber30ExtractLeftChunk_0_eq_take :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber30Key (tauStateChunk32 0) =
      tmFiber30DirectStates.take 32 := by
  decide

theorem tmFiber30ExtractLeftChunk_32_eq_drop :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber30Key (tauStateChunk32 32) =
      tmFiber30DirectStates.drop 32 := by
  decide

theorem tmFiber30ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber30Key (tauStateChunk32 64) = [] := by
  decide

theorem tmFiber30ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber30Key (tauStateChunk32 96) = [] := by
  decide

theorem tmFiber30ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber30Key (tauStateChunk32 128) = [] := by
  decide

theorem tmFiber30ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber30Key (tauStateChunk32 160) = [] := by
  decide

theorem tmFiber30ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber30Key tauStateTail192 = [] := by
  decide

theorem tmFiber30ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber30Key allTauStates = tmFiber30DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [tmFiber30ExtractLeftChunk_0_eq_take,
    tmFiber30ExtractLeftChunk_32_eq_drop,
    tmFiber30ExtractLeftChunk_64_eq_nil,
    tmFiber30ExtractLeftChunk_96_eq_nil,
    tmFiber30ExtractLeftChunk_128_eq_nil,
    tmFiber30ExtractLeftChunk_160_eq_nil,
    tmFiber30ExtractLeftTail_eq_nil]
  simp

theorem tmFiber30RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber30Key = tmFiber30DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber30Key]
  exact tmFiber30ExtractAllLefts_eq_direct

theorem tmFiber30RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber30Key) = true := by
  rw [tmFiber30RealFiber_eq_direct]
  exact tmFiber30DirectConnected

theorem tmFiber36ExtractLeftChunk_0_eq_take :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber36Key (tauStateChunk32 0) =
      tmFiber36DirectStates.take 32 := by
  decide

theorem tmFiber36ExtractLeftChunk_32_eq_drop :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber36Key (tauStateChunk32 32) =
      tmFiber36DirectStates.drop 32 := by
  decide

theorem tmFiber36ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber36Key (tauStateChunk32 64) = [] := by
  decide

theorem tmFiber36ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber36Key (tauStateChunk32 96) = [] := by
  decide

theorem tmFiber36ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber36Key (tauStateChunk32 128) = [] := by
  decide

theorem tmFiber36ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber36Key (tauStateChunk32 160) = [] := by
  decide

theorem tmFiber36ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber36Key tauStateTail192 = [] := by
  decide

theorem tmFiber36ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber36Key allTauStates = tmFiber36DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [tmFiber36ExtractLeftChunk_0_eq_take,
    tmFiber36ExtractLeftChunk_32_eq_drop,
    tmFiber36ExtractLeftChunk_64_eq_nil,
    tmFiber36ExtractLeftChunk_96_eq_nil,
    tmFiber36ExtractLeftChunk_128_eq_nil,
    tmFiber36ExtractLeftChunk_160_eq_nil,
    tmFiber36ExtractLeftTail_eq_nil]
  simp

theorem tmFiber36RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber36Key = tmFiber36DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber36Key]
  exact tmFiber36ExtractAllLefts_eq_direct

theorem tmFiber36RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber36Key) = true := by
  rw [tmFiber36RealFiber_eq_direct]
  exact tmFiber36DirectConnected

theorem tmFiber60ExtractLeftChunk_0_eq_take :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber60Key (tauStateChunk32 0) =
      tmFiber60DirectStates.take 32 := by
  decide

theorem tmFiber60ExtractLeftChunk_32_eq_drop :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber60Key (tauStateChunk32 32) =
      tmFiber60DirectStates.drop 32 := by
  decide

theorem tmFiber60ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber60Key (tauStateChunk32 64) = [] := by
  decide

theorem tmFiber60ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber60Key (tauStateChunk32 96) = [] := by
  decide

theorem tmFiber60ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber60Key (tauStateChunk32 128) = [] := by
  decide

theorem tmFiber60ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber60Key (tauStateChunk32 160) = [] := by
  decide

theorem tmFiber60ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber60Key tauStateTail192 = [] := by
  decide

theorem tmFiber60ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber60Key allTauStates = tmFiber60DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [tmFiber60ExtractLeftChunk_0_eq_take,
    tmFiber60ExtractLeftChunk_32_eq_drop,
    tmFiber60ExtractLeftChunk_64_eq_nil,
    tmFiber60ExtractLeftChunk_96_eq_nil,
    tmFiber60ExtractLeftChunk_128_eq_nil,
    tmFiber60ExtractLeftChunk_160_eq_nil,
    tmFiber60ExtractLeftTail_eq_nil]
  simp

theorem tmFiber60RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber60Key = tmFiber60DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber60Key]
  exact tmFiber60ExtractAllLefts_eq_direct

theorem tmFiber60RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber60Key) = true := by
  rw [tmFiber60RealFiber_eq_direct]
  exact tmFiber60DirectConnected

theorem tmFiber72ExtractLeftChunk_0_eq_take :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber72Key (tauStateChunk32 0) =
      tmFiber72DirectStates.take 32 := by
  decide

theorem tmFiber72ExtractLeftChunk_32_eq_drop :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber72Key (tauStateChunk32 32) =
      tmFiber72DirectStates.drop 32 := by
  decide

theorem tmFiber72ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber72Key (tauStateChunk32 64) = [] := by
  decide

theorem tmFiber72ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber72Key (tauStateChunk32 96) = [] := by
  decide

theorem tmFiber72ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber72Key (tauStateChunk32 128) = [] := by
  decide

theorem tmFiber72ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber72Key (tauStateChunk32 160) = [] := by
  decide

theorem tmFiber72ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber72Key tauStateTail192 = [] := by
  decide

theorem tmFiber72ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber72Key allTauStates = tmFiber72DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [tmFiber72ExtractLeftChunk_0_eq_take,
    tmFiber72ExtractLeftChunk_32_eq_drop,
    tmFiber72ExtractLeftChunk_64_eq_nil,
    tmFiber72ExtractLeftChunk_96_eq_nil,
    tmFiber72ExtractLeftChunk_128_eq_nil,
    tmFiber72ExtractLeftChunk_160_eq_nil,
    tmFiber72ExtractLeftTail_eq_nil]
  simp

theorem tmFiber72RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber72Key = tmFiber72DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber72Key]
  exact tmFiber72ExtractAllLefts_eq_direct

theorem tmFiber72RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber72Key) = true := by
  rw [tmFiber72RealFiber_eq_direct]
  exact tmFiber72DirectConnected

end GoertzelLemma818LengthTwoTMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
