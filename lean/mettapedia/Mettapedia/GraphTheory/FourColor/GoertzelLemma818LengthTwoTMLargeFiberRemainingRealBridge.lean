import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiber4Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiber8Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiber10Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiber20Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiber44Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiber50Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiber70Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiber76Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for remaining size-64 `normal,mirror` length-two fibers

This generated module identifies the generated direct fiber lists for the
remaining eight size-64 fibers with their actual real fibers.
-/

namespace GoertzelLemma818LengthTwoTMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoTMLargeFiberBridge

theorem tmFiber4ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber4Key (tauStateChunk32 0) =
      [] := by
  decide

theorem tmFiber4ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber4Key (tauStateChunk32 32) =
      [] := by
  decide

theorem tmFiber4ExtractLeftChunk_64_eq_take :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber4Key (tauStateChunk32 64) =
      tmFiber4DirectStates.take 32 := by
  decide

theorem tmFiber4ExtractLeftChunk_96_eq_drop :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber4Key (tauStateChunk32 96) =
      tmFiber4DirectStates.drop 32 := by
  decide

theorem tmFiber4ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber4Key (tauStateChunk32 128) =
      [] := by
  decide

theorem tmFiber4ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber4Key (tauStateChunk32 160) =
      [] := by
  decide

theorem tmFiber4ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber4Key tauStateTail192 = [] := by
  decide

theorem tmFiber4ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber4Key allTauStates = tmFiber4DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [tmFiber4ExtractLeftChunk_0_eq_nil,
    tmFiber4ExtractLeftChunk_32_eq_nil,
    tmFiber4ExtractLeftChunk_64_eq_take,
    tmFiber4ExtractLeftChunk_96_eq_drop,
    tmFiber4ExtractLeftChunk_128_eq_nil,
    tmFiber4ExtractLeftChunk_160_eq_nil,
    tmFiber4ExtractLeftTail_eq_nil]
  simp

theorem tmFiber4RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber4Key = tmFiber4DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber4Key]
  exact tmFiber4ExtractAllLefts_eq_direct

theorem tmFiber4RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber4Key) = true := by
  rw [tmFiber4RealFiber_eq_direct]
  exact tmFiber4DirectConnected

theorem tmFiber8ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber8Key (tauStateChunk32 0) =
      [] := by
  decide

theorem tmFiber8ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber8Key (tauStateChunk32 32) =
      [] := by
  decide

theorem tmFiber8ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber8Key (tauStateChunk32 64) =
      [] := by
  decide

theorem tmFiber8ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber8Key (tauStateChunk32 96) =
      [] := by
  decide

theorem tmFiber8ExtractLeftChunk_128_eq_take :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber8Key (tauStateChunk32 128) =
      tmFiber8DirectStates.take 32 := by
  decide

theorem tmFiber8ExtractLeftChunk_160_eq_drop :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber8Key (tauStateChunk32 160) =
      tmFiber8DirectStates.drop 32 := by
  decide

theorem tmFiber8ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber8Key tauStateTail192 = [] := by
  decide

theorem tmFiber8ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber8Key allTauStates = tmFiber8DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [tmFiber8ExtractLeftChunk_0_eq_nil,
    tmFiber8ExtractLeftChunk_32_eq_nil,
    tmFiber8ExtractLeftChunk_64_eq_nil,
    tmFiber8ExtractLeftChunk_96_eq_nil,
    tmFiber8ExtractLeftChunk_128_eq_take,
    tmFiber8ExtractLeftChunk_160_eq_drop,
    tmFiber8ExtractLeftTail_eq_nil]
  simp

theorem tmFiber8RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber8Key = tmFiber8DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber8Key]
  exact tmFiber8ExtractAllLefts_eq_direct

theorem tmFiber8RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber8Key) = true := by
  rw [tmFiber8RealFiber_eq_direct]
  exact tmFiber8DirectConnected

theorem tmFiber10ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber10Key (tauStateChunk32 0) =
      [] := by
  decide

theorem tmFiber10ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber10Key (tauStateChunk32 32) =
      [] := by
  decide

theorem tmFiber10ExtractLeftChunk_64_eq_take :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber10Key (tauStateChunk32 64) =
      tmFiber10DirectStates.take 32 := by
  decide

theorem tmFiber10ExtractLeftChunk_96_eq_drop :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber10Key (tauStateChunk32 96) =
      tmFiber10DirectStates.drop 32 := by
  decide

theorem tmFiber10ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber10Key (tauStateChunk32 128) =
      [] := by
  decide

theorem tmFiber10ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber10Key (tauStateChunk32 160) =
      [] := by
  decide

theorem tmFiber10ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber10Key tauStateTail192 = [] := by
  decide

theorem tmFiber10ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber10Key allTauStates = tmFiber10DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [tmFiber10ExtractLeftChunk_0_eq_nil,
    tmFiber10ExtractLeftChunk_32_eq_nil,
    tmFiber10ExtractLeftChunk_64_eq_take,
    tmFiber10ExtractLeftChunk_96_eq_drop,
    tmFiber10ExtractLeftChunk_128_eq_nil,
    tmFiber10ExtractLeftChunk_160_eq_nil,
    tmFiber10ExtractLeftTail_eq_nil]
  simp

theorem tmFiber10RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber10Key = tmFiber10DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber10Key]
  exact tmFiber10ExtractAllLefts_eq_direct

theorem tmFiber10RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber10Key) = true := by
  rw [tmFiber10RealFiber_eq_direct]
  exact tmFiber10DirectConnected

theorem tmFiber20ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber20Key (tauStateChunk32 0) =
      [] := by
  decide

theorem tmFiber20ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber20Key (tauStateChunk32 32) =
      [] := by
  decide

theorem tmFiber20ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber20Key (tauStateChunk32 64) =
      [] := by
  decide

theorem tmFiber20ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber20Key (tauStateChunk32 96) =
      [] := by
  decide

theorem tmFiber20ExtractLeftChunk_128_eq_take :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber20Key (tauStateChunk32 128) =
      tmFiber20DirectStates.take 32 := by
  decide

theorem tmFiber20ExtractLeftChunk_160_eq_drop :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber20Key (tauStateChunk32 160) =
      tmFiber20DirectStates.drop 32 := by
  decide

theorem tmFiber20ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber20Key tauStateTail192 = [] := by
  decide

theorem tmFiber20ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber20Key allTauStates = tmFiber20DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [tmFiber20ExtractLeftChunk_0_eq_nil,
    tmFiber20ExtractLeftChunk_32_eq_nil,
    tmFiber20ExtractLeftChunk_64_eq_nil,
    tmFiber20ExtractLeftChunk_96_eq_nil,
    tmFiber20ExtractLeftChunk_128_eq_take,
    tmFiber20ExtractLeftChunk_160_eq_drop,
    tmFiber20ExtractLeftTail_eq_nil]
  simp

theorem tmFiber20RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber20Key = tmFiber20DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber20Key]
  exact tmFiber20ExtractAllLefts_eq_direct

theorem tmFiber20RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber20Key) = true := by
  rw [tmFiber20RealFiber_eq_direct]
  exact tmFiber20DirectConnected

theorem tmFiber44ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber44Key (tauStateChunk32 0) =
      [] := by
  decide

theorem tmFiber44ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber44Key (tauStateChunk32 32) =
      [] := by
  decide

theorem tmFiber44ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber44Key (tauStateChunk32 64) =
      [] := by
  decide

theorem tmFiber44ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber44Key (tauStateChunk32 96) =
      [] := by
  decide

theorem tmFiber44ExtractLeftChunk_128_eq_take :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber44Key (tauStateChunk32 128) =
      tmFiber44DirectStates.take 32 := by
  decide

theorem tmFiber44ExtractLeftChunk_160_eq_drop :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber44Key (tauStateChunk32 160) =
      tmFiber44DirectStates.drop 32 := by
  decide

theorem tmFiber44ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber44Key tauStateTail192 = [] := by
  decide

theorem tmFiber44ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber44Key allTauStates = tmFiber44DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [tmFiber44ExtractLeftChunk_0_eq_nil,
    tmFiber44ExtractLeftChunk_32_eq_nil,
    tmFiber44ExtractLeftChunk_64_eq_nil,
    tmFiber44ExtractLeftChunk_96_eq_nil,
    tmFiber44ExtractLeftChunk_128_eq_take,
    tmFiber44ExtractLeftChunk_160_eq_drop,
    tmFiber44ExtractLeftTail_eq_nil]
  simp

theorem tmFiber44RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber44Key = tmFiber44DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber44Key]
  exact tmFiber44ExtractAllLefts_eq_direct

theorem tmFiber44RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber44Key) = true := by
  rw [tmFiber44RealFiber_eq_direct]
  exact tmFiber44DirectConnected

theorem tmFiber50ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber50Key (tauStateChunk32 0) =
      [] := by
  decide

theorem tmFiber50ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber50Key (tauStateChunk32 32) =
      [] := by
  decide

theorem tmFiber50ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber50Key (tauStateChunk32 64) =
      [] := by
  decide

theorem tmFiber50ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber50Key (tauStateChunk32 96) =
      [] := by
  decide

theorem tmFiber50ExtractLeftChunk_128_eq_take :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber50Key (tauStateChunk32 128) =
      tmFiber50DirectStates.take 32 := by
  decide

theorem tmFiber50ExtractLeftChunk_160_eq_drop :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber50Key (tauStateChunk32 160) =
      tmFiber50DirectStates.drop 32 := by
  decide

theorem tmFiber50ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber50Key tauStateTail192 = [] := by
  decide

theorem tmFiber50ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber50Key allTauStates = tmFiber50DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [tmFiber50ExtractLeftChunk_0_eq_nil,
    tmFiber50ExtractLeftChunk_32_eq_nil,
    tmFiber50ExtractLeftChunk_64_eq_nil,
    tmFiber50ExtractLeftChunk_96_eq_nil,
    tmFiber50ExtractLeftChunk_128_eq_take,
    tmFiber50ExtractLeftChunk_160_eq_drop,
    tmFiber50ExtractLeftTail_eq_nil]
  simp

theorem tmFiber50RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber50Key = tmFiber50DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber50Key]
  exact tmFiber50ExtractAllLefts_eq_direct

theorem tmFiber50RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber50Key) = true := by
  rw [tmFiber50RealFiber_eq_direct]
  exact tmFiber50DirectConnected

theorem tmFiber70ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber70Key (tauStateChunk32 0) =
      [] := by
  decide

theorem tmFiber70ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber70Key (tauStateChunk32 32) =
      [] := by
  decide

theorem tmFiber70ExtractLeftChunk_64_eq_take :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber70Key (tauStateChunk32 64) =
      tmFiber70DirectStates.take 32 := by
  decide

theorem tmFiber70ExtractLeftChunk_96_eq_drop :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber70Key (tauStateChunk32 96) =
      tmFiber70DirectStates.drop 32 := by
  decide

theorem tmFiber70ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber70Key (tauStateChunk32 128) =
      [] := by
  decide

theorem tmFiber70ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber70Key (tauStateChunk32 160) =
      [] := by
  decide

theorem tmFiber70ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber70Key tauStateTail192 = [] := by
  decide

theorem tmFiber70ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber70Key allTauStates = tmFiber70DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [tmFiber70ExtractLeftChunk_0_eq_nil,
    tmFiber70ExtractLeftChunk_32_eq_nil,
    tmFiber70ExtractLeftChunk_64_eq_take,
    tmFiber70ExtractLeftChunk_96_eq_drop,
    tmFiber70ExtractLeftChunk_128_eq_nil,
    tmFiber70ExtractLeftChunk_160_eq_nil,
    tmFiber70ExtractLeftTail_eq_nil]
  simp

theorem tmFiber70RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber70Key = tmFiber70DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber70Key]
  exact tmFiber70ExtractAllLefts_eq_direct

theorem tmFiber70RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber70Key) = true := by
  rw [tmFiber70RealFiber_eq_direct]
  exact tmFiber70DirectConnected

theorem tmFiber76ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber76Key (tauStateChunk32 0) =
      [] := by
  decide

theorem tmFiber76ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber76Key (tauStateChunk32 32) =
      [] := by
  decide

theorem tmFiber76ExtractLeftChunk_64_eq_take :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber76Key (tauStateChunk32 64) =
      tmFiber76DirectStates.take 32 := by
  decide

theorem tmFiber76ExtractLeftChunk_96_eq_drop :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber76Key (tauStateChunk32 96) =
      tmFiber76DirectStates.drop 32 := by
  decide

theorem tmFiber76ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber76Key (tauStateChunk32 128) =
      [] := by
  decide

theorem tmFiber76ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber76Key (tauStateChunk32 160) =
      [] := by
  decide

theorem tmFiber76ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber76Key tauStateTail192 = [] := by
  decide

theorem tmFiber76ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList tmWord tmFiber76Key allTauStates = tmFiber76DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [tmFiber76ExtractLeftChunk_0_eq_nil,
    tmFiber76ExtractLeftChunk_32_eq_nil,
    tmFiber76ExtractLeftChunk_64_eq_take,
    tmFiber76ExtractLeftChunk_96_eq_drop,
    tmFiber76ExtractLeftChunk_128_eq_nil,
    tmFiber76ExtractLeftChunk_160_eq_nil,
    tmFiber76ExtractLeftTail_eq_nil]
  simp

theorem tmFiber76RealFiber_eq_direct :
    chainFiberFrom tmWord (allChainStates tmWord) tmFiber76Key = tmFiber76DirectStates := by
  rw [chainFiberFrom_tm_lengthTwo_eq_extracts tmFiber76Key]
  exact tmFiber76ExtractAllLefts_eq_direct

theorem tmFiber76RealFiberConnected :
    chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) tmFiber76Key) = true := by
  rw [tmFiber76RealFiber_eq_direct]
  exact tmFiber76DirectConnected

end GoertzelLemma818LengthTwoTMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
