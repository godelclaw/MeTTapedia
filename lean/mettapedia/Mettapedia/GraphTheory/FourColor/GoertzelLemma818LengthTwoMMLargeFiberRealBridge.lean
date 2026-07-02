import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMLargeFiber4Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMLargeFiber8Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMLargeFiber10Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMLargeFiber20Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMLargeFiber30Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMLargeFiber36Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMLargeFiber44Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMLargeFiber50Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMLargeFiber60Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMLargeFiber70Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMLargeFiber72Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMLargeFiber76Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for size-64 `mirror,mirror` length-two fibers

This generated module identifies generated direct fiber lists with their actual
real fibers using per-left-chunk extraction lemmas.
-/

namespace GoertzelLemma818LengthTwoMMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMMBridge

theorem mmFiber4ExtractLeftChunk_0_eq_take :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber4Key (tauStateChunk32 0) =
      mmFiber4DirectStates.take 32 := by
  decide

theorem mmFiber4ExtractLeftChunk_32_eq_drop :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber4Key (tauStateChunk32 32) =
      mmFiber4DirectStates.drop 32 := by
  decide

theorem mmFiber4ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber4Key (tauStateChunk32 64) =
      [] := by
  decide

theorem mmFiber4ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber4Key (tauStateChunk32 96) =
      [] := by
  decide

theorem mmFiber4ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber4Key (tauStateChunk32 128) =
      [] := by
  decide

theorem mmFiber4ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber4Key (tauStateChunk32 160) =
      [] := by
  decide

theorem mmFiber4ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber4Key tauStateTail192 = [] := by
  decide

theorem mmFiber4ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber4Key allTauStates = mmFiber4DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mmFiber4ExtractLeftChunk_0_eq_take, mmFiber4ExtractLeftChunk_32_eq_drop, mmFiber4ExtractLeftChunk_64_eq_nil, mmFiber4ExtractLeftChunk_96_eq_nil, mmFiber4ExtractLeftChunk_128_eq_nil, mmFiber4ExtractLeftChunk_160_eq_nil, mmFiber4ExtractLeftTail_eq_nil]
  simp

theorem mmFiber4RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber4Key = mmFiber4DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber4Key]
  exact mmFiber4ExtractAllLefts_eq_direct

theorem mmFiber4RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber4Key) = true := by
  rw [mmFiber4RealFiber_eq_direct]
  exact mmFiber4DirectConnected

theorem mmFiber8ExtractLeftChunk_0_eq_take :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber8Key (tauStateChunk32 0) =
      mmFiber8DirectStates.take 32 := by
  decide

theorem mmFiber8ExtractLeftChunk_32_eq_drop :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber8Key (tauStateChunk32 32) =
      mmFiber8DirectStates.drop 32 := by
  decide

theorem mmFiber8ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber8Key (tauStateChunk32 64) =
      [] := by
  decide

theorem mmFiber8ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber8Key (tauStateChunk32 96) =
      [] := by
  decide

theorem mmFiber8ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber8Key (tauStateChunk32 128) =
      [] := by
  decide

theorem mmFiber8ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber8Key (tauStateChunk32 160) =
      [] := by
  decide

theorem mmFiber8ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber8Key tauStateTail192 = [] := by
  decide

theorem mmFiber8ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber8Key allTauStates = mmFiber8DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mmFiber8ExtractLeftChunk_0_eq_take, mmFiber8ExtractLeftChunk_32_eq_drop, mmFiber8ExtractLeftChunk_64_eq_nil, mmFiber8ExtractLeftChunk_96_eq_nil, mmFiber8ExtractLeftChunk_128_eq_nil, mmFiber8ExtractLeftChunk_160_eq_nil, mmFiber8ExtractLeftTail_eq_nil]
  simp

theorem mmFiber8RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber8Key = mmFiber8DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber8Key]
  exact mmFiber8ExtractAllLefts_eq_direct

theorem mmFiber8RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber8Key) = true := by
  rw [mmFiber8RealFiber_eq_direct]
  exact mmFiber8DirectConnected

theorem mmFiber10ExtractLeftChunk_0_eq_take :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber10Key (tauStateChunk32 0) =
      mmFiber10DirectStates.take 32 := by
  decide

theorem mmFiber10ExtractLeftChunk_32_eq_drop :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber10Key (tauStateChunk32 32) =
      mmFiber10DirectStates.drop 32 := by
  decide

theorem mmFiber10ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber10Key (tauStateChunk32 64) =
      [] := by
  decide

theorem mmFiber10ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber10Key (tauStateChunk32 96) =
      [] := by
  decide

theorem mmFiber10ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber10Key (tauStateChunk32 128) =
      [] := by
  decide

theorem mmFiber10ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber10Key (tauStateChunk32 160) =
      [] := by
  decide

theorem mmFiber10ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber10Key tauStateTail192 = [] := by
  decide

theorem mmFiber10ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber10Key allTauStates = mmFiber10DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mmFiber10ExtractLeftChunk_0_eq_take, mmFiber10ExtractLeftChunk_32_eq_drop, mmFiber10ExtractLeftChunk_64_eq_nil, mmFiber10ExtractLeftChunk_96_eq_nil, mmFiber10ExtractLeftChunk_128_eq_nil, mmFiber10ExtractLeftChunk_160_eq_nil, mmFiber10ExtractLeftTail_eq_nil]
  simp

theorem mmFiber10RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber10Key = mmFiber10DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber10Key]
  exact mmFiber10ExtractAllLefts_eq_direct

theorem mmFiber10RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber10Key) = true := by
  rw [mmFiber10RealFiber_eq_direct]
  exact mmFiber10DirectConnected

theorem mmFiber20ExtractLeftChunk_0_eq_take :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber20Key (tauStateChunk32 0) =
      mmFiber20DirectStates.take 32 := by
  decide

theorem mmFiber20ExtractLeftChunk_32_eq_drop :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber20Key (tauStateChunk32 32) =
      mmFiber20DirectStates.drop 32 := by
  decide

theorem mmFiber20ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber20Key (tauStateChunk32 64) =
      [] := by
  decide

theorem mmFiber20ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber20Key (tauStateChunk32 96) =
      [] := by
  decide

theorem mmFiber20ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber20Key (tauStateChunk32 128) =
      [] := by
  decide

theorem mmFiber20ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber20Key (tauStateChunk32 160) =
      [] := by
  decide

theorem mmFiber20ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber20Key tauStateTail192 = [] := by
  decide

theorem mmFiber20ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber20Key allTauStates = mmFiber20DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mmFiber20ExtractLeftChunk_0_eq_take, mmFiber20ExtractLeftChunk_32_eq_drop, mmFiber20ExtractLeftChunk_64_eq_nil, mmFiber20ExtractLeftChunk_96_eq_nil, mmFiber20ExtractLeftChunk_128_eq_nil, mmFiber20ExtractLeftChunk_160_eq_nil, mmFiber20ExtractLeftTail_eq_nil]
  simp

theorem mmFiber20RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber20Key = mmFiber20DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber20Key]
  exact mmFiber20ExtractAllLefts_eq_direct

theorem mmFiber20RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber20Key) = true := by
  rw [mmFiber20RealFiber_eq_direct]
  exact mmFiber20DirectConnected

theorem mmFiber30ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber30Key (tauStateChunk32 0) =
      [] := by
  decide

theorem mmFiber30ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber30Key (tauStateChunk32 32) =
      [] := by
  decide

theorem mmFiber30ExtractLeftChunk_64_eq_take :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber30Key (tauStateChunk32 64) =
      mmFiber30DirectStates.take 32 := by
  decide

theorem mmFiber30ExtractLeftChunk_96_eq_drop :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber30Key (tauStateChunk32 96) =
      mmFiber30DirectStates.drop 32 := by
  decide

theorem mmFiber30ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber30Key (tauStateChunk32 128) =
      [] := by
  decide

theorem mmFiber30ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber30Key (tauStateChunk32 160) =
      [] := by
  decide

theorem mmFiber30ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber30Key tauStateTail192 = [] := by
  decide

theorem mmFiber30ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber30Key allTauStates = mmFiber30DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mmFiber30ExtractLeftChunk_0_eq_nil, mmFiber30ExtractLeftChunk_32_eq_nil, mmFiber30ExtractLeftChunk_64_eq_take, mmFiber30ExtractLeftChunk_96_eq_drop, mmFiber30ExtractLeftChunk_128_eq_nil, mmFiber30ExtractLeftChunk_160_eq_nil, mmFiber30ExtractLeftTail_eq_nil]
  simp

theorem mmFiber30RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber30Key = mmFiber30DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber30Key]
  exact mmFiber30ExtractAllLefts_eq_direct

theorem mmFiber30RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber30Key) = true := by
  rw [mmFiber30RealFiber_eq_direct]
  exact mmFiber30DirectConnected

theorem mmFiber36ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber36Key (tauStateChunk32 0) =
      [] := by
  decide

theorem mmFiber36ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber36Key (tauStateChunk32 32) =
      [] := by
  decide

theorem mmFiber36ExtractLeftChunk_64_eq_take :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber36Key (tauStateChunk32 64) =
      mmFiber36DirectStates.take 32 := by
  decide

theorem mmFiber36ExtractLeftChunk_96_eq_drop :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber36Key (tauStateChunk32 96) =
      mmFiber36DirectStates.drop 32 := by
  decide

theorem mmFiber36ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber36Key (tauStateChunk32 128) =
      [] := by
  decide

theorem mmFiber36ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber36Key (tauStateChunk32 160) =
      [] := by
  decide

theorem mmFiber36ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber36Key tauStateTail192 = [] := by
  decide

theorem mmFiber36ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber36Key allTauStates = mmFiber36DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mmFiber36ExtractLeftChunk_0_eq_nil, mmFiber36ExtractLeftChunk_32_eq_nil, mmFiber36ExtractLeftChunk_64_eq_take, mmFiber36ExtractLeftChunk_96_eq_drop, mmFiber36ExtractLeftChunk_128_eq_nil, mmFiber36ExtractLeftChunk_160_eq_nil, mmFiber36ExtractLeftTail_eq_nil]
  simp

theorem mmFiber36RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber36Key = mmFiber36DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber36Key]
  exact mmFiber36ExtractAllLefts_eq_direct

theorem mmFiber36RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber36Key) = true := by
  rw [mmFiber36RealFiber_eq_direct]
  exact mmFiber36DirectConnected

theorem mmFiber44ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber44Key (tauStateChunk32 0) =
      [] := by
  decide

theorem mmFiber44ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber44Key (tauStateChunk32 32) =
      [] := by
  decide

theorem mmFiber44ExtractLeftChunk_64_eq_take :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber44Key (tauStateChunk32 64) =
      mmFiber44DirectStates.take 32 := by
  decide

theorem mmFiber44ExtractLeftChunk_96_eq_drop :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber44Key (tauStateChunk32 96) =
      mmFiber44DirectStates.drop 32 := by
  decide

theorem mmFiber44ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber44Key (tauStateChunk32 128) =
      [] := by
  decide

theorem mmFiber44ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber44Key (tauStateChunk32 160) =
      [] := by
  decide

theorem mmFiber44ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber44Key tauStateTail192 = [] := by
  decide

theorem mmFiber44ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber44Key allTauStates = mmFiber44DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mmFiber44ExtractLeftChunk_0_eq_nil, mmFiber44ExtractLeftChunk_32_eq_nil, mmFiber44ExtractLeftChunk_64_eq_take, mmFiber44ExtractLeftChunk_96_eq_drop, mmFiber44ExtractLeftChunk_128_eq_nil, mmFiber44ExtractLeftChunk_160_eq_nil, mmFiber44ExtractLeftTail_eq_nil]
  simp

theorem mmFiber44RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber44Key = mmFiber44DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber44Key]
  exact mmFiber44ExtractAllLefts_eq_direct

theorem mmFiber44RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber44Key) = true := by
  rw [mmFiber44RealFiber_eq_direct]
  exact mmFiber44DirectConnected

theorem mmFiber50ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber50Key (tauStateChunk32 0) =
      [] := by
  decide

theorem mmFiber50ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber50Key (tauStateChunk32 32) =
      [] := by
  decide

theorem mmFiber50ExtractLeftChunk_64_eq_take :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber50Key (tauStateChunk32 64) =
      mmFiber50DirectStates.take 32 := by
  decide

theorem mmFiber50ExtractLeftChunk_96_eq_drop :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber50Key (tauStateChunk32 96) =
      mmFiber50DirectStates.drop 32 := by
  decide

theorem mmFiber50ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber50Key (tauStateChunk32 128) =
      [] := by
  decide

theorem mmFiber50ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber50Key (tauStateChunk32 160) =
      [] := by
  decide

theorem mmFiber50ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber50Key tauStateTail192 = [] := by
  decide

theorem mmFiber50ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber50Key allTauStates = mmFiber50DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mmFiber50ExtractLeftChunk_0_eq_nil, mmFiber50ExtractLeftChunk_32_eq_nil, mmFiber50ExtractLeftChunk_64_eq_take, mmFiber50ExtractLeftChunk_96_eq_drop, mmFiber50ExtractLeftChunk_128_eq_nil, mmFiber50ExtractLeftChunk_160_eq_nil, mmFiber50ExtractLeftTail_eq_nil]
  simp

theorem mmFiber50RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber50Key = mmFiber50DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber50Key]
  exact mmFiber50ExtractAllLefts_eq_direct

theorem mmFiber50RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber50Key) = true := by
  rw [mmFiber50RealFiber_eq_direct]
  exact mmFiber50DirectConnected

theorem mmFiber60ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber60Key (tauStateChunk32 0) =
      [] := by
  decide

theorem mmFiber60ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber60Key (tauStateChunk32 32) =
      [] := by
  decide

theorem mmFiber60ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber60Key (tauStateChunk32 64) =
      [] := by
  decide

theorem mmFiber60ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber60Key (tauStateChunk32 96) =
      [] := by
  decide

theorem mmFiber60ExtractLeftChunk_128_eq_take :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber60Key (tauStateChunk32 128) =
      mmFiber60DirectStates.take 32 := by
  decide

theorem mmFiber60ExtractLeftChunk_160_eq_drop :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber60Key (tauStateChunk32 160) =
      mmFiber60DirectStates.drop 32 := by
  decide

theorem mmFiber60ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber60Key tauStateTail192 = [] := by
  decide

theorem mmFiber60ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber60Key allTauStates = mmFiber60DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mmFiber60ExtractLeftChunk_0_eq_nil, mmFiber60ExtractLeftChunk_32_eq_nil, mmFiber60ExtractLeftChunk_64_eq_nil, mmFiber60ExtractLeftChunk_96_eq_nil, mmFiber60ExtractLeftChunk_128_eq_take, mmFiber60ExtractLeftChunk_160_eq_drop, mmFiber60ExtractLeftTail_eq_nil]
  simp

theorem mmFiber60RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber60Key = mmFiber60DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber60Key]
  exact mmFiber60ExtractAllLefts_eq_direct

theorem mmFiber60RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber60Key) = true := by
  rw [mmFiber60RealFiber_eq_direct]
  exact mmFiber60DirectConnected

theorem mmFiber70ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber70Key (tauStateChunk32 0) =
      [] := by
  decide

theorem mmFiber70ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber70Key (tauStateChunk32 32) =
      [] := by
  decide

theorem mmFiber70ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber70Key (tauStateChunk32 64) =
      [] := by
  decide

theorem mmFiber70ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber70Key (tauStateChunk32 96) =
      [] := by
  decide

theorem mmFiber70ExtractLeftChunk_128_eq_take :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber70Key (tauStateChunk32 128) =
      mmFiber70DirectStates.take 32 := by
  decide

theorem mmFiber70ExtractLeftChunk_160_eq_drop :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber70Key (tauStateChunk32 160) =
      mmFiber70DirectStates.drop 32 := by
  decide

theorem mmFiber70ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber70Key tauStateTail192 = [] := by
  decide

theorem mmFiber70ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber70Key allTauStates = mmFiber70DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mmFiber70ExtractLeftChunk_0_eq_nil, mmFiber70ExtractLeftChunk_32_eq_nil, mmFiber70ExtractLeftChunk_64_eq_nil, mmFiber70ExtractLeftChunk_96_eq_nil, mmFiber70ExtractLeftChunk_128_eq_take, mmFiber70ExtractLeftChunk_160_eq_drop, mmFiber70ExtractLeftTail_eq_nil]
  simp

theorem mmFiber70RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber70Key = mmFiber70DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber70Key]
  exact mmFiber70ExtractAllLefts_eq_direct

theorem mmFiber70RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber70Key) = true := by
  rw [mmFiber70RealFiber_eq_direct]
  exact mmFiber70DirectConnected

theorem mmFiber72ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber72Key (tauStateChunk32 0) =
      [] := by
  decide

theorem mmFiber72ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber72Key (tauStateChunk32 32) =
      [] := by
  decide

theorem mmFiber72ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber72Key (tauStateChunk32 64) =
      [] := by
  decide

theorem mmFiber72ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber72Key (tauStateChunk32 96) =
      [] := by
  decide

theorem mmFiber72ExtractLeftChunk_128_eq_take :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber72Key (tauStateChunk32 128) =
      mmFiber72DirectStates.take 32 := by
  decide

theorem mmFiber72ExtractLeftChunk_160_eq_drop :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber72Key (tauStateChunk32 160) =
      mmFiber72DirectStates.drop 32 := by
  decide

theorem mmFiber72ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber72Key tauStateTail192 = [] := by
  decide

theorem mmFiber72ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber72Key allTauStates = mmFiber72DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mmFiber72ExtractLeftChunk_0_eq_nil, mmFiber72ExtractLeftChunk_32_eq_nil, mmFiber72ExtractLeftChunk_64_eq_nil, mmFiber72ExtractLeftChunk_96_eq_nil, mmFiber72ExtractLeftChunk_128_eq_take, mmFiber72ExtractLeftChunk_160_eq_drop, mmFiber72ExtractLeftTail_eq_nil]
  simp

theorem mmFiber72RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber72Key = mmFiber72DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber72Key]
  exact mmFiber72ExtractAllLefts_eq_direct

theorem mmFiber72RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber72Key) = true := by
  rw [mmFiber72RealFiber_eq_direct]
  exact mmFiber72DirectConnected

theorem mmFiber76ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber76Key (tauStateChunk32 0) =
      [] := by
  decide

theorem mmFiber76ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber76Key (tauStateChunk32 32) =
      [] := by
  decide

theorem mmFiber76ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber76Key (tauStateChunk32 64) =
      [] := by
  decide

theorem mmFiber76ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber76Key (tauStateChunk32 96) =
      [] := by
  decide

theorem mmFiber76ExtractLeftChunk_128_eq_take :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber76Key (tauStateChunk32 128) =
      mmFiber76DirectStates.take 32 := by
  decide

theorem mmFiber76ExtractLeftChunk_160_eq_drop :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber76Key (tauStateChunk32 160) =
      mmFiber76DirectStates.drop 32 := by
  decide

theorem mmFiber76ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber76Key tauStateTail192 = [] := by
  decide

theorem mmFiber76ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mmWord mmFiber76Key allTauStates = mmFiber76DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mmFiber76ExtractLeftChunk_0_eq_nil, mmFiber76ExtractLeftChunk_32_eq_nil, mmFiber76ExtractLeftChunk_64_eq_nil, mmFiber76ExtractLeftChunk_96_eq_nil, mmFiber76ExtractLeftChunk_128_eq_take, mmFiber76ExtractLeftChunk_160_eq_drop, mmFiber76ExtractLeftTail_eq_nil]
  simp

theorem mmFiber76RealFiber_eq_direct :
    chainFiberFrom mmWord (allChainStates mmWord) mmFiber76Key = mmFiber76DirectStates := by
  rw [chainFiberFrom_mm_lengthTwo_eq_extracts mmFiber76Key]
  exact mmFiber76ExtractAllLefts_eq_direct

theorem mmFiber76RealFiberConnected :
    chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) mmFiber76Key) = true := by
  rw [mmFiber76RealFiber_eq_direct]
  exact mmFiber76DirectConnected

end GoertzelLemma818LengthTwoMMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
