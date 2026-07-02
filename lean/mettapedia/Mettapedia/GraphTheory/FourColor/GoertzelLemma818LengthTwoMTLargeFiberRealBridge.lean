import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTLargeFiber4Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTLargeFiber8Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTLargeFiber10Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTLargeFiber20Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTLargeFiber30Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTLargeFiber36Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTLargeFiber44Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTLargeFiber50Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTLargeFiber60Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTLargeFiber70Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTLargeFiber72Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTLargeFiber76Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Real-fiber bridge for size-64 `mirror,normal` length-two fibers

This generated module identifies generated direct fiber lists with their actual
real fibers using per-left-chunk extraction lemmas.
-/

namespace GoertzelLemma818LengthTwoMTRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype
open GoertzelLemma818LengthTwoMTBridge

theorem mtFiber4ExtractLeftChunk_0_eq_take :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber4Key (tauStateChunk32 0) =
      mtFiber4DirectStates.take 32 := by
  decide

theorem mtFiber4ExtractLeftChunk_32_eq_drop :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber4Key (tauStateChunk32 32) =
      mtFiber4DirectStates.drop 32 := by
  decide

theorem mtFiber4ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber4Key (tauStateChunk32 64) =
      [] := by
  decide

theorem mtFiber4ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber4Key (tauStateChunk32 96) =
      [] := by
  decide

theorem mtFiber4ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber4Key (tauStateChunk32 128) =
      [] := by
  decide

theorem mtFiber4ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber4Key (tauStateChunk32 160) =
      [] := by
  decide

theorem mtFiber4ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber4Key tauStateTail192 = [] := by
  decide

theorem mtFiber4ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber4Key allTauStates = mtFiber4DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mtFiber4ExtractLeftChunk_0_eq_take, mtFiber4ExtractLeftChunk_32_eq_drop, mtFiber4ExtractLeftChunk_64_eq_nil, mtFiber4ExtractLeftChunk_96_eq_nil, mtFiber4ExtractLeftChunk_128_eq_nil, mtFiber4ExtractLeftChunk_160_eq_nil, mtFiber4ExtractLeftTail_eq_nil]
  simp

theorem mtFiber4RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber4Key = mtFiber4DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber4Key]
  exact mtFiber4ExtractAllLefts_eq_direct

theorem mtFiber4RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber4Key) = true := by
  rw [mtFiber4RealFiber_eq_direct]
  exact mtFiber4DirectConnected

theorem mtFiber8ExtractLeftChunk_0_eq_take :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber8Key (tauStateChunk32 0) =
      mtFiber8DirectStates.take 32 := by
  decide

theorem mtFiber8ExtractLeftChunk_32_eq_drop :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber8Key (tauStateChunk32 32) =
      mtFiber8DirectStates.drop 32 := by
  decide

theorem mtFiber8ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber8Key (tauStateChunk32 64) =
      [] := by
  decide

theorem mtFiber8ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber8Key (tauStateChunk32 96) =
      [] := by
  decide

theorem mtFiber8ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber8Key (tauStateChunk32 128) =
      [] := by
  decide

theorem mtFiber8ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber8Key (tauStateChunk32 160) =
      [] := by
  decide

theorem mtFiber8ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber8Key tauStateTail192 = [] := by
  decide

theorem mtFiber8ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber8Key allTauStates = mtFiber8DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mtFiber8ExtractLeftChunk_0_eq_take, mtFiber8ExtractLeftChunk_32_eq_drop, mtFiber8ExtractLeftChunk_64_eq_nil, mtFiber8ExtractLeftChunk_96_eq_nil, mtFiber8ExtractLeftChunk_128_eq_nil, mtFiber8ExtractLeftChunk_160_eq_nil, mtFiber8ExtractLeftTail_eq_nil]
  simp

theorem mtFiber8RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber8Key = mtFiber8DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber8Key]
  exact mtFiber8ExtractAllLefts_eq_direct

theorem mtFiber8RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber8Key) = true := by
  rw [mtFiber8RealFiber_eq_direct]
  exact mtFiber8DirectConnected

theorem mtFiber10ExtractLeftChunk_0_eq_take :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber10Key (tauStateChunk32 0) =
      mtFiber10DirectStates.take 32 := by
  decide

theorem mtFiber10ExtractLeftChunk_32_eq_drop :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber10Key (tauStateChunk32 32) =
      mtFiber10DirectStates.drop 32 := by
  decide

theorem mtFiber10ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber10Key (tauStateChunk32 64) =
      [] := by
  decide

theorem mtFiber10ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber10Key (tauStateChunk32 96) =
      [] := by
  decide

theorem mtFiber10ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber10Key (tauStateChunk32 128) =
      [] := by
  decide

theorem mtFiber10ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber10Key (tauStateChunk32 160) =
      [] := by
  decide

theorem mtFiber10ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber10Key tauStateTail192 = [] := by
  decide

theorem mtFiber10ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber10Key allTauStates = mtFiber10DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mtFiber10ExtractLeftChunk_0_eq_take, mtFiber10ExtractLeftChunk_32_eq_drop, mtFiber10ExtractLeftChunk_64_eq_nil, mtFiber10ExtractLeftChunk_96_eq_nil, mtFiber10ExtractLeftChunk_128_eq_nil, mtFiber10ExtractLeftChunk_160_eq_nil, mtFiber10ExtractLeftTail_eq_nil]
  simp

theorem mtFiber10RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber10Key = mtFiber10DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber10Key]
  exact mtFiber10ExtractAllLefts_eq_direct

theorem mtFiber10RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber10Key) = true := by
  rw [mtFiber10RealFiber_eq_direct]
  exact mtFiber10DirectConnected

theorem mtFiber20ExtractLeftChunk_0_eq_take :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber20Key (tauStateChunk32 0) =
      mtFiber20DirectStates.take 32 := by
  decide

theorem mtFiber20ExtractLeftChunk_32_eq_drop :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber20Key (tauStateChunk32 32) =
      mtFiber20DirectStates.drop 32 := by
  decide

theorem mtFiber20ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber20Key (tauStateChunk32 64) =
      [] := by
  decide

theorem mtFiber20ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber20Key (tauStateChunk32 96) =
      [] := by
  decide

theorem mtFiber20ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber20Key (tauStateChunk32 128) =
      [] := by
  decide

theorem mtFiber20ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber20Key (tauStateChunk32 160) =
      [] := by
  decide

theorem mtFiber20ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber20Key tauStateTail192 = [] := by
  decide

theorem mtFiber20ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber20Key allTauStates = mtFiber20DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mtFiber20ExtractLeftChunk_0_eq_take, mtFiber20ExtractLeftChunk_32_eq_drop, mtFiber20ExtractLeftChunk_64_eq_nil, mtFiber20ExtractLeftChunk_96_eq_nil, mtFiber20ExtractLeftChunk_128_eq_nil, mtFiber20ExtractLeftChunk_160_eq_nil, mtFiber20ExtractLeftTail_eq_nil]
  simp

theorem mtFiber20RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber20Key = mtFiber20DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber20Key]
  exact mtFiber20ExtractAllLefts_eq_direct

theorem mtFiber20RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber20Key) = true := by
  rw [mtFiber20RealFiber_eq_direct]
  exact mtFiber20DirectConnected

theorem mtFiber30ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber30Key (tauStateChunk32 0) =
      [] := by
  decide

theorem mtFiber30ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber30Key (tauStateChunk32 32) =
      [] := by
  decide

theorem mtFiber30ExtractLeftChunk_64_eq_take :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber30Key (tauStateChunk32 64) =
      mtFiber30DirectStates.take 32 := by
  decide

theorem mtFiber30ExtractLeftChunk_96_eq_drop :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber30Key (tauStateChunk32 96) =
      mtFiber30DirectStates.drop 32 := by
  decide

theorem mtFiber30ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber30Key (tauStateChunk32 128) =
      [] := by
  decide

theorem mtFiber30ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber30Key (tauStateChunk32 160) =
      [] := by
  decide

theorem mtFiber30ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber30Key tauStateTail192 = [] := by
  decide

theorem mtFiber30ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber30Key allTauStates = mtFiber30DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mtFiber30ExtractLeftChunk_0_eq_nil, mtFiber30ExtractLeftChunk_32_eq_nil, mtFiber30ExtractLeftChunk_64_eq_take, mtFiber30ExtractLeftChunk_96_eq_drop, mtFiber30ExtractLeftChunk_128_eq_nil, mtFiber30ExtractLeftChunk_160_eq_nil, mtFiber30ExtractLeftTail_eq_nil]
  simp

theorem mtFiber30RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber30Key = mtFiber30DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber30Key]
  exact mtFiber30ExtractAllLefts_eq_direct

theorem mtFiber30RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber30Key) = true := by
  rw [mtFiber30RealFiber_eq_direct]
  exact mtFiber30DirectConnected

theorem mtFiber36ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber36Key (tauStateChunk32 0) =
      [] := by
  decide

theorem mtFiber36ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber36Key (tauStateChunk32 32) =
      [] := by
  decide

theorem mtFiber36ExtractLeftChunk_64_eq_take :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber36Key (tauStateChunk32 64) =
      mtFiber36DirectStates.take 32 := by
  decide

theorem mtFiber36ExtractLeftChunk_96_eq_drop :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber36Key (tauStateChunk32 96) =
      mtFiber36DirectStates.drop 32 := by
  decide

theorem mtFiber36ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber36Key (tauStateChunk32 128) =
      [] := by
  decide

theorem mtFiber36ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber36Key (tauStateChunk32 160) =
      [] := by
  decide

theorem mtFiber36ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber36Key tauStateTail192 = [] := by
  decide

theorem mtFiber36ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber36Key allTauStates = mtFiber36DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mtFiber36ExtractLeftChunk_0_eq_nil, mtFiber36ExtractLeftChunk_32_eq_nil, mtFiber36ExtractLeftChunk_64_eq_take, mtFiber36ExtractLeftChunk_96_eq_drop, mtFiber36ExtractLeftChunk_128_eq_nil, mtFiber36ExtractLeftChunk_160_eq_nil, mtFiber36ExtractLeftTail_eq_nil]
  simp

theorem mtFiber36RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber36Key = mtFiber36DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber36Key]
  exact mtFiber36ExtractAllLefts_eq_direct

theorem mtFiber36RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber36Key) = true := by
  rw [mtFiber36RealFiber_eq_direct]
  exact mtFiber36DirectConnected

theorem mtFiber44ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber44Key (tauStateChunk32 0) =
      [] := by
  decide

theorem mtFiber44ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber44Key (tauStateChunk32 32) =
      [] := by
  decide

theorem mtFiber44ExtractLeftChunk_64_eq_take :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber44Key (tauStateChunk32 64) =
      mtFiber44DirectStates.take 32 := by
  decide

theorem mtFiber44ExtractLeftChunk_96_eq_drop :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber44Key (tauStateChunk32 96) =
      mtFiber44DirectStates.drop 32 := by
  decide

theorem mtFiber44ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber44Key (tauStateChunk32 128) =
      [] := by
  decide

theorem mtFiber44ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber44Key (tauStateChunk32 160) =
      [] := by
  decide

theorem mtFiber44ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber44Key tauStateTail192 = [] := by
  decide

theorem mtFiber44ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber44Key allTauStates = mtFiber44DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mtFiber44ExtractLeftChunk_0_eq_nil, mtFiber44ExtractLeftChunk_32_eq_nil, mtFiber44ExtractLeftChunk_64_eq_take, mtFiber44ExtractLeftChunk_96_eq_drop, mtFiber44ExtractLeftChunk_128_eq_nil, mtFiber44ExtractLeftChunk_160_eq_nil, mtFiber44ExtractLeftTail_eq_nil]
  simp

theorem mtFiber44RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber44Key = mtFiber44DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber44Key]
  exact mtFiber44ExtractAllLefts_eq_direct

theorem mtFiber44RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber44Key) = true := by
  rw [mtFiber44RealFiber_eq_direct]
  exact mtFiber44DirectConnected

theorem mtFiber50ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber50Key (tauStateChunk32 0) =
      [] := by
  decide

theorem mtFiber50ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber50Key (tauStateChunk32 32) =
      [] := by
  decide

theorem mtFiber50ExtractLeftChunk_64_eq_take :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber50Key (tauStateChunk32 64) =
      mtFiber50DirectStates.take 32 := by
  decide

theorem mtFiber50ExtractLeftChunk_96_eq_drop :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber50Key (tauStateChunk32 96) =
      mtFiber50DirectStates.drop 32 := by
  decide

theorem mtFiber50ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber50Key (tauStateChunk32 128) =
      [] := by
  decide

theorem mtFiber50ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber50Key (tauStateChunk32 160) =
      [] := by
  decide

theorem mtFiber50ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber50Key tauStateTail192 = [] := by
  decide

theorem mtFiber50ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber50Key allTauStates = mtFiber50DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mtFiber50ExtractLeftChunk_0_eq_nil, mtFiber50ExtractLeftChunk_32_eq_nil, mtFiber50ExtractLeftChunk_64_eq_take, mtFiber50ExtractLeftChunk_96_eq_drop, mtFiber50ExtractLeftChunk_128_eq_nil, mtFiber50ExtractLeftChunk_160_eq_nil, mtFiber50ExtractLeftTail_eq_nil]
  simp

theorem mtFiber50RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber50Key = mtFiber50DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber50Key]
  exact mtFiber50ExtractAllLefts_eq_direct

theorem mtFiber50RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber50Key) = true := by
  rw [mtFiber50RealFiber_eq_direct]
  exact mtFiber50DirectConnected

theorem mtFiber60ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber60Key (tauStateChunk32 0) =
      [] := by
  decide

theorem mtFiber60ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber60Key (tauStateChunk32 32) =
      [] := by
  decide

theorem mtFiber60ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber60Key (tauStateChunk32 64) =
      [] := by
  decide

theorem mtFiber60ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber60Key (tauStateChunk32 96) =
      [] := by
  decide

theorem mtFiber60ExtractLeftChunk_128_eq_take :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber60Key (tauStateChunk32 128) =
      mtFiber60DirectStates.take 32 := by
  decide

theorem mtFiber60ExtractLeftChunk_160_eq_drop :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber60Key (tauStateChunk32 160) =
      mtFiber60DirectStates.drop 32 := by
  decide

theorem mtFiber60ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber60Key tauStateTail192 = [] := by
  decide

theorem mtFiber60ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber60Key allTauStates = mtFiber60DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mtFiber60ExtractLeftChunk_0_eq_nil, mtFiber60ExtractLeftChunk_32_eq_nil, mtFiber60ExtractLeftChunk_64_eq_nil, mtFiber60ExtractLeftChunk_96_eq_nil, mtFiber60ExtractLeftChunk_128_eq_take, mtFiber60ExtractLeftChunk_160_eq_drop, mtFiber60ExtractLeftTail_eq_nil]
  simp

theorem mtFiber60RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber60Key = mtFiber60DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber60Key]
  exact mtFiber60ExtractAllLefts_eq_direct

theorem mtFiber60RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber60Key) = true := by
  rw [mtFiber60RealFiber_eq_direct]
  exact mtFiber60DirectConnected

theorem mtFiber70ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber70Key (tauStateChunk32 0) =
      [] := by
  decide

theorem mtFiber70ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber70Key (tauStateChunk32 32) =
      [] := by
  decide

theorem mtFiber70ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber70Key (tauStateChunk32 64) =
      [] := by
  decide

theorem mtFiber70ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber70Key (tauStateChunk32 96) =
      [] := by
  decide

theorem mtFiber70ExtractLeftChunk_128_eq_take :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber70Key (tauStateChunk32 128) =
      mtFiber70DirectStates.take 32 := by
  decide

theorem mtFiber70ExtractLeftChunk_160_eq_drop :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber70Key (tauStateChunk32 160) =
      mtFiber70DirectStates.drop 32 := by
  decide

theorem mtFiber70ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber70Key tauStateTail192 = [] := by
  decide

theorem mtFiber70ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber70Key allTauStates = mtFiber70DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mtFiber70ExtractLeftChunk_0_eq_nil, mtFiber70ExtractLeftChunk_32_eq_nil, mtFiber70ExtractLeftChunk_64_eq_nil, mtFiber70ExtractLeftChunk_96_eq_nil, mtFiber70ExtractLeftChunk_128_eq_take, mtFiber70ExtractLeftChunk_160_eq_drop, mtFiber70ExtractLeftTail_eq_nil]
  simp

theorem mtFiber70RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber70Key = mtFiber70DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber70Key]
  exact mtFiber70ExtractAllLefts_eq_direct

theorem mtFiber70RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber70Key) = true := by
  rw [mtFiber70RealFiber_eq_direct]
  exact mtFiber70DirectConnected

theorem mtFiber72ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber72Key (tauStateChunk32 0) =
      [] := by
  decide

theorem mtFiber72ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber72Key (tauStateChunk32 32) =
      [] := by
  decide

theorem mtFiber72ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber72Key (tauStateChunk32 64) =
      [] := by
  decide

theorem mtFiber72ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber72Key (tauStateChunk32 96) =
      [] := by
  decide

theorem mtFiber72ExtractLeftChunk_128_eq_take :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber72Key (tauStateChunk32 128) =
      mtFiber72DirectStates.take 32 := by
  decide

theorem mtFiber72ExtractLeftChunk_160_eq_drop :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber72Key (tauStateChunk32 160) =
      mtFiber72DirectStates.drop 32 := by
  decide

theorem mtFiber72ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber72Key tauStateTail192 = [] := by
  decide

theorem mtFiber72ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber72Key allTauStates = mtFiber72DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mtFiber72ExtractLeftChunk_0_eq_nil, mtFiber72ExtractLeftChunk_32_eq_nil, mtFiber72ExtractLeftChunk_64_eq_nil, mtFiber72ExtractLeftChunk_96_eq_nil, mtFiber72ExtractLeftChunk_128_eq_take, mtFiber72ExtractLeftChunk_160_eq_drop, mtFiber72ExtractLeftTail_eq_nil]
  simp

theorem mtFiber72RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber72Key = mtFiber72DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber72Key]
  exact mtFiber72ExtractAllLefts_eq_direct

theorem mtFiber72RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber72Key) = true := by
  rw [mtFiber72RealFiber_eq_direct]
  exact mtFiber72DirectConnected

theorem mtFiber76ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber76Key (tauStateChunk32 0) =
      [] := by
  decide

theorem mtFiber76ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber76Key (tauStateChunk32 32) =
      [] := by
  decide

theorem mtFiber76ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber76Key (tauStateChunk32 64) =
      [] := by
  decide

theorem mtFiber76ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber76Key (tauStateChunk32 96) =
      [] := by
  decide

theorem mtFiber76ExtractLeftChunk_128_eq_take :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber76Key (tauStateChunk32 128) =
      mtFiber76DirectStates.take 32 := by
  decide

theorem mtFiber76ExtractLeftChunk_160_eq_drop :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber76Key (tauStateChunk32 160) =
      mtFiber76DirectStates.drop 32 := by
  decide

theorem mtFiber76ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber76Key tauStateTail192 = [] := by
  decide

theorem mtFiber76ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList mtWord mtFiber76Key allTauStates = mtFiber76DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [mtFiber76ExtractLeftChunk_0_eq_nil, mtFiber76ExtractLeftChunk_32_eq_nil, mtFiber76ExtractLeftChunk_64_eq_nil, mtFiber76ExtractLeftChunk_96_eq_nil, mtFiber76ExtractLeftChunk_128_eq_take, mtFiber76ExtractLeftChunk_160_eq_drop, mtFiber76ExtractLeftTail_eq_nil]
  simp

theorem mtFiber76RealFiber_eq_direct :
    chainFiberFrom mtWord (allChainStates mtWord) mtFiber76Key = mtFiber76DirectStates := by
  rw [chainFiberFrom_mt_lengthTwo_eq_extracts mtFiber76Key]
  exact mtFiber76ExtractAllLefts_eq_direct

theorem mtFiber76RealFiberConnected :
    chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) mtFiber76Key) = true := by
  rw [mtFiber76RealFiber_eq_direct]
  exact mtFiber76DirectConnected

end GoertzelLemma818LengthTwoMTRealFiberBridge

end Mettapedia.GraphTheory.FourColor
