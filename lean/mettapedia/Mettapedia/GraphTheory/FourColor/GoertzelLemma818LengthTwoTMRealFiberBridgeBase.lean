import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoRealFiberBridgePrototype
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Shared real-fiber extraction helpers for `normal,mirror` length-two bridges
-/

namespace GoertzelLemma818LengthTwoTMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype

theorem tmAllChainStates_lengthTwo_eq :
    allChainStates tmWord = bindList allTauStates fun left => lengthTwoStatesFromLeft tmWord left := by
  simp [tmWord, allChainStates, buildChainStatesFrom, extendChainStates,
    lengthTwoStatesFromLeft, chainStateAt, tauOrientAt, listGetD, bindList_map]

theorem chainFiberFrom_tm_lengthTwo_eq_extracts (key : List LColor) :
    chainFiberFrom tmWord (allChainStates tmWord) key =
      lengthTwoFiberExtractLeftStateList tmWord key allTauStates := by
  unfold chainFiberFrom lengthTwoFiberExtractLeftStateList lengthTwoFiberExtractLeftState
  rw [tmAllChainStates_lengthTwo_eq]
  rw [bindList_filter]

end GoertzelLemma818LengthTwoTMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
