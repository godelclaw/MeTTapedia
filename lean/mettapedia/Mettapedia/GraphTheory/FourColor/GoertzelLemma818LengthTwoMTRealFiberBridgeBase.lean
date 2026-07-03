import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoRealFiberBridgePrototype
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Shared real-fiber extraction helpers for `mirror,normal` length-two bridges
-/

namespace GoertzelLemma818LengthTwoMTRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype

theorem mtAllChainStates_lengthTwo_eq :
    allChainStates mtWord = bindList allTauStates fun left => lengthTwoStatesFromLeft mtWord left := by
  simp [mtWord, allChainStates, buildChainStatesFrom, extendChainStates,
    lengthTwoStatesFromLeft, chainStateAt, tauOrientAt, listGetD, bindList_map]

theorem chainFiberFrom_mt_lengthTwo_eq_extracts (key : List LColor) :
    chainFiberFrom mtWord (allChainStates mtWord) key =
      lengthTwoFiberExtractLeftStateList mtWord key allTauStates := by
  unfold chainFiberFrom lengthTwoFiberExtractLeftStateList lengthTwoFiberExtractLeftState
  rw [mtAllChainStates_lengthTwo_eq]
  rw [bindList_filter]

end GoertzelLemma818LengthTwoMTRealFiberBridge

end Mettapedia.GraphTheory.FourColor
