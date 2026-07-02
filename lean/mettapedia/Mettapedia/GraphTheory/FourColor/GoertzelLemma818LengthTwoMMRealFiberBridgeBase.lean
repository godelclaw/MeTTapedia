import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoRealFiberBridgePrototype
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Shared real-fiber extraction helpers for `mirror,mirror` length-two bridges
-/

namespace GoertzelLemma818LengthTwoMMRealFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype

theorem mmAllChainStates_lengthTwo_eq :
    allChainStates mmWord = bindList allTauStates fun left => lengthTwoStatesFromLeft mmWord left := by
  simp [mmWord, allChainStates, buildChainStatesFrom, extendChainStates,
    lengthTwoStatesFromLeft, chainStateAt, tauOrientAt, listGetD, bindList_map]

theorem chainFiberFrom_mm_lengthTwo_eq_extracts (key : List LColor) :
    chainFiberFrom mmWord (allChainStates mmWord) key =
      lengthTwoFiberExtractLeftStateList mmWord key allTauStates := by
  unfold chainFiberFrom lengthTwoFiberExtractLeftStateList lengthTwoFiberExtractLeftState
  rw [mmAllChainStates_lengthTwo_eq]
  rw [bindList_filter]

end GoertzelLemma818LengthTwoMMRealFiberBridge

end Mettapedia.GraphTheory.FourColor
