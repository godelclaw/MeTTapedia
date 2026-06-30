import Mettapedia.GraphTheory.FourColor.GoertzelLemma818FrontierMode
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: length-two base to frontier-mode bridge

This module connects the generated length-two chain certificates to the
profile-mode DFA surface.  It is a small base bridge for the future
frontier/DFA induction, not the all-chain `LKR_in` consequence.
-/

namespace GoertzelLemma818FrontierBaseBridge

def chainOrientToFrontier :
    GoertzelLemma814.TauOrient → GoertzelLemma818FrontierMode.TauOrient
  | GoertzelLemma814.TauOrient.normal =>
      GoertzelLemma818FrontierMode.TauOrient.tau
  | GoertzelLemma814.TauOrient.mirror =>
      GoertzelLemma818FrontierMode.TauOrient.mirror

def lengthTwoChainFrontierWord
    (w : GoertzelLemma818LengthTwoBase.LengthTwoOrientWord) :
    List GoertzelLemma818FrontierMode.TauOrient :=
  (GoertzelLemma818LengthTwoBase.lengthTwoOrientWord w).map
    chainOrientToFrontier

def lengthTwoFrontierWord :
    GoertzelLemma818LengthTwoBase.LengthTwoOrientWord →
      List GoertzelLemma818FrontierMode.TauOrient
  | GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.tt =>
      [ GoertzelLemma818FrontierMode.TauOrient.tau
      , GoertzelLemma818FrontierMode.TauOrient.tau
      ]
  | GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.tm =>
      [ GoertzelLemma818FrontierMode.TauOrient.tau
      , GoertzelLemma818FrontierMode.TauOrient.mirror
      ]
  | GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.mt =>
      [ GoertzelLemma818FrontierMode.TauOrient.mirror
      , GoertzelLemma818FrontierMode.TauOrient.tau
      ]
  | GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.mm =>
      [ GoertzelLemma818FrontierMode.TauOrient.mirror
      , GoertzelLemma818FrontierMode.TauOrient.mirror
      ]

def lengthTwoFrontierMode :
    GoertzelLemma818LengthTwoBase.LengthTwoOrientWord →
      GoertzelLemma818FrontierMode.FrontierMode
  | GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.tt =>
      GoertzelLemma818FrontierMode.FrontierMode.mode10
  | GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.tm =>
      GoertzelLemma818FrontierMode.FrontierMode.mode18
  | GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.mt =>
      GoertzelLemma818FrontierMode.FrontierMode.mode11
  | GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.mm =>
      GoertzelLemma818FrontierMode.FrontierMode.mode04

theorem lengthTwoChainFrontierWord_eq
    (w : GoertzelLemma818LengthTwoBase.LengthTwoOrientWord) :
    lengthTwoChainFrontierWord w = lengthTwoFrontierWord w := by
  cases w <;> rfl

theorem lengthTwoFrontierWordMode_ok
    (w : GoertzelLemma818LengthTwoBase.LengthTwoOrientWord) :
    GoertzelLemma818FrontierMode.wordMode (lengthTwoFrontierWord w) =
      some (lengthTwoFrontierMode w) := by
  cases w <;> rfl

theorem lengthTwoFrontierMode_hasArchivedConnectivityEvidence
    (w : GoertzelLemma818LengthTwoBase.LengthTwoOrientWord) :
    GoertzelLemma818FrontierMode.modeHasArchivedConnectivityEvidence
      (lengthTwoFrontierMode w) = true := by
  cases w <;> decide

def lengthTwoFrontierBaseAudit
    (w : GoertzelLemma818LengthTwoBase.LengthTwoOrientWord) : Bool :=
  GoertzelLemma818LengthTwoBase.lengthTwoCertificateAudit w
    && (lengthTwoChainFrontierWord w == lengthTwoFrontierWord w)
    && (GoertzelLemma818FrontierMode.wordMode (lengthTwoFrontierWord w) ==
      some (lengthTwoFrontierMode w))
    && GoertzelLemma818FrontierMode.modeHasArchivedConnectivityEvidence
      (lengthTwoFrontierMode w)

theorem lengthTwoFrontierBaseAudit_ok
    (w : GoertzelLemma818LengthTwoBase.LengthTwoOrientWord) :
    lengthTwoFrontierBaseAudit w = true := by
  cases w <;>
    simp [lengthTwoFrontierBaseAudit, lengthTwoChainFrontierWord,
      lengthTwoFrontierWord, lengthTwoFrontierMode,
      GoertzelLemma818LengthTwoBase.lengthTwoCertificateAudit_ok] <;>
    decide

def lengthTwoFrontierBaseCoverageAudit : Bool :=
  GoertzelLemma818LengthTwoBase.allLengthTwoOrientWords.all
    lengthTwoFrontierBaseAudit

theorem lengthTwoFrontierBaseCoverageAudit_ok :
    lengthTwoFrontierBaseCoverageAudit = true := by
  simp [lengthTwoFrontierBaseCoverageAudit,
    GoertzelLemma818LengthTwoBase.allLengthTwoOrientWords,
    lengthTwoFrontierBaseAudit_ok]

end GoertzelLemma818FrontierBaseBridge

end Mettapedia.GraphTheory.FourColor
