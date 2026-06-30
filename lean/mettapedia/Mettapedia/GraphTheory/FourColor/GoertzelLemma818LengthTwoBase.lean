import Mettapedia.GraphTheory.FourColor.GoertzelLemma818CompositeCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TauMirrorCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorTauCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorMirrorCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: length-two base certificate surface

This module packages the four generated length-two direct parent/path
certificate tables behind a small finite interface.  It is the base hook for a
future frontier/DFA induction; it is not the all-chain `LKR_in` consequence.
-/

namespace GoertzelLemma818LengthTwoBase

open GoertzelLemma814

inductive LengthTwoOrientWord
  | tt
  | tm
  | mt
  | mm
  deriving DecidableEq, BEq, Repr, Inhabited

def lengthTwoOrientWord : LengthTwoOrientWord → List TauOrient
  | LengthTwoOrientWord.tt => [TauOrient.normal, TauOrient.normal]
  | LengthTwoOrientWord.tm => [TauOrient.normal, TauOrient.mirror]
  | LengthTwoOrientWord.mt => [TauOrient.mirror, TauOrient.normal]
  | LengthTwoOrientWord.mm => [TauOrient.mirror, TauOrient.mirror]

def lengthTwoCertificateAudit : LengthTwoOrientWord → Bool
  | LengthTwoOrientWord.tt =>
      GoertzelLemma818CompositeCertificate.ttAllFiberCertificateAudit
  | LengthTwoOrientWord.tm =>
      GoertzelLemma818TauMirrorCertificate.tmAllFiberCertificateAudit
  | LengthTwoOrientWord.mt =>
      GoertzelLemma818MirrorTauCertificate.mtAllFiberCertificateAudit
  | LengthTwoOrientWord.mm =>
      GoertzelLemma818MirrorMirrorCertificate.mmAllFiberCertificateAudit

def allLengthTwoOrientWords : List LengthTwoOrientWord :=
  [ LengthTwoOrientWord.tt
  , LengthTwoOrientWord.tm
  , LengthTwoOrientWord.mt
  , LengthTwoOrientWord.mm
  ]

def lengthTwoAllCertificateAudit : Bool :=
  allLengthTwoOrientWords.all lengthTwoCertificateAudit

theorem lengthTwoCertificateAudit_ok (w : LengthTwoOrientWord) :
    lengthTwoCertificateAudit w = true := by
  cases w <;>
    simp [lengthTwoCertificateAudit,
      GoertzelLemma818CompositeCertificate.ttAllFiberCertificateAudit_ok,
      GoertzelLemma818TauMirrorCertificate.tmAllFiberCertificateAudit_ok,
      GoertzelLemma818MirrorTauCertificate.mtAllFiberCertificateAudit_ok,
      GoertzelLemma818MirrorMirrorCertificate.mmAllFiberCertificateAudit_ok]

theorem lengthTwoAllCertificateAudit_ok :
    lengthTwoAllCertificateAudit = true := by
  simp [lengthTwoAllCertificateAudit, allLengthTwoOrientWords,
    lengthTwoCertificateAudit_ok]

end GoertzelLemma818LengthTwoBase

end Mettapedia.GraphTheory.FourColor
