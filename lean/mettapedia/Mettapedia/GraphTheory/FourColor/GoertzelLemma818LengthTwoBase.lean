import Mettapedia.GraphTheory.FourColor.GoertzelLemma818CompositeCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818CompositeReverseAudit
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TauMirrorCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TauMirrorReverseAudit
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorTauCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorTauReverseAudit
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorMirrorCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorMirrorReverseAudit

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: length-two base certificate surface

This module packages the four generated length-two direct parent/path
certificate tables behind a small finite interface.  It is the base hook for a
future frontier/DFA induction; it is not the all-chain `LKR_in` consequence.

The `tt` certificate also exposes a small real-fiber smoke audit through the
shared `ChainFiberCertificate` checker.  That audit validates generated parent
rows against `allChainStates` fiber indices rather than only against the
generated direct-row list.

It also exposes one reverse-direction smoke audit for the first nonempty `tt`
input fiber.  Parent rows are generated from source to parent, while the real
closure grows from the root outward; the reverse-direction check records the
extra Kempe-step direction needed by a future certificate-to-closure theorem.

The full reverse-direction surfaces are split into generated two-row chunks.
Larger chunks hit Lean's default recursion-depth budget on these tables, so the
named chunk audits are the reusable base for the next closure bridge.
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

def lengthTwoRealFiberSmokeAudit : Bool :=
  GoertzelLemma818CompositeCertificate.ttRealFiberSmokeAudit

def lengthTwoReverseDirectionSmokeAudit : Bool :=
  GoertzelLemma818CompositeCertificate.ttFiber3ReverseCertificateAudit

def lengthTwoTTReverseDirectionAudit : Bool :=
  GoertzelLemma818CompositeReverseAudit.ttReverseAllFiberChunkAudit

def lengthTwoTMReverseDirectionAudit : Bool :=
  GoertzelLemma818TauMirrorReverseAudit.tmReverseAllFiberChunkAudit

def lengthTwoMTReverseDirectionAudit : Bool :=
  GoertzelLemma818MirrorTauReverseAudit.mtReverseAllFiberChunkAudit

def lengthTwoMMReverseDirectionAudit : Bool :=
  GoertzelLemma818MirrorMirrorReverseAudit.mmReverseAllFiberChunkAudit

def lengthTwoReverseDirectionAudit : LengthTwoOrientWord → Bool
  | LengthTwoOrientWord.tt => lengthTwoTTReverseDirectionAudit
  | LengthTwoOrientWord.tm => lengthTwoTMReverseDirectionAudit
  | LengthTwoOrientWord.mt => lengthTwoMTReverseDirectionAudit
  | LengthTwoOrientWord.mm => lengthTwoMMReverseDirectionAudit

def lengthTwoAllReverseDirectionAudit : Bool :=
  allLengthTwoOrientWords.all lengthTwoReverseDirectionAudit

theorem lengthTwoTTReverseDirectionAudit_ok :
    lengthTwoTTReverseDirectionAudit = true := by
  simp [lengthTwoTTReverseDirectionAudit,
    GoertzelLemma818CompositeReverseAudit.ttReverseAllFiberChunkAudit_ok]

theorem lengthTwoTMReverseDirectionAudit_ok :
    lengthTwoTMReverseDirectionAudit = true := by
  simp [lengthTwoTMReverseDirectionAudit,
    GoertzelLemma818TauMirrorReverseAudit.tmReverseAllFiberChunkAudit_ok]

theorem lengthTwoMTReverseDirectionAudit_ok :
    lengthTwoMTReverseDirectionAudit = true := by
  simp [lengthTwoMTReverseDirectionAudit,
    GoertzelLemma818MirrorTauReverseAudit.mtReverseAllFiberChunkAudit_ok]

theorem lengthTwoMMReverseDirectionAudit_ok :
    lengthTwoMMReverseDirectionAudit = true := by
  simp [lengthTwoMMReverseDirectionAudit,
    GoertzelLemma818MirrorMirrorReverseAudit.mmReverseAllFiberChunkAudit_ok]

theorem lengthTwoReverseDirectionAudit_ok (w : LengthTwoOrientWord) :
    lengthTwoReverseDirectionAudit w = true := by
  cases w <;>
    simp [lengthTwoReverseDirectionAudit,
      lengthTwoTTReverseDirectionAudit_ok,
      lengthTwoTMReverseDirectionAudit_ok,
      lengthTwoMTReverseDirectionAudit_ok,
      lengthTwoMMReverseDirectionAudit_ok]

theorem lengthTwoAllReverseDirectionAudit_ok :
    lengthTwoAllReverseDirectionAudit = true := by
  simp [lengthTwoAllReverseDirectionAudit, allLengthTwoOrientWords,
    lengthTwoReverseDirectionAudit_ok]

theorem lengthTwoReverseDirectionSmokeAudit_ok :
    lengthTwoReverseDirectionSmokeAudit = true := by
  simp [lengthTwoReverseDirectionSmokeAudit,
    GoertzelLemma818CompositeCertificate.ttFiber3ReverseCertificateAudit_ok]

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
