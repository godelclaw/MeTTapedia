import Mettapedia.GraphTheory.FourColor.GoertzelLemma814RealAudit
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818FrontierMode
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoBase
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMRealAudit
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealAudit
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealAudit
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTTRealAudit

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

theorem lengthTwoFrontierState_ok
    (w : GoertzelLemma818LengthTwoBase.LengthTwoOrientWord) :
    GoertzelLemma818FrontierMode.frontierState (lengthTwoFrontierWord w) =
      GoertzelLemma818FrontierMode.FrontierState.active
        (lengthTwoFrontierMode w) := by
  cases w <;> decide

def lengthTwoFrontierBaseAudit
    (w : GoertzelLemma818LengthTwoBase.LengthTwoOrientWord) : Bool :=
  GoertzelLemma818LengthTwoBase.lengthTwoCertificateAudit w
    && (lengthTwoChainFrontierWord w == lengthTwoFrontierWord w)
    && (GoertzelLemma818FrontierMode.wordMode (lengthTwoFrontierWord w) ==
      some (lengthTwoFrontierMode w))
    && (GoertzelLemma818FrontierMode.frontierState (lengthTwoFrontierWord w) ==
      GoertzelLemma818FrontierMode.FrontierState.active
        (lengthTwoFrontierMode w))

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

/--
The frontier modes whose representative words already have real chain-level
per-fixed-input parent/path certificates in Lean.

The remaining frontier modes still only have archived atom/quotient evidence
until representative chain certificates are generated for them.
-/
inductive BaseCertifiedWord
  | t
  | m
  | tt
  | tm
  | mt
  | mm
  deriving DecidableEq, BEq, Repr, Inhabited

def allBaseCertifiedWords : List BaseCertifiedWord :=
  [ BaseCertifiedWord.t
  , BaseCertifiedWord.m
  , BaseCertifiedWord.tt
  , BaseCertifiedWord.tm
  , BaseCertifiedWord.mt
  , BaseCertifiedWord.mm
  ]

def baseCertifiedChainWord : BaseCertifiedWord → List GoertzelLemma814.TauOrient
  | BaseCertifiedWord.t => [GoertzelLemma814.TauOrient.normal]
  | BaseCertifiedWord.m => [GoertzelLemma814.TauOrient.mirror]
  | BaseCertifiedWord.tt =>
      GoertzelLemma818LengthTwoBase.lengthTwoOrientWord
        GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.tt
  | BaseCertifiedWord.tm =>
      GoertzelLemma818LengthTwoBase.lengthTwoOrientWord
        GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.tm
  | BaseCertifiedWord.mt =>
      GoertzelLemma818LengthTwoBase.lengthTwoOrientWord
        GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.mt
  | BaseCertifiedWord.mm =>
      GoertzelLemma818LengthTwoBase.lengthTwoOrientWord
        GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.mm

def baseCertifiedFrontierWord :
    BaseCertifiedWord → List GoertzelLemma818FrontierMode.TauOrient
  | BaseCertifiedWord.t => [GoertzelLemma818FrontierMode.TauOrient.tau]
  | BaseCertifiedWord.m => [GoertzelLemma818FrontierMode.TauOrient.mirror]
  | BaseCertifiedWord.tt =>
      [ GoertzelLemma818FrontierMode.TauOrient.tau
      , GoertzelLemma818FrontierMode.TauOrient.tau
      ]
  | BaseCertifiedWord.tm =>
      [ GoertzelLemma818FrontierMode.TauOrient.tau
      , GoertzelLemma818FrontierMode.TauOrient.mirror
      ]
  | BaseCertifiedWord.mt =>
      [ GoertzelLemma818FrontierMode.TauOrient.mirror
      , GoertzelLemma818FrontierMode.TauOrient.tau
      ]
  | BaseCertifiedWord.mm =>
      [ GoertzelLemma818FrontierMode.TauOrient.mirror
      , GoertzelLemma818FrontierMode.TauOrient.mirror
      ]

def baseCertifiedChainFrontierWord
    (w : BaseCertifiedWord) : List GoertzelLemma818FrontierMode.TauOrient :=
  (baseCertifiedChainWord w).map chainOrientToFrontier

def baseCertifiedFrontierMode :
    BaseCertifiedWord → GoertzelLemma818FrontierMode.FrontierMode
  | BaseCertifiedWord.t => GoertzelLemma818FrontierMode.FrontierMode.mode07
  | BaseCertifiedWord.m => GoertzelLemma818FrontierMode.FrontierMode.mode16
  | BaseCertifiedWord.tt => GoertzelLemma818FrontierMode.FrontierMode.mode10
  | BaseCertifiedWord.tm => GoertzelLemma818FrontierMode.FrontierMode.mode18
  | BaseCertifiedWord.mt => GoertzelLemma818FrontierMode.FrontierMode.mode11
  | BaseCertifiedWord.mm => GoertzelLemma818FrontierMode.FrontierMode.mode04

/--
Base-word chain audit.  The one-gadget normal and mirror cases are checked
against the actual `chainLKRInAudit`; the length-two cases now use their real
`chainLKRInAudit` assemblies rather than only the generated direct certificate
audits.
-/
def baseCertifiedChainCertificateAudit : BaseCertifiedWord → Bool
  | BaseCertifiedWord.t =>
      GoertzelLemma814.chainLKRInAudit [GoertzelLemma814.TauOrient.normal]
  | BaseCertifiedWord.m =>
      GoertzelLemma814.chainLKRInAudit [GoertzelLemma814.TauOrient.mirror]
  | BaseCertifiedWord.tt =>
      GoertzelLemma814.chainLKRInAudit
        GoertzelLemma818CompositeCertificate.ttWord
  | BaseCertifiedWord.tm =>
      GoertzelLemma814.chainLKRInAudit
        GoertzelLemma818TauMirrorCertificate.tmWord
  | BaseCertifiedWord.mt =>
      GoertzelLemma814.chainLKRInAudit
        GoertzelLemma818MirrorTauCertificate.mtWord
  | BaseCertifiedWord.mm =>
      GoertzelLemma814.chainLKRInAudit
        GoertzelLemma818MirrorMirrorCertificate.mmWord

theorem baseCertifiedChainCertificateAudit_ok (w : BaseCertifiedWord) :
    baseCertifiedChainCertificateAudit w = true := by
  cases w <;>
    simp [baseCertifiedChainCertificateAudit,
      GoertzelLemma814RealAudit.tauSingleNormalChainLKRInAudit_ok,
      GoertzelLemma814RealAudit.tauSingleMirrorChainLKRInAudit_ok,
      GoertzelLemma818LengthTwoTTRealAudit.ttChainLKRInAudit_ok,
      GoertzelLemma818LengthTwoTMRealAudit.tmChainLKRInAudit_ok,
      GoertzelLemma818LengthTwoMTRealAudit.mtChainLKRInAudit_ok,
      GoertzelLemma818LengthTwoMMRealAudit.mmChainLKRInAudit_ok]

theorem baseCertifiedChainFrontierWord_eq (w : BaseCertifiedWord) :
    baseCertifiedChainFrontierWord w = baseCertifiedFrontierWord w := by
  cases w <;> rfl

theorem baseCertifiedFrontierWordMode_ok (w : BaseCertifiedWord) :
    GoertzelLemma818FrontierMode.wordMode (baseCertifiedFrontierWord w) =
      some (baseCertifiedFrontierMode w) := by
  cases w <;> rfl

theorem baseCertifiedFrontierState_ok
    (w : BaseCertifiedWord) :
    GoertzelLemma818FrontierMode.frontierState (baseCertifiedFrontierWord w) =
      GoertzelLemma818FrontierMode.FrontierState.active
        (baseCertifiedFrontierMode w) := by
  cases w <;> decide

def baseCertifiedFrontierAudit (w : BaseCertifiedWord) : Bool :=
  baseCertifiedChainCertificateAudit w
    && (baseCertifiedChainFrontierWord w == baseCertifiedFrontierWord w)
    && (GoertzelLemma818FrontierMode.wordMode (baseCertifiedFrontierWord w) ==
      some (baseCertifiedFrontierMode w))
    && (GoertzelLemma818FrontierMode.frontierState (baseCertifiedFrontierWord w) ==
      GoertzelLemma818FrontierMode.FrontierState.active
        (baseCertifiedFrontierMode w))

theorem baseCertifiedFrontierAudit_ok (w : BaseCertifiedWord) :
    baseCertifiedFrontierAudit w = true := by
  cases w <;>
    simp [baseCertifiedFrontierAudit, baseCertifiedChainCertificateAudit_ok,
      baseCertifiedChainFrontierWord, baseCertifiedChainWord,
      baseCertifiedFrontierWord, baseCertifiedFrontierMode] <;>
    decide

def baseCertifiedFrontierCoverageAudit : Bool :=
  allBaseCertifiedWords.all baseCertifiedFrontierAudit

theorem baseCertifiedFrontierCoverageAudit_ok :
    baseCertifiedFrontierCoverageAudit = true := by
  simp [baseCertifiedFrontierCoverageAudit, allBaseCertifiedWords,
    baseCertifiedFrontierAudit_ok]

end GoertzelLemma818FrontierBaseBridge

end Mettapedia.GraphTheory.FourColor
