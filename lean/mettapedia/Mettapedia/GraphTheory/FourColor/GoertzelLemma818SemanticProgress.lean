import Mettapedia.GraphTheory.FourColor.GoertzelLemma818SemanticBridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauTargetProgress

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: semantic progress after `TTT`

This module records the checked semantic frontier after the first non-base
representative target is fully certified.  The six base modes remain supplied
by the length-one/length-two chain certificates, and `TTT`/`mode09` is supplied
by the explicit component certificates from
`GoertzelLemma818TripleTauTargetProgress`.

It is a progress frontier for the finite target surface, not the all-chain
`LKR_in` consequence.
-/

namespace GoertzelLemma818SemanticProgress

open GoertzelLemma818FrontierMode
open GoertzelLemma818FrontierBaseBridge
open GoertzelLemma818RepresentativeTargets
open GoertzelLemma818SemanticBridge
open GoertzelLemma818TripleTauTargetProgress

def certifiedRepresentativeTargetsAfterTTT : List RepresentativeSemanticTarget :=
  [RepresentativeSemanticTarget.ttt]

def remainingRepresentativeTargetsAfterTTT : List RepresentativeSemanticTarget :=
  [ RepresentativeSemanticTarget.mtm
  , RepresentativeSemanticTarget.mmt
  , RepresentativeSemanticTarget.mmmt
  , RepresentativeSemanticTarget.tmt
  , RepresentativeSemanticTarget.mmm
  , RepresentativeSemanticTarget.tmm
  , RepresentativeSemanticTarget.mtmt
  , RepresentativeSemanticTarget.tmmt
  , RepresentativeSemanticTarget.ttttm
  , RepresentativeSemanticTarget.tmmm
  , RepresentativeSemanticTarget.mtttt
  , RepresentativeSemanticTarget.mmmm
  , RepresentativeSemanticTarget.tmtm
  ]

def certifiedSemanticModesAfterTTT : List FrontierMode :=
  baseCertifiedModes ++ [FrontierMode.mode09]

def remainingSemanticModesAfterTTT : List FrontierMode :=
  remainingRepresentativeTargetsAfterTTT.map targetFrontierMode

def targetAuditAfterTTT : RepresentativeSemanticTarget → Bool
  | RepresentativeSemanticTarget.ttt => tttTargetCertificateAudit
  | _ => false

theorem targetAuditAfterTTT_ttt_ok :
    targetAuditAfterTTT RepresentativeSemanticTarget.ttt = true := by
  simpa [targetAuditAfterTTT] using tttTargetCertificateAudit_ok

theorem semanticModeAudit_mode09_afterTTT_ok :
    semanticModeAudit targetAuditAfterTTT FrontierMode.mode09 = true := by
  simp [semanticModeAudit, semanticWitnessForMode, semanticWitnessAudit,
    targetAuditAfterTTT_ttt_ok]

theorem semanticModeAudit_base_afterTTT_ok (w : BaseCertifiedWord) :
    semanticModeAudit targetAuditAfterTTT (baseCertifiedFrontierMode w) =
      true := by
  cases w <;>
    simp [semanticModeAudit, semanticWitnessForMode, semanticWitnessAudit,
      baseCertifiedFrontierMode,
      baseCertifiedChainCertificateAudit_ok]

def targetFrontierAfterTTTAudit : Bool :=
  certifiedRepresentativeTargetsAfterTTT.length == 1
    && remainingRepresentativeTargetsAfterTTT.length == 13
    && certifiedRepresentativeTargetsAfterTTT ++
        remainingRepresentativeTargetsAfterTTT ==
      [ RepresentativeSemanticTarget.ttt
      , RepresentativeSemanticTarget.mtm
      , RepresentativeSemanticTarget.mmt
      , RepresentativeSemanticTarget.mmmt
      , RepresentativeSemanticTarget.tmt
      , RepresentativeSemanticTarget.mmm
      , RepresentativeSemanticTarget.tmm
      , RepresentativeSemanticTarget.mtmt
      , RepresentativeSemanticTarget.tmmt
      , RepresentativeSemanticTarget.ttttm
      , RepresentativeSemanticTarget.tmmm
      , RepresentativeSemanticTarget.mtttt
      , RepresentativeSemanticTarget.mmmm
      , RepresentativeSemanticTarget.tmtm
      ]
    && allRepresentativeSemanticTargets.all fun t =>
      certifiedRepresentativeTargetsAfterTTT.contains t ||
        remainingRepresentativeTargetsAfterTTT.contains t
    && remainingRepresentativeTargetsAfterTTT.all fun t =>
      !(certifiedRepresentativeTargetsAfterTTT.contains t)
    && remainingSemanticModesAfterTTT ==
      [ FrontierMode.mode00
      , FrontierMode.mode01
      , FrontierMode.mode02
      , FrontierMode.mode03
      , FrontierMode.mode05
      , FrontierMode.mode06
      , FrontierMode.mode08
      , FrontierMode.mode12
      , FrontierMode.mode13
      , FrontierMode.mode14
      , FrontierMode.mode15
      , FrontierMode.mode17
      , FrontierMode.mode19
      ]

theorem targetFrontierAfterTTTAudit_ok :
    targetFrontierAfterTTTAudit = true := by
  decide

def certifiedSemanticModesFrontierAfterTTTAudit : Bool :=
  certifiedSemanticModesAfterTTT.length == 7
    && remainingSemanticModesAfterTTT.length == 13
    && allModes.all fun mode =>
      certifiedSemanticModesAfterTTT.contains mode ||
        remainingSemanticModesAfterTTT.contains mode
    && remainingSemanticModesAfterTTT.all fun mode =>
      !(certifiedSemanticModesAfterTTT.contains mode)

theorem certifiedSemanticModesFrontierAfterTTTAudit_ok :
    certifiedSemanticModesFrontierAfterTTTAudit = true := by
  decide

def certifiedSemanticModeCertificateAfterTTTAudit : Bool :=
  allBaseCertifiedWords.all fun w =>
      semanticModeAudit targetAuditAfterTTT (baseCertifiedFrontierMode w)
    && semanticModeAudit targetAuditAfterTTT FrontierMode.mode09

theorem certifiedSemanticModeCertificateAfterTTTAudit_ok :
    certifiedSemanticModeCertificateAfterTTTAudit = true := by
  simp [certifiedSemanticModeCertificateAfterTTTAudit, allBaseCertifiedWords,
    semanticModeAudit_base_afterTTT_ok,
    semanticModeAudit_mode09_afterTTT_ok]

def certifiedSemanticModesAfterTTTAudit : Bool :=
  certifiedSemanticModesFrontierAfterTTTAudit
    && certifiedSemanticModeCertificateAfterTTTAudit

theorem certifiedSemanticModesAfterTTTAudit_ok :
    certifiedSemanticModesAfterTTTAudit = true := by
  simp [certifiedSemanticModesAfterTTTAudit,
    certifiedSemanticModesFrontierAfterTTTAudit_ok,
    certifiedSemanticModeCertificateAfterTTTAudit_ok]

def semanticProgressAfterTTTAudit : Bool :=
  targetFrontierAfterTTTAudit
    && certifiedSemanticModesAfterTTTAudit
    && targetAuditAfterTTT RepresentativeSemanticTarget.ttt
    && semanticModeAudit targetAuditAfterTTT FrontierMode.mode09

theorem semanticProgressAfterTTTAudit_ok :
    semanticProgressAfterTTTAudit = true := by
  simp [semanticProgressAfterTTTAudit,
    targetFrontierAfterTTTAudit_ok,
    certifiedSemanticModesAfterTTTAudit_ok,
    targetAuditAfterTTT_ttt_ok,
    semanticModeAudit_mode09_afterTTT_ok]

end GoertzelLemma818SemanticProgress

end Mettapedia.GraphTheory.FourColor
