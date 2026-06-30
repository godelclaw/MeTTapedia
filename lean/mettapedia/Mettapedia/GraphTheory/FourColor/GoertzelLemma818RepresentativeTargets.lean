import Mettapedia.GraphTheory.FourColor.GoertzelLemma818FrontierBaseBridge

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: remaining representative semantic targets

This module names the finite set of frontier modes that still need real
chain-level representative certificates before the DFA induction can imply
all-chain `LKR_in`.  It is a target surface, not a certificate for those
remaining modes.
-/

namespace GoertzelLemma818RepresentativeTargets

open GoertzelLemma818FrontierMode
open GoertzelLemma818FrontierBaseBridge

/--
The fourteen frontier modes not covered by the current real chain-level base
certificates (`T/M/TT/TM/MT/MM`).

Each constructor names one representative word already present in the
frontier-mode DFA table.  The next proof step is to attach generated
per-fixed-input chain certificates to these words.
-/
inductive RepresentativeSemanticTarget
  | mtm
  | mmt
  | mmmt
  | tmt
  | mmm
  | tmm
  | mtmt
  | ttt
  | tmmt
  | ttttm
  | tmmm
  | mtttt
  | mmmm
  | tmtm
  deriving DecidableEq, BEq, Repr, Inhabited

def allRepresentativeSemanticTargets : List RepresentativeSemanticTarget :=
  [ RepresentativeSemanticTarget.mtm
  , RepresentativeSemanticTarget.mmt
  , RepresentativeSemanticTarget.mmmt
  , RepresentativeSemanticTarget.tmt
  , RepresentativeSemanticTarget.mmm
  , RepresentativeSemanticTarget.tmm
  , RepresentativeSemanticTarget.mtmt
  , RepresentativeSemanticTarget.ttt
  , RepresentativeSemanticTarget.tmmt
  , RepresentativeSemanticTarget.ttttm
  , RepresentativeSemanticTarget.tmmm
  , RepresentativeSemanticTarget.mtttt
  , RepresentativeSemanticTarget.mmmm
  , RepresentativeSemanticTarget.tmtm
  ]

def targetFrontierWord :
    RepresentativeSemanticTarget → List TauOrient
  | RepresentativeSemanticTarget.mtm =>
      [TauOrient.mirror, TauOrient.tau, TauOrient.mirror]
  | RepresentativeSemanticTarget.mmt =>
      [TauOrient.mirror, TauOrient.mirror, TauOrient.tau]
  | RepresentativeSemanticTarget.mmmt =>
      [TauOrient.mirror, TauOrient.mirror, TauOrient.mirror, TauOrient.tau]
  | RepresentativeSemanticTarget.tmt =>
      [TauOrient.tau, TauOrient.mirror, TauOrient.tau]
  | RepresentativeSemanticTarget.mmm =>
      [TauOrient.mirror, TauOrient.mirror, TauOrient.mirror]
  | RepresentativeSemanticTarget.tmm =>
      [TauOrient.tau, TauOrient.mirror, TauOrient.mirror]
  | RepresentativeSemanticTarget.mtmt =>
      [TauOrient.mirror, TauOrient.tau, TauOrient.mirror, TauOrient.tau]
  | RepresentativeSemanticTarget.ttt =>
      [TauOrient.tau, TauOrient.tau, TauOrient.tau]
  | RepresentativeSemanticTarget.tmmt =>
      [TauOrient.tau, TauOrient.mirror, TauOrient.mirror, TauOrient.tau]
  | RepresentativeSemanticTarget.ttttm =>
      [TauOrient.tau, TauOrient.tau, TauOrient.tau, TauOrient.tau, TauOrient.mirror]
  | RepresentativeSemanticTarget.tmmm =>
      [TauOrient.tau, TauOrient.mirror, TauOrient.mirror, TauOrient.mirror]
  | RepresentativeSemanticTarget.mtttt =>
      [TauOrient.mirror, TauOrient.tau, TauOrient.tau, TauOrient.tau, TauOrient.tau]
  | RepresentativeSemanticTarget.mmmm =>
      [TauOrient.mirror, TauOrient.mirror, TauOrient.mirror, TauOrient.mirror]
  | RepresentativeSemanticTarget.tmtm =>
      [TauOrient.tau, TauOrient.mirror, TauOrient.tau, TauOrient.mirror]

def targetFrontierMode :
    RepresentativeSemanticTarget → FrontierMode
  | RepresentativeSemanticTarget.mtm => FrontierMode.mode00
  | RepresentativeSemanticTarget.mmt => FrontierMode.mode01
  | RepresentativeSemanticTarget.mmmt => FrontierMode.mode02
  | RepresentativeSemanticTarget.tmt => FrontierMode.mode03
  | RepresentativeSemanticTarget.mmm => FrontierMode.mode05
  | RepresentativeSemanticTarget.tmm => FrontierMode.mode06
  | RepresentativeSemanticTarget.mtmt => FrontierMode.mode08
  | RepresentativeSemanticTarget.ttt => FrontierMode.mode09
  | RepresentativeSemanticTarget.tmmt => FrontierMode.mode12
  | RepresentativeSemanticTarget.ttttm => FrontierMode.mode13
  | RepresentativeSemanticTarget.tmmm => FrontierMode.mode14
  | RepresentativeSemanticTarget.mtttt => FrontierMode.mode15
  | RepresentativeSemanticTarget.mmmm => FrontierMode.mode17
  | RepresentativeSemanticTarget.tmtm => FrontierMode.mode19

def baseCertifiedModes : List FrontierMode :=
  allBaseCertifiedWords.map baseCertifiedFrontierMode

def representativeTargetModes : List FrontierMode :=
  allRepresentativeSemanticTargets.map targetFrontierMode

def representativeTargetAudit (t : RepresentativeSemanticTarget) : Bool :=
  wordMode (targetFrontierWord t) == some (targetFrontierMode t)
    && modeHasArchivedConnectivityEvidence (targetFrontierMode t)
    && !(baseCertifiedModes.contains (targetFrontierMode t))

theorem representativeTargetFrontierWordMode_ok
    (t : RepresentativeSemanticTarget) :
    wordMode (targetFrontierWord t) = some (targetFrontierMode t) := by
  cases t <;> rfl

theorem representativeTargetMode_hasArchivedConnectivityEvidence
    (t : RepresentativeSemanticTarget) :
    modeHasArchivedConnectivityEvidence (targetFrontierMode t) = true := by
  cases t <;> decide

theorem representativeTarget_not_baseCertified
    (t : RepresentativeSemanticTarget) :
    baseCertifiedModes.contains (targetFrontierMode t) = false := by
  cases t <;> decide

theorem representativeTargetAudit_ok
    (t : RepresentativeSemanticTarget) :
    representativeTargetAudit t = true := by
  cases t <;> decide

def representativeTargetCoverageAudit : Bool :=
  allRepresentativeSemanticTargets.all representativeTargetAudit

theorem representativeTargetCoverageAudit_ok :
    representativeTargetCoverageAudit = true := by
  decide

def plannedSemanticModeCoverage (mode : FrontierMode) : Bool :=
  baseCertifiedModes.contains mode || representativeTargetModes.contains mode

def plannedSemanticModeCoverageAudit : Bool :=
  allModes.all plannedSemanticModeCoverage
    && baseCertifiedModes.length == 6
    && representativeTargetModes.length == 14
    && (baseCertifiedModes ++ representativeTargetModes).length == 20

theorem plannedSemanticModeCoverageAudit_ok :
    plannedSemanticModeCoverageAudit = true := by
  decide

end GoertzelLemma818RepresentativeTargets

end Mettapedia.GraphTheory.FourColor
