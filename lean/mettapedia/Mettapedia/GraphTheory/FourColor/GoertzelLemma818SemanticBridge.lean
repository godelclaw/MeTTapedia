import Mettapedia.GraphTheory.FourColor.GoertzelLemma818RepresentativeTargets

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: semantic bridge for the frontier-mode plan

This module is the finite handoff from the profile-mode DFA table to the real
semantic certificate work.  It records, mode by mode, which witness must carry
the actual chain-level certificate: one of the six already checked base words,
or one of the fourteen remaining representative targets.

It does not assert that the remaining target certificates exist.  Instead it
proves the small consequence hook: if those fourteen target audits are supplied,
then every nonempty `tau`/mirror-`tau` word folds to a mode whose planned
semantic audit is true.
-/

namespace GoertzelLemma818SemanticBridge

open GoertzelLemma818FrontierMode
open GoertzelLemma818FrontierBaseBridge
open GoertzelLemma818RepresentativeTargets

def frontierOrientToChain :
    GoertzelLemma818FrontierMode.TauOrient → GoertzelLemma814.TauOrient
  | GoertzelLemma818FrontierMode.TauOrient.tau =>
      GoertzelLemma814.TauOrient.normal
  | GoertzelLemma818FrontierMode.TauOrient.mirror =>
      GoertzelLemma814.TauOrient.mirror

def frontierWordToChainWord
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    List GoertzelLemma814.TauOrient :=
  word.map frontierOrientToChain

inductive SemanticModeWitness
  | base (w : BaseCertifiedWord)
  | target (t : RepresentativeSemanticTarget)
  deriving DecidableEq, BEq, Repr, Inhabited

def semanticWitnessMode : SemanticModeWitness → FrontierMode
  | SemanticModeWitness.base w => baseCertifiedFrontierMode w
  | SemanticModeWitness.target t => targetFrontierMode t

def semanticWitnessFrontierWord :
    SemanticModeWitness → List GoertzelLemma818FrontierMode.TauOrient
  | SemanticModeWitness.base w => baseCertifiedFrontierWord w
  | SemanticModeWitness.target t => targetFrontierWord t

def semanticWitnessChainWord :
    SemanticModeWitness → List GoertzelLemma814.TauOrient
  | SemanticModeWitness.base w => baseCertifiedChainWord w
  | SemanticModeWitness.target t => frontierWordToChainWord (targetFrontierWord t)

def semanticWitnessForMode : FrontierMode → SemanticModeWitness
  | FrontierMode.mode00 => SemanticModeWitness.target RepresentativeSemanticTarget.mtm
  | FrontierMode.mode01 => SemanticModeWitness.target RepresentativeSemanticTarget.mmt
  | FrontierMode.mode02 => SemanticModeWitness.target RepresentativeSemanticTarget.mmmt
  | FrontierMode.mode03 => SemanticModeWitness.target RepresentativeSemanticTarget.tmt
  | FrontierMode.mode04 => SemanticModeWitness.base BaseCertifiedWord.mm
  | FrontierMode.mode05 => SemanticModeWitness.target RepresentativeSemanticTarget.mmm
  | FrontierMode.mode06 => SemanticModeWitness.target RepresentativeSemanticTarget.tmm
  | FrontierMode.mode07 => SemanticModeWitness.base BaseCertifiedWord.t
  | FrontierMode.mode08 => SemanticModeWitness.target RepresentativeSemanticTarget.mtmt
  | FrontierMode.mode09 => SemanticModeWitness.target RepresentativeSemanticTarget.ttt
  | FrontierMode.mode10 => SemanticModeWitness.base BaseCertifiedWord.tt
  | FrontierMode.mode11 => SemanticModeWitness.base BaseCertifiedWord.mt
  | FrontierMode.mode12 => SemanticModeWitness.target RepresentativeSemanticTarget.tmmt
  | FrontierMode.mode13 => SemanticModeWitness.target RepresentativeSemanticTarget.ttttm
  | FrontierMode.mode14 => SemanticModeWitness.target RepresentativeSemanticTarget.tmmm
  | FrontierMode.mode15 => SemanticModeWitness.target RepresentativeSemanticTarget.mtttt
  | FrontierMode.mode16 => SemanticModeWitness.base BaseCertifiedWord.m
  | FrontierMode.mode17 => SemanticModeWitness.target RepresentativeSemanticTarget.mmmm
  | FrontierMode.mode18 => SemanticModeWitness.base BaseCertifiedWord.tm
  | FrontierMode.mode19 => SemanticModeWitness.target RepresentativeSemanticTarget.tmtm

def allSemanticModeWitnesses : List SemanticModeWitness :=
  (allBaseCertifiedWords.map SemanticModeWitness.base) ++
    (allRepresentativeSemanticTargets.map SemanticModeWitness.target)

def semanticWitnessCoverageAudit : Bool :=
  allSemanticModeWitnesses.length == 20
    && allModes.all (fun mode =>
      semanticWitnessMode (semanticWitnessForMode mode) == mode)
    && allModes.all (fun mode =>
      wordMode (semanticWitnessFrontierWord (semanticWitnessForMode mode)) ==
        some mode)
    && allModes.all (fun mode =>
      frontierWordToChainWord
          (semanticWitnessFrontierWord (semanticWitnessForMode mode)) ==
        semanticWitnessChainWord (semanticWitnessForMode mode))

theorem semanticWitnessCoverageAudit_ok :
    semanticWitnessCoverageAudit = true := by
  decide

theorem semanticWitnessForMode_mode_ok (mode : FrontierMode) :
    semanticWitnessMode (semanticWitnessForMode mode) = mode := by
  cases mode <;> rfl

theorem semanticWitnessForMode_wordMode_ok (mode : FrontierMode) :
    wordMode (semanticWitnessFrontierWord (semanticWitnessForMode mode)) =
      some mode := by
  cases mode <;> rfl

theorem semanticWitnessForMode_chainWord_ok (mode : FrontierMode) :
    frontierWordToChainWord
        (semanticWitnessFrontierWord (semanticWitnessForMode mode)) =
      semanticWitnessChainWord (semanticWitnessForMode mode) := by
  cases mode <;> rfl

def semanticPlanStepClosureAudit : Bool :=
  allModes.all (fun mode =>
    allOrientations.all fun orient =>
      semanticWitnessMode (semanticWitnessForMode (step mode orient)) ==
        step mode orient)

theorem semanticPlanStepClosureAudit_ok :
    semanticPlanStepClosureAudit = true := by
  decide

def semanticWitnessAudit
    (targetAudit : RepresentativeSemanticTarget → Bool) :
    SemanticModeWitness → Bool
  | SemanticModeWitness.base w => baseCertifiedChainCertificateAudit w
  | SemanticModeWitness.target t => targetAudit t

def semanticModeAudit
    (targetAudit : RepresentativeSemanticTarget → Bool)
    (mode : FrontierMode) : Bool :=
  semanticWitnessAudit targetAudit (semanticWitnessForMode mode)

def semanticPlanAudit
    (targetAudit : RepresentativeSemanticTarget → Bool) : Bool :=
  allModes.all (semanticModeAudit targetAudit)

theorem semanticModeAudit_ok_of_targets
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hTarget : ∀ t, targetAudit t = true)
    (mode : FrontierMode) :
    semanticModeAudit targetAudit mode = true := by
  cases mode <;>
    simp [semanticModeAudit, semanticWitnessForMode, semanticWitnessAudit,
      baseCertifiedChainCertificateAudit_ok, hTarget]

theorem semanticPlanAudit_ok_of_targets
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hTarget : ∀ t, targetAudit t = true) :
    semanticPlanAudit targetAudit = true := by
  simp [semanticPlanAudit, semanticModeAudit_ok_of_targets hTarget]

theorem semanticModeAudit_initial_ok_of_targets
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hTarget : ∀ t, targetAudit t = true)
    (orient : GoertzelLemma818FrontierMode.TauOrient) :
    semanticModeAudit targetAudit (initialMode orient) = true :=
  semanticModeAudit_ok_of_targets hTarget (initialMode orient)

theorem semanticModeAudit_step_ok_of_targets
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hTarget : ∀ t, targetAudit t = true)
    (mode : FrontierMode)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hmode : semanticModeAudit targetAudit mode = true) :
    semanticModeAudit targetAudit (step mode orient) = true :=
  semanticModeAudit_ok_of_targets hTarget (step mode orient)

/--
Every nonempty orientation word has a planned semantic audit once the fourteen
remaining representative target audits are supplied.

The conclusion is deliberately an audit over the DFA mode, not a claim of
`chainLKRInAudit`: a separate semantic certificate must still show that these
mode audits entail real per-fixed-input Kempe connectivity for the concrete
chain words.
-/
theorem wordMode_hasSemanticModeAudit_of_targets
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hTarget : ∀ t, targetAudit t = true)
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {mode : FrontierMode}
    (hmode : wordMode word = some mode) :
    semanticModeAudit targetAudit mode = true :=
  wordMode_bool_induction
    (semanticModeAudit targetAudit)
    (semanticModeAudit_initial_ok_of_targets hTarget)
    (semanticModeAudit_step_ok_of_targets hTarget)
    hmode

end GoertzelLemma818SemanticBridge

end Mettapedia.GraphTheory.FourColor
