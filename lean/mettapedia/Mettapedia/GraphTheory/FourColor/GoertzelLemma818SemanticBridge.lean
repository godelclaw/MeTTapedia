import Mettapedia.GraphTheory.FourColor.GoertzelLemma818Fibration
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
open GoertzelLemma818Fibration
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

def semanticFrontierStateAudit
    (targetAudit : RepresentativeSemanticTarget → Bool) :
    FrontierState → Bool
  | FrontierState.empty => true
  | FrontierState.active mode => semanticModeAudit targetAudit mode

theorem semanticFrontierStateAudit_eq_wordMode
    (targetAudit : RepresentativeSemanticTarget → Bool)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    semanticFrontierStateAudit targetAudit (frontierState word) =
      match wordMode word with
      | none => true
      | some mode => semanticModeAudit targetAudit mode := by
  rw [frontierState_eq_wordMode]
  cases wordMode word <;> rfl

theorem semanticFrontierStateAudit_transfer_ok_of_targets
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hTarget : ∀ t, targetAudit t = true)
    (state : FrontierState)
    (orient : GoertzelLemma818FrontierMode.TauOrient) :
    semanticFrontierStateAudit targetAudit (transfer state orient) = true := by
  cases state with
  | empty =>
      cases orient <;>
        simp [semanticFrontierStateAudit, transfer,
          semanticModeAudit_ok_of_targets hTarget]
  | active mode =>
      simpa [semanticFrontierStateAudit, transfer] using
        semanticModeAudit_ok_of_targets hTarget (step mode orient)

theorem frontierState_hasSemanticStateAudit_of_targets
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hTarget : ∀ t, targetAudit t = true)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    semanticFrontierStateAudit targetAudit (frontierState word) = true := by
  rw [semanticFrontierStateAudit_eq_wordMode]
  cases hmode : wordMode word with
  | none =>
      rfl
  | some mode =>
      exact semanticModeAudit_ok_of_targets hTarget mode

def chainAuditForFrontierWord
    (word : List GoertzelLemma818FrontierMode.TauOrient) : Bool :=
  GoertzelLemma814.chainLKRInAudit (frontierWordToChainWord word)

def concreteChainStates
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    List (List GoertzelLemma814.TauState) :=
  GoertzelLemma814.allChainStates (frontierWordToChainWord word)

def concreteChainFiber
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor) :
    List (List GoertzelLemma814.TauState) :=
  GoertzelLemma814.chainFiberFrom
    (frontierWordToChainWord word) (concreteChainStates word) key

def ChainFiberPoint
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor) : Type :=
  { states : List GoertzelLemma814.TauState //
    states ∈ concreteChainFiber word key }

theorem concreteChainFiberPoint_length
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (point : ChainFiberPoint word key) :
    point.1.length = word.length := by
  have hmemStates : point.1 ∈ concreteChainStates word := by
    have hmem := point.2
    unfold concreteChainFiber GoertzelLemma814.chainFiberFrom at hmem
    exact (List.mem_filter.mp hmem).1
  have hlen :=
    GoertzelLemma814.allChainStates_mem_length
      (orients := frontierWordToChainWord word) hmemStates
  simpa [concreteChainStates, frontierWordToChainWord] using hlen

def chainFiberRootState
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor) :
    List GoertzelLemma814.TauState :=
  GoertzelLemma814.listGetD (concreteChainFiber word key) 0 []

def chainFiberRootClosureStep
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor)
    (_x y : ChainFiberPoint word key) : Prop :=
  y.1 ∈ GoertzelLemma814.closeChainFiber
    (frontierWordToChainWord word)
    (concreteChainFiber word key)
    (concreteChainFiber word key).length
    [chainFiberRootState word key]

structure ChainFiberFibrationCertificate
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor) : Type 1 where
  Base : Type
  baseStep : Base → Base → Prop
  proj : ChainFiberPoint word key → Base
  fibration : Fibration (chainFiberRootClosureStep word key) baseStep proj
  baseConnected : Connected baseStep

theorem ChainFiberFibrationCertificate.connected
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (cert : ChainFiberFibrationCertificate word key) :
    Connected (chainFiberRootClosureStep word key) :=
  cert.fibration.totalConnected_of_baseConnected cert.baseConnected

theorem chainFiberRootClosureReach_mem
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    {root : List GoertzelLemma814.TauState}
    {rest : List (List GoertzelLemma814.TauState)}
    (hfiber : concreteChainFiber word key = root :: rest)
    {target : ChainFiberPoint word key}
    (hreach : Reach (chainFiberRootClosureStep word key)
      (⟨root, by simp [hfiber]⟩ : ChainFiberPoint word key)
      target) :
    target.1 ∈ GoertzelLemma814.closeChainFiber
      (frontierWordToChainWord word)
      (concreteChainFiber word key)
      (concreteChainFiber word key).length
      [root] := by
  induction hreach with
  | refl =>
      exact GoertzelLemma814.closeChainFiber_mem_of_seen
        (frontierWordToChainWord word)
        (concreteChainFiber word key)
        (concreteChainFiber word key).length
        [root] root (by simp)
  | tail _ hstep _ =>
      simpa [chainFiberRootClosureStep, chainFiberRootState,
        GoertzelLemma814.listGetD, hfiber] using hstep

theorem chainFiberRootClosureReach_mem_of_mem
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    {x y : ChainFiberPoint word key}
    (hx : x.1 ∈ GoertzelLemma814.closeChainFiber
      (frontierWordToChainWord word)
      (concreteChainFiber word key)
      (concreteChainFiber word key).length
      [chainFiberRootState word key])
    (hreach : Reach (chainFiberRootClosureStep word key) x y) :
    y.1 ∈ GoertzelLemma814.closeChainFiber
      (frontierWordToChainWord word)
      (concreteChainFiber word key)
      (concreteChainFiber word key).length
      [chainFiberRootState word key] := by
  induction hreach with
  | refl =>
      exact hx
  | tail _ hstep _ =>
      simpa [chainFiberRootClosureStep] using hstep

theorem chainFiberConnected_of_rootClosureConnected
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (hconn : Connected (chainFiberRootClosureStep word key)) :
    GoertzelLemma814.chainFiberConnected
      (frontierWordToChainWord word) (concreteChainFiber word key) = true := by
  unfold GoertzelLemma814.chainFiberConnected
  cases hfiber : concreteChainFiber word key with
  | nil =>
      rfl
  | cons root rest =>
      simp only
      rw [List.all_eq_true]
      intro state hmem
      let rootPoint : ChainFiberPoint word key :=
        ⟨root, by simp [hfiber]⟩
      let statePoint : ChainFiberPoint word key :=
        ⟨state, by simpa [hfiber] using hmem⟩
      exact List.contains_iff_mem.mpr
        (by
          simpa [hfiber] using
            chainFiberRootClosureReach_mem hfiber (hconn rootPoint statePoint))

theorem chainFiberConnected_of_fibrationCertificate
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (cert : ChainFiberFibrationCertificate word key) :
    GoertzelLemma814.chainFiberConnected
      (frontierWordToChainWord word) (concreteChainFiber word key) = true :=
  chainFiberConnected_of_rootClosureConnected cert.connected

theorem chainFiberRootClosureConnected_of_chainFiberConnected
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (hconn : GoertzelLemma814.chainFiberConnected
      (frontierWordToChainWord word) (concreteChainFiber word key) = true) :
    Connected (chainFiberRootClosureStep word key) := by
  cases hfiber : concreteChainFiber word key with
  | nil =>
      intro x _y
      have hx : x.1 ∈ ([] : List (List GoertzelLemma814.TauState)) := by
        simpa [hfiber] using x.2
      cases hx
  | cons root rest =>
      intro x y
      have hyMem : y.1 ∈ root :: rest := by
        simpa [hfiber] using y.2
      have hyCloseContains :
          (GoertzelLemma814.closeChainFiber
            (frontierWordToChainWord word)
            (concreteChainFiber word key)
            (concreteChainFiber word key).length
            [root]).contains y.1 = true := by
        unfold GoertzelLemma814.chainFiberConnected at hconn
        rw [hfiber] at hconn
        rw [List.all_eq_true] at hconn
        have hraw := hconn y.1 hyMem
        simpa [hfiber] using hraw
      have hyClose :
          y.1 ∈ GoertzelLemma814.closeChainFiber
            (frontierWordToChainWord word)
            (concreteChainFiber word key)
            (concreteChainFiber word key).length
            [chainFiberRootState word key] := by
        have hyCloseMem := List.contains_iff_mem.mp hyCloseContains
        simpa [chainFiberRootState, GoertzelLemma814.listGetD, hfiber] using
          hyCloseMem
      exact Reach.single (by
        simpa [chainFiberRootClosureStep] using hyClose)

def ChainFiberFibrationCertificate.ofChainFiberConnected
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (hconn : GoertzelLemma814.chainFiberConnected
      (frontierWordToChainWord word) (concreteChainFiber word key) = true) :
    ChainFiberFibrationCertificate word key :=
  let baseStep : Unit → Unit → Prop := fun _ _ => True
  let proj : ChainFiberPoint word key → Unit := fun _ => ()
  let htotal : Connected (chainFiberRootClosureStep word key) :=
    chainFiberRootClosureConnected_of_chainFiberConnected hconn
  let hfibration : Fibration (chainFiberRootClosureStep word key) baseStep proj :=
    { fiberReach := by
        intro x y _
        exact htotal x y
      liftStep := by
        intro x b _
        cases b
        exact ⟨x, rfl, Reach.refl x⟩ }
  let hbase : Connected baseStep := by
    intro x y
    cases x
    cases y
    exact Reach.refl ()
  ChainFiberFibrationCertificate.mk Unit baseStep proj hfibration hbase

structure ChainWordConcreteFibrationCertificate
    (word : List GoertzelLemma818FrontierMode.TauOrient) : Type 1 where
  compatibleStates :
    (concreteChainStates word).all
      (GoertzelLemma814.compatibleChainStates (frontierWordToChainWord word)) =
        true
  fiberCertificate :
    ∀ key : List GoertzelLemma814.LColor,
      key ∈ GoertzelLemma814.colorAssignments4 →
      Nonempty (ChainFiberFibrationCertificate word key)

theorem chainFiberPoint_mem_rootClosure_of_concreteCertificate
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (hcert : Nonempty (ChainWordConcreteFibrationCertificate word))
    (hkey : key ∈ GoertzelLemma814.colorAssignments4)
    (point : ChainFiberPoint word key) :
    point.1 ∈ GoertzelLemma814.closeChainFiber
      (frontierWordToChainWord word)
      (concreteChainFiber word key)
      (concreteChainFiber word key).length
      [chainFiberRootState word key] := by
  rcases hcert with ⟨wordCert⟩
  rcases wordCert.fiberCertificate key hkey with ⟨fiberCert⟩
  let fiber := concreteChainFiber word key
  change point.1 ∈ GoertzelLemma814.closeChainFiber
    (frontierWordToChainWord word) fiber fiber.length
      [chainFiberRootState word key]
  cases hfiber : fiber with
  | nil =>
      have hpoint : point.1 ∈ ([] : List (List GoertzelLemma814.TauState)) := by
        simpa [fiber, hfiber] using point.2
      cases hpoint
  | cons root rest =>
      let rootPoint : ChainFiberPoint word key :=
        ⟨root, by
          simp [fiber, hfiber]⟩
      have hreach : Reach (chainFiberRootClosureStep word key) rootPoint point :=
        fiberCert.connected rootPoint point
      have hfiberConcrete : concreteChainFiber word key = root :: rest := by
        simpa [fiber] using hfiber
      have hmem := chainFiberRootClosureReach_mem hfiberConcrete hreach
      simpa [chainFiberRootState, GoertzelLemma814.listGetD, fiber, hfiber]
        using hmem

theorem emptyConcreteChainStatesCompatible :
    (concreteChainStates []).all
      (GoertzelLemma814.compatibleChainStates (frontierWordToChainWord [])) =
        true := by
  decide

theorem emptyConcreteChainFiberPoint_unique
    (key : List GoertzelLemma814.LColor)
    (x y : ChainFiberPoint [] key) :
    x = y := by
  apply Subtype.ext
  have hx : x.1 = [] := by
    have hxmem := x.2
    simp [concreteChainFiber, concreteChainStates, frontierWordToChainWord,
      GoertzelLemma814.chainFiberFrom, GoertzelLemma814.allChainStates] at hxmem
    exact hxmem.1
  have hy : y.1 = [] := by
    have hymem := y.2
    simp [concreteChainFiber, concreteChainStates, frontierWordToChainWord,
      GoertzelLemma814.chainFiberFrom, GoertzelLemma814.allChainStates] at hymem
    exact hymem.1
  exact hx.trans hy.symm

def emptyConcreteChainFiberFibrationCertificate
    (key : List GoertzelLemma814.LColor) :
    ChainFiberFibrationCertificate [] key :=
  let baseStep : Unit → Unit → Prop := fun _ _ => True
  let proj : ChainFiberPoint [] key → Unit := fun _ => ()
  let hfibration : Fibration (chainFiberRootClosureStep [] key) baseStep proj :=
    { fiberReach := by
        intro x y _
        have hxy : x = y := emptyConcreteChainFiberPoint_unique key x y
        subst hxy
        exact Reach.refl x
      liftStep := by
        intro x b _
        cases b
        exact ⟨x, rfl, Reach.refl x⟩ }
  let hbase : Connected baseStep := by
    intro x y
    cases x
    cases y
    exact Reach.refl ()
  ChainFiberFibrationCertificate.mk Unit baseStep proj hfibration hbase

def emptyConcreteChainWordFibrationCertificate :
    ChainWordConcreteFibrationCertificate [] :=
  { compatibleStates := emptyConcreteChainStatesCompatible
    fiberCertificate := fun key _hkey =>
      ⟨emptyConcreteChainFiberFibrationCertificate key⟩ }

theorem concreteChainWordFibrationEmptyCertificate_ok :
    Nonempty (ChainWordConcreteFibrationCertificate []) :=
  ⟨emptyConcreteChainWordFibrationCertificate⟩

theorem chainAuditForFrontierWord_of_concreteFibrationCertificate
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    (cert : ChainWordConcreteFibrationCertificate word) :
    chainAuditForFrontierWord word = true := by
  unfold chainAuditForFrontierWord GoertzelLemma814.chainLKRInAudit
  change ((concreteChainStates word).all
      (GoertzelLemma814.compatibleChainStates (frontierWordToChainWord word)) &&
    GoertzelLemma814.colorAssignments4.all (fun key =>
      GoertzelLemma814.chainFiberConnected
        (frontierWordToChainWord word) (concreteChainFiber word key))) = true
  simp [cert.compatibleStates]
  intro key _hkey
  rcases cert.fiberCertificate key _hkey with ⟨fiberCert⟩
  exact chainFiberConnected_of_fibrationCertificate fiberCert

def concreteChainAuditFibrationTransferClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      Nonempty (ChainWordConcreteFibrationCertificate (word ++ [orient]))

def concreteChainStatesCompatible
    (word : List GoertzelLemma818FrontierMode.TauOrient) : Prop :=
  (concreteChainStates word).all
    (GoertzelLemma814.compatibleChainStates (frontierWordToChainWord word)) =
      true

def concreteChainStatesAppendCompatibleClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      concreteChainStatesCompatible (word ++ [orient])

def concreteChainStatesGeneratedCompatible : Prop :=
  ∀ word : List GoertzelLemma818FrontierMode.TauOrient,
    concreteChainStatesCompatible word

theorem concreteChainStatesGeneratedCompatible_ok :
    concreteChainStatesGeneratedCompatible := by
  intro word
  unfold concreteChainStatesCompatible concreteChainStates
  exact GoertzelLemma814.allChainStates_compatible (frontierWordToChainWord word)

def concreteChainFiberFibrationTransferClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ key : List GoertzelLemma814.LColor,
        key ∈ GoertzelLemma814.colorAssignments4 →
        Nonempty (ChainFiberFibrationCertificate (word ++ [orient]) key)

def concreteChainFiberFibrationNonemptyTransferClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ key : List GoertzelLemma814.LColor,
        key ∈ GoertzelLemma814.colorAssignments4 →
        Nonempty (ChainFiberFibrationCertificate (word ++ [orient]) key)

def concreteChainStatesAppendPrefixClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
      ∀ states : List GoertzelLemma814.TauState,
        states ∈ concreteChainStates (word ++ [orient]) →
          states.take word.length ∈ concreteChainStates word

theorem concreteChainStatesAppendPrefixClosed_ok :
    concreteChainStatesAppendPrefixClosed := by
  intro word orient hne states hmem
  unfold concreteChainStates at hmem ⊢
  have hchain_ne : frontierWordToChainWord word ≠ [] := by
    cases word with
    | nil =>
        exact False.elim (hne rfl)
    | cons head rest =>
        simp [frontierWordToChainWord]
  have hmem' :
      states ∈ GoertzelLemma814.allChainStates
        (frontierWordToChainWord word ++ [frontierOrientToChain orient]) := by
    simpa [frontierWordToChainWord] using hmem
  have hprefix :=
    GoertzelLemma814.allChainStates_append_singleton_mem_prefix
      (orients := frontierWordToChainWord word)
      (next := frontierOrientToChain orient)
      (states := states)
      hchain_ne hmem'
  simpa [frontierWordToChainWord] using hprefix

def concreteChainInputKeyAppendPrefixClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
      ∀ (states : List GoertzelLemma814.TauState)
        (key : List GoertzelLemma814.LColor),
        GoertzelLemma814.chainInputKey
            (frontierWordToChainWord (word ++ [orient])) states == key →
          GoertzelLemma814.chainInputKey
            (frontierWordToChainWord word) (states.take word.length) == key

theorem concreteChainInputKeyAppendPrefixClosed_ok :
    concreteChainInputKeyAppendPrefixClosed := by
  intro word orient hne states key hkey
  have hchain_ne : frontierWordToChainWord word ≠ [] := by
    cases word with
    | nil =>
        exact False.elim (hne rfl)
    | cons head rest =>
        simp [frontierWordToChainWord]
  have hEq :
      GoertzelLemma814.chainInputKey
          (frontierWordToChainWord word) (states.take word.length) =
        GoertzelLemma814.chainInputKey
          (frontierWordToChainWord (word ++ [orient])) states := by
    simpa [frontierWordToChainWord] using
      (GoertzelLemma814.chainInputKey_append_prefix_take
        (frontierWordToChainWord word) (frontierOrientToChain orient)
        states hchain_ne)
  rw [hEq]
  exact hkey

def concreteChainFiberAppendPrefixClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
      ∀ (key : List GoertzelLemma814.LColor)
        (states : List GoertzelLemma814.TauState),
        states ∈ concreteChainFiber (word ++ [orient]) key →
          states.take word.length ∈ concreteChainFiber word key

theorem concreteChainFiberAppendPrefixClosed_of_states_and_key
    (hStates : concreteChainStatesAppendPrefixClosed)
    (hKey : concreteChainInputKeyAppendPrefixClosed) :
    concreteChainFiberAppendPrefixClosed := by
  intro word orient hne key states hmem
  unfold concreteChainFiber GoertzelLemma814.chainFiberFrom at hmem ⊢
  rw [List.mem_filter] at hmem
  rw [List.mem_filter]
  exact
    ⟨hStates word orient hne states hmem.1,
      hKey word orient hne states key hmem.2⟩

theorem concreteChainFiberAppendPrefixClosed_of_states
    (hStates : concreteChainStatesAppendPrefixClosed) :
    concreteChainFiberAppendPrefixClosed :=
  concreteChainFiberAppendPrefixClosed_of_states_and_key
    hStates concreteChainInputKeyAppendPrefixClosed_ok

theorem concreteChainFiberAppendPrefixClosed_ok :
    concreteChainFiberAppendPrefixClosed :=
  concreteChainFiberAppendPrefixClosed_of_states
    concreteChainStatesAppendPrefixClosed_ok

structure ChainFiberAppendProjection
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor) : Type where
  prefixPoint :
    ChainFiberPoint (word ++ [orient]) key → ChainFiberPoint word key

structure ChainFiberAppendFibrationLift
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor) : Type where
  projection : ChainFiberAppendProjection word orient key
  fibration :
    Fibration
      (chainFiberRootClosureStep (word ++ [orient]) key)
      (chainFiberRootClosureStep word key)
      projection.prefixPoint

def concreteChainFiberAppendFibrationLiftClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ key : List GoertzelLemma814.LColor,
        key ∈ GoertzelLemma814.colorAssignments4 →
        Nonempty (ChainFiberAppendFibrationLift word orient key)

def concreteChainFiberAppendProjectionClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ key : List GoertzelLemma814.LColor,
        key ∈ GoertzelLemma814.colorAssignments4 →
        Nonempty (ChainFiberAppendProjection word orient key)

def concreteChainFiberAppendFibrationOverProjectionClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ projection : ChainFiberAppendProjection word orient key,
            Fibration
              (chainFiberRootClosureStep (word ++ [orient]) key)
              (chainFiberRootClosureStep word key)
              projection.prefixPoint

def concreteChainFiberAppendPrefixProjection
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ [])
    (key : List GoertzelLemma814.LColor) :
    ChainFiberAppendProjection word orient key :=
  { prefixPoint := fun point =>
      ⟨point.1.take word.length,
        concreteChainFiberAppendPrefixClosed_ok
          word orient hne key point.1 point.2⟩ }

@[simp] theorem concreteChainFiberAppendPrefixProjection_value
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ [])
    (key : List GoertzelLemma814.LColor)
    (point : ChainFiberPoint (word ++ [orient]) key) :
    ((concreteChainFiberAppendPrefixProjection word orient hne key).prefixPoint
      point).1 = point.1.take word.length :=
  rfl

theorem concreteChainFiberAppendPoint_mem_split
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ [])
    (key : List GoertzelLemma814.LColor)
    (point : ChainFiberPoint (word ++ [orient]) key) :
    ∃ pref last,
      pref ∈ concreteChainFiber word key ∧
        last ∈ GoertzelLemma814.allTauStates ∧
        GoertzelLemma814.compatibleAdjacent
          (GoertzelLemma814.tauOrientAt
            (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
          (GoertzelLemma814.tauOrientAt
            (frontierWordToChainWord (word ++ [orient])) word.length)
          (GoertzelLemma814.chainStateAt pref (word.length - 1)) last = true ∧
        point.1 = pref ++ [last] ∧
        pref = point.1.take word.length := by
  have hmemStates : point.1 ∈ concreteChainStates (word ++ [orient]) := by
    have hmem := point.2
    unfold concreteChainFiber GoertzelLemma814.chainFiberFrom at hmem
    exact (List.mem_filter.mp hmem).1
  have hchain_ne : frontierWordToChainWord word ≠ [] := by
    cases word with
    | nil =>
        exact False.elim (hne rfl)
    | cons head rest =>
        simp [frontierWordToChainWord]
  have hmemStates' :
      point.1 ∈ GoertzelLemma814.allChainStates
        (frontierWordToChainWord word ++ [frontierOrientToChain orient]) := by
    simpa [concreteChainStates, frontierWordToChainWord] using hmemStates
  rcases GoertzelLemma814.allChainStates_append_singleton_mem_split
      (orients := frontierWordToChainWord word)
      (next := frontierOrientToChain orient)
      (states := point.1)
      hchain_ne hmemStates' with
    ⟨pref, last, hprefStates, hlast, hcompatible, hpoint⟩
  have hprefLen : pref.length = word.length := by
    have hlen :=
      GoertzelLemma814.allChainStates_mem_length
        (orients := frontierWordToChainWord word) hprefStates
    simpa [frontierWordToChainWord] using hlen
  have htake : point.1.take word.length = pref := by
    rw [hpoint, ← hprefLen]
    simp
  have hprefFiber : pref ∈ concreteChainFiber word key := by
    have hprefTake :=
      concreteChainFiberAppendPrefixClosed_ok
        word orient hne key point.1 point.2
    simpa [htake] using hprefTake
  refine ⟨pref, last, hprefFiber, hlast, ?_, hpoint, htake.symm⟩
  simpa [frontierWordToChainWord] using hcompatible

theorem concreteChainFiberAppend_mem_of_prefix_last
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ [])
    (key : List GoertzelLemma814.LColor)
    {pref : List GoertzelLemma814.TauState}
    {last : GoertzelLemma814.TauState}
    (hpref : pref ∈ concreteChainFiber word key)
    (hlast : last ∈ GoertzelLemma814.allTauStates)
    (hcompatible : GoertzelLemma814.compatibleAdjacent
      (GoertzelLemma814.tauOrientAt
        (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
      (GoertzelLemma814.tauOrientAt
        (frontierWordToChainWord (word ++ [orient])) word.length)
      (GoertzelLemma814.chainStateAt pref (word.length - 1)) last = true) :
    pref ++ [last] ∈ concreteChainFiber (word ++ [orient]) key := by
  unfold concreteChainFiber GoertzelLemma814.chainFiberFrom at hpref ⊢
  rw [List.mem_filter] at hpref ⊢
  have hchain_ne : frontierWordToChainWord word ≠ [] := by
    cases word with
    | nil =>
        exact False.elim (hne rfl)
    | cons head rest =>
        simp [frontierWordToChainWord]
  have hprefStates :
      pref ∈ GoertzelLemma814.allChainStates (frontierWordToChainWord word) := by
    simpa [concreteChainStates] using hpref.1
  have hprefLen : pref.length = word.length := by
    have hlen :=
      GoertzelLemma814.allChainStates_mem_length
        (orients := frontierWordToChainWord word) hprefStates
    simpa [frontierWordToChainWord] using hlen
  constructor
  · have hstates :
        pref ++ [last] ∈ GoertzelLemma814.allChainStates
          (frontierWordToChainWord word ++ [frontierOrientToChain orient]) :=
      GoertzelLemma814.allChainStates_append_singleton_mem_of_split
        (orients := frontierWordToChainWord word)
        (next := frontierOrientToChain orient)
        (pref := pref) (last := last)
        hchain_ne hprefStates hlast
        (by simpa [frontierWordToChainWord] using hcompatible)
    simpa [concreteChainStates, frontierWordToChainWord] using hstates
  · have hchainLen :
        (frontierWordToChainWord word).length = pref.length := by
      rw [hprefLen]
      simp [frontierWordToChainWord]
    have htake :
        (pref ++ [last]).take (frontierWordToChainWord word).length = pref := by
      rw [hchainLen]
      simp
    have hinput :
        GoertzelLemma814.chainInputKey (frontierWordToChainWord word) pref =
          GoertzelLemma814.chainInputKey
            (frontierWordToChainWord word ++ [frontierOrientToChain orient])
            (pref ++ [last]) := by
      simpa [htake] using
        (GoertzelLemma814.chainInputKey_append_prefix_take
          (frontierWordToChainWord word) (frontierOrientToChain orient)
          (pref ++ [last]) hchain_ne)
    have hkey :
        (GoertzelLemma814.chainInputKey
            (frontierWordToChainWord word ++ [frontierOrientToChain orient])
            (pref ++ [last]) == key) = true := by
      rw [← hinput]
      exact hpref.2
    simpa [frontierWordToChainWord] using hkey

theorem concreteChainFiberAppendPrefixProjection_eq_iff_take
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ [])
    (key : List GoertzelLemma814.LColor)
    (x y : ChainFiberPoint (word ++ [orient]) key) :
    (concreteChainFiberAppendPrefixProjection word orient hne key).prefixPoint x =
      (concreteChainFiberAppendPrefixProjection word orient hne key).prefixPoint y ↔
        x.1.take word.length = y.1.take word.length := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

def concreteChainFiberAppendPrefixFiberReachClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ x y : ChainFiberPoint (word ++ [orient]) key,
            (concreteChainFiberAppendPrefixProjection word orient hne key).prefixPoint x =
              (concreteChainFiberAppendPrefixProjection word orient hne key).prefixPoint y →
                Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y

def concreteChainFiberAppendRawPrefixReachClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ x y : ChainFiberPoint (word ++ [orient]) key,
            x.1.take word.length = y.1.take word.length →
              Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y

def concreteChainFiberAppendLastInterfaceTrace
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (last : GoertzelLemma814.TauState) : List GoertzelLemma814.LColor :=
  (GoertzelLemma814.tauOrientOutputOrder (frontierOrientToChain orient)).map
    fun edge => last.color edge

def concreteChainFiberAppendFixedPrefixLastReachClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX lastY : GoertzelLemma814.TauState),
            (hpref : pref ∈ concreteChainFiber word key) →
            (hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (hlastY : lastY ∈ GoertzelLemma814.allTauStates) →
            (hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            (hcompatibleY : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastY = true) →
              Reach (chainFiberRootClosureStep (word ++ [orient]) key)
                (⟨pref ++ [lastX],
                  concreteChainFiberAppend_mem_of_prefix_last
                    word orient hne key hpref hlastX hcompatibleX⟩ :
                  ChainFiberPoint (word ++ [orient]) key)
                (⟨pref ++ [lastY],
                  concreteChainFiberAppend_mem_of_prefix_last
                    word orient hne key hpref hlastY hcompatibleY⟩ :
                  ChainFiberPoint (word ++ [orient]) key)

def concreteChainFiberAppendFixedPrefixSameInterfaceTraceReachClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX lastY : GoertzelLemma814.TauState),
            (hpref : pref ∈ concreteChainFiber word key) →
            (hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (hlastY : lastY ∈ GoertzelLemma814.allTauStates) →
            (hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            (hcompatibleY : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastY = true) →
            concreteChainFiberAppendLastInterfaceTrace orient lastX =
              concreteChainFiberAppendLastInterfaceTrace orient lastY →
              Reach (chainFiberRootClosureStep (word ++ [orient]) key)
                (⟨pref ++ [lastX],
                  concreteChainFiberAppend_mem_of_prefix_last
                    word orient hne key hpref hlastX hcompatibleX⟩ :
                  ChainFiberPoint (word ++ [orient]) key)
                (⟨pref ++ [lastY],
                  concreteChainFiberAppend_mem_of_prefix_last
                    word orient hne key hpref hlastY hcompatibleY⟩ :
                  ChainFiberPoint (word ++ [orient]) key)

def concreteChainFiberAppendFixedPrefixInterfaceMobilityReachClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX lastY : GoertzelLemma814.TauState),
            (hpref : pref ∈ concreteChainFiber word key) →
            (hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (hlastY : lastY ∈ GoertzelLemma814.allTauStates) →
            (hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            (hcompatibleY : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastY = true) →
            concreteChainFiberAppendLastInterfaceTrace orient lastX ≠
              concreteChainFiberAppendLastInterfaceTrace orient lastY →
              Reach (chainFiberRootClosureStep (word ++ [orient]) key)
                (⟨pref ++ [lastX],
                  concreteChainFiberAppend_mem_of_prefix_last
                    word orient hne key hpref hlastX hcompatibleX⟩ :
                  ChainFiberPoint (word ++ [orient]) key)
                (⟨pref ++ [lastY],
                  concreteChainFiberAppend_mem_of_prefix_last
                    word orient hne key hpref hlastY hcompatibleY⟩ :
                  ChainFiberPoint (word ++ [orient]) key)

theorem concreteChainFiberAppendFixedPrefixLastReachClosed_of_interface_trace_cases
    (hSame : concreteChainFiberAppendFixedPrefixSameInterfaceTraceReachClosed)
    (hMobility : concreteChainFiberAppendFixedPrefixInterfaceMobilityReachClosed) :
    concreteChainFiberAppendFixedPrefixLastReachClosed := by
  intro word orient hne hcert key hkey pref lastX lastY hpref hlastX hlastY
    hcompatibleX hcompatibleY
  by_cases htrace :
      concreteChainFiberAppendLastInterfaceTrace orient lastX =
        concreteChainFiberAppendLastInterfaceTrace orient lastY
  · exact hSame word orient hne hcert key hkey pref lastX lastY
      hpref hlastX hlastY hcompatibleX hcompatibleY htrace
  · exact hMobility word orient hne hcert key hkey pref lastX lastY
      hpref hlastX hlastY hcompatibleX hcompatibleY htrace

theorem concreteChainFiberAppendRawPrefixReachClosed_of_fixed_prefix_last_reach
    (hLast : concreteChainFiberAppendFixedPrefixLastReachClosed) :
    concreteChainFiberAppendRawPrefixReachClosed := by
  intro word orient hne hcert key hkey x y htake
  rcases concreteChainFiberAppendPoint_mem_split word orient hne key x with
    ⟨prefX, lastX, hprefX, hlastX, hcompatibleX, hxValue, hxPrefix⟩
  rcases concreteChainFiberAppendPoint_mem_split word orient hne key y with
    ⟨prefY, lastY, _hprefY, hlastY, hcompatibleY, hyValue, hyPrefix⟩
  have hpref : prefX = prefY := by
    rw [hxPrefix, hyPrefix]
    exact htake
  have hcompatibleY' :
      GoertzelLemma814.compatibleAdjacent
        (GoertzelLemma814.tauOrientAt
          (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
        (GoertzelLemma814.tauOrientAt
          (frontierWordToChainWord (word ++ [orient])) word.length)
        (GoertzelLemma814.chainStateAt prefX (word.length - 1)) lastY =
        true := by
    simpa [hpref] using hcompatibleY
  have hyValue' : y.1 = prefX ++ [lastY] := by
    simpa [hpref] using hyValue
  let x' : ChainFiberPoint (word ++ [orient]) key :=
    ⟨prefX ++ [lastX],
      concreteChainFiberAppend_mem_of_prefix_last
        word orient hne key hprefX hlastX hcompatibleX⟩
  let y' : ChainFiberPoint (word ++ [orient]) key :=
    ⟨prefX ++ [lastY],
      concreteChainFiberAppend_mem_of_prefix_last
        word orient hne key hprefX hlastY hcompatibleY'⟩
  have hxEq : x = x' := by
    exact Subtype.ext (by simpa [x'] using hxValue)
  have hyEq : y = y' := by
    exact Subtype.ext (by simpa [y'] using hyValue')
  have hreach :=
    hLast word orient hne hcert key hkey prefX lastX lastY
      hprefX hlastX hlastY hcompatibleX hcompatibleY'
  rw [hxEq, hyEq]
  simpa [x', y'] using hreach

theorem concreteChainFiberAppendRawPrefixReachClosed_of_interface_trace_cases
    (hSame : concreteChainFiberAppendFixedPrefixSameInterfaceTraceReachClosed)
    (hMobility : concreteChainFiberAppendFixedPrefixInterfaceMobilityReachClosed) :
    concreteChainFiberAppendRawPrefixReachClosed :=
  concreteChainFiberAppendRawPrefixReachClosed_of_fixed_prefix_last_reach
    (concreteChainFiberAppendFixedPrefixLastReachClosed_of_interface_trace_cases
      hSame hMobility)

theorem concreteChainFiberAppendPrefixFiberReachClosed_of_raw
    (hRaw : concreteChainFiberAppendRawPrefixReachClosed) :
    concreteChainFiberAppendPrefixFiberReachClosed := by
  intro word orient hne hcert key hkey x y hproj
  exact hRaw word orient hne hcert key hkey x y
    ((concreteChainFiberAppendPrefixProjection_eq_iff_take
      word orient hne key x y).mp hproj)

theorem concreteChainFiberAppendRawPrefixReachClosed_of_projection
    (hProjection : concreteChainFiberAppendPrefixFiberReachClosed) :
    concreteChainFiberAppendRawPrefixReachClosed := by
  intro word orient hne hcert key hkey x y htake
  exact hProjection word orient hne hcert key hkey x y
    ((concreteChainFiberAppendPrefixProjection_eq_iff_take
      word orient hne key x y).mpr htake)

def concreteChainFiberAppendPrefixLiftStepClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (x : ChainFiberPoint (word ++ [orient]) key)
            (b : ChainFiberPoint word key),
            chainFiberRootClosureStep word key
              ((concreteChainFiberAppendPrefixProjection
                word orient hne key).prefixPoint x) b →
              ∃ y : ChainFiberPoint (word ++ [orient]) key,
                (concreteChainFiberAppendPrefixProjection
                  word orient hne key).prefixPoint y = b ∧
                  Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y

def concreteChainFiberAppendPrefixFiberClosureClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ x y : ChainFiberPoint (word ++ [orient]) key,
            (concreteChainFiberAppendPrefixProjection word orient hne key).prefixPoint x =
              (concreteChainFiberAppendPrefixProjection word orient hne key).prefixPoint y →
                y.1 ∈ GoertzelLemma814.closeChainFiber
                  (frontierWordToChainWord (word ++ [orient]))
                  (concreteChainFiber (word ++ [orient]) key)
                  (concreteChainFiber (word ++ [orient]) key).length
                  [chainFiberRootState (word ++ [orient]) key]

def concreteChainFiberAppendPrefixLiftClosureClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (x : ChainFiberPoint (word ++ [orient]) key)
            (b : ChainFiberPoint word key),
            chainFiberRootClosureStep word key
              ((concreteChainFiberAppendPrefixProjection
                word orient hne key).prefixPoint x) b →
              ∃ y : ChainFiberPoint (word ++ [orient]) key,
                (concreteChainFiberAppendPrefixProjection
                  word orient hne key).prefixPoint y = b ∧
                  y.1 ∈ GoertzelLemma814.closeChainFiber
                    (frontierWordToChainWord (word ++ [orient]))
                    (concreteChainFiber (word ++ [orient]) key)
                    (concreteChainFiber (word ++ [orient]) key).length
                    [chainFiberRootState (word ++ [orient]) key]

def concreteChainFiberAppendPrefixSelfLiftClosureClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ x : ChainFiberPoint (word ++ [orient]) key,
            ∃ y : ChainFiberPoint (word ++ [orient]) key,
              (concreteChainFiberAppendPrefixProjection
                word orient hne key).prefixPoint y =
                  (concreteChainFiberAppendPrefixProjection
                    word orient hne key).prefixPoint x ∧
              y.1 ∈ GoertzelLemma814.closeChainFiber
                (frontierWordToChainWord (word ++ [orient]))
                (concreteChainFiber (word ++ [orient]) key)
                (concreteChainFiber (word ++ [orient]) key).length
                [chainFiberRootState (word ++ [orient]) key]

def concreteChainFiberAppendSamePrefixClosureTransferClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ x y : ChainFiberPoint (word ++ [orient]) key,
            (concreteChainFiberAppendPrefixProjection word orient hne key).prefixPoint x =
              (concreteChainFiberAppendPrefixProjection word orient hne key).prefixPoint y →
            x.1 ∈ GoertzelLemma814.closeChainFiber
              (frontierWordToChainWord (word ++ [orient]))
              (concreteChainFiber (word ++ [orient]) key)
              (concreteChainFiber (word ++ [orient]) key).length
              [chainFiberRootState (word ++ [orient]) key] →
            y.1 ∈ GoertzelLemma814.closeChainFiber
              (frontierWordToChainWord (word ++ [orient]))
              (concreteChainFiber (word ++ [orient]) key)
              (concreteChainFiber (word ++ [orient]) key).length
              [chainFiberRootState (word ++ [orient]) key]

def concreteChainFiberAppendPrefixRootClosureLiftClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ b : ChainFiberPoint word key,
            b.1 ∈ GoertzelLemma814.closeChainFiber
              (frontierWordToChainWord word)
              (concreteChainFiber word key)
              (concreteChainFiber word key).length
              [chainFiberRootState word key] →
            ∃ y : ChainFiberPoint (word ++ [orient]) key,
              (concreteChainFiberAppendPrefixProjection
                word orient hne key).prefixPoint y = b ∧
              y.1 ∈ GoertzelLemma814.closeChainFiber
                (frontierWordToChainWord (word ++ [orient]))
                (concreteChainFiber (word ++ [orient]) key)
                (concreteChainFiber (word ++ [orient]) key).length
                [chainFiberRootState (word ++ [orient]) key]

def concreteChainFiberAppendPrefixPointClosureLiftClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ b : ChainFiberPoint word key,
            ∃ y : ChainFiberPoint (word ++ [orient]) key,
              (concreteChainFiberAppendPrefixProjection
                word orient hne key).prefixPoint y = b ∧
              y.1 ∈ GoertzelLemma814.closeChainFiber
                (frontierWordToChainWord (word ++ [orient]))
                (concreteChainFiber (word ++ [orient]) key)
                (concreteChainFiber (word ++ [orient]) key).length
                [chainFiberRootState (word ++ [orient]) key]

theorem concreteChainFiberAppendPrefixPointClosureLiftClosed_of_root_lift
    (hLift : concreteChainFiberAppendPrefixRootClosureLiftClosed) :
    concreteChainFiberAppendPrefixPointClosureLiftClosed := by
  intro word orient hne hcert key hkey b
  exact hLift word orient hne hcert key hkey b
    (chainFiberPoint_mem_rootClosure_of_concreteCertificate hcert hkey b)

theorem concreteChainFiberAppendPrefixRootClosureLiftClosed_of_point_lift
    (hLift : concreteChainFiberAppendPrefixPointClosureLiftClosed) :
    concreteChainFiberAppendPrefixRootClosureLiftClosed := by
  intro word orient hne hcert key hkey b _hbClose
  exact hLift word orient hne hcert key hkey b

theorem concreteChainFiberAppendPrefixLiftClosureClosed_of_root_lift
    (hLift : concreteChainFiberAppendPrefixRootClosureLiftClosed) :
    concreteChainFiberAppendPrefixLiftClosureClosed := by
  intro word orient hne hcert key hkey _x b hroot
  exact hLift word orient hne hcert key hkey b
    (by simpa [chainFiberRootClosureStep] using hroot)

theorem concreteChainFiberAppendPrefixLiftClosureClosed_of_point_lift
    (hLift : concreteChainFiberAppendPrefixPointClosureLiftClosed) :
    concreteChainFiberAppendPrefixLiftClosureClosed := by
  intro word orient hne hcert key hkey _x b _hroot
  exact hLift word orient hne hcert key hkey b

theorem concreteChainFiberAppendSamePrefixClosureTransferClosed_of_reach
    (hReach : concreteChainFiberAppendPrefixFiberReachClosed) :
    concreteChainFiberAppendSamePrefixClosureTransferClosed := by
  intro word orient hne hcert key hkey x y hxy hxClose
  exact chainFiberRootClosureReach_mem_of_mem
    (word := word ++ [orient]) (key := key)
    hxClose (hReach word orient hne hcert key hkey x y hxy)

theorem concreteChainFiberAppendPrefixSelfLiftClosureClosed_of_lift
    (hLift : concreteChainFiberAppendPrefixLiftClosureClosed) :
    concreteChainFiberAppendPrefixSelfLiftClosureClosed := by
  intro word orient hne hcert key hkey x
  let prefixProjection :=
    (concreteChainFiberAppendPrefixProjection word orient hne key).prefixPoint x
  have hprefixClose :
      chainFiberRootClosureStep word key prefixProjection prefixProjection := by
    exact chainFiberPoint_mem_rootClosure_of_concreteCertificate
      hcert hkey prefixProjection
  exact hLift word orient hne hcert key hkey x prefixProjection hprefixClose

theorem concreteChainFiberAppendPrefixFiberClosureClosed_of_self_lift_and_same_prefix
    (hSelf : concreteChainFiberAppendPrefixSelfLiftClosureClosed)
    (hSame : concreteChainFiberAppendSamePrefixClosureTransferClosed) :
    concreteChainFiberAppendPrefixFiberClosureClosed := by
  intro word orient hne hcert key hkey x y hxy
  rcases hSelf word orient hne hcert key hkey x with
    ⟨x₀, hx₀Proj, hx₀Close⟩
  exact hSame word orient hne hcert key hkey x₀ y (by
    exact hx₀Proj.trans hxy) hx₀Close

theorem concreteChainFiberAppendPrefixFiberClosureClosed_of_lift_and_same_prefix
    (hLift : concreteChainFiberAppendPrefixLiftClosureClosed)
    (hSame : concreteChainFiberAppendSamePrefixClosureTransferClosed) :
    concreteChainFiberAppendPrefixFiberClosureClosed :=
  concreteChainFiberAppendPrefixFiberClosureClosed_of_self_lift_and_same_prefix
    (concreteChainFiberAppendPrefixSelfLiftClosureClosed_of_lift hLift)
    hSame

theorem concreteChainFiberAppendPrefixFiberReachClosed_of_closure
    (hClosure : concreteChainFiberAppendPrefixFiberClosureClosed) :
    concreteChainFiberAppendPrefixFiberReachClosed := by
  intro word orient hne hcert key hkey x y hproj
  exact Reach.single (by
    simpa [chainFiberRootClosureStep] using
      hClosure word orient hne hcert key hkey x y hproj)

theorem concreteChainFiberAppendPrefixLiftStepClosed_of_closure
    (hClosure : concreteChainFiberAppendPrefixLiftClosureClosed) :
    concreteChainFiberAppendPrefixLiftStepClosed := by
  intro word orient hne hcert key hkey x b hstep
  rcases hClosure word orient hne hcert key hkey x b hstep with
    ⟨y, hyProj, hyClose⟩
  exact ⟨y, hyProj, Reach.single (by
    simpa [chainFiberRootClosureStep] using hyClose)⟩

def concreteChainFiberAppendPrefixFibrationClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          Fibration
            (chainFiberRootClosureStep (word ++ [orient]) key)
            (chainFiberRootClosureStep word key)
            (concreteChainFiberAppendPrefixProjection
              word orient hne key).prefixPoint

theorem concreteChainFiberAppendPrefixFibrationClosed_of_fields
    (hFiber : concreteChainFiberAppendPrefixFiberReachClosed)
    (hLift : concreteChainFiberAppendPrefixLiftStepClosed) :
    concreteChainFiberAppendPrefixFibrationClosed := by
  intro word orient hne hcert key hkey
  exact
    { fiberReach := hFiber word orient hne hcert key hkey
      liftStep := hLift word orient hne hcert key hkey }

theorem concreteChainFiberAppendPrefixFibrationClosed_of_closure
    (hFiber : concreteChainFiberAppendPrefixFiberClosureClosed)
    (hLift : concreteChainFiberAppendPrefixLiftClosureClosed) :
    concreteChainFiberAppendPrefixFibrationClosed :=
  concreteChainFiberAppendPrefixFibrationClosed_of_fields
    (concreteChainFiberAppendPrefixFiberReachClosed_of_closure hFiber)
    (concreteChainFiberAppendPrefixLiftStepClosed_of_closure hLift)

theorem concreteChainFiberAppendPrefixFibrationClosed_of_lift_and_same_prefix
    (hLift : concreteChainFiberAppendPrefixLiftClosureClosed)
    (hSame : concreteChainFiberAppendSamePrefixClosureTransferClosed) :
    concreteChainFiberAppendPrefixFibrationClosed :=
  concreteChainFiberAppendPrefixFibrationClosed_of_closure
    (concreteChainFiberAppendPrefixFiberClosureClosed_of_lift_and_same_prefix
      hLift hSame)
    hLift

theorem concreteChainFiberAppendPrefixFibrationClosed_of_root_lift_and_same_prefix_reach
    (hLift : concreteChainFiberAppendPrefixRootClosureLiftClosed)
    (hReach : concreteChainFiberAppendPrefixFiberReachClosed) :
    concreteChainFiberAppendPrefixFibrationClosed :=
  concreteChainFiberAppendPrefixFibrationClosed_of_lift_and_same_prefix
    (concreteChainFiberAppendPrefixLiftClosureClosed_of_root_lift hLift)
    (concreteChainFiberAppendSamePrefixClosureTransferClosed_of_reach hReach)

theorem concreteChainFiberAppendPrefixFibrationClosed_of_point_lift_and_same_prefix_reach
    (hLift : concreteChainFiberAppendPrefixPointClosureLiftClosed)
    (hReach : concreteChainFiberAppendPrefixFiberReachClosed) :
    concreteChainFiberAppendPrefixFibrationClosed :=
  concreteChainFiberAppendPrefixFibrationClosed_of_lift_and_same_prefix
    (concreteChainFiberAppendPrefixLiftClosureClosed_of_point_lift hLift)
    (concreteChainFiberAppendSamePrefixClosureTransferClosed_of_reach hReach)

theorem concreteChainFiberAppendPrefixFibrationClosed_of_point_lift_and_raw_prefix_reach
    (hLift : concreteChainFiberAppendPrefixPointClosureLiftClosed)
    (hReach : concreteChainFiberAppendRawPrefixReachClosed) :
    concreteChainFiberAppendPrefixFibrationClosed :=
  concreteChainFiberAppendPrefixFibrationClosed_of_point_lift_and_same_prefix_reach
    hLift (concreteChainFiberAppendPrefixFiberReachClosed_of_raw hReach)

theorem concreteChainFiberAppendPrefixFibrationClosed_of_root_lift_and_raw_prefix_reach
    (hLift : concreteChainFiberAppendPrefixRootClosureLiftClosed)
    (hReach : concreteChainFiberAppendRawPrefixReachClosed) :
    concreteChainFiberAppendPrefixFibrationClosed :=
  concreteChainFiberAppendPrefixFibrationClosed_of_point_lift_and_raw_prefix_reach
    (concreteChainFiberAppendPrefixPointClosureLiftClosed_of_root_lift hLift)
    hReach

theorem concreteChainFiberAppendPrefixFibrationClosed_of_projection_fibration
    (hFibration : concreteChainFiberAppendFibrationOverProjectionClosed) :
    concreteChainFiberAppendPrefixFibrationClosed := by
  intro word orient hne hcert key hkey
  exact hFibration word orient hne hcert key hkey
    (concreteChainFiberAppendPrefixProjection word orient hne key)

theorem concreteChainFiberAppendProjectionClosed_of_prefix
    (hPrefix : concreteChainFiberAppendPrefixClosed) :
    concreteChainFiberAppendProjectionClosed := by
  intro word orient hne _hcert key _hkey
  exact
    ⟨{ prefixPoint := fun point =>
        ⟨point.1.take word.length,
          hPrefix word orient hne key point.1 point.2⟩ }⟩

theorem concreteChainFiberAppendFibrationLiftClosed_of_projection_and_fibration
    (hProjection : concreteChainFiberAppendProjectionClosed)
    (hFibration : concreteChainFiberAppendFibrationOverProjectionClosed) :
    concreteChainFiberAppendFibrationLiftClosed := by
  intro word orient hne hcert key hkey
  rcases hProjection word orient hne hcert key hkey with ⟨projection⟩
  exact
    ⟨{ projection := projection
       fibration := hFibration word orient hne hcert key hkey projection }⟩

theorem concreteChainFiberAppendFibrationLiftClosed_of_prefix_fibration
    (hFibration : concreteChainFiberAppendPrefixFibrationClosed) :
    concreteChainFiberAppendFibrationLiftClosed := by
  intro word orient hne hcert key hkey
  let projection := concreteChainFiberAppendPrefixProjection word orient hne key
  exact
    ⟨{ projection := projection
       fibration := hFibration word orient hne hcert key hkey }⟩

def ChainFiberFibrationCertificate.ofAppendLift
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {orient : GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (prefixCert : ChainFiberFibrationCertificate word key)
    (lift : ChainFiberAppendFibrationLift word orient key) :
    ChainFiberFibrationCertificate (word ++ [orient]) key :=
  { Base := ChainFiberPoint word key
    baseStep := chainFiberRootClosureStep word key
    proj := lift.projection.prefixPoint
    fibration := lift.fibration
    baseConnected := prefixCert.connected }

theorem concreteChainFiberFibrationNonemptyTransferClosed_of_append_lift
    (hLift : concreteChainFiberAppendFibrationLiftClosed) :
    concreteChainFiberFibrationNonemptyTransferClosed := by
  intro word orient hne hcert key hkey
  rcases hcert with ⟨wordCert⟩
  rcases wordCert.fiberCertificate key hkey with ⟨prefixCert⟩
  rcases hLift word orient hne ⟨wordCert⟩ key hkey with ⟨lift⟩
  exact ⟨ChainFiberFibrationCertificate.ofAppendLift prefixCert lift⟩

theorem concreteChainFiberFibrationNonemptyTransferClosed_of_projection_and_fibration
    (hProjection : concreteChainFiberAppendProjectionClosed)
    (hFibration : concreteChainFiberAppendFibrationOverProjectionClosed) :
    concreteChainFiberFibrationNonemptyTransferClosed :=
  concreteChainFiberFibrationNonemptyTransferClosed_of_append_lift
    (concreteChainFiberAppendFibrationLiftClosed_of_projection_and_fibration
      hProjection hFibration)

theorem concreteChainFiberFibrationNonemptyTransferClosed_of_prefix_and_fibration
    (hPrefix : concreteChainFiberAppendPrefixClosed)
    (hFibration : concreteChainFiberAppendFibrationOverProjectionClosed) :
    concreteChainFiberFibrationNonemptyTransferClosed :=
  concreteChainFiberFibrationNonemptyTransferClosed_of_projection_and_fibration
    (concreteChainFiberAppendProjectionClosed_of_prefix hPrefix)
    hFibration

def concreteChainAuditFibrationNonemptyTransferClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      Nonempty (ChainWordConcreteFibrationCertificate (word ++ [orient]))

theorem concreteChainAuditFibrationTransferClosed_of_append_components
    (hCompat : concreteChainStatesAppendCompatibleClosed)
    (hFiber : concreteChainFiberFibrationTransferClosed) :
    concreteChainAuditFibrationTransferClosed := by
  intro word orient hcert
  exact
    ⟨{ compatibleStates := hCompat word orient hcert
       fiberCertificate := hFiber word orient hcert }⟩

theorem concreteChainStatesAppendCompatibleClosed_of_generated
    (hGenerated : concreteChainStatesGeneratedCompatible) :
    concreteChainStatesAppendCompatibleClosed := by
  intro word orient _hcert
  exact hGenerated (word ++ [orient])

theorem concreteChainAuditFibrationTransferClosed_of_generated_and_fiber
    (hGenerated : concreteChainStatesGeneratedCompatible)
    (hFiber : concreteChainFiberFibrationTransferClosed) :
    concreteChainAuditFibrationTransferClosed :=
  concreteChainAuditFibrationTransferClosed_of_append_components
    (concreteChainStatesAppendCompatibleClosed_of_generated hGenerated)
    hFiber

theorem concreteChainAuditFibrationTransferClosed_of_fiber
    (hFiber : concreteChainFiberFibrationTransferClosed) :
    concreteChainAuditFibrationTransferClosed :=
  concreteChainAuditFibrationTransferClosed_of_generated_and_fiber
    concreteChainStatesGeneratedCompatible_ok hFiber

theorem concreteChainAuditFibrationNonemptyTransferClosed_of_append_components
    (hGenerated : concreteChainStatesGeneratedCompatible)
    (hFiber : concreteChainFiberFibrationNonemptyTransferClosed) :
    concreteChainAuditFibrationNonemptyTransferClosed := by
  intro word orient hne hcert
  exact
    ⟨{ compatibleStates := hGenerated (word ++ [orient])
       fiberCertificate := hFiber word orient hne hcert }⟩

theorem concreteChainAuditFibrationNonemptyTransferClosed_of_append_lift
    (hLift : concreteChainFiberAppendFibrationLiftClosed) :
    concreteChainAuditFibrationNonemptyTransferClosed :=
  concreteChainAuditFibrationNonemptyTransferClosed_of_append_components
    concreteChainStatesGeneratedCompatible_ok
    (concreteChainFiberFibrationNonemptyTransferClosed_of_append_lift hLift)

theorem concreteChainAuditFibrationNonemptyTransferClosed_of_projection_and_fibration
    (hProjection : concreteChainFiberAppendProjectionClosed)
    (hFibration : concreteChainFiberAppendFibrationOverProjectionClosed) :
    concreteChainAuditFibrationNonemptyTransferClosed :=
  concreteChainAuditFibrationNonemptyTransferClosed_of_append_components
    concreteChainStatesGeneratedCompatible_ok
    (concreteChainFiberFibrationNonemptyTransferClosed_of_projection_and_fibration
      hProjection hFibration)

theorem concreteChainAuditFibrationNonemptyTransferClosed_of_prefix_and_fibration
    (hPrefix : concreteChainFiberAppendPrefixClosed)
    (hFibration : concreteChainFiberAppendFibrationOverProjectionClosed) :
    concreteChainAuditFibrationNonemptyTransferClosed :=
  concreteChainAuditFibrationNonemptyTransferClosed_of_append_components
    concreteChainStatesGeneratedCompatible_ok
    (concreteChainFiberFibrationNonemptyTransferClosed_of_prefix_and_fibration
      hPrefix hFibration)

theorem chainWordConcreteFibrationCertificate_of_empty_and_transfer_aux
    (hTransfer : concreteChainAuditFibrationTransferClosed)
    (suffix pref : List GoertzelLemma818FrontierMode.TauOrient)
    (hpref : Nonempty (ChainWordConcreteFibrationCertificate pref)) :
    Nonempty (ChainWordConcreteFibrationCertificate (pref ++ suffix)) := by
  induction suffix generalizing pref with
  | nil =>
      simpa using hpref
  | cons orient rest ih =>
      have hnext : Nonempty
          (ChainWordConcreteFibrationCertificate (pref ++ [orient])) :=
        hTransfer pref orient hpref
      have hrest : Nonempty
          (ChainWordConcreteFibrationCertificate ((pref ++ [orient]) ++ rest)) :=
        ih (pref ++ [orient]) hnext
      simpa [List.append_assoc] using hrest

theorem chainWordConcreteFibrationCertificate_of_empty_and_transfer
    (hEmpty : Nonempty (ChainWordConcreteFibrationCertificate []))
    (hTransfer : concreteChainAuditFibrationTransferClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    Nonempty (ChainWordConcreteFibrationCertificate word) := by
  simpa using
    chainWordConcreteFibrationCertificate_of_empty_and_transfer_aux
      hTransfer word [] hEmpty

theorem chainAuditForFrontierWord_ok_of_concrete_empty_and_transfer
    (hEmpty : Nonempty (ChainWordConcreteFibrationCertificate []))
    (hTransfer : concreteChainAuditFibrationTransferClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true := by
  rcases chainWordConcreteFibrationCertificate_of_empty_and_transfer
    hEmpty hTransfer word with ⟨cert⟩
  exact chainAuditForFrontierWord_of_concreteFibrationCertificate cert

theorem chainWordConcreteFibrationCertificate_of_transfer
    (hTransfer : concreteChainAuditFibrationTransferClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    Nonempty (ChainWordConcreteFibrationCertificate word) :=
  chainWordConcreteFibrationCertificate_of_empty_and_transfer
    concreteChainWordFibrationEmptyCertificate_ok hTransfer word

theorem chainAuditForFrontierWord_ok_of_concrete_transfer
    (hTransfer : concreteChainAuditFibrationTransferClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_concrete_empty_and_transfer
    concreteChainWordFibrationEmptyCertificate_ok hTransfer word

theorem chainAuditForFrontierWord_ok_of_generated_and_fiber_transfer
    (hGenerated : concreteChainStatesGeneratedCompatible)
    (hFiber : concreteChainFiberFibrationTransferClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_concrete_transfer
    (concreteChainAuditFibrationTransferClosed_of_generated_and_fiber
      hGenerated hFiber)
    word

theorem chainAuditForFrontierWord_ok_of_fiber_transfer
    (hFiber : concreteChainFiberFibrationTransferClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_concrete_transfer
    (concreteChainAuditFibrationTransferClosed_of_fiber hFiber)
    word

def concreteChainWordFibrationSingletonSeeds : Prop :=
  ∀ orient : GoertzelLemma818FrontierMode.TauOrient,
    Nonempty (ChainWordConcreteFibrationCertificate [orient])

theorem chainWordConcreteFibrationCertificate_of_singletons_and_nonempty_transfer_aux
    (hTransfer : concreteChainAuditFibrationNonemptyTransferClosed)
    (suffix pref : List GoertzelLemma818FrontierMode.TauOrient)
    (hpref_ne : pref ≠ [])
    (hpref : Nonempty (ChainWordConcreteFibrationCertificate pref)) :
    Nonempty (ChainWordConcreteFibrationCertificate (pref ++ suffix)) := by
  induction suffix generalizing pref with
  | nil =>
      simpa using hpref
  | cons orient rest ih =>
      have hnext : Nonempty
          (ChainWordConcreteFibrationCertificate (pref ++ [orient])) :=
        hTransfer pref orient hpref_ne hpref
      have hnext_ne : pref ++ [orient] ≠ [] := by
        simp
      have hrest : Nonempty
          (ChainWordConcreteFibrationCertificate
            ((pref ++ [orient]) ++ rest)) :=
        ih (pref ++ [orient]) hnext_ne hnext
      simpa [List.append_assoc] using hrest

theorem chainWordConcreteFibrationCertificate_of_singletons_and_nonempty_transfer
    (hSeed : concreteChainWordFibrationSingletonSeeds)
    (hTransfer : concreteChainAuditFibrationNonemptyTransferClosed)
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    (hne : word ≠ []) :
    Nonempty (ChainWordConcreteFibrationCertificate word) := by
  cases word with
  | nil =>
      exact False.elim (hne rfl)
  | cons orient rest =>
      have hbase : Nonempty (ChainWordConcreteFibrationCertificate [orient]) :=
        hSeed orient
      simpa using
        chainWordConcreteFibrationCertificate_of_singletons_and_nonempty_transfer_aux
          hTransfer rest [orient] (by simp) hbase

theorem chainAuditForFrontierWord_ok_of_concrete_singletons_and_nonempty_transfer
    (hSeed : concreteChainWordFibrationSingletonSeeds)
    (hTransfer : concreteChainAuditFibrationNonemptyTransferClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true := by
  cases word with
  | nil =>
      decide
  | cons orient rest =>
      have hcert :
          Nonempty (ChainWordConcreteFibrationCertificate (orient :: rest)) :=
        chainWordConcreteFibrationCertificate_of_singletons_and_nonempty_transfer
          hSeed hTransfer (by simp)
      rcases hcert with ⟨cert⟩
      exact chainAuditForFrontierWord_of_concreteFibrationCertificate cert

theorem chainAuditForFrontierWord_ok_of_append_lift
    (hSeed : concreteChainWordFibrationSingletonSeeds)
    (hLift : concreteChainFiberAppendFibrationLiftClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_concrete_singletons_and_nonempty_transfer
    hSeed
    (concreteChainAuditFibrationNonemptyTransferClosed_of_append_lift hLift)
    word

theorem chainAuditForFrontierWord_ok_of_projection_and_fibration
    (hSeed : concreteChainWordFibrationSingletonSeeds)
    (hProjection : concreteChainFiberAppendProjectionClosed)
    (hFibration : concreteChainFiberAppendFibrationOverProjectionClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_concrete_singletons_and_nonempty_transfer
    hSeed
    (concreteChainAuditFibrationNonemptyTransferClosed_of_projection_and_fibration
      hProjection hFibration)
    word

theorem chainAuditForFrontierWord_ok_of_prefix_and_fibration
    (hSeed : concreteChainWordFibrationSingletonSeeds)
    (hPrefix : concreteChainFiberAppendPrefixClosed)
    (hFibration : concreteChainFiberAppendFibrationOverProjectionClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_concrete_singletons_and_nonempty_transfer
    hSeed
    (concreteChainAuditFibrationNonemptyTransferClosed_of_prefix_and_fibration
      hPrefix hFibration)
    word

structure ChainAuditFibrationCertificate
    (word : List GoertzelLemma818FrontierMode.TauOrient) : Type 1 where
  Total : Type
  Base : Type
  totalStep : Total → Total → Prop
  baseStep : Base → Base → Prop
  proj : Total → Base
  fibration : Fibration totalStep baseStep proj
  baseConnected : Connected baseStep
  auditOfTotalConnected :
    Connected totalStep → chainAuditForFrontierWord word = true

theorem ChainAuditFibrationCertificate.audit_ok
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    (cert : ChainAuditFibrationCertificate word) :
    chainAuditForFrontierWord word = true :=
  cert.auditOfTotalConnected
    (cert.fibration.totalConnected_of_baseConnected cert.baseConnected)

def ChainAuditFibrationCertificate.ofAudit
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    (hAudit : chainAuditForFrontierWord word = true) :
    ChainAuditFibrationCertificate word :=
  { Total := Unit
    Base := Unit
    totalStep := fun _ _ => True
    baseStep := fun _ _ => True
    proj := fun _ => ()
    fibration :=
      { fiberReach := by
          intro x y _
          cases x
          cases y
          exact Reach.refl ()
        liftStep := by
          intro x b _
          cases x
          cases b
          exact ⟨(), rfl, Reach.refl ()⟩ }
    baseConnected := by
      intro x y
      cases x
      cases y
      exact Reach.refl ()
    auditOfTotalConnected := by
      intro _
      exact hAudit }

def ChainAuditFibrationCertificate.ofConcrete
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    (cert : ChainWordConcreteFibrationCertificate word) :
    ChainAuditFibrationCertificate word :=
  { Total := Unit
    Base := Unit
    totalStep := fun _ _ => True
    baseStep := fun _ _ => True
    proj := fun _ => ()
    fibration :=
      { fiberReach := by
          intro x y _
          cases x
          cases y
          exact Reach.refl ()
        liftStep := by
          intro x b _
          cases x
          cases b
          exact ⟨(), rfl, Reach.refl ()⟩ }
    baseConnected := by
      intro x y
      cases x
      cases y
      exact Reach.refl ()
    auditOfTotalConnected := by
      intro _
      exact chainAuditForFrontierWord_of_concreteFibrationCertificate cert }

def semanticFrontierStateFibrationCertificates
    (targetAudit : RepresentativeSemanticTarget → Bool) : Prop :=
  ∀ {word : List GoertzelLemma818FrontierMode.TauOrient} {state : FrontierState},
    frontierState word = state →
    semanticFrontierStateAudit targetAudit state = true →
    Nonempty (ChainAuditFibrationCertificate word)

def chainAuditFibrationEmptyCertificate : Prop :=
  Nonempty (ChainAuditFibrationCertificate [])

theorem emptyChainAuditForFrontierWord_ok :
    chainAuditForFrontierWord [] = true := by
  decide

def emptyChainAuditFibrationCertificate :
    ChainAuditFibrationCertificate [] :=
  { Total := Unit
    Base := Unit
    totalStep := fun _ _ => True
    baseStep := fun _ _ => True
    proj := fun _ => ()
    fibration :=
      { fiberReach := by
          intro x y _
          cases x
          cases y
          exact Reach.refl ()
        liftStep := by
          intro x b _
          cases x
          cases b
          exact ⟨(), rfl, Reach.refl ()⟩ }
    baseConnected := by
      intro x y
      cases x
      cases y
      exact Reach.refl ()
    auditOfTotalConnected := by
      intro _
      exact emptyChainAuditForFrontierWord_ok }

theorem chainAuditFibrationEmptyCertificate_ok :
    chainAuditFibrationEmptyCertificate :=
  ⟨emptyChainAuditFibrationCertificate⟩

theorem singletonChainAuditForFrontierWord_ok
    (orient : GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord [orient] = true := by
  cases orient with
  | tau =>
      simpa [chainAuditForFrontierWord, frontierWordToChainWord,
        frontierOrientToChain, baseCertifiedChainCertificateAudit] using
        baseCertifiedChainCertificateAudit_ok BaseCertifiedWord.t
  | mirror =>
      simpa [chainAuditForFrontierWord, frontierWordToChainWord,
        frontierOrientToChain, baseCertifiedChainCertificateAudit] using
        baseCertifiedChainCertificateAudit_ok BaseCertifiedWord.m

def chainAuditFibrationSingletonSeeds : Prop :=
  ∀ orient : GoertzelLemma818FrontierMode.TauOrient,
    Nonempty (ChainAuditFibrationCertificate [orient])

theorem chainAuditFibrationSingletonSeeds_ok :
    chainAuditFibrationSingletonSeeds := by
  intro orient
  exact ⟨ChainAuditFibrationCertificate.ofAudit
    (singletonChainAuditForFrontierWord_ok orient)⟩

theorem concreteChainWordFibrationSingletonSeeds_ok :
    concreteChainWordFibrationSingletonSeeds := by
  intro orient
  refine
    ⟨{ compatibleStates := concreteChainStatesGeneratedCompatible_ok [orient]
       fiberCertificate := ?_ }⟩
  intro key hkey
  have hAudit := singletonChainAuditForFrontierWord_ok orient
  unfold chainAuditForFrontierWord GoertzelLemma814.chainLKRInAudit at hAudit
  change ((concreteChainStates [orient]).all
      (GoertzelLemma814.compatibleChainStates
        (frontierWordToChainWord [orient])) &&
    GoertzelLemma814.colorAssignments4.all (fun key =>
      GoertzelLemma814.chainFiberConnected
        (frontierWordToChainWord [orient])
        (concreteChainFiber [orient] key))) = true at hAudit
  have hFiberAll :
      GoertzelLemma814.colorAssignments4.all (fun key =>
        GoertzelLemma814.chainFiberConnected
          (frontierWordToChainWord [orient])
          (concreteChainFiber [orient] key)) = true :=
    by
      cases hCompat :
        ((concreteChainStates [orient]).all
          (GoertzelLemma814.compatibleChainStates
            (frontierWordToChainWord [orient]))) with
      | false =>
          simp [hCompat] at hAudit
      | true =>
          simpa [hCompat] using hAudit
  have hFiber :
      GoertzelLemma814.chainFiberConnected
        (frontierWordToChainWord [orient])
        (concreteChainFiber [orient] key) = true :=
    (List.all_eq_true.mp hFiberAll) key hkey
  exact ⟨ChainFiberFibrationCertificate.ofChainFiberConnected hFiber⟩

def chainAuditFibrationTransferClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    Nonempty (ChainAuditFibrationCertificate word) →
      Nonempty (ChainAuditFibrationCertificate (word ++ [orient]))

def chainAuditFibrationNonemptyTransferClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
    Nonempty (ChainAuditFibrationCertificate word) →
      Nonempty (ChainAuditFibrationCertificate (word ++ [orient]))

theorem chainAuditFibrationTransferClosed_of_concrete_empty_and_transfer
    (hEmpty : Nonempty (ChainWordConcreteFibrationCertificate []))
    (hTransfer : concreteChainAuditFibrationTransferClosed) :
    chainAuditFibrationTransferClosed := by
  intro word orient _hcert
  rcases chainWordConcreteFibrationCertificate_of_empty_and_transfer
    hEmpty hTransfer (word ++ [orient]) with ⟨cert⟩
  exact ⟨ChainAuditFibrationCertificate.ofConcrete cert⟩

theorem chainAuditFibrationTransferClosed_of_concrete_transfer
    (hTransfer : concreteChainAuditFibrationTransferClosed) :
    chainAuditFibrationTransferClosed :=
  chainAuditFibrationTransferClosed_of_concrete_empty_and_transfer
    concreteChainWordFibrationEmptyCertificate_ok hTransfer

theorem chainAuditFibrationTransferClosed_of_generated_and_fiber
    (hGenerated : concreteChainStatesGeneratedCompatible)
    (hFiber : concreteChainFiberFibrationTransferClosed) :
    chainAuditFibrationTransferClosed :=
  chainAuditFibrationTransferClosed_of_concrete_transfer
    (concreteChainAuditFibrationTransferClosed_of_generated_and_fiber
      hGenerated hFiber)

theorem chainAuditFibrationTransferClosed_of_fiber
    (hFiber : concreteChainFiberFibrationTransferClosed) :
    chainAuditFibrationTransferClosed :=
  chainAuditFibrationTransferClosed_of_concrete_transfer
    (concreteChainAuditFibrationTransferClosed_of_fiber hFiber)

theorem chainAuditFibrationNonemptyTransferClosed_of_transfer
    (hTransfer : chainAuditFibrationTransferClosed) :
    chainAuditFibrationNonemptyTransferClosed := by
  intro word orient _hne hcert
  exact hTransfer word orient hcert

theorem chainAuditFibrationCertificate_of_singletons_and_nonempty_transfer_aux
    (hTransfer : chainAuditFibrationNonemptyTransferClosed)
    (suffix pref : List GoertzelLemma818FrontierMode.TauOrient)
    (hpref_ne : pref ≠ [])
    (hpref : Nonempty (ChainAuditFibrationCertificate pref)) :
    Nonempty (ChainAuditFibrationCertificate (pref ++ suffix)) := by
  induction suffix generalizing pref with
  | nil =>
      simpa using hpref
  | cons orient rest ih =>
      have hnext : Nonempty
          (ChainAuditFibrationCertificate (pref ++ [orient])) :=
        hTransfer pref orient hpref_ne hpref
      have hnext_ne : pref ++ [orient] ≠ [] := by
        simp
      have hrest : Nonempty
          (ChainAuditFibrationCertificate ((pref ++ [orient]) ++ rest)) :=
        ih (pref ++ [orient]) hnext_ne hnext
      simpa [List.append_assoc] using hrest

theorem chainAuditFibrationCertificate_of_singletons_and_nonempty_transfer
    (hSeed : chainAuditFibrationSingletonSeeds)
    (hTransfer : chainAuditFibrationNonemptyTransferClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    Nonempty (ChainAuditFibrationCertificate word) := by
  cases word with
  | nil =>
      exact chainAuditFibrationEmptyCertificate_ok
  | cons orient rest =>
      have hbase : Nonempty (ChainAuditFibrationCertificate [orient]) :=
        hSeed orient
      simpa using
        chainAuditFibrationCertificate_of_singletons_and_nonempty_transfer_aux
          hTransfer rest [orient] (by simp) hbase

theorem chainAuditFibrationCertificate_of_empty_and_transfer_aux
    (hTransfer : chainAuditFibrationTransferClosed)
    (suffix pref : List GoertzelLemma818FrontierMode.TauOrient)
    (hpref : Nonempty (ChainAuditFibrationCertificate pref)) :
    Nonempty (ChainAuditFibrationCertificate (pref ++ suffix)) := by
  induction suffix generalizing pref with
  | nil =>
      simpa using hpref
  | cons orient rest ih =>
      have hnext : Nonempty
          (ChainAuditFibrationCertificate (pref ++ [orient])) :=
        hTransfer pref orient hpref
      have hrest : Nonempty
          (ChainAuditFibrationCertificate ((pref ++ [orient]) ++ rest)) :=
        ih (pref ++ [orient]) hnext
      simpa [List.append_assoc] using hrest

theorem chainAuditFibrationCertificate_of_empty_and_transfer
    (hEmpty : chainAuditFibrationEmptyCertificate)
    (hTransfer : chainAuditFibrationTransferClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    Nonempty (ChainAuditFibrationCertificate word) := by
  simpa using
    chainAuditFibrationCertificate_of_empty_and_transfer_aux
      hTransfer word [] hEmpty

theorem semanticFrontierStateFibrationCertificates_of_empty_and_transfer
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hEmpty : chainAuditFibrationEmptyCertificate)
    (hTransfer : chainAuditFibrationTransferClosed) :
    semanticFrontierStateFibrationCertificates targetAudit := by
  intro word _state _hstate _haudit
  exact chainAuditFibrationCertificate_of_empty_and_transfer
    hEmpty hTransfer word

/--
The finite sufficiency hook still missing from the frontier plan.

It says that a successful semantic audit of the DFA mode is enough to prove the
real chain audit for every concrete word folding to that mode.  Supplying this
hook is the future congruence/sufficiency theorem; the theorem below proves the
remaining induction plumbing.
-/
def semanticModeSufficientForChain
    (targetAudit : RepresentativeSemanticTarget → Bool) : Prop :=
  ∀ {word : List GoertzelLemma818FrontierMode.TauOrient} {mode : FrontierMode},
    wordMode word = some mode →
    semanticModeAudit targetAudit mode = true →
    chainAuditForFrontierWord word = true

theorem chainAuditForFrontierWord_ok_of_targets_and_sufficiency
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hTarget : ∀ t, targetAudit t = true)
    (hSufficient : semanticModeSufficientForChain targetAudit)
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {mode : FrontierMode}
    (hmode : wordMode word = some mode) :
    chainAuditForFrontierWord word = true :=
  hSufficient hmode (wordMode_hasSemanticModeAudit_of_targets hTarget hmode)

/--
The same missing sufficiency theorem, stated over the explicit total finite
frontier state `frontierState word`.
-/
def semanticFrontierStateSufficientForChain
    (targetAudit : RepresentativeSemanticTarget → Bool) : Prop :=
  ∀ {word : List GoertzelLemma818FrontierMode.TauOrient} {state : FrontierState},
    frontierState word = state →
    semanticFrontierStateAudit targetAudit state = true →
    chainAuditForFrontierWord word = true

theorem chainAuditForFrontierWord_ok_of_targets_and_frontier_state_sufficiency
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hTarget : ∀ t, targetAudit t = true)
    (hSufficient : semanticFrontierStateSufficientForChain targetAudit)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  hSufficient rfl (frontierState_hasSemanticStateAudit_of_targets hTarget word)

theorem semanticFrontierStateSufficientForChain_of_concrete_empty_and_transfer
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hEmpty : Nonempty (ChainWordConcreteFibrationCertificate []))
    (hTransfer : concreteChainAuditFibrationTransferClosed) :
    semanticFrontierStateSufficientForChain targetAudit := by
  intro word _state _hstate _haudit
  exact chainAuditForFrontierWord_ok_of_concrete_empty_and_transfer
    hEmpty hTransfer word

theorem semanticFrontierStateSufficientForChain_of_concrete_transfer
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hTransfer : concreteChainAuditFibrationTransferClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_concrete_empty_and_transfer
    concreteChainWordFibrationEmptyCertificate_ok hTransfer

theorem semanticFrontierStateSufficientForChain_of_generated_and_fiber
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hGenerated : concreteChainStatesGeneratedCompatible)
    (hFiber : concreteChainFiberFibrationTransferClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_concrete_transfer
    (concreteChainAuditFibrationTransferClosed_of_generated_and_fiber
      hGenerated hFiber)

theorem semanticFrontierStateSufficientForChain_of_fiber
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hFiber : concreteChainFiberFibrationTransferClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_concrete_transfer
    (concreteChainAuditFibrationTransferClosed_of_fiber hFiber)

theorem semanticFrontierStateSufficientForChain_of_append_lift
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hLift : concreteChainFiberAppendFibrationLiftClosed) :
    semanticFrontierStateSufficientForChain targetAudit := by
  intro word _state _hstate _haudit
  exact chainAuditForFrontierWord_ok_of_append_lift
    concreteChainWordFibrationSingletonSeeds_ok hLift word

theorem semanticFrontierStateSufficientForChain_of_prefix_fibration
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hFibration : concreteChainFiberAppendPrefixFibrationClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_append_lift
    (concreteChainFiberAppendFibrationLiftClosed_of_prefix_fibration hFibration)

theorem semanticFrontierStateSufficientForChain_of_prefix_fibration_fields
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hFiber : concreteChainFiberAppendPrefixFiberReachClosed)
    (hLift : concreteChainFiberAppendPrefixLiftStepClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_prefix_fibration
    (concreteChainFiberAppendPrefixFibrationClosed_of_fields hFiber hLift)

theorem semanticFrontierStateSufficientForChain_of_prefix_closure_fields
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hFiber : concreteChainFiberAppendPrefixFiberClosureClosed)
    (hLift : concreteChainFiberAppendPrefixLiftClosureClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_prefix_fibration
    (concreteChainFiberAppendPrefixFibrationClosed_of_closure hFiber hLift)

theorem semanticFrontierStateSufficientForChain_of_lift_and_same_prefix
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hLift : concreteChainFiberAppendPrefixLiftClosureClosed)
    (hSame : concreteChainFiberAppendSamePrefixClosureTransferClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_prefix_fibration
    (concreteChainFiberAppendPrefixFibrationClosed_of_lift_and_same_prefix
      hLift hSame)

theorem semanticFrontierStateSufficientForChain_of_root_lift_and_same_prefix_reach
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hLift : concreteChainFiberAppendPrefixRootClosureLiftClosed)
    (hReach : concreteChainFiberAppendPrefixFiberReachClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_prefix_fibration
    (concreteChainFiberAppendPrefixFibrationClosed_of_root_lift_and_same_prefix_reach
      hLift hReach)

theorem semanticFrontierStateSufficientForChain_of_point_lift_and_same_prefix_reach
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hLift : concreteChainFiberAppendPrefixPointClosureLiftClosed)
    (hReach : concreteChainFiberAppendPrefixFiberReachClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_prefix_fibration
    (concreteChainFiberAppendPrefixFibrationClosed_of_point_lift_and_same_prefix_reach
      hLift hReach)

theorem semanticFrontierStateSufficientForChain_of_point_lift_and_raw_prefix_reach
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hLift : concreteChainFiberAppendPrefixPointClosureLiftClosed)
    (hReach : concreteChainFiberAppendRawPrefixReachClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_prefix_fibration
    (concreteChainFiberAppendPrefixFibrationClosed_of_point_lift_and_raw_prefix_reach
      hLift hReach)

theorem semanticFrontierStateSufficientForChain_of_root_lift_and_raw_prefix_reach
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hLift : concreteChainFiberAppendPrefixRootClosureLiftClosed)
    (hReach : concreteChainFiberAppendRawPrefixReachClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_prefix_fibration
    (concreteChainFiberAppendPrefixFibrationClosed_of_root_lift_and_raw_prefix_reach
      hLift hReach)

theorem semanticFrontierStateSufficientForChain_of_projection_and_fibration
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hProjection : concreteChainFiberAppendProjectionClosed)
    (hFibration : concreteChainFiberAppendFibrationOverProjectionClosed) :
    semanticFrontierStateSufficientForChain targetAudit := by
  intro word _state _hstate _haudit
  exact chainAuditForFrontierWord_ok_of_projection_and_fibration
    concreteChainWordFibrationSingletonSeeds_ok hProjection hFibration word

theorem semanticFrontierStateSufficientForChain_of_prefix_and_fibration
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hPrefix : concreteChainFiberAppendPrefixClosed)
    (hFibration : concreteChainFiberAppendFibrationOverProjectionClosed) :
    semanticFrontierStateSufficientForChain targetAudit := by
  intro word _state _hstate _haudit
  exact chainAuditForFrontierWord_ok_of_prefix_and_fibration
    concreteChainWordFibrationSingletonSeeds_ok hPrefix hFibration word

theorem semanticFrontierStateSufficientForChain_of_append_fibration
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hFibration : concreteChainFiberAppendFibrationOverProjectionClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_prefix_and_fibration
    concreteChainFiberAppendPrefixClosed_ok hFibration

theorem semanticFrontierStateSufficientForChain_of_fibrationCertificates
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hCerts : semanticFrontierStateFibrationCertificates targetAudit) :
    semanticFrontierStateSufficientForChain targetAudit := by
  intro word state hstate haudit
  rcases hCerts hstate haudit with ⟨cert⟩
  exact cert.audit_ok

theorem semanticFrontierStateSufficientForChain_of_empty_and_transfer
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hEmpty : chainAuditFibrationEmptyCertificate)
    (hTransfer : chainAuditFibrationTransferClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_fibrationCertificates
    (semanticFrontierStateFibrationCertificates_of_empty_and_transfer
      hEmpty hTransfer)

theorem semanticFrontierStateSufficientForChain_of_singletons_and_nonempty_transfer
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hSeed : chainAuditFibrationSingletonSeeds)
    (hTransfer : chainAuditFibrationNonemptyTransferClosed) :
    semanticFrontierStateSufficientForChain targetAudit := by
  intro word _state _hstate _haudit
  rcases chainAuditFibrationCertificate_of_singletons_and_nonempty_transfer
    hSeed hTransfer word with ⟨cert⟩
  exact cert.audit_ok

theorem chainAuditForFrontierWord_ok_of_targets_empty_and_transfer
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hTarget : ∀ t, targetAudit t = true)
    (hEmpty : chainAuditFibrationEmptyCertificate)
    (hTransfer : chainAuditFibrationTransferClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_targets_and_frontier_state_sufficiency
    hTarget
    (semanticFrontierStateSufficientForChain_of_empty_and_transfer
      hEmpty hTransfer)
    word

theorem semanticFrontierStateSufficientForChain_of_transfer
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hTransfer : chainAuditFibrationTransferClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_empty_and_transfer
    chainAuditFibrationEmptyCertificate_ok hTransfer

theorem chainAuditForFrontierWord_ok_of_targets_and_transfer
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hTarget : ∀ t, targetAudit t = true)
    (hTransfer : chainAuditFibrationTransferClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_targets_empty_and_transfer
    hTarget chainAuditFibrationEmptyCertificate_ok hTransfer word

end GoertzelLemma818SemanticBridge

end Mettapedia.GraphTheory.FourColor
