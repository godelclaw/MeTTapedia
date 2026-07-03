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

theorem tauOrientAt_frontierWordToChainWord_append_length
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient) :
    GoertzelLemma814.tauOrientAt
      (frontierWordToChainWord (word ++ [orient])) word.length =
      frontierOrientToChain orient := by
  unfold GoertzelLemma814.tauOrientAt frontierWordToChainWord
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [← List.length_map (f := frontierOrientToChain) (as := word)]
  exact GoertzelLemma814.listGetD_append_length
    (List.map frontierOrientToChain word) (frontierOrientToChain orient)
    GoertzelLemma814.TauOrient.normal

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

def ChainWordConcreteFibrationCertificate.ofChainAudit
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    (hAudit : chainAuditForFrontierWord word = true) :
    ChainWordConcreteFibrationCertificate word := by
  unfold chainAuditForFrontierWord GoertzelLemma814.chainLKRInAudit at hAudit
  change ((concreteChainStates word).all
      (GoertzelLemma814.compatibleChainStates (frontierWordToChainWord word)) &&
    GoertzelLemma814.colorAssignments4.all (fun key =>
      GoertzelLemma814.chainFiberConnected
        (frontierWordToChainWord word) (concreteChainFiber word key))) = true
    at hAudit
  have hCompat :
      (concreteChainStates word).all
        (GoertzelLemma814.compatibleChainStates (frontierWordToChainWord word)) =
          true := by
    cases h :
        (concreteChainStates word).all
          (GoertzelLemma814.compatibleChainStates
            (frontierWordToChainWord word)) with
    | false =>
        simp [h] at hAudit
    | true =>
        rfl
  have hFiberAll :
      GoertzelLemma814.colorAssignments4.all (fun key =>
        GoertzelLemma814.chainFiberConnected
          (frontierWordToChainWord word) (concreteChainFiber word key)) =
        true := by
    cases h :
        (concreteChainStates word).all
          (GoertzelLemma814.compatibleChainStates
            (frontierWordToChainWord word)) with
    | false =>
        simp [h] at hAudit
    | true =>
        simpa [h] using hAudit
  exact
    { compatibleStates := hCompat
      fiberCertificate := by
        intro key hkey
        have hFiber :
            GoertzelLemma814.chainFiberConnected
              (frontierWordToChainWord word) (concreteChainFiber word key) =
              true :=
          (List.all_eq_true.mp hFiberAll) key hkey
        exact ⟨ChainFiberFibrationCertificate.ofChainFiberConnected hFiber⟩ }

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

structure ChainFiberAppendQuotientFibrationLift
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor) : Type 1 where
  Base : Type
  baseStep : Base → Base → Prop
  proj : ChainFiberPoint (word ++ [orient]) key → Base
  fibration :
    Fibration
      (chainFiberRootClosureStep (word ++ [orient]) key)
      baseStep
      proj
  baseConnected : Connected baseStep

structure ChainFiberAppendQuotientFibrationFields
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor) : Type 1 where
  Base : Type
  baseStep : Base → Base → Prop
  proj : ChainFiberPoint (word ++ [orient]) key → Base
  fiberReach :
    ∀ x y : ChainFiberPoint (word ++ [orient]) key,
      proj x = proj y →
        Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y
  liftStep :
    ∀ (x : ChainFiberPoint (word ++ [orient]) key) (b : Base),
      baseStep (proj x) b →
        ∃ y : ChainFiberPoint (word ++ [orient]) key,
          proj y = b ∧
            Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y
  baseConnected : Connected baseStep

structure ChainFiberAppendQuotientFibrationRootFields
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor) : Type 1 where
  Base : Type
  baseStep : Base → Base → Prop
  proj : ChainFiberPoint (word ++ [orient]) key → Base
  fiberReach :
    ∀ x y : ChainFiberPoint (word ++ [orient]) key,
      proj x = proj y →
        Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y
  liftStep :
    ∀ (x : ChainFiberPoint (word ++ [orient]) key) (b : Base),
      baseStep (proj x) b →
        ∃ y : ChainFiberPoint (word ++ [orient]) key,
          proj y = b ∧
            Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y
  baseRooted : RootedConnectedCertificate baseStep

structure ChainFiberAppendQuotientFibrationSymmetricRootFields
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor) : Type 1 where
  Base : Type
  baseStep : Base → Base → Prop
  proj : ChainFiberPoint (word ++ [orient]) key → Base
  fiberReach :
    ∀ x y : ChainFiberPoint (word ++ [orient]) key,
      proj x = proj y →
        Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y
  liftStep :
    ∀ (x : ChainFiberPoint (word ++ [orient]) key) (b : Base),
      baseStep (proj x) b →
        ∃ y : ChainFiberPoint (word ++ [orient]) key,
          proj y = b ∧
            Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y
  baseSymmetricRooted : SymmetricRootedConnectedCertificate baseStep

structure ChainFiberAppendQuotientFibrationListedSymmetricRootFields
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor) : Type 1 where
  Base : Type
  baseStep : Base → Base → Prop
  proj : ChainFiberPoint (word ++ [orient]) key → Base
  fiberReach :
    ∀ x y : ChainFiberPoint (word ++ [orient]) key,
      proj x = proj y →
        Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y
  liftStep :
    ∀ (x : ChainFiberPoint (word ++ [orient]) key) (b : Base),
      baseStep (proj x) b →
        ∃ y : ChainFiberPoint (word ++ [orient]) key,
          proj y = b ∧
            Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y
  baseListedSymmetricRooted :
    ListedSymmetricRootedConnectedCertificate baseStep

structure ChainFiberAppendQuotientFibrationParentMapFields
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor) : Type 1 where
  Base : Type
  baseStep : Base → Base → Prop
  proj : ChainFiberPoint (word ++ [orient]) key → Base
  fiberReach :
    ∀ x y : ChainFiberPoint (word ++ [orient]) key,
      proj x = proj y →
        Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y
  liftStep :
    ∀ (x : ChainFiberPoint (word ++ [orient]) key) (b : Base),
      baseStep (proj x) b →
        ∃ y : ChainFiberPoint (word ++ [orient]) key,
          proj y = b ∧
            Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y
  baseParentMapSymmetricRooted :
    ParentMapSymmetricRootedConnectedCertificate baseStep

structure ChainFiberAppendQuotientFibrationParentRowsFields
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor) : Type 1 where
  Base : Type
  baseDecidableEq : DecidableEq Base
  baseStep : Base → Base → Prop
  proj : ChainFiberPoint (word ++ [orient]) key → Base
  fiberReach :
    ∀ x y : ChainFiberPoint (word ++ [orient]) key,
      proj x = proj y →
        Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y
  liftStep :
    ∀ (x : ChainFiberPoint (word ++ [orient]) key) (b : Base),
      baseStep (proj x) b →
        ∃ y : ChainFiberPoint (word ++ [orient]) key,
          proj y = b ∧
            Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y
  baseParentRowsSymmetricRooted :
    @ParentRowsSymmetricRootedConnectedCertificate
      Base baseDecidableEq baseStep

structure ChainFiberAppendQuotientFibrationParentRowsBaseData
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor) : Type 1 where
  Base : Type
  baseDecidableEq : DecidableEq Base
  baseStep : Base → Base → Prop
  baseParentRowsSymmetricRooted :
    @ParentRowsSymmetricRootedConnectedCertificate
      Base baseDecidableEq baseStep

structure ChainFiberAppendQuotientFibrationParentRowsStructuralFields
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {orient : GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (data :
      ChainFiberAppendQuotientFibrationParentRowsBaseData
        word orient key) : Type 1 where
  proj : ChainFiberPoint (word ++ [orient]) key → data.Base
  fiberReach :
    ∀ x y : ChainFiberPoint (word ++ [orient]) key,
      proj x = proj y →
        Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y
  liftStep :
    ∀ (x : ChainFiberPoint (word ++ [orient]) key) (b : data.Base),
      data.baseStep (proj x) b →
        ∃ y : ChainFiberPoint (word ++ [orient]) key,
          proj y = b ∧
            Reach (chainFiberRootClosureStep (word ++ [orient]) key) x y

structure ChainFiberAppendQuotientFibrationPathRowsFields
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor) : Type 1 where
  Base : Type
  baseDecidableEq : DecidableEq Base
  baseStep : Base → Base → Prop
  proj : ChainFiberPoint (word ++ [orient]) key → Base
  totalDecidableEq :
    DecidableEq (ChainFiberPoint (word ++ [orient]) key)
  fiberReachRows :
    ∀ x y : ChainFiberPoint (word ++ [orient]) key,
      proj x = proj y →
        @ParentRowsReachCertificate
          (ChainFiberPoint (word ++ [orient]) key) totalDecidableEq
          (chainFiberRootClosureStep (word ++ [orient]) key) x y
  liftStepRows :
    ∀ (x : ChainFiberPoint (word ++ [orient]) key) (b : Base),
      baseStep (proj x) b →
        Sigma (fun y : { y : ChainFiberPoint (word ++ [orient]) key //
            proj y = b } =>
            @ParentRowsReachCertificate
              (ChainFiberPoint (word ++ [orient]) key) totalDecidableEq
              (chainFiberRootClosureStep (word ++ [orient]) key) x y.1)
  baseParentRowsSymmetricRooted :
    @ParentRowsSymmetricRootedConnectedCertificate
      Base baseDecidableEq baseStep

def ChainFiberAppendQuotientFibrationParentRowsFields.ofPathRows
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {orient : GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (fields :
      ChainFiberAppendQuotientFibrationPathRowsFields word orient key) :
    ChainFiberAppendQuotientFibrationParentRowsFields word orient key :=
  letI := fields.totalDecidableEq
  { Base := fields.Base
    baseDecidableEq := fields.baseDecidableEq
    baseStep := fields.baseStep
    proj := fields.proj
    fiberReach := fun x y hproj =>
      (fields.fiberReachRows x y hproj).reach
    liftStep := fun x b hstep => by
      rcases fields.liftStepRows x b hstep with ⟨y, cert⟩
      exact ⟨y.1, y.2, cert.reach⟩
    baseParentRowsSymmetricRooted := fields.baseParentRowsSymmetricRooted }

def ChainFiberAppendQuotientFibrationParentRowsFields.ofBaseDataAndStructural
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {orient : GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (data :
      ChainFiberAppendQuotientFibrationParentRowsBaseData
        word orient key)
    (structural :
      ChainFiberAppendQuotientFibrationParentRowsStructuralFields data) :
    ChainFiberAppendQuotientFibrationParentRowsFields word orient key :=
  { Base := data.Base
    baseDecidableEq := data.baseDecidableEq
    baseStep := data.baseStep
    proj := structural.proj
    fiberReach := structural.fiberReach
    liftStep := structural.liftStep
    baseParentRowsSymmetricRooted := data.baseParentRowsSymmetricRooted }

def ChainFiberAppendQuotientFibrationParentRowsFields.ofConcreteAppend
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {orient : GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (hkey : key ∈ GoertzelLemma814.colorAssignments4)
    (cert :
      ChainWordConcreteFibrationCertificate (word ++ [orient])) :
    ChainFiberAppendQuotientFibrationParentRowsFields word orient key :=
  let baseStep : Unit → Unit → Prop := fun _ _ => True
  { Base := Unit
    baseDecidableEq := inferInstance
    baseStep := baseStep
    proj := fun _ => ()
    fiberReach := by
      intro x y _hproj
      rcases cert.fiberCertificate key hkey with ⟨fiberCert⟩
      exact fiberCert.connected x y
    liftStep := by
      intro x b _hstep
      cases b
      exact ⟨x, rfl, Reach.refl x⟩
    baseParentRowsSymmetricRooted :=
      unitParentRowsSymmetricRootedConnectedCertificate baseStep }

noncomputable def ChainFiberAppendQuotientFibrationParentRowsBaseData.ofPrefixRootStar
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {orient : GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (hcert : Nonempty (ChainWordConcreteFibrationCertificate word))
    (hkey : key ∈ GoertzelLemma814.colorAssignments4)
    {root : List GoertzelLemma814.TauState}
    {rest : List (List GoertzelLemma814.TauState)}
    (hfiber : concreteChainFiber word key = root :: rest) :
    ChainFiberAppendQuotientFibrationParentRowsBaseData word orient key :=
  letI : DecidableEq (ChainFiberPoint word key) := Classical.decEq _
  let baseStep := chainFiberRootClosureStep word key
  let rootPoint : ChainFiberPoint word key :=
    ⟨root, by simp [hfiber]⟩
  let nodes : List (ChainFiberPoint word key) :=
    (concreteChainFiber word key).attach
  let rootMem : rootPoint ∈ nodes := by
    exact List.mem_attach _ _
  let rootClose :
      rootPoint.1 ∈ GoertzelLemma814.closeChainFiber
        (frontierWordToChainWord word)
        (concreteChainFiber word key)
        (concreteChainFiber word key).length
        [chainFiberRootState word key] := by
    have hseen :
        root ∈ ([root] : List (List GoertzelLemma814.TauState)) := by
      simp
    simpa [rootPoint, chainFiberRootState, GoertzelLemma814.listGetD,
      hfiber] using
      GoertzelLemma814.closeChainFiber_mem_of_seen
        (frontierWordToChainWord word)
        (concreteChainFiber word key)
        (concreteChainFiber word key).length
        [root] root hseen
  { Base := ChainFiberPoint word key
    baseDecidableEq := inferInstance
    baseStep := baseStep
    baseParentRowsSymmetricRooted :=
      rootStarParentRowsSymmetricRootedConnectedCertificate
        nodes rootPoint rootMem
        (by
          intro x
          exact List.mem_attach _ _)
        (by
          intro x _y _hstep
          exact chainFiberPoint_mem_rootClosure_of_concreteCertificate
            hcert hkey x)
        (by
          intro _x
          simpa [baseStep, chainFiberRootClosureStep] using rootClose) }

def ChainFiberAppendQuotientFibrationParentRowsBaseData.unit
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {orient : GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor} :
    ChainFiberAppendQuotientFibrationParentRowsBaseData word orient key :=
  let baseStep : Unit → Unit → Prop := fun _ _ => True
  { Base := Unit
    baseDecidableEq := inferInstance
    baseStep := baseStep
    baseParentRowsSymmetricRooted :=
      unitParentRowsSymmetricRootedConnectedCertificate baseStep }

def ChainFiberAppendQuotientFibrationParentMapFields.ofParentRows
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {orient : GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (fields :
      ChainFiberAppendQuotientFibrationParentRowsFields word orient key) :
    ChainFiberAppendQuotientFibrationParentMapFields word orient key :=
  letI := fields.baseDecidableEq
  { Base := fields.Base
    baseStep := fields.baseStep
    proj := fields.proj
    fiberReach := fields.fiberReach
    liftStep := fields.liftStep
    baseParentMapSymmetricRooted :=
      fields.baseParentRowsSymmetricRooted.toParentMap }

def ChainFiberAppendQuotientFibrationListedSymmetricRootFields.ofParentMap
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {orient : GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (fields :
      ChainFiberAppendQuotientFibrationParentMapFields word orient key) :
    ChainFiberAppendQuotientFibrationListedSymmetricRootFields
      word orient key :=
  { Base := fields.Base
    baseStep := fields.baseStep
    proj := fields.proj
    fiberReach := fields.fiberReach
    liftStep := fields.liftStep
    baseListedSymmetricRooted :=
      fields.baseParentMapSymmetricRooted.toListed }

def ChainFiberAppendQuotientFibrationSymmetricRootFields.ofListed
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {orient : GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (fields :
      ChainFiberAppendQuotientFibrationListedSymmetricRootFields
        word orient key) :
    ChainFiberAppendQuotientFibrationSymmetricRootFields word orient key :=
  { Base := fields.Base
    baseStep := fields.baseStep
    proj := fields.proj
    fiberReach := fields.fiberReach
    liftStep := fields.liftStep
    baseSymmetricRooted :=
      fields.baseListedSymmetricRooted.toSymmetricRooted }

def ChainFiberAppendQuotientFibrationRootFields.ofSymmetricRootFields
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {orient : GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (fields :
      ChainFiberAppendQuotientFibrationSymmetricRootFields word orient key) :
    ChainFiberAppendQuotientFibrationRootFields word orient key :=
  { Base := fields.Base
    baseStep := fields.baseStep
    proj := fields.proj
    fiberReach := fields.fiberReach
    liftStep := fields.liftStep
    baseRooted := fields.baseSymmetricRooted.toRooted }

def ChainFiberAppendQuotientFibrationFields.ofRootFields
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {orient : GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (fields : ChainFiberAppendQuotientFibrationRootFields word orient key) :
    ChainFiberAppendQuotientFibrationFields word orient key :=
  { Base := fields.Base
    baseStep := fields.baseStep
    proj := fields.proj
    fiberReach := fields.fiberReach
    liftStep := fields.liftStep
    baseConnected := fields.baseRooted.connected }

def ChainFiberAppendQuotientFibrationLift.ofFields
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {orient : GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (fields : ChainFiberAppendQuotientFibrationFields word orient key) :
    ChainFiberAppendQuotientFibrationLift word orient key :=
  { Base := fields.Base
    baseStep := fields.baseStep
    proj := fields.proj
    fibration :=
      { fiberReach := fields.fiberReach
        liftStep := fields.liftStep }
    baseConnected := fields.baseConnected }

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

def concreteChainFiberAppendQuotientFibrationClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          Nonempty (ChainFiberAppendQuotientFibrationLift word orient key)

def concreteChainFiberAppendQuotientFibrationFieldsClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          Nonempty (ChainFiberAppendQuotientFibrationFields word orient key)

def concreteChainFiberAppendQuotientFibrationRootFieldsClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          Nonempty (ChainFiberAppendQuotientFibrationRootFields word orient key)

def concreteChainFiberAppendQuotientFibrationSymmetricRootFieldsClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          Nonempty
            (ChainFiberAppendQuotientFibrationSymmetricRootFields
              word orient key)

def concreteChainFiberAppendQuotientFibrationListedSymmetricRootFieldsClosed :
    Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          Nonempty
            (ChainFiberAppendQuotientFibrationListedSymmetricRootFields
              word orient key)

def concreteChainFiberAppendQuotientFibrationParentMapFieldsClosed :
    Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          Nonempty
            (ChainFiberAppendQuotientFibrationParentMapFields
              word orient key)

def concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed :
    Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          Nonempty
            (ChainFiberAppendQuotientFibrationParentRowsFields
              word orient key)

def concreteChainFiberAppendQuotientFibrationPathRowsFieldsClosed :
    Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    word ≠ [] →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          Nonempty
            (ChainFiberAppendQuotientFibrationPathRowsFields
              word orient key)

theorem concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_path_rows
    (hFields :
      concreteChainFiberAppendQuotientFibrationPathRowsFieldsClosed) :
    concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed := by
  intro word orient hne hcert key hkey
  rcases hFields word orient hne hcert key hkey with ⟨fields⟩
  exact ⟨ChainFiberAppendQuotientFibrationParentRowsFields.ofPathRows
    fields⟩

theorem concreteChainFiberAppendQuotientFibrationParentMapFieldsClosed_of_parent_rows
    (hFields :
      concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed) :
    concreteChainFiberAppendQuotientFibrationParentMapFieldsClosed := by
  intro word orient hne hcert key hkey
  rcases hFields word orient hne hcert key hkey with ⟨fields⟩
  exact ⟨ChainFiberAppendQuotientFibrationParentMapFields.ofParentRows
    fields⟩

theorem concreteChainFiberAppendQuotientFibrationListedSymmetricRootFieldsClosed_of_parent_map
    (hFields :
      concreteChainFiberAppendQuotientFibrationParentMapFieldsClosed) :
    concreteChainFiberAppendQuotientFibrationListedSymmetricRootFieldsClosed := by
  intro word orient hne hcert key hkey
  rcases hFields word orient hne hcert key hkey with ⟨fields⟩
  exact ⟨ChainFiberAppendQuotientFibrationListedSymmetricRootFields.ofParentMap
    fields⟩

theorem concreteChainFiberAppendQuotientFibrationSymmetricRootFieldsClosed_of_listed
    (hFields :
      concreteChainFiberAppendQuotientFibrationListedSymmetricRootFieldsClosed) :
    concreteChainFiberAppendQuotientFibrationSymmetricRootFieldsClosed := by
  intro word orient hne hcert key hkey
  rcases hFields word orient hne hcert key hkey with ⟨fields⟩
  exact ⟨ChainFiberAppendQuotientFibrationSymmetricRootFields.ofListed
    fields⟩

theorem concreteChainFiberAppendQuotientFibrationRootFieldsClosed_of_symmetric
    (hFields :
      concreteChainFiberAppendQuotientFibrationSymmetricRootFieldsClosed) :
    concreteChainFiberAppendQuotientFibrationRootFieldsClosed := by
  intro word orient hne hcert key hkey
  rcases hFields word orient hne hcert key hkey with ⟨fields⟩
  exact ⟨ChainFiberAppendQuotientFibrationRootFields.ofSymmetricRootFields
    fields⟩

theorem concreteChainFiberAppendQuotientFibrationFieldsClosed_of_root_fields
    (hFields : concreteChainFiberAppendQuotientFibrationRootFieldsClosed) :
    concreteChainFiberAppendQuotientFibrationFieldsClosed := by
  intro word orient hne hcert key hkey
  rcases hFields word orient hne hcert key hkey with ⟨fields⟩
  exact ⟨ChainFiberAppendQuotientFibrationFields.ofRootFields fields⟩

theorem concreteChainFiberAppendQuotientFibrationClosed_of_fields
    (hFields : concreteChainFiberAppendQuotientFibrationFieldsClosed) :
    concreteChainFiberAppendQuotientFibrationClosed := by
  intro word orient hne hcert key hkey
  rcases hFields word orient hne hcert key hkey with ⟨fields⟩
  exact ⟨ChainFiberAppendQuotientFibrationLift.ofFields fields⟩

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

def concreteChainFiberAppendLastInputTrace
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (last : GoertzelLemma814.TauState) : List GoertzelLemma814.LColor :=
  (GoertzelLemma814.tauOrientInputOrder (frontierOrientToChain orient)).map
    fun edge => last.color edge

theorem colorAssignments4_mem_tuple
    (c0 c1 c2 c3 : GoertzelLemma814.LColor) :
    [c0, c1, c2, c3] ∈ GoertzelLemma814.colorAssignments4 := by
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> decide

theorem concreteChainFiberAppendLastInputTrace_mem_colorAssignments4
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (last : GoertzelLemma814.TauState) :
    concreteChainFiberAppendLastInputTrace orient last ∈
      GoertzelLemma814.colorAssignments4 := by
  cases orient <;>
    simp [concreteChainFiberAppendLastInputTrace, frontierOrientToChain,
      GoertzelLemma814.tauOrientInputOrder, colorAssignments4_mem_tuple]

theorem concreteChainFiberAppendLastInputTrace_eq_of_compatible
    (left : GoertzelLemma814.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (prev lastX lastY : GoertzelLemma814.TauState)
    (hx : GoertzelLemma814.compatibleAdjacent left (frontierOrientToChain orient)
      prev lastX = true)
    (hy : GoertzelLemma814.compatibleAdjacent left (frontierOrientToChain orient)
      prev lastY = true) :
    concreteChainFiberAppendLastInputTrace orient lastX =
      concreteChainFiberAppendLastInputTrace orient lastY := by
  cases left <;> cases orient <;>
    simp [concreteChainFiberAppendLastInputTrace, frontierOrientToChain,
      GoertzelLemma814.compatibleAdjacent, GoertzelLemma814.colorEq,
      GoertzelLemma814.tauOrientInputOrder,
      GoertzelLemma814.tauOrientOutputOrder] at hx hy ⊢ <;>
    aesop

theorem concreteChainFiber_singleton_mem_of_last_input_trace
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    {last : GoertzelLemma814.TauState}
    (hlast : last ∈ GoertzelLemma814.allTauStates) :
    [last] ∈ concreteChainFiber [orient]
      (concreteChainFiberAppendLastInputTrace orient last) := by
  unfold concreteChainFiber GoertzelLemma814.chainFiberFrom concreteChainStates
  rw [List.mem_filter]
  constructor
  · cases orient <;>
      simp [frontierWordToChainWord, frontierOrientToChain,
        GoertzelLemma814.allChainStates, GoertzelLemma814.buildChainStatesFrom,
        hlast]
  · cases orient <;>
      simp [frontierWordToChainWord, frontierOrientToChain,
        GoertzelLemma814.chainInputKey, GoertzelLemma814.chainInputOrder,
        GoertzelLemma814.tauOrientInputOrder, GoertzelLemma814.tauOrientAt,
        GoertzelLemma814.listGetD, GoertzelLemma814.chainStateAt,
        GoertzelLemma814.tauStateColorAt, concreteChainFiberAppendLastInputTrace]

theorem concreteChainFiber_singleton_of_mem
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor)
    {states : List GoertzelLemma814.TauState}
    (hstates : states ∈ concreteChainFiber [orient] key) :
    ∃ last : GoertzelLemma814.TauState, states = [last] := by
  have hmemStates : states ∈ concreteChainStates [orient] := by
    unfold concreteChainFiber GoertzelLemma814.chainFiberFrom at hstates
    exact (List.mem_filter.mp hstates).1
  have hlen :=
    GoertzelLemma814.allChainStates_mem_length
      (orients := frontierWordToChainWord [orient]) hmemStates
  cases states with
  | nil =>
      simp [frontierWordToChainWord] at hlen
  | cons last rest =>
      cases rest with
      | nil =>
          exact ⟨last, rfl⟩
      | cons next rest =>
          simp [frontierWordToChainWord] at hlen

theorem concreteChainFiber_singleton_last_mem_allTauStates
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor)
    {last : GoertzelLemma814.TauState}
    (hstates : [last] ∈ concreteChainFiber [orient] key) :
    last ∈ GoertzelLemma814.allTauStates := by
  have hmemStates : [last] ∈ concreteChainStates [orient] := by
    unfold concreteChainFiber GoertzelLemma814.chainFiberFrom at hstates
    exact (List.mem_filter.mp hstates).1
  cases orient <;>
    simpa [concreteChainStates, frontierWordToChainWord, frontierOrientToChain,
      GoertzelLemma814.allChainStates, GoertzelLemma814.buildChainStatesFrom]
      using hmemStates

theorem concreteChainFiber_singleton_input_trace_eq_of_mem
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor)
    {last : GoertzelLemma814.TauState}
    (hstates : [last] ∈ concreteChainFiber [orient] key) :
    concreteChainFiberAppendLastInputTrace orient last = key := by
  have hkeyBool :
      (GoertzelLemma814.chainInputKey (frontierWordToChainWord [orient])
        [last] == key) = true := by
    unfold concreteChainFiber GoertzelLemma814.chainFiberFrom at hstates
    exact (List.mem_filter.mp hstates).2
  have hkeyEq :
      GoertzelLemma814.chainInputKey (frontierWordToChainWord [orient])
        [last] = key :=
    beq_iff_eq.mp hkeyBool
  rw [← hkeyEq]
  cases orient <;>
    simp [concreteChainFiberAppendLastInputTrace, frontierWordToChainWord,
      frontierOrientToChain, GoertzelLemma814.chainInputKey,
      GoertzelLemma814.chainInputOrder, GoertzelLemma814.tauOrientAt,
      GoertzelLemma814.listGetD, GoertzelLemma814.tauOrientInputOrder,
      GoertzelLemma814.chainStateAt, GoertzelLemma814.tauStateColorAt]

theorem concreteChainFiberAppend_compatible_of_last_input_trace_eq
    (left : GoertzelLemma814.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (prev lastX lastY : GoertzelLemma814.TauState)
    (hcompatibleX : GoertzelLemma814.compatibleAdjacent
      left (frontierOrientToChain orient) prev lastX = true)
    (hinput : concreteChainFiberAppendLastInputTrace orient lastY =
      concreteChainFiberAppendLastInputTrace orient lastX) :
    GoertzelLemma814.compatibleAdjacent
      left (frontierOrientToChain orient) prev lastY = true := by
  cases left <;> cases orient <;>
    simp [concreteChainFiberAppendLastInputTrace, frontierOrientToChain,
      GoertzelLemma814.compatibleAdjacent, GoertzelLemma814.colorEq,
      GoertzelLemma814.tauOrientInputOrder,
      GoertzelLemma814.tauOrientOutputOrder] at hcompatibleX hinput ⊢ <;>
    aesop

theorem concreteChainFiberAppend_mem_of_prefix_and_local_singleton
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ [])
    (key : List GoertzelLemma814.LColor)
    {pref : List GoertzelLemma814.TauState}
    {lastX targetLast : GoertzelLemma814.TauState}
    {target : List GoertzelLemma814.TauState}
    (hpref : pref ∈ concreteChainFiber word key)
    (hcompatibleX : GoertzelLemma814.compatibleAdjacent
      (GoertzelLemma814.tauOrientAt
        (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
      (GoertzelLemma814.tauOrientAt
        (frontierWordToChainWord (word ++ [orient])) word.length)
      (GoertzelLemma814.chainStateAt pref (word.length - 1))
      lastX = true)
    (htarget : target ∈ concreteChainFiber [orient]
      (concreteChainFiberAppendLastInputTrace orient lastX))
    (htargetEq : target = [targetLast]) :
    pref ++ [targetLast] ∈ concreteChainFiber (word ++ [orient]) key := by
  have htargetMem :
      [targetLast] ∈ concreteChainFiber [orient]
        (concreteChainFiberAppendLastInputTrace orient lastX) := by
    simpa [htargetEq] using htarget
  have htargetAll :
      targetLast ∈ GoertzelLemma814.allTauStates :=
    concreteChainFiber_singleton_last_mem_allTauStates orient
      (concreteChainFiberAppendLastInputTrace orient lastX) htargetMem
  have hinputTarget :
      concreteChainFiberAppendLastInputTrace orient targetLast =
        concreteChainFiberAppendLastInputTrace orient lastX :=
    concreteChainFiber_singleton_input_trace_eq_of_mem orient
      (concreteChainFiberAppendLastInputTrace orient lastX) htargetMem
  have hright :=
    tauOrientAt_frontierWordToChainWord_append_length word orient
  have hcompatibleX' :
      GoertzelLemma814.compatibleAdjacent
        (GoertzelLemma814.tauOrientAt
          (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
        (frontierOrientToChain orient)
        (GoertzelLemma814.chainStateAt pref (word.length - 1)) lastX =
        true := by
    simpa [hright] using hcompatibleX
  have hcompatibleTarget' :
      GoertzelLemma814.compatibleAdjacent
        (GoertzelLemma814.tauOrientAt
          (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
        (frontierOrientToChain orient)
        (GoertzelLemma814.chainStateAt pref (word.length - 1)) targetLast =
        true :=
    concreteChainFiberAppend_compatible_of_last_input_trace_eq
      (GoertzelLemma814.tauOrientAt
        (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
      orient (GoertzelLemma814.chainStateAt pref (word.length - 1))
      lastX targetLast hcompatibleX' hinputTarget
  have hcompatibleTarget :
      GoertzelLemma814.compatibleAdjacent
        (GoertzelLemma814.tauOrientAt
          (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
        (GoertzelLemma814.tauOrientAt
          (frontierWordToChainWord (word ++ [orient])) word.length)
        (GoertzelLemma814.chainStateAt pref (word.length - 1)) targetLast =
        true := by
    simpa [hright] using hcompatibleTarget'
  exact concreteChainFiberAppend_mem_of_prefix_last
    word orient hne key hpref htargetAll hcompatibleTarget

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

def concreteChainFiberAppendSameTraceRelativeSingletonReachClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
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
              ∃ (_hkeyLocal :
                  concreteChainFiberAppendLastInputTrace orient lastX ∈
                    GoertzelLemma814.colorAssignments4)
                (xLocal : ChainFiberPoint [orient]
                  (concreteChainFiberAppendLastInputTrace orient lastX))
                (yLocal : ChainFiberPoint [orient]
                  (concreteChainFiberAppendLastInputTrace orient lastX)),
                xLocal.1 = [lastX] ∧
                  yLocal.1 = [lastY] ∧
                    Reach
                      (chainFiberRootClosureStep [orient]
                        (concreteChainFiberAppendLastInputTrace orient lastX))
                      xLocal yLocal

def concreteChainFiberAppendRelativeSingletonLiftClosed : Prop :=
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
            ∀ (_hkeyLocal :
                concreteChainFiberAppendLastInputTrace orient lastX ∈
                  GoertzelLemma814.colorAssignments4)
              (xLocal : ChainFiberPoint [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX))
              (yLocal : ChainFiberPoint [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX)),
              xLocal.1 = [lastX] →
                yLocal.1 = [lastY] →
                  Reach
                    (chainFiberRootClosureStep [orient]
                      (concreteChainFiberAppendLastInputTrace orient lastX))
                    xLocal yLocal →
                    Reach (chainFiberRootClosureStep (word ++ [orient]) key)
                      (⟨pref ++ [lastX],
                        concreteChainFiberAppend_mem_of_prefix_last
                          word orient hne key hpref hlastX hcompatibleX⟩ :
                        ChainFiberPoint (word ++ [orient]) key)
                      (⟨pref ++ [lastY],
                        concreteChainFiberAppend_mem_of_prefix_last
                          word orient hne key hpref hlastY hcompatibleY⟩ :
                        ChainFiberPoint (word ++ [orient]) key)

def concreteChainFiberAppendRelativeSingletonClosureLiftClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX lastY : GoertzelLemma814.TauState),
            (_hpref : pref ∈ concreteChainFiber word key) →
            (_hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (_hlastY : lastY ∈ GoertzelLemma814.allTauStates) →
            (_hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            (_hcompatibleY : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastY = true) →
            ∀ (_hkeyLocal :
                concreteChainFiberAppendLastInputTrace orient lastX ∈
                  GoertzelLemma814.colorAssignments4)
              (yLocal : ChainFiberPoint [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX)),
              yLocal.1 = [lastY] →
                yLocal.1 ∈ GoertzelLemma814.closeChainFiber
                  (frontierWordToChainWord [orient])
                  (concreteChainFiber [orient]
                    (concreteChainFiberAppendLastInputTrace orient lastX))
                  (concreteChainFiber [orient]
                    (concreteChainFiberAppendLastInputTrace orient lastX)).length
                  [chainFiberRootState [orient]
                    (concreteChainFiberAppendLastInputTrace orient lastX)] →
                  pref ++ [lastY] ∈ GoertzelLemma814.closeChainFiber
                    (frontierWordToChainWord (word ++ [orient]))
                    (concreteChainFiber (word ++ [orient]) key)
                    (concreteChainFiber (word ++ [orient]) key).length
                    [chainFiberRootState (word ++ [orient]) key]

def concreteChainFiberAppendRelativeSingletonClosureRootLiftClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX : GoertzelLemma814.TauState),
            (_hpref : pref ∈ concreteChainFiber word key) →
            (_hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (_hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            ∀ (_hkeyLocal :
                concreteChainFiberAppendLastInputTrace orient lastX ∈
                  GoertzelLemma814.colorAssignments4),
              ∃ rootLast : GoertzelLemma814.TauState,
                chainFiberRootState [orient]
                    (concreteChainFiberAppendLastInputTrace orient lastX) =
                  [rootLast] ∧
                pref ++ [rootLast] ∈ GoertzelLemma814.closeChainFiber
                  (frontierWordToChainWord (word ++ [orient]))
                  (concreteChainFiber (word ++ [orient]) key)
                  (concreteChainFiber (word ++ [orient]) key).length
                  [chainFiberRootState (word ++ [orient]) key]

def concreteChainFiberAppendRelativeSingletonClosureStepLiftClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX : GoertzelLemma814.TauState),
            (_hpref : pref ∈ concreteChainFiber word key) →
            (_hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (_hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            ∀ (_hkeyLocal :
                concreteChainFiberAppendLastInputTrace orient lastX ∈
                  GoertzelLemma814.colorAssignments4)
              (current target : List GoertzelLemma814.TauState)
              (currentLast targetLast : GoertzelLemma814.TauState),
              current ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              target ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              current = [currentLast] →
              target = [targetLast] →
              pref ++ [currentLast] ∈ GoertzelLemma814.closeChainFiber
                (frontierWordToChainWord (word ++ [orient]))
                (concreteChainFiber (word ++ [orient]) key)
                (concreteChainFiber (word ++ [orient]) key).length
                [chainFiberRootState (word ++ [orient]) key] →
              GoertzelLemma814.chainSingleKempeStep
                (frontierWordToChainWord [orient]) current target = true →
              pref ++ [targetLast] ∈ GoertzelLemma814.closeChainFiber
                (frontierWordToChainWord (word ++ [orient]))
                (concreteChainFiber (word ++ [orient]) key)
                (concreteChainFiber (word ++ [orient]) key).length
                [chainFiberRootState (word ++ [orient]) key]

def concreteChainFiberAppendRelativeSingletonGlobalKempeStepLiftClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX : GoertzelLemma814.TauState),
            (_hpref : pref ∈ concreteChainFiber word key) →
            (_hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (_hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            ∀ (_hkeyLocal :
                concreteChainFiberAppendLastInputTrace orient lastX ∈
                  GoertzelLemma814.colorAssignments4)
              (current target : List GoertzelLemma814.TauState)
              (currentLast targetLast : GoertzelLemma814.TauState),
              current ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              target ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              current = [currentLast] →
              target = [targetLast] →
              GoertzelLemma814.chainSingleKempeStep
                (frontierWordToChainWord [orient]) current target = true →
              GoertzelLemma814.chainSingleKempeStep
                (frontierWordToChainWord (word ++ [orient]))
                (pref ++ [currentLast]) (pref ++ [targetLast]) = true

def concreteChainFiberAppendRelativeSingletonSpecifiedKempeStepLiftClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX : GoertzelLemma814.TauState),
            (_hpref : pref ∈ concreteChainFiber word key) →
            (_hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (_hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            ∀ (_hkeyLocal :
                concreteChainFiberAppendLastInputTrace orient lastX ∈
                  GoertzelLemma814.colorAssignments4)
              (current target : List GoertzelLemma814.TauState)
              (currentLast targetLast : GoertzelLemma814.TauState),
              current ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              target ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              current = [currentLast] →
              target = [targetLast] →
              ∀ (move : GoertzelLemma814.ChainMove),
                GoertzelLemma814.colorPairs.contains (move.a, move.c) = true →
                (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
                  move.seed = true →
                GoertzelLemma814.chainSpecifiedKempeStep
                  (frontierWordToChainWord [orient]) current target move = true →
                GoertzelLemma814.chainSingleKempeStep
                  (frontierWordToChainWord (word ++ [orient]))
                  (pref ++ [currentLast]) (pref ++ [targetLast]) = true

def concreteChainFiberAppendShiftMove
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (move : GoertzelLemma814.ChainMove) : GoertzelLemma814.ChainMove :=
  { a := move.a
    c := move.c
    seed :=
      { occ := move.seed.occ + word.length
        edge := move.seed.edge } }

def concreteChainFiberAppendShiftEdge
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (edge : GoertzelLemma814.ChainEdge) : GoertzelLemma814.ChainEdge :=
  { occ := edge.occ + word.length
    edge := edge.edge }

theorem concreteChainFiberAppendShiftEdge_injective
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    Function.Injective (concreteChainFiberAppendShiftEdge word) := by
  intro edge other h
  cases edge with
  | mk edgeOcc edgeTau =>
      cases other with
      | mk otherOcc otherTau =>
          have hocc : edgeOcc + word.length = otherOcc + word.length := by
            simpa [concreteChainFiberAppendShiftEdge] using
              congrArg GoertzelLemma814.ChainEdge.occ h
          have htau : edgeTau = otherTau := by
            simpa [concreteChainFiberAppendShiftEdge] using
              congrArg GoertzelLemma814.ChainEdge.edge h
          subst htau
          have : edgeOcc = otherOcc := by omega
          subst this
          rfl

theorem concreteChainFiberAppend_chainEdgeColor_shift_occ_zero
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (pref : List GoertzelLemma814.TauState)
    (last : GoertzelLemma814.TauState)
    (edge : GoertzelLemma814.ChainEdge)
    (hprefLen : pref.length = word.length)
    (hocc : edge.occ = 0) :
    GoertzelLemma814.chainEdgeColor (pref ++ [last])
        (concreteChainFiberAppendShiftEdge word edge) =
      GoertzelLemma814.chainEdgeColor [last] edge := by
  cases edge with
  | mk occ tauEdge =>
      simp at hocc
      subst occ
      have hstate :
          GoertzelLemma814.chainStateAt (pref ++ [last]) word.length = last :=
        GoertzelLemma814.chainStateAt_append_length pref last word.length hprefLen
      calc
        GoertzelLemma814.chainEdgeColor (pref ++ [last])
            (concreteChainFiberAppendShiftEdge word
              ({ occ := 0, edge := tauEdge } : GoertzelLemma814.ChainEdge)) =
          (GoertzelLemma814.chainStateAt (pref ++ [last]) word.length).color
            tauEdge := by
              simp [concreteChainFiberAppendShiftEdge,
                GoertzelLemma814.chainEdgeColor,
                GoertzelLemma814.tauStateColorAt]
        _ = last.color tauEdge := by
              rw [hstate]
        _ =
          GoertzelLemma814.chainEdgeColor [last]
            ({ occ := 0, edge := tauEdge } : GoertzelLemma814.ChainEdge) := by
              simp [GoertzelLemma814.chainEdgeColor,
                GoertzelLemma814.tauStateColorAt,
                GoertzelLemma814.chainStateAt, GoertzelLemma814.listGetD]

theorem concreteChainFiberAppend_chainEdgesShareEndpoint_shift_occ_zero
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (edge other : GoertzelLemma814.ChainEdge)
    (hedgeOcc : edge.occ = 0)
    (hotherOcc : other.occ = 0)
    (hedgeNotInput :
      (GoertzelLemma814.tauOrientInputOrder (frontierOrientToChain orient)).contains
        edge.edge = false)
    (hotherNotInput :
      (GoertzelLemma814.tauOrientInputOrder (frontierOrientToChain orient)).contains
        other.edge = false) :
    GoertzelLemma814.chainEdgesShareEndpoint
        (frontierWordToChainWord (word ++ [orient]))
        (concreteChainFiberAppendShiftEdge word edge)
        (concreteChainFiberAppendShiftEdge word other) =
      GoertzelLemma814.chainEdgesShareEndpoint
        (frontierWordToChainWord [orient]) edge other := by
  cases edge with
  | mk edgeOcc edgeTau =>
      cases other with
      | mk otherOcc otherTau =>
          simp at hedgeOcc hotherOcc
          subst edgeOcc
          subst otherOcc
          generalize hlen : word.length = n
          cases n <;>
          cases orient <;> cases edgeTau <;> cases otherTau <;>
            simp [concreteChainFiberAppendShiftEdge,
              GoertzelLemma814.chainEdgesShareEndpoint,
              GoertzelLemma814.chainEdgeEndpoints,
              GoertzelLemma814.chainIsGluedOutput,
              GoertzelLemma814.tauOrientAt,
              GoertzelLemma814.tauOrientInputOrder,
              frontierWordToChainWord, frontierOrientToChain,
              hlen,
              GoertzelLemma814.listGetD,
              GoertzelLemma814.edgeEndpoints,
              GoertzelLemma814.tauEndpointToChainEndpoint,
              GoertzelLemma814.isInternalEndpoint,
              Bool.beq_eq_decide_eq] at hedgeNotInput hotherNotInput ⊢

def chainEndpointOcc : GoertzelLemma814.ChainEndpoint → Nat
  | GoertzelLemma814.ChainEndpoint.internal occ _ => occ
  | GoertzelLemma814.ChainEndpoint.boundary occ _ => occ

theorem chainEndpointOcc_tauEndpointToChainEndpoint
    (i : Nat) (v : GoertzelLemma814.TauEndpoint) :
    chainEndpointOcc (GoertzelLemma814.tauEndpointToChainEndpoint i v) =
      i := by
  unfold GoertzelLemma814.tauEndpointToChainEndpoint
  by_cases h : GoertzelLemma814.isInternalEndpoint v = true <;>
    simp [h, chainEndpointOcc]

theorem chainEdgeEndpoints_fst_occ
    (orients : List GoertzelLemma814.TauOrient)
    (ge : GoertzelLemma814.ChainEdge) :
    chainEndpointOcc
        (GoertzelLemma814.chainEdgeEndpoints orients ge).1 =
      ge.occ := by
  unfold GoertzelLemma814.chainEdgeEndpoints
  split
  · split
    · simp [chainEndpointOcc]
    · exact chainEndpointOcc_tauEndpointToChainEndpoint ge.occ
        (GoertzelLemma814.edgeEndpoints ge.edge).1
  · exact chainEndpointOcc_tauEndpointToChainEndpoint ge.occ
      (GoertzelLemma814.edgeEndpoints ge.edge).1

theorem chainEdgeEndpoints_snd_occ_eq_or_succ
    (orients : List GoertzelLemma814.TauOrient)
    (ge : GoertzelLemma814.ChainEdge) :
    chainEndpointOcc
          (GoertzelLemma814.chainEdgeEndpoints orients ge).2 =
        ge.occ ∨
      chainEndpointOcc
          (GoertzelLemma814.chainEdgeEndpoints orients ge).2 =
        ge.occ + 1 := by
  unfold GoertzelLemma814.chainEdgeEndpoints
  split
  · split
    · exact Or.inr (by simp [chainEndpointOcc])
    · exact Or.inl (chainEndpointOcc_tauEndpointToChainEndpoint ge.occ
        (GoertzelLemma814.edgeEndpoints ge.edge).2)
  · exact Or.inl (chainEndpointOcc_tauEndpointToChainEndpoint ge.occ
      (GoertzelLemma814.edgeEndpoints ge.edge).2)

theorem concreteChainFiberAppend_shift_endpoint_occs
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (localEdge : GoertzelLemma814.ChainEdge)
    (hlocalOcc : localEdge.occ = 0) :
    let shifted := concreteChainFiberAppendShiftEdge word localEdge
    chainEndpointOcc
        (GoertzelLemma814.chainEdgeEndpoints
          (frontierWordToChainWord (word ++ [orient])) shifted).1 =
        word.length ∧
      chainEndpointOcc
        (GoertzelLemma814.chainEdgeEndpoints
          (frontierWordToChainWord (word ++ [orient])) shifted).2 =
        word.length := by
  cases localEdge with
  | mk occ edge =>
      simp at hlocalOcc
      subst occ
      simp [concreteChainFiberAppendShiftEdge,
        GoertzelLemma814.chainEdgeEndpoints,
        GoertzelLemma814.chainIsGluedOutput, frontierWordToChainWord,
        chainEndpointOcc_tauEndpointToChainEndpoint]

theorem concreteChainFiberAppend_prefix_share_shift_occ_succ
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (ge localEdge : GoertzelLemma814.ChainEdge)
    (hprefix : ge.occ < word.length)
    (hlocalOcc : localEdge.occ = 0)
    (hshare :
      GoertzelLemma814.chainEdgesShareEndpoint
        (frontierWordToChainWord (word ++ [orient])) ge
        (concreteChainFiberAppendShiftEdge word localEdge) = true) :
    ge.occ + 1 = word.length := by
  let globalOrients := frontierWordToChainWord (word ++ [orient])
  let shifted := concreteChainFiberAppendShiftEdge word localEdge
  have hshiftOccs :=
    concreteChainFiberAppend_shift_endpoint_occs word orient localEdge
      hlocalOcc
  have hshiftFst :
      chainEndpointOcc
          (GoertzelLemma814.chainEdgeEndpoints globalOrients shifted).1 =
        word.length := by
    simpa [globalOrients, shifted] using hshiftOccs.1
  have hshiftSnd :
      chainEndpointOcc
          (GoertzelLemma814.chainEdgeEndpoints globalOrients shifted).2 =
        word.length := by
    simpa [globalOrients, shifted] using hshiftOccs.2
  by_cases hsame : (ge == shifted) = true
  · have hfalse : False := by
      unfold GoertzelLemma814.chainEdgesShareEndpoint at hshare
      rw [hsame] at hshare
      cases hshare
    exact False.elim hfalse
  · have hsameFalse := GoertzelLemma814.bool_false_of_not_true hsame
    have hshare' := hshare
    unfold GoertzelLemma814.chainEdgesShareEndpoint at hshare'
    simp [shifted, hsameFalse, Bool.beq_eq_decide_eq] at hshare'
    rcases hshare' with ((h | h) | h) | h
    · have hocc : ge.occ = word.length := by
        calc
          ge.occ =
              chainEndpointOcc
                (GoertzelLemma814.chainEdgeEndpoints globalOrients ge).1 := by
            exact (chainEdgeEndpoints_fst_occ globalOrients ge).symm
          _ =
              chainEndpointOcc
                (GoertzelLemma814.chainEdgeEndpoints globalOrients
                  shifted).1 := by
            rw [h]
          _ = word.length := hshiftFst
      omega
    · have hocc : ge.occ = word.length := by
        calc
          ge.occ =
              chainEndpointOcc
                (GoertzelLemma814.chainEdgeEndpoints globalOrients ge).1 := by
            exact (chainEdgeEndpoints_fst_occ globalOrients ge).symm
          _ =
              chainEndpointOcc
                (GoertzelLemma814.chainEdgeEndpoints globalOrients
                  shifted).2 := by
            rw [h]
          _ = word.length := hshiftSnd
      omega
    · rcases chainEdgeEndpoints_snd_occ_eq_or_succ globalOrients ge with
        hsnd | hsnd
      · have hocc : ge.occ = word.length := by
          calc
            ge.occ =
                chainEndpointOcc
                  (GoertzelLemma814.chainEdgeEndpoints globalOrients ge).2 := by
              exact hsnd.symm
            _ =
                chainEndpointOcc
                  (GoertzelLemma814.chainEdgeEndpoints globalOrients
                    shifted).1 := by
              rw [h]
            _ = word.length := hshiftFst
        omega
      · calc
          ge.occ + 1 =
              chainEndpointOcc
                (GoertzelLemma814.chainEdgeEndpoints globalOrients ge).2 := by
            exact hsnd.symm
          _ =
              chainEndpointOcc
                (GoertzelLemma814.chainEdgeEndpoints globalOrients
                  shifted).1 := by
            rw [h]
          _ = word.length := hshiftFst
    · rcases chainEdgeEndpoints_snd_occ_eq_or_succ globalOrients ge with
        hsnd | hsnd
      · have hocc : ge.occ = word.length := by
          calc
            ge.occ =
                chainEndpointOcc
                  (GoertzelLemma814.chainEdgeEndpoints globalOrients ge).2 := by
              exact hsnd.symm
            _ =
                chainEndpointOcc
                  (GoertzelLemma814.chainEdgeEndpoints globalOrients
                    shifted).2 := by
              rw [h]
            _ = word.length := hshiftSnd
        omega
      · calc
          ge.occ + 1 =
              chainEndpointOcc
                (GoertzelLemma814.chainEdgeEndpoints globalOrients ge).2 := by
            exact hsnd.symm
          _ =
              chainEndpointOcc
                (GoertzelLemma814.chainEdgeEndpoints globalOrients
                  shifted).2 := by
            rw [h]
          _ = word.length := hshiftSnd

theorem chainEdgeEndpoints_snd_occ_of_not_glued
    (orients : List GoertzelLemma814.TauOrient)
    (ge : GoertzelLemma814.ChainEdge)
    (hglued :
      GoertzelLemma814.chainIsGluedOutput orients ge.occ ge.edge = false) :
    chainEndpointOcc
        (GoertzelLemma814.chainEdgeEndpoints orients ge).2 =
      ge.occ := by
  unfold GoertzelLemma814.chainEdgeEndpoints
  rw [hglued]
  exact chainEndpointOcc_tauEndpointToChainEndpoint ge.occ
    (GoertzelLemma814.edgeEndpoints ge.edge).2

theorem concreteChainFiberAppend_prefix_share_shift_forces_glued_output
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (ge localEdge : GoertzelLemma814.ChainEdge)
    (hprefix : ge.occ < word.length)
    (hlocalOcc : localEdge.occ = 0)
    (hshare :
      GoertzelLemma814.chainEdgesShareEndpoint
        (frontierWordToChainWord (word ++ [orient])) ge
        (concreteChainFiberAppendShiftEdge word localEdge) = true) :
    GoertzelLemma814.chainIsGluedOutput
      (frontierWordToChainWord (word ++ [orient])) ge.occ ge.edge =
        true := by
  let globalOrients := frontierWordToChainWord (word ++ [orient])
  let shifted := concreteChainFiberAppendShiftEdge word localEdge
  by_cases hglued :
      GoertzelLemma814.chainIsGluedOutput globalOrients ge.occ ge.edge =
        true
  · simpa [globalOrients] using hglued
  · have hgluedFalse := GoertzelLemma814.bool_false_of_not_true hglued
    exfalso
    have hshiftOccs :=
      concreteChainFiberAppend_shift_endpoint_occs word orient localEdge
        hlocalOcc
    have hshiftFst :
        chainEndpointOcc
            (GoertzelLemma814.chainEdgeEndpoints globalOrients
              shifted).1 =
          word.length := by
      simpa [globalOrients, shifted] using hshiftOccs.1
    have hshiftSnd :
        chainEndpointOcc
            (GoertzelLemma814.chainEdgeEndpoints globalOrients
              shifted).2 =
          word.length := by
      simpa [globalOrients, shifted] using hshiftOccs.2
    have hgeSnd :
        chainEndpointOcc
            (GoertzelLemma814.chainEdgeEndpoints globalOrients ge).2 =
          ge.occ :=
      chainEdgeEndpoints_snd_occ_of_not_glued globalOrients ge hgluedFalse
    by_cases hsame : (ge == shifted) = true
    · unfold GoertzelLemma814.chainEdgesShareEndpoint at hshare
      rw [hsame] at hshare
      cases hshare
    · have hsameFalse := GoertzelLemma814.bool_false_of_not_true hsame
      have hshare' := hshare
      unfold GoertzelLemma814.chainEdgesShareEndpoint at hshare'
      simp [shifted, hsameFalse, Bool.beq_eq_decide_eq] at hshare'
      rcases hshare' with ((h | h) | h) | h
      · have hocc : ge.occ = word.length := by
          calc
            ge.occ =
                chainEndpointOcc
                  (GoertzelLemma814.chainEdgeEndpoints globalOrients ge).1 := by
              exact (chainEdgeEndpoints_fst_occ globalOrients ge).symm
            _ =
                chainEndpointOcc
                  (GoertzelLemma814.chainEdgeEndpoints globalOrients
                    shifted).1 := by
              rw [h]
            _ = word.length := hshiftFst
        omega
      · have hocc : ge.occ = word.length := by
          calc
            ge.occ =
                chainEndpointOcc
                  (GoertzelLemma814.chainEdgeEndpoints globalOrients ge).1 := by
              exact (chainEdgeEndpoints_fst_occ globalOrients ge).symm
            _ =
                chainEndpointOcc
                  (GoertzelLemma814.chainEdgeEndpoints globalOrients
                    shifted).2 := by
              rw [h]
            _ = word.length := hshiftSnd
        omega
      · have hocc : ge.occ = word.length := by
          calc
            ge.occ =
                chainEndpointOcc
                  (GoertzelLemma814.chainEdgeEndpoints globalOrients ge).2 := by
              exact hgeSnd.symm
            _ =
                chainEndpointOcc
                  (GoertzelLemma814.chainEdgeEndpoints globalOrients
                    shifted).1 := by
              rw [h]
            _ = word.length := hshiftFst
        omega
      · have hocc : ge.occ = word.length := by
          calc
            ge.occ =
                chainEndpointOcc
                  (GoertzelLemma814.chainEdgeEndpoints globalOrients ge).2 := by
              exact hgeSnd.symm
            _ =
                chainEndpointOcc
                  (GoertzelLemma814.chainEdgeEndpoints globalOrients
                    shifted).2 := by
              rw [h]
            _ = word.length := hshiftSnd
        omega

theorem tauOrientOutputOrder_contains_zip_input
    (left right : GoertzelLemma814.TauOrient)
    (outputEdge : GoertzelLemma814.TauEdge)
    (hcontains :
      (GoertzelLemma814.tauOrientOutputOrder left).contains outputEdge =
        true) :
    ∃ inputEdge,
      (outputEdge, inputEdge) ∈
        (GoertzelLemma814.tauOrientOutputOrder left).zip
          (GoertzelLemma814.tauOrientInputOrder right) := by
  cases left <;> cases right <;> cases outputEdge <;>
    simp [GoertzelLemma814.tauOrientOutputOrder,
      GoertzelLemma814.tauOrientInputOrder] at hcontains ⊢

theorem concreteChainFiberAppend_gluedOutput_zip_of_left
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (leftOrient : GoertzelLemma814.TauOrient)
    (ge : GoertzelLemma814.ChainEdge)
    (hleft :
      GoertzelLemma814.tauOrientAt
        (frontierWordToChainWord (word ++ [orient])) ge.occ =
        leftOrient)
    (hglued :
      GoertzelLemma814.chainIsGluedOutput
        (frontierWordToChainWord (word ++ [orient])) ge.occ ge.edge =
        true) :
    ∃ inputEdge,
      (ge.edge, inputEdge) ∈
        (GoertzelLemma814.tauOrientOutputOrder leftOrient).zip
          (GoertzelLemma814.tauOrientInputOrder
            (frontierOrientToChain orient)) := by
  have hparts := hglued
  unfold GoertzelLemma814.chainIsGluedOutput at hparts
  simp only [Bool.and_eq_true] at hparts
  rcases hparts with ⟨_hbound, hcontainsAt⟩
  have hcontainsLeft :
      (GoertzelLemma814.tauOrientOutputOrder leftOrient).contains ge.edge =
        true := by
    simpa [hleft] using hcontainsAt
  exact tauOrientOutputOrder_contains_zip_input leftOrient
    (frontierOrientToChain orient) ge.edge hcontainsLeft

theorem concreteChainFiberAppend_prefix_share_shift_output_zip
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (leftOrient : GoertzelLemma814.TauOrient)
    (ge localEdge : GoertzelLemma814.ChainEdge)
    (hleft :
      GoertzelLemma814.tauOrientAt
        (frontierWordToChainWord (word ++ [orient])) (word.length - 1) =
        leftOrient)
    (hprefix : ge.occ < word.length)
    (hoccSucc : ge.occ + 1 = word.length)
    (hlocalOcc : localEdge.occ = 0)
    (hshare :
      GoertzelLemma814.chainEdgesShareEndpoint
        (frontierWordToChainWord (word ++ [orient])) ge
        (concreteChainFiberAppendShiftEdge word localEdge) = true) :
    ∃ outputEdge inputEdge,
      (outputEdge, inputEdge) ∈
          (GoertzelLemma814.tauOrientOutputOrder leftOrient).zip
            (GoertzelLemma814.tauOrientInputOrder
              (frontierOrientToChain orient)) ∧
        ge = ({ occ := word.length - 1, edge := outputEdge } :
          GoertzelLemma814.ChainEdge) := by
  let globalOrients := frontierWordToChainWord (word ++ [orient])
  have hglued :
      GoertzelLemma814.chainIsGluedOutput globalOrients ge.occ ge.edge =
        true := by
    simpa [globalOrients] using
      concreteChainFiberAppend_prefix_share_shift_forces_glued_output
        word orient ge localEdge hprefix hlocalOcc hshare
  have hgeOcc : ge.occ = word.length - 1 := by
    rw [← hoccSucc]
    simp
  have hleftGe :
      GoertzelLemma814.tauOrientAt globalOrients ge.occ = leftOrient := by
    simpa [globalOrients, hgeOcc] using hleft
  rcases concreteChainFiberAppend_gluedOutput_zip_of_left word orient
      leftOrient ge hleftGe hglued with
    ⟨inputEdge, hzip⟩
  refine ⟨ge.edge, inputEdge, hzip, ?_⟩
  cases ge with
  | mk occ edge =>
      simp at hgeOcc
      simp [hgeOcc]

theorem concreteChainFiberAppend_chainEdgeInPair_shift_occ_zero
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (pref : List GoertzelLemma814.TauState)
    (last : GoertzelLemma814.TauState)
    (a c : GoertzelLemma814.LColor)
    (edge : GoertzelLemma814.ChainEdge)
    (hprefLen : pref.length = word.length)
    (hocc : edge.occ = 0) :
    GoertzelLemma814.chainEdgeInPair (pref ++ [last]) a c
        (concreteChainFiberAppendShiftEdge word edge) =
      GoertzelLemma814.chainEdgeInPair [last] a c edge := by
  unfold GoertzelLemma814.chainEdgeInPair
  rw [concreteChainFiberAppend_chainEdgeColor_shift_occ_zero
    word pref last edge hprefLen hocc]

def concreteChainFiberAppendShiftComponent
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (component : List GoertzelLemma814.ChainEdge) :
    List GoertzelLemma814.ChainEdge :=
  component.map (concreteChainFiberAppendShiftEdge word)

theorem concreteChainFiberAppendShiftComponent_appendFresh
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (xs ys : List GoertzelLemma814.ChainEdge) :
    concreteChainFiberAppendShiftComponent word
        (GoertzelLemma814.appendFresh xs ys) =
      GoertzelLemma814.appendFresh
        (concreteChainFiberAppendShiftComponent word xs)
        (concreteChainFiberAppendShiftComponent word ys) := by
  exact GoertzelLemma814.map_appendFresh_injective
    (concreteChainFiberAppendShiftEdge word)
    (concreteChainFiberAppendShiftEdge_injective word) xs ys

theorem concreteChainFiberAppendShiftComponent_contains_shift_eq
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (component : List GoertzelLemma814.ChainEdge)
    (edge : GoertzelLemma814.ChainEdge) :
    (concreteChainFiberAppendShiftComponent word component).contains
        (concreteChainFiberAppendShiftEdge word edge) =
      component.contains edge := by
  by_cases hshift :
      (concreteChainFiberAppendShiftComponent word component).contains
        (concreteChainFiberAppendShiftEdge word edge) = true
  · have hmem :
        concreteChainFiberAppendShiftEdge word edge ∈
          concreteChainFiberAppendShiftComponent word component :=
      List.contains_iff_mem.mp hshift
    unfold concreteChainFiberAppendShiftComponent at hmem
    rcases List.mem_map.mp hmem with ⟨localEdge, hlocalMem, hlocalEq⟩
    have hlocalEdge : localEdge = edge :=
      concreteChainFiberAppendShiftEdge_injective word hlocalEq
    have hlocalContains : component.contains edge = true :=
      List.contains_iff_mem.mpr (by simpa [hlocalEdge] using hlocalMem)
    rw [hshift, hlocalContains]
  · have hshiftFalse := GoertzelLemma814.bool_false_of_not_true hshift
    by_cases hlocal : component.contains edge = true
    · have hlocalMem : edge ∈ component := List.contains_iff_mem.mp hlocal
      have hshiftMem :
          concreteChainFiberAppendShiftEdge word edge ∈
            concreteChainFiberAppendShiftComponent word component := by
        unfold concreteChainFiberAppendShiftComponent
        exact List.mem_map.mpr ⟨edge, hlocalMem, rfl⟩
      exact False.elim (hshift (List.contains_iff_mem.mpr hshiftMem))
    · have hlocalFalse := GoertzelLemma814.bool_false_of_not_true hlocal
      rw [hshiftFalse, hlocalFalse]

theorem concreteChainFiberAppendShiftComponent_any_shareEndpoint_shift_occ_zero
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (component : List GoertzelLemma814.ChainEdge)
    (edge : GoertzelLemma814.ChainEdge)
    (hedgeOcc : edge.occ = 0)
    (hedgeNotInput :
      (GoertzelLemma814.tauOrientInputOrder (frontierOrientToChain orient)).contains
        edge.edge = false)
    (hcomponent :
      ∀ other, other ∈ component →
        other.occ = 0 ∧
          (GoertzelLemma814.tauOrientInputOrder
            (frontierOrientToChain orient)).contains other.edge = false) :
    (concreteChainFiberAppendShiftComponent word component).any
        (fun other => GoertzelLemma814.chainEdgesShareEndpoint
          (frontierWordToChainWord (word ++ [orient]))
          (concreteChainFiberAppendShiftEdge word edge) other) =
      component.any (fun other => GoertzelLemma814.chainEdgesShareEndpoint
        (frontierWordToChainWord [orient]) edge other) := by
  induction component with
  | nil =>
      simp [concreteChainFiberAppendShiftComponent]
  | cons head tail ih =>
      have hhead := hcomponent head (by simp)
      have htail :
          ∀ other, other ∈ tail →
            other.occ = 0 ∧
              (GoertzelLemma814.tauOrientInputOrder
                (frontierOrientToChain orient)).contains other.edge = false := by
        intro other hmem
        exact hcomponent other (by simp [hmem])
      have hheadShare :
          GoertzelLemma814.chainEdgesShareEndpoint
              (frontierWordToChainWord (word ++ [orient]))
              (concreteChainFiberAppendShiftEdge word edge)
              (concreteChainFiberAppendShiftEdge word head) =
            GoertzelLemma814.chainEdgesShareEndpoint
              (frontierWordToChainWord [orient]) edge head :=
        concreteChainFiberAppend_chainEdgesShareEndpoint_shift_occ_zero
          word orient edge head hedgeOcc hhead.1 hedgeNotInput hhead.2
      have htailAny :
          tail.any
              ((fun other => GoertzelLemma814.chainEdgesShareEndpoint
                (frontierWordToChainWord (word ++ [orient]))
                (concreteChainFiberAppendShiftEdge word edge) other) ∘
                  concreteChainFiberAppendShiftEdge word) =
            tail.any (fun other => GoertzelLemma814.chainEdgesShareEndpoint
              (frontierWordToChainWord [orient]) edge other) := by
        simpa [concreteChainFiberAppendShiftComponent] using ih htail
      simp [concreteChainFiberAppendShiftComponent, hheadShare, htailAny]

theorem concreteChainFiberAppendShiftComponent_contains_prefix_false
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (component : List GoertzelLemma814.ChainEdge)
    (ge : GoertzelLemma814.ChainEdge)
    (hprefix : ge.occ < word.length) :
    (concreteChainFiberAppendShiftComponent word component).contains ge =
      false := by
  apply GoertzelLemma814.bool_false_of_not_true
  intro hcontains
  have hmem : ge ∈ concreteChainFiberAppendShiftComponent word component :=
    List.contains_iff_mem.mp hcontains
  unfold concreteChainFiberAppendShiftComponent at hmem
  rcases List.mem_map.mp hmem with ⟨localEdge, _hLocal, hshift⟩
  have hocc :
      localEdge.occ + word.length = ge.occ := by
    simpa [concreteChainFiberAppendShiftEdge] using
      congrArg GoertzelLemma814.ChainEdge.occ hshift
  omega

theorem concreteChainFiberAppendShiftComponent_contains_canonical_prefix_false
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (component : List GoertzelLemma814.ChainEdge)
    (ge : GoertzelLemma814.ChainEdge)
    (hprefix : ge.occ < word.length) :
    (concreteChainFiberAppendShiftComponent word component).contains
      (GoertzelLemma814.chainCanonicalEdge
        (frontierWordToChainWord (word ++ [orient])) ge) = false := by
  have hcanonicalPrefix :
      (GoertzelLemma814.chainCanonicalEdge
        (frontierWordToChainWord (word ++ [orient])) ge).occ < word.length := by
    unfold GoertzelLemma814.chainCanonicalEdge
    split
    · split
      · simp
        omega
      · exact hprefix
    · exact hprefix
  exact concreteChainFiberAppendShiftComponent_contains_prefix_false
    word component
    (GoertzelLemma814.chainCanonicalEdge
      (frontierWordToChainWord (word ++ [orient])) ge)
    hcanonicalPrefix

theorem concreteChainFiberAppendShiftComponent_contains_last_eq
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (component : List GoertzelLemma814.ChainEdge)
    (ge : GoertzelLemma814.ChainEdge)
    (hlast : ge.occ = word.length) :
    (concreteChainFiberAppendShiftComponent word component).contains ge =
      component.contains
        ({ occ := 0, edge := ge.edge } : GoertzelLemma814.ChainEdge) := by
  let localGe : GoertzelLemma814.ChainEdge := { occ := 0, edge := ge.edge }
  by_cases hshift :
      (concreteChainFiberAppendShiftComponent word component).contains ge =
        true
  · have hmem : ge ∈ concreteChainFiberAppendShiftComponent word component :=
      List.contains_iff_mem.mp hshift
    unfold concreteChainFiberAppendShiftComponent at hmem
    rcases List.mem_map.mp hmem with ⟨localEdge, hlocalMem, hshiftEq⟩
    have hlocalEq : localEdge = localGe := by
      cases localEdge with
      | mk localOcc localTau =>
          cases ge with
          | mk geOcc geTau =>
              have hocc : localOcc + word.length = geOcc := by
                simpa [concreteChainFiberAppendShiftEdge] using
                  congrArg GoertzelLemma814.ChainEdge.occ hshiftEq
              have hedge : localTau = geTau := by
                simpa [concreteChainFiberAppendShiftEdge] using
                  congrArg GoertzelLemma814.ChainEdge.edge hshiftEq
              have hzero : localOcc = 0 := by
                simp at hlast
                omega
              subst localOcc
              subst localTau
              rfl
    have hlocalContains :
        component.contains localGe = true :=
      List.contains_iff_mem.mpr (by simpa [hlocalEq] using hlocalMem)
    rw [hshift, hlocalContains]
  · have hshiftFalse :=
      GoertzelLemma814.bool_false_of_not_true hshift
    by_cases hlocal : component.contains localGe = true
    · have hlocalMem : localGe ∈ component :=
        List.contains_iff_mem.mp hlocal
      have hshiftMem :
          ge ∈ concreteChainFiberAppendShiftComponent word component := by
        unfold concreteChainFiberAppendShiftComponent
        rw [List.mem_map]
        refine ⟨localGe, hlocalMem, ?_⟩
        cases ge with
        | mk geOcc geTau =>
            simp at hlast
            simp [localGe, concreteChainFiberAppendShiftEdge, hlast.symm]
      exact False.elim (hshift (List.contains_iff_mem.mpr hshiftMem))
    · have hlocalFalse :=
        GoertzelLemma814.bool_false_of_not_true hlocal
      rw [hshiftFalse, hlocalFalse]

theorem concreteChainFiberAppend_chainLocalEdges_append_singleton
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient) :
    GoertzelLemma814.chainLocalEdges (frontierWordToChainWord (word ++ [orient])) =
      GoertzelLemma814.chainLocalEdges (frontierWordToChainWord word) ++
        (GoertzelLemma814.tauEdges.map fun e =>
          ({ occ := word.length, edge := e } : GoertzelLemma814.ChainEdge)) := by
  unfold GoertzelLemma814.chainLocalEdges GoertzelLemma814.bindList
    frontierWordToChainWord
  simp only [List.map_append, List.map_cons, List.map_nil, List.length_append,
    List.length_map, List.length_cons, List.length_nil, Nat.add_one]
  rw [List.range_succ]
  simp [List.foldr_append]

theorem concreteChainFiberAppend_chainIsRepresentativeEdge_prefix
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (ge : GoertzelLemma814.ChainEdge)
    (hmem :
      ge ∈ GoertzelLemma814.chainLocalEdges (frontierWordToChainWord word)) :
    GoertzelLemma814.chainIsRepresentativeEdge
        (frontierWordToChainWord (word ++ [orient])) ge =
      GoertzelLemma814.chainIsRepresentativeEdge
        (frontierWordToChainWord word) ge := by
  have hocc : ge.occ < (frontierWordToChainWord word).length :=
    GoertzelLemma814.chainLocalEdges_mem_occ_lt hmem
  unfold GoertzelLemma814.chainIsRepresentativeEdge
    GoertzelLemma814.chainIsGluedInput
  have horient :
      GoertzelLemma814.tauOrientAt
          (frontierWordToChainWord (word ++ [orient])) ge.occ =
        GoertzelLemma814.tauOrientAt
          (frontierWordToChainWord word) ge.occ := by
    simpa [frontierWordToChainWord] using
      GoertzelLemma814.tauOrientAt_append_left
        (frontierWordToChainWord word) [frontierOrientToChain orient] hocc
  rw [horient]

theorem concreteChainFiberAppend_chainEdges_append_singleton_non_input
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (hne : word ≠ []) :
    GoertzelLemma814.chainEdges (frontierWordToChainWord (word ++ [orient])) =
      GoertzelLemma814.chainEdges (frontierWordToChainWord word) ++
        ((GoertzelLemma814.tauEdges.filter fun e =>
          !(GoertzelLemma814.tauOrientInputOrder
            (frontierOrientToChain orient)).contains e).map fun e =>
            ({ occ := word.length, edge := e } :
              GoertzelLemma814.ChainEdge)) := by
  unfold GoertzelLemma814.chainEdges
  rw [concreteChainFiberAppend_chainLocalEdges_append_singleton word orient]
  rw [List.filter_append]
  have hprefix :
      List.filter
          (GoertzelLemma814.chainIsRepresentativeEdge
            (frontierWordToChainWord (word ++ [orient])))
          (GoertzelLemma814.chainLocalEdges (frontierWordToChainWord word)) =
        List.filter
          (GoertzelLemma814.chainIsRepresentativeEdge
            (frontierWordToChainWord word))
          (GoertzelLemma814.chainLocalEdges (frontierWordToChainWord word)) := by
    apply List.filter_congr
    intro ge hmem
    exact concreteChainFiberAppend_chainIsRepresentativeEdge_prefix
      word orient ge hmem
  rw [hprefix]
  rw [List.filter_map]
  apply congrArg (fun xs =>
    List.filter
        (GoertzelLemma814.chainIsRepresentativeEdge
          (frontierWordToChainWord word))
        (GoertzelLemma814.chainLocalEdges (frontierWordToChainWord word)) ++
      List.map (fun e =>
        ({ occ := word.length, edge := e } : GoertzelLemma814.ChainEdge)) xs)
  apply List.filter_congr
  intro e _he
  unfold Function.comp GoertzelLemma814.chainIsRepresentativeEdge
    GoertzelLemma814.chainIsGluedInput
  have hpos : word.length > 0 := by
    cases word with
    | nil => contradiction
    | cons _ _ => simp
  have horient :
      GoertzelLemma814.tauOrientAt
          (frontierWordToChainWord (word ++ [orient])) word.length =
        frontierOrientToChain orient :=
    tauOrientAt_frontierWordToChainWord_append_length word orient
  simp [hpos, horient]

theorem concreteChainFiberAppend_chainEdges_singleton
    (orient : GoertzelLemma818FrontierMode.TauOrient) :
    GoertzelLemma814.chainEdges (frontierWordToChainWord [orient]) =
      GoertzelLemma814.tauEdges.map fun e =>
        ({ occ := 0, edge := e } : GoertzelLemma814.ChainEdge) := by
  cases orient <;>
    simp [frontierWordToChainWord, frontierOrientToChain,
      GoertzelLemma814.chainEdges, GoertzelLemma814.chainLocalEdges,
      GoertzelLemma814.bindList, GoertzelLemma814.chainIsRepresentativeEdge,
      GoertzelLemma814.chainIsGluedInput]

theorem concreteChainFiberAppend_chainEdgeColor_last
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (pref : List GoertzelLemma814.TauState)
    (last : GoertzelLemma814.TauState)
    (ge : GoertzelLemma814.ChainEdge)
    (hprefLen : pref.length = word.length)
    (hlast : ge.occ = word.length) :
    GoertzelLemma814.chainEdgeColor (pref ++ [last]) ge =
      GoertzelLemma814.chainEdgeColor [last]
        ({ occ := 0, edge := ge.edge } : GoertzelLemma814.ChainEdge) := by
  cases ge with
  | mk occ edge =>
      simp at hlast
      subst occ
      have hstate :
          GoertzelLemma814.chainStateAt (pref ++ [last]) word.length = last :=
        GoertzelLemma814.chainStateAt_append_length pref last word.length hprefLen
      unfold GoertzelLemma814.chainEdgeColor GoertzelLemma814.tauStateColorAt
      rw [hstate]
      simp [GoertzelLemma814.chainStateAt, GoertzelLemma814.listGetD]

theorem concreteChainFiberAppend_boundary_output_pair_forces_input_pair
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (leftOrient : GoertzelLemma814.TauOrient)
    (pref : List GoertzelLemma814.TauState)
    (lastX currentLast : GoertzelLemma814.TauState)
    (a c : GoertzelLemma814.LColor)
    (outputEdge inputEdge : GoertzelLemma814.TauEdge)
    (hne : word ≠ [])
    (hprefLen : pref.length = word.length)
    (hcompatibleX : GoertzelLemma814.compatibleAdjacent
      leftOrient (frontierOrientToChain orient)
      (GoertzelLemma814.chainStateAt pref (word.length - 1))
      lastX = true)
    (htrace :
      concreteChainFiberAppendLastInputTrace orient currentLast =
        concreteChainFiberAppendLastInputTrace orient lastX)
    (hzip :
      (outputEdge, inputEdge) ∈
        (GoertzelLemma814.tauOrientOutputOrder leftOrient).zip
          (GoertzelLemma814.tauOrientInputOrder
            (frontierOrientToChain orient)))
    (hpairOutput :
      GoertzelLemma814.chainEdgeInPair (pref ++ [currentLast]) a c
        ({ occ := word.length - 1, edge := outputEdge } :
          GoertzelLemma814.ChainEdge) = true) :
    GoertzelLemma814.chainEdgeInPair [currentLast] a c
      ({ occ := 0, edge := inputEdge } : GoertzelLemma814.ChainEdge) =
        true := by
  have hprevState :
      GoertzelLemma814.chainStateAt (pref ++ [currentLast])
          (word.length - 1) =
        GoertzelLemma814.chainStateAt pref (word.length - 1) :=
    GoertzelLemma814.chainStateAt_append_left pref currentLast
      (by
        rw [hprefLen]
        cases word with
        | nil => contradiction
        | cons _ _ => simp)
  unfold GoertzelLemma814.chainEdgeInPair GoertzelLemma814.chainEdgeColor
    GoertzelLemma814.tauStateColorAt at hpairOutput
  rw [hprevState] at hpairOutput
  cases leftOrient <;> cases orient <;>
    simp [GoertzelLemma814.tauOrientOutputOrder,
      GoertzelLemma814.tauOrientInputOrder, frontierOrientToChain] at hzip
  all_goals
    rcases hzip with hzip | hzip | hzip | hzip <;> cases hzip
    · have hcompatColor :
          (GoertzelLemma814.chainStateAt pref (word.length - 1)).color
              outputEdge =
            lastX.color inputEdge := by
        have h := hcompatibleX
        simp [GoertzelLemma814.compatibleAdjacent,
          GoertzelLemma814.tauOrientOutputOrder,
          GoertzelLemma814.tauOrientInputOrder, GoertzelLemma814.colorEq,
          frontierOrientToChain] at h
        aesop
      have htraceColor :
          currentLast.color inputEdge = lastX.color inputEdge := by
        have h := htrace
        simp [concreteChainFiberAppendLastInputTrace, frontierOrientToChain,
          GoertzelLemma814.tauOrientInputOrder] at h
        aesop
      have hcolor :
          currentLast.color inputEdge =
            (GoertzelLemma814.chainStateAt pref (word.length - 1)).color
              outputEdge := by
        rw [htraceColor, ← hcompatColor]
      simpa [GoertzelLemma814.chainEdgeInPair,
        GoertzelLemma814.chainEdgeColor, GoertzelLemma814.tauStateColorAt,
        GoertzelLemma814.chainStateAt, GoertzelLemma814.listGetD, hcolor]
        using hpairOutput
    · have hcompatColor :
          (GoertzelLemma814.chainStateAt pref (word.length - 1)).color
              outputEdge =
            lastX.color inputEdge := by
        have h := hcompatibleX
        simp [GoertzelLemma814.compatibleAdjacent,
          GoertzelLemma814.tauOrientOutputOrder,
          GoertzelLemma814.tauOrientInputOrder, GoertzelLemma814.colorEq,
          frontierOrientToChain] at h
        aesop
      have htraceColor :
          currentLast.color inputEdge = lastX.color inputEdge := by
        have h := htrace
        simp [concreteChainFiberAppendLastInputTrace, frontierOrientToChain,
          GoertzelLemma814.tauOrientInputOrder] at h
        aesop
      have hcolor :
          currentLast.color inputEdge =
            (GoertzelLemma814.chainStateAt pref (word.length - 1)).color
              outputEdge := by
        rw [htraceColor, ← hcompatColor]
      simpa [GoertzelLemma814.chainEdgeInPair,
        GoertzelLemma814.chainEdgeColor, GoertzelLemma814.tauStateColorAt,
        GoertzelLemma814.chainStateAt, GoertzelLemma814.listGetD, hcolor]
        using hpairOutput
    · have hcompatColor :
          (GoertzelLemma814.chainStateAt pref (word.length - 1)).color
              outputEdge =
            lastX.color inputEdge := by
        have h := hcompatibleX
        simp [GoertzelLemma814.compatibleAdjacent,
          GoertzelLemma814.tauOrientOutputOrder,
          GoertzelLemma814.tauOrientInputOrder, GoertzelLemma814.colorEq,
          frontierOrientToChain] at h
        aesop
      have htraceColor :
          currentLast.color inputEdge = lastX.color inputEdge := by
        have h := htrace
        simp [concreteChainFiberAppendLastInputTrace, frontierOrientToChain,
          GoertzelLemma814.tauOrientInputOrder] at h
        aesop
      have hcolor :
          currentLast.color inputEdge =
            (GoertzelLemma814.chainStateAt pref (word.length - 1)).color
              outputEdge := by
        rw [htraceColor, ← hcompatColor]
      simpa [GoertzelLemma814.chainEdgeInPair,
        GoertzelLemma814.chainEdgeColor, GoertzelLemma814.tauStateColorAt,
        GoertzelLemma814.chainStateAt, GoertzelLemma814.listGetD, hcolor]
        using hpairOutput
    · have hcompatColor :
          (GoertzelLemma814.chainStateAt pref (word.length - 1)).color
              outputEdge =
            lastX.color inputEdge := by
        have h := hcompatibleX
        simp [GoertzelLemma814.compatibleAdjacent,
          GoertzelLemma814.tauOrientOutputOrder,
          GoertzelLemma814.tauOrientInputOrder, GoertzelLemma814.colorEq,
          frontierOrientToChain] at h
        aesop
      have htraceColor :
          currentLast.color inputEdge = lastX.color inputEdge := by
        have h := htrace
        simp [concreteChainFiberAppendLastInputTrace, frontierOrientToChain,
          GoertzelLemma814.tauOrientInputOrder] at h
        aesop
      have hcolor :
          currentLast.color inputEdge =
            (GoertzelLemma814.chainStateAt pref (word.length - 1)).color
              outputEdge := by
        rw [htraceColor, ← hcompatColor]
      simpa [GoertzelLemma814.chainEdgeInPair,
        GoertzelLemma814.chainEdgeColor, GoertzelLemma814.tauStateColorAt,
        GoertzelLemma814.chainStateAt, GoertzelLemma814.listGetD, hcolor]
        using hpairOutput

theorem concreteChainFiberAppend_boundary_output_share_shift_forces_input_share
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (leftOrient : GoertzelLemma814.TauOrient)
    (outputEdge inputEdge : GoertzelLemma814.TauEdge)
    (localEdge : GoertzelLemma814.ChainEdge)
    (hne : word ≠ [])
    (hleft :
      GoertzelLemma814.tauOrientAt
        (frontierWordToChainWord (word ++ [orient])) (word.length - 1) =
        leftOrient)
    (hlocalOcc : localEdge.occ = 0)
    (hlocalNotInput :
      (GoertzelLemma814.tauOrientInputOrder
        (frontierOrientToChain orient)).contains localEdge.edge = false)
    (hzip :
      (outputEdge, inputEdge) ∈
        (GoertzelLemma814.tauOrientOutputOrder leftOrient).zip
          (GoertzelLemma814.tauOrientInputOrder
            (frontierOrientToChain orient)))
    (hshare :
      GoertzelLemma814.chainEdgesShareEndpoint
        (frontierWordToChainWord (word ++ [orient]))
        ({ occ := word.length - 1, edge := outputEdge } :
          GoertzelLemma814.ChainEdge)
        (concreteChainFiberAppendShiftEdge word localEdge) = true) :
    GoertzelLemma814.chainEdgesShareEndpoint (frontierWordToChainWord [orient])
      ({ occ := 0, edge := inputEdge } : GoertzelLemma814.ChainEdge)
      localEdge = true := by
  cases localEdge with
  | mk localOcc localTau =>
      simp at hlocalOcc
      subst localOcc
      cases word with
      | nil =>
          exact False.elim (hne rfl)
      | cons head tail =>
          have hleftAt :
              GoertzelLemma814.listGetD
                (frontierOrientToChain head ::
                  (List.map frontierOrientToChain tail ++
                    [frontierOrientToChain orient]))
                tail.length GoertzelLemma814.TauOrient.normal =
                leftOrient := by
            simpa [GoertzelLemma814.tauOrientAt, frontierWordToChainWord] using
              hleft
          have hnextAt :
              GoertzelLemma814.listGetD
                (List.map frontierOrientToChain tail ++
                  [frontierOrientToChain orient])
                tail.length GoertzelLemma814.TauOrient.normal =
                frontierOrientToChain orient := by
            rw [← List.length_map (f := frontierOrientToChain) (as := tail)]
            exact GoertzelLemma814.listGetD_append_length
              (List.map frontierOrientToChain tail) (frontierOrientToChain orient)
              GoertzelLemma814.TauOrient.normal
          cases leftOrient <;> cases orient <;>
            simp [GoertzelLemma814.tauOrientOutputOrder,
              GoertzelLemma814.tauOrientInputOrder, frontierOrientToChain] at hzip
          all_goals
            simp [frontierOrientToChain] at hleftAt hnextAt
            rcases hzip with
              ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              cases localTau <;>
              simp [concreteChainFiberAppendShiftEdge,
                GoertzelLemma814.chainEdgesShareEndpoint,
                GoertzelLemma814.chainEdgeEndpoints,
                GoertzelLemma814.chainIsGluedOutput,
                GoertzelLemma814.indexOf?,
                GoertzelLemma814.indexOfAux,
                GoertzelLemma814.tauOrientAt,
                GoertzelLemma814.listGetD,
                GoertzelLemma814.edgeEndpoints,
                GoertzelLemma814.tauEndpointToChainEndpoint,
                GoertzelLemma814.isInternalEndpoint,
                GoertzelLemma814.tauStubInternalEndpoint,
                GoertzelLemma814.tauOrientOutputOrder,
                GoertzelLemma814.tauOrientInputOrder,
                frontierWordToChainWord, frontierOrientToChain,
                hleftAt, hnextAt] at hlocalNotInput hshare ⊢

theorem concreteChainFiberAppend_boundary_output_ingress_local_input_nextLayer
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (leftOrient : GoertzelLemma814.TauOrient)
    (pref : List GoertzelLemma814.TauState)
    (lastX currentLast : GoertzelLemma814.TauState)
    (move : GoertzelLemma814.ChainMove)
    (localComponent : List GoertzelLemma814.ChainEdge)
    (localEdge : GoertzelLemma814.ChainEdge)
    (outputEdge inputEdge : GoertzelLemma814.TauEdge)
    (hne : word ≠ [])
    (hprefLen : pref.length = word.length)
    (hleft :
      GoertzelLemma814.tauOrientAt
        (frontierWordToChainWord (word ++ [orient])) (word.length - 1) =
        leftOrient)
    (hcompatibleX : GoertzelLemma814.compatibleAdjacent
      leftOrient (frontierOrientToChain orient)
      (GoertzelLemma814.chainStateAt pref (word.length - 1))
      lastX = true)
    (htrace :
      concreteChainFiberAppendLastInputTrace orient currentLast =
        concreteChainFiberAppendLastInputTrace orient lastX)
    (hzip :
      (outputEdge, inputEdge) ∈
        (GoertzelLemma814.tauOrientOutputOrder leftOrient).zip
          (GoertzelLemma814.tauOrientInputOrder
            (frontierOrientToChain orient)))
    (hlocalMem : localEdge ∈ localComponent)
    (hlocalAvoid :
      GoertzelLemma814.chainComponentAvoidsInputs
        (frontierWordToChainWord [orient]) localComponent = true)
    (hlocalOcc : localEdge.occ = 0)
    (hlocalNotInput :
      (GoertzelLemma814.tauOrientInputOrder
        (frontierOrientToChain orient)).contains localEdge.edge = false)
    (houtputPair :
      GoertzelLemma814.chainEdgeInPair (pref ++ [currentLast])
        move.a move.c
        ({ occ := word.length - 1, edge := outputEdge } :
          GoertzelLemma814.ChainEdge) = true)
    (hshare :
      GoertzelLemma814.chainEdgesShareEndpoint
        (frontierWordToChainWord (word ++ [orient]))
        ({ occ := word.length - 1, edge := outputEdge } :
          GoertzelLemma814.ChainEdge)
        (concreteChainFiberAppendShiftEdge word localEdge) = true) :
    ({ occ := 0, edge := inputEdge } : GoertzelLemma814.ChainEdge) ∈
      GoertzelLemma814.nextChainComponentLayer
        (frontierWordToChainWord [orient]) [currentLast]
        move.a move.c localComponent := by
  let inputLocal : GoertzelLemma814.ChainEdge :=
    { occ := 0, edge := inputEdge }
  have hinputPair :
      GoertzelLemma814.chainEdgeInPair [currentLast] move.a move.c
        inputLocal = true := by
    simpa [inputLocal] using
      concreteChainFiberAppend_boundary_output_pair_forces_input_pair
        word orient leftOrient pref lastX currentLast move.a move.c
        outputEdge inputEdge hne hprefLen hcompatibleX htrace hzip
        houtputPair
  have hinputShare :
      GoertzelLemma814.chainEdgesShareEndpoint
        (frontierWordToChainWord [orient]) inputLocal localEdge = true := by
    simpa [inputLocal] using
      concreteChainFiberAppend_boundary_output_share_shift_forces_input_share
        word orient leftOrient outputEdge inputEdge localEdge hne hleft
        hlocalOcc hlocalNotInput hzip hshare
  have hinputChain :
      inputLocal ∈ GoertzelLemma814.chainEdges
        (frontierWordToChainWord [orient]) := by
    cases leftOrient <;> cases orient <;>
      simp [GoertzelLemma814.tauOrientOutputOrder,
        GoertzelLemma814.tauOrientInputOrder, frontierOrientToChain] at hzip
    all_goals
      rcases hzip with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [inputLocal, frontierWordToChainWord, frontierOrientToChain,
          GoertzelLemma814.chainEdges, GoertzelLemma814.chainLocalEdges,
          GoertzelLemma814.bindList, GoertzelLemma814.chainIsRepresentativeEdge,
          GoertzelLemma814.chainIsGluedInput, GoertzelLemma814.tauOrientAt,
          GoertzelLemma814.listGetD, GoertzelLemma814.tauOrientInputOrder,
          GoertzelLemma814.tauEdges]
  have hinputOuter :
      (GoertzelLemma814.chainOuterInputEdges
        (frontierWordToChainWord [orient])).contains inputLocal = true := by
    cases leftOrient <;> cases orient <;>
      simp [GoertzelLemma814.tauOrientOutputOrder,
        GoertzelLemma814.tauOrientInputOrder, frontierOrientToChain] at hzip
    all_goals
      rcases hzip with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [inputLocal, frontierWordToChainWord, frontierOrientToChain,
          GoertzelLemma814.chainOuterInputEdges, GoertzelLemma814.chainInputOrder,
          GoertzelLemma814.tauOrientAt, GoertzelLemma814.listGetD,
          GoertzelLemma814.tauOrientInputOrder]
  have hinputNotMem : inputLocal ∉ localComponent := by
    intro hmem
    have houterFalse :
        (GoertzelLemma814.chainOuterInputEdges
          (frontierWordToChainWord [orient])).contains inputLocal = false :=
      GoertzelLemma814.chainComponentAvoidsInputs_contains_false
        (frontierWordToChainWord [orient]) localComponent hlocalAvoid hmem
    rw [hinputOuter] at houterFalse
    cases houterFalse
  have hinputFresh : (!localComponent.contains inputLocal) = true := by
    simpa using hinputNotMem
  have hinputAny :
      localComponent.any
        (GoertzelLemma814.chainEdgesShareEndpoint
          (frontierWordToChainWord [orient]) inputLocal) = true :=
    GoertzelLemma814.list_any_true_of_mem hlocalMem hinputShare
  unfold GoertzelLemma814.nextChainComponentLayer
  rw [List.mem_filter]
  exact ⟨hinputChain, by
    rw [hinputPair, hinputFresh, hinputAny]
    rfl⟩

theorem concreteChainFiberAppend_chainCanonicalEdge_last_non_glued
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (ge : GoertzelLemma814.ChainEdge)
    (hne : word ≠ [])
    (hlast : ge.occ = word.length)
    (hnonGlued : GoertzelLemma814.chainIsGluedInput
      (frontierWordToChainWord (word ++ [orient])) ge.occ ge.edge = false) :
    GoertzelLemma814.chainCanonicalEdge
      (frontierWordToChainWord (word ++ [orient])) ge = ge := by
  have hpos : ge.occ > 0 := by
    rw [hlast]
    cases word with
    | nil =>
        exact False.elim (hne rfl)
    | cons _ _ =>
        simp
  have hinputFalse :
      (GoertzelLemma814.tauOrientInputOrder
        (GoertzelLemma814.tauOrientAt
          (frontierWordToChainWord (word ++ [orient])) ge.occ)).contains
        ge.edge = false := by
    unfold GoertzelLemma814.chainIsGluedInput at hnonGlued
    simpa [hpos] using hnonGlued
  unfold GoertzelLemma814.chainCanonicalEdge
  simp [hpos,
    GoertzelLemma814.indexOf?_eq_none_of_contains_false _ _ hinputFalse]

theorem concreteChainFiberAppendShiftedEdgePresent_of_not_input
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (edge : GoertzelLemma814.TauEdge)
    (hnot :
      (GoertzelLemma814.tauOrientInputOrder (frontierOrientToChain orient)).contains
        edge = false) :
    (GoertzelLemma814.chainEdges
      (frontierWordToChainWord (word ++ [orient]))).contains
      ({ occ := word.length, edge := edge } : GoertzelLemma814.ChainEdge) =
        true := by
  apply GoertzelLemma814.chainEdges_contains_of_occ_edge_and_representative
  · simp [frontierWordToChainWord]
  · unfold GoertzelLemma814.chainIsRepresentativeEdge
      GoertzelLemma814.chainIsGluedInput
    rw [tauOrientAt_frontierWordToChainWord_append_length]
    cases word with
    | nil =>
        simp
    | cons _ _ =>
        have hnotMem :
            ¬ edge ∈
              GoertzelLemma814.tauOrientInputOrder (frontierOrientToChain orient) := by
          intro hmem
          have hcontains :
              (GoertzelLemma814.tauOrientInputOrder
                (frontierOrientToChain orient)).contains edge = true :=
            List.contains_iff_mem.mpr hmem
          rw [hnot] at hcontains
          cases hcontains
        simpa using hnotMem

def concreteChainFiberAppendRelativeSingletonShiftedSeedPresentClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX : GoertzelLemma814.TauState),
            (_hpref : pref ∈ concreteChainFiber word key) →
            (_hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (_hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            ∀ (_hkeyLocal :
                concreteChainFiberAppendLastInputTrace orient lastX ∈
                  GoertzelLemma814.colorAssignments4)
              (current target : List GoertzelLemma814.TauState)
              (currentLast targetLast : GoertzelLemma814.TauState),
              current ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              target ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              current = [currentLast] →
              target = [targetLast] →
              ∀ (move : GoertzelLemma814.ChainMove),
                GoertzelLemma814.colorPairs.contains (move.a, move.c) = true →
                (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
                  move.seed = true →
                GoertzelLemma814.chainSpecifiedKempeStep
                  (frontierWordToChainWord [orient]) current target move = true →
                (GoertzelLemma814.chainEdges
                  (frontierWordToChainWord (word ++ [orient]))).contains
                    (concreteChainFiberAppendShiftMove word move).seed = true

theorem concreteChainFiberAppendRelativeSingletonShiftedSeedPresentClosed_of_local_specified :
    concreteChainFiberAppendRelativeSingletonShiftedSeedPresentClosed := by
  intro word orient _hne _hcert _key _hkey _pref _lastX _hpref _hlastX
    _hcompatibleX _hkeyLocal current target _currentLast _targetLast _hcurrent
    _htarget _hcurrentEq _htargetEq move _hpair hseed hspecified
  have houter :
      (GoertzelLemma814.chainOuterInputEdges
        [frontierOrientToChain orient]).contains move.seed = false :=
    GoertzelLemma814.chainSpecifiedKempeStep_seed_not_outer_input
      (frontierWordToChainWord [orient]) current target move
      (by simpa [frontierWordToChainWord] using hspecified)
  have hocc : move.seed.occ = 0 :=
    GoertzelLemma814.chainEdges_singleton_seed_occ_zero
      (frontierOrientToChain orient) move.seed
      (by simpa [frontierWordToChainWord] using hseed)
  have hnotInput :
      (GoertzelLemma814.tauOrientInputOrder
        (frontierOrientToChain orient)).contains move.seed.edge = false :=
    GoertzelLemma814.tauOrientInputOrder_contains_edge_false_of_chainOuterInput_false_singleton
      (frontierOrientToChain orient) move.seed hocc houter
  have hshift :=
    concreteChainFiberAppendShiftedEdgePresent_of_not_input
      word orient move.seed.edge hnotInput
  simpa [concreteChainFiberAppendShiftMove, hocc] using hshift

theorem concreteChainFiberAppendOuterInputContainsShiftEdge_false
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (edge : GoertzelLemma814.ChainEdge)
    (hne : word ≠ []) :
    (GoertzelLemma814.chainOuterInputEdges
      (frontierWordToChainWord (word ++ [orient]))).contains
        (concreteChainFiberAppendShiftEdge word edge) = false := by
  cases word with
  | nil =>
      contradiction
  | cons _ _ =>
      cases edge with
      | mk _ _ =>
          simp [concreteChainFiberAppendShiftEdge,
            GoertzelLemma814.chainOuterInputEdges,
            GoertzelLemma814.chainInputOrder, frontierWordToChainWord,
            GoertzelLemma814.tauOrientAt, GoertzelLemma814.listGetD]

theorem concreteChainFiberAppendShiftComponent_avoids_inputs
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (component : List GoertzelLemma814.ChainEdge)
    (hne : word ≠ []) :
    GoertzelLemma814.chainComponentAvoidsInputs
      (frontierWordToChainWord (word ++ [orient]))
      (concreteChainFiberAppendShiftComponent word component) = true := by
  unfold GoertzelLemma814.chainComponentAvoidsInputs
  have hany :
      (concreteChainFiberAppendShiftComponent word component).any
        (fun e => (GoertzelLemma814.chainOuterInputEdges
          (frontierWordToChainWord (word ++ [orient]))).contains e) = false := by
    apply GoertzelLemma814.list_any_false_of_forall_mem
    intro edge hmem
    unfold concreteChainFiberAppendShiftComponent at hmem
    rcases List.mem_map.mp hmem with ⟨localEdge, _hLocal, rfl⟩
    exact concreteChainFiberAppendOuterInputContainsShiftEdge_false
      word orient localEdge hne
  rw [hany]
  rfl

theorem concreteChainFiberAppendLocalSingletonComponent_edge_occ_zero_not_input
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (current target : List GoertzelLemma814.TauState)
    (move : GoertzelLemma814.ChainMove)
    (hseed :
      (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
        move.seed = true)
    (hspecified :
      GoertzelLemma814.chainSpecifiedKempeStep
        (frontierWordToChainWord [orient]) current target move = true)
    {edge : GoertzelLemma814.ChainEdge}
    (hmem :
      edge ∈ GoertzelLemma814.chainComponent
        (frontierWordToChainWord [orient]) current move.a move.c move.seed) :
    edge.occ = 0 ∧
      (GoertzelLemma814.tauOrientInputOrder
        (frontierOrientToChain orient)).contains edge.edge = false := by
  let localComponent :=
    GoertzelLemma814.chainComponent (frontierWordToChainWord [orient])
      current move.a move.c move.seed
  have hspecifiedParts := hspecified
  unfold GoertzelLemma814.chainSpecifiedKempeStep at hspecifiedParts
  change (!localComponent.isEmpty &&
      GoertzelLemma814.chainComponentAvoidsInputs
        (frontierWordToChainWord [orient]) localComponent &&
      GoertzelLemma814.chainAgreesWithSwitch
        (frontierWordToChainWord [orient]) current target localComponent
        move.a move.c) = true at hspecifiedParts
  simp only [Bool.and_eq_true] at hspecifiedParts
  rcases hspecifiedParts with ⟨⟨_hNonempty, hAvoid⟩, _hAgree⟩
  have hocc : edge.occ = 0 :=
    GoertzelLemma814.chainComponent_mem_occ_zero_of_singleton
      (frontierOrientToChain orient) current move.a move.c move.seed edge
      (by simpa [frontierWordToChainWord] using hseed)
      (by simpa [frontierWordToChainWord, localComponent] using hmem)
  have houter :
      (GoertzelLemma814.chainOuterInputEdges
        (frontierWordToChainWord [orient])).contains edge = false :=
    GoertzelLemma814.chainComponentAvoidsInputs_contains_false
      (frontierWordToChainWord [orient]) localComponent hAvoid
      (by simpa [localComponent] using hmem)
  have hnotInput :
      (GoertzelLemma814.tauOrientInputOrder
        (frontierOrientToChain orient)).contains edge.edge = false :=
    GoertzelLemma814.tauOrientInputOrder_contains_edge_false_of_chainOuterInput_false_singleton
      (frontierOrientToChain orient) edge hocc
      (by simpa [frontierWordToChainWord] using houter)
  exact ⟨hocc, hnotInput⟩

theorem concreteChainFiberAppendLocalSingletonComponent_shift_edge_present
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (current target : List GoertzelLemma814.TauState)
    (move : GoertzelLemma814.ChainMove)
    (hseed :
      (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
        move.seed = true)
    (hspecified :
      GoertzelLemma814.chainSpecifiedKempeStep
        (frontierWordToChainWord [orient]) current target move = true)
    {edge : GoertzelLemma814.ChainEdge}
    (hmem :
      edge ∈ GoertzelLemma814.chainComponent
        (frontierWordToChainWord [orient]) current move.a move.c move.seed) :
    (GoertzelLemma814.chainEdges
      (frontierWordToChainWord (word ++ [orient]))).contains
        (concreteChainFiberAppendShiftEdge word edge) = true := by
  have hedge :
      edge.occ = 0 ∧
        (GoertzelLemma814.tauOrientInputOrder
          (frontierOrientToChain orient)).contains edge.edge = false :=
    concreteChainFiberAppendLocalSingletonComponent_edge_occ_zero_not_input
      orient current target move hseed hspecified (edge := edge) hmem
  have hshift :=
    concreteChainFiberAppendShiftedEdgePresent_of_not_input
      word orient edge.edge hedge.2
  simpa [concreteChainFiberAppendShiftEdge, hedge.1] using hshift

theorem concreteChainFiberAppendLocalNonInputEdge_shift_nextLayer_pred
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (pref : List GoertzelLemma814.TauState)
    (currentLast : GoertzelLemma814.TauState)
    (move : GoertzelLemma814.ChainMove)
    (seen : List GoertzelLemma814.ChainEdge)
    (edge : GoertzelLemma814.ChainEdge)
    (hprefLen : pref.length = word.length)
    (hedgeOcc : edge.occ = 0)
    (hedgeNotInput :
      (GoertzelLemma814.tauOrientInputOrder
        (frontierOrientToChain orient)).contains edge.edge = false)
    (hseenParts :
      ∀ other, other ∈ seen →
        other.occ = 0 ∧
          (GoertzelLemma814.tauOrientInputOrder
            (frontierOrientToChain orient)).contains other.edge = false) :
    let localOrients := frontierWordToChainWord [orient]
    let globalOrients := frontierWordToChainWord (word ++ [orient])
    let shiftedSeen := concreteChainFiberAppendShiftComponent word seen
    let shiftedEdge := concreteChainFiberAppendShiftEdge word edge
    (GoertzelLemma814.chainEdgeInPair (pref ++ [currentLast])
        move.a move.c shiftedEdge &&
      !shiftedSeen.contains shiftedEdge &&
      shiftedSeen.any
        (fun other => GoertzelLemma814.chainEdgesShareEndpoint
          globalOrients shiftedEdge other)) =
    (GoertzelLemma814.chainEdgeInPair [currentLast] move.a move.c edge &&
      !seen.contains edge &&
      seen.any (fun other => GoertzelLemma814.chainEdgesShareEndpoint
        localOrients edge other)) := by
  let localOrients := frontierWordToChainWord [orient]
  let globalOrients := frontierWordToChainWord (word ++ [orient])
  let shiftedSeen := concreteChainFiberAppendShiftComponent word seen
  let shiftedEdge := concreteChainFiberAppendShiftEdge word edge
  have hpair :
      GoertzelLemma814.chainEdgeInPair (pref ++ [currentLast])
          move.a move.c shiftedEdge =
        GoertzelLemma814.chainEdgeInPair [currentLast] move.a move.c edge := by
    simpa [shiftedEdge] using
      concreteChainFiberAppend_chainEdgeInPair_shift_occ_zero
        word pref currentLast move.a move.c edge hprefLen hedgeOcc
  have hfresh :
      shiftedSeen.contains shiftedEdge = seen.contains edge := by
    simpa [shiftedSeen, shiftedEdge] using
      concreteChainFiberAppendShiftComponent_contains_shift_eq word seen edge
  have hshiftedMemIff : shiftedEdge ∈ shiftedSeen ↔ edge ∈ seen := by
    constructor
    · intro hmem
      have hcontains : shiftedSeen.contains shiftedEdge = true :=
        List.contains_iff_mem.mpr hmem
      have hlocalContains : seen.contains edge = true := by
        rw [← hfresh]
        exact hcontains
      exact List.contains_iff_mem.mp hlocalContains
    · intro hmem
      have hlocalContains : seen.contains edge = true :=
        List.contains_iff_mem.mpr hmem
      have hcontains : shiftedSeen.contains shiftedEdge = true := by
        rw [hfresh]
        exact hlocalContains
      exact List.contains_iff_mem.mp hcontains
  have hshare :
      shiftedSeen.any
          (fun other => GoertzelLemma814.chainEdgesShareEndpoint
            globalOrients shiftedEdge other) =
        seen.any (fun other => GoertzelLemma814.chainEdgesShareEndpoint
          localOrients edge other) := by
    simpa [shiftedSeen, shiftedEdge, globalOrients, localOrients] using
      concreteChainFiberAppendShiftComponent_any_shareEndpoint_shift_occ_zero
        word orient seen edge hedgeOcc hedgeNotInput hseenParts
  simp [localOrients, globalOrients, shiftedSeen, shiftedEdge, hpair,
    hshiftedMemIff, hshare]

theorem concreteChainFiberAppendLocalNonInputEdge_shift_nextLayer_contains
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (pref : List GoertzelLemma814.TauState)
    (currentLast : GoertzelLemma814.TauState)
    (move : GoertzelLemma814.ChainMove)
    (seen : List GoertzelLemma814.ChainEdge)
    (edge : GoertzelLemma814.ChainEdge)
    (hprefLen : pref.length = word.length)
    (hedgeOcc : edge.occ = 0)
    (hedgeNotInput :
      (GoertzelLemma814.tauOrientInputOrder
        (frontierOrientToChain orient)).contains edge.edge = false)
    (hseenParts :
      ∀ other, other ∈ seen →
        other.occ = 0 ∧
          (GoertzelLemma814.tauOrientInputOrder
            (frontierOrientToChain orient)).contains other.edge = false) :
    (GoertzelLemma814.nextChainComponentLayer
        (frontierWordToChainWord (word ++ [orient]))
        (pref ++ [currentLast]) move.a move.c
        (concreteChainFiberAppendShiftComponent word seen)).contains
        (concreteChainFiberAppendShiftEdge word edge) =
      (GoertzelLemma814.nextChainComponentLayer
        (frontierWordToChainWord [orient]) [currentLast] move.a move.c
        seen).contains edge := by
  let localOrients := frontierWordToChainWord [orient]
  let globalOrients := frontierWordToChainWord (word ++ [orient])
  let shiftedSeen := concreteChainFiberAppendShiftComponent word seen
  let shiftedEdge := concreteChainFiberAppendShiftEdge word edge
  change
    (GoertzelLemma814.nextChainComponentLayer globalOrients
      (pref ++ [currentLast]) move.a move.c shiftedSeen).contains
        shiftedEdge =
      (GoertzelLemma814.nextChainComponentLayer localOrients
        [currentLast] move.a move.c seen).contains edge
  have hedgeLocalEdges :
      edge ∈ GoertzelLemma814.chainEdges localOrients := by
    have hcontains :
        (GoertzelLemma814.chainEdges localOrients).contains edge = true := by
      cases edge with
      | mk occ tauEdge =>
          simp at hedgeOcc
          subst occ
          rw [concreteChainFiberAppend_chainEdges_singleton orient]
          exact List.contains_iff_mem.mpr
            (List.mem_map.mpr ⟨tauEdge, GoertzelLemma814.tauEdges_mem tauEdge, rfl⟩)
    exact List.contains_iff_mem.mp hcontains
  have hglobalEdgeContains :
      (GoertzelLemma814.chainEdges globalOrients).contains shiftedEdge = true := by
    have hshift :=
      concreteChainFiberAppendShiftedEdgePresent_of_not_input
        word orient edge.edge hedgeNotInput
    simpa [globalOrients, shiftedEdge, concreteChainFiberAppendShiftEdge,
      hedgeOcc] using hshift
  have hpair :
      GoertzelLemma814.chainEdgeInPair (pref ++ [currentLast])
          move.a move.c shiftedEdge =
        GoertzelLemma814.chainEdgeInPair [currentLast] move.a move.c edge := by
    simpa [shiftedEdge] using
      concreteChainFiberAppend_chainEdgeInPair_shift_occ_zero
        word pref currentLast move.a move.c edge hprefLen hedgeOcc
  have hfresh :
      shiftedSeen.contains shiftedEdge = seen.contains edge := by
    simpa [shiftedSeen, shiftedEdge] using
      concreteChainFiberAppendShiftComponent_contains_shift_eq word seen edge
  have hshiftedMemIff : shiftedEdge ∈ shiftedSeen ↔ edge ∈ seen := by
    constructor
    · intro hmem
      have hcontains : shiftedSeen.contains shiftedEdge = true :=
        List.contains_iff_mem.mpr hmem
      have hlocalContains : seen.contains edge = true := by
        rw [← hfresh]
        exact hcontains
      exact List.contains_iff_mem.mp hlocalContains
    · intro hmem
      have hlocalContains : seen.contains edge = true :=
        List.contains_iff_mem.mpr hmem
      have hcontains : shiftedSeen.contains shiftedEdge = true := by
        rw [hfresh]
        exact hlocalContains
      exact List.contains_iff_mem.mp hcontains
  have hshare :
      shiftedSeen.any
          (fun other => GoertzelLemma814.chainEdgesShareEndpoint
            globalOrients shiftedEdge other) =
        seen.any (fun other => GoertzelLemma814.chainEdgesShareEndpoint
          localOrients edge other) := by
    simpa [shiftedSeen, shiftedEdge, globalOrients, localOrients] using
      concreteChainFiberAppendShiftComponent_any_shareEndpoint_shift_occ_zero
        word orient seen edge hedgeOcc hedgeNotInput hseenParts
  by_cases hlocal :
      (GoertzelLemma814.nextChainComponentLayer localOrients [currentLast]
        move.a move.c seen).contains edge = true
  · have hlocalMem :
        edge ∈ GoertzelLemma814.nextChainComponentLayer localOrients
          [currentLast] move.a move.c seen :=
      List.contains_iff_mem.mp hlocal
    have hlocalFilter := hlocalMem
    unfold GoertzelLemma814.nextChainComponentLayer at hlocalFilter
    rw [List.mem_filter] at hlocalFilter
    rcases hlocalFilter with ⟨_hedgeChain, hlocalPred⟩
    have hglobalPred :
        (GoertzelLemma814.chainEdgeInPair (pref ++ [currentLast])
            move.a move.c shiftedEdge &&
          !shiftedSeen.contains shiftedEdge &&
          shiftedSeen.any
            (fun other => GoertzelLemma814.chainEdgesShareEndpoint
              globalOrients shiftedEdge other)) = true := by
      simpa [hpair, hfresh, hshiftedMemIff, hshare,
        globalOrients, localOrients] using
        hlocalPred
    have hglobalMem :
        shiftedEdge ∈ GoertzelLemma814.nextChainComponentLayer globalOrients
          (pref ++ [currentLast]) move.a move.c shiftedSeen := by
      unfold GoertzelLemma814.nextChainComponentLayer
      rw [List.mem_filter]
      exact ⟨List.contains_iff_mem.mp hglobalEdgeContains, hglobalPred⟩
    have hglobal :
        (GoertzelLemma814.nextChainComponentLayer globalOrients
          (pref ++ [currentLast]) move.a move.c shiftedSeen).contains
          shiftedEdge = true :=
      List.contains_iff_mem.mpr hglobalMem
    rw [hlocal]
    exact hglobal
  · have hlocalFalse := GoertzelLemma814.bool_false_of_not_true hlocal
    rw [hlocalFalse]
    apply GoertzelLemma814.bool_false_of_not_true
    intro hglobal
    have hglobalMem :
        shiftedEdge ∈ GoertzelLemma814.nextChainComponentLayer globalOrients
          (pref ++ [currentLast]) move.a move.c shiftedSeen :=
      List.contains_iff_mem.mp hglobal
    have hglobalFilter := hglobalMem
    unfold GoertzelLemma814.nextChainComponentLayer at hglobalFilter
    rw [List.mem_filter] at hglobalFilter
    rcases hglobalFilter with ⟨_hglobalChain, hglobalPred⟩
    have hlocalPred :
        (GoertzelLemma814.chainEdgeInPair [currentLast] move.a move.c edge &&
          !seen.contains edge &&
          seen.any (fun other => GoertzelLemma814.chainEdgesShareEndpoint
            localOrients edge other)) = true := by
      simpa [hpair, hfresh, hshiftedMemIff, hshare,
        globalOrients, localOrients] using
        hglobalPred
    have hlocalMem :
        edge ∈ GoertzelLemma814.nextChainComponentLayer localOrients
          [currentLast] move.a move.c seen := by
      unfold GoertzelLemma814.nextChainComponentLayer
      rw [List.mem_filter]
      exact ⟨hedgeLocalEdges, hlocalPred⟩
    have hlocalTrue :
        (GoertzelLemma814.nextChainComponentLayer localOrients
          [currentLast] move.a move.c seen).contains edge = true :=
      List.contains_iff_mem.mpr hlocalMem
    rw [hlocalFalse] at hlocalTrue
    cases hlocalTrue

theorem concreteChainFiberAppendLocalSingletonComponent_shift_nextLayer_contains
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (pref target : List GoertzelLemma814.TauState)
    (currentLast : GoertzelLemma814.TauState)
    (move : GoertzelLemma814.ChainMove)
    (seen : List GoertzelLemma814.ChainEdge)
    (hprefLen : pref.length = word.length)
    (hseed :
      (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
        move.seed = true)
    (hspecified :
      GoertzelLemma814.chainSpecifiedKempeStep
        (frontierWordToChainWord [orient]) [currentLast] target move = true)
    (hseen :
      ∀ edge, edge ∈ seen →
        edge ∈ GoertzelLemma814.chainComponent
          (frontierWordToChainWord [orient]) [currentLast]
          move.a move.c move.seed)
    {edge : GoertzelLemma814.ChainEdge}
    (hedge :
      edge ∈ GoertzelLemma814.chainComponent
        (frontierWordToChainWord [orient]) [currentLast]
        move.a move.c move.seed) :
    (GoertzelLemma814.nextChainComponentLayer
        (frontierWordToChainWord (word ++ [orient]))
        (pref ++ [currentLast]) move.a move.c
        (concreteChainFiberAppendShiftComponent word seen)).contains
        (concreteChainFiberAppendShiftEdge word edge) =
      (GoertzelLemma814.nextChainComponentLayer
        (frontierWordToChainWord [orient]) [currentLast] move.a move.c
        seen).contains edge := by
  let localOrients := frontierWordToChainWord [orient]
  let globalOrients := frontierWordToChainWord (word ++ [orient])
  let localComponent :=
    GoertzelLemma814.chainComponent localOrients [currentLast]
      move.a move.c move.seed
  let shiftedSeen := concreteChainFiberAppendShiftComponent word seen
  let shiftedEdge := concreteChainFiberAppendShiftEdge word edge
  change
    (GoertzelLemma814.nextChainComponentLayer globalOrients
      (pref ++ [currentLast]) move.a move.c shiftedSeen).contains
        shiftedEdge =
      (GoertzelLemma814.nextChainComponentLayer localOrients
        [currentLast] move.a move.c seen).contains edge
  have hseedMem : move.seed ∈ GoertzelLemma814.chainEdges localOrients :=
    List.contains_iff_mem.mp (by simpa [localOrients] using hseed)
  have hedgeLocalEdges :
      edge ∈ GoertzelLemma814.chainEdges localOrients :=
    GoertzelLemma814.chainComponent_mem_chainEdges
      localOrients [currentLast] move.a move.c move.seed hseedMem
      (by simpa [localOrients, localComponent] using hedge)
  have hedgeParts :=
    concreteChainFiberAppendLocalSingletonComponent_edge_occ_zero_not_input
      orient [currentLast] target move
      (by simpa [localOrients] using hseed)
      (by simpa [localOrients] using hspecified)
      (by simpa [localOrients, localComponent] using hedge)
  have hseenParts :
      ∀ other, other ∈ seen →
        other.occ = 0 ∧
          (GoertzelLemma814.tauOrientInputOrder
            (frontierOrientToChain orient)).contains other.edge = false := by
    intro other hother
    exact
      concreteChainFiberAppendLocalSingletonComponent_edge_occ_zero_not_input
        orient [currentLast] target move
        (by simpa [localOrients] using hseed)
        (by simpa [localOrients] using hspecified)
        (by simpa [localOrients, localComponent] using hseen other hother)
  have hglobalEdgeContains :
      (GoertzelLemma814.chainEdges globalOrients).contains shiftedEdge = true := by
    simpa [globalOrients, shiftedEdge] using
      concreteChainFiberAppendLocalSingletonComponent_shift_edge_present
        word orient [currentLast] target move hseed hspecified
        (by simpa [localOrients, localComponent] using hedge)
  have hpair :
      GoertzelLemma814.chainEdgeInPair (pref ++ [currentLast])
          move.a move.c shiftedEdge =
        GoertzelLemma814.chainEdgeInPair [currentLast] move.a move.c edge := by
    simpa [shiftedEdge] using
      concreteChainFiberAppend_chainEdgeInPair_shift_occ_zero
        word pref currentLast move.a move.c edge hprefLen hedgeParts.1
  have hfresh :
      shiftedSeen.contains shiftedEdge = seen.contains edge := by
    simpa [shiftedSeen, shiftedEdge] using
      concreteChainFiberAppendShiftComponent_contains_shift_eq word seen edge
  have hshiftedMemIff : shiftedEdge ∈ shiftedSeen ↔ edge ∈ seen := by
    constructor
    · intro hmem
      have hcontains : shiftedSeen.contains shiftedEdge = true :=
        List.contains_iff_mem.mpr hmem
      have hlocalContains : seen.contains edge = true := by
        rw [← hfresh]
        exact hcontains
      exact List.contains_iff_mem.mp hlocalContains
    · intro hmem
      have hlocalContains : seen.contains edge = true :=
        List.contains_iff_mem.mpr hmem
      have hcontains : shiftedSeen.contains shiftedEdge = true := by
        rw [hfresh]
        exact hlocalContains
      exact List.contains_iff_mem.mp hcontains
  have hshare :
      shiftedSeen.any
          (fun other => GoertzelLemma814.chainEdgesShareEndpoint
            globalOrients shiftedEdge other) =
        seen.any (fun other => GoertzelLemma814.chainEdgesShareEndpoint
          localOrients edge other) := by
    simpa [shiftedSeen, shiftedEdge, globalOrients, localOrients] using
      concreteChainFiberAppendShiftComponent_any_shareEndpoint_shift_occ_zero
        word orient seen edge hedgeParts.1 hedgeParts.2 hseenParts
  by_cases hlocal :
      (GoertzelLemma814.nextChainComponentLayer localOrients [currentLast]
        move.a move.c seen).contains edge = true
  · have hlocalMem :
        edge ∈ GoertzelLemma814.nextChainComponentLayer localOrients
          [currentLast] move.a move.c seen :=
      List.contains_iff_mem.mp hlocal
    have hlocalFilter := hlocalMem
    unfold GoertzelLemma814.nextChainComponentLayer at hlocalFilter
    rw [List.mem_filter] at hlocalFilter
    rcases hlocalFilter with ⟨_hedgeChain, hlocalPred⟩
    have hglobalPred :
        (GoertzelLemma814.chainEdgeInPair (pref ++ [currentLast])
            move.a move.c shiftedEdge &&
          !shiftedSeen.contains shiftedEdge &&
          shiftedSeen.any
            (fun other => GoertzelLemma814.chainEdgesShareEndpoint
              globalOrients shiftedEdge other)) = true := by
      simpa [hpair, hfresh, hshiftedMemIff, hshare,
        globalOrients, localOrients] using
        hlocalPred
    have hglobalMem :
        shiftedEdge ∈ GoertzelLemma814.nextChainComponentLayer globalOrients
          (pref ++ [currentLast]) move.a move.c shiftedSeen := by
      unfold GoertzelLemma814.nextChainComponentLayer
      rw [List.mem_filter]
      exact ⟨List.contains_iff_mem.mp hglobalEdgeContains, hglobalPred⟩
    have hglobal :
        (GoertzelLemma814.nextChainComponentLayer globalOrients
          (pref ++ [currentLast]) move.a move.c shiftedSeen).contains
          shiftedEdge = true :=
      List.contains_iff_mem.mpr hglobalMem
    rw [hlocal]
    exact hglobal
  · have hlocalFalse := GoertzelLemma814.bool_false_of_not_true hlocal
    rw [hlocalFalse]
    apply GoertzelLemma814.bool_false_of_not_true
    intro hglobal
    have hglobalMem :
        shiftedEdge ∈ GoertzelLemma814.nextChainComponentLayer globalOrients
          (pref ++ [currentLast]) move.a move.c shiftedSeen :=
      List.contains_iff_mem.mp hglobal
    have hglobalFilter := hglobalMem
    unfold GoertzelLemma814.nextChainComponentLayer at hglobalFilter
    rw [List.mem_filter] at hglobalFilter
    rcases hglobalFilter with ⟨_hglobalChain, hglobalPred⟩
    have hlocalPred :
        (GoertzelLemma814.chainEdgeInPair [currentLast] move.a move.c edge &&
          !seen.contains edge &&
          seen.any (fun other => GoertzelLemma814.chainEdgesShareEndpoint
            localOrients edge other)) = true := by
      simpa [hpair, hfresh, hshiftedMemIff, hshare,
        globalOrients, localOrients] using
        hglobalPred
    have hlocalMem :
        edge ∈ GoertzelLemma814.nextChainComponentLayer localOrients
          [currentLast] move.a move.c seen := by
      unfold GoertzelLemma814.nextChainComponentLayer
      rw [List.mem_filter]
      exact ⟨hedgeLocalEdges, hlocalPred⟩
    have hlocalTrue :
        (GoertzelLemma814.nextChainComponentLayer localOrients
          [currentLast] move.a move.c seen).contains edge = true :=
      List.contains_iff_mem.mpr hlocalMem
    rw [hlocalFalse] at hlocalTrue
    cases hlocalTrue

theorem concreteChainFiberAppendLocalSingletonComponent_nextLayer_mem_component
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (currentLast : GoertzelLemma814.TauState)
    (move : GoertzelLemma814.ChainMove)
    (seen : List GoertzelLemma814.ChainEdge)
    (hseed :
      (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
        move.seed = true)
    (hseen :
      ∀ edge, edge ∈ seen →
        edge ∈ GoertzelLemma814.chainComponent
          (frontierWordToChainWord [orient]) [currentLast]
          move.a move.c move.seed)
    {edge : GoertzelLemma814.ChainEdge}
    (hmem :
      edge ∈ GoertzelLemma814.nextChainComponentLayer
        (frontierWordToChainWord [orient]) [currentLast] move.a move.c seen) :
    edge ∈ GoertzelLemma814.chainComponent
      (frontierWordToChainWord [orient]) [currentLast]
      move.a move.c move.seed := by
  let localOrients := frontierWordToChainWord [orient]
  let localComponent :=
    GoertzelLemma814.chainComponent localOrients [currentLast]
      move.a move.c move.seed
  have hseedMem : move.seed ∈ GoertzelLemma814.chainEdges localOrients :=
    List.contains_iff_mem.mp (by simpa [localOrients] using hseed)
  have hseenLocal :
      ∀ edge, edge ∈ seen → edge ∈ localComponent := by
    intro edge hmemSeen
    simpa [localOrients, localComponent] using hseen edge hmemSeen
  rcases GoertzelLemma814.nextChainComponentLayer_mem_mono_seen
      localOrients [currentLast] move.a move.c
      (seen₁ := seen) (seen₂ := localComponent)
      hseenLocal (by simpa [localOrients] using hmem) with
    hcomponent | hnext
  · simpa [localOrients, localComponent] using hcomponent
  · exact False.elim
      (GoertzelLemma814.chainComponent_nextLayer_empty
        localOrients [currentLast] move.a move.c move.seed hseedMem hnext)

theorem concreteChainFiberAppendLocalSingletonComponent_nextLayer_edge_occ_zero_not_input
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (target : List GoertzelLemma814.TauState)
    (currentLast : GoertzelLemma814.TauState)
    (move : GoertzelLemma814.ChainMove)
    (seen : List GoertzelLemma814.ChainEdge)
    (hseed :
      (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
        move.seed = true)
    (hspecified :
      GoertzelLemma814.chainSpecifiedKempeStep
        (frontierWordToChainWord [orient]) [currentLast] target move = true)
    (hseen :
      ∀ edge, edge ∈ seen →
        edge ∈ GoertzelLemma814.chainComponent
          (frontierWordToChainWord [orient]) [currentLast]
          move.a move.c move.seed)
    {edge : GoertzelLemma814.ChainEdge}
    (hmem :
      edge ∈ GoertzelLemma814.nextChainComponentLayer
        (frontierWordToChainWord [orient]) [currentLast] move.a move.c seen) :
    edge.occ = 0 ∧
      (GoertzelLemma814.tauOrientInputOrder
        (frontierOrientToChain orient)).contains edge.edge = false := by
  have hcomponent :
      edge ∈ GoertzelLemma814.chainComponent
        (frontierWordToChainWord [orient]) [currentLast]
        move.a move.c move.seed :=
    concreteChainFiberAppendLocalSingletonComponent_nextLayer_mem_component
      orient currentLast move seen hseed hseen hmem
  exact concreteChainFiberAppendLocalSingletonComponent_edge_occ_zero_not_input
    orient [currentLast] target move hseed hspecified hcomponent

theorem concreteChainFiberAppendLocalSingletonComponent_shift_nextLayer_lastBlock_eq
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (pref target : List GoertzelLemma814.TauState)
    (currentLast : GoertzelLemma814.TauState)
    (move : GoertzelLemma814.ChainMove)
    (seen : List GoertzelLemma814.ChainEdge)
    (hprefLen : pref.length = word.length)
    (hseed :
      (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
        move.seed = true)
    (hspecified :
      GoertzelLemma814.chainSpecifiedKempeStep
        (frontierWordToChainWord [orient]) [currentLast] target move = true)
    (hseen :
      ∀ edge, edge ∈ seen →
        edge ∈ GoertzelLemma814.chainComponent
          (frontierWordToChainWord [orient]) [currentLast]
          move.a move.c move.seed) :
    let localOrients := frontierWordToChainWord [orient]
    let globalOrients := frontierWordToChainWord (word ++ [orient])
    let shiftedSeen := concreteChainFiberAppendShiftComponent word seen
    List.filter
        (fun ge =>
          GoertzelLemma814.chainEdgeInPair (pref ++ [currentLast])
              move.a move.c ge &&
            !shiftedSeen.contains ge &&
            shiftedSeen.any
              (fun other => GoertzelLemma814.chainEdgesShareEndpoint
                globalOrients ge other))
        ((GoertzelLemma814.tauEdges.filter fun e =>
          !(GoertzelLemma814.tauOrientInputOrder
            (frontierOrientToChain orient)).contains e).map fun e =>
            ({ occ := word.length, edge := e } :
              GoertzelLemma814.ChainEdge)) =
      concreteChainFiberAppendShiftComponent word
        (GoertzelLemma814.nextChainComponentLayer localOrients [currentLast]
          move.a move.c seen) := by
  let localOrients := frontierWordToChainWord [orient]
  let globalOrients := frontierWordToChainWord (word ++ [orient])
  let shiftedSeen := concreteChainFiberAppendShiftComponent word seen
  let nonInput : GoertzelLemma814.TauEdge → Bool := fun e =>
    !(GoertzelLemma814.tauOrientInputOrder (frontierOrientToChain orient)).contains e
  let mkLocal : GoertzelLemma814.TauEdge → GoertzelLemma814.ChainEdge := fun e =>
    { occ := 0, edge := e }
  let mkGlobal : GoertzelLemma814.TauEdge → GoertzelLemma814.ChainEdge := fun e =>
    { occ := word.length, edge := e }
  let globalPred : GoertzelLemma814.ChainEdge → Bool := fun ge =>
    GoertzelLemma814.chainEdgeInPair (pref ++ [currentLast])
        move.a move.c ge &&
      !shiftedSeen.contains ge &&
      shiftedSeen.any (fun other =>
        GoertzelLemma814.chainEdgesShareEndpoint globalOrients ge other)
  let localPred : GoertzelLemma814.ChainEdge → Bool := fun edge =>
    GoertzelLemma814.chainEdgeInPair [currentLast] move.a move.c edge &&
      !seen.contains edge &&
      seen.any (fun other =>
        GoertzelLemma814.chainEdgesShareEndpoint localOrients edge other)
  have hseenParts :
      ∀ other, other ∈ seen →
        other.occ = 0 ∧
          (GoertzelLemma814.tauOrientInputOrder
            (frontierOrientToChain orient)).contains other.edge = false := by
    intro other hother
    exact concreteChainFiberAppendLocalSingletonComponent_edge_occ_zero_not_input
      orient [currentLast] target move hseed hspecified (hseen other hother)
  change List.filter globalPred
      ((GoertzelLemma814.tauEdges.filter nonInput).map mkGlobal) =
    concreteChainFiberAppendShiftComponent word
      (GoertzelLemma814.nextChainComponentLayer localOrients [currentLast]
        move.a move.c seen)
  calc
    List.filter globalPred
        ((GoertzelLemma814.tauEdges.filter nonInput).map mkGlobal) =
      List.map mkGlobal
        (List.filter (fun e => globalPred (mkGlobal e) && nonInput e)
          GoertzelLemma814.tauEdges) := by
          rw [List.filter_map]
          rw [List.filter_filter]
          rfl
    _ =
      List.map mkGlobal
        (List.filter (fun e => localPred (mkLocal e))
          GoertzelLemma814.tauEdges) := by
          apply congrArg (fun xs => List.map mkGlobal xs)
          apply List.filter_congr
          intro e _he
          by_cases hnon : nonInput e = true
          · have hpred :=
              concreteChainFiberAppendLocalNonInputEdge_shift_nextLayer_pred
                word orient pref currentLast move seen (mkLocal e) hprefLen
                (by simp [mkLocal])
                (by simpa [nonInput] using hnon)
                hseenParts
            rw [hnon]
            simp only [Bool.and_true]
            simpa [globalPred, localPred, mkGlobal, mkLocal, shiftedSeen,
              globalOrients, localOrients, concreteChainFiberAppendShiftEdge]
              using hpred
          · have hnonFalse : nonInput e = false :=
              GoertzelLemma814.bool_false_of_not_true hnon
            rw [hnonFalse]
            simp only [Bool.and_false]
            apply Eq.symm
            apply GoertzelLemma814.bool_false_of_not_true
            intro hlocalTrue
            have hchain : mkLocal e ∈ GoertzelLemma814.chainEdges localOrients := by
              have hcontains :
                  (GoertzelLemma814.chainEdges localOrients).contains
                      (mkLocal e) = true := by
                rw [concreteChainFiberAppend_chainEdges_singleton orient]
                exact List.contains_iff_mem.mpr
                  (List.mem_map.mpr
                    ⟨e, GoertzelLemma814.tauEdges_mem e, by simp [mkLocal]⟩)
              exact List.contains_iff_mem.mp hcontains
            have hlocalMem :
                mkLocal e ∈ GoertzelLemma814.nextChainComponentLayer
                  localOrients [currentLast] move.a move.c seen := by
              unfold GoertzelLemma814.nextChainComponentLayer
              rw [List.mem_filter]
              exact ⟨hchain, hlocalTrue⟩
            have hparts :=
              concreteChainFiberAppendLocalSingletonComponent_nextLayer_edge_occ_zero_not_input
                orient target currentLast move seen hseed hspecified hseen
                hlocalMem
            have hnotInput :
                (GoertzelLemma814.tauOrientInputOrder
                  (frontierOrientToChain orient)).contains e = false := by
              simpa [mkLocal] using hparts.2
            have hnotMem :
                ¬ e ∈ GoertzelLemma814.tauOrientInputOrder
                  (frontierOrientToChain orient) := by
              intro hmemInput
              have hcontains :
                  (GoertzelLemma814.tauOrientInputOrder
                    (frontierOrientToChain orient)).contains e = true :=
                List.contains_iff_mem.mpr hmemInput
              rw [hnotInput] at hcontains
              cases hcontains
            have hnonTrue : nonInput e = true := by
              simpa [nonInput] using hnotMem
            rw [hnonFalse] at hnonTrue
            cases hnonTrue
    _ =
      concreteChainFiberAppendShiftComponent word
        (GoertzelLemma814.nextChainComponentLayer localOrients [currentLast]
          move.a move.c seen) := by
          unfold concreteChainFiberAppendShiftComponent
            GoertzelLemma814.nextChainComponentLayer
          rw [concreteChainFiberAppend_chainEdges_singleton orient]
          rw [List.filter_map]
          rw [List.map_map]
          apply List.map_congr_left
          intro e _he
          simp [mkGlobal, concreteChainFiberAppendShiftEdge]

theorem concreteChainFiberAppendSingletonChainEdges_length_le
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient) :
    (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).length ≤
      (GoertzelLemma814.chainEdges
        (frontierWordToChainWord (word ++ [orient]))).length := by
  cases word with
  | nil =>
      simp [frontierWordToChainWord]
  | cons head tail =>
      cases head <;> cases orient <;>
        simp [frontierWordToChainWord, GoertzelLemma814.chainEdges,
          GoertzelLemma814.chainLocalEdges, GoertzelLemma814.bindList,
          List.range_succ_eq_map] <;>
        exact Nat.le_add_right 13 _

theorem concreteChainFiberAppendLocalSingletonComponent_shift_seed_globalComponent_mem
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (pref target : List GoertzelLemma814.TauState)
    (currentLast : GoertzelLemma814.TauState)
    (move : GoertzelLemma814.ChainMove)
    (hprefLen : pref.length = word.length)
    (hseed :
      (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
        move.seed = true)
    (hspecified :
      GoertzelLemma814.chainSpecifiedKempeStep
        (frontierWordToChainWord [orient]) [currentLast] target move = true) :
    (concreteChainFiberAppendShiftMove word move).seed ∈
      GoertzelLemma814.chainComponent
        (frontierWordToChainWord (word ++ [orient]))
        (pref ++ [currentLast]) move.a move.c
        (concreteChainFiberAppendShiftMove word move).seed := by
  let localOrients := frontierWordToChainWord [orient]
  let globalOrients := frontierWordToChainWord (word ++ [orient])
  let localComponent :=
    GoertzelLemma814.chainComponent localOrients [currentLast]
      move.a move.c move.seed
  have hspecifiedParts := hspecified
  unfold GoertzelLemma814.chainSpecifiedKempeStep at hspecifiedParts
  change (!localComponent.isEmpty &&
      GoertzelLemma814.chainComponentAvoidsInputs localOrients localComponent &&
      GoertzelLemma814.chainAgreesWithSwitch localOrients [currentLast] target
        localComponent move.a move.c) = true at hspecifiedParts
  simp only [Bool.and_eq_true] at hspecifiedParts
  rcases hspecifiedParts with ⟨⟨hLocalNonempty, _hLocalAvoid⟩, _hLocalAgree⟩
  have hlocalPair :
      GoertzelLemma814.chainEdgeInPair [currentLast] move.a move.c
        move.seed = true := by
    by_cases hpair :
        GoertzelLemma814.chainEdgeInPair [currentLast] move.a move.c
          move.seed = true
    · exact hpair
    · have hpairFalse := GoertzelLemma814.bool_false_of_not_true hpair
      have hempty : localComponent = [] := by
        simp [localComponent, GoertzelLemma814.chainComponent, localOrients,
          hpairFalse]
      rw [hempty] at hLocalNonempty
      cases hLocalNonempty
  have hseedOcc : move.seed.occ = 0 :=
    GoertzelLemma814.chainEdges_singleton_seed_occ_zero
      (frontierOrientToChain orient) move.seed
      (by simpa [frontierWordToChainWord] using hseed)
  have hglobalPair :
      GoertzelLemma814.chainEdgeInPair (pref ++ [currentLast]) move.a move.c
          (concreteChainFiberAppendShiftMove word move).seed = true := by
    have hpairEq :=
      concreteChainFiberAppend_chainEdgeInPair_shift_occ_zero
        word pref currentLast move.a move.c move.seed hprefLen hseedOcc
    simpa [concreteChainFiberAppendShiftMove, concreteChainFiberAppendShiftEdge]
      using hpairEq.trans hlocalPair
  have hmemClose :
      (concreteChainFiberAppendShiftMove word move).seed ∈
        GoertzelLemma814.closeChainComponent globalOrients
          (pref ++ [currentLast]) move.a move.c
          (GoertzelLemma814.chainEdges globalOrients).length
          [(concreteChainFiberAppendShiftMove word move).seed] := by
    exact GoertzelLemma814.closeChainComponent_mem_of_seen
      globalOrients (pref ++ [currentLast]) move.a move.c
      (GoertzelLemma814.chainEdges globalOrients).length
      (seen := [(concreteChainFiberAppendShiftMove word move).seed])
      (edge := (concreteChainFiberAppendShiftMove word move).seed)
      (by simp)
  simpa [GoertzelLemma814.chainComponent, globalOrients, hglobalPair]
    using hmemClose

theorem concreteChainFiberAppendLocalSingletonComponent_shift_close_mem_aux
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (pref target : List GoertzelLemma814.TauState)
    (currentLast : GoertzelLemma814.TauState)
    (move : GoertzelLemma814.ChainMove)
    (hprefLen : pref.length = word.length)
    (hseed :
      (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
        move.seed = true)
    (hspecified :
      GoertzelLemma814.chainSpecifiedKempeStep
        (frontierWordToChainWord [orient]) [currentLast] target move = true) :
    ∀ (k n : Nat) (seen : List GoertzelLemma814.ChainEdge),
      k + n ≤ (GoertzelLemma814.chainEdges
        (frontierWordToChainWord [orient])).length →
      (∀ edge, edge ∈ seen →
        edge ∈ GoertzelLemma814.closeChainComponent
          (frontierWordToChainWord [orient]) [currentLast]
          move.a move.c k [move.seed]) →
      (∀ edge, edge ∈ seen →
        concreteChainFiberAppendShiftEdge word edge ∈
          GoertzelLemma814.closeChainComponent
            (frontierWordToChainWord (word ++ [orient]))
            (pref ++ [currentLast]) move.a move.c k
            [(concreteChainFiberAppendShiftMove word move).seed]) →
      ∀ edge,
        edge ∈ GoertzelLemma814.closeChainComponent
          (frontierWordToChainWord [orient]) [currentLast]
          move.a move.c n seen →
        concreteChainFiberAppendShiftEdge word edge ∈
          GoertzelLemma814.closeChainComponent
            (frontierWordToChainWord (word ++ [orient]))
            (pref ++ [currentLast]) move.a move.c (k + n)
            [(concreteChainFiberAppendShiftMove word move).seed] := by
  let localOrients := frontierWordToChainWord [orient]
  let globalOrients := frontierWordToChainWord (word ++ [orient])
  let localLen := (GoertzelLemma814.chainEdges localOrients).length
  let localComponent :=
    GoertzelLemma814.chainComponent localOrients [currentLast]
      move.a move.c move.seed
  have hspecifiedParts := hspecified
  unfold GoertzelLemma814.chainSpecifiedKempeStep at hspecifiedParts
  change (!localComponent.isEmpty &&
      GoertzelLemma814.chainComponentAvoidsInputs localOrients localComponent &&
      GoertzelLemma814.chainAgreesWithSwitch localOrients [currentLast] target
        localComponent move.a move.c) = true at hspecifiedParts
  simp only [Bool.and_eq_true] at hspecifiedParts
  rcases hspecifiedParts with ⟨⟨hLocalNonempty, _hLocalAvoid⟩, _hLocalAgree⟩
  have hlocalPair :
      GoertzelLemma814.chainEdgeInPair [currentLast] move.a move.c
        move.seed = true := by
    by_cases hpair :
        GoertzelLemma814.chainEdgeInPair [currentLast] move.a move.c
          move.seed = true
    · exact hpair
    · have hpairFalse := GoertzelLemma814.bool_false_of_not_true hpair
      have hempty : localComponent = [] := by
        simp [localComponent, GoertzelLemma814.chainComponent, localOrients,
          hpairFalse]
      rw [hempty] at hLocalNonempty
      cases hLocalNonempty
  have hclose_mem_component :
      ∀ (j : Nat), j ≤ localLen → ∀ {edge : GoertzelLemma814.ChainEdge},
        edge ∈ GoertzelLemma814.closeChainComponent localOrients [currentLast]
          move.a move.c j [move.seed] →
        edge ∈ localComponent := by
    intro j hj edge hmem
    have hmono := GoertzelLemma814.closeChainComponent_mem_mono_add
      localOrients [currentLast] move.a move.c j (localLen - j) [move.seed]
      hmem
    have hnat : j + (localLen - j) = localLen := Nat.add_sub_of_le hj
    have hcloseLen :
        edge ∈ GoertzelLemma814.closeChainComponent localOrients [currentLast]
          move.a move.c localLen [move.seed] := by
      simpa [hnat] using hmono
    simpa [localComponent, GoertzelLemma814.chainComponent, localOrients,
      localLen, hlocalPair] using hcloseLen
  intro k n
  induction n generalizing k with
  | zero =>
      intro seen _hbudget _hseenLocal hseenGlobal edge hmem
      have hseen : edge ∈ seen := by
        simpa [GoertzelLemma814.closeChainComponent] using hmem
      simpa using hseenGlobal edge hseen
  | succ n ih =>
      intro seen hbudget hseenLocal hseenGlobal edge hmem
      simp only [GoertzelLemma814.closeChainComponent] at hmem
      have hrec := ih (k := k + 1)
        (seen := GoertzelLemma814.appendFresh seen
          (GoertzelLemma814.nextChainComponentLayer localOrients [currentLast]
            move.a move.c seen))
        (by omega)
        (by
          intro other hother
          rcases GoertzelLemma814.mem_appendFresh_source_or_mem seen
              (GoertzelLemma814.nextChainComponentLayer localOrients
                [currentLast] move.a move.c seen) hother with
            hseen | hlayer
          · exact GoertzelLemma814.closeChainComponent_mem_mono_succ
              localOrients [currentLast] move.a move.c k [move.seed]
              (hseenLocal other hseen)
          · rcases GoertzelLemma814.nextChainComponentLayer_mem_mono_seen
                localOrients [currentLast] move.a move.c
                (seen₁ := seen)
                (seen₂ := GoertzelLemma814.closeChainComponent localOrients
                  [currentLast] move.a move.c k [move.seed])
                hseenLocal hlayer with
              hclose | hnext
            · exact GoertzelLemma814.closeChainComponent_mem_mono_succ
                localOrients [currentLast] move.a move.c k [move.seed] hclose
            · exact GoertzelLemma814.closeChainComponent_mem_nextLayer_close
                localOrients [currentLast] move.a move.c k [move.seed] hnext)
        (by
          intro other hother
          rcases GoertzelLemma814.mem_appendFresh_source_or_mem seen
              (GoertzelLemma814.nextChainComponentLayer localOrients
                [currentLast] move.a move.c seen) hother with
            hseen | hlayer
          · exact GoertzelLemma814.closeChainComponent_mem_mono_succ
              globalOrients (pref ++ [currentLast]) move.a move.c k
              [(concreteChainFiberAppendShiftMove word move).seed]
              (hseenGlobal other hseen)
          · have hk_le_raw :
                k ≤ (GoertzelLemma814.chainEdges
                  (frontierWordToChainWord [orient])).length := by
              omega
            have hk_le : k ≤ localLen := by
              simpa [localLen, localOrients] using hk_le_raw
            have hseenComponent :
                ∀ seenEdge, seenEdge ∈ seen →
                  seenEdge ∈ localComponent := by
              intro seenEdge hseenEdge
              exact hclose_mem_component k hk_le
                (hseenLocal seenEdge hseenEdge)
            have hlocalNextClose :
                other ∈ GoertzelLemma814.closeChainComponent localOrients
                  [currentLast] move.a move.c (k + 1) [move.seed] := by
              rcases GoertzelLemma814.nextChainComponentLayer_mem_mono_seen
                  localOrients [currentLast] move.a move.c
                  (seen₁ := seen)
                  (seen₂ := GoertzelLemma814.closeChainComponent localOrients
                    [currentLast] move.a move.c k [move.seed])
                  hseenLocal hlayer with
                hclose | hnext
              · exact GoertzelLemma814.closeChainComponent_mem_mono_succ
                  localOrients [currentLast] move.a move.c k [move.seed] hclose
              · exact GoertzelLemma814.closeChainComponent_mem_nextLayer_close
                  localOrients [currentLast] move.a move.c k [move.seed] hnext
            have hk1_le_raw :
                k + 1 ≤ (GoertzelLemma814.chainEdges
                  (frontierWordToChainWord [orient])).length := by
              omega
            have hk1_le : k + 1 ≤ localLen := by
              simpa [localLen, localOrients] using hk1_le_raw
            have hedgeComponent : other ∈ localComponent :=
              hclose_mem_component (k + 1) hk1_le hlocalNextClose
            have hcontainsEq :=
              concreteChainFiberAppendLocalSingletonComponent_shift_nextLayer_contains
                word orient pref target currentLast move seen hprefLen hseed
                hspecified hseenComponent hedgeComponent
            have hlocalContains :
                (GoertzelLemma814.nextChainComponentLayer localOrients
                  [currentLast] move.a move.c seen).contains other = true :=
              List.contains_iff_mem.mpr hlayer
            have hglobalContains :
                (GoertzelLemma814.nextChainComponentLayer globalOrients
                  (pref ++ [currentLast]) move.a move.c
                  (concreteChainFiberAppendShiftComponent word seen)).contains
                  (concreteChainFiberAppendShiftEdge word other) = true := by
              rw [hcontainsEq]
              exact hlocalContains
            have hglobalLayer :
                concreteChainFiberAppendShiftEdge word other ∈
                  GoertzelLemma814.nextChainComponentLayer globalOrients
                    (pref ++ [currentLast]) move.a move.c
                    (concreteChainFiberAppendShiftComponent word seen) :=
              List.contains_iff_mem.mp hglobalContains
            have hsubGlobal :
                ∀ ge, ge ∈ concreteChainFiberAppendShiftComponent word seen →
                  ge ∈ GoertzelLemma814.closeChainComponent globalOrients
                    (pref ++ [currentLast]) move.a move.c k
                    [(concreteChainFiberAppendShiftMove word move).seed] := by
              intro ge hge
              unfold concreteChainFiberAppendShiftComponent at hge
              rcases List.mem_map.mp hge with ⟨localEdge, hlocalEdge, rfl⟩
              exact hseenGlobal localEdge hlocalEdge
            rcases GoertzelLemma814.nextChainComponentLayer_mem_mono_seen
                globalOrients (pref ++ [currentLast]) move.a move.c
                (seen₁ := concreteChainFiberAppendShiftComponent word seen)
                (seen₂ := GoertzelLemma814.closeChainComponent globalOrients
                  (pref ++ [currentLast]) move.a move.c k
                  [(concreteChainFiberAppendShiftMove word move).seed])
                hsubGlobal hglobalLayer with
              hclose | hnext
            · exact GoertzelLemma814.closeChainComponent_mem_mono_succ
                globalOrients (pref ++ [currentLast]) move.a move.c k
                [(concreteChainFiberAppendShiftMove word move).seed] hclose
            · exact GoertzelLemma814.closeChainComponent_mem_nextLayer_close
                globalOrients (pref ++ [currentLast]) move.a move.c k
                [(concreteChainFiberAppendShiftMove word move).seed] hnext)
        edge hmem
      have hnat : k + 1 + n = k + (n + 1) := by omega
      simpa [hnat] using hrec

theorem concreteChainFiberAppendLocalSingletonComponent_shift_globalComponent_mem
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (pref target : List GoertzelLemma814.TauState)
    (currentLast : GoertzelLemma814.TauState)
    (move : GoertzelLemma814.ChainMove)
    (hprefLen : pref.length = word.length)
    (hseed :
      (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
        move.seed = true)
    (hspecified :
      GoertzelLemma814.chainSpecifiedKempeStep
        (frontierWordToChainWord [orient]) [currentLast] target move = true)
    {edge : GoertzelLemma814.ChainEdge}
    (hmem :
      edge ∈ GoertzelLemma814.chainComponent
        (frontierWordToChainWord [orient]) [currentLast]
        move.a move.c move.seed) :
    concreteChainFiberAppendShiftEdge word edge ∈
      GoertzelLemma814.chainComponent
        (frontierWordToChainWord (word ++ [orient]))
        (pref ++ [currentLast]) move.a move.c
        (concreteChainFiberAppendShiftMove word move).seed := by
  let localOrients := frontierWordToChainWord [orient]
  let globalOrients := frontierWordToChainWord (word ++ [orient])
  let localLen := (GoertzelLemma814.chainEdges localOrients).length
  let globalLen := (GoertzelLemma814.chainEdges globalOrients).length
  let localComponent :=
    GoertzelLemma814.chainComponent localOrients [currentLast]
      move.a move.c move.seed
  have hspecifiedParts := hspecified
  unfold GoertzelLemma814.chainSpecifiedKempeStep at hspecifiedParts
  change (!localComponent.isEmpty &&
      GoertzelLemma814.chainComponentAvoidsInputs localOrients localComponent &&
      GoertzelLemma814.chainAgreesWithSwitch localOrients [currentLast] target
        localComponent move.a move.c) = true at hspecifiedParts
  simp only [Bool.and_eq_true] at hspecifiedParts
  rcases hspecifiedParts with ⟨⟨hLocalNonempty, _hLocalAvoid⟩, _hLocalAgree⟩
  have hlocalPair :
      GoertzelLemma814.chainEdgeInPair [currentLast] move.a move.c
        move.seed = true := by
    by_cases hpair :
        GoertzelLemma814.chainEdgeInPair [currentLast] move.a move.c
          move.seed = true
    · exact hpair
    · have hpairFalse := GoertzelLemma814.bool_false_of_not_true hpair
      have hempty : localComponent = [] := by
        simp [localComponent, GoertzelLemma814.chainComponent, localOrients,
          hpairFalse]
      rw [hempty] at hLocalNonempty
      cases hLocalNonempty
  have hlocalClose :
      edge ∈ GoertzelLemma814.closeChainComponent localOrients [currentLast]
        move.a move.c localLen [move.seed] := by
    simpa [localComponent, GoertzelLemma814.chainComponent, localOrients,
      localLen, hlocalPair] using hmem
  have hshiftSeed :
      concreteChainFiberAppendShiftEdge word move.seed =
        (concreteChainFiberAppendShiftMove word move).seed := by
    simp [concreteChainFiberAppendShiftEdge, concreteChainFiberAppendShiftMove]
  have hglobalCloseLocalLen :
      concreteChainFiberAppendShiftEdge word edge ∈
        GoertzelLemma814.closeChainComponent globalOrients
          (pref ++ [currentLast]) move.a move.c localLen
          [(concreteChainFiberAppendShiftMove word move).seed] := by
    have haux :=
      concreteChainFiberAppendLocalSingletonComponent_shift_close_mem_aux
        word orient pref target currentLast move hprefLen hseed hspecified
        0 localLen [move.seed] (by simp [localLen, localOrients])
        (by
          intro seenEdge hseenEdge
          have hseenEq : seenEdge = move.seed := by
            simpa using hseenEdge
          subst seenEdge
          simp [GoertzelLemma814.closeChainComponent])
        (by
          intro seenEdge hseenEdge
          have hseenEq : seenEdge = move.seed := by
            simpa using hseenEdge
          subst seenEdge
          simp [GoertzelLemma814.closeChainComponent, hshiftSeed])
        edge hlocalClose
    simpa [Nat.zero_add, globalOrients, localOrients, localLen] using haux
  have hlenLeRaw :
      (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).length ≤
        (GoertzelLemma814.chainEdges
          (frontierWordToChainWord (word ++ [orient]))).length :=
    concreteChainFiberAppendSingletonChainEdges_length_le word orient
  have hlenLe : localLen ≤ globalLen := by
    simpa [localLen, globalLen, localOrients, globalOrients] using hlenLeRaw
  have hglobalCloseLen :
      concreteChainFiberAppendShiftEdge word edge ∈
        GoertzelLemma814.closeChainComponent globalOrients
          (pref ++ [currentLast]) move.a move.c globalLen
          [(concreteChainFiberAppendShiftMove word move).seed] := by
    have hmono := GoertzelLemma814.closeChainComponent_mem_mono_add
      globalOrients (pref ++ [currentLast]) move.a move.c localLen
      (globalLen - localLen) [(concreteChainFiberAppendShiftMove word move).seed]
      hglobalCloseLocalLen
    have hnat : localLen + (globalLen - localLen) = globalLen :=
      Nat.add_sub_of_le hlenLe
    simpa [hnat] using hmono
  have hseedOcc : move.seed.occ = 0 :=
    GoertzelLemma814.chainEdges_singleton_seed_occ_zero
      (frontierOrientToChain orient) move.seed
      (by simpa [frontierWordToChainWord] using hseed)
  have hglobalPair :
      GoertzelLemma814.chainEdgeInPair (pref ++ [currentLast])
          move.a move.c (concreteChainFiberAppendShiftMove word move).seed =
        true := by
    have hpairEq :=
      concreteChainFiberAppend_chainEdgeInPair_shift_occ_zero
        word pref currentLast move.a move.c move.seed hprefLen hseedOcc
    simpa [concreteChainFiberAppendShiftMove, concreteChainFiberAppendShiftEdge]
      using hpairEq.trans hlocalPair
  simpa [GoertzelLemma814.chainComponent, globalOrients, globalLen, hglobalPair]
    using hglobalCloseLen

/--
Local singleton saturation pin for the remaining reverse/no-ingress direction.

For a specified singleton Kempe step, let `localComponent` be the component
closed for the singleton gadget.  The remaining local fact is that no outer
input edge can still be present in the next component layer of that already
closed component.  This is the exact local saturation/avoidance statement
needed after the boundary pair-color and endpoint-sharing transfers reduce a
glued-boundary prefix ingress to a singleton input-edge ingress.
-/
def concreteChainFiberAppendLocalSingletonComponentOuterInputNextLayerClosed :
    Prop :=
  ∀ (orient : GoertzelLemma818FrontierMode.TauOrient)
    (currentLast : GoertzelLemma814.TauState)
    (target : List GoertzelLemma814.TauState)
    (move : GoertzelLemma814.ChainMove)
    (inputEdge : GoertzelLemma814.TauEdge),
    (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
        move.seed = true →
      GoertzelLemma814.chainSpecifiedKempeStep
        (frontierWordToChainWord [orient]) [currentLast] target move = true →
      let inputLocal : GoertzelLemma814.ChainEdge := { occ := 0, edge := inputEdge }
      let localOrients := frontierWordToChainWord [orient]
      let localComponent :=
        GoertzelLemma814.chainComponent localOrients [currentLast]
          move.a move.c move.seed
      (GoertzelLemma814.chainOuterInputEdges localOrients).contains
          inputLocal = true →
        inputLocal ∈ GoertzelLemma814.nextChainComponentLayer
          localOrients [currentLast] move.a move.c localComponent →
          False

theorem concreteChainFiberAppendLocalSingletonComponentOuterInputNextLayerClosed_ok :
    concreteChainFiberAppendLocalSingletonComponentOuterInputNextLayerClosed := by
  intro orient currentLast _target move inputEdge hseed _hspecified
  dsimp
  intro _houter hnext
  exact GoertzelLemma814.chainComponent_nextLayer_empty
    (frontierWordToChainWord [orient]) [currentLast] move.a move.c move.seed
    (List.contains_iff_mem.mp hseed) hnext

theorem concreteChainFiberAppend_boundary_output_ingress_contradiction
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (leftOrient : GoertzelLemma814.TauOrient)
    (pref : List GoertzelLemma814.TauState)
    (lastX currentLast : GoertzelLemma814.TauState)
    (move : GoertzelLemma814.ChainMove)
    (localComponent : List GoertzelLemma814.ChainEdge)
    (localEdge : GoertzelLemma814.ChainEdge)
    (outputEdge inputEdge : GoertzelLemma814.TauEdge)
    (target : List GoertzelLemma814.TauState)
    (hne : word ≠ [])
    (hprefLen : pref.length = word.length)
    (hleft :
      GoertzelLemma814.tauOrientAt
        (frontierWordToChainWord (word ++ [orient])) (word.length - 1) =
        leftOrient)
    (hcompatibleX : GoertzelLemma814.compatibleAdjacent
      leftOrient (frontierOrientToChain orient)
      (GoertzelLemma814.chainStateAt pref (word.length - 1))
      lastX = true)
    (htrace :
      concreteChainFiberAppendLastInputTrace orient currentLast =
        concreteChainFiberAppendLastInputTrace orient lastX)
    (hzip :
      (outputEdge, inputEdge) ∈
        (GoertzelLemma814.tauOrientOutputOrder leftOrient).zip
          (GoertzelLemma814.tauOrientInputOrder
            (frontierOrientToChain orient)))
    (hlocalComponent :
      localComponent = GoertzelLemma814.chainComponent
        (frontierWordToChainWord [orient]) [currentLast]
        move.a move.c move.seed)
    (hlocalMem : localEdge ∈ localComponent)
    (hlocalAvoid :
      GoertzelLemma814.chainComponentAvoidsInputs
        (frontierWordToChainWord [orient]) localComponent = true)
    (hlocalOcc : localEdge.occ = 0)
    (hlocalNotInput :
      (GoertzelLemma814.tauOrientInputOrder
        (frontierOrientToChain orient)).contains localEdge.edge = false)
    (houtputPair :
      GoertzelLemma814.chainEdgeInPair (pref ++ [currentLast])
        move.a move.c
        ({ occ := word.length - 1, edge := outputEdge } :
          GoertzelLemma814.ChainEdge) = true)
    (hshare :
      GoertzelLemma814.chainEdgesShareEndpoint
        (frontierWordToChainWord (word ++ [orient]))
        ({ occ := word.length - 1, edge := outputEdge } :
          GoertzelLemma814.ChainEdge)
        (concreteChainFiberAppendShiftEdge word localEdge) = true)
    (hseed :
      (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
        move.seed = true)
    (hspecified :
      GoertzelLemma814.chainSpecifiedKempeStep
        (frontierWordToChainWord [orient]) [currentLast] target move = true) :
    False := by
  let inputLocal : GoertzelLemma814.ChainEdge := { occ := 0, edge := inputEdge }
  have hnext : inputLocal ∈ GoertzelLemma814.nextChainComponentLayer
      (frontierWordToChainWord [orient]) [currentLast]
      move.a move.c localComponent := by
    simpa [inputLocal] using
      concreteChainFiberAppend_boundary_output_ingress_local_input_nextLayer
        word orient leftOrient pref lastX currentLast move localComponent
        localEdge outputEdge inputEdge hne hprefLen hleft hcompatibleX htrace
        hzip hlocalMem hlocalAvoid hlocalOcc hlocalNotInput houtputPair hshare
  have houter :
      (GoertzelLemma814.chainOuterInputEdges
        (frontierWordToChainWord [orient])).contains inputLocal = true := by
    cases leftOrient <;> cases orient <;>
      simp [GoertzelLemma814.tauOrientOutputOrder,
        GoertzelLemma814.tauOrientInputOrder, frontierOrientToChain] at hzip
    all_goals
      rcases hzip with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [inputLocal, frontierWordToChainWord, frontierOrientToChain,
          GoertzelLemma814.chainOuterInputEdges, GoertzelLemma814.chainInputOrder,
          GoertzelLemma814.tauOrientAt, GoertzelLemma814.listGetD,
          GoertzelLemma814.tauOrientInputOrder]
  have hnextComponent : inputLocal ∈ GoertzelLemma814.nextChainComponentLayer
      (frontierWordToChainWord [orient]) [currentLast]
      move.a move.c
      (GoertzelLemma814.chainComponent (frontierWordToChainWord [orient])
        [currentLast] move.a move.c move.seed) := by
    simpa [hlocalComponent] using hnext
  exact concreteChainFiberAppendLocalSingletonComponentOuterInputNextLayerClosed_ok
    orient currentLast target move inputEdge hseed hspecified houter
    hnextComponent

theorem concreteChainFiberAppendLocalSingletonComponent_shift_nextLayer_prefix_empty
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (pref target : List GoertzelLemma814.TauState)
    (lastX currentLast : GoertzelLemma814.TauState)
    (move : GoertzelLemma814.ChainMove)
    (seen : List GoertzelLemma814.ChainEdge)
    (hne : word ≠ [])
    (hprefLen : pref.length = word.length)
    (hcompatibleX : GoertzelLemma814.compatibleAdjacent
      (GoertzelLemma814.tauOrientAt
        (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
      (frontierOrientToChain orient)
      (GoertzelLemma814.chainStateAt pref (word.length - 1))
      lastX = true)
    (htrace :
      concreteChainFiberAppendLastInputTrace orient currentLast =
        concreteChainFiberAppendLastInputTrace orient lastX)
    (hseed :
      (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
        move.seed = true)
    (hspecified :
      GoertzelLemma814.chainSpecifiedKempeStep
        (frontierWordToChainWord [orient]) [currentLast] target move = true)
    (hseen :
      ∀ edge, edge ∈ seen →
        edge ∈ GoertzelLemma814.chainComponent
          (frontierWordToChainWord [orient]) [currentLast]
          move.a move.c move.seed) :
    let globalOrients := frontierWordToChainWord (word ++ [orient])
    let shiftedSeen := concreteChainFiberAppendShiftComponent word seen
    List.filter
        (fun ge =>
          GoertzelLemma814.chainEdgeInPair (pref ++ [currentLast])
              move.a move.c ge &&
            !shiftedSeen.contains ge &&
            shiftedSeen.any
              (fun other => GoertzelLemma814.chainEdgesShareEndpoint
                globalOrients ge other))
        (GoertzelLemma814.chainEdges (frontierWordToChainWord word)) =
      [] := by
  let localOrients := frontierWordToChainWord [orient]
  let globalOrients := frontierWordToChainWord (word ++ [orient])
  let shiftedSeen := concreteChainFiberAppendShiftComponent word seen
  let localComponent :=
    GoertzelLemma814.chainComponent localOrients [currentLast]
      move.a move.c move.seed
  let globalPred : GoertzelLemma814.ChainEdge → Bool := fun ge =>
    GoertzelLemma814.chainEdgeInPair (pref ++ [currentLast])
        move.a move.c ge &&
      !shiftedSeen.contains ge &&
      shiftedSeen.any (fun other =>
        GoertzelLemma814.chainEdgesShareEndpoint globalOrients ge other)
  have hspecifiedParts := hspecified
  unfold GoertzelLemma814.chainSpecifiedKempeStep at hspecifiedParts
  change (!localComponent.isEmpty &&
      GoertzelLemma814.chainComponentAvoidsInputs localOrients localComponent &&
      GoertzelLemma814.chainAgreesWithSwitch localOrients [currentLast] target
        localComponent move.a move.c) = true at hspecifiedParts
  simp only [Bool.and_eq_true] at hspecifiedParts
  rcases hspecifiedParts with
    ⟨⟨_hLocalNonempty, hlocalAvoid⟩, _hLocalAgree⟩
  change List.filter globalPred
      (GoertzelLemma814.chainEdges (frontierWordToChainWord word)) = []
  apply List.eq_nil_iff_forall_not_mem.2
  intro ge hgeFilter
  rw [List.mem_filter] at hgeFilter
  rcases hgeFilter with ⟨hgeChain, hpred⟩
  have hgeChainFilter := hgeChain
  unfold GoertzelLemma814.chainEdges at hgeChainFilter
  rw [List.mem_filter] at hgeChainFilter
  rcases hgeChainFilter with ⟨hgeLocal, _hgeRep⟩
  have hprefixRaw :
      ge.occ < (frontierWordToChainWord word).length :=
    GoertzelLemma814.chainLocalEdges_mem_occ_lt hgeLocal
  have hprefix : ge.occ < word.length := by
    simpa [frontierWordToChainWord] using hprefixRaw
  have hpredParts := hpred
  simp only [globalPred, Bool.and_eq_true] at hpredParts
  rcases hpredParts with ⟨⟨hpair, _hfresh⟩, hany⟩
  rw [List.any_eq_true] at hany
  rcases hany with ⟨other, hotherMem, hshareOther⟩
  unfold shiftedSeen concreteChainFiberAppendShiftComponent at hotherMem
  rcases List.mem_map.mp hotherMem with
    ⟨localEdge, hlocalSeen, hotherEq⟩
  subst other
  have hlocalMem : localEdge ∈ localComponent := by
    simpa [localOrients, localComponent] using hseen localEdge hlocalSeen
  have hlocalParts :=
    concreteChainFiberAppendLocalSingletonComponent_edge_occ_zero_not_input
      orient [currentLast] target move hseed hspecified
      (by simpa [localOrients, localComponent] using hlocalMem)
  have hlocalOcc : localEdge.occ = 0 := hlocalParts.1
  have hlocalNotInput :
      (GoertzelLemma814.tauOrientInputOrder
        (frontierOrientToChain orient)).contains localEdge.edge = false :=
    hlocalParts.2
  have hshareShift :
      GoertzelLemma814.chainEdgesShareEndpoint globalOrients ge
        (concreteChainFiberAppendShiftEdge word localEdge) = true := by
    simpa [globalOrients] using hshareOther
  have hoccSucc : ge.occ + 1 = word.length :=
    concreteChainFiberAppend_prefix_share_shift_occ_succ
      word orient ge localEdge hprefix hlocalOcc
      (by simpa [globalOrients] using hshareShift)
  let leftOrient :=
    GoertzelLemma814.tauOrientAt globalOrients (word.length - 1)
  have hleft :
      GoertzelLemma814.tauOrientAt globalOrients (word.length - 1) =
        leftOrient := rfl
  rcases concreteChainFiberAppend_prefix_share_shift_output_zip
      word orient leftOrient ge localEdge
      (by simpa [globalOrients] using hleft) hprefix hoccSucc hlocalOcc
      (by simpa [globalOrients] using hshareShift) with
    ⟨outputEdge, inputEdge, hzip, hgeEq⟩
  have houtputPair :
      GoertzelLemma814.chainEdgeInPair (pref ++ [currentLast])
        move.a move.c
        ({ occ := word.length - 1, edge := outputEdge } :
          GoertzelLemma814.ChainEdge) = true := by
    simpa [← hgeEq] using hpair
  have hshareOutput :
      GoertzelLemma814.chainEdgesShareEndpoint globalOrients
        ({ occ := word.length - 1, edge := outputEdge } :
          GoertzelLemma814.ChainEdge)
        (concreteChainFiberAppendShiftEdge word localEdge) = true := by
    simpa [← hgeEq] using hshareShift
  exact concreteChainFiberAppend_boundary_output_ingress_contradiction
    word orient leftOrient pref lastX currentLast move localComponent localEdge
    outputEdge inputEdge target hne hprefLen
    (by simpa [globalOrients] using hleft)
    (by simpa [globalOrients, leftOrient] using hcompatibleX)
    htrace hzip rfl hlocalMem hlocalAvoid hlocalOcc hlocalNotInput
    houtputPair (by simpa [globalOrients] using hshareOutput)
    hseed hspecified

/--
Pinned reverse/no-ingress component equality for the singleton append lift.

Forward membership from the local singleton component into the appended global
component is proved by
`concreteChainFiberAppendLocalSingletonComponent_shift_globalComponent_mem`.
The remaining direction is to show that the appended global component cannot
grow a prefix or glued-boundary edge. The boundary transfer pieces are now
isolated and wired to a contradiction: pair-color transfer is
`concreteChainFiberAppend_boundary_output_pair_forces_input_pair`,
endpoint-sharing transfer is
`concreteChainFiberAppend_boundary_output_share_shift_forces_input_share`, and
their combined next-layer ingress is
`concreteChainFiberAppend_boundary_output_ingress_local_input_nextLayer`.
Local singleton saturation is proved by
`concreteChainFiberAppendLocalSingletonComponentOuterInputNextLayerClosed_ok`,
and glued-boundary output ingress is refuted by
`concreteChainFiberAppend_boundary_output_ingress_contradiction`.

The remaining list-level pin is the order-preserving next-layer commutation
needed by the closure induction: for every shifted seen list `seen` whose
members lie in the singleton local component, the appended-chain
`nextChainComponentLayer` from
`concreteChainFiberAppendShiftComponent word seen` must be exactly
`concreteChainFiberAppendShiftComponent word` applied to the singleton local
`nextChainComponentLayer`.  The shifted-local candidate direction is
`concreteChainFiberAppendLocalSingletonComponent_shift_nextLayer_contains`;
the reverse direction must classify every appended-chain candidate sharing a
shifted local endpoint as either a shifted local edge or a glued-boundary
prefix output, then use the boundary-ingress contradiction above.
-/
def concreteChainFiberAppendRelativeSingletonShiftedComponentClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX : GoertzelLemma814.TauState),
            (_hpref : pref ∈ concreteChainFiber word key) →
            (_hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (_hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            ∀ (_hkeyLocal :
                concreteChainFiberAppendLastInputTrace orient lastX ∈
                  GoertzelLemma814.colorAssignments4)
              (current target : List GoertzelLemma814.TauState)
              (currentLast targetLast : GoertzelLemma814.TauState),
              current ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              target ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              current = [currentLast] →
              target = [targetLast] →
              ∀ (move : GoertzelLemma814.ChainMove),
                GoertzelLemma814.colorPairs.contains (move.a, move.c) = true →
                (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
                  move.seed = true →
                GoertzelLemma814.chainSpecifiedKempeStep
                  (frontierWordToChainWord [orient]) current target move = true →
                GoertzelLemma814.chainComponent
                  (frontierWordToChainWord (word ++ [orient]))
                  (pref ++ [currentLast]) move.a move.c
                  (concreteChainFiberAppendShiftMove word move).seed =
                concreteChainFiberAppendShiftComponent word
                  (GoertzelLemma814.chainComponent
                    (frontierWordToChainWord [orient]) current move.a move.c
                    move.seed)

def concreteChainFiberAppendRelativeSingletonShiftedSwitchAgreementClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX : GoertzelLemma814.TauState),
            (_hpref : pref ∈ concreteChainFiber word key) →
            (_hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (_hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            ∀ (_hkeyLocal :
                concreteChainFiberAppendLastInputTrace orient lastX ∈
                  GoertzelLemma814.colorAssignments4)
              (current target : List GoertzelLemma814.TauState)
              (currentLast targetLast : GoertzelLemma814.TauState),
              current ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              target ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              current = [currentLast] →
              target = [targetLast] →
              ∀ (move : GoertzelLemma814.ChainMove),
                GoertzelLemma814.colorPairs.contains (move.a, move.c) = true →
                (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
                  move.seed = true →
                GoertzelLemma814.chainSpecifiedKempeStep
                  (frontierWordToChainWord [orient]) current target move = true →
                GoertzelLemma814.chainAgreesWithSwitch
                  (frontierWordToChainWord (word ++ [orient]))
                  (pref ++ [currentLast]) (pref ++ [targetLast])
                  (concreteChainFiberAppendShiftComponent word
                    (GoertzelLemma814.chainComponent
                      (frontierWordToChainWord [orient]) current move.a move.c
                      move.seed))
                  move.a move.c = true

def concreteChainFiberAppendRelativeSingletonShiftedSwitchPointClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX : GoertzelLemma814.TauState),
            (_hpref : pref ∈ concreteChainFiber word key) →
            (_hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (_hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            ∀ (_hkeyLocal :
                concreteChainFiberAppendLastInputTrace orient lastX ∈
                  GoertzelLemma814.colorAssignments4)
              (current target : List GoertzelLemma814.TauState)
              (currentLast targetLast : GoertzelLemma814.TauState),
              current ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              target ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              current = [currentLast] →
              target = [targetLast] →
              ∀ (move : GoertzelLemma814.ChainMove),
                GoertzelLemma814.colorPairs.contains (move.a, move.c) = true →
                (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
                  move.seed = true →
                GoertzelLemma814.chainSpecifiedKempeStep
                  (frontierWordToChainWord [orient]) current target move = true →
                ∀ (ge : GoertzelLemma814.ChainEdge),
                  ge ∈ GoertzelLemma814.chainLocalEdges
                    (frontierWordToChainWord (word ++ [orient])) →
                    GoertzelLemma814.colorEq
                      (GoertzelLemma814.chainEdgeColor
                        (pref ++ [targetLast]) ge)
                      (GoertzelLemma814.chainSwitchedColor
                        (frontierWordToChainWord (word ++ [orient]))
                        (pref ++ [currentLast])
                        (concreteChainFiberAppendShiftComponent word
                          (GoertzelLemma814.chainComponent
                            (frontierWordToChainWord [orient]) current
                            move.a move.c move.seed))
                        move.a move.c ge) = true

def concreteChainFiberAppendRelativeSingletonShiftedSwitchPointGoal
    (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (pref current : List GoertzelLemma814.TauState)
    (currentLast targetLast : GoertzelLemma814.TauState)
    (move : GoertzelLemma814.ChainMove)
    (ge : GoertzelLemma814.ChainEdge) : Prop :=
  GoertzelLemma814.colorEq
    (GoertzelLemma814.chainEdgeColor (pref ++ [targetLast]) ge)
    (GoertzelLemma814.chainSwitchedColor
      (frontierWordToChainWord (word ++ [orient]))
      (pref ++ [currentLast])
      (concreteChainFiberAppendShiftComponent word
        (GoertzelLemma814.chainComponent
          (frontierWordToChainWord [orient]) current
          move.a move.c move.seed))
      move.a move.c ge) = true

def concreteChainFiberAppendRelativeSingletonShiftedSwitchPrefixPointClosed :
    Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX : GoertzelLemma814.TauState),
            (_hpref : pref ∈ concreteChainFiber word key) →
            (_hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (_hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            ∀ (_hkeyLocal :
                concreteChainFiberAppendLastInputTrace orient lastX ∈
                  GoertzelLemma814.colorAssignments4)
              (current target : List GoertzelLemma814.TauState)
              (currentLast targetLast : GoertzelLemma814.TauState),
              current ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              target ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              current = [currentLast] →
              target = [targetLast] →
              ∀ (move : GoertzelLemma814.ChainMove),
                GoertzelLemma814.colorPairs.contains (move.a, move.c) = true →
                (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
                  move.seed = true →
                GoertzelLemma814.chainSpecifiedKempeStep
                  (frontierWordToChainWord [orient]) current target move = true →
                ∀ (ge : GoertzelLemma814.ChainEdge),
                  ge ∈ GoertzelLemma814.chainLocalEdges
                    (frontierWordToChainWord (word ++ [orient])) →
                  ge.occ < word.length →
                    concreteChainFiberAppendRelativeSingletonShiftedSwitchPointGoal
                      word orient pref current currentLast targetLast move ge

theorem concreteChainFiberAppendRelativeSingletonShiftedSwitchPrefixPointClosed_of_compatible_prefix :
    concreteChainFiberAppendRelativeSingletonShiftedSwitchPrefixPointClosed := by
  intro word orient hne _hcert key _hkey pref lastX hpref _hlastX
    hcompatibleX _hkeyLocal current target currentLast targetLast hcurrent
    htarget hcurrentEq htargetEq move _hpair _hseed _hspecified ge _hge
    hprefix
  subst current
  subst target
  let localComponent :=
    GoertzelLemma814.chainComponent (frontierWordToChainWord [orient])
      [currentLast] move.a move.c move.seed
  let shiftedComponent := concreteChainFiberAppendShiftComponent word localComponent
  have hprefLen : pref.length = word.length := by
    have hprefRaw := hpref
    unfold concreteChainFiber GoertzelLemma814.chainFiberFrom at hprefRaw
    have hprefStates : pref ∈ concreteChainStates word :=
      (List.mem_filter.mp hprefRaw).1
    have hlen :=
      GoertzelLemma814.allChainStates_mem_length
        (orients := frontierWordToChainWord word)
        (by simpa [concreteChainStates] using hprefStates)
    simpa [frontierWordToChainWord] using hlen
  have hcurrentGlobal :
      pref ++ [currentLast] ∈ concreteChainFiber (word ++ [orient]) key :=
    concreteChainFiberAppend_mem_of_prefix_and_local_singleton
      word orient hne key hpref hcompatibleX hcurrent rfl
  have hcurrentStates :
      pref ++ [currentLast] ∈ concreteChainStates (word ++ [orient]) := by
    unfold concreteChainFiber GoertzelLemma814.chainFiberFrom at hcurrentGlobal
    exact (List.mem_filter.mp hcurrentGlobal).1
  have hcurrentCompatible :
      GoertzelLemma814.compatibleChainStates
        (frontierWordToChainWord (word ++ [orient]))
        (pref ++ [currentLast]) = true := by
    have hAll :=
      GoertzelLemma814.allChainStates_compatible
        (frontierWordToChainWord (word ++ [orient]))
    rw [List.all_eq_true] at hAll
    exact hAll (pref ++ [currentLast])
      (by simpa [concreteChainStates] using hcurrentStates)
  have htargetColor :
      GoertzelLemma814.chainEdgeColor (pref ++ [targetLast]) ge =
        GoertzelLemma814.chainEdgeColor pref ge := by
    cases ge with
    | mk occ edge =>
        have hocc : occ < pref.length := by
          simpa [hprefLen] using hprefix
        simp [GoertzelLemma814.chainEdgeColor, GoertzelLemma814.tauStateColorAt,
          GoertzelLemma814.chainStateAt_append_left pref targetLast hocc]
  have hcurrentColor :
      GoertzelLemma814.chainEdgeColor (pref ++ [currentLast]) ge =
        GoertzelLemma814.chainEdgeColor pref ge := by
    cases ge with
    | mk occ edge =>
        have hocc : occ < pref.length := by
          simpa [hprefLen] using hprefix
        simp [GoertzelLemma814.chainEdgeColor, GoertzelLemma814.tauStateColorAt,
          GoertzelLemma814.chainStateAt_append_left pref currentLast hocc]
  have hglobalOcc :
      ge.occ < (frontierWordToChainWord (word ++ [orient])).length := by
    simp [frontierWordToChainWord]
    omega
  have hcanonicalColor :
      GoertzelLemma814.chainEdgeColor (pref ++ [currentLast])
          (GoertzelLemma814.chainCanonicalEdge
            (frontierWordToChainWord (word ++ [orient])) ge) =
        GoertzelLemma814.chainEdgeColor (pref ++ [currentLast]) ge :=
    GoertzelLemma814.chainEdgeColor_chainCanonicalEdge_of_compatible
      hcurrentCompatible ge hglobalOcc
  have hcontainsFalse :
      shiftedComponent.contains
          (GoertzelLemma814.chainCanonicalEdge
            (frontierWordToChainWord (word ++ [orient])) ge) = false := by
    simpa [shiftedComponent, localComponent] using
      concreteChainFiberAppendShiftComponent_contains_canonical_prefix_false
        word orient localComponent ge hprefix
  have hcontainsFalseRaw :
      (concreteChainFiberAppendShiftComponent word
          (GoertzelLemma814.chainComponent (frontierWordToChainWord [orient])
            [currentLast] move.a move.c move.seed)).contains
          (GoertzelLemma814.chainCanonicalEdge
            (frontierWordToChainWord (word ++ [orient])) ge) = false := by
    simpa [shiftedComponent, localComponent] using hcontainsFalse
  have hcanonicalNotMemRaw :
      GoertzelLemma814.chainCanonicalEdge
          (frontierWordToChainWord (word ++ [orient])) ge ∉
        concreteChainFiberAppendShiftComponent word
          (GoertzelLemma814.chainComponent (frontierWordToChainWord [orient])
            [currentLast] move.a move.c move.seed) := by
    intro hmem
    have hcontainsTrue :
        (concreteChainFiberAppendShiftComponent word
            (GoertzelLemma814.chainComponent (frontierWordToChainWord [orient])
              [currentLast] move.a move.c move.seed)).contains
            (GoertzelLemma814.chainCanonicalEdge
              (frontierWordToChainWord (word ++ [orient])) ge) = true :=
      List.contains_iff_mem.mpr hmem
    rw [hcontainsFalseRaw] at hcontainsTrue
    cases hcontainsTrue
  have hswitch :
      GoertzelLemma814.chainSwitchedColor
          (frontierWordToChainWord (word ++ [orient]))
          (pref ++ [currentLast])
          (concreteChainFiberAppendShiftComponent word
            (GoertzelLemma814.chainComponent (frontierWordToChainWord [orient])
              [currentLast] move.a move.c move.seed))
          move.a move.c ge =
        GoertzelLemma814.chainEdgeColor pref ge := by
    simp [GoertzelLemma814.chainSwitchedColor, hcanonicalNotMemRaw,
      hcanonicalColor, hcurrentColor]
  unfold concreteChainFiberAppendRelativeSingletonShiftedSwitchPointGoal
  simp [hswitch, htargetColor, GoertzelLemma814.colorEq]

def concreteChainFiberAppendRelativeSingletonShiftedSwitchLastNonGluedPointClosed :
    Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX : GoertzelLemma814.TauState),
            (_hpref : pref ∈ concreteChainFiber word key) →
            (_hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (_hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            ∀ (_hkeyLocal :
                concreteChainFiberAppendLastInputTrace orient lastX ∈
                  GoertzelLemma814.colorAssignments4)
              (current target : List GoertzelLemma814.TauState)
              (currentLast targetLast : GoertzelLemma814.TauState),
              current ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              target ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              current = [currentLast] →
              target = [targetLast] →
              ∀ (move : GoertzelLemma814.ChainMove),
                GoertzelLemma814.colorPairs.contains (move.a, move.c) = true →
                (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
                  move.seed = true →
                GoertzelLemma814.chainSpecifiedKempeStep
                  (frontierWordToChainWord [orient]) current target move = true →
                ∀ (ge : GoertzelLemma814.ChainEdge),
                  ge ∈ GoertzelLemma814.chainLocalEdges
                    (frontierWordToChainWord (word ++ [orient])) →
                  ge.occ = word.length →
                  GoertzelLemma814.chainIsGluedInput
                    (frontierWordToChainWord (word ++ [orient]))
                    ge.occ ge.edge = false →
                    concreteChainFiberAppendRelativeSingletonShiftedSwitchPointGoal
                      word orient pref current currentLast targetLast move ge

def concreteChainFiberAppendRelativeSingletonShiftedSwitchLastGluedPointClosed :
    Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX : GoertzelLemma814.TauState),
            (_hpref : pref ∈ concreteChainFiber word key) →
            (_hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (_hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            ∀ (_hkeyLocal :
                concreteChainFiberAppendLastInputTrace orient lastX ∈
                  GoertzelLemma814.colorAssignments4)
              (current target : List GoertzelLemma814.TauState)
              (currentLast targetLast : GoertzelLemma814.TauState),
              current ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              target ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              current = [currentLast] →
              target = [targetLast] →
              ∀ (move : GoertzelLemma814.ChainMove),
                GoertzelLemma814.colorPairs.contains (move.a, move.c) = true →
                (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
                  move.seed = true →
                GoertzelLemma814.chainSpecifiedKempeStep
                  (frontierWordToChainWord [orient]) current target move = true →
                ∀ (ge : GoertzelLemma814.ChainEdge),
                  ge ∈ GoertzelLemma814.chainLocalEdges
                    (frontierWordToChainWord (word ++ [orient])) →
                  ge.occ = word.length →
                  GoertzelLemma814.chainIsGluedInput
                    (frontierWordToChainWord (word ++ [orient]))
                    ge.occ ge.edge = true →
                    concreteChainFiberAppendRelativeSingletonShiftedSwitchPointGoal
                      word orient pref current currentLast targetLast move ge

theorem concreteChainFiberAppendRelativeSingletonShiftedSwitchPointClosed_of_edge_cases
    (hPrefix :
      concreteChainFiberAppendRelativeSingletonShiftedSwitchPrefixPointClosed)
    (hLastNonGlued :
      concreteChainFiberAppendRelativeSingletonShiftedSwitchLastNonGluedPointClosed)
    (hLastGlued :
      concreteChainFiberAppendRelativeSingletonShiftedSwitchLastGluedPointClosed) :
    concreteChainFiberAppendRelativeSingletonShiftedSwitchPointClosed := by
  intro word orient hne hcert key hkey pref lastX hpref hlastX
    hcompatibleX hkeyLocal current target currentLast targetLast hcurrent
    htarget hcurrentEq htargetEq move hpair hseed hspecified ge hge
  have hoccLtAppend :
      ge.occ < (frontierWordToChainWord (word ++ [orient])).length :=
    GoertzelLemma814.chainLocalEdges_mem_occ_lt hge
  have happendLen :
      (frontierWordToChainWord (word ++ [orient])).length =
        word.length + 1 := by
    simp [frontierWordToChainWord]
  have hoccLtSucc : ge.occ < word.length + 1 := by
    simpa [happendLen] using hoccLtAppend
  by_cases hprefix : ge.occ < word.length
  · exact hPrefix word orient hne hcert key hkey pref lastX hpref hlastX
      hcompatibleX hkeyLocal current target currentLast targetLast hcurrent
      htarget hcurrentEq htargetEq move hpair hseed hspecified ge hge hprefix
  · have hlast : ge.occ = word.length := by
      omega
    by_cases hglued :
        GoertzelLemma814.chainIsGluedInput
          (frontierWordToChainWord (word ++ [orient])) ge.occ ge.edge = true
    · exact hLastGlued word orient hne hcert key hkey pref lastX hpref hlastX
        hcompatibleX hkeyLocal current target currentLast targetLast hcurrent
        htarget hcurrentEq htargetEq move hpair hseed hspecified ge hge hlast
        hglued
    · have hnonGlued :
          GoertzelLemma814.chainIsGluedInput
            (frontierWordToChainWord (word ++ [orient])) ge.occ ge.edge =
              false := by
        cases hcase :
            GoertzelLemma814.chainIsGluedInput
              (frontierWordToChainWord (word ++ [orient])) ge.occ ge.edge <;>
          simp_all
      exact hLastNonGlued word orient hne hcert key hkey pref lastX hpref
        hlastX hcompatibleX hkeyLocal current target currentLast targetLast
        hcurrent htarget hcurrentEq htargetEq move hpair hseed hspecified ge
        hge hlast hnonGlued

theorem concreteChainFiberAppendRelativeSingletonShiftedSwitchLastNonGluedPointClosed_of_local_specified :
    concreteChainFiberAppendRelativeSingletonShiftedSwitchLastNonGluedPointClosed := by
  intro word orient hne _hcert key _hkey pref _lastX hpref _hlastX
    _hcompatibleX _hkeyLocal current target currentLast targetLast _hcurrent
    _htarget hcurrentEq htargetEq move _hpair _hseed hspecified ge _hge hlast
    hnonGlued
  subst current
  subst target
  let component :=
    GoertzelLemma814.chainComponent
      (frontierWordToChainWord [orient]) [currentLast]
      move.a move.c move.seed
  let localGe : GoertzelLemma814.ChainEdge :=
    { occ := 0, edge := ge.edge }
  have hprefLen : pref.length = word.length := by
    have hprefRaw := hpref
    unfold concreteChainFiber GoertzelLemma814.chainFiberFrom at hprefRaw
    have hprefStates : pref ∈ concreteChainStates word :=
      (List.mem_filter.mp hprefRaw).1
    have hlen :=
      GoertzelLemma814.allChainStates_mem_length
        (orients := frontierWordToChainWord word)
        (by simpa [concreteChainStates] using hprefStates)
    simpa [frontierWordToChainWord] using hlen
  have hlocalGe :
      localGe ∈ GoertzelLemma814.chainLocalEdges
        (frontierWordToChainWord [orient]) := by
    simpa [localGe, frontierWordToChainWord] using
      (GoertzelLemma814.chainLocalEdges_mem_of_occ_edge
        (frontierWordToChainWord [orient]) 0 ge.edge
        (by simp [frontierWordToChainWord]))
  have hlocalAgree :
      GoertzelLemma814.chainAgreesWithSwitch
        (frontierWordToChainWord [orient]) [currentLast] [targetLast]
        component move.a move.c = true := by
    unfold GoertzelLemma814.chainSpecifiedKempeStep at hspecified
    simp only [Bool.and_eq_true] at hspecified
    simpa [component] using hspecified.2
  have hlocalPoint :
      GoertzelLemma814.colorEq
        (GoertzelLemma814.chainEdgeColor [targetLast] localGe)
        (GoertzelLemma814.chainSwitchedColor
          (frontierWordToChainWord [orient]) [currentLast]
          component move.a move.c localGe) = true := by
    unfold GoertzelLemma814.chainAgreesWithSwitch at hlocalAgree
    rw [List.all_eq_true] at hlocalAgree
    exact hlocalAgree localGe hlocalGe
  have hlocalCanon :
      GoertzelLemma814.chainCanonicalEdge
        (frontierWordToChainWord [orient]) localGe = localGe := by
    simp [GoertzelLemma814.chainCanonicalEdge, localGe]
  have hlocalPointRaw :
      GoertzelLemma814.colorEq
        (GoertzelLemma814.chainEdgeColor [targetLast] localGe)
        (if component.contains localGe then
          GoertzelLemma814.swapColor move.a move.c
            (GoertzelLemma814.chainEdgeColor [currentLast] localGe)
        else
          GoertzelLemma814.chainEdgeColor [currentLast] localGe) = true := by
    simpa [GoertzelLemma814.chainSwitchedColor, localGe, hlocalCanon] using
      hlocalPoint
  have hcanon :
      GoertzelLemma814.chainCanonicalEdge
        (frontierWordToChainWord (word ++ [orient])) ge = ge :=
    concreteChainFiberAppend_chainCanonicalEdge_last_non_glued
      word orient ge hne hlast hnonGlued
  have hcontains :
      (concreteChainFiberAppendShiftComponent word component).contains ge =
        component.contains localGe :=
    concreteChainFiberAppendShiftComponent_contains_last_eq
      word component ge hlast
  have hcontainsIff :
      ge ∈ concreteChainFiberAppendShiftComponent word component ↔
        localGe ∈ component := by
    constructor
    · intro hmem
      have hshiftContains :
          (concreteChainFiberAppendShiftComponent word component).contains ge =
            true :=
        List.contains_iff_mem.mpr hmem
      have hlocalContains : component.contains localGe = true := by
        rw [← hcontains]
        exact hshiftContains
      exact List.contains_iff_mem.mp hlocalContains
    · intro hmem
      have hlocalContains : component.contains localGe = true :=
        List.contains_iff_mem.mpr hmem
      have hshiftContains :
          (concreteChainFiberAppendShiftComponent word component).contains ge =
            true := by
        rw [hcontains]
        exact hlocalContains
      exact List.contains_iff_mem.mp hshiftContains
  have htargetColor :
      GoertzelLemma814.chainEdgeColor (pref ++ [targetLast]) ge =
        GoertzelLemma814.chainEdgeColor [targetLast] localGe := by
    simpa [localGe] using
      concreteChainFiberAppend_chainEdgeColor_last
        word pref targetLast ge hprefLen hlast
  have hcurrentColor :
      GoertzelLemma814.chainEdgeColor (pref ++ [currentLast]) ge =
        GoertzelLemma814.chainEdgeColor [currentLast] localGe := by
    simpa [localGe] using
      concreteChainFiberAppend_chainEdgeColor_last
        word pref currentLast ge hprefLen hlast
  unfold concreteChainFiberAppendRelativeSingletonShiftedSwitchPointGoal
  simpa [GoertzelLemma814.chainSwitchedColor, component, localGe, hcanon,
    hcontainsIff, htargetColor, hcurrentColor] using hlocalPointRaw

theorem concreteChainFiberAppendRelativeSingletonShiftedSwitchLastGluedPointClosed_of_input_trace :
    concreteChainFiberAppendRelativeSingletonShiftedSwitchLastGluedPointClosed := by
  intro word orient hne _hcert key _hkey pref lastX hpref _hlastX
    hcompatibleX _hkeyLocal current target currentLast targetLast hcurrent
    htarget hcurrentEq htargetEq move _hpair _hseed _hspecified ge _hge hlast
    hglued
  subst current
  subst target
  let localComponent :=
    GoertzelLemma814.chainComponent (frontierWordToChainWord [orient])
      [currentLast] move.a move.c move.seed
  let shiftedComponent := concreteChainFiberAppendShiftComponent word localComponent
  have hprefLen : pref.length = word.length := by
    have hprefRaw := hpref
    unfold concreteChainFiber GoertzelLemma814.chainFiberFrom at hprefRaw
    have hprefStates : pref ∈ concreteChainStates word :=
      (List.mem_filter.mp hprefRaw).1
    have hlen :=
      GoertzelLemma814.allChainStates_mem_length
        (orients := frontierWordToChainWord word)
        (by simpa [concreteChainStates] using hprefStates)
    simpa [frontierWordToChainWord] using hlen
  have hcurrentGlobal :
      pref ++ [currentLast] ∈ concreteChainFiber (word ++ [orient]) key :=
    concreteChainFiberAppend_mem_of_prefix_and_local_singleton
      word orient hne key hpref hcompatibleX hcurrent rfl
  have hcurrentStates :
      pref ++ [currentLast] ∈ concreteChainStates (word ++ [orient]) := by
    unfold concreteChainFiber GoertzelLemma814.chainFiberFrom at hcurrentGlobal
    exact (List.mem_filter.mp hcurrentGlobal).1
  have hcurrentCompatible :
      GoertzelLemma814.compatibleChainStates
        (frontierWordToChainWord (word ++ [orient]))
        (pref ++ [currentLast]) = true := by
    have hAll :=
      GoertzelLemma814.allChainStates_compatible
        (frontierWordToChainWord (word ++ [orient]))
    rw [List.all_eq_true] at hAll
    exact hAll (pref ++ [currentLast])
      (by simpa [concreteChainStates] using hcurrentStates)
  have hglobalOcc :
      ge.occ < (frontierWordToChainWord (word ++ [orient])).length := by
    rw [hlast]
    simp [frontierWordToChainWord]
  have hcanonicalColor :
      GoertzelLemma814.chainEdgeColor (pref ++ [currentLast])
          (GoertzelLemma814.chainCanonicalEdge
            (frontierWordToChainWord (word ++ [orient])) ge) =
        GoertzelLemma814.chainEdgeColor (pref ++ [currentLast]) ge :=
    GoertzelLemma814.chainEdgeColor_chainCanonicalEdge_of_compatible
      hcurrentCompatible ge hglobalOcc
  have htargetTrace :
      concreteChainFiberAppendLastInputTrace orient targetLast =
        concreteChainFiberAppendLastInputTrace orient lastX :=
    concreteChainFiber_singleton_input_trace_eq_of_mem orient
      (concreteChainFiberAppendLastInputTrace orient lastX) htarget
  have hcurrentTrace :
      concreteChainFiberAppendLastInputTrace orient currentLast =
        concreteChainFiberAppendLastInputTrace orient lastX :=
    concreteChainFiber_singleton_input_trace_eq_of_mem orient
      (concreteChainFiberAppendLastInputTrace orient lastX) hcurrent
  have htargetCurrentColor :
      GoertzelLemma814.chainEdgeColor (pref ++ [targetLast]) ge =
        GoertzelLemma814.chainEdgeColor (pref ++ [currentLast]) ge := by
    cases ge with
    | mk occ edge =>
        simp at hlast
        subst occ
        have htargetState :
            GoertzelLemma814.chainStateAt (pref ++ [targetLast]) word.length =
              targetLast :=
          GoertzelLemma814.chainStateAt_append_length pref targetLast
            word.length hprefLen
        have hcurrentState :
            GoertzelLemma814.chainStateAt (pref ++ [currentLast]) word.length =
              currentLast :=
          GoertzelLemma814.chainStateAt_append_length pref currentLast
            word.length hprefLen
        cases orient <;> cases edge <;>
          simp [GoertzelLemma814.chainIsGluedInput,
            tauOrientAt_frontierWordToChainWord_append_length,
            concreteChainFiberAppendLastInputTrace, frontierOrientToChain,
            GoertzelLemma814.tauOrientInputOrder,
            GoertzelLemma814.chainEdgeColor, GoertzelLemma814.tauStateColorAt,
            htargetState, hcurrentState] at hglued htargetTrace hcurrentTrace ⊢ <;>
          aesop
  have hlastOrient :
      GoertzelLemma814.tauOrientAt
        (frontierWordToChainWord (word ++ [orient])) word.length =
        frontierOrientToChain orient :=
    tauOrientAt_frontierWordToChainWord_append_length word orient
  have hcanonicalPrefix :
      (GoertzelLemma814.chainCanonicalEdge
        (frontierWordToChainWord (word ++ [orient])) ge).occ < word.length := by
    cases ge with
    | mk occ edge =>
        simp at hlast
        subst occ
        have hpos : word.length > 0 := by
          cases word with
          | nil =>
              exact False.elim (hne rfl)
          | cons _ _ =>
              simp
        have hinputAt :
            (GoertzelLemma814.tauOrientInputOrder
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient]))
                word.length)).contains edge = true := by
          unfold GoertzelLemma814.chainIsGluedInput at hglued
          simpa [hpos] using hglued
        have hinput :
            (GoertzelLemma814.tauOrientInputOrder
              (frontierOrientToChain orient)).contains edge = true := by
          simpa [hlastOrient] using hinputAt
        unfold GoertzelLemma814.chainCanonicalEdge
        cases orient <;> cases edge <;>
          simp [hpos, hlastOrient, frontierOrientToChain,
            GoertzelLemma814.tauOrientInputOrder,
            GoertzelLemma814.indexOf?, GoertzelLemma814.indexOfAux] at hinput ⊢ <;>
          omega
  have hcontainsFalse :
      shiftedComponent.contains
          (GoertzelLemma814.chainCanonicalEdge
            (frontierWordToChainWord (word ++ [orient])) ge) = false := by
    exact concreteChainFiberAppendShiftComponent_contains_prefix_false
      word localComponent
      (GoertzelLemma814.chainCanonicalEdge
        (frontierWordToChainWord (word ++ [orient])) ge)
      hcanonicalPrefix
  have hcontainsFalseRaw :
      (concreteChainFiberAppendShiftComponent word
          (GoertzelLemma814.chainComponent (frontierWordToChainWord [orient])
            [currentLast] move.a move.c move.seed)).contains
          (GoertzelLemma814.chainCanonicalEdge
            (frontierWordToChainWord (word ++ [orient])) ge) = false := by
    simpa [shiftedComponent, localComponent] using hcontainsFalse
  have hcanonicalNotMemRaw :
      GoertzelLemma814.chainCanonicalEdge
          (frontierWordToChainWord (word ++ [orient])) ge ∉
        concreteChainFiberAppendShiftComponent word
          (GoertzelLemma814.chainComponent (frontierWordToChainWord [orient])
            [currentLast] move.a move.c move.seed) := by
    intro hmem
    have hcontainsTrue :
        (concreteChainFiberAppendShiftComponent word
            (GoertzelLemma814.chainComponent (frontierWordToChainWord [orient])
              [currentLast] move.a move.c move.seed)).contains
            (GoertzelLemma814.chainCanonicalEdge
              (frontierWordToChainWord (word ++ [orient])) ge) = true :=
      List.contains_iff_mem.mpr hmem
    rw [hcontainsFalseRaw] at hcontainsTrue
    cases hcontainsTrue
  have hswitch :
      GoertzelLemma814.chainSwitchedColor
          (frontierWordToChainWord (word ++ [orient]))
          (pref ++ [currentLast])
          (concreteChainFiberAppendShiftComponent word
            (GoertzelLemma814.chainComponent (frontierWordToChainWord [orient])
              [currentLast] move.a move.c move.seed))
          move.a move.c ge =
        GoertzelLemma814.chainEdgeColor (pref ++ [currentLast])
          (GoertzelLemma814.chainCanonicalEdge
            (frontierWordToChainWord (word ++ [orient])) ge) := by
    simp [GoertzelLemma814.chainSwitchedColor, hcanonicalNotMemRaw]
  unfold concreteChainFiberAppendRelativeSingletonShiftedSwitchPointGoal
  simp [hswitch, hcanonicalColor, htargetCurrentColor,
    GoertzelLemma814.colorEq]

theorem concreteChainFiberAppendRelativeSingletonShiftedSwitchPointClosed_of_prefix_and_glued
    (hPrefix :
      concreteChainFiberAppendRelativeSingletonShiftedSwitchPrefixPointClosed)
    (hLastGlued :
      concreteChainFiberAppendRelativeSingletonShiftedSwitchLastGluedPointClosed) :
    concreteChainFiberAppendRelativeSingletonShiftedSwitchPointClosed :=
  concreteChainFiberAppendRelativeSingletonShiftedSwitchPointClosed_of_edge_cases
    hPrefix
    concreteChainFiberAppendRelativeSingletonShiftedSwitchLastNonGluedPointClosed_of_local_specified
    hLastGlued

theorem concreteChainFiberAppendRelativeSingletonShiftedSwitchPointClosed_of_compatible_prefix_and_glued
    (hLastGlued :
      concreteChainFiberAppendRelativeSingletonShiftedSwitchLastGluedPointClosed) :
    concreteChainFiberAppendRelativeSingletonShiftedSwitchPointClosed :=
  concreteChainFiberAppendRelativeSingletonShiftedSwitchPointClosed_of_prefix_and_glued
    concreteChainFiberAppendRelativeSingletonShiftedSwitchPrefixPointClosed_of_compatible_prefix
    hLastGlued

theorem concreteChainFiberAppendRelativeSingletonShiftedSwitchAgreementClosed_of_pointwise
    (hPoint :
      concreteChainFiberAppendRelativeSingletonShiftedSwitchPointClosed) :
    concreteChainFiberAppendRelativeSingletonShiftedSwitchAgreementClosed := by
  intro word orient hne hcert key hkey pref lastX hpref hlastX
    hcompatibleX hkeyLocal current target currentLast targetLast hcurrent
    htarget hcurrentEq htargetEq move hpair hseed hspecified
  unfold GoertzelLemma814.chainAgreesWithSwitch
  rw [List.all_eq_true]
  intro ge hge
  exact hPoint word orient hne hcert key hkey pref lastX hpref hlastX
    hcompatibleX hkeyLocal current target currentLast targetLast hcurrent
    htarget hcurrentEq htargetEq move hpair hseed hspecified ge hge

theorem concreteChainFiberAppendRelativeSingletonShiftedSwitchAgreementClosed_of_prefix_and_glued
    (hPrefix :
      concreteChainFiberAppendRelativeSingletonShiftedSwitchPrefixPointClosed)
    (hLastGlued :
      concreteChainFiberAppendRelativeSingletonShiftedSwitchLastGluedPointClosed) :
    concreteChainFiberAppendRelativeSingletonShiftedSwitchAgreementClosed :=
  concreteChainFiberAppendRelativeSingletonShiftedSwitchAgreementClosed_of_pointwise
    (concreteChainFiberAppendRelativeSingletonShiftedSwitchPointClosed_of_prefix_and_glued
      hPrefix hLastGlued)

theorem concreteChainFiberAppendRelativeSingletonShiftedSwitchAgreementClosed_of_compatible_prefix_and_glued
    (hLastGlued :
      concreteChainFiberAppendRelativeSingletonShiftedSwitchLastGluedPointClosed) :
    concreteChainFiberAppendRelativeSingletonShiftedSwitchAgreementClosed :=
  concreteChainFiberAppendRelativeSingletonShiftedSwitchAgreementClosed_of_pointwise
    (concreteChainFiberAppendRelativeSingletonShiftedSwitchPointClosed_of_compatible_prefix_and_glued
      hLastGlued)

def concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX : GoertzelLemma814.TauState),
            (_hpref : pref ∈ concreteChainFiber word key) →
            (_hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (_hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            ∀ (_hkeyLocal :
                concreteChainFiberAppendLastInputTrace orient lastX ∈
                  GoertzelLemma814.colorAssignments4)
              (current target : List GoertzelLemma814.TauState)
              (currentLast targetLast : GoertzelLemma814.TauState),
              current ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              target ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              current = [currentLast] →
              target = [targetLast] →
              ∀ (move : GoertzelLemma814.ChainMove),
                GoertzelLemma814.colorPairs.contains (move.a, move.c) = true →
                (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
                  move.seed = true →
                GoertzelLemma814.chainSpecifiedKempeStep
                  (frontierWordToChainWord [orient]) current target move = true →
                GoertzelLemma814.chainSpecifiedKempeStep
                  (frontierWordToChainWord (word ++ [orient]))
                  (pref ++ [currentLast]) (pref ++ [targetLast])
                  (concreteChainFiberAppendShiftMove word move) = true

theorem concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed_of_component_and_switch
    (hComponent :
      concreteChainFiberAppendRelativeSingletonShiftedComponentClosed)
    (hSwitch :
      concreteChainFiberAppendRelativeSingletonShiftedSwitchAgreementClosed) :
    concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed := by
  intro word orient hne hcert key hkey pref lastX hpref hlastX
    hcompatibleX hkeyLocal current target currentLast targetLast hcurrent
    htarget hcurrentEq htargetEq move hpair hseed hspecified
  let localComponent :=
    GoertzelLemma814.chainComponent (frontierWordToChainWord [orient])
      current move.a move.c move.seed
  let shiftedComponent :=
    concreteChainFiberAppendShiftComponent word localComponent
  let globalComponent :=
    GoertzelLemma814.chainComponent
      (frontierWordToChainWord (word ++ [orient]))
      (pref ++ [currentLast]) move.a move.c
      (concreteChainFiberAppendShiftMove word move).seed
  have hspecifiedParts := hspecified
  unfold GoertzelLemma814.chainSpecifiedKempeStep at hspecifiedParts
  change (!localComponent.isEmpty &&
      GoertzelLemma814.chainComponentAvoidsInputs
        (frontierWordToChainWord [orient]) localComponent &&
      GoertzelLemma814.chainAgreesWithSwitch
        (frontierWordToChainWord [orient]) current target localComponent
        move.a move.c) = true at hspecifiedParts
  simp only [Bool.and_eq_true] at hspecifiedParts
  rcases hspecifiedParts with ⟨⟨hLocalNonempty, _hLocalAvoid⟩, _hLocalAgree⟩
  have hComponentEq : globalComponent = shiftedComponent := by
    exact hComponent word orient hne hcert key hkey pref lastX hpref hlastX
      hcompatibleX hkeyLocal current target currentLast targetLast hcurrent
      htarget hcurrentEq htargetEq move hpair hseed hspecified
  have hGlobalNonempty : (!globalComponent.isEmpty) = true := by
    rw [hComponentEq]
    simpa [shiftedComponent, concreteChainFiberAppendShiftComponent,
      localComponent] using hLocalNonempty
  have hGlobalAvoid :
      GoertzelLemma814.chainComponentAvoidsInputs
        (frontierWordToChainWord (word ++ [orient])) globalComponent = true := by
    rw [hComponentEq]
    exact concreteChainFiberAppendShiftComponent_avoids_inputs
      word orient localComponent hne
  have hGlobalAgreeShifted :
      GoertzelLemma814.chainAgreesWithSwitch
        (frontierWordToChainWord (word ++ [orient]))
        (pref ++ [currentLast]) (pref ++ [targetLast]) shiftedComponent
        move.a move.c = true := by
    simpa [shiftedComponent, localComponent] using
      hSwitch word orient hne hcert key hkey pref lastX hpref hlastX
        hcompatibleX hkeyLocal current target currentLast targetLast hcurrent
        htarget hcurrentEq htargetEq move hpair hseed hspecified
  have hGlobalAgree :
      GoertzelLemma814.chainAgreesWithSwitch
        (frontierWordToChainWord (word ++ [orient]))
        (pref ++ [currentLast]) (pref ++ [targetLast]) globalComponent
        move.a move.c = true := by
    rw [hComponentEq]
    exact hGlobalAgreeShifted
  unfold GoertzelLemma814.chainSpecifiedKempeStep
  change (!globalComponent.isEmpty &&
      GoertzelLemma814.chainComponentAvoidsInputs
        (frontierWordToChainWord (word ++ [orient])) globalComponent &&
      GoertzelLemma814.chainAgreesWithSwitch
        (frontierWordToChainWord (word ++ [orient]))
        (pref ++ [currentLast]) (pref ++ [targetLast]) globalComponent
        move.a move.c) = true
  simp [hGlobalNonempty, hGlobalAvoid, hGlobalAgree]

theorem concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed_of_component_prefix_and_glued
    (hComponent :
      concreteChainFiberAppendRelativeSingletonShiftedComponentClosed)
    (hPrefix :
      concreteChainFiberAppendRelativeSingletonShiftedSwitchPrefixPointClosed)
    (hLastGlued :
      concreteChainFiberAppendRelativeSingletonShiftedSwitchLastGluedPointClosed) :
    concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed :=
  concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed_of_component_and_switch
    hComponent
    (concreteChainFiberAppendRelativeSingletonShiftedSwitchAgreementClosed_of_prefix_and_glued
      hPrefix hLastGlued)

theorem concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed_of_component_and_glued
    (hComponent :
      concreteChainFiberAppendRelativeSingletonShiftedComponentClosed)
    (hLastGlued :
      concreteChainFiberAppendRelativeSingletonShiftedSwitchLastGluedPointClosed) :
    concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed :=
  concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed_of_component_and_switch
    hComponent
    (concreteChainFiberAppendRelativeSingletonShiftedSwitchAgreementClosed_of_compatible_prefix_and_glued
      hLastGlued)

def concreteChainFiberAppendRelativeSingletonShiftedSpecifiedKempeStepClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX : GoertzelLemma814.TauState),
            (_hpref : pref ∈ concreteChainFiber word key) →
            (_hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (_hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            ∀ (_hkeyLocal :
                concreteChainFiberAppendLastInputTrace orient lastX ∈
                  GoertzelLemma814.colorAssignments4)
              (current target : List GoertzelLemma814.TauState)
              (currentLast targetLast : GoertzelLemma814.TauState),
              current ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              target ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              current = [currentLast] →
              target = [targetLast] →
              ∀ (move : GoertzelLemma814.ChainMove),
                GoertzelLemma814.colorPairs.contains (move.a, move.c) = true →
                (GoertzelLemma814.chainEdges (frontierWordToChainWord [orient])).contains
                  move.seed = true →
                GoertzelLemma814.chainSpecifiedKempeStep
                  (frontierWordToChainWord [orient]) current target move = true →
                (GoertzelLemma814.chainEdges
                  (frontierWordToChainWord (word ++ [orient]))).contains
                    (concreteChainFiberAppendShiftMove word move).seed = true ∧
                GoertzelLemma814.chainSpecifiedKempeStep
                  (frontierWordToChainWord (word ++ [orient]))
                  (pref ++ [currentLast]) (pref ++ [targetLast])
                  (concreteChainFiberAppendShiftMove word move) = true

theorem concreteChainFiberAppendRelativeSingletonShiftedSpecifiedKempeStepClosed_of_seed_and_step
    (hSeed :
      concreteChainFiberAppendRelativeSingletonShiftedSeedPresentClosed)
    (hStep :
      concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed) :
    concreteChainFiberAppendRelativeSingletonShiftedSpecifiedKempeStepClosed := by
  intro word orient hne hcert key hkey pref lastX hpref hlastX
    hcompatibleX hkeyLocal current target currentLast targetLast hcurrent
    htarget hcurrentEq htargetEq move hpair hseed hspecified
  exact
    ⟨hSeed word orient hne hcert key hkey pref lastX hpref hlastX
        hcompatibleX hkeyLocal current target currentLast targetLast hcurrent
        htarget hcurrentEq htargetEq move hpair hseed hspecified,
      hStep word orient hne hcert key hkey pref lastX hpref hlastX
        hcompatibleX hkeyLocal current target currentLast targetLast hcurrent
        htarget hcurrentEq htargetEq move hpair hseed hspecified⟩

theorem concreteChainFiberAppendRelativeSingletonShiftedSpecifiedKempeStepClosed_of_shifted_step
    (hStep :
      concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed) :
    concreteChainFiberAppendRelativeSingletonShiftedSpecifiedKempeStepClosed :=
  concreteChainFiberAppendRelativeSingletonShiftedSpecifiedKempeStepClosed_of_seed_and_step
    concreteChainFiberAppendRelativeSingletonShiftedSeedPresentClosed_of_local_specified
    hStep

theorem concreteChainFiberAppendRelativeSingletonSpecifiedKempeStepLiftClosed_of_shifted
    (hShift :
      concreteChainFiberAppendRelativeSingletonShiftedSpecifiedKempeStepClosed) :
    concreteChainFiberAppendRelativeSingletonSpecifiedKempeStepLiftClosed := by
  intro word orient hne hcert key hkey pref lastX hpref hlastX hcompatibleX
    hkeyLocal current target currentLast targetLast hcurrent htarget
    hcurrentEq htargetEq move hpair hseed hspecified
  rcases hShift word orient hne hcert key hkey pref lastX hpref hlastX
      hcompatibleX hkeyLocal current target currentLast targetLast hcurrent
      htarget hcurrentEq htargetEq move hpair hseed hspecified with
    ⟨hglobalSeed, hglobalSpecified⟩
  exact GoertzelLemma814.chainSpecifiedKempeStep_implies_single
    (frontierWordToChainWord (word ++ [orient]))
    (pref ++ [currentLast]) (pref ++ [targetLast])
    (concreteChainFiberAppendShiftMove word move)
    hpair hglobalSeed hglobalSpecified

theorem concreteChainFiberAppendRelativeSingletonSpecifiedKempeStepLiftClosed_of_shifted_step
    (hStep :
      concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed) :
    concreteChainFiberAppendRelativeSingletonSpecifiedKempeStepLiftClosed :=
  concreteChainFiberAppendRelativeSingletonSpecifiedKempeStepLiftClosed_of_shifted
    (concreteChainFiberAppendRelativeSingletonShiftedSpecifiedKempeStepClosed_of_shifted_step
      hStep)

theorem concreteChainFiberAppendRelativeSingletonSpecifiedKempeStepLiftClosed_of_component_and_glued
    (hComponent :
      concreteChainFiberAppendRelativeSingletonShiftedComponentClosed)
    (hLastGlued :
      concreteChainFiberAppendRelativeSingletonShiftedSwitchLastGluedPointClosed) :
    concreteChainFiberAppendRelativeSingletonSpecifiedKempeStepLiftClosed :=
  concreteChainFiberAppendRelativeSingletonSpecifiedKempeStepLiftClosed_of_shifted_step
    (concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed_of_component_and_glued
      hComponent hLastGlued)

theorem concreteChainFiberAppendRelativeSingletonGlobalKempeStepLiftClosed_of_specified_step
    (hSpecified :
      concreteChainFiberAppendRelativeSingletonSpecifiedKempeStepLiftClosed) :
    concreteChainFiberAppendRelativeSingletonGlobalKempeStepLiftClosed := by
  intro word orient hne hcert key hkey pref lastX hpref hlastX hcompatibleX
    hkeyLocal current target currentLast targetLast hcurrent htarget
    hcurrentEq htargetEq hlocalStep
  unfold GoertzelLemma814.chainSingleKempeStep at hlocalStep
  rw [List.any_eq_true] at hlocalStep
  rcases hlocalStep with ⟨pair, hpairMem, hseedAny⟩
  rw [List.any_eq_true] at hseedAny
  rcases hseedAny with ⟨seed, hseedMem, hspecified⟩
  let move : GoertzelLemma814.ChainMove :=
    { a := pair.1, c := pair.2, seed := seed }
  exact hSpecified word orient hne hcert key hkey pref lastX hpref hlastX
    hcompatibleX hkeyLocal current target currentLast targetLast hcurrent
    htarget hcurrentEq htargetEq move
    (List.contains_iff_mem.mpr hpairMem)
    (List.contains_iff_mem.mpr hseedMem)
    (by simpa [move, GoertzelLemma814.chainSpecifiedKempeStep] using hspecified)

theorem concreteChainFiberAppendRelativeSingletonGlobalKempeStepLiftClosed_of_shifted_step
    (hStep :
      concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed) :
    concreteChainFiberAppendRelativeSingletonGlobalKempeStepLiftClosed :=
  concreteChainFiberAppendRelativeSingletonGlobalKempeStepLiftClosed_of_specified_step
    (concreteChainFiberAppendRelativeSingletonSpecifiedKempeStepLiftClosed_of_shifted_step
      hStep)

theorem concreteChainFiberAppendRelativeSingletonGlobalKempeStepLiftClosed_of_component_and_glued
    (hComponent :
      concreteChainFiberAppendRelativeSingletonShiftedComponentClosed)
    (hLastGlued :
      concreteChainFiberAppendRelativeSingletonShiftedSwitchLastGluedPointClosed) :
    concreteChainFiberAppendRelativeSingletonGlobalKempeStepLiftClosed :=
  concreteChainFiberAppendRelativeSingletonGlobalKempeStepLiftClosed_of_shifted_step
    (concreteChainFiberAppendRelativeSingletonShiftedSpecifiedStepClosed_of_component_and_glued
      hComponent hLastGlued)

def concreteChainFiberAppendRelativeSingletonGlobalStepClosureClosed : Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient)
    (_hne : word ≠ []),
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ (key : List GoertzelLemma814.LColor),
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ (pref : List GoertzelLemma814.TauState)
            (lastX : GoertzelLemma814.TauState),
            (_hpref : pref ∈ concreteChainFiber word key) →
            (_hlastX : lastX ∈ GoertzelLemma814.allTauStates) →
            (_hcompatibleX : GoertzelLemma814.compatibleAdjacent
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
              (GoertzelLemma814.tauOrientAt
                (frontierWordToChainWord (word ++ [orient])) word.length)
              (GoertzelLemma814.chainStateAt pref (word.length - 1))
              lastX = true) →
            ∀ (_hkeyLocal :
                concreteChainFiberAppendLastInputTrace orient lastX ∈
                  GoertzelLemma814.colorAssignments4)
              (current target : List GoertzelLemma814.TauState)
              (currentLast targetLast : GoertzelLemma814.TauState),
              current ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              target ∈ concreteChainFiber [orient]
                (concreteChainFiberAppendLastInputTrace orient lastX) →
              current = [currentLast] →
              target = [targetLast] →
              pref ++ [targetLast] ∈ concreteChainFiber
                (word ++ [orient]) key →
              pref ++ [currentLast] ∈ GoertzelLemma814.closeChainFiber
                (frontierWordToChainWord (word ++ [orient]))
                (concreteChainFiber (word ++ [orient]) key)
                (concreteChainFiber (word ++ [orient]) key).length
                [chainFiberRootState (word ++ [orient]) key] →
              GoertzelLemma814.chainSingleKempeStep
                (frontierWordToChainWord (word ++ [orient]))
                (pref ++ [currentLast]) (pref ++ [targetLast]) = true →
              pref ++ [targetLast] ∈ GoertzelLemma814.closeChainFiber
                (frontierWordToChainWord (word ++ [orient]))
                (concreteChainFiber (word ++ [orient]) key)
                (concreteChainFiber (word ++ [orient]) key).length
                [chainFiberRootState (word ++ [orient]) key]

theorem concreteChainFiberAppendRelativeSingletonClosureStepLiftClosed_of_global_step
    (hKempe :
      concreteChainFiberAppendRelativeSingletonGlobalKempeStepLiftClosed)
    (hClosure :
      concreteChainFiberAppendRelativeSingletonGlobalStepClosureClosed) :
    concreteChainFiberAppendRelativeSingletonClosureStepLiftClosed := by
  intro word orient hne hcert key hkey pref lastX hpref hlastX
    hcompatibleX hkeyLocal current target currentLast targetLast hcurrent
    htarget hcurrentEq htargetEq hcurrentClose hlocalStep
  have htargetGlobal :
      pref ++ [targetLast] ∈ concreteChainFiber (word ++ [orient]) key :=
    concreteChainFiberAppend_mem_of_prefix_and_local_singleton
      word orient hne key hpref hcompatibleX htarget htargetEq
  have hglobalStep :
      GoertzelLemma814.chainSingleKempeStep
        (frontierWordToChainWord (word ++ [orient]))
        (pref ++ [currentLast]) (pref ++ [targetLast]) = true :=
    hKempe word orient hne hcert key hkey pref lastX hpref hlastX
      hcompatibleX hkeyLocal current target currentLast targetLast hcurrent
      htarget hcurrentEq htargetEq hlocalStep
  exact hClosure word orient hne hcert key hkey pref lastX hpref hlastX
    hcompatibleX hkeyLocal current target currentLast targetLast hcurrent
    htarget hcurrentEq htargetEq htargetGlobal hcurrentClose hglobalStep

theorem concreteChainFiberAppendRelativeSingletonGlobalStepClosureClosed_of_bounded_saturation
    (hSat : GoertzelLemma814.closeChainFiberBoundedSaturationClosed) :
    concreteChainFiberAppendRelativeSingletonGlobalStepClosureClosed := by
  intro word orient _hne _hcert key _hkey pref _lastX _hpref _hlastX
    _hcompatibleX _hkeyLocal current target currentLast targetLast _hcurrent
    _htarget _hcurrentEq _htargetEq htargetGlobal hcurrentClose hglobalStep
  exact
    GoertzelLemma814.closeChainFiber_mem_step_of_close_at_length_of_bounded_saturation
      hSat
      (frontierWordToChainWord (word ++ [orient]))
      (concreteChainFiber (word ++ [orient]) key)
      [chainFiberRootState (word ++ [orient]) key]
      (pref ++ [currentLast]) (pref ++ [targetLast])
      (by simp) hcurrentClose htargetGlobal hglobalStep

theorem concreteChainFiberAppendRelativeSingletonClosureLiftClosed_of_root_and_step_lift
    (hRoot :
      concreteChainFiberAppendRelativeSingletonClosureRootLiftClosed)
    (hStep :
      concreteChainFiberAppendRelativeSingletonClosureStepLiftClosed) :
    concreteChainFiberAppendRelativeSingletonClosureLiftClosed := by
  intro word orient hne hcert key hkey pref lastX lastY hpref hlastX _hlastY
    hcompatibleX _hcompatibleY hkeyLocal yLocal hyLocal hyCloseLocal
  let localKey := concreteChainFiberAppendLastInputTrace orient lastX
  let localFiber := concreteChainFiber [orient] localKey
  let globalClose : List GoertzelLemma814.TauState → Prop := fun states =>
    states ∈ GoertzelLemma814.closeChainFiber
      (frontierWordToChainWord (word ++ [orient]))
      (concreteChainFiber (word ++ [orient]) key)
      (concreteChainFiber (word ++ [orient]) key).length
      [chainFiberRootState (word ++ [orient]) key]
  let P : List GoertzelLemma814.TauState → Prop := fun states =>
    states ∈ localFiber ∧
      ∃ last : GoertzelLemma814.TauState,
        states = [last] ∧ globalClose (pref ++ [last])
  have hlastXLocal : [lastX] ∈ localFiber := by
    simpa [localFiber, localKey] using
      concreteChainFiber_singleton_mem_of_last_input_trace orient hlastX
  have hrootMem :
      chainFiberRootState [orient] localKey ∈ localFiber := by
    cases hfiber : localFiber with
    | nil =>
        have hfalse : [lastX] ∈ ([] : List (List GoertzelLemma814.TauState)) := by
          simp [localFiber, hfiber] at hlastXLocal
        cases hfalse
    | cons root rest =>
        simp [chainFiberRootState, localFiber, hfiber,
          GoertzelLemma814.listGetD]
  have hrootLift :=
    hRoot word orient hne hcert key hkey pref lastX hpref hlastX
      hcompatibleX (by simpa [localKey] using hkeyLocal)
  have hseen : ∀ states,
      states ∈ [chainFiberRootState [orient] localKey] → P states := by
    intro states hstates
    simp only [List.mem_singleton] at hstates
    subst states
    rcases hrootLift with ⟨rootLast, hrootEq, hrootClose⟩
    exact ⟨hrootMem, rootLast, hrootEq, by simpa [globalClose] using hrootClose⟩
  have hstep : ∀ current target,
      P current →
      target ∈ localFiber →
      GoertzelLemma814.chainSingleKempeStep
        (frontierWordToChainWord [orient]) current target = true →
      P target := by
    intro current target hcurrent htarget hsingle
    rcases hcurrent with
      ⟨hcurrentMem, currentLast, hcurrentEq, hcurrentClose⟩
    rcases concreteChainFiber_singleton_of_mem orient localKey
        (by simpa [localFiber] using htarget) with
      ⟨targetLast, htargetEq⟩
    refine ⟨htarget, targetLast, htargetEq, ?_⟩
    exact hStep word orient hne hcert key hkey pref lastX hpref hlastX
      hcompatibleX (by simpa [localKey] using hkeyLocal)
      current target currentLast targetLast
      (by simpa [localFiber] using hcurrentMem)
      (by simpa [localFiber] using htarget)
      hcurrentEq htargetEq (by simpa [globalClose] using hcurrentClose)
      hsingle
  have hyLift := GoertzelLemma814.closeChainFiber_lift_property
    (frontierWordToChainWord [orient]) localFiber localFiber.length
    [chainFiberRootState [orient] localKey] P hseen hstep yLocal.1
    (by simpa [localFiber, localKey] using hyCloseLocal)
  rcases hyLift with ⟨_hyMem, targetLast, htargetEq, htargetClose⟩
  have hlastEq : targetLast = lastY := by
    have hsingle :
        ([targetLast] : List GoertzelLemma814.TauState) = [lastY] := by
      rw [← htargetEq, hyLocal]
    simpa using hsingle
  simpa [globalClose, hlastEq] using htargetClose

theorem concreteChainFiberAppendFixedPrefixSameInterfaceTraceReachClosed_of_relative_singleton
    (hRelative :
      concreteChainFiberAppendSameTraceRelativeSingletonReachClosed)
    (hLift : concreteChainFiberAppendRelativeSingletonLiftClosed) :
    concreteChainFiberAppendFixedPrefixSameInterfaceTraceReachClosed := by
  intro word orient hne hcert key hkey pref lastX lastY hpref hlastX hlastY
    hcompatibleX hcompatibleY htrace
  rcases hRelative word orient hne hcert key hkey pref lastX lastY
      hpref hlastX hlastY hcompatibleX hcompatibleY htrace with
    ⟨hkeyLocal, xLocal, yLocal, hxLocal, hyLocal, hreachLocal⟩
  exact hLift word orient hne hcert key hkey pref lastX lastY
    hpref hlastX hlastY hcompatibleX hcompatibleY hkeyLocal xLocal yLocal
    hxLocal hyLocal hreachLocal

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

def ChainFiberFibrationCertificate.ofAppendQuotientLift
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {orient : GoertzelLemma818FrontierMode.TauOrient}
    {key : List GoertzelLemma814.LColor}
    (lift : ChainFiberAppendQuotientFibrationLift word orient key) :
    ChainFiberFibrationCertificate (word ++ [orient]) key :=
  { Base := lift.Base
    baseStep := lift.baseStep
    proj := lift.proj
    fibration := lift.fibration
    baseConnected := lift.baseConnected }

theorem concreteChainFiberFibrationNonemptyTransferClosed_of_append_lift
    (hLift : concreteChainFiberAppendFibrationLiftClosed) :
    concreteChainFiberFibrationNonemptyTransferClosed := by
  intro word orient hne hcert key hkey
  rcases hcert with ⟨wordCert⟩
  rcases wordCert.fiberCertificate key hkey with ⟨prefixCert⟩
  rcases hLift word orient hne ⟨wordCert⟩ key hkey with ⟨lift⟩
  exact ⟨ChainFiberFibrationCertificate.ofAppendLift prefixCert lift⟩

theorem concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_fibration
    (hLift : concreteChainFiberAppendQuotientFibrationClosed) :
    concreteChainFiberFibrationNonemptyTransferClosed := by
  intro word orient hne hcert key hkey
  rcases hLift word orient hne hcert key hkey with ⟨lift⟩
  exact ⟨ChainFiberFibrationCertificate.ofAppendQuotientLift lift⟩

theorem concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_fields
    (hFields : concreteChainFiberAppendQuotientFibrationFieldsClosed) :
    concreteChainFiberFibrationNonemptyTransferClosed :=
  concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_fibration
    (concreteChainFiberAppendQuotientFibrationClosed_of_fields hFields)

theorem concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_root_fields
    (hFields : concreteChainFiberAppendQuotientFibrationRootFieldsClosed) :
    concreteChainFiberFibrationNonemptyTransferClosed :=
  concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_fields
    (concreteChainFiberAppendQuotientFibrationFieldsClosed_of_root_fields
      hFields)

theorem concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_symmetric_root
    (hFields :
      concreteChainFiberAppendQuotientFibrationSymmetricRootFieldsClosed) :
    concreteChainFiberFibrationNonemptyTransferClosed :=
  concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_root_fields
    (concreteChainFiberAppendQuotientFibrationRootFieldsClosed_of_symmetric
      hFields)

theorem concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_listed_symmetric_root
    (hFields :
      concreteChainFiberAppendQuotientFibrationListedSymmetricRootFieldsClosed) :
    concreteChainFiberFibrationNonemptyTransferClosed :=
  concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_symmetric_root
    (concreteChainFiberAppendQuotientFibrationSymmetricRootFieldsClosed_of_listed
      hFields)

theorem concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_parent_map
    (hFields :
      concreteChainFiberAppendQuotientFibrationParentMapFieldsClosed) :
    concreteChainFiberFibrationNonemptyTransferClosed :=
  concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_listed_symmetric_root
    (concreteChainFiberAppendQuotientFibrationListedSymmetricRootFieldsClosed_of_parent_map
      hFields)

theorem concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_parent_rows
    (hFields :
      concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed) :
    concreteChainFiberFibrationNonemptyTransferClosed :=
  concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_parent_map
    (concreteChainFiberAppendQuotientFibrationParentMapFieldsClosed_of_parent_rows
      hFields)

theorem concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_path_rows
    (hFields :
      concreteChainFiberAppendQuotientFibrationPathRowsFieldsClosed) :
    concreteChainFiberFibrationNonemptyTransferClosed :=
  concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_parent_rows
    (concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_path_rows
      hFields)

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

theorem concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_fibration
    (hLift : concreteChainFiberAppendQuotientFibrationClosed) :
    concreteChainAuditFibrationNonemptyTransferClosed :=
  concreteChainAuditFibrationNonemptyTransferClosed_of_append_components
    concreteChainStatesGeneratedCompatible_ok
    (concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_fibration
      hLift)

theorem concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_fields
    (hFields : concreteChainFiberAppendQuotientFibrationFieldsClosed) :
    concreteChainAuditFibrationNonemptyTransferClosed :=
  concreteChainAuditFibrationNonemptyTransferClosed_of_append_components
    concreteChainStatesGeneratedCompatible_ok
    (concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_fields
      hFields)

theorem concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_root_fields
    (hFields : concreteChainFiberAppendQuotientFibrationRootFieldsClosed) :
    concreteChainAuditFibrationNonemptyTransferClosed :=
  concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_fields
    (concreteChainFiberAppendQuotientFibrationFieldsClosed_of_root_fields
      hFields)

theorem concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_symmetric_root
    (hFields :
      concreteChainFiberAppendQuotientFibrationSymmetricRootFieldsClosed) :
    concreteChainAuditFibrationNonemptyTransferClosed :=
  concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_root_fields
    (concreteChainFiberAppendQuotientFibrationRootFieldsClosed_of_symmetric
      hFields)

theorem concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_listed_symmetric_root
    (hFields :
      concreteChainFiberAppendQuotientFibrationListedSymmetricRootFieldsClosed) :
    concreteChainAuditFibrationNonemptyTransferClosed :=
  concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_symmetric_root
    (concreteChainFiberAppendQuotientFibrationSymmetricRootFieldsClosed_of_listed
      hFields)

theorem concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_parent_map
    (hFields :
      concreteChainFiberAppendQuotientFibrationParentMapFieldsClosed) :
    concreteChainAuditFibrationNonemptyTransferClosed :=
  concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_listed_symmetric_root
    (concreteChainFiberAppendQuotientFibrationListedSymmetricRootFieldsClosed_of_parent_map
      hFields)

theorem concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_parent_rows
    (hFields :
      concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed) :
    concreteChainAuditFibrationNonemptyTransferClosed :=
  concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_parent_map
    (concreteChainFiberAppendQuotientFibrationParentMapFieldsClosed_of_parent_rows
      hFields)

theorem concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_path_rows
    (hFields :
      concreteChainFiberAppendQuotientFibrationPathRowsFieldsClosed) :
    concreteChainAuditFibrationNonemptyTransferClosed :=
  concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_parent_rows
    (concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_path_rows
      hFields)

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

theorem frontierWordToChainWord_baseCertifiedFrontierWord_eq
    (w : BaseCertifiedWord) :
    frontierWordToChainWord (baseCertifiedFrontierWord w) =
      baseCertifiedChainWord w := by
  cases w <;> rfl

theorem chainAuditForBaseCertifiedFrontierWord_ok
    (w : BaseCertifiedWord) :
    chainAuditForFrontierWord (baseCertifiedFrontierWord w) = true := by
  cases w
  · simpa [chainAuditForFrontierWord, frontierWordToChainWord,
      frontierOrientToChain, baseCertifiedFrontierWord,
      baseCertifiedChainCertificateAudit] using
      baseCertifiedChainCertificateAudit_ok BaseCertifiedWord.t
  · simpa [chainAuditForFrontierWord, frontierWordToChainWord,
      frontierOrientToChain, baseCertifiedFrontierWord,
      baseCertifiedChainCertificateAudit] using
      baseCertifiedChainCertificateAudit_ok BaseCertifiedWord.m
  · simpa [chainAuditForFrontierWord, frontierWordToChainWord,
      frontierOrientToChain, baseCertifiedFrontierWord,
      baseCertifiedChainCertificateAudit,
      GoertzelLemma818LengthTwoBase.lengthTwoOrientWord,
      GoertzelLemma818CompositeCertificate.ttWord] using
      baseCertifiedChainCertificateAudit_ok BaseCertifiedWord.tt
  · simpa [chainAuditForFrontierWord, frontierWordToChainWord,
      frontierOrientToChain, baseCertifiedFrontierWord,
      baseCertifiedChainCertificateAudit,
      GoertzelLemma818LengthTwoBase.lengthTwoOrientWord,
      GoertzelLemma818TauMirrorCertificate.tmWord] using
      baseCertifiedChainCertificateAudit_ok BaseCertifiedWord.tm
  · simpa [chainAuditForFrontierWord, frontierWordToChainWord,
      frontierOrientToChain, baseCertifiedFrontierWord,
      baseCertifiedChainCertificateAudit,
      GoertzelLemma818LengthTwoBase.lengthTwoOrientWord,
      GoertzelLemma818MirrorTauCertificate.mtWord] using
      baseCertifiedChainCertificateAudit_ok BaseCertifiedWord.mt
  · simpa [chainAuditForFrontierWord, frontierWordToChainWord,
      frontierOrientToChain, baseCertifiedFrontierWord,
      baseCertifiedChainCertificateAudit,
      GoertzelLemma818LengthTwoBase.lengthTwoOrientWord,
      GoertzelLemma818MirrorMirrorCertificate.mmWord] using
      baseCertifiedChainCertificateAudit_ok BaseCertifiedWord.mm

def concreteChainWordFibrationBaseCertifiedSeeds : Prop :=
  ∀ w : BaseCertifiedWord,
    Nonempty
      (ChainWordConcreteFibrationCertificate (baseCertifiedFrontierWord w))

theorem concreteChainWordFibrationBaseCertifiedSeeds_ok :
    concreteChainWordFibrationBaseCertifiedSeeds := by
  intro w
  exact ⟨ChainWordConcreteFibrationCertificate.ofChainAudit
    (chainAuditForBaseCertifiedFrontierWord_ok w)⟩

def concreteChainWordFibrationLengthTwoSeeds : Prop :=
  ∀ w : GoertzelLemma818LengthTwoBase.LengthTwoOrientWord,
    Nonempty
      (ChainWordConcreteFibrationCertificate
        (GoertzelLemma818FrontierBaseBridge.lengthTwoFrontierWord w))

theorem concreteChainWordFibrationLengthTwoSeeds_ok :
    concreteChainWordFibrationLengthTwoSeeds := by
  intro w
  cases w
  · simpa [GoertzelLemma818FrontierBaseBridge.lengthTwoFrontierWord,
      baseCertifiedFrontierWord] using
      concreteChainWordFibrationBaseCertifiedSeeds_ok BaseCertifiedWord.tt
  · simpa [GoertzelLemma818FrontierBaseBridge.lengthTwoFrontierWord,
      baseCertifiedFrontierWord] using
      concreteChainWordFibrationBaseCertifiedSeeds_ok BaseCertifiedWord.tm
  · simpa [GoertzelLemma818FrontierBaseBridge.lengthTwoFrontierWord,
      baseCertifiedFrontierWord] using
      concreteChainWordFibrationBaseCertifiedSeeds_ok BaseCertifiedWord.mt
  · simpa [GoertzelLemma818FrontierBaseBridge.lengthTwoFrontierWord,
      baseCertifiedFrontierWord] using
      concreteChainWordFibrationBaseCertifiedSeeds_ok BaseCertifiedWord.mm

def concreteChainFiberAppendQuotientFibrationParentRowsLengthTwoSeeds : Prop :=
  ∀ (orient next : GoertzelLemma818FrontierMode.TauOrient)
    (key : List GoertzelLemma814.LColor),
    key ∈ GoertzelLemma814.colorAssignments4 →
      Nonempty
        (ChainFiberAppendQuotientFibrationParentRowsFields
          [orient] next key)

theorem concreteChainFiberAppendQuotientFibrationParentRowsLengthTwoSeeds_ok :
    concreteChainFiberAppendQuotientFibrationParentRowsLengthTwoSeeds := by
  intro orient next key hkey
  have hcert :
      Nonempty
        (ChainWordConcreteFibrationCertificate ([orient] ++ [next])) := by
    cases orient <;> cases next
    · simpa [GoertzelLemma818FrontierBaseBridge.lengthTwoFrontierWord] using
        concreteChainWordFibrationLengthTwoSeeds_ok
          GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.tt
    · simpa [GoertzelLemma818FrontierBaseBridge.lengthTwoFrontierWord] using
        concreteChainWordFibrationLengthTwoSeeds_ok
          GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.tm
    · simpa [GoertzelLemma818FrontierBaseBridge.lengthTwoFrontierWord] using
        concreteChainWordFibrationLengthTwoSeeds_ok
          GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.mt
    · simpa [GoertzelLemma818FrontierBaseBridge.lengthTwoFrontierWord] using
        concreteChainWordFibrationLengthTwoSeeds_ok
          GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.mm
  rcases hcert with ⟨cert⟩
  exact ⟨ChainFiberAppendQuotientFibrationParentRowsFields.ofConcreteAppend
    hkey cert⟩

def concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixFieldsClosed :
    Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    1 < word.length →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ key : List GoertzelLemma814.LColor,
        key ∈ GoertzelLemma814.colorAssignments4 →
          Nonempty
            (ChainFiberAppendQuotientFibrationParentRowsFields
              word orient key)

def concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataClosed :
    Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    1 < word.length →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ key : List GoertzelLemma814.LColor,
        key ∈ GoertzelLemma814.colorAssignments4 →
          Nonempty
            (ChainFiberAppendQuotientFibrationParentRowsBaseData
              word orient key)

/--
The remaining parent-row structural pin for the non-singleton append route.

For every non-singleton prefix `word`, append orientation `orient`, audited
prefix certificate, fixed input `key`, and supplied parent-row base-data record
`data`, this asks for the structural glue: a projection from the appended
concrete fiber to `data.Base`, reachability between appended points with the
same projection, and a lifted appended-fiber reachability witness for every
`data.baseStep` out of a projected point.

The base-data half is theorem-supplied separately by
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataClosed_of_prefix_root_star`.
This Prop is stronger than the paired
`concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed`
route: it quantifies over every supplied `data`, not only the generated
prefix-root-star base data. Since `ChainFiberAppendQuotientFibrationParentRowsBaseData`
is an unrestricted structure with public `mk`, this is not a case split over
`unit` and `ofPrefixRootStar`: an all-data proof must work for any finite
parent-row base record and provide a projection whose image supports every
`data.baseStep` lift. The downstream parent-row sufficiency theorems remain
conditional until this structural pin, or an equivalent paired
base-data/structural record for the chosen generated base data, is proved.
-/
def concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixStructuralClosed :
    Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    1 < word.length →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ key : List GoertzelLemma814.LColor,
        key ∈ GoertzelLemma814.colorAssignments4 →
          ∀ data :
            ChainFiberAppendQuotientFibrationParentRowsBaseData
              word orient key,
              Nonempty
                (ChainFiberAppendQuotientFibrationParentRowsStructuralFields
                  data)

def concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed :
    Prop :=
  ∀ (word : List GoertzelLemma818FrontierMode.TauOrient)
    (orient : GoertzelLemma818FrontierMode.TauOrient),
    1 < word.length →
    Nonempty (ChainWordConcreteFibrationCertificate word) →
      ∀ key : List GoertzelLemma814.LColor,
        key ∈ GoertzelLemma814.colorAssignments4 →
          Nonempty
            (Sigma (fun data :
              ChainFiberAppendQuotientFibrationParentRowsBaseData
                word orient key =>
              ChainFiberAppendQuotientFibrationParentRowsStructuralFields
                data))

theorem concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataClosed_of_prefix_root_star :
    concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataClosed := by
  intro word orient _hlen hcert key hkey
  cases hfiber : concreteChainFiber word key with
  | nil =>
      exact ⟨ChainFiberAppendQuotientFibrationParentRowsBaseData.unit⟩
  | cons root rest =>
      exact ⟨
        ChainFiberAppendQuotientFibrationParentRowsBaseData.ofPrefixRootStar
          hcert hkey hfiber⟩

theorem concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixFieldsClosed_of_base_data_and_structural
    (hData :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataClosed)
    (hStructural :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixStructuralClosed) :
    concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixFieldsClosed := by
  intro word orient hlen hcert key hkey
  rcases hData word orient hlen hcert key hkey with ⟨data⟩
  rcases hStructural word orient hlen hcert key hkey data with ⟨structural⟩
  exact ⟨
    ChainFiberAppendQuotientFibrationParentRowsFields.ofBaseDataAndStructural
      data structural⟩

theorem concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixFieldsClosed_of_base_data_structural
    (hPair :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed) :
    concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixFieldsClosed := by
  intro word orient hlen hcert key hkey
  rcases hPair word orient hlen hcert key hkey with ⟨⟨data, structural⟩⟩
  exact ⟨
    ChainFiberAppendQuotientFibrationParentRowsFields.ofBaseDataAndStructural
      data structural⟩

theorem concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed_of_base_data_and_structural
    (hData :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataClosed)
    (hStructural :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixStructuralClosed) :
    concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed := by
  intro word orient hlen hcert key hkey
  rcases hData word orient hlen hcert key hkey with ⟨data⟩
  rcases hStructural word orient hlen hcert key hkey data with ⟨structural⟩
  exact ⟨⟨data, structural⟩⟩

theorem concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed_of_structural
    (hStructural :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixStructuralClosed) :
    concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed :=
  concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed_of_base_data_and_structural
    concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataClosed_of_prefix_root_star
    hStructural

theorem concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed_of_prefix_fibration
    (hFibration : concreteChainFiberAppendPrefixFibrationClosed) :
    concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed := by
  intro word orient hlen hcert key hkey
  have hne : word ≠ [] := by
    intro hnil
    subst word
    simp at hlen
  cases hfiber : concreteChainFiber word key with
  | nil =>
      let data :
          ChainFiberAppendQuotientFibrationParentRowsBaseData
            word orient key :=
        ChainFiberAppendQuotientFibrationParentRowsBaseData.unit
      let structural :
          ChainFiberAppendQuotientFibrationParentRowsStructuralFields data :=
        { proj := fun _ => ()
          fiberReach := by
            intro x _y _hproj
            have hxPrefix :
                x.1.take word.length ∈ concreteChainFiber word key :=
              concreteChainFiberAppendPrefixClosed_ok
                word orient hne key x.1 x.2
            rw [hfiber] at hxPrefix
            cases hxPrefix
          liftStep := by
            intro x _b _hstep
            have hxPrefix :
                x.1.take word.length ∈ concreteChainFiber word key :=
              concreteChainFiberAppendPrefixClosed_ok
                word orient hne key x.1 x.2
            rw [hfiber] at hxPrefix
            cases hxPrefix }
      exact ⟨⟨data, structural⟩⟩
  | cons root rest =>
      let data :
          ChainFiberAppendQuotientFibrationParentRowsBaseData
            word orient key :=
        ChainFiberAppendQuotientFibrationParentRowsBaseData.ofPrefixRootStar
          hcert hkey hfiber
      have hfib :
          Fibration
            (chainFiberRootClosureStep (word ++ [orient]) key)
            (chainFiberRootClosureStep word key)
            (concreteChainFiberAppendPrefixProjection
              word orient hne key).prefixPoint :=
        hFibration word orient hne hcert key hkey
      let structural :
          ChainFiberAppendQuotientFibrationParentRowsStructuralFields data :=
        { proj :=
            (concreteChainFiberAppendPrefixProjection
              word orient hne key).prefixPoint
          fiberReach := hfib.fiberReach
          liftStep := hfib.liftStep }
      exact ⟨⟨data, structural⟩⟩

theorem concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixFieldsClosed_of_prefix_fibration
    (hFibration : concreteChainFiberAppendPrefixFibrationClosed) :
    concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixFieldsClosed :=
  concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixFieldsClosed_of_base_data_structural
    (concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed_of_prefix_fibration
      hFibration)

theorem concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_length_two_seeds_and_non_singleton
    (hLengthTwo :
      concreteChainFiberAppendQuotientFibrationParentRowsLengthTwoSeeds)
    (hNonSingleton :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixFieldsClosed) :
    concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed := by
  intro word orient hne hcert key hkey
  cases word with
  | nil =>
      exact False.elim (hne rfl)
  | cons head tail =>
      cases tail with
      | nil =>
          simpa using hLengthTwo head orient key hkey
      | cons next rest =>
          have hlen : 1 < (head :: next :: rest).length := by
            simp
          exact hNonSingleton (head :: next :: rest) orient hlen hcert key hkey

theorem concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_non_singleton
    (hNonSingleton :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixFieldsClosed) :
    concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed :=
  concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_length_two_seeds_and_non_singleton
    concreteChainFiberAppendQuotientFibrationParentRowsLengthTwoSeeds_ok
    hNonSingleton

theorem concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_non_singleton_base_data_structural
    (hPair :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed) :
    concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed :=
  concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_non_singleton
    (concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixFieldsClosed_of_base_data_structural
      hPair)

theorem concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_non_singleton_base_data_and_structural
    (hData :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataClosed)
    (hStructural :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixStructuralClosed) :
    concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed :=
  concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_non_singleton
    (concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixFieldsClosed_of_base_data_and_structural
      hData hStructural)

theorem concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_non_singleton_structural
    (hStructural :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixStructuralClosed) :
    concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed :=
  concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_non_singleton_base_data_structural
    (concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed_of_structural
      hStructural)

theorem concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_parent_rows_base_data_and_structural
    (hData :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataClosed)
    (hStructural :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixStructuralClosed) :
    concreteChainFiberFibrationNonemptyTransferClosed :=
  concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_parent_rows
    (concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_non_singleton_base_data_and_structural
      hData hStructural)

theorem concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_parent_rows_base_data_structural
    (hPair :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed) :
    concreteChainFiberFibrationNonemptyTransferClosed :=
  concreteChainFiberFibrationNonemptyTransferClosed_of_append_quotient_parent_rows
    (concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_non_singleton_base_data_structural
      hPair)

theorem concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_parent_rows_base_data_and_structural
    (hData :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataClosed)
    (hStructural :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixStructuralClosed) :
    concreteChainAuditFibrationNonemptyTransferClosed :=
  concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_parent_rows
    (concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_non_singleton_base_data_and_structural
      hData hStructural)

theorem concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_parent_rows_base_data_structural
    (hPair :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed) :
    concreteChainAuditFibrationNonemptyTransferClosed :=
  concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_parent_rows
    (concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_non_singleton_base_data_structural
      hPair)

def concreteChainWordFibrationSingletonSeeds : Prop :=
  ∀ orient : GoertzelLemma818FrontierMode.TauOrient,
    Nonempty (ChainWordConcreteFibrationCertificate [orient])

theorem concreteChainFiberAppendSameTraceRelativeSingletonReachClosed_of_singleton_seeds
    (hSeed : concreteChainWordFibrationSingletonSeeds) :
    concreteChainFiberAppendSameTraceRelativeSingletonReachClosed := by
  intro word orient _hne _hcert key _hkey pref lastX lastY _hpref hlastX hlastY
    hcompatibleX hcompatibleY _htrace
  let localKey := concreteChainFiberAppendLastInputTrace orient lastX
  have hkeyLocal :
      localKey ∈ GoertzelLemma814.colorAssignments4 := by
    simpa [localKey] using
      concreteChainFiberAppendLastInputTrace_mem_colorAssignments4 orient lastX
  have hright :
      GoertzelLemma814.tauOrientAt
        (frontierWordToChainWord (word ++ [orient])) word.length =
        frontierOrientToChain orient := by
    unfold GoertzelLemma814.tauOrientAt frontierWordToChainWord
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [← List.length_map (f := frontierOrientToChain) (as := word)]
    exact GoertzelLemma814.listGetD_append_length
      (List.map frontierOrientToChain word) (frontierOrientToChain orient)
      GoertzelLemma814.TauOrient.normal
  have hinputTrace :
      concreteChainFiberAppendLastInputTrace orient lastX =
        concreteChainFiberAppendLastInputTrace orient lastY :=
    concreteChainFiberAppendLastInputTrace_eq_of_compatible
      (GoertzelLemma814.tauOrientAt
        (frontierWordToChainWord (word ++ [orient])) (word.length - 1))
      orient
      (GoertzelLemma814.chainStateAt pref (word.length - 1))
      lastX lastY (by simpa [hright] using hcompatibleX)
      (by simpa [hright] using hcompatibleY)
  let xLocal : ChainFiberPoint [orient] localKey :=
    ⟨[lastX],
      by
        simpa [localKey] using
          concreteChainFiber_singleton_mem_of_last_input_trace orient hlastX⟩
  let yLocal : ChainFiberPoint [orient] localKey :=
    ⟨[lastY],
      by
        have hyLocal :=
          concreteChainFiber_singleton_mem_of_last_input_trace orient hlastY
        simpa [localKey, hinputTrace] using hyLocal⟩
  refine ⟨hkeyLocal, xLocal, yLocal, rfl, rfl, ?_⟩
  rcases hSeed orient with ⟨cert⟩
  rcases cert.fiberCertificate localKey hkeyLocal with ⟨fiberCert⟩
  exact fiberCert.connected xLocal yLocal

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

theorem chainAuditForFrontierWord_ok_of_append_quotient_fibration
    (hSeed : concreteChainWordFibrationSingletonSeeds)
    (hLift : concreteChainFiberAppendQuotientFibrationClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_concrete_singletons_and_nonempty_transfer
    hSeed
    (concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_fibration
      hLift)
    word

theorem chainAuditForFrontierWord_ok_of_append_quotient_fields
    (hSeed : concreteChainWordFibrationSingletonSeeds)
    (hFields : concreteChainFiberAppendQuotientFibrationFieldsClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_concrete_singletons_and_nonempty_transfer
    hSeed
    (concreteChainAuditFibrationNonemptyTransferClosed_of_append_quotient_fields
      hFields)
    word

theorem chainAuditForFrontierWord_ok_of_append_quotient_root_fields
    (hSeed : concreteChainWordFibrationSingletonSeeds)
    (hFields : concreteChainFiberAppendQuotientFibrationRootFieldsClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_append_quotient_fields
    hSeed
    (concreteChainFiberAppendQuotientFibrationFieldsClosed_of_root_fields
      hFields)
    word

theorem chainAuditForFrontierWord_ok_of_append_quotient_symmetric_root
    (hSeed : concreteChainWordFibrationSingletonSeeds)
    (hFields :
      concreteChainFiberAppendQuotientFibrationSymmetricRootFieldsClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_append_quotient_root_fields
    hSeed
    (concreteChainFiberAppendQuotientFibrationRootFieldsClosed_of_symmetric
      hFields)
    word

theorem chainAuditForFrontierWord_ok_of_append_quotient_listed_symmetric_root
    (hSeed : concreteChainWordFibrationSingletonSeeds)
    (hFields :
      concreteChainFiberAppendQuotientFibrationListedSymmetricRootFieldsClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_append_quotient_symmetric_root
    hSeed
    (concreteChainFiberAppendQuotientFibrationSymmetricRootFieldsClosed_of_listed
      hFields)
    word

theorem chainAuditForFrontierWord_ok_of_append_quotient_parent_map
    (hSeed : concreteChainWordFibrationSingletonSeeds)
    (hFields :
      concreteChainFiberAppendQuotientFibrationParentMapFieldsClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_append_quotient_listed_symmetric_root
    hSeed
    (concreteChainFiberAppendQuotientFibrationListedSymmetricRootFieldsClosed_of_parent_map
      hFields)
    word

theorem chainAuditForFrontierWord_ok_of_append_quotient_parent_rows
    (hSeed : concreteChainWordFibrationSingletonSeeds)
    (hFields :
      concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_append_quotient_parent_map
    hSeed
    (concreteChainFiberAppendQuotientFibrationParentMapFieldsClosed_of_parent_rows
      hFields)
    word

theorem chainAuditForFrontierWord_ok_of_append_quotient_parent_rows_base_data_and_structural
    (hSeed : concreteChainWordFibrationSingletonSeeds)
    (hData :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataClosed)
    (hStructural :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixStructuralClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_append_quotient_parent_rows
    hSeed
    (concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_non_singleton_base_data_and_structural
      hData hStructural)
    word

theorem chainAuditForFrontierWord_ok_of_append_quotient_parent_rows_base_data_structural
    (hSeed : concreteChainWordFibrationSingletonSeeds)
    (hPair :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_append_quotient_parent_rows
    hSeed
    (concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_non_singleton_base_data_structural
      hPair)
    word

theorem chainAuditForFrontierWord_ok_of_append_quotient_path_rows
    (hSeed : concreteChainWordFibrationSingletonSeeds)
    (hFields :
      concreteChainFiberAppendQuotientFibrationPathRowsFieldsClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_append_quotient_parent_rows
    hSeed
    (concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_path_rows
      hFields)
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

theorem concreteChainFiberAppendRelativeSingletonLiftClosed_of_closure_lift
    (hClosureLift :
      concreteChainFiberAppendRelativeSingletonClosureLiftClosed) :
    concreteChainFiberAppendRelativeSingletonLiftClosed := by
  intro word orient hne hcert key hkey pref lastX lastY hpref hlastX hlastY
    hcompatibleX hcompatibleY hkeyLocal xLocal yLocal _hxLocal hyLocal
    hreachLocal
  have hxCloseLocal :
      xLocal.1 ∈ GoertzelLemma814.closeChainFiber
        (frontierWordToChainWord [orient])
        (concreteChainFiber [orient]
          (concreteChainFiberAppendLastInputTrace orient lastX))
        (concreteChainFiber [orient]
          (concreteChainFiberAppendLastInputTrace orient lastX)).length
        [chainFiberRootState [orient]
          (concreteChainFiberAppendLastInputTrace orient lastX)] :=
    chainFiberPoint_mem_rootClosure_of_concreteCertificate
      (concreteChainWordFibrationSingletonSeeds_ok orient) hkeyLocal xLocal
  have hyCloseLocal :
      yLocal.1 ∈ GoertzelLemma814.closeChainFiber
        (frontierWordToChainWord [orient])
        (concreteChainFiber [orient]
          (concreteChainFiberAppendLastInputTrace orient lastX))
        (concreteChainFiber [orient]
          (concreteChainFiberAppendLastInputTrace orient lastX)).length
        [chainFiberRootState [orient]
          (concreteChainFiberAppendLastInputTrace orient lastX)] :=
    chainFiberRootClosureReach_mem_of_mem
      (word := [orient])
      (key := concreteChainFiberAppendLastInputTrace orient lastX)
      hxCloseLocal hreachLocal
  have hyCloseGlobal :=
    hClosureLift word orient hne hcert key hkey pref lastX lastY
      hpref hlastX hlastY hcompatibleX hcompatibleY hkeyLocal yLocal
      hyLocal hyCloseLocal
  exact Reach.single (by
    simpa [chainFiberRootClosureStep] using hyCloseGlobal)

theorem concreteChainFiberAppendFixedPrefixSameInterfaceTraceReachClosed_of_singleton_lift
    (hLift : concreteChainFiberAppendRelativeSingletonLiftClosed) :
    concreteChainFiberAppendFixedPrefixSameInterfaceTraceReachClosed :=
  concreteChainFiberAppendFixedPrefixSameInterfaceTraceReachClosed_of_relative_singleton
    (concreteChainFiberAppendSameTraceRelativeSingletonReachClosed_of_singleton_seeds
      concreteChainWordFibrationSingletonSeeds_ok)
    hLift

theorem concreteChainFiberAppendFixedPrefixLastReachClosed_of_singleton_lift_and_mobility
    (hLift : concreteChainFiberAppendRelativeSingletonLiftClosed)
    (hMobility : concreteChainFiberAppendFixedPrefixInterfaceMobilityReachClosed) :
    concreteChainFiberAppendFixedPrefixLastReachClosed :=
  concreteChainFiberAppendFixedPrefixLastReachClosed_of_interface_trace_cases
    (concreteChainFiberAppendFixedPrefixSameInterfaceTraceReachClosed_of_singleton_lift
      hLift)
    hMobility

theorem concreteChainFiberAppendRawPrefixReachClosed_of_singleton_lift_and_mobility
    (hLift : concreteChainFiberAppendRelativeSingletonLiftClosed)
    (hMobility : concreteChainFiberAppendFixedPrefixInterfaceMobilityReachClosed) :
    concreteChainFiberAppendRawPrefixReachClosed :=
  concreteChainFiberAppendRawPrefixReachClosed_of_fixed_prefix_last_reach
    (concreteChainFiberAppendFixedPrefixLastReachClosed_of_singleton_lift_and_mobility
      hLift hMobility)

theorem concreteChainFiberAppendPrefixFiberReachClosed_of_singleton_lift_and_mobility
    (hLift : concreteChainFiberAppendRelativeSingletonLiftClosed)
    (hMobility : concreteChainFiberAppendFixedPrefixInterfaceMobilityReachClosed) :
    concreteChainFiberAppendPrefixFiberReachClosed :=
  concreteChainFiberAppendPrefixFiberReachClosed_of_raw
    (concreteChainFiberAppendRawPrefixReachClosed_of_singleton_lift_and_mobility
      hLift hMobility)

theorem concreteChainFiberAppendFixedPrefixSameInterfaceTraceReachClosed_of_singleton_closure_lift
    (hClosureLift :
      concreteChainFiberAppendRelativeSingletonClosureLiftClosed) :
    concreteChainFiberAppendFixedPrefixSameInterfaceTraceReachClosed :=
  concreteChainFiberAppendFixedPrefixSameInterfaceTraceReachClosed_of_singleton_lift
    (concreteChainFiberAppendRelativeSingletonLiftClosed_of_closure_lift
      hClosureLift)

theorem concreteChainFiberAppendRawPrefixReachClosed_of_singleton_closure_lift_and_mobility
    (hClosureLift :
      concreteChainFiberAppendRelativeSingletonClosureLiftClosed)
    (hMobility : concreteChainFiberAppendFixedPrefixInterfaceMobilityReachClosed) :
    concreteChainFiberAppendRawPrefixReachClosed :=
  concreteChainFiberAppendRawPrefixReachClosed_of_singleton_lift_and_mobility
    (concreteChainFiberAppendRelativeSingletonLiftClosed_of_closure_lift
      hClosureLift)
    hMobility

theorem concreteChainFiberAppendPrefixFiberReachClosed_of_singleton_closure_lift_and_mobility
    (hClosureLift :
      concreteChainFiberAppendRelativeSingletonClosureLiftClosed)
    (hMobility : concreteChainFiberAppendFixedPrefixInterfaceMobilityReachClosed) :
    concreteChainFiberAppendPrefixFiberReachClosed :=
  concreteChainFiberAppendPrefixFiberReachClosed_of_singleton_lift_and_mobility
    (concreteChainFiberAppendRelativeSingletonLiftClosed_of_closure_lift
      hClosureLift)
    hMobility

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

theorem semanticFrontierStateSufficientForChain_of_append_quotient_fibration
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hLift : concreteChainFiberAppendQuotientFibrationClosed) :
    semanticFrontierStateSufficientForChain targetAudit := by
  intro word _state _hstate _haudit
  exact chainAuditForFrontierWord_ok_of_append_quotient_fibration
    concreteChainWordFibrationSingletonSeeds_ok hLift word

theorem semanticFrontierStateSufficientForChain_of_append_quotient_fields
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hFields : concreteChainFiberAppendQuotientFibrationFieldsClosed) :
    semanticFrontierStateSufficientForChain targetAudit := by
  intro word _state _hstate _haudit
  exact chainAuditForFrontierWord_ok_of_append_quotient_fields
    concreteChainWordFibrationSingletonSeeds_ok hFields word

theorem semanticFrontierStateSufficientForChain_of_append_quotient_root_fields
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hFields : concreteChainFiberAppendQuotientFibrationRootFieldsClosed) :
    semanticFrontierStateSufficientForChain targetAudit := by
  intro word _state _hstate _haudit
  exact chainAuditForFrontierWord_ok_of_append_quotient_root_fields
    concreteChainWordFibrationSingletonSeeds_ok hFields word

theorem semanticFrontierStateSufficientForChain_of_append_quotient_symmetric_root
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hFields :
      concreteChainFiberAppendQuotientFibrationSymmetricRootFieldsClosed) :
    semanticFrontierStateSufficientForChain targetAudit := by
  intro word _state _hstate _haudit
  exact chainAuditForFrontierWord_ok_of_append_quotient_symmetric_root
    concreteChainWordFibrationSingletonSeeds_ok hFields word

theorem semanticFrontierStateSufficientForChain_of_append_quotient_listed_symmetric_root
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hFields :
      concreteChainFiberAppendQuotientFibrationListedSymmetricRootFieldsClosed) :
    semanticFrontierStateSufficientForChain targetAudit := by
  intro word _state _hstate _haudit
  exact chainAuditForFrontierWord_ok_of_append_quotient_listed_symmetric_root
    concreteChainWordFibrationSingletonSeeds_ok hFields word

theorem semanticFrontierStateSufficientForChain_of_append_quotient_parent_map
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hFields :
      concreteChainFiberAppendQuotientFibrationParentMapFieldsClosed) :
    semanticFrontierStateSufficientForChain targetAudit := by
  intro word _state _hstate _haudit
  exact chainAuditForFrontierWord_ok_of_append_quotient_parent_map
    concreteChainWordFibrationSingletonSeeds_ok hFields word

theorem semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hFields :
      concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed) :
    semanticFrontierStateSufficientForChain targetAudit := by
  intro word _state _hstate _haudit
  exact chainAuditForFrontierWord_ok_of_append_quotient_parent_rows
    concreteChainWordFibrationSingletonSeeds_ok hFields word

theorem semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows_non_singleton
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hNonSingleton :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixFieldsClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows
    (concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_non_singleton
      hNonSingleton)

theorem semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows_base_data_and_structural
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hData :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataClosed)
    (hStructural :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixStructuralClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows
    (concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_non_singleton_base_data_and_structural
      hData hStructural)

theorem semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows_base_data_structural
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hPair :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows
    (concreteChainFiberAppendQuotientFibrationParentRowsFieldsClosed_of_non_singleton_base_data_structural
      hPair)

theorem semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows_structural
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hStructural :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixStructuralClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows_base_data_structural
    (concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed_of_structural
      hStructural)

theorem semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows_prefix_fibration
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hFibration : concreteChainFiberAppendPrefixFibrationClosed) :
    semanticFrontierStateSufficientForChain targetAudit :=
  semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows_base_data_structural
    (concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed_of_prefix_fibration
      hFibration)

theorem semanticFrontierStateSufficientForChain_of_append_quotient_path_rows
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hFields :
      concreteChainFiberAppendQuotientFibrationPathRowsFieldsClosed) :
    semanticFrontierStateSufficientForChain targetAudit := by
  intro word _state _hstate _haudit
  exact chainAuditForFrontierWord_ok_of_append_quotient_path_rows
    concreteChainWordFibrationSingletonSeeds_ok hFields word

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

theorem chainAuditForFrontierWord_ok_of_targets_and_append_quotient_parent_rows_base_data_and_structural
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hTarget : ∀ t, targetAudit t = true)
    (hData :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataClosed)
    (hStructural :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixStructuralClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_targets_and_frontier_state_sufficiency
    hTarget
    (semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows_base_data_and_structural
      hData hStructural)
    word

theorem chainAuditForFrontierWord_ok_of_targets_and_append_quotient_parent_rows_base_data_structural
    {targetAudit : RepresentativeSemanticTarget → Bool}
    (hTarget : ∀ t, targetAudit t = true)
    (hPair :
      concreteChainFiberAppendQuotientFibrationParentRowsNonSingletonPrefixBaseDataStructuralClosed)
    (word : List GoertzelLemma818FrontierMode.TauOrient) :
    chainAuditForFrontierWord word = true :=
  chainAuditForFrontierWord_ok_of_targets_and_frontier_state_sufficiency
    hTarget
    (semanticFrontierStateSufficientForChain_of_append_quotient_parent_rows_base_data_structural
      hPair)
    word

end GoertzelLemma818SemanticBridge

end Mettapedia.GraphTheory.FourColor
