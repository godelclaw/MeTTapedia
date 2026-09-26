import Mettapedia.QuantumTheory.YangMills.MassGap
import Mettapedia.QuantumTheory.YangMills.RGBootstrap
import Mettapedia.QuantumTheory.YangMills.RGCrux
import Mettapedia.QuantumTheory.YangMills.ContinuumOSReconstruction
import Mettapedia.QuantumTheory.YangMills.CompletionSteelman
import Mettapedia.QuantumTheory.YangMills.Dimension16WilsonExtractionCertificate
import Mettapedia.QuantumTheory.YangMills.ExtractionConstantBreak
import Mettapedia.QuantumTheory.YangMills.ExtractionStateRouteCollapse
import Mettapedia.QuantumTheory.YangMills.V14FDQuotientTransferNoGo
import Mettapedia.QuantumTheory.YangMills.V14BoundaryCochainBootstrap
import Mettapedia.QuantumTheory.YangMills.SU2LatticeFDCensusNoGo
import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticBasis
import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticWilsonBridge
import Mettapedia.QuantumTheory.YangMills.V14HypercubicFDCensusPaddingNoGo
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldFiveCommutatorSeparator
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CommutatorRowEvaluation
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16RelationEvaluationEquivariance
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LeibnizFDIBPCochainBridge
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LeibnizSourceSix
import Mettapedia.QuantumTheory.YangMills.CrossingInput
import Mettapedia.QuantumTheory.YangMills.MarginalBlindness
import Mettapedia.QuantumTheory.YangMills.TwistDiagnostic
import Mettapedia.QuantumTheory.YangMills.TwistEater
import Mettapedia.QuantumTheory.YangMills.StrongCouplingCrossing
import Mettapedia.QuantumTheory.YangMills.StrongCouplingTwist
import Mettapedia.QuantumTheory.YangMills.WilsonReflectionPositivity
import Mettapedia.QuantumTheory.YangMills.StrongCouplingTransferGap
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FDIBPCochainJointBridge
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCoordinateCompletion
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantBianchi
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantEOM
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderTraceTopologyRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileDifferential
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalFamily
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalFieldEight
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalCycleProfile
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalThreeCoordinate
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceAnticommutatorPhysicalFamily
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldEightTracePhysicalCompleteness
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenCorrectionRefutation
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibility
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderFixedPointTopologyScreen
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepairTracelessRefutation
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderThreeClassScalarExtensionRefutation
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonCartanTraceOrderFaithfulnessNoGo

/-!
# Yang-Mills proof state

This module records the current Yang-Mills route state as checked Lean data.
It is an audit surface for the active formalization lane, not a solution of the
Millennium problem.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

open V14FDQuotientTransferNoGo
open V14BoundaryCochainComplex
open V14BoundaryCochainExtraction
open V14BoundaryCochainBootstrap
open SU2LatticeFDCensusNoGo
open V14HypercubicQuarticCensus
open V14HypercubicQuarticWilsonBridge
open V14HypercubicFDCensusPaddingNoGo
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalRelationBlocks
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16FieldFiveCommutatorSeparator
open HypercubicDimension16FDIBPCochainJointBridge
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceInvariantWitness
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16WilsonTraceOrderRepair
open HypercubicDimension16WilsonTraceOrderCoordinateCompletion
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantBianchi
open HypercubicDimension16WilsonTraceOrderInvariantEOM
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction
open HypercubicDimension16WilsonTraceOrderTraceTopologyRepair
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
open HypercubicDimension16FundamentalTraceCycleProfile
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileDifferential
open HypercubicDimension16FundamentalTracePhysicalFamily
open HypercubicDimension16FundamentalTracePhysicalCycleProfile
open HypercubicDimension16FundamentalTracePhysicalThreeCoordinate
open HypercubicDimension16TraceAnticommutatorPhysicalFamily
open HypercubicDimension16FieldEightTracePhysicalCompleteness
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenMismatch
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenCorrectionRefutation
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenTwoClassCompatibility
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileSourceSevenThreeClassTracelessRefutation
open HypercubicDimension16WilsonTraceOrderFixedPointTopologyScreen
open HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepair
open HypercubicDimension16WilsonTraceOrderExistingScalarParameterRepairTracelessRefutation
open HypercubicDimension16WilsonTraceOrderThreeClassScalarExtensionRefutation
open HypercubicDimension16WilsonCartanTraceOrderFaithfulnessNoGo

/-- Coarse status tags for central Yang-Mills route nodes. -/
inductive YangMillsProofStatus where
  | surveyed
  | checked
  | refuted
  | constructiveGateUncleared
  | openGoal
deriving DecidableEq, Repr

/-- Constructive-QFT checks that must be represented before this lane can
promote RG/extraction evidence to a continuum mass-gap endpoint. -/
inductive YangMillsConstructiveCheck where
  | continuumMeasure
  | euclideanCovariance
  | reflectionPositivity
  | osReconstruction
  | hamiltonianMassGapTransfer
deriving DecidableEq, Repr

/-- Challenge worlds for cheap-falsifying a Yang-Mills mass-gap route before it
is promoted from finite RG/extraction evidence to continuum constructive QFT. -/
inductive YangMillsConstructiveWorld where
  | latticeFieldFamily
  | continuumEuclideanMeasure
  | euclideanSymmetry
  | reflectionPositiveFunctional
  | osHilbertSpace
  | hamiltonianSpectrum
deriving DecidableEq, Repr

/-- Route interfaces needed to pass the constructive-QFT challenge worlds.  A
finite RG/extraction ledger is useful route evidence, but it is not one of the
continuum constructive interfaces required below. -/
inductive YangMillsConstructiveWorldInterface where
  | finiteRGExtractionLedger
  | latticeFieldFamilySampler
  | continuumMeasureTightness
  | continuumMeasureLimit
  | euclideanCovarianceAction
  | euclideanCovarianceMeasurePreservation
  | reflectionPositiveFunctional
  | reflectionPositiveCone
  | osHilbertSpaceConstruction
  | osHamiltonianConstruction
  | hamiltonianSpectrumTransfer
  | positiveMassGapWitness
deriving DecidableEq, Repr

/-- Immediate constructive-QFT prerequisites for each advertised promotion
check.  This is a route audit dependency order, not a construction. -/
def YangMillsConstructiveCheck.prerequisites :
    YangMillsConstructiveCheck → List YangMillsConstructiveCheck
  | .continuumMeasure => []
  | .euclideanCovariance => [.continuumMeasure]
  | .reflectionPositivity => [.continuumMeasure]
  | .osReconstruction => [.euclideanCovariance, .reflectionPositivity]
  | .hamiltonianMassGapTransfer => [.osReconstruction]

/-- Canonical challenge world associated with each constructive-QFT check. -/
def YangMillsConstructiveCheck.challengeWorld :
    YangMillsConstructiveCheck → YangMillsConstructiveWorld
  | .continuumMeasure => .continuumEuclideanMeasure
  | .euclideanCovariance => .euclideanSymmetry
  | .reflectionPositivity => .reflectionPositiveFunctional
  | .osReconstruction => .osHilbertSpace
  | .hamiltonianMassGapTransfer => .hamiltonianSpectrum

/-- Interfaces required before a route can claim to have passed one
constructive-QFT challenge world. -/
def YangMillsConstructiveCheck.requiredWorldInterfaces :
    YangMillsConstructiveCheck → List YangMillsConstructiveWorldInterface
  | .continuumMeasure =>
      [ .latticeFieldFamilySampler
      , .continuumMeasureTightness
      , .continuumMeasureLimit
      ]
  | .euclideanCovariance =>
      [ .euclideanCovarianceAction
      , .euclideanCovarianceMeasurePreservation
      ]
  | .reflectionPositivity =>
      [ .reflectionPositiveFunctional
      , .reflectionPositiveCone
      ]
  | .osReconstruction =>
      [ .osHilbertSpaceConstruction
      , .osHamiltonianConstruction
      ]
  | .hamiltonianMassGapTransfer =>
      [ .hamiltonianSpectrumTransfer
      , .positiveMassGapWitness
      ]

/-- Current verdict for one constructive-QFT obligation. -/
inductive YangMillsConstructiveVerdict where
  | cleared
  | blocked
  | notRepresented
deriving DecidableEq, Repr

/-- Boolean clearance flag for a constructive-QFT verdict. -/
def YangMillsConstructiveVerdict.clears :
    YangMillsConstructiveVerdict → Bool
  | .cleared => true
  | .blocked => false
  | .notRepresented => false

/-- Constructive-QFT gate status for a named Yang-Mills route. -/
structure YangMillsConstructiveStatus where
  routeKey : String
  continuumMeasure : YangMillsConstructiveVerdict
  euclideanCovariance : YangMillsConstructiveVerdict
  reflectionPositivity : YangMillsConstructiveVerdict
  osReconstruction : YangMillsConstructiveVerdict
  hamiltonianMassGapTransfer : YangMillsConstructiveVerdict
deriving Repr

/-- Route-local representation status for constructive challenge-world
interfaces. -/
structure YangMillsConstructiveRouteWorldInterfaces where
  routeKey : String
  supplied : List YangMillsConstructiveWorldInterface
deriving Repr

/-- A mass-gap promotion is constructively cleared only when every required
continuum/OS transfer check is represented and cleared. -/
def YangMillsConstructiveStatus.ClearsForMassGap
    (status : YangMillsConstructiveStatus) : Prop :=
  status.continuumMeasure.clears &&
    status.euclideanCovariance.clears &&
    status.reflectionPositivity.clears &&
    status.osReconstruction.clears &&
    status.hamiltonianMassGapTransfer.clears = true

/-- Checks whose current route verdict is still not represented by Lean evidence. -/
def YangMillsConstructiveStatus.unrepresentedChecks
    (status : YangMillsConstructiveStatus) : List YangMillsConstructiveCheck :=
  (if status.continuumMeasure = .notRepresented then [.continuumMeasure] else []) ++
    (if status.euclideanCovariance = .notRepresented then [.euclideanCovariance] else []) ++
    (if status.reflectionPositivity = .notRepresented then [.reflectionPositivity] else []) ++
    (if status.osReconstruction = .notRepresented then [.osReconstruction] else []) ++
    (if status.hamiltonianMassGapTransfer = .notRepresented then
      [.hamiltonianMassGapTransfer]
    else
      [])

/-- Constructive checks whose route status has at least some Lean-side
representation, whether cleared or blocked. -/
def YangMillsConstructiveStatus.representedChecks
    (status : YangMillsConstructiveStatus) : List YangMillsConstructiveCheck :=
  (if status.continuumMeasure = .notRepresented then [] else [.continuumMeasure]) ++
    (if status.euclideanCovariance = .notRepresented then [] else [.euclideanCovariance]) ++
    (if status.reflectionPositivity = .notRepresented then [] else [.reflectionPositivity]) ++
    (if status.osReconstruction = .notRepresented then [] else [.osReconstruction]) ++
    (if status.hamiltonianMassGapTransfer = .notRepresented then
      []
    else
      [.hamiltonianMassGapTransfer])

/-- Immediate prerequisites for a constructive check that the route has not yet
represented. -/
def YangMillsConstructiveStatus.missingPrerequisitesFor
    (status : YangMillsConstructiveStatus)
    (check : YangMillsConstructiveCheck) : List YangMillsConstructiveCheck :=
  check.prerequisites.filter
    (fun prerequisite => decide (prerequisite ∉ status.representedChecks))

/-- Required constructive challenge-world interfaces not supplied by the route. -/
def YangMillsConstructiveRouteWorldInterfaces.missingFor
    (interfaces : YangMillsConstructiveRouteWorldInterfaces)
    (check : YangMillsConstructiveCheck) :
    List YangMillsConstructiveWorldInterface :=
  check.requiredWorldInterfaces.filter fun requirement =>
    !decide (requirement ∈ interfaces.supplied)

/-- A route has represented the constructive challenge-world interface layer
only when every constructive-QFT check has no missing interface requirement. -/
def YangMillsConstructiveRouteWorldInterfaces.ClearsAll
    (interfaces : YangMillsConstructiveRouteWorldInterfaces) : Prop :=
  interfaces.missingFor .continuumMeasure = [] ∧
    interfaces.missingFor .euclideanCovariance = [] ∧
    interfaces.missingFor .reflectionPositivity = [] ∧
    interfaces.missingFor .osReconstruction = [] ∧
    interfaces.missingFor .hamiltonianMassGapTransfer = []

/-- The dependency order clears only when every promoted constructive check has
its prerequisite checks already represented in the route ledger. -/
def YangMillsConstructiveStatus.ClearsDependencyOrder
    (status : YangMillsConstructiveStatus) : Prop :=
  status.missingPrerequisitesFor .euclideanCovariance = [] ∧
    status.missingPrerequisitesFor .reflectionPositivity = [] ∧
    status.missingPrerequisitesFor .osReconstruction = [] ∧
    status.missingPrerequisitesFor .hamiltonianMassGapTransfer = []

/-- Three-layer gate for promoting RG/extraction evidence into a continuum
Yang-Mills mass-gap route candidate. -/
structure YangMillsMassGapPromotionGate where
  routeKey : String
  constructiveStatus : YangMillsConstructiveStatus
  worldInterfaces : YangMillsConstructiveRouteWorldInterfaces
deriving Repr

/-- A mass-gap promotion gate clears only when the constructive verdicts,
dependency order, and challenge-world interfaces all clear. -/
def YangMillsMassGapPromotionGate.ClearsAll
    (gate : YangMillsMassGapPromotionGate) : Prop :=
  gate.constructiveStatus.ClearsForMassGap ∧
    gate.constructiveStatus.ClearsDependencyOrder ∧
    gate.worldInterfaces.ClearsAll

/-- A constructively cleared route has no unrepresented constructive-QFT checks. -/
theorem YangMillsConstructiveStatus.unrepresentedChecks_eq_nil_of_clearsForMassGap
    {status : YangMillsConstructiveStatus}
    (h : status.ClearsForMassGap) :
    status.unrepresentedChecks = [] := by
  cases status with
  | mk routeKey continuumMeasure euclideanCovariance reflectionPositivity
      osReconstruction hamiltonianMassGapTransfer =>
      cases continuumMeasure <;>
        cases euclideanCovariance <;>
          cases reflectionPositivity <;>
            cases osReconstruction <;>
              cases hamiltonianMassGapTransfer <;>
                simp [YangMillsConstructiveStatus.ClearsForMassGap,
                  YangMillsConstructiveStatus.unrepresentedChecks,
                  YangMillsConstructiveVerdict.clears] at h ⊢

/-- A nonempty unrepresented-check list prevents constructive mass-gap clearance. -/
theorem YangMillsConstructiveStatus.not_clearsForMassGap_of_unrepresentedChecks_ne_nil
    {status : YangMillsConstructiveStatus}
    (h : status.unrepresentedChecks ≠ []) :
    ¬ status.ClearsForMassGap := by
  intro hclear
  exact
    h (YangMillsConstructiveStatus.unrepresentedChecks_eq_nil_of_clearsForMassGap
      (status := status) hclear)

/-- Snapshot of the active Yang-Mills Lean lane. -/
structure YangMillsLaneSurvey where
  sourceFiles : Nat
  sourceLines : Nat
  regressionFiles : Nat
  filesOverThousandLines : Nat
  filesOverSevenHundredFiftyLines : Nat
deriving Repr

/-- Current dependency-map counts for `QuantumTheory/YangMills`. -/
def currentYangMillsLaneSurvey : YangMillsLaneSurvey where
  sourceFiles := 43
  sourceLines := 8084
  regressionFiles := 19
  filesOverThousandLines := 0
  filesOverSevenHundredFiftyLines := 0

/-- Current constructive-QFT gate status for the audited Yang-Mills route. -/
def currentYangMillsConstructiveStatus : YangMillsConstructiveStatus where
  routeKey := "yang-mills-rg-extraction-to-mass-gap"
  continuumMeasure := .notRepresented
  euclideanCovariance := .notRepresented
  reflectionPositivity := .notRepresented
  osReconstruction := .notRepresented
  hamiltonianMassGapTransfer := .notRepresented

/-- The current RG/extraction route has a finite route ledger, but no continuum
constructive-QFT challenge-world interface. -/
def currentYangMillsConstructiveWorldInterfaces :
    YangMillsConstructiveRouteWorldInterfaces where
  routeKey := "yang-mills-rg-extraction-to-mass-gap"
  supplied := [.finiteRGExtractionLedger]

/-- The current RG/extraction route packaged as a continuum mass-gap promotion
gate. -/
def currentYangMillsMassGapPromotionGate :
    YangMillsMassGapPromotionGate where
  routeKey := "yang-mills-rg-extraction-to-mass-gap"
  constructiveStatus := currentYangMillsConstructiveStatus
  worldInterfaces := currentYangMillsConstructiveWorldInterfaces

theorem challengeWorld_continuumMeasure :
    YangMillsConstructiveCheck.continuumMeasure.challengeWorld =
      .continuumEuclideanMeasure := by
  rfl

theorem challengeWorld_euclideanCovariance :
    YangMillsConstructiveCheck.euclideanCovariance.challengeWorld =
      .euclideanSymmetry := by
  rfl

theorem challengeWorld_reflectionPositivity :
    YangMillsConstructiveCheck.reflectionPositivity.challengeWorld =
      .reflectionPositiveFunctional := by
  rfl

theorem challengeWorld_osReconstruction :
    YangMillsConstructiveCheck.osReconstruction.challengeWorld =
      .osHilbertSpace := by
  rfl

theorem challengeWorld_hamiltonianMassGapTransfer :
    YangMillsConstructiveCheck.hamiltonianMassGapTransfer.challengeWorld =
      .hamiltonianSpectrum := by
  rfl

theorem requiredWorldInterfaces_continuumMeasure :
    YangMillsConstructiveCheck.continuumMeasure.requiredWorldInterfaces =
      [ .latticeFieldFamilySampler
      , .continuumMeasureTightness
      , .continuumMeasureLimit
      ] := by
  rfl

theorem requiredWorldInterfaces_euclideanCovariance :
    YangMillsConstructiveCheck.euclideanCovariance.requiredWorldInterfaces =
      [ .euclideanCovarianceAction
      , .euclideanCovarianceMeasurePreservation
      ] := by
  rfl

theorem requiredWorldInterfaces_reflectionPositivity :
    YangMillsConstructiveCheck.reflectionPositivity.requiredWorldInterfaces =
      [ .reflectionPositiveFunctional
      , .reflectionPositiveCone
      ] := by
  rfl

theorem requiredWorldInterfaces_osReconstruction :
    YangMillsConstructiveCheck.osReconstruction.requiredWorldInterfaces =
      [ .osHilbertSpaceConstruction
      , .osHamiltonianConstruction
      ] := by
  rfl

theorem requiredWorldInterfaces_hamiltonianMassGapTransfer :
    YangMillsConstructiveCheck.hamiltonianMassGapTransfer.requiredWorldInterfaces =
      [ .hamiltonianSpectrumTransfer
      , .positiveMassGapWitness
      ] := by
  rfl

theorem currentYangMillsConstructiveWorldInterfaces_supplied :
    currentYangMillsConstructiveWorldInterfaces.supplied =
      [.finiteRGExtractionLedger] := by
  rfl

theorem currentYangMillsConstructiveWorldInterfaces_missing_continuumMeasure :
    currentYangMillsConstructiveWorldInterfaces.missingFor .continuumMeasure =
      YangMillsConstructiveCheck.continuumMeasure.requiredWorldInterfaces := by
  simp [YangMillsConstructiveRouteWorldInterfaces.missingFor,
    currentYangMillsConstructiveWorldInterfaces,
    YangMillsConstructiveCheck.requiredWorldInterfaces]

theorem currentYangMillsConstructiveWorldInterfaces_missing_euclideanCovariance :
    currentYangMillsConstructiveWorldInterfaces.missingFor .euclideanCovariance =
      YangMillsConstructiveCheck.euclideanCovariance.requiredWorldInterfaces := by
  simp [YangMillsConstructiveRouteWorldInterfaces.missingFor,
    currentYangMillsConstructiveWorldInterfaces,
    YangMillsConstructiveCheck.requiredWorldInterfaces]

theorem currentYangMillsConstructiveWorldInterfaces_missing_reflectionPositivity :
    currentYangMillsConstructiveWorldInterfaces.missingFor .reflectionPositivity =
      YangMillsConstructiveCheck.reflectionPositivity.requiredWorldInterfaces := by
  simp [YangMillsConstructiveRouteWorldInterfaces.missingFor,
    currentYangMillsConstructiveWorldInterfaces,
    YangMillsConstructiveCheck.requiredWorldInterfaces]

theorem currentYangMillsConstructiveWorldInterfaces_missing_osReconstruction :
    currentYangMillsConstructiveWorldInterfaces.missingFor .osReconstruction =
      YangMillsConstructiveCheck.osReconstruction.requiredWorldInterfaces := by
  simp [YangMillsConstructiveRouteWorldInterfaces.missingFor,
    currentYangMillsConstructiveWorldInterfaces,
    YangMillsConstructiveCheck.requiredWorldInterfaces]

theorem currentYangMillsConstructiveWorldInterfaces_missing_hamiltonianTransfer :
    currentYangMillsConstructiveWorldInterfaces.missingFor
        .hamiltonianMassGapTransfer =
      YangMillsConstructiveCheck.hamiltonianMassGapTransfer.requiredWorldInterfaces := by
  simp [YangMillsConstructiveRouteWorldInterfaces.missingFor,
    currentYangMillsConstructiveWorldInterfaces,
    YangMillsConstructiveCheck.requiredWorldInterfaces]

theorem currentYangMillsConstructiveWorldInterfaces_not_cleared :
    ¬ currentYangMillsConstructiveWorldInterfaces.ClearsAll := by
  intro hclears
  have hcontinuum := hclears.1
  rw [currentYangMillsConstructiveWorldInterfaces_missing_continuumMeasure] at hcontinuum
  simp [YangMillsConstructiveCheck.requiredWorldInterfaces] at hcontinuum

theorem currentYangMillsConstructiveStatus_unrepresentedChecks :
    currentYangMillsConstructiveStatus.unrepresentedChecks =
      [ .continuumMeasure
      , .euclideanCovariance
      , .reflectionPositivity
      , .osReconstruction
      , .hamiltonianMassGapTransfer
      ] := by
  simp [YangMillsConstructiveStatus.unrepresentedChecks,
    currentYangMillsConstructiveStatus]

theorem currentYangMillsConstructiveStatus_representedChecks :
    currentYangMillsConstructiveStatus.representedChecks = [] := by
  simp [YangMillsConstructiveStatus.representedChecks,
    currentYangMillsConstructiveStatus]

theorem currentYangMillsConstructiveStatus_missingPrerequisites_euclideanCovariance :
    currentYangMillsConstructiveStatus.missingPrerequisitesFor
      .euclideanCovariance = [.continuumMeasure] := by
  simp [YangMillsConstructiveStatus.missingPrerequisitesFor,
    YangMillsConstructiveCheck.prerequisites,
    currentYangMillsConstructiveStatus_representedChecks]

theorem currentYangMillsConstructiveStatus_missingPrerequisites_reflectionPositivity :
    currentYangMillsConstructiveStatus.missingPrerequisitesFor
      .reflectionPositivity = [.continuumMeasure] := by
  simp [YangMillsConstructiveStatus.missingPrerequisitesFor,
    YangMillsConstructiveCheck.prerequisites,
    currentYangMillsConstructiveStatus_representedChecks]

theorem currentYangMillsConstructiveStatus_missingPrerequisites_osReconstruction :
    currentYangMillsConstructiveStatus.missingPrerequisitesFor
      .osReconstruction = [.euclideanCovariance, .reflectionPositivity] := by
  simp [YangMillsConstructiveStatus.missingPrerequisitesFor,
    YangMillsConstructiveCheck.prerequisites,
    currentYangMillsConstructiveStatus_representedChecks]

theorem currentYangMillsConstructiveStatus_missingPrerequisites_hamiltonianTransfer :
    currentYangMillsConstructiveStatus.missingPrerequisitesFor
      .hamiltonianMassGapTransfer = [.osReconstruction] := by
  simp [YangMillsConstructiveStatus.missingPrerequisitesFor,
    YangMillsConstructiveCheck.prerequisites,
    currentYangMillsConstructiveStatus_representedChecks]

theorem currentYangMillsConstructiveStatus_unrepresentedChecks_nonempty :
    currentYangMillsConstructiveStatus.unrepresentedChecks ≠ [] := by
  simp [currentYangMillsConstructiveStatus_unrepresentedChecks]

theorem currentYangMillsConstructiveStatus_not_cleared :
    ¬ currentYangMillsConstructiveStatus.ClearsForMassGap := by
  exact
    YangMillsConstructiveStatus.not_clearsForMassGap_of_unrepresentedChecks_ne_nil
      currentYangMillsConstructiveStatus_unrepresentedChecks_nonempty

theorem currentYangMillsConstructiveStatus_dependencyOrder_not_cleared :
    ¬ currentYangMillsConstructiveStatus.ClearsDependencyOrder := by
  intro hclears
  have hhamiltonian := hclears.2.2.2
  rw [currentYangMillsConstructiveStatus_missingPrerequisites_hamiltonianTransfer] at hhamiltonian
  simp at hhamiltonian

theorem currentYangMillsMassGapPromotionGate_layers :
    currentYangMillsMassGapPromotionGate.constructiveStatus =
        currentYangMillsConstructiveStatus ∧
      currentYangMillsMassGapPromotionGate.worldInterfaces =
        currentYangMillsConstructiveWorldInterfaces := by
  exact ⟨rfl, rfl⟩

theorem currentYangMillsMassGapPromotionGate_not_cleared :
    ¬ currentYangMillsMassGapPromotionGate.ClearsAll := by
  intro hclears
  exact currentYangMillsConstructiveStatus_not_cleared hclears.1

/-- Simple PLN-style truth bookkeeping: support and confidence percentages. -/
structure SimpleTruthValue where
  supportPercent : Nat
  confidencePercent : Nat
deriving Repr

/-- A compact route-node record for the current Yang-Mills formalization. -/
structure YangMillsProofNode where
  id : String
  status : YangMillsProofStatus
  truthValue : SimpleTruthValue
  evidence : String
  nextObligation : String
deriving Repr

/-- The live Yang-Mills surface imports the checked route modules. -/
def yangMillsLiveSurfaceNode : YangMillsProofNode where
  id := "yang-mills.live-surface"
  status := .checked
  truthValue := ⟨100, 93⟩
  evidence := "Mettapedia.QuantumTheory.YangMills imports the clustering, extraction, mass-gap, RG bootstrap, and RG crux surfaces."
  nextObligation := "Keep regression checks in the separate regression aggregator unless a live theorem needs them."

/-- The regression surface is already split into module-level companions. -/
def yangMillsRegressionSurfaceNode : YangMillsProofNode where
  id := "yang-mills.regression-surface"
  status := .checked
  truthValue := ⟨100, 93⟩
  evidence := "Mettapedia.QuantumTheory.YangMills.Regression imports the focused regression companions for the live route modules."
  nextObligation := "Add future regression companions beside the route module they protect."

/-- The same-constant lower-even extraction repair is arithmetically refuted. -/
def yangMillsSameConstantLowerEvenExtractionNode : YangMillsProofNode where
  id := "yang-mills.rg.same-constant-lower-even-extraction"
  status := .refuted
  truthValue := ⟨100, 98⟩
  evidence := "not_sameConstantEvenBelowSixteenGapRouteCertificate and not_atLeast2048EvenBelowSixteenGapRouteCertificate rule out the lower-even extraction repair, while rgContraction_2224_two_sixteen records the positive dmax=16 arithmetic benchmark."
  nextObligation := "Do not revive lower-even extraction as a mass-gap route unless the recombination constant or route shape is genuinely changed and audited."

/-- Source adjudication of the former extraction-constant erratum.  The
sign-only repair and the literal factor-fourteen reading are refuted; only the
parameterized scalar arithmetic and our explicit norm-one realization stand. -/
def yangMillsExtractionConstantErratumNode : YangMillsProofNode where
  id := "yang-mills.rg.extraction-constant-erratum"
  status := .refuted
  truthValue := ⟨0, 99⟩
  evidence := "ExtractionMajorant refutes the displayed bound-two calculation. V14FDQuotientTransferNoGo proves that both MOVE-4 survivor extractors retain an explicit canonical-dimension-18 scalar derivative operator, and that the integration-by-parts quotient common to the on-shell and off-shell policies has a nonzero block-boundary descendant, so neither policy admits the ordinary block-functional or RG-compatible transfer socket. The range-only and polymer-contact countermodels remain independent obstructions."
  nextObligation := "The fixed-width carrier no-go applies only to that encoding. OUR unpadded exact carrier and coordinate-free joint relation submodule now exist; complete the policy-indexed relation census, sparse joint rank and conditioning certificates, and Wilson-functional-to-cochain coordinates in the repaired norm."

/-- Constructed algebraic/mechanical part of the postponed-IBP repair.  The
full Wilson analytic and RG transfer remains open. -/
def yangMillsPostponedIBPRepairNode : YangMillsProofNode where
  id := "yang-mills.rg.postponed-ibp-boundary-cochain"
  status := .checked
  truthValue := ⟨100, 98⟩
  evidence := "V14BoundaryCochainComplex constructs an exact two-block boundary complex and an interface-compatible SU(2) witness with nonzero values +1 and -1 cancelling in global H0. V14BoundaryCochainExtraction supplies a derivative-aware coordinate cutoff with constant one in coefficient-l1 and in F.3's coefficient-sup branch after coordinatization. YM MOVE 7 then proves that the requested actual-lattice O.9 coordinate completion is impossible already at canonical dimension eight: an exact SU(2) Wilson observable has a hypercubic quartic jet outside every Lorentz-scalar span."
  nextObligation := "Use the boundary-cochain repair with the existing unpadded exact carrier and coordinate-free joint relation submodule. Supply the remaining H(4)-stable relation rows, complete sparse rank and conditioning certificates, and actual Wilson analytic coordinates."

/-- Terminal decision for the requested O.9/F.4.3 actual-lattice coordinate
campaign.  The no-go is SU(2)-scoped and occurs at canonical dimension eight,
before basis reduction, dual jets, or conditioning. -/
def yangMillsDimension16O9WilsonCensusNode : YangMillsProofNode where
  id := "yang-mills.rg.dimension16-o9-wilson-census"
  status := .refuted
  truthValue := ⟨0, 99⟩
  evidence := "ymMove7_dimension16WilsonCoordinate_terminalNoGo constructs the exact SU(2) Cartan link chart, proves that the actual normalized Wilson observable has fourth jet 6 times the hypercubic quartic, exhibits an orthogonal rotation changing that jet from 1 to 337/625, and refutes every finite O.9 Lorentz-scalar spanning census under both off-shell and on-shell relation policies and all enumerated same-target variants."
  nextObligation := "Continue the same Wilson route through a hypercubic-complete lattice census or a controlled continuum/Symanzik projection. Neither may inherit the old dual-jet conditioning or bootstrap constants without a fresh same-object proof."

/-- Complete derivative-free Cartan quartic census on an unpadded carrier. -/
def yangMillsHypercubicQuarticCensusNode : YangMillsProofNode where
  id := "yang-mills.rg.hypercubic-quartic-census"
  status := .checked
  truthValue := ⟨100, 99⟩
  evidence := "V14HypercubicQuarticCensusCertificate classifies all 126 quartic monomials into four admissible signed H(4) orbits and seven killed orbit classes. V14HypercubicQuarticBasis constructs the four covariant orbit basis functions, representative-evaluation duals, identity conditioning matrix, reconstruction, and coordinate independence. V14HypercubicQuarticWilsonBridge identifies the actual Wilson coefficient vector as (6,0,0,0), realizes its exact fourth jet, and proves the O(4)-invariant subspace is proper with a nonzero pure-fourth artifact quotient class."
  nextObligation := "Use this as the unpadded dimension-eight regression anchor only. It does not include noncommutative color/trace syntax, derivatives, or the dimension-sixteen relation quotient."

/-- Terminal decision for the current fixed-width dimension-sixteen raw
carrier.  Inactive padding prevents an invertible census from also being a
faithful census of active operator syntax. -/
def yangMillsHypercubicDimension16PaddedCensusNode : YangMillsProofNode where
  id := "yang-mills.rg.hypercubic-dimension16-padded-census"
  status := .refuted
  truthValue := ⟨0, 99⟩
  evidence := "faithful_dimension16_exactCensus_uninhabited gives two distinct padded encodings with zero active fields and derivatives but identical active syntax, then proves that no invertible ExactCensusCertificate can make every basis column padding-invariant: equal basis rows contradict the right-inverse identity matrix."
  nextObligation := "The unpadded/dependent syntax is now available. Complete the Bianchi/EOM/IBP/trace/Cayley--Hamilton relation census, its joint sparse rank and dual conditioning, and the Wilson-functional analytic bridge on that repaired carrier."

/-- OUR physical source-band descent closes every arbitrary relation column
outside field count seven for the full cycle-profile correction.  It does not
classify the source-seven relation band or prove descent through all of the
coordinate-free relation submodule. -/
theorem currentYangMillsCycleProfileCorrection_physicalRelation_zero_of_source_ne_seven
    (policy : PhysicalRelationPolicy)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ)
    (hseven : physicalRelationGeneratorSourceFieldCount generator ≠ ourSevenFieldCount) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient)) = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_ne_seven
    policy generator coefficient hseven

#print axioms currentYangMillsCycleProfileCorrection_physicalRelation_zero_of_source_ne_seven

/-- OUR present one-class cycle-profile correction is exactly refuted on a
second concrete physical source-seven covariant-commutator row.  The theorem
does not rule out a revised multi-class correction. -/
theorem currentYangMillsCycleProfileCorrection_secondarySourceSeven_ne_zero
    (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) ≠ 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_ourSecondaryCommutator_ne_zero policy

#print axioms currentYangMillsCycleProfileCorrection_secondarySourceSeven_ne_zero

/-- OUR rank-two plane-profile repair annihilates the two explicitly realized
source-seven commutator rows under either policy.  It is a bounded repair of
those rows only, not a complete source-seven descent theorem. -/
theorem currentYangMillsTwoClassSourceSevenRepair_namedRows_zero
    (policy : PhysicalRelationPolicy) :
    ourTwoClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 ∧
    ourTwoClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) = 0 := by
  exact ⟨ourTwoClassSourceSevenTraceOrderCorrection_ourCommutator_zero policy,
    ourTwoClassSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero policy⟩

#print axioms currentYangMillsTwoClassSourceSevenRepair_namedRows_zero

/-- OUR two-class augmentation is explicitly incompatible with the genuine
second-IBP row.  The exact failure is preserved as a finite obstruction
certificate rather than being hidden by the subsequent repair. -/
theorem currentYangMillsTwoClassSourceSevenAugmentation_secondIBP_ne_zero
    (policy : PhysicalRelationPolicy) :
    ourAugmentedCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) ≠ 0 :=
  ourAugmentedCycleProfileInvariantTraceOrderCorrection_ourSecondIBP_ne_zero
    policy

#print axioms currentYangMillsTwoClassSourceSevenAugmentation_secondIBP_ne_zero

/-- OUR three-class source-seven repair retains the named differential and
trace checks while cancelling both explicit source-seven commutators.  It is
a finite compatibility result, not a complete source-seven descent theorem. -/
theorem currentYangMillsThreeClassSourceSevenRepair_namedRows_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 ∧
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) =
      0 ∧
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 ∧
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 ∧
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 ∧
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 ∧
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 ∧
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 ∧
    (∀ generator : FieldEightTraceGenerator,
      ourThreeClassSourceSevenTraceOrderCorrection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)) =
        0) := by
  exact ⟨ourThreeClassSourceSevenTraceOrderCorrection_ourCommutator_zero
      policy,
    ourThreeClassSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero
      policy,
    ourThreeClassSourceSevenTraceOrderCorrection_ourIBP_zero,
    ourThreeClassSourceSevenTraceOrderCorrection_ourSecondIBP_zero policy,
    ourThreeClassSourceSevenTraceOrderCorrection_ourBianchi_zero policy,
    ourThreeClassSourceSevenTraceOrderCorrection_ourEOM_zero,
    ourThreeClassSourceSevenTraceOrderCorrection_ourFundamentalThreeCut_zero
      policy,
    ourThreeClassSourceSevenTraceOrderCorrection_ourTraceAnticommutator_zero
      policy,
    fun generator =>
      ourThreeClassSourceSevenTraceOrderCorrection_liftedTraceGenerator_zero
        policy generator⟩

#print axioms currentYangMillsThreeClassSourceSevenRepair_namedRows_zero

/-- OUR three-class source-seven extension is explicitly refuted by a genuine
singleton-trace relation.  Its exact value is `(-1/10)` times the certified
nonzero incoming trace class under either physical policy. -/
theorem currentYangMillsThreeClassSourceSevenRepair_singletonTrace_ne_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeClassSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) ≠ 0 :=
  ourThreeClassSourceSevenTraceOrderCorrection_ourSingletonTrace_ne_zero policy

#print axioms currentYangMillsThreeClassSourceSevenRepair_singletonTrace_ne_zero

/-- OUR first full-existing-coordinate reparameterization check.  The signed
invariant deformation uses no new coordinate: it cancels the singleton row
while retaining both explicit source-seven commutators.  The named differential
and trace rows and complete descent remain separate obligations. -/
theorem currentYangMillsExistingScalarParameterRepair_firstChecks
    (policy : PhysicalRelationPolicy) :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) = 0 ∧
      ourParameterSynthesizedSourceSevenTraceOrderCorrection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 ∧
      ourParameterSynthesizedSourceSevenTraceOrderCorrection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single
            (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) = 0 :=
  ⟨ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSingletonTrace_zero
      policy,
    ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourCommutator_zero
      policy,
    ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero
      policy⟩

#print axioms currentYangMillsExistingScalarParameterRepair_firstChecks

/-- OUR expanded existing-coordinate reparameterization audit.  The signed
invariant deformation now cancels the singleton row and retains the two
concrete commutators, the displayed IBP/Bianchi rows, and the on-shell EOM
row.  This is a finite named-row result, not descent through the complete
source-seven relation submodule. -/
theorem currentYangMillsExistingScalarParameterRepair_sevenChecks
    (policy : PhysicalRelationPolicy) :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) = 0 ∧
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 ∧
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single
          (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) = 0 ∧
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 ∧
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 ∧
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 ∧
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  exact ⟨ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSingletonTrace_zero
      policy,
    ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourCommutator_zero
      policy,
    ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSecondaryCommutator_zero
      policy,
    ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourIBP_zero,
    ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourSecondIBP_zero
      policy,
    ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourBianchi_zero
      policy,
    ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourEOM_zero⟩

#print axioms currentYangMillsExistingScalarParameterRepair_sevenChecks

/- OUR expanded named-family packet also includes the canonical fundamental
three-cut and polarized trace-anticommutator rows.  It remains a finite audit,
not a theorem of descent through all source-seven relations. -/
set_option maxRecDepth 100000 in
theorem currentYangMillsExistingScalarParameterRepair_nineChecks
    (policy : PhysicalRelationPolicy) :
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourSingletonTraceGenerator policy) 1)) = 0 ∧
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 ∧
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single
          (ourSecondaryFieldSevenCommutatorGenerator policy) 1)) = 0 ∧
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 ∧
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 ∧
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 ∧
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 ∧
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 ∧
    ourParameterSynthesizedSourceSevenTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 := by
  rcases currentYangMillsExistingScalarParameterRepair_sevenChecks policy with
    ⟨singleton, incoming, secondary, ibp, secondIBP, bianchi, eom⟩
  exact ⟨singleton, incoming, secondary, ibp, secondIBP, bianchi, eom,
    ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourFundamentalThreeCut_zero
      policy,
    ourParameterSynthesizedSourceSevenTraceOrderCorrection_ourTraceAnticommutator_zero
      policy⟩

#print axioms currentYangMillsExistingScalarParameterRepair_nineChecks

/-- The nine named checks are not a descent theorem: a second actual
singleton-trace carrier preserves the independent second-IBP derivative
geometry and gives an exact quotient-functional mismatch. -/
theorem currentYangMillsExistingScalarParameterRepair_not_descends
    (policy : PhysicalRelationPolicy) :
    ¬ orbitPhysicalRelationSubmodule policy ≤
      LinearMap.ker ourParameterSynthesizedSourceSevenTraceOrderCorrection :=
  ourParameterSynthesizedSourceSevenTraceOrderCorrection_not_descends policy

#print axioms currentYangMillsExistingScalarParameterRepair_not_descends

/-- The same witness rules out every scalar-valued extension in the literal
incoming quotient direction, not only the displayed six-scalar choice. -/
theorem currentYangMillsThreeClassScalarLiteralExtension_not_descends
    (scalar : ExactFieldRelabelOrbitSpace →ₗ[ℚ] ℚ)
    (policy : PhysicalRelationPolicy) :
    ¬ orbitPhysicalRelationSubmodule policy ≤
      LinearMap.ker (ourThreeClassScalarLiteralExtension scalar) :=
  ourThreeClassScalarLiteralExtension_not_descends scalar policy

#print axioms currentYangMillsThreeClassScalarLiteralExtension_not_descends

/-- OUR preliminary fixed-trace-point gate detects the singleton row, but its
same signed character has fundamental three-cut numerator `-64`; this is a
screening constraint, not yet a descended coordinate. -/
theorem currentYangMillsFixedPointTopologyScreen_packet :
    (ourFixedTracePointCount ourSingletonTraceLabeled = 1) ∧
      (ourFixedPointTraceAxisSignedWeight ourSingletonTraceLabeled = 32) ∧
      (ourFixedPointTraceAxisSignedWeight ourFundamentalThreeCutBaseLabeled -
          ourFixedPointTraceAxisSignedWeight
            ourFundamentalThreeCutSwapFirstSecondLabeled -
            ourFixedPointTraceAxisSignedWeight
              ourFundamentalThreeCutSwapFirstThirdLabeled -
              ourFixedPointTraceAxisSignedWeight
                ourFundamentalThreeCutSwapSecondThirdLabeled +
                ourFixedPointTraceAxisSignedWeight
                  ourFundamentalThreeCutForwardLabeled +
                  ourFixedPointTraceAxisSignedWeight
                    ourFundamentalThreeCutBackwardLabeled = -64) := by
  exact ⟨ourSingletonTrace_fixedTracePointCount,
    ourSingletonTrace_fixedPointTraceAxisSignedWeight,
    ourFundamentalThreeCut_fixedPointTraceAxisSignedWeight⟩

#print axioms currentYangMillsFixedPointTopologyScreen_packet

/-- OUR repaired finite relation interface continues the Wilson-lattice proof
programme on an unpadded hypercubic carrier. It is coordinate-free before a
row ordering and records only the certified lower bound, not a complete
physical quotient calculation. -/
def yangMillsJointPhysicalRelationNode : YangMillsProofNode where
  id := "yang-mills.rg.joint-physical-relation-interface"
  status := .checked
  truthValue := ⟨100, 99⟩
  evidence := "HypercubicDimension16JointPhysicalQuotient defines the invariant physical relation submodule as the coordinate-free preimage of the full relation range and proves off-shell inclusion into the on-shell policy. HypercubicDimension16FieldFiveCommutatorSeparator proves joint invariant relation rank at least 11558 for either policy from 11556 field-eight trace rows, a seven-to-eight commutator row, and a field-five separator; that submodule uses the earlier commutator row, which is not a field identity when the commutator's field carries outer derivatives, and it contains an invariant vector with nonzero background value, so it is not a space of relations (see the Leibniz-correction node). OUR HypercubicDimension16LeibnizJointRank proves the same bound 11558 for the Leibniz-corrected joint submodule, where the two operators agree in the sectors with seven or eight fields. OUR HypercubicDimension16FDIBPCochainJointBridge gives an equivariant finite F,D/IBP cochain realization with that same range, and OUR HypercubicDimension16LeibnizFDIBPCochainBridge gives one onto the corrected submodule. OUR trace-order repairs identify and correct successive explicit canonical obstructions, while the complete three-cut cycle-profile census forces coefficients (6/5, 13/10, -1, -7/10, -3/5) and checks its alternating topology profile on all 210 labels. OUR HypercubicDimension16FundamentalTracePhysicalFamily realizes each label as an actual policy-indexed FundamentalTraceSite and carries its finite cochains by signed Reynolds semantics into the coordinate-free joint relation submodule. Its field-eight, profile, and three-coordinate bridges prove that the full current correction annihilates that 210-label physical family. OUR HypercubicDimension16TraceAnticommutatorPhysicalFamily realizes all seven adjacent polarized SU(2) trace-anticommutator placements on the same physical seven-cycle. Each has the common three-coordinate residual 1/2 and profile value -1/2, so the full current correction annihilates its complete finite cochain family under either policy. OUR arbitrary-carrier field-eight bridge identifies every source-eight physical traceless, anticommutator, and fundamental row with the derivative-free field-eight schema; derivative-bearing sites are empty there. OUR source-six curvature-pair theorem proves exact cancellation of the only cross-sector covariant-commutator branch there. Together with support below six, the full correction annihilates every arbitrary physical relation column outside source seven; OUR HypercubicDimension16LeibnizSourceSix proves the same for the corrected operator, which agrees with the earlier one on the source bands seven and eight. In the remaining source-seven band, a genuine singleton-trace row refutes every choice of the three added selector values with the cycle-profile base held fixed. OUR signed-H(4)-invariant reparameterization then uses only the six already constructed scalar coordinates and cancels that singleton row while retaining the two explicit source-seven commutators, the displayed first- and second-IBP rows, Bianchi, the on-shell EOM row, the canonical fundamental three-cut row, and the polarized trace-anticommutator row. This nine-row audit is not a complete source-seven relation census, a descent theorem, rank calculation, conditioning certificate, or Wilson-functional coordinate construction."
  nextObligation := "The existing six-scalar deformation is now refuted by a second actual singleton-trace relation with the independent second-IBP derivative geometry. Construct and semantically identify an enlarged coordinate family, or machine-check a further impossibility theorem for that larger family. Do not use the refuted map for sparse rank, conditioning, or Wilson-functional coordinates."

/-- OUR Leibniz correction of the covariant-derivative commutator rows. -/
def yangMillsCommutatorLeibnizCorrectionNode : YangMillsProofNode where
  id := "yang-mills.rg.commutator-leibniz-correction"
  status := .checked
  truthValue := ⟨100, 99⟩
  evidence := "The covariant-commutator row of HypercubicDimension16CovariantCommutator keeps every outer derivative of the commutator's field on that field, so it is a field identity only when the field has no derivative outside the pair. OUR HypercubicDimension16CommutatorRowEvaluation evaluates rows on gauge backgrounds and proves that the earlier four-field commutator row has value 64 on an explicit constant SU(2) background, so it is not a consequence of the field identities. OUR HypercubicDimension16LeibnizCommutator defines the Leibniz-correct row, which distributes the outer derivatives over both factors; OUR HypercubicDimension16LeibnizRelationOperator assembles the corrected operator and its joint invariant relation submodule under either policy; OUR HypercubicDimension16LeibnizJointRank proves the certified lower bounds 11557 and 11558 for that submodule. OUR HypercubicDimension16LeibnizCommutatorSoundness and HypercubicDimension16RelationRowSoundness prove every row of the corrected operator sound: its integrated value vanishes on every gauge background, and that of the equation-of-motion rows on every on-shell background. OUR HypercubicDimension16RelationEvaluationDescent carries the evaluation to the field-label orbit space and to the corrected joint scalar quotient. OUR HypercubicDimension16RelationEvaluationEquivariance proves evaluation equivariant under the signed hypercubic group and shows that the Reynolds-averaged earlier four-field row, a vector of the earlier joint submodule, has averaged value 32/3 on the constant background, so the earlier joint submodule is not a space of relations. OUR HypercubicDimension16LeibnizFDIBPCochainBridge maps the finite cochains onto the corrected joint submodule, and OUR HypercubicDimension16LeibnizSourceSix proves that the full profile correction annihilates every corrected column outside source seven and that the two operators agree on the source bands seven and eight."
  nextObligation := "None inside this correction. The joint-interface obligations continue on the corrected joint submodule only: the earlier joint submodule contains an invariant non-relation and must not be used as a relation space. Background evaluations give certified non-membership, hence lower bounds, for the corrected scalar quotient."

/-- OUR crossing input for the stopping-scale step: stated, sufficient for
uniform clustering, and calibrated against the free-field barrier. -/
def yangMillsCrossingInputNode : YangMillsProofNode where
  id := "yang-mills.rg.crossing-input"
  status := .openGoal
  truthValue := ⟨0, 90⟩
  evidence := "CrossingInput records the bounds the stopping-scale step needs on the activities of a polymer representation over a block-product reference measure: per-block Kotecky-Preiss smallness with a positive rate and constants independent of the volume. That an actual stopped Wilson or RG measure admits such a representation is part of what the route must supply. CrossingInput.clustering proves that it implies exponential clustering of bounded block observables uniformly in the volume (PolymerGas.LatticeClustering, by Dobrushin's criterion, an influence recursion and conditioning, without a cluster expansion). CrossingInput.false_of_tendsto_dominating proves that no family satisfying it has bounded two-point functions whose limits dominate the free lattice Maxwell field-strength two-point function; currentYangMillsFreeMaxwell_barrier records that this function has no exponential bound in four and five dimensions, and CrossingInput.norm_fieldStrengthCorrelation_le_gaussian gives the domination for the bounded Gaussian observables exp(i sqrt t F01). The separation hypothesis is eventual in the volume for each fixed displacement; on the tori of StrongCouplingCrossing it holds for single-link supports with slope 1/d, offset 0 and support size one, so the torus specialization CalibrationSeparation.false_of_tendsto_dominating leaves only the convergence and domination of the two-point functions as hypotheses. The comparison lemma is an algebraic estimate on the free correlation with the factor 2 exp(t sigma^2) / t for 0 < t <= 1/2; the Gaussian covariance identity and the beta -> infinity limit that would place four-dimensional U(1) and the abelian components of five-dimensional SU(2) in this situation are not formalized. TwistDiagnostic adds a calibration that can be tested at finite coupling: if the untwisted and twisted representations share the Kotecky-Preiss bounds and the twist changes only the integrated activities of polymers that meet a cut and wind around the torus, the twist free energy is at most 2|Y| eps exp(-kappa D) (TwistDiagnostic.abs_logTwistRatio_le, from PolymerGas.Twist), and TwistDiagnostic.false_of_twistFreeEnergy_ge_of_poly_linear proves that on tori with cuts of polynomial size and linearly growing winding diameters no such family has twist free energy bounded below by a positive constant; the winding hypothesis is stated, not derived from a lattice measure. MarginalBlindness proves that one-site marginal criteria admitting a nonzero one-site covariance cannot by themselves imply clustering: the product and diagonal measures share their marginals, the first with no correlations at distinct sites and the second with the covariance at every pair. TwistCost proves that every twisted U(1) configuration costs at least 2 beta L^(d-4) in the twisted planes, and TwistEater that in SU(2) the anticommuting i sigma_1, i sigma_2 absorb the twist at zero action in the twisted planes, so the classical minima give SU(2) no action cost of the U(1) kind. goertzel_ym.tex records the numerical stopping-scale test, the hierarchical-lattice barrier, where U(1) confines too, and the candidate crossing mechanisms with Monte Carlo twist free energies."
  nextObligation := "Prove the crossing input for four-dimensional SU(2) at some block scale: control of the flow from beta_min to a strong effective coupling with Kotecky-Preiss-small activities, by a mechanism that fails for four-dimensional U(1) and five-dimensional SU(2)."

/-- OUR strong-coupling instance of the crossing input: it holds for Wilson-type
lattice measures at small coupling, uniformly in the volume. -/
def yangMillsCrossingInputStrongCouplingNode : YangMillsProofNode where
  id := "yang-mills.rg.crossing-input.strong-coupling"
  status := .checked
  truthValue := ⟨100, 95⟩
  evidence := "StrongCouplingCrossing.crossingInput proves CrossingInput for the connected plaquette activities of every Wilson-type measure on the tori (Z/(n+3))^d: independent link variables, any measurable four-link potential with values in [0, 2] (the Wilson action 1 - Re tr U_p / N for SU(N) with Haar measure is one), and 0 <= beta <= beta0 d = exp(-18) / (4 (4 d^2 + 1) (16 d^2 + 1)^2), with decay rate one and smallness exp(-1) at every volume. StrongCouplingCrossing.wilson_clustering gives exponential clustering of the Wilson expectations, uniformly in the volume. The proof uses the connected plaquette expansion (PolymerGas.PlaquetteExpansion, from PolymerGas.ConnectedDecomposition and PolymerGas.SupportRegrouping), the count of connected sets through a vertex, at most (Delta + 1)^(2n) (PolymerGas.ConnectedCount), and the explicit smallness threshold (PolymerGas.PlaquetteSmallness). So the crossing input holds where clustering is known and fails at the barrier theories. StrongCouplingTwist verifies the twist diagnostic there: for a group with a central involution z (the centre element -1 of SU(2)), a z-invariant probability measure and a measurable plaquette function psi in [0, 2], moving the twist is a measure-preserving change of variables and distant polymers do not see it, so the untwisted and twisted activities form a twist-compatible crossing family (StrongCouplingTwist.twistCompatibleCrossing), and the Wilson twist free energy -log (Z_tw / Z), both partition functions real Wilson integrals, tends to zero as the volume grows (StrongCouplingTwist.tendsto_twistFreeEnergy)."
  nextObligation := "None at strong coupling. The open crossing is the passage from weak coupling to this regime for four-dimensional SU(2)."

/-- OUR lattice reflection positivity of the Wilson-type measure (site
reflection), at every real coupling. -/
def yangMillsWilsonReflectionPositivityNode : YangMillsProofNode where
  id := "yang-mills.lattice.wilson-reflection-positivity"
  status := .checked
  truthValue := ⟨100, 95⟩
  evidence := "WilsonReflectionPositivity proves site reflection positivity of the Wilson-type measure on the tori (Z/2(n+2))^(d+1): for a group with measurable operations, an inversion-invariant probability measure on link variables, a bounded measurable class function psi with psi(g^-1) = psi(g), any real beta and every bounded measurable observable F of the links with both ends in the closed half 0 <= x0 <= n+2, the reflection form int conj(F o Theta) F prod_p exp(-beta psi(U_p)) is integrable, real and nonnegative (Lattice.bounded_wilson_reflection_positive), and so is its normalization, the Wilson expectation of the strong-coupling construction (Lattice.wilsonExpectation_reflection_positive). Theta reflects x0 -> -x0 and inverts the reflected temporal variables; the density factors as W+ (W+ o Theta) with fixed-plane plaquettes contributing half their action (Lattice.density_factorization), and conditioning on the plane variables turns the form into an integral of squared moduli (Lattice.wilson_conditional_square). This is the lattice Wilson-measure reflection positivity of the route; the reflection compatibility of its RG kernels is a separate, open input."
  nextObligation := "Reflection compatibility of the route's RG kernels; extension of the strong-coupling transfer gap from finite to compact gauge groups."

/-- OUR strong-coupling transfer-matrix gap for finite gauge groups, uniform in
the spatial volume. -/
def yangMillsStrongCouplingTransferGapNode : YangMillsProofNode where
  id := "yang-mills.lattice.strong-coupling-transfer-gap"
  status := .checked
  truthValue := ⟨100, 95⟩
  evidence := "StrongCouplingTransferGap.WilsonFinite.uniform_transfer_gap proves, for every finite gauge group, every class function psi with psi(g^-1) = psi(g) and values in [0, 2], and 0 <= beta <= beta0 (d + 1), that there is a mass m > 0 such that for every spatial side the Wilson transfer matrix (temporal links summed, half of each spatial action on either side) has a positive leading eigenvalue lambda0 with |lambda_j / lambda0| <= exp(-m) for every other eigenvalue, on the full spatial state space. Wilson expectations on rectangular tori are exact cyclic products of the transfer matrix (WilsonFinite.wilsonExpectation_eq_cycle), time-slice clustering from the strong-coupling crossing input has a rate independent of both extents, with a prefactor growing with the spatial volume that disappears in the time-power limit (Rectangular.slice_clustering), and the finite-dimensional spectral theorem converts the bound on squared traces into the gap (Spectral.absolute_gap_of_squared_correlations). This is a lattice mass gap at strong coupling, not the continuum Yang-Mills mass gap."
  nextObligation := "None at strong coupling for finite groups. Compact groups need an infinite-dimensional spectral argument; the continuum problem needs the open crossing and the continuum limit."

/-- Conditional OS reconstruction scaffold for the continuum endpoint. -/
def yangMillsContinuumOSConditionalScaffoldNode : YangMillsProofNode where
  id := "yang-mills.continuum-os-reconstruction-conditional"
  status := .checked
  truthValue := ⟨100, 96⟩
  evidence := "BenYMContinuumOSConditional.continuumMassGap is an abstract conditional endpoint: its carried bridge supplies lattice mass gap and exponential clustering, after which OS reflection positivity and a Kirk-style reconstruction machine yield HasSpectralMassGap. The legacy numerical contraction inside that wrapper is not an actual-map Wilson constant certificate."
  nextObligation := "First derive the actual Wilson RG constant and recursion; then prove the bridge to lattice gap/clustering, Wilson-measure reflection positivity for the same lattice family, and OS reconstruction/subsequential-limit machinery."

/-- Five-input completion steelman for Ben's current Yang-Mills route. -/
def yangMillsCompletionSteelmanNode : YangMillsProofNode where
  id := "yang-mills.completion-steelman"
  status := .checked
  truthValue := ⟨100, 94⟩
  evidence := "currentYangMillsCompletionSteelmanRows classifies the five completion inputs. The v14 extraction/recombination constant is refuted as written, the July blueprint is audited guidance, and support, two-marked identity, KP/RP, and the actual Wilson RG recursion remain explicit construction obligations."
  nextObligation := "OUR unpadded carrier and coordinate-free joint relation quotient continue the repaired route. Complete its full relation census, sparse dual conditioning, Wilson-functional analytic coordinates, and rooted cumulant estimate before instantiating the remaining completion inputs."

/-- The current route audit does not construct the full continuum object. -/
def yangMillsConstructiveQFTNode : YangMillsProofNode where
  id := "yang-mills.constructive-qft"
  status := .constructiveGateUncleared
  truthValue := ⟨0, 95⟩
  evidence := "currentYangMillsConstructiveStatus_unrepresentedChecks, currentYangMillsConstructiveDependency_packet, currentYangMillsConstructiveWorldInterface_packet, and currentYangMillsMassGapPromotionGate_refuted record that continuum measure, Euclidean covariance, reflection positivity, OS reconstruction, and Hamiltonian mass-gap transfer are not represented for the RG/extraction route; the route supplies only a finite RG/extraction ledger and misses the required constructive challenge-world interfaces."
  nextObligation := "Replace each unrepresented constructive check with a checked construction or a precise route refutation in dependency order, including the continuum measure, covariance, reflection-positivity, OS, and Hamiltonian challenge-world interfaces, before advertising a mass-gap endpoint."

/-- Finite canaries for the continuum-measure interface gate. -/
def yangMillsContinuumMeasureCanaryNode : YangMillsProofNode where
  id := "yang-mills.constructive-qft.continuum-measure-canaries"
  status := .checked
  truthValue := ⟨100, 97⟩
  evidence := "yangMillsContinuumMeasure_bool_guardrails checks that the local finite gate requires lattice-field sampler, tightness, and limit interfaces; sampler-only, tightness-without-limit, and limit-without-tightness evidence all remain blocked."
  nextObligation := "Do not promote finite lattice samples to downstream covariance or OS gates without both tightness and a continuum-measure limit."

/-- Finite canaries for the Euclidean-covariance interface gate. -/
def yangMillsEuclideanCovarianceCanaryNode : YangMillsProofNode where
  id := "yang-mills.constructive-qft.euclidean-covariance-canaries"
  status := .checked
  truthValue := ⟨100, 97⟩
  evidence := "yangMillsEuclideanCovariance_bool_guardrails checks that the local finite gate requires both Euclidean action and measure-preservation interfaces, and that covariance interfaces do not bypass the continuum-measure prerequisite."
  nextObligation := "Do not promote covariance action, measure preservation, or both covariance interfaces to OS reconstruction without the upstream continuum-measure gate."

/-- Finite canaries for the constructive-QFT/OS interface gate. -/
def yangMillsOSGateCanaryNode : YangMillsProofNode where
  id := "yang-mills.constructive-qft.os-gate-canaries"
  status := .checked
  truthValue := ⟨100, 97⟩
  evidence := "The OS-gate canary packet records that a toy route with every constructive interface supplied clears the promotion gate, while the current finite RG/extraction ledger and an OS-only interface toy route do not clear the full constructive-QFT interface layer."
  nextObligation := "Do not use finite RG evidence or OS reconstruction interfaces alone as a substitute for continuum measure, Euclidean covariance, reflection positivity, and Hamiltonian mass-gap transfer."

/-- Finite canaries for the reflection-positivity interface gate. -/
def yangMillsReflectionPositivityCanaryNode : YangMillsProofNode where
  id := "yang-mills.constructive-qft.reflection-positivity-canaries"
  status := .checked
  truthValue := ⟨100, 97⟩
  evidence := "yangMillsReflectionPositivity_bool_guardrails checks that the local finite gate requires both the reflection-positive functional and cone interfaces; sample nonnegativity, functional-only, and cone-only evidence all remain blocked."
  nextObligation := "Do not promote sample positivity or one-sided reflection data to OS reconstruction without both reflection-positivity interfaces and the upstream continuum/covariance gates."

/-- The current RG/extraction route fails the combined continuum mass-gap promotion gate. -/
def yangMillsMassGapPromotionGateNode : YangMillsProofNode where
  id := "yang-mills.mass-gap-promotion-gate"
  status := .constructiveGateUncleared
  truthValue := ⟨0, 99⟩
  evidence := "currentYangMillsMassGapPromotionGate_refuted records that the RG/extraction route fails all three promotion layers: constructive verdicts, dependency order, and constructive challenge-world interfaces."
  nextObligation := "Do not promote finite RG/extraction evidence to a continuum mass-gap endpoint unless the constructive checks, dependency order, and challenge-world interfaces all clear."

/-- The final mass-gap endpoint remains an open goal in this lane. -/
def yangMillsMassGapEndpointNode : YangMillsProofNode where
  id := "yang-mills.mass-gap-endpoint"
  status := .openGoal
  truthValue := ⟨0, 95⟩
  evidence := "currentYangMillsMassGapEndpoint_blockedByConstructiveGate blocks promotion from the audited RG/extraction surfaces to a continuum mass-gap endpoint, and currentYangMillsConstructiveDependency_packet, currentYangMillsConstructiveWorldInterface_packet, and currentYangMillsMassGapPromotionGate_refuted record that the constructive checks, OS/Hamiltonian transfer prerequisites, and interfaces are absent."
  nextObligation := "Connect the RG and extraction surfaces to a genuine continuum mass-gap statement only after the constructive-QFT gate, OS/Hamiltonian transfer dependency packet, challenge-world interface packet, and mass-gap promotion gate clear."

/-- Central Yang-Mills route nodes currently tracked by the live lane. -/
def currentYangMillsProofNodes : List YangMillsProofNode :=
  [ yangMillsLiveSurfaceNode
  , yangMillsRegressionSurfaceNode
  , yangMillsSameConstantLowerEvenExtractionNode
  , yangMillsExtractionConstantErratumNode
  , yangMillsPostponedIBPRepairNode
  , yangMillsDimension16O9WilsonCensusNode
  , yangMillsHypercubicQuarticCensusNode
  , yangMillsHypercubicDimension16PaddedCensusNode
  , yangMillsJointPhysicalRelationNode
  , yangMillsCommutatorLeibnizCorrectionNode
  , yangMillsCrossingInputNode
  , yangMillsCrossingInputStrongCouplingNode
  , yangMillsWilsonReflectionPositivityNode
  , yangMillsStrongCouplingTransferGapNode
  , yangMillsContinuumOSConditionalScaffoldNode
  , yangMillsCompletionSteelmanNode
  , yangMillsConstructiveQFTNode
  , yangMillsContinuumMeasureCanaryNode
  , yangMillsEuclideanCovarianceCanaryNode
  , yangMillsOSGateCanaryNode
  , yangMillsReflectionPositivityCanaryNode
  , yangMillsMassGapPromotionGateNode
  , yangMillsMassGapEndpointNode
  ]

theorem currentYangMillsProofNodes_nonempty : currentYangMillsProofNodes ≠ [] := by
  simp [currentYangMillsProofNodes]

theorem yangMillsConstructiveQFTNode_constructiveGateUncleared :
    yangMillsConstructiveQFTNode.status = .constructiveGateUncleared := by
  rfl

theorem yangMillsSameConstantLowerEvenExtractionNode_refuted :
    yangMillsSameConstantLowerEvenExtractionNode.status = .refuted := by
  rfl

theorem yangMillsExtractionConstantErratumNode_refuted :
    yangMillsExtractionConstantErratumNode.status = .refuted := by
  rfl

theorem yangMillsPostponedIBPRepairNode_checked :
    yangMillsPostponedIBPRepairNode.status = .checked := by
  rfl

theorem yangMillsDimension16O9WilsonCensusNode_refuted :
    yangMillsDimension16O9WilsonCensusNode.status = .refuted := by
  rfl

theorem yangMillsHypercubicQuarticCensusNode_checked :
    yangMillsHypercubicQuarticCensusNode.status = .checked := by
  rfl

theorem yangMillsHypercubicDimension16PaddedCensusNode_refuted :
    yangMillsHypercubicDimension16PaddedCensusNode.status = .refuted := by
  rfl

theorem yangMillsJointPhysicalRelationNode_checked :
    yangMillsJointPhysicalRelationNode.status = .checked := by
  rfl

/-- OUR repaired finite relation packet is a lower bound inside the genuine
joint invariant relation submodule for either relation policy. -/
theorem currentYangMillsJointPhysicalRelation_packet
    (policy : PhysicalRelationPolicy) :
    11558 ≤ Module.finrank ℚ (jointInvariantRelationSubmodule policy) := by
  exact jointInvariantRelationSubmodule_rank_lower_bound_fieldFiveCommutator policy

#print axioms currentYangMillsJointPhysicalRelation_packet

theorem yangMillsCommutatorLeibnizCorrectionNode_checked :
    yangMillsCommutatorLeibnizCorrectionNode.status = .checked := by
  rfl

/-- OUR certified lower bound for the Leibniz-corrected joint invariant
relation submodule, for either relation policy. -/
theorem currentYangMillsLeibnizJointPhysicalRelation_packet
    (policy : PhysicalRelationPolicy) :
    11558 ≤ Module.finrank ℚ
      (HypercubicDimension16LeibnizRelationOperator.leibnizJointInvariantRelationSubmodule
        policy) :=
  HypercubicDimension16LeibnizJointRank.leibnizJointInvariantRelationSubmodule_rank_lower_bound_fieldFiveCommutator
    policy

#print axioms currentYangMillsLeibnizJointPhysicalRelation_packet

/-- The earlier four-field commutator row is not a consequence of the field
identities: it does not vanish on some gauge background. -/
theorem currentYangMillsEarlierCommutatorRow_not_fieldIdentity :
    ∃ bg : HypercubicDimension16BackgroundCalculus.GaugeBackground ℚ,
      HypercubicDimension16CommutatorRowEvaluation.relationValue bg
        (HypercubicDimension16CovariantCommutator.covariantCommutatorRow fieldFourSite) ≠ 0 :=
  HypercubicDimension16CommutatorRowEvaluation.covariantCommutatorRow_fieldFour_not_fieldIdentity

#print axioms currentYangMillsEarlierCommutatorRow_not_fieldIdentity

/-- Every relation of the Leibniz-corrected operator integrates to zero on
every gauge background, and under the on-shell policy on every on-shell
background. -/
theorem currentYangMillsLeibnizRelations_integrate_to_zero
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (bg : HypercubicDimension16BackgroundCalculus.GaugeBackground S)
    {policy : PhysicalRelationPolicy}
    (hshell : policy = .onShell →
      HypercubicDimension16RelationRowSoundness.IsOnShell bg) :
    HypercubicDimension16LeibnizRelationOperator.leibnizPhysicalRelationSubmodule policy ≤
      LinearMap.ker (HypercubicDimension16RelationRowSoundness.integratedValue bg) :=
  HypercubicDimension16RelationRowSoundness.leibnizPhysicalRelationSubmodule_le_ker_integratedValue
    bg hshell

#print axioms currentYangMillsLeibnizRelations_integrate_to_zero

/-- Background evaluation vanishes on the corrected joint invariant relation
submodule, so it is a functional on the corrected joint scalar quotient. -/
theorem currentYangMillsLeibnizJointRelations_evaluate_to_zero
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (bg : HypercubicDimension16BackgroundCalculus.GaugeBackground S)
    {policy : PhysicalRelationPolicy}
    (hshell : policy = .onShell →
      HypercubicDimension16RelationRowSoundness.IsOnShell bg) :
    HypercubicDimension16LeibnizRelationOperator.leibnizJointInvariantRelationSubmodule
        policy ≤
      LinearMap.ker (HypercubicDimension16RelationEvaluationDescent.jointIntegratedValue bg) :=
  HypercubicDimension16RelationEvaluationDescent.leibnizJointInvariantRelationSubmodule_le_ker
    bg hshell

#print axioms currentYangMillsLeibnizJointRelations_evaluate_to_zero

/-- The earlier joint invariant relation submodule contains a vector that is
not a relation: its averaged value on the constant background is `32/3`. -/
theorem currentYangMillsEarlierJointSubmodule_contains_nonRelation :
    fieldFourInvariantCommutatorRow .offShell ∈ jointInvariantRelationSubmodule .offShell ∧
      HypercubicDimension16RelationEvaluationDescent.jointIntegratedValue
          HypercubicDimension16CommutatorRowEvaluation.defectBackground
          (fieldFourInvariantCommutatorRow .offShell) = 32 / 3 ∧
      fieldFourInvariantCommutatorRow .offShell ∉
        HypercubicDimension16LeibnizRelationOperator.leibnizJointInvariantRelationSubmodule
          .offShell :=
  ⟨(HypercubicDimension16RelationEvaluationEquivariance.fieldFourInvariantRow_not_mem_leibnizJointInvariantRelationSubmodule).1,
    HypercubicDimension16RelationEvaluationEquivariance.jointIntegratedValue_defect_fieldFourInvariantRow,
    (HypercubicDimension16RelationEvaluationEquivariance.fieldFourInvariantRow_not_mem_leibnizJointInvariantRelationSubmodule).2⟩

#print axioms currentYangMillsEarlierJointSubmodule_contains_nonRelation

/-- OUR finite cochains surject onto the corrected joint relation submodule. -/
theorem currentYangMillsLeibnizFDIBPCochainBridge_surjective
    (policy : PhysicalRelationPolicy) :
    Function.Surjective
      (HypercubicDimension16LeibnizFDIBPCochainBridge.leibnizFDIBPCochainToJointRelation
        policy) :=
  HypercubicDimension16LeibnizFDIBPCochainBridge.leibnizFDIBPCochainToJointRelation_surjective
    policy

#print axioms currentYangMillsLeibnizFDIBPCochainBridge_surjective

/-- OUR full profile correction annihilates every column of the corrected
operator outside the source-seven band. -/
theorem currentYangMillsLeibnizProfileCorrection_zero_of_source_ne_seven
    (policy : PhysicalRelationPolicy)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ)
    (hseven : physicalRelationGeneratorSourceFieldCount generator ≠ ourSevenFieldCount) :
    ourCycleProfileInvariantTraceOrderCorrection
      (HypercubicDimension16LeibnizRelationOperator.leibnizOrbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient)) = 0 :=
  HypercubicDimension16LeibnizSourceSix.ourCycleProfileInvariantTraceOrderCorrection_leibnizPhysicalRelation_zero_of_source_ne_seven
    policy generator coefficient hseven

#print axioms currentYangMillsLeibnizProfileCorrection_zero_of_source_ne_seven

/-- The free-field barrier in four and five dimensions: the field-strength
two-point function of the free lattice Maxwell field has no exponential bound. -/
theorem currentYangMillsFreeMaxwell_barrier :
    (∀ K μ : ℝ, 0 < μ → ¬ ∀ k : Fin (1 + 3) → ℤ,
      ‖FreeMaxwellNonClustering.fieldStrengthCorrelation (n := 1) k‖ ≤
        K * Real.exp (-μ * ∑ i, |((k i : ℤ) : ℝ)|)) ∧
    (∀ K μ : ℝ, 0 < μ → ¬ ∀ k : Fin (2 + 3) → ℤ,
      ‖FreeMaxwellNonClustering.fieldStrengthCorrelation (n := 2) k‖ ≤
        K * Real.exp (-μ * ∑ i, |((k i : ℤ) : ℝ)|)) :=
  ⟨fun K μ hμ => FreeMaxwellNonClustering.not_exponentialDecay_fieldStrengthCorrelation K μ hμ,
    fun K μ hμ => FreeMaxwellNonClustering.not_exponentialDecay_fieldStrengthCorrelation K μ hμ⟩

#print axioms currentYangMillsFreeMaxwell_barrier

/-- The crossing input holds at strong coupling for every Wilson-type measure,
below a positive threshold depending only on the dimension. -/
theorem currentYangMillsStrongCoupling_crossingInput (d : ℕ) {E : Type*} [MeasurableSpace E]
    (base : E) {φ : (Fin 4 → E) → ℝ} (hφ : Measurable φ) (hφ0 : ∀ v, 0 ≤ φ v)
    (hφ2 : ∀ v, φ v ≤ 2) :
    0 < StrongCouplingCrossing.beta0 d ∧
      ∀ β : ℝ, 0 ≤ β → β ≤ StrongCouplingCrossing.beta0 d →
        CrossingInput.CrossingInput (StrongCouplingCrossing.Link d) E
          (StrongCouplingCrossing.activity d base φ β) :=
  ⟨StrongCouplingCrossing.beta0_pos d, fun _ hβ hβ0 =>
    StrongCouplingCrossing.crossingInput d base hφ hφ0 hφ2 hβ hβ0⟩

#print axioms currentYangMillsStrongCoupling_crossingInput

/-- At strong coupling the centre-twist free energy of Wilson-type measures with a
central involution tends to zero as the volume grows. -/
theorem currentYangMillsStrongCoupling_twistFreeEnergy (d : ℕ) {E : Type*} [Group E]
    [MeasurableSpace E] [MeasurableMul₂ E] [MeasurableInv E]
    (ν₀ : MeasureTheory.Measure E) [MeasureTheory.IsProbabilityMeasure ν₀]
    {z : E} (hz : ∀ g, z * g = g * z) (hzz : z * z = 1)
    (hν : ν₀.map (fun g => z * g) = ν₀) {ψ : E → ℝ} (hψ : Measurable ψ)
    (hψ0 : ∀ g, 0 ≤ ψ g) (hψ2 : ∀ g, ψ g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ StrongCouplingCrossing.beta0 (d + 2)) :
    Filter.Tendsto (fun n => StrongCouplingTwist.twistFreeEnergy d n ν₀ z ψ β)
      Filter.atTop (nhds 0) :=
  StrongCouplingTwist.tendsto_twistFreeEnergy d ν₀ hz hzz hν hψ hψ0 hψ2 hβ hβ0

#print axioms currentYangMillsStrongCoupling_twistFreeEnergy

/-- Site reflection positivity of the Wilson-type measure at every real coupling,
for bounded observables of the closed positive half: the reflection form is
integrable, real and nonnegative. -/
theorem currentYangMillsWilson_reflectionPositive {d n : ℕ} {E : Type*} [Group E]
    [MeasurableSpace E] [MeasurableMul₂ E] [MeasurableInv E]
    (ν₀ : MeasureTheory.Measure E) [MeasureTheory.IsProbabilityMeasure ν₀]
    (hν : ν₀.map Inv.inv = ν₀) {ψ : E → ℝ} (hψ : Measurable ψ) {C : ℝ}
    (hbound : ∀ g, |ψ g| ≤ C) (β : ℝ) (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h)
    (hinv : ∀ g, ψ g⁻¹ = ψ g)
    {F : (WilsonReflectionPositivity.Lattice.Link d n → E) → ℂ} (hF : Measurable F) {M : ℝ}
    (hFb : ∀ ω, ‖F ω‖ ≤ M) (hlocal : WilsonReflectionPositivity.Lattice.HalfLocal F) :
    MeasureTheory.Integrable (fun ω => (starRingEnd ℂ)
        (F (WilsonReflectionPositivity.Lattice.theta ω)) * F ω *
        (WilsonReflectionPositivity.Lattice.density ψ β ω : ℂ))
      (MeasureTheory.Measure.pi (fun _ : WilsonReflectionPositivity.Lattice.Link d n => ν₀)) ∧
    (∫ ω, (starRingEnd ℂ) (F (WilsonReflectionPositivity.Lattice.theta ω)) * F ω *
        (WilsonReflectionPositivity.Lattice.density ψ β ω : ℂ)
        ∂MeasureTheory.Measure.pi (fun _ : WilsonReflectionPositivity.Lattice.Link d n => ν₀)).im = 0 ∧
    0 ≤ (∫ ω, (starRingEnd ℂ) (F (WilsonReflectionPositivity.Lattice.theta ω)) * F ω *
        (WilsonReflectionPositivity.Lattice.density ψ β ω : ℂ)
        ∂MeasureTheory.Measure.pi (fun _ : WilsonReflectionPositivity.Lattice.Link d n => ν₀)).re :=
  WilsonReflectionPositivity.Lattice.bounded_wilson_reflection_positive ν₀ hν hψ hbound β
    hclass hinv hF hFb hlocal

#print axioms currentYangMillsWilson_reflectionPositive

/-- OUR finite `F,D`/IBP relation cochains surject onto the honest joint
relation submodule under either relation policy. -/
theorem currentYangMillsFDIBPCochainJointBridge_surjective
    (policy : PhysicalRelationPolicy) :
    Function.Surjective (ourFDIBPCochainToJointRelation policy) :=
  ourFDIBPCochainToJointRelation_surjective policy

#print axioms currentYangMillsFDIBPCochainJointBridge_surjective

/-- OUR complete certified physical three-cut cochain family lies in the
kernel of the repaired trace-cycle-profile coordinate. -/
theorem currentYangMillsPhysicalThreeCut_profileCoordinate_kernel
    (policy : PhysicalRelationPolicy)
    (cochain : OurFundamentalTraceCochainSpace) :
    ourInvariantTraceCycleProfileCoordinate
      ((ourFundamentalTraceToJointRelation policy cochain).1).1 = 0 :=
  ourInvariantTraceCycleProfileCoordinate_fundamentalTrace_zero policy cochain

#print axioms currentYangMillsPhysicalThreeCut_profileCoordinate_kernel

/-- OUR complete certified physical three-cut cochain family lies in the
kernel of the separate three-coordinate correction. -/
theorem currentYangMillsPhysicalThreeCut_threeCoordinate_kernel
    (policy : PhysicalRelationPolicy)
    (cochain : OurFundamentalTraceCochainSpace) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      ((ourFundamentalTraceToJointRelation policy cochain).1).1 = 0 :=
  ourThreeCoordinateInvariantTraceOrderCorrection_fundamentalTrace_zero
    policy cochain

#print axioms currentYangMillsPhysicalThreeCut_threeCoordinate_kernel

/-- OUR full current cycle-profile correction annihilates the complete
certified physical three-cut cochain family.  This remains a theorem about
one realized family, not about every member of the joint relation submodule. -/
theorem currentYangMillsPhysicalThreeCut_cycleProfileCorrection_kernel
    (policy : PhysicalRelationPolicy)
    (cochain : OurFundamentalTraceCochainSpace) :
    ourCycleProfileInvariantTraceOrderCorrection
      ((ourFundamentalTraceToJointRelation policy cochain).1).1 = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_fundamentalTrace_zero
    policy cochain

#print axioms currentYangMillsPhysicalThreeCut_cycleProfileCorrection_kernel

/-- OUR complete seven-placement physical adjacent trace-anticommutator
cochain family lies in the kernel of the full current cycle-profile
correction.  This is a second realized trace-family block, not a statement
about all trace-anticommutator carriers or the full joint relation submodule. -/
theorem currentYangMillsPhysicalTraceAnticommutator_cycleProfileCorrection_kernel
    (policy : PhysicalRelationPolicy)
    (cochain : OurPhysicalTraceAnticommutatorCochainSpace) :
    ourCycleProfileInvariantTraceOrderCorrection
      ((ourPhysicalTraceAnticommutatorToJointRelation policy cochain).1).1 = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_physicalTraceAnticommutator_zero
    policy cochain

#print axioms currentYangMillsPhysicalTraceAnticommutator_cycleProfileCorrection_kernel

set_option maxRecDepth 100000 in
/-- OUR current profile correction annihilates the concrete differential
calibration packet at the invariant coordinate-free relation boundary.  The
named invariant rows already belong to their indicated joint relation
submodules; this theorem does not assert that they span either submodule. -/
theorem currentYangMillsCycleProfileDifferential_invariantPacket :
    (∀ policy : PhysicalRelationPolicy,
      (ourInvariantCommutatorRow policy ∈
          jointInvariantRelationSubmodule policy ∧
        ourCycleProfileInvariantTraceOrderCorrection
          (ourInvariantCommutatorRow policy).1 = 0) ∧
      (ourInvariantSecondIBPRow policy ∈
          jointInvariantRelationSubmodule policy ∧
        ourCycleProfileInvariantTraceOrderCorrection
          (ourInvariantSecondIBPRow policy).1 = 0) ∧
      (ourInvariantBianchiRow policy ∈
          jointInvariantRelationSubmodule policy ∧
        ourCycleProfileInvariantTraceOrderCorrection
          (ourInvariantBianchiRow policy).1 = 0)) ∧
    (ourInvariantIBPRow ∈ jointInvariantRelationSubmodule .offShell ∧
      ourCycleProfileInvariantTraceOrderCorrection ourInvariantIBPRow.1 = 0) ∧
    (ourInvariantEOMRow ∈ jointInvariantRelationSubmodule .onShell ∧
      ourCycleProfileInvariantTraceOrderCorrection ourInvariantEOMRow.1 = 0) ∧
    (∀ (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator),
      ourCycleProfileInvariantTraceOrderCorrection
        (exactFieldOrbitReynolds
          (orbitPhysicalRelationOperator policy
            (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1))) =
          0) := by
  refine ⟨?_, ⟨ourInvariantIBPRow_mem,
    ourCycleProfileInvariantTraceOrderCorrection_invariantIBP_zero⟩,
    ⟨ourInvariantEOMRow_mem,
      ourCycleProfileInvariantTraceOrderCorrection_invariantEOM_zero⟩, ?_⟩
  · intro policy
    exact ⟨⟨ourInvariantCommutatorRow_mem policy,
        ourCycleProfileInvariantTraceOrderCorrection_invariantCommutator_zero policy⟩,
      ⟨ourInvariantSecondIBPRow_mem policy,
        ourCycleProfileInvariantTraceOrderCorrection_invariantSecondIBP_zero policy⟩,
      ⟨ourInvariantBianchiRow_mem policy,
        ourCycleProfileInvariantTraceOrderCorrection_invariantBianchi_zero policy⟩⟩
  · intro policy generator
    exact ourCycleProfileInvariantTraceOrderCorrection_invariantLiftedTraceGenerator_zero
      policy generator

#print axioms currentYangMillsCycleProfileDifferential_invariantPacket

/-- OUR current three-coordinate trace-order correction is certified not to
annihilate the whole coordinate-free invariant relation submodule: a genuine
polarized `SU(2)` trace-anticommutator row supplies the exact failing member
under either policy. -/
theorem currentYangMillsThreeCoordinateTraceRepair_traceAnticommutator_obstruction
    (policy : PhysicalRelationPolicy) :
    ¬ ∀ value : exactFieldOrbitInvariantSubmodule,
      value ∈ jointInvariantRelationSubmodule policy →
        ourThreeCoordinateInvariantTraceOrderCorrection value.1 = 0 :=
  ourThreeCoordinateInvariantTraceOrderCorrection_not_annihilates_joint policy

#print axioms currentYangMillsThreeCoordinateTraceRepair_traceAnticommutator_obstruction

/-- OUR fourth coordinate gates the derivative-axis character by the
relabel-invariant two-cycle count of the trace permutation.  It repairs the
canonical polarized `SU(2)` trace-anticommutator row both before and after
Reynolds averaging; this is a finite known-family result, not full descent
through the joint relation submodule. -/
theorem currentYangMillsFourCoordinateTraceRepair_traceAnticommutator
    (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 ∧
    ourFourCoordinateInvariantTraceOrderCorrection
      (ourInvariantTraceAnticommutatorRow policy).1 = 0 :=
  ⟨ourFourCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator_zero
      policy,
    ourFourCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero
      policy⟩

#print axioms currentYangMillsFourCoordinateTraceRepair_traceAnticommutator

/-- OUR fifth coordinate adds the relabel-invariant six-cycle gate.  The
four-coordinate functional has an exact nonzero residual on the canonical
fundamental three-cut row; the fifth functional kills that physical and
Reynolds-averaged row while retaining the earlier trace-anticommutator
cancellation.  This remains a named-family calculation, not full relation
submodule descent. -/
theorem currentYangMillsFiveCoordinateTraceRepair_fundamentalThreeCut
    (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      (-1 / 2 : ℚ) •
        HypercubicDimension16IncomingCommutatorTraceCertificate.literalIncomingCommutatorClass ∧
    ourFourCoordinateInvariantTraceOrderCorrection
      (ourInvariantFundamentalThreeCutRow policy).1 ≠ 0 ∧
    ourFiveCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) = 0 ∧
    ourFiveCoordinateInvariantTraceOrderCorrection
      (ourInvariantFundamentalThreeCutRow policy).1 = 0 ∧
    ourFiveCoordinateInvariantTraceOrderCorrection
      (ourInvariantTraceAnticommutatorRow policy).1 = 0 ∧
    ourInvariantFundamentalThreeCutRow policy ∈
      jointInvariantRelationSubmodule policy := by
  exact ⟨ourFourCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut
      policy,
    ourFourCoordinateInvariantTraceOrderCorrection_invariantFundamentalThreeCut_ne_zero
      policy,
    ourFiveCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero
      policy,
    ourFiveCoordinateInvariantTraceOrderCorrection_invariantFundamentalThreeCut_zero
      policy,
    ourFiveCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero
      policy,
    ourInvariantFundamentalThreeCutRow_mem policy⟩

#print axioms currentYangMillsFiveCoordinateTraceRepair_fundamentalThreeCut

/-- OUR trace-cycle profile is forced by the four finite topology types and
the polarized trace-anticommutator equation.  Its numerator vanishes on all
`210` ordered distinct three-cut labels.  The signed-`H(4)` coordinate lift
is presently certified on the two displayed canonical physical rows and their
Reynolds members only; this does not assert identification of all `210`
abstract placements with physical relation rows or descent through all of the
joint relation submodule. -/
theorem currentYangMillsCycleProfileTraceRepair_twoCanonicalRows
    (policy : PhysicalRelationPolicy) :
    ourDistinctThreeCutLabels.length = 210 ∧
    (∀ numerator ∈ ourDistinctThreeCutProfileNumerators, numerator = 0) ∧
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) = 0 ∧
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) = 0 ∧
    ourCycleProfileInvariantTraceOrderCorrection
      (ourInvariantFundamentalThreeCutRow policy).1 = 0 ∧
    ourCycleProfileInvariantTraceOrderCorrection
      (ourInvariantTraceAnticommutatorRow policy).1 = 0 := by
  exact ⟨ourDistinctThreeCutLabels_card,
    ourDistinctThreeCutProfileNumerators_all_zero,
    ourCycleProfileInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero policy,
    ourCycleProfileInvariantTraceOrderCorrection_ourTraceAnticommutator_zero policy,
    ourCycleProfileInvariantTraceOrderCorrection_invariantFundamentalThreeCut_zero policy,
    ourCycleProfileInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero policy⟩

#print axioms currentYangMillsCycleProfileTraceRepair_twoCanonicalRows

/-- The existing actual Cartan Wilson eighth jet cannot itself be a
trace-order-faithful quotient coordinate.  This leaves open, but makes
necessary, a larger noncommutative Wilson-coordinate system. -/
theorem currentYangMillsCartanWilsonTraceOrderFaithfulnessNoGo
    (a : ℝ) :
    ¬ Nonempty (OurIncomingTraceOrderFaithfulCartanWilsonCoordinate a) ∧
    ¬ Nonempty (OurTraceOrderFaithfulCartanWilsonCoordinate a) := by
  exact ⟨no_ourIncomingTraceOrderFaithfulCartanWilsonCoordinate a,
    no_ourTraceOrderFaithfulCartanWilsonCoordinate a⟩

#print axioms currentYangMillsCartanWilsonTraceOrderFaithfulnessNoGo

/-- OUR local trace-order repair packet: its quotient coordinate kills the
complete coupled physical commutator for either policy, retains the isolated
eight-field trace signal, and cannot be replaced by the eight-field trace
coordinate alone. -/
theorem currentYangMillsTraceOrderLocalRepair_packet
    (policy : PhysicalRelationPolicy) :
    ourTraceOrderAwareLocalQuotientCoordinate
      (coupledIncomingQuotientMap
        (exactFieldSevenEightProjection
          (orbitPhysicalRelationOperator policy
            (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)))) = 0 ∧
      ourTraceOrderAwareLocalQuotientCoordinate
        (coupledIncomingQuotientMap
          (0, coupledIncomingCommutatorVector.2)) ≠ 0 ∧
      ¬ ∃ descended : CoupledIncomingQuotient →ₗ[ℚ]
          FieldEightPhysicalTraceQuotient,
        descended.comp coupledIncomingQuotientMap =
          ourFieldEightTraceOnlyCoordinate := by
  exact ⟨ourTraceOrderAwareLocalQuotientCoordinate_physicalCommutator_zero policy,
    ourTraceOrderAwareLocalQuotientCoordinate_detects_eightComponent_ne_zero,
    no_ourFieldEightTraceOnlyCoordinate_descent⟩

#print axioms currentYangMillsTraceOrderLocalRepair_packet

/-- OUR finite trace-order completion supplies all `98` exact ordinary trace
coordinates after the forced local compensation.  It remains a local coupled
quotient construction, not full-relation descent or an analytic Wilson jet. -/
theorem currentYangMillsTraceOrderCoordinateCompletion_packet
    (policy : PhysicalRelationPolicy) :
    Function.Injective ourPhysicalTraceCoordinatePacket ∧
    ourCoupledTraceOrderCoordinatePacket
      (coupledIncomingQuotientMap
        (exactFieldSevenEightProjection
          (orbitPhysicalRelationOperator policy
            (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)))) = 0 ∧
    ourCoupledTraceOrderCoordinatePacket
      (coupledIncomingQuotientMap
        (0, coupledIncomingCommutatorVector.2)) ≠ 0 := by
  exact ⟨ourPhysicalTraceCoordinatePacket_injective,
    ourCoupledTraceOrderCoordinatePacket_physicalCommutator_zero policy,
    ourCoupledTraceOrderCoordinatePacket_eightComponent_ne_zero⟩

#print axioms currentYangMillsTraceOrderCoordinateCompletion_packet

/-- OUR two-coordinate invariant trace-order repair packet.  It repairs the
explicit IBP failure of the first invariant coordinate and records concrete
commutator, Bianchi, on-shell EOM, and lifted derivative-free trace checks.
It does not assert annihilation of every physical relation. -/
theorem currentYangMillsTraceOrderInvariantRepair_packet
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 ∧
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 ∧
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)) = 0 ∧
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 ∧
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 := by
  exact ⟨ourTwoCoordinateInvariantTraceOrderCorrection_ourCommutator_zero policy,
    ourTwoCoordinateInvariantTraceOrderCorrection_ourIBP_zero,
    ourTwoCoordinateInvariantTraceOrderCorrection_liftedTraceGenerator_zero
      policy generator,
    ourTwoCoordinateInvariantTraceOrderCorrection_ourBianchi_zero policy,
    ourTwoCoordinateInvariantTraceOrderCorrection_ourEOM_zero⟩

#print axioms currentYangMillsTraceOrderInvariantRepair_packet

/-- OUR three-coordinate invariant trace-order repair packet.  The second
explicit IBP row is a certified obstruction to the two-coordinate functional;
the third coordinate repairs that row while retaining all earlier displayed
physical and Reynolds-averaged relation checks.  It does not assert full
relation-range descent. -/
theorem currentYangMillsTraceOrderThreeCoordinateRepair_packet
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) ≠ 0 ∧
    ourThreeCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 ∧
    ourInvariantSecondIBPRow policy ∈ jointInvariantRelationSubmodule policy ∧
    ourThreeCoordinateInvariantTraceOrderCorrection
      (ourInvariantSecondIBPRow policy).1 = 0 ∧
    ourThreeCoordinateInvariantTraceOrderCorrection
      (ourInvariantCommutatorRow policy).1 = 0 ∧
    ourThreeCoordinateInvariantTraceOrderCorrection ourInvariantIBPRow.1 = 0 ∧
    ourThreeCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)) = 0 ∧
    ourThreeCoordinateInvariantTraceOrderCorrection
      (ourInvariantBianchiRow policy).1 = 0 ∧
    ourThreeCoordinateInvariantTraceOrderCorrection ourInvariantEOMRow.1 = 0 := by
  exact ⟨ourTwoCoordinateInvariantTraceOrderCorrection_ourSecondIBP_ne_zero policy,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourSecondIBP_zero policy,
    ourInvariantSecondIBPRow_mem policy,
    ourThreeCoordinateInvariantTraceOrderCorrection_invariantSecondIBP_zero policy,
    ourThreeCoordinateInvariantTraceOrderCorrection_invariantCommutator_zero policy,
    ourThreeCoordinateInvariantTraceOrderCorrection_invariantIBP_zero,
    ourThreeCoordinateInvariantTraceOrderCorrection_liftedTraceGenerator_zero
      policy generator,
    ourThreeCoordinateInvariantTraceOrderCorrection_invariantBianchi_zero policy,
    ourThreeCoordinateInvariantTraceOrderCorrection_invariantEOM_zero⟩

#print axioms currentYangMillsTraceOrderThreeCoordinateRepair_packet

theorem yangMillsContinuumOSConditionalScaffoldNode_checked :
    yangMillsContinuumOSConditionalScaffoldNode.status = .checked := by
  rfl

theorem yangMillsCompletionSteelmanNode_checked :
    yangMillsCompletionSteelmanNode.status = .checked := by
  rfl

theorem yangMillsMassGapPromotionGateNode_constructiveGateUncleared :
    yangMillsMassGapPromotionGateNode.status = .constructiveGateUncleared := by
  rfl

theorem yangMillsOSGateCanaryNode_checked :
    yangMillsOSGateCanaryNode.status = .checked := by
  rfl

theorem yangMillsContinuumMeasureCanaryNode_checked :
    yangMillsContinuumMeasureCanaryNode.status = .checked := by
  rfl

theorem yangMillsReflectionPositivityCanaryNode_checked :
    yangMillsReflectionPositivityCanaryNode.status = .checked := by
  rfl

theorem yangMillsMassGapEndpointNode_open :
    yangMillsMassGapEndpointNode.status = .openGoal := by
  rfl

theorem currentYangMillsRGCrux_sameConstantEvenBelowSixteenRoute_refuted
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ : ℝ} :
    ¬ SameConstantEvenBelowSixteenGapRouteCertificate A corr Δ := by
  exact not_sameConstantEvenBelowSixteenGapRouteCertificate

theorem currentYangMillsRGCrux_atLeast2048EvenBelowSixteenRoute_refuted
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {corr : SpatialCorrelation} {Δ C : ℝ} :
    ¬ AtLeast2048EvenBelowSixteenGapRouteCertificate A corr Δ C := by
  exact not_atLeast2048EvenBelowSixteenGapRouteCertificate

theorem currentYangMillsRGCrux_lowerEvenExtraction_arithmetic_packet :
    HasExtendedExtractionContraction 2224 2 16 ∧
      ¬ HasExtendedExtractionContraction 2224 2 14 := by
  exact
    ⟨rgContraction_2224_two_sixteen,
      not_rgContraction_2224_two_fourteen⟩

theorem currentYangMillsExtractionConstantAdjudication_packet :
    ¬ V14LiteralExtractionRecombinationClaims ∧
      f5DisplayedConstantAtBlockTwo = 33152 ∧
      proposedMajorantLedgerConstant = (5544 : ℝ) / 5 ∧
      HasTwoSourceBootstrapSlack proposedMajorantLedgerConstant 2 15 ∧
      (∀ D : ℕ, D ≤ 14 →
        ¬ HasTwoSourceBootstrapSlack proposedMajorantLedgerConstant 2 D) := by
  exact
    ⟨not_v14LiteralExtractionRecombinationClaims,
      f5DisplayedConstantAtBlockTwo_eq,
      proposedMajorantLedgerConstant_eq,
      proposedMajorantLedger_twoSourceSlack_two_fifteen,
      fun _ hD =>
        not_proposedMajorantLedger_twoSourceSlack_of_depth_le_fourteen hD⟩

/-- The earlier source-only audit remains true: the relation policies
disagree, the supplied coordinate certificate is incomplete, and the
advertised bound is not derived.  It is superseded as a campaign verdict by
the stronger SU(2) actual-lattice symmetry no-go. -/
theorem currentYangMillsDimension16CoordinateCertificate_packet :
    (¬ V14Dimension16SourceCertificateComplete) ∧
      v14F4RelationPolicy ≠ v14O9RelationPolicy ∧
      (¬ V14LiteralDimension16ExtractionBound) ∧
      v14Dimension16CertificateStatus .extractionConstant = .notDerived ∧
      v14Dimension16CertificateStatus .wilsonRecursionConstant = .notDerived :=
  v14Dimension16WilsonExtraction_asWritten_obstructed

/-- The completed MOVE-5 transfer audit: neither surviving radial extractor is
the canonical `F,D` cutoff, and neither EOM policy admits the as-written
ordinary block-functional realization or an RG-compatible extension. -/
theorem currentYangMillsFDQuotientTransferNoGo_packet :
    (¬ AssociatedRadialImplementsCanonicalCutoff) ∧
      (¬ IndependentRadialImplementsCanonicalCutoff) ∧
      (¬ Nonempty (V14FaithfulFDTransferSocket .onShell)) ∧
      (¬ Nonempty (V14FaithfulFDTransferSocket .offShell)) ∧
      (¬ Nonempty (V14RGCompatibleFDTransferSocket .onShell)) ∧
      (¬ Nonempty (V14RGCompatibleFDTransferSocket .offShell)) := by
  exact
    ⟨not_associatedRadialImplementsCanonicalCutoff,
      not_independentRadialImplementsCanonicalCutoff,
      no_faithfulFDTransferSocket .onShell,
      no_faithfulFDTransferSocket .offShell,
      no_rgCompatibleFDTransferSocket .onShell,
      no_rgCompatibleFDTransferSocket .offShell⟩

/-- Constructed MOVE-6 replacement packet.  The exact block cancellation,
coordinate certificate, and conditional arithmetic are proved; the analytic
transfer rows remain visibly open in `boundaryCochainRouteMatrix`. -/
theorem currentYangMillsPostponedIBPRepair_packet :
    (LinearMap.range
        (sharedBoundaryCoboundaryLinear ActionLaplacianCensus)).mkQ
      assembledActionLaplacianBulk = 0 ∧
    RepairedBoundaryCochainExtractionCertificate ∧
    repairedBoundaryCochainRecursionBudget = (5544 : ℝ) / 5 ∧
    HasTwoSourceBootstrapSlack
      repairedBoundaryCochainRecursionBudget 2 15 :=
  v14_postponedIBP_boundaryCochain_constructed_packet

theorem currentYangMillsExtractionConstant_hypotheticalThreshold_packet :
    ∀ {C : ℝ}, (8192 : ℝ) ≤ C →
      ¬ HasExtendedExtractionContraction C 2 16 := by
  intro C hC
  exact hypothetical_not_rgContraction_two_sixteen_of_constant_ge_8192 hC

theorem currentYangMillsBenRoute_reflectionPositivityOpenInput :
    currentYangMillsConstructiveWorldInterfaces.missingFor .reflectionPositivity =
      [.reflectionPositiveFunctional, .reflectionPositiveCone] := by
  simpa [YangMillsConstructiveCheck.requiredWorldInterfaces]
    using currentYangMillsConstructiveWorldInterfaces_missing_reflectionPositivity

theorem currentYangMillsContinuumOSConditional_packet
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : LinearOperator H} {Δ : ℝ} {corr : SpatialCorrelation}
    (D : BenYMContinuumOSConditional A Δ corr) :
    HasTwoSourceBootstrapSlack D.lambdaBridge.Ctrue 2 16 ∧
      HasSpectralMassGap A Δ ∧
        0 < Δ ∧
          currentYangMillsConstructiveWorldInterfaces.missingFor
              .reflectionPositivity =
            [.reflectionPositiveFunctional, .reflectionPositiveCone] ∧
          preprints2025041268Verdict = .notRouteBlocking ∧
          yangMillsContinuumOSConditionalScaffoldNode.status = .checked ∧
          yangMillsMassGapEndpointNode.status = .openGoal := by
  have hpacket := D.reductionPacket
  exact
    ⟨hpacket.1,
      hpacket.2.1,
      hpacket.2.2,
      currentYangMillsBenRoute_reflectionPositivityOpenInput,
      preprints2025041268Verdict_notRouteBlocking,
      yangMillsContinuumOSConditionalScaffoldNode_checked,
      yangMillsMassGapEndpointNode_open⟩

theorem currentYangMillsCompletionSteelman_packet :
    recombinationConstantSteelmanRow.verdict = .refutedOrInconsistent ∧
      supportRecurrenceSteelmanRow.verdict = .reducedToNamedAssumption ∧
      twoMarkedIdentitySteelmanRow.verdict = .reducedToNamedAssumption ∧
      kpWilsonSteelmanRow.verdict = .reducedToNamedAssumption ∧
      realRGRecursionSteelmanRow.verdict = .reducedToNamedAssumption ∧
      proBlueprintSteelmanRow.verdict = .verified ∧
      ¬ V14LiteralExtractionRecombinationClaims ∧
      HasTwoSourceBootstrapSlack proposedMajorantLedgerConstant 2 15 ∧
      (∀ D : ℕ, D ≤ 14 →
        ¬ HasTwoSourceBootstrapSlack proposedMajorantLedgerConstant 2 D) ∧
      yangMillsCompletionSteelmanNode.status = .checked := by
  exact
    ⟨recombinationConstantSteelman_refutedOrInconsistent,
      supportRecurrenceSteelman_reduced,
      twoMarkedIdentitySteelman_reduced,
      kpWilsonSteelman_reduced,
      realRGRecursionSteelman_reduced,
      proBlueprintSteelman_verified,
      not_v14LiteralExtractionRecombinationClaims,
      proposedMajorantLedger_twoSourceSlack_two_fifteen,
      fun _ hD =>
        not_proposedMajorantLedger_twoSourceSlack_of_depth_le_fourteen hD,
      yangMillsCompletionSteelmanNode_checked⟩

theorem currentYangMillsConstructiveDependency_packet :
    currentYangMillsConstructiveStatus.representedChecks = [] ∧
      currentYangMillsConstructiveStatus.missingPrerequisitesFor
        .euclideanCovariance = [.continuumMeasure] ∧
      currentYangMillsConstructiveStatus.missingPrerequisitesFor
        .reflectionPositivity = [.continuumMeasure] ∧
      currentYangMillsConstructiveStatus.missingPrerequisitesFor
        .osReconstruction = [.euclideanCovariance, .reflectionPositivity] ∧
      currentYangMillsConstructiveStatus.missingPrerequisitesFor
        .hamiltonianMassGapTransfer = [.osReconstruction] := by
  exact
    ⟨currentYangMillsConstructiveStatus_representedChecks,
      currentYangMillsConstructiveStatus_missingPrerequisites_euclideanCovariance,
      currentYangMillsConstructiveStatus_missingPrerequisites_reflectionPositivity,
      currentYangMillsConstructiveStatus_missingPrerequisites_osReconstruction,
      currentYangMillsConstructiveStatus_missingPrerequisites_hamiltonianTransfer⟩

theorem currentYangMillsConstructiveWorldInterface_packet :
    currentYangMillsConstructiveWorldInterfaces.supplied =
        [.finiteRGExtractionLedger] ∧
      currentYangMillsConstructiveWorldInterfaces.missingFor .continuumMeasure =
        YangMillsConstructiveCheck.continuumMeasure.requiredWorldInterfaces ∧
      currentYangMillsConstructiveWorldInterfaces.missingFor .euclideanCovariance =
        YangMillsConstructiveCheck.euclideanCovariance.requiredWorldInterfaces ∧
      currentYangMillsConstructiveWorldInterfaces.missingFor .reflectionPositivity =
        YangMillsConstructiveCheck.reflectionPositivity.requiredWorldInterfaces ∧
      currentYangMillsConstructiveWorldInterfaces.missingFor .osReconstruction =
        YangMillsConstructiveCheck.osReconstruction.requiredWorldInterfaces ∧
      currentYangMillsConstructiveWorldInterfaces.missingFor
          .hamiltonianMassGapTransfer =
        YangMillsConstructiveCheck.hamiltonianMassGapTransfer.requiredWorldInterfaces := by
  exact
    ⟨currentYangMillsConstructiveWorldInterfaces_supplied,
      currentYangMillsConstructiveWorldInterfaces_missing_continuumMeasure,
      currentYangMillsConstructiveWorldInterfaces_missing_euclideanCovariance,
      currentYangMillsConstructiveWorldInterfaces_missing_reflectionPositivity,
      currentYangMillsConstructiveWorldInterfaces_missing_osReconstruction,
      currentYangMillsConstructiveWorldInterfaces_missing_hamiltonianTransfer⟩

theorem currentYangMillsConstructiveDependency_and_worldInterface_packet :
    currentYangMillsConstructiveStatus.representedChecks = [] ∧
      currentYangMillsConstructiveWorldInterfaces.supplied =
        [.finiteRGExtractionLedger] ∧
      currentYangMillsConstructiveWorldInterfaces.missingFor .continuumMeasure =
        YangMillsConstructiveCheck.continuumMeasure.requiredWorldInterfaces ∧
      currentYangMillsConstructiveWorldInterfaces.missingFor .euclideanCovariance =
        YangMillsConstructiveCheck.euclideanCovariance.requiredWorldInterfaces ∧
      currentYangMillsConstructiveWorldInterfaces.missingFor .reflectionPositivity =
        YangMillsConstructiveCheck.reflectionPositivity.requiredWorldInterfaces ∧
      currentYangMillsConstructiveWorldInterfaces.missingFor .osReconstruction =
        YangMillsConstructiveCheck.osReconstruction.requiredWorldInterfaces ∧
      currentYangMillsConstructiveWorldInterfaces.missingFor
          .hamiltonianMassGapTransfer =
        YangMillsConstructiveCheck.hamiltonianMassGapTransfer.requiredWorldInterfaces ∧
      currentYangMillsConstructiveStatus.missingPrerequisitesFor
        .hamiltonianMassGapTransfer = [.osReconstruction] := by
  exact
    ⟨currentYangMillsConstructiveStatus_representedChecks,
      currentYangMillsConstructiveWorldInterfaces_supplied,
      currentYangMillsConstructiveWorldInterfaces_missing_continuumMeasure,
      currentYangMillsConstructiveWorldInterfaces_missing_euclideanCovariance,
      currentYangMillsConstructiveWorldInterfaces_missing_reflectionPositivity,
      currentYangMillsConstructiveWorldInterfaces_missing_osReconstruction,
      currentYangMillsConstructiveWorldInterfaces_missing_hamiltonianTransfer,
      currentYangMillsConstructiveStatus_missingPrerequisites_hamiltonianTransfer⟩

theorem currentYangMillsMassGapPromotionGate_refuted :
    ¬ currentYangMillsConstructiveStatus.ClearsForMassGap ∧
      ¬ currentYangMillsConstructiveStatus.ClearsDependencyOrder ∧
      ¬ currentYangMillsConstructiveWorldInterfaces.ClearsAll ∧
      ¬ currentYangMillsMassGapPromotionGate.ClearsAll ∧
      currentYangMillsConstructiveStatus.representedChecks = [] ∧
      currentYangMillsConstructiveWorldInterfaces.supplied =
        [.finiteRGExtractionLedger] := by
  exact
    ⟨currentYangMillsConstructiveStatus_not_cleared,
      currentYangMillsConstructiveStatus_dependencyOrder_not_cleared,
      currentYangMillsConstructiveWorldInterfaces_not_cleared,
      currentYangMillsMassGapPromotionGate_not_cleared,
      currentYangMillsConstructiveStatus_representedChecks,
      currentYangMillsConstructiveWorldInterfaces_supplied⟩

theorem currentYangMillsMassGapEndpoint_blockedByConstructiveGate :
    yangMillsMassGapEndpointNode.status = .openGoal ∧
      ¬ currentYangMillsConstructiveStatus.ClearsForMassGap ∧
      ¬ currentYangMillsMassGapPromotionGate.ClearsAll ∧
      currentYangMillsConstructiveStatus.representedChecks = [] ∧
      currentYangMillsConstructiveWorldInterfaces.supplied =
        [.finiteRGExtractionLedger] ∧
      currentYangMillsConstructiveStatus.missingPrerequisitesFor
        .hamiltonianMassGapTransfer = [.osReconstruction] ∧
      currentYangMillsConstructiveStatus.unrepresentedChecks =
        [ .continuumMeasure
        , .euclideanCovariance
        , .reflectionPositivity
        , .osReconstruction
        , .hamiltonianMassGapTransfer
        ] := by
  exact
    ⟨yangMillsMassGapEndpointNode_open,
      currentYangMillsConstructiveStatus_not_cleared,
      currentYangMillsMassGapPromotionGate_not_cleared,
      currentYangMillsConstructiveStatus_representedChecks,
      currentYangMillsConstructiveWorldInterfaces_supplied,
      currentYangMillsConstructiveStatus_missingPrerequisites_hamiltonianTransfer,
      currentYangMillsConstructiveStatus_unrepresentedChecks⟩

end YangMills
end QuantumTheory
end Mettapedia
