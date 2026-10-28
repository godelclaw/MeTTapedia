import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyBKMBridge

/-!
# Navier-Stokes scaling status

This module records the cheap-falsification surface for route steps that try to
promote finite-energy or BKM-style evidence into a global regularity claim.  A
route is not scaling-cleared until its critical-norm, supercritical-upgrade,
and averaged-equation compatibility checks have explicit Lean evidence.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Scaling/no-go checks that a Navier-Stokes global-regularity route must confront. -/
inductive NavierScalingCheck where
  | criticalNorm
  | supercriticalUpgrade
  | averagedEquationCompatibility
deriving DecidableEq, Repr

/-- Diagnostic world families for scaling cheap-falsification. -/
inductive NavierScalingWorld where
  | criticalBoundary
  | supercriticalFamily
  | averagedEquation
deriving DecidableEq, Repr

/-- Route interfaces needed to test a global-regularity promotion against the
Navier-Stokes scaling challenge worlds. -/
inductive NavierScalingWorldInterface where
  | finiteEnergyL2Diagnostic
  | criticalInitialDataFamily
  | criticalNormControlWitness
  | supercriticalConcentrationFamily
  | scaleInvariantUpgradeWitness
  | averagedEquationWorldFamily
  | averagedMomentumWitness
  | reynoldsStressClosureWitness
  | energyInequalityTransport
  | criticalScalingTransport
deriving DecidableEq, Repr

/-- Obligations needed before an averaged-equation route can be treated as
compatible with the Navier-Stokes target rather than only with a model equation. -/
inductive NavierAveragedEquationObligation where
  | averagedMomentumEquation
  | reynoldsStressClosure
  | energyInequalityCompatibility
  | criticalScalingCompatibility
deriving DecidableEq, Repr

/-- The challenge-world interface that would witness one averaged-equation obligation. -/
def NavierAveragedEquationObligation.requiredWorldInterface :
    NavierAveragedEquationObligation → NavierScalingWorldInterface
  | .averagedMomentumEquation => .averagedMomentumWitness
  | .reynoldsStressClosure => .reynoldsStressClosureWitness
  | .energyInequalityCompatibility => .energyInequalityTransport
  | .criticalScalingCompatibility => .criticalScalingTransport

/-- The canonical diagnostic world associated with a scaling/no-go check. -/
def NavierScalingCheck.challengeWorld : NavierScalingCheck → NavierScalingWorld
  | .criticalNorm => .criticalBoundary
  | .supercriticalUpgrade => .supercriticalFamily
  | .averagedEquationCompatibility => .averagedEquation

/-- Interfaces required before a route can claim to have passed one scaling
challenge world.  The finite-energy `L^2` diagnostic is useful bookkeeping, but
it is not one of the critical-world clearance interfaces below. -/
def NavierScalingCheck.requiredWorldInterfaces :
    NavierScalingCheck → List NavierScalingWorldInterface
  | .criticalNorm =>
      [ .criticalInitialDataFamily
      , .criticalNormControlWitness
      ]
  | .supercriticalUpgrade =>
      [ .supercriticalConcentrationFamily
      , .scaleInvariantUpgradeWitness
      ]
  | .averagedEquationCompatibility =>
      [ .averagedEquationWorldFamily
      , .averagedMomentumWitness
      , .reynoldsStressClosureWitness
      , .energyInequalityTransport
      , .criticalScalingTransport
      ]

/-- Current route verdict for one scaling/no-go check. -/
inductive NavierScalingVerdict where
  | cleared
  | blocked
  | notRepresented
deriving DecidableEq, Repr

/-- Coarse scaling regime for a velocity `L^p` diagnostic norm. -/
inductive NavierScalingRegime where
  | supercritical
  | critical
  | subcritical
deriving DecidableEq, Repr

/-- A diagnostic scaling regime is at least critical when it is not supercritical. -/
def NavierScalingRegime.clearsCriticalPromotion : NavierScalingRegime → Bool
  | .supercritical => false
  | .critical => true
  | .subcritical => true

/-- Boolean clearance flag for a scaling/no-go verdict. -/
def NavierScalingVerdict.clears : NavierScalingVerdict → Bool
  | .cleared => true
  | .blocked => false
  | .notRepresented => false

/-- Scaling/no-go status for a named Navier-Stokes route candidate. -/
structure NavierScalingStatus where
  routeKey : String
  criticalNorm : NavierScalingVerdict
  supercriticalUpgrade : NavierScalingVerdict
  averagedEquationCompatibility : NavierScalingVerdict
deriving Repr

/-- Route-local representation status for averaged-equation compatibility. -/
structure NavierAveragedEquationCompatibilityStatus where
  routeKey : String
  required : List NavierAveragedEquationObligation
  represented : List NavierAveragedEquationObligation
deriving Repr

/-- Route-local representation status for the world interfaces demanded by
the scaling challenge worlds. -/
structure NavierScalingRouteWorldInterfaces where
  routeKey : String
  supplied : List NavierScalingWorldInterface
deriving Repr

/-- A route is scaling-cleared only when all three required checks clear. -/
def NavierScalingStatus.ClearsAll (status : NavierScalingStatus) : Prop :=
  status.criticalNorm.clears &&
    status.supercriticalUpgrade.clears &&
    status.averagedEquationCompatibility.clears = true

/-- Averaged-equation compatibility clears only when every required obligation
has an explicitly represented route witness. -/
def NavierAveragedEquationCompatibilityStatus.Clears
    (status : NavierAveragedEquationCompatibilityStatus) : Prop :=
  status.required.all (fun obligation => decide (obligation ∈ status.represented)) = true

/-- Averaged-equation obligations that still lack represented route witnesses. -/
def NavierAveragedEquationCompatibilityStatus.missingObligations
    (status : NavierAveragedEquationCompatibilityStatus) :
    List NavierAveragedEquationObligation :=
  status.required.filter fun obligation =>
    !decide (obligation ∈ status.represented)

/-- A missing averaged-equation obligation is required by the route. -/
theorem NavierAveragedEquationCompatibilityStatus.required_of_mem_missingObligations
    {status : NavierAveragedEquationCompatibilityStatus}
    {obligation : NavierAveragedEquationObligation}
    (h : obligation ∈ status.missingObligations) :
    obligation ∈ status.required := by
  have h' : obligation ∈ status.required ∧ obligation ∉ status.represented := by
    simpa [NavierAveragedEquationCompatibilityStatus.missingObligations] using h
  exact h'.1

/-- A missing averaged-equation obligation has not been represented by the route. -/
theorem NavierAveragedEquationCompatibilityStatus.not_represented_of_mem_missingObligations
    {status : NavierAveragedEquationCompatibilityStatus}
    {obligation : NavierAveragedEquationObligation}
    (h : obligation ∈ status.missingObligations) :
    ¬ obligation ∈ status.represented := by
  have h' : obligation ∈ status.required ∧ obligation ∉ status.represented := by
    simpa [NavierAveragedEquationCompatibilityStatus.missingObligations] using h
  exact h'.2

/-- Required scaling-world interfaces not supplied by the route. -/
def NavierScalingRouteWorldInterfaces.missingFor
    (interfaces : NavierScalingRouteWorldInterfaces)
    (check : NavierScalingCheck) : List NavierScalingWorldInterface :=
  check.requiredWorldInterfaces.filter fun requirement =>
    !decide (requirement ∈ interfaces.supplied)

/-- A missing challenge-world interface is required by the corresponding check. -/
theorem NavierScalingRouteWorldInterfaces.required_of_mem_missingFor
    {interfaces : NavierScalingRouteWorldInterfaces}
    {check : NavierScalingCheck}
    {requirement : NavierScalingWorldInterface}
    (h : requirement ∈ interfaces.missingFor check) :
    requirement ∈ check.requiredWorldInterfaces := by
  have h' : requirement ∈ check.requiredWorldInterfaces ∧ requirement ∉ interfaces.supplied := by
    simpa [NavierScalingRouteWorldInterfaces.missingFor] using h
  exact h'.1

/-- A missing challenge-world interface has not been supplied by the route. -/
theorem NavierScalingRouteWorldInterfaces.not_supplied_of_mem_missingFor
    {interfaces : NavierScalingRouteWorldInterfaces}
    {check : NavierScalingCheck}
    {requirement : NavierScalingWorldInterface}
    (h : requirement ∈ interfaces.missingFor check) :
    ¬ requirement ∈ interfaces.supplied := by
  have h' : requirement ∈ check.requiredWorldInterfaces ∧ requirement ∉ interfaces.supplied := by
    simpa [NavierScalingRouteWorldInterfaces.missingFor] using h
  exact h'.2

/-- A route has represented the scaling challenge-world interface layer only
when every scaling/no-go check has no missing interface requirement. -/
def NavierScalingRouteWorldInterfaces.ClearsAll
    (interfaces : NavierScalingRouteWorldInterfaces) : Prop :=
  interfaces.missingFor .criticalNorm = [] ∧
    interfaces.missingFor .supercriticalUpgrade = [] ∧
    interfaces.missingFor .averagedEquationCompatibility = []

/-- Three-layer gate for promoting finite-energy/BKM evidence into a candidate
global-regularity route. -/
structure NavierRegularityPromotionGate where
  routeKey : String
  scalingStatus : NavierScalingStatus
  worldInterfaces : NavierScalingRouteWorldInterfaces
  averagedEquationStatus : NavierAveragedEquationCompatibilityStatus
deriving Repr

/-- The global-regularity promotion gate clears only when the scaling verdicts,
challenge-world interfaces, and averaged-equation compatibility all clear. -/
def NavierRegularityPromotionGate.ClearsAll
    (gate : NavierRegularityPromotionGate) : Prop :=
  gate.scalingStatus.ClearsAll ∧
    gate.worldInterfaces.ClearsAll ∧
    gate.averagedEquationStatus.Clears

/-- Verdict lookup for one named scaling/no-go check. -/
def NavierScalingStatus.verdictFor
    (status : NavierScalingStatus) : NavierScalingCheck → NavierScalingVerdict
  | .criticalNorm => status.criticalNorm
  | .supercriticalUpgrade => status.supercriticalUpgrade
  | .averagedEquationCompatibility => status.averagedEquationCompatibility

/-- Checks whose current route verdict is still not represented by Lean evidence. -/
def NavierScalingStatus.unrepresentedChecks
    (status : NavierScalingStatus) : List NavierScalingCheck :=
  (if status.criticalNorm = .notRepresented then [.criticalNorm] else []) ++
    (if status.supercriticalUpgrade = .notRepresented then [.supercriticalUpgrade] else []) ++
    (if status.averagedEquationCompatibility = .notRepresented then
      [.averagedEquationCompatibility]
    else
      [])

/-- A cleared route has no unrepresented scaling/no-go checks. -/
theorem NavierScalingStatus.unrepresentedChecks_eq_nil_of_clearsAll
    {status : NavierScalingStatus} (h : status.ClearsAll) :
    status.unrepresentedChecks = [] := by
  cases status with
  | mk routeKey criticalNorm supercriticalUpgrade averagedEquationCompatibility =>
      cases criticalNorm <;>
        cases supercriticalUpgrade <;>
          cases averagedEquationCompatibility <;>
            simp [NavierScalingStatus.ClearsAll,
              NavierScalingStatus.unrepresentedChecks,
              NavierScalingVerdict.clears] at h ⊢

/-- A nonempty unrepresented-check list prevents scaling clearance. -/
theorem NavierScalingStatus.not_clearsAll_of_unrepresentedChecks_ne_nil
    {status : NavierScalingStatus} (h : status.unrepresentedChecks ≠ []) :
    ¬ status.ClearsAll := by
  intro hclear
  exact
    h (NavierScalingStatus.unrepresentedChecks_eq_nil_of_clearsAll
      (status := status) hclear)

/-- Numerator of the parabolic Navier-Stokes velocity `L^p` scaling exponent
`1 - 3 / p`, tracked as `p - 3` to avoid analytic side conditions here. -/
def velocityLpScalingNumerator (p : Nat) : Int :=
  Int.ofNat p - 3

/-- Coarse `L^p` velocity scaling regime in three spatial dimensions. -/
def velocityLpScalingRegime (p : Nat) : NavierScalingRegime :=
  if p < 3 then
    .supercritical
  else if p = 3 then
    .critical
  else
    .subcritical

/-- Boolean gate for using an `L^p` velocity diagnostic as a critical-or-better
promotion surface. -/
def velocityLpClearsCriticalPromotion (p : Nat) : Bool :=
  (velocityLpScalingRegime p).clearsCriticalPromotion

/-- The finite-energy velocity norm is the `L^2` diagnostic norm. -/
def finiteEnergyVelocityLpIndex : Nat := 2

/-- The scale-critical velocity diagnostic norm is `L^3`. -/
def criticalVelocityLpIndex : Nat := 3

/-- The three diagnostic world families used for the current Navier route audit. -/
def currentNavierScalingChallengeWorlds : List NavierScalingWorld :=
  [ .criticalBoundary
  , .supercriticalFamily
  , .averagedEquation
  ]

/-- Current averaged-equation obligations for the finite-energy/BKM route. -/
def currentNavierAveragedEquationCompatibilityObligations :
    List NavierAveragedEquationObligation :=
  [ .averagedMomentumEquation
  , .reynoldsStressClosure
  , .energyInequalityCompatibility
  , .criticalScalingCompatibility
  ]

/-- The current finite-energy/BKM route is blocked at the critical-norm gate and
the supercritical-upgrade gate; averaged-equation compatibility is still not
represented by Lean evidence. -/
def currentNavierEnergyBKMScalingStatus : NavierScalingStatus where
  routeKey := "navier.energy-bkm-finite-energy-route"
  criticalNorm := .blocked
  supercriticalUpgrade := .blocked
  averagedEquationCompatibility := .notRepresented

/-- The current finite-energy/BKM route has not supplied any averaged-equation
compatibility witnesses. -/
def currentNavierEnergyBKMAveragedEquationCompatibilityStatus :
    NavierAveragedEquationCompatibilityStatus where
  routeKey := "navier.energy-bkm-finite-energy-route"
  required := currentNavierAveragedEquationCompatibilityObligations
  represented := []

/-- Sanity-check status: all averaged-equation obligations are represented.
This is a bookkeeping example, not the current Navier route. -/
def exampleNavierAveragedEquationCompatibilityClearedStatus :
    NavierAveragedEquationCompatibilityStatus where
  routeKey := "navier.example-averaged-equation-cleared"
  required := currentNavierAveragedEquationCompatibilityObligations
  represented := currentNavierAveragedEquationCompatibilityObligations

/-- The current finite-energy/BKM route records its finite-energy `L^2`
diagnostic, but no critical challenge-world clearance interface. -/
def currentNavierEnergyBKMRouteWorldInterfaces :
    NavierScalingRouteWorldInterfaces where
  routeKey := "navier.energy-bkm-finite-energy-route"
  supplied := [ .finiteEnergyL2Diagnostic ]

/-- The current finite-energy/BKM route packaged as a global-regularity
promotion gate. -/
def currentNavierEnergyBKMRegularityPromotionGate :
    NavierRegularityPromotionGate where
  routeKey := "navier.energy-bkm-finite-energy-route"
  scalingStatus := currentNavierEnergyBKMScalingStatus
  worldInterfaces := currentNavierEnergyBKMRouteWorldInterfaces
  averagedEquationStatus := currentNavierEnergyBKMAveragedEquationCompatibilityStatus

theorem challengeWorld_criticalNorm :
    NavierScalingCheck.criticalNorm.challengeWorld = .criticalBoundary := by
  rfl

theorem challengeWorld_supercriticalUpgrade :
    NavierScalingCheck.supercriticalUpgrade.challengeWorld = .supercriticalFamily := by
  rfl

theorem challengeWorld_averagedEquationCompatibility :
    NavierScalingCheck.averagedEquationCompatibility.challengeWorld = .averagedEquation := by
  rfl

theorem requiredWorldInterfaces_criticalNorm :
    NavierScalingCheck.criticalNorm.requiredWorldInterfaces =
      [ .criticalInitialDataFamily
      , .criticalNormControlWitness
      ] := by
  rfl

theorem requiredWorldInterfaces_supercriticalUpgrade :
    NavierScalingCheck.supercriticalUpgrade.requiredWorldInterfaces =
      [ .supercriticalConcentrationFamily
      , .scaleInvariantUpgradeWitness
      ] := by
  rfl

theorem requiredWorldInterfaces_averagedEquationCompatibility :
    NavierScalingCheck.averagedEquationCompatibility.requiredWorldInterfaces =
      [ .averagedEquationWorldFamily
      , .averagedMomentumWitness
      , .reynoldsStressClosureWitness
      , .energyInequalityTransport
      , .criticalScalingTransport
      ] := by
  rfl

theorem requiredWorldInterface_averagedMomentumEquation :
    NavierAveragedEquationObligation.averagedMomentumEquation.requiredWorldInterface =
      .averagedMomentumWitness := by
  rfl

theorem requiredWorldInterface_mem_averagedEquationCompatibility
    (obligation : NavierAveragedEquationObligation) :
    obligation.requiredWorldInterface ∈
      NavierScalingCheck.averagedEquationCompatibility.requiredWorldInterfaces := by
  cases obligation <;>
    simp [NavierAveragedEquationObligation.requiredWorldInterface,
      NavierScalingCheck.requiredWorldInterfaces]

theorem currentNavierScalingChallengeWorlds_length :
    currentNavierScalingChallengeWorlds.length = 3 := by
  rfl

theorem currentNavierAveragedEquationCompatibilityObligations_length :
    currentNavierAveragedEquationCompatibilityObligations.length = 4 := by
  rfl

theorem currentNavierEnergyBKMScalingStatus_not_cleared :
    ¬ currentNavierEnergyBKMScalingStatus.ClearsAll := by
  simp [NavierScalingStatus.ClearsAll, NavierScalingVerdict.clears,
    currentNavierEnergyBKMScalingStatus]

theorem currentNavierEnergyBKMScalingStatus_criticalNorm_blocked :
    currentNavierEnergyBKMScalingStatus.criticalNorm = .blocked := by
  rfl

theorem currentNavierEnergyBKMScalingStatus_supercriticalUpgrade_blocked :
    currentNavierEnergyBKMScalingStatus.supercriticalUpgrade = .blocked := by
  rfl

theorem currentNavierEnergyBKMScalingStatus_averagedEquationCompatibility_notRepresented :
    currentNavierEnergyBKMScalingStatus.averagedEquationCompatibility = .notRepresented := by
  rfl

theorem currentNavierEnergyBKMScalingStatus_unrepresentedChecks :
    currentNavierEnergyBKMScalingStatus.unrepresentedChecks =
      [ .averagedEquationCompatibility ] := by
  simp [NavierScalingStatus.unrepresentedChecks, currentNavierEnergyBKMScalingStatus]

theorem currentNavierEnergyBKMAveragedEquationCompatibility_required :
    currentNavierEnergyBKMAveragedEquationCompatibilityStatus.required =
      currentNavierAveragedEquationCompatibilityObligations := by
  rfl

theorem currentNavierEnergyBKMAveragedEquationCompatibility_represented :
    currentNavierEnergyBKMAveragedEquationCompatibilityStatus.represented = [] := by
  rfl

theorem currentNavierEnergyBKMAveragedEquationCompatibility_missingObligations :
    currentNavierEnergyBKMAveragedEquationCompatibilityStatus.missingObligations =
      [ .averagedMomentumEquation
      , .reynoldsStressClosure
      , .energyInequalityCompatibility
      , .criticalScalingCompatibility
      ] := by
  simp [NavierAveragedEquationCompatibilityStatus.missingObligations,
    currentNavierEnergyBKMAveragedEquationCompatibilityStatus,
    currentNavierAveragedEquationCompatibilityObligations]

theorem currentNavierEnergyBKMAveragedEquationCompatibility_missing_averagedMomentumEquation :
    NavierAveragedEquationObligation.averagedMomentumEquation ∈
      currentNavierEnergyBKMAveragedEquationCompatibilityStatus.missingObligations := by
  simp [currentNavierEnergyBKMAveragedEquationCompatibility_missingObligations]

theorem currentNavierEnergyBKMAveragedEquationCompatibility_not_represented_averagedMomentumEquation :
    ¬ NavierAveragedEquationObligation.averagedMomentumEquation ∈
      currentNavierEnergyBKMAveragedEquationCompatibilityStatus.represented := by
  exact
    NavierAveragedEquationCompatibilityStatus.not_represented_of_mem_missingObligations
      currentNavierEnergyBKMAveragedEquationCompatibility_missing_averagedMomentumEquation

theorem exampleNavierAveragedEquationCompatibilityClearedStatus_clears :
    exampleNavierAveragedEquationCompatibilityClearedStatus.Clears := by
  simp [NavierAveragedEquationCompatibilityStatus.Clears,
    exampleNavierAveragedEquationCompatibilityClearedStatus,
    currentNavierAveragedEquationCompatibilityObligations]

theorem exampleNavierAveragedEquationCompatibilityClearedStatus_missingObligations :
    exampleNavierAveragedEquationCompatibilityClearedStatus.missingObligations = [] := by
  simp [NavierAveragedEquationCompatibilityStatus.missingObligations,
    exampleNavierAveragedEquationCompatibilityClearedStatus,
    currentNavierAveragedEquationCompatibilityObligations]

theorem currentNavierEnergyBKMRouteWorldInterfaces_supplied :
    currentNavierEnergyBKMRouteWorldInterfaces.supplied =
      [ .finiteEnergyL2Diagnostic ] := by
  rfl

theorem currentNavierEnergyBKMRouteWorldInterfaces_missing_criticalNorm :
    currentNavierEnergyBKMRouteWorldInterfaces.missingFor .criticalNorm =
      NavierScalingCheck.criticalNorm.requiredWorldInterfaces := by
  simp [NavierScalingRouteWorldInterfaces.missingFor,
    currentNavierEnergyBKMRouteWorldInterfaces,
    NavierScalingCheck.requiredWorldInterfaces]

theorem currentNavierEnergyBKMRouteWorldInterfaces_missing_supercriticalUpgrade :
    currentNavierEnergyBKMRouteWorldInterfaces.missingFor .supercriticalUpgrade =
      NavierScalingCheck.supercriticalUpgrade.requiredWorldInterfaces := by
  simp [NavierScalingRouteWorldInterfaces.missingFor,
    currentNavierEnergyBKMRouteWorldInterfaces,
    NavierScalingCheck.requiredWorldInterfaces]

theorem currentNavierEnergyBKMRouteWorldInterfaces_missing_averagedEquationCompatibility :
    currentNavierEnergyBKMRouteWorldInterfaces.missingFor .averagedEquationCompatibility =
      NavierScalingCheck.averagedEquationCompatibility.requiredWorldInterfaces := by
  simp [NavierScalingRouteWorldInterfaces.missingFor,
    currentNavierEnergyBKMRouteWorldInterfaces,
    NavierScalingCheck.requiredWorldInterfaces]

theorem currentNavierEnergyBKMRouteWorldInterfaces_missing_averagedMomentumWitness :
    NavierScalingWorldInterface.averagedMomentumWitness ∈
      currentNavierEnergyBKMRouteWorldInterfaces.missingFor .averagedEquationCompatibility := by
  simp [NavierScalingRouteWorldInterfaces.missingFor,
    currentNavierEnergyBKMRouteWorldInterfaces,
    NavierScalingCheck.requiredWorldInterfaces]

theorem currentNavierEnergyBKMRouteWorldInterfaces_not_supplied_averagedMomentumWitness :
    ¬ NavierScalingWorldInterface.averagedMomentumWitness ∈
      currentNavierEnergyBKMRouteWorldInterfaces.supplied := by
  exact
    NavierScalingRouteWorldInterfaces.not_supplied_of_mem_missingFor
      currentNavierEnergyBKMRouteWorldInterfaces_missing_averagedMomentumWitness

theorem currentNavierEnergyBKMRouteWorldInterfaces_not_cleared :
    ¬ currentNavierEnergyBKMRouteWorldInterfaces.ClearsAll := by
  intro hclears
  have hcrit := hclears.1
  rw [currentNavierEnergyBKMRouteWorldInterfaces_missing_criticalNorm] at hcrit
  simp [NavierScalingCheck.requiredWorldInterfaces] at hcrit

theorem currentNavierEnergyBKMAveragedEquationCompatibility_not_cleared :
    ¬ currentNavierEnergyBKMAveragedEquationCompatibilityStatus.Clears := by
  simp [NavierAveragedEquationCompatibilityStatus.Clears,
    currentNavierEnergyBKMAveragedEquationCompatibilityStatus,
    currentNavierAveragedEquationCompatibilityObligations]

theorem currentNavierEnergyBKMScalingStatus_unrepresentedChecks_nonempty :
    currentNavierEnergyBKMScalingStatus.unrepresentedChecks ≠ [] := by
  simp [currentNavierEnergyBKMScalingStatus_unrepresentedChecks]

theorem currentNavierEnergyBKMScalingStatus_not_cleared_from_unrepresentedChecks :
    ¬ currentNavierEnergyBKMScalingStatus.ClearsAll := by
  exact
    NavierScalingStatus.not_clearsAll_of_unrepresentedChecks_ne_nil
      currentNavierEnergyBKMScalingStatus_unrepresentedChecks_nonempty

theorem currentNavierEnergyBKMRegularityPromotionGate_layers :
    currentNavierEnergyBKMRegularityPromotionGate.scalingStatus =
        currentNavierEnergyBKMScalingStatus ∧
      currentNavierEnergyBKMRegularityPromotionGate.worldInterfaces =
        currentNavierEnergyBKMRouteWorldInterfaces ∧
      currentNavierEnergyBKMRegularityPromotionGate.averagedEquationStatus =
        currentNavierEnergyBKMAveragedEquationCompatibilityStatus := by
  exact ⟨rfl, rfl, rfl⟩

theorem currentNavierEnergyBKMRegularityPromotionGate_not_cleared :
    ¬ currentNavierEnergyBKMRegularityPromotionGate.ClearsAll := by
  intro hclears
  exact currentNavierEnergyBKMScalingStatus_not_cleared hclears.1

theorem velocityLpScalingNumerator_two :
    velocityLpScalingNumerator 2 = -1 := by
  norm_num [velocityLpScalingNumerator]

theorem velocityLpScalingNumerator_three :
    velocityLpScalingNumerator 3 = 0 := by
  norm_num [velocityLpScalingNumerator]

theorem finiteEnergyVelocityLpIndex_supercritical :
    velocityLpScalingRegime finiteEnergyVelocityLpIndex = .supercritical := by
  simp [velocityLpScalingRegime, finiteEnergyVelocityLpIndex]

theorem finiteEnergyVelocityLpIndex_not_clearsCriticalPromotion :
    velocityLpClearsCriticalPromotion finiteEnergyVelocityLpIndex = false := by
  simp [velocityLpClearsCriticalPromotion, NavierScalingRegime.clearsCriticalPromotion,
    velocityLpScalingRegime, finiteEnergyVelocityLpIndex]

theorem criticalVelocityLpIndex_critical :
    velocityLpScalingRegime criticalVelocityLpIndex = .critical := by
  simp [velocityLpScalingRegime, criticalVelocityLpIndex]

theorem finiteEnergyVelocityLpIndex_ne_criticalVelocityLpIndex :
    finiteEnergyVelocityLpIndex ≠ criticalVelocityLpIndex := by
  norm_num [finiteEnergyVelocityLpIndex, criticalVelocityLpIndex]

theorem currentNavierEnergyBKMRoute_criticalNorm_blocked_by_supercritical_energy :
    currentNavierEnergyBKMScalingStatus.criticalNorm = .blocked ∧
      velocityLpScalingRegime finiteEnergyVelocityLpIndex = .supercritical ∧
      velocityLpScalingRegime criticalVelocityLpIndex = .critical ∧
      finiteEnergyVelocityLpIndex ≠ criticalVelocityLpIndex := by
  exact
    ⟨currentNavierEnergyBKMScalingStatus_criticalNorm_blocked,
      finiteEnergyVelocityLpIndex_supercritical,
      criticalVelocityLpIndex_critical,
      finiteEnergyVelocityLpIndex_ne_criticalVelocityLpIndex⟩

theorem currentNavierEnergyBKMRoute_supercriticalUpgrade_blocked_by_supercritical_energy :
    currentNavierEnergyBKMScalingStatus.supercriticalUpgrade = .blocked ∧
      velocityLpScalingRegime finiteEnergyVelocityLpIndex = .supercritical ∧
      velocityLpClearsCriticalPromotion finiteEnergyVelocityLpIndex = false := by
  exact
    ⟨currentNavierEnergyBKMScalingStatus_supercriticalUpgrade_blocked,
      finiteEnergyVelocityLpIndex_supercritical,
      finiteEnergyVelocityLpIndex_not_clearsCriticalPromotion⟩

theorem currentNavierEnergyBKMRoute_averagedEquationCompatibility_obligation_packet :
    currentNavierEnergyBKMScalingStatus.averagedEquationCompatibility = .notRepresented ∧
      currentNavierEnergyBKMAveragedEquationCompatibilityStatus.required =
        currentNavierAveragedEquationCompatibilityObligations ∧
      currentNavierEnergyBKMAveragedEquationCompatibilityStatus.represented = [] ∧
      currentNavierEnergyBKMAveragedEquationCompatibilityStatus.missingObligations =
        currentNavierAveragedEquationCompatibilityObligations ∧
      ¬ currentNavierEnergyBKMAveragedEquationCompatibilityStatus.Clears := by
  exact
    ⟨currentNavierEnergyBKMScalingStatus_averagedEquationCompatibility_notRepresented,
      currentNavierEnergyBKMAveragedEquationCompatibility_required,
      currentNavierEnergyBKMAveragedEquationCompatibility_represented,
      (by
        simpa [currentNavierAveragedEquationCompatibilityObligations] using
          currentNavierEnergyBKMAveragedEquationCompatibility_missingObligations),
      currentNavierEnergyBKMAveragedEquationCompatibility_not_cleared⟩

theorem currentNavierEnergyBKMRoute_averagedEquationFrontier_packet :
    exampleNavierAveragedEquationCompatibilityClearedStatus.Clears ∧
      exampleNavierAveragedEquationCompatibilityClearedStatus.missingObligations = [] ∧
      currentNavierEnergyBKMAveragedEquationCompatibilityStatus.represented = [] ∧
      currentNavierEnergyBKMAveragedEquationCompatibilityStatus.missingObligations =
        [ .averagedMomentumEquation
        , .reynoldsStressClosure
        , .energyInequalityCompatibility
        , .criticalScalingCompatibility
        ] ∧
      ¬ currentNavierEnergyBKMAveragedEquationCompatibilityStatus.Clears := by
  exact
    ⟨exampleNavierAveragedEquationCompatibilityClearedStatus_clears,
      exampleNavierAveragedEquationCompatibilityClearedStatus_missingObligations,
      currentNavierEnergyBKMAveragedEquationCompatibility_represented,
      currentNavierEnergyBKMAveragedEquationCompatibility_missingObligations,
      currentNavierEnergyBKMAveragedEquationCompatibility_not_cleared⟩

theorem currentNavierEnergyBKMRoute_averagedMomentumEquation_obstruction :
    NavierAveragedEquationObligation.averagedMomentumEquation ∈
        currentNavierEnergyBKMAveragedEquationCompatibilityStatus.missingObligations ∧
      ¬ NavierAveragedEquationObligation.averagedMomentumEquation ∈
        currentNavierEnergyBKMAveragedEquationCompatibilityStatus.represented ∧
      NavierAveragedEquationObligation.averagedMomentumEquation.requiredWorldInterface =
        .averagedMomentumWitness ∧
      NavierScalingWorldInterface.averagedMomentumWitness ∈
        currentNavierEnergyBKMRouteWorldInterfaces.missingFor .averagedEquationCompatibility ∧
      ¬ NavierScalingWorldInterface.averagedMomentumWitness ∈
        currentNavierEnergyBKMRouteWorldInterfaces.supplied := by
  exact
    ⟨currentNavierEnergyBKMAveragedEquationCompatibility_missing_averagedMomentumEquation,
      currentNavierEnergyBKMAveragedEquationCompatibility_not_represented_averagedMomentumEquation,
      requiredWorldInterface_averagedMomentumEquation,
      currentNavierEnergyBKMRouteWorldInterfaces_missing_averagedMomentumWitness,
      currentNavierEnergyBKMRouteWorldInterfaces_not_supplied_averagedMomentumWitness⟩

theorem currentNavierEnergyBKMRoute_scaling_diagnostic_packet :
    currentNavierEnergyBKMScalingStatus.criticalNorm = .blocked ∧
      currentNavierEnergyBKMScalingStatus.supercriticalUpgrade = .blocked ∧
      currentNavierEnergyBKMScalingStatus.averagedEquationCompatibility = .notRepresented ∧
      currentNavierEnergyBKMScalingStatus.unrepresentedChecks =
        [ .averagedEquationCompatibility ] ∧
      ¬ currentNavierEnergyBKMAveragedEquationCompatibilityStatus.Clears ∧
      velocityLpScalingRegime finiteEnergyVelocityLpIndex = .supercritical ∧
      velocityLpClearsCriticalPromotion finiteEnergyVelocityLpIndex = false ∧
      velocityLpScalingRegime criticalVelocityLpIndex = .critical ∧
      finiteEnergyVelocityLpIndex ≠ criticalVelocityLpIndex := by
  exact
    ⟨currentNavierEnergyBKMScalingStatus_criticalNorm_blocked,
      currentNavierEnergyBKMScalingStatus_supercriticalUpgrade_blocked,
      currentNavierEnergyBKMScalingStatus_averagedEquationCompatibility_notRepresented,
      currentNavierEnergyBKMScalingStatus_unrepresentedChecks,
      currentNavierEnergyBKMAveragedEquationCompatibility_not_cleared,
      finiteEnergyVelocityLpIndex_supercritical,
      finiteEnergyVelocityLpIndex_not_clearsCriticalPromotion,
      criticalVelocityLpIndex_critical,
      finiteEnergyVelocityLpIndex_ne_criticalVelocityLpIndex⟩

theorem currentNavierEnergyBKMRoute_world_interface_packet :
    currentNavierEnergyBKMRouteWorldInterfaces.supplied =
        [ .finiteEnergyL2Diagnostic ] ∧
      currentNavierEnergyBKMRouteWorldInterfaces.missingFor .criticalNorm =
        NavierScalingCheck.criticalNorm.requiredWorldInterfaces ∧
      currentNavierEnergyBKMRouteWorldInterfaces.missingFor .supercriticalUpgrade =
        NavierScalingCheck.supercriticalUpgrade.requiredWorldInterfaces ∧
      currentNavierEnergyBKMRouteWorldInterfaces.missingFor .averagedEquationCompatibility =
        NavierScalingCheck.averagedEquationCompatibility.requiredWorldInterfaces := by
  exact
    ⟨currentNavierEnergyBKMRouteWorldInterfaces_supplied,
      currentNavierEnergyBKMRouteWorldInterfaces_missing_criticalNorm,
      currentNavierEnergyBKMRouteWorldInterfaces_missing_supercriticalUpgrade,
      currentNavierEnergyBKMRouteWorldInterfaces_missing_averagedEquationCompatibility⟩

theorem currentNavierEnergyBKMRoute_scaling_and_world_interface_packet :
    currentNavierEnergyBKMScalingStatus.criticalNorm = .blocked ∧
      currentNavierEnergyBKMScalingStatus.supercriticalUpgrade = .blocked ∧
      currentNavierEnergyBKMScalingStatus.averagedEquationCompatibility = .notRepresented ∧
      currentNavierEnergyBKMRouteWorldInterfaces.supplied =
        [ .finiteEnergyL2Diagnostic ] ∧
      currentNavierEnergyBKMRouteWorldInterfaces.missingFor .criticalNorm =
        NavierScalingCheck.criticalNorm.requiredWorldInterfaces ∧
      currentNavierEnergyBKMRouteWorldInterfaces.missingFor .supercriticalUpgrade =
        NavierScalingCheck.supercriticalUpgrade.requiredWorldInterfaces ∧
      currentNavierEnergyBKMRouteWorldInterfaces.missingFor .averagedEquationCompatibility =
        NavierScalingCheck.averagedEquationCompatibility.requiredWorldInterfaces := by
  exact
    ⟨currentNavierEnergyBKMScalingStatus_criticalNorm_blocked,
      currentNavierEnergyBKMScalingStatus_supercriticalUpgrade_blocked,
      currentNavierEnergyBKMScalingStatus_averagedEquationCompatibility_notRepresented,
      currentNavierEnergyBKMRouteWorldInterfaces_supplied,
      currentNavierEnergyBKMRouteWorldInterfaces_missing_criticalNorm,
      currentNavierEnergyBKMRouteWorldInterfaces_missing_supercriticalUpgrade,
      currentNavierEnergyBKMRouteWorldInterfaces_missing_averagedEquationCompatibility⟩

/-- The current finite-energy/BKM route fails every layer required for a
global-regularity promotion certificate. -/
theorem currentNavierEnergyBKMRoute_regularityPromotionGate_refuted :
    ¬ currentNavierEnergyBKMScalingStatus.ClearsAll ∧
      ¬ currentNavierEnergyBKMRouteWorldInterfaces.ClearsAll ∧
      ¬ currentNavierEnergyBKMAveragedEquationCompatibilityStatus.Clears ∧
      ¬ currentNavierEnergyBKMRegularityPromotionGate.ClearsAll ∧
      velocityLpScalingRegime finiteEnergyVelocityLpIndex = .supercritical ∧
      velocityLpClearsCriticalPromotion finiteEnergyVelocityLpIndex = false := by
  exact
    ⟨currentNavierEnergyBKMScalingStatus_not_cleared,
      currentNavierEnergyBKMRouteWorldInterfaces_not_cleared,
      currentNavierEnergyBKMAveragedEquationCompatibility_not_cleared,
      currentNavierEnergyBKMRegularityPromotionGate_not_cleared,
      finiteEnergyVelocityLpIndex_supercritical,
      finiteEnergyVelocityLpIndex_not_clearsCriticalPromotion⟩

/-- The current route has finite-energy/BKM no-go evidence but not scaling
clearance for a global-regularity promotion. -/
theorem currentNavierEnergyBKMRoute_not_scalingCleared :
    (∀ {c : NSSpace} {T : ℝ}, c ≠ 0 → 0 ≤ T →
      ¬ ∃ u : NSVelocityField,
        MatchesInitialVelocity (constantInitialVelocity c) u ∧
          ∀ t, 0 ≤ t → t ≤ T → Integrable (kineticEnergyDensity u t)) ∧
      ¬ currentNavierEnergyBKMScalingStatus.ClearsAll := by
  exact
    ⟨fun hc hT =>
      not_exists_energyBKMBridge_kineticIntegrabilityOnSlab_constantInitialVelocity
        hc hT,
      currentNavierEnergyBKMScalingStatus_not_cleared⟩

end NavierStokes
end FluidDynamics
end Mettapedia
