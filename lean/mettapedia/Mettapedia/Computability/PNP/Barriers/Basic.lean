import Mettapedia.Computability.PNP.CruxKpolyPromotedPacket

/-!
# PNP barrier status

This module records the cheap-falsification surface for promoting a local PNP
ledger result into a global complexity route.  A local stop-grade packet is not
barrier-cleared until the relativization, natural-proof, and algebrization
checks have explicit Lean evidence.
-/

namespace Mettapedia.Computability.PNP

/-- Barrier families that any advertised PNP route must confront. -/
inductive PNPBarrierKind where
  | relativization
  | naturalProof
  | algebrization
deriving DecidableEq, Repr

/-- The complete barrier checklist for the current PNP audit layer. -/
def PNPBarrierKind.all : List PNPBarrierKind :=
  [ .relativization
  , .naturalProof
  , .algebrization
  ]

/-- The barrier families still lacking represented evidence after the current
relativization route-shape refutation. -/
def PNPBarrierKind.currentMissingEvidenceAfterRelativizationBlock :
    List PNPBarrierKind :=
  [ .naturalProof
  , .algebrization
  ]

/-- The barrier families still lacking represented evidence after the current
relativization and natural-proof route-shape refutations. -/
def PNPBarrierKind.currentMissingEvidenceAfterNaturalProofBlock :
    List PNPBarrierKind :=
  [ .algebrization
  ]

/-- No barrier family remains merely unrepresented after the current
relativization, natural-proof, and algebrization route-shape refutations. -/
def PNPBarrierKind.currentMissingEvidenceAfterAlgebrizationBlock :
    List PNPBarrierKind :=
  []

/-- Diagnostic worlds used for the cheap-falsification pass. -/
inductive PNPBarrierWorldKind where
  | oracle
  | pseudorandom
  | algebraicOracle
deriving DecidableEq, Repr

/-- Route interfaces demanded by the barrier challenge worlds. -/
inductive PNPBarrierWorldInterface where
  | oracleChallengeWorldGenerator
  | oracleInvariantSeparationClaim
  | pseudorandomChallengeWorldSampler
  | constructivityLargenessUsefulnessAudit
  | nonNaturalEscapeCertificate
  | algebraicOracleChallengeWorldGenerator
  | algebraicLiftInterface
  | algebraicOracleInvariantSeparationClaim
deriving DecidableEq, Repr

/-- Positive witnesses needed before a route can claim to escape a PNP barrier
rather than only record that the barrier is relevant. -/
inductive PNPBarrierEscapeWitness where
  | nonrelativizingOracleSeparation
  | nonNaturalPropertyEscape
  | nonAlgebrizingAlgebraicOracleSeparation
deriving DecidableEq, Repr

/-- The canonical challenge world associated with a PNP barrier family. -/
def PNPBarrierKind.challengeWorld : PNPBarrierKind → PNPBarrierWorldKind
  | .relativization => .oracle
  | .naturalProof => .pseudorandom
  | .algebrization => .algebraicOracle

/-- The route interfaces required to test a proposed PNP route against one
barrier-world family. -/
def PNPBarrierKind.requiredWorldInterfaces :
    PNPBarrierKind → List PNPBarrierWorldInterface
  | .relativization =>
      [ .oracleChallengeWorldGenerator
      , .oracleInvariantSeparationClaim
      ]
  | .naturalProof =>
      [ .pseudorandomChallengeWorldSampler
      , .constructivityLargenessUsefulnessAudit
      , .nonNaturalEscapeCertificate
      ]
  | .algebrization =>
      [ .algebraicOracleChallengeWorldGenerator
      , .algebraicLiftInterface
      , .algebraicOracleInvariantSeparationClaim
      ]

/-- Positive escape witnesses required before a route can claim to have passed
one of the classical PNP barriers. -/
def PNPBarrierKind.requiredEscapeWitnesses :
    PNPBarrierKind → List PNPBarrierEscapeWitness
  | .relativization => [ .nonrelativizingOracleSeparation ]
  | .naturalProof => [ .nonNaturalPropertyEscape ]
  | .algebrization => [ .nonAlgebrizingAlgebraicOracleSeparation ]

/-- Current route verdict for one barrier family. -/
inductive PNPBarrierVerdict where
  | cleared
  | blocked
  | notRepresented
deriving DecidableEq, Repr

/-- Boolean clearance flag for a barrier verdict. -/
def PNPBarrierVerdict.clears : PNPBarrierVerdict → Bool
  | .cleared => true
  | .blocked => false
  | .notRepresented => false

/-- `true` when a barrier has not been cleared. -/
def PNPBarrierVerdict.isUncleared : PNPBarrierVerdict → Bool
  | .cleared => false
  | .blocked => true
  | .notRepresented => true

/-- `true` when the current ledger has not even represented evidence for a
barrier family.  This distinguishes an honest missing-interface gap from a
checked negative barrier result. -/
def PNPBarrierVerdict.isMissingEvidence : PNPBarrierVerdict → Bool
  | .cleared => false
  | .blocked => false
  | .notRepresented => true

/-- Barrier status for a named PNP route candidate. -/
structure PNPBarrierStatus where
  routeKey : String
  relativization : PNPBarrierVerdict
  naturalProof : PNPBarrierVerdict
  algebrization : PNPBarrierVerdict
deriving Repr

/-- A route is barrier-cleared only when all three required families clear. -/
def PNPBarrierStatus.ClearsAll (status : PNPBarrierStatus) : Prop :=
  status.relativization.clears &&
    status.naturalProof.clears &&
    status.algebrization.clears = true

/-- Verdict lookup for one barrier family. -/
def PNPBarrierStatus.verdict
    (status : PNPBarrierStatus) : PNPBarrierKind → PNPBarrierVerdict
  | .relativization => status.relativization
  | .naturalProof => status.naturalProof
  | .algebrization => status.algebrization

/-- Barrier families not cleared by this status. -/
def PNPBarrierStatus.unclearedBarriers
    (status : PNPBarrierStatus) : List PNPBarrierKind :=
  PNPBarrierKind.all.filter fun kind =>
    (status.verdict kind).isUncleared

/-- Barrier families for which this status has no represented evidence yet. -/
def PNPBarrierStatus.missingEvidenceBarriers
    (status : PNPBarrierStatus) : List PNPBarrierKind :=
  PNPBarrierKind.all.filter fun kind =>
    (status.verdict kind).isMissingEvidence

/-- Barrier-world interfaces supplied by a route candidate. -/
structure PNPBarrierRouteWorldInterfaces where
  routeKey : String
  supplied : List PNPBarrierWorldInterface
deriving Repr

/-- Positive barrier-escape witnesses represented by a route candidate. -/
structure PNPBarrierEscapeLedger where
  routeKey : String
  represented : List PNPBarrierEscapeWitness
deriving Repr

/-- Barrier-world interfaces still missing for a barrier family. -/
def PNPBarrierRouteWorldInterfaces.missingFor
    (interfaces : PNPBarrierRouteWorldInterfaces)
    (kind : PNPBarrierKind) : List PNPBarrierWorldInterface :=
  kind.requiredWorldInterfaces.filter fun requirement =>
    decide (requirement ∉ interfaces.supplied)

/-- A route has represented the barrier-world interface layer only when every
barrier family has no missing world-interface requirement. -/
def PNPBarrierRouteWorldInterfaces.ClearsAll
    (interfaces : PNPBarrierRouteWorldInterfaces) : Prop :=
  interfaces.missingFor .relativization = [] ∧
    interfaces.missingFor .naturalProof = [] ∧
    interfaces.missingFor .algebrization = []

/-- Positive barrier-escape witnesses still missing for a barrier family. -/
def PNPBarrierEscapeLedger.missingFor
    (ledger : PNPBarrierEscapeLedger)
    (kind : PNPBarrierKind) : List PNPBarrierEscapeWitness :=
  kind.requiredEscapeWitnesses.filter fun witness =>
    decide (witness ∉ ledger.represented)

/-- A route has represented the positive escape-witness layer only when every
barrier family has no missing escape witness. -/
def PNPBarrierEscapeLedger.ClearsAll
    (ledger : PNPBarrierEscapeLedger) : Prop :=
  ledger.missingFor .relativization = [] ∧
    ledger.missingFor .naturalProof = [] ∧
    ledger.missingFor .algebrization = []

/-- Three-layer gate for promoting a local PNP ledger into a global
barrier-cleared route candidate. -/
structure PNPBarrierPromotionGate where
  routeKey : String
  status : PNPBarrierStatus
  worldInterfaces : PNPBarrierRouteWorldInterfaces
  escapeLedger : PNPBarrierEscapeLedger
deriving Repr

/-- The promotion gate clears only when the verdict, challenge-world interface,
and positive escape-witness layers all clear. -/
def PNPBarrierPromotionGate.ClearsAll
    (gate : PNPBarrierPromotionGate) : Prop :=
  gate.status.ClearsAll ∧
    gate.worldInterfaces.ClearsAll ∧
    gate.escapeLedger.ClearsAll

/-- Minimal route-shape interface needed before a PNP route can claim to clear
the relativization barrier. -/
structure PNPRelativizationRouteShape where
  routeKey : String
  hasOracleChallengeWorldGenerator : Bool
  hasOracleInvariantSeparationClaim : Bool
deriving Repr

/-- A route clears the relativization interface only when it supplies both the
oracle challenge-world generator and an invariant separation claim over those
worlds. -/
def PNPRelativizationRouteShape.Clears
    (shape : PNPRelativizationRouteShape) : Prop :=
  shape.hasOracleChallengeWorldGenerator = true ∧
    shape.hasOracleInvariantSeparationClaim = true

/-- The current Kpoly-promoted route shape is still only the local finite
ledger; it has no oracle-world generator. -/
def currentPNPKpolyPromotedRelativizationRouteShape :
    PNPRelativizationRouteShape where
  routeKey := "pnp.kpoly-promoted-local-ledger"
  hasOracleChallengeWorldGenerator := false
  hasOracleInvariantSeparationClaim := false

/-- Minimal route-shape interface needed before a PNP route can claim to clear
the natural-proofs barrier. -/
structure PNPNaturalProofRouteShape where
  routeKey : String
  hasPseudorandomChallengeWorldSampler : Bool
  hasConstructivityLargenessUsefulnessAudit : Bool
  hasNonNaturalEscapeCertificate : Bool
deriving Repr

/-- A route clears the natural-proofs interface only when it supplies the
pseudorandom challenge worlds, audits the constructive/large/useful property
shape, and proves an escape certificate for that shape. -/
def PNPNaturalProofRouteShape.Clears
    (shape : PNPNaturalProofRouteShape) : Prop :=
  shape.hasPseudorandomChallengeWorldSampler = true ∧
    shape.hasConstructivityLargenessUsefulnessAudit = true ∧
    shape.hasNonNaturalEscapeCertificate = true

/-- The current Kpoly-promoted route shape is still only the local finite
ledger; it has no pseudorandom-world sampler or non-naturalness certificate. -/
def currentPNPKpolyPromotedNaturalProofRouteShape :
    PNPNaturalProofRouteShape where
  routeKey := "pnp.kpoly-promoted-local-ledger"
  hasPseudorandomChallengeWorldSampler := false
  hasConstructivityLargenessUsefulnessAudit := false
  hasNonNaturalEscapeCertificate := false

/-- Minimal route-shape interface needed before a PNP route can claim to clear
the algebrization barrier. -/
structure PNPAlgebrizationRouteShape where
  routeKey : String
  hasAlgebraicOracleChallengeWorldGenerator : Bool
  hasAlgebraicLiftInterface : Bool
  hasAlgebraicOracleInvariantSeparationClaim : Bool
deriving Repr

/-- A route clears the algebrization interface only when it supplies algebraic
oracle challenge worlds, an algebraic lift interface, and an invariant
separation claim over those lifted worlds. -/
def PNPAlgebrizationRouteShape.Clears
    (shape : PNPAlgebrizationRouteShape) : Prop :=
  shape.hasAlgebraicOracleChallengeWorldGenerator = true ∧
    shape.hasAlgebraicLiftInterface = true ∧
    shape.hasAlgebraicOracleInvariantSeparationClaim = true

/-- The current Kpoly-promoted route shape is still only the local finite
ledger; it has no algebraic-oracle generator or algebraic lift interface. -/
def currentPNPKpolyPromotedAlgebrizationRouteShape :
    PNPAlgebrizationRouteShape where
  routeKey := "pnp.kpoly-promoted-local-ledger"
  hasAlgebraicOracleChallengeWorldGenerator := false
  hasAlgebraicLiftInterface := false
  hasAlgebraicOracleInvariantSeparationClaim := false

/-- The three challenge worlds used for the current PNP route audit. -/
def currentPNPBarrierChallengeWorlds : List PNPBarrierWorldKind :=
  [ .oracle
  , .pseudorandom
  , .algebraicOracle
  ]

/-- Barrier-world interfaces supplied by the current Kpoly-promoted local
ledger route.  It supplies none of the global challenge-world interfaces. -/
def currentPNPKpolyPromotedWorldInterfaces :
    PNPBarrierRouteWorldInterfaces where
  routeKey := "pnp.kpoly-promoted-local-ledger"
  supplied := []

/-- Positive barrier-escape witnesses represented by the current Kpoly-promoted
local ledger route.  The local ledger currently represents none of them. -/
def currentPNPKpolyPromotedBarrierEscapeLedger :
    PNPBarrierEscapeLedger where
  routeKey := "pnp.kpoly-promoted-local-ledger"
  represented := []

/-- The current PNP local ledger has no represented barrier clearance yet. -/
def currentPNPKpolyPromotedBarrierStatus : PNPBarrierStatus where
  routeKey := "pnp.kpoly-promoted-local-ledger"
  relativization := .blocked
  naturalProof := .blocked
  algebrization := .blocked

/-- The current promotion-gate packet combines the local barrier verdicts,
world-interface ledger, and positive escape-witness ledger. -/
def currentPNPKpolyPromotedBarrierPromotionGate :
    PNPBarrierPromotionGate where
  routeKey := "pnp.kpoly-promoted-local-ledger"
  status := currentPNPKpolyPromotedBarrierStatus
  worldInterfaces := currentPNPKpolyPromotedWorldInterfaces
  escapeLedger := currentPNPKpolyPromotedBarrierEscapeLedger

theorem challengeWorld_relativization :
    PNPBarrierKind.relativization.challengeWorld = .oracle := by
  rfl

theorem challengeWorld_naturalProof :
    PNPBarrierKind.naturalProof.challengeWorld = .pseudorandom := by
  rfl

theorem challengeWorld_algebrization :
    PNPBarrierKind.algebrization.challengeWorld = .algebraicOracle := by
  rfl

theorem currentPNPBarrierChallengeWorlds_length :
    currentPNPBarrierChallengeWorlds.length = 3 := by
  rfl

theorem currentPNPBarrierChallengeWorlds_eq_all_barrier_worlds :
    PNPBarrierKind.all.map PNPBarrierKind.challengeWorld =
      currentPNPBarrierChallengeWorlds := by
  rfl

theorem requiredWorldInterfaces_relativization :
    PNPBarrierKind.relativization.requiredWorldInterfaces =
      [ .oracleChallengeWorldGenerator
      , .oracleInvariantSeparationClaim
      ] := by
  rfl

theorem requiredWorldInterfaces_naturalProof :
    PNPBarrierKind.naturalProof.requiredWorldInterfaces =
      [ .pseudorandomChallengeWorldSampler
      , .constructivityLargenessUsefulnessAudit
      , .nonNaturalEscapeCertificate
      ] := by
  rfl

theorem requiredWorldInterfaces_algebrization :
    PNPBarrierKind.algebrization.requiredWorldInterfaces =
      [ .algebraicOracleChallengeWorldGenerator
      , .algebraicLiftInterface
      , .algebraicOracleInvariantSeparationClaim
      ] := by
  rfl

theorem requiredEscapeWitnesses_relativization :
    PNPBarrierKind.relativization.requiredEscapeWitnesses =
      [ .nonrelativizingOracleSeparation ] := by
  rfl

theorem requiredEscapeWitnesses_naturalProof :
    PNPBarrierKind.naturalProof.requiredEscapeWitnesses =
      [ .nonNaturalPropertyEscape ] := by
  rfl

theorem requiredEscapeWitnesses_algebrization :
    PNPBarrierKind.algebrization.requiredEscapeWitnesses =
      [ .nonAlgebrizingAlgebraicOracleSeparation ] := by
  rfl

theorem PNPBarrierStatus.clearsAll_iff_unclearedBarriers_eq_nil
    (status : PNPBarrierStatus) :
    status.ClearsAll ↔ status.unclearedBarriers = [] := by
  rcases status with ⟨routeKey, relativization, naturalProof, algebrization⟩
  cases relativization <;> cases naturalProof <;> cases algebrization <;>
    simp [PNPBarrierStatus.ClearsAll, PNPBarrierStatus.unclearedBarriers,
      PNPBarrierStatus.verdict, PNPBarrierKind.all, PNPBarrierVerdict.clears,
      PNPBarrierVerdict.isUncleared]

theorem PNPBarrierStatus.not_clearsAll_of_unclearedBarriers_ne_nil
    {status : PNPBarrierStatus}
    (hmissing : status.unclearedBarriers ≠ []) :
    ¬ status.ClearsAll := by
  intro hcleared
  exact hmissing
    ((PNPBarrierStatus.clearsAll_iff_unclearedBarriers_eq_nil status).1 hcleared)

theorem currentPNPKpolyPromotedRelativizationRouteShape_no_oracle_generator :
    currentPNPKpolyPromotedRelativizationRouteShape.hasOracleChallengeWorldGenerator =
      false := by
  rfl

theorem currentPNPKpolyPromotedRelativizationRouteShape_not_cleared :
    ¬ currentPNPKpolyPromotedRelativizationRouteShape.Clears := by
  intro hclears
  exact Bool.noConfusion hclears.1

theorem currentPNPKpolyPromotedNaturalProofRouteShape_no_pseudorandom_sampler :
    currentPNPKpolyPromotedNaturalProofRouteShape.hasPseudorandomChallengeWorldSampler =
      false := by
  rfl

theorem currentPNPKpolyPromotedNaturalProofRouteShape_not_cleared :
    ¬ currentPNPKpolyPromotedNaturalProofRouteShape.Clears := by
  intro hclears
  exact Bool.noConfusion hclears.1

theorem currentPNPKpolyPromotedAlgebrizationRouteShape_no_algebraic_oracle_generator :
    currentPNPKpolyPromotedAlgebrizationRouteShape.hasAlgebraicOracleChallengeWorldGenerator =
      false := by
  rfl

theorem currentPNPKpolyPromotedAlgebrizationRouteShape_not_cleared :
    ¬ currentPNPKpolyPromotedAlgebrizationRouteShape.Clears := by
  intro hclears
  exact Bool.noConfusion hclears.1

theorem currentPNPKpolyPromotedBarrierStatus_verdicts :
    currentPNPKpolyPromotedBarrierStatus.relativization = .blocked ∧
      currentPNPKpolyPromotedBarrierStatus.naturalProof = .blocked ∧
      currentPNPKpolyPromotedBarrierStatus.algebrization = .blocked := by
  simp [currentPNPKpolyPromotedBarrierStatus]

theorem currentPNPKpolyPromotedBarrierStatus_unclearedBarriers :
    currentPNPKpolyPromotedBarrierStatus.unclearedBarriers =
      PNPBarrierKind.all := by
  rfl

theorem currentPNPKpolyPromotedBarrierStatus_missingEvidenceBarriers :
    currentPNPKpolyPromotedBarrierStatus.missingEvidenceBarriers =
      PNPBarrierKind.currentMissingEvidenceAfterAlgebrizationBlock := by
  rfl

theorem currentPNPKpolyPromotedWorldInterfaces_supplied :
    currentPNPKpolyPromotedWorldInterfaces.supplied = [] := by
  rfl

theorem currentPNPKpolyPromotedBarrierEscapeLedger_represented :
    currentPNPKpolyPromotedBarrierEscapeLedger.represented = [] := by
  rfl

theorem currentPNPKpolyPromotedWorldInterfaces_missing_relativization :
    currentPNPKpolyPromotedWorldInterfaces.missingFor .relativization =
      PNPBarrierKind.relativization.requiredWorldInterfaces := by
  simp [PNPBarrierRouteWorldInterfaces.missingFor,
    currentPNPKpolyPromotedWorldInterfaces,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPKpolyPromotedWorldInterfaces_missing_naturalProof :
    currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof =
      PNPBarrierKind.naturalProof.requiredWorldInterfaces := by
  simp [PNPBarrierRouteWorldInterfaces.missingFor,
    currentPNPKpolyPromotedWorldInterfaces,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPKpolyPromotedWorldInterfaces_missing_algebrization :
    currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization =
      PNPBarrierKind.algebrization.requiredWorldInterfaces := by
  simp [PNPBarrierRouteWorldInterfaces.missingFor,
    currentPNPKpolyPromotedWorldInterfaces,
    PNPBarrierKind.requiredWorldInterfaces]

theorem currentPNPKpolyPromotedWorldInterfaces_not_cleared :
    ¬ currentPNPKpolyPromotedWorldInterfaces.ClearsAll := by
  intro hclears
  have hrel := hclears.1
  rw [currentPNPKpolyPromotedWorldInterfaces_missing_relativization] at hrel
  simp [PNPBarrierKind.requiredWorldInterfaces] at hrel

theorem currentPNPKpolyPromotedBarrierEscapeLedger_missing_relativization :
    currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .relativization =
      PNPBarrierKind.relativization.requiredEscapeWitnesses := by
  simp [PNPBarrierEscapeLedger.missingFor,
    currentPNPKpolyPromotedBarrierEscapeLedger,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPKpolyPromotedBarrierEscapeLedger_missing_naturalProof :
    currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .naturalProof =
      PNPBarrierKind.naturalProof.requiredEscapeWitnesses := by
  simp [PNPBarrierEscapeLedger.missingFor,
    currentPNPKpolyPromotedBarrierEscapeLedger,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPKpolyPromotedBarrierEscapeLedger_missing_algebrization :
    currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .algebrization =
      PNPBarrierKind.algebrization.requiredEscapeWitnesses := by
  simp [PNPBarrierEscapeLedger.missingFor,
    currentPNPKpolyPromotedBarrierEscapeLedger,
    PNPBarrierKind.requiredEscapeWitnesses]

theorem currentPNPKpolyPromotedBarrierEscapeLedger_not_cleared :
    ¬ currentPNPKpolyPromotedBarrierEscapeLedger.ClearsAll := by
  intro hclears
  have hrel := hclears.1
  rw [currentPNPKpolyPromotedBarrierEscapeLedger_missing_relativization] at hrel
  simp [PNPBarrierKind.requiredEscapeWitnesses] at hrel

theorem currentPNPKpolyPromotedRelativization_blocked_by_route_shape :
    currentPNPKpolyPromotedBarrierStatus.relativization = .blocked ∧
      ¬ currentPNPKpolyPromotedRelativizationRouteShape.Clears := by
  exact
    ⟨(currentPNPKpolyPromotedBarrierStatus_verdicts).1,
      currentPNPKpolyPromotedRelativizationRouteShape_not_cleared⟩

theorem currentPNPKpolyPromotedNaturalProof_blocked_by_route_shape :
    currentPNPKpolyPromotedBarrierStatus.naturalProof = .blocked ∧
      ¬ currentPNPKpolyPromotedNaturalProofRouteShape.Clears := by
  exact
    ⟨(currentPNPKpolyPromotedBarrierStatus_verdicts).2.1,
      currentPNPKpolyPromotedNaturalProofRouteShape_not_cleared⟩

theorem currentPNPKpolyPromotedAlgebrization_blocked_by_route_shape :
    currentPNPKpolyPromotedBarrierStatus.algebrization = .blocked ∧
      ¬ currentPNPKpolyPromotedAlgebrizationRouteShape.Clears := by
  exact
    ⟨(currentPNPKpolyPromotedBarrierStatus_verdicts).2.2,
      currentPNPKpolyPromotedAlgebrizationRouteShape_not_cleared⟩

theorem currentPNPKpolyPromotedBarrierStatus_not_cleared :
    ¬ currentPNPKpolyPromotedBarrierStatus.ClearsAll := by
  exact
    PNPBarrierStatus.not_clearsAll_of_unclearedBarriers_ne_nil (by
      simp [currentPNPKpolyPromotedBarrierStatus_unclearedBarriers,
        PNPBarrierKind.all])

theorem currentPNPKpolyPromotedBarrierPromotionGate_layers :
    currentPNPKpolyPromotedBarrierPromotionGate.status =
        currentPNPKpolyPromotedBarrierStatus ∧
      currentPNPKpolyPromotedBarrierPromotionGate.worldInterfaces =
        currentPNPKpolyPromotedWorldInterfaces ∧
      currentPNPKpolyPromotedBarrierPromotionGate.escapeLedger =
        currentPNPKpolyPromotedBarrierEscapeLedger := by
  exact ⟨rfl, rfl, rfl⟩

theorem currentPNPKpolyPromotedBarrierPromotionGate_not_cleared :
    ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll := by
  intro hclears
  exact currentPNPKpolyPromotedBarrierStatus_not_cleared hclears.1

/-- The current Kpoly-promoted packet closes the local ledger but not the
barrier-cleared global route check. -/
theorem currentPNPKpolyPromotedPacket_stopGrade_and_not_barrierCleared :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      ¬ currentPNPKpolyPromotedBarrierStatus.ClearsAll := by
  exact
    ⟨stopGrade_currentPNPKpolyCompressionBridgePromotedPacket,
      currentPNPKpolyPromotedBarrierStatus_not_cleared⟩

/-- The current Kpoly-promoted packet is locally stop-grade, and no barrier
family remains merely unrepresented; the active barriers are route-shape
blocks. -/
theorem currentPNPKpolyPromotedPacket_stopGrade_and_missingBarrierEvidence :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierStatus.missingEvidenceBarriers =
        PNPBarrierKind.currentMissingEvidenceAfterAlgebrizationBlock := by
  exact
    ⟨stopGrade_currentPNPKpolyCompressionBridgePromotedPacket,
      currentPNPKpolyPromotedBarrierStatus_missingEvidenceBarriers⟩

/-- The current Kpoly-promoted packet is locally stop-grade, but the
relativization barrier is already blocked for this local-ledger route shape. -/
theorem currentPNPKpolyPromotedPacket_stopGrade_and_relativizationBlocked :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierStatus.relativization = .blocked ∧
      ¬ currentPNPKpolyPromotedRelativizationRouteShape.Clears := by
  exact
    ⟨stopGrade_currentPNPKpolyCompressionBridgePromotedPacket,
      currentPNPKpolyPromotedRelativization_blocked_by_route_shape⟩

/-- The current Kpoly-promoted packet is locally stop-grade, but the
natural-proofs barrier is already blocked for this local-ledger route shape. -/
theorem currentPNPKpolyPromotedPacket_stopGrade_and_naturalProofBlocked :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierStatus.naturalProof = .blocked ∧
      ¬ currentPNPKpolyPromotedNaturalProofRouteShape.Clears := by
  exact
    ⟨stopGrade_currentPNPKpolyCompressionBridgePromotedPacket,
      currentPNPKpolyPromotedNaturalProof_blocked_by_route_shape⟩

/-- The current Kpoly-promoted packet is locally stop-grade, but the
algebrization barrier is already blocked for this local-ledger route shape. -/
theorem currentPNPKpolyPromotedPacket_stopGrade_and_algebrizationBlocked :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierStatus.algebrization = .blocked ∧
      ¬ currentPNPKpolyPromotedAlgebrizationRouteShape.Clears := by
  exact
    ⟨stopGrade_currentPNPKpolyCompressionBridgePromotedPacket,
      currentPNPKpolyPromotedAlgebrization_blocked_by_route_shape⟩

/-- The current Kpoly-promoted packet is locally stop-grade, but each PNP
barrier family is blocked for this local-ledger route shape. -/
theorem currentPNPKpolyPromotedPacket_stopGrade_and_allBarriersBlocked :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierStatus.relativization = .blocked ∧
      currentPNPKpolyPromotedBarrierStatus.naturalProof = .blocked ∧
      currentPNPKpolyPromotedBarrierStatus.algebrization = .blocked ∧
      ¬ currentPNPKpolyPromotedRelativizationRouteShape.Clears ∧
      ¬ currentPNPKpolyPromotedNaturalProofRouteShape.Clears ∧
      ¬ currentPNPKpolyPromotedAlgebrizationRouteShape.Clears := by
  exact
    ⟨stopGrade_currentPNPKpolyCompressionBridgePromotedPacket,
      (currentPNPKpolyPromotedBarrierStatus_verdicts).1,
      (currentPNPKpolyPromotedBarrierStatus_verdicts).2.1,
      (currentPNPKpolyPromotedBarrierStatus_verdicts).2.2,
      currentPNPKpolyPromotedRelativizationRouteShape_not_cleared,
      currentPNPKpolyPromotedNaturalProofRouteShape_not_cleared,
      currentPNPKpolyPromotedAlgebrizationRouteShape_not_cleared⟩

/-- The current Kpoly-promoted packet is locally stop-grade, but its
barrier-world test has no supplied global interfaces and therefore misses every
required world-interface for all three barrier families. -/
theorem currentPNPKpolyPromotedPacket_stopGrade_and_worldInterface_packet :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedWorldInterfaces.supplied = [] ∧
      currentPNPKpolyPromotedWorldInterfaces.missingFor .relativization =
        PNPBarrierKind.relativization.requiredWorldInterfaces ∧
      currentPNPKpolyPromotedWorldInterfaces.missingFor .naturalProof =
        PNPBarrierKind.naturalProof.requiredWorldInterfaces ∧
      currentPNPKpolyPromotedWorldInterfaces.missingFor .algebrization =
        PNPBarrierKind.algebrization.requiredWorldInterfaces := by
  exact
    ⟨stopGrade_currentPNPKpolyCompressionBridgePromotedPacket,
      currentPNPKpolyPromotedWorldInterfaces_supplied,
      currentPNPKpolyPromotedWorldInterfaces_missing_relativization,
      currentPNPKpolyPromotedWorldInterfaces_missing_naturalProof,
      currentPNPKpolyPromotedWorldInterfaces_missing_algebrization⟩

/-- The current Kpoly-promoted packet is locally stop-grade, but it has not
represented the positive witnesses needed to escape any of the three PNP
barriers. -/
theorem currentPNPKpolyPromotedPacket_stopGrade_and_escapeWitness_packet :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      currentPNPKpolyPromotedBarrierEscapeLedger.represented = [] ∧
      currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .relativization =
        PNPBarrierKind.relativization.requiredEscapeWitnesses ∧
      currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .naturalProof =
        PNPBarrierKind.naturalProof.requiredEscapeWitnesses ∧
      currentPNPKpolyPromotedBarrierEscapeLedger.missingFor .algebrization =
        PNPBarrierKind.algebrization.requiredEscapeWitnesses ∧
      ¬ currentPNPKpolyPromotedBarrierEscapeLedger.ClearsAll := by
  exact
    ⟨stopGrade_currentPNPKpolyCompressionBridgePromotedPacket,
      currentPNPKpolyPromotedBarrierEscapeLedger_represented,
      currentPNPKpolyPromotedBarrierEscapeLedger_missing_relativization,
      currentPNPKpolyPromotedBarrierEscapeLedger_missing_naturalProof,
      currentPNPKpolyPromotedBarrierEscapeLedger_missing_algebrization,
      currentPNPKpolyPromotedBarrierEscapeLedger_not_cleared⟩

/-- The current Kpoly-promoted packet is locally stop-grade, but it fails every
layer needed for a global PNP barrier-promotion certificate. -/
theorem currentPNPKpolyPromotedPacket_stopGrade_and_promotionGate_refuted :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      ¬ currentPNPKpolyPromotedBarrierStatus.ClearsAll ∧
      ¬ currentPNPKpolyPromotedWorldInterfaces.ClearsAll ∧
      ¬ currentPNPKpolyPromotedBarrierEscapeLedger.ClearsAll ∧
      ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll := by
  exact
    ⟨stopGrade_currentPNPKpolyCompressionBridgePromotedPacket,
      currentPNPKpolyPromotedBarrierStatus_not_cleared,
      currentPNPKpolyPromotedWorldInterfaces_not_cleared,
      currentPNPKpolyPromotedBarrierEscapeLedger_not_cleared,
      currentPNPKpolyPromotedBarrierPromotionGate_not_cleared⟩

end Mettapedia.Computability.PNP
