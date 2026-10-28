import Mettapedia.Computability.PNP.Barriers.ProperSubsetLabCanaries

/-!
# PNP replacement route opened at the barrier gate

This module records the decided barrier verdict for the current Kpoly lane.
The local Kpoly-promoted ledger remains blocked as a global route, while the
separate all-barrier replacement gate is represented.  This opens only the
replacement route interface; it does not assert a final complexity separation.
-/

namespace Mettapedia.Computability.PNP

/-- Verdict for the current Kpoly barrier decision. -/
inductive PNPBarrierRouteDecisionVerdict where
  | replacementRouteOpenedAtBarrierGate
deriving DecidableEq, Repr

/-- First concrete obligation after opening the replacement barrier gate. -/
inductive PNPReplacementRouteFirstObligation where
  | globalComplexityClassInterface
deriving DecidableEq, Repr

/-- Checked decision packet for the Kpoly barrier route. -/
structure PNPBarrierRouteDecision where
  blockedKpolyRouteKey : String
  replacementRouteKey : String
  verdict : PNPBarrierRouteDecisionVerdict
  barrierGate : PNPBarrierPromotionGate
  firstObligation : PNPReplacementRouteFirstObligation
  claimsFinalSeparation : Bool
deriving Repr

/-- The current decision: the Kpoly local-ledger route stays blocked, and the
all-barrier replacement gate is the opened successor interface. -/
def currentPNPBarrierRouteDecision : PNPBarrierRouteDecision where
  blockedKpolyRouteKey := "pnp.kpoly-promoted-local-ledger"
  replacementRouteKey := currentPNPAllBarrierCandidateRouteKey
  verdict := .replacementRouteOpenedAtBarrierGate
  barrierGate := currentPNPAllBarrierCandidatePromotionGate
  firstObligation := .globalComplexityClassInterface
  claimsFinalSeparation := false

theorem currentPNPBarrierRouteDecision_scope :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll ∧
      currentPNPBarrierRouteDecision.verdict =
        .replacementRouteOpenedAtBarrierGate ∧
      currentPNPBarrierRouteDecision.barrierGate.ClearsAll ∧
      currentPNPBarrierRouteDecision.firstObligation =
        .globalComplexityClassInterface ∧
      currentPNPBarrierRouteDecision.claimsFinalSeparation = false := by
  exact
    ⟨stopGrade_currentPNPKpolyCompressionBridgePromotedPacket,
      currentPNPKpolyPromotedBarrierPromotionGate_not_cleared,
      rfl,
      currentPNPAllBarrierCandidatePromotionGate_clears,
      rfl,
      rfl⟩

theorem currentPNPBarrierRouteDecision_represented_layers :
    currentPNPBarrierRouteDecision.barrierGate.ClearsAll ∧
      (∀ {kind : PNPBarrierKind} {requirement : PNPBarrierWorldInterface},
        requirement ∈ kind.requiredWorldInterfaces →
          requirement ∈
            currentPNPBarrierRouteDecision.barrierGate.worldInterfaces.supplied) ∧
      (∀ {kind : PNPBarrierKind} {witness : PNPBarrierEscapeWitness},
        witness ∈ kind.requiredEscapeWitnesses →
          witness ∈
            currentPNPBarrierRouteDecision.barrierGate.escapeLedger.represented) := by
  have hclears := (currentPNPBarrierRouteDecision_scope).2.2.2.1
  exact
    ⟨hclears,
      fun hrequired =>
        PNPBarrierPromotionGate.clearsAll_requires_world_interface
          hclears hrequired,
      fun hrequired =>
        PNPBarrierPromotionGate.clearsAll_requires_escape_witness
          hclears hrequired⟩

theorem currentPNPBarrierRouteDecision_first_obligation :
    currentPNPBarrierRouteDecision.firstObligation =
      .globalComplexityClassInterface ∧
      currentPNPBarrierRouteDecision.claimsFinalSeparation = false := by
  exact ⟨rfl, rfl⟩

theorem currentPNPBarrierRouteDecision_verdict_packet :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll ∧
      currentPNPBarrierRouteDecision.barrierGate.ClearsAll ∧
      currentPNPBarrierRouteDecision.firstObligation =
        .globalComplexityClassInterface ∧
      currentPNPBarrierRouteDecision.claimsFinalSeparation = false := by
  exact
    ⟨(currentPNPBarrierRouteDecision_scope).1,
      (currentPNPBarrierRouteDecision_scope).2.1,
      (currentPNPBarrierRouteDecision_scope).2.2.2.1,
      (currentPNPBarrierRouteDecision_first_obligation).1,
      (currentPNPBarrierRouteDecision_first_obligation).2⟩

end Mettapedia.Computability.PNP
