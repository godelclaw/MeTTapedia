import Mettapedia.Computability.PNP.Barriers.AllBarrierObstruction

/-!
# PNP replacement-route promotion gate

This module records generic obligations for any future PNP route that attempts
to replace the currently blocked local Kpoly ledger.  It does not construct a
separation route; it proves what any candidate must supply before the existing
barrier gate can clear.
-/

namespace Mettapedia.Computability.PNP

theorem PNPBarrierStatus.clearsAll_verdicts
    (status : PNPBarrierStatus)
    (hclears : status.ClearsAll) :
    status.relativization = .cleared ∧
      status.naturalProof = .cleared ∧
      status.algebrization = .cleared := by
  rcases status with ⟨routeKey, relativization, naturalProof, algebrization⟩
  cases relativization <;> cases naturalProof <;> cases algebrization <;>
    simp [PNPBarrierStatus.ClearsAll, PNPBarrierVerdict.clears] at hclears ⊢

theorem PNPBarrierRouteWorldInterfaces.mem_supplied_of_clearsAll
    {interfaces : PNPBarrierRouteWorldInterfaces}
    {kind : PNPBarrierKind}
    {requirement : PNPBarrierWorldInterface}
    (hclears : interfaces.ClearsAll)
    (hrequired : requirement ∈ kind.requiredWorldInterfaces) :
    requirement ∈ interfaces.supplied := by
  classical
  by_contra hmissingSupplied
  have hmissing : requirement ∈ interfaces.missingFor kind := by
    simp [PNPBarrierRouteWorldInterfaces.missingFor, hrequired, hmissingSupplied]
  cases kind with
  | relativization =>
      rw [hclears.1] at hmissing
      simp at hmissing
  | naturalProof =>
      rw [hclears.2.1] at hmissing
      simp at hmissing
  | algebrization =>
      rw [hclears.2.2] at hmissing
      simp at hmissing

theorem PNPBarrierEscapeLedger.mem_represented_of_clearsAll
    {ledger : PNPBarrierEscapeLedger}
    {kind : PNPBarrierKind}
    {witness : PNPBarrierEscapeWitness}
    (hclears : ledger.ClearsAll)
    (hrequired : witness ∈ kind.requiredEscapeWitnesses) :
    witness ∈ ledger.represented := by
  classical
  by_contra hmissingRepresented
  have hmissing : witness ∈ ledger.missingFor kind := by
    simp [PNPBarrierEscapeLedger.missingFor, hrequired, hmissingRepresented]
  cases kind with
  | relativization =>
      rw [hclears.1] at hmissing
      simp at hmissing
  | naturalProof =>
      rw [hclears.2.1] at hmissing
      simp at hmissing
  | algebrization =>
      rw [hclears.2.2] at hmissing
      simp at hmissing

theorem PNPBarrierPromotionGate.clearsAll_requires_world_interface
    {gate : PNPBarrierPromotionGate}
    (hclears : gate.ClearsAll)
    {kind : PNPBarrierKind}
    {requirement : PNPBarrierWorldInterface}
    (hrequired : requirement ∈ kind.requiredWorldInterfaces) :
    requirement ∈ gate.worldInterfaces.supplied := by
  exact
    PNPBarrierRouteWorldInterfaces.mem_supplied_of_clearsAll
      hclears.2.1 hrequired

theorem PNPBarrierPromotionGate.clearsAll_requires_escape_witness
    {gate : PNPBarrierPromotionGate}
    (hclears : gate.ClearsAll)
    {kind : PNPBarrierKind}
    {witness : PNPBarrierEscapeWitness}
    (hrequired : witness ∈ kind.requiredEscapeWitnesses) :
    witness ∈ gate.escapeLedger.represented := by
  exact
    PNPBarrierEscapeLedger.mem_represented_of_clearsAll
      hclears.2.2 hrequired

theorem PNPBarrierPromotionGate.clearsAll_requires_replacement_obligations
    {gate : PNPBarrierPromotionGate}
    (hclears : gate.ClearsAll) :
    (gate.status.relativization = .cleared ∧
      gate.status.naturalProof = .cleared ∧
      gate.status.algebrization = .cleared) ∧
      (∀ {kind : PNPBarrierKind} {requirement : PNPBarrierWorldInterface},
        requirement ∈ kind.requiredWorldInterfaces →
          requirement ∈ gate.worldInterfaces.supplied) ∧
      (∀ {kind : PNPBarrierKind} {witness : PNPBarrierEscapeWitness},
        witness ∈ kind.requiredEscapeWitnesses →
          witness ∈ gate.escapeLedger.represented) := by
  exact
    ⟨PNPBarrierStatus.clearsAll_verdicts gate.status hclears.1,
      fun hrequired =>
        PNPBarrierPromotionGate.clearsAll_requires_world_interface hclears hrequired,
      fun hrequired =>
        PNPBarrierPromotionGate.clearsAll_requires_escape_witness hclears hrequired⟩

theorem PNPBarrierPromotionGate.not_clearsAll_of_missing_world_interface
    {gate : PNPBarrierPromotionGate}
    {kind : PNPBarrierKind}
    {requirement : PNPBarrierWorldInterface}
    (hrequired : requirement ∈ kind.requiredWorldInterfaces)
    (hmissing : requirement ∉ gate.worldInterfaces.supplied) :
    ¬ gate.ClearsAll := by
  intro hclears
  exact hmissing
    (PNPBarrierPromotionGate.clearsAll_requires_world_interface hclears hrequired)

theorem PNPBarrierPromotionGate.not_clearsAll_of_missing_escape_witness
    {gate : PNPBarrierPromotionGate}
    {kind : PNPBarrierKind}
    {witness : PNPBarrierEscapeWitness}
    (hrequired : witness ∈ kind.requiredEscapeWitnesses)
    (hmissing : witness ∉ gate.escapeLedger.represented) :
    ¬ gate.ClearsAll := by
  intro hclears
  exact hmissing
    (PNPBarrierPromotionGate.clearsAll_requires_escape_witness hclears hrequired)

theorem currentPNPKpolyPromotedPacket_stopGrade_and_replacement_gate_obligations :
    currentPNPKpolyCompressionBridgePromotedPacket.StopGrade ∧
      (∀ {gate : PNPBarrierPromotionGate},
        gate.ClearsAll →
          (gate.status.relativization = .cleared ∧
            gate.status.naturalProof = .cleared ∧
            gate.status.algebrization = .cleared) ∧
          (∀ {kind : PNPBarrierKind} {requirement : PNPBarrierWorldInterface},
            requirement ∈ kind.requiredWorldInterfaces →
              requirement ∈ gate.worldInterfaces.supplied) ∧
          (∀ {kind : PNPBarrierKind} {witness : PNPBarrierEscapeWitness},
            witness ∈ kind.requiredEscapeWitnesses →
              witness ∈ gate.escapeLedger.represented)) ∧
      ¬ currentPNPKpolyPromotedBarrierPromotionGate.ClearsAll := by
  exact
    ⟨stopGrade_currentPNPKpolyCompressionBridgePromotedPacket,
      fun hclears =>
        PNPBarrierPromotionGate.clearsAll_requires_replacement_obligations hclears,
      currentPNPKpolyPromotedBarrierPromotionGate_not_cleared⟩

end Mettapedia.Computability.PNP
