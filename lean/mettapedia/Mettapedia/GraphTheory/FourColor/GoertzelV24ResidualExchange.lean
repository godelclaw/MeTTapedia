import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualDefectDescent

/-!
# Exact residual effect of a matching exchange

For a graph-supported perfect matching, the residual graph is obtained by
deleting the matching edges.  If `sigma` is exchanged with another pairing
`tau` on a vertex set closed under both pairings, the residual graph changes
by symmetric difference with the alternating carrier selected by that set.

This is the exact local law needed before any wall-facing residual-defect
argument.  It does not assert that exchange decreases residual defect: the
exchange may split, merge, or reroute residual components.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ResidualExchange

open SimpleGraph MatchingParity
open scoped symmDiff
open GoertzelV24ResidualTwoFactor

variable {V : Type*}
variable {G : SimpleGraph V}

/-- The one-regular simple graph carried by a pairing. -/
def pairingGraph (sigma : Pairing V) : SimpleGraph V where
  Adj v w := sigma.partner v = w
  symm := ⟨by
    intro v w h
    rw [← h]
    exact sigma.partner_partner v⟩
  loopless := ⟨fun v h => sigma.partner_ne v h⟩

@[simp] theorem pairingGraph_adj (sigma : Pairing V) {v w : V} :
    (pairingGraph sigma).Adj v w ↔ sigma.partner v = w := Iff.rfl

variable [DecidableEq V]

/-- The alternating carrier selected by a vertex set: retain, inside the set,
exactly the edges on which the two pairings differ. -/
def exchangeCarrier (sigma tau : Pairing V) (s : Finset V) : SimpleGraph V :=
  { Adj := fun v w =>
      v ∈ s ∧ w ∈ s ∧ (pairingGraph sigma ∆ pairingGraph tau).Adj v w
    symm := ⟨by
      rintro v w ⟨hv, hw, hadj⟩
      exact ⟨hw, hv, hadj.symm⟩⟩
    loopless := ⟨by
      rintro v ⟨_, _, hadj⟩
      exact hadj.ne rfl⟩ }

omit [DecidableEq V] in
@[simp] theorem exchangeCarrier_adj (sigma tau : Pairing V) (s : Finset V)
    {v w : V} :
    (exchangeCarrier sigma tau s).Adj v w ↔
      v ∈ s ∧ w ∈ s ∧ (pairingGraph sigma ∆ pairingGraph tau).Adj v w := Iff.rfl

/-- Exchanging a graph-supported pairing changes its residual graph by
symmetric difference with precisely the selected alternating carrier. -/
theorem residualGraph_exchange_eq_symmDiff
    (sigma tau : Pairing V) (s : Finset V)
    (hσs : ∀ v ∈ s, sigma.partner v ∈ s)
    (hτs : ∀ v ∈ s, tau.partner v ∈ s)
    (hσG : sigma.SupportedBy G) (hτG : tau.SupportedBy G) :
    residualGraph G (sigma.exchange tau s hσs hτs) =
      residualGraph G sigma ∆ exchangeCarrier sigma tau s := by
  ext v w
  by_cases hv : v ∈ s
  · by_cases hw : w ∈ s
    · simp only [residualGraph_adj, symmDiff_def, exchangeCarrier,
        pairingGraph]
      rw [Pairing.exchange_of_mem sigma tau s hσs hτs hv]
      by_cases hp : sigma.partner v = w
      · have hGvw : G.Adj v w := hp ▸ hσG v
        simp [hv, hw, hp, hGvw]
      · by_cases hq : tau.partner v = w
        · have hGvw : G.Adj v w := hq ▸ hτG v
          simp [hv, hw, hp, hq, hGvw]
        · simp [hv, hw, hp, hq]
    · have hp : sigma.partner v ≠ w := by
        intro h
        exact hw (h ▸ hσs v hv)
      have hq : tau.partner v ≠ w := by
        intro h
        exact hw (h ▸ hτs v hv)
      simp only [residualGraph_adj, symmDiff_def, exchangeCarrier,
        pairingGraph]
      rw [Pairing.exchange_of_mem sigma tau s hσs hτs hv]
      simp [hv, hw, hp, hq]
  · simp only [residualGraph_adj, symmDiff_def, exchangeCarrier,
      pairingGraph]
    rw [Pairing.exchange_of_notMem sigma tau s hσs hτs hv]
    simp [hv]

/-- Consumer-facing exchange receipt: the exchanged pairing remains supported
by the ambient graph and has the stated residual graph. -/
theorem exchange_supportedBy_and_residualGraph_eq_symmDiff
    (sigma tau : Pairing V) (s : Finset V)
    (hσs : ∀ v ∈ s, sigma.partner v ∈ s)
    (hτs : ∀ v ∈ s, tau.partner v ∈ s)
    (hσG : sigma.SupportedBy G) (hτG : tau.SupportedBy G) :
    (sigma.exchange tau s hσs hτs).SupportedBy G ∧
      residualGraph G (sigma.exchange tau s hσs hτs) =
        residualGraph G sigma ∆ exchangeCarrier sigma tau s :=
  ⟨Pairing.exchange_supportedBy sigma tau s hσs hτs hσG hτG,
    residualGraph_exchange_eq_symmDiff sigma tau s hσs hτs hσG hτG⟩

/-- Inside the exchanged carrier, the new residual adjacency is exactly the
residual adjacency of the incoming pairing. -/
theorem residualGraph_exchange_adj_of_mem
    (sigma tau : Pairing V) (s : Finset V)
    (hσs : ∀ v ∈ s, sigma.partner v ∈ s)
    (hτs : ∀ v ∈ s, tau.partner v ∈ s)
    {v w : V} (hv : v ∈ s) :
    (residualGraph G (sigma.exchange tau s hσs hτs)).Adj v w ↔
      (residualGraph G tau).Adj v w := by
  simp only [residualGraph_adj]
  rw [Pairing.exchange_of_mem sigma tau s hσs hτs hv]

/-- Outside the exchanged carrier, residual adjacency is unchanged. -/
theorem residualGraph_exchange_adj_of_notMem
    (sigma tau : Pairing V) (s : Finset V)
    (hσs : ∀ v ∈ s, sigma.partner v ∈ s)
    (hτs : ∀ v ∈ s, tau.partner v ∈ s)
    {v w : V} (hv : v ∉ s) :
    (residualGraph G (sigma.exchange tau s hσs hτs)).Adj v w ↔
      (residualGraph G sigma).Adj v w := by
  simp only [residualGraph_adj]
  rw [Pairing.exchange_of_notMem sigma tau s hσs hτs hv]

end GoertzelV24ResidualExchange

end Mettapedia.GraphTheory.FourColor
