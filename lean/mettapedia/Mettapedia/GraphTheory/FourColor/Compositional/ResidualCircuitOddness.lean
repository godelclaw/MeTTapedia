import Mettapedia.GraphTheory.FourColor.Compositional.ResidualCircuitComponentDecomposition
import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualOddness

/-!
# Odd residual components as finite circuit states

The circuit state at an alternating matching exchange now has a literal
physical interpretation.  This file connects its `ZMod 2` parity coordinate
to the two equivalent descriptions used by residual-defect descent: membership
in `oddComponents` and failure of two-colourability of the corresponding
residual component.

No monotonicity is asserted.  These equivalences expose the exact finite-state
observable that a later wall argument must control.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualCircuitOddness

open GoertzelV24AlternatingMatchingComponent
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualOddness
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualTwoFactor
open MatchingParity
open ResidualCircuitComponentDecomposition
open ResidualCircuitParity
open SimpleGraph

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The old finite circuit has parity one exactly when its physical residual
component belongs to `oddComponents`. -/
theorem oldCircuitParity_eq_one_iff_mem_oddComponents
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : CyclePosition sigma site) :
    oldCircuitParity hG sigma hSigma site root = 1 ↔
      (residualGraph G sigma).connectedComponentMk
          (cycleVertexOrder sigma site root).1 ∈
        (residualGraph G sigma).oddComponents := by
  change oldCircuitParity hG sigma hSigma site root = 1 ↔
    Odd ((residualGraph G sigma).connectedComponentMk
      (cycleVertexOrder sigma site root).1).supp.ncard
  rw [← oldResidual_component_cardParity_eq_oldCircuitParity,
    ZMod.natCast_eq_one_iff_odd]

/-- The new finite circuit has parity one exactly when its physical residual
component after exchange belongs to `oddComponents`. -/
theorem newCircuitParity_eq_one_iff_mem_oddComponents
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : CyclePosition sigma site) :
    newCircuitParity hG sigma hSigma site root = 1 ↔
      (residualGraph G
        (sigma.exchange site.tau site.carrier
          site.sigma_closed site.tau_closed)).connectedComponentMk
            (cycleVertexOrder sigma site root).1 ∈
        (residualGraph G
          (sigma.exchange site.tau site.carrier
            site.sigma_closed site.tau_closed)).oddComponents := by
  change newCircuitParity hG sigma hSigma site root = 1 ↔
    Odd ((residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed)).connectedComponentMk
          (cycleVertexOrder sigma site root).1).supp.ncard
  rw [← newResidual_component_cardParity_eq_newCircuitParity,
    ZMod.natCast_eq_one_iff_odd]

/-- Equivalently, old circuit parity one is exactly non-two-colourability of
the corresponding residual component. -/
theorem oldCircuitParity_eq_one_iff_component_not_colorable
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : CyclePosition sigma site) :
    oldCircuitParity hG sigma hSigma site root = 1 ↔
      ¬ ((residualGraph G sigma).connectedComponentMk
        (cycleVertexOrder sigma site root).1).toSimpleGraph.Colorable 2 := by
  classical
  letI : DecidableRel (residualGraph G sigma).Adj := Classical.decRel _
  let component := (residualGraph G sigma).connectedComponentMk
    (cycleVertexOrder sigma site root).1
  have htwo : ∀ vertex,
      ((residualGraph G sigma).neighborSet vertex).ncard = 2 := by
    intro vertex
    simpa only [Set.ncard_eq_toFinset_card', SimpleGraph.neighborFinset_def] using
      card_neighborFinset_residualGraph_eq_two hG sigma hSigma vertex
  have hcolor := connectedComponent_colorable_two_iff_even_supp htwo component
  rw [← oldResidual_component_cardParity_eq_oldCircuitParity,
    ZMod.natCast_eq_one_iff_odd, ← Nat.not_even_iff_odd]
  simpa only [component] using not_congr hcolor.symm

/-- The same non-two-colourability characterization after exchange. -/
theorem newCircuitParity_eq_one_iff_component_not_colorable
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : CyclePosition sigma site) :
    newCircuitParity hG sigma hSigma site root = 1 ↔
      ¬ ((residualGraph G
        (sigma.exchange site.tau site.carrier
          site.sigma_closed site.tau_closed)).connectedComponentMk
            (cycleVertexOrder sigma site root).1).toSimpleGraph.Colorable 2 := by
  classical
  let exchanged := sigma.exchange site.tau site.carrier
    site.sigma_closed site.tau_closed
  letI : DecidableRel (residualGraph G exchanged).Adj := Classical.decRel _
  have hExchanged : exchanged.SupportedBy G :=
    Pairing.exchange_supportedBy sigma site.tau site.carrier
      site.sigma_closed site.tau_closed hSigma site.tau_supported
  let component := (residualGraph G exchanged).connectedComponentMk
    (cycleVertexOrder sigma site root).1
  have htwo : ∀ vertex,
      ((residualGraph G exchanged).neighborSet vertex).ncard = 2 := by
    intro vertex
    simpa only [Set.ncard_eq_toFinset_card', SimpleGraph.neighborFinset_def] using
      card_neighborFinset_residualGraph_eq_two hG exchanged hExchanged vertex
  have hcolor := connectedComponent_colorable_two_iff_even_supp htwo component
  rw [← newResidual_component_cardParity_eq_newCircuitParity,
    ZMod.natCast_eq_one_iff_odd, ← Nat.not_even_iff_odd]
  simpa only [component, exchanged] using not_congr hcolor.symm

end

end ResidualCircuitOddness

end Mettapedia.GraphTheory.FourColor.Compositional
