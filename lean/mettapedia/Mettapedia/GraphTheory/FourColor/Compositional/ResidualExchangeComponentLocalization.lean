import Mettapedia.GraphTheory.ComponentAvoidance
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualCircuitPhysicalReachability

/-!
# Residual exchange changes only carrier-touching components

The residual graphs before and after a matching exchange have identical
adjacency away from the operated alternating carrier.  Hence every old
residual component which avoids the carrier survives with exactly the same
vertex support after exchange.  This is the cancellation boundary required
before comparing residual defect: only carrier-touching components can split,
merge, or change parity.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualExchangeComponentLocalization

open GoertzelV24AlternatingMatchingComponent
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualTwoFactor
open MatchingParity
open ResidualCircuitPhysicalReachability
open SimpleGraph

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The old and new residual adjacency relations agree at every vertex
outside the operated carrier. -/
theorem oldResidual_adj_iff_newResidual_of_not_mem_carrier
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second left right : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (hleft : left ∉ site.carrier) :
    (residualGraph G sigma).Adj left right ↔
      (residualGraph G
        (sigma.exchange site.tau site.carrier
          site.sigma_closed site.tau_closed)).Adj left right := by
  rw [oldResidualGraph_adj_iff_common_or_tau sigma site,
    newResidualGraph_adj_iff_common_or_sigma sigma hSigma site]
  simp only [hleft, false_and, or_false]

/-- An old residual component avoids the exchange carrier when none of the
carrier vertices is reachable from its root. -/
def OldComponentAvoidsCarrier
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : V) : Prop :=
  ∀ vertex, vertex ∈ site.carrier →
    ¬ (residualGraph G sigma).Reachable root vertex

/-- Reachability from an old component avoiding the carrier is identical
before and after exchange. -/
theorem oldResidual_reachable_iff_newResidual_of_avoids_carrier
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : V) (havoid : OldComponentAvoidsCarrier sigma site root)
    (target : V) :
    (residualGraph G sigma).Reachable root target ↔
      (residualGraph G
        (sigma.exchange site.tau site.carrier
          site.sigma_closed site.tau_closed)).Reachable root target := by
  apply Mettapedia.GraphTheory.reachable_iff_of_adj_iff_off_set
    (G := residualGraph G sigma)
    (H := residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed))
    (modified := (site.carrier : Set V))
  · exact havoid
  · intro left right hleft
    exact oldResidual_adj_iff_newResidual_of_not_mem_carrier
      sigma hSigma site (by simpa using hleft)

/-- Set-level cancellation: an avoiding residual component has exactly the
same support after exchange. -/
theorem oldResidual_connectedComponent_supp_eq_newResidual_of_avoids_carrier
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : V) (havoid : OldComponentAvoidsCarrier sigma site root) :
    ((residualGraph G sigma).connectedComponentMk root).supp =
      ((residualGraph G
        (sigma.exchange site.tau site.carrier
          site.sigma_closed site.tau_closed)).connectedComponentMk root).supp := by
  apply Mettapedia.GraphTheory.connectedComponentMk_supp_eq_of_adj_iff_off_set
    (G := residualGraph G sigma)
    (H := residualGraph G
      (sigma.exchange site.tau site.carrier
        site.sigma_closed site.tau_closed))
    (modified := (site.carrier : Set V))
  · exact havoid
  · intro left right hleft
    exact oldResidual_adj_iff_newResidual_of_not_mem_carrier
      sigma hSigma site (by simpa using hleft)

/-- The unchanged supports carry isomorphic induced component graphs, not
merely equal vertex sets. -/
def oldResidualComponentIsoNewResidual_of_avoids_carrier
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : V) (havoid : OldComponentAvoidsCarrier sigma site root) :
    ((residualGraph G sigma).connectedComponentMk root).toSimpleGraph ≃g
      ((residualGraph G
        (sigma.exchange site.tau site.carrier
          site.sigma_closed site.tau_closed)).connectedComponentMk root).toSimpleGraph where
  toEquiv := Equiv.setCongr
    (oldResidual_connectedComponent_supp_eq_newResidual_of_avoids_carrier
      sigma hSigma site root havoid)
  map_rel_iff' := by
    intro left right
    simp only [SimpleGraph.ConnectedComponent.toSimpleGraph,
      SimpleGraph.induce_adj]
    have houtside : left.1 ∉ site.carrier := by
      intro hleft
      exact havoid left.1 hleft
        (((residualGraph G sigma).connectedComponentMk root).reachable_of_mem_supp
          SimpleGraph.ConnectedComponent.connectedComponentMk_mem left.2)
    exact (oldResidual_adj_iff_newResidual_of_not_mem_carrier
      sigma hSigma site houtside).symm

/-- Consequently an avoiding component has the same colorability, and hence
the same bipartite/non-bipartite status, before and after exchange. -/
theorem oldResidualComponent_colorable_iff_newResidual_of_avoids_carrier
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : V) (havoid : OldComponentAvoidsCarrier sigma site root)
    (colorCount : Nat) :
    ((residualGraph G sigma).connectedComponentMk root).toSimpleGraph.Colorable
        colorCount ↔
      ((residualGraph G
        (sigma.exchange site.tau site.carrier
          site.sigma_closed site.tau_closed)).connectedComponentMk root).toSimpleGraph.Colorable
        colorCount := by
  let componentIso :=
    oldResidualComponentIsoNewResidual_of_avoids_carrier
      sigma hSigma site root havoid
  exact ⟨fun hcolor => SimpleGraph.Colorable.of_hom componentIso.symm.toHom hcolor,
    fun hcolor => SimpleGraph.Colorable.of_hom componentIso.toHom hcolor⟩

/-- Avoidance can equivalently be checked on the finite cyclic coordinate of
the alternating carrier. -/
theorem oldComponentAvoidsCarrier_iff_forall_cyclePosition
    (sigma : Pairing V) {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (root : V) :
    OldComponentAvoidsCarrier sigma site root ↔
      ∀ position : CyclePosition sigma site,
        ¬ (residualGraph G sigma).Reachable root
          (cycleVertexOrder sigma site position).1 := by
  constructor
  · intro havoid position
    exact havoid _ (cycleVertexOrder sigma site position).2
  · intro havoid vertex hvertex
    let position : CyclePosition sigma site :=
      (cycleVertexOrder sigma site).symm ⟨vertex, hvertex⟩
    have hposition : (cycleVertexOrder sigma site position).1 = vertex := by
      exact congrArg Subtype.val
        ((cycleVertexOrder sigma site).apply_symm_apply ⟨vertex, hvertex⟩)
    simpa only [hposition] using havoid position

end

end ResidualExchangeComponentLocalization

end Mettapedia.GraphTheory.FourColor.Compositional
