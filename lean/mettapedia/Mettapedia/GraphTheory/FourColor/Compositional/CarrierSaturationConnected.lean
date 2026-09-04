import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnComponentSaturation
import Mettapedia.GraphTheory.FourColor.Compositional.PathPrefixBoundary

/-!
# Connectedness of a component-saturated carrier prefix

The selected carrier coordinates before a sweep cut are an ordinary prefix
of the simple path obtained by opening the alternating cycle.  Hence they
form a connected boundary skeleton.  Filling every common-residual component
whose paired endpoints are selected preserves that connectedness by the
generic pairing-saturation theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace CarrierSaturationConnected

open GoertzelV24OrderedMeshResidualSiteFacialBond
open GoertzelV24OrderedMeshResidualSiteMatching
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnPairing
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24ResidualReturnShore
open MatchingParity
open Mettapedia.GraphTheory
open PathPrefixBoundary
open ResidualReturnComponentSaturation
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The same numerical cut, expressed in the ordinary walk coordinates of
the carrier cycle with its initial vertex removed. -/
def carrierPrefixPathCut
    {sigma : Pairing V} {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) : Fin (site.cycle.tail.length + 1) :=
  ⟨cut.val, by
    simpa only [SimpleGraph.Walk.length_support] using cut.isLt⟩

@[simp] theorem carrierPrefixPathCut_val
    {sigma : Pairing V} {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    (carrierPrefixPathCut site cut).val = cut.val :=
  rfl

/-- The selected cyclic carrier vertices are exactly an ordinary strict
prefix of the simple path `site.cycle.tail`. -/
theorem carrierPrefixBoundarySide_eq_pathPrefixSide
    {sigma : Pairing V} {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) :
    (fun vertex => ∃ position : CyclePosition sigma site,
      carrierPrefixSelected cut position ∧
        (cycleVertexOrder sigma site position).1 = vertex) =
      pathPrefixSide site.cycle.tail (carrierPrefixPathCut site cut) := by
  funext vertex
  apply propext
  constructor
  · rintro ⟨position, hposition, rfl⟩
    let coordinate : Fin (site.cycle.tail.length + 1) :=
      ⟨position.val, by
        simpa only [SimpleGraph.Walk.length_support] using position.isLt⟩
    refine ⟨coordinate, ?_, ?_⟩
    · apply Fin.mk_lt_mk.mpr
      exact hposition
    · rw [cycleVertexOrder_apply_val]
      symm
      simpa only [List.get_eq_getElem] using
        site.cycle.tail.support_getElem_eq_getVert position.isLt
  · rintro ⟨coordinate, hcoordinate, heq⟩
    let position : CyclePosition sigma site :=
      ⟨coordinate.val, by
        simpa only [SimpleGraph.Walk.length_support] using coordinate.isLt⟩
    refine ⟨position, ?_, ?_⟩
    · apply Fin.mk_lt_mk.mpr
      exact hcoordinate
    · rw [cycleVertexOrder_apply_val]
      calc
        site.cycle.tail.support.get position =
            site.cycle.tail.getVert coordinate := by
          simpa only [List.get_eq_getElem] using
            site.cycle.tail.support_getElem_eq_getVert position.isLt
        _ = vertex := heq

/-- A nonempty selected carrier prefix is connected in the ambient graph. -/
theorem induce_carrierPrefixBoundarySide_connected
    {sigma : Pairing V} {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) (hcut : 0 < cut.val) :
    (G.induce (fun vertex => ∃ position : CyclePosition sigma site,
      carrierPrefixSelected cut position ∧
        (cycleVertexOrder sigma site position).1 = vertex)).Connected := by
  rw [carrierPrefixBoundarySide_eq_pathPrefixSide site cut]
  exact induce_pathPrefixSide_connected site.cycle_isCycle.isPath_tail
    (carrierPrefixPathCut site cut) hcut

/-- Filling completed common-residual return components preserves the
connectedness of a positive carrier prefix. -/
theorem induce_carrierPrefixReturnSaturation_connected
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingSiteWitness G sigma first second)
    (cut : CyclePosition sigma site) (hcut : 0 < cut.val) :
    (G.induce
      (carrierPrefixReturnSaturation hG sigma hSigma site cut)).Connected := by
  apply induce_pairingBoundarySaturation_connected
    (H := commonResidualGraph G sigma site)
    (fun position => (cycleVertexOrder sigma site position).1)
    (orderedSiteReturnPairing hG sigma hSigma site)
    (carrierPrefixSelected cut)
    (commonResidualGraph_le sigma site)
  exact induce_carrierPrefixBoundarySide_connected site cut hcut

end

end CarrierSaturationConnected

end Mettapedia.GraphTheory.FourColor.Compositional
