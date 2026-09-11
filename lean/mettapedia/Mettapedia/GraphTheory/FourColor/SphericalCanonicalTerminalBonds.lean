import Mettapedia.GraphTheory.FourColor.CanonicalTerminalBonds
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationMultigraphAdapter
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality
import Mettapedia.GraphTheory.FourColor.NestedCyclicCutStrictness

/-!
# Canonical terminal cuts supply genuine spherical interfaces

The canonical finite minimization may split arbitrary off-terminal cap
material. Connected terminal sets force its two shores connected, hence
the existing planar-bond theorem supplies the full first-return orders.
Advancing terminals supplies strictly nested original incident-edge shores.

No cut, connected shore, cyclic order, or cut-width bound is assumed as a
supplier. Terminal geometry is still an input. This does not bound the
optimal widths or prove equal Count states or a shortening.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalCanonicalTerminalBonds

open SimpleGraph SimpleGraphDartRotation CanonicalTerminalCuts CanonicalTerminalBonds
open GoertzelV24RotationMultigraphAdapter GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24FaceDualConnectedness GoertzelV24TwoEdgeCutMinimality
open GoertzelV24OrbitFaceTwoSided GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24ComplementaryRegionBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24ConnectedVertexSideEdgeShore

noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G

theorem step_iff (data : Data G) (u v : V) :
    (toMultigraph data.toRotationSystem).Step u v ↔ G.Adj u v := by
  simpa only [rotationPrimalGraph_toRotationSystem_eq] using
    step_iff_primal_adj data.toRotationSystem u v

/-- The actual optimal cut has both connected shores. -/
theorem connected_sides (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (A B : Finset V) (hA : (G.induce (↑A : Set V)).Connected)
    (hB : (G.induce (↑B : Set V)).Connected) (hAB : Disjoint A B) :
    let S := canonical (toMultigraph data.toRotationSystem) A B hAB
    (G.induce (↑S : Set V)).Connected ∧ (G.induce (↑Sᶜ : Set V)).Connected := by
  have hG : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using ambient.primalConnected
  exact canonical_bond _ G (step_iff data) hG A B hA hB hAB

/-- Boundary order is derived on every original crossing dart. -/
theorem full_boundary_orders (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (A B : Finset V) (hA : (G.induce (↑A : Set V)).Connected)
    (hB : (G.induce (↑B : Set V)).Connected) (hAB : Disjoint A B) :
    let S := canonical (toMultigraph data.toRotationSystem) A B hAB
    CutFacesHaveUniqueRetainedBoundaryDart data.toRotationSystem Sᶜ ∧
      retainedRegionBoundarySuccessor data.toRotationSystem (deletedRegionKeep Sᶜ) =
        (deletedRegionBoundarySuccessor data.toRotationSystem Sᶜ)⁻¹ := by
  let S := canonical (toMultigraph data.toRotationSystem) A B hAB
  have hc := connected_sides data ambient A B hA hB hAB
  have hkeep : {v | deletedRegionKeep Sᶜ v} = (↑S : Set V) := by
    ext v
    simp [deletedRegionKeep]
  have hnot : {v | ¬ deletedRegionKeep Sᶜ v} = (↑Sᶜ : Set V) := by
    ext v
    simp [deletedRegionKeep]
  have hret : (G.induce {v | deletedRegionKeep Sᶜ v}).Connected := hkeep ▸ hc.1
  have hdel : (G.induce {v | ¬ deletedRegionKeep Sᶜ v}).Connected := hnot ▸ hc.2
  have hG : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using ambient.primalConnected
  exact ⟨cutFacesHaveUniqueRetainedBoundaryDart_of_planar_bond data Sᶜ
      ambient.spherical htwo hG ambient.vertexRotationCyclic hret hdel,
    retained_boundarySuccessor_eq_deleted_inverse_of_planar_bond data Sᶜ
      ambient.spherical htwo hG ambient.vertexRotationCyclic hret hdel⟩

/-- Terminal progress is strict on the full incident-edge shores as well
as on vertex sides. This is the nesting consumed by the Count-node route. -/
theorem full_shores_strict (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    {A B A' B' : Finset V}
    (hA : (G.induce (↑A : Set V)).Connected) (hB : (G.induce (↑B : Set V)).Connected)
    (hB' : (G.induce (↑B' : Set V)).Connected)
    (hAB : Disjoint A B) (hAB' : Disjoint A' B')
    (hAA : A ⊆ A') (hBB : B' ⊆ B) (hmove : ∃ v, v ∈ B ∧ v ∈ A') :
    let S := canonical (toMultigraph data.toRotationSystem) A B hAB
    let T := canonical (toMultigraph data.toRotationSystem) A' B' hAB'
    S ⊂ T ∧ incidentEdgeShore G (· ∈ S) ⊂ incidentEdgeShore G (· ∈ T) := by
  let g := toMultigraph data.toRotationSystem
  let S := canonical g A B hAB
  let T := canonical g A' B' hAB'
  have hs : S ⊂ T := canonical_ssubset g hAB hAB' hAA hBB hmove
  obtain ⟨v, hvT, hvS⟩ := Finset.exists_of_ssubset hs
  obtain ⟨b⟩ := hB'.nonempty
  have hb : b.val ∉ T := fun h =>
    Finset.disjoint_left.mp (canonical_spec g A' B' hAB').feasible.2 h b.property
  have hc := (connected_sides data ambient A B hA hB hAB).2.preconnected
  have hcomp : (G.induce {v | v ∉ S}).Preconnected := by
    have heq : {v | v ∉ S} = (↑Sᶜ : Set V) := by ext v; simp
    rw [heq]
    exact hc
  exact ⟨hs, NestedCyclicCutStrictness.incidentEdgeShore_ssubset
    hs.subset ⟨v, hvT, hvS⟩ ⟨b, hb⟩ hcomp⟩

end
end Mettapedia.GraphTheory.FourColor.SphericalCanonicalTerminalBonds
