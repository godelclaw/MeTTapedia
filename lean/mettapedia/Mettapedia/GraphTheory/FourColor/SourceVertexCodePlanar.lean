import Mettapedia.GraphTheory.FourColor.VertexCodeSourceSemantics
import Mettapedia.GraphTheory.FourColor.VertexSideEulerMass
import Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryConnectivity

/-!
# Source planarity is retained by the finite-prefix pruning

Encode an actual connected spherical cubic source, then decode it. The
geometric round trip transfers its Euler defect and connectedness, so the
lossless-prefix theorem now applies with hypotheses on the source itself.
No colouring of the source is assumed or used.
-/

namespace Mettapedia.GraphTheory.FourColor.SourceVertexCodePlanar

open GoertzelV24OpenTangleComposition GoertzelV24RotationCutDartDecomposition
open GoertzelV24FaceDualConnectedness GoertzelV24OrbitFaceCurvatureBulk
open VertexSideCappedComponents OpenTangleBoundaryConnectivity
open VertexCodeSourceGeometry VertexCodeSourceSemantics SourceVertexCodeTrace
open VertexCodeDartGeometry VertexCodeLosslessPruning
open GoertzelV24CompositeSeamMultigraph SerialTangleSmallCutTransfer
open OpenTangleReplacementEuler

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem.{u,u,u} V E} {inner : V → Prop}
variable {W I : Type*} [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]
variable {l : ℕ} {T : TwoSidedOpenTangleData W I (Fin 0) (Fin l)}
  {mi : Fin l ≃ BoundaryDart RS inner}

def sideComponents (outer : RetainedDart RS inner) :
    Quotient (BoundarySmallCutViability.componentSetoid
      (sideMultigraph (OpenTangleData.ofVertexSide RS inner outer))) ≃
      (SideGraph RS inner).ConnectedComponent :=
  Quot.congrRight (sideReach_iff_induce_reachable RS inner outer)

theorem model_planar (M : Model T mi)
    (hs : OrbitSphericalCubicMapData RS) (hc : (rotationPrimalGraph RS).Connected)
    (hr : VertexRotationCyclic RS) : VertexAttachmentTransfer.defect T = 0 := by
  let outer := M.dart (compact.symm T.outer)
  rw [source_defect M outer]
  unfold OpenTangleEulerPresentation.defect
  rw [VertexSideEulerMass.mass_eq_four_components RS hs hc hr]
  have hn := (Nat.card_congr (sideComponents outer)).trans
    (Nat.card_eq_fintype_card (α := (SideGraph RS inner).ConnectedComponent))
  rw [hn]
  omega

theorem model_connected (M : Model T mi) (hcover : ∀ v, inner v)
    (hc : (rotationPrimalGraph RS).Connected) : (sideMultigraph (asOpen T)).Connected := by
  let outer := M.dart (compact.symm T.outer)
  let f : (rotationPrimalGraph RS) →g SideGraph RS inner :=
    ⟨fun v => ⟨v, hcover v⟩, fun h => h⟩
  intro x y
  apply (source_reach M outer x y).mpr
  apply sideReach_of_induce_reachable RS inner outer
  exact (hc.preconnected (M.vertex x).1 (M.vertex y).1).map f

open TubeSlab.VertexTransfer

/-- Lossless finite-prefix pruning for the actual source class. In particular,
the theorem is independent of the source's Tait-colourability. -/
theorem source_prefixes_viable (hs : OrbitSphericalCubicMapData RS)
    (hc : (rotationPrimalGraph RS).Connected) (hr : VertexRotationCyclic RS)
    (order : List V) (hn : order.Nodup) (he : order ≠ [])
    (hcover : ∀ v, visited order v) :
    prefixesViable (encodeClosed hs.cubic hr order hn he hcover).trace = true := by
  let e := encodeClosed hs.cubic hr order hn he hcover
  exact prefixesViable_of_connected_planar e.trace
    (model_connected e.model hcover hc) (model_planar e.model hs hc hr)

/-- The existing minimality class supplies every source hypothesis. A complete
sweep and its surviving, geometry-faithful run are constructed, not assumed. -/
theorem class_covered
    (hclass : GoertzelV24TwoEdgeCutMinimality.BridgelessSphericalCubicMapData RS) :
    ∃ t : VertexCodeTrace.Trace 0,
      Nonempty (Model t.realize (terminalCoordinates (RS := RS) completeOrder visited_complete)) ∧
      prefixesViable t = true := by
  have hn : (completeOrder (V := V)).Nodup := Finset.nodup_toList _
  have he : completeOrder (V := V) ≠ [] := by
    intro h
    have hm := (visited_iff_mem _ _).mp (visited_complete (RS.vertOf RS.outer))
    rw [h] at hm
    exact List.not_mem_nil hm
  let e := encodeClosed hclass.spherical.cubic hclass.vertexRotationCyclic
    completeOrder hn he visited_complete
  exact ⟨e.trace, ⟨e.model⟩,
    source_prefixes_viable hclass.spherical hclass.primalConnected
      hclass.vertexRotationCyclic completeOrder hn he visited_complete⟩

end
end Mettapedia.GraphTheory.FourColor.SourceVertexCodePlanar
