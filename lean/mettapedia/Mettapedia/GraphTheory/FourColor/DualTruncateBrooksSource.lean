import Mettapedia.GraphTheory.SubcubicCliqueDomain
import Mettapedia.GraphTheory.FourColor.DualTruncateInverseGeometry

/-!
# Uniform source choices after dual-and-truncate recognition

The recovered simple source is subcubic. For a connected target with
more than twelve vertices, inverse geometry gives a connected source
with more than four vertices, excluding the Brooks exception. Its three
vertex colours reconstruct actual target edge colours and complete GSLT
sweeps. No cyclic-cut supplier or source colour table is required.

Occurrence of the face cover remains a hypothesis. The factor-three
size decrease does not assert a Tait-to-Tait reduction.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateBrooksSource

open DualTruncateColoring DualTruncateInverse
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationEdgeBridge GoertzelV24TwoEdgeCutMinimality
open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace
open VertexConstructionGSLT

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {W F : Type u} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

theorem source_of_cliqueFree (S : RotationSystem.{u,u,u} W F) (hcubic : S.IsCubic)
    (hfree : (rotationPrimalGraph S).CliqueFree 4) : Nonempty (ThreeVertexColoring S) := by
  obtain ⟨c⟩ := SubcubicThreeColouring.colourable (rotationPrimalGraph S) (by
    intro v
    exact (SimpleGraph.degree_instance_independent (G := rotationPrimalGraph S) v _ _).trans_le
      (DualTruncateStructuralColoring.primal_degree_le_three S hcubic v)) hfree
  exact ⟨DualTruncateStructuralColoring.ofPrimalColouring S c⟩

theorem source_of_connected_large (S : RotationSystem.{u,u,u} W F) (hcubic : S.IsCubic)
    (hconn : (rotationPrimalGraph S).Connected) (hlarge : 4 < Fintype.card W) :
    Nonempty (ThreeVertexColoring S) := by
  have hdeg : ∀ v, (rotationPrimalGraph S).degree v ≤ 3 :=
    DualTruncateStructuralColoring.primal_degree_le_three S hcubic
  exact source_of_cliqueFree S hcubic
    (SubcubicCliqueDomain.cliqueFree_of_connected_card_gt (rotationPrimalGraph S)
      (fun v => (SimpleGraph.degree_instance_independent
        (G := rotationPrimalGraph S) v _ _).trans_le (hdeg v)) hconn hlarge)

variable (T : RotationSystem.{u,u,u} W F) (d : Data T) (htwo : OrbitFacesTwoSided T)

/-- Actual target size supplies the recovered source's exception-free
domain; source cyclic connectivity is not a hypothesis. -/
theorem inverse_source
    (hhex : ∀ x : T.D, ¬d.marked (dartOrbitFace T x) → (T.faceOrbit x).card = 6)
    (hconn : (rotationPrimalGraph T).Connected) (hlarge : 12 < Fintype.card W) :
    Nonempty (ThreeVertexColoring (source T d htwo)) := by
  have hsize := DualTruncateInverseGeometry.source_size T d htwo hhex
  have hsource : 4 < Fintype.card (SourceVertex T d) := by omega
  exact source_of_connected_large (source T d htwo)
    (DualTruncateInverseGeometry.source_cubic T d htwo hhex)
    (DualTruncateInverseGeometry.source_connected T d htwo hconn) hsource

include htwo in
theorem inverse_tait
    (hhex : ∀ x : T.D, ¬d.marked (dartOrbitFace T x) → (T.faceOrbit x).card = 6)
    (hconn : (rotationPrimalGraph T).Connected) (hlarge : 12 < Fintype.card W) :
    RotationSystemTaitColorable T := by
  obtain ⟨c⟩ := inverse_source T d htwo hhex hconn hlarge
  exact DualTruncateInverseGeometry.tait T d htwo c

include htwo in
/-- Recognition begins with an actual marked target-face cover. -/
theorem recognized_tait (hsphere : OrbitSphericalCubicMapData T)
    (hrotation : VertexRotationCyclic T) (cover : DualTruncateFaceCoverFrame.Cover T)
    (hconn : (rotationPrimalGraph T).Connected)
    (hhex : ∀ x : T.D, ¬cover.marked (dartOrbitFace T x) → (T.faceOrbit x).card = 6)
    (hlarge : 12 < Fintype.card W) : RotationSystemTaitColorable T :=
  inverse_tait T (fromCover T hsphere.cubic hrotation cover) htwo hhex hconn hlarge

theorem every_complete_sweep
    (hhex : ∀ x : T.D, ¬d.marked (dartOrbitFace T x) → (T.faceOrbit x).card = 6)
    (hconn : (rotationPrimalGraph T).Connected) (hlarge : 12 < Fintype.card W)
    (order : List W) (hn : order.Nodup) (he : order ≠ []) (hcover : ∀ w, visited order w) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed
        (RotationSystemExactTransport.cubic (rotation (source T d htwo)) T d.frame.dart
          (Equiv.refl W) (adapter_vertex T d htwo) (DualTruncateColoring.cubic _))
        (RotationSystemExactTransport.rotationCyclic (rotation (source T d htwo)) T d.frame.dart
          (Equiv.refl W) (adapter_vertex T d htwo) (adapter_rho T d htwo)
          (DualTruncateConstructionGSLT.rotationCyclic _)) order hn he hcover).trace)
      Fin.elim0 Fin.elim0 := by
  obtain ⟨c⟩ := inverse_source T d htwo hhex hconn hlarge
  exact DualTruncateInverseGeometry.every_complete_sweep T d htwo c order hn he hcover

end
end Mettapedia.GraphTheory.FourColor.DualTruncateBrooksSource
