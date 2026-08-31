import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceCutTrailTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24WalkFaceCut

/-!
# Exact face cuts in a finite combinatorial map

This module gives stable, semantic names to the face-side construction used
by the compositional four-colour development.  An `ExactFaceCut` is a labeling
of facial orbits whose value changes across precisely the selected primal
edges.  It is independent of the particular route that produced the cut.

The current implementation is backed by the established rotation-system
library in `GraphTheory.FourColor`; the declarations here are the migration
surface for moving that generic map theory out of the theorem-specific tree.
-/

namespace Mettapedia.GraphTheory.Embedding

open Mettapedia.GraphTheory.FourColor
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceBoundaryLinearAlgebra
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence
open Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCurvatureBulk
open Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceTwoSided
open Mettapedia.GraphTheory.FourColor.GoertzelV24WalkFaceCut
open Mettapedia.GraphTheory.FourColor.GoertzelV24WalkCycleParity
open Mettapedia.GraphTheory.FourColor.SimpleGraphDartRotation
open SimpleGraph

noncomputable section

/-- A labeling of facial orbits that changes value across exactly the
selected primal edges. -/
structure ExactFaceCut
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (selected : E → Prop) (A : Type*) where
  label : OrbitFace RS → A
  separates : ∀ dart : RS.D,
    label (dartOrbitFace RS dart) ≠
        label (dartOrbitFace RS (RS.alpha dart)) ↔
      selected (RS.edgeOf dart)

namespace ExactFaceCut

variable {V E A : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
  {RS : RotationSystem V E} {selected : E → Prop}

/-- Over `F2`, the two face labels adjacent to a dart sum to one exactly
when its primal edge belongs to the cut.  This is the additive form of
`ExactFaceCut.separates`. -/
theorem label_add_opposite_eq_one_iff_selected
    (cut : ExactFaceCut RS selected F2) (dart : RS.D) :
    cut.label (dartOrbitFace RS dart) +
        cut.label (dartOrbitFace RS (RS.alpha dart)) = 1 ↔
      selected (RS.edgeOf dart) := by
  rw [f2_add_eq_one_iff_ne]
  exact cut.separates dart

/-- The same binary jump law expressed between a dart face and the face
following the dart in the vertex rotation. -/
theorem label_add_rotation_eq_one_iff_selected
    (cut : ExactFaceCut RS selected F2) (dart : RS.D) :
    cut.label (dartOrbitFace RS dart) +
        cut.label (dartOrbitFace RS (RS.rho dart)) = 1 ↔
      selected (RS.edgeOf dart) := by
  rw [← dartOrbitFace_alpha_eq_dartOrbitFace_rho RS dart]
  exact cut.label_add_opposite_eq_one_iff_selected dart

/-- Crossing an unselected edge preserves the face label. -/
theorem label_eq_opposite_of_not_selected
    (cut : ExactFaceCut RS selected A) (dart : RS.D)
    (hnot : ¬selected (RS.edgeOf dart)) :
    cut.label (dartOrbitFace RS dart) =
      cut.label (dartOrbitFace RS (RS.alpha dart)) := by
  exact GoertzelV24FaceCutTransport.labels_eq_alpha_of_not_cut
    RS cut.label selected cut.separates dart hnot

/-- Following a finite nonbacktracking trail of unselected edges in a cubic
map preserves the face label from the first oriented side to the opposite
side of the last dart. -/
theorem label_eq_along_nonbacktracking_trail
    (cut : ExactFaceCut RS selected A)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (darts : List RS.D) (hne : darts ≠ [])
    (hchain : darts.IsChain RS.FaceCutTrailStep)
    (hnot : ∀ dart ∈ darts, ¬selected (RS.edgeOf dart)) :
    cut.label (dartOrbitFace RS (darts.head hne)) =
      cut.label (dartOrbitFace RS (RS.alpha (darts.getLast hne))) := by
  exact RS.labels_eq_head_alpha_getLast_of_faceCutTrail
    hcubic hrotation cut.label selected cut.separates darts hne hchain hnot

end ExactFaceCut

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every closed trail in a connected cellular sphere map determines an
exact binary face cut supported on precisely the trail edges.  The accompanying
linear equation records the canonical `F2` boundary representation. -/
theorem exists_exactFaceCut_of_closedTrail
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    {vertex : V} (walk : G.Walk vertex vertex) (htrail : walk.IsTrail) :
    ∃ cut : ExactFaceCut data.toRotationSystem
        (fun edge : G.edgeSet ↦ edge.1 ∈ walk.edges) F2,
      orbitFaceBoundaryLinearMap data.toRotationSystem cut.label =
        walkEdgeParity walk := by
  rcases exists_orbitFaceLabeling_ne_alpha_iff_mem_edges_of_isTrail
      data htwoSided hdual hconnected hsphere walk htrail with
    ⟨label, hboundary, hexact⟩
  exact ⟨⟨label, hexact⟩, hboundary⟩

end

end Mettapedia.GraphTheory.Embedding
