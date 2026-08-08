import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedWeightedCurvature

/-!
# The internal annular dual as a two-face deletion

The internal facial dual of an embedded source trail is not a second,
unrelated graph.  It is canonically isomorphic to the full quotient facial
dual induced on every face except the two named container holes.  This
identifies the remaining connectivity premise of framed weighted L1 with the
topological statement that deleting the two container faces leaves the dual
connected.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceOrbitIncidence
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- A retained internal face, regarded as a full quotient face together with
the proof that it is not one of the two holes. -/
def internalFaceToFullFace {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    AmbientFace embedded.cellulation.interiorFaces ≃
      {face : AmbientFace
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem)) //
        face.1 ∈ embedded.cellulation.interiorFaces} where
  toFun face := ⟨⟨face.1, Finset.mem_univ _⟩, face.2⟩
  invFun face := ⟨face.1.1, face.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Restricting the full facial dual to non-hole faces gives exactly the
internal annular dual. -/
def interiorDualIsoFullDualInduce {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        embedded.cellulation.interiorFaces ≃g
      (interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).induce
        (fun face => face.1 ∈ embedded.cellulation.interiorFaces) where
  toEquiv := embedded.internalFaceToFullFace
  map_rel_iff' := by
    intro left right
    let boundary := orbitFaceBoundary
      embedded.cellulation.rotation.toRotationSystem
    constructor
    · intro hfull
      change (interiorDualGraph boundary
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
          ⟨left.1, Finset.mem_univ _⟩ ⟨right.1, Finset.mem_univ _⟩ at hfull
      rcases (interiorDualGraph_adj_iff boundary
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).1
          hfull with ⟨hne, edge, _hinterior, hleft, hright⟩
      exact
        interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
          boundary embedded.cellulation.interiorFaces
          embedded.internalFace_incidence_le_two hne hleft hright
    · intro hinternal
      rcases (interiorDualGraph_adj_iff boundary
        embedded.cellulation.interiorFaces).1 hinternal with
          ⟨hne, edge, _hinterior, hleft, hright⟩
      change (interiorDualGraph boundary
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Adj
          ⟨left.1, Finset.mem_univ _⟩ ⟨right.1, Finset.mem_univ _⟩
      exact
        interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
          boundary
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem))
          (orbitFace_incidence_le_two
            embedded.cellulation.rotation.toRotationSystem)
          hne hleft hright

/-- The corridor connectivity premise is equivalent to connectedness of the
full facial dual after retaining exactly the non-hole faces. -/
theorem internalDualConnected_iff_fullDualInduceConnected
    {source : SourceTrail G} (embedded : source.AnnularEmbedding) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      embedded.cellulation.interiorFaces).Connected ↔
      ((interiorDualGraph
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))).induce
        (fun face => face.1 ∈ embedded.cellulation.interiorFaces)).Connected :=
  embedded.interiorDualIsoFullDualInduce.connected_iff

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
