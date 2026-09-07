import Mettapedia.GraphTheory.FourColor.MarkedSeamFaces
import Mettapedia.GraphTheory.FourColor.SphericalMeshFreeSeam

/-!
# Ordered mesh or a smaller Count map retaining designated faces

The designated data are ambient face roots. Their complete facial darts,
edge reversals and base vertices are computed internally, then supplied to
the geometric seam construction. Thus neither marks, a seam nor a facial
transport is a supplied hypothesis. The Count predicate here remains the
ordinary closed-map predicate, not a frozen-colour refinement.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalMarkedFaceReduction

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationMultigraphAdapter GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24SimpleGraphTaitBridge GoertzelV24MajorityShorePhysicalReplacement
open GoertzelV24ConnectedEdgeShoreMajority
open MarkedCotreeSeam SphericalMeshFreeSeam

noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Every dart of every designated face, including repeated vertex visits. -/
def faceDarts (rotation : Data G) (holes : Finset G.Dart) : Finset G.Dart :=
  holes.biUnion rotation.toRotationSystem.faceOrbit

/-- Both ends of every edge of a designated face. -/
def edgeDarts (rotation : Data G) (holes : Finset G.Dart) : Finset G.Dart :=
  faceDarts rotation holes ∪ (faceDarts rotation holes).image rotation.toRotationSystem.alpha

/-- These vertices, computed from the designated faces, cannot be deleted. -/
def vertexMarks (rotation : Data G) (holes : Finset G.Dart) : Finset V :=
  (edgeDarts rotation holes).image (fun d => d.fst)

theorem edgeDarts_alpha (rotation : Data G) (holes : Finset G.Dart)
    {d : G.Dart} (hd : d ∈ edgeDarts rotation holes) :
    rotation.toRotationSystem.alpha d ∈ edgeDarts rotation holes := by
  rcases Finset.mem_union.mp hd with hd | hd
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_union_left _ (by simpa using he)

theorem faceDarts_mem (rotation : Data G) (holes : Finset G.Dart)
    {root e : G.Dart} (hr : root ∈ holes) (he : e ∈ rotation.toRotationSystem.faceOrbit root) :
    e ∈ edgeDarts rotation holes :=
  Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨root, hr, he⟩)

/-- A physical, rooted, length-preserving identification of one entire face.
The iteration equation records cyclic order, not just equal cardinality. -/
def PreservesFace {rotation : Data G} {marks : Finset V} {M : Type*}
    {mark : M → G.Dart} {w : ℕ} (pair : SeamPair rotation marks mark w) (root : G.Dart) : Prop :=
  ∃ d : pair.candidate.D, pair.ambientDart d = root ∧
    (pair.candidate.faceOrbit d).image pair.ambientDart = rotation.toRotationSystem.faceOrbit root ∧
    (pair.candidate.faceOrbit d).card = (rotation.toRotationSystem.faceOrbit root).card ∧
    ∀ n : ℕ, pair.ambientDart ((pair.candidate.phi ^ n) d) =
      (rotation.toRotationSystem.phi ^ n) root

/-- The marking convention discharges all face-transport premises on the
actual seam returned by either geometric branch. -/
theorem preservesFace (rotation : Data G) (holes : Finset G.Dart) {w : ℕ}
    (pair : SeamPair rotation (vertexMarks rotation holes)
      (Subtype.val : ↥(edgeDarts rotation holes) → G.Dart) w)
    {root : G.Dart} (hr : root ∈ holes) : PreservesFace pair root := by
  apply pair.designated_face_survives
  · intro m
    exact Finset.mem_image.mpr ⟨m.val, m.property, rfl⟩
  · intro m
    exact ⟨⟨rotation.toRotationSystem.alpha m.val, edgeDarts_alpha rotation holes m.property⟩, rfl⟩
  · intro e he
    exact ⟨⟨e, faceDarts_mem rotation holes hr he⟩, rfl⟩

/-- Every vertex visit of every designated face is outside the deleted slab.
Faces are allowed to cross a persistent seam edge. -/
theorem face_avoids_material (rotation : Data G) (holes : Finset G.Dart) {w : ℕ}
    (pair : SeamPair rotation (vertexMarks rotation holes)
      (Subtype.val : ↥(edgeDarts rotation holes) → G.Dart) w)
    {root e : G.Dart} (hr : root ∈ holes) (he : e ∈ rotation.toRotationSystem.faceOrbit root) :
    ¬ (majorityVertexSide G pair.outer.shore e.fst ∧
      ¬ majorityVertexSide G pair.inner.shore e.fst) := by
  exact pair.mark_not_in_material
    (fun m => Finset.mem_image.mpr ⟨m.val, m.property, rfl⟩)
    ⟨e, faceDarts_mem rotation holes hr he⟩

variable [G.LocallyFinite]

/-- No radius, cut chain, matching, endpoint marking or facial transport is
assumed. Ordered-mesh exclusion and largeness construct the smaller map
and preserve all the supplied ambient face roots. -/
theorem exists_replacement_of_no_orderedMesh (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hzero : ¬ RotationSystemTaitColorable rotation.toRotationSystem)
    (a b : ℕ) (ha : 2 ≤ a) (holes : Finset G.Dart)
    (hno : ¬ Nonempty (OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a b))
    (hlarge : sizeBound a b (vertexMarks rotation holes).card (edgeDarts rotation holes).card <
      Fintype.card V) :
    ∃ w, w ≤ widthBound a b (vertexMarks rotation holes).card (edgeDarts rotation holes).card ∧
      ∃ pair : SeamPair rotation (vertexMarks rotation holes)
        (Subtype.val : ↥(edgeDarts rotation holes) → G.Dart) w,
        Nonempty (StrictPhysicalReplacementData rotation pair.outer.shore pair.inner.shore
          pair.outer.outsideOuter pair.inner.innerOuter pair.width pair.outerWidth pair.innerWidth) ∧
        ∀ root ∈ holes, PreservesFace pair root := by
  have hl : sizeBound a b (vertexMarks rotation holes).card
      (Fintype.card ↥(edgeDarts rotation holes)) < Fintype.card V := by
    simpa only [Fintype.card_coe] using hlarge
  obtain ⟨w, hw, ⟨pair⟩⟩ := exists_seamPair_of_no_orderedMesh rotation ambient htwo
    a b ha (vertexMarks rotation holes) (Subtype.val : ↥(edgeDarts rotation holes) → G.Dart) hno hl
  refine ⟨w, ?_, pair, ⟨pair.replacement ambient htwo hzero⟩, ?_⟩
  · simpa only [Fintype.card_coe] using hw
  · exact fun _ hr => preservesFace rotation holes pair hr

/-- The geometric alternative now retains the designated faces on the
smaller zero-Count branch. Fixed-mesh exclusion remains a separate problem. -/
theorem exists_orderedMesh_or_replacement (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hzero : ¬ RotationSystemTaitColorable rotation.toRotationSystem)
    (a b : ℕ) (ha : 2 ≤ a) (holes : Finset G.Dart)
    (hlarge : sizeBound a b (vertexMarks rotation holes).card (edgeDarts rotation holes).card <
      Fintype.card V) :
    Nonempty (OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a b) ∨
      ∃ w, w ≤ widthBound a b (vertexMarks rotation holes).card (edgeDarts rotation holes).card ∧
        ∃ pair : SeamPair rotation (vertexMarks rotation holes)
          (Subtype.val : ↥(edgeDarts rotation holes) → G.Dart) w,
          Nonempty (StrictPhysicalReplacementData rotation pair.outer.shore pair.inner.shore
            pair.outer.outsideOuter pair.inner.innerOuter pair.width pair.outerWidth pair.innerWidth) ∧
          ∀ root ∈ holes, PreservesFace pair root := by
  classical
  by_cases h : Nonempty (OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a b)
  · exact Or.inl h
  · exact Or.inr (exists_replacement_of_no_orderedMesh rotation ambient htwo hzero a b ha holes h hlarge)

end
end Mettapedia.GraphTheory.FourColor.SphericalMarkedFaceReduction
