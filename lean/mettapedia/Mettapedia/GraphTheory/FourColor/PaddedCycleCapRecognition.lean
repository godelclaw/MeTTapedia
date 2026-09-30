import Mettapedia.GraphTheory.FourColor.PaddedCycleCapPortGeometry
import Mettapedia.GraphTheory.FourColor.OpenTangleDartRecognition
import Mettapedia.GraphTheory.FourColor.PaddedCycleCapPhysicalGeometry

/-!
# Recognizing the face-traced cap as an actual vertex shore

The face trace constructs every dart, vertex and boundary coordinate. Short
seam faces prove that all final ports leave the cap. Vertex injectivity is
the remaining local geometric hypothesis. The resulting representation is
consumed by the strict all-width cap reduction and minimality theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap.FaceTraversal

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open SerialTangleSmallCutTransfer OpenTangleIsomorphism
open GoertzelV24RotationCutDartDecomposition GoertzelV24VertexSideOpenTangle
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open PhysicalForkCodeFaces GoertzelV24TwoEdgeCutMinimality GoertzelV24OrbitFaceTwoSided

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem V E) (m : ℕ) [NeZero m] (hm : 2 ≤ m) (root : RS.D)

def deleted : Finset V := Finset.univ.image (vertex RS m root)

omit [NeZero m] in
theorem mem_deleted_iff (v : V) : v ∈ deleted RS m root ↔
    ∃ w : Vertex m, vertex RS m root w = v := by
  simp [deleted]

def coordinate : Interior m ⊕ (Empty ⊕ Fin (m*2)) ≃ Dart m :=
  TwoSidedBoundaryReindex.darts (Equiv.sumCongr (Equiv.refl Empty) (portIndex m).symm)

def ambient (d : Interior m ⊕ (Empty ⊕ Fin (m*2))) : RS.D :=
  dart RS m root (coordinate m d)

theorem literal_vertex (d : Dart m) : (tangle m hm).vertOf d = vertexOf m d := by
  rcases d with d | (e | b)
  · rfl
  · exact nomatch e
  · rfl

theorem ambient_vertex (d : Interior m ⊕ (Empty ⊕ Fin (m*2))) :
    RS.vertOf (ambient RS m root d) = vertex RS m root ((asOpen (indexedCap m hm)).vertOf d) := by
  rw [ambient, dart_vertex]
  apply congrArg (vertex RS m root)
  rw [asOpen_vertOf]
  rw [indexedCap, TwoSidedBoundaryReindex.vert_reindex, literal_vertex]
  rfl

def retained (d : Interior m ⊕ (Empty ⊕ Fin (m*2))) :
    RetainedDart RS (deletedSideKeep (deleted RS m root)) :=
  ⟨ambient RS m root d, by
    rw [ambient_vertex RS m hm root]
    simp [deletedSideKeep, deletedRegionKeep, deleted]⟩

def insideRoot : RetainedDart RS (deletedSideKeep (deleted RS m root)) :=
  retained RS m hm root (.inr (.inr 0))

variable (hC : Cubic3 RS) (hf : FaceLengths RS m root)
  (hv : Function.Injective (vertex RS m root)) (hs : BoundaryShortFaces RS m root)

def vertices : Vertex m ≃ {v : V // deletedSideKeep (deleted RS m root) v} :=
  Equiv.ofBijective (fun v => ⟨vertex RS m root v, by
    simp [deletedSideKeep, deletedRegionKeep, deleted]⟩) ⟨by
      intro v w he
      exact hv (congrArg Subtype.val he), by
      intro v
      have hm : v.1 ∈ deleted RS m root := by
        simpa [deletedSideKeep, deletedRegionKeep] using v.2
      obtain ⟨w,hw⟩ := (mem_deleted_iff RS m root v.1).mp hm
      exact ⟨w, Subtype.ext hw⟩⟩

include hC in
def darts : Interior m ⊕ (Empty ⊕ Fin (m*2)) ≃
    RetainedDart RS (deletedSideKeep (deleted RS m root)) :=
  Equiv.ofBijective (retained RS m hm root) ⟨by
    intro d e he
    exact (coordinate m).injective
      (dart_injective RS m root hC hv (congrArg Subtype.val he)), by
    intro d
    have hm' : RS.vertOf d.1 ∈ deleted RS m root := by
      simpa [deletedSideKeep, deletedRegionKeep] using d.2
    obtain ⟨v,hv'⟩ := (mem_deleted_iff RS m root _).mp hm'
    obtain ⟨s,hs'⟩ := atStar_surjective_at RS m root hC v d.1 hv'.symm
    refine ⟨(coordinate m).symm (star m (v.1,v.2,s)), Subtype.ext ?_⟩
    change ambient RS m root ((coordinate m).symm (star m (v.1,v.2,s))) = d.1
    simpa only [ambient, Equiv.apply_symm_apply, dart, position_star] using hs'⟩

include hC hf in
theorem ambient_alpha (i : Interior m) :
    ambient RS m root (.inl ((asOpen (indexedCap m hm)).interiorAlpha i)) =
      RS.alpha (ambient RS m root (.inl i)) :=
  dart_alpha RS m root hC hf i

include hC in
theorem ambient_rotation (d : Interior m ⊕ (Empty ⊕ Fin (m*2))) :
    ambient RS m root ((asOpen (indexedCap m hm)).rho d) =
      RS.rho (ambient RS m root d) := by
  change dart RS m root ((coordinate m) ((coordinate m).symm
    (rotation m (coordinate m d)))) = _
  rw [Equiv.apply_symm_apply]
  exact dart_rotation RS m root hC _

include hC hf hv hs in
theorem port_not_deleted (i : Fin (m*2)) :
    RS.vertOf (RS.alpha (port RS m root i)) ∉ deleted RS m root := by
  intro he
  obtain ⟨v,hv'⟩ := (mem_deleted_iff RS m root _).mp he
  exact port_outside RS m root hC hf hv hs i v hv'.symm

include hC hf in
def outsideRoot : RetainedDart RS (deletedRegionKeep (deleted RS m root)) :=
  ⟨RS.alpha (port RS m root 0), port_not_deleted RS m root hC hf hv hs 0⟩

include hC hf in
/-- The local representation is constructed from actual faces and vertex
separation. Its internal edges, boundary classification and star maps are
all proved, rather than supplied as isomorphism fields. -/
def recognition : Iso (asOpen (indexedCap m hm))
    (ofVertexSide RS (deletedSideKeep (deleted RS m root)) (insideRoot RS m hm root)) := by
  apply ofRetainedDarts (asOpen (indexedCap m hm)) RS
    (deletedSideKeep (deleted RS m root)) (insideRoot RS m hm root)
    (vertices RS m root hv) (darts RS m hm root hC hv)
  · intro i
    have he := (retained RS m hm root
      (.inl ((asOpen (indexedCap m hm)).interiorAlpha i))).2
    change deletedSideKeep (deleted RS m root) (RS.vertOf (ambient RS m root _)) at he
    rw [ambient_alpha RS m hm root hC hf] at he
    exact he
  · rintro (e | i)
    · exact nomatch e
    · change ¬ deletedSideKeep (deleted RS m root)
        (RS.vertOf (RS.alpha (port RS m root i)))
      simpa [deletedSideKeep, deletedRegionKeep] using
        port_not_deleted RS m root hC hf hv hs i
  · intro i
    exact ambient_alpha RS m hm root hC hf i
  · intro d
    apply Subtype.ext
    exact (ambient_vertex RS m hm root d).symm
  · intro d
    apply Subtype.ext
    exact ambient_rotation RS m hm root hC d

end

noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (rotation : SimpleGraphDartRotation.Data G)

local instance capRecognitionEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance capRecognitionEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- The face-derived representation is consumed by the original strict
reduction. Vertex injectivity and exterior connectivity remain explicit. -/
theorem no_face_traced_cap (m : ℕ) [NeZero m] (hm : 2 ≤ m)
    (root : rotation.toRotationSystem.D)
    (hf : FaceLengths rotation.toRotationSystem m root)
    (hv : Function.Injective (vertex rotation.toRotationSystem m root))
    (hs : BoundaryShortFaces rotation.toRotationSystem m root)
    (houtside : (G.induce {v | deletedRegionKeep
      (deleted rotation.toRotationSystem m root) v}).Connected)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False := by
  let RS := rotation.toRotationSystem
  let hC := cubic3_of RS minimal.spherical.cubic minimal.vertexRotationCyclic
  let e := recognition RS m hm root hC hf hv hs
  exact no_recognized_cap m hm rotation (deleted RS m root)
    (outsideRoot RS m root hC hf hv hs) (insideRoot RS m hm root) e.symm minimal houtside

end
end Mettapedia.GraphTheory.FourColor.PaddedCycleCap.FaceTraversal
