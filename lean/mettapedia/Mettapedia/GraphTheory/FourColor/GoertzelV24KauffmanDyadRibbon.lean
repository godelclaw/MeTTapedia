import Mettapedia.GraphTheory.FourColor.GoertzelV24KauffmanFacePotential
import Mettapedia.GraphTheory.FourColor.GoertzelV24KauffmanFaceRibbonParity
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationCycleSpace

/-!
# The face-potential dyad as a finite ribbon surgery

For a face potential `q` and a colour `x`, select the faces with potential
`0` or `x`.  An edge of colour `x` has either both incident faces selected
or neither; every edge of either complementary colour has exactly one
selected incident face.  Thus the selected subsurface is obtained from its
face discs by gluing exactly the selected `x`-edges.

This file builds that gluing list on the literal dart carrier and applies the
generic face-ribbon parity theorem.  The remaining adapter identifies the
resulting boundary permutation with the complementary two-colour circuits.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24KauffmanDyadRibbon

open GoertzelV24FaceOrbitIncidence
open GoertzelV24KauffmanFacePotential
open GoertzelV24KauffmanFaceRibbonParity
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PermutationOrbitParity
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24RotationCycleSpace
open GoertzelV24SimpleGraphTaitBridge
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The quotient faces whose potential lies in the dyad `{0,x}`. -/
def dyadFaces
    {data : Data G} {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain) (x : Color) :
    Finset (OrbitFace data.toRotationSystem) :=
  Finset.univ.filter fun face =>
    coordinates.potential face = 0 ∨ coordinates.potential face = x

@[simp]
theorem mem_dyadFaces_iff
    {data : Data G} {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain) (x : Color)
    (face : OrbitFace data.toRotationSystem) :
    face ∈ dyadFaces coordinates x ↔
      coordinates.potential face = 0 ∨
        coordinates.potential face = x := by
  simp [dyadFaces]

/-- Across an edge represented by `x`, membership of one incident face in
the dyad `{0,x}` is equivalent to membership of the other. -/
theorem incident_mem_dyad_iff_of_chain_eq
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {chain : G.edgeSet → Color}
    (coordinates : ColorFacePotential data chain) (x : Color)
    (dart : data.toRotationSystem.D)
    (hchain : chain (data.toRotationSystem.edgeOf dart) = x) :
    dartOrbitFace data.toRotationSystem dart ∈ dyadFaces coordinates x ↔
      dartOrbitFace data.toRotationSystem
        (data.toRotationSystem.alpha dart) ∈ dyadFaces coordinates x := by
  rw [mem_dyadFaces_iff, mem_dyadFaces_iff]
  have hadd := coordinates.incident_add htwoSided dart
  rw [hchain] at hadd
  constructor
  · rintro (hzero | hx)
    · exact Or.inr (by simpa only [hzero, zero_add] using hadd)
    · refine Or.inl ?_
      apply add_left_cancel (a := x)
      simpa only [hx, add_zero] using hadd
  · rintro (hzero | hx)
    · exact Or.inr (by simpa only [hzero, add_zero] using hadd)
    · refine Or.inl ?_
      apply add_right_cancel (b := x)
      simpa only [hx, zero_add] using hadd

/-- The `x`-coloured edges whose two face sides belong to the selected dyad.
One representative dart is sufficient because dyad membership is invariant
under the edge flip on an `x`-edge. -/
def internalDyadEdges
    {data : Data G} (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    Finset G.edgeSet :=
  Finset.univ.filter fun edge =>
    C edge = x ∧
      dartOrbitFace data.toRotationSystem
        (chosenDart data.toRotationSystem edge) ∈ dyadFaces coordinates x

@[simp]
theorem mem_internalDyadEdges_iff
    {data : Data G} (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (edge : G.edgeSet) :
    edge ∈ internalDyadEdges C coordinates x ↔
      C edge = x ∧
        dartOrbitFace data.toRotationSystem
          (chosenDart data.toRotationSystem edge) ∈ dyadFaces coordinates x := by
  simp [internalDyadEdges]

/-- The selected-dart pair glued across one internal dyad edge. -/
def internalDyadEdgePair
    {data : Data G} (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (edge : {edge : G.edgeSet // edge ∈ internalDyadEdges C coordinates x}) :
    SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x) ×
      SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x) := by
  let dart := chosenDart data.toRotationSystem edge.1
  have hedge := (mem_internalDyadEdges_iff C coordinates x edge.1).mp edge.2
  have hdartEdge : data.toRotationSystem.edgeOf dart = edge.1 :=
    chosenDart_edgeOf data.toRotationSystem edge.1
  have hchain : C (data.toRotationSystem.edgeOf dart) = x := by
    rw [hdartEdge]
    exact hedge.1
  have hleft : dartOrbitFace data.toRotationSystem dart ∈
      dyadFaces coordinates x := hedge.2
  have hright : dartOrbitFace data.toRotationSystem
      (data.toRotationSystem.alpha dart) ∈ dyadFaces coordinates x :=
    (incident_mem_dyad_iff_of_chain_eq data htwoSided coordinates x
      dart hchain).mp hleft
  exact (⟨dart, hleft⟩,
    ⟨data.toRotationSystem.alpha dart, hright⟩)

theorem internalDyadEdgePair_ne
    {data : Data G} (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (edge : {edge : G.edgeSet // edge ∈ internalDyadEdges C coordinates x}) :
    (internalDyadEdgePair htwoSided C coordinates x edge).1 ≠
      (internalDyadEdgePair htwoSided C coordinates x edge).2 := by
  intro heq
  have hval := congrArg Subtype.val heq
  exact data.toRotationSystem.alpha_fixfree
    (chosenDart data.toRotationSystem edge.1) hval.symm

/-- One pair for every internal dyad edge, in an arbitrary finite order. -/
def internalDyadPairList
    {data : Data G} (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    List
      (SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x) ×
        SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x)) :=
  (internalDyadEdges C coordinates x).attach.toList.map
    (internalDyadEdgePair htwoSided C coordinates x)

theorem internalDyadPairList_length
    {data : Data G} (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    (internalDyadPairList htwoSided C coordinates x).length =
      (internalDyadEdges C coordinates x).card := by
  simp [internalDyadPairList]

@[simp]
theorem edgeOf_internalDyadEdgePair_fst
    {data : Data G} (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (edge : {edge : G.edgeSet // edge ∈ internalDyadEdges C coordinates x}) :
    data.toRotationSystem.edgeOf
        (internalDyadEdgePair htwoSided C coordinates x edge).1.1 = edge.1 := by
  exact chosenDart_edgeOf data.toRotationSystem edge.1

@[simp]
theorem edgeOf_internalDyadEdgePair_snd
    {data : Data G} (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (edge : {edge : G.edgeSet // edge ∈ internalDyadEdges C coordinates x}) :
    data.toRotationSystem.edgeOf
        (internalDyadEdgePair htwoSided C coordinates x edge).2.1 = edge.1 := by
  rw [show (internalDyadEdgePair htwoSided C coordinates x edge).2.1 =
      data.toRotationSystem.alpha
        (chosenDart data.toRotationSystem edge.1) by rfl,
    data.toRotationSystem.edge_alpha,
    chosenDart_edgeOf]

theorem internalDyadEdgePair_injective
    {data : Data G} (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    Function.Injective (internalDyadEdgePair htwoSided C coordinates x) := by
  intro left right heq
  apply Subtype.ext
  have hfirst := congrArg
    (fun pair => data.toRotationSystem.edgeOf pair.1.1) heq
  rw [edgeOf_internalDyadEdgePair_fst htwoSided C coordinates x left,
    edgeOf_internalDyadEdgePair_fst htwoSided C coordinates x right] at hfirst
  exact hfirst

theorem internalDyadPairList_nodup
    {data : Data G} (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    (internalDyadPairList htwoSided C coordinates x).Nodup := by
  apply List.Nodup.map
    (internalDyadEdgePair_injective htwoSided C coordinates x)
  exact Finset.nodup_toList _

/-- Different internal dyad edges contribute endpoint-disjoint dart pairs. -/
theorem internalDyadPairList_isolated
    {data : Data G} (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color)
    (pair : SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x) ×
      SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x))
    (hpair : pair ∈ internalDyadPairList htwoSided C coordinates x) :
    ∀ other ∈ internalDyadPairList htwoSided C coordinates x,
      other ≠ pair →
      pair.1 ≠ other.1 ∧ pair.1 ≠ other.2 ∧
      pair.2 ≠ other.1 ∧ pair.2 ≠ other.2 := by
  rcases List.mem_map.mp hpair with ⟨edge, _hedge, rfl⟩
  intro other hother hne
  rcases List.mem_map.mp hother with ⟨otherEdge, _hotherEdge, rfl⟩
  have hedgeNe : edge ≠ otherEdge := by
    intro hedge
    subst otherEdge
    exact hne rfl
  have endpoint_ne
      (left : SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x))
      (right : SelectedFaceDart data.toRotationSystem (dyadFaces coordinates x))
      (hleftEdge : data.toRotationSystem.edgeOf left.1 = edge.1)
      (hrightEdge : data.toRotationSystem.edgeOf right.1 = otherEdge.1) :
      left ≠ right := by
    intro heq
    apply hedgeNe
    apply Subtype.ext
    calc
      edge.1 = data.toRotationSystem.edgeOf left.1 := hleftEdge.symm
      _ = data.toRotationSystem.edgeOf right.1 :=
        congrArg (fun dart => data.toRotationSystem.edgeOf dart.1) heq
      _ = otherEdge.1 := hrightEdge
  exact ⟨
    endpoint_ne _ _ (edgeOf_internalDyadEdgePair_fst
      htwoSided C coordinates x edge)
      (edgeOf_internalDyadEdgePair_fst
        htwoSided C coordinates x otherEdge),
    endpoint_ne _ _ (edgeOf_internalDyadEdgePair_fst
      htwoSided C coordinates x edge)
      (edgeOf_internalDyadEdgePair_snd
        htwoSided C coordinates x otherEdge),
    endpoint_ne _ _ (edgeOf_internalDyadEdgePair_snd
      htwoSided C coordinates x edge)
      (edgeOf_internalDyadEdgePair_fst
        htwoSided C coordinates x otherEdge),
    endpoint_ne _ _ (edgeOf_internalDyadEdgePair_snd
      htwoSided C coordinates x edge)
      (edgeOf_internalDyadEdgePair_snd
        htwoSided C coordinates x otherEdge)⟩

/-- The actual face-ribbon surgery determined by one potential dyad. -/
def dyadFaceRibbonSurgery
    {data : Data G} (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    FaceRibbonSurgery data.toRotationSystem (dyadFaces coordinates x) where
  pairs := internalDyadPairList htwoSided C coordinates x
  pair_ne := by
    intro pair hpair
    rcases List.mem_map.mp hpair with ⟨edge, _hedge, rfl⟩
    exact internalDyadEdgePair_ne htwoSided C coordinates x edge

/-- The boundary-orbit parity of the concrete potential dyad is selected
faces plus selected internal `x`-edges. -/
theorem orbitCount_dyadBoundaryPerm_mod_two
    {data : Data G} (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (C : G.EdgeColoring Color)
    (coordinates : ColorFacePotential data C) (x : Color) :
    orbitCount (dyadFaceRibbonSurgery htwoSided C coordinates x).boundaryPerm % 2 =
      ((dyadFaces coordinates x).card +
        (internalDyadEdges C coordinates x).card) % 2 := by
  have hparity :=
    (dyadFaceRibbonSurgery htwoSided C coordinates x).orbitCount_boundaryPerm_mod_two
  change orbitCount
      (dyadFaceRibbonSurgery htwoSided C coordinates x).boundaryPerm % 2 =
    ((dyadFaces coordinates x).card +
      (internalDyadPairList htwoSided C coordinates x).length) % 2 at hparity
  rw [internalDyadPairList_length] at hparity
  exact hparity

end

end GoertzelV24KauffmanDyadRibbon

end Mettapedia.GraphTheory.FourColor
