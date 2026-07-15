import Mathlib.Combinatorics.SimpleGraph.Paths
import Mettapedia.GraphTheory.FourColor.GoertzelV24CyclicFiveFaceIntersections

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DualPathTransversal

open GoertzelV24CyclicFiveFaceIntersections
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {F E : Type*} [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The primal edge crossed at one step of a facial-dual walk, computed from
the unique shared interior edge of the two consecutive faces. -/
def dualWalkCrossingEdge
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (step : Fin walk.length) : E :=
  sharedInteriorEdgeOfAdjOfPairwiseUnique faceBoundary allFaces hunique
    (walk.adj_getVert_succ step.isLt)

/-- A dual-walk crossing is an ambient interior edge. -/
theorem dualWalkCrossingEdge_mem_interiorEdgeSupport
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (step : Fin walk.length) :
    dualWalkCrossingEdge faceBoundary allFaces hunique walk step ∈
      interiorEdgeSupport faceBoundary allFaces := by
  exact (mem_sharedInteriorEdges_iff faceBoundary allFaces).1
    (sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges
      faceBoundary allFaces hunique
      (walk.adj_getVert_succ step.isLt)) |>.1

/-- The crossed primal edge lies on the face before its dual step. -/
theorem dualWalkCrossingEdge_mem_leftFace
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (step : Fin walk.length) :
    dualWalkCrossingEdge faceBoundary allFaces hunique walk step ∈
      faceBoundary (walk.getVert step.val).1 := by
  exact sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_left
    faceBoundary allFaces hunique (walk.adj_getVert_succ step.isLt)

/-- The crossed primal edge lies on the face after its dual step. -/
theorem dualWalkCrossingEdge_mem_rightFace
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (step : Fin walk.length) :
    dualWalkCrossingEdge faceBoundary allFaces hunique walk step ∈
      faceBoundary (walk.getVert (step.val + 1)).1 := by
  exact sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right
    faceBoundary allFaces hunique (walk.adj_getVert_succ step.isLt)

/-- Consecutive primal crossings in the dual-walk order both lie on the
intermediate face. This is the local face arc joining consecutive crossings. -/
theorem consecutive_dualWalkCrossingEdges_share_intermediateFace
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (step : Nat) (hnext : step + 1 < walk.length) :
    dualWalkCrossingEdge faceBoundary allFaces hunique walk
        ⟨step, by omega⟩ ∈ faceBoundary (walk.getVert (step + 1)).1 ∧
      dualWalkCrossingEdge faceBoundary allFaces hunique walk
        ⟨step + 1, hnext⟩ ∈ faceBoundary (walk.getVert (step + 1)).1 := by
  exact ⟨dualWalkCrossingEdge_mem_rightFace faceBoundary allFaces hunique
      walk ⟨step, by omega⟩,
    dualWalkCrossingEdge_mem_leftFace faceBoundary allFaces hunique
      walk ⟨step + 1, hnext⟩⟩

/-- A simple facial-dual path crosses distinct primal edges. The proof uses
only path vertex-injectivity and the at-most-two face-incidence law: if two
steps crossed the same edge, the later step's two faces would have to repeat
the earlier step's two faces. -/
theorem dualWalkCrossingEdge_injective_of_isPath
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ edge,
      totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (hpath : walk.IsPath) :
    Function.Injective
      (dualWalkCrossingEdge faceBoundary allFaces hunique walk) := by
  intro first second hedges
  let firstLeft := walk.getVert first.val
  let firstRight := walk.getVert (first.val + 1)
  let secondLeft := walk.getVert second.val
  let secondRight := walk.getVert (second.val + 1)
  have hfirstAdj := walk.adj_getVert_succ first.isLt
  have hfirstFaces : firstLeft.1 ≠ firstRight.1 := by
    intro hfaces
    exact hfirstAdj.ne (Subtype.ext hfaces)
  have hfirstLeft :
      dualWalkCrossingEdge faceBoundary allFaces hunique walk first ∈
        faceBoundary firstLeft.1 :=
    dualWalkCrossingEdge_mem_leftFace faceBoundary allFaces hunique walk first
  have hfirstRight :
      dualWalkCrossingEdge faceBoundary allFaces hunique walk first ∈
        faceBoundary firstRight.1 :=
    dualWalkCrossingEdge_mem_rightFace faceBoundary allFaces hunique walk first
  have hsecondLeft :
      dualWalkCrossingEdge faceBoundary allFaces hunique walk first ∈
        faceBoundary secondLeft.1 := by
    rw [hedges]
    exact dualWalkCrossingEdge_mem_leftFace faceBoundary allFaces hunique
      walk second
  have hsecondRight :
      dualWalkCrossingEdge faceBoundary allFaces hunique walk first ∈
        faceBoundary secondRight.1 := by
    rw [hedges]
    exact dualWalkCrossingEdge_mem_rightFace faceBoundary allFaces hunique
      walk second
  have hsecondLeftCases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      faceBoundary allFaces hall firstLeft.2 firstRight.2 secondLeft.2
      hfirstFaces hfirstLeft hfirstRight hsecondLeft
  rcases hsecondLeftCases with hsecondFirst | hsecondNext
  · apply Fin.ext
    exact hpath.getVert_injOn
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega)
      (Subtype.ext hsecondFirst.symm)
  · have hsecondVal : second.val = first.val + 1 :=
      hpath.getVert_injOn
        (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega)
        (Subtype.ext hsecondNext)
    have hsecondRightCases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        faceBoundary allFaces hall firstLeft.2 firstRight.2 secondRight.2
        hfirstFaces hfirstLeft hfirstRight hsecondRight
    rcases hsecondRightCases with hrightFirst | hrightNext
    · have hvalue : second.val + 1 = first.val :=
        hpath.getVert_injOn
          (by simp only [Set.mem_setOf_eq]; omega)
          (by simp only [Set.mem_setOf_eq]; omega)
          (Subtype.ext hrightFirst)
      omega
    · have hvalue : second.val + 1 = first.val + 1 :=
        hpath.getVert_injOn
          (by simp only [Set.mem_setOf_eq]; omega)
          (by simp only [Set.mem_setOf_eq]; omega)
          (Subtype.ext hrightNext)
      omega

/-- The finite set of primal edges crossed by a facial-dual walk. -/
def dualWalkCrossingEdges
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish) :
    Finset E :=
  Finset.univ.image
    (dualWalkCrossingEdge faceBoundary allFaces hunique walk)

@[simp]
theorem mem_dualWalkCrossingEdges_iff
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (edge : E) :
    edge ∈ dualWalkCrossingEdges faceBoundary allFaces hunique walk ↔
      ∃ step : Fin walk.length,
        dualWalkCrossingEdge faceBoundary allFaces hunique walk step = edge := by
  simp [dualWalkCrossingEdges]

/-- A simple dual path of length `n` crosses exactly `n` distinct primal
edges. -/
theorem card_dualWalkCrossingEdges_eq_length_of_isPath
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ edge,
      totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (hpath : walk.IsPath) :
    (dualWalkCrossingEdges faceBoundary allFaces hunique walk).card =
      walk.length := by
  rw [dualWalkCrossingEdges,
    Finset.card_image_of_injective _
      (dualWalkCrossingEdge_injective_of_isPath faceBoundary allFaces hall
        hunique walk hpath),
    Finset.card_univ, Fintype.card_fin]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In the v24 normal form, every simple path in the computed orbit-face dual
therefore supplies an ordered injective primal transversal. Face-intersection
uniqueness is derived here from cyclic 5-edge connectivity. -/
theorem orbitFaceDualPathCrossingEdge_injective_of_cyclicallyFiveEdgeConnected
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hcyclicFive : CyclicallyFiveEdgeConnected G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Walk
        start finish)
    (hpath : walk.IsPath) :
    Function.Injective (dualWalkCrossingEdge
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges_of_cyclicallyFiveEdgeConnected
        data htwoSided hconnected hsphere hrotation hcyclicFive)
      walk) := by
  apply dualWalkCrossingEdge_injective_of_isPath
  · exact orbitFace_incidence_le_two data.toRotationSystem
  · exact hpath

/-- Consequently, the normal-form transversal cut set has cardinality exactly
the length of its simple dual path. -/
theorem card_orbitFaceDualPathCrossingEdges_eq_length_of_cyclicallyFiveEdgeConnected
    (data : Data G) (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hcyclicFive : CyclicallyFiveEdgeConnected G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (walk : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Walk
        start finish)
    (hpath : walk.IsPath) :
    (dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      (pairwiseUniqueSharedInteriorEdges_of_cyclicallyFiveEdgeConnected
        data htwoSided hconnected hsphere hrotation hcyclicFive)
      walk).card = walk.length := by
  apply card_dualWalkCrossingEdges_eq_length_of_isPath
  · exact orbitFace_incidence_le_two data.toRotationSystem
  · exact hpath

end

end GoertzelV24DualPathTransversal

end Mettapedia.GraphTheory.FourColor
