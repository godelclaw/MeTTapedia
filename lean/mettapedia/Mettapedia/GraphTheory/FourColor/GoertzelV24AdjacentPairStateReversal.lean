import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOverlapKempeState
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairReversal

/-!
# Reversing the finite boundary Kempe state

Reversing an adjacent-pair deletion changes only the presentation of its
four ports.  This file proves that the complete finite boundary observation
is transported by the permutation `[0,1,2,3] -> [2,3,0,1]`.

The proof uses the canonical graph isomorphism between the two orders of the
same deletion.  It transports incident-edge sums and bicoloured reachability,
so both the boundary word and every labelled Kempe-connectivity bit are
preserved.  No planarity, cancellation, or wall statement is involved.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AdjacentPairStateReversal

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairReversal
open GoertzelV24FourDefectBoundary
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

abbrev OriginalGraph (data : AdjacentPairData G) :=
  DeletedAdjacentPairGraph G data.firstVertex data.secondVertex

abbrev ReversedGraph (data : AdjacentPairData G) :=
  DeletedAdjacentPairGraph G (reverse data).firstVertex
    (reverse data).secondVertex

/-- The graph isomorphism which exchanges the two proofs in the retained
vertex subtype. -/
def swapIso (data : AdjacentPairData G) :
    OriginalGraph data ≃g ReversedGraph data :=
  deletedAdjacentPairSwapIso data.firstVertex data.secondVertex

/-- Graph isomorphisms preserve membership in the incident-edge set. -/
theorem mapEdgeSet_mem_incidentEdgeFinset_iff
    {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (iso : G ≃g H) (edge : G.edgeSet) (vertex : V) :
    iso.mapEdgeSet edge ∈ incidentEdgeFinset H (iso vertex) ↔
      edge ∈ incidentEdgeFinset G vertex := by
  rw [incidentEdgeFinset, incidentEdgeFinset]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right =>
      simp [SimpleGraph.Iso.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet,
        Sym2.mem_iff]

/-- An isomorphism maps the complete incident-edge finset onto the complete
incident-edge finset at the image vertex. -/
theorem incidentEdgeFinset_map_swapIso
    (data : AdjacentPairData G)
    (vertex : retainedVertexSet data.firstVertex data.secondVertex) :
    (incidentEdgeFinset (OriginalGraph data) vertex).map
        (swapIso data).mapEdgeSet.toEmbedding =
      incidentEdgeFinset (ReversedGraph data) (swapIso data vertex) := by
  ext edge
  constructor
  · intro hmem
    rcases Finset.mem_map.mp hmem with ⟨source, hsource, hmap⟩
    subst edge
    exact (mapEdgeSet_mem_incidentEdgeFinset_iff
      (swapIso data) source vertex).2 hsource
  · intro hmem
    let source := (swapIso data).mapEdgeSet.symm edge
    have hmapSource : (swapIso data).mapEdgeSet source = edge := by
      exact (swapIso data).mapEdgeSet.apply_symm_apply edge
    have hsource : source ∈ incidentEdgeFinset (OriginalGraph data) vertex :=
      (mapEdgeSet_mem_incidentEdgeFinset_iff
        (swapIso data) source vertex).1 (by
          rw [hmapSource]
          exact hmem)
    exact Finset.mem_map.mpr ⟨source, hsource,
      (swapIso data).mapEdgeSet.apply_symm_apply edge⟩

@[simp] theorem reverseColoring_mapEdgeSet
    (data : AdjacentPairData G)
    (coloring : (OriginalGraph data).EdgeColoring Color)
    (edge : (OriginalGraph data).edgeSet) :
    reverseColoring data coloring ((swapIso data).mapEdgeSet edge) =
      coloring edge := by
  change coloring
      ((swapIso data).symm.mapEdgeSet ((swapIso data).mapEdgeSet edge)) =
    coloring edge
  have hedge :
      (swapIso data).symm.mapEdgeSet ((swapIso data).mapEdgeSet edge) =
        (swapIso data).mapEdgeSet.symm ((swapIso data).mapEdgeSet edge) :=
    (SimpleGraph.Iso.mapEdgeSet_symm_apply
      (swapIso data) ((swapIso data).mapEdgeSet edge)).symm
  rw [hedge]
  rw [(swapIso data).mapEdgeSet.symm_apply_apply]

/-- Kirchhoff boundary sums are invariant under the endpoint-order swap. -/
theorem vertexKirchhoffSum_reverseColoring
    (data : AdjacentPairData G)
    (coloring : (OriginalGraph data).EdgeColoring Color)
    (vertex : retainedVertexSet data.firstVertex data.secondVertex) :
    vertexKirchhoffSum (ReversedGraph data) (reverseColoring data coloring)
        (swapIso data vertex) =
      vertexKirchhoffSum (OriginalGraph data) coloring vertex := by
  unfold vertexKirchhoffSum
  rw [← incidentEdgeFinset_map_swapIso data vertex, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro edge _hedge
  exact reverseColoring_mapEdgeSet data coloring edge

/-- The reversed port is the image of the corresponding original port under
the retained-vertex isomorphism. -/
theorem reverse_retainedPort_eq
    (data : AdjacentPairData G) (port : Fin 4) :
    (reverse data).retainedPort port =
      swapIso data (data.retainedPort (reversePort port)) := by
  apply Subtype.ext
  rfl

/-- Reversal merely precomposes the four-port boundary word. -/
theorem colorWord_reverseColoring
    (data : AdjacentPairData G)
    (coloring : (OriginalGraph data).EdgeColoring Color)
    (port : Fin 4) :
    (reverse data).degreeTwoBoundaryData.colorWord
        (reverseColoring data coloring) port =
      data.degreeTwoBoundaryData.colorWord coloring (reversePort port) := by
  change vertexKirchhoffSum (ReversedGraph data) (reverseColoring data coloring)
      ((reverse data).retainedPort port) =
    vertexKirchhoffSum (OriginalGraph data) coloring
      (data.retainedPort (reversePort port))
  rw [reverse_retainedPort_eq]
  exact vertexKirchhoffSum_reverseColoring data coloring _

/-- The bicoloured line subgraphs before and after reversal are canonically
isomorphic. -/
def bicoloredSubgraphIso
    (data : AdjacentPairData G)
    (coloring : (OriginalGraph data).EdgeColoring Color)
    (firstColor secondColor : Color) :
    coloring.bicoloredSubgraph firstColor secondColor ≃g
      (reverseColoring data coloring).bicoloredSubgraph
        firstColor secondColor where
  toFun edge := ⟨(swapIso data).mapEdgeSet edge.1, by
    change reverseColoring data coloring ((swapIso data).mapEdgeSet edge.1) =
        firstColor ∨
      reverseColoring data coloring ((swapIso data).mapEdgeSet edge.1) =
        secondColor
    rw [reverseColoring_mapEdgeSet]
    exact edge.2⟩
  invFun edge := ⟨(swapIso data).mapEdgeSet.symm edge.1, by
    change coloring ((swapIso data).mapEdgeSet.symm edge.1) = firstColor ∨
      coloring ((swapIso data).mapEdgeSet.symm edge.1) = secondColor
    have hproperty := edge.2
    change coloring ((swapIso data).symm.mapEdgeSet edge.1) = firstColor ∨
      coloring ((swapIso data).symm.mapEdgeSet edge.1) = secondColor at hproperty
    have hedge : (swapIso data).symm.mapEdgeSet edge.1 =
        (swapIso data).mapEdgeSet.symm edge.1 :=
      (SimpleGraph.Iso.mapEdgeSet_symm_apply (swapIso data) edge.1).symm
    rw [hedge] at hproperty
    exact hproperty⟩
  left_inv edge := by
    apply Subtype.ext
    exact (swapIso data).mapEdgeSet.symm_apply_apply edge.1
  right_inv edge := by
    apply Subtype.ext
    exact (swapIso data).mapEdgeSet.apply_symm_apply edge.1
  map_rel_iff' := by
    intro first second
    exact (swapIso data).lineGraph.map_rel_iff

@[simp] theorem bicoloredSubgraphIso_apply_val
    (data : AdjacentPairData G)
    (coloring : (OriginalGraph data).EdgeColoring Color)
    (firstColor secondColor : Color)
    (edge : coloring.bicoloredSet firstColor secondColor) :
    (bicoloredSubgraphIso data coloring firstColor secondColor edge).1 =
      (swapIso data).mapEdgeSet edge.1 := rfl

@[simp] theorem bicoloredSubgraphIso_symm_apply_val
    (data : AdjacentPairData G)
    (coloring : (OriginalGraph data).EdgeColoring Color)
    (firstColor secondColor : Color)
    (edge : (reverseColoring data coloring).bicoloredSet
      firstColor secondColor) :
    ((bicoloredSubgraphIso data coloring firstColor secondColor).symm edge).1 =
      (swapIso data).mapEdgeSet.symm edge.1 := rfl

/-- Every labelled two-colour port-connectivity assertion is invariant under
reversal, after applying the four-port reversal permutation. -/
theorem kempePortsConnected_reverseColoring_iff
    (data : AdjacentPairData G)
    (coloring : (OriginalGraph data).EdgeColoring Color)
    (firstColor secondColor : Color) (left right : Fin 4) :
    (reverse data).degreeTwoBoundaryData.KempePortsConnected
        (reverseColoring data coloring) firstColor secondColor left right ↔
      data.degreeTwoBoundaryData.KempePortsConnected coloring
        firstColor secondColor (reversePort left) (reversePort right) := by
  let iso := bicoloredSubgraphIso data coloring firstColor secondColor
  constructor
  · rintro ⟨leftEdge, rightEdge, hleft, hright, hreach⟩
    refine ⟨iso.symm leftEdge, iso.symm rightEdge, ?_, ?_, ?_⟩
    · apply (mapEdgeSet_mem_incidentEdgeFinset_iff
        (swapIso data) (iso.symm leftEdge).1
        (data.retainedPort (reversePort left))).1
      change (swapIso data).mapEdgeSet
          ((swapIso data).mapEdgeSet.symm leftEdge.1) ∈
        incidentEdgeFinset (ReversedGraph data)
          (swapIso data (data.retainedPort (reversePort left)))
      rw [(swapIso data).mapEdgeSet.apply_symm_apply]
      rw [← reverse_retainedPort_eq]
      exact hleft
    · apply (mapEdgeSet_mem_incidentEdgeFinset_iff
        (swapIso data) (iso.symm rightEdge).1
        (data.retainedPort (reversePort right))).1
      change (swapIso data).mapEdgeSet
          ((swapIso data).mapEdgeSet.symm rightEdge.1) ∈
        incidentEdgeFinset (ReversedGraph data)
          (swapIso data (data.retainedPort (reversePort right)))
      rw [(swapIso data).mapEdgeSet.apply_symm_apply]
      rw [← reverse_retainedPort_eq]
      exact hright
    · have hmapped :
          (reverseColoring data coloring).bicoloredSubgraph
              firstColor secondColor |>.Reachable
            (iso (iso.symm leftEdge)) (iso (iso.symm rightEdge)) := by
        rw [iso.apply_symm_apply, iso.apply_symm_apply]
        exact hreach
      exact (SimpleGraph.Iso.reachable_iff (φ := iso)).1 hmapped
  · rintro ⟨leftEdge, rightEdge, hleft, hright, hreach⟩
    refine ⟨iso leftEdge, iso rightEdge, ?_, ?_, ?_⟩
    · change (swapIso data).mapEdgeSet leftEdge.1 ∈
        incidentEdgeFinset (ReversedGraph data)
          ((reverse data).retainedPort left)
      rw [reverse_retainedPort_eq]
      exact (mapEdgeSet_mem_incidentEdgeFinset_iff
          (swapIso data) leftEdge.1
          (data.retainedPort (reversePort left))).2 hleft
    · change (swapIso data).mapEdgeSet rightEdge.1 ∈
        incidentEdgeFinset (ReversedGraph data)
          ((reverse data).retainedPort right)
      rw [reverse_retainedPort_eq]
      exact (mapEdgeSet_mem_incidentEdgeFinset_iff
          (swapIso data) rightEdge.1
          (data.retainedPort (reversePort right))).2 hright
    · exact (SimpleGraph.Iso.reachable_iff (φ := iso)).2 hreach

/-- The action of reversal on the finite one-side state. -/
def reverseBoundaryKempeState (state : BoundaryKempeState) :
    BoundaryKempeState :=
  (fun port => state.1 (reversePort port),
    fun firstColor secondColor left right =>
      state.2 firstColor secondColor (reversePort left) (reversePort right))

@[simp] theorem reversePort_apply_reversePort (port : Fin 4) :
    reversePort (reversePort port) = port := by
  fin_cases port <;> rfl

/-- Reversing a finite boundary state twice is the identity. -/
@[simp] theorem reverseBoundaryKempeState_involutive
    (state : BoundaryKempeState) :
    reverseBoundaryKempeState (reverseBoundaryKempeState state) = state := by
  apply Prod.ext
  · funext port
    simp [reverseBoundaryKempeState]
  · funext firstColor secondColor left right
    simp [reverseBoundaryKempeState]

/-- Boundary-state reversal is an equivalence, not a lossy projection. -/
def reverseBoundaryKempeStateEquiv :
    BoundaryKempeState ≃ BoundaryKempeState where
  toFun := reverseBoundaryKempeState
  invFun := reverseBoundaryKempeState
  left_inv := reverseBoundaryKempeState_involutive
  right_inv := reverseBoundaryKempeState_involutive

/-- The complete finite boundary state of the reversed physical site is the
port-reversal of the original state. -/
theorem boundaryKempeState_reverseColoring
    (data : AdjacentPairData G)
    (coloring : (OriginalGraph data).EdgeColoring Color) :
    boundaryKempeState (reverse data) (reverseColoring data coloring) =
      reverseBoundaryKempeState (boundaryKempeState data coloring) := by
  apply Prod.ext
  · funext port
    exact colorWord_reverseColoring data coloring port
  · funext firstColor secondColor left right
    simp only [boundaryKempeState, reverseBoundaryKempeState,
      kempePortConnectivityBit]
    rw [kempePortsConnected_reverseColoring_iff]

/-- Dependent transport form used when two site records are known equal only
through their data field and a heterogeneous equality of their colourings. -/
theorem boundaryKempeState_eq_reverse_of_data_eq_of_base_heq
    (source target : AdjacentPairData G)
    (sourceColoring : (DeletedAdjacentPairGraph G source.firstVertex
      source.secondVertex).EdgeColoring Color)
    (targetColoring : (DeletedAdjacentPairGraph G target.firstVertex
      target.secondVertex).EdgeColoring Color)
    (hdata : target = reverse source)
    (hcoloring : HEq targetColoring
      (reverseColoring source sourceColoring)) :
    boundaryKempeState target targetColoring =
      reverseBoundaryKempeState
        (boundaryKempeState source sourceColoring) := by
  subst target
  have hcoloringEq : targetColoring = reverseColoring source sourceColoring :=
    eq_of_heq hcoloring
  subst targetColoring
  exact boundaryKempeState_reverseColoring source sourceColoring

end

end GoertzelV24AdjacentPairStateReversal

end Mettapedia.GraphTheory.FourColor
