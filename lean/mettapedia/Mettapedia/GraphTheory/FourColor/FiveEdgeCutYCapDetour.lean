import Mettapedia.GraphTheory.FourColor.FiveEdgeCutYCapBridge
import Mettapedia.GraphTheory.FourColor.CubicTripleEdgeCyclicCut
import Mettapedia.GraphTheory.FourColor.IncidentEdgeFinset
import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedEdgeTrail

/-!
# Discharging the Y-cap detour from cyclic five-edge-connectivity

Deleting the two seam-forming cut edges and one retained internal edge
cannot disconnect the ambient graph: the triple-deletion dichotomy would
otherwise produce a cyclic edge cut of at most three edges — impossible at
cyclic connectivity five — or a vertex carrying exactly those three edges,
impossible because a deleted-side vertex cannot carry a retained internal
edge and a retained vertex carrying both seam edges would identify the two
distinct seam endpoints.  Connectivity of the triple-deleted graph then
maps into the internal detour graph dart by dart.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24RotationCutDartDecomposition
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace FiveEdgeCutYCapData

variable (rotation : SimpleGraphDartRotation.Data G)
  (data : FiveEdgeCutYCapData rotation.toRotationSystem)

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G

/-- A retained vertex on a crossing edge is that edge's outward-dart base. -/
theorem keep_endpoint_eq (j : Fin 5) (vertex : V)
    (hkeep : data.keep vertex)
    (hmem : vertex ∈ ((data.crossing j : G.edgeSet).1 : Sym2 V)) :
    vertex = rotation.toRotationSystem.vertOf
      (data.crossingBoundaryDartEquiv j).1.1 := by
  set d : G.Dart := (data.crossingBoundaryDartEquiv j).1.1 with hd
  have hedge : data.crossing j =
      rotation.toRotationSystem.edgeOf d :=
    (data.crossingBoundaryDartEquiv_edgeOf j).symm
  have hval : ((data.crossing j : G.edgeSet).1 : Sym2 V) =
      s(d.fst, d.snd) := by
    rw [hedge]
    rfl
  rw [hval] at hmem
  rcases Sym2.mem_iff.mp hmem with heq | heq
  · exact heq
  · exfalso
    apply (data.crossingBoundaryDartEquiv j).2
    have hsnd : rotation.toRotationSystem.vertOf
        (rotation.toRotationSystem.alpha d) = d.snd := rfl
    rw [hsnd, ← heq]
    exact hkeep

/-- A retained internal edge differs from every crossing edge. -/
theorem internal_edge_ne_crossing
    (removed : InternalDart rotation.toRotationSystem data.keep)
    (j : Fin 5) :
    rotation.toRotationSystem.edgeOf removed.1.1 ≠ data.crossing j := by
  intro hedge
  set d : G.Dart := (data.crossingBoundaryDartEquiv j).1.1 with hd
  have hcrossEdge : data.crossing j =
      rotation.toRotationSystem.edgeOf d :=
    (data.crossingBoundaryDartEquiv_edgeOf j).symm
  have hvals : s(removed.1.1.fst, removed.1.1.snd) = s(d.fst, d.snd) := by
    have := congrArg Subtype.val (hedge.trans hcrossEdge)
    exact this
  have hsndKeep : data.keep removed.1.1.snd := removed.2
  have hsndNotKeep : ¬ data.keep d.snd :=
    (data.crossingBoundaryDartEquiv j).2
  have hfstKeep : data.keep removed.1.1.fst := removed.1.2
  rcases Sym2.eq_iff.mp hvals with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · apply hsndNotKeep
    rw [← hsnd]
    exact hsndKeep
  · apply hsndNotKeep
    rw [← hfst]
    exact hfstKeep

/-- The seam-forming crossing edges are distinct from each other. -/
theorem crossing_zero_ne_one : data.crossing 0 ≠ data.crossing 1 :=
  data.crossing_injective.ne (by decide)

/-- **Detour discharge.**  At cyclic connectivity five, deleting the two
seam-forming cut edges and any retained internal edge leaves the ambient
graph connected, hence the internal detour graph reaches around every
retained internal edge. -/
theorem internalDetourGraph_reachable_of_cyclicFive
    (hregular : G.IsRegularOfDegree 3)
    (hconnected : G.Connected)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (removed : InternalDart rotation.toRotationSystem data.keep) :
    (data.internalDetourGraph removed).Reachable
      (rotation.toRotationSystem.vertOf removed.1.1)
      (rotation.toRotationSystem.vertOf
        (rotation.toRotationSystem.alpha removed.1.1)) := by
  classical
  set c0 : G.edgeSet := data.crossing 0 with hc0
  set c1 : G.edgeSet := data.crossing 1 with hc1
  set ce : G.edgeSet := rotation.toRotationSystem.edgeOf removed.1.1
    with hce
  have hce0 : ce ≠ c0 := data.internal_edge_ne_crossing rotation removed 0
  have hce1 : ce ≠ c1 := data.internal_edge_ne_crossing rotation removed 1
  have hc01 : c0 ≠ c1 := data.crossing_zero_ne_one rotation
  have htriple :
      (G.deleteEdges ({c0.1, c1.1, ce.1} : Set (Sym2 V))).Connected := by
    by_contra hnot
    rcases cyclicCut_or_incident_of_not_connected_deleteEdges_triple
        (by
          intro v
          have hgiven := hregular v
          convert hgiven using 2 <;> exact Subsingleton.elim _ _)
        hconnected c0 c1 ce hnot with
      ⟨cut, hcard⟩ | ⟨v, hv⟩
    · have := hcyclic cut
      omega
    · -- a vertex carrying exactly the triple
      have hcardTriple :
          ({c0, c1, ce} : Finset G.edgeSet).card = 3 :=
        Finset.card_eq_three.mpr
          ⟨c0, c1, ce, hc01, hce0.symm, hce1.symm, rfl⟩
      have hsubset : incidentEdgeFinset G v ⊆
          ({c0, c1, ce} : Finset G.edgeSet) := by
        intro edge hedge
        apply hv
        simpa [incidentEdgeFinset] using hedge
      have hcardIncident : (incidentEdgeFinset G v).card = 3 := by
        rw [GoertzelV24DeletedEdgeTrail.incidentEdgeFinset_card_eq_degree]
        have hgiven := hregular v
        convert hgiven using 2 <;> exact Subsingleton.elim _ _
      have hall : incidentEdgeFinset G v =
          ({c0, c1, ce} : Finset G.edgeSet) :=
        Finset.eq_of_subset_of_card_le hsubset (by omega)
      by_cases hkeep : data.keep v
      · -- both seam edges at one retained vertex
        have hmem0 : v ∈ ((c0.1 : Sym2 V)) := by
          have : c0 ∈ incidentEdgeFinset G v := by
            rw [hall]
            simp
          simpa [incidentEdgeFinset] using this
        have hmem1 : v ∈ ((c1.1 : Sym2 V)) := by
          have : c1 ∈ incidentEdgeFinset G v := by
            rw [hall]
            simp
          simpa [incidentEdgeFinset] using this
        have h0 := data.keep_endpoint_eq rotation 0 v hkeep hmem0
        have h1 := data.keep_endpoint_eq rotation 1 v hkeep hmem1
        apply data.seamDart_vert_ne
        exact (h0.symm.trans h1 :)
      · -- a deleted vertex on the retained internal edge
        have hmemE : v ∈ ((ce.1 : Sym2 V)) := by
          have : ce ∈ incidentEdgeFinset G v := by
            rw [hall]
            simp
          simpa [incidentEdgeFinset] using this
        have hval : ((ce.1 : Sym2 V)) =
            s(removed.1.1.fst, removed.1.1.snd) := rfl
        rw [hval] at hmemE
        rcases Sym2.mem_iff.mp hmemE with heq | heq
        · exact hkeep (heq ▸ removed.1.2)
        · exact hkeep (heq ▸ removed.2)
  have hle : G.deleteEdges ({c0.1, c1.1, ce.1} : Set (Sym2 V)) ≤
      data.internalDetourGraph removed := by
    intro x y hadj
    rw [SimpleGraph.deleteEdges_adj] at hadj
    obtain ⟨hGadj, hnotmem⟩ := hadj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hnotmem
    push Not at hnotmem
    refine ⟨(⟨(x, y), hGadj⟩ : G.Dart), ?_, ?_, ?_, rfl, rfl⟩
    · intro hedge
      exact hnotmem.2.2 (congrArg Subtype.val hedge)
    · intro hedge
      exact hnotmem.1 (congrArg Subtype.val hedge)
    · intro hedge
      exact hnotmem.2.1 (congrArg Subtype.val hedge)
  exact SimpleGraph.Reachable.mono hle
    (htriple.preconnected removed.1.1.fst removed.1.1.snd)

end FiveEdgeCutYCapData

end

end Mettapedia.GraphTheory.FourColor
