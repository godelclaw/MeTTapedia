import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedTrail

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DeletedEdgeTrail

open SimpleGraph
open GoertzelV24FramedTrail

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The graph-side trail obtained by removing the edge with endpoints `u`
and `v`. -/
abbrev DeletedEdgeGraph (G : SimpleGraph V) (u v : V) : SimpleGraph V :=
  G.deleteEdges ({s(u, v)} : Set (Sym2 V))

local instance ambientEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance ambientEdgeSetFintype : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

local instance deletedEdgeSetFintype (u v : V) :
    Fintype (DeletedEdgeGraph G u v).edgeSet :=
  Fintype.ofFinite (DeletedEdgeGraph G u v).edgeSet

local instance graphNeighborSetFintype (H : SimpleGraph V) (vertex : V) :
    Fintype (H.neighborSet vertex) :=
  Fintype.ofFinite (H.neighborSet vertex)

/-- The two marked defects of a deleted edge, in endpoint order. -/
def deletedEdgeDefectVertex (u v : V) : Fin 2 → V :=
  fun i => if i = 0 then u else v

@[simp]
theorem deletedEdgeDefectVertex_zero (u v : V) :
    deletedEdgeDefectVertex u v 0 = u := by
  simp [deletedEdgeDefectVertex]

@[simp]
theorem deletedEdgeDefectVertex_one (u v : V) :
    deletedEdgeDefectVertex u v 1 = v := by
  simp [deletedEdgeDefectVertex]

/-- A graph-side deleted-edge frame with no frozen edges. It is the widest
Kempe-move domain attached canonically to a removed edge; annular applications
may replace the three structural finsets while keeping the same defects. -/
def unrestrictedDeletedEdgeFrame (G : SimpleGraph V) (u v : V) :
    FramedTrailData (DeletedEdgeGraph G u v) where
  innerContainerEdges := ∅
  outerContainerEdges := ∅
  betweenRegionCoreEdges := Finset.univ
  frozenInterfaceEdges := ∅
  defectVertex := deletedEdgeDefectVertex u v

@[simp]
theorem unrestrictedDeletedEdgeFrame_defectVertex
    (G : SimpleGraph V) (u v : V) :
    (unrestrictedDeletedEdgeFrame G u v).defectVertex =
      deletedEdgeDefectVertex u v := rfl

/-- The incident-edge finset has Mathlib's graph degree as its cardinality.
This local copy keeps the deleted-edge bridge independent of the flow layer. -/
private theorem incidentEdgeFinset_card_eq_degree_local
    {H : SimpleGraph V} [Fintype H.edgeSet] (vertex : V) :
    (incidentEdgeFinset H vertex).card = H.degree vertex := by
  have hmap :
      (incidentEdgeFinset H vertex).map
          (Function.Embedding.subtype (fun edge : Sym2 V => edge ∈ H.edgeSet)) =
        H.incidenceFinset vertex := by
    rw [SimpleGraph.incidenceFinset_eq_filter]
    ext edge
    simp [incidentEdgeFinset, and_comm]
  calc
    (incidentEdgeFinset H vertex).card =
        ((incidentEdgeFinset H vertex).map
          (Function.Embedding.subtype
            (fun edge : Sym2 V => edge ∈ H.edgeSet))).card := by simp
    _ = (H.incidenceFinset vertex).card := by rw [hmap]
    _ = H.degree vertex := by simp

/-- At the first endpoint, deleting `s(u,v)` erases exactly the neighbor
`v`. -/
theorem neighborFinset_deletedEdgeGraph_left {u v : V}
    (huv : G.Adj u v) :
    (DeletedEdgeGraph G u v).neighborFinset u =
      (G.neighborFinset u).erase v := by
  ext vertex
  simp [DeletedEdgeGraph, huv.ne, and_comm]

/-- At the second endpoint, deleting `s(u,v)` erases exactly the neighbor
`u`. -/
theorem neighborFinset_deletedEdgeGraph_right {u v : V}
    (huv : G.Adj u v) :
    (DeletedEdgeGraph G u v).neighborFinset v =
      (G.neighborFinset v).erase u := by
  ext vertex
  simp [DeletedEdgeGraph, Ne.symm huv.ne, and_comm]

/-- Deleting `s(u,v)` changes no incidence at a vertex other than `u` and
`v`. -/
theorem neighborFinset_deletedEdgeGraph_of_ne {u v vertex : V}
    (hvertexU : vertex ≠ u) (hvertexV : vertex ≠ v) :
    (DeletedEdgeGraph G u v).neighborFinset vertex =
      G.neighborFinset vertex := by
  ext other
  simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj,
    Set.mem_singleton_iff]
  constructor
  · exact And.left
  · intro hadj
    refine ⟨hadj, ?_⟩
    intro hedge
    rcases Sym2.eq_iff.mp hedge with hstraight | hswapped
    · exact hvertexU hstraight.1
    · exact hvertexV hswapped.1

/-- Removing one edge from a cubic graph leaves degree two at its endpoints
and degree three everywhere else. Therefore the canonical unrestricted frame
has exactly the computed defect structure required by `FramedTrailData`. -/
theorem unrestrictedDeletedEdgeFrame_wellFormed {u v : V}
    (huv : G.Adj u v)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3) :
    (unrestrictedDeletedEdgeFrame G u v).WellFormed := by
  have huvNe : u ≠ v := huv.ne
  have hdegreeG : ∀ vertex : V, G.degree vertex = 3 := by
    intro vertex
    rw [← incidentEdgeFinset_card_eq_degree_local (H := G)]
    exact hcubic vertex
  have hleft :
      (incidentEdgeFinset (DeletedEdgeGraph G u v) u).card = 2 := by
    rw [incidentEdgeFinset_card_eq_degree_local]
    change ((DeletedEdgeGraph G u v).neighborFinset u).card = 2
    rw [neighborFinset_deletedEdgeGraph_left huv,
      Finset.card_erase_of_mem]
    · simp [hdegreeG u]
    · simpa using huv
  have hright :
      (incidentEdgeFinset (DeletedEdgeGraph G u v) v).card = 2 := by
    rw [incidentEdgeFinset_card_eq_degree_local]
    change ((DeletedEdgeGraph G u v).neighborFinset v).card = 2
    rw [neighborFinset_deletedEdgeGraph_right huv,
      Finset.card_erase_of_mem]
    · simp [hdegreeG v]
    · simpa using huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro first second heq
    fin_cases first <;> fin_cases second <;>
      simp_all [deletedEdgeDefectVertex]
  · intro i
    fin_cases i
    · exact hleft
    · exact hright
  · intro vertex hvertex
    have hvertexU : vertex ≠ u := by
      simpa using hvertex 0
    have hvertexV : vertex ≠ v := by
      simpa using hvertex 1
    rw [incidentEdgeFinset_card_eq_degree_local]
    change ((DeletedEdgeGraph G u v).neighborFinset vertex).card = 3
    rw [neighborFinset_deletedEdgeGraph_of_ne hvertexU hvertexV]
    exact hdegreeG vertex
  · simp [FramedTrailData.movableEdges, unrestrictedDeletedEdgeFrame]
  · simp [FramedTrailData.movableEdges, unrestrictedDeletedEdgeFrame]
  · simp [FramedTrailData.movableEdges, unrestrictedDeletedEdgeFrame]

/-- A retained edge of the deleted-edge graph, regarded as an ambient edge. -/
def deletedEdgeToAmbientEdge {u v : V}
    (edge : (DeletedEdgeGraph G u v).edgeSet) : G.edgeSet :=
  ⟨edge.1, by
    have hedge :
        edge.1 ∈ G.edgeSet ∧ edge.1 ∉ ({s(u, v)} : Set (Sym2 V)) := by
      simpa [DeletedEdgeGraph] using edge.2
    exact hedge.1⟩

/-- An ambient edge distinct from the removed edge, regarded as an edge of
the deleted-edge graph. -/
def ambientEdgeToDeletedEdge {u v : V}
    (edge : G.edgeSet) (hne : edge.1 ≠ s(u, v)) :
    (DeletedEdgeGraph G u v).edgeSet :=
  ⟨edge.1, by simp [DeletedEdgeGraph, edge.2, hne]⟩

@[simp]
theorem deletedEdgeToAmbientEdge_val {u v : V}
    (edge : (DeletedEdgeGraph G u v).edgeSet) :
    (deletedEdgeToAmbientEdge edge).1 = edge.1 := rfl

@[simp]
theorem ambientEdgeToDeletedEdge_val {u v : V}
    (edge : G.edgeSet) (hne : edge.1 ≠ s(u, v)) :
    (ambientEdgeToDeletedEdge edge hne).1 = edge.1 := rfl

/-- The edge-color function obtained by assigning `missingColor` to the
removed edge and retaining every color on the deleted-edge graph. -/
def insertMissingEdgeColorFunction {u v : V}
    (C : (DeletedEdgeGraph G u v).EdgeColoring Color)
    (missingColor : Color) (edge : G.edgeSet) : Color :=
  if h : edge.1 = s(u, v) then missingColor
  else C (ambientEdgeToDeletedEdge edge h)

/-- Properness of the inserted-edge color function. The only new
adjacencies are between the inserted edge and retained edges incident to one
of its two endpoints. -/
theorem insertMissingEdgeColorFunction_valid {u v : V}
    (C : (DeletedEdgeGraph G u v).EdgeColoring Color)
    (missingColor : Color)
    (hadmissibleU :
      ∀ edge ∈ incidentEdgeFinset (DeletedEdgeGraph G u v) u,
        missingColor ≠ C edge)
    (hadmissibleV :
      ∀ edge ∈ incidentEdgeFinset (DeletedEdgeGraph G u v) v,
        missingColor ≠ C edge) :
    ∀ {first second : G.edgeSet}, G.lineGraph.Adj first second →
      insertMissingEdgeColorFunction C missingColor first ≠
        insertMissingEdgeColorFunction C missingColor second := by
  intro first second hadj
  by_cases hfirst : first.1 = s(u, v)
  · have hsecond : second.1 ≠ s(u, v) := by
      intro hsecond
      exact hadj.ne (Subtype.ext (hfirst.trans hsecond.symm))
    rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hadj with
      ⟨_hne, endpoint, hendpointFirst, hendpointSecond⟩
    have hendpoint : endpoint = u ∨ endpoint = v := by
      simpa [hfirst] using hendpointFirst
    have hnew :
        missingColor ≠ C (ambientEdgeToDeletedEdge second hsecond) := by
      rcases hendpoint with rfl | rfl
      · apply hadmissibleU
        simpa [incidentEdgeFinset] using hendpointSecond
      · apply hadmissibleV
        simpa [incidentEdgeFinset] using hendpointSecond
    simpa [insertMissingEdgeColorFunction, hfirst, hsecond] using hnew
  · by_cases hsecond : second.1 = s(u, v)
    · rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hadj with
        ⟨_hne, endpoint, hendpointFirst, hendpointSecond⟩
      have hendpoint : endpoint = u ∨ endpoint = v := by
        simpa [hsecond] using hendpointSecond
      have hnew :
          missingColor ≠ C (ambientEdgeToDeletedEdge first hfirst) := by
        rcases hendpoint with rfl | rfl
        · apply hadmissibleU
          simpa [incidentEdgeFinset] using hendpointFirst
        · apply hadmissibleV
          simpa [incidentEdgeFinset] using hendpointFirst
      simpa [insertMissingEdgeColorFunction, hfirst, hsecond] using hnew.symm
    · have hdeletedAdj :
          (DeletedEdgeGraph G u v).lineGraph.Adj
            (ambientEdgeToDeletedEdge first hfirst)
            (ambientEdgeToDeletedEdge second hsecond) := by
        rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hadj with
          ⟨hne, endpoint, hendpointFirst, hendpointSecond⟩
        apply (SimpleGraph.lineGraph_adj_iff_exists).2
        refine ⟨?_, endpoint, hendpointFirst, hendpointSecond⟩
        intro heq
        apply hne
        apply Subtype.ext
        exact congrArg
          (fun edge : (DeletedEdgeGraph G u v).edgeSet => edge.1) heq
      simpa [insertMissingEdgeColorFunction, hfirst, hsecond] using
        C.valid hdeletedAdj

/-- Insert the missing edge with a color admissible at both defects. -/
def insertMissingEdgeColoring {u v : V}
    (C : (DeletedEdgeGraph G u v).EdgeColoring Color)
    (missingColor : Color)
    (hadmissibleU :
      ∀ edge ∈ incidentEdgeFinset (DeletedEdgeGraph G u v) u,
        missingColor ≠ C edge)
    (hadmissibleV :
      ∀ edge ∈ incidentEdgeFinset (DeletedEdgeGraph G u v) v,
        missingColor ≠ C edge) : G.EdgeColoring Color :=
  SimpleGraph.Coloring.mk (insertMissingEdgeColorFunction C missingColor)
    (insertMissingEdgeColorFunction_valid C missingColor
      hadmissibleU hadmissibleV)

@[simp]
theorem insertMissingEdgeColoring_apply_removed {u v : V}
    (C : (DeletedEdgeGraph G u v).EdgeColoring Color)
    (missingColor : Color)
    (hadmissibleU :
      ∀ edge ∈ incidentEdgeFinset (DeletedEdgeGraph G u v) u,
        missingColor ≠ C edge)
    (hadmissibleV :
      ∀ edge ∈ incidentEdgeFinset (DeletedEdgeGraph G u v) v,
        missingColor ≠ C edge)
    (edge : G.edgeSet) (hedge : edge.1 = s(u, v)) :
    insertMissingEdgeColoring C missingColor hadmissibleU hadmissibleV edge =
      missingColor := by
  change insertMissingEdgeColorFunction C missingColor edge = missingColor
  simp [insertMissingEdgeColorFunction, hedge]

@[simp]
theorem insertMissingEdgeColoring_apply_retained {u v : V}
    (C : (DeletedEdgeGraph G u v).EdgeColoring Color)
    (missingColor : Color)
    (hadmissibleU :
      ∀ edge ∈ incidentEdgeFinset (DeletedEdgeGraph G u v) u,
        missingColor ≠ C edge)
    (hadmissibleV :
      ∀ edge ∈ incidentEdgeFinset (DeletedEdgeGraph G u v) v,
        missingColor ≠ C edge)
    (edge : G.edgeSet) (hedge : edge.1 ≠ s(u, v)) :
    insertMissingEdgeColoring C missingColor hadmissibleU hadmissibleV edge =
      C (ambientEdgeToDeletedEdge edge hedge) := by
  change insertMissingEdgeColorFunction C missingColor edge =
    C (ambientEdgeToDeletedEdge edge hedge)
  simp [insertMissingEdgeColorFunction, hedge]

/-- A Tait coloring of the deleted-edge graph extends to the ambient graph
when one nonzero color is admissible at both endpoints of the removed edge. -/
theorem isTaitEdgeColoring_insertMissingEdgeColoring {u v : V}
    (C : (DeletedEdgeGraph G u v).EdgeColoring Color)
    (hC : IsTaitEdgeColoring (DeletedEdgeGraph G u v) C)
    (missingColor : Color) (hmissingColor : missingColor ≠ 0)
    (hadmissibleU :
      ∀ edge ∈ incidentEdgeFinset (DeletedEdgeGraph G u v) u,
        missingColor ≠ C edge)
    (hadmissibleV :
      ∀ edge ∈ incidentEdgeFinset (DeletedEdgeGraph G u v) v,
        missingColor ≠ C edge) :
    IsTaitEdgeColoring G
      (insertMissingEdgeColoring C missingColor hadmissibleU hadmissibleV) := by
  intro edge
  by_cases hedge : edge.1 = s(u, v)
  · simpa [insertMissingEdgeColoring_apply_removed C missingColor
      hadmissibleU hadmissibleV edge hedge] using hmissingColor
  · simpa [insertMissingEdgeColoring_apply_retained C missingColor
      hadmissibleU hadmissibleV edge hedge] using
      hC (ambientEdgeToDeletedEdge edge hedge)

/-- Honest graph-level endpoint of Trail Completability. If the framed
deleted-edge coloring can be moved until its two defect requests match, the
missing edge can be inserted and the ambient graph is Tait colorable. -/
theorem exists_taitColoring_of_framedTangleCompletable {u v : V}
    (data : FramedTrailData (DeletedEdgeGraph G u v))
    (hdata : data.WellFormed)
    (hdefectZero : data.defectVertex 0 = u)
    (hdefectOne : data.defectVertex 1 = v)
    (C : (DeletedEdgeGraph G u v).EdgeColoring Color)
    (hC : IsTaitEdgeColoring (DeletedEdgeGraph G u v) C)
    (hcomplete : FramedTangleCompletable data C) :
    ∃ ambientColoring : G.EdgeColoring Color,
      IsTaitEdgeColoring G ambientColoring := by
  rcases
      (framedTangleCompletable_iff_exists_reachable_properTrailExtensionColor
        data hdata C hC).1 hcomplete with
    ⟨C', missingColor, hreachable, hadmissible⟩
  have hC' : IsTaitEdgeColoring (DeletedEdgeGraph G u v) C' :=
    framedTangleKempeReachable_preserves_isTaitEdgeColoring hreachable hC
  have hadmissibleU :
      FramedTrailData.IsAdmissibleAtDefect data C' 0 missingColor :=
    hadmissible.1
  have hadmissibleV :
      FramedTrailData.IsAdmissibleAtDefect data C' 1 missingColor :=
    hadmissible.2
  have hadmissibleAtU :
      ∀ edge ∈ incidentEdgeFinset (DeletedEdgeGraph G u v) u,
        missingColor ≠ C' edge := by
    simpa [hdefectZero] using hadmissibleU.2
  have hadmissibleAtV :
      ∀ edge ∈ incidentEdgeFinset (DeletedEdgeGraph G u v) v,
        missingColor ≠ C' edge := by
    simpa [hdefectOne] using hadmissibleV.2
  exact ⟨insertMissingEdgeColoring C' missingColor
      hadmissibleAtU hadmissibleAtV,
    isTaitEdgeColoring_insertMissingEdgeColoring C' hC' missingColor
      hadmissibleU.1 hadmissibleAtU hadmissibleAtV⟩

/-- Contrapositive form consumed by a minimal-counterexample argument: in an
uncolorable ambient graph, no Tait coloring of its framed deleted-edge trail
can be completable. -/
theorem not_framedTangleCompletable_of_not_taitColorable {u v : V}
    (data : FramedTrailData (DeletedEdgeGraph G u v))
    (hdata : data.WellFormed)
    (hdefectZero : data.defectVertex 0 = u)
    (hdefectOne : data.defectVertex 1 = v)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedEdgeGraph G u v).EdgeColoring Color)
    (hC : IsTaitEdgeColoring (DeletedEdgeGraph G u v) C) :
    ¬ FramedTangleCompletable data C := by
  intro hcomplete
  exact hnotColorable
    (exists_taitColoring_of_framedTangleCompletable data hdata
      hdefectZero hdefectOne C hC hcomplete)

/-- Canonical deleted-edge specialization: on a cubic graph, completion in
the unrestricted frame inserts the removed edge and colors the ambient
graph. -/
theorem exists_taitColoring_of_unrestrictedDeletedEdgeCompletable {u v : V}
    (huv : G.Adj u v)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedEdgeGraph G u v).EdgeColoring Color)
    (hC : IsTaitEdgeColoring (DeletedEdgeGraph G u v) C)
    (hcomplete :
      FramedTangleCompletable (unrestrictedDeletedEdgeFrame G u v) C) :
    ∃ ambientColoring : G.EdgeColoring Color,
      IsTaitEdgeColoring G ambientColoring := by
  apply exists_taitColoring_of_framedTangleCompletable
    (unrestrictedDeletedEdgeFrame G u v)
    (unrestrictedDeletedEdgeFrame_wellFormed huv hcubic)
  · simp
  · simp
  · exact hC
  · exact hcomplete

/-- Exact obstruction exposed by an uncolorable cubic graph: every Tait
coloring of a one-edge deletion is non-completable, even when no interface
edge is frozen. -/
theorem not_unrestrictedDeletedEdgeCompletable_of_not_taitColorable
    {u v : V}
    (huv : G.Adj u v)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedEdgeGraph G u v).EdgeColoring Color)
    (hC : IsTaitEdgeColoring (DeletedEdgeGraph G u v) C) :
    ¬ FramedTangleCompletable (unrestrictedDeletedEdgeFrame G u v) C := by
  apply not_framedTangleCompletable_of_not_taitColorable
    (unrestrictedDeletedEdgeFrame G u v)
    (unrestrictedDeletedEdgeFrame_wellFormed huv hcubic)
  · simp
  · simp
  · exact hnotColorable
  · exact hC

/-- The precise final bridge needed from a Trail Completability theorem. A
single colorable edge deletion of a cubic graph suffices, provided every such
starting coloring is completable in its graph-side frame. -/
theorem exists_taitColoring_of_deletedEdgeColorable_and_completable
    {u v : V}
    (huv : G.Adj u v)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hdeletedColorable :
      ∃ C : (DeletedEdgeGraph G u v).EdgeColoring Color,
        IsTaitEdgeColoring (DeletedEdgeGraph G u v) C)
    (hcompletable :
      ∀ C : (DeletedEdgeGraph G u v).EdgeColoring Color,
        IsTaitEdgeColoring (DeletedEdgeGraph G u v) C →
          FramedTangleCompletable
            (unrestrictedDeletedEdgeFrame G u v) C) :
    ∃ ambientColoring : G.EdgeColoring Color,
      IsTaitEdgeColoring G ambientColoring := by
  rcases hdeletedColorable with ⟨C, hC⟩
  exact exists_taitColoring_of_unrestrictedDeletedEdgeCompletable
    huv hcubic C hC (hcompletable C hC)

end

end GoertzelV24DeletedEdgeTrail

end Mettapedia.GraphTheory.FourColor
