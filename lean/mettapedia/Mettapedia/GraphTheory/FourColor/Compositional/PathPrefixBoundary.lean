import Mettapedia.GraphTheory.CubicPathChordDiagram
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutAttachment
import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedEdgeTrail

/-!
# The edge boundary of a prefix of a simple cubic path

For an interior sweep position, every edge leaving the path prefix is one of
four kinds: it is incident to the initial endpoint, incident to the final
endpoint, the forward path edge, or the edge of an internal chord open at the
sweep.  Consequently, in a cubic graph the boundary width is at most seven
plus the number of open internal chords.

This is graph-theoretic bookkeeping.  It assumes no embedding, colouring, or
four-colour-specific separation theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.PathPrefixBoundary

open CubicPathAttachment
open CubicPathChordDiagram
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DeletedEdgeTrail
open Mettapedia.GraphTheory
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The vertices encountered strictly before a displayed sweep coordinate. -/
def pathPrefixSide {start finish : V} (path : G.Walk start finish)
    (cut : Fin (path.length + 1)) (vertex : V) : Prop :=
  ∃ coordinate : Fin (path.length + 1),
    coordinate < cut ∧ path.getVert coordinate = vertex

@[simp] theorem pathPrefixSide_getVert_iff
    {start finish : V} {path : G.Walk start finish} (hpath : path.IsPath)
    (cut coordinate : Fin (path.length + 1)) :
    pathPrefixSide path cut (path.getVert coordinate) ↔ coordinate < cut := by
  constructor
  · rintro ⟨other, hother, heq⟩
    have hcoordinate : other = coordinate := by
      apply Fin.ext
      exact hpath.getVert_injOn
        (Nat.lt_succ_iff.mp other.isLt)
        (Nat.lt_succ_iff.mp coordinate.isLt) heq
    simpa [hcoordinate] using hother
  · intro hcoordinate
    exact ⟨coordinate, hcoordinate, rfl⟩

/-- The path edge crossing the gap immediately before a positive sweep
coordinate. -/
def forwardPathEdge {start finish : V} (path : G.Walk start finish)
    (cut : Fin (path.length + 1)) (hcut : 0 < cut.val) : G.edgeSet :=
  ⟨s(path.getVert (cut.val - 1), path.getVert cut), by
    have hprevious : cut.val - 1 < path.length := by
      have hcutBound : cut.val ≤ path.length := Nat.lt_succ_iff.mp cut.isLt
      omega
    simpa [Nat.sub_add_cancel hcut] using path.adj_getVert_succ hprevious⟩

/-- The graph edge represented by one internal path chord. -/
def internalChordEdge {start finish : V} (path : G.Walk start finish)
    (chord : OrderedPathChord (path.length + 1))
    (hchord : IsInternalChord chord) : G.edgeSet :=
  ⟨s(path.getVert chord.left, path.getVert chord.right), hchord.2.2.2⟩

/-- Internal chords whose endpoints lie on opposite sides of the sweep. -/
def openInternalChords {start finish : V}
    (path : G.Walk start finish) (cut : Fin (path.length + 1)) :
    Finset (OrderedPathChord (path.length + 1)) :=
  (internalChords path).filter fun chord =>
    chord.left < cut ∧ cut ≤ chord.right

/-- Edges represented by the open internal chords. -/
def openInternalChordEdges {start finish : V}
    (path : G.Walk start finish) (cut : Fin (path.length + 1)) :
    Finset G.edgeSet :=
  (openInternalChords path cut).attach.image fun chord =>
    internalChordEdge path chord.1
      ((mem_internalChords_iff.mp (Finset.mem_filter.mp chord.2).1))

theorem card_openInternalChordEdges_le {start finish : V}
    (path : G.Walk start finish) (cut : Fin (path.length + 1)) :
    (openInternalChordEdges path cut).card ≤
      (openInternalChords path cut).card := by
  rw [openInternalChordEdges]
  exact (Finset.card_image_le.trans_eq Finset.card_attach)

/-- The finite carrier which covers the boundary of a path prefix. -/
def prefixBoundaryCover {start finish : V}
    (path : G.Walk start finish) (cut : Fin (path.length + 1))
    (hcut : 0 < cut.val) : Finset G.edgeSet :=
  incidentEdgeFinset G start ∪ incidentEdgeFinset G finish ∪
    {forwardPathEdge path cut hcut} ∪ openInternalChordEdges path cut

theorem card_prefixBoundaryCover_le
    {start finish : V} {path : G.Walk start finish}
    (hregular : G.IsRegularOfDegree 3)
    (cut : Fin (path.length + 1)) (hcut : 0 < cut.val) :
    (prefixBoundaryCover path cut hcut).card ≤
      7 + (openInternalChords path cut).card := by
  calc
    (prefixBoundaryCover path cut hcut).card ≤
        (incidentEdgeFinset G start).card +
          (incidentEdgeFinset G finish).card +
          ({forwardPathEdge path cut hcut} : Finset G.edgeSet).card +
          (openInternalChordEdges path cut).card := by
      simp only [prefixBoundaryCover]
      calc
        (_ ∪ openInternalChordEdges path cut).card ≤
            (incidentEdgeFinset G start ∪ incidentEdgeFinset G finish ∪
              {forwardPathEdge path cut hcut}).card +
              (openInternalChordEdges path cut).card :=
          Finset.card_union_le _ _
        _ ≤ ((incidentEdgeFinset G start ∪
              incidentEdgeFinset G finish).card +
              ({forwardPathEdge path cut hcut} : Finset G.edgeSet).card) +
              (openInternalChordEdges path cut).card := by
            gcongr
            exact Finset.card_union_le _ _
        _ ≤ (((incidentEdgeFinset G start).card +
              (incidentEdgeFinset G finish).card) +
              ({forwardPathEdge path cut hcut} : Finset G.edgeSet).card) +
              (openInternalChordEdges path cut).card := by
            gcongr
            exact Finset.card_union_le _ _
    _ ≤ 3 + 3 + 1 + (openInternalChords path cut).card := by
      rw [incidentEdgeFinset_card_eq_degree,
        incidentEdgeFinset_card_eq_degree,
        hregular.degree_eq, hregular.degree_eq]
      simp only [Finset.card_singleton]
      exact Nat.add_le_add_left (card_openInternalChordEdges_le path cut) 7
    _ = 7 + (openInternalChords path cut).card := by omega

theorem internalChordEdge_mem_openInternalChordEdges
    {start finish : V} {path : G.Walk start finish}
    (cut : Fin (path.length + 1))
    (chord : OrderedPathChord (path.length + 1))
    (hopen : chord ∈ openInternalChords path cut) :
    internalChordEdge path chord
        (mem_internalChords_iff.mp (Finset.mem_filter.mp hopen).1) ∈
      openInternalChordEdges path cut := by
  rw [openInternalChordEdges]
  apply Finset.mem_image.mpr
  refine ⟨⟨chord, hopen⟩, by simp, ?_⟩
  rfl

/-- Every edge crossing a positive path prefix belongs to the explicit
endpoint/forward/open-chord cover, provided no strict internal attachment
leaves the full path. -/
theorem mem_prefixBoundaryCover_of_crosses
    {start finish : V} {path : G.Walk start finish}
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (hnoExternal : ∀ position : InternalPosition path,
      ¬IsExternalAttachment hpath hregular position)
    (cut : Fin (path.length + 1)) (hcut : 0 < cut.val)
    (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G (pathPrefixSide path cut) edge) :
    edge ∈ prefixBoundaryCover path cut hcut := by
  rcases hcross with
    ⟨inside, outside, hinsideEdge, houtsideEdge,
      ⟨coordinate, hcoordinateCut, hcoordinateInside⟩, houtside⟩
  rw [prefixBoundaryCover]
  simp only [Finset.mem_union]
  have hne : inside ≠ outside := by
    intro heq
    exact houtside (heq ▸
      ⟨coordinate, hcoordinateCut, hcoordinateInside⟩)
  have hedgeValue : (edge : Sym2 V) = s(inside, outside) :=
    sym2_eq_mk_of_mem_of_mem_of_ne hinsideEdge houtsideEdge hne
  have hadj : G.Adj inside outside :=
    (SimpleGraph.mem_edgeSet G).mp (by simpa [hedgeValue] using edge.property)
  by_cases hcoordinateZero : coordinate.val = 0
  · have hinsideStart : inside = start := by
      rw [← hcoordinateInside]
      have : coordinate = 0 := Fin.ext hcoordinateZero
      simp [this]
    have hincident : edge ∈ incidentEdgeFinset G start := by
      simp [incidentEdgeFinset, hedgeValue, hinsideStart]
    exact Or.inl (Or.inl (Or.inl hincident))
  · let position : InternalPosition path :=
      ⟨coordinate.val - 1, by
        have hcoordinateLtLength : coordinate.val < path.length := by
          have hcutBound : cut.val ≤ path.length :=
            Nat.lt_succ_iff.mp cut.isLt
          omega
        omega⟩
    have hpositionIndex : position.index = coordinate.val := by
      simp [position, InternalPosition.index]
      omega
    have hpositionCoordinate : position.coordinate = coordinate := by
      apply Fin.ext
      exact hpositionIndex
    have hpositionVertex : position.vertex = inside := by
      simp only [InternalPosition.vertex, hpositionIndex]
      exact hcoordinateInside
    have hpreviousInside : pathPrefixSide path cut position.previousVertex := by
      refine ⟨⟨position.index - 1, by
        have := position.index_lt_length
        omega⟩, ?_, rfl⟩
      change position.index - 1 < cut.val
      rw [hpositionIndex]
      omega
    have houtsideNotPrevious : outside ≠ position.previousVertex := by
      intro heq
      exact houtside (heq ▸ hpreviousInside)
    by_cases houtsideNext : outside = position.nextVertex
    · have hnextIndex : position.index + 1 = cut.val := by
        by_contra hneIndex
        have hnextLt : position.index + 1 < cut.val := by
          rw [hpositionIndex]
          omega
        apply houtside
        refine ⟨⟨position.index + 1, by
          have := cut.isLt
          omega⟩, hnextLt, ?_⟩
        simpa [InternalPosition.nextVertex] using houtsideNext.symm
      have hedgeForward : edge = forwardPathEdge path cut hcut := by
        apply Subtype.ext
        rw [hedgeValue, forwardPathEdge]
        change s(inside, outside) =
          s(path.getVert (cut.val - 1), path.getVert cut)
        have hinsidePrevious : inside = path.getVert (cut.val - 1) := by
          rw [← hcoordinateInside]
          congr 1
          rw [hpositionIndex] at hnextIndex
          omega
        have houtsideCut : outside = path.getVert cut := by
          simpa [InternalPosition.nextVertex, hnextIndex] using houtsideNext
        rw [hinsidePrevious, houtsideCut]
      exact Or.inl (Or.inr (by rw [hedgeForward]; simp))
    · have houtsideMemAttachment :
          outside ∈ attachmentNeighborSet path position := by
        refine ⟨?_, ?_⟩
        · simpa [hpositionVertex] using hadj
        · change outside ∉
            path.toSubgraph.neighborSet (path.getVert position.index)
          rw [hpath.neighborSet_toSubgraph_internal
            position.index_ne_zero position.index_lt_length]
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          push Not
          exact ⟨houtsideNotPrevious, houtsideNext⟩
      have houtsideAttachment : outside =
          attachmentNeighbor hpath hregular position :=
        eq_attachmentNeighbor_of_mem hpath hregular position
          houtsideMemAttachment
      rcases external_or_endpoint_or_mem_internalChord
          hpath hregular position with
        hexternal | hendpoint | ⟨chord, hchordMem, hincident⟩
      · exact False.elim (hnoExternal position hexternal)
      · rcases hendpoint with hinitial | hfinal
        · have houtsideStart : outside = start :=
            houtsideAttachment.trans hinitial
          have hincidentStart : edge ∈ incidentEdgeFinset G start := by
            simp [incidentEdgeFinset, hedgeValue, houtsideStart]
          exact Or.inl (Or.inl (Or.inl hincidentStart))
        · have houtsideFinish : outside = finish :=
            houtsideAttachment.trans hfinal
          have hincidentFinish : edge ∈ incidentEdgeFinset G finish := by
            simp [incidentEdgeFinset, hedgeValue, houtsideFinish]
          exact Or.inl (Or.inl (Or.inr hincidentFinish))
      · have hincidentLeft : position.coordinate = chord.left := by
          rcases hincident with hleft | hright
          · exact hleft
          · have hrightLtCut : chord.right < cut := by
              calc
                chord.right = position.coordinate := hright.symm
                _ = coordinate := hpositionCoordinate
                _ < cut := hcoordinateCut
            have hleftLtCut : chord.left < cut :=
              lt_trans chord.left_lt_right hrightLtCut
            have hotherInside : pathPrefixSide path cut
                (path.getVert chord.left) :=
              (pathPrefixSide_getVert_iff hpath cut chord.left).2 hleftLtCut
            have hpositionRight : position =
                rightPosition chord (mem_internalChords_iff.mp hchordMem) := by
              apply internalPosition_coordinate_injective
              exact hright.trans
                (rightPosition_coordinate chord
                  (mem_internalChords_iff.mp hchordMem)).symm
            have hotherAttachment : path.getVert chord.left =
                attachmentNeighbor hpath hregular position := by
              have hendpoint :=
                (rightAttachment hpath hregular chord
                  (mem_internalChords_iff.mp hchordMem)).endpoint_eq
              change path.getVert chord.left =
                attachmentNeighbor hpath hregular
                  (rightPosition chord (mem_internalChords_iff.mp hchordMem))
                at hendpoint
              simpa [hpositionRight] using hendpoint
            exact False.elim (houtside (by
              rw [houtsideAttachment, ← hotherAttachment]
              exact hotherInside))
        have hleftLtCut : chord.left < cut := by
          simpa [← hincidentLeft, hpositionCoordinate] using hcoordinateCut
        have hpositionLeft : position =
            leftPosition chord (mem_internalChords_iff.mp hchordMem) := by
          apply internalPosition_coordinate_injective
          exact hincidentLeft.trans
            (leftPosition_coordinate chord
              (mem_internalChords_iff.mp hchordMem)).symm
        have hrightAttachment : path.getVert chord.right =
            attachmentNeighbor hpath hregular position := by
          have hendpoint :=
            (leftAttachment hpath hregular chord
              (mem_internalChords_iff.mp hchordMem)).endpoint_eq
          change path.getVert chord.right =
            attachmentNeighbor hpath hregular
              (leftPosition chord (mem_internalChords_iff.mp hchordMem))
            at hendpoint
          simpa [hpositionLeft] using hendpoint
        have hcutLeRight : cut ≤ chord.right := by
          by_contra hnot
          have hrightLtCut : chord.right < cut := lt_of_not_ge hnot
          apply houtside
          rw [houtsideAttachment, ← hrightAttachment]
          exact (pathPrefixSide_getVert_iff hpath cut chord.right).2
            hrightLtCut
        have hopen : chord ∈ openInternalChords path cut := by
          exact Finset.mem_filter.mpr ⟨hchordMem, hleftLtCut, hcutLeRight⟩
        have hedgeChord : edge = internalChordEdge path chord
            (mem_internalChords_iff.mp hchordMem) := by
          apply Subtype.ext
          rw [hedgeValue, internalChordEdge]
          change s(inside, outside) =
            s(path.getVert chord.left, path.getVert chord.right)
          have hinsideLeft : inside = path.getVert chord.left := by
            rw [← hcoordinateInside]
            congr 1
            exact congrArg Fin.val
              (hpositionCoordinate.symm.trans hincidentLeft)
          rw [hinsideLeft, houtsideAttachment, ← hrightAttachment]
        exact Or.inr (by simpa [hedgeChord] using
          internalChordEdge_mem_openInternalChordEdges cut chord hopen)

/-- A positive prefix has boundary width at most seven plus the number of
open internal chords. -/
theorem card_crossingEdgeFinset_pathPrefixSide_le
    {start finish : V} {path : G.Walk start finish}
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (hnoExternal : ∀ position : InternalPosition path,
      ¬IsExternalAttachment hpath hregular position)
    (cut : Fin (path.length + 1)) (hcut : 0 < cut.val) :
    (crossingEdgeFinset G (pathPrefixSide path cut)).card ≤
      7 + (openInternalChords path cut).card := by
  apply le_trans (Finset.card_le_card ?_)
    (card_prefixBoundaryCover_le hregular cut hcut)
  intro edge hedge
  exact mem_prefixBoundaryCover_of_crosses hpath hregular hnoExternal cut hcut
    edge ((mem_crossingEdgeFinset_iff _ _).mp hedge)

end

end Mettapedia.GraphTheory.FourColor.Compositional.PathPrefixBoundary
