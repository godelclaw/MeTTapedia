import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedTrail

/-!
# Source-side between-region moves and the framed L10 seam

The v23 spine permits switches on two-color circuits lying in the annular
between-region.  The repaired framed model permits every two-color component
disjoint from the frozen outward interface, including noncircuit components
ending at the two defects.  This module states the two relations independently
and isolates their exact difference.

No equality of the move relations is claimed.  Under an explicit edge-level
alignment of the source annulus with the movable part of the frame, a framed
move is either a v23 circuit move or a noncircuit framed move.  Identifying the
second alternative with the source formation's defect-ending path operation is
the remaining geometric part of playbook flag L10.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [Fintype G.edgeSet] [DecidableEq G.edgeSet]

namespace FramedTrailData

/-- The graph edges explicitly named by the source annulus: its two container
curves and the formation edges between them. -/
def sourceBetweenRegionEdges (data : FramedTrailData G) : Finset G.edgeSet :=
  data.innerContainerEdges ∪ data.outerContainerEdges ∪
    data.betweenRegionCoreEdges

/-- Edge-level formation/frame alignment needed before comparing the source
and framed move relations.  This is deliberately a separate hypothesis: the
generic framed graph does not by itself assert that the three named source
pieces exhaust every movable edge. -/
def BetweenRegionEdgeAligned (data : FramedTrailData G) : Prop :=
  data.sourceBetweenRegionEdges = data.movableEdges

omit [Fintype V] in
/-- Every edge explicitly belonging to a well-formed source annulus is movable
in its frame. -/
theorem sourceBetweenRegionEdges_subset_movableEdges
    (data : FramedTrailData G) (hdata : data.WellFormed) :
    data.sourceBetweenRegionEdges ⊆ data.movableEdges := by
  intro edge hedge
  simp only [sourceBetweenRegionEdges, Finset.mem_union] at hedge
  rcases hedge with (hedge | hedge) | hedge
  · exact hdata.innerContainer_movable hedge
  · exact hdata.outerContainer_movable hedge
  · exact hdata.betweenRegionCore_movable hedge

end FramedTrailData

/-- A selected Kempe component is circuit-shaped when its connected induced
line graph is 2-regular.  Its vertices are the selected edges of the original
framed graph.  This structural condition is independent of frozen-interface
legality and of the source annulus support condition. -/
def IsCircuitKempeComponent
    (C : G.EdgeColoring Color) (a b : Color)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) : Prop :=
  ∀ edge : K, (K.toSimpleGraph.neighborSet edge).ncard = 2

/-- The v23 source-side one-step relation: switch a genuine two-color circuit
whose complete support lies in the annular between-region.  Container edges
are part of that region, matching the repaired source convention that the
containers move while only outward-crossing interface edges freeze. -/
def KauffmanBetweenRegionKempeStep
    (data : FramedTrailData G)
    (C C' : G.EdgeColoring Color) : Prop :=
  ∃ a b : Color,
    ∃ K : (C.bicoloredSubgraph a b).ConnectedComponent,
      ValidColorPair a b ∧
      IsCircuitKempeComponent C a b K ∧
      C.kempeComponentSet a b K ⊆
        (data.sourceBetweenRegionEdges : Set G.edgeSet) ∧
      C' = C.swapOnKempeComponent a b K

/-- The framed residue absent from the cycle-only v23 relation: a legal
component switch whose selected component is not circuit-shaped.  In the
source geometry these are intended to be the paths ending at the two defects;
that endpoint identification is not built into this definition. -/
def NoncircuitFramedKempeStep
    (data : FramedTrailData G)
    (C C' : G.EdgeColoring Color) : Prop :=
  ∃ a b : Color,
    ∃ K : (C.bicoloredSubgraph a b).ConnectedComponent,
      ValidColorPair a b ∧
      ¬IsCircuitKempeComponent C a b K ∧
      Disjoint (C.kempeComponentSet a b K)
        (data.frozenInterfaceEdges : Set G.edgeSet) ∧
      C' = C.swapOnKempeComponent a b K

/-- Every source-side circuit move is a legal framed move.  This direction
uses only well-formedness: all three named parts of the annulus are movable. -/
theorem kauffmanBetweenRegionKempeStep_imp_framedTangleLegalKempeStep
    {data : FramedTrailData G} (hdata : data.WellFormed)
    {C C' : G.EdgeColoring Color}
    (hstep : KauffmanBetweenRegionKempeStep data C C') :
    FramedTangleLegalKempeStep data C C' := by
  rcases hstep with ⟨a, b, K, hab, _hcircuit, hsource, rfl⟩
  apply (movableSupportKempeStep_iff_framedTangleLegalKempeStep
    data C _).1
  exact ⟨a, b, K, hab,
    hsource.trans (data.sourceBetweenRegionEdges_subset_movableEdges hdata),
    rfl⟩

omit [Fintype V] [DecidableEq V] [Fintype G.edgeSet]
  [DecidableEq G.edgeSet] in
/-- Every noncircuit framed move is, by construction, a legal framed move. -/
theorem noncircuitFramedKempeStep_imp_framedTangleLegalKempeStep
    {data : FramedTrailData G} {C C' : G.EdgeColoring Color}
    (hstep : NoncircuitFramedKempeStep data C C') :
    FramedTangleLegalKempeStep data C C' := by
  rcases hstep with ⟨a, b, K, hab, _hnoncircuit, hfrozen, rfl⟩
  exact ⟨a, b, K, hab, hfrozen, rfl⟩

/-- First formation/frame alignment theorem for L10.  Once the source annulus
is certified to cover exactly the movable framed edges, the repaired framed
relation is the disjoint logical split between the v23 circuit relation and
the noncircuit residue.  A later geometric theorem must identify that residue
with the defect-ending source operation before any equality version of L10 can
be considered closed. -/
theorem framedTangleLegalKempeStep_iff_kauffman_or_noncircuit
    {data : FramedTrailData G} (hdata : data.WellFormed)
    (haligned : data.BetweenRegionEdgeAligned)
    (C C' : G.EdgeColoring Color) :
    FramedTangleLegalKempeStep data C C' ↔
      KauffmanBetweenRegionKempeStep data C C' ∨
        NoncircuitFramedKempeStep data C C' := by
  constructor
  · rintro ⟨a, b, K, hab, hfrozen, rfl⟩
    by_cases hcircuit : IsCircuitKempeComponent C a b K
    · left
      refine ⟨a, b, K, hab, hcircuit, ?_, rfl⟩
      have hmovable :
          C.kempeComponentSet a b K ⊆
            (data.movableEdges : Set G.edgeSet) := by
        intro edge hedge
        have hnotFrozen : edge ∉ data.frozenInterfaceEdges := by
          intro hfrozenEdge
          exact (Set.disjoint_left.1 hfrozen) hedge (by simpa using hfrozenEdge)
        simp [FramedTrailData.movableEdges, hnotFrozen]
      rw [haligned]
      exact hmovable
    · right
      exact ⟨a, b, K, hab, hcircuit, hfrozen, rfl⟩
  · rintro (hsource | hpath)
    · exact kauffmanBetweenRegionKempeStep_imp_framedTangleLegalKempeStep
        hdata hsource
    · exact noncircuitFramedKempeStep_imp_framedTangleLegalKempeStep hpath

/-- Finite sequences using only the cycle-based v23 source relation. -/
def KauffmanBetweenRegionKempeReachable
    (data : FramedTrailData G) :
    G.EdgeColoring Color → G.EdgeColoring Color → Prop :=
  Relation.ReflTransGen (KauffmanBetweenRegionKempeStep data)

/-- The source relation augmented by precisely the noncircuit framed residue.
This is a bookkeeping relation for the repaired L10 seam, not a renaming of
the original v23 relation. -/
def RepairedBetweenRegionKempeStep
    (data : FramedTrailData G)
    (C C' : G.EdgeColoring Color) : Prop :=
  KauffmanBetweenRegionKempeStep data C C' ∨
    NoncircuitFramedKempeStep data C C'

/-- Finite sequences for the repaired source relation. -/
def RepairedBetweenRegionKempeReachable
    (data : FramedTrailData G) :
    G.EdgeColoring Color → G.EdgeColoring Color → Prop :=
  Relation.ReflTransGen (RepairedBetweenRegionKempeStep data)

/-- Cycle-only source reachability embeds into framed reachability.  This is
the safe direction of L10 and requires no claim about the defect paths. -/
theorem kauffmanBetweenRegionKempeReachable_imp_framedTangleKempeReachable
    {data : FramedTrailData G} (hdata : data.WellFormed)
    {C C' : G.EdgeColoring Color}
    (hreach : KauffmanBetweenRegionKempeReachable data C C') :
    FramedTangleKempeReachable data C C' := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head hstep _ ih =>
      exact .head
        (kauffmanBetweenRegionKempeStep_imp_framedTangleLegalKempeStep
          hdata hstep)
        ih

/-- The edge-aligned repaired source relation and the framed relation have
exactly the same finite reachability.  The qualification `repaired` matters:
the theorem does not equate the original cycle-only v23 reachability with the
framed reachability. -/
theorem repairedBetweenRegionKempeReachable_iff_framedTangleKempeReachable
    {data : FramedTrailData G} (hdata : data.WellFormed)
    (haligned : data.BetweenRegionEdgeAligned)
    (C C' : G.EdgeColoring Color) :
    RepairedBetweenRegionKempeReachable data C C' ↔
      FramedTangleKempeReachable data C C' := by
  have hstep :
      RepairedBetweenRegionKempeStep data =
        FramedTangleLegalKempeStep data := by
    funext source target
    exact propext
      (framedTangleLegalKempeStep_iff_kauffman_or_noncircuit
        hdata haligned source target).symm
  simp only [RepairedBetweenRegionKempeReachable,
    FramedTangleKempeReachable, hstep]

/-- Completion using only the cycle-based source moves from v23. -/
def KauffmanBetweenRegionCompletable
    (data : FramedTrailData G) (C : G.EdgeColoring Color) : Prop :=
  ∃ C' : G.EdgeColoring Color,
    KauffmanBetweenRegionKempeReachable data C C' ∧
      data.HasMatchingDefectColors C'

/-- Source-side cycle completion implies framed completion.  The converse is
exactly where noncircuit defect paths matter and is intentionally absent. -/
theorem kauffmanBetweenRegionCompletable_imp_framedTangleCompletable
    {data : FramedTrailData G} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color}
    (hcomplete : KauffmanBetweenRegionCompletable data C) :
    FramedTangleCompletable data C := by
  rcases hcomplete with ⟨C', hreach, hmatch⟩
  exact ⟨C',
    kauffmanBetweenRegionKempeReachable_imp_framedTangleKempeReachable
      hdata hreach,
    hmatch⟩

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
