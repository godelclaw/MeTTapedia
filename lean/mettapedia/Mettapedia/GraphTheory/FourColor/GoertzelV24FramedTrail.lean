import Mettapedia.GraphTheory.EdgeColoring
import Mettapedia.GraphTheory.FourColor.GoertzelDefinition48
import Mettapedia.GraphTheory.FourColor.Theorem49TargetSubspace

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open SimpleGraph
open Relation
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [Fintype G.edgeSet] [DecidableEq G.edgeSet]

/-- Data of the container-inclusive framed tangle from v24 Addendum XXVIII.
The graph `G` is the framed tangle itself; the two container cycles remain in
`G`, while only the outward-crossing interface is frozen. Structural
well-formedness is stated separately as a computed predicate. -/
structure FramedTrailData (G : SimpleGraph V) where
  innerContainerEdges : Finset G.edgeSet
  outerContainerEdges : Finset G.edgeSet
  betweenRegionCoreEdges : Finset G.edgeSet
  frozenInterfaceEdges : Finset G.edgeSet
  defectVertex : Fin 2 -> V

namespace FramedTrailData

/-- All framed-tangle edges except the outward-crossing frozen interface.
In particular, container edges are movable when the data are well formed. -/
def movableEdges (data : FramedTrailData G) : Finset G.edgeSet :=
  Finset.univ \ data.frozenInterfaceEdges

/-- Computed structural conditions for a framed trail: distinct degree-two
defects, cubicity elsewhere, and inclusion of both containers and the region
core in the movable edge domain. -/
def WellFormed (data : FramedTrailData G) : Prop :=
  Function.Injective data.defectVertex ∧
  (∀ i : Fin 2,
    (incidentEdgeFinset G (data.defectVertex i)).card = 2) ∧
  (∀ v : V, (∀ i : Fin 2, v ≠ data.defectVertex i) ->
    (incidentEdgeFinset G v).card = 3) ∧
  data.innerContainerEdges ⊆ data.movableEdges ∧
  data.outerContainerEdges ⊆ data.movableEdges ∧
  data.betweenRegionCoreEdges ⊆ data.movableEdges

/-- The color missing at a defect vertex, expressed in the existing
`F2 x F2` bookkeeping as the sum of its two incident nonzero colors. -/
def missingColorAt (data : FramedTrailData G)
    (C : G.EdgeColoring Color) (i : Fin 2) : Color :=
  ∑ e ∈ incidentEdgeFinset G (data.defectVertex i), C e

/-- The graph coloring extends across the missing trail edge exactly when the
two degree-two defects request the same third color. -/
def HasMatchingDefectColors (data : FramedTrailData G)
    (C : G.EdgeColoring Color) : Prop :=
  data.missingColorAt C 0 = data.missingColorAt C 1

end FramedTrailData

/-- Kauffman-facing one-step definition: switch one genuine two-color
component whose entire support lies in the movable between-region, including
the two container cycles. -/
def KauffmanBetweenRegionKempeStep
    (data : FramedTrailData G)
    (C C' : G.EdgeColoring Color) : Prop :=
  ∃ a b : Color,
    ∃ K : (C.bicoloredSubgraph a b).ConnectedComponent,
      ValidColorPair a b ∧
      C.kempeComponentSet a b K ⊆ (data.movableEdges : Set G.edgeSet) ∧
      C' = C.swapOnKempeComponent a b K

/-- Framed-tangle one-step definition: switch one genuine two-color
component disjoint from the outward-crossing frozen interface. Components may
be paths terminating at defects; no circuit premise is inserted. -/
def FramedTangleLegalKempeStep
    (data : FramedTrailData G)
    (C C' : G.EdgeColoring Color) : Prop :=
  ∃ a b : Color,
    ∃ K : (C.bicoloredSubgraph a b).ConnectedComponent,
      ValidColorPair a b ∧
      Disjoint (C.kempeComponentSet a b K)
        (data.frozenInterfaceEdges : Set G.edgeSet) ∧
      C' = C.swapOnKempeComponent a b K

/-- L10, one-step move-definition alignment. Support in the complement of
the frozen interface is exactly disjointness from that interface. -/
theorem L10_kauffmanBetweenRegionKempeStep_iff_framedTangleLegalKempeStep
    (data : FramedTrailData G) (C C' : G.EdgeColoring Color) :
    KauffmanBetweenRegionKempeStep data C C' ↔
      FramedTangleLegalKempeStep data C C' := by
  constructor
  · rintro ⟨a, b, K, hab, hsupport, rfl⟩
    refine ⟨a, b, K, hab, ?_, rfl⟩
    rw [Set.disjoint_left]
    intro e heComponent heFrozen
    have heMovable := hsupport heComponent
    simpa [FramedTrailData.movableEdges, heFrozen] using heMovable
  · rintro ⟨a, b, K, hab, hdisjoint, rfl⟩
    refine ⟨a, b, K, hab, ?_, rfl⟩
    intro e heComponent
    have heNotFrozen : e ∉ data.frozenInterfaceEdges := by
      intro heFrozen
      exact (Set.disjoint_left.1 hdisjoint) heComponent (by simpa using heFrozen)
    simp [FramedTrailData.movableEdges, heNotFrozen]

/-- A legal framed step leaves every frozen interface edge unchanged. -/
theorem framedTangleLegalKempeStep_eq_on_frozenInterface
    {data : FramedTrailData G} {C C' : G.EdgeColoring Color}
    (hstep : FramedTangleLegalKempeStep data C C')
    {e : G.edgeSet} (heFrozen : e ∈ data.frozenInterfaceEdges) :
    C' e = C e := by
  rcases hstep with ⟨a, b, K, _hab, hdisjoint, rfl⟩
  apply Coloring.swapOnKempeComponent_apply_of_not_mem
  intro heComponent
  exact (Set.disjoint_left.1 hdisjoint) heComponent (by simpa using heFrozen)

/-- Finite sequences of Kauffman between-region moves. -/
def KauffmanBetweenRegionKempeReachable
    (data : FramedTrailData G) :
    G.EdgeColoring Color -> G.EdgeColoring Color -> Prop :=
  ReflTransGen (KauffmanBetweenRegionKempeStep data)

/-- Finite sequences of legal framed-tangle moves. -/
def FramedTangleKempeReachable
    (data : FramedTrailData G) :
    G.EdgeColoring Color -> G.EdgeColoring Color -> Prop :=
  ReflTransGen (FramedTangleLegalKempeStep data)

/-- L10 alignment is stable under arbitrary finite move sequences. -/
theorem L10_kauffmanBetweenRegionKempeReachable_iff_framedTangleKempeReachable
    (data : FramedTrailData G) (C C' : G.EdgeColoring Color) :
    KauffmanBetweenRegionKempeReachable data C C' ↔
      FramedTangleKempeReachable data C C' := by
  have hstep :
      KauffmanBetweenRegionKempeStep data =
        FramedTangleLegalKempeStep data := by
    funext source target
    exact propext
      (L10_kauffmanBetweenRegionKempeStep_iff_framedTangleLegalKempeStep
        data source target)
  simp only [KauffmanBetweenRegionKempeReachable,
    FramedTangleKempeReachable, hstep]

/-- Completion phrased with Kauffman's between-region move relation. -/
def KauffmanBetweenRegionCompletable
    (data : FramedTrailData G) (C : G.EdgeColoring Color) : Prop :=
  ∃ C' : G.EdgeColoring Color,
    KauffmanBetweenRegionKempeReachable data C C' ∧
      data.HasMatchingDefectColors C'

/-- Completion phrased with the frozen-interface framed-tangle relation. -/
def FramedTangleCompletable
    (data : FramedTrailData G) (C : G.EdgeColoring Color) : Prop :=
  ∃ C' : G.EdgeColoring Color,
    FramedTangleKempeReachable data C C' ∧
      data.HasMatchingDefectColors C'

/-- L10 alignment at the completion predicate consumed by Trail
Completability. -/
theorem L10_kauffmanBetweenRegionCompletable_iff_framedTangleCompletable
    (data : FramedTrailData G) (C : G.EdgeColoring Color) :
    KauffmanBetweenRegionCompletable data C ↔
      FramedTangleCompletable data C := by
  constructor
  · rintro ⟨C', hreach, hmatch⟩
    exact ⟨C',
      (L10_kauffmanBetweenRegionKempeReachable_iff_framedTangleKempeReachable
        data C C').1 hreach,
      hmatch⟩
  · rintro ⟨C', hreach, hmatch⟩
    exact ⟨C',
      (L10_kauffmanBetweenRegionKempeReachable_iff_framedTangleKempeReachable
        data C C').2 hreach,
      hmatch⟩

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
