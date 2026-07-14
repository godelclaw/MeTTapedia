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

/-- A nonzero color can be placed on the missing trail edge at one defect
when it differs from every color already incident there. -/
def IsAdmissibleAtDefect (data : FramedTrailData G)
    (C : G.EdgeColoring Color) (i : Fin 2) (c : Color) : Prop :=
  c ≠ 0 ∧
    ∀ e ∈ incidentEdgeFinset G (data.defectVertex i), c ≠ C e

/-- A color extends the missing trail edge properly at both endpoints. -/
def IsProperTrailExtensionColor (data : FramedTrailData G)
    (C : G.EdgeColoring Color) (c : Color) : Prop :=
  data.IsAdmissibleAtDefect C 0 c ∧ data.IsAdmissibleAtDefect C 1 c

private theorem eq_add_of_three_distinct_nonzero {a b c : Color}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c = a + b := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl <;>
    simp at hab hac hbc ⊢

/-- At a well-formed degree-two defect of a Tait coloring, the incident-edge
sum is the unique nonzero color that can be assigned to the missing edge. -/
theorem missingColorAt_is_unique_admissible
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (i : Fin 2) :
    data.IsAdmissibleAtDefect C i (data.missingColorAt C i) ∧
      ∀ c : Color,
        data.IsAdmissibleAtDefect C i c -> c = data.missingColorAt C i := by
  rcases Finset.card_eq_two.mp (hdata.2.1 i) with ⟨e, f, hef, hincident⟩
  have heMem : e ∈ incidentEdgeFinset G (data.defectVertex i) := by
    rw [hincident]
    simp
  have hfMem : f ∈ incidentEdgeFinset G (data.defectVertex i) := by
    rw [hincident]
    simp
  have heAtDefect : data.defectVertex i ∈ (e : Sym2 V) := by
    simpa [incidentEdgeFinset] using heMem
  have hfAtDefect : data.defectVertex i ∈ (f : Sym2 V) := by
    simpa [incidentEdgeFinset] using hfMem
  have hcolors : C e ≠ C f :=
    C.valid (G.lineGraph_adj_of_edgeSet_common_vertex hef heAtDefect hfAtDefect)
  have hmissing : data.missingColorAt C i = C e + C f := by
    simp [missingColorAt, hincident, hef]
  have hthird := third_color_properties (hC e) (hC f) hcolors
  constructor
  · constructor
    · rw [hmissing]
      exact hthird.1
    · intro x hx
      rw [hincident] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [hmissing]
        exact hthird.2.1
      · rw [hmissing]
        exact hthird.2.2
  · intro c hc
    calc
      c = C e + C f := eq_add_of_three_distinct_nonzero
        (hC e) (hC f) hc.1 hcolors (Ne.symm (hc.2 e heMem))
          (Ne.symm (hc.2 f hfMem))
      _ = data.missingColorAt C i := hmissing.symm

/-- The computed equality of the two defect requests is exactly the existence
of one nonzero color that extends the missing trail edge properly at both
endpoints. -/
theorem hasMatchingDefectColors_iff_exists_properTrailExtensionColor
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    data.HasMatchingDefectColors C ↔
      ∃ c : Color, data.IsProperTrailExtensionColor C c := by
  have hunique0 := data.missingColorAt_is_unique_admissible hdata C hC 0
  have hunique1 := data.missingColorAt_is_unique_admissible hdata C hC 1
  constructor
  · intro hmatch
    refine ⟨data.missingColorAt C 0, hunique0.1, ?_⟩
    simpa [HasMatchingDefectColors] using hmatch ▸ hunique1.1
  · rintro ⟨c, hc0, hc1⟩
    rw [HasMatchingDefectColors]
    exact (hunique0.2 c hc0).symm.trans (hunique1.2 c hc1)

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

/-- Swapping a genuine component of two nonzero colors preserves the Tait
condition. -/
theorem isTaitEdgeColoring_swapOnKempeComponent
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    IsTaitEdgeColoring G (C.swapOnKempeComponent a b K) := by
  intro e
  by_cases he : e ∈ C.kempeComponentSet a b K
  · rw [C.swapOnKempeComponent_apply_of_mem he]
    rcases C.mem_bicoloredSet_of_mem_kempeComponentSet he with hcolor | hcolor
    · simpa [hcolor] using hab.2.1
    · simpa [hcolor] using hab.1
  · rw [C.swapOnKempeComponent_apply_of_not_mem he]
    exact hC e

/-- Every legal framed-tangle move preserves use of the three nonzero Tait
colors. -/
theorem framedTangleLegalKempeStep_preserves_isTaitEdgeColoring
    {data : FramedTrailData G} {C C' : G.EdgeColoring Color}
    (hstep : FramedTangleLegalKempeStep data C C')
    (hC : IsTaitEdgeColoring G C) :
    IsTaitEdgeColoring G C' := by
  rcases hstep with ⟨a, b, K, hab, _hdisjoint, rfl⟩
  exact isTaitEdgeColoring_swapOnKempeComponent hC hab K

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

/-- Tait colors remain nonzero through any finite sequence of legal framed
moves. -/
theorem framedTangleKempeReachable_preserves_isTaitEdgeColoring
    {data : FramedTrailData G} {C C' : G.EdgeColoring Color}
    (hreach : FramedTangleKempeReachable data C C')
    (hC : IsTaitEdgeColoring G C) :
    IsTaitEdgeColoring G C' := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => exact hC
  | head hstep _ ih =>
      exact ih (framedTangleLegalKempeStep_preserves_isTaitEdgeColoring hstep hC)

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

/-- The framed completion predicate has its direct graph meaning: after legal
moves, one nonzero color can be placed on the missing trail edge and is proper
at both defect endpoints. -/
theorem framedTangleCompletable_iff_exists_reachable_properTrailExtensionColor
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    FramedTangleCompletable data C ↔
      ∃ C' : G.EdgeColoring Color, ∃ c : Color,
        FramedTangleKempeReachable data C C' ∧
          data.IsProperTrailExtensionColor C' c := by
  constructor
  · rintro ⟨C', hreach, hmatch⟩
    have hC' :=
      framedTangleKempeReachable_preserves_isTaitEdgeColoring hreach hC
    rcases (data.hasMatchingDefectColors_iff_exists_properTrailExtensionColor
      hdata C' hC').1 hmatch with ⟨c, hc⟩
    exact ⟨C', c, hreach, hc⟩
  · rintro ⟨C', c, hreach, hc⟩
    have hC' :=
      framedTangleKempeReachable_preserves_isTaitEdgeColoring hreach hC
    exact ⟨C', hreach,
      (data.hasMatchingDefectColors_iff_exists_properTrailExtensionColor
        hdata C' hC').2 ⟨c, hc⟩⟩

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
