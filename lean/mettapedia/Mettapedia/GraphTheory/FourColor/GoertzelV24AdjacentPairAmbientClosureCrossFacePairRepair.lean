import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairGenerator

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossFacePairRepairGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Let a cubic flow vanish on one distinguished incident edge and take a
nonzero value on one of the other two. The two arms then both have that
value. Adding any transfer which takes that value uniquely on the
distinguished edge leaves all three incident values nonzero. -/
theorem IsGraphFlow.add_incident_ne_zero_of_card_three_of_source_zero_of_other_value
    {base repair : G.edgeSet → Color} (hbase : IsGraphFlow G base)
    (vertex : V) (hcubic : (incidentEdgeFinset G vertex).card = 3)
    (source : G.edgeSet)
    (hsourceIncident : source ∈ incidentEdgeFinset G vertex)
    (value : Color) (hvalue : value ≠ 0)
    (hbaseSource : base source = 0)
    (hrepairSource : repair source = value)
    (hrepairUnique : ∀ edge ∈ incidentEdgeFinset G vertex,
      repair edge = value → edge = source)
    (hbaseWitness : ∃ edge ∈ incidentEdgeFinset G vertex,
      base edge = value) :
    ∀ edge ∈ incidentEdgeFinset G vertex,
      base edge + repair edge ≠ 0 := by
  rcases Finset.card_eq_three.mp hcubic with
    ⟨first, second, third, hfirstSecond, hfirstThird,
      hsecondThird, hset⟩
  have hfirstIncident : first ∈ incidentEdgeFinset G vertex := by
    rw [hset]
    simp
  have hsecondIncident : second ∈ incidentEdgeFinset G vertex := by
    rw [hset]
    simp
  have hthirdIncident : third ∈ incidentEdgeFinset G vertex := by
    rw [hset]
    simp
  have hlocal : base first + base second + base third = 0 := by
    have hvertex := hbase vertex
    unfold vertexKirchhoffSum at hvertex
    rw [hset] at hvertex
    simpa [hfirstSecond, hfirstThird, hsecondThird, add_assoc] using hvertex
  have hsourceCases : source = first ∨ source = second ∨ source = third := by
    rw [hset] at hsourceIncident
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hsourceIncident
  rcases hbaseWitness with ⟨witness, hwitnessIncident, hwitnessValue⟩
  have hwitnessCases :
      witness = first ∨ witness = second ∨ witness = third := by
    rw [hset] at hwitnessIncident
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      hwitnessIncident
  rcases hsourceCases with hsource | hsource | hsource
  · subst source
    have harms : base second = value ∧ base third = value := by
      rcases hwitnessCases with hwitness | hwitness | hwitness
      · subst witness
        exact False.elim (hvalue (hwitnessValue.symm.trans hbaseSource))
      · subst witness
        refine ⟨hwitnessValue, ?_⟩
        have hsum : value + base third = 0 := by
          simpa [hbaseSource, hwitnessValue, add_assoc] using hlocal
        exact ((add_eq_zero_iff_eq value (base third)).1 hsum).symm
      · subst witness
        refine ⟨?_, hwitnessValue⟩
        have hsum : base second + value = 0 := by
          simpa [hbaseSource, hwitnessValue, add_assoc] using hlocal
        exact (add_eq_zero_iff_eq (base second) value).1 hsum
    have hfirstNonzero : base first + repair first ≠ 0 := by
      rw [hbaseSource, hrepairSource, zero_add]
      exact hvalue
    have hsecondNonzero : base second + repair second ≠ 0 := by
      rw [harms.1]
      apply add_ne_zero_of_ne
      intro heq
      exact hfirstSecond
        (hrepairUnique second hsecondIncident heq.symm).symm
    have hthirdNonzero : base third + repair third ≠ 0 := by
      rw [harms.2]
      apply add_ne_zero_of_ne
      intro heq
      exact hfirstThird
        (hrepairUnique third hthirdIncident heq.symm).symm
    intro edge hedge
    rw [hset] at hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl | rfl
    · exact hfirstNonzero
    · exact hsecondNonzero
    · exact hthirdNonzero
  · subst source
    have harms : base first = value ∧ base third = value := by
      rcases hwitnessCases with hwitness | hwitness | hwitness
      · subst witness
        refine ⟨hwitnessValue, ?_⟩
        have hsum : value + base third = 0 := by
          simpa [hbaseSource, hwitnessValue, add_assoc] using hlocal
        exact ((add_eq_zero_iff_eq value (base third)).1 hsum).symm
      · subst witness
        exact False.elim (hvalue (hwitnessValue.symm.trans hbaseSource))
      · subst witness
        refine ⟨?_, hwitnessValue⟩
        have hsum : base first + value = 0 := by
          simpa [hbaseSource, hwitnessValue, add_assoc] using hlocal
        exact (add_eq_zero_iff_eq (base first) value).1 hsum
    have hfirstNonzero : base first + repair first ≠ 0 := by
      rw [harms.1]
      apply add_ne_zero_of_ne
      intro heq
      exact hfirstSecond
        (hrepairUnique first hfirstIncident heq.symm)
    have hsecondNonzero : base second + repair second ≠ 0 := by
      rw [hbaseSource, hrepairSource, zero_add]
      exact hvalue
    have hthirdNonzero : base third + repair third ≠ 0 := by
      rw [harms.2]
      apply add_ne_zero_of_ne
      intro heq
      exact hsecondThird
        (hrepairUnique third hthirdIncident heq.symm).symm
    intro edge hedge
    rw [hset] at hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl | rfl
    · exact hfirstNonzero
    · exact hsecondNonzero
    · exact hthirdNonzero
  · subst source
    have harms : base first = value ∧ base second = value := by
      rcases hwitnessCases with hwitness | hwitness | hwitness
      · subst witness
        refine ⟨hwitnessValue, ?_⟩
        have hsum : value + base second = 0 := by
          simpa [hbaseSource, hwitnessValue, add_assoc] using hlocal
        exact ((add_eq_zero_iff_eq value (base second)).1 hsum).symm
      · subst witness
        refine ⟨?_, hwitnessValue⟩
        have hsum : base first + value = 0 := by
          simpa [hbaseSource, hwitnessValue, add_assoc] using hlocal
        exact (add_eq_zero_iff_eq (base first) value).1 hsum
      · subst witness
        exact False.elim (hvalue (hwitnessValue.symm.trans hbaseSource))
    have hfirstNonzero : base first + repair first ≠ 0 := by
      rw [harms.1]
      apply add_ne_zero_of_ne
      intro heq
      exact hfirstThird
        (hrepairUnique first hfirstIncident heq.symm)
    have hsecondNonzero : base second + repair second ≠ 0 := by
      rw [harms.2]
      apply add_ne_zero_of_ne
      intro heq
      exact hsecondThird
        (hrepairUnique second hsecondIncident heq.symm)
    have hthirdNonzero : base third + repair third ≠ 0 := by
      rw [hbaseSource, hrepairSource, zero_add]
      exact hvalue
    intro edge hedge
    rw [hset] at hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl | rfl
    · exact hfirstNonzero
    · exact hsecondNonzero
    · exact hthirdNonzero

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- Add the independently weighted two-face transfer through the retained
cross to the exact two-closure perturbation. -/
def CrossCentralExactFaceCutPair.oneZeroCrossFacePairPerturbation
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color) (edge : G.edgeSet) : Color :=
  pair.oneZeroClosureBasisPerturbation C first second edge +
    edgeTwoFaceColorTransfer graphData
      (retainedEdgeToAmbientEdge data cross) first second edge

@[simp]
theorem CrossCentralExactFaceCutPair.oneZeroCrossFacePairPerturbation_apply
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color) (edge : G.edgeSet) :
    pair.oneZeroCrossFacePairPerturbation C first second edge =
      pair.oneZeroClosureBasisPerturbation C first second edge +
        edgeTwoFaceColorTransfer graphData
          (retainedEdgeToAmbientEdge data cross) first second edge :=
  rfl

/-- The cross-face pair repair preserves Kirchhoff's law. -/
theorem CrossCentralExactFaceCutPair.oneZeroCrossFacePairPerturbation_isGraphFlow
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3)
    (first second : Color) :
    IsGraphFlow G
      (pair.oneZeroCrossFacePairPerturbation C first second) := by
  exact
    (pair.oneZeroClosureBasisPerturbation_isGraphFlow
      minimal C hC hsame first second).add
    (edgeTwoFaceColorTransfer_isGraphFlow graphData minimal
      (retainedEdgeToAmbientEdge data cross) first second)

/-- When the retained cross has the coefficient-sum color, the paired
facial repair changes its zero into that nonzero sum. -/
theorem CrossCentralExactFaceCutPair.oneZeroCrossFacePairPerturbation_retainedCross
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color) (hcross : C cross = first + second) :
    pair.oneZeroCrossFacePairPerturbation C first second
        (retainedEdgeToAmbientEdge data cross) = first + second := by
  rw [pair.oneZeroCrossFacePairPerturbation_apply,
    pair.oneZeroClosureBasisPerturbation_retainedCross
      minimal C first second hcross,
    edgeTwoFaceColorTransfer_source graphData minimal, zero_add]

/-- Distinct nonzero coefficients keep the restored central edge nonzero:
the paired transfer can take their sum only on the retained cross. -/
theorem CrossCentralExactFaceCutPair.oneZeroCrossFacePairPerturbation_centralEdge_ne_zero
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color) (hfirst : first ≠ 0) (hsecond : second ≠ 0)
    (hdistinct : first ≠ second) :
    pair.oneZeroCrossFacePairPerturbation C first second
        (centralEdge data) ≠ 0 := by
  rw [pair.oneZeroCrossFacePairPerturbation_apply,
    pair.oneZeroClosureBasisPerturbation_centralEdge minimal]
  apply add_ne_zero_of_ne
  intro heq
  have hcentralCross : centralEdge data =
      retainedEdgeToAmbientEdge data cross :=
    (edgeTwoFaceColorTransfer_eq_add_iff graphData minimal
      (retainedEdgeToAmbientEdge data cross) (centralEdge data)
      hfirst hsecond hdistinct).1 heq.symm
  exact (retainedEdgeToAmbientEdge_ne_centralEdge data cross)
    hcentralCross.symm

/-- A locally all-zero endpoint of the exact closure flow is completely
repaired by the paired cross-side facial transfer. -/
theorem CrossCentralExactFaceCutPair.oneZeroCrossFacePairPerturbation_incident_ne_zero_of_bad
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (first second : Color) (hfirst : first ≠ 0) (hsecond : second ≠ 0)
    (hdistinct : first ≠ second) (vertex : V)
    (hvertex : vertex ∈ ((retainedEdgeToAmbientEdge data cross).1 : Sym2 V))
    (hbad : ¬ IsCDLGoodAtVertex G
      (pair.oneZeroClosureBasisPerturbation C first second) vertex) :
    ∀ edge ∈ incidentEdgeFinset G vertex,
      pair.oneZeroCrossFacePairPerturbation C first second edge ≠ 0 := by
  have hbaseZero : ∀ edge ∈ incidentEdgeFinset G vertex,
      pair.oneZeroClosureBasisPerturbation C first second edge = 0 := by
    intro edge hedge
    by_contra hnonzero
    exact hbad ⟨edge, hedge, hnonzero⟩
  have hrepair := edgeTwoFaceColorTransfer_incident_ne_zero
    graphData minimal (retainedEdgeToAmbientEdge data cross)
      hfirst hsecond hdistinct vertex hvertex
  intro edge hedge
  rw [pair.oneZeroCrossFacePairPerturbation_apply,
    hbaseZero edge hedge, zero_add]
  exact hrepair edge hedge

/-- At the other endpoint, a coefficient-sum witness in the exact closure
flow combines with the paired facial transfer without creating a zero. -/
theorem CrossCentralExactFaceCutPair.oneZeroCrossFacePairPerturbation_incident_ne_zero_of_sum_witness
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3)
    (first second : Color) (hfirst : first ≠ 0) (hsecond : second ≠ 0)
    (hdistinct : first ≠ second) (hcross : C cross = first + second)
    (vertex : V)
    (hvertex : vertex ∈ ((retainedEdgeToAmbientEdge data cross).1 : Sym2 V))
    (hwitness : ∃ edge ∈ incidentEdgeFinset G vertex,
      pair.oneZeroClosureBasisPerturbation C first second edge =
        first + second) :
    ∀ edge ∈ incidentEdgeFinset G vertex,
      pair.oneZeroCrossFacePairPerturbation C first second edge ≠ 0 := by
  have hsourceIncident : retainedEdgeToAmbientEdge data cross ∈
      incidentEdgeFinset G vertex := by
    simpa [incidentEdgeFinset] using hvertex
  apply
    (pair.oneZeroClosureBasisPerturbation_isGraphFlow
      minimal C hC hsame first second)
      |>.add_incident_ne_zero_of_card_three_of_source_zero_of_other_value
        vertex
        (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
          graphData minimal.spherical.cubic vertex)
        (retainedEdgeToAmbientEdge data cross) hsourceIncident
        (first + second) (add_ne_zero_of_ne hdistinct)
  · exact pair.oneZeroClosureBasisPerturbation_retainedCross
      minimal C first second hcross
  · exact edgeTwoFaceColorTransfer_source graphData minimal
      (retainedEdgeToAmbientEdge data cross) first second
  · intro edge _hedge hvalue
    exact (edgeTwoFaceColorTransfer_eq_add_iff graphData minimal
      (retainedEdgeToAmbientEdge data cross) edge
      hfirst hsecond hdistinct).1 hvalue
  · exact hwitness

/-- The first strict exit arm of a cross carries the coefficient sum in
the exact closure perturbation. This is the witness needed by the paired
facial repair at the exit endpoint. -/
theorem CrossCentralExactFaceCutPair.crossExit_sum_witness
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a firstColor secondColor : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a firstColor firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a secondColor secondLeft secondRight)
    (haFirst : a ≠ firstColor) (haSecond : a ≠ secondColor)
    (hcolors : firstColor ≠ secondColor)
    (site : first.CrossSite second)
    (hunique : ∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet,
      edge ∈ first.ambientPath.support →
      edge ∈ second.ambientPath.support → edge = site.1)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (first.crossSplice second site).support.map Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (first.crossSuffixSplice second site).support.map Subtype.val) :
    ∃ edge ∈ incidentEdgeFinset G
        (first.firstCrossExitDart second haFirst hcolors site).fst.1,
      pair.oneZeroClosureBasisPerturbation C firstColor secondColor edge =
        firstColor + secondColor := by
  let firstExitEdge :=
    (first.firstSuffixFromCrossSite second site).getVert 1
  let exit := (first.firstCrossExitDart second haFirst hcolors site).fst
  have hfirstExitColor : C firstExitEdge = firstColor := by
    simpa only [firstExitEdge] using
      first.firstCrossExitEdge_color second haFirst hcolors site
  have htransfers := pair.edgeTransferInBasis_crossExitEdges minimal
    first second haFirst haSecond hcolors site hunique hprefixEdges
      hsuffixEdges
  have hfirstTransfer : pair.edgeTransferInBasis firstColor secondColor
      (retainedEdgeToAmbientEdge data firstExitEdge) = secondColor := by
    simpa only [firstExitEdge] using htransfers.1
  have hfirstExitBaseRetained : exit ∈
      (firstExitEdge.1 : Sym2 _) := by
    change
      (first.firstSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨0, first.firstSuffixFromCrossSite_length_pos
            second haFirst hcolors site⟩ ∈
        (((first.firstSuffixFromCrossSite second site).getVert 1).1 :
          Sym2 _)
    have hmem :=
      (first.firstSuffixFromCrossSite second site)
        |>.lineGraphJunctionAt_mem_right
          ⟨0, first.firstSuffixFromCrossSite_length_pos
            second haFirst hcolors site⟩
    simpa only [Nat.zero_add] using hmem
  have hfirstExitAmbient : exit.1 ∈
      ((retainedEdgeToAmbientEdge data firstExitEdge).1 : Sym2 V) := by
    rw [retainedEdgeToAmbientEdge_val]
    exact Sym2.mem_map.mpr ⟨exit, hfirstExitBaseRetained, rfl⟩
  have hfirstExitIncident : retainedEdgeToAmbientEdge data firstExitEdge ∈
      incidentEdgeFinset G exit.1 := by
    simpa [incidentEdgeFinset] using hfirstExitAmbient
  refine ⟨retainedEdgeToAmbientEdge data firstExitEdge,
    hfirstExitIncident, ?_⟩
  rw [pair.oneZeroClosureBasisPerturbation_apply,
    oneZeroAmbientChain_retainedEdgeToAmbientEdge,
    hfirstExitColor, hfirstTransfer]

/-- If the paired repair is nonzero on both endpoint stars and on the
restored central edge, noncolorability forces a zero strictly outside that
entire local configuration. -/
theorem CrossCentralExactFaceCutPair.exists_zero_off_repaired_cross
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3)
    (first second : Color) (entry exit : V)
    (hentry : ∀ edge ∈ incidentEdgeFinset G entry,
      pair.oneZeroCrossFacePairPerturbation C first second edge ≠ 0)
    (hexit : ∀ edge ∈ incidentEdgeFinset G exit,
      pair.oneZeroCrossFacePairPerturbation C first second edge ≠ 0)
    (hcentral : pair.oneZeroCrossFacePairPerturbation C first second
      (centralEdge data) ≠ 0) :
    ∃ edge : G.edgeSet,
      pair.oneZeroCrossFacePairPerturbation C first second edge = 0 ∧
        edge ∉ incidentEdgeFinset G entry ∧
        edge ∉ incidentEdgeFinset G exit ∧
        edge ≠ centralEdge data := by
  let chain := pair.oneZeroCrossFacePairPerturbation C first second
  have hflow : IsGraphFlow G chain :=
    pair.oneZeroCrossFacePairPerturbation_isGraphFlow
      minimal C hC hsame first second
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hexistsZero : ∃ edge : G.edgeSet, chain edge = 0 := by
    by_contra hnone
    push Not at hnone
    have hnowhere : IsNowhereZeroFlow G chain := ⟨hflow, hnone⟩
    exact
      (graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
        graphData minimal)
        (exists_taitEdgeColoring_of_nowhereZeroFlow_of_hasCubicIncidentEdgeTriples
          (hasCubicIncidentEdgeTriples_of_incidentEdgeFinset_card_eq_three
            hcubic)
          chain hnowhere)
  rcases hexistsZero with ⟨edge, hedge⟩
  refine ⟨edge, hedge, ?_, ?_, ?_⟩
  · intro hmem
    exact hentry edge hmem hedge
  · intro hmem
    exact hexit edge hmem hedge
  · intro heq
    subst edge
    exact hcentral hedge

/-- The paired cross-side transfer repairs the complete rejected local
state: every edge at both cross endpoints is nonzero, and the restored
central edge remains nonzero. -/
theorem CrossCentralExactFaceCutPair.reversedCross_crossFacePair_repaired
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a firstColor secondColor : Color}
    {firstLeft firstRight secondLeft secondRight : Fin 4}
    (first : data.degreeTwoBoundaryData.EvenKempePortPath
      C a firstColor firstLeft firstRight)
    (second : data.degreeTwoBoundaryData.EvenKempePortPath
      C a secondColor secondLeft secondRight)
    (haFirst : a ≠ firstColor) (haSecond : a ≠ secondColor)
    (hcolors : firstColor ≠ secondColor)
    (site : first.CrossSite second)
    (hunique : ∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet,
      edge ∈ first.ambientPath.support →
      edge ∈ second.ambientPath.support → edge = site.1)
    (hpairing : first.crossPairingBit second haFirst haSecond hcolors site =
      false)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (first.crossSplice second site).support.map Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (first.crossSuffixSplice second site).support.map Subtype.val)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3)
    (hsum : a = firstColor + secondColor) :
    (∀ edge ∈ incidentEdgeFinset G
        (first.firstCrossEntryVertex second haFirst hcolors site).1,
      pair.oneZeroCrossFacePairPerturbation C
        firstColor secondColor edge ≠ 0) ∧
      (∀ edge ∈ incidentEdgeFinset G
          (first.firstCrossExitDart second haFirst hcolors site).fst.1,
        pair.oneZeroCrossFacePairPerturbation C
          firstColor secondColor edge ≠ 0) ∧
      pair.oneZeroCrossFacePairPerturbation C firstColor secondColor
        (centralEdge data) ≠ 0 := by
  let entry := first.firstCrossEntryVertex second haFirst hcolors site
  let exit := (first.firstCrossExitDart second haFirst hcolors site).fst
  let firstExitEdge :=
    (first.firstSuffixFromCrossSite second site).getVert 1
  let secondExitEdge :=
    (first.secondSuffixFromCrossSite second site).getVert 1
  have hfirstExitColor : C firstExitEdge = firstColor := by
    simpa only [firstExitEdge] using
      first.firstCrossExitEdge_color second haFirst hcolors site
  have hsecondExitColor : C secondExitEdge = secondColor := by
    simpa only [secondExitEdge] using
      first.secondCrossExitEdge_color second haSecond hcolors site
  have hfirstNonzero : firstColor ≠ 0 := by
    rw [← hfirstExitColor]
    exact hC firstExitEdge
  have hsecondNonzero : secondColor ≠ 0 := by
    rw [← hsecondExitColor]
    exact hC secondExitEdge
  have hsiteColor : C site.1 = a :=
    first.color_eq_first_of_crossSite second hcolors site
  have hcross : C site.1 = firstColor + secondColor :=
    hsiteColor.trans hsum
  have hentryRetained : entry ∈ (site.1.1 : Sym2 _) := by
    simpa only [entry] using
      first.firstCrossEntryVertex_mem_site second haFirst hcolors site
  have hentryAmbient : entry.1 ∈
      ((retainedEdgeToAmbientEdge data site.1).1 : Sym2 V) := by
    rw [retainedEdgeToAmbientEdge_val]
    exact Sym2.mem_map.mpr ⟨entry, hentryRetained, rfl⟩
  have hexitRetained : exit ∈ (site.1.1 : Sym2 _) := by
    simpa only [exit] using
      first.firstCrossExitDart_fst_mem_site second haFirst hcolors site
  have hexitAmbient : exit.1 ∈
      ((retainedEdgeToAmbientEdge data site.1).1 : Sym2 V) := by
    rw [retainedEdgeToAmbientEdge_val]
    exact Sym2.mem_map.mpr ⟨exit, hexitRetained, rfl⟩
  have hlocal := pair.reversedCross_entry_bad_exit_good minimal
    first second haFirst haSecond hcolors site hunique hpairing
      hprefixEdges hsuffixEdges hC hsame hsum
  have hwitness := pair.crossExit_sum_witness minimal
    first second haFirst haSecond hcolors site hunique
      hprefixEdges hsuffixEdges
  refine ⟨?_, ?_, pair.oneZeroCrossFacePairPerturbation_centralEdge_ne_zero
    minimal C firstColor secondColor hfirstNonzero hsecondNonzero hcolors⟩
  · exact pair.oneZeroCrossFacePairPerturbation_incident_ne_zero_of_bad
      minimal C firstColor secondColor hfirstNonzero hsecondNonzero hcolors
        entry.1 hentryAmbient hlocal.1
  · exact
      pair.oneZeroCrossFacePairPerturbation_incident_ne_zero_of_sum_witness
        minimal C hC hsame firstColor secondColor hfirstNonzero
          hsecondNonzero hcolors hcross exit.1 hexitAmbient hwitness

/-- The rejected singleton `bc` cross is repaired on both endpoint stars
and on the restored central edge by its two cross-side facial generators. -/
theorem EvenKempeFusionLens.bcCrossExactPair_crossFacePair_repaired
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (lens01.bRoute.crossSplice lens23.cRoute site).support.map
        Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (lens01.bRoute.crossSuffixSplice lens23.cRoute site).support.map
        Subtype.val)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3) :
    (∀ edge ∈ incidentEdgeFinset G
        (lens01.bRoute.firstCrossEntryVertex lens23.cRoute
          hab hbc site).1,
      pair.oneZeroCrossFacePairPerturbation C b c edge ≠ 0) ∧
      (∀ edge ∈ incidentEdgeFinset G
          (lens01.bRoute.firstCrossExitDart lens23.cRoute
            hab hbc site).fst.1,
        pair.oneZeroCrossFacePairPerturbation C b c edge ≠ 0) ∧
      pair.oneZeroCrossFacePairPerturbation C b c
        (centralEdge data) ≠ 0 := by
  have hunique : ∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet,
      edge ∈ lens01.bRoute.ambientPath.support →
      edge ∈ lens23.cRoute.ambientPath.support → edge = site.1 := by
    intro edge hfirst hsecond
    exact lens01.bcCrossSite_eq_of_length_le_one lens23 hcount site edge
      hfirst hsecond
  have hpairing : lens01.bRoute.crossPairingBit lens23.cRoute
      hab hac hbc site = false :=
    (crossExitFaceTransferBit_eq_false_iff_pairing_false_and_turns_eq
      data graphData lens01.bRoute lens23.cRoute hab hac hbc site).1
      (by
        simpa only [EvenKempeFusionLens.bcCrossExitFaceTransferBit] using
          hfalse) |>.1
  have ha : a ≠ 0 := by
    rw [← lens01.bRoute.color_eq_first_of_crossSite
      lens23.cRoute hbc site]
    exact hC site.1
  have hb : b ≠ 0 := by
    rw [← lens01.bRoute.firstCrossExitEdge_color
      lens23.cRoute hab hbc site]
    exact hC ((lens01.bRoute.firstSuffixFromCrossSite
      lens23.cRoute site).getVert 1)
  have hc : c ≠ 0 := by
    rw [← lens01.bRoute.secondCrossExitEdge_color
      lens23.cRoute hac hbc site]
    exact hC ((lens01.bRoute.secondSuffixFromCrossSite
      lens23.cRoute site).getVert 1)
  have hsum : a = b + c :=
    color_eq_add_of_three_distinct_nonzero ha hb hc hab hac hbc
  exact pair.reversedCross_crossFacePair_repaired minimal
    lens01.bRoute lens23.cRoute hab hac hbc site hunique hpairing
      hprefixEdges hsuffixEdges hC hsame hsum

/-- The symmetric rejected singleton `cb` cross has the same complete
paired-face repair, with the two route colors exchanged. -/
theorem EvenKempeFusionLens.cbCrossExactPair_crossFacePair_repaired
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (lens01.cRoute.crossSplice lens23.bRoute site).support.map
        Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (lens01.cRoute.crossSuffixSplice lens23.bRoute site).support.map
        Subtype.val)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3) :
    (∀ edge ∈ incidentEdgeFinset G
        (lens01.cRoute.firstCrossEntryVertex lens23.bRoute
          hac hbc.symm site).1,
      pair.oneZeroCrossFacePairPerturbation C c b edge ≠ 0) ∧
      (∀ edge ∈ incidentEdgeFinset G
          (lens01.cRoute.firstCrossExitDart lens23.bRoute
            hac hbc.symm site).fst.1,
        pair.oneZeroCrossFacePairPerturbation C c b edge ≠ 0) ∧
      pair.oneZeroCrossFacePairPerturbation C c b
        (centralEdge data) ≠ 0 := by
  have hunique : ∀ edge : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet,
      edge ∈ lens01.cRoute.ambientPath.support →
      edge ∈ lens23.bRoute.ambientPath.support → edge = site.1 := by
    intro edge hfirst hsecond
    exact lens01.cbCrossSite_eq_of_length_le_one lens23 hcount site edge
      hfirst hsecond
  have hpairing : lens01.cRoute.crossPairingBit lens23.bRoute
      hac hab hbc.symm site = false :=
    (crossExitFaceTransferBit_eq_false_iff_pairing_false_and_turns_eq
      data graphData lens01.cRoute lens23.bRoute hac hab hbc.symm site).1
      (by
        simpa only [EvenKempeFusionLens.cbCrossExitFaceTransferBit] using
          hfalse) |>.1
  have ha : a ≠ 0 := by
    rw [← lens01.cRoute.color_eq_first_of_crossSite
      lens23.bRoute hbc.symm site]
    exact hC site.1
  have hc : c ≠ 0 := by
    rw [← lens01.cRoute.firstCrossExitEdge_color
      lens23.bRoute hac hbc.symm site]
    exact hC ((lens01.cRoute.firstSuffixFromCrossSite
      lens23.bRoute site).getVert 1)
  have hb : b ≠ 0 := by
    rw [← lens01.cRoute.secondCrossExitEdge_color
      lens23.bRoute hab hbc.symm site]
    exact hC ((lens01.cRoute.secondSuffixFromCrossSite
      lens23.bRoute site).getVert 1)
  have hsum : a = c + b :=
    color_eq_add_of_three_distinct_nonzero ha hc hb hac hab hbc.symm
  exact pair.reversedCross_crossFacePair_repaired minimal
    lens01.cRoute lens23.bRoute hac hab hbc.symm site hunique hpairing
      hprefixEdges hsuffixEdges hC hsame hsum

/-- Noncolorability forces every residual zero for the repaired rejected
`bc` cross away from both cross endpoints and the restored central edge. -/
theorem EvenKempeFusionLens.bcCrossExactPair_exists_zero_off_repaired_cross
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (lens01.bRoute.crossSplice lens23.cRoute site).support.map
        Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (lens01.bRoute.crossSuffixSplice lens23.cRoute site).support.map
        Subtype.val)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3) :
    ∃ edge : G.edgeSet,
      pair.oneZeroCrossFacePairPerturbation C b c edge = 0 ∧
        edge ∉ incidentEdgeFinset G
          (lens01.bRoute.firstCrossEntryVertex lens23.cRoute
            hab hbc site).1 ∧
        edge ∉ incidentEdgeFinset G
          (lens01.bRoute.firstCrossExitDart lens23.cRoute
            hab hbc site).fst.1 ∧
        edge ≠ centralEdge data := by
  have hrepair := EvenKempeFusionLens.bcCrossExactPair_crossFacePair_repaired
    graphData minimal data lens01 lens23 hab hac hbc hcount site hfalse pair
      hprefixEdges hsuffixEdges hC hsame
  exact pair.exists_zero_off_repaired_cross minimal C hC hsame b c
    (lens01.bRoute.firstCrossEntryVertex lens23.cRoute hab hbc site).1
    (lens01.bRoute.firstCrossExitDart lens23.cRoute
      hab hbc site).fst.1
    hrepair.1 hrepair.2.1 hrepair.2.2

/-- The symmetric repaired `cb` cross likewise expels every residual zero
from its endpoint stars and the restored central edge. -/
theorem EvenKempeFusionLens.cbCrossExactPair_exists_zero_off_repaired_cross
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (lens01.cRoute.crossSplice lens23.bRoute site).support.map
        Subtype.val)
    (hsuffixEdges : pair.suffixTrail.edges =
      (lens01.cRoute.crossSuffixSplice lens23.bRoute site).support.map
        Subtype.val)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hsame :
      data.degreeTwoBoundaryData.colorWord C 0 =
          data.degreeTwoBoundaryData.colorWord C 1 ∧
        data.degreeTwoBoundaryData.colorWord C 2 =
          data.degreeTwoBoundaryData.colorWord C 3) :
    ∃ edge : G.edgeSet,
      pair.oneZeroCrossFacePairPerturbation C c b edge = 0 ∧
        edge ∉ incidentEdgeFinset G
          (lens01.cRoute.firstCrossEntryVertex lens23.bRoute
            hac hbc.symm site).1 ∧
        edge ∉ incidentEdgeFinset G
          (lens01.cRoute.firstCrossExitDart lens23.bRoute
            hac hbc.symm site).fst.1 ∧
        edge ≠ centralEdge data := by
  have hrepair := EvenKempeFusionLens.cbCrossExactPair_crossFacePair_repaired
    graphData minimal data lens01 lens23 hab hac hbc hcount site hfalse pair
      hprefixEdges hsuffixEdges hC hsame
  exact pair.exists_zero_off_repaired_cross minimal C hC hsame c b
    (lens01.cRoute.firstCrossEntryVertex lens23.bRoute
      hac hbc.symm site).1
    (lens01.cRoute.firstCrossExitDart lens23.bRoute
      hac hbc.symm site).fst.1
    hrepair.1 hrepair.2.1 hrepair.2.2

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
