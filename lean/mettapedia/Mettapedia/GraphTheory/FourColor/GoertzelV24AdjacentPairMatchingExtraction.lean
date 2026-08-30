import Mettapedia.Combinatorics.Matching.PermutationBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCommonConstantOrbit
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairInsertion
import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualOddness
import Mettapedia.GraphTheory.FourColor.GoertzelV24TaitMatchingDecomposition

/-!
# Perfect matchings extracted from adjacent-pair deletion colourings

A colouring of the graph obtained by deleting two adjacent vertices need not
extend to a Tait colouring of the ambient graph.  Nevertheless, in the exact
same-side obstruction sector forced by ambient non-colourability, one of its
three colour classes does extend to an ambient perfect matching: choose a
colour absent from all four boundary requests and match the two deleted
vertices by their common edge.

This is the local-to-global connector between the adjacent-pair Kempe states
and the residual-perfect-matching descent.  It uses no planar configuration
enumeration.  The only finite calculation is the uniform four-element colour
algebra which says that a nonzero colour distinct from the missing third
colour occurs on one of the two incident edges.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AdjacentPairMatchingExtraction

open SimpleGraph
open MatchingParity
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24ResidualDefectDescent
open GoertzelV24TaitMatchingDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

local instance adjacentPairMatchingRetainedFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

/-- Among the three nonzero colours, any colour other than the missing sum of
two distinct nonzero colours occurs on one of the two edges. -/
theorem eq_left_or_eq_right_of_ne_missingColor :
    ∀ left right wanted : Color,
      left ≠ 0 → right ≠ 0 → left ≠ right → wanted ≠ 0 →
      left + right ≠ wanted → wanted = left ∨ wanted = right := by
  intro left right wanted hleft hright _hne hwanted hmissing
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero left hleft with
    rfl | rfl | rfl <;>
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero right hright with
    rfl | rfl | rfl <;>
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero wanted hwanted with
    rfl | rfl | rfl <;>
  simp_all

/-- If one Tait colour is absent from every request of a well-formed
degree-two boundary, that colour class is a perfect matching of the whole
open graph.  At an interior cubic vertex this is the usual colour-class
argument.  At a degree-two port the absent request says that the selected
colour is one of the two colours already incident there. -/
theorem colorClassSubgraph_isPerfectMatching_of_boundary_absent
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (i : Fin 3)
    (habsent : ∀ port, data.colorWord C port ≠ taitColor i) :
    (colorClassSubgraph C (taitColor i)).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro vertex
  have uniqueFor (edge : G.edgeSet)
      (hedge : edge ∈ incidentEdgeFinset G vertex)
      (hcolour : C edge = taitColor i) :
      ∃! other, (colorClassSubgraph C (taitColor i)).Adj vertex other := by
    have hvertex : vertex ∈ (edge.1 : Sym2 V) := by
      simpa [incidentEdgeFinset] using hedge
    rcases Sym2.mem_iff_exists.mp hvertex with ⟨other, hedgeValue⟩
    have hadj : G.Adj vertex other := by
      rw [← SimpleGraph.mem_edgeSet, ← hedgeValue]
      exact edge.property
    have hedgeEq : (⟨s(vertex, other), hadj⟩ : G.edgeSet) = edge :=
      Subtype.ext hedgeValue.symm
    have hcolour' : C (⟨s(vertex, other), hadj⟩ : G.edgeSet) =
        taitColor i := by
      simpa [hedgeEq] using hcolour
    refine ⟨other, ⟨hadj, hcolour'⟩, ?_⟩
    intro other' hother'
    rcases hother' with ⟨hadj', hcolourOther⟩
    by_contra hne
    let edge' : G.edgeSet := ⟨s(vertex, other'), hadj'⟩
    have hedgesNe : (⟨s(vertex, other), hadj⟩ : G.edgeSet) ≠ edge' := by
      intro heq
      apply hne
      exact (Sym2.congr_right.mp (congrArg Subtype.val heq)).symm
    have hline : G.lineGraph.Adj
        (⟨s(vertex, other), hadj⟩ : G.edgeSet) edge' :=
      (SimpleGraph.lineGraph_adj_iff_exists).2
        ⟨hedgesNe, vertex, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
    exact (C.valid hline) (hcolour'.trans hcolourOther.symm)
  by_cases hport : ∃ port, vertex = data.defectVertex port
  · rcases hport with ⟨port, rfl⟩
    rcases Finset.card_eq_two.mp (hdata.2.1 port) with
      ⟨first, second, hne, hset⟩
    have hfirstMem : first ∈
        incidentEdgeFinset G (data.defectVertex port) := by
      rw [hset]
      simp
    have hsecondMem : second ∈
        incidentEdgeFinset G (data.defectVertex port) := by
      rw [hset]
      simp
    have hfirstVertex : data.defectVertex port ∈ (first.1 : Sym2 V) := by
      simpa [incidentEdgeFinset] using hfirstMem
    have hsecondVertex : data.defectVertex port ∈ (second.1 : Sym2 V) := by
      simpa [incidentEdgeFinset] using hsecondMem
    have hcolours : C first ≠ C second :=
      C.valid ((SimpleGraph.lineGraph_adj_iff_exists).2
        ⟨hne, data.defectVertex port, hfirstVertex, hsecondVertex⟩)
    have hword : data.colorWord C port = C first + C second := by
      simp [DegreeTwoBoundaryData.colorWord, vertexKirchhoffSum, hset, hne]
    have hmissing : C first + C second ≠ taitColor i := by
      intro heq
      apply habsent port
      exact hword.trans heq
    rcases eq_left_or_eq_right_of_ne_missingColor
        (C first) (C second) (taitColor i)
        (hC first) (hC second) hcolours (taitColor_ne_zero i) hmissing with
      hfirst | hsecond
    · exact uniqueFor first hfirstMem hfirst.symm
    · exact uniqueFor second hsecondMem hsecond.symm
  · rcases Finset.card_eq_three.mp
        (hdata.2.2 vertex (fun port heq ↦ hport ⟨port, heq⟩)) with
      ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
        hset⟩
    have hincident : IsIncidentEdgeTriple G vertex first second third :=
      ⟨hset, hfirstSecond, hfirstThird, hsecondThird⟩
    have hlocal :=
      isLocalTaitTriple_of_taitEdgeColoring_at_incidentTriple hincident hC
    rcases localTaitTriple_contains_taitColor hlocal i with
      hfirst | hsecond | hthird
    · apply uniqueFor first
      · rw [hset]
        simp
      · exact hfirst
    · apply uniqueFor second
      · rw [hset]
        simp
      · exact hsecond
    · apply uniqueFor third
      · rw [hset]
        simp
      · exact hthird

/-- A four-letter word which is constant on each of the two adjacent-pair
sides omits at least one of the three Tait colours. -/
theorem exists_taitColor_absent_of_sameSidePairs :
    ∀ word : SquareBoundaryWord,
      word 0 = word 1 → word 2 = word 3 →
      ∃ i : Fin 3, ∀ port : Fin 4, word port ≠ taitColor i := by
  decide

namespace AdjacentPairData

/-- The selected absent colour class as a pairing of the retained vertices. -/
noncomputable def deletedColorClassPairing
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (i : Fin 3)
    (habsent : ∀ port, data.degreeTwoBoundaryData.colorWord C port ≠
      taitColor i) :
    Pairing (retainedVertexSet data.firstVertex data.secondVertex) :=
  Pairing.ofPerfectMatching
    (colorClassSubgraph_isPerfectMatching_of_boundary_absent
      data.degreeTwoBoundaryData
      (data.degreeTwoBoundaryData_wellFormed hcubic) C hC i habsent)

theorem deletedColorClassPairing_supportedBy
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (i : Fin 3)
    (habsent : ∀ port, data.degreeTwoBoundaryData.colorWord C port ≠
      taitColor i) :
    (deletedColorClassPairing data hcubic C hC i habsent).SupportedBy
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) :=
  Pairing.ofPerfectMatching_supportedBy
    (colorClassSubgraph_isPerfectMatching_of_boundary_absent
      data.degreeTwoBoundaryData
      (data.degreeTwoBoundaryData_wellFormed hcubic) C hC i habsent)

/-- Extend the absent retained colour class by pairing the two deleted
vertices through their common ambient edge. -/
noncomputable def centralCompletionPairing
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (i : Fin 3)
    (habsent : ∀ port, data.degreeTwoBoundaryData.colorWord C port ≠
      taitColor i) : Pairing V := by
  let retained := deletedColorClassPairing data hcubic C hC i habsent
  exact MatchingBridge.ofMem
    (Amplitude.extendPairing_mem_pairings data.centralAdjacent.ne
      retained.toPerm retained.partner_partner retained.partner_ne)

@[simp]
theorem centralCompletionPairing_partner_first
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (i : Fin 3)
    (habsent : ∀ port, data.degreeTwoBoundaryData.colorWord C port ≠
      taitColor i) :
    (centralCompletionPairing data hcubic C hC i habsent).partner
        data.firstVertex = data.secondVertex := by
  simp [centralCompletionPairing, Amplitude.extendPairing]

/-- The central completion uses only edges of the ambient graph. -/
theorem centralCompletionPairing_supportedBy
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (i : Fin 3)
    (habsent : ∀ port, data.degreeTwoBoundaryData.colorWord C port ≠
      taitColor i) :
    (centralCompletionPairing data hcubic C hC i habsent).SupportedBy G := by
  intro vertex
  by_cases hfirst : vertex = data.firstVertex
  · subst vertex
    rw [centralCompletionPairing_partner_first]
    exact data.centralAdjacent
  by_cases hsecond : vertex = data.secondVertex
  · subst vertex
    have hpartner :=
      (centralCompletionPairing data hcubic C hC i habsent).partner_partner
        data.firstVertex
    rw [centralCompletionPairing_partner_first] at hpartner
    rw [hpartner]
    exact data.centralAdjacent.symm
  · let retained := deletedColorClassPairing data hcubic C hC i habsent
    have hretained := deletedColorClassPairing_supportedBy data
      hcubic C hC i habsent ⟨vertex, hfirst, hsecond⟩
    change G.Adj
      (⟨vertex, hfirst, hsecond⟩ :
        retainedVertexSet data.firstVertex data.secondVertex).1
      ((retained.partner ⟨vertex, hfirst, hsecond⟩).1) at hretained
    simpa [centralCompletionPairing, Amplitude.extendPairing, hfirst, hsecond]
      using hretained

/-- Every Tait colouring of an adjacent-pair deletion in an ambient Tait
counterexample yields a graph-supported ambient perfect matching containing
the deleted central edge.  This is strictly weaker than restoring the full
three-edge-colouring, and is therefore non-vacuous in the counterexample. -/
theorem exists_central_supportedPairing_of_not_taitColorable
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    ∃ pairing : Pairing V,
      pairing.SupportedBy G ∧
      pairing.partner data.firstVertex = data.secondVertex := by
  have hsame :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      data hcubic hnotColorable C hC
  obtain ⟨i, habsent⟩ := exists_taitColor_absent_of_sameSidePairs
    (data.degreeTwoBoundaryData.colorWord C) hsame.1 hsame.2
  exact ⟨centralCompletionPairing data hcubic C hC i habsent,
    centralCompletionPairing_supportedBy data hcubic C hC i habsent,
    centralCompletionPairing_partner_first data hcubic C hC i habsent⟩

/-- Package one adjacent-pair deletion colouring directly with the
exchange-rigid minimum-oddness obstruction.  The first matching `sigma` is a
global residual-defect minimizer.  The second matching `tau` is extracted from
the supplied deletion colouring and contains the selected central edge.  Thus
every exchange on a vertex set closed under both matchings is certified not to
decrease residual defect. -/
theorem exists_exchangeRigid_with_central_sitePairing_of_cubic_edgeBridgeFree
    (data : AdjacentPairData G)
    (hCubic : G.IsRegularOfDegree 3)
    (hfree : ∀ edge : G.edgeSet, ¬ G.IsBridge edge.1)
    (hnot : ¬ TaitColorable G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    ∃ sigma tau : Pairing V,
      sigma.SupportedBy G ∧
      2 ≤ residualDefect G sigma ∧
      tau.SupportedBy G ∧
      tau.partner data.firstVertex = data.secondVertex ∧
      ∀ (s : Finset V)
        (hSigmaS : ∀ vertex ∈ s, sigma.partner vertex ∈ s)
        (hTauS : ∀ vertex ∈ s, tau.partner vertex ∈ s),
        residualDefect G sigma ≤
          residualDefect G (sigma.exchange tau s hSigmaS hTauS) := by
  have hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 := by
    intro vertex
    rw [incidentEdgeFinset_card_eq_degree, hCubic vertex]
  obtain ⟨tau, htau, hcentral⟩ :=
    exists_central_supportedPairing_of_not_taitColorable
      data hcubic hnot C hC
  obtain ⟨sigma, hsigma, hodd, hminimal⟩ :=
    GoertzelV24ResidualOddness.exists_exchangeRigid_residualOddness_of_cubic_edgeBridgeFree
      hCubic hfree hnot
  refine ⟨sigma, tau, hsigma, hodd, htau, hcentral, ?_⟩
  intro s hSigmaS hTauS
  exact hminimal tau s hSigmaS hTauS htau

end AdjacentPairData

end

end GoertzelV24AdjacentPairMatchingExtraction

end Mettapedia.GraphTheory.FourColor
