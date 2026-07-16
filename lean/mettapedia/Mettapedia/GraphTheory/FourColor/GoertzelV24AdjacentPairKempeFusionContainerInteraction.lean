import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionMinimalCircuits

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary
open GoertzelV24AdjacentPairBoundary
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Routes joining the two distinct same-side port pairs lie in distinct
components of a bicolored line graph, hence have disjoint ambient supports. -/
theorem EvenKempePortPath.sameSide_ambientPath_support_disjoint
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b : Color}
    (hprofile : data.HasSameSideKempeReachabilityProfile C a b)
    (route01 : data.EvenKempePortPath C a b 0 1)
    (route23 : data.EvenKempePortPath C a b 2 3) :
    route01.ambientPath.support.Disjoint
      route23.ambientPath.support := by
  rw [List.disjoint_left]
  intro edge hroute01 hroute23
  rcases (route01.mem_ambientPath_support_iff edge).1 hroute01 with
    ⟨hselected01, hpath01⟩
  rcases (route23.mem_ambientPath_support_iff edge).1 hroute23 with
    ⟨hselected23, hpath23⟩
  let shared : C.bicoloredSet a b := ⟨edge, hselected01⟩
  have hshared01 : shared ∈ route01.path.support := by
    simpa only [shared] using hpath01
  have hshared23 : shared ∈ route23.path.support := by
    simpa only [shared] using hpath23
  have hreach01 :
      (C.bicoloredSubgraph a b).Reachable route01.leftEdge shared :=
    (route01.path.takeUntil shared hshared01).reachable
  have hreach23 :
      (C.bicoloredSubgraph a b).Reachable route23.leftEdge shared :=
    (route23.path.takeUntil shared hshared23).reachable
  have hconnected : data.KempePortsConnected C a b 0 2 :=
    ⟨route01.leftEdge, route23.leftEdge,
      route01.leftIncident, route23.leftIncident,
      hreach01.trans hreach23.symm⟩
  have hside := (hprofile 0 2).1 hconnected
  simp at hside

/-- For complementary fusion lenses, the two first-family routes are
disjoint, and independently the two second-family routes are disjoint. -/
theorem EvenKempeFusionLens.sameFamily_ambientPath_supports_disjoint
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (hbProfile : data.HasSameSideKempeReachabilityProfile C a b)
    (hcProfile : data.HasSameSideKempeReachabilityProfile C a c)
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3) :
    lens01.bRoute.ambientPath.support.Disjoint
        lens23.bRoute.ambientPath.support ∧
      lens01.cRoute.ambientPath.support.Disjoint
        lens23.cRoute.ambientPath.support :=
  ⟨lens01.bRoute.sameSide_ambientPath_support_disjoint
      hbProfile lens23.bRoute,
    lens01.cRoute.sameSide_ambientPath_support_disjoint
      hcProfile lens23.cRoute⟩

/-- An edge shared by routes from the two complementary color families has
the common first color. -/
theorem EvenKempePortPath.color_eq_first_of_mem_ambientPath_supports
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (hbc : b ≠ c)
    {leftB rightB leftC rightC : Fin 4}
    (bRoute : data.EvenKempePortPath C a b leftB rightB)
    (cRoute : data.EvenKempePortPath C a c leftC rightC)
    {edge : G.edgeSet}
    (hb : edge ∈ bRoute.ambientPath.support)
    (hc : edge ∈ cRoute.ambientPath.support) :
    C edge = a := by
  rcases (bRoute.mem_ambientPath_support_iff edge).1 hb with
    ⟨hbSelected, _⟩
  rcases (cRoute.mem_ambientPath_support_iff edge).1 hc with
    ⟨hcSelected, _⟩
  exact C.color_eq_of_mem_two_bicoloredSets hbc hbSelected hcSelected

/-- Once same-family overlaps are excluded, the intersection of the two
route unions is exactly the union of the two cross-family channels. -/
theorem EvenKempeFusionLens.mem_routeUnions_iff_crossFamily
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (edge : G.edgeSet) :
    (edge ∈ lens01.bRoute.ambientPath.support ++
        lens01.cRoute.ambientPath.support ∧
      edge ∈ lens23.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support) ↔
      ((edge ∈ lens01.bRoute.ambientPath.support ∧
          edge ∈ lens23.cRoute.ambientPath.support) ∨
        (edge ∈ lens01.cRoute.ambientPath.support ∧
          edge ∈ lens23.bRoute.ambientPath.support)) := by
  simp only [List.mem_append]
  constructor
  · rintro ⟨hb01 | hc01, hb23 | hc23⟩
    · exact False.elim
        ((List.disjoint_left.mp hbDisjoint) hb01 hb23)
    · exact Or.inl ⟨hb01, hc23⟩
    · exact Or.inr ⟨hc01, hb23⟩
    · exact False.elim
        ((List.disjoint_left.mp hcDisjoint) hc01 hc23)
  · rintro (hcross | hcross)
    · exact ⟨Or.inl hcross.1, Or.inr hcross.2⟩
    · exact ⟨Or.inr hcross.1, Or.inl hcross.2⟩

/-- Therefore every edge in the intersection of the two complementary
route containers has the common first color. -/
theorem EvenKempeFusionLens.color_eq_first_of_mem_both_routeUnions
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    {edge : G.edgeSet}
    (hboth : edge ∈ lens01.bRoute.ambientPath.support ++
        lens01.cRoute.ambientPath.support ∧
      edge ∈ lens23.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support) :
    C edge = a := by
  rcases (lens01.mem_routeUnions_iff_crossFamily
      lens23 hbDisjoint hcDisjoint edge).1 hboth with
    hcross | hcross
  · exact lens01.bRoute.color_eq_first_of_mem_ambientPath_supports
      hbc lens23.cRoute hcross.1 hcross.2
  · exact lens23.bRoute.color_eq_first_of_mem_ambientPath_supports
      hbc lens01.cRoute hcross.2 hcross.1

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  adjacentFusionLensGraphEdgeSetDecidableEq
  adjacentFusionLensRetainedVertexSetFintype
  adjacentFusionLensRetainedVertexSetDecidableEq

/-- In a graph-backed minimal counterexample, the two complementary fusion
lenses can be chosen after one reachable Kempe recoloring so that their
same-family routes lie in distinct bicolored components. -/
theorem CyclicKempeProfile.exists_two_sameFamilySeparatedFusionLenses_of_minimal
    {graphData : SimpleGraphDartRotation.Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    (profile : CyclicKempeProfile graphData data)
    {a b : Color} (hab : ValidColorPair a b) :
    ∃ C' : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).EdgeColoring Color,
      C' ∈ (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).lineGraph.KempeClosure profile.coloring ∧
      IsTaitEdgeColoring
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C' ∧
      (∀ port : Fin 4,
        data.degreeTwoBoundaryData.colorWord C' port = a) ∧
      ∃ (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
          C' a b (a + b) 0 1)
        (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
          C' a b (a + b) 2 3),
        lens01.bRoute.ambientPath.support.Disjoint
            lens23.bRoute.ambientPath.support ∧
          lens01.cRoute.ambientPath.support.Disjoint
            lens23.cRoute.ambientPath.support := by
  rcases profile.exists_two_evenKempeFusionLenses_of_minimal minimal hab with
    ⟨C', hclosure, hC', hconstant, ⟨lens01⟩, ⟨lens23⟩⟩
  have hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      (V := V) (G := G) graphData minimal.spherical.cubic
  have hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      (V := V) (G := G) graphData minimal
  have hthird := third_color_properties hab.1 hab.2.1 hab.2.2
  have hac : ValidColorPair a (a + b) :=
    ⟨hab.1, hthird.1, hthird.2.1.symm⟩
  have hbProfile :=
    data.hasSameSideKempeReachabilityProfile_of_constant_colorWord
      hcubic hnotColorable C' hC' hab hconstant
  have hcProfile :=
    data.hasSameSideKempeReachabilityProfile_of_constant_colorWord
      hcubic hnotColorable C' hC' hac hconstant
  exact ⟨C', hclosure, hC', hconstant, lens01, lens23,
    lens01.sameFamily_ambientPath_supports_disjoint
      hbProfile hcProfile lens23⟩

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
