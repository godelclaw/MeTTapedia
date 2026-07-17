import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelCoherence
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionTerminalRouteSegments

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossChannelTailGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Lift the strict first-route tail after a cross site, retaining a chosen
terminal cap. The first cross edge itself is omitted. -/
noncomputable def EvenKempePortPath.firstCrossTailSegment
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c) (site : first.CrossSite second)
    (endVertex : V)
    (hendMem : endVertex ∈ (first.rightEdge.1.1 : Sym2 V))
    (hendNe :
      (first.firstSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.firstSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.firstSuffixFromCrossSite_length_pos
                second hab hbc site)
              Nat.zero_lt_one⟩ ≠ endVertex) :
    G.Walk
      ((first.firstSuffixFromCrossSite second site).lineGraphJunctionAt
        ⟨0, first.firstSuffixFromCrossSite_length_pos
          second hab hbc site⟩)
      endVertex :=
  (first.firstSuffixFromCrossSite second site).canonicalPrimalTailLift
    (first.firstSuffixFromCrossSite_length_pos second hab hbc site)
    (first.firstSuffixFromCrossSite_isPrimalCoherent second site)
    endVertex hendMem hendNe

@[simp] theorem EvenKempePortPath.firstCrossTailSegment_length
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c) (site : first.CrossSite second)
    (endVertex : V)
    (hendMem : endVertex ∈ (first.rightEdge.1.1 : Sym2 V))
    (hendNe :
      (first.firstSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.firstSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.firstSuffixFromCrossSite_length_pos
                second hab hbc site)
              Nat.zero_lt_one⟩ ≠ endVertex) :
    (first.firstCrossTailSegment second hab hbc site
      endVertex hendMem hendNe).length =
      (first.firstSuffixFromCrossSite second site).length := by
  exact (first.firstSuffixFromCrossSite second site)
    |>.canonicalPrimalTailLift_length
      (first.firstSuffixFromCrossSite_length_pos second hab hbc site)
      (first.firstSuffixFromCrossSite_isPrimalCoherent second site)
      endVertex hendMem hendNe

theorem EvenKempePortPath.firstCrossTailSegment_not_nil
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c) (site : first.CrossSite second)
    (endVertex : V)
    (hendMem : endVertex ∈ (first.rightEdge.1.1 : Sym2 V))
    (hendNe :
      (first.firstSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.firstSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.firstSuffixFromCrossSite_length_pos
                second hab hbc site)
              Nat.zero_lt_one⟩ ≠ endVertex) :
    ¬(first.firstCrossTailSegment second hab hbc site
      endVertex hendMem hendNe).Nil := by
  exact (first.firstSuffixFromCrossSite second site)
    |>.canonicalPrimalTailLift_not_nil
      (first.firstSuffixFromCrossSite_length_pos second hab hbc site)
      (first.firstSuffixFromCrossSite_isPrimalCoherent second site)
      endVertex hendMem hendNe

theorem EvenKempePortPath.firstCrossTailSegment_isTrail
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c) (site : first.CrossSite second)
    (endVertex : V)
    (hendMem : endVertex ∈ (first.rightEdge.1.1 : Sym2 V))
    (hendNe :
      (first.firstSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.firstSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.firstSuffixFromCrossSite_length_pos
                second hab hbc site)
              Nat.zero_lt_one⟩ ≠ endVertex) :
    (first.firstCrossTailSegment second hab hbc site
      endVertex hendMem hendNe).IsTrail := by
  exact (first.firstSuffixFromCrossSite second site)
    |>.canonicalPrimalTailLift_isTrail_of_isPath
      (first.firstSuffixFromCrossSite_length_pos second hab hbc site)
      (first.firstSuffixFromCrossSite_isPrimalCoherent second site)
      (first.firstSuffixFromCrossSite_isPath second site)
      endVertex hendMem hendNe

theorem EvenKempePortPath.firstCrossTailSegment_edges
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c) (site : first.CrossSite second)
    (endVertex : V)
    (hendMem : endVertex ∈ (first.rightEdge.1.1 : Sym2 V))
    (hendNe :
      (first.firstSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.firstSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.firstSuffixFromCrossSite_length_pos
                second hab hbc site)
              Nat.zero_lt_one⟩ ≠ endVertex) :
    (first.firstCrossTailSegment second hab hbc site
      endVertex hendMem hendNe).edges =
      (first.firstSuffixFromCrossSite second site).support.tail.map
        Subtype.val := by
  exact (first.firstSuffixFromCrossSite second site)
    |>.canonicalPrimalTailLift_edges_eq_map_support_tail
      (first.firstSuffixFromCrossSite_length_pos second hab hbc site)
      (first.firstSuffixFromCrossSite_isPrimalCoherent second site)
      endVertex hendMem hendNe

theorem EvenKempePortPath.firstCrossTailSegment_firstDart_edge
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c) (site : first.CrossSite second)
    (endVertex : V)
    (hendMem : endVertex ∈ (first.rightEdge.1.1 : Sym2 V))
    (hendNe :
      (first.firstSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.firstSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.firstSuffixFromCrossSite_length_pos
                second hab hbc site)
              Nat.zero_lt_one⟩ ≠ endVertex)
    (hnil : ¬(first.firstCrossTailSegment second hab hbc site
      endVertex hendMem hendNe).Nil) :
    ((first.firstCrossTailSegment second hab hbc site
      endVertex hendMem hendNe).firstDart hnil).edge =
      ((first.firstSuffixFromCrossSite second site).getVert 1).1 := by
  exact (first.firstSuffixFromCrossSite second site)
    |>.canonicalPrimalTailLift_firstDart_edge
      (first.firstSuffixFromCrossSite_length_pos second hab hbc site)
      (first.firstSuffixFromCrossSite_isPrimalCoherent second site)
      endVertex hendMem hendNe hnil

theorem EvenKempePortPath.firstCrossTailSegment_lastDart_edge
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c) (site : first.CrossSite second)
    (endVertex : V)
    (hendMem : endVertex ∈ (first.rightEdge.1.1 : Sym2 V))
    (hendNe :
      (first.firstSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.firstSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.firstSuffixFromCrossSite_length_pos
                second hab hbc site)
              Nat.zero_lt_one⟩ ≠ endVertex)
    (hnil : ¬(first.firstCrossTailSegment second hab hbc site
      endVertex hendMem hendNe).Nil) :
    ((first.firstCrossTailSegment second hab hbc site
      endVertex hendMem hendNe).lastDart hnil).edge =
      first.rightEdge.1.1 := by
  exact (first.firstSuffixFromCrossSite second site)
    |>.canonicalPrimalTailLift_lastDart_edge
      (first.firstSuffixFromCrossSite_length_pos second hab hbc site)
      (first.firstSuffixFromCrossSite_isPrimalCoherent second site)
      endVertex hendMem hendNe hnil

/-- Lift the strict second-route tail after a cross site, again omitting
the shared cross edge and retaining a chosen terminal cap. -/
noncomputable def EvenKempePortPath.secondCrossTailSegment
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c) (site : first.CrossSite second)
    (endVertex : V)
    (hendMem : endVertex ∈ (second.rightEdge.1.1 : Sym2 V))
    (hendNe :
      (first.secondSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.secondSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.secondSuffixFromCrossSite_length_pos
                second hac hbc site)
              Nat.zero_lt_one⟩ ≠ endVertex) :
    G.Walk
      ((first.secondSuffixFromCrossSite second site).lineGraphJunctionAt
        ⟨0, first.secondSuffixFromCrossSite_length_pos
          second hac hbc site⟩)
      endVertex :=
  (first.secondSuffixFromCrossSite second site).canonicalPrimalTailLift
    (first.secondSuffixFromCrossSite_length_pos second hac hbc site)
    (first.secondSuffixFromCrossSite_isPrimalCoherent second site)
    endVertex hendMem hendNe

@[simp] theorem EvenKempePortPath.secondCrossTailSegment_length
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c) (site : first.CrossSite second)
    (endVertex : V)
    (hendMem : endVertex ∈ (second.rightEdge.1.1 : Sym2 V))
    (hendNe :
      (first.secondSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.secondSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.secondSuffixFromCrossSite_length_pos
                second hac hbc site)
              Nat.zero_lt_one⟩ ≠ endVertex) :
    (first.secondCrossTailSegment second hac hbc site
      endVertex hendMem hendNe).length =
      (first.secondSuffixFromCrossSite second site).length := by
  exact (first.secondSuffixFromCrossSite second site)
    |>.canonicalPrimalTailLift_length
      (first.secondSuffixFromCrossSite_length_pos second hac hbc site)
      (first.secondSuffixFromCrossSite_isPrimalCoherent second site)
      endVertex hendMem hendNe

theorem EvenKempePortPath.secondCrossTailSegment_not_nil
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c) (site : first.CrossSite second)
    (endVertex : V)
    (hendMem : endVertex ∈ (second.rightEdge.1.1 : Sym2 V))
    (hendNe :
      (first.secondSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.secondSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.secondSuffixFromCrossSite_length_pos
                second hac hbc site)
              Nat.zero_lt_one⟩ ≠ endVertex) :
    ¬(first.secondCrossTailSegment second hac hbc site
      endVertex hendMem hendNe).Nil := by
  exact (first.secondSuffixFromCrossSite second site)
    |>.canonicalPrimalTailLift_not_nil
      (first.secondSuffixFromCrossSite_length_pos second hac hbc site)
      (first.secondSuffixFromCrossSite_isPrimalCoherent second site)
      endVertex hendMem hendNe

theorem EvenKempePortPath.secondCrossTailSegment_isTrail
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c) (site : first.CrossSite second)
    (endVertex : V)
    (hendMem : endVertex ∈ (second.rightEdge.1.1 : Sym2 V))
    (hendNe :
      (first.secondSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.secondSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.secondSuffixFromCrossSite_length_pos
                second hac hbc site)
              Nat.zero_lt_one⟩ ≠ endVertex) :
    (first.secondCrossTailSegment second hac hbc site
      endVertex hendMem hendNe).IsTrail := by
  exact (first.secondSuffixFromCrossSite second site)
    |>.canonicalPrimalTailLift_isTrail_of_isPath
      (first.secondSuffixFromCrossSite_length_pos second hac hbc site)
      (first.secondSuffixFromCrossSite_isPrimalCoherent second site)
      (first.secondSuffixFromCrossSite_isPath second site)
      endVertex hendMem hendNe

theorem EvenKempePortPath.secondCrossTailSegment_edges
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c) (site : first.CrossSite second)
    (endVertex : V)
    (hendMem : endVertex ∈ (second.rightEdge.1.1 : Sym2 V))
    (hendNe :
      (first.secondSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.secondSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.secondSuffixFromCrossSite_length_pos
                second hac hbc site)
              Nat.zero_lt_one⟩ ≠ endVertex) :
    (first.secondCrossTailSegment second hac hbc site
      endVertex hendMem hendNe).edges =
      (first.secondSuffixFromCrossSite second site).support.tail.map
        Subtype.val := by
  exact (first.secondSuffixFromCrossSite second site)
    |>.canonicalPrimalTailLift_edges_eq_map_support_tail
      (first.secondSuffixFromCrossSite_length_pos second hac hbc site)
      (first.secondSuffixFromCrossSite_isPrimalCoherent second site)
      endVertex hendMem hendNe

theorem EvenKempePortPath.secondCrossTailSegment_firstDart_edge
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c) (site : first.CrossSite second)
    (endVertex : V)
    (hendMem : endVertex ∈ (second.rightEdge.1.1 : Sym2 V))
    (hendNe :
      (first.secondSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.secondSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.secondSuffixFromCrossSite_length_pos
                second hac hbc site)
              Nat.zero_lt_one⟩ ≠ endVertex)
    (hnil : ¬(first.secondCrossTailSegment second hac hbc site
      endVertex hendMem hendNe).Nil) :
    ((first.secondCrossTailSegment second hac hbc site
      endVertex hendMem hendNe).firstDart hnil).edge =
      ((first.secondSuffixFromCrossSite second site).getVert 1).1 := by
  exact (first.secondSuffixFromCrossSite second site)
    |>.canonicalPrimalTailLift_firstDart_edge
      (first.secondSuffixFromCrossSite_length_pos second hac hbc site)
      (first.secondSuffixFromCrossSite_isPrimalCoherent second site)
      endVertex hendMem hendNe hnil

theorem EvenKempePortPath.secondCrossTailSegment_lastDart_edge
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c) (site : first.CrossSite second)
    (endVertex : V)
    (hendMem : endVertex ∈ (second.rightEdge.1.1 : Sym2 V))
    (hendNe :
      (first.secondSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.secondSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.secondSuffixFromCrossSite_length_pos
                second hac hbc site)
              Nat.zero_lt_one⟩ ≠ endVertex)
    (hnil : ¬(first.secondCrossTailSegment second hac hbc site
      endVertex hendMem hendNe).Nil) :
    ((first.secondCrossTailSegment second hac hbc site
      endVertex hendMem hendNe).lastDart hnil).edge =
      second.rightEdge.1.1 := by
  exact (first.secondSuffixFromCrossSite second site)
    |>.canonicalPrimalTailLift_lastDart_edge
      (first.secondSuffixFromCrossSite_length_pos second hac hbc site)
      (first.secondSuffixFromCrossSite_isPrimalCoherent second site)
      endVertex hendMem hendNe hnil

/-- The first strict `bc` suffix reaches port `1` without bouncing at its
terminal cap. -/
theorem EvenKempeFusionLens.bcFirstSuffix_endCap_ne
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.bRoute.CrossSite lens23.cRoute) :
    (lens01.bRoute.firstSuffixFromCrossSite
        lens23.cRoute site).lineGraphJunctionAt
      ⟨(lens01.bRoute.firstSuffixFromCrossSite
          lens23.cRoute site).length - 1,
        Nat.sub_lt
          (lens01.bRoute.firstSuffixFromCrossSite_length_pos
            lens23.cRoute hab hbc site)
          Nat.zero_lt_one⟩ ≠ data.defectVertex 1 := by
  rw [lens01.bRoute.firstSuffixFromCrossSite_lastJunction
      lens23.cRoute hab hbc site,
    ← lens01.rightConnectorVertex_eq_defectVertex]
  exact lens01.bRouteLastJunction_ne_rightConnectorVertex
    hdata hab hac
      (lens01.bRoute.firstAmbientPath_length_pos_of_crossSite
        lens23.cRoute hab hbc site)

/-- The second strict `bc` suffix reaches port `3` without terminal
bounce. -/
theorem EvenKempeFusionLens.bcSecondSuffix_endCap_ne
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.bRoute.CrossSite lens23.cRoute) :
    (lens01.bRoute.secondSuffixFromCrossSite
        lens23.cRoute site).lineGraphJunctionAt
      ⟨(lens01.bRoute.secondSuffixFromCrossSite
          lens23.cRoute site).length - 1,
        Nat.sub_lt
          (lens01.bRoute.secondSuffixFromCrossSite_length_pos
            lens23.cRoute hac hbc site)
          Nat.zero_lt_one⟩ ≠ data.defectVertex 3 := by
  rw [lens01.bRoute.secondSuffixFromCrossSite_lastJunction
      lens23.cRoute hac hbc site,
    ← lens23.rightConnectorVertex_eq_defectVertex]
  exact lens23.cRouteLastJunction_ne_rightConnectorVertex
    hdata hab hac
      (lens01.bRoute.secondAmbientPath_length_pos_of_crossSite
        lens23.cRoute hac hbc site)

/-- The first strict `cb` suffix reaches port `1` without terminal
bounce. -/
theorem EvenKempeFusionLens.cbFirstSuffix_endCap_ne
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.cRoute.CrossSite lens23.bRoute) :
    (lens01.cRoute.firstSuffixFromCrossSite
        lens23.bRoute site).lineGraphJunctionAt
      ⟨(lens01.cRoute.firstSuffixFromCrossSite
          lens23.bRoute site).length - 1,
        Nat.sub_lt
          (lens01.cRoute.firstSuffixFromCrossSite_length_pos
            lens23.bRoute hac hbc.symm site)
          Nat.zero_lt_one⟩ ≠ data.defectVertex 1 := by
  rw [lens01.cRoute.firstSuffixFromCrossSite_lastJunction
      lens23.bRoute hac hbc.symm site,
    ← lens01.rightConnectorVertex_eq_defectVertex]
  exact lens01.cRouteLastJunction_ne_rightConnectorVertex
    hdata hab hac
      (lens01.cRoute.firstAmbientPath_length_pos_of_crossSite
        lens23.bRoute hac hbc.symm site)

/-- The second strict `cb` suffix reaches port `3` without terminal
bounce. -/
theorem EvenKempeFusionLens.cbSecondSuffix_endCap_ne
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.cRoute.CrossSite lens23.bRoute) :
    (lens01.cRoute.secondSuffixFromCrossSite
        lens23.bRoute site).lineGraphJunctionAt
      ⟨(lens01.cRoute.secondSuffixFromCrossSite
          lens23.bRoute site).length - 1,
        Nat.sub_lt
          (lens01.cRoute.secondSuffixFromCrossSite_length_pos
            lens23.bRoute hab hbc.symm site)
          Nat.zero_lt_one⟩ ≠ data.defectVertex 3 := by
  rw [lens01.cRoute.secondSuffixFromCrossSite_lastJunction
      lens23.bRoute hab hbc.symm site,
    ← lens23.rightConnectorVertex_eq_defectVertex]
  exact lens23.bRouteLastJunction_ne_rightConnectorVertex
    hdata hab hac
      (lens01.cRoute.secondAmbientPath_length_pos_of_crossSite
        lens23.bRoute hab hbc.symm site)

/-- The first route's outgoing dart immediately after a cross edge. -/
def EvenKempePortPath.firstCrossExitDart
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) : G.Dart :=
  SimpleGraph.edgeDartAt
    ((first.firstSuffixFromCrossSite second site).getVert 1)
    (by
      have hmem :=
        (first.firstSuffixFromCrossSite second site)
          |>.lineGraphJunctionAt_mem_right
            ⟨0, first.firstSuffixFromCrossSite_length_pos
              second hab hbc site⟩
      simpa only [Nat.zero_add] using hmem)

@[simp] theorem EvenKempePortPath.firstCrossExitDart_fst
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.firstCrossExitDart second hab hbc site).fst =
      (first.firstSuffixFromCrossSite second site).lineGraphJunctionAt
        ⟨0, first.firstSuffixFromCrossSite_length_pos
          second hab hbc site⟩ :=
  rfl

@[simp] theorem EvenKempePortPath.firstCrossExitDart_edge
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.firstCrossExitDart second hab hbc site).edge =
      ((first.firstSuffixFromCrossSite second site).getVert 1).1 :=
  SimpleGraph.edgeDartAt_edge _ _

/-- The first dart of every first cross-tail lift is its canonical outgoing
cross-site dart. -/
theorem EvenKempePortPath.firstCrossTailSegment_firstDart
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c) (site : first.CrossSite second)
    (endVertex : V)
    (hendMem : endVertex ∈ (first.rightEdge.1.1 : Sym2 V))
    (hendNe :
      (first.firstSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.firstSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.firstSuffixFromCrossSite_length_pos
                second hab hbc site)
              Nat.zero_lt_one⟩ ≠ endVertex)
    (hnil : ¬(first.firstCrossTailSegment second hab hbc site
      endVertex hendMem hendNe).Nil) :
    (first.firstCrossTailSegment second hab hbc site
      endVertex hendMem hendNe).firstDart hnil =
        first.firstCrossExitDart second hab hbc site := by
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · simp
  · exact (first.firstCrossTailSegment_firstDart_edge
      second hab hbc site endVertex hendMem hendNe hnil).trans
        (first.firstCrossExitDart_edge second hab hbc site).symm

/-- The second route's outgoing dart immediately after the same cross
edge. -/
def EvenKempePortPath.secondCrossExitDart
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) : G.Dart :=
  SimpleGraph.edgeDartAt
    ((first.secondSuffixFromCrossSite second site).getVert 1)
    (by
      have hmem :=
        (first.secondSuffixFromCrossSite second site)
          |>.lineGraphJunctionAt_mem_right
            ⟨0, first.secondSuffixFromCrossSite_length_pos
              second hac hbc site⟩
      simpa only [Nat.zero_add] using hmem)

@[simp] theorem EvenKempePortPath.secondCrossExitDart_fst
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.secondCrossExitDart second hac hbc site).fst =
      (first.secondSuffixFromCrossSite second site).lineGraphJunctionAt
        ⟨0, first.secondSuffixFromCrossSite_length_pos
          second hac hbc site⟩ :=
  rfl

@[simp] theorem EvenKempePortPath.secondCrossExitDart_edge
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c)
    (site : first.CrossSite second) :
    (first.secondCrossExitDart second hac hbc site).edge =
      ((first.secondSuffixFromCrossSite second site).getVert 1).1 :=
  SimpleGraph.edgeDartAt_edge _ _

/-- The first dart of every second cross-tail lift is its canonical outgoing
cross-site dart. -/
theorem EvenKempePortPath.secondCrossTailSegment_firstDart
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c) (site : first.CrossSite second)
    (endVertex : V)
    (hendMem : endVertex ∈ (second.rightEdge.1.1 : Sym2 V))
    (hendNe :
      (first.secondSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.secondSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.secondSuffixFromCrossSite_length_pos
                second hac hbc site)
              Nat.zero_lt_one⟩ ≠ endVertex)
    (hnil : ¬(first.secondCrossTailSegment second hac hbc site
      endVertex hendMem hendNe).Nil) :
    (first.secondCrossTailSegment second hac hbc site
      endVertex hendMem hendNe).firstDart hnil =
        first.secondCrossExitDart second hac hbc site := by
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · simp
  · exact (first.secondCrossTailSegment_firstDart_edge
      second hac hbc site endVertex hendMem hendNe hnil).trans
        (first.secondCrossExitDart_edge second hac hbc site).symm

/-- A first-route cross-tail lift ending at its boundary defect retains the
canonical right terminal dart. -/
theorem EvenKempePortPath.firstCrossTailSegment_lastDart_symm
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hab : a ≠ b) (hbc : b ≠ c) (site : first.CrossSite second)
    (hendNe :
      (first.firstSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.firstSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.firstSuffixFromCrossSite_length_pos
                second hab hbc site)
              Nat.zero_lt_one⟩ ≠ data.defectVertex firstRight)
    (hnil : ¬(first.firstCrossTailSegment second hab hbc site
      (data.defectVertex firstRight)
      (by simpa [incidentEdgeFinset] using first.rightIncident)
      hendNe).Nil) :
    ((first.firstCrossTailSegment second hab hbc site
      (data.defectVertex firstRight)
      (by simpa [incidentEdgeFinset] using first.rightIncident)
      hendNe).lastDart hnil).symm = first.rightTerminalDart := by
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · simp
  · rw [SimpleGraph.Dart.edge_symm]
    exact (first.firstCrossTailSegment_lastDart_edge second hab hbc site
      (data.defectVertex firstRight)
      (by simpa [incidentEdgeFinset] using first.rightIncident)
      hendNe hnil).trans first.rightTerminalDart_edge.symm

/-- A second-route cross-tail lift ending at its boundary defect likewise
retains that route's right terminal dart. -/
theorem EvenKempePortPath.secondCrossTailSegment_lastDart_symm
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {firstLeft firstRight secondLeft secondRight : Fin portCount}
    (first : data.EvenKempePortPath C a b firstLeft firstRight)
    (second : data.EvenKempePortPath C a c secondLeft secondRight)
    (hac : a ≠ c) (hbc : b ≠ c) (site : first.CrossSite second)
    (hendNe :
      (first.secondSuffixFromCrossSite second site).lineGraphJunctionAt
          ⟨(first.secondSuffixFromCrossSite second site).length - 1,
            Nat.sub_lt
              (first.secondSuffixFromCrossSite_length_pos
                second hac hbc site)
              Nat.zero_lt_one⟩ ≠ data.defectVertex secondRight)
    (hnil : ¬(first.secondCrossTailSegment second hac hbc site
      (data.defectVertex secondRight)
      (by simpa [incidentEdgeFinset] using second.rightIncident)
      hendNe).Nil) :
    ((first.secondCrossTailSegment second hac hbc site
      (data.defectVertex secondRight)
      (by simpa [incidentEdgeFinset] using second.rightIncident)
      hendNe).lastDart hnil).symm = second.rightTerminalDart := by
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · simp
  · rw [SimpleGraph.Dart.edge_symm]
    exact (first.secondCrossTailSegment_lastDart_edge second hac hbc site
      (data.defectVertex secondRight)
      (by simpa [incidentEdgeFinset] using second.rightIncident)
      hendNe hnil).trans second.rightTerminalDart_edge.symm

/-- The cut-complementary first `bc` tail from the cross site to port
`1`. -/
noncomputable def EvenKempeFusionLens.bcFirstRightTailSegment
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.bRoute.CrossSite lens23.cRoute) :
    G.Walk
      ((lens01.bRoute.firstSuffixFromCrossSite
        lens23.cRoute site).lineGraphJunctionAt
          ⟨0, lens01.bRoute.firstSuffixFromCrossSite_length_pos
            lens23.cRoute hab hbc site⟩)
      (data.defectVertex 1) :=
  lens01.bRoute.firstCrossTailSegment lens23.cRoute hab hbc site
    (data.defectVertex 1)
    (by simpa [incidentEdgeFinset] using lens01.bRoute.rightIncident)
    (lens01.bcFirstSuffix_endCap_ne lens23 hdata hab hac hbc site)

/-- The cut-complementary second `bc` tail from the cross site to port
`3`. -/
noncomputable def EvenKempeFusionLens.bcSecondRightTailSegment
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.bRoute.CrossSite lens23.cRoute) :
    G.Walk
      ((lens01.bRoute.secondSuffixFromCrossSite
        lens23.cRoute site).lineGraphJunctionAt
          ⟨0, lens01.bRoute.secondSuffixFromCrossSite_length_pos
            lens23.cRoute hac hbc site⟩)
      (data.defectVertex 3) :=
  lens01.bRoute.secondCrossTailSegment lens23.cRoute hac hbc site
    (data.defectVertex 3)
    (by simpa [incidentEdgeFinset] using lens23.cRoute.rightIncident)
    (lens01.bcSecondSuffix_endCap_ne lens23 hdata hab hac hbc site)

/-- The cut-complementary first `cb` tail from the cross site to port
`1`. -/
noncomputable def EvenKempeFusionLens.cbFirstRightTailSegment
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.cRoute.CrossSite lens23.bRoute) :
    G.Walk
      ((lens01.cRoute.firstSuffixFromCrossSite
        lens23.bRoute site).lineGraphJunctionAt
          ⟨0, lens01.cRoute.firstSuffixFromCrossSite_length_pos
            lens23.bRoute hac hbc.symm site⟩)
      (data.defectVertex 1) :=
  lens01.cRoute.firstCrossTailSegment lens23.bRoute hac hbc.symm site
    (data.defectVertex 1)
    (by simpa [incidentEdgeFinset] using lens01.cRoute.rightIncident)
    (lens01.cbFirstSuffix_endCap_ne lens23 hdata hab hac hbc site)

/-- The cut-complementary second `cb` tail from the cross site to port
`3`. -/
noncomputable def EvenKempeFusionLens.cbSecondRightTailSegment
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (site : lens01.cRoute.CrossSite lens23.bRoute) :
    G.Walk
      ((lens01.cRoute.secondSuffixFromCrossSite
        lens23.bRoute site).lineGraphJunctionAt
          ⟨0, lens01.cRoute.secondSuffixFromCrossSite_length_pos
            lens23.bRoute hab hbc.symm site⟩)
      (data.defectVertex 3) :=
  lens01.cRoute.secondCrossTailSegment lens23.bRoute hab hbc.symm site
    (data.defectVertex 3)
    (by simpa [incidentEdgeFinset] using lens23.bRoute.rightIncident)
    (lens01.cbSecondSuffix_endCap_ne lens23 hdata hab hac hbc site)

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
