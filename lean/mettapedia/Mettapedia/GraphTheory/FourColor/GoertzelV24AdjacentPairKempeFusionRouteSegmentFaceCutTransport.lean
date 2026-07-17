import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionAmbientTrailFaceCutTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionPrimalCircuit
import Mettapedia.GraphTheory.FourColor.GoertzelV24LineGraphTrimmedPrimalLift

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The `(a,c)` neighbor dart based at the entry endpoint of a fusion
edge. -/
def EvenKempeFusionLens.cEntryNeighborDart
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) : G.Dart :=
  SimpleGraph.edgeDartAt (lens.cPreviousVertex site).1
    (lens.cEntryVertex_mem_previousEdge hac site)

/-- The `(a,c)` neighbor dart based at the exit endpoint of a fusion
edge. -/
def EvenKempeFusionLens.cExitNeighborDart
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) : G.Dart :=
  SimpleGraph.edgeDartAt (lens.cNextVertex site).1
    (lens.cExitVertex_mem_nextEdge hac site)

@[simp] theorem EvenKempeFusionLens.cEntryNeighborDart_fst
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cEntryNeighborDart hac site).fst =
      lens.cEntryVertex hac site :=
  rfl

@[simp] theorem EvenKempeFusionLens.cExitNeighborDart_fst
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cExitNeighborDart hac site).fst =
      lens.cExitVertex hac site :=
  rfl

@[simp] theorem EvenKempeFusionLens.cEntryNeighborDart_edge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cEntryNeighborDart hac site).edge =
      (lens.cPreviousVertex site).1.1 :=
  SimpleGraph.edgeDartAt_edge _ _

@[simp] theorem EvenKempeFusionLens.cExitNeighborDart_edge
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cExitNeighborDart hac site).edge =
      (lens.cNextVertex site).1.1 :=
  SimpleGraph.edgeDartAt_edge _ _

/-- Distinct fusion edges of one color cannot be consecutive vertices of
the properly colored first route. -/
theorem EvenKempeFusionLens.bFusionOrderInterval_length_two_le
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    2 ≤ (lens.bFusionOrderInterval first second hbOrder).length := by
  let interval := lens.bFusionOrderInterval first second hbOrder
  have hpositive : 0 < interval.length :=
    lens.bFusionOrderInterval_length_pos first second hbOrder
  by_contra hnot
  change ¬2 ≤ interval.length at hnot
  have hlength : interval.length = 1 := by omega
  have hedge : lens.fusionSupportEdgeAt second =
      (lens.bNextVertex (lens.bFusionSiteAt first)).1 := by
    calc
      lens.fusionSupportEdgeAt second = interval.getVert interval.length := by
        symm
        exact interval.getVert_length
      _ = interval.getVert 1 := by rw [hlength]
      _ = (lens.bNextVertex (lens.bFusionSiteAt first)).1 :=
        lens.bFusionOrderInterval_getVert_one hab first second hbOrder
  have hfusionColor : C (lens.fusionSupportEdgeAt second) = a := by
    rw [lens.fusionSupportEdgeAt_eq_bFusionSiteAt]
    exact lens.color_eq_of_mem_bFusionSites
      (lens.bFusionSiteAt second).2
  have hnextColor := lens.bNextColor hab (lens.bFusionSiteAt first)
  apply hab
  calc
    a = C (lens.fusionSupportEdgeAt second) := hfusionColor.symm
    _ = C (lens.bNextVertex (lens.bFusionSiteAt first)).1 :=
      congrArg C hedge
    _ = b := hnextColor

theorem EvenKempeFusionLens.bFusionOrderInterval_startCap_mem
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (first : Fin lens.fusionSiteCount) :
    lens.bEntryVertex hab (lens.bFusionSiteAt first) ∈
      ((lens.fusionSupportEdgeAt first).1 : Sym2 V) := by
  simpa only [lens.fusionSupportEdgeAt_eq_bFusionSiteAt] using
    lens.bEntryVertex_mem_fusionEdge hab (lens.bFusionSiteAt first)

theorem EvenKempeFusionLens.bFusionOrderInterval_endCap_mem
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (second : Fin lens.fusionSiteCount) :
    lens.bExitVertex hab (lens.bFusionSiteAt second) ∈
      ((lens.fusionSupportEdgeAt second).1 : Sym2 V) := by
  simpa only [lens.fusionSupportEdgeAt_eq_bFusionSiteAt] using
    lens.bExitVertex_mem_fusionEdge hab (lens.bFusionSiteAt second)

theorem EvenKempeFusionLens.bFusionOrderInterval_startCap_ne
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    lens.bEntryVertex hab (lens.bFusionSiteAt first) ≠
      (lens.bFusionOrderInterval first second hbOrder).lineGraphJunctionAt
        ⟨0, lens.bFusionOrderInterval_length_pos first second hbOrder⟩ := by
  rw [lens.bFusionOrderInterval_firstJunction hab first second hbOrder]
  exact lens.bEntryVertex_ne_bExitVertex hab (lens.bFusionSiteAt first)

theorem EvenKempeFusionLens.bFusionOrderInterval_endCap_ne
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    (lens.bFusionOrderInterval first second hbOrder).lineGraphJunctionAt
        ⟨(lens.bFusionOrderInterval first second hbOrder).length - 1,
          Nat.sub_lt
            (lens.bFusionOrderInterval_length_pos first second hbOrder)
            Nat.zero_lt_one⟩ ≠
      lens.bExitVertex hab (lens.bFusionSiteAt second) := by
  rw [lens.bFusionOrderInterval_lastJunction hab first second hbOrder]
  exact lens.bEntryVertex_ne_bExitVertex hab (lens.bFusionSiteAt second)

/-- The primal route segment strictly between two ordered first-route
fusion edges. Its cap edges are precisely the two fusion edges and are not
traversed. -/
noncomputable def EvenKempeFusionLens.bFusionRouteSegment
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    G.Walk
      (lens.bExitVertex hab (lens.bFusionSiteAt first))
      (lens.bEntryVertex hab (lens.bFusionSiteAt second)) :=
  let interval := lens.bFusionOrderInterval first second hbOrder
  let middle := interval.cappedPrimalMiddleLift
    (lens.bFusionOrderInterval_length_pos first second hbOrder)
    (lens.bFusionOrderInterval_isPrimalCoherent first second hbOrder)
    (lens.bEntryVertex hab (lens.bFusionSiteAt first))
    (lens.bExitVertex hab (lens.bFusionSiteAt second))
    (lens.bFusionOrderInterval_startCap_mem hab first)
    (lens.bFusionOrderInterval_endCap_mem hab second)
    (lens.bFusionOrderInterval_startCap_ne hab first second hbOrder)
    (lens.bFusionOrderInterval_endCap_ne hab first second hbOrder)
  middle.copy
    (lens.bFusionOrderInterval_firstJunction hab first second hbOrder)
    (lens.bFusionOrderInterval_lastJunction hab first second hbOrder)

@[simp] theorem EvenKempeFusionLens.bFusionRouteSegment_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    (lens.bFusionRouteSegment hab first second hbOrder).length =
      (lens.bFusionOrderInterval first second hbOrder).length - 1 := by
  simp only [EvenKempeFusionLens.bFusionRouteSegment,
    SimpleGraph.Walk.length_copy]
  exact (lens.bFusionOrderInterval first second hbOrder).cappedPrimalMiddleLift_length
    (lens.bFusionOrderInterval_length_pos first second hbOrder)
    (lens.bFusionOrderInterval_isPrimalCoherent first second hbOrder)
    (lens.bEntryVertex hab (lens.bFusionSiteAt first))
    (lens.bExitVertex hab (lens.bFusionSiteAt second))
    (lens.bFusionOrderInterval_startCap_mem hab first)
    (lens.bFusionOrderInterval_endCap_mem hab second)
    (lens.bFusionOrderInterval_startCap_ne hab first second hbOrder)
    (lens.bFusionOrderInterval_endCap_ne hab first second hbOrder)

theorem EvenKempeFusionLens.bFusionRouteSegment_not_nil
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    ¬(lens.bFusionRouteSegment hab first second hbOrder).Nil := by
  apply SimpleGraph.Walk.not_nil_iff_lt_length.mpr
  rw [lens.bFusionRouteSegment_length hab first second hbOrder]
  have htwo := lens.bFusionOrderInterval_length_two_le
    hab first second hbOrder
  omega

theorem EvenKempeFusionLens.bFusionRouteSegment_isTrail
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    (lens.bFusionRouteSegment hab first second hbOrder).IsTrail := by
  simp only [EvenKempeFusionLens.bFusionRouteSegment,
    SimpleGraph.Walk.isTrail_copy]
  exact (lens.bFusionOrderInterval first second hbOrder)
    |>.cappedPrimalMiddleLift_isTrail_of_isPath
      (lens.bFusionOrderInterval_length_pos first second hbOrder)
      (lens.bFusionOrderInterval_isPrimalCoherent first second hbOrder)
      (lens.bFusionOrderInterval_isPath first second hbOrder)
      (lens.bEntryVertex hab (lens.bFusionSiteAt first))
      (lens.bExitVertex hab (lens.bFusionSiteAt second))
      (lens.bFusionOrderInterval_startCap_mem hab first)
      (lens.bFusionOrderInterval_endCap_mem hab second)
      (lens.bFusionOrderInterval_startCap_ne hab first second hbOrder)
      (lens.bFusionOrderInterval_endCap_ne hab first second hbOrder)

theorem EvenKempeFusionLens.bFusionRouteSegment_edges
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    (lens.bFusionRouteSegment hab first second hbOrder).edges =
      (lens.bFusionOrderInterval first second hbOrder).support.tail.dropLast.map
        Subtype.val := by
  simp only [EvenKempeFusionLens.bFusionRouteSegment,
    SimpleGraph.Walk.edges_copy]
  exact (lens.bFusionOrderInterval first second hbOrder)
    |>.cappedPrimalMiddleLift_edges_eq_map_support_tail_dropLast
      (lens.bFusionOrderInterval_length_pos first second hbOrder)
      (lens.bFusionOrderInterval_isPrimalCoherent first second hbOrder)
      (lens.bEntryVertex hab (lens.bFusionSiteAt first))
      (lens.bExitVertex hab (lens.bFusionSiteAt second))
      (lens.bFusionOrderInterval_startCap_mem hab first)
      (lens.bFusionOrderInterval_endCap_mem hab second)
      (lens.bFusionOrderInterval_startCap_ne hab first second hbOrder)
      (lens.bFusionOrderInterval_endCap_ne hab first second hbOrder)

theorem EvenKempeFusionLens.bFusionRouteSegment_getVert
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second)
    (position : Fin (lens.bFusionOrderInterval first second hbOrder).length) :
    (lens.bFusionRouteSegment hab first second hbOrder).getVert position.val =
      (lens.bFusionOrderInterval first second hbOrder).lineGraphJunctionAt
        position := by
  simp only [EvenKempeFusionLens.bFusionRouteSegment,
    SimpleGraph.Walk.getVert_copy]
  exact (lens.bFusionOrderInterval first second hbOrder)
    |>.cappedPrimalMiddleLift_getVert
      (lens.bFusionOrderInterval_length_pos first second hbOrder)
      (lens.bFusionOrderInterval_isPrimalCoherent first second hbOrder)
      (lens.bEntryVertex hab (lens.bFusionSiteAt first))
      (lens.bExitVertex hab (lens.bFusionSiteAt second))
      (lens.bFusionOrderInterval_startCap_mem hab first)
      (lens.bFusionOrderInterval_endCap_mem hab second)
      (lens.bFusionOrderInterval_startCap_ne hab first second hbOrder)
      (lens.bFusionOrderInterval_endCap_ne hab first second hbOrder)
      position

/-- The first dart of a first-route fusion segment is the route-neighbor
dart pointing away from the first fusion edge. -/
theorem EvenKempeFusionLens.bFusionRouteSegment_firstDart
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    (lens.bFusionRouteSegment hab first second hbOrder).firstDart
        (lens.bFusionRouteSegment_not_nil hab first second hbOrder) =
      lens.bExitNeighborDart hab (lens.bFusionSiteAt first) := by
  let interval := lens.bFusionOrderInterval first second hbOrder
  let segment := lens.bFusionRouteSegment hab first second hbOrder
  let hnil := lens.bFusionRouteSegment_not_nil hab first second hbOrder
  have htwo : 2 ≤ interval.length :=
    lens.bFusionOrderInterval_length_two_le hab first second hbOrder
  have hsnd : segment.snd =
      interval.lineGraphJunctionAt ⟨1, by omega⟩ := by
    exact lens.bFusionRouteSegment_getVert hab first second hbOrder
      ⟨1, by
        change 1 < interval.length
        omega⟩
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · rfl
  · calc
      (segment.firstDart hnil).edge =
          s(lens.bExitVertex hab (lens.bFusionSiteAt first), segment.snd) :=
        segment.edge_firstDart hnil
      _ = s(interval.lineGraphJunctionAt
              ⟨0, lens.bFusionOrderInterval_length_pos
                first second hbOrder⟩,
            interval.lineGraphJunctionAt ⟨1, by omega⟩) := by
        rw [hsnd, lens.bFusionOrderInterval_firstJunction
          hab first second hbOrder]
      _ = (interval.getVert 1).1 :=
        interval.pair_lineGraphJunctionAt_succ_eq_getVert_open
          0 (by omega)
          (lens.bFusionOrderInterval_isPrimalCoherent
            first second hbOrder)
      _ = (lens.bNextVertex (lens.bFusionSiteAt first)).1.1 := by
        exact congrArg Subtype.val
          (lens.bFusionOrderInterval_getVert_one
            hab first second hbOrder)
      _ = (lens.bExitNeighborDart hab
          (lens.bFusionSiteAt first)).edge := by
        symm
        exact lens.bExitNeighborDart_edge hab (lens.bFusionSiteAt first)

/-- Reversing the last dart of a first-route fusion segment gives the
route-neighbor dart pointing away from the second fusion edge. -/
theorem EvenKempeFusionLens.bFusionRouteSegment_lastDart_symm
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second) :
    ((lens.bFusionRouteSegment hab first second hbOrder).lastDart
        (lens.bFusionRouteSegment_not_nil hab first second hbOrder)).symm =
      lens.bEntryNeighborDart hab (lens.bFusionSiteAt second) := by
  let interval := lens.bFusionOrderInterval first second hbOrder
  let segment := lens.bFusionRouteSegment hab first second hbOrder
  let hnil := lens.bFusionRouteSegment_not_nil hab first second hbOrder
  have htwo : 2 ≤ interval.length :=
    lens.bFusionOrderInterval_length_two_le hab first second hbOrder
  have hpenultimate : segment.penultimate =
      interval.lineGraphJunctionAt ⟨interval.length - 2, by omega⟩ := by
    change segment.getVert (segment.length - 1) = _
    rw [lens.bFusionRouteSegment_length hab first second hbOrder]
    have hindex : interval.length - 1 - 1 = interval.length - 2 := by
      omega
    rw [hindex]
    exact lens.bFusionRouteSegment_getVert hab first second hbOrder
      ⟨interval.length - 2, by
        change interval.length - 2 < interval.length
        omega⟩
  have hjunctionLast :
      interval.lineGraphJunctionAt ⟨interval.length - 2 + 1, by omega⟩ =
        interval.lineGraphJunctionAt
          ⟨interval.length - 1,
            Nat.sub_lt
              (lens.bFusionOrderInterval_length_pos first second hbOrder)
              Nat.zero_lt_one⟩ := by
    apply congrArg interval.lineGraphJunctionAt
    apply Fin.ext
    dsimp only
    omega
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · rfl
  · calc
      ((segment.lastDart hnil).symm).edge =
          (segment.lastDart hnil).edge :=
        SimpleGraph.Dart.edge_symm (segment.lastDart hnil)
      _ = s(segment.penultimate,
          lens.bEntryVertex hab (lens.bFusionSiteAt second)) :=
        segment.edge_lastDart hnil
      _ = s(interval.lineGraphJunctionAt
              ⟨interval.length - 2, by omega⟩,
            interval.lineGraphJunctionAt
              ⟨interval.length - 2 + 1, by omega⟩) := by
        rw [hpenultimate, hjunctionLast,
          lens.bFusionOrderInterval_lastJunction
            hab first second hbOrder]
      _ = (interval.getVert (interval.length - 2 + 1)).1 :=
        interval.pair_lineGraphJunctionAt_succ_eq_getVert_open
          (interval.length - 2) (by omega)
          (lens.bFusionOrderInterval_isPrimalCoherent
            first second hbOrder)
      _ = (interval.getVert (interval.length - 1)).1 := by
        congr 2
        omega
      _ = (lens.bPreviousVertex (lens.bFusionSiteAt second)).1.1 := by
        exact congrArg Subtype.val
          (lens.bFusionOrderInterval_getVert_penultimate
            hab first second hbOrder)
      _ = (lens.bEntryNeighborDart hab
          (lens.bFusionSiteAt second)).edge := by
        symm
        exact lens.bEntryNeighborDart_edge hab (lens.bFusionSiteAt second)

/-- The oppositely ordered second-route interval remains nonempty after
reversal. -/
theorem EvenKempeFusionLens.cFusionOrderInterval_reverse_length_pos
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    0 < (lens.cFusionOrderInterval first second hcOrder).reverse.length := by
  simpa only [SimpleGraph.Walk.length_reverse] using
    lens.cFusionOrderInterval_length_pos first second hcOrder

/-- Distinct fusion edges of one color cannot be consecutive vertices of
the properly colored reversed second-route interval. -/
theorem EvenKempeFusionLens.cFusionOrderInterval_reverse_length_two_le
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    2 ≤ (lens.cFusionOrderInterval first second hcOrder).reverse.length := by
  let interval := (lens.cFusionOrderInterval first second hcOrder).reverse
  have hpositive : 0 < interval.length :=
    lens.cFusionOrderInterval_reverse_length_pos first second hcOrder
  by_contra hnot
  change ¬2 ≤ interval.length at hnot
  have hlength : interval.length = 1 := by omega
  have hedge : lens.fusionSupportEdgeAt first =
      (lens.cNextVertex (lens.bFusionSiteAt second)).1 := by
    calc
      lens.fusionSupportEdgeAt first = interval.getVert interval.length := by
        symm
        exact interval.getVert_length
      _ = interval.getVert 1 := by rw [hlength]
      _ = (lens.cNextVertex (lens.bFusionSiteAt second)).1 :=
        lens.cFusionOrderInterval_reverse_getVert_one
          hac first second hcOrder
  have hfusionColor : C (lens.fusionSupportEdgeAt first) = a := by
    rw [lens.fusionSupportEdgeAt_eq_bFusionSiteAt]
    exact lens.color_eq_of_mem_bFusionSites
      (lens.bFusionSiteAt first).2
  have hnextColor := lens.cNextColor hac (lens.bFusionSiteAt second)
  apply hac
  calc
    a = C (lens.fusionSupportEdgeAt first) := hfusionColor.symm
    _ = C (lens.cNextVertex (lens.bFusionSiteAt second)).1 :=
      congrArg C hedge
    _ = c := hnextColor

theorem EvenKempeFusionLens.cFusionOrderInterval_reverse_startCap_mem
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (second : Fin lens.fusionSiteCount) :
    lens.cEntryVertex hac (lens.bFusionSiteAt second) ∈
      ((lens.fusionSupportEdgeAt second).1 : Sym2 V) := by
  simpa only [lens.fusionSupportEdgeAt_eq_bFusionSiteAt] using
    lens.cEntryVertex_mem_fusionEdge hac (lens.bFusionSiteAt second)

theorem EvenKempeFusionLens.cFusionOrderInterval_reverse_endCap_mem
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (first : Fin lens.fusionSiteCount) :
    lens.cExitVertex hac (lens.bFusionSiteAt first) ∈
      ((lens.fusionSupportEdgeAt first).1 : Sym2 V) := by
  simpa only [lens.fusionSupportEdgeAt_eq_bFusionSiteAt] using
    lens.cExitVertex_mem_fusionEdge hac (lens.bFusionSiteAt first)

theorem EvenKempeFusionLens.cFusionOrderInterval_reverse_startCap_ne
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    lens.cEntryVertex hac (lens.bFusionSiteAt second) ≠
      (lens.cFusionOrderInterval first second hcOrder).reverse.lineGraphJunctionAt
        ⟨0, lens.cFusionOrderInterval_reverse_length_pos
          first second hcOrder⟩ := by
  rw [lens.cFusionOrderInterval_reverse_firstJunction
    hac first second hcOrder]
  exact lens.cEntryVertex_ne_cExitVertex hac (lens.bFusionSiteAt second)

theorem EvenKempeFusionLens.cFusionOrderInterval_reverse_endCap_ne
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    (lens.cFusionOrderInterval first second hcOrder).reverse.lineGraphJunctionAt
        ⟨(lens.cFusionOrderInterval first second hcOrder).reverse.length - 1,
          Nat.sub_lt
            (lens.cFusionOrderInterval_reverse_length_pos
              first second hcOrder) Nat.zero_lt_one⟩ ≠
      lens.cExitVertex hac (lens.bFusionSiteAt first) := by
  rw [lens.cFusionOrderInterval_reverse_lastJunction
    hac first second hcOrder]
  exact lens.cEntryVertex_ne_cExitVertex hac (lens.bFusionSiteAt first)

/-- The primal route segment strictly between two oppositely ordered
second-route fusion edges, oriented forward along that route. -/
noncomputable def EvenKempeFusionLens.cFusionRouteSegment
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    G.Walk
      (lens.cExitVertex hac (lens.bFusionSiteAt second))
      (lens.cEntryVertex hac (lens.bFusionSiteAt first)) :=
  let interval := (lens.cFusionOrderInterval first second hcOrder).reverse
  let middle := interval.cappedPrimalMiddleLift
    (lens.cFusionOrderInterval_reverse_length_pos first second hcOrder)
    (lens.cFusionOrderInterval_reverse_isPrimalCoherent
      first second hcOrder)
    (lens.cEntryVertex hac (lens.bFusionSiteAt second))
    (lens.cExitVertex hac (lens.bFusionSiteAt first))
    (lens.cFusionOrderInterval_reverse_startCap_mem hac second)
    (lens.cFusionOrderInterval_reverse_endCap_mem hac first)
    (lens.cFusionOrderInterval_reverse_startCap_ne
      hac first second hcOrder)
    (lens.cFusionOrderInterval_reverse_endCap_ne
      hac first second hcOrder)
  middle.copy
    (lens.cFusionOrderInterval_reverse_firstJunction
      hac first second hcOrder)
    (lens.cFusionOrderInterval_reverse_lastJunction
      hac first second hcOrder)

@[simp] theorem EvenKempeFusionLens.cFusionRouteSegment_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    (lens.cFusionRouteSegment hac first second hcOrder).length =
      (lens.cFusionOrderInterval first second hcOrder).reverse.length - 1 := by
  simp only [EvenKempeFusionLens.cFusionRouteSegment,
    SimpleGraph.Walk.length_copy]
  exact (lens.cFusionOrderInterval first second hcOrder).reverse
    |>.cappedPrimalMiddleLift_length
      (lens.cFusionOrderInterval_reverse_length_pos first second hcOrder)
      (lens.cFusionOrderInterval_reverse_isPrimalCoherent
        first second hcOrder)
      (lens.cEntryVertex hac (lens.bFusionSiteAt second))
      (lens.cExitVertex hac (lens.bFusionSiteAt first))
      (lens.cFusionOrderInterval_reverse_startCap_mem hac second)
      (lens.cFusionOrderInterval_reverse_endCap_mem hac first)
      (lens.cFusionOrderInterval_reverse_startCap_ne
        hac first second hcOrder)
      (lens.cFusionOrderInterval_reverse_endCap_ne
        hac first second hcOrder)

theorem EvenKempeFusionLens.cFusionRouteSegment_not_nil
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    ¬(lens.cFusionRouteSegment hac first second hcOrder).Nil := by
  apply SimpleGraph.Walk.not_nil_iff_lt_length.mpr
  rw [lens.cFusionRouteSegment_length hac first second hcOrder]
  have htwo := lens.cFusionOrderInterval_reverse_length_two_le
    hac first second hcOrder
  omega

theorem EvenKempeFusionLens.cFusionRouteSegment_isTrail
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    (lens.cFusionRouteSegment hac first second hcOrder).IsTrail := by
  simp only [EvenKempeFusionLens.cFusionRouteSegment,
    SimpleGraph.Walk.isTrail_copy]
  exact (lens.cFusionOrderInterval first second hcOrder).reverse
    |>.cappedPrimalMiddleLift_isTrail_of_isPath
      (lens.cFusionOrderInterval_reverse_length_pos first second hcOrder)
      (lens.cFusionOrderInterval_reverse_isPrimalCoherent
        first second hcOrder)
      ((lens.cFusionOrderInterval first second hcOrder).isPath_reverse_iff.mpr
        (lens.cFusionOrderInterval_isPath first second hcOrder))
      (lens.cEntryVertex hac (lens.bFusionSiteAt second))
      (lens.cExitVertex hac (lens.bFusionSiteAt first))
      (lens.cFusionOrderInterval_reverse_startCap_mem hac second)
      (lens.cFusionOrderInterval_reverse_endCap_mem hac first)
      (lens.cFusionOrderInterval_reverse_startCap_ne
        hac first second hcOrder)
      (lens.cFusionOrderInterval_reverse_endCap_ne
        hac first second hcOrder)

theorem EvenKempeFusionLens.cFusionRouteSegment_edges
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    (lens.cFusionRouteSegment hac first second hcOrder).edges =
      (lens.cFusionOrderInterval first second hcOrder).reverse.support.tail.dropLast.map
        Subtype.val := by
  simp only [EvenKempeFusionLens.cFusionRouteSegment,
    SimpleGraph.Walk.edges_copy]
  exact (lens.cFusionOrderInterval first second hcOrder).reverse
    |>.cappedPrimalMiddleLift_edges_eq_map_support_tail_dropLast
      (lens.cFusionOrderInterval_reverse_length_pos first second hcOrder)
      (lens.cFusionOrderInterval_reverse_isPrimalCoherent
        first second hcOrder)
      (lens.cEntryVertex hac (lens.bFusionSiteAt second))
      (lens.cExitVertex hac (lens.bFusionSiteAt first))
      (lens.cFusionOrderInterval_reverse_startCap_mem hac second)
      (lens.cFusionOrderInterval_reverse_endCap_mem hac first)
      (lens.cFusionOrderInterval_reverse_startCap_ne
        hac first second hcOrder)
      (lens.cFusionOrderInterval_reverse_endCap_ne
        hac first second hcOrder)

theorem EvenKempeFusionLens.cFusionRouteSegment_getVert
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first)))
    (position : Fin
      (lens.cFusionOrderInterval first second hcOrder).reverse.length) :
    (lens.cFusionRouteSegment hac first second hcOrder).getVert position.val =
      (lens.cFusionOrderInterval first second hcOrder).reverse.lineGraphJunctionAt
        position := by
  simp only [EvenKempeFusionLens.cFusionRouteSegment,
    SimpleGraph.Walk.getVert_copy]
  exact (lens.cFusionOrderInterval first second hcOrder).reverse
    |>.cappedPrimalMiddleLift_getVert
      (lens.cFusionOrderInterval_reverse_length_pos first second hcOrder)
      (lens.cFusionOrderInterval_reverse_isPrimalCoherent
        first second hcOrder)
      (lens.cEntryVertex hac (lens.bFusionSiteAt second))
      (lens.cExitVertex hac (lens.bFusionSiteAt first))
      (lens.cFusionOrderInterval_reverse_startCap_mem hac second)
      (lens.cFusionOrderInterval_reverse_endCap_mem hac first)
      (lens.cFusionOrderInterval_reverse_startCap_ne
        hac first second hcOrder)
      (lens.cFusionOrderInterval_reverse_endCap_ne
        hac first second hcOrder)
      position

/-- The first dart of a reversed second-route fusion segment is the
route-neighbor dart pointing away from the lower fusion edge. -/
theorem EvenKempeFusionLens.cFusionRouteSegment_firstDart
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    (lens.cFusionRouteSegment hac first second hcOrder).firstDart
        (lens.cFusionRouteSegment_not_nil hac first second hcOrder) =
      lens.cExitNeighborDart hac (lens.bFusionSiteAt second) := by
  let interval := (lens.cFusionOrderInterval first second hcOrder).reverse
  let segment := lens.cFusionRouteSegment hac first second hcOrder
  let hnil := lens.cFusionRouteSegment_not_nil hac first second hcOrder
  have htwo : 2 ≤ interval.length :=
    lens.cFusionOrderInterval_reverse_length_two_le
      hac first second hcOrder
  have hsnd : segment.snd =
      interval.lineGraphJunctionAt ⟨1, by omega⟩ := by
    exact lens.cFusionRouteSegment_getVert hac first second hcOrder
      ⟨1, by
        change 1 < interval.length
        omega⟩
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · rfl
  · calc
      (segment.firstDart hnil).edge =
          s(lens.cExitVertex hac (lens.bFusionSiteAt second), segment.snd) :=
        segment.edge_firstDart hnil
      _ = s(interval.lineGraphJunctionAt
              ⟨0, lens.cFusionOrderInterval_reverse_length_pos
                first second hcOrder⟩,
            interval.lineGraphJunctionAt ⟨1, by omega⟩) := by
        rw [hsnd, lens.cFusionOrderInterval_reverse_firstJunction
          hac first second hcOrder]
      _ = (interval.getVert 1).1 :=
        interval.pair_lineGraphJunctionAt_succ_eq_getVert_open
          0 (by omega)
          (lens.cFusionOrderInterval_reverse_isPrimalCoherent
            first second hcOrder)
      _ = (lens.cNextVertex (lens.bFusionSiteAt second)).1.1 := by
        exact congrArg Subtype.val
          (lens.cFusionOrderInterval_reverse_getVert_one
            hac first second hcOrder)
      _ = (lens.cExitNeighborDart hac
          (lens.bFusionSiteAt second)).edge := by
        symm
        exact lens.cExitNeighborDart_edge hac (lens.bFusionSiteAt second)

/-- Reversing the last dart of a second-route fusion segment gives the
route-neighbor dart pointing away from the upper fusion edge. -/
theorem EvenKempeFusionLens.cFusionRouteSegment_lastDart_symm
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first))) :
    ((lens.cFusionRouteSegment hac first second hcOrder).lastDart
        (lens.cFusionRouteSegment_not_nil hac first second hcOrder)).symm =
      lens.cEntryNeighborDart hac (lens.bFusionSiteAt first) := by
  let interval := (lens.cFusionOrderInterval first second hcOrder).reverse
  let segment := lens.cFusionRouteSegment hac first second hcOrder
  let hnil := lens.cFusionRouteSegment_not_nil hac first second hcOrder
  have htwo : 2 ≤ interval.length :=
    lens.cFusionOrderInterval_reverse_length_two_le
      hac first second hcOrder
  have hpenultimate : segment.penultimate =
      interval.lineGraphJunctionAt ⟨interval.length - 2, by omega⟩ := by
    change segment.getVert (segment.length - 1) = _
    rw [lens.cFusionRouteSegment_length hac first second hcOrder]
    have hindex : interval.length - 1 - 1 = interval.length - 2 := by
      omega
    rw [hindex]
    exact lens.cFusionRouteSegment_getVert hac first second hcOrder
      ⟨interval.length - 2, by
        change interval.length - 2 < interval.length
        omega⟩
  have hjunctionLast :
      interval.lineGraphJunctionAt ⟨interval.length - 2 + 1, by omega⟩ =
        interval.lineGraphJunctionAt
          ⟨interval.length - 1,
            Nat.sub_lt
              (lens.cFusionOrderInterval_reverse_length_pos
                first second hcOrder) Nat.zero_lt_one⟩ := by
    apply congrArg interval.lineGraphJunctionAt
    apply Fin.ext
    dsimp only
    omega
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · rfl
  · calc
      ((segment.lastDart hnil).symm).edge =
          (segment.lastDart hnil).edge :=
        SimpleGraph.Dart.edge_symm (segment.lastDart hnil)
      _ = s(segment.penultimate,
          lens.cEntryVertex hac (lens.bFusionSiteAt first)) :=
        segment.edge_lastDart hnil
      _ = s(interval.lineGraphJunctionAt
              ⟨interval.length - 2, by omega⟩,
            interval.lineGraphJunctionAt
              ⟨interval.length - 2 + 1, by omega⟩) := by
        rw [hpenultimate, hjunctionLast,
          lens.cFusionOrderInterval_reverse_lastJunction
            hac first second hcOrder]
      _ = (interval.getVert (interval.length - 2 + 1)).1 :=
        interval.pair_lineGraphJunctionAt_succ_eq_getVert_open
          (interval.length - 2) (by omega)
          (lens.cFusionOrderInterval_reverse_isPrimalCoherent
            first second hcOrder)
      _ = (interval.getVert (interval.length - 1)).1 := by
        congr 2
        omega
      _ = (lens.cPreviousVertex (lens.bFusionSiteAt first)).1.1 := by
        simpa only [interval, SimpleGraph.Walk.length_reverse] using
          congrArg Subtype.val
            (lens.cFusionOrderInterval_reverse_getVert_penultimate
              hac first second hcOrder)
      _ = (lens.cEntryNeighborDart hac
          (lens.bFusionSiteAt first)).edge := by
        symm
        exact lens.cEntryNeighborDart_edge hac (lens.bFusionSiteAt first)

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The `c`-route entry-neighbor dart lifted from the retained graph to
the ambient graph. -/
def ambientCEntryNeighborDart (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) : G.Dart :=
  retainedDartToAmbientDart data (lens.cEntryNeighborDart hac site)

/-- The `c`-route exit-neighbor dart lifted from the retained graph to
the ambient graph. -/
def ambientCExitNeighborDart (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) : G.Dart :=
  retainedDartToAmbientDart data (lens.cExitNeighborDart hac site)

/-- Every exact-cut label is constant along the internal first-route
segment between two ordered fusion sites, provided just those internal
edges avoid the cut. The fusion edges themselves are not assumed to avoid
the cut. -/
theorem EvenKempeFusionLens.bAmbientRouteSegmentFaceLabels_eq_of_not_cut
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second)
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (hnot : ∀ edge ∈
      (lens.bFusionOrderInterval first second hbOrder).support.tail.dropLast,
      ¬cut (retainedEdgeToAmbientEdge data edge)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientBExitNeighborDart data lens hab
          (lens.bFusionSiteAt first))) =
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientBEntryNeighborDart data lens hab
          (lens.bFusionSiteAt second))) := by
  let trail := lens.bFusionRouteSegment hab first second hbOrder
  let hnil := lens.bFusionRouteSegment_not_nil hab first second hbOrder
  have hlabels := retainedTrail_labels_eq_terminalDarts_of_support_not_cut
    graphData hcubic hrotation data labels cut hexact trail hnil
      (lens.bFusionRouteSegment_isTrail hab first second hbOrder)
      (lens.bFusionOrderInterval first second hbOrder).support.tail.dropLast
      (by
        intro edge hedge
        rw [lens.bFusionRouteSegment_edges hab first second hbOrder] at hedge
        exact hedge)
      hnot
  rw [lens.bFusionRouteSegment_firstDart hab first second hbOrder,
    lens.bFusionRouteSegment_lastDart_symm hab first second hbOrder]
    at hlabels
  simpa only [ambientBExitNeighborDart,
    ambientBEntryNeighborDart] using hlabels

/-- Every exact-cut label is constant along the internal second-route
segment between two oppositely ordered fusion sites, with no assumption on
the two fusion edges themselves. -/
theorem EvenKempeFusionLens.cAmbientRouteSegmentFaceLabels_eq_of_not_cut
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hac : a ≠ c) (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first)))
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (hnot : ∀ edge ∈
      (lens.cFusionOrderInterval first second hcOrder).reverse.support.tail.dropLast,
      ¬cut (retainedEdgeToAmbientEdge data edge)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (ambientCExitNeighborDart data lens hac
          (lens.bFusionSiteAt second))) =
      labels (dartOrbitFace graphData.toRotationSystem
        (ambientCEntryNeighborDart data lens hac
          (lens.bFusionSiteAt first))) := by
  let trail := lens.cFusionRouteSegment hac first second hcOrder
  let hnil := lens.cFusionRouteSegment_not_nil hac first second hcOrder
  have hlabels := retainedTrail_labels_eq_terminalDarts_of_support_not_cut
    graphData hcubic hrotation data labels cut hexact trail hnil
      (lens.cFusionRouteSegment_isTrail hac first second hcOrder)
      (lens.cFusionOrderInterval first second hcOrder).reverse.support.tail.dropLast
      (by
        intro edge hedge
        rw [lens.cFusionRouteSegment_edges hac first second hcOrder] at hedge
        exact hedge)
      hnot
  rw [lens.cFusionRouteSegment_firstDart hac first second hcOrder,
    lens.cFusionRouteSegment_lastDart_symm hac first second hcOrder]
    at hlabels
  simpa only [ambientCExitNeighborDart,
    ambientCEntryNeighborDart] using hlabels

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
