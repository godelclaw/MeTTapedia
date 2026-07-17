import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionRouteSegmentFaceCutTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionReturnCircuit
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionDisjointCircuit
import Mettapedia.GraphTheory.FourColor.GoertzelV24LineGraphOneSidedPrimalLift

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance fusionTerminalSegmentGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The cap opposite the first junction of a reversed `b`-prefix is the
exit endpoint of the fusion edge. -/
theorem EvenKempeFusionLens.bLeftPrefixReverse_startCap_ne
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.bExitVertex hab site ≠
      (lens.bAmbientPrefixToFusion site).reverse.lineGraphJunctionAt
        ⟨0, by simpa only [SimpleGraph.Walk.length_reverse] using
          lens.bAmbientPrefixToFusion_length_pos hab hac site⟩ := by
  rw [lens.bAmbientPrefixToFusion_reverse_firstJunction hab hac site]
  exact (lens.bEntryVertex_ne_bExitVertex hab site).symm

/-- At the retained terminal cap, the last reversed-prefix junction is
not the boundary defect vertex. -/
theorem EvenKempeFusionLens.bLeftPrefixReverse_endCap_ne
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    let reversed := (lens.bAmbientPrefixToFusion site).reverse
    reversed.lineGraphJunctionAt
        ⟨reversed.length - 1,
          Nat.sub_lt (by
            dsimp only [reversed]
            simpa only [SimpleGraph.Walk.length_reverse] using
              lens.bAmbientPrefixToFusion_length_pos hab hac site)
            Nat.zero_lt_one⟩ ≠
      data.defectVertex left := by
  dsimp only
  rw [lens.bAmbientPrefixToFusion_reverse_lastJunction hab hac site,
    ← lens.leftConnectorVertex_eq_defectVertex]
  exact (lens.leftConnectorVertex_ne_bPrefixFirstJunction
    hdata hab hac site).symm

/-- The retained primal segment from the `b`-entry arm of a fusion site
back to the left route terminal. The fusion edge is the deleted cap; the
terminal route edge remains in the segment. -/
noncomputable def EvenKempeFusionLens.bLeftTerminalRouteSegment
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    G.Walk (lens.bEntryVertex hab site) (data.defectVertex left) :=
  let reversed := (lens.bAmbientPrefixToFusion site).reverse
  let hpositive : 0 < reversed.length := by
    dsimp only [reversed]
    simpa only [SimpleGraph.Walk.length_reverse] using
      lens.bAmbientPrefixToFusion_length_pos hab hac site
  let tailLift := reversed.cappedPrimalTailLift hpositive
    (lens.bAmbientPrefixToFusion_reverse_isPrimalCoherent site)
    (lens.bExitVertex hab site) (data.defectVertex left)
    (lens.bExitVertex_mem_fusionEdge hab site)
    (by simpa [incidentEdgeFinset] using lens.bRoute.leftIncident)
    (lens.bLeftPrefixReverse_startCap_ne hab hac site)
    (lens.bLeftPrefixReverse_endCap_ne hdata hab hac site)
  tailLift.copy
    (lens.bAmbientPrefixToFusion_reverse_firstJunction hab hac site)
    rfl

@[simp] theorem EvenKempeFusionLens.bLeftTerminalRouteSegment_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.bLeftTerminalRouteSegment hdata hab hac site).length =
      (lens.bAmbientPrefixToFusion site).length := by
  simp only [EvenKempeFusionLens.bLeftTerminalRouteSegment,
    SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.cappedPrimalTailLift_length,
    SimpleGraph.Walk.length_reverse]

theorem EvenKempeFusionLens.bLeftTerminalRouteSegment_not_nil
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    ¬(lens.bLeftTerminalRouteSegment hdata hab hac site).Nil := by
  apply SimpleGraph.Walk.not_nil_iff_lt_length.mpr
  rw [lens.bLeftTerminalRouteSegment_length hdata hab hac site]
  exact lens.bAmbientPrefixToFusion_length_pos hab hac site

theorem EvenKempeFusionLens.bLeftTerminalRouteSegment_isTrail
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.bLeftTerminalRouteSegment hdata hab hac site).IsTrail := by
  simp only [EvenKempeFusionLens.bLeftTerminalRouteSegment,
    SimpleGraph.Walk.isTrail_copy]
  exact (lens.bAmbientPrefixToFusion site).reverse
    |>.cappedPrimalTailLift_isTrail_of_isPath
      (by simpa only [SimpleGraph.Walk.length_reverse] using
        lens.bAmbientPrefixToFusion_length_pos hab hac site)
      (lens.bAmbientPrefixToFusion_reverse_isPrimalCoherent site)
      ((lens.bAmbientPrefixToFusion site).isPath_reverse_iff.mpr
        (lens.bAmbientPrefixToFusion_isPath site))
      (lens.bExitVertex hab site) (data.defectVertex left)
      (lens.bExitVertex_mem_fusionEdge hab site)
      (by simpa [incidentEdgeFinset] using lens.bRoute.leftIncident)
      (lens.bLeftPrefixReverse_startCap_ne hab hac site)
      (lens.bLeftPrefixReverse_endCap_ne hdata hab hac site)

theorem EvenKempeFusionLens.bLeftTerminalRouteSegment_edges
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.bLeftTerminalRouteSegment hdata hab hac site).edges =
      (lens.bAmbientPrefixToFusion site).reverse.support.tail.map
        Subtype.val := by
  simp only [EvenKempeFusionLens.bLeftTerminalRouteSegment,
    SimpleGraph.Walk.edges_copy]
  exact (lens.bAmbientPrefixToFusion site).reverse
    |>.cappedPrimalTailLift_edges_eq_map_support_tail
      (by simpa only [SimpleGraph.Walk.length_reverse] using
        lens.bAmbientPrefixToFusion_length_pos hab hac site)
      (lens.bAmbientPrefixToFusion_reverse_isPrimalCoherent site)
      (lens.bExitVertex hab site) (data.defectVertex left)
      (lens.bExitVertex_mem_fusionEdge hab site)
      (by simpa [incidentEdgeFinset] using lens.bRoute.leftIncident)
      (lens.bLeftPrefixReverse_startCap_ne hab hac site)
      (lens.bLeftPrefixReverse_endCap_ne hdata hab hac site)

/-- The segment leaves the fusion site along its `b`-entry neighbor
dart. -/
theorem EvenKempeFusionLens.bLeftTerminalRouteSegment_firstDart
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.bLeftTerminalRouteSegment hdata hab hac site).firstDart
        (lens.bLeftTerminalRouteSegment_not_nil hdata hab hac site) =
      lens.bEntryNeighborDart hab site := by
  let reversed := (lens.bAmbientPrefixToFusion site).reverse
  let hpositive : 0 < reversed.length := by
    dsimp only [reversed]
    simpa only [SimpleGraph.Walk.length_reverse] using
      lens.bAmbientPrefixToFusion_length_pos hab hac site
  let hcoherent := lens.bAmbientPrefixToFusion_reverse_isPrimalCoherent site
  let tailLift := reversed.cappedPrimalTailLift hpositive hcoherent
    (lens.bExitVertex hab site) (data.defectVertex left)
    (lens.bExitVertex_mem_fusionEdge hab site)
    (by simpa [incidentEdgeFinset] using lens.bRoute.leftIncident)
    (lens.bLeftPrefixReverse_startCap_ne hab hac site)
    (lens.bLeftPrefixReverse_endCap_ne hdata hab hac site)
  let htailNil : ¬tailLift.Nil :=
    reversed.cappedPrimalTailLift_not_nil hpositive hcoherent
      (lens.bExitVertex hab site) (data.defectVertex left)
      (lens.bExitVertex_mem_fusionEdge hab site)
      (by simpa [incidentEdgeFinset] using lens.bRoute.leftIncident)
      (lens.bLeftPrefixReverse_startCap_ne hab hac site)
      (lens.bLeftPrefixReverse_endCap_ne hdata hab hac site)
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · rfl
  · calc
      ((lens.bLeftTerminalRouteSegment hdata hab hac site).firstDart
          (lens.bLeftTerminalRouteSegment_not_nil hdata hab hac site)).edge =
          (tailLift.firstDart htailNil).edge := by
        rw [SimpleGraph.Walk.edge_firstDart,
          SimpleGraph.Walk.edge_firstDart]
        apply congrArg₂ (fun first second => s(first, second))
        · exact (lens.bAmbientPrefixToFusion_reverse_firstJunction
            hab hac site).symm
        · dsimp only [tailLift, reversed, hpositive, hcoherent]
          simp only [SimpleGraph.Walk.snd,
            EvenKempeFusionLens.bLeftTerminalRouteSegment,
            SimpleGraph.Walk.getVert_copy]
      _ = (reversed.getVert 1).1 :=
        reversed.cappedPrimalTailLift_firstDart_edge hpositive hcoherent
          (lens.bExitVertex hab site) (data.defectVertex left)
          (lens.bExitVertex_mem_fusionEdge hab site)
          (by simpa [incidentEdgeFinset] using lens.bRoute.leftIncident)
          (lens.bLeftPrefixReverse_startCap_ne hab hac site)
          (lens.bLeftPrefixReverse_endCap_ne hdata hab hac site)
          htailNil
      _ = (lens.bPreviousVertex site).1.1 := by
        simpa only [reversed, SimpleGraph.Walk.getVert_reverse,
          lens.bAmbientPrefixToFusion_getVert_penultimate hab site]
      _ = (lens.bEntryNeighborDart hab site).edge := by
        symm
        exact lens.bEntryNeighborDart_edge hab site

/-- At the terminal end, reversing the segment's last dart recovers the
canonical left terminal dart. -/
theorem EvenKempeFusionLens.bLeftTerminalRouteSegment_lastDart_symm
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    ((lens.bLeftTerminalRouteSegment hdata hab hac site).lastDart
        (lens.bLeftTerminalRouteSegment_not_nil hdata hab hac site)).symm =
      lens.bRoute.leftTerminalDart := by
  let reversed := (lens.bAmbientPrefixToFusion site).reverse
  let hpositive : 0 < reversed.length := by
    dsimp only [reversed]
    simpa only [SimpleGraph.Walk.length_reverse] using
      lens.bAmbientPrefixToFusion_length_pos hab hac site
  let hcoherent := lens.bAmbientPrefixToFusion_reverse_isPrimalCoherent site
  let tailLift := reversed.cappedPrimalTailLift hpositive hcoherent
    (lens.bExitVertex hab site) (data.defectVertex left)
    (lens.bExitVertex_mem_fusionEdge hab site)
    (by simpa [incidentEdgeFinset] using lens.bRoute.leftIncident)
    (lens.bLeftPrefixReverse_startCap_ne hab hac site)
    (lens.bLeftPrefixReverse_endCap_ne hdata hab hac site)
  let htailNil : ¬tailLift.Nil :=
    reversed.cappedPrimalTailLift_not_nil hpositive hcoherent
      (lens.bExitVertex hab site) (data.defectVertex left)
      (lens.bExitVertex_mem_fusionEdge hab site)
      (by simpa [incidentEdgeFinset] using lens.bRoute.leftIncident)
      (lens.bLeftPrefixReverse_startCap_ne hab hac site)
      (lens.bLeftPrefixReverse_endCap_ne hdata hab hac site)
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · rfl
  · calc
      (((lens.bLeftTerminalRouteSegment hdata hab hac site).lastDart
          (lens.bLeftTerminalRouteSegment_not_nil
            hdata hab hac site)).symm).edge =
          (tailLift.lastDart htailNil).edge := by
        rw [SimpleGraph.Dart.edge_symm,
          SimpleGraph.Walk.edge_lastDart,
          SimpleGraph.Walk.edge_lastDart]
        apply congrArg₂ (fun first second => s(first, second))
        · dsimp only [tailLift, reversed, hpositive, hcoherent]
          simp only [SimpleGraph.Walk.penultimate,
            EvenKempeFusionLens.bLeftTerminalRouteSegment,
            SimpleGraph.Walk.length_copy,
            SimpleGraph.Walk.getVert_copy]
        · rfl
      _ = lens.bRoute.leftEdge.1.1 :=
        reversed.cappedPrimalTailLift_lastDart_edge hpositive hcoherent
          (lens.bExitVertex hab site) (data.defectVertex left)
          (lens.bExitVertex_mem_fusionEdge hab site)
          (by simpa [incidentEdgeFinset] using lens.bRoute.leftIncident)
          (lens.bLeftPrefixReverse_startCap_ne hab hac site)
          (lens.bLeftPrefixReverse_endCap_ne hdata hab hac site)
          htailNil
      _ = lens.bRoute.leftTerminalDart.edge := by
        symm
        exact lens.bRoute.leftTerminalDart_edge

/-- Reversing a prefix of the `(a,c)` route preserves its open primal
coherence. -/
theorem EvenKempeFusionLens.cAmbientPrefixToFusion_reverse_isPrimalCoherent
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.cAmbientPrefixToFusion site).reverse.IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := a) (b := c)
    (walk := (lens.cAmbientPrefixToFusion site).reverse)
    (hpath := (lens.cAmbientPrefixToFusion site).isPath_reverse_iff.mpr
      (lens.cAmbientPrefixToFusion_isPath site))
    (hcolors := by
      intro edge hedge
      have hprefix : edge ∈
          (lens.cAmbientPrefixToFusion site).support := by
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hedge
      have hambient : edge ∈ lens.cRoute.ambientPath.support :=
        lens.cAmbientPrefixToFusion_support_subset site hprefix
      rcases (lens.cRoute.mem_ambientPath_support_iff edge).1 hambient with
        ⟨hcolor, _⟩
      exact hcolor)
    (position := position) hposition

/-- The first junction of a reversed `c`-prefix is its entry endpoint at
the fusion edge. -/
theorem EvenKempeFusionLens.cAmbientPrefixToFusion_reverse_firstJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cAmbientPrefixToFusion site).reverse.lineGraphJunctionAt
        ⟨0, by simpa only [SimpleGraph.Walk.length_reverse] using
          lens.cAmbientPrefixToFusion_length_pos hab hac site⟩ =
      lens.cEntryVertex hac site := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := lens.cEntryVertex_mem_fusionEdge hac site
    simpa only [SimpleGraph.Walk.getVert_zero] using hmem
  · have hmem := lens.cEntryVertex_mem_previousEdge hac site
    simpa only [SimpleGraph.Walk.getVert_reverse,
      lens.cAmbientPrefixToFusion_getVert_penultimate hac site] using hmem

/-- The last junction of a reversed `c`-prefix is the first junction of
the original prefix. -/
theorem EvenKempeFusionLens.cAmbientPrefixToFusion_reverse_lastJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    let reversed := (lens.cAmbientPrefixToFusion site).reverse
    reversed.lineGraphJunctionAt
        ⟨reversed.length - 1,
          Nat.sub_lt (by
            dsimp only [reversed]
            simpa only [SimpleGraph.Walk.length_reverse] using
              lens.cAmbientPrefixToFusion_length_pos hab hac site)
            Nat.zero_lt_one⟩ =
      (lens.cAmbientPrefixToFusion site).lineGraphJunctionAt
        ⟨0, lens.cAmbientPrefixToFusion_length_pos hab hac site⟩ := by
  dsimp only
  exact (lens.cAmbientPrefixToFusion site).lineGraphJunctionAt_reverse_last
    (lens.cAmbientPrefixToFusion_length_pos hab hac site)

/-- The cap opposite the first junction of a reversed `c`-prefix is the
exit endpoint of the fusion edge. -/
theorem EvenKempeFusionLens.cLeftPrefixReverse_startCap_ne
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    lens.cExitVertex hac site ≠
      (lens.cAmbientPrefixToFusion site).reverse.lineGraphJunctionAt
        ⟨0, by simpa only [SimpleGraph.Walk.length_reverse] using
          lens.cAmbientPrefixToFusion_length_pos hab hac site⟩ := by
  rw [lens.cAmbientPrefixToFusion_reverse_firstJunction hab hac site]
  exact (lens.cEntryVertex_ne_cExitVertex hac site).symm

/-- At the retained `c`-terminal cap, the last reversed-prefix junction
is not the boundary defect vertex. -/
theorem EvenKempeFusionLens.cLeftPrefixReverse_endCap_ne
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    let reversed := (lens.cAmbientPrefixToFusion site).reverse
    reversed.lineGraphJunctionAt
        ⟨reversed.length - 1,
          Nat.sub_lt (by
            dsimp only [reversed]
            simpa only [SimpleGraph.Walk.length_reverse] using
              lens.cAmbientPrefixToFusion_length_pos hab hac site)
            Nat.zero_lt_one⟩ ≠
      data.defectVertex left := by
  dsimp only
  rw [lens.cAmbientPrefixToFusion_reverse_lastJunction hab hac site,
    ← lens.leftConnectorVertex_eq_defectVertex]
  exact (lens.leftConnectorVertex_ne_cPrefixFirstJunction
    hdata hab hac site).symm

/-- The retained primal segment from the `c`-entry arm of a fusion site
back to the left route terminal. -/
noncomputable def EvenKempeFusionLens.cLeftTerminalRouteSegment
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    G.Walk (lens.cEntryVertex hac site) (data.defectVertex left) :=
  let reversed := (lens.cAmbientPrefixToFusion site).reverse
  let hpositive : 0 < reversed.length := by
    dsimp only [reversed]
    simpa only [SimpleGraph.Walk.length_reverse] using
      lens.cAmbientPrefixToFusion_length_pos hab hac site
  let tailLift := reversed.cappedPrimalTailLift hpositive
    (lens.cAmbientPrefixToFusion_reverse_isPrimalCoherent site)
    (lens.cExitVertex hac site) (data.defectVertex left)
    (lens.cExitVertex_mem_fusionEdge hac site)
    (by simpa [incidentEdgeFinset] using lens.cRoute.leftIncident)
    (lens.cLeftPrefixReverse_startCap_ne hab hac site)
    (lens.cLeftPrefixReverse_endCap_ne hdata hab hac site)
  tailLift.copy
    (lens.cAmbientPrefixToFusion_reverse_firstJunction hab hac site)
    rfl

@[simp] theorem EvenKempeFusionLens.cLeftTerminalRouteSegment_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cLeftTerminalRouteSegment hdata hab hac site).length =
      (lens.cAmbientPrefixToFusion site).length := by
  simp only [EvenKempeFusionLens.cLeftTerminalRouteSegment,
    SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.cappedPrimalTailLift_length,
    SimpleGraph.Walk.length_reverse]

theorem EvenKempeFusionLens.cLeftTerminalRouteSegment_not_nil
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    ¬(lens.cLeftTerminalRouteSegment hdata hab hac site).Nil := by
  apply SimpleGraph.Walk.not_nil_iff_lt_length.mpr
  rw [lens.cLeftTerminalRouteSegment_length hdata hab hac site]
  exact lens.cAmbientPrefixToFusion_length_pos hab hac site

theorem EvenKempeFusionLens.cLeftTerminalRouteSegment_isTrail
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cLeftTerminalRouteSegment hdata hab hac site).IsTrail := by
  simp only [EvenKempeFusionLens.cLeftTerminalRouteSegment,
    SimpleGraph.Walk.isTrail_copy]
  exact (lens.cAmbientPrefixToFusion site).reverse
    |>.cappedPrimalTailLift_isTrail_of_isPath
      (by simpa only [SimpleGraph.Walk.length_reverse] using
        lens.cAmbientPrefixToFusion_length_pos hab hac site)
      (lens.cAmbientPrefixToFusion_reverse_isPrimalCoherent site)
      ((lens.cAmbientPrefixToFusion site).isPath_reverse_iff.mpr
        (lens.cAmbientPrefixToFusion_isPath site))
      (lens.cExitVertex hac site) (data.defectVertex left)
      (lens.cExitVertex_mem_fusionEdge hac site)
      (by simpa [incidentEdgeFinset] using lens.cRoute.leftIncident)
      (lens.cLeftPrefixReverse_startCap_ne hab hac site)
      (lens.cLeftPrefixReverse_endCap_ne hdata hab hac site)

theorem EvenKempeFusionLens.cLeftTerminalRouteSegment_edges
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cLeftTerminalRouteSegment hdata hab hac site).edges =
      (lens.cAmbientPrefixToFusion site).reverse.support.tail.map
        Subtype.val := by
  simp only [EvenKempeFusionLens.cLeftTerminalRouteSegment,
    SimpleGraph.Walk.edges_copy]
  exact (lens.cAmbientPrefixToFusion site).reverse
    |>.cappedPrimalTailLift_edges_eq_map_support_tail
      (by simpa only [SimpleGraph.Walk.length_reverse] using
        lens.cAmbientPrefixToFusion_length_pos hab hac site)
      (lens.cAmbientPrefixToFusion_reverse_isPrimalCoherent site)
      (lens.cExitVertex hac site) (data.defectVertex left)
      (lens.cExitVertex_mem_fusionEdge hac site)
      (by simpa [incidentEdgeFinset] using lens.cRoute.leftIncident)
      (lens.cLeftPrefixReverse_startCap_ne hab hac site)
      (lens.cLeftPrefixReverse_endCap_ne hdata hab hac site)

/-- The second-channel segment leaves the fusion site along its entry
neighbor dart. -/
theorem EvenKempeFusionLens.cLeftTerminalRouteSegment_firstDart
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cLeftTerminalRouteSegment hdata hab hac site).firstDart
        (lens.cLeftTerminalRouteSegment_not_nil hdata hab hac site) =
      lens.cEntryNeighborDart hac site := by
  let reversed := (lens.cAmbientPrefixToFusion site).reverse
  let hpositive : 0 < reversed.length := by
    dsimp only [reversed]
    simpa only [SimpleGraph.Walk.length_reverse] using
      lens.cAmbientPrefixToFusion_length_pos hab hac site
  let hcoherent := lens.cAmbientPrefixToFusion_reverse_isPrimalCoherent site
  let tailLift := reversed.cappedPrimalTailLift hpositive hcoherent
    (lens.cExitVertex hac site) (data.defectVertex left)
    (lens.cExitVertex_mem_fusionEdge hac site)
    (by simpa [incidentEdgeFinset] using lens.cRoute.leftIncident)
    (lens.cLeftPrefixReverse_startCap_ne hab hac site)
    (lens.cLeftPrefixReverse_endCap_ne hdata hab hac site)
  let htailNil : ¬tailLift.Nil :=
    reversed.cappedPrimalTailLift_not_nil hpositive hcoherent
      (lens.cExitVertex hac site) (data.defectVertex left)
      (lens.cExitVertex_mem_fusionEdge hac site)
      (by simpa [incidentEdgeFinset] using lens.cRoute.leftIncident)
      (lens.cLeftPrefixReverse_startCap_ne hab hac site)
      (lens.cLeftPrefixReverse_endCap_ne hdata hab hac site)
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · rfl
  · calc
      ((lens.cLeftTerminalRouteSegment hdata hab hac site).firstDart
          (lens.cLeftTerminalRouteSegment_not_nil hdata hab hac site)).edge =
          (tailLift.firstDart htailNil).edge := by
        rw [SimpleGraph.Walk.edge_firstDart,
          SimpleGraph.Walk.edge_firstDart]
        apply congrArg₂ (fun first second => s(first, second))
        · exact (lens.cAmbientPrefixToFusion_reverse_firstJunction
            hab hac site).symm
        · dsimp only [tailLift, reversed, hpositive, hcoherent]
          simp only [SimpleGraph.Walk.snd,
            EvenKempeFusionLens.cLeftTerminalRouteSegment,
            SimpleGraph.Walk.getVert_copy]
      _ = (reversed.getVert 1).1 :=
        reversed.cappedPrimalTailLift_firstDart_edge hpositive hcoherent
          (lens.cExitVertex hac site) (data.defectVertex left)
          (lens.cExitVertex_mem_fusionEdge hac site)
          (by simpa [incidentEdgeFinset] using lens.cRoute.leftIncident)
          (lens.cLeftPrefixReverse_startCap_ne hab hac site)
          (lens.cLeftPrefixReverse_endCap_ne hdata hab hac site)
          htailNil
      _ = (lens.cPreviousVertex site).1.1 := by
        simpa only [reversed, SimpleGraph.Walk.getVert_reverse,
          lens.cAmbientPrefixToFusion_getVert_penultimate hac site]
      _ = (lens.cEntryNeighborDart hac site).edge := by
        symm
        exact lens.cEntryNeighborDart_edge hac site

/-- Reversing the second-channel segment's final dart gives its canonical
left terminal dart. -/
theorem EvenKempeFusionLens.cLeftTerminalRouteSegment_lastDart_symm
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    ((lens.cLeftTerminalRouteSegment hdata hab hac site).lastDart
        (lens.cLeftTerminalRouteSegment_not_nil hdata hab hac site)).symm =
      lens.cRoute.leftTerminalDart := by
  let reversed := (lens.cAmbientPrefixToFusion site).reverse
  let hpositive : 0 < reversed.length := by
    dsimp only [reversed]
    simpa only [SimpleGraph.Walk.length_reverse] using
      lens.cAmbientPrefixToFusion_length_pos hab hac site
  let hcoherent := lens.cAmbientPrefixToFusion_reverse_isPrimalCoherent site
  let tailLift := reversed.cappedPrimalTailLift hpositive hcoherent
    (lens.cExitVertex hac site) (data.defectVertex left)
    (lens.cExitVertex_mem_fusionEdge hac site)
    (by simpa [incidentEdgeFinset] using lens.cRoute.leftIncident)
    (lens.cLeftPrefixReverse_startCap_ne hab hac site)
    (lens.cLeftPrefixReverse_endCap_ne hdata hab hac site)
  let htailNil : ¬tailLift.Nil :=
    reversed.cappedPrimalTailLift_not_nil hpositive hcoherent
      (lens.cExitVertex hac site) (data.defectVertex left)
      (lens.cExitVertex_mem_fusionEdge hac site)
      (by simpa [incidentEdgeFinset] using lens.cRoute.leftIncident)
      (lens.cLeftPrefixReverse_startCap_ne hab hac site)
      (lens.cLeftPrefixReverse_endCap_ne hdata hab hac site)
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · rfl
  · calc
      (((lens.cLeftTerminalRouteSegment hdata hab hac site).lastDart
          (lens.cLeftTerminalRouteSegment_not_nil
            hdata hab hac site)).symm).edge =
          (tailLift.lastDart htailNil).edge := by
        rw [SimpleGraph.Dart.edge_symm,
          SimpleGraph.Walk.edge_lastDart,
          SimpleGraph.Walk.edge_lastDart]
        apply congrArg₂ (fun first second => s(first, second))
        · dsimp only [tailLift, reversed, hpositive, hcoherent]
          simp only [SimpleGraph.Walk.penultimate,
            EvenKempeFusionLens.cLeftTerminalRouteSegment,
            SimpleGraph.Walk.length_copy,
            SimpleGraph.Walk.getVert_copy]
        · rfl
      _ = lens.cRoute.leftEdge.1.1 :=
        reversed.cappedPrimalTailLift_lastDart_edge hpositive hcoherent
          (lens.cExitVertex hac site) (data.defectVertex left)
          (lens.cExitVertex_mem_fusionEdge hac site)
          (by simpa [incidentEdgeFinset] using lens.cRoute.leftIncident)
          (lens.cLeftPrefixReverse_startCap_ne hab hac site)
          (lens.cLeftPrefixReverse_endCap_ne hdata hab hac site)
          htailNil
      _ = lens.cRoute.leftTerminalDart.edge := by
        symm
        exact lens.cRoute.leftTerminalDart_edge

/-- The ambient `(a,b)` route suffix beginning at a fusion site. -/
noncomputable def EvenKempeFusionLens.bAmbientSuffixFromFusion
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    G.lineGraph.Walk site.1 lens.bRoute.rightEdge.1 :=
  (lens.bRoute.ambientPath.drop (lens.bFusionPathIndex site)).copy
    (by
      rw [lens.bRoute.ambientPath_getVert]
      exact congrArg Subtype.val
        (lens.bRoute_getVert_fusionPathIndex site))
    rfl

@[simp] theorem EvenKempeFusionLens.bAmbientSuffixFromFusion_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.bAmbientSuffixFromFusion site).length =
      lens.bRoute.path.length - lens.bFusionPathIndex site := by
  simp only [EvenKempeFusionLens.bAmbientSuffixFromFusion,
    SimpleGraph.Walk.length_copy, SimpleGraph.Walk.drop_length,
    EvenKempePortPath.ambientPath_length]

theorem EvenKempeFusionLens.bAmbientSuffixFromFusion_length_pos
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    0 < (lens.bAmbientSuffixFromFusion site).length := by
  rw [lens.bAmbientSuffixFromFusion_length]
  exact Nat.sub_pos_of_lt (lens.bFusionPathIndex_bounds hab site).2

@[simp] theorem EvenKempeFusionLens.bAmbientSuffixFromFusion_getVert
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) (position : Nat) :
    (lens.bAmbientSuffixFromFusion site).getVert position =
      lens.bRoute.ambientPath.getVert
        (lens.bFusionPathIndex site + position) := by
  simp only [EvenKempeFusionLens.bAmbientSuffixFromFusion,
    SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.drop_getVert]

@[simp] theorem EvenKempeFusionLens.bAmbientSuffixFromFusion_getVert_one
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.bAmbientSuffixFromFusion site).getVert 1 =
      (lens.bNextVertex site).1 := by
  rw [lens.bAmbientSuffixFromFusion_getVert,
    lens.bRoute.ambientPath_getVert]
  rfl

theorem EvenKempeFusionLens.bAmbientSuffixFromFusion_isPath
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.bAmbientSuffixFromFusion site).IsPath := by
  simp only [EvenKempeFusionLens.bAmbientSuffixFromFusion,
    SimpleGraph.Walk.isPath_copy]
  exact lens.bRoute.ambientPath_isPath.drop _

theorem EvenKempeFusionLens.bAmbientSuffixFromFusion_support_subset
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.bAmbientSuffixFromFusion site).support ⊆
      lens.bRoute.ambientPath.support := by
  simpa only [EvenKempeFusionLens.bAmbientSuffixFromFusion,
    SimpleGraph.Walk.support_copy] using
      (lens.bRoute.ambientPath.isSubwalk_drop
        (lens.bFusionPathIndex site)).support_subset

theorem EvenKempeFusionLens.bAmbientSuffixFromFusion_isPrimalCoherent
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.bAmbientSuffixFromFusion site).IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := a) (b := b)
    (walk := lens.bAmbientSuffixFromFusion site)
    (hpath := lens.bAmbientSuffixFromFusion_isPath site)
    (hcolors := by
      intro edge hedge
      have hambient : edge ∈ lens.bRoute.ambientPath.support :=
        lens.bAmbientSuffixFromFusion_support_subset site hedge
      rcases (lens.bRoute.mem_ambientPath_support_iff edge).1 hambient with
        ⟨hcolor, _⟩
      exact hcolor)
    (position := position) hposition

/-- The first junction of the first-channel suffix is its fusion exit
endpoint. -/
theorem EvenKempeFusionLens.bAmbientSuffixFromFusion_firstJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    (lens.bAmbientSuffixFromFusion site).lineGraphJunctionAt
        ⟨0, lens.bAmbientSuffixFromFusion_length_pos hab site⟩ =
      lens.bExitVertex hab site := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := lens.bExitVertex_mem_fusionEdge hab site
    simpa only [SimpleGraph.Walk.getVert_zero] using hmem
  · have hmem := lens.bExitVertex_mem_nextEdge hab site
    simpa only [lens.bAmbientSuffixFromFusion_getVert_one site] using hmem

/-- A route suffix has the same final primal junction as the full route. -/
theorem EvenKempeFusionLens.bAmbientSuffixFromFusion_lastJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    (lens.bAmbientSuffixFromFusion site).lineGraphJunctionAt
        ⟨(lens.bAmbientSuffixFromFusion site).length - 1,
          Nat.sub_lt (lens.bAmbientSuffixFromFusion_length_pos hab site)
            Nat.zero_lt_one⟩ =
      lens.bRoute.ambientPath.lineGraphJunctionAt
        ⟨lens.bRoute.ambientPath.length - 1,
          Nat.sub_lt (by
            rw [EvenKempePortPath.ambientPath_length]
            have hbounds := lens.bFusionPathIndex_bounds hab site
            omega) Nat.zero_lt_one⟩ := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := lens.bRoute.ambientPath.lineGraphJunctionAt_mem_left
      ⟨lens.bRoute.ambientPath.length - 1, by
        rw [EvenKempePortPath.ambientPath_length]
        have hbounds := lens.bFusionPathIndex_bounds hab site
        omega⟩
    have hbounds := lens.bFusionPathIndex_bounds hab site
    have hindex : lens.bFusionPathIndex site +
        (lens.bRoute.path.length - lens.bFusionPathIndex site - 1) =
      lens.bRoute.path.length - 1 := by omega
    simpa only [lens.bAmbientSuffixFromFusion_getVert,
      lens.bAmbientSuffixFromFusion_length,
      EvenKempePortPath.ambientPath_length, hindex] using hmem
  · have hmem := lens.bRoute.ambientPath.lineGraphJunctionAt_mem_right
      ⟨lens.bRoute.ambientPath.length - 1, by
        rw [EvenKempePortPath.ambientPath_length]
        have hbounds := lens.bFusionPathIndex_bounds hab site
        omega⟩
    have hbounds := lens.bFusionPathIndex_bounds hab site
    have hindex : lens.bFusionPathIndex site +
        (lens.bRoute.path.length - lens.bFusionPathIndex site - 1 + 1) =
      lens.bRoute.path.length := by omega
    have hlast : lens.bRoute.path.length - 1 + 1 =
        lens.bRoute.path.length := by omega
    simpa only [lens.bAmbientSuffixFromFusion_getVert,
      lens.bAmbientSuffixFromFusion_length,
      EvenKempePortPath.ambientPath_length, hindex, hlast] using hmem

/-- The deleted cap at the right-going `b` suffix is the fusion edge. -/
theorem EvenKempeFusionLens.bRightSuffix_startCap_ne
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    lens.bEntryVertex hab site ≠
      (lens.bAmbientSuffixFromFusion site).lineGraphJunctionAt
        ⟨0, lens.bAmbientSuffixFromFusion_length_pos hab site⟩ := by
  rw [lens.bAmbientSuffixFromFusion_firstJunction hab site]
  exact lens.bEntryVertex_ne_bExitVertex hab site

/-- The retained right terminal cap meets the suffix at the non-defect
endpoint of its terminal edge. -/
theorem EvenKempeFusionLens.bRightSuffix_endCap_ne
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.bAmbientSuffixFromFusion site).lineGraphJunctionAt
        ⟨(lens.bAmbientSuffixFromFusion site).length - 1,
          Nat.sub_lt (lens.bAmbientSuffixFromFusion_length_pos hab site)
            Nat.zero_lt_one⟩ ≠
      data.defectVertex right := by
  rw [lens.bAmbientSuffixFromFusion_lastJunction hab site,
    ← lens.rightConnectorVertex_eq_defectVertex]
  apply lens.bRouteLastJunction_ne_rightConnectorVertex hdata hab hac
  rw [EvenKempePortPath.ambientPath_length]
  have hbounds := lens.bFusionPathIndex_bounds hab site
  omega

/-- The retained primal segment from the `b`-exit arm of a fusion site
to the right route terminal. -/
noncomputable def EvenKempeFusionLens.bRightTerminalRouteSegment
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    G.Walk (lens.bExitVertex hab site) (data.defectVertex right) :=
  let suffix := lens.bAmbientSuffixFromFusion site
  let hpositive : 0 < suffix.length :=
    lens.bAmbientSuffixFromFusion_length_pos hab site
  let tailLift := suffix.cappedPrimalTailLift hpositive
    (lens.bAmbientSuffixFromFusion_isPrimalCoherent site)
    (lens.bEntryVertex hab site) (data.defectVertex right)
    (lens.bEntryVertex_mem_fusionEdge hab site)
    (by simpa [incidentEdgeFinset] using lens.bRoute.rightIncident)
    (lens.bRightSuffix_startCap_ne hab site)
    (lens.bRightSuffix_endCap_ne hdata hab hac site)
  tailLift.copy
    (lens.bAmbientSuffixFromFusion_firstJunction hab site)
    rfl

@[simp] theorem EvenKempeFusionLens.bRightTerminalRouteSegment_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.bRightTerminalRouteSegment hdata hab hac site).length =
      (lens.bAmbientSuffixFromFusion site).length := by
  simp only [EvenKempeFusionLens.bRightTerminalRouteSegment,
    SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.cappedPrimalTailLift_length]

theorem EvenKempeFusionLens.bRightTerminalRouteSegment_not_nil
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    ¬(lens.bRightTerminalRouteSegment hdata hab hac site).Nil := by
  apply SimpleGraph.Walk.not_nil_iff_lt_length.mpr
  rw [lens.bRightTerminalRouteSegment_length hdata hab hac site]
  exact lens.bAmbientSuffixFromFusion_length_pos hab site

theorem EvenKempeFusionLens.bRightTerminalRouteSegment_isTrail
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.bRightTerminalRouteSegment hdata hab hac site).IsTrail := by
  simp only [EvenKempeFusionLens.bRightTerminalRouteSegment,
    SimpleGraph.Walk.isTrail_copy]
  exact (lens.bAmbientSuffixFromFusion site)
    |>.cappedPrimalTailLift_isTrail_of_isPath
      (lens.bAmbientSuffixFromFusion_length_pos hab site)
      (lens.bAmbientSuffixFromFusion_isPrimalCoherent site)
      (lens.bAmbientSuffixFromFusion_isPath site)
      (lens.bEntryVertex hab site) (data.defectVertex right)
      (lens.bEntryVertex_mem_fusionEdge hab site)
      (by simpa [incidentEdgeFinset] using lens.bRoute.rightIncident)
      (lens.bRightSuffix_startCap_ne hab site)
      (lens.bRightSuffix_endCap_ne hdata hab hac site)

theorem EvenKempeFusionLens.bRightTerminalRouteSegment_edges
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.bRightTerminalRouteSegment hdata hab hac site).edges =
      (lens.bAmbientSuffixFromFusion site).support.tail.map
        Subtype.val := by
  simp only [EvenKempeFusionLens.bRightTerminalRouteSegment,
    SimpleGraph.Walk.edges_copy]
  exact (lens.bAmbientSuffixFromFusion site)
    |>.cappedPrimalTailLift_edges_eq_map_support_tail
      (lens.bAmbientSuffixFromFusion_length_pos hab site)
      (lens.bAmbientSuffixFromFusion_isPrimalCoherent site)
      (lens.bEntryVertex hab site) (data.defectVertex right)
      (lens.bEntryVertex_mem_fusionEdge hab site)
      (by simpa [incidentEdgeFinset] using lens.bRoute.rightIncident)
      (lens.bRightSuffix_startCap_ne hab site)
      (lens.bRightSuffix_endCap_ne hdata hab hac site)

/-- The right-going first-channel segment starts on the fusion exit
neighbor dart. -/
theorem EvenKempeFusionLens.bRightTerminalRouteSegment_firstDart
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.bRightTerminalRouteSegment hdata hab hac site).firstDart
        (lens.bRightTerminalRouteSegment_not_nil hdata hab hac site) =
      lens.bExitNeighborDart hab site := by
  let suffix := lens.bAmbientSuffixFromFusion site
  let hpositive : 0 < suffix.length :=
    lens.bAmbientSuffixFromFusion_length_pos hab site
  let hcoherent := lens.bAmbientSuffixFromFusion_isPrimalCoherent site
  let tailLift := suffix.cappedPrimalTailLift hpositive hcoherent
    (lens.bEntryVertex hab site) (data.defectVertex right)
    (lens.bEntryVertex_mem_fusionEdge hab site)
    (by simpa [incidentEdgeFinset] using lens.bRoute.rightIncident)
    (lens.bRightSuffix_startCap_ne hab site)
    (lens.bRightSuffix_endCap_ne hdata hab hac site)
  let htailNil : ¬tailLift.Nil :=
    suffix.cappedPrimalTailLift_not_nil hpositive hcoherent
      (lens.bEntryVertex hab site) (data.defectVertex right)
      (lens.bEntryVertex_mem_fusionEdge hab site)
      (by simpa [incidentEdgeFinset] using lens.bRoute.rightIncident)
      (lens.bRightSuffix_startCap_ne hab site)
      (lens.bRightSuffix_endCap_ne hdata hab hac site)
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · rfl
  · calc
      ((lens.bRightTerminalRouteSegment hdata hab hac site).firstDart
          (lens.bRightTerminalRouteSegment_not_nil hdata hab hac site)).edge =
          (tailLift.firstDart htailNil).edge := by
        rw [SimpleGraph.Walk.edge_firstDart,
          SimpleGraph.Walk.edge_firstDart]
        apply congrArg₂ (fun first second => s(first, second))
        · exact (lens.bAmbientSuffixFromFusion_firstJunction
            hab site).symm
        · dsimp only [tailLift, suffix, hpositive, hcoherent]
          simp only [SimpleGraph.Walk.snd,
            EvenKempeFusionLens.bRightTerminalRouteSegment,
            SimpleGraph.Walk.getVert_copy]
      _ = (suffix.getVert 1).1 :=
        suffix.cappedPrimalTailLift_firstDart_edge hpositive hcoherent
          (lens.bEntryVertex hab site) (data.defectVertex right)
          (lens.bEntryVertex_mem_fusionEdge hab site)
          (by simpa [incidentEdgeFinset] using lens.bRoute.rightIncident)
          (lens.bRightSuffix_startCap_ne hab site)
          (lens.bRightSuffix_endCap_ne hdata hab hac site)
          htailNil
      _ = (lens.bNextVertex site).1.1 := by
        simpa only [suffix,
          lens.bAmbientSuffixFromFusion_getVert_one site]
      _ = (lens.bExitNeighborDart hab site).edge := by
        symm
        exact lens.bExitNeighborDart_edge hab site

/-- Reversing the right-going first-channel segment's final dart gives
the canonical right terminal dart. -/
theorem EvenKempeFusionLens.bRightTerminalRouteSegment_lastDart_symm
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    ((lens.bRightTerminalRouteSegment hdata hab hac site).lastDart
        (lens.bRightTerminalRouteSegment_not_nil hdata hab hac site)).symm =
      lens.bRoute.rightTerminalDart := by
  let suffix := lens.bAmbientSuffixFromFusion site
  let hpositive : 0 < suffix.length :=
    lens.bAmbientSuffixFromFusion_length_pos hab site
  let hcoherent := lens.bAmbientSuffixFromFusion_isPrimalCoherent site
  let tailLift := suffix.cappedPrimalTailLift hpositive hcoherent
    (lens.bEntryVertex hab site) (data.defectVertex right)
    (lens.bEntryVertex_mem_fusionEdge hab site)
    (by simpa [incidentEdgeFinset] using lens.bRoute.rightIncident)
    (lens.bRightSuffix_startCap_ne hab site)
    (lens.bRightSuffix_endCap_ne hdata hab hac site)
  let htailNil : ¬tailLift.Nil :=
    suffix.cappedPrimalTailLift_not_nil hpositive hcoherent
      (lens.bEntryVertex hab site) (data.defectVertex right)
      (lens.bEntryVertex_mem_fusionEdge hab site)
      (by simpa [incidentEdgeFinset] using lens.bRoute.rightIncident)
      (lens.bRightSuffix_startCap_ne hab site)
      (lens.bRightSuffix_endCap_ne hdata hab hac site)
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · rfl
  · calc
      (((lens.bRightTerminalRouteSegment hdata hab hac site).lastDart
          (lens.bRightTerminalRouteSegment_not_nil
            hdata hab hac site)).symm).edge =
          (tailLift.lastDart htailNil).edge := by
        rw [SimpleGraph.Dart.edge_symm,
          SimpleGraph.Walk.edge_lastDart,
          SimpleGraph.Walk.edge_lastDart]
        apply congrArg₂ (fun first second => s(first, second))
        · dsimp only [tailLift, suffix, hpositive, hcoherent]
          simp only [SimpleGraph.Walk.penultimate,
            EvenKempeFusionLens.bRightTerminalRouteSegment,
            SimpleGraph.Walk.length_copy,
            SimpleGraph.Walk.getVert_copy]
        · rfl
      _ = lens.bRoute.rightEdge.1.1 :=
        suffix.cappedPrimalTailLift_lastDart_edge hpositive hcoherent
          (lens.bEntryVertex hab site) (data.defectVertex right)
          (lens.bEntryVertex_mem_fusionEdge hab site)
          (by simpa [incidentEdgeFinset] using lens.bRoute.rightIncident)
          (lens.bRightSuffix_startCap_ne hab site)
          (lens.bRightSuffix_endCap_ne hdata hab hac site)
          htailNil
      _ = lens.bRoute.rightTerminalDart.edge := by
        symm
        exact lens.bRoute.rightTerminalDart_edge

/-- The ambient `(a,c)` route suffix beginning at a fusion site. -/
noncomputable def EvenKempeFusionLens.cAmbientSuffixFromFusion
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    G.lineGraph.Walk site.1 lens.cRoute.rightEdge.1 :=
  (lens.cRoute.ambientPath.drop (lens.cFusionPathIndex site)).copy
    (by
      rw [lens.cRoute.ambientPath_getVert]
      exact congrArg Subtype.val
        (lens.cRoute_getVert_fusionPathIndex site))
    rfl

@[simp] theorem EvenKempeFusionLens.cAmbientSuffixFromFusion_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.cAmbientSuffixFromFusion site).length =
      lens.cRoute.path.length - lens.cFusionPathIndex site := by
  simp only [EvenKempeFusionLens.cAmbientSuffixFromFusion,
    SimpleGraph.Walk.length_copy, SimpleGraph.Walk.drop_length,
    EvenKempePortPath.ambientPath_length]

theorem EvenKempeFusionLens.cAmbientSuffixFromFusion_length_pos
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    0 < (lens.cAmbientSuffixFromFusion site).length := by
  rw [lens.cAmbientSuffixFromFusion_length]
  exact Nat.sub_pos_of_lt (lens.cFusionPathIndex_bounds hac site).2

@[simp] theorem EvenKempeFusionLens.cAmbientSuffixFromFusion_getVert
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) (position : Nat) :
    (lens.cAmbientSuffixFromFusion site).getVert position =
      lens.cRoute.ambientPath.getVert
        (lens.cFusionPathIndex site + position) := by
  simp only [EvenKempeFusionLens.cAmbientSuffixFromFusion,
    SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.drop_getVert]

@[simp] theorem EvenKempeFusionLens.cAmbientSuffixFromFusion_getVert_one
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.cAmbientSuffixFromFusion site).getVert 1 =
      (lens.cNextVertex site).1 := by
  rw [lens.cAmbientSuffixFromFusion_getVert,
    lens.cRoute.ambientPath_getVert]
  rfl

theorem EvenKempeFusionLens.cAmbientSuffixFromFusion_isPath
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.cAmbientSuffixFromFusion site).IsPath := by
  simp only [EvenKempeFusionLens.cAmbientSuffixFromFusion,
    SimpleGraph.Walk.isPath_copy]
  exact lens.cRoute.ambientPath_isPath.drop _

theorem EvenKempeFusionLens.cAmbientSuffixFromFusion_support_subset
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.cAmbientSuffixFromFusion site).support ⊆
      lens.cRoute.ambientPath.support := by
  simpa only [EvenKempeFusionLens.cAmbientSuffixFromFusion,
    SimpleGraph.Walk.support_copy] using
      (lens.cRoute.ambientPath.isSubwalk_drop
        (lens.cFusionPathIndex site)).support_subset

theorem EvenKempeFusionLens.cAmbientSuffixFromFusion_isPrimalCoherent
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.cAmbientSuffixFromFusion site).IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := a) (b := c)
    (walk := lens.cAmbientSuffixFromFusion site)
    (hpath := lens.cAmbientSuffixFromFusion_isPath site)
    (hcolors := by
      intro edge hedge
      have hambient : edge ∈ lens.cRoute.ambientPath.support :=
        lens.cAmbientSuffixFromFusion_support_subset site hedge
      rcases (lens.cRoute.mem_ambientPath_support_iff edge).1 hambient with
        ⟨hcolor, _⟩
      exact hcolor)
    (position := position) hposition

/-- The first junction of the second-channel suffix is its fusion exit
endpoint. -/
theorem EvenKempeFusionLens.cAmbientSuffixFromFusion_firstJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cAmbientSuffixFromFusion site).lineGraphJunctionAt
        ⟨0, lens.cAmbientSuffixFromFusion_length_pos hac site⟩ =
      lens.cExitVertex hac site := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := lens.cExitVertex_mem_fusionEdge hac site
    simpa only [SimpleGraph.Walk.getVert_zero] using hmem
  · have hmem := lens.cExitVertex_mem_nextEdge hac site
    simpa only [lens.cAmbientSuffixFromFusion_getVert_one site] using hmem

/-- A second-channel suffix has the same final primal junction as the full
route. -/
theorem EvenKempeFusionLens.cAmbientSuffixFromFusion_lastJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cAmbientSuffixFromFusion site).lineGraphJunctionAt
        ⟨(lens.cAmbientSuffixFromFusion site).length - 1,
          Nat.sub_lt (lens.cAmbientSuffixFromFusion_length_pos hac site)
            Nat.zero_lt_one⟩ =
      lens.cRoute.ambientPath.lineGraphJunctionAt
        ⟨lens.cRoute.ambientPath.length - 1,
          Nat.sub_lt (by
            rw [EvenKempePortPath.ambientPath_length]
            have hbounds := lens.cFusionPathIndex_bounds hac site
            omega) Nat.zero_lt_one⟩ := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := lens.cRoute.ambientPath.lineGraphJunctionAt_mem_left
      ⟨lens.cRoute.ambientPath.length - 1, by
        rw [EvenKempePortPath.ambientPath_length]
        have hbounds := lens.cFusionPathIndex_bounds hac site
        omega⟩
    have hbounds := lens.cFusionPathIndex_bounds hac site
    have hindex : lens.cFusionPathIndex site +
        (lens.cRoute.path.length - lens.cFusionPathIndex site - 1) =
      lens.cRoute.path.length - 1 := by omega
    simpa only [lens.cAmbientSuffixFromFusion_getVert,
      lens.cAmbientSuffixFromFusion_length,
      EvenKempePortPath.ambientPath_length, hindex] using hmem
  · have hmem := lens.cRoute.ambientPath.lineGraphJunctionAt_mem_right
      ⟨lens.cRoute.ambientPath.length - 1, by
        rw [EvenKempePortPath.ambientPath_length]
        have hbounds := lens.cFusionPathIndex_bounds hac site
        omega⟩
    have hbounds := lens.cFusionPathIndex_bounds hac site
    have hindex : lens.cFusionPathIndex site +
        (lens.cRoute.path.length - lens.cFusionPathIndex site - 1 + 1) =
      lens.cRoute.path.length := by omega
    have hlast : lens.cRoute.path.length - 1 + 1 =
        lens.cRoute.path.length := by omega
    simpa only [lens.cAmbientSuffixFromFusion_getVert,
      lens.cAmbientSuffixFromFusion_length,
      EvenKempePortPath.ambientPath_length, hindex, hlast] using hmem

/-- The deleted cap at the right-going `c` suffix is the fusion edge. -/
theorem EvenKempeFusionLens.cRightSuffix_startCap_ne
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    lens.cEntryVertex hac site ≠
      (lens.cAmbientSuffixFromFusion site).lineGraphJunctionAt
        ⟨0, lens.cAmbientSuffixFromFusion_length_pos hac site⟩ := by
  rw [lens.cAmbientSuffixFromFusion_firstJunction hac site]
  exact lens.cEntryVertex_ne_cExitVertex hac site

/-- The retained right `c`-terminal cap meets the suffix away from the
defect endpoint. -/
theorem EvenKempeFusionLens.cRightSuffix_endCap_ne
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cAmbientSuffixFromFusion site).lineGraphJunctionAt
        ⟨(lens.cAmbientSuffixFromFusion site).length - 1,
          Nat.sub_lt (lens.cAmbientSuffixFromFusion_length_pos hac site)
            Nat.zero_lt_one⟩ ≠
      data.defectVertex right := by
  rw [lens.cAmbientSuffixFromFusion_lastJunction hac site,
    ← lens.rightConnectorVertex_eq_defectVertex]
  apply lens.cRouteLastJunction_ne_rightConnectorVertex hdata hab hac
  rw [EvenKempePortPath.ambientPath_length]
  have hbounds := lens.cFusionPathIndex_bounds hac site
  omega

/-- The retained primal segment from the `c`-exit arm of a fusion site
to the right route terminal. -/
noncomputable def EvenKempeFusionLens.cRightTerminalRouteSegment
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    G.Walk (lens.cExitVertex hac site) (data.defectVertex right) :=
  let suffix := lens.cAmbientSuffixFromFusion site
  let hpositive : 0 < suffix.length :=
    lens.cAmbientSuffixFromFusion_length_pos hac site
  let tailLift := suffix.cappedPrimalTailLift hpositive
    (lens.cAmbientSuffixFromFusion_isPrimalCoherent site)
    (lens.cEntryVertex hac site) (data.defectVertex right)
    (lens.cEntryVertex_mem_fusionEdge hac site)
    (by simpa [incidentEdgeFinset] using lens.cRoute.rightIncident)
    (lens.cRightSuffix_startCap_ne hac site)
    (lens.cRightSuffix_endCap_ne hdata hab hac site)
  tailLift.copy
    (lens.cAmbientSuffixFromFusion_firstJunction hac site)
    rfl

@[simp] theorem EvenKempeFusionLens.cRightTerminalRouteSegment_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cRightTerminalRouteSegment hdata hab hac site).length =
      (lens.cAmbientSuffixFromFusion site).length := by
  simp only [EvenKempeFusionLens.cRightTerminalRouteSegment,
    SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.cappedPrimalTailLift_length]

theorem EvenKempeFusionLens.cRightTerminalRouteSegment_not_nil
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    ¬(lens.cRightTerminalRouteSegment hdata hab hac site).Nil := by
  apply SimpleGraph.Walk.not_nil_iff_lt_length.mpr
  rw [lens.cRightTerminalRouteSegment_length hdata hab hac site]
  exact lens.cAmbientSuffixFromFusion_length_pos hac site

theorem EvenKempeFusionLens.cRightTerminalRouteSegment_isTrail
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cRightTerminalRouteSegment hdata hab hac site).IsTrail := by
  simp only [EvenKempeFusionLens.cRightTerminalRouteSegment,
    SimpleGraph.Walk.isTrail_copy]
  exact (lens.cAmbientSuffixFromFusion site)
    |>.cappedPrimalTailLift_isTrail_of_isPath
      (lens.cAmbientSuffixFromFusion_length_pos hac site)
      (lens.cAmbientSuffixFromFusion_isPrimalCoherent site)
      (lens.cAmbientSuffixFromFusion_isPath site)
      (lens.cEntryVertex hac site) (data.defectVertex right)
      (lens.cEntryVertex_mem_fusionEdge hac site)
      (by simpa [incidentEdgeFinset] using lens.cRoute.rightIncident)
      (lens.cRightSuffix_startCap_ne hac site)
      (lens.cRightSuffix_endCap_ne hdata hab hac site)

theorem EvenKempeFusionLens.cRightTerminalRouteSegment_edges
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cRightTerminalRouteSegment hdata hab hac site).edges =
      (lens.cAmbientSuffixFromFusion site).support.tail.map
        Subtype.val := by
  simp only [EvenKempeFusionLens.cRightTerminalRouteSegment,
    SimpleGraph.Walk.edges_copy]
  exact (lens.cAmbientSuffixFromFusion site)
    |>.cappedPrimalTailLift_edges_eq_map_support_tail
      (lens.cAmbientSuffixFromFusion_length_pos hac site)
      (lens.cAmbientSuffixFromFusion_isPrimalCoherent site)
      (lens.cEntryVertex hac site) (data.defectVertex right)
      (lens.cEntryVertex_mem_fusionEdge hac site)
      (by simpa [incidentEdgeFinset] using lens.cRoute.rightIncident)
      (lens.cRightSuffix_startCap_ne hac site)
      (lens.cRightSuffix_endCap_ne hdata hab hac site)

/-- The right-going second-channel segment starts on the fusion exit
neighbor dart. -/
theorem EvenKempeFusionLens.cRightTerminalRouteSegment_firstDart
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cRightTerminalRouteSegment hdata hab hac site).firstDart
        (lens.cRightTerminalRouteSegment_not_nil hdata hab hac site) =
      lens.cExitNeighborDart hac site := by
  let suffix := lens.cAmbientSuffixFromFusion site
  let hpositive : 0 < suffix.length :=
    lens.cAmbientSuffixFromFusion_length_pos hac site
  let hcoherent := lens.cAmbientSuffixFromFusion_isPrimalCoherent site
  let tailLift := suffix.cappedPrimalTailLift hpositive hcoherent
    (lens.cEntryVertex hac site) (data.defectVertex right)
    (lens.cEntryVertex_mem_fusionEdge hac site)
    (by simpa [incidentEdgeFinset] using lens.cRoute.rightIncident)
    (lens.cRightSuffix_startCap_ne hac site)
    (lens.cRightSuffix_endCap_ne hdata hab hac site)
  let htailNil : ¬tailLift.Nil :=
    suffix.cappedPrimalTailLift_not_nil hpositive hcoherent
      (lens.cEntryVertex hac site) (data.defectVertex right)
      (lens.cEntryVertex_mem_fusionEdge hac site)
      (by simpa [incidentEdgeFinset] using lens.cRoute.rightIncident)
      (lens.cRightSuffix_startCap_ne hac site)
      (lens.cRightSuffix_endCap_ne hdata hab hac site)
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · rfl
  · calc
      ((lens.cRightTerminalRouteSegment hdata hab hac site).firstDart
          (lens.cRightTerminalRouteSegment_not_nil hdata hab hac site)).edge =
          (tailLift.firstDart htailNil).edge := by
        rw [SimpleGraph.Walk.edge_firstDart,
          SimpleGraph.Walk.edge_firstDart]
        apply congrArg₂ (fun first second => s(first, second))
        · exact (lens.cAmbientSuffixFromFusion_firstJunction
            hac site).symm
        · dsimp only [tailLift, suffix, hpositive, hcoherent]
          simp only [SimpleGraph.Walk.snd,
            EvenKempeFusionLens.cRightTerminalRouteSegment,
            SimpleGraph.Walk.getVert_copy]
      _ = (suffix.getVert 1).1 :=
        suffix.cappedPrimalTailLift_firstDart_edge hpositive hcoherent
          (lens.cEntryVertex hac site) (data.defectVertex right)
          (lens.cEntryVertex_mem_fusionEdge hac site)
          (by simpa [incidentEdgeFinset] using lens.cRoute.rightIncident)
          (lens.cRightSuffix_startCap_ne hac site)
          (lens.cRightSuffix_endCap_ne hdata hab hac site)
          htailNil
      _ = (lens.cNextVertex site).1.1 := by
        simpa only [suffix,
          lens.cAmbientSuffixFromFusion_getVert_one site]
      _ = (lens.cExitNeighborDart hac site).edge := by
        symm
        exact lens.cExitNeighborDart_edge hac site

/-- Reversing the right-going second-channel segment's final dart gives
the canonical right terminal dart. -/
theorem EvenKempeFusionLens.cRightTerminalRouteSegment_lastDart_symm
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    ((lens.cRightTerminalRouteSegment hdata hab hac site).lastDart
        (lens.cRightTerminalRouteSegment_not_nil hdata hab hac site)).symm =
      lens.cRoute.rightTerminalDart := by
  let suffix := lens.cAmbientSuffixFromFusion site
  let hpositive : 0 < suffix.length :=
    lens.cAmbientSuffixFromFusion_length_pos hac site
  let hcoherent := lens.cAmbientSuffixFromFusion_isPrimalCoherent site
  let tailLift := suffix.cappedPrimalTailLift hpositive hcoherent
    (lens.cEntryVertex hac site) (data.defectVertex right)
    (lens.cEntryVertex_mem_fusionEdge hac site)
    (by simpa [incidentEdgeFinset] using lens.cRoute.rightIncident)
    (lens.cRightSuffix_startCap_ne hac site)
    (lens.cRightSuffix_endCap_ne hdata hab hac site)
  let htailNil : ¬tailLift.Nil :=
    suffix.cappedPrimalTailLift_not_nil hpositive hcoherent
      (lens.cEntryVertex hac site) (data.defectVertex right)
      (lens.cEntryVertex_mem_fusionEdge hac site)
      (by simpa [incidentEdgeFinset] using lens.cRoute.rightIncident)
      (lens.cRightSuffix_startCap_ne hac site)
      (lens.cRightSuffix_endCap_ne hdata hab hac site)
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · rfl
  · calc
      (((lens.cRightTerminalRouteSegment hdata hab hac site).lastDart
          (lens.cRightTerminalRouteSegment_not_nil
            hdata hab hac site)).symm).edge =
          (tailLift.lastDart htailNil).edge := by
        rw [SimpleGraph.Dart.edge_symm,
          SimpleGraph.Walk.edge_lastDart,
          SimpleGraph.Walk.edge_lastDart]
        apply congrArg₂ (fun first second => s(first, second))
        · dsimp only [tailLift, suffix, hpositive, hcoherent]
          simp only [SimpleGraph.Walk.penultimate,
            EvenKempeFusionLens.cRightTerminalRouteSegment,
            SimpleGraph.Walk.length_copy,
            SimpleGraph.Walk.getVert_copy]
        · rfl
      _ = lens.cRoute.rightEdge.1.1 :=
        suffix.cappedPrimalTailLift_lastDart_edge hpositive hcoherent
          (lens.cEntryVertex hac site) (data.defectVertex right)
          (lens.cEntryVertex_mem_fusionEdge hac site)
          (by simpa [incidentEdgeFinset] using lens.cRoute.rightIncident)
          (lens.cRightSuffix_startCap_ne hac site)
          (lens.cRightSuffix_endCap_ne hdata hab hac site)
          htailNil
      _ = lens.cRoute.rightTerminalDart.edge := by
        symm
        exact lens.cRoute.rightTerminalDart_edge

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
