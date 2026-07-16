import Mettapedia.GraphTheory.FourColor.GoertzelV24PrimalCoherentCircuitExtraction

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem lineGraphJunctionAt_cons_zero
    {first second last : G.edgeSet}
    (hadj : G.lineGraph.Adj first second)
    (walk : G.lineGraph.Walk second last) :
    (walk.cons hadj).lineGraphJunctionAt
        ⟨0, by simp⟩ = SimpleGraph.lineGraphCommonVertex hadj := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · simpa only [SimpleGraph.Walk.getVert_zero] using
      SimpleGraph.lineGraphCommonVertex_mem_left hadj
  · simpa only [SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero] using
      SimpleGraph.lineGraphCommonVertex_mem_right hadj

theorem lineGraphJunctionAt_cons_succ
    {first second last : G.edgeSet}
    (hadj : G.lineGraph.Adj first second)
    (walk : G.lineGraph.Walk second last)
    (position : Fin walk.length) :
    (walk.cons hadj).lineGraphJunctionAt
        ⟨position.val + 1, by simp⟩ =
      walk.lineGraphJunctionAt position := by
  unfold lineGraphJunctionAt
  congr 1

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

theorem EvenKempeFusionLens.bAmbientPrefixToFusion_length_pos
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    0 < (lens.bAmbientPrefixToFusion site).length := by
  apply SimpleGraph.Walk.not_nil_iff_lt_length.mp
  apply SimpleGraph.Walk.not_nil_of_ne
  intro hedge
  exact (lens.endpoints_not_mem_bFusionSites hab hac).1
    (hedge ▸ site.2)

theorem EvenKempeFusionLens.cAmbientPrefixToFusion_length_pos
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    0 < (lens.cAmbientPrefixToFusion site).length := by
  apply SimpleGraph.Walk.not_nil_iff_lt_length.mp
  apply SimpleGraph.Walk.not_nil_of_ne
  intro hedge
  exact (lens.endpoints_not_mem_bFusionSites hab hac).2.2.1
    (hedge ▸ site.2)

theorem EvenKempeFusionLens.bAmbientPrefixToFusion_length_eq_pathIndex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    (lens.bAmbientPrefixToFusion site).length =
      lens.bFusionPathIndex site := by
  let hsite := ((lens.mem_bFusionSites_iff site.1).1 site.2).1
  have hprefixBound : (lens.bAmbientPrefixToFusion site).length ≤
      lens.bRoute.ambientPath.length :=
    lens.bRoute.ambientPath.length_takeUntil_le_length hsite
  have hindexBound : lens.bFusionPathIndex site ≤
      lens.bRoute.ambientPath.length := by
    have hbounds := lens.bFusionPathIndex_bounds hab site
    rw [lens.bRoute.ambientPath_length]
    omega
  apply lens.bRoute.ambientPath_isPath.getVert_injOn
    (by simpa only [Set.mem_setOf_eq] using hprefixBound)
    (by simpa only [Set.mem_setOf_eq] using hindexBound)
  calc
    lens.bRoute.ambientPath.getVert
          (lens.bAmbientPrefixToFusion site).length = site.1 :=
      lens.bRoute.ambientPath.getVert_length_takeUntil hsite
    _ = lens.bRoute.ambientPath.getVert
          (lens.bFusionPathIndex site) := by
      rw [lens.bRoute.ambientPath_getVert]
      exact congrArg Subtype.val
        (lens.bRoute_getVert_fusionPathIndex site).symm

theorem EvenKempeFusionLens.cAmbientPrefixToFusion_length_eq_pathIndex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cAmbientPrefixToFusion site).length =
      lens.cFusionPathIndex site := by
  let hsite := ((lens.mem_bFusionSites_iff site.1).1 site.2).2
  have hprefixBound : (lens.cAmbientPrefixToFusion site).length ≤
      lens.cRoute.ambientPath.length :=
    lens.cRoute.ambientPath.length_takeUntil_le_length hsite
  have hindexBound : lens.cFusionPathIndex site ≤
      lens.cRoute.ambientPath.length := by
    have hbounds := lens.cFusionPathIndex_bounds hac site
    rw [lens.cRoute.ambientPath_length]
    omega
  apply lens.cRoute.ambientPath_isPath.getVert_injOn
    (by simpa only [Set.mem_setOf_eq] using hprefixBound)
    (by simpa only [Set.mem_setOf_eq] using hindexBound)
  calc
    lens.cRoute.ambientPath.getVert
          (lens.cAmbientPrefixToFusion site).length = site.1 :=
      lens.cRoute.ambientPath.getVert_length_takeUntil hsite
    _ = lens.cRoute.ambientPath.getVert
          (lens.cFusionPathIndex site) := by
      rw [lens.cRoute.ambientPath_getVert]
      exact congrArg Subtype.val
        (lens.cRoute_getVert_fusionPathIndex site).symm

theorem EvenKempeFusionLens.bAmbientPrefixToFusion_getVert_penultimate
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (site : lens.FusionSite) :
    (lens.bAmbientPrefixToFusion site).getVert
        ((lens.bAmbientPrefixToFusion site).length - 1) =
      (lens.bPreviousVertex site).1 := by
  let hsite := ((lens.mem_bFusionSites_iff site.1).1 site.2).1
  calc
    _ = lens.bRoute.ambientPath.getVert
          ((lens.bAmbientPrefixToFusion site).length - 1) :=
      lens.bRoute.ambientPath.getVert_takeUntil hsite (Nat.sub_le _ _)
    _ = lens.bRoute.ambientPath.getVert
          (lens.bFusionPathIndex site - 1) := by
      rw [lens.bAmbientPrefixToFusion_length_eq_pathIndex hab site]
    _ = _ := by
      rw [lens.bRoute.ambientPath_getVert]
      rfl

theorem EvenKempeFusionLens.cAmbientPrefixToFusion_getVert_penultimate
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cAmbientPrefixToFusion site).getVert
        ((lens.cAmbientPrefixToFusion site).length - 1) =
      (lens.cPreviousVertex site).1 := by
  let hsite := ((lens.mem_bFusionSites_iff site.1).1 site.2).2
  calc
    _ = lens.cRoute.ambientPath.getVert
          ((lens.cAmbientPrefixToFusion site).length - 1) :=
      lens.cRoute.ambientPath.getVert_takeUntil hsite (Nat.sub_le _ _)
    _ = lens.cRoute.ambientPath.getVert
          (lens.cFusionPathIndex site - 1) := by
      rw [lens.cAmbientPrefixToFusion_length_eq_pathIndex hac site]
    _ = _ := by
      rw [lens.cRoute.ambientPath_getVert]
      rfl

/-- At a well-formed left port, the two terminal route edges are exactly
the two incident graph edges. -/
theorem EvenKempeFusionLens.leftTerminalEdges_eq_incidentEdgeFinset
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) :
    incidentEdgeFinset G (data.defectVertex left) =
      {lens.bRoute.leftEdge.1, lens.cRoute.leftEdge.1} := by
  have hsubset :
      {lens.bRoute.leftEdge.1, lens.cRoute.leftEdge.1} ⊆
        incidentEdgeFinset G (data.defectVertex left) := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · exact lens.bRoute.leftIncident
    · exact lens.cRoute.leftIncident
  have hpairEq := Finset.eq_of_subset_of_card_le hsubset (by
    rw [hdata.2.1 left, Finset.card_pair lens.leftConnector.ne])
  exact hpairEq.symm

theorem EvenKempeFusionLens.leftConnectorVertex_eq_defectVertex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    SimpleGraph.lineGraphCommonVertex lens.leftConnector =
      data.defectVertex left := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · simpa [incidentEdgeFinset] using lens.bRoute.leftIncident
  · simpa [incidentEdgeFinset] using lens.cRoute.leftIncident

theorem EvenKempeFusionLens.leftConnectorVertex_ne_bPrefixFirstJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c)
    (site : lens.FusionSite) :
    SimpleGraph.lineGraphCommonVertex lens.leftConnector ≠
      (lens.bAmbientPrefixToFusion site).lineGraphJunctionAt
        ⟨0, lens.bAmbientPrefixToFusion_length_pos hab hac site⟩ := by
  intro hjunction
  let bPrefix := lens.bAmbientPrefixToFusion site
  have hnextMem := bPrefix.lineGraphJunctionAt_mem_right
    ⟨0, lens.bAmbientPrefixToFusion_length_pos hab hac site⟩
  have hdefectMem : data.defectVertex left ∈
      ((bPrefix.getVert 1).1 : Sym2 V) := by
    rw [← lens.leftConnectorVertex_eq_defectVertex,
      hjunction]
    exact hnextMem
  have hnextIncident : bPrefix.getVert 1 ∈
      incidentEdgeFinset G (data.defectVertex left) := by
    simpa [incidentEdgeFinset] using hdefectMem
  rw [lens.leftTerminalEdges_eq_incidentEdgeFinset hdata] at hnextIncident
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnextIncident
  rcases hnextIncident with hbLeft | hcLeft
  · have hadj := bPrefix.adj_getVert_succ
        (i := 0) (lens.bAmbientPrefixToFusion_length_pos hab hac site)
    exact hadj.ne (by
      simpa only [SimpleGraph.Walk.getVert_zero] using hbLeft.symm)
  · apply lens.cLeftEdge_not_mem_bAmbientPath_support hab hac
    apply lens.bAmbientPrefixToFusion_support_subset site
    exact hcLeft ▸ bPrefix.getVert_mem_support 1

theorem EvenKempeFusionLens.leftConnectorVertex_ne_cPrefixFirstJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c)
    (site : lens.FusionSite) :
    SimpleGraph.lineGraphCommonVertex lens.leftConnector ≠
      (lens.cAmbientPrefixToFusion site).lineGraphJunctionAt
        ⟨0, lens.cAmbientPrefixToFusion_length_pos hab hac site⟩ := by
  intro hjunction
  let cPrefix := lens.cAmbientPrefixToFusion site
  have hnextMem := cPrefix.lineGraphJunctionAt_mem_right
    ⟨0, lens.cAmbientPrefixToFusion_length_pos hab hac site⟩
  have hdefectMem : data.defectVertex left ∈
      ((cPrefix.getVert 1).1 : Sym2 V) := by
    rw [← lens.leftConnectorVertex_eq_defectVertex,
      hjunction]
    exact hnextMem
  have hnextIncident : cPrefix.getVert 1 ∈
      incidentEdgeFinset G (data.defectVertex left) := by
    simpa [incidentEdgeFinset] using hdefectMem
  rw [lens.leftTerminalEdges_eq_incidentEdgeFinset hdata] at hnextIncident
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnextIncident
  rcases hnextIncident with hbLeft | hcLeft
  · apply lens.bLeftEdge_not_mem_cAmbientPath_support hab hac
    apply lens.cAmbientPrefixToFusion_support_subset site
    exact hbLeft ▸ cPrefix.getVert_mem_support 1
  · have hadj := cPrefix.adj_getVert_succ
        (i := 0) (lens.cAmbientPrefixToFusion_length_pos hab hac site)
    exact hadj.ne (by
      simpa only [SimpleGraph.Walk.getVert_zero] using hcLeft.symm)

theorem EvenKempeFusionLens.bAmbientPrefixToFusion_reverse_isPrimalCoherent
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.bAmbientPrefixToFusion site).reverse.IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := a) (b := b)
    (walk := (lens.bAmbientPrefixToFusion site).reverse)
    (hpath := (lens.bAmbientPrefixToFusion site).isPath_reverse_iff.mpr
      (lens.bAmbientPrefixToFusion_isPath site))
    (hcolors := by
      intro edge hedge
      have hprefix : edge ∈
          (lens.bAmbientPrefixToFusion site).support := by
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hedge
      have hambient : edge ∈ lens.bRoute.ambientPath.support :=
        lens.bAmbientPrefixToFusion_support_subset site hprefix
      rcases (lens.bRoute.mem_ambientPath_support_iff edge).1 hambient with
        ⟨hcolor, _⟩
      exact hcolor)
    (position := position) hposition

theorem EvenKempeFusionLens.cLeftConnectedPrefixToFusion_isPrimalCoherent
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c)
    (site : lens.FusionSite) :
    (lens.cLeftConnectedPrefixToFusion site).IsPrimalCoherent := by
  intro position hposition
  by_cases hzero : position = 0
  · subst position
    let cPrefix := lens.cAmbientPrefixToFusion site
    have hfirst := SimpleGraph.Walk.lineGraphJunctionAt_cons_zero
      lens.leftConnector cPrefix
    have hsecond := SimpleGraph.Walk.lineGraphJunctionAt_cons_succ
      lens.leftConnector cPrefix
      ⟨0, lens.cAmbientPrefixToFusion_length_pos hab hac site⟩
    intro hjunction
    exact (lens.leftConnectorVertex_ne_cPrefixFirstJunction
      hdata hab hac site)
        (hfirst.symm.trans (hjunction.trans hsecond))
  · obtain ⟨previous, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hzero
    have hprevious : previous + 1 <
        (lens.cAmbientPrefixToFusion site).length := by
      simp only [EvenKempeFusionLens.cLeftConnectedPrefixToFusion,
        SimpleGraph.Walk.length_cons] at hposition
      omega
    have hcoherent :=
      SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
        (C := C) (a := a) (b := c)
        (walk := lens.cAmbientPrefixToFusion site)
        (hpath := lens.cAmbientPrefixToFusion_isPath site)
        (hcolors := by
          intro edge hedge
          have hambient : edge ∈ lens.cRoute.ambientPath.support :=
            lens.cAmbientPrefixToFusion_support_subset site hedge
          rcases (lens.cRoute.mem_ambientPath_support_iff edge).1 hambient with
            ⟨hcolor, _⟩
          exact hcolor)
        (position := previous) hprevious
    let cPrefix := lens.cAmbientPrefixToFusion site
    have hfirst := SimpleGraph.Walk.lineGraphJunctionAt_cons_succ
      lens.leftConnector cPrefix ⟨previous, by
        dsimp only [cPrefix]
        omega⟩
    have hsecond := SimpleGraph.Walk.lineGraphJunctionAt_cons_succ
      lens.leftConnector cPrefix ⟨previous + 1, hprevious⟩
    intro hjunction
    exact hcoherent (hfirst.symm.trans (hjunction.trans hsecond))

theorem EvenKempeFusionLens.cLeftConnectedPrefixToFusion_length_pos
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    0 < (lens.cLeftConnectedPrefixToFusion site).length := by
  simp only [lens.cLeftConnectedPrefixToFusion_length]
  omega

theorem EvenKempeFusionLens.cLeftConnectedPrefixToFusion_getVert_penultimate
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.cLeftConnectedPrefixToFusion site).getVert
        ((lens.cLeftConnectedPrefixToFusion site).length - 1) =
      (lens.cPreviousVertex site).1 := by
  let cPrefix := lens.cAmbientPrefixToFusion site
  have hcPositive : 0 < cPrefix.length :=
    lens.cAmbientPrefixToFusion_length_pos hab hac site
  change (cPrefix.cons lens.leftConnector).getVert
      ((cPrefix.cons lens.leftConnector).length - 1) = _
  rw [SimpleGraph.Walk.length_cons]
  have hindex : cPrefix.length + 1 - 1 = cPrefix.length := by omega
  rw [hindex, cPrefix.getVert_cons lens.leftConnector
    (Nat.ne_of_gt hcPositive)]
  exact lens.cAmbientPrefixToFusion_getVert_penultimate hac site

theorem EvenKempeFusionLens.cLeftConnectedPrefixToFusion_lastJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    let connected := lens.cLeftConnectedPrefixToFusion site
    connected.lineGraphJunctionAt
        ⟨connected.length - 1,
          Nat.sub_lt (lens.cLeftConnectedPrefixToFusion_length_pos site)
            Nat.zero_lt_one⟩ =
      lens.cEntryVertex hac site := by
  dsimp only
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := lens.cEntryVertex_mem_previousEdge hac site
    simpa only [lens.cLeftConnectedPrefixToFusion_getVert_penultimate
      hab hac site] using hmem
  · have hmem := lens.cEntryVertex_mem_fusionEdge hac site
    simpa only [Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt
          (lens.cLeftConnectedPrefixToFusion_length_pos site))),
      SimpleGraph.Walk.getVert_length] using hmem

theorem EvenKempeFusionLens.bAmbientPrefixToFusion_reverse_firstJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.bAmbientPrefixToFusion site).reverse.lineGraphJunctionAt
        ⟨0, by simpa only [SimpleGraph.Walk.length_reverse] using
          lens.bAmbientPrefixToFusion_length_pos hab hac site⟩ =
      lens.bEntryVertex hab site := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := lens.bEntryVertex_mem_fusionEdge hab site
    simpa only [SimpleGraph.Walk.getVert_zero] using hmem
  · have hmem := lens.bEntryVertex_mem_previousEdge hab site
    simpa only [SimpleGraph.Walk.getVert_reverse,
      lens.bAmbientPrefixToFusion_getVert_penultimate hab site] using hmem

theorem EvenKempeFusionLens.cLeftConnectedPrefixToFusion_firstJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    (lens.cLeftConnectedPrefixToFusion site).lineGraphJunctionAt
        ⟨0, lens.cLeftConnectedPrefixToFusion_length_pos site⟩ =
      SimpleGraph.lineGraphCommonVertex lens.leftConnector := by
  exact SimpleGraph.Walk.lineGraphJunctionAt_cons_zero
    lens.leftConnector (lens.cAmbientPrefixToFusion site)

theorem EvenKempeFusionLens.bAmbientPrefixToFusion_reverse_lastJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    let reversed := (lens.bAmbientPrefixToFusion site).reverse
    reversed.lineGraphJunctionAt
        ⟨reversed.length - 1,
          Nat.sub_lt (by
            dsimp only [reversed]
            simpa only [SimpleGraph.Walk.length_reverse] using
              lens.bAmbientPrefixToFusion_length_pos hab hac site)
            Nat.zero_lt_one⟩ =
      (lens.bAmbientPrefixToFusion site).lineGraphJunctionAt
        ⟨0, lens.bAmbientPrefixToFusion_length_pos hab hac site⟩ := by
  dsimp only
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem :=
      (lens.bAmbientPrefixToFusion site).lineGraphJunctionAt_mem_right
        ⟨0, lens.bAmbientPrefixToFusion_length_pos hab hac site⟩
    simpa only [SimpleGraph.Walk.length_reverse,
      SimpleGraph.Walk.getVert_reverse,
      Nat.sub_sub_self (Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt
        (lens.bAmbientPrefixToFusion_length_pos hab hac site)))] using hmem
  · have hmem :=
      (lens.bAmbientPrefixToFusion site).lineGraphJunctionAt_mem_left
        ⟨0, lens.bAmbientPrefixToFusion_length_pos hab hac site⟩
    have hindex : (lens.bAmbientPrefixToFusion site).length - 1 + 1 =
        (lens.bAmbientPrefixToFusion site).length :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt
        (lens.bAmbientPrefixToFusion_length_pos hab hac site)))
    simpa only [SimpleGraph.Walk.length_reverse,
      SimpleGraph.Walk.getVert_reverse, hindex, Nat.sub_self,
      SimpleGraph.Walk.getVert_zero] using hmem

/-- The reverse orientation of the prefix-return loop. It follows the
left-connected `(a,c)` prefix to the fusion site and returns along the
reversed `(a,b)` prefix. -/
def EvenKempeFusionLens.fusionSiteLeftReturnOppositeLoop
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (site : lens.FusionSite) :
    G.lineGraph.Walk lens.bRoute.leftEdge.1 lens.bRoute.leftEdge.1 :=
  (lens.cLeftConnectedPrefixToFusion site).append
    (lens.bAmbientPrefixToFusion site).reverse

theorem EvenKempeFusionLens.fusionSiteLeftReturnOppositeLoop_length_lt_closedWalk
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite) :
    (lens.fusionSiteLeftReturnOppositeLoop site).length <
      lens.closedWalk.length := by
  have hshorter := lens.fusionSiteLeftReturnLoop_length_lt_closedWalk
    hab hac site
  rw [EvenKempeFusionLens.fusionSiteLeftReturnLoop,
    SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] at hshorter
  rw [EvenKempeFusionLens.fusionSiteLeftReturnOppositeLoop,
    SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

theorem EvenKempeFusionLens.fusionSiteLeftReturnOppositeLoop_isPrimalCoherentClosed
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c)
    (site : lens.FusionSite)
    (hreturn : lens.ReturnSpliceCoherent hab hac site) :
    (lens.fusionSiteLeftReturnOppositeLoop site).IsPrimalCoherentClosed := by
  rw [EvenKempeFusionLens.fusionSiteLeftReturnOppositeLoop]
  apply SimpleGraph.Walk.IsPrimalCoherent.append_isPrimalCoherentClosed
    (lens.cLeftConnectedPrefixToFusion_isPrimalCoherent
      hdata hab hac site)
    (lens.bAmbientPrefixToFusion_reverse_isPrimalCoherent site)
    (lens.cLeftConnectedPrefixToFusion_length_pos site)
    (by simpa only [SimpleGraph.Walk.length_reverse] using
      lens.bAmbientPrefixToFusion_length_pos hab hac site)
  · simpa only [lens.cLeftConnectedPrefixToFusion_lastJunction
        hab hac site,
      lens.bAmbientPrefixToFusion_reverse_firstJunction
        hab hac site] using hreturn.symm
  · simpa only [lens.bAmbientPrefixToFusion_reverse_lastJunction
        hab hac site,
      lens.cLeftConnectedPrefixToFusion_firstJunction site] using
      (lens.leftConnectorVertex_ne_bPrefixFirstJunction
        hdata hab hac site).symm

/-- A coherent return splice at a well-formed degree-two boundary produces
a strictly shorter primal cycle, even when its line-graph return loop meets
earlier fusion sites. -/
theorem EvenKempeFusionLens.exists_shorter_primalCycle_of_coherentReturn
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c)
    (site : lens.FusionSite)
    (hreturn : lens.ReturnSpliceCoherent hab hac site) :
    ∃ (start : V) (cycle : G.Walk start start),
      cycle.IsCycle ∧ cycle.length < lens.closedWalk.length := by
  let returnLoop := lens.fusionSiteLeftReturnOppositeLoop site
  have hpositive : 0 < returnLoop.length := by
    dsimp only [returnLoop]
    rw [EvenKempeFusionLens.fusionSiteLeftReturnOppositeLoop,
      SimpleGraph.Walk.length_append]
    exact Nat.lt_add_right _ (lens.cLeftConnectedPrefixToFusion_length_pos site)
  have hcoherent : returnLoop.IsPrimalCoherentClosed :=
    lens.fusionSiteLeftReturnOppositeLoop_isPrimalCoherentClosed
      hdata hab hac site hreturn
  rcases returnLoop.exists_primal_isCycle_length_le_of_primalCoherentClosed
      hpositive hcoherent with ⟨start, cycle, hcycle, hlength⟩
  exact ⟨start, cycle, hcycle,
    lt_of_le_of_lt hlength
      (lens.fusionSiteLeftReturnOppositeLoop_length_lt_closedWalk
        hab hac site)⟩

/-- Signed fusion nontriviality now has no residual branch: for a
well-formed degree-two boundary it always yields a strictly shorter primal
circuit. -/
theorem EvenKempeFusionLens.exists_shorter_primalCircuit_of_signedMonodromy_ne_refl
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c)
    (hsigned : lens.signedFusionMonodromy hab hac ≠
      Equiv.refl (Fin lens.fusionSiteCount × Bool)) :
    ∃ (start : V) (circuit : G.Walk start start),
      circuit.IsCircuit ∧ circuit.length < lens.closedWalk.length := by
  rcases lens.exists_shorter_primalCircuit_or_coherentReturn_of_signedMonodromy_ne_refl
      hab hac hsigned with hshorter | hreturn
  · exact hshorter
  · rcases hreturn with ⟨position, _hlineShorter, hcoherent⟩
    rcases lens.exists_shorter_primalCycle_of_coherentReturn
        hdata hab hac (lens.bFusionSiteAt position) hcoherent with
      ⟨start, cycle, hcycle, hcycleShorter⟩
    exact ⟨start, cycle, hcycle.isCircuit, hcycleShorter⟩

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
