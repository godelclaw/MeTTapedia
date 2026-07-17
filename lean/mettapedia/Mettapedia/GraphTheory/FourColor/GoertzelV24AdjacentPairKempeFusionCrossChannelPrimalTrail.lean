import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelCoherence
import Mettapedia.GraphTheory.FourColor.GoertzelV24LineGraphOpenPrimalLift

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossChannelPrimalTrailGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A path leaving through the first terminal family cannot bounce at its
boundary defect when the other terminal edge is absent from its support. -/
theorem EvenKempeFusionLens.leftDefect_ne_firstJunction_of_bTerminal
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) {lastEdge : G.edgeSet}
    (joined : G.lineGraph.Walk lens.bRoute.leftEdge.1 lastEdge)
    (hpositive : 0 < joined.length)
    (hcAbsent : lens.cRoute.leftEdge.1 ∉ joined.support) :
    data.defectVertex left ≠
      joined.lineGraphJunctionAt ⟨0, hpositive⟩ := by
  intro hjunction
  have hnextMem := joined.lineGraphJunctionAt_mem_right ⟨0, hpositive⟩
  have hdefectMem : data.defectVertex left ∈
      ((joined.getVert 1).1 : Sym2 V) := by
    rw [hjunction]
    exact hnextMem
  have hnextIncident : joined.getVert 1 ∈
      incidentEdgeFinset G (data.defectVertex left) := by
    simpa [incidentEdgeFinset] using hdefectMem
  rw [lens.leftTerminalEdges_eq_incidentEdgeFinset hdata] at hnextIncident
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnextIncident
  rcases hnextIncident with hbLeft | hcLeft
  · have hadj := joined.adj_getVert_succ (i := 0) hpositive
    exact hadj.ne (by
      simpa only [joined.getVert_zero] using hbLeft.symm)
  · apply hcAbsent
    exact hcLeft ▸ joined.getVert_mem_support 1

theorem EvenKempeFusionLens.leftDefect_ne_firstJunction_of_cTerminal
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) {lastEdge : G.edgeSet}
    (joined : G.lineGraph.Walk lens.cRoute.leftEdge.1 lastEdge)
    (hpositive : 0 < joined.length)
    (hbAbsent : lens.bRoute.leftEdge.1 ∉ joined.support) :
    data.defectVertex left ≠
      joined.lineGraphJunctionAt ⟨0, hpositive⟩ := by
  intro hjunction
  have hnextMem := joined.lineGraphJunctionAt_mem_right ⟨0, hpositive⟩
  have hdefectMem : data.defectVertex left ∈
      ((joined.getVert 1).1 : Sym2 V) := by
    rw [hjunction]
    exact hnextMem
  have hnextIncident : joined.getVert 1 ∈
      incidentEdgeFinset G (data.defectVertex left) := by
    simpa [incidentEdgeFinset] using hdefectMem
  rw [lens.leftTerminalEdges_eq_incidentEdgeFinset hdata] at hnextIncident
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnextIncident
  rcases hnextIncident with hbLeft | hcLeft
  · apply hbAbsent
    exact hbLeft ▸ joined.getVert_mem_support 1
  · have hadj := joined.adj_getVert_succ (i := 0) hpositive
    exact hadj.ne (by
      simpa only [joined.getVert_zero] using hcLeft.symm)

/-- The symmetric no-bounce statement at the final boundary terminal. -/
theorem EvenKempeFusionLens.lastJunction_ne_leftDefect_of_bTerminal
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) {firstEdge : G.edgeSet}
    (joined : G.lineGraph.Walk firstEdge lens.bRoute.leftEdge.1)
    (hpositive : 0 < joined.length)
    (hcAbsent : lens.cRoute.leftEdge.1 ∉ joined.support) :
    joined.lineGraphJunctionAt
        ⟨joined.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠
      data.defectVertex left := by
  intro hjunction
  let finalPosition : Fin joined.length :=
    ⟨joined.length - 1,
      Nat.sub_lt hpositive Nat.zero_lt_one⟩
  have hpreviousMem := joined.lineGraphJunctionAt_mem_left finalPosition
  have hdefectMem : data.defectVertex left ∈
      ((joined.getVert (joined.length - 1)).1 : Sym2 V) := by
    rw [← hjunction]
    exact hpreviousMem
  have hpreviousIncident : joined.getVert (joined.length - 1) ∈
      incidentEdgeFinset G (data.defectVertex left) := by
    simpa [incidentEdgeFinset] using hdefectMem
  rw [lens.leftTerminalEdges_eq_incidentEdgeFinset hdata] at hpreviousIncident
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpreviousIncident
  rcases hpreviousIncident with hbLeft | hcLeft
  · have hadj := joined.adj_getVert_succ
        (i := joined.length - 1) (by omega)
    exact hadj.ne (by
      have hlast : joined.length - 1 + 1 = joined.length := by omega
      simpa only [hlast, joined.getVert_length] using hbLeft)
  · apply hcAbsent
    exact hcLeft ▸ joined.getVert_mem_support (joined.length - 1)

theorem EvenKempeFusionLens.lastJunction_ne_leftDefect_of_cTerminal
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) {firstEdge : G.edgeSet}
    (joined : G.lineGraph.Walk firstEdge lens.cRoute.leftEdge.1)
    (hpositive : 0 < joined.length)
    (hbAbsent : lens.bRoute.leftEdge.1 ∉ joined.support) :
    joined.lineGraphJunctionAt
        ⟨joined.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠
      data.defectVertex left := by
  intro hjunction
  let finalPosition : Fin joined.length :=
    ⟨joined.length - 1,
      Nat.sub_lt hpositive Nat.zero_lt_one⟩
  have hpreviousMem := joined.lineGraphJunctionAt_mem_left finalPosition
  have hdefectMem : data.defectVertex left ∈
      ((joined.getVert (joined.length - 1)).1 : Sym2 V) := by
    rw [← hjunction]
    exact hpreviousMem
  have hpreviousIncident : joined.getVert (joined.length - 1) ∈
      incidentEdgeFinset G (data.defectVertex left) := by
    simpa [incidentEdgeFinset] using hdefectMem
  rw [lens.leftTerminalEdges_eq_incidentEdgeFinset hdata] at hpreviousIncident
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpreviousIncident
  rcases hpreviousIncident with hbLeft | hcLeft
  · apply hbAbsent
    exact hbLeft ▸ joined.getVert_mem_support (joined.length - 1)
  · have hadj := joined.adj_getVert_succ
        (i := joined.length - 1) (by omega)
    exact hadj.ne (by
      have hlast : joined.length - 1 + 1 = joined.length := by omega
      simpa only [hlast, joined.getVert_length] using hcLeft)

/-- A nonempty first cross channel lifts to a primal trail that contains
every edge of a selected cross splice except possibly its cross site. -/
theorem EvenKempeFusionLens.exists_bcPrimalTrail_with_crossSpliceCoverage
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hnonempty : lens01.bcCrossSites lens23 ≠ []) :
    ∃ (site : lens01.bRoute.CrossSite lens23.cRoute)
        (trail : G.Walk (data.defectVertex 0) (data.defectVertex 2)),
      trail.IsTrail ∧ 0 < trail.length ∧
        trail.edges ⊆
          (lens01.bRoute.crossSplice lens23.cRoute site).support.map
            Subtype.val ∧
        trail.edges ⊆
          (lens01.bRoute.ambientPath.support ++
            lens23.cRoute.ambientPath.support).map Subtype.val ∧
        (∀ edge ∈
          (lens01.bRoute.crossSplice lens23.cRoute site).support,
          edge = site.1 ∨ edge.1 ∈ trail.edges) := by
  rcases lens01.exists_bcPrimalCoherentCrossPath_with_spliceCoverage lens23
      hab hac hbc hnonempty with
    ⟨site, joined, hpath, hcoherent, hpositive, _hlength,
      hspliceSupport, hsupport, hcoverage⟩
  have hc01Start : lens01.cRoute.leftEdge.1 ∈
      lens01.cRoute.ambientPath.support := by
    simpa only [lens01.cRoute.ambientPath.getVert_zero] using
      lens01.cRoute.ambientPath.getVert_mem_support 0
  have hb23Start : lens23.bRoute.leftEdge.1 ∈
      lens23.bRoute.ambientPath.support := by
    simpa only [lens23.bRoute.ambientPath.getVert_zero] using
      lens23.bRoute.ambientPath.getVert_mem_support 0
  have hc01Absent : lens01.cRoute.leftEdge.1 ∉ joined.support := by
    intro hmem
    rcases List.mem_append.mp (hsupport hmem) with hb01 | hc23
    · exact lens01.cLeftEdge_not_mem_bAmbientPath_support hab hac hb01
    · exact (List.disjoint_left.mp hcDisjoint) hc01Start hc23
  have hb23Absent : lens23.bRoute.leftEdge.1 ∉ joined.support := by
    intro hmem
    rcases List.mem_append.mp (hsupport hmem) with hb01 | hc23
    · exact (List.disjoint_left.mp hbDisjoint) hb01 hb23Start
    · exact lens23.bLeftEdge_not_mem_cAmbientPath_support hab hac hc23
  have hstartNe := lens01.leftDefect_ne_firstJunction_of_bTerminal
    hdata joined hpositive hc01Absent
  have hendNe := lens23.lastJunction_ne_leftDefect_of_cTerminal
    hdata joined hpositive hb23Absent
  have hstartMem : data.defectVertex 0 ∈
      (lens01.bRoute.leftEdge.1.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using lens01.bRoute.leftIncident
  have hendMem : data.defectVertex 2 ∈
      (lens23.cRoute.leftEdge.1.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using lens23.cRoute.leftIncident
  let trail := joined.cappedPrimalLift hpositive hcoherent
    (data.defectVertex 0) (data.defectVertex 2)
    hstartMem hendMem hstartNe hendNe
  refine ⟨site, trail, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [trail]
    exact joined.cappedPrimalLift_isTrail_of_isPath
      hpositive hcoherent hpath
      (data.defectVertex 0) (data.defectVertex 2)
      hstartMem hendMem hstartNe hendNe
  · dsimp only [trail]
    rw [joined.cappedPrimalLift_length]
    omega
  · dsimp only [trail]
    rw [joined.cappedPrimalLift_edges_eq_map_support
      hpositive hcoherent
      (data.defectVertex 0) (data.defectVertex 2)
      hstartMem hendMem hstartNe hendNe]
    intro edge hedge
    rcases List.mem_map.mp hedge with ⟨source, hsource, rfl⟩
    exact List.mem_map.mpr ⟨source, hspliceSupport hsource, rfl⟩
  · dsimp only [trail]
    rw [joined.cappedPrimalLift_edges_eq_map_support
      hpositive hcoherent
      (data.defectVertex 0) (data.defectVertex 2)
      hstartMem hendMem hstartNe hendNe]
    intro edge hedge
    rcases List.mem_map.mp hedge with ⟨source, hsource, rfl⟩
    exact List.mem_map.mpr ⟨source, hsupport hsource, rfl⟩
  · intro edge hedge
    rcases hcoverage edge hedge with hedgeSite | hedgeJoined
    · exact Or.inl hedgeSite
    · apply Or.inr
      dsimp only [trail]
      rw [joined.cappedPrimalLift_edges_eq_map_support
        hpositive hcoherent
        (data.defectVertex 0) (data.defectVertex 2)
        hstartMem hendMem hstartNe hendNe]
      exact List.mem_map.mpr ⟨edge, hedgeJoined, rfl⟩

/-- Route-support form of the first cross-channel primal trail. -/
theorem EvenKempeFusionLens.exists_bcPrimalTrail_with_routeSupport
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hnonempty : lens01.bcCrossSites lens23 ≠ []) :
    ∃ trail : G.Walk (data.defectVertex 0) (data.defectVertex 2),
      trail.IsTrail ∧ 0 < trail.length ∧
        trail.edges ⊆
          (lens01.bRoute.ambientPath.support ++
            lens23.cRoute.ambientPath.support).map Subtype.val := by
  rcases lens01.exists_bcPrimalTrail_with_crossSpliceCoverage lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hnonempty with
    ⟨_site, trail, htrail, hpositive, _hspliceSupport, hsupport,
      _hcoverage⟩
  exact ⟨trail, htrail, hpositive, hsupport⟩

/-- Support-forgetting form of the first cross-channel primal trail. -/
theorem EvenKempeFusionLens.exists_bcPrimalTrail
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hnonempty : lens01.bcCrossSites lens23 ≠ []) :
    ∃ trail : G.Walk (data.defectVertex 0) (data.defectVertex 2),
      trail.IsTrail ∧ 0 < trail.length := by
  rcases lens01.exists_bcPrimalTrail_with_routeSupport lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hnonempty with
    ⟨trail, htrail, hpositive, _hsupport⟩
  exact ⟨trail, htrail, hpositive⟩

/-- The second cross channel gives the complementary primal trail with the
same exact one-site splice coverage. -/
theorem EvenKempeFusionLens.exists_cbPrimalTrail_with_crossSpliceCoverage
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hnonempty : lens01.cbCrossSites lens23 ≠ []) :
    ∃ (site : lens01.cRoute.CrossSite lens23.bRoute)
        (trail : G.Walk (data.defectVertex 0) (data.defectVertex 2)),
      trail.IsTrail ∧ 0 < trail.length ∧
        trail.edges ⊆
          (lens01.cRoute.crossSplice lens23.bRoute site).support.map
            Subtype.val ∧
        trail.edges ⊆
          (lens01.cRoute.ambientPath.support ++
            lens23.bRoute.ambientPath.support).map Subtype.val ∧
        (∀ edge ∈
          (lens01.cRoute.crossSplice lens23.bRoute site).support,
          edge = site.1 ∨ edge.1 ∈ trail.edges) := by
  rcases lens01.exists_cbPrimalCoherentCrossPath_with_spliceCoverage lens23
      hab hac hbc hnonempty with
    ⟨site, joined, hpath, hcoherent, hpositive, _hlength,
      hspliceSupport, hsupport, hcoverage⟩
  have hb01Start : lens01.bRoute.leftEdge.1 ∈
      lens01.bRoute.ambientPath.support := by
    simpa only [lens01.bRoute.ambientPath.getVert_zero] using
      lens01.bRoute.ambientPath.getVert_mem_support 0
  have hc23Start : lens23.cRoute.leftEdge.1 ∈
      lens23.cRoute.ambientPath.support := by
    simpa only [lens23.cRoute.ambientPath.getVert_zero] using
      lens23.cRoute.ambientPath.getVert_mem_support 0
  have hb01Absent : lens01.bRoute.leftEdge.1 ∉ joined.support := by
    intro hmem
    rcases List.mem_append.mp (hsupport hmem) with hc01 | hb23
    · exact lens01.bLeftEdge_not_mem_cAmbientPath_support hab hac hc01
    · exact (List.disjoint_left.mp hbDisjoint) hb01Start hb23
  have hc23Absent : lens23.cRoute.leftEdge.1 ∉ joined.support := by
    intro hmem
    rcases List.mem_append.mp (hsupport hmem) with hc01 | hb23
    · exact (List.disjoint_left.mp hcDisjoint) hc01 hc23Start
    · exact lens23.cLeftEdge_not_mem_bAmbientPath_support hab hac hb23
  have hstartNe := lens01.leftDefect_ne_firstJunction_of_cTerminal
    hdata joined hpositive hb01Absent
  have hendNe := lens23.lastJunction_ne_leftDefect_of_bTerminal
    hdata joined hpositive hc23Absent
  have hstartMem : data.defectVertex 0 ∈
      (lens01.cRoute.leftEdge.1.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using lens01.cRoute.leftIncident
  have hendMem : data.defectVertex 2 ∈
      (lens23.bRoute.leftEdge.1.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using lens23.bRoute.leftIncident
  let trail := joined.cappedPrimalLift hpositive hcoherent
    (data.defectVertex 0) (data.defectVertex 2)
    hstartMem hendMem hstartNe hendNe
  refine ⟨site, trail, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [trail]
    exact joined.cappedPrimalLift_isTrail_of_isPath
      hpositive hcoherent hpath
      (data.defectVertex 0) (data.defectVertex 2)
      hstartMem hendMem hstartNe hendNe
  · dsimp only [trail]
    rw [joined.cappedPrimalLift_length]
    omega
  · dsimp only [trail]
    rw [joined.cappedPrimalLift_edges_eq_map_support
      hpositive hcoherent
      (data.defectVertex 0) (data.defectVertex 2)
      hstartMem hendMem hstartNe hendNe]
    intro edge hedge
    rcases List.mem_map.mp hedge with ⟨source, hsource, rfl⟩
    exact List.mem_map.mpr ⟨source, hspliceSupport hsource, rfl⟩
  · dsimp only [trail]
    rw [joined.cappedPrimalLift_edges_eq_map_support
      hpositive hcoherent
      (data.defectVertex 0) (data.defectVertex 2)
      hstartMem hendMem hstartNe hendNe]
    intro edge hedge
    rcases List.mem_map.mp hedge with ⟨source, hsource, rfl⟩
    exact List.mem_map.mpr ⟨source, hsupport hsource, rfl⟩
  · intro edge hedge
    rcases hcoverage edge hedge with hedgeSite | hedgeJoined
    · exact Or.inl hedgeSite
    · apply Or.inr
      dsimp only [trail]
      rw [joined.cappedPrimalLift_edges_eq_map_support
        hpositive hcoherent
        (data.defectVertex 0) (data.defectVertex 2)
        hstartMem hendMem hstartNe hendNe]
      exact List.mem_map.mpr ⟨edge, hedgeJoined, rfl⟩

/-- Route-support form of the complementary cross-channel trail. -/
theorem EvenKempeFusionLens.exists_cbPrimalTrail_with_routeSupport
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hnonempty : lens01.cbCrossSites lens23 ≠ []) :
    ∃ trail : G.Walk (data.defectVertex 0) (data.defectVertex 2),
      trail.IsTrail ∧ 0 < trail.length ∧
        trail.edges ⊆
          (lens01.cRoute.ambientPath.support ++
            lens23.bRoute.ambientPath.support).map Subtype.val := by
  rcases lens01.exists_cbPrimalTrail_with_crossSpliceCoverage lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hnonempty with
    ⟨_site, trail, htrail, hpositive, _hspliceSupport, hsupport,
      _hcoverage⟩
  exact ⟨trail, htrail, hpositive, hsupport⟩

/-- Support-forgetting form of the complementary cross-channel trail. -/
theorem EvenKempeFusionLens.exists_cbPrimalTrail
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hnonempty : lens01.cbCrossSites lens23 ≠ []) :
    ∃ trail : G.Walk (data.defectVertex 0) (data.defectVertex 2),
      trail.IsTrail ∧ 0 < trail.length := by
  rcases lens01.exists_cbPrimalTrail_with_routeSupport lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hnonempty with
    ⟨trail, htrail, hpositive, _hsupport⟩
  exact ⟨trail, htrail, hpositive⟩

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
