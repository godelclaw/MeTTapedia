import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelPrimalTrail
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceCutTrailTransport

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24InducedHexCorridorTypes
open SimpleGraph
open SimpleGraphDartRotation

namespace SimpleGraph.Dart

variable {V : Type*} {G : SimpleGraph V}

/-- An oriented simple-graph edge is determined by its underlying edge and
its initial vertex. -/
theorem eq_of_fst_eq_of_edge_eq (first second : G.Dart)
    (hfst : first.fst = second.fst)
    (hedge : first.edge = second.edge) :
    first = second := by
  rcases (SimpleGraph.dart_edge_eq_iff first second).1 hedge with
    hsame | hopposite
  · exact hsame
  · exfalso
    apply second.snd_ne_fst
    calc
      second.snd = second.symm.fst := rfl
      _ = first.fst := congrArg (fun dart : G.Dart => dart.fst) hopposite.symm
      _ = second.fst := hfst

end SimpleGraph.Dart

namespace SimpleGraph.Walk

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance terminalTrailGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- At a degree-two endpoint, excluding one incident edge identifies the
first oriented dart with the other edge oriented away from the endpoint. -/
theorem firstDart_eq_edgeDartAt_of_incident_pair_of_other_not_mem_edges
    {start finish : V} (walk : G.Walk start finish)
    (hnil : ¬walk.Nil) (selected other : G.edgeSet)
    (hpair : ∀ edge ∈ incidentEdgeFinset G start,
      edge = selected ∨ edge = other)
    (hselectedMem : start ∈ (selected.1 : Sym2 V))
    (hother : other.1 ∉ walk.edges) :
    walk.firstDart hnil = SimpleGraph.edgeDartAt selected hselectedMem := by
  let firstEdge : G.edgeSet :=
    ⟨(walk.firstDart hnil).edge, (walk.firstDart hnil).edge_mem⟩
  have hfirstIncident : firstEdge ∈ incidentEdgeFinset G start := by
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    dsimp only [firstEdge]
    simpa [SimpleGraph.Dart.edge] using
      Sym2.mem_mk_left (walk.firstDart hnil).fst
        (walk.firstDart hnil).snd
  have hfirstInEdges : firstEdge.1 ∈ walk.edges := by
    dsimp only [firstEdge]
    simpa only [walk.edge_firstDart] using
      walk.mk_start_snd_mem_edges hnil
  rcases hpair firstEdge hfirstIncident with hselected | hotherEdge
  · apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
    · simp
    · simpa only [SimpleGraph.edgeDartAt_edge] using
        congrArg Subtype.val hselected
  · exfalso
    apply hother
    rw [← congrArg Subtype.val hotherEdge]
    exact hfirstInEdges

/-- The analogous degree-two endpoint rule for the final dart, reversed so
that it points away from the terminal vertex. -/
theorem lastDart_symm_eq_edgeDartAt_of_incident_pair_of_other_not_mem_edges
    {start finish : V} (walk : G.Walk start finish)
    (hnil : ¬walk.Nil) (selected other : G.edgeSet)
    (hpair : ∀ edge ∈ incidentEdgeFinset G finish,
      edge = selected ∨ edge = other)
    (hselectedMem : finish ∈ (selected.1 : Sym2 V))
    (hother : other.1 ∉ walk.edges) :
    (walk.lastDart hnil).symm =
      SimpleGraph.edgeDartAt selected hselectedMem := by
  let lastEdge : G.edgeSet :=
    ⟨(walk.lastDart hnil).edge, (walk.lastDart hnil).edge_mem⟩
  have hlastIncident : lastEdge ∈ incidentEdgeFinset G finish := by
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    dsimp only [lastEdge]
    simpa [SimpleGraph.Dart.edge] using
      Sym2.mem_mk_right (walk.lastDart hnil).fst
        (walk.lastDart hnil).snd
  have hlastInEdges : lastEdge.1 ∈ walk.edges := by
    dsimp only [lastEdge]
    simpa only [walk.edge_lastDart] using
      walk.mk_penultimate_end_mem_edges hnil
  rcases hpair lastEdge hlastIncident with hselected | hotherEdge
  · apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
    · simp
    · simpa only [SimpleGraph.Dart.edge_symm,
        SimpleGraph.edgeDartAt_edge] using congrArg Subtype.val hselected
  · exfalso
    apply hother
    rw [← congrArg Subtype.val hotherEdge]
    exact hlastInEdges

end SimpleGraph.Walk

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance crossChannelFaceCutGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The support certificate of a `bc` cross-channel trail determines its
two outward-facing terminal darts. -/
theorem EvenKempeFusionLens.bcPrimalTrail_terminalDarts
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (trail : G.Walk (data.defectVertex 0) (data.defectVertex 2))
    (hnil : ¬trail.Nil)
    (hsupport : trail.edges ⊆
      (lens01.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support).map Subtype.val) :
    trail.firstDart hnil = lens01.bRoute.leftTerminalDart ∧
      (trail.lastDart hnil).symm = lens23.cRoute.leftTerminalDart := by
  have hc01Start : lens01.cRoute.leftEdge.1 ∈
      lens01.cRoute.ambientPath.support := by
    simpa only [lens01.cRoute.ambientPath.getVert_zero] using
      lens01.cRoute.ambientPath.getVert_mem_support 0
  have hb23Start : lens23.bRoute.leftEdge.1 ∈
      lens23.bRoute.ambientPath.support := by
    simpa only [lens23.bRoute.ambientPath.getVert_zero] using
      lens23.bRoute.ambientPath.getVert_mem_support 0
  have hc01Absent : lens01.cRoute.leftEdge.1.1 ∉ trail.edges := by
    intro hedge
    rcases List.mem_map.mp (hsupport hedge) with
      ⟨source, hsource, hvalue⟩
    have hsourceEq : source = lens01.cRoute.leftEdge.1 :=
      Subtype.ext hvalue
    subst source
    rcases List.mem_append.mp hsource with hb01 | hc23
    · exact lens01.cLeftEdge_not_mem_bAmbientPath_support hab hac hb01
    · exact (List.disjoint_left.mp hcDisjoint) hc01Start hc23
  have hb23Absent : lens23.bRoute.leftEdge.1.1 ∉ trail.edges := by
    intro hedge
    rcases List.mem_map.mp (hsupport hedge) with
      ⟨source, hsource, hvalue⟩
    have hsourceEq : source = lens23.bRoute.leftEdge.1 :=
      Subtype.ext hvalue
    subst source
    rcases List.mem_append.mp hsource with hb01 | hc23
    · exact (List.disjoint_left.mp hbDisjoint) hb01 hb23Start
    · exact lens23.bLeftEdge_not_mem_cAmbientPath_support hab hac hc23
  constructor
  · simpa only [EvenKempePortPath.leftTerminalDart] using
      SimpleGraph.Walk.firstDart_eq_edgeDartAt_of_incident_pair_of_other_not_mem_edges
        trail
        hnil lens01.bRoute.leftEdge.1 lens01.cRoute.leftEdge.1
        (by
          intro edge hedge
          rw [lens01.leftTerminalEdges_eq_incidentEdgeFinset hdata] at hedge
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hedge)
        (by simpa [incidentEdgeFinset] using lens01.bRoute.leftIncident)
        hc01Absent
  · simpa only [EvenKempePortPath.leftTerminalDart] using
      SimpleGraph.Walk.lastDart_symm_eq_edgeDartAt_of_incident_pair_of_other_not_mem_edges
        trail
        hnil lens23.cRoute.leftEdge.1 lens23.bRoute.leftEdge.1
        (by
          intro edge hedge
          rw [lens23.leftTerminalEdges_eq_incidentEdgeFinset hdata] at hedge
          simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
          rcases hedge with hb | hc
          · exact Or.inr hb
          · exact Or.inl hc)
        (by simpa [incidentEdgeFinset] using lens23.cRoute.leftIncident)
        hb23Absent

/-- The complementary `cb` support certificate identifies the opposite
choice of terminal dart in each degree-two boundary fiber. -/
theorem EvenKempeFusionLens.cbPrimalTrail_terminalDarts
    {data : DegreeTwoBoundaryData G 4}
    {C : G.EdgeColoring Color} {a b c : Color}
    (lens01 : data.EvenKempeFusionLens C a b c 0 1)
    (lens23 : data.EvenKempeFusionLens C a b c 2 3)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (trail : G.Walk (data.defectVertex 0) (data.defectVertex 2))
    (hnil : ¬trail.Nil)
    (hsupport : trail.edges ⊆
      (lens01.cRoute.ambientPath.support ++
        lens23.bRoute.ambientPath.support).map Subtype.val) :
    trail.firstDart hnil = lens01.cRoute.leftTerminalDart ∧
      (trail.lastDart hnil).symm = lens23.bRoute.leftTerminalDart := by
  have hb01Start : lens01.bRoute.leftEdge.1 ∈
      lens01.bRoute.ambientPath.support := by
    simpa only [lens01.bRoute.ambientPath.getVert_zero] using
      lens01.bRoute.ambientPath.getVert_mem_support 0
  have hc23Start : lens23.cRoute.leftEdge.1 ∈
      lens23.cRoute.ambientPath.support := by
    simpa only [lens23.cRoute.ambientPath.getVert_zero] using
      lens23.cRoute.ambientPath.getVert_mem_support 0
  have hb01Absent : lens01.bRoute.leftEdge.1.1 ∉ trail.edges := by
    intro hedge
    rcases List.mem_map.mp (hsupport hedge) with
      ⟨source, hsource, hvalue⟩
    have hsourceEq : source = lens01.bRoute.leftEdge.1 :=
      Subtype.ext hvalue
    subst source
    rcases List.mem_append.mp hsource with hc01 | hb23
    · exact lens01.bLeftEdge_not_mem_cAmbientPath_support hab hac hc01
    · exact (List.disjoint_left.mp hbDisjoint) hb01Start hb23
  have hc23Absent : lens23.cRoute.leftEdge.1.1 ∉ trail.edges := by
    intro hedge
    rcases List.mem_map.mp (hsupport hedge) with
      ⟨source, hsource, hvalue⟩
    have hsourceEq : source = lens23.cRoute.leftEdge.1 :=
      Subtype.ext hvalue
    subst source
    rcases List.mem_append.mp hsource with hc01 | hb23
    · exact (List.disjoint_left.mp hcDisjoint) hc01 hc23Start
    · exact lens23.cLeftEdge_not_mem_bAmbientPath_support hab hac hb23
  constructor
  · simpa only [EvenKempePortPath.leftTerminalDart] using
      SimpleGraph.Walk.firstDart_eq_edgeDartAt_of_incident_pair_of_other_not_mem_edges
        trail
        hnil lens01.cRoute.leftEdge.1 lens01.bRoute.leftEdge.1
        (by
          intro edge hedge
          rw [lens01.leftTerminalEdges_eq_incidentEdgeFinset hdata] at hedge
          simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
          rcases hedge with hb | hc
          · exact Or.inr hb
          · exact Or.inl hc)
        (by simpa [incidentEdgeFinset] using lens01.cRoute.leftIncident)
        hb01Absent
  · simpa only [EvenKempePortPath.leftTerminalDart] using
      SimpleGraph.Walk.lastDart_symm_eq_edgeDartAt_of_incident_pair_of_other_not_mem_edges
        trail
        hnil lens23.bRoute.leftEdge.1 lens23.cRoute.leftEdge.1
        (by
          intro edge hedge
          rw [lens23.leftTerminalEdges_eq_incidentEdgeFinset hdata] at hedge
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hedge)
        (by simpa [incidentEdgeFinset] using lens23.bRoute.leftIncident)
        hc23Absent

/-- A nonempty `bc` cross channel supported away from an exact cut carries
one face-side label between the two opposite boundary defects. -/
theorem EvenKempeFusionLens.exists_bcPrimalTrail_with_faceCutTransport
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
    (hnonempty : lens01.bcCrossSites lens23 ≠ [])
    (graphData : SimpleGraphDartRotation.Data G)
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
      lens01.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support,
      ¬cut edge) :
    ∃ (trail : G.Walk (data.defectVertex 0) (data.defectVertex 2))
        (hnil : ¬trail.Nil),
      trail.IsTrail ∧ 0 < trail.length ∧
        trail.edges ⊆
          (lens01.bRoute.ambientPath.support ++
            lens23.cRoute.ambientPath.support).map Subtype.val ∧
        labels (dartOrbitFace graphData.toRotationSystem
            (trail.firstDart hnil)) =
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha
              (trail.lastDart hnil))) := by
  rcases lens01.exists_bcPrimalTrail_with_routeSupport lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hnonempty with
    ⟨trail, htrail, hpositive, hsupport⟩
  let hnil : ¬trail.Nil :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpositive
  have hlabels :=
    graphData.trail_labels_eq_firstDart_alpha_lastDart_of_walk_edges_not_cut
      hcubic hrotation labels cut hexact trail hnil htrail (by
        intro edge hedge
        rcases List.mem_map.mp (hsupport hedge) with
          ⟨source, hsource, hvalue⟩
        have hsourceEq : source = edge := Subtype.ext hvalue
        subst source
        exact hnot edge hsource)
  exact ⟨trail, hnil, htrail, hpositive, hsupport, hlabels⟩

/-- Exact-cut transport along a `bc` cross channel, with the auxiliary
primal trail eliminated from the statement. -/
theorem EvenKempeFusionLens.bcTerminalFaceLabels_eq_of_crossChannel_not_cut
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
    (hnonempty : lens01.bcCrossSites lens23 ≠ [])
    (graphData : SimpleGraphDartRotation.Data G)
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
      lens01.bRoute.ambientPath.support ++
        lens23.cRoute.ambientPath.support,
      ¬cut edge) :
    labels (dartOrbitFace graphData.toRotationSystem
        lens01.bRoute.leftTerminalDart) =
      labels (dartOrbitFace graphData.toRotationSystem
        lens23.cRoute.leftTerminalDart) := by
  rcases lens01.exists_bcPrimalTrail_with_faceCutTransport lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hnonempty graphData
      hcubic hrotation labels cut hexact hnot with
    ⟨trail, hnil, _htrail, _hpositive, hsupport, hlabels⟩
  have hterminals := lens01.bcPrimalTrail_terminalDarts lens23
    hdata hab hac hbDisjoint hcDisjoint trail hnil hsupport
  rw [hterminals.1, SimpleGraphDartRotation.Data.toRotationSystem_alpha,
    hterminals.2] at hlabels
  exact hlabels

/-- The complementary `cb` cross channel has the same exact-cut transport
property with the two route families exchanged. -/
theorem EvenKempeFusionLens.exists_cbPrimalTrail_with_faceCutTransport
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
    (hnonempty : lens01.cbCrossSites lens23 ≠ [])
    (graphData : SimpleGraphDartRotation.Data G)
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
      lens01.cRoute.ambientPath.support ++
        lens23.bRoute.ambientPath.support,
      ¬cut edge) :
    ∃ (trail : G.Walk (data.defectVertex 0) (data.defectVertex 2))
        (hnil : ¬trail.Nil),
      trail.IsTrail ∧ 0 < trail.length ∧
        trail.edges ⊆
          (lens01.cRoute.ambientPath.support ++
            lens23.bRoute.ambientPath.support).map Subtype.val ∧
        labels (dartOrbitFace graphData.toRotationSystem
            (trail.firstDart hnil)) =
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha
              (trail.lastDart hnil))) := by
  rcases lens01.exists_cbPrimalTrail_with_routeSupport lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hnonempty with
    ⟨trail, htrail, hpositive, hsupport⟩
  let hnil : ¬trail.Nil :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpositive
  have hlabels :=
    graphData.trail_labels_eq_firstDart_alpha_lastDart_of_walk_edges_not_cut
      hcubic hrotation labels cut hexact trail hnil htrail (by
        intro edge hedge
        rcases List.mem_map.mp (hsupport hedge) with
          ⟨source, hsource, hvalue⟩
        have hsourceEq : source = edge := Subtype.ext hvalue
        subst source
        exact hnot edge hsource)
  exact ⟨trail, hnil, htrail, hpositive, hsupport, hlabels⟩

/-- Exact-cut transport along the complementary `cb` cross channel, stated
directly between its selected boundary darts. -/
theorem EvenKempeFusionLens.cbTerminalFaceLabels_eq_of_crossChannel_not_cut
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
    (hnonempty : lens01.cbCrossSites lens23 ≠ [])
    (graphData : SimpleGraphDartRotation.Data G)
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
      lens01.cRoute.ambientPath.support ++
        lens23.bRoute.ambientPath.support,
      ¬cut edge) :
    labels (dartOrbitFace graphData.toRotationSystem
        lens01.cRoute.leftTerminalDart) =
      labels (dartOrbitFace graphData.toRotationSystem
        lens23.bRoute.leftTerminalDart) := by
  rcases lens01.exists_cbPrimalTrail_with_faceCutTransport lens23
      hdata hab hac hbc hbDisjoint hcDisjoint hnonempty graphData
      hcubic hrotation labels cut hexact hnot with
    ⟨trail, hnil, _htrail, _hpositive, hsupport, hlabels⟩
  have hterminals := lens01.cbPrimalTrail_terminalDarts lens23
    hdata hab hac hbDisjoint hcDisjoint trail hnil hsupport
  rw [hterminals.1, SimpleGraphDartRotation.Data.toRotationSystem_alpha,
    hterminals.2] at hlabels
  exact hlabels

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
