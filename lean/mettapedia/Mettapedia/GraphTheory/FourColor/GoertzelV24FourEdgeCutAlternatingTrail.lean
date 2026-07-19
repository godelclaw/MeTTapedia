import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceCutTrailTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24CyclicExactCutConnectedSides
import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutClosureColor
import Mettapedia.GraphTheory.FourColor.GoertzelV24WalkFaceCut

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FourEdgeCutAlternatingTrail

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24CyclicExactCutConnectedSides
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourEdgeCutNoncrossingInterfaces
open GoertzelV24FourEdgeCutClosureColor
open GoertzelV24FourEdgeCutBoundaryData
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationVertexCutProfile
open GoertzelV24ThreeEdgeCutMinimality
open GoertzelV24WalkFaceCut
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Inclusion of one induced cut side into the ambient graph. -/
abbrev cutSideGraphHom (cut : SmallCyclicEdgeCut G) :
    CyclicCutSideGraph cut →g G where
  toFun := Subtype.val
  map_rel' := fun {_ _} hedge ↦ hedge

/-- Map a walk in one induced cut side back to the ambient graph. -/
def cutSideWalkToAmbient (cut : SmallCyclicEdgeCut G)
    {left right : CyclicCutSideVertex cut}
    (walk : (CyclicCutSideGraph cut).Walk left right) :
    G.Walk left.1 right.1 :=
  walk.map (cutSideGraphHom cut)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem cutSideWalkToAmbient_isPath
    (cut : SmallCyclicEdgeCut G)
    {left right : CyclicCutSideVertex cut}
    {walk : (CyclicCutSideGraph cut).Walk left right}
    (hwalk : walk.IsPath) :
    (cutSideWalkToAmbient cut walk).IsPath := by
  exact SimpleGraph.Walk.map_isPath_of_injective
    Subtype.val_injective hwalk

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem cutSideWalkToAmbient_isTrail
    (cut : SmallCyclicEdgeCut G)
    {left right : CyclicCutSideVertex cut}
    {walk : (CyclicCutSideGraph cut).Walk left right}
    (hwalk : walk.IsTrail) :
    (cutSideWalkToAmbient cut walk).IsTrail := by
  exact SimpleGraph.Walk.map_isTrail_of_injective
    Subtype.val_injective hwalk

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A cut edge cannot occur in a walk lying in either induced side. -/
theorem cutEdge_not_mem_cutSideWalkToAmbient_edges
    (cut : SmallCyclicEdgeCut G) {edge : G.edgeSet}
    (hedge : edge ∈ cut.edgeCut)
    {left right : CyclicCutSideVertex cut}
    (walk : (CyclicCutSideGraph cut).Walk left right) :
    edge.1 ∉ (cutSideWalkToAmbient cut walk).edges := by
  intro hmem
  rw [cutSideWalkToAmbient, SimpleGraph.Walk.edges_map] at hmem
  rcases List.mem_map.mp hmem with ⟨sideEdge, _hsideEdge, hedgeEq⟩
  have hcross : EdgeCrossesVertexSide G cut.side edge :=
    (cut.hcut_eq edge).1 hedge
  rcases hcross with ⟨inside, outside, hinside, houtside,
    hinsideSide, houtsideSide⟩
  have everyMappedEndpoint : ∀ vertex : V,
      vertex ∈ sideEdge.map (cutSideGraphHom cut) → cut.side vertex := by
    intro vertex hvertex
    rcases Sym2.mem_map.mp hvertex with
      ⟨sideVertex, _hsideVertex, rfl⟩
    exact sideVertex.2
  apply houtsideSide
  apply everyMappedEndpoint outside
  rw [hedgeEq]
  exact houtside

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Walks confined to complementary induced sides have disjoint ambient
edge lists. -/
theorem cutSideWalkToAmbient_edges_disjoint_compl
    (cut : SmallCyclicEdgeCut G)
    {left right : CyclicCutSideVertex cut}
    (insideWalk : (CyclicCutSideGraph cut).Walk left right)
    {outsideLeft outsideRight : CyclicCutSideVertex cut.compl}
    (outsideWalk :
      (CyclicCutSideGraph cut.compl).Walk outsideLeft outsideRight) :
    (cutSideWalkToAmbient cut insideWalk).edges.Disjoint
      (cutSideWalkToAmbient cut.compl outsideWalk).edges := by
  rw [List.disjoint_left]
  intro edge hinside houtside
  rw [cutSideWalkToAmbient, SimpleGraph.Walk.edges_map] at hinside houtside
  rcases List.mem_map.mp hinside with
    ⟨insideEdge, _hinsideEdge, hinsideEq⟩
  rcases List.mem_map.mp houtside with
    ⟨outsideEdge, _houtsideEdge, houtsideEq⟩
  induction insideEdge using Sym2.inductionOn with
  | _ insideFirst insideSecond =>
      have hfirstMem : insideFirst.1 ∈
          s(insideFirst, insideSecond).map (cutSideGraphHom cut) := by
        exact Sym2.mem_map.mpr ⟨insideFirst, by simp, rfl⟩
      have hfirstOutside : insideFirst.1 ∈
          outsideEdge.map (cutSideGraphHom cut.compl) := by
        rw [hinsideEq, ← houtsideEq] at hfirstMem
        exact hfirstMem
      rcases Sym2.mem_map.mp hfirstOutside with
        ⟨outsideVertex, _houtsideVertex, hvalue⟩
      apply outsideVertex.2
      change outsideVertex.1 = insideFirst.1 at hvalue
      rw [hvalue]
      exact insideFirst.2

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Edge-disjoint walks in one induced side remain edge-disjoint after
embedding into the ambient graph. -/
theorem cutSideWalkToAmbient_edges_disjoint_of_disjoint
    (cut : SmallCyclicEdgeCut G)
    {firstLeft firstRight secondLeft secondRight :
      CyclicCutSideVertex cut}
    (first : (CyclicCutSideGraph cut).Walk firstLeft firstRight)
    (second : (CyclicCutSideGraph cut).Walk secondLeft secondRight)
    (hdisjoint : first.edges.Disjoint second.edges) :
    (cutSideWalkToAmbient cut first).edges.Disjoint
      (cutSideWalkToAmbient cut second).edges := by
  rw [cutSideWalkToAmbient, cutSideWalkToAmbient,
    SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_map]
  exact hdisjoint.map (Sym2.map.injective Subtype.val_injective)

/-- The endpoint of a cyclic boundary edge on the deleted side of the cut. -/
def commonDeletedPort
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (port : Fin 4) : CyclicCutSideVertex cut :=
  ⟨graphData.toRotationSystem.vertOf
      (graphData.toRotationSystem.alpha
        (cyclicData.boundaryOrder port).1.1),
    by
      simpa [deletedRegionKeep, mem_cyclicCutVertexSide_iff] using
        (cyclicData.boundaryOrder port).2⟩

@[simp]
theorem commonDeletedPort_val
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (port : Fin 4) :
    (commonDeletedPort graphData cut cyclicData port).1 =
      graphData.toRotationSystem.vertOf
        (graphData.toRotationSystem.alpha
          (cyclicData.boundaryOrder port).1.1) :=
  rfl

/-- The one-edge walk across a named cyclic boundary coordinate, oriented
from the retained side to the deleted side. -/
def commonCutWalk
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (port : Fin 4) :
    G.Walk (commonRetainedPort graphData cut cyclicData port).1
      (commonDeletedPort graphData cut cyclicData port).1 :=
  (cyclicData.boundaryOrder port).1.1.adj.toWalk

@[simp]
theorem commonCutWalk_edges
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (port : Fin 4) :
    (commonCutWalk graphData cut cyclicData port).edges =
      [(graphData.toRotationSystem.edgeOf
        (cyclicData.boundaryOrder port).1.1).1] := by
  rfl

/-- The ambient edge underlying one common cyclic boundary coordinate. -/
def commonBoundaryEdge
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (port : Fin 4) : Sym2 V :=
  (graphData.toRotationSystem.edgeOf
    (cyclicData.boundaryOrder port).1.1).1

@[simp]
theorem commonCutWalk_edges_eq
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (port : Fin 4) :
    (commonCutWalk graphData cut cyclicData port).edges =
      [commonBoundaryEdge graphData cut cyclicData port] := by
  rfl

/-- Every common cyclic boundary coordinate is an actual edge of the
exact cut. -/
theorem commonBoundaryEdge_mem_cut
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (port : Fin 4) :
    ⟨commonBoundaryEdge graphData cut cyclicData port,
      (graphData.toRotationSystem.edgeOf
        (cyclicData.boundaryOrder port).1.1).2⟩ ∈ cut.edgeCut := by
  exact (commonCutEdge graphData cut cyclicData port).2

/-- Distinct cyclic boundary coordinates name distinct ambient edges. -/
theorem commonBoundaryEdge_injective
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) :
    Function.Injective (commonBoundaryEdge graphData cut cyclicData) := by
  intro first second hedges
  apply boundaryCrossing_injective graphData.toRotationSystem
    (cyclicCutVertexSide cut) cyclicData.boundaryOrder
  simpa [commonBoundaryEdge, boundaryCrossing] using hedges

/-- Close from retained port `2` to retained port `0` through the deleted
side, using exactly the two named cut edges at its ends. -/
def oppositeCutReturn
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (deletedPath : (CyclicCutSideGraph cut).Walk
      (commonDeletedPort graphData cut cyclicData 2)
      (commonDeletedPort graphData cut cyclicData 0)) :
    G.Walk (commonRetainedPort graphData cut cyclicData 2).1
      (commonRetainedPort graphData cut cyclicData 0).1 :=
  (commonCutWalk graphData cut cyclicData 2).append
    ((cutSideWalkToAmbient cut deletedPath).append
      (commonCutWalk graphData cut cyclicData 0).reverse)

/-- The opposite-side return is a trail whenever its internal deleted-side
route is a trail. -/
theorem oppositeCutReturn_isTrail
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (deletedPath : (CyclicCutSideGraph cut).Walk
      (commonDeletedPort graphData cut cyclicData 2)
      (commonDeletedPort graphData cut cyclicData 0))
    (hdeletedPath : deletedPath.IsTrail) :
    (oppositeCutReturn graphData cut cyclicData deletedPath).IsTrail := by
  let edge0 : G.edgeSet :=
    graphData.toRotationSystem.edgeOf
      (cyclicData.boundaryOrder 0).1.1
  let edge2 : G.edgeSet :=
    graphData.toRotationSystem.edgeOf
      (cyclicData.boundaryOrder 2).1.1
  have hedge0Cut : edge0 ∈ cut.edgeCut := by
    exact commonBoundaryEdge_mem_cut graphData cut cyclicData 0
  have hedge2Cut : edge2 ∈ cut.edgeCut := by
    exact commonBoundaryEdge_mem_cut graphData cut cyclicData 2
  have hedge0NotPath : edge0.1 ∉
      (cutSideWalkToAmbient cut deletedPath).edges :=
    cutEdge_not_mem_cutSideWalkToAmbient_edges cut hedge0Cut deletedPath
  have hedge2NotPath : edge2.1 ∉
      (cutSideWalkToAmbient cut deletedPath).edges :=
    cutEdge_not_mem_cutSideWalkToAmbient_edges cut hedge2Cut deletedPath
  have hedge20 : edge2.1 ≠ edge0.1 := by
    intro heq
    have hport := commonBoundaryEdge_injective graphData cut cyclicData heq
    exact (by decide : (2 : Fin 4) ≠ 0) hport
  change ((commonCutWalk graphData cut cyclicData 2).append
    ((cutSideWalkToAmbient cut deletedPath).append
      (commonCutWalk graphData cut cyclicData 0).reverse)).IsTrail
  rw [SimpleGraph.Walk.isTrail_append]
  refine ⟨?_, ?_, ?_⟩
  · change ((cyclicData.boundaryOrder 2).1.1.adj.toWalk).IsTrail
    exact (SimpleGraph.Walk.IsPath.of_adj
      (cyclicData.boundaryOrder 2).1.1.adj).isTrail
  · rw [SimpleGraph.Walk.isTrail_append]
    refine ⟨cutSideWalkToAmbient_isTrail cut hdeletedPath, ?_, ?_⟩
    · change
        ((cyclicData.boundaryOrder 0).1.1.adj.toWalk).reverse.IsTrail
      exact (SimpleGraph.Walk.IsPath.of_adj
        (cyclicData.boundaryOrder 0).1.1.adj).reverse.isTrail
    rw [List.disjoint_left]
    intro edge hedge hboundary
    simp only [commonCutWalk_edges_eq, SimpleGraph.Walk.edges_reverse,
      List.reverse_singleton, List.mem_singleton] at hboundary
    subst edge
    exact hedge0NotPath hedge
  · rw [List.disjoint_left]
    intro edge hedge2 hright
    simp only [commonCutWalk_edges_eq, List.mem_singleton] at hedge2
    subst edge
    rw [SimpleGraph.Walk.edges_append] at hright
    simp only [commonCutWalk_edges_eq, SimpleGraph.Walk.edges_reverse,
      List.reverse_singleton, List.mem_append, List.mem_singleton] at hright
    exact hright.elim hedge2NotPath hedge20

/-- The return contains a common boundary edge exactly at coordinates
`0` and `2`. -/
theorem commonBoundaryEdge_mem_oppositeCutReturn_edges_iff
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (deletedPath : (CyclicCutSideGraph cut).Walk
      (commonDeletedPort graphData cut cyclicData 2)
      (commonDeletedPort graphData cut cyclicData 0))
    (port : Fin 4) :
    commonBoundaryEdge graphData cut cyclicData port ∈
        (oppositeCutReturn graphData cut cyclicData deletedPath).edges ↔
      port = 0 ∨ port = 2 := by
  let edge : G.edgeSet :=
    graphData.toRotationSystem.edgeOf
      (cyclicData.boundaryOrder port).1.1
  have hedgeCut : edge ∈ cut.edgeCut := by
    exact commonBoundaryEdge_mem_cut graphData cut cyclicData port
  have hedgeNotPath : edge.1 ∉
      (cutSideWalkToAmbient cut deletedPath).edges :=
    cutEdge_not_mem_cutSideWalkToAmbient_edges cut hedgeCut deletedPath
  change edge.1 ∈
      (oppositeCutReturn graphData cut cyclicData deletedPath).edges ↔ _
  rw [oppositeCutReturn, SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_append]
  simp only [commonCutWalk_edges_eq, SimpleGraph.Walk.edges_reverse,
    List.reverse_singleton, List.mem_append, List.mem_singleton]
  constructor
  · intro hmem
    rcases hmem with htwo | hpath | hzero
    · exact Or.inr
        (commonBoundaryEdge_injective graphData cut cyclicData htwo)
    · exact False.elim (hedgeNotPath hpath)
    · exact Or.inl
        (commonBoundaryEdge_injective graphData cut cyclicData hzero)
  · rintro (rfl | rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl

/-- Close a retained `0`--`2` trail through any deleted-side `2`--`0`
trail. -/
def oppositeCutClosure
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (retainedPath : (CyclicCutSideGraph cut.compl).Walk
      (commonRetainedPort graphData cut cyclicData 0)
      (commonRetainedPort graphData cut cyclicData 2))
    (deletedPath : (CyclicCutSideGraph cut).Walk
      (commonDeletedPort graphData cut cyclicData 2)
      (commonDeletedPort graphData cut cyclicData 0)) :
    G.Walk (commonRetainedPort graphData cut cyclicData 0).1
      (commonRetainedPort graphData cut cyclicData 0).1 :=
  (cutSideWalkToAmbient cut.compl retainedPath).append
    (oppositeCutReturn graphData cut cyclicData deletedPath)

/-- The opposite-cut closure is a closed trail. -/
theorem oppositeCutClosure_isTrail
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (retainedPath : (CyclicCutSideGraph cut.compl).Walk
      (commonRetainedPort graphData cut cyclicData 0)
      (commonRetainedPort graphData cut cyclicData 2))
    (deletedPath : (CyclicCutSideGraph cut).Walk
      (commonDeletedPort graphData cut cyclicData 2)
      (commonDeletedPort graphData cut cyclicData 0))
    (hretainedPath : retainedPath.IsTrail)
    (hdeletedPath : deletedPath.IsTrail) :
    (oppositeCutClosure graphData cut cyclicData
      retainedPath deletedPath).IsTrail := by
  let edge0 : G.edgeSet :=
    graphData.toRotationSystem.edgeOf
      (cyclicData.boundaryOrder 0).1.1
  let edge2 : G.edgeSet :=
    graphData.toRotationSystem.edgeOf
      (cyclicData.boundaryOrder 2).1.1
  have hedge0Cut : edge0 ∈ cut.compl.edgeCut := by
    exact commonBoundaryEdge_mem_cut graphData cut cyclicData 0
  have hedge2Cut : edge2 ∈ cut.compl.edgeCut := by
    exact commonBoundaryEdge_mem_cut graphData cut cyclicData 2
  have hedge0NotRetained : edge0.1 ∉
      (cutSideWalkToAmbient cut.compl retainedPath).edges :=
    cutEdge_not_mem_cutSideWalkToAmbient_edges
      cut.compl hedge0Cut retainedPath
  have hedge2NotRetained : edge2.1 ∉
      (cutSideWalkToAmbient cut.compl retainedPath).edges :=
    cutEdge_not_mem_cutSideWalkToAmbient_edges
      cut.compl hedge2Cut retainedPath
  have hsides :
      (cutSideWalkToAmbient cut.compl retainedPath).edges.Disjoint
        (cutSideWalkToAmbient cut deletedPath).edges :=
    (cutSideWalkToAmbient_edges_disjoint_compl
      cut deletedPath retainedPath).symm
  change ((cutSideWalkToAmbient cut.compl retainedPath).append
    (oppositeCutReturn graphData cut cyclicData deletedPath)).IsTrail
  rw [SimpleGraph.Walk.isTrail_append]
  refine ⟨cutSideWalkToAmbient_isTrail cut.compl hretainedPath,
    oppositeCutReturn_isTrail graphData cut cyclicData deletedPath
      hdeletedPath, ?_⟩
  rw [List.disjoint_left]
  intro edge hretained hreturn
  rw [oppositeCutReturn, SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_append] at hreturn
  simp only [commonCutWalk_edges_eq, SimpleGraph.Walk.edges_reverse,
    List.reverse_singleton, List.mem_append, List.mem_singleton] at hreturn
  rcases hreturn with hedge2 | hdeleted | hedge0
  · subst edge
    exact hedge2NotRetained hretained
  · exact (List.disjoint_left.mp hsides) hretained hdeleted
  · subst edge
    exact hedge0NotRetained hretained

/-- The closed trail meets the common four-boundary exactly at the
opposite coordinates `0` and `2`. -/
theorem commonBoundaryEdge_mem_oppositeCutClosure_edges_iff
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (retainedPath : (CyclicCutSideGraph cut.compl).Walk
      (commonRetainedPort graphData cut cyclicData 0)
      (commonRetainedPort graphData cut cyclicData 2))
    (deletedPath : (CyclicCutSideGraph cut).Walk
      (commonDeletedPort graphData cut cyclicData 2)
      (commonDeletedPort graphData cut cyclicData 0))
    (port : Fin 4) :
    commonBoundaryEdge graphData cut cyclicData port ∈
        (oppositeCutClosure graphData cut cyclicData
          retainedPath deletedPath).edges ↔
      port = 0 ∨ port = 2 := by
  let edge : G.edgeSet :=
    graphData.toRotationSystem.edgeOf
      (cyclicData.boundaryOrder port).1.1
  have hedgeCut : edge ∈ cut.compl.edgeCut := by
    exact commonBoundaryEdge_mem_cut graphData cut cyclicData port
  have hedgeNotRetained : edge.1 ∉
      (cutSideWalkToAmbient cut.compl retainedPath).edges :=
    cutEdge_not_mem_cutSideWalkToAmbient_edges
      cut.compl hedgeCut retainedPath
  change edge.1 ∈
      (oppositeCutClosure graphData cut cyclicData
        retainedPath deletedPath).edges ↔ _
  rw [oppositeCutClosure, SimpleGraph.Walk.edges_append]
  constructor
  · rw [List.mem_append]
    rintro (hretained | hreturn)
    · exact False.elim (hedgeNotRetained hretained)
    · exact (commonBoundaryEdge_mem_oppositeCutReturn_edges_iff
        graphData cut cyclicData deletedPath port).1 hreturn
  · intro hport
    apply List.mem_append_right
    exact (commonBoundaryEdge_mem_oppositeCutReturn_edges_iff
      graphData cut cyclicData deletedPath port).2 hport

/-- The deleted-side successor carries each cyclic boundary coordinate to
the next coordinate. -/
theorem deletedRegionBoundarySuccessor_boundaryOrder
    (graphData : Data G) (deleted : Finset V)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem deleted)
    (port : Fin 4) :
    deletedRegionBoundarySuccessor graphData.toRotationSystem deleted
        (cyclicData.boundaryOrder port) =
      cyclicData.boundaryOrder (finRotate 4 port) := by
  have happly := DFunLike.congr_fun cyclicData.deleted_order
    (cyclicData.boundaryOrder port)
  simpa [Equiv.permCongr_apply] using happly

/-- Consecutive cyclic boundary coordinates expose opposite sides of one
ambient face. -/
theorem boundaryOrder_sameFace_alpha_next
    (graphData : Data G) (deleted : Finset V)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem deleted)
    (port : Fin 4) :
    dartOrbitFace graphData.toRotationSystem
        (cyclicData.boundaryOrder port).1.1 =
      dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha
          (cyclicData.boundaryOrder (finRotate 4 port)).1.1) := by
  apply Quotient.sound
  have hface := deletedRegionBoundarySuccessor_sameAmbientFace_alpha
    graphData.toRotationSystem deleted (cyclicData.boundaryOrder port)
  rw [deletedRegionBoundarySuccessor_boundaryOrder
    graphData deleted cyclicData port] at hface
  exact hface

/-- A closed trail crossing the first edge of a cyclic four-boundary, but
not its two adjacent boundary edges, separates the retained endpoints of
the two adjacent ports. Consequently a trail between those endpoints must
meet the closed trail. -/
theorem no_disjoint_trail_between_one_and_three
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (deleted : Finset V)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem deleted)
    {base : V} (separator : G.Walk base base)
    (hseparator : separator.IsTrail)
    (hzero :
      (graphData.toRotationSystem.edgeOf
        (cyclicData.boundaryOrder 0).1.1).1 ∈ separator.edges)
    (hone :
      (graphData.toRotationSystem.edgeOf
        (cyclicData.boundaryOrder 1).1.1).1 ∉ separator.edges)
    (hthree :
      (graphData.toRotationSystem.edgeOf
        (cyclicData.boundaryOrder 3).1.1).1 ∉ separator.edges)
    (route : G.Walk
      (graphData.toRotationSystem.vertOf
        (cyclicData.boundaryOrder 1).1.1)
      (graphData.toRotationSystem.vertOf
        (cyclicData.boundaryOrder 3).1.1))
    (hrouteNil : ¬route.Nil) (hrouteTrail : route.IsTrail)
    (hrouteDisjoint : ∀ edge : G.edgeSet,
      edge.1 ∈ route.edges → edge.1 ∉ separator.edges)
    (hfirstNe : route.firstDart hrouteNil ≠
      (cyclicData.boundaryOrder 1).1.1)
    (hlastNe : graphData.toRotationSystem.alpha
        (route.lastDart hrouteNil) ≠
      (cyclicData.boundaryOrder 3).1.1) :
    False := by
  rcases exists_orbitFaceLabeling_ne_alpha_iff_mem_edges_of_isTrail
      graphData htwoSided hdual hconnected hsphere separator hseparator with
    ⟨labels, _hlabels, hexact⟩
  let d0 := (cyclicData.boundaryOrder 0).1.1
  let d1 := (cyclicData.boundaryOrder 1).1.1
  let d3 := (cyclicData.boundaryOrder 3).1.1
  have hface01 :
      dartOrbitFace graphData.toRotationSystem d0 =
        dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha d1) := by
    simpa [d0, d1] using boundaryOrder_sameFace_alpha_next
      graphData deleted cyclicData 0
  have hface30 :
      dartOrbitFace graphData.toRotationSystem d3 =
        dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha d0) := by
    simpa [d0, d3] using boundaryOrder_sameFace_alpha_next
      graphData deleted cyclicData 3
  have hzeroNe :
      labels (dartOrbitFace graphData.toRotationSystem d0) ≠
        labels (dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha d0)) := by
    exact (hexact d0).2 hzero
  have honeEq :
      labels (dartOrbitFace graphData.toRotationSystem d1) =
        labels (dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha d1)) := by
    apply not_ne_iff.mp
    exact fun hne ↦ hone ((hexact d1).1 hne)
  have honeThreeNe :
      labels (dartOrbitFace graphData.toRotationSystem d1) ≠
        labels (dartOrbitFace graphData.toRotationSystem d3) := by
    intro heq
    apply hzeroNe
    calc
      labels (dartOrbitFace graphData.toRotationSystem d0) =
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha d1)) := congrArg labels hface01
      _ = labels (dartOrbitFace graphData.toRotationSystem d1) := honeEq.symm
      _ = labels (dartOrbitFace graphData.toRotationSystem d3) := heq
      _ = labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha d0)) := congrArg labels hface30
  have hrouteExact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        (graphData.toRotationSystem.edgeOf dart).1 ∈ separator.edges :=
    hexact
  have hfirstNot :
      (graphData.toRotationSystem.edgeOf (route.firstDart hrouteNil)).1 ∉
        separator.edges := by
    apply hrouteDisjoint
    change (route.firstDart hrouteNil).edge ∈ route.edges
    rw [route.edge_firstDart hrouteNil]
    exact route.mk_start_snd_mem_edges hrouteNil
  have hlastNot :
      (graphData.toRotationSystem.edgeOf
        (graphData.toRotationSystem.alpha
          (route.lastDart hrouteNil))).1 ∉ separator.edges := by
    rw [graphData.toRotationSystem.edge_alpha]
    apply hrouteDisjoint
    change (route.lastDart hrouteNil).edge ∈ route.edges
    rw [route.edge_lastDart hrouteNil]
    exact route.mk_penultimate_end_mem_edges hrouteNil
  have hfirstLabels :
      labels (dartOrbitFace graphData.toRotationSystem d1) =
        labels (dartOrbitFace graphData.toRotationSystem
          (route.firstDart hrouteNil)) := by
    apply graphData.toRotationSystem.labels_eq_of_distinct_dartsAt_of_edges_not_cut
      hcubic hrotation labels
        (fun edge : G.edgeSet ↦ edge.1 ∈ separator.edges)
        hrouteExact d1 (route.firstDart hrouteNil)
    · simp [d1]
    · exact hfirstNe.symm
    · exact hone
    · exact hfirstNot
  have hlastLabels :
      labels (dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha (route.lastDart hrouteNil))) =
        labels (dartOrbitFace graphData.toRotationSystem d3) := by
    apply graphData.toRotationSystem.labels_eq_of_distinct_dartsAt_of_edges_not_cut
      hcubic hrotation labels
        (fun edge : G.edgeSet ↦ edge.1 ∈ separator.edges)
        hrouteExact
        (graphData.toRotationSystem.alpha (route.lastDart hrouteNil)) d3
    · simp [d3]
    · exact hlastNe
    · exact hlastNot
    · exact hthree
  have htransport :=
    graphData.trail_labels_eq_firstDart_alpha_lastDart_of_walk_edges_not_cut
      hcubic hrotation labels
        (fun edge : G.edgeSet ↦ edge.1 ∈ separator.edges)
        hrouteExact route hrouteNil hrouteTrail hrouteDisjoint
  apply honeThreeNe
  exact hfirstLabels.trans (htransport.trans hlastLabels)

/-- In a spherical cubic rotation system, two edge-disjoint retained-side
trails cannot join the alternating port pairs `0`--`2` and `1`--`3` of an
exact cyclic four-boundary. -/
theorem no_edge_disjoint_opposite_retained_trails
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (firstPath : (CyclicCutSideGraph cut.compl).Walk
      (commonRetainedPort graphData cut cyclicData 0)
      (commonRetainedPort graphData cut cyclicData 2))
    (secondPath : (CyclicCutSideGraph cut.compl).Walk
      (commonRetainedPort graphData cut cyclicData 1)
      (commonRetainedPort graphData cut cyclicData 3))
    (deletedPath : (CyclicCutSideGraph cut).Walk
      (commonDeletedPort graphData cut cyclicData 2)
      (commonDeletedPort graphData cut cyclicData 0))
    (hfirstTrail : firstPath.IsTrail)
    (hsecondTrail : secondPath.IsTrail)
    (hsecondNil : ¬secondPath.Nil)
    (hdeletedTrail : deletedPath.IsTrail)
    (hdisjoint : firstPath.edges.Disjoint secondPath.edges) :
    False := by
  let separator := oppositeCutClosure graphData cut cyclicData
    firstPath deletedPath
  let route := cutSideWalkToAmbient cut.compl secondPath
  have hseparator : separator.IsTrail :=
    oppositeCutClosure_isTrail graphData cut cyclicData
      firstPath deletedPath hfirstTrail hdeletedTrail
  have hrouteNil : ¬route.Nil := by
    intro hnil
    apply hsecondNil
    exact Iff.mp (SimpleGraph.Walk.nil_map_iff
      (p := secondPath) (f := cutSideGraphHom cut.compl)) hnil
  have hrouteTrail : route.IsTrail :=
    cutSideWalkToAmbient_isTrail cut.compl hsecondTrail
  have hfirstSecondAmbient :
      (cutSideWalkToAmbient cut.compl firstPath).edges.Disjoint
        route.edges := by
    exact cutSideWalkToAmbient_edges_disjoint_of_disjoint
      cut.compl firstPath secondPath hdisjoint
  have hsecondDeletedAmbient :
      route.edges.Disjoint
        (cutSideWalkToAmbient cut deletedPath).edges :=
    (cutSideWalkToAmbient_edges_disjoint_compl
      cut deletedPath secondPath).symm
  have hrouteDisjoint : ∀ edge : G.edgeSet,
      edge.1 ∈ route.edges → edge.1 ∉ separator.edges := by
    intro edge hroute hseparatorEdge
    dsimp only [separator] at hseparatorEdge
    rw [oppositeCutClosure,
      SimpleGraph.Walk.edges_append] at hseparatorEdge
    rcases List.mem_append.mp hseparatorEdge with hfirst | hreturn
    · exact (List.disjoint_left.mp hfirstSecondAmbient) hfirst hroute
    · rw [oppositeCutReturn, SimpleGraph.Walk.edges_append,
        SimpleGraph.Walk.edges_append] at hreturn
      simp only [commonCutWalk_edges_eq,
        SimpleGraph.Walk.edges_reverse, List.reverse_singleton,
        List.mem_append, List.mem_singleton] at hreturn
      rcases hreturn with hedge2 | hdeleted | hedge0
      · rw [hedge2] at hroute
        have hedge2Cut :
            (graphData.toRotationSystem.edgeOf
              (cyclicData.boundaryOrder 2).1.1) ∈ cut.compl.edgeCut := by
          exact commonBoundaryEdge_mem_cut graphData cut cyclicData 2
        exact (cutEdge_not_mem_cutSideWalkToAmbient_edges
          cut.compl hedge2Cut secondPath) hroute
      · exact (List.disjoint_left.mp hsecondDeletedAmbient) hroute hdeleted
      · rw [hedge0] at hroute
        have hedge0Cut :
            (graphData.toRotationSystem.edgeOf
              (cyclicData.boundaryOrder 0).1.1) ∈ cut.compl.edgeCut := by
          exact commonBoundaryEdge_mem_cut graphData cut cyclicData 0
        exact (cutEdge_not_mem_cutSideWalkToAmbient_edges
          cut.compl hedge0Cut secondPath) hroute
  have hfirstNe : route.firstDart hrouteNil ≠
      (cyclicData.boundaryOrder 1).1.1 := by
    intro heq
    have hedge1Cut :
        (graphData.toRotationSystem.edgeOf
          (cyclicData.boundaryOrder 1).1.1) ∈ cut.compl.edgeCut := by
      exact commonBoundaryEdge_mem_cut graphData cut cyclicData 1
    apply (cutEdge_not_mem_cutSideWalkToAmbient_edges
      cut.compl hedge1Cut secondPath)
    change (cyclicData.boundaryOrder 1).1.1.edge ∈ route.edges
    rw [← heq, route.edge_firstDart hrouteNil]
    exact route.mk_start_snd_mem_edges hrouteNil
  have hlastNe : graphData.toRotationSystem.alpha
        (route.lastDart hrouteNil) ≠
      (cyclicData.boundaryOrder 3).1.1 := by
    intro heq
    have hedge3Cut :
        (graphData.toRotationSystem.edgeOf
          (cyclicData.boundaryOrder 3).1.1) ∈ cut.compl.edgeCut := by
      exact commonBoundaryEdge_mem_cut graphData cut cyclicData 3
    apply (cutEdge_not_mem_cutSideWalkToAmbient_edges
      cut.compl hedge3Cut secondPath)
    have hedgeEq : graphData.toRotationSystem.edgeOf
          (route.lastDart hrouteNil) =
        graphData.toRotationSystem.edgeOf
          (cyclicData.boundaryOrder 3).1.1 := by
      calc
        graphData.toRotationSystem.edgeOf (route.lastDart hrouteNil) =
            graphData.toRotationSystem.edgeOf
              (graphData.toRotationSystem.alpha
                (route.lastDart hrouteNil)) :=
          (graphData.toRotationSystem.edge_alpha
            (route.lastDart hrouteNil)).symm
        _ = graphData.toRotationSystem.edgeOf
              (cyclicData.boundaryOrder 3).1.1 :=
          congrArg graphData.toRotationSystem.edgeOf heq
    rw [← hedgeEq]
    change (route.lastDart hrouteNil).edge ∈ route.edges
    rw [route.edge_lastDart hrouteNil]
    exact route.mk_penultimate_end_mem_edges hrouteNil
  have hzeroSeparator :
      (graphData.toRotationSystem.edgeOf
        (cyclicData.boundaryOrder 0).1.1).1 ∈ separator.edges := by
    exact (commonBoundaryEdge_mem_oppositeCutClosure_edges_iff
      graphData cut cyclicData firstPath deletedPath 0).2 (Or.inl rfl)
  have honeSeparator :
      (graphData.toRotationSystem.edgeOf
        (cyclicData.boundaryOrder 1).1.1).1 ∉ separator.edges := by
    intro hone
    have := (commonBoundaryEdge_mem_oppositeCutClosure_edges_iff
      graphData cut cyclicData firstPath deletedPath 1).1 hone
    rcases this with h | h
    · exact (by decide : (1 : Fin 4) ≠ 0) h
    · exact (by decide : (1 : Fin 4) ≠ 2) h
  have hthreeSeparator :
      (graphData.toRotationSystem.edgeOf
        (cyclicData.boundaryOrder 3).1.1).1 ∉ separator.edges := by
    intro hthree
    have := (commonBoundaryEdge_mem_oppositeCutClosure_edges_iff
      graphData cut cyclicData firstPath deletedPath 3).1 hthree
    rcases this with h | h
    · exact (by decide : (3 : Fin 4) ≠ 0) h
    · exact (by decide : (3 : Fin 4) ≠ 2) h
  exact no_disjoint_trail_between_one_and_three graphData
    htwoSided hdual hconnected hsphere hcubic hrotation
    (cyclicCutVertexSide cut) cyclicData separator hseparator
    hzeroSeparator honeSeparator hthreeSeparator route hrouteNil
    hrouteTrail hrouteDisjoint hfirstNe hlastNe

/-- Exact cyclic four-connectivity supplies the deleted-side path required
by the alternating-trail obstruction. -/
theorem no_edge_disjoint_opposite_retained_trails_of_exact_cut
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (firstPath : (CyclicCutSideGraph cut.compl).Walk
      (commonRetainedPort graphData cut cyclicData 0)
      (commonRetainedPort graphData cut cyclicData 2))
    (secondPath : (CyclicCutSideGraph cut.compl).Walk
      (commonRetainedPort graphData cut cyclicData 1)
      (commonRetainedPort graphData cut cyclicData 3))
    (hfirstTrail : firstPath.IsTrail)
    (hsecondTrail : secondPath.IsTrail)
    (hsecondNil : ¬secondPath.Nil)
    (hdisjoint : firstPath.edges.Disjoint secondPath.edges) :
    False := by
  have hdeletedConnected : (CyclicCutSideGraph cut).Connected :=
    induce_side_connected_of_card_eq hconnected hcyclic cut hcard
  rcases hdeletedConnected.exists_isPath
      (commonDeletedPort graphData cut cyclicData 2)
      (commonDeletedPort graphData cut cyclicData 0) with
    ⟨deletedPath, hdeletedPath⟩
  exact no_edge_disjoint_opposite_retained_trails graphData
    htwoSided hdual hconnected hsphere hcubic hrotation cut cyclicData
    firstPath secondPath deletedPath hfirstTrail hsecondTrail hsecondNil
    hdeletedPath.isTrail hdisjoint

end

end GoertzelV24FourEdgeCutAlternatingTrail

end Mettapedia.GraphTheory.FourColor
