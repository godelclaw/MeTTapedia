import Mettapedia.GraphTheory.FourColor.GoertzelV24CyclicExactCutConnectedSides
import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutBoundaryData
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24SharedFacesTwoEdgeSeparator

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FourEdgeCutBoundaryOrder

open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24CyclicExactCutConnectedSides
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourEdgeCutBoundaryData
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SharedFacesTwoEdgeSeparator
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24ThreeEdgeCutMinimality
open GoertzelV24TwoEdgeCutCapGeometry
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A fixed-point-free permutation of four points is either transitive or
contains a two-cycle. -/
theorem fixedPointFree_perm_card_four_transitive_or_twoCycle
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hcard : Fintype.card A = 4)
    (hfixed : ∀ point, perm point ≠ point) :
    (∀ left right, perm.SameCycle left right) ∨
      ∃ point, perm point ≠ point ∧ perm (perm point) = point := by
  let coordinate : A ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  let coordinatePerm : Equiv.Perm (Fin 4) := coordinate.permCongr perm
  have hcoordinateFixed : ∀ point, coordinatePerm point ≠ point := by
    intro point hpoint
    apply hfixed (coordinate.symm point)
    apply coordinate.injective
    simpa [coordinatePerm, Equiv.permCongr_apply] using hpoint
  have hfinite :
      (∀ left right, coordinatePerm.SameCycle left right) ∨
        ∃ point, coordinatePerm (coordinatePerm point) = point := by
    have hclassification : ∀ (finitePerm : Equiv.Perm (Fin 4)),
        (∀ point, finitePerm point ≠ point) →
          (∀ left right, finitePerm.SameCycle left right) ∨
            ∃ point, finitePerm (finitePerm point) = point := by
      decide
    exact hclassification coordinatePerm hcoordinateFixed
  rcases hfinite with htransitive | ⟨point, htwoCycle⟩
  · left
    intro left right
    exact (permCongr_sameCycle_iff coordinate perm left right).1
      (htransitive (coordinate left) (coordinate right))
  · right
    let source := coordinate.symm point
    refine ⟨source, hfixed source, ?_⟩
    apply coordinate.injective
    simpa [source, coordinatePerm, Equiv.permCongr_apply] using htwoCycle

/-- A transitive permutation of a four-point carrier admits cyclic
coordinates in which it is the standard positive rotation of `Fin 4`. -/
theorem transitive_perm_card_four_exists_finRotate_coordinate
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hcard : Fintype.card A = 4)
    (htransitive : ∀ left right, perm.SameCycle left right) :
    ∃ coordinate : Fin 4 ≃ A,
      perm = coordinate.permCongr (finRotate 4) := by
  let ambientCoordinate : A ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  let coordinatePerm : Equiv.Perm (Fin 4) :=
    ambientCoordinate.permCongr perm
  have hcoordinateTransitive : ∀ left right,
      coordinatePerm.SameCycle left right := by
    intro left right
    simpa [coordinatePerm] using
      (permCongr_sameCycle_iff ambientCoordinate perm
        (ambientCoordinate.symm left) (ambientCoordinate.symm right)).2
          (htransitive (ambientCoordinate.symm left)
            (ambientCoordinate.symm right))
  have hfinite : ∀ (finitePerm : Equiv.Perm (Fin 4)),
      (∀ left right, finitePerm.SameCycle left right) →
        ∃ coordinate : Fin 4 ≃ Fin 4,
          finitePerm = coordinate.permCongr (finRotate 4) := by
    decide
  rcases hfinite coordinatePerm hcoordinateTransitive with
    ⟨finiteCoordinate, hfiniteCoordinate⟩
  let coordinate : Fin 4 ≃ A :=
    finiteCoordinate.trans ambientCoordinate.symm
  refine ⟨coordinate, ?_⟩
  apply Equiv.ext
  intro point
  apply ambientCoordinate.injective
  have happly := DFunLike.congr_fun hfiniteCoordinate
    (ambientCoordinate point)
  simpa [coordinatePerm, coordinate, Equiv.permCongr_apply] using happly

/-- The endpoint-computed crossing edges of the finite selected side are
exactly the edge set carried by the predicate-defined cyclic cut. -/
theorem vertexSetCrossingEdges_cyclicCutVertexSide
    (graphData : Data G) (cut : SmallCyclicEdgeCut G) :
    vertexSetCrossingEdges graphData.toRotationSystem
        (cyclicCutVertexSide cut) = cut.edgeCut := by
  ext edge
  rw [mem_simpleGraph_vertexSetCrossingEdges_iff]
  simpa [mem_cyclicCutVertexSide_iff] using (cut.hcut_eq edge).symm

/-- The retained boundary carrier of an exact four-cut has four points. -/
theorem card_boundaryDart_cyclicCutVertexSide_eq_four
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (hcard : cut.edgeCut.card = 4) :
    Fintype.card (BoundaryDart graphData.toRotationSystem
      (deletedRegionKeep (cyclicCutVertexSide cut))) = 4 := by
  rw [card_boundaryDart_deletedRegionKeep,
    vertexSetCrossingEdges_cyclicCutVertexSide graphData cut, hcard]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Deleting any two distinct edges of a four-edge bond leaves the graph
connected. Each induced side remains connected, and either undeleted cut
edge joins the two sides. -/
theorem deleteEdges_pair_connected_of_fourEdgeBond
    (hconnected : G.Connected) (cut : SmallCyclicEdgeCut G)
    (hcard : cut.edgeCut.card = 4)
    (hsideConnected : (G.induce cut.side).Connected)
    (hcomplementConnected :
      (G.induce (fun vertex ↦ ¬ cut.side vertex)).Connected)
    (first second : G.edgeSet) (hfirstCut : first ∈ cut.edgeCut)
    (hsecondCut : second ∈ cut.edgeCut) (hedgesNe : first ≠ second) :
    (G.deleteEdges ({first.1, second.1} : Set (Sym2 V))).Connected := by
  classical
  let removed : Set (Sym2 V) := {first.1, second.1}
  have hremaining : ∃ third ∈ cut.edgeCut,
      third ≠ first ∧ third ≠ second := by
    by_contra hnone
    push Not at hnone
    have hsubset : cut.edgeCut ⊆ ({first, second} : Finset G.edgeSet) := by
      intro third hthird
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hthirdFirst : third = first
      · exact Or.inl hthirdFirst
      · exact Or.inr (hnone third hthird hthirdFirst)
    have hcardLe := Finset.card_le_card hsubset
    have hpairCard : ({first, second} : Finset G.edgeSet).card = 2 := by
      simp [hedgesNe]
    rw [hcard, hpairCard] at hcardLe
    omega
  rcases hremaining with
    ⟨third, hthirdCut, hthirdFirst, hthirdSecond⟩
  rcases (cut.hcut_eq third).1 hthirdCut with
    ⟨inner, outer, hinnerEdge, houterEdge, hinnerSide, houterSide⟩
  have hinnerOuterNe : inner ≠ outer := by
    intro heq
    exact houterSide (heq ▸ hinnerSide)
  have hthirdPair : (third.1 : Sym2 V) = s(inner, outer) :=
    sym2_eq_mk_of_mem_of_mem_of_ne
      hinnerEdge houterEdge hinnerOuterNe
  have hinnerOuterAdj : G.Adj inner outer := by
    apply (SimpleGraph.mem_edgeSet G).1
    rw [← hthirdPair]
    exact third.2
  have hsideEdgeAvoids : ∀ {left right : V},
      cut.side left → cut.side right → G.Adj left right →
        s(left, right) ∉ removed := by
    intro left right hleft hright hadj hmem
    rcases hmem with hfirst | hsecond
    · have hopposite :=
        not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
          hfirst.symm ((cut.hcut_eq first).1 hfirstCut)
      exact hopposite ⟨fun _ ↦ hright, fun _ ↦ hleft⟩
    · have hopposite :=
        not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
          hsecond.symm ((cut.hcut_eq second).1 hsecondCut)
      exact hopposite ⟨fun _ ↦ hright, fun _ ↦ hleft⟩
  have hcomplementEdgeAvoids : ∀ {left right : V},
      ¬ cut.side left → ¬ cut.side right → G.Adj left right →
        s(left, right) ∉ removed := by
    intro left right hleft hright hadj hmem
    rcases hmem with hfirst | hsecond
    · have hopposite :=
        not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
          hfirst.symm ((cut.hcut_eq first).1 hfirstCut)
      exact hopposite
        ⟨fun hleftSide ↦ (hleft hleftSide).elim,
          fun hrightSide ↦ (hright hrightSide).elim⟩
    · have hopposite :=
        not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
          hsecond.symm ((cut.hcut_eq second).1 hsecondCut)
      exact hopposite
        ⟨fun hleftSide ↦ (hleft hleftSide).elim,
          fun hrightSide ↦ (hright hrightSide).elim⟩
  let sideHom : G.induce cut.side →g G.deleteEdges removed :=
    { toFun := Subtype.val
      map_rel' := by
        intro left right hadj
        apply SimpleGraph.deleteEdges_adj.mpr
        exact ⟨hadj,
          hsideEdgeAvoids left.2 right.2 hadj⟩ }
  let complementHom :
      G.induce (fun vertex ↦ ¬ cut.side vertex) →g
        G.deleteEdges removed :=
    { toFun := Subtype.val
      map_rel' := by
        intro left right hadj
        apply SimpleGraph.deleteEdges_adj.mpr
        exact ⟨hadj,
          hcomplementEdgeAvoids left.2 right.2 hadj⟩ }
  have hsideReach : ∀ {left right : V},
      cut.side left → cut.side right →
        (G.deleteEdges removed).Reachable left right := by
    intro left right hleft hright
    simpa [sideHom] using
      (hsideConnected ⟨left, hleft⟩ ⟨right, hright⟩).map sideHom
  have hcomplementReach : ∀ {left right : V},
      ¬ cut.side left → ¬ cut.side right →
        (G.deleteEdges removed).Reachable left right := by
    intro left right hleft hright
    simpa [complementHom] using
      (hcomplementConnected ⟨left, hleft⟩
        ⟨right, hright⟩).map complementHom
  have hthirdAvoids : s(inner, outer) ∉ removed := by
    intro hmem
    rcases hmem with hfirst | hsecond
    · apply hthirdFirst
      apply Subtype.ext
      exact hthirdPair.trans hfirst
    · apply hthirdSecond
      apply Subtype.ext
      exact hthirdPair.trans hsecond
  have hcrossing : (G.deleteEdges removed).Adj inner outer :=
    SimpleGraph.deleteEdges_adj.mpr ⟨hinnerOuterAdj, hthirdAvoids⟩
  letI : Nonempty V := hconnected.nonempty
  have hdeletedConnected : (G.deleteEdges removed).Connected := by
    refine ⟨?_⟩
    intro left right
    by_cases hleft : cut.side left <;>
      by_cases hright : cut.side right
    · exact hsideReach hleft hright
    · exact (hsideReach hleft hinnerSide).trans
        (hcrossing.reachable.trans
          (hcomplementReach houterSide hright))
    · exact (hcomplementReach hleft houterSide).trans
        (hcrossing.symm.reachable.trans
          (hsideReach hinnerSide hright))
    · exact hcomplementReach hleft hright
  simpa [removed] using hdeletedConnected

/-- No boundary dart can be fixed by the deleted-side first-return order in
a two-sided map: that would put both orientations of its edge on one face. -/
theorem deletedBoundarySuccessor_fixedPointFree
    (RS : RotationSystem V E) (deleted : Finset V)
    (htwoSided : OrbitFacesTwoSided RS) :
    ∀ boundary : BoundaryDart RS (deletedRegionKeep deleted),
      deletedRegionBoundarySuccessor RS deleted boundary ≠ boundary := by
  intro boundary hfixed
  apply htwoSided boundary.1.1
  change Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) boundary.1.1 =
    Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
      (RS.alpha boundary.1.1)
  apply Quotient.sound
  change RS.phi.SameCycle boundary.1.1 (RS.alpha boundary.1.1)
  simpa [hfixed] using
    (deletedRegionBoundarySuccessor_sameAmbientFace_alpha
      RS deleted boundary)

/-- If two retained boundary darts form a two-cycle of the deleted-side
successor, their distinct edges have the same two ambient facial sides. -/
theorem twoCycle_boundaryEdges_share_face_pair
    (RS : RotationSystem V E) (deleted : Finset V)
    (htwoSided : OrbitFacesTwoSided RS)
    (first : BoundaryDart RS (deletedRegionKeep deleted))
    (hfirstNe : deletedRegionBoundarySuccessor RS deleted first ≠ first)
    (htwoCycle : deletedRegionBoundarySuccessor RS deleted
        (deletedRegionBoundarySuccessor RS deleted first) = first) :
    let second := deletedRegionBoundarySuccessor RS deleted first
    let left := dartOrbitFace RS first.1.1
    let right := dartOrbitFace RS (RS.alpha first.1.1)
    left ≠ right ∧ RS.edgeOf first.1.1 ≠ RS.edgeOf second.1.1 ∧
      RS.edgeOf first.1.1 ∈ orbitFaceBoundary RS left ∧
      RS.edgeOf first.1.1 ∈ orbitFaceBoundary RS right ∧
      RS.edgeOf second.1.1 ∈ orbitFaceBoundary RS left ∧
      RS.edgeOf second.1.1 ∈ orbitFaceBoundary RS right := by
  dsimp only
  let second := deletedRegionBoundarySuccessor RS deleted first
  have hfirstFace : dartOrbitFace RS first.1.1 =
      dartOrbitFace RS (RS.alpha second.1.1) := by
    exact Quotient.sound
      (deletedRegionBoundarySuccessor_sameAmbientFace_alpha
        RS deleted first)
  have hsecondFace : dartOrbitFace RS second.1.1 =
      dartOrbitFace RS (RS.alpha first.1.1) := by
    apply Quotient.sound
    change RS.phi.SameCycle second.1.1 (RS.alpha first.1.1)
    simpa [second, htwoCycle] using
      (deletedRegionBoundarySuccessor_sameAmbientFace_alpha
        RS deleted second)
  have hedgesNe : RS.edgeOf first.1.1 ≠ RS.edgeOf second.1.1 := by
    intro hedges
    apply hfirstNe
    apply boundaryDart_eq_of_edgeOf_eq
    exact hedges.symm
  refine ⟨htwoSided first.1.1, hedgesNe,
    edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS first.1.1, ?_, ?_, ?_⟩
  · simpa [RS.edge_alpha] using edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      RS (RS.alpha first.1.1)
  · rw [hfirstFace]
    simpa [RS.edge_alpha] using edgeOf_mem_orbitFaceBoundary_dartOrbitFace
      RS (RS.alpha second.1.1)
  · rw [← hsecondFace]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS second.1.1

/-- For an exact cyclic four-edge bond in a connected spherical graph-backed
map, the deleted-side first-return order is one four-cycle. A second boundary
component would be a two-cycle, hence a separating pair of cut edges, whereas
either of the other two cut edges still joins the connected induced sides. -/
theorem deletedBoundarySuccessor_sameCycle_of_exactCyclicFourCut
    (graphData : Data G)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4) :
    ∀ first second : BoundaryDart graphData.toRotationSystem
        (deletedRegionKeep (cyclicCutVertexSide cut)),
      (deletedRegionBoundarySuccessor graphData.toRotationSystem
        (cyclicCutVertexSide cut)).SameCycle first second := by
  let RS := graphData.toRotationSystem
  let deleted := cyclicCutVertexSide cut
  let successor := deletedRegionBoundarySuccessor RS deleted
  have hsides := induce_both_sides_connected_of_card_eq_four
    hconnected hcyclic cut hcard
  have hboundaryCard : Fintype.card
      (BoundaryDart RS (deletedRegionKeep deleted)) = 4 := by
    exact card_boundaryDart_cyclicCutVertexSide_eq_four
      graphData cut hcard
  have hfixed : ∀ boundary : BoundaryDart RS
      (deletedRegionKeep deleted), successor boundary ≠ boundary := by
    exact deletedBoundarySuccessor_fixedPointFree RS deleted htwoSided
  rcases fixedPointFree_perm_card_four_transitive_or_twoCycle
      successor hboundaryCard hfixed with htransitive | htwoCycle
  · exact htransitive
  · rcases htwoCycle with ⟨first, hfirstNe, hfirstTwoCycle⟩
    let second := successor first
    let left := dartOrbitFace RS first.1.1
    let right := dartOrbitFace RS (RS.alpha first.1.1)
    have hfacePair := twoCycle_boundaryEdges_share_face_pair
      RS deleted htwoSided first hfirstNe hfirstTwoCycle
    change left ≠ right ∧ RS.edgeOf first.1.1 ≠ RS.edgeOf second.1.1 ∧
        RS.edgeOf first.1.1 ∈ orbitFaceBoundary RS left ∧
        RS.edgeOf first.1.1 ∈ orbitFaceBoundary RS right ∧
        RS.edgeOf second.1.1 ∈ orbitFaceBoundary RS left ∧
        RS.edgeOf second.1.1 ∈ orbitFaceBoundary RS right at hfacePair
    rcases hfacePair with
      ⟨hfaces, hedgesNe, hfirstLeft, hfirstRight,
        hsecondLeft, hsecondRight⟩
    have hprimal : (rotationPrimalGraph RS).Connected := by
      change (rotationPrimalGraph graphData.toRotationSystem).Connected
      rw [rotationPrimalGraph_toRotationSystem_eq]
      exact hconnected
    have hdual := orbitFaceInteriorDual_connected
      RS hsphere.cubic hprimal hrotation
    have hseparator :=
      not_connected_deleteEdges_pair_of_shared_face_pair
        graphData htwoSided hdual hconnected hsphere hfaces hedgesNe
        hfirstLeft hfirstRight hsecondLeft hsecondRight
    have hfirstCut : RS.edgeOf first.1.1 ∈ cut.edgeCut := by
      rw [← vertexSetCrossingEdges_cyclicCutVertexSide graphData cut]
      exact boundaryDart_edge_mem_vertexSetCrossingEdges
        RS deleted first
    have hsecondCut : RS.edgeOf second.1.1 ∈ cut.edgeCut := by
      rw [← vertexSetCrossingEdges_cyclicCutVertexSide graphData cut]
      exact boundaryDart_edge_mem_vertexSetCrossingEdges
        RS deleted second
    have hstillConnected := deleteEdges_pair_connected_of_fourEdgeBond
      hconnected cut hcard hsides.1 hsides.2
      (RS.edgeOf first.1.1) (RS.edgeOf second.1.1)
      hfirstCut hsecondCut hedgesNe
    exact (hseparator hstillConnected).elim

/-- The two actual first-return orders on the complementary sides of an
exact cyclic four-edge cut have opposite orientation. -/
theorem retainedBoundarySuccessor_eq_deleted_inverse_of_exactCyclicFourCut
    (graphData : Data G)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4) :
    retainedRegionBoundarySuccessor graphData.toRotationSystem
        (deletedRegionKeep (cyclicCutVertexSide cut)) =
      (deletedRegionBoundarySuccessor graphData.toRotationSystem
        (cyclicCutVertexSide cut))⁻¹ := by
  have hsides := induce_both_sides_connected_of_card_eq_four
    hconnected hcyclic cut hcard
  have hkeep : deletedRegionKeep (cyclicCutVertexSide cut) =
      (fun vertex ↦ ¬ cut.side vertex) := by
    funext vertex
    simp [deletedRegionKeep, mem_cyclicCutVertexSide_iff]
  have hdeleted :
      (fun vertex ↦ ¬ deletedRegionKeep
        (cyclicCutVertexSide cut) vertex) = cut.side := by
    funext vertex
    simp [deletedRegionKeep, mem_cyclicCutVertexSide_iff]
  apply retained_boundarySuccessor_eq_deleted_inverse_of_planar_bond
    graphData (cyclicCutVertexSide cut) hsphere htwoSided hconnected hrotation
  · rw [hkeep]
    exact hsides.2
  · rw [hdeleted]
    exact hsides.1

/-- An exact cyclic four-edge cut therefore has genuine cyclic boundary
coordinates. In those coordinates the deleted-side order is positive
rotation and the retained-side order is its inverse. -/
theorem exists_boundaryOrder_of_exactCyclicFourCut
    (graphData : Data G)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4) :
    ∃ boundaryOrder : Fin 4 ≃
        BoundaryDart graphData.toRotationSystem
          (deletedRegionKeep (cyclicCutVertexSide cut)),
      deletedRegionBoundarySuccessor graphData.toRotationSystem
          (cyclicCutVertexSide cut) =
        boundaryOrder.permCongr (finRotate 4) ∧
      retainedRegionBoundarySuccessor graphData.toRotationSystem
          (deletedRegionKeep (cyclicCutVertexSide cut)) =
        (boundaryOrder.permCongr (finRotate 4))⁻¹ := by
  let successor := deletedRegionBoundarySuccessor
    graphData.toRotationSystem (cyclicCutVertexSide cut)
  have hboundaryCard : Fintype.card
      (BoundaryDart graphData.toRotationSystem
        (deletedRegionKeep (cyclicCutVertexSide cut))) = 4 :=
    card_boundaryDart_cyclicCutVertexSide_eq_four graphData cut hcard
  have htransitive : ∀ first second,
      successor.SameCycle first second :=
    deletedBoundarySuccessor_sameCycle_of_exactCyclicFourCut
      graphData hsphere htwoSided hconnected hrotation hcyclic cut hcard
  rcases transitive_perm_card_four_exists_finRotate_coordinate
      successor hboundaryCard htransitive with ⟨boundaryOrder, horder⟩
  refine ⟨boundaryOrder, horder, ?_⟩
  rw [retainedBoundarySuccessor_eq_deleted_inverse_of_exactCyclicFourCut
    graphData hsphere htwoSided hconnected hrotation hcyclic cut hcard]
  change successor⁻¹ = (boundaryOrder.permCongr (finRotate 4))⁻¹
  rw [horder]

end

end GoertzelV24FourEdgeCutBoundaryOrder

end Mettapedia.GraphTheory.FourColor
