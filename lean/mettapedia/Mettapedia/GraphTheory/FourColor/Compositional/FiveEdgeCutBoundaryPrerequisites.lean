import Mettapedia.GraphTheory.FourColor.Compositional.CutPairDeletionConnectivity
import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutBoundaryOrder
import Mettapedia.GraphTheory.FourColor.ExactSizedCyclicEdgeCut

set_option maxRecDepth 100000

/-!
# Boundary-order prerequisites for an exact cyclic five-edge cut

This file separates the finite permutation facts and the generic exact-cut
facts from the remaining planar exclusion of a two-cycle in the boundary
first-return permutation.  No boundary colourings occur here.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace FiveEdgeCutBoundaryPrerequisites

open Equiv Equiv.Perm
open CutPairDeletionConnectivity
open GoertzelV24CyclicExactCutConnectedSides
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FourEdgeCutBoundaryOrder
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24ThreeEdgeCutMinimality
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- A fixed-point-free permutation of five points is either transitive or
contains a two-cycle. -/
theorem fixedPointFree_perm_card_five_transitive_or_twoCycle
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hcard : Fintype.card A = 5)
    (hfixed : ∀ point, perm point ≠ point) :
    (∀ left right, perm.SameCycle left right) ∨
      ∃ point, perm point ≠ point ∧ perm (perm point) = point := by
  let coordinate : A ≃ Fin 5 := Fintype.equivFinOfCardEq hcard
  let coordinatePerm : Equiv.Perm (Fin 5) := coordinate.permCongr perm
  have hcoordinateFixed : ∀ point, coordinatePerm point ≠ point := by
    intro point hpoint
    apply hfixed (coordinate.symm point)
    apply coordinate.injective
    simpa [coordinatePerm, Equiv.permCongr_apply] using hpoint
  have hfinite :
      (∀ left right, coordinatePerm.SameCycle left right) ∨
        ∃ point, coordinatePerm (coordinatePerm point) = point := by
    have hclassification : ∀ (finitePerm : Equiv.Perm (Fin 5)),
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

/-- A transitive permutation of a five-point carrier admits cyclic
coordinates in which it is the standard positive rotation of `Fin 5`. -/
theorem transitive_perm_card_five_exists_finRotate_coordinate
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hcard : Fintype.card A = 5)
    (htransitive : ∀ left right, perm.SameCycle left right) :
    ∃ coordinate : Fin 5 ≃ A,
      perm = coordinate.permCongr (finRotate 5) := by
  let ambientCoordinate : A ≃ Fin 5 := Fintype.equivFinOfCardEq hcard
  let coordinatePerm : Equiv.Perm (Fin 5) :=
    ambientCoordinate.permCongr perm
  have hcoordinateTransitive : ∀ left right,
      coordinatePerm.SameCycle left right := by
    intro left right
    simpa [coordinatePerm] using
      (permCongr_sameCycle_iff ambientCoordinate perm
        (ambientCoordinate.symm left) (ambientCoordinate.symm right)).2
          (htransitive (ambientCoordinate.symm left)
            (ambientCoordinate.symm right))
  have hfinite : ∀ (finitePerm : Equiv.Perm (Fin 5)),
      (∀ left right, finitePerm.SameCycle left right) →
        ∃ coordinate : Fin 5 ≃ Fin 5,
          finitePerm = coordinate.permCongr (finRotate 5) := by
    decide
  rcases hfinite coordinatePerm hcoordinateTransitive with
    ⟨finiteCoordinate, hfiniteCoordinate⟩
  let coordinate : Fin 5 ≃ A :=
    finiteCoordinate.trans ambientCoordinate.symm
  refine ⟨coordinate, ?_⟩
  apply Equiv.ext
  intro point
  apply ambientCoordinate.injective
  have happly := DFunLike.congr_fun hfiniteCoordinate
    (ambientCoordinate point)
  simpa [coordinatePerm, coordinate, Equiv.permCongr_apply] using happly

/-- The retained boundary carrier of an exact cyclic five-edge cut has five
points. -/
theorem card_boundaryDart_exactCutVertexSide_eq_five
    (graphData : SimpleGraphDartRotation.Data G)
    (cut : ExactSizedCyclicEdgeCut G 5) :
    Fintype.card (BoundaryDart graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut))) = 5 := by
  rw [card_boundaryDart_deletedRegionKeep,
    vertexSetCrossingEdges_exactCutVertexSide graphData cut, cut.hcard_eq]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- At cyclic connectivity five, an exact cyclic five-edge cut has connected
induced shores. -/
theorem induce_both_sides_connected_of_card_eq_five
    (hconnected : G.Connected)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : ExactSizedCyclicEdgeCut G 5) :
    (G.induce cut.side).Connected ∧
      (G.induce (fun vertex => ¬ cut.side vertex)).Connected :=
  induce_both_sides_connected_of_exactSized hconnected hcyclic cut

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Deleting any two distinct edges of an exact five-edge bond leaves the
graph connected.  Any one of the three remaining cut edges joins the two
connected shores. -/
theorem deleteEdges_pair_connected_of_exactCyclicFiveCut
    (cut : ExactSizedCyclicEdgeCut G 5)
    (hsideConnected : (G.induce cut.side).Connected)
    (hcomplementConnected :
      (G.induce (fun vertex ↦ ¬ cut.side vertex)).Connected)
    (first second : G.edgeSet) (hfirstCut : first ∈ cut.edgeCut)
    (hsecondCut : second ∈ cut.edgeCut) (hedgesNe : first ≠ second) :
    (G.deleteEdges ({first.1, second.1} : Set (Sym2 V))).Connected := by
  classical
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
    rw [cut.hcard_eq, hpairCard] at hcardLe
    omega
  rcases hremaining with
    ⟨third, hthirdCut, hthirdFirst, hthirdSecond⟩
  exact deleteEdges_pair_connected_of_connected_shores cut.side
    hsideConnected hcomplementConnected first second third
    ((cut.hcut_eq first).1 hfirstCut)
    ((cut.hcut_eq second).1 hsecondCut)
    ((cut.hcut_eq third).1 hthirdCut) hthirdFirst hthirdSecond

end

end FiveEdgeCutBoundaryPrerequisites

end Mettapedia.GraphTheory.FourColor.Compositional
