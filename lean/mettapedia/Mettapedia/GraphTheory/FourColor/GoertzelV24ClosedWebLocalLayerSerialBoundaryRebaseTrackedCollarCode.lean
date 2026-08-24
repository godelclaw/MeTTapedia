import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedCoreRecurrence
import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedCarrierGraphFamilyCode

/-!
# A bounded code for the actual rebase tracked collar

The tracked rebase recurrence has two finite factors: the component relation
in the unchanged core and the genuinely local successor residual.  This file
transports both through one common carrier of at most twenty-eight edges and
retains all four literal rebase roles as named points.

The resulting `BoundedCarrierGraphFamilyCode` is a finite, graph-free value.
For each tracked color pair, closure of its inherited and local coded graphs
computes successor reachability exactly between collar coordinates.  This
does not yet combine tracked and facial recurrences into the complete rebase
support letter.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseTrackedCollarCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Stable ordering of the old rung, two new crossings, and new rung. -/
def sourceLocalLayerBoundaryRebaseRoleEquivFin :
    SourceLocalLayerBoundaryRebaseRole ≃ Fin 4 :=
  (Equiv.sumCongr (Equiv.refl (Fin 1))
      (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3)).trans
    (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4)

/-- The unchanged-core component relation for one tracked color pair, made
into a graph on the finite collar. -/
noncomputable def sourceLocalLayerBoundaryRebaseTrackedCoreComponentGraphAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair) : SimpleGraph G.edgeSet where
  Adj left right :=
    left ≠ right ∧
      left ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique
        offset hnext ∧
      right ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique
        offset hnext ∧
      (sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt corridor hunique offset
        hnext pair).Reachable left right
  symm := ⟨by
    rintro left right ⟨hne, hleft, hright, hreach⟩
    exact ⟨hne.symm, hright, hleft, hreach.symm⟩⟩
  loopless := ⟨by
    intro edge hadj
    exact hadj.1 rfl⟩

@[simp]
theorem sourceLocalLayerBoundaryRebaseTrackedCoreComponentGraphAt_adj
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair) (left right : G.edgeSet) :
    (sourceLocalLayerBoundaryRebaseTrackedCoreComponentGraphAt corridor hunique
      offset hnext pair).Adj left right ↔
      left ≠ right ∧
        left ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique
          offset hnext ∧
        right ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique
          offset hnext ∧
        (sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt corridor hunique offset
          hnext pair).Reachable left right :=
  Iff.rfl

theorem sourceLocalLayerBoundaryRebaseTrackedCoreComponentGraphAt_support_subset_collar
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair) :
    (sourceLocalLayerBoundaryRebaseTrackedCoreComponentGraphAt corridor hunique
      offset hnext pair).support ⊆
      sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
        hnext := by
  intro edge hedge
  rcases (SimpleGraph.mem_support _).1 hedge with ⟨other, hadj⟩
  exact hadj.2.1

/-- The core-component graph represents the ambient core relation exactly on
collar edges. -/
theorem sourceLocalLayerBoundaryRebaseTrackedCoreComponentGraphAt_reachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair) (left right : G.edgeSet)
    (hleft : left ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor
      hunique offset hnext)
    (hright : right ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor
      hunique offset hnext) :
    (sourceLocalLayerBoundaryRebaseTrackedCoreComponentGraphAt corridor hunique
      offset hnext pair).Reachable left right ↔
      (sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt corridor hunique offset
        hnext pair).Reachable left right := by
  constructor
  · intro hreach
    have hpath := (SimpleGraph.reachable_iff_reflTransGen left right).mp hreach
    exact Relation.ReflTransGen.trans_induction_on
      (motive := fun {first second} _ =>
        (sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt corridor hunique offset
          hnext pair).Reachable first second)
      hpath
      (fun _ => SimpleGraph.Reachable.rfl)
      (fun hadj => hadj.2.2.2)
      (fun _ _ hfirst hsecond => hfirst.trans hsecond)
  · intro hreach
    by_cases heq : left = right
    · subst right
      exact SimpleGraph.Reachable.rfl
    · exact SimpleGraph.Adj.reachable (show
        (sourceLocalLayerBoundaryRebaseTrackedCoreComponentGraphAt corridor
          hunique offset hnext pair).Adj left right from
          ⟨heq, hleft, hright, hreach⟩)

/-- Every named rebase role belongs to the finite tracked collar. -/
noncomputable def sourceLocalLayerBoundaryRebaseTrackedCollarPointAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (index : Fin 4) :
    {edge // edge ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor
      hunique offset hnext} := by
  let role := sourceLocalLayerBoundaryRebaseRoleEquivFin.symm index
  refine ⟨sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
    role, ?_⟩
  apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ _).2
  exact Or.inl ((mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff corridor
    hunique offset hnext _).2 ⟨role, rfl⟩)

/-- For each tracked pair, `false` codes the inherited core-component
relation and `true` codes the local successor residual. -/
noncomputable def sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    BoundedCarrierGraphFamilyCode 28 4 (TrackedColorPair × Bool) :=
  boundedCarrierGraphFamilyCode
    (sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset hnext)
    28 4
    (sourceLocalLayerBoundaryRebaseTrackedCollarAt_card_le_twentyEight corridor
      hunique offset hnext)
    (sourceLocalLayerBoundaryRebaseTrackedCollarPointAt corridor hunique offset
      hnext)
    (fun family => if family.2 then
      sourceLocalLayerBoundaryRebaseLocalTrackedGraphAt corridor hunique offset
        hnext family.1
    else
      sourceLocalLayerBoundaryRebaseTrackedCoreComponentGraphAt corridor hunique
        offset hnext family.1)

theorem sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt_false_reachable_iff_core
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair)
    (left right : {edge // edge ∈
      sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
        hnext}) :
    ((sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt corridor hunique offset
      hnext).graph (pair, false)).Reachable
        (carrierCoordinate _ left) (carrierCoordinate _ right) ↔
      (sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt corridor hunique offset
        hnext pair).Reachable left.1 right.1 := by
  have hcode := boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    (sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset hnext)
    28 4
    (sourceLocalLayerBoundaryRebaseTrackedCollarAt_card_le_twentyEight corridor
      hunique offset hnext)
    (sourceLocalLayerBoundaryRebaseTrackedCollarPointAt corridor hunique offset
      hnext)
    (fun family : TrackedColorPair × Bool => if family.2 then
      sourceLocalLayerBoundaryRebaseLocalTrackedGraphAt corridor hunique offset
        hnext family.1
    else
      sourceLocalLayerBoundaryRebaseTrackedCoreComponentGraphAt corridor hunique
        offset hnext family.1)
    (pair, false)
    (by simpa using
      (sourceLocalLayerBoundaryRebaseTrackedCoreComponentGraphAt_support_subset_collar
        corridor hunique offset hnext pair))
    left right
  simp only [Bool.false_eq_true, if_false] at hcode
  rw [sourceLocalLayerBoundaryRebaseTrackedCoreComponentGraphAt_reachable_iff
    corridor hunique offset hnext pair left.1 right.1 left.2 right.2] at hcode
  simpa [sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt] using hcode

theorem sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt_true_reachable_iff_local
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair)
    (left right : {edge // edge ∈
      sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
        hnext}) :
    ((sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt corridor hunique offset
      hnext).graph (pair, true)).Reachable
        (carrierCoordinate _ left) (carrierCoordinate _ right) ↔
      (sourceLocalLayerBoundaryRebaseLocalTrackedGraphAt corridor hunique offset
        hnext pair).Reachable left.1 right.1 := by
  have hcode := boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    (sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset hnext)
    28 4
    (sourceLocalLayerBoundaryRebaseTrackedCollarAt_card_le_twentyEight corridor
      hunique offset hnext)
    (sourceLocalLayerBoundaryRebaseTrackedCollarPointAt corridor hunique offset
      hnext)
    (fun family : TrackedColorPair × Bool => if family.2 then
      sourceLocalLayerBoundaryRebaseLocalTrackedGraphAt corridor hunique offset
        hnext family.1
    else
      sourceLocalLayerBoundaryRebaseTrackedCoreComponentGraphAt corridor hunique
        offset hnext family.1)
    (pair, true)
    (by simpa using
      (sourceLocalLayerBoundaryRebaseLocalTrackedGraphAt_support_subset_collar
        corridor hunique offset hnext pair))
    left right
  simpa [sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt] using hcode

/-- Successor tracked reachability is exactly the closure computed by the
bounded two-factor code. -/
theorem sourceLocalLayerBoundaryRebaseSuccessorTracked_reachable_iff_collarCode
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair) (left right : G.edgeSet)
    (hleft : left ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor
      hunique offset hnext)
    (hright : right ∈ sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor
      hunique offset hnext) :
    (sourceLocalLayerBoundaryRebaseSuccessorTrackedGraphAt corridor hunique
      offset hnext pair).Reachable left right ↔
      Relation.ReflTransGen
        (fun first second : Fin
            (sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt corridor hunique
              offset hnext).vertexCount.val =>
          ((sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt corridor hunique
            offset hnext).graph (pair, false)).Reachable first second ∨
          ((sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt corridor hunique
            offset hnext).graph (pair, true)).Reachable first second)
        (carrierCoordinate _ ⟨left, hleft⟩)
        (carrierCoordinate _ ⟨right, hright⟩) := by
  let carrier :=
    sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset hnext
  let coordinate := carrierCoordinate carrier
  rw [sourceLocalLayerBoundaryRebaseSuccessorTracked_reachable_iff_collarComponentClosure
    corridor hunique offset hnext pair left right hleft hright]
  have hstep (first second : {edge // edge ∈ carrier}) :
      (sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt corridor hunique offset
          hnext pair).Reachable first.1 second.1 ∨
        (sourceLocalLayerBoundaryRebaseLocalTrackedGraphAt corridor hunique
          offset hnext pair).Reachable first.1 second.1 ↔
      ((sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt corridor hunique offset
        hnext).graph (pair, false)).Reachable
          (coordinate first) (coordinate second) ∨
        ((sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt corridor hunique
          offset hnext).graph (pair, true)).Reachable
            (coordinate first) (coordinate second) := by
    constructor
    · rintro (hcore | hlocal)
      · exact Or.inl
          ((sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt_false_reachable_iff_core
            corridor hunique offset hnext pair first second).2 hcore)
      · exact Or.inr
          ((sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt_true_reachable_iff_local
            corridor hunique offset hnext pair first second).2 hlocal)
    · rintro (hcore | hlocal)
      · exact Or.inl
          ((sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt_false_reachable_iff_core
            corridor hunique offset hnext pair first second).1 hcore)
      · exact Or.inr
          ((sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt_true_reachable_iff_local
            corridor hunique offset hnext pair first second).1 hlocal)
  constructor
  · intro hclosure
    exact Relation.ReflTransGen.lift coordinate
      (fun first second h => (hstep first second).1 h) hclosure
  · intro hclosure
    have hlift : Relation.ReflTransGen
        (fun first second : {edge // edge ∈ carrier} =>
          (sourceLocalLayerBoundaryRebaseCoreTrackedGraphAt corridor hunique
              offset hnext pair).Reachable first.1 second.1 ∨
            (sourceLocalLayerBoundaryRebaseLocalTrackedGraphAt corridor hunique
              offset hnext pair).Reachable first.1 second.1)
        (coordinate.symm (coordinate ⟨left, hleft⟩))
        (coordinate.symm (coordinate ⟨right, hright⟩)) :=
      Relation.ReflTransGen.lift coordinate.symm
        (fun first second h =>
          (hstep (coordinate.symm first) (coordinate.symm second)).2 (by
            simpa only [Equiv.apply_symm_apply] using h)) hclosure
    simpa only [Equiv.symm_apply_apply] using hlift

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
