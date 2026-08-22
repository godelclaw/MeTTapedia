import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFaceCollarRecurrence
import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedCarrierGraphFamilyCode

/-!
# A bounded code for the actual rebase facial collar

The semantic collar recurrence has two factors: an inherited component
relation through the unchanged core and the genuinely local successor
residual.  This file transports both factors through one common carrier of at
most twenty-four darts.  The resulting code is a finite, graph-free value of
`BoundedCarrierGraphFamilyCode 24 0 Bool`, and its closure computes successor
facial reachability exactly between collar coordinates.

The code is extracted from one actual source rebase.  It does not yet show
that the incoming finite profile and residual receipt alone determine its core
component matrix, nor does it assemble the complete five-coordinate letter.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseFaceCollarCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The unchanged-core component relation, made into a graph on collar darts.
Distinct collar darts are adjacent exactly when the unchanged core connects
them. -/
noncomputable def sourceLocalLayerBoundaryRebaseCoreComponentGraphAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SimpleGraph web.annular.RS.D where
  Adj left right :=
    left ≠ right ∧
      left ∈ sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset
        hnext ∧
      right ∈ sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset
        hnext ∧
      (sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique offset
        hnext).Reachable left right
  symm := ⟨by
    rintro left right ⟨hne, hleft, hright, hreach⟩
    exact ⟨hne.symm, hright, hleft, hreach.symm⟩⟩
  loopless := ⟨by
    intro dart hadj
    exact hadj.1 rfl⟩

@[simp]
theorem sourceLocalLayerBoundaryRebaseCoreComponentGraphAt_adj
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : web.annular.RS.D) :
    (sourceLocalLayerBoundaryRebaseCoreComponentGraphAt corridor hunique offset
      hnext).Adj left right ↔
      left ≠ right ∧
        left ∈ sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset
          hnext ∧
        right ∈ sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset
          hnext ∧
        (sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique offset
          hnext).Reachable left right :=
  Iff.rfl

theorem sourceLocalLayerBoundaryRebaseCoreComponentGraphAt_support_subset_collar
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerBoundaryRebaseCoreComponentGraphAt corridor hunique offset
      hnext).support ⊆
      sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext := by
  intro dart hdart
  rcases (SimpleGraph.mem_support _).1 hdart with ⟨other, hadj⟩
  exact hadj.2.1

/-- The core-component graph represents the ambient core relation exactly on
collar darts. -/
theorem sourceLocalLayerBoundaryRebaseCoreComponentGraphAt_reachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : web.annular.RS.D)
    (hleft : left ∈ sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique
      offset hnext)
    (hright : right ∈ sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique
      offset hnext) :
    (sourceLocalLayerBoundaryRebaseCoreComponentGraphAt corridor hunique offset
      hnext).Reachable left right ↔
      (sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique offset
        hnext).Reachable left right := by
  constructor
  · intro hreach
    have hpath := (SimpleGraph.reachable_iff_reflTransGen left right).mp hreach
    exact Relation.ReflTransGen.trans_induction_on
      (motive := fun {first second} _ =>
        (sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique offset
          hnext).Reachable first second)
      hpath
      (fun _ => SimpleGraph.Reachable.rfl)
      (fun hadj => hadj.2.2.2)
      (fun _ _ hfirst hsecond => hfirst.trans hsecond)
  · intro hreach
    by_cases heq : left = right
    · subst right
      exact SimpleGraph.Reachable.rfl
    · exact SimpleGraph.Adj.reachable (show
        (sourceLocalLayerBoundaryRebaseCoreComponentGraphAt corridor hunique
          offset hnext).Adj left right from ⟨heq, hleft, hright, hreach⟩)

/-- The two facial factors transported through one common bounded carrier.
`false` is the inherited core-component relation and `true` is the local
successor residual. -/
noncomputable def sourceLocalLayerBoundaryRebaseFaceCollarCodeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    BoundedCarrierGraphFamilyCode 24 0 Bool :=
  boundedCarrierGraphFamilyCode
    (sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext)
    24 0
    (card_sourceLocalLayerBoundaryRebaseFaceCollarAt_le_twentyFour corridor
      hunique offset hnext)
    (fun point => Fin.elim0 point)
    (fun isLocal => if isLocal then
      sourceLocalLayerBoundaryRebaseLocalFaceGraphAt corridor hunique offset hnext
    else
      sourceLocalLayerBoundaryRebaseCoreComponentGraphAt corridor hunique offset
        hnext)

theorem sourceLocalLayerBoundaryRebaseFaceCollarCodeAt_false_reachable_iff_core
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : {dart // dart ∈
      sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext}) :
    ((sourceLocalLayerBoundaryRebaseFaceCollarCodeAt corridor hunique offset
      hnext).graph false).Reachable
        (carrierCoordinate _ left) (carrierCoordinate _ right) ↔
      (sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique offset
        hnext).Reachable left.1 right.1 := by
  have hcode := boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    (sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext)
    24 0
    (card_sourceLocalLayerBoundaryRebaseFaceCollarAt_le_twentyFour corridor
      hunique offset hnext)
    (fun point => Fin.elim0 point)
    (fun isLocal => if isLocal then
      sourceLocalLayerBoundaryRebaseLocalFaceGraphAt corridor hunique offset hnext
    else
      sourceLocalLayerBoundaryRebaseCoreComponentGraphAt corridor hunique offset
        hnext)
    false
    (by simpa using
      (sourceLocalLayerBoundaryRebaseCoreComponentGraphAt_support_subset_collar
        corridor hunique offset hnext))
    left right
  simp only [Bool.false_eq_true, if_false] at hcode
  rw [sourceLocalLayerBoundaryRebaseCoreComponentGraphAt_reachable_iff
    corridor hunique offset hnext left.1 right.1 left.2 right.2] at hcode
  simpa [sourceLocalLayerBoundaryRebaseFaceCollarCodeAt] using hcode

theorem sourceLocalLayerBoundaryRebaseFaceCollarCodeAt_true_reachable_iff_local
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : {dart // dart ∈
      sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext}) :
    ((sourceLocalLayerBoundaryRebaseFaceCollarCodeAt corridor hunique offset
      hnext).graph true).Reachable
        (carrierCoordinate _ left) (carrierCoordinate _ right) ↔
      (sourceLocalLayerBoundaryRebaseLocalFaceGraphAt corridor hunique offset
        hnext).Reachable left.1 right.1 := by
  have hcode := boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    (sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext)
    24 0
    (card_sourceLocalLayerBoundaryRebaseFaceCollarAt_le_twentyFour corridor
      hunique offset hnext)
    (fun point => Fin.elim0 point)
    (fun isLocal => if isLocal then
      sourceLocalLayerBoundaryRebaseLocalFaceGraphAt corridor hunique offset hnext
    else
      sourceLocalLayerBoundaryRebaseCoreComponentGraphAt corridor hunique offset
        hnext)
    true
    (by simpa using
      (sourceLocalLayerBoundaryRebaseLocalFaceGraphAt_support_subset_collar
        corridor hunique offset hnext))
    left right
  simpa [sourceLocalLayerBoundaryRebaseFaceCollarCodeAt] using hcode

/-- Successor facial reachability is exactly the closure computed by the
bounded two-factor code. -/
theorem sourceLocalLayerBoundaryRebaseSuccessor_reachable_iff_faceCollarCode
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : web.annular.RS.D)
    (hleft : left ∈ sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique
      offset hnext)
    (hright : right ∈ sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique
      offset hnext) :
    (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique offset
      hnext).Reachable left right ↔
      Relation.ReflTransGen
        (fun first second : Fin
            (sourceLocalLayerBoundaryRebaseFaceCollarCodeAt corridor hunique
              offset hnext).vertexCount.val =>
          ((sourceLocalLayerBoundaryRebaseFaceCollarCodeAt corridor hunique
            offset hnext).graph false).Reachable first second ∨
          ((sourceLocalLayerBoundaryRebaseFaceCollarCodeAt corridor hunique
            offset hnext).graph true).Reachable first second)
        (carrierCoordinate _ ⟨left, hleft⟩)
        (carrierCoordinate _ ⟨right, hright⟩) := by
  let carrier :=
    sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext
  let coordinate := carrierCoordinate carrier
  rw [sourceLocalLayerBoundaryRebaseSuccessor_reachable_iff_collarComponentClosure
    corridor hunique offset hnext left right hleft hright]
  have hstep (first second : {dart // dart ∈ carrier}) :
      (sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique offset
          hnext).Reachable first.1 second.1 ∨
        (sourceLocalLayerBoundaryRebaseLocalFaceGraphAt corridor hunique offset
          hnext).Reachable first.1 second.1 ↔
      ((sourceLocalLayerBoundaryRebaseFaceCollarCodeAt corridor hunique offset
        hnext).graph false).Reachable (coordinate first) (coordinate second) ∨
        ((sourceLocalLayerBoundaryRebaseFaceCollarCodeAt corridor hunique offset
          hnext).graph true).Reachable (coordinate first) (coordinate second) := by
    constructor
    · rintro (hcore | hlocal)
      · exact Or.inl
          ((sourceLocalLayerBoundaryRebaseFaceCollarCodeAt_false_reachable_iff_core
            corridor hunique offset hnext first second).2 hcore)
      · exact Or.inr
          ((sourceLocalLayerBoundaryRebaseFaceCollarCodeAt_true_reachable_iff_local
            corridor hunique offset hnext first second).2 hlocal)
    · rintro (hcore | hlocal)
      · exact Or.inl
          ((sourceLocalLayerBoundaryRebaseFaceCollarCodeAt_false_reachable_iff_core
            corridor hunique offset hnext first second).1 hcore)
      · exact Or.inr
          ((sourceLocalLayerBoundaryRebaseFaceCollarCodeAt_true_reachable_iff_local
            corridor hunique offset hnext first second).1 hlocal)
  constructor
  · intro hclosure
    exact Relation.ReflTransGen.lift coordinate
      (fun first second h => (hstep first second).1 h) hclosure
  · intro hclosure
    have hlift : Relation.ReflTransGen
        (fun first second : {dart // dart ∈ carrier} =>
          (sourceLocalLayerBoundaryRebaseCoreFaceGraphAt corridor hunique offset
              hnext).Reachable first.1 second.1 ∨
            (sourceLocalLayerBoundaryRebaseLocalFaceGraphAt corridor hunique
              offset hnext).Reachable first.1 second.1)
        (coordinate.symm (coordinate ⟨left, hleft⟩))
        (coordinate.symm (coordinate ⟨right, hright⟩)) :=
      Relation.ReflTransGen.lift coordinate.symm
        (fun first second h =>
          (hstep (coordinate.symm first) (coordinate.symm second)).2 (by
            simpa using h)) hclosure
    simpa [coordinate, carrier] using hlift

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
