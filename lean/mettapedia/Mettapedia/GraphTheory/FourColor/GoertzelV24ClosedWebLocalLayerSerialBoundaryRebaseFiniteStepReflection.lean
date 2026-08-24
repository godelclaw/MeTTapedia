import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedCarrierBoolGraphFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFaceCollarCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedCollarCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteBoolRelationClosure

/-!
# Boolean reflection of the literal boundary-rebase recurrence

The source boundary rebase has two exact finite recurrences.  For each tracked
two-colour pair, the successor component relation is the closure of an
unchanged-core factor and a local residual factor on at most twenty-eight
edges.  The facial recurrence has the same two-factor form on at most
twenty-four darts.

This file reflects those proof-facing graph families to Boolean adjacency
tables and computes their directed closures.  The two final iff theorems say
that the Boolean answers agree exactly with the actual successor tracked and
facial reachability relations.  No orientation quotient, profile projection,
or realizability converse is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteBoolRelationClosure
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseFiniteStepReflectionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- One executable tracked rebase step: traverse either the inherited core
component relation or the local successor residual. -/
def SourceLocalLayerBoundaryRebaseTrackedFiniteStepBool
    (code : BoundedCarrierBoolGraphFamilyCode 28 4
      (TrackedColorPair × Bool))
    (pair : TrackedColorPair)
    (left right : Fin code.vertexCount.val) : Bool :=
  code.reachable (pair, false) left right ||
    code.reachable (pair, true) left right

/-- Directed saturation of the executable tracked rebase step. -/
def SourceLocalLayerBoundaryRebaseTrackedFiniteClosureBool
    (code : BoundedCarrierBoolGraphFamilyCode 28 4
      (TrackedColorPair × Bool))
    (pair : TrackedColorPair)
    (left right : Fin code.vertexCount.val) : Bool :=
  boolRelationReachable
    (SourceLocalLayerBoundaryRebaseTrackedFiniteStepBool code pair) left right

/-- One executable facial rebase step: traverse either the inherited core
component relation or the local successor residual. -/
def SourceLocalLayerBoundaryRebaseFaceFiniteStepBool
    (code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool)
    (left right : Fin code.vertexCount.val) : Bool :=
  code.reachable false left right || code.reachable true left right

/-- Directed saturation of the executable facial rebase step. -/
def SourceLocalLayerBoundaryRebaseFaceFiniteClosureBool
    (code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool)
    (left right : Fin code.vertexCount.val) : Bool :=
  boolRelationReachable
    (SourceLocalLayerBoundaryRebaseFaceFiniteStepBool code) left right

/-- Boolean reflection preserves one proof-facing tracked rebase step exactly. -/
@[simp]
theorem trackedFiniteStepBool_ofGraphFamilyCode_eq_true_iff
    (code : BoundedCarrierGraphFamilyCode 28 4
      (TrackedColorPair × Bool))
    (pair : TrackedColorPair)
    (left right : Fin code.vertexCount.val) :
    SourceLocalLayerBoundaryRebaseTrackedFiniteStepBool
        (ofGraphFamilyCode code) pair left right = true ↔
      (code.graph (pair, false)).Reachable left right ∨
        (code.graph (pair, true)).Reachable left right := by
  simp only [SourceLocalLayerBoundaryRebaseTrackedFiniteStepBool,
    Bool.or_eq_true, ofGraphFamilyCode_reachable_eq_true_iff]

/-- Boolean reflection preserves one proof-facing facial rebase step exactly. -/
@[simp]
theorem faceFiniteStepBool_ofGraphFamilyCode_eq_true_iff
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (left right : Fin code.vertexCount.val) :
    SourceLocalLayerBoundaryRebaseFaceFiniteStepBool
        (ofGraphFamilyCode code) left right = true ↔
      (code.graph false).Reachable left right ∨
        (code.graph true).Reachable left right := by
  simp only [SourceLocalLayerBoundaryRebaseFaceFiniteStepBool,
    Bool.or_eq_true, ofGraphFamilyCode_reachable_eq_true_iff]

/-- Boolean saturation of a reflected tracked collar is exactly the
proof-facing two-factor closure. -/
@[simp]
theorem trackedFiniteClosureBool_ofGraphFamilyCode_eq_true_iff
    (code : BoundedCarrierGraphFamilyCode 28 4
      (TrackedColorPair × Bool))
    (pair : TrackedColorPair)
    (left right : Fin code.vertexCount.val) :
    SourceLocalLayerBoundaryRebaseTrackedFiniteClosureBool
        (ofGraphFamilyCode code) pair left right = true ↔
      Relation.ReflTransGen
        (fun first second =>
          (code.graph (pair, false)).Reachable first second ∨
            (code.graph (pair, true)).Reachable first second)
        left right := by
  rw [SourceLocalLayerBoundaryRebaseTrackedFiniteClosureBool,
    boolRelationReachable_eq_true_iff]
  constructor
  · exact Relation.ReflTransGen.mono fun first second hstep =>
      (trackedFiniteStepBool_ofGraphFamilyCode_eq_true_iff
        code pair first second).1 hstep
  · exact Relation.ReflTransGen.mono fun first second hstep =>
      (trackedFiniteStepBool_ofGraphFamilyCode_eq_true_iff
        code pair first second).2 hstep

/-- Boolean saturation of a reflected facial collar is exactly the
proof-facing two-factor closure. -/
@[simp]
theorem faceFiniteClosureBool_ofGraphFamilyCode_eq_true_iff
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (left right : Fin code.vertexCount.val) :
    SourceLocalLayerBoundaryRebaseFaceFiniteClosureBool
        (ofGraphFamilyCode code) left right = true ↔
      Relation.ReflTransGen
        (fun first second =>
          (code.graph false).Reachable first second ∨
            (code.graph true).Reachable first second)
        left right := by
  rw [SourceLocalLayerBoundaryRebaseFaceFiniteClosureBool,
    boolRelationReachable_eq_true_iff]
  constructor
  · exact Relation.ReflTransGen.mono fun first second hstep =>
      (faceFiniteStepBool_ofGraphFamilyCode_eq_true_iff
        code first second).1 hstep
  · exact Relation.ReflTransGen.mono fun first second hstep =>
      (faceFiniteStepBool_ofGraphFamilyCode_eq_true_iff
        code first second).2 hstep

/-- The Boolean tracked collar query computes actual successor tracked
reachability exactly between any two collar edges. -/
theorem sourceLocalLayerBoundaryRebaseTrackedFiniteClosureBoolAt_eq_true_iff
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
    SourceLocalLayerBoundaryRebaseTrackedFiniteClosureBool
        (ofGraphFamilyCode
          (sourceLocalLayerBoundaryRebaseTrackedCollarCodeAt corridor hunique
            offset hnext)) pair
        (carrierCoordinate _ ⟨left, hleft⟩)
        (carrierCoordinate _ ⟨right, hright⟩) = true ↔
      (sourceLocalLayerBoundaryRebaseSuccessorTrackedGraphAt corridor hunique
        offset hnext pair).Reachable left right := by
  rw [trackedFiniteClosureBool_ofGraphFamilyCode_eq_true_iff]
  exact (sourceLocalLayerBoundaryRebaseSuccessorTracked_reachable_iff_collarCode
    corridor hunique offset hnext pair left right hleft hright).symm

/-- The Boolean facial collar query computes actual successor facial
reachability exactly between any two collar darts. -/
theorem sourceLocalLayerBoundaryRebaseFaceFiniteClosureBoolAt_eq_true_iff
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
    SourceLocalLayerBoundaryRebaseFaceFiniteClosureBool
        (ofGraphFamilyCode
          (sourceLocalLayerBoundaryRebaseFaceCollarCodeAt corridor hunique
            offset hnext))
        (carrierCoordinate _ ⟨left, hleft⟩)
        (carrierCoordinate _ ⟨right, hright⟩) = true ↔
      (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique offset
        hnext).Reachable left right := by
  rw [faceFiniteClosureBool_ofGraphFamilyCode_eq_true_iff]
  exact (sourceLocalLayerBoundaryRebaseSuccessor_reachable_iff_faceCollarCode
    corridor hunique offset hnext left right hleft hright).symm

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
