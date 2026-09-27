import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceAmbientFaceCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceEdgeCount

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RetainedSpliceEuler

open GoertzelV24CurvatureScope
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RetainedSpliceAmbientFaceCount
open GoertzelV24RetainedSpliceEdgeCount
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Vertices removed by the retained-carrier predicate. -/
def DeletedVertex (keep : V -> Prop) := {vertex : V // Not (keep vertex)}

noncomputable instance deletedVertexFintype (keep : V -> Prop) :
    Fintype (DeletedVertex keep) :=
  Fintype.ofInjective (fun vertex : DeletedVertex keep => vertex.1)
    Subtype.val_injective

/-- Ambient edges which do not have a complete retained two-dart fiber. -/
def RemovedEdge (RS : RotationSystem V E) (keep : V -> Prop) :=
  {edge : E // Not (exists dart : InternalDart RS keep,
    RS.edgeOf dart.1.1 = edge)}

noncomputable instance removedEdgeFintype
    (RS : RotationSystem V E) (keep : V -> Prop) :
    Fintype (RemovedEdge RS keep) :=
  Fintype.ofInjective (fun edge : RemovedEdge RS keep => edge.1)
    Subtype.val_injective

/-- Ambient face cycles meeting at least one deleted vertex. -/
abbrev AmbientDeletedFaceOrbit
    (RS : RotationSystem V E) (keep : V -> Prop) :=
  HitOrbit RS.phi (fun dart => Not (keep (RS.vertOf dart)))

/-- Retained and deleted vertices partition the ambient vertex carrier. -/
theorem card_retainedVertex_add_card_deletedVertex
    (keep : V -> Prop) :
    Fintype.card (RetainedVertex keep) +
      Fintype.card (DeletedVertex keep) = Fintype.card V := by
  classical
  calc
    Fintype.card (RetainedVertex keep) +
        Fintype.card (DeletedVertex keep) =
      Fintype.card (RetainedVertex keep ⊕ DeletedVertex keep) :=
        Fintype.card_sum.symm
    _ = Fintype.card V :=
      Fintype.card_congr (Equiv.sumCompl keep)

/-- Retained internal and removed edges partition the ambient edge carrier. -/
theorem card_retainedInternalEdge_add_card_removedEdge
    (RS : RotationSystem V E) (keep : V -> Prop) :
    Fintype.card (RetainedInternalEdge RS keep) +
      Fintype.card (RemovedEdge RS keep) = Fintype.card E := by
  classical
  let retained : E -> Prop := fun edge =>
    exists dart : InternalDart RS keep, RS.edgeOf dart.1.1 = edge
  change Fintype.card {edge : E // retained edge} +
      Fintype.card {edge : E // Not (retained edge)} = Fintype.card E
  calc
    Fintype.card {edge : E // retained edge} +
        Fintype.card {edge : E // Not (retained edge)} =
      Fintype.card
        ({edge : E // retained edge} ⊕ {edge : E // Not (retained edge)}) :=
          Fintype.card_sum.symm
    _ = Fintype.card E :=
      Fintype.card_congr (Equiv.sumCompl retained)

/-- Untouched and deleted-incident ambient face cycles partition all ambient
faces. -/
theorem card_ambientRetained_add_deletedFaceOrbit
    (RS : RotationSystem V E) (keep : V -> Prop) :
    Fintype.card (AmbientRetainedFaceOrbit RS keep) +
        Fintype.card (AmbientDeletedFaceOrbit RS keep) =
      (faceCycleLengths RS).card := by
  have horbits := card_permOrbit_eq_hit_add_nonHit RS.phi
    (fun dart => Not (keep (RS.vertOf dart)))
  rw [card_permOrbit_eq_card_partition_parts RS.phi] at horbits
  simpa only [faceCycleLengths, Nat.add_comm] using horbits.symm

/-- The exact local annulus equation required for an ordered deletion-splice
to preserve Euler characteristic. Every term is computed from the ambient
rotation system, the retained carrier, and the ordered face-return
permutation. -/
def RetainedSpliceLocalEulerBalance
    (RS : RotationSystem V E) (keep : V -> Prop)
    (leftCrossing rightCrossing : Fin n -> E)
    (hleftCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = leftCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hrightCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = rightCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : forall dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing \/
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer)) : Prop :=
  Fintype.card (RemovedEdge RS keep) +
      (actualOrderedCutFaceReturnSuccessor RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter).partition.parts.card =
    Fintype.card (DeletedVertex keep) + n +
      Fintype.card (AmbientDeletedFaceOrbit RS keep)

/-- A spherical cubic ambient map remains a spherical cubic map after the
ordered deletion-splice whenever the computed local annulus Euler equation
holds. -/
theorem sphericalCubicMapData_orderedCutRetainedVertexRotationSystem
    (RS : RotationSystem V E) (keep : V -> Prop)
    (leftCrossing rightCrossing : Fin n -> E)
    (hleftCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = leftCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hrightCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = rightCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : forall dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing \/
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer))
    (hseamEndpoints : forall step,
      RS.vertOf (orderedBoundaryDart RS keep leftCrossing
          hleftCrosses step).1.1.1 ≠
        RS.vertOf (orderedBoundaryDart RS keep rightCrossing
          hrightCrosses step).1.1.1)
    (hambient : SphericalCubicMapData RS)
    (hbalance : RetainedSpliceLocalEulerBalance RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter) :
    SphericalCubicMapData
      (orderedCutRetainedVertexRotationSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints) where
  cubic := orderedCutRetainedVertexRotationSystem_isCubic RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
    hseamEndpoints hambient.cubic
  euler := by
    have hvertices := card_retainedVertex_add_card_deletedVertex keep
    have hedges := card_retainedInternalEdge_add_card_removedEdge RS keep
    have hambientFaces := card_ambientRetained_add_deletedFaceOrbit RS keep
    have hnewEdges := card_orderedCutRetainedVertexRotationSystem_edges
      RS keep leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter hseamEndpoints
    have hnewFaces :=
      card_orderedCutRetainedVertex_faceCycleLengths_eq_ambient_add_return
        RS keep leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter hseamEndpoints
    have hambientEuler := hambient.euler
    unfold RetainedSpliceLocalEulerBalance at hbalance
    have hverticesInt :
        (Fintype.card (RetainedVertex keep) : Int) +
            Fintype.card (DeletedVertex keep) = Fintype.card V := by
      exact_mod_cast hvertices
    have hedgesInt :
        (Fintype.card (RetainedInternalEdge RS keep) : Int) +
            Fintype.card (RemovedEdge RS keep) = Fintype.card E := by
      exact_mod_cast hedges
    have hambientFacesInt :
        (Fintype.card (AmbientRetainedFaceOrbit RS keep) : Int) +
            Fintype.card (AmbientDeletedFaceOrbit RS keep) =
          (faceCycleLengths RS).card := by
      exact_mod_cast hambientFaces
    have hnewEdgesInt :
        (Fintype.card
          (orderedCutRetainedVertexRewiredDartSystem RS keep
            leftCrossing rightCrossing hleftCrosses hrightCrosses
            hleftInjective hrightInjective hcover hdisjoint houter
            hseamEndpoints).Edge : Int) =
          Fintype.card (RetainedInternalEdge RS keep) + n := by
      exact_mod_cast hnewEdges
    have hnewFacesInt :
        ((faceCycleLengths
          (orderedCutRetainedVertexRotationSystem RS keep
            leftCrossing rightCrossing hleftCrosses hrightCrosses
            hleftInjective hrightInjective hcover hdisjoint houter
            hseamEndpoints)).card : Int) =
          Fintype.card (AmbientRetainedFaceOrbit RS keep) +
            (actualOrderedCutFaceReturnSuccessor RS keep
              leftCrossing rightCrossing hleftCrosses hrightCrosses
              hleftInjective hrightInjective hcover hdisjoint
              houter).partition.parts.card := by
      exact_mod_cast hnewFaces
    have hbalanceInt :
        (Fintype.card (RemovedEdge RS keep) : Int) +
            (actualOrderedCutFaceReturnSuccessor RS keep
              leftCrossing rightCrossing hleftCrosses hrightCrosses
              hleftInjective hrightInjective hcover hdisjoint
              houter).partition.parts.card =
          Fintype.card (DeletedVertex keep) + n +
            Fintype.card (AmbientDeletedFaceOrbit RS keep) := by
      exact_mod_cast hbalance
    omega

end

end GoertzelV24RetainedSpliceEuler

end Mettapedia.GraphTheory.FourColor
