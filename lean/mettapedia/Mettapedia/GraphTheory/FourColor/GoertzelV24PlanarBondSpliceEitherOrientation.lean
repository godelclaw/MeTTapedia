import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondSpliceEuler

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PlanarBondSpliceEitherOrientation

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24CurvatureScope
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24PlanarBondSpliceEuler
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RetainedSpliceAmbientFaceCount
open GoertzelV24RetainedSpliceEdgeCount
open GoertzelV24RetainedSpliceEuler
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24RotationSpliceConstructor
open GoertzelV24SimpleGraphFaceDualConnectedness
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

noncomputable section

/-- A simple dual loop has no mathematically preferred global orientation.
This predicate records the two coherent possibilities for the order in which
the actual deleted boundary meets a pair of ordered crosscuts.  It is not a
weakening: a source construction must still establish one displayed equality.

The extra inverse branch is topologically harmless for the splice because the
seam cap is an involution; the resulting capped face-cycle count is unchanged.
This lets source layer geometry choose its natural orientation rather than
encoding that arbitrary choice into the planar-bond API. -/
def CutsFollowEitherDeletedBoundaryOrientation
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing)) : Prop :=
  CutsFollowOppositeDeletedBoundaryOrder RS deleted
      leftCrossing rightCrossing hboundary hleftInjective hrightInjective
      hdisjoint ∨
    deletedRegionBoundarySuccessor RS deleted =
      (orderedBoundaryPositionEquiv RS deleted leftCrossing rightCrossing
        hboundary hleftInjective hrightInjective hdisjoint).permCongr
        (oppositeBoundaryCycle n)⁻¹

/-- The planar-bond splice face count is independent of the coherent global
orientation used to enumerate the two crosscuts.  The forward case is the
existing theorem; the reverse case computes the retained boundary directly.
No profile or catalogue data is involved. -/
theorem card_actualOrderedCutFaceReturnSuccessor_partition_of_planar_bond_of_either_orientation
    (data : Data G) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → G.edgeSet)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges data.toRotationSystem deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (hn : 0 < n)
    (horder : CutsFollowEitherDeletedBoundaryOrientation
      data.toRotationSystem deleted leftCrossing rightCrossing hboundary
      hleftInjective hrightInjective hdisjoint)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep deleted vertex)}).Connected)
    (houter : data.toRotationSystem.vertOf data.toRotationSystem.outer ∉
      deleted) :
    let hleftCrosses := leftCrossing_outward data.toRotationSystem deleted
      leftCrossing rightCrossing hboundary
    let hrightCrosses := rightCrossing_outward data.toRotationSystem deleted
      leftCrossing rightCrossing hboundary
    let hcover := deletedRegionBoundaryCover data.toRotationSystem deleted
      leftCrossing rightCrossing hboundary
    (actualOrderedCutFaceReturnSuccessor data.toRotationSystem
      (deletedRegionKeep deleted) leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter).partition.parts.card = n + 1 := by
  rcases horder with hforward | hreverse
  · exact card_actualOrderedCutFaceReturnSuccessor_partition_of_planar_bond
      data deleted leftCrossing rightCrossing hboundary hleftInjective
      hrightInjective hdisjoint hn hforward hsphere htwoSided hconnected
      hrotation hretainedConnected hdeletedConnected houter
  · dsimp only
    let positionEquiv := orderedRetainedBoundaryPositionEquiv
      data.toRotationSystem (deletedRegionKeep deleted)
        leftCrossing rightCrossing
        (leftCrossing_outward data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary)
        (rightCrossing_outward data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary)
        hleftInjective hrightInjective
        (deletedRegionBoundaryCover data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary) hdisjoint
    let seamSwap := orderedBoundarySeamSwap data.toRotationSystem
      (deletedRegionKeep deleted) leftCrossing rightCrossing
        (leftCrossing_outward data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary)
        (rightCrossing_outward data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary)
        hleftInjective hrightInjective
        (deletedRegionBoundaryCover data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary) hdisjoint
    have hretainedBoundary :
        retainedRegionBoundarySuccessor data.toRotationSystem
            (deletedRegionKeep deleted) =
          positionEquiv.permCongr (oppositeBoundaryCycle n) := by
      rw [retained_boundarySuccessor_eq_deleted_inverse_of_planar_bond
        data deleted hsphere htwoSided hconnected hrotation
        hretainedConnected hdeletedConnected, hreverse]
      rfl
    have hseamCoordinate :
        positionEquiv.symm.permCongr seamSwap =
          orderedPositionSeamSwap n := by
      exact orderedRetainedBoundaryPosition_seamSwap_congr
        data.toRotationSystem deleted leftCrossing rightCrossing hboundary
          hleftInjective hrightInjective hdisjoint
    have hactual :
        actualOrderedCutFaceReturnSuccessor data.toRotationSystem
            (deletedRegionKeep deleted) leftCrossing rightCrossing
            (leftCrossing_outward data.toRotationSystem deleted
              leftCrossing rightCrossing hboundary)
            (rightCrossing_outward data.toRotationSystem deleted
              leftCrossing rightCrossing hboundary)
            hleftInjective hrightInjective
            (deletedRegionBoundaryCover data.toRotationSystem deleted
              leftCrossing rightCrossing hboundary) hdisjoint houter =
          oppositeBoundaryCycle n * orderedPositionSeamSwap n := by
      rw [actualOrderedCutFaceReturnSuccessor_eq_retainedBoundarySuccessor,
        hretainedBoundary]
      change positionEquiv.symm.permCongr
          (positionEquiv.permCongr (oppositeBoundaryCycle n) * seamSwap) =
        oppositeBoundaryCycle n * orderedPositionSeamSwap n
      apply Equiv.ext
      intro position
      simp only [Equiv.permCongr_apply, Equiv.Perm.mul_apply,
        Equiv.symm_symm, Equiv.symm_apply_apply]
      exact congrArg
        (fun point => (oppositeBoundaryCycle n :
          Equiv.Perm (OrderedSeamPosition n)) point)
        (DFunLike.congr_fun hseamCoordinate position)
    rw [hactual]
    exact card_oppositeBoundary_capPerm_partition hn

/-- The local annulus Euler equation for an ordered planar-bond splice is
orientation independent. -/
theorem retainedSpliceLocalEulerBalance_of_planar_bond_of_either_orientation
    (data : Data G) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → G.edgeSet)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges data.toRotationSystem deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (hn : 0 < n)
    (horder : CutsFollowEitherDeletedBoundaryOrientation
      data.toRotationSystem deleted leftCrossing rightCrossing hboundary
      hleftInjective hrightInjective hdisjoint)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep deleted vertex)}).Connected)
    (houter : data.toRotationSystem.vertOf data.toRotationSystem.outer ∉
      deleted) :
    let hleftCrosses := leftCrossing_outward data.toRotationSystem deleted
      leftCrossing rightCrossing hboundary
    let hrightCrosses := rightCrossing_outward data.toRotationSystem deleted
      leftCrossing rightCrossing hboundary
    let hcover := deletedRegionBoundaryCover data.toRotationSystem deleted
      leftCrossing rightCrossing hboundary
    RetainedSpliceLocalEulerBalance data.toRotationSystem
      (deletedRegionKeep deleted) leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter := by
  dsimp only
  have hreturns :=
    card_actualOrderedCutFaceReturnSuccessor_partition_of_planar_bond_of_either_orientation
      data deleted leftCrossing rightCrossing hboundary hleftInjective
      hrightInjective hdisjoint hn horder hsphere htwoSided hconnected
      hrotation hretainedConnected hdeletedConnected houter
  have hdeletedEuler := planarBond_deletedRegionEulerBalance
    data deleted hsphere htwoSided hconnected hrotation
      hretainedConnected hdeletedConnected
  unfold RetainedSpliceLocalEulerBalance
  rw [hreturns]
  omega

/-- Shortening along an ordered planar bond preserves spherical cubicity for
either coherent source orientation.  The proof still needs an explicit
orientation witness; only the arbitrary choice of direction is abstracted. -/
theorem orbitSphericalCubicMapData_orderedCutSplice_of_planar_bond_of_either_orientation
    (data : Data G) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → G.edgeSet)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges data.toRotationSystem deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (hn : 0 < n)
    (horder : CutsFollowEitherDeletedBoundaryOrientation
      data.toRotationSystem deleted leftCrossing rightCrossing hboundary
      hleftInjective hrightInjective hdisjoint)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        Not (deletedRegionKeep deleted vertex)}).Connected)
    (houter : data.toRotationSystem.vertOf data.toRotationSystem.outer ∉
      deleted)
    (hseamEndpoints : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (deletedRegionKeep deleted) leftCrossing
            (leftCrossing_outward data.toRotationSystem deleted
              leftCrossing rightCrossing hboundary) step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (deletedRegionKeep deleted) rightCrossing
            (rightCrossing_outward data.toRotationSystem deleted
              leftCrossing rightCrossing hboundary) step).1.1.1) :
    OrbitSphericalCubicMapData
      (orderedCutRetainedVertexRotationSystem data.toRotationSystem
        (deletedRegionKeep deleted) leftCrossing rightCrossing
        (leftCrossing_outward data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary)
        (rightCrossing_outward data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary)
        hleftInjective hrightInjective
        (deletedRegionBoundaryCover data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary)
        hdisjoint houter hseamEndpoints) := by
  have hbalance :=
    retainedSpliceLocalEulerBalance_of_planar_bond_of_either_orientation
      data deleted leftCrossing rightCrossing hboundary hleftInjective
      hrightInjective hdisjoint hn horder hsphere htwoSided hconnected
      hrotation hretainedConnected hdeletedConnected houter
  have hambient : SphericalCubicMapData data.toRotationSystem := by
    refine ⟨hsphere.cubic, ?_⟩
    have hfaceCard := card_orbitFace_eq_faceCycleLengths_card
      data.toRotationSystem
    have heuler := hsphere.euler
    omega
  let shortened := orderedCutRetainedVertexRotationSystem
    data.toRotationSystem (deletedRegionKeep deleted)
      leftCrossing rightCrossing
      (leftCrossing_outward data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary)
      (rightCrossing_outward data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary)
      hleftInjective hrightInjective
      (deletedRegionBoundaryCover data.toRotationSystem deleted
        leftCrossing rightCrossing hboundary)
      hdisjoint houter hseamEndpoints
  have hshortened : SphericalCubicMapData shortened :=
    sphericalCubicMapData_orderedCutRetainedVertexRotationSystem
      data.toRotationSystem (deletedRegionKeep deleted)
        leftCrossing rightCrossing
        (leftCrossing_outward data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary)
        (rightCrossing_outward data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary)
        hleftInjective hrightInjective
        (deletedRegionBoundaryCover data.toRotationSystem deleted
          leftCrossing rightCrossing hboundary)
        hdisjoint houter hseamEndpoints hambient hbalance
  exact OrbitSphericalCubicMapData.ofSphericalCubicMapData
    shortened hshortened

end

end GoertzelV24PlanarBondSpliceEitherOrientation

end Mettapedia.GraphTheory.FourColor
