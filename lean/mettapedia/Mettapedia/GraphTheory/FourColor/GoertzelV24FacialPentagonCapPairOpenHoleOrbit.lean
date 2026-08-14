import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairBoundaryFaces
import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairDeletedCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionBoundaryOrbit
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionBoundaryOrbitClassification

/-!
# Hole orbits of the simultaneous facial-cap opening

The preceding local calculation places each five-port cap family in a cycle
of the literal two-cap deleted-face permutation.  The corridor-selected remote
facial-separation condition gives unique retained occurrence on every touched
ambient face.  This module combines those facts through the already-proved
complementary boundary-order theorem and obtains two actual five-stub face
orbits in the simultaneous open-region rotation.

These theorems prove both orbit equality within each named family and orbit
inequality between the inner and outer families.  They do not yet package an
annular cellulation or construct remote facial separation from the source
corridor.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapPairOpenHoleOrbit

open SimpleGraphDartRotation
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapPairBoundaryFaces
open GoertzelV24FacialPentagonCapPairDeletedCycle
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OpenRegionBoundaryOrbit
open GoertzelV24OpenRegionBoundaryOrbitClassification
open GoertzelV24OpenRegionRotation
open GoertzelV24PentagonCapOpening
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24TwoPentagonCapOpening
open GoertzelV24TwoEdgeCutMinimality

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexFintype
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

namespace FacialPentagonCapBoundaryWalkPair

variable {data : Data G}

private theorem innerSupport_subset_deleted
    (caps : FacialPentagonCapBoundaryWalkPair data) :
    caps.inner.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport ⊆
      caps.toPentagonCapPair.deletedVertexSupport := by
  intro vertex hvertex
  exact Finset.mem_union_left _ hvertex

private theorem outerSupport_subset_deleted
    (caps : FacialPentagonCapBoundaryWalkPair data) :
    caps.outer.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport ⊆
      caps.toPentagonCapPair.deletedVertexSupport := by
  intro vertex hvertex
  exact Finset.mem_union_right _ hvertex

private theorem innerSpoke_not_mem_deleted
    (caps : FacialPentagonCapBoundaryWalkPair data) (step : Fin 5) :
    caps.inner.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.spokeOuter step ∉
      caps.toPentagonCapPair.deletedVertexSupport := by
  rw [PentagonCapPair.deletedVertexSupport, Finset.mem_union, not_or]
  exact ⟨caps.inner.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.spokeOuter_not_mem_vertexSupport step,
    caps.inner_spokeOuter_not_mem_outerSupport step⟩

private theorem outerSpoke_not_mem_deleted
    (caps : FacialPentagonCapBoundaryWalkPair data) (step : Fin 5) :
    caps.outer.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.spokeOuter step ∉
      caps.toPentagonCapPair.deletedVertexSupport := by
  rw [PentagonCapPair.deletedVertexSupport, Finset.mem_union, not_or]
  exact ⟨caps.outer_spokeOuter_not_mem_innerSupport step,
    caps.outer.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.spokeOuter_not_mem_vertexSupport step⟩

/-- The inner cap-side half-dart in the exact simultaneous deleted carrier. -/
def innerDeletedBoundary
    (caps : FacialPentagonCapBoundaryWalkPair data) (step : Fin 5) :
    DeletedBoundaryHalfDart data.toRotationSystem
      caps.toPentagonCapPair.deletedVertexSupport :=
  FacialPentagonCapBoundaryWalk.extendedCapDeletedBoundaryDart
    caps.inner caps.toPentagonCapPair.deletedVertexSupport
    (innerSupport_subset_deleted caps) (innerSpoke_not_mem_deleted caps) step

/-- The outer cap-side half-dart in the exact simultaneous deleted carrier. -/
def outerDeletedBoundary
    (caps : FacialPentagonCapBoundaryWalkPair data) (step : Fin 5) :
    DeletedBoundaryHalfDart data.toRotationSystem
      caps.toPentagonCapPair.deletedVertexSupport :=
  FacialPentagonCapBoundaryWalk.extendedCapDeletedBoundaryDart
    caps.outer caps.toPentagonCapPair.deletedVertexSupport
    (outerSupport_subset_deleted caps) (outerSpoke_not_mem_deleted caps) step

/-- The inner port, on the retained `BoundaryDart` carrier used by the literal
open-region rotation. -/
def innerRetainedBoundary
    (caps : FacialPentagonCapBoundaryWalkPair data) (step : Fin 5) :
    BoundaryDart data.toRotationSystem
      (deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport) :=
  deletedBoundaryHalfDartEquivBoundaryDart data.toRotationSystem
    caps.toPentagonCapPair.deletedVertexSupport (innerDeletedBoundary caps step)

/-- The outer port, on the retained `BoundaryDart` carrier used by the literal
open-region rotation. -/
def outerRetainedBoundary
    (caps : FacialPentagonCapBoundaryWalkPair data) (step : Fin 5) :
    BoundaryDart data.toRotationSystem
      (deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport) :=
  deletedBoundaryHalfDartEquivBoundaryDart data.toRotationSystem
    caps.toPentagonCapPair.deletedVertexSupport (outerDeletedBoundary caps step)

/-- All five inner ports lie in one cycle of the retained first-return order
of the simultaneous cut. -/
theorem retainedBoundarySuccessor_inner_sameCycle
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (first second : Fin 5) :
    (retainedRegionBoundarySuccessor data.toRotationSystem
      (deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport)).SameCycle
        (innerRetainedBoundary caps first)
        (innerRetainedBoundary caps second) := by
  have hunique :=
    OrientedFacialPentagonCapPair.cutFacesHaveUniqueRetainedBoundaryDart_of_remoteBoundaryFacesSeparated
      caps.toOrientedFacialPentagonCapPair minimal hremote
  have horder :=
    retained_boundarySuccessor_eq_deleted_boundarySuccessor_inv_of_cutFacesUnique
      data.toRotationSystem caps.toPentagonCapPair.deletedVertexSupport hunique
  rw [horder, Equiv.Perm.sameCycle_inv]
  exact (deletedRegionBoundarySuccessor_sameCycle_iff data.toRotationSystem
    caps.toPentagonCapPair.deletedVertexSupport
    (innerDeletedBoundary caps first) (innerDeletedBoundary caps second)).2
      (FacialPentagonCapBoundaryWalkPair.innerDeletedBoundary_sameCycle
        caps hcubic hrotation first second)

/-- All five outer ports lie in one cycle of the retained first-return order
of the simultaneous cut. -/
theorem retainedBoundarySuccessor_outer_sameCycle
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (first second : Fin 5) :
    (retainedRegionBoundarySuccessor data.toRotationSystem
      (deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport)).SameCycle
        (outerRetainedBoundary caps first)
        (outerRetainedBoundary caps second) := by
  have hunique :=
    OrientedFacialPentagonCapPair.cutFacesHaveUniqueRetainedBoundaryDart_of_remoteBoundaryFacesSeparated
      caps.toOrientedFacialPentagonCapPair minimal hremote
  have horder :=
    retained_boundarySuccessor_eq_deleted_boundarySuccessor_inv_of_cutFacesUnique
      data.toRotationSystem caps.toPentagonCapPair.deletedVertexSupport hunique
  rw [horder, Equiv.Perm.sameCycle_inv]
  exact (deletedRegionBoundarySuccessor_sameCycle_iff data.toRotationSystem
    caps.toPentagonCapPair.deletedVertexSupport
    (outerDeletedBoundary caps first) (outerDeletedBoundary caps second)).2
      (FacialPentagonCapBoundaryWalkPair.outerDeletedBoundary_sameCycle
        caps hcubic hrotation first second)

/-- The inner and outer named ports lie in distinct retained first-return
cycles.  The proof transports the invariant-component separation of the
simultaneous deleted carrier across the complementary boundary order. -/
theorem retainedBoundarySuccessor_inner_outer_not_sameCycle
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair) :
    ¬ (retainedRegionBoundarySuccessor data.toRotationSystem
      (deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport)).SameCycle
        (innerRetainedBoundary caps 0)
        (outerRetainedBoundary caps 0) := by
  have hunique :=
    OrientedFacialPentagonCapPair.cutFacesHaveUniqueRetainedBoundaryDart_of_remoteBoundaryFacesSeparated
      caps.toOrientedFacialPentagonCapPair minimal hremote
  have horder :=
    retained_boundarySuccessor_eq_deleted_boundarySuccessor_inv_of_cutFacesUnique
      data.toRotationSystem caps.toPentagonCapPair.deletedVertexSupport hunique
  rw [horder, Equiv.Perm.sameCycle_inv]
  change ¬ (deletedRegionBoundarySuccessor data.toRotationSystem
    caps.toPentagonCapPair.deletedVertexSupport).SameCycle
      (deletedBoundaryHalfDartEquivBoundaryDart data.toRotationSystem
        caps.toPentagonCapPair.deletedVertexSupport (innerDeletedBoundary caps 0))
      (deletedBoundaryHalfDartEquivBoundaryDart data.toRotationSystem
        caps.toPentagonCapPair.deletedVertexSupport (outerDeletedBoundary caps 0))
  rw [deletedRegionBoundarySuccessor_sameCycle_iff]
  exact FacialPentagonCapBoundaryWalkPair.inner_outerDeletedBoundary_not_sameCycle caps

/-- The five inner stubs are one actual face orbit of the simultaneous literal
open-region rotation. -/
theorem openedInnerHoleFace_stub_eq
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (root : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport))
    (first second : Fin 5) :
    dartOrbitFace
        (rotationSystem data.toRotationSystem
          (deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport) root)
        (Sum.inr (innerRetainedBoundary caps first)) =
      dartOrbitFace
        (rotationSystem data.toRotationSystem
          (deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport) root)
        (Sum.inr (innerRetainedBoundary caps second)) := by
  apply dartOrbitFace_stub_eq_of_boundarySuccessor_sameCycle
  exact retainedBoundarySuccessor_inner_sameCycle caps minimal hremote hcubic
    hrotation first second

/-- The five outer stubs are one actual face orbit of the simultaneous literal
open-region rotation. -/
theorem openedOuterHoleFace_stub_eq
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (root : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport))
    (first second : Fin 5) :
    dartOrbitFace
        (rotationSystem data.toRotationSystem
          (deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport) root)
        (Sum.inr (outerRetainedBoundary caps first)) =
      dartOrbitFace
        (rotationSystem data.toRotationSystem
          (deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport) root)
        (Sum.inr (outerRetainedBoundary caps second)) := by
  apply dartOrbitFace_stub_eq_of_boundarySuccessor_sameCycle
  exact retainedBoundarySuccessor_outer_sameCycle caps minimal hremote hcubic
    hrotation first second

/-- The two literal opened collars are distinct face orbits.  Thus simultaneous
cap opening produces two named boundary components rather than one face seen
through two coordinate systems. -/
theorem openedInnerHoleFace_ne_openedOuterHoleFace
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (root : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport)) :
    dartOrbitFace
        (rotationSystem data.toRotationSystem
          (deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport) root)
        (Sum.inr (innerRetainedBoundary caps 0)) ≠
      dartOrbitFace
        (rotationSystem data.toRotationSystem
          (deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport) root)
        (Sum.inr (outerRetainedBoundary caps 0)) := by
  intro hface
  have hsame :=
    (dartOrbitFace_stub_eq_iff_boundarySuccessor_sameCycle
      data.toRotationSystem
      (deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport)
      root (innerRetainedBoundary caps 0) (outerRetainedBoundary caps 0)).1 hface
  exact retainedBoundarySuccessor_inner_outer_not_sameCycle caps minimal hremote hsame

end FacialPentagonCapBoundaryWalkPair

end


end GoertzelV24FacialPentagonCapPairOpenHoleOrbit

end Mettapedia.GraphTheory.FourColor
