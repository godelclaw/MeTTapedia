import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorRightFaceRoles
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorFiniteFaceAttachment

/-!
# Finite right-face coordinates of one literal source Cell

The outgoing face carrier has exactly the three stable roles `first`,
`center`, and `second`.  This module computes the remaining purely outgoing
face fields in those coordinates.  Face continuation is equality of roles,
and port incidence is the fixed path pattern

* `first` contains only port `0`;
* `center` contains both ports;
* `second` contains only port `1`.

The proof is derived from the actual two-step facial-dual path and the unique
occurrence-sensitive regional fragment over each named face.  No Boolean mask
is admitted merely because it fits in a finite type.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open SimpleGraph
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- On a face-injective boundary-fragment carrier, every retained cut edge
incident to a fragment's named face lies in that unique fragment. -/
theorem mem_boundaryRegionalFragmentEdges_of_face_injective
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (cut region : Finset E)
    (hinjective : Function.Injective
      (fun fragment : BoundaryRegionalFragment RS cut region => fragment.1))
    (fragment : BoundaryRegionalFragment RS cut region) (edge : E)
    (hedgeCut : edge ∈ cut)
    (hedgeFace : edge ∈ orbitFaceBoundary RS fragment.1.1)
    (hedgeRegion : edge ∈ region) :
    edge ∈ boundaryRegionalFragmentEdges RS cut region fragment := by
  have hedgeAll : edge ∈ allFaceRegionalFragmentEdges RS
      (orbitFaceRoot RS fragment.1.1) region := by
    rw [allFaceRegionalFragmentEdges_eq_boundary_inter_region RS htwoSided]
    simpa using Finset.mem_inter.2 ⟨hedgeFace, hedgeRegion⟩
  rw [allFaceRegionalFragmentEdges, Finset.mem_biUnion] at hedgeAll
  rcases hedgeAll with ⟨regionalFragment, _hregional, hedgeFragment⟩
  let candidate : BoundaryRegionalFragment RS cut region :=
    ⟨fragment.1, ⟨regionalFragment,
      ⟨edge, hedgeFragment, hedgeCut⟩⟩⟩
  have hcandidate : edge ∈
      boundaryRegionalFragmentEdges RS cut region candidate :=
    hedgeFragment
  have heq : candidate = fragment := hinjective rfl
  rw [heq] at hcandidate
  exact hcandidate

/-- Fixed port-incidence relation of the three outgoing face roles. -/
def LocalLayerRightFaceRole.ContainsPort :
    LocalLayerRightFaceRole → Fin 2 → Prop
  | .first, step => step = 0
  | .center, _step => True
  | .second, step => step = 1

instance (role : LocalLayerRightFaceRole) (step : Fin 2) :
    Decidable (role.ContainsPort step) :=
  Classical.propDecidable _

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance framedCorridorFiniteRightFaceUpdateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceConsecutiveSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- A displayed right crossing is incident to a named role face exactly for
the fixed two-step path incidence pattern. -/
theorem nextLocalLayerPrefixCrossing_mem_faceOfRole_iff
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (role : LocalLayerRightFaceRole) (step : Fin 2) :
    interface.nextLocalLayerPrefixCrossing step ∈ orbitFaceBoundary
        embedded.cellulation.rotation.toRotationSystem
        (interface.localLayerRightFaceOfRole role) ↔
      role.ContainsPort step := by
  constructor
  · intro hmem
    have hmem' : dualWalkCrossingEdge
        (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
        (Finset.univ : Finset
          (OrbitFace embedded.cellulation.rotation.toRotationSystem))
        hunique interface.nextLocalLayer.walk
        (Fin.cast interface.nextLocalLayer_walk_length_eq_two.symm step) ∈
          orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
            (interface.localLayerRightFaceOfRole role) := by
      simpa [nextLocalLayerPrefixCrossing,
        GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge] using hmem
    have hcases := orbitFace_eq_left_or_right_of_mem_dualWalkCrossingEdge
      embedded.cellulation.rotation.toRotationSystem htwoSided hunique
      interface.nextLocalLayer.walk
      (Fin.cast interface.nextLocalLayer_walk_length_eq_two.symm step)
      (interface.localLayerRightFaceOfRole role) hmem'
    fin_cases step <;> cases role <;>
      simp [LocalLayerRightFaceRole.ContainsPort, localLayerRightFaceOfRole,
        nextLocalLayer, nextLocalLayerWalk,
        interface.firstLayerFace_ne_nextCenterLayerFace,
        interface.firstLayerFace_ne_secondLayerFace,
        Ne.symm interface.firstLayerFace_ne_secondLayerFace,
        interface.secondLayerFace_ne_nextCenterLayerFace] at hcases ⊢
  · intro hport
    fin_cases step <;> cases role
    · simpa [nextLocalLayerPrefixCrossing,
        GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge,
        localLayerRightFaceOfRole, nextLocalLayer, nextLocalLayerWalk] using
        (dualWalkCrossingEdge_mem_leftFace
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem))
          hunique interface.nextLocalLayer.walk
          (Fin.cast interface.nextLocalLayer_walk_length_eq_two.symm (0 : Fin 2)))
    · simpa [nextLocalLayerPrefixCrossing,
        GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge,
        localLayerRightFaceOfRole, nextLocalLayer, nextLocalLayerWalk] using
        (dualWalkCrossingEdge_mem_rightFace
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem))
          hunique interface.nextLocalLayer.walk
          (Fin.cast interface.nextLocalLayer_walk_length_eq_two.symm (0 : Fin 2)))
    · simp [LocalLayerRightFaceRole.ContainsPort] at hport
    · simp [LocalLayerRightFaceRole.ContainsPort] at hport
    · simpa [nextLocalLayerPrefixCrossing,
        GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge,
        localLayerRightFaceOfRole, nextLocalLayer, nextLocalLayerWalk] using
        (dualWalkCrossingEdge_mem_leftFace
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem))
          hunique interface.nextLocalLayer.walk
          (Fin.cast interface.nextLocalLayer_walk_length_eq_two.symm (1 : Fin 2)))
    · simpa [nextLocalLayerPrefixCrossing,
        GoertzelV24AnnularCrosscut.SimpleDualCrosscut.crossingEdge,
        localLayerRightFaceOfRole, nextLocalLayer, nextLocalLayerWalk] using
        (dualWalkCrossingEdge_mem_rightFace
          (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
          (Finset.univ : Finset
            (OrbitFace embedded.cellulation.rotation.toRotationSystem))
          hunique interface.nextLocalLayer.walk
          (Fin.cast interface.nextLocalLayer_walk_length_eq_two.symm (1 : Fin 2)))

/-- Exact role-level incidence of a displayed crossing with an actual
outgoing occurrence-sensitive boundary fragment. -/
theorem nextLocalLayerPrefixCrossing_mem_boundaryFragmentEdges_iff_role
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
      interface.localLayerRightPrefixRegion)
    (step : Fin 2) :
    interface.nextLocalLayerPrefixCrossing step ∈
        boundaryRegionalFragmentEdges
          embedded.cellulation.rotation.toRotationSystem
          (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
          interface.localLayerRightPrefixRegion fragment ↔
      (interface.localLayerRightBoundaryFragmentRole fragment).ContainsPort
        step := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let edge := interface.nextLocalLayerPrefixCrossing step
  constructor
  · intro hedge
    have hedgeFace : edge ∈ orbitFaceBoundary RS fragment.1.1 :=
      (Finset.mem_inter.1
        (boundaryRegionalFragmentEdges_subset_boundary_inter_region RS
          (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
          interface.localLayerRightPrefixRegion fragment hedge)).1
    have hroleFace :=
      interface.localLayerRightFaceOfRole_boundaryFragmentRole fragment
    apply (interface.nextLocalLayerPrefixCrossing_mem_faceOfRole_iff
      (interface.localLayerRightBoundaryFragmentRole fragment) step).1
    rw [hroleFace]
    exact hedgeFace
  · intro hrole
    have hedgeCut : edge ∈
        indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing :=
      (mem_indexedCrossingEdgeSet_iff
        interface.nextLocalLayerPrefixCrossing edge).2 ⟨step, rfl⟩
    have hedgeRegion : edge ∈ interface.localLayerRightPrefixRegion :=
      interface.indexedNextLocalLayerPrefixCrossing_subset_rightPrefixRegion
        hedgeCut
    have hedgeFace : edge ∈ orbitFaceBoundary RS fragment.1.1 := by
      rw [← interface.localLayerRightFaceOfRole_boundaryFragmentRole fragment]
      exact (interface.nextLocalLayerPrefixCrossing_mem_faceOfRole_iff
        (interface.localLayerRightBoundaryFragmentRole fragment) step).2 hrole
    exact mem_boundaryRegionalFragmentEdges_of_face_injective RS htwoSided
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
      interface.localLayerRightPrefixRegion
      interface.localLayerRightPrefixBoundaryFragment_face_injective
      fragment edge hedgeCut hedgeFace hedgeRegion

/-- Outgoing face-continuation is equality of finite fragment coordinates. -/
theorem localLayerRightPrefixBoundedProfile_faceContinues_eq_true_iff_eq
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (interface.nextLocalLayerPrefixCrossing step) ≠ 0)
    (left right : Fin (Fintype.card (BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
      interface.localLayerRightPrefixRegion))) :
    (((interface.localLayerRightPrefixBoundedProfile color hcolor).profile
        |>.faceContinues left right) = true) ↔ left = right := by
  rw [interface.localLayerRightPrefixBoundedProfile_faceContinues_eq_true_iff]
  constructor
  · intro hface
    have hface' :
        (boundaryRegionalFragmentAt
          embedded.cellulation.rotation.toRotationSystem
          (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
          interface.localLayerRightPrefixRegion left).1.1 =
        (boundaryRegionalFragmentAt
          embedded.cellulation.rotation.toRotationSystem
          (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
          interface.localLayerRightPrefixRegion right).1.1 := by
      simpa only [localLayerRightPrefixBoundaryFragmentAt,
        congrArg (fun face => face.1)
          (interface.localLayerRightPrefixBoundaryFragmentEquiv_face
            (boundaryRegionalFragmentAt
              embedded.cellulation.rotation.toRotationSystem
              (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
              interface.localLayerRightPrefixRegion left)),
        congrArg (fun face => face.1)
          (interface.localLayerRightPrefixBoundaryFragmentEquiv_face
            (boundaryRegionalFragmentAt
              embedded.cellulation.rotation.toRotationSystem
              (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
              interface.localLayerRightPrefixRegion right))] using hface
    apply boundaryRegionalFragmentAt_injective
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
      interface.localLayerRightPrefixRegion
    apply interface.localLayerRightPrefixBoundaryFragment_face_injective
    exact Subtype.ext hface'
  · intro heq
    subst right
    rfl

/-- The outgoing profile's port-incidence matrix is exactly the fixed
three-role path pattern. -/
theorem localLayerRightPrefixBoundedProfile_fragmentContainsPort_eq_role
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (interface.nextLocalLayerPrefixCrossing step) ≠ 0)
    (index : Fin (Fintype.card (BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
      interface.localLayerRightPrefixRegion)))
    (step : Fin 2) :
    (((interface.localLayerRightPrefixBoundedProfile color hcolor).profile
        |>.fragmentContainsPort index (.inl step)) = true) ↔
      (interface.localLayerRightBoundaryFragmentRole
        (boundaryRegionalFragmentAt
          embedded.cellulation.rotation.toRotationSystem
          (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
          interface.localLayerRightPrefixRegion index)).ContainsPort step := by
  let data := interface.localLayerRightPrefixGraphCutData
  have hfragmentEdges : data.regionalFragmentEdges index =
      boundaryRegionalFragmentEdges
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
        interface.localLayerRightPrefixRegion
        (boundaryRegionalFragmentAt
          embedded.cellulation.rotation.toRotationSystem
          (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
          interface.localLayerRightPrefixRegion index) := by
    rw [data.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
      (regionalBoundaryGraphCutData_fragmentsOnFaceInRegion
        embedded.cellulation.rotation.toRotationSystem
        interface.localLayerRightPrefixRegion
        interface.nextLocalLayerPrefixCrossing)]
    rfl
  change ((data.regionalProfile color hcolor).fragmentContainsPort
      index (.inl step) = true) ↔ _
  rw [data.regionalProfile_fragmentContainsPort_eq_true_iff,
    hfragmentEdges]
  exact interface
    |>.nextLocalLayerPrefixCrossing_mem_boundaryFragmentEdges_iff_role
      (boundaryRegionalFragmentAt
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
        interface.localLayerRightPrefixRegion index) step

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
