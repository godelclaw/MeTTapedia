import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileCellFactor

/-!
# Support-preserving resolution of source-prefix face factors

The old-prefix contribution to one outgoing face fragment is a finite family
of literal factor fragments.  A numerical cap value alone does not identify
which incoming profile fragment supplied a contribution: distinct fragments
can have the same capped size.  This file resolves each contributing factor
by its exact edge support instead.

Every factor is assigned either an incoming boundary-profile coordinate with
identical support, or the explicit singleton shared-rung residue.  The same
assignment can therefore be used coherently for face identity, port
incidence, and capped progress in the later finite transfer relation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileFaceCapUpdate
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileSupportResolutionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceCornerAlignedSlabInterface

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

/-- An incoming coordinate represents the same ambient face and the same
literal edge support as the selected old-prefix factor.  Support equality by
itself is deliberately not enough: one cut edge is incident with two ambient
faces. -/
def LocalLayerLeftFactorHasProfileFragmentCoordinate
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment) : Prop :=
  ∃ index : aligned.LocalLayerLeftBoundaryIndex,
    (aligned.localLayerLeftBoundaryFragmentAt index).1.1 = fragment.1.1 ∧
      aligned.localLayerLeftBoundaryFragmentEdgesAt index =
        aligned.localLayerLeftFactorEdges fragment factor

/-- A factor meeting the incoming cut has a profile coordinate preserving
both its face and its full support. -/
theorem localLayerLeftFactorHasProfileFragmentCoordinate_of_touchesPrefixCut
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment)
    (htouches : aligned.LocalLayerLeftFactorTouchesPrefixCut fragment factor) :
    aligned.LocalLayerLeftFactorHasProfileFragmentCoordinate fragment factor := by
  rcases htouches with ⟨step, htouch⟩
  let witness := aligned.localLayerLeftFactorBoundaryWitnessOfTouch
    fragment factor step htouch
  rcases exists_boundaryRegionalFragmentAt_eq
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet aligned.toInterface.localLayerPrefixCrossing)
      aligned.toInterface.localLayerLeftPrefixRegion witness.boundaryFragment with
    ⟨index, hindex⟩
  refine ⟨index, ?_, ?_⟩
  · exact (congrArg (fun boundaryFragment => boundaryFragment.1.1) hindex).trans
      witness.face_eq
  · change aligned.localLayerLeftBoundaryFragmentEdges
      (aligned.localLayerLeftBoundaryFragmentAt index) = _
    rw [show aligned.localLayerLeftBoundaryFragmentAt index =
      witness.boundaryFragment by exact hindex]
    exact witness.edges_eq

/-- Every contributing factor has a full face/support coordinate unless it
is the explicit shared-rung residue. -/
theorem localLayerLeftFactorHasProfileFragmentCoordinate_or_containsSharedRung
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment)
    (hfactor : factor ∈ aligned.localLayerLeftFactorFragments fragment) :
    aligned.LocalLayerLeftFactorHasProfileFragmentCoordinate fragment factor ∨
      aligned.LocalLayerLeftFactorContainsSharedRung fragment factor := by
  rcases aligned
      |>.localLayerLeftFactorFragment_touches_prefixCut_or_contains_sharedRung
        hcubic hrotation fragment factor hfactor with htouches | hshared
  · exact Or.inl
      (aligned
        |>.localLayerLeftFactorHasProfileFragmentCoordinate_of_touchesPrefixCut
          fragment factor htouches)
  · exact Or.inr hshared

/-- A support-selected incoming coordinate carries the occurrence-sensitive
cap of that same factor.  This is an indexed form of the earlier existential
cap theorem; it prevents a later proof from switching to a different
coordinate that happens to have the same number. -/
theorem localLayerLeftPrefixProfileFaceLengthCap_eq_factorPositionCap_of_support
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment)
    (index : aligned.LocalLayerLeftBoundaryIndex)
    (hsupport : aligned.localLayerLeftBoundaryFragmentEdgesAt index =
      aligned.localLayerLeftFactorEdges fragment factor) :
    (((aligned.toInterface.localLayerLeftPrefixBoundedProfile color hcolor)
        |>.profile.faceLengthCap index).val) =
      aligned.localLayerLeftFactorPositionCap fragment factor := by
  let interface := aligned.toInterface
  let data := interface.localLayerLeftPrefixGraphCutData
  have hfragmentEdges : data.regionalFragmentEdges index =
      aligned.localLayerLeftBoundaryFragmentEdgesAt index := by
    rw [data.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
      (regionalBoundaryGraphCutData_fragmentsOnFaceInRegion
        embedded.cellulation.rotation.toRotationSystem
        interface.localLayerLeftPrefixRegion
        interface.localLayerPrefixCrossing)]
    rfl
  change min (data.regionalFragmentEdges index).card 5 = _
  rw [hfragmentEdges, hsupport]
  simpa [localLayerLeftFactorEdges, localLayerLeftFactorPositionCap] using
    (min_card_faceRegionalFragmentEdges_eq_positions
      embedded.cellulation.rotation.toRotationSystem htwoSided
      (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
        fragment.1.1)
      interface.localLayerLeftPrefixRegion factor 5)

/-- Resolve every contributing old-prefix factor by its literal support.

`some index` identifies a genuine incoming boundary fragment whose edge
support and ambient face are exactly those of the factor.  `none` is reserved
for the one local factor that consists solely of the shared corridor rung. -/
theorem exists_localLayerLeftFactorSupportResolution
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment) :
    ∃ assignment : aligned.LocalLayerLeftFactor fragment →
        Option aligned.LocalLayerLeftBoundaryIndex,
      ∀ factor, factor ∈ aligned.localLayerLeftFactorFragments fragment →
        match assignment factor with
        | some index =>
            (aligned.localLayerLeftBoundaryFragmentAt index).1.1 =
                fragment.1.1 ∧
              aligned.localLayerLeftBoundaryFragmentEdgesAt index =
                aligned.localLayerLeftFactorEdges fragment factor
        | none =>
            aligned.LocalLayerLeftFactorContainsSharedRung fragment factor ∧
              aligned.localLayerLeftFactorEdges fragment factor =
                {aligned.toInterface.localLayerSharedRungEdge} := by
  classical
  let assignment : aligned.LocalLayerLeftFactor fragment →
      Option aligned.LocalLayerLeftBoundaryIndex := fun factor =>
    if hcoordinate :
        aligned.LocalLayerLeftFactorHasProfileFragmentCoordinate
          fragment factor then
      some (Classical.choose hcoordinate)
    else
      none
  refine ⟨assignment, ?_⟩
  intro factor hfactor
  by_cases hcoordinate :
      aligned.LocalLayerLeftFactorHasProfileFragmentCoordinate fragment factor
  · simp only [assignment, dif_pos hcoordinate]
    exact Classical.choose_spec hcoordinate
  · simp only [assignment, dif_neg hcoordinate]
    rcases aligned
        |>.localLayerLeftFactorHasProfileFragmentCoordinate_or_containsSharedRung
        hcubic hrotation fragment factor hfactor with hprofile | hshared
    · exact (hcoordinate hprofile).elim
    · exact ⟨hshared,
        aligned.localLayerLeftFactorEdges_eq_singleton_of_containsSharedRung
          fragment factor hshared⟩

/-- The outgoing cap law using one coherent face/support assignment.

Unlike the earlier cap-only relation, the selected incoming index here is
also the coordinate used to identify the factor's ambient face and support.
Thus all face fields of the eventual five-coordinate update can consume the
same finite witness. -/
theorem exists_localLayerRightPrefixProfileCoherentFaceCapRelation
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : G.edgeSet → Color)
    (hleftColor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (hrightColor : ∀ step,
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0)
    (index : Fin (Fintype.card (BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet
        aligned.toInterface.nextLocalLayerPrefixCrossing)
      aligned.toInterface.localLayerRightPrefixRegion))) :
    ∃ assignment : aligned.LocalLayerLeftFactor
          (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt index) →
        Option aligned.LocalLayerLeftBoundaryIndex,
      (∀ factor, factor ∈ aligned.localLayerLeftFactorFragments
            (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt index) →
        match assignment factor with
        | some inputIndex =>
            (aligned.localLayerLeftBoundaryFragmentAt inputIndex).1.1 =
                (aligned.toInterface
                  |>.localLayerRightPrefixBoundaryFragmentAt index).1.1 ∧
              aligned.localLayerLeftBoundaryFragmentEdgesAt inputIndex =
                aligned.localLayerLeftFactorEdges
                  (aligned.toInterface
                    |>.localLayerRightPrefixBoundaryFragmentAt index)
                  factor ∧
              (((aligned.toInterface.localLayerLeftPrefixBoundedProfile
                    color hleftColor).profile.faceLengthCap inputIndex).val) =
                aligned.localLayerLeftFactorPositionCap
                  (aligned.toInterface
                    |>.localLayerRightPrefixBoundaryFragmentAt index)
                  factor
        | none =>
            aligned.LocalLayerLeftFactorContainsSharedRung
                (aligned.toInterface
                  |>.localLayerRightPrefixBoundaryFragmentAt index)
                factor ∧
              aligned.localLayerLeftFactorEdges
                  (aligned.toInterface
                    |>.localLayerRightPrefixBoundaryFragmentAt index)
                  factor = {aligned.toInterface.localLayerSharedRungEdge} ∧
              aligned.localLayerLeftFactorPositionCap
                  (aligned.toInterface
                    |>.localLayerRightPrefixBoundaryFragmentAt index)
                  factor = 1) ∧
      (((aligned.toInterface.localLayerRightPrefixBoundedProfile
          color hrightColor).profile.faceLengthCap index).val) =
        min
          (min
              (∑ factor ∈ aligned.localLayerLeftFactorFragments
                  (aligned.toInterface
                    |>.localLayerRightPrefixBoundaryFragmentAt index),
                match assignment factor with
                | some inputIndex =>
                    ((aligned.toInterface.localLayerLeftPrefixBoundedProfile
                        color hleftColor).profile.faceLengthCap inputIndex).val
                | none => 1)
              5 +
            (if (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt
                    index).1.1 =
                  aligned.toInterface.nextCenterLayerFace.1 then 5 else 1) -
            (if (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt
                    index).1.1 =
                  aligned.toInterface.nextCenterLayerFace.1 then 1 else 0))
          5 := by
  let fragment :=
    aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt index
  rcases aligned.exists_localLayerLeftFactorSupportResolution hcubic hrotation
      fragment with ⟨assignment, hresolution⟩
  have hcoherent : ∀ factor,
      factor ∈ aligned.localLayerLeftFactorFragments fragment →
        match assignment factor with
        | some inputIndex =>
            (aligned.localLayerLeftBoundaryFragmentAt inputIndex).1.1 =
                fragment.1.1 ∧
              aligned.localLayerLeftBoundaryFragmentEdgesAt inputIndex =
                aligned.localLayerLeftFactorEdges fragment factor ∧
              (((aligned.toInterface.localLayerLeftPrefixBoundedProfile
                    color hleftColor).profile.faceLengthCap inputIndex).val) =
                aligned.localLayerLeftFactorPositionCap fragment factor
        | none =>
            aligned.LocalLayerLeftFactorContainsSharedRung fragment factor ∧
              aligned.localLayerLeftFactorEdges fragment factor =
                {aligned.toInterface.localLayerSharedRungEdge} ∧
              aligned.localLayerLeftFactorPositionCap fragment factor = 1 := by
    intro factor hfactor
    have hresolved := hresolution factor hfactor
    cases hassignment : assignment factor with
    | none =>
        simp only [hassignment] at hresolved ⊢
        exact ⟨hresolved.1, hresolved.2,
          aligned.localLayerLeftFactorPositionCap_eq_one_of_containsSharedRung
            fragment factor hresolved.1⟩
    | some inputIndex =>
        simp only [hassignment] at hresolved ⊢
        exact ⟨hresolved.1, hresolved.2,
          aligned
            |>.localLayerLeftPrefixProfileFaceLengthCap_eq_factorPositionCap_of_support
              color hleftColor fragment factor inputIndex hresolved.2⟩
  have hsum :
      aligned.toInterface.localLayerFactorFragmentCapSum
          aligned.toInterface.localLayerLeftPrefixRegion fragment =
        min
          (∑ factor ∈ aligned.localLayerLeftFactorFragments fragment,
            match assignment factor with
            | some inputIndex =>
                ((aligned.toInterface.localLayerLeftPrefixBoundedProfile
                    color hleftColor).profile.faceLengthCap inputIndex).val
            | none => 1)
          5 := by
    change
      min
          (∑ factor ∈ aligned.localLayerLeftFactorFragments fragment,
            aligned.localLayerLeftFactorPositionCap fragment factor)
          5 = _
    congr 1
    apply Finset.sum_congr rfl
    intro factor hfactor
    have hfactorData := hcoherent factor hfactor
    cases hassignment : assignment factor with
    | none =>
        simp only [hassignment] at hfactorData ⊢
        exact hfactorData.2.2
    | some inputIndex =>
        simp only [hassignment] at hfactorData ⊢
        exact hfactorData.2.2.symm
  refine ⟨assignment, hcoherent, ?_⟩
  rw [aligned.localLayerRightPrefixBoundedProfile_faceLengthCap_eq_cellUpdate,
    hsum]

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
