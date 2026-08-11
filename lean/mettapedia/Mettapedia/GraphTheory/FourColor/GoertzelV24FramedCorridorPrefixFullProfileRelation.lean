import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileConnectivityRelation
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileFaceCoordinates
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileSupportResolution

/-!
# The full relational profile law for one source Cell

The cumulative source-prefix construction computes a complete five-field
profile on either side of one Cell.  The preceding modules proved the
connectivity and occurrence-sensitive face laws separately.  This file keeps
those laws together as one proposition: cut colors, tracked connectivity,
face identity, fragment-to-port incidence, and capped face progress all refer
to the same incoming and outgoing graph-derived profiles.

The law remains relational.  In particular, the face-cap coordinate retains
its finite existential assignment and the shared-rung residue.  No successor
profile is chosen, and no identification is made between the complete
hex-face boundary and the different literal removed-open-tangle carrier.
Connecting this law to the latter carrier's `Count` support is a subsequent
transport theorem, not a definitional coercion hidden here.

This proposition characterizes the two actual graph-derived states.  It is
not yet the finite transfer relation on arbitrary bounded states: the old
prefix component moves still mention their literal graph.  The factorization
step must contract those moves through the incoming profile and combine them
with the literal Cell `Count` support.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixFullProfileRelationEdgeSetDecidableEq :
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

/-- Finite outgoing fragment coordinates for the cumulative prefix after one
source Cell. -/
abbrev LocalLayerRightBoundaryIndex
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :=
  Fin (Fintype.card (BoundaryRegionalFragment
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet
      aligned.toInterface.nextLocalLayerPrefixCrossing)
    aligned.toInterface.localLayerRightPrefixRegion))

/-- The exact dependent input-profile carrier before embedding it in the
common four-fragment bounded carrier. -/
abbrev LocalLayerLeftPrefixProfileState
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :=
  CorridorCutProfile 2 0 (Fintype.card (BoundaryRegionalFragment
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet aligned.toInterface.localLayerPrefixCrossing)
    aligned.toInterface.localLayerLeftPrefixRegion))

/-- The exact dependent output-profile carrier after the source Cell. -/
abbrev LocalLayerRightPrefixProfileState
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :=
  CorridorCutProfile 2 0 (Fintype.card (BoundaryRegionalFragment
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet
      aligned.toInterface.nextLocalLayerPrefixCrossing)
    aligned.toInterface.localLayerRightPrefixRegion))

/-- The input profile's cut-color coordinate is the literal color on the
incoming source crossing. -/
theorem localLayerLeftPrefixBoundedProfile_edgeColor_toColor
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (step : Fin 2) :
    (((aligned.toInterface.localLayerLeftPrefixBoundedProfile color hcolor)
        |>.profile.edgeColor step).toColor) =
      color (aligned.toInterface.localLayerPrefixCrossing step) := by
  exact aligned.toInterface.localLayerLeftPrefixGraphCutData
    |>.regionalProfile_edgeColor_toColor color hcolor step

/-- The output profile's cut-color coordinate is the literal color on the
newly exposed source crossing. -/
theorem localLayerRightPrefixBoundedProfile_edgeColor_toColor
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0)
    (step : Fin 2) :
    (((aligned.toInterface.localLayerRightPrefixBoundedProfile color hcolor)
        |>.profile.edgeColor step).toColor) =
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step) := by
  exact aligned.toInterface.localLayerRightPrefixGraphCutData
    |>.regionalProfile_edgeColor_toColor color hcolor step

/-- The input profile's face-identity matrix names exactly the ambient faces
of its two finite boundary-fragment coordinates. -/
theorem localLayerLeftPrefixBoundedProfile_faceContinues_eq_true_iff
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (left right : aligned.LocalLayerLeftBoundaryIndex) :
    (((aligned.toInterface.localLayerLeftPrefixBoundedProfile color hcolor)
        |>.profile.faceContinues left right) = true) ↔
      (aligned.localLayerLeftBoundaryFragmentAt left).1.1 =
        (aligned.localLayerLeftBoundaryFragmentAt right).1.1 := by
  change
    ((aligned.toInterface.localLayerLeftPrefixGraphCutData
        |>.regionalProfile color hcolor).faceContinues left right = true) ↔ _
  rw [GraphCorridorCutData.regionalProfile_faceContinues_eq_true_iff]
  rfl

/-- The input profile's incidence matrix records membership of an incoming
crossing in the exact incoming boundary-fragment support. -/
theorem localLayerLeftPrefixBoundedProfile_fragmentContainsPort_eq_true_iff
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (index : aligned.LocalLayerLeftBoundaryIndex) (step : Fin 2) :
    (((aligned.toInterface.localLayerLeftPrefixBoundedProfile color hcolor)
        |>.profile.fragmentContainsPort index (.inl step)) = true) ↔
      aligned.toInterface.localLayerPrefixCrossing step ∈
        aligned.localLayerLeftBoundaryFragmentEdgesAt index := by
  let data := aligned.toInterface.localLayerLeftPrefixGraphCutData
  have hfragmentEdges : data.regionalFragmentEdges index =
      aligned.localLayerLeftBoundaryFragmentEdgesAt index := by
    rw [data.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
      (regionalBoundaryGraphCutData_fragmentsOnFaceInRegion
        embedded.cellulation.rotation.toRotationSystem
        aligned.toInterface.localLayerLeftPrefixRegion
        aligned.toInterface.localLayerPrefixCrossing)]
    rfl
  change
    ((data.regionalProfile color hcolor).fragmentContainsPort
        index (.inl step) = true) ↔ _
  rw [GraphCorridorCutData.regionalProfile_fragmentContainsPort_eq_true_iff,
    hfragmentEdges]
  rfl

/-- The single source-Cell relation, with all five finite profile fields kept
together.  The propositions below characterize the two graph-derived states;
they do not assert that arbitrary finite states have a deterministic update.
-/
structure LocalLayerPrefixFullProfileRelation
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (input : aligned.LocalLayerLeftPrefixProfileState)
    (output : aligned.LocalLayerRightPrefixProfileState) :
    Prop where
  leftEdgeColor : ∀ step : Fin 2,
    ((input.edgeColor step).toColor) =
      color (aligned.toInterface.localLayerPrefixCrossing step)
  rightEdgeColor : ∀ step : Fin 2,
    ((output.edgeColor step).toColor) =
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step)
  leftStrandConnected : ∀ (pair : TrackedColorPair) (left right : Fin 2),
    (input.strandConnected pair (.inl left) (.inl right) = true) ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color (aligned.toInterface.localLayerPrefixCrossing left)) ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color (aligned.toInterface.localLayerPrefixCrossing right)) ∧
        (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          aligned.toInterface.localLayerLeftPrefixRegion color
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
            (aligned.toInterface.localLayerPrefixCrossing left)
            (aligned.toInterface.localLayerPrefixCrossing right)
  rightStrandConnected : ∀ (pair : TrackedColorPair) (left right : Fin 2),
    (output.strandConnected pair (.inl left) (.inl right) = true) ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color (aligned.toInterface.nextLocalLayerPrefixCrossing left)) ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color (aligned.toInterface.nextLocalLayerPrefixCrossing right)) ∧
        Relation.ReflTransGen
          (aligned.localLayerTrackedComponentStep color
            (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2)
          (aligned.toInterface.nextLocalLayerPrefixCrossing left)
          (aligned.toInterface.nextLocalLayerPrefixCrossing right)
  leftFaceContinues : ∀ left right : aligned.LocalLayerLeftBoundaryIndex,
    (input.faceContinues left right = true) ↔
      (aligned.localLayerLeftBoundaryFragmentAt left).1.1 =
        (aligned.localLayerLeftBoundaryFragmentAt right).1.1
  rightFaceContinues : ∀ left right : aligned.LocalLayerRightBoundaryIndex,
    (output.faceContinues left right = true) ↔
      (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt left).1.1 =
        (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt right).1.1
  leftFragmentContainsPort :
    ∀ (index : aligned.LocalLayerLeftBoundaryIndex) (step : Fin 2),
      (input.fragmentContainsPort index (.inl step) = true) ↔
        aligned.toInterface.localLayerPrefixCrossing step ∈
          aligned.localLayerLeftBoundaryFragmentEdgesAt index
  rightFragmentContainsPort :
    ∀ (index : aligned.LocalLayerRightBoundaryIndex) (step : Fin 2),
      (output.fragmentContainsPort index (.inl step) = true) ↔
        ∃ factorFragment ∈
            aligned.toInterface.localLayerCellFactorFragments
              (aligned.toInterface
                |>.localLayerRightPrefixBoundaryFragmentAt index),
          aligned.toInterface.nextLocalLayerPrefixCrossing step ∈
            faceRegionalFragmentEdges
              embedded.cellulation.rotation.toRotationSystem
              (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
                (aligned.toInterface
                  |>.localLayerRightPrefixBoundaryFragmentAt index).1.1)
              aligned.toInterface.localLayerCellBoundaryRegion
              factorFragment
  faceLengthCap : ∀ index : aligned.LocalLayerRightBoundaryIndex,
    ∃ assignment : aligned.LocalLayerLeftFactor
          (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt index) →
        Option aligned.LocalLayerLeftBoundaryIndex,
      (∀ factor, factor ∈ aligned.localLayerLeftFactorFragments
            (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt
              index) →
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
              (input.faceLengthCap inputIndex).val =
                aligned.localLayerLeftFactorPositionCap
                  (aligned.toInterface
                    |>.localLayerRightPrefixBoundaryFragmentAt index)
                  factor
        | none =>
            aligned.LocalLayerLeftFactorContainsSharedRung
                (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt
                  index)
                factor ∧
              aligned.localLayerLeftFactorEdges
                  (aligned.toInterface
                    |>.localLayerRightPrefixBoundaryFragmentAt index)
                  factor = {aligned.toInterface.localLayerSharedRungEdge} ∧
              aligned.localLayerLeftFactorPositionCap
                (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt
                  index)
                factor = 1) ∧
      (output.faceLengthCap index).val =
        min
          (min
              (∑ factor ∈ aligned.localLayerLeftFactorFragments
                  (aligned.toInterface
                    |>.localLayerRightPrefixBoundaryFragmentAt index),
                match assignment factor with
                | some inputIndex =>
                    (input.faceLengthCap inputIndex).val
                | none => 1)
              5 +
            (if (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt
                    index).1.1 =
                  aligned.toInterface.nextCenterLayerFace.1 then 5 else 1) -
            (if (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt
                    index).1.1 =
                  aligned.toInterface.nextCenterLayerFace.1 then 1 else 0))
          5

/-- The two actual cumulative profiles on either side of a source Cell obey
the single full five-field relational law. -/
theorem localLayerPrefixFullProfileRelation
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : G.edgeSet → Color)
    (hleftColor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (hrightColor : ∀ step,
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0) :
    aligned.LocalLayerPrefixFullProfileRelation color
      (aligned.toInterface.localLayerLeftPrefixBoundedProfile color
        hleftColor).profile
      (aligned.toInterface.localLayerRightPrefixBoundedProfile color
        hrightColor).profile := by
  refine {
    leftEdgeColor := ?_
    rightEdgeColor := ?_
    leftStrandConnected := ?_
    rightStrandConnected := ?_
    leftFaceContinues := ?_
    rightFaceContinues := ?_
    leftFragmentContainsPort := ?_
    rightFragmentContainsPort := ?_
    faceLengthCap := ?_ }
  · exact aligned.localLayerLeftPrefixBoundedProfile_edgeColor_toColor
      color hleftColor
  · exact aligned.localLayerRightPrefixBoundedProfile_edgeColor_toColor
      color hrightColor
  · exact aligned.localLayerLeftPrefixBoundedProfile_strandConnected_eq_true_iff
      color hleftColor
  · exact aligned.localLayerRightPrefixBoundedProfile_strandConnected_eq_true_iff
      color hrightColor
  · exact aligned.localLayerLeftPrefixBoundedProfile_faceContinues_eq_true_iff
      color hleftColor
  · exact aligned.toInterface
      |>.localLayerRightPrefixBoundedProfile_faceContinues_eq_true_iff
        color hrightColor
  · exact aligned.localLayerLeftPrefixBoundedProfile_fragmentContainsPort_eq_true_iff
      color hleftColor
  · exact
      SourceConsecutiveSlabInterface.localLayerRightPrefixBoundedProfile_fragmentContainsPort_eq_true_iff
        aligned color hrightColor
  · exact aligned.exists_localLayerRightPrefixProfileCoherentFaceCapRelation
      hcubic hrotation color hleftColor hrightColor

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
