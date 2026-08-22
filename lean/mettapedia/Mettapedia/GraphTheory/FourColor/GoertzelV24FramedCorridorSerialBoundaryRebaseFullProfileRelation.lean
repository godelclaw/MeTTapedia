import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixFullProfileRelation
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebase

/-!
# Full profile relation for the literal serial boundary rebase

One source Cell ends at its actual outgoing two-edge presentation.  Before
the next Cell is adjoined, the same accumulated prefix is presented with the
next Cell's two input crossings.  These two presentations are not
definitionally equal; their change is the boundary-rebase letter.

This module gives that letter its exact graph-level semantics.  The old
prefix, the two newly displayed edges, and the residual seam determine the
successor tracked and facial graphs by the already-proved three-factor
closure laws.  All five manuscript profile coordinates are packaged from the
same two regional carriers.

This is the semantic target for a finite rebase decoder.  It does not yet
prove that the old profile and `BoundedSerialBoundaryRebaseLetterCode`
determine the new profile: that quotient still requires the old-prefix
attachment to factor through the two named old ports.
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
open GoertzelV24RotationFaceFragments
open GoertzelV24SimpleGraphSupResidual
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFullProfileRelationEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The exact five-field relation between the outgoing presentation of one
literal source Cell and the input presentation of its successor. -/
structure SourceCorridorSerialBoundaryRebaseFullProfileRelation
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (input : SerialCutProfileState
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset))
    (output : SerialCutProfileState
      (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))) : Prop where
  inputEdgeColor : ∀ step : Fin 2,
    (input.edgeColor step).toColor =
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).nextLocalLayerPrefixCrossing step)
  outputEdgeColor : ∀ step : Fin 2,
    (output.edgeColor step).toColor =
      color (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
        hrotation htwoSided hunique offset hnext step)
  inputStrandConnected : ∀ (pair : TrackedColorPair) (left right : Fin 2),
    (input.strandConnected pair (.inl left) (.inl right) = true) ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color ((sourceSlabInterfaceAt realization hcubic hrotation
            htwoSided hunique offset).nextLocalLayerPrefixCrossing left)) ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color ((sourceSlabInterfaceAt realization hcubic hrotation
            htwoSided hunique offset).nextLocalLayerPrefixCrossing right)) ∧
        (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges color
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
            ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
              hunique offset).nextLocalLayerPrefixCrossing left)
            ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
              hunique offset).nextLocalLayerPrefixCrossing right)
  outputStrandConnected : ∀ (pair : TrackedColorPair) (left right : Fin 2),
    (output.strandConnected pair (.inl left) (.inl right) = true) ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color (sourceCorridorSerialBoundaryRebaseCrossingAt realization
            hcubic hrotation htwoSided hunique offset hnext left)) ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color (sourceCorridorSerialBoundaryRebaseCrossingAt realization
            hcubic hrotation htwoSided hunique offset hnext right)) ∧
        Relation.ReflTransGen
          (ThreeFactorComponentStep
            (regionalTrackedEdgeGraph
              embedded.cellulation.rotation.toRotationSystem
              (sourceCorridorSerialPrefixCutDataAt realization hcubic
                hrotation htwoSided hunique offset).regionEdges color
              (trackedColorPairColors pair).1
              (trackedColorPairColors pair).2)
            (regionalTrackedEdgeGraph
              embedded.cellulation.rotation.toRotationSystem
              (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
                hrotation htwoSided hunique offset hnext) color
              (trackedColorPairColors pair).1
              (trackedColorPairColors pair).2)
            (sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization hcubic
              hrotation htwoSided hunique offset hnext color
              (trackedColorPairColors pair).1
              (trackedColorPairColors pair).2))
          (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
            hrotation htwoSided hunique offset hnext left)
          (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
            hrotation htwoSided hunique offset hnext right)
  inputFaceContinues : ∀
      (left right : SerialCutFragmentIndex
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset)),
    (input.faceContinues left right = true) ↔
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).fragmentFace left =
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).fragmentFace right
  outputFaceContinues : ∀
      (left right : SerialCutFragmentIndex
        (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))),
    (output.faceContinues left right = true) ↔
      (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
        ).fragmentFace left =
      (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
        ).fragmentFace right
  inputFragmentContainsPort : ∀
      (index : SerialCutFragmentIndex
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset))
      (port : CorridorPort 2 0),
    (input.fragmentContainsPort index port = true) ↔
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).portEdge port ∈
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionalFragmentEdges index
  outputFragmentContainsPort : ∀
      (index : SerialCutFragmentIndex
        (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)))
      (port : CorridorPort 2 0),
    (output.fragmentContainsPort index port = true) ↔
      (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
        ).portEdge port ∈
      (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
        ).regionalFragmentEdges index
  inputFaceLengthCap : ∀
      index : SerialCutFragmentIndex
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset),
    (input.faceLengthCap index).val =
      min ((sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionalFragmentEdges index).card 5
  outputFaceLengthCap : ∀
      index : SerialCutFragmentIndex
        (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)),
    (output.faceLengthCap index).val =
      min ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
        ).regionalFragmentEdges index).card 5
  outputFaceReachable : ∀
      (root : embedded.cellulation.rotation.toRotationSystem.D)
      (left right : Fin
        (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card),
    (faceRegionalAmbientPositionGraph
      embedded.cellulation.rotation.toRotationSystem root
      (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
        hunique (sourceCorridorSerialNextOffset offset hnext))).Reachable
          left right ↔
      Relation.ReflTransGen
        (ThreeFactorComponentStep
          (faceRegionalAmbientPositionGraph
            embedded.cellulation.rotation.toRotationSystem root
            (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
              htwoSided hunique offset).regionEdges)
          (faceRegionalAmbientPositionGraph
            embedded.cellulation.rotation.toRotationSystem root
            (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
              hrotation htwoSided hunique offset hnext))
          (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic
            hrotation htwoSided hunique offset hnext root)) left right

/-- The two graph-derived profiles on either side of a literal rebase satisfy
the exact joint relation. -/
theorem sourceCorridorSerialBoundaryRebaseFullProfileRelation
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hinputColor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0)
    (houtputColor : ∀ step,
      color (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
        hrotation htwoSided hunique offset hnext step) ≠ 0) :
    SourceCorridorSerialBoundaryRebaseFullProfileRelation realization hcubic
      hrotation htwoSided hunique offset hnext color
      ((sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionalProfile color hinputColor)
      ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
        ).regionalProfile color houtputColor) := by
  let inputData := sourceCorridorSerialPrefixCutDataAt realization hcubic
    hrotation htwoSided hunique offset
  let outputData := sourceCorridorSerialInputCutDataAt realization hcubic
    hrotation htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  refine {
    inputEdgeColor := ?_
    outputEdgeColor := ?_
    inputStrandConnected := ?_
    outputStrandConnected := ?_
    inputFaceContinues := ?_
    outputFaceContinues := ?_
    inputFragmentContainsPort := ?_
    outputFragmentContainsPort := ?_
    inputFaceLengthCap := ?_
    outputFaceLengthCap := ?_
    outputFaceReachable := ?_ }
  · intro step
    exact inputData.regionalProfile_edgeColor_toColor color hinputColor step
  · intro step
    exact outputData.regionalProfile_edgeColor_toColor color houtputColor step
  · intro pair left right
    rw [inputData.regionalProfile_strandConnected_eq_true_iff]
    constructor
    · rintro ⟨_hleftMem, _hrightMem, hleft, hright, hreachable⟩
      exact ⟨hleft, hright, hreachable⟩
    · rintro ⟨hleft, hright, hreachable⟩
      exact ⟨
        sourceCorridorSerialPrefixCutDataAt_portsInRegion realization hcubic
          hrotation htwoSided hunique offset (.inl left),
        sourceCorridorSerialPrefixCutDataAt_portsInRegion realization hcubic
          hrotation htwoSided hunique offset (.inl right),
        hleft, hright, hreachable⟩
  · intro pair left right
    rw [outputData.regionalProfile_strandConnected_eq_true_iff]
    constructor
    · rintro ⟨_hleftMem, _hrightMem, hleft, hright, hreachable⟩
      refine ⟨hleft, hright, ?_⟩
      change
        (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialCutRegionAt realization hcubic hrotation
            htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
          color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
            (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
              hrotation htwoSided hunique offset hnext left)
            (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
              hrotation htwoSided hunique offset hnext right) at hreachable
      rw [sourceCorridorSerialInputTrackedGraph_next_eq_rebase_three_factor
        realization hcubic hrotation htwoSided hunique offset hnext] at hreachable
      exact (reachable_sup_sup_iff_threeFactorComponentClosure _ _ _ _ _).1
        hreachable
    · rintro ⟨hleft, hright, hreachable⟩
      refine ⟨
        sourceCorridorSerialInputCutDataAt_portsInRegion realization hcubic
          hrotation htwoSided hunique
          (sourceCorridorSerialNextOffset offset hnext) (.inl left),
        sourceCorridorSerialInputCutDataAt_portsInRegion realization hcubic
          hrotation htwoSided hunique
        (sourceCorridorSerialNextOffset offset hnext) (.inl right),
        hleft, hright, ?_⟩
      change
        (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialCutRegionAt realization hcubic hrotation
            htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
          color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
            (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
              hrotation htwoSided hunique offset hnext left)
            (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
              hrotation htwoSided hunique offset hnext right)
      rw [sourceCorridorSerialInputTrackedGraph_next_eq_rebase_three_factor
        realization hcubic hrotation htwoSided hunique offset hnext]
      exact (reachable_sup_sup_iff_threeFactorComponentClosure _ _ _ _ _).2
        hreachable
  · intro left right
    exact inputData.regionalProfile_faceContinues_eq_true_iff
      color hinputColor left right
  · intro left right
    exact outputData.regionalProfile_faceContinues_eq_true_iff
      color houtputColor left right
  · intro index port
    exact inputData.regionalProfile_fragmentContainsPort_eq_true_iff
      color hinputColor index port
  · intro index port
    exact outputData.regionalProfile_fragmentContainsPort_eq_true_iff
      color houtputColor index port
  · intro index
    exact inputData.regionalProfile_faceLengthCap_val color hinputColor index
  · intro index
    exact outputData.regionalProfile_faceLengthCap_val color houtputColor index
  · intro root left right
    rw [sourceCorridorSerialInputFaceGraph_next_eq_rebase_three_factor
      realization hcubic hrotation htwoSided hunique offset hnext]
    exact reachable_sup_sup_iff_threeFactorComponentClosure _ _ _ _ _

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
