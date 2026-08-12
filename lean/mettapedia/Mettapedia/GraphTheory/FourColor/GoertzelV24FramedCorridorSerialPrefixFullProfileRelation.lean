import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixUpdate

/-!
# Full profile relation for one literal serial source Cell

The serial corridor prefix grows by adjoining the actual complementary open
Cell selected by the source.  Connectivity and facial continuation may cross
the displayed factor seam, so the update is relational rather than a
fieldwise function.

This file packages the two graph-derived profiles together with the exact
three-factor tracked and facial closures already proved for that literal
union.  All five profile fields are characterized from the same regional
carriers.  No deterministic transition, terminal reconstruction, or final
annular splice is asserted here.
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

local instance framedCorridorSerialPrefixFullProfileRelationEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The dependent profile carrier determined by one graph-derived cut. -/
abbrev SerialCutProfileState
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    {RS : RotationSystem V G.edgeSet}
    (_data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount) :=
  CorridorCutProfile crossingEdgeCount terminalCount faceFragmentCount

/-- The finite face-fragment coordinates determined by one graph-derived cut. -/
abbrev SerialCutFragmentIndex
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    {RS : RotationSystem V G.edgeSet}
    (_data : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount) :=
  Fin faceFragmentCount

/-- One source-indexed literal prefix update, with all five finite profile
coordinates and both residual seam closures kept in a single relation.

The input and output states remain explicit arguments: this is the source's
relational transfer step, not a claim that an input state computes a unique
output state. -/
structure SourceCorridorSerialPrefixFullProfileRelation
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
    (color : G.edgeSet → Color)
    (input : SerialCutProfileState
      (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique offset))
    (output : SerialCutProfileState
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset)) : Prop where
  inputEdgeColor : ∀ step : Fin 2,
    (input.edgeColor step).toColor =
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).localLayerPrefixCrossing step)
  outputEdgeColor : ∀ step : Fin 2,
    (output.edgeColor step).toColor =
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).nextLocalLayerPrefixCrossing step)
  inputStrandConnected : ∀ (pair : TrackedColorPair) (left right : Fin 2),
    (input.strandConnected pair (.inl left) (.inl right) = true) ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color ((sourceSlabInterfaceAt realization hcubic hrotation
            htwoSided hunique offset).localLayerPrefixCrossing left)) ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color ((sourceSlabInterfaceAt realization hcubic hrotation
            htwoSided hunique offset).localLayerPrefixCrossing right)) ∧
        (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialCutRegionAt realization hcubic hrotation
            htwoSided hunique offset) color
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
            ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
              hunique offset).localLayerPrefixCrossing left)
            ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
              hunique offset).localLayerPrefixCrossing right)
  outputStrandConnected : ∀ (pair : TrackedColorPair) (left right : Fin 2),
    (output.strandConnected pair (.inl left) (.inl right) = true) ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color ((sourceSlabInterfaceAt realization hcubic hrotation
            htwoSided hunique offset).nextLocalLayerPrefixCrossing left)) ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color ((sourceSlabInterfaceAt realization hcubic hrotation
            htwoSided hunique offset).nextLocalLayerPrefixCrossing right)) ∧
        Relation.ReflTransGen
          (ThreeFactorComponentStep
            (regionalTrackedEdgeGraph
              embedded.cellulation.rotation.toRotationSystem
              (sourceCorridorSerialCutRegionAt realization hcubic hrotation
                htwoSided hunique offset) color
              (trackedColorPairColors pair).1
              (trackedColorPairColors pair).2)
            (regionalTrackedEdgeGraph
              embedded.cellulation.rotation.toRotationSystem
              (sourceSlabLiteralCellRegionAt realization hcubic hrotation
                htwoSided hunique offset) color
              (trackedColorPairColors pair).1
              (trackedColorPairColors pair).2)
            (sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic
              hrotation htwoSided hunique offset color
              (trackedColorPairColors pair).1
              (trackedColorPairColors pair).2))
          ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).nextLocalLayerPrefixCrossing left)
          ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).nextLocalLayerPrefixCrossing right)
  inputFaceContinues : ∀
      (left right : SerialCutFragmentIndex
        (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
          htwoSided hunique offset)),
    (input.faceContinues left right = true) ↔
      (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique offset).fragmentFace left =
      (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique offset).fragmentFace right
  outputFaceContinues : ∀
      (left right : SerialCutFragmentIndex
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset)),
    (output.faceContinues left right = true) ↔
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).fragmentFace left =
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).fragmentFace right
  inputFragmentContainsPort : ∀
      (index : SerialCutFragmentIndex
        (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
          htwoSided hunique offset))
      (port : CorridorPort 2 0),
    (input.fragmentContainsPort index port = true) ↔
      (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique offset).portEdge port ∈
      (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionalFragmentEdges index
  outputFragmentContainsPort : ∀
      (index : SerialCutFragmentIndex
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset))
      (port : CorridorPort 2 0),
    (output.fragmentContainsPort index port = true) ↔
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).portEdge port ∈
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionalFragmentEdges index
  inputFaceLengthCap : ∀
      index : SerialCutFragmentIndex
        (sourceCorridorSerialInputCutDataAt realization hcubic hrotation
          htwoSided hunique offset),
    (input.faceLengthCap index).val =
      min ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionalFragmentEdges index).card 5
  outputFaceLengthCap : ∀
      index : SerialCutFragmentIndex
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset),
    (output.faceLengthCap index).val =
      min ((sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionalFragmentEdges index).card 5
  outputFaceReachable : ∀
      (root : embedded.cellulation.rotation.toRotationSystem.D)
      (left right : Fin
        (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card),
    (faceRegionalAmbientPositionGraph
      embedded.cellulation.rotation.toRotationSystem root
      (sourceCorridorSerialPrefixRegion realization hcubic hrotation
        htwoSided hunique (offset.val + 1))).Reachable left right ↔
      Relation.ReflTransGen
        (ThreeFactorComponentStep
          (faceRegionalAmbientPositionGraph
            embedded.cellulation.rotation.toRotationSystem root
            (sourceCorridorSerialCutRegionAt realization hcubic hrotation
              htwoSided hunique offset))
          (faceRegionalAmbientPositionGraph
            embedded.cellulation.rotation.toRotationSystem root
            (sourceSlabLiteralCellRegionAt realization hcubic hrotation
              htwoSided hunique offset))
          (sourceCorridorSerialInputFaceSeamGraphAt realization hcubic
            hrotation htwoSided hunique offset root)) left right

/-- The two actual graph-derived profiles on either side of one literal
source Cell satisfy the joint five-field serial relation. -/
theorem sourceCorridorSerialPrefixFullProfileRelation
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
    (color : G.edgeSet → Color)
    (hinputColor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).localLayerPrefixCrossing step) ≠ 0)
    (houtputColor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0) :
    SourceCorridorSerialPrefixFullProfileRelation realization hcubic
      hrotation htwoSided hunique offset color
      ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionalProfile color hinputColor)
      ((sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionalProfile color houtputColor) := by
  let inputData := sourceCorridorSerialInputCutDataAt realization hcubic
    hrotation htwoSided hunique offset
  let outputData := sourceCorridorSerialPrefixCutDataAt realization hcubic
    hrotation htwoSided hunique offset
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
        sourceCorridorSerialInputCutDataAt_portsInRegion realization hcubic
          hrotation htwoSided hunique offset (.inl left),
        sourceCorridorSerialInputCutDataAt_portsInRegion realization hcubic
          hrotation htwoSided hunique offset (.inl right),
        hleft, hright, hreachable⟩
  · intro pair left right
    rw [outputData.regionalProfile_strandConnected_eq_true_iff]
    constructor
    · rintro ⟨_hleftMem, _hrightMem, hleft, hright, hreachable⟩
      exact ⟨hleft, hright,
        (sourceCorridorSerialPrefixTrackedReachable_input_iff realization
          hcubic hrotation htwoSided hunique offset color
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 _ _).1 hreachable⟩
    · rintro ⟨hleft, hright, hreachable⟩
      exact ⟨
        sourceCorridorSerialPrefixCutDataAt_portsInRegion realization hcubic
          hrotation htwoSided hunique offset (.inl left),
        sourceCorridorSerialPrefixCutDataAt_portsInRegion realization hcubic
          hrotation htwoSided hunique offset (.inl right),
        hleft, hright,
        (sourceCorridorSerialPrefixTrackedReachable_input_iff realization
          hcubic hrotation htwoSided hunique offset color
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 _ _).2 hreachable⟩
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
    exact sourceCorridorSerialPrefixFaceReachable_input_iff realization
      hcubic hrotation htwoSided hunique offset root left right

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
