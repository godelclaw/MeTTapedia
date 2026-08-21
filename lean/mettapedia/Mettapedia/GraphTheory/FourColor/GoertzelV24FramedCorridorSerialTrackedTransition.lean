import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixFullProfileRelation

/-!
# A finite tracked-connectivity transition for the literal serial prefix

The route-correct serial prefix need not have only its two displayed input
edges on its true vertex frontier.  Accordingly, a tracked output component
has two honest possibilities: it meets a tracked component represented by an
input profile coordinate, or it is an old-prefix residue invisible at the
displayed input cut.

This file records that dichotomy as finite data.  The visible branch is
reconstructed through the incoming profile's `strandConnected` matrix.  One
additional Boolean matrix records output components which meet no tracked
input coordinate.  Thus no global portal-completeness assertion is smuggled
into the finite letter.  A later exact portal theorem may prove the residual
matrix empty; the transition below is already exact without that theorem.

This is a source-image theorem.  It does not claim that every abstract code is
realized by a literal Cell, compute a reachable closure, or derive `V₀`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open SimpleGraph
open SimpleGraphDartRotation

/-- Finite attachment data for the three tracked colour pairs at a width-two
serial transition.  `usesInput pair output input` means that the output
component reaches the displayed input component.  `hiddenConnected` retains
the exact residual case in which an output component reaches no displayed
input coordinate. -/
structure BoundedSerialTrackedTransitionCode where
  usesInput : TrackedColorPair → Fin 2 → Fin 2 → Bool
  hiddenConnected : TrackedColorPair → Fin 2 → Fin 2 → Bool
  deriving DecidableEq, Fintype

/-- Exact finite tracked-connectivity relation between two width-two serial
profiles.  Output connectivity is either an explicitly retained hidden
component or a connection through the incoming profile. -/
def BoundedSerialTrackedTransition
    (input output : BoundedCorridorCutProfile 2 0 4) : Prop :=
  ∃ code : BoundedSerialTrackedTransitionCode,
    ∀ (pair : TrackedColorPair) (left right : Fin 2),
      (output.profile.strandConnected pair (.inl left) (.inl right) = true) ↔
        IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (output.profile.edgeColor left).toColor ∧
          IsTrackedColor (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2
            (output.profile.edgeColor right).toColor ∧
          (code.hiddenConnected pair left right = true ∨
            ∃ inputLeft inputRight : Fin 2,
              code.usesInput pair left inputLeft = true ∧
                input.profile.strandConnected pair
                    (.inl inputLeft) (.inl inputRight) = true ∧
                code.usesInput pair right inputRight = true)

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialTrackedTransitionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The actual tracked graph after adjoining one literal source Cell. -/
noncomputable def sourceCorridorSerialOutputTrackedGraphAt
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
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    SimpleGraph G.edgeSet :=
  regionalTrackedEdgeGraph embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
      hunique (offset.val + 1)) color
    (trackedColorPairColors pair).1 (trackedColorPairColors pair).2

/-- Whether one actual output component reaches a displayed tracked input
component.  The diagonal input bit is included so an isolated untracked edge
cannot be mistaken for a portal merely by reflexivity of `Reachable`. -/
noncomputable def sourceCorridorSerialTrackedUsesInputAt
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
    (pair : TrackedColorPair) (output input : Fin 2) : Prop :=
  let inputProfile := sourceCorridorSerialInputBoundedProfileAt realization
    hcubic hrotation htwoSided hunique offset color hinputColor
  inputProfile.profile.strandConnected pair (.inl input) (.inl input) = true ∧
    (sourceCorridorSerialOutputTrackedGraphAt realization hcubic hrotation
      htwoSided hunique offset color pair).Reachable
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing output)
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).localLayerPrefixCrossing input)

/-- Finite Boolean form of the visible-input attachment relation. -/
noncomputable def sourceCorridorSerialTrackedUsesInputBoolAt
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
    (pair : TrackedColorPair) (output input : Fin 2) : Bool := by
  classical
  exact decide (sourceCorridorSerialTrackedUsesInputAt realization hcubic
    hrotation htwoSided hunique offset color hinputColor pair output input)

@[simp]
theorem sourceCorridorSerialTrackedUsesInputBoolAt_eq_true_iff
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
    (pair : TrackedColorPair) (output input : Fin 2) :
    sourceCorridorSerialTrackedUsesInputBoolAt realization hcubic hrotation
        htwoSided hunique offset color hinputColor pair output input = true ↔
      sourceCorridorSerialTrackedUsesInputAt realization hcubic hrotation
        htwoSided hunique offset color hinputColor pair output input := by
  simp [sourceCorridorSerialTrackedUsesInputBoolAt]

/-- Extract the exact finite visible/residual split of the three tracked
output relations. -/
noncomputable def sourceCorridorSerialTrackedTransitionCodeAt
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
        hunique offset).localLayerPrefixCrossing step) ≠ 0) :
    BoundedSerialTrackedTransitionCode where
  usesInput pair output input :=
    sourceCorridorSerialTrackedUsesInputBoolAt realization hcubic hrotation
      htwoSided hunique offset color hinputColor pair output input
  hiddenConnected pair left right := by
    classical
    exact decide
      ((sourceCorridorSerialOutputTrackedGraphAt realization hcubic hrotation
          htwoSided hunique offset color pair).Reachable
          ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).nextLocalLayerPrefixCrossing left)
          ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).nextLocalLayerPrefixCrossing right) ∧
        ∀ input : Fin 2,
          ¬ sourceCorridorSerialTrackedUsesInputAt realization hcubic hrotation
            htwoSided hunique offset color hinputColor pair left input)

/-- The two graph-derived profiles around one literal source Cell satisfy the
exact finite visible/residual tracked transition. -/
theorem sourceCorridorSerialBoundedProfiles_trackedTransition
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
    BoundedSerialTrackedTransition
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique offset color hinputColor)
      (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic hrotation
        htwoSided hunique offset color houtputColor) := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let interface := sourceSlabInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let input := sourceCorridorSerialInputBoundedProfileAt realization hcubic
    hrotation htwoSided hunique offset color hinputColor
  let output := sourceCorridorSerialPrefixBoundedProfileAt realization hcubic
    hrotation htwoSided hunique offset color houtputColor
  let outputGraph := sourceCorridorSerialOutputTrackedGraphAt realization
    hcubic hrotation htwoSided hunique offset color
  let code := sourceCorridorSerialTrackedTransitionCodeAt realization hcubic
    hrotation htwoSided hunique offset color hinputColor
  have hfull := sourceCorridorSerialPrefixFullProfileRelation realization
    hcubic hrotation htwoSided hunique offset color hinputColor houtputColor
  have houtputEdgeColor : ∀ step : Fin 2,
      (output.profile.edgeColor step).toColor =
        color (interface.nextLocalLayerPrefixCrossing step) := by
    intro step
    simp [output, sourceCorridorSerialPrefixBoundedProfileAt,
      regionalBoundaryBoundedProfile, regionalBoundaryGraphCutData,
      GoertzelV24GraphDerivedCorridorCutProfile.GraphCorridorCutData.regionalProfile,
      interface]
  change BoundedSerialTrackedTransition input output
  refine ⟨code, ?_⟩
  intro pair left right
  constructor
  · intro hconnected
    rcases (hfull.outputStrandConnected pair left right).1 hconnected with
      ⟨hleftTracked, hrightTracked, hthree⟩
    have hreachable :
        (outputGraph pair).Reachable
          (interface.nextLocalLayerPrefixCrossing left)
          (interface.nextLocalLayerPrefixCrossing right) := by
      exact (sourceCorridorSerialPrefixTrackedReachable_input_iff realization
        hcubic hrotation htwoSided hunique offset color
        (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
        (interface.nextLocalLayerPrefixCrossing left)
        (interface.nextLocalLayerPrefixCrossing right)).2 hthree
    refine ⟨?_, ?_, ?_⟩
    · rw [houtputEdgeColor left]
      exact hleftTracked
    · rw [houtputEdgeColor right]
      exact hrightTracked
    · by_cases hvisible : ∃ inputPort : Fin 2,
          sourceCorridorSerialTrackedUsesInputAt realization hcubic hrotation
            htwoSided hunique offset color hinputColor pair left inputPort
      · rcases hvisible with ⟨inputPort, huses⟩
        refine Or.inr ⟨inputPort, inputPort, ?_, huses.1, ?_⟩
        · exact
            (sourceCorridorSerialTrackedUsesInputBoolAt_eq_true_iff
              realization hcubic hrotation htwoSided hunique offset color
              hinputColor pair left inputPort).2 huses
        · apply
            (sourceCorridorSerialTrackedUsesInputBoolAt_eq_true_iff
              realization hcubic hrotation htwoSided hunique offset color
              hinputColor pair right inputPort).2
          exact ⟨huses.1, hreachable.symm.trans huses.2⟩
      · apply Or.inl
        change decide (_ ∧ ∀ inputPort : Fin 2, ¬
          sourceCorridorSerialTrackedUsesInputAt realization hcubic hrotation
            htwoSided hunique offset color hinputColor pair left inputPort) =
          true
        apply decide_eq_true
        refine ⟨?_, ?_⟩
        · simpa [outputGraph, interface] using hreachable
        · intro inputPort huses
          exact hvisible ⟨inputPort, huses⟩
  · rintro ⟨hleftTracked, hrightTracked, hhidden | hvisible⟩
    · have hhidden' :
          (outputGraph pair).Reachable
            (interface.nextLocalLayerPrefixCrossing left)
            (interface.nextLocalLayerPrefixCrossing right) ∧
          ∀ inputPort : Fin 2,
            ¬ sourceCorridorSerialTrackedUsesInputAt realization hcubic
              hrotation htwoSided hunique offset color hinputColor pair left
              inputPort := by
        have hraw := of_decide_eq_true hhidden
        simpa [code, sourceCorridorSerialTrackedTransitionCodeAt,
          outputGraph, interface] using hraw
      apply (hfull.outputStrandConnected pair left right).2
      refine ⟨?_, ?_, ?_⟩
      · rw [← houtputEdgeColor left]
        exact hleftTracked
      · rw [← houtputEdgeColor right]
        exact hrightTracked
      · exact
          (sourceCorridorSerialPrefixTrackedReachable_input_iff realization
            hcubic hrotation htwoSided hunique offset color
            (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
            (interface.nextLocalLayerPrefixCrossing left)
            (interface.nextLocalLayerPrefixCrossing right)).1 hhidden'.1
    · rcases hvisible with
        ⟨inputLeft, inputRight, husesLeft, hinputConnected, husesRight⟩
      have husesLeft' :=
        (sourceCorridorSerialTrackedUsesInputBoolAt_eq_true_iff realization
          hcubic hrotation htwoSided hunique offset color hinputColor pair left
          inputLeft).1 husesLeft
      have husesRight' :=
        (sourceCorridorSerialTrackedUsesInputBoolAt_eq_true_iff realization
          hcubic hrotation htwoSided hunique offset color hinputColor pair right
          inputRight).1 husesRight
      rcases (hfull.inputStrandConnected pair inputLeft inputRight).1
          hinputConnected with
        ⟨_hinputLeftTracked, _hinputRightTracked, hinputReachable⟩
      have hregion :
          sourceCorridorSerialCutRegionAt realization hcubic hrotation
              htwoSided hunique offset ⊆
            sourceCorridorSerialPrefixRegion realization hcubic hrotation
              htwoSided hunique (offset.val + 1) := by
        intro edge hedge
        rw [← sourceCorridorSerialCutRegionAt_union_cell realization hcubic
          hrotation htwoSided hunique offset]
        exact Finset.mem_union_left _ hedge
      have hinputReachable' :
          (outputGraph pair).Reachable
            (interface.localLayerPrefixCrossing inputLeft)
            (interface.localLayerPrefixCrossing inputRight) := by
        exact hinputReachable.mono
          (regionalTrackedEdgeGraph_mono RS color
            (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
            hregion)
      have hreachable :
          (outputGraph pair).Reachable
            (interface.nextLocalLayerPrefixCrossing left)
            (interface.nextLocalLayerPrefixCrossing right) :=
        husesLeft'.2.trans (hinputReachable'.trans husesRight'.2.symm)
      apply (hfull.outputStrandConnected pair left right).2
      refine ⟨?_, ?_, ?_⟩
      · rw [← houtputEdgeColor left]
        exact hleftTracked
      · rw [← houtputEdgeColor right]
        exact hrightTracked
      · exact
          (sourceCorridorSerialPrefixTrackedReachable_input_iff realization
            hcubic hrotation htwoSided hunique offset color
            (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
            (interface.nextLocalLayerPrefixCrossing left)
            (interface.nextLocalLayerPrefixCrossing right)).1 hreachable

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
