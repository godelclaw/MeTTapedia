import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileTerminalForgetting

/-!
# Rail-mediated profile transition of an aligned two-tile slab

The actual source-aligned slab has one six-edge regional profile.  Four of
those edges are the consecutive moving cuts and two are the exterior rails.
After the `4+2` partition, the incoming and outgoing states must therefore be
restrictions of one common terminal-aware profile; they are not obtained by
identifying two ambient crossing-edge maps.

This file names that finite relation and proves that the graph-derived source
slab inhabits it.  Forgetting the two rail terminals gives the corresponding
crossing-only relation.  No identification with a cumulative corridor-prefix
profile, no terminal reconstruction, and no completed splice is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfile
open GoertzelV24CorridorProfileRestriction
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedTerminalProfile
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TerminalProfileRestrictionComposition
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileProfileTransitionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Two endpoint profiles form one aligned-slab transition when both are
restrictions of a common four-moving-port profile with the same fixed
terminal family and face-fragment carrier.

The relation is deliberately relational: a pair may have several common
profiles, and graph realizability is supplied separately at the source use
site below. -/
def AlignedTwoTileCommonProfileRelation
    {terminalCount faceFragmentCount : Nat}
    (input output : CorridorCutProfile 2 terminalCount faceFragmentCount) :
    Prop :=
  ∃ common : CorridorCutProfile 4 terminalCount faceFragmentCount,
    CorridorCutProfile.restrictCrossings common
        sourceTwoTileAlignedFirstTerminalCrossingIndex = input ∧
      CorridorCutProfile.restrictCrossings common
        sourceTwoTileAlignedSecondTerminalCrossingIndex = output

/-- The common-profile relation is a generated finite relation on the
existing profile carrier. -/
noncomputable instance alignedTwoTileCommonProfileRelationDecidable
    (terminalCount faceFragmentCount : Nat) :
    DecidableRel
      (@AlignedTwoTileCommonProfileRelation terminalCount faceFragmentCount) := by
  classical
  intro input output
  unfold AlignedTwoTileCommonProfileRelation
  infer_instance

/-- Both endpoint states retain the same face-identity matrix from their
common slab profile. -/
theorem AlignedTwoTileCommonProfileRelation.faceContinues_eq
    {terminalCount faceFragmentCount : Nat}
    {input output : CorridorCutProfile 2 terminalCount faceFragmentCount}
    (relation : AlignedTwoTileCommonProfileRelation input output) :
    input.faceContinues = output.faceContinues := by
  rcases relation with ⟨common, hinput, houtput⟩
  rw [← hinput, ← houtput]
  rfl

/-- Both endpoint states retain the same capped face-progress coordinate. -/
theorem AlignedTwoTileCommonProfileRelation.faceLengthCap_eq
    {terminalCount faceFragmentCount : Nat}
    {input output : CorridorCutProfile 2 terminalCount faceFragmentCount}
    (relation : AlignedTwoTileCommonProfileRelation input output) :
    input.faceLengthCap = output.faceLengthCap := by
  rcases relation with ⟨common, hinput, houtput⟩
  rw [← hinput, ← houtput]
  rfl

/-- Connectivity between two fixed terminals is unchanged when the moving
crossing block is switched from the incoming to the outgoing interface. -/
theorem AlignedTwoTileCommonProfileRelation.terminalConnected_eq
    {terminalCount faceFragmentCount : Nat}
    {input output : CorridorCutProfile 2 terminalCount faceFragmentCount}
    (relation : AlignedTwoTileCommonProfileRelation input output)
    (pair : TrackedColorPair) (first second : Fin terminalCount) :
    input.strandConnected pair (.inr first) (.inr second) =
      output.strandConnected pair (.inr first) (.inr second) := by
  rcases relation with ⟨common, hinput, houtput⟩
  rw [← hinput, ← houtput]
  rfl

/-- Incidence of a fixed terminal with every regional face fragment is
unchanged across the two moving presentations. -/
theorem AlignedTwoTileCommonProfileRelation.fragmentContainsTerminal_eq
    {terminalCount faceFragmentCount : Nat}
    {input output : CorridorCutProfile 2 terminalCount faceFragmentCount}
    (relation : AlignedTwoTileCommonProfileRelation input output)
    (fragment : Fin faceFragmentCount) (terminal : Fin terminalCount) :
    input.fragmentContainsPort fragment (.inr terminal) =
      output.fragmentContainsPort fragment (.inr terminal) := by
  rcases relation with ⟨common, hinput, houtput⟩
  rw [← hinput, ← houtput]
  rfl

/-- Forgetting a common fixed-terminal family maps a terminal-aware
transition to the corresponding crossing-only transition.  The implication
is one-way: terminal observations are never reconstructed from their
projection. -/
theorem AlignedTwoTileCommonProfileRelation.forgetTerminals
    {terminalCount faceFragmentCount : Nat}
    {input output : CorridorCutProfile 2 terminalCount faceFragmentCount}
    (relation : AlignedTwoTileCommonProfileRelation input output) :
    AlignedTwoTileCommonProfileRelation
      (GoertzelV24GraphDerivedTerminalProfile.forgetTerminals input)
      (GoertzelV24GraphDerivedTerminalProfile.forgetTerminals output) := by
  rcases relation with ⟨common, hinput, houtput⟩
  refine
    ⟨GoertzelV24GraphDerivedTerminalProfile.forgetTerminals common, ?_, ?_⟩
  · rw [← forgetTerminals_restrictCrossings, hinput]
  · rw [← forgetTerminals_restrictCrossings, houtput]

/-- The two terminal-aware graph-derived states of one actual source-aligned
slab are restrictions of its single `4+2` regional profile.  This is the
rail-mediated full-profile transition promised by the source geometry: all
five profile fields travel through one common witness. -/
theorem sourceTwoTileAlignedTerminalRegionalProfiles_commonProfileRelation
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
    (offset : Fin (blockLength - 4))
    (color : G.edgeSet → Color)
    (hcolor : ∀ crossing,
      color ((sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge crossing) ≠ 0) :
    AlignedTwoTileCommonProfileRelation
      ((sourceTwoTileAlignedFirstTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).regionalProfile color
          (fun step => hcolor
            (sourceTwoTileAlignedFirstTerminalCrossingIndex step)))
      ((sourceTwoTileAlignedSecondTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).regionalProfile color
          (fun step => hcolor
            (sourceTwoTileAlignedSecondTerminalCrossingIndex step))) := by
  refine ⟨
    (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic hrotation
      htwoSided hunique offset).regionalProfile color hcolor,
    ?_, ?_⟩
  · exact sourceTwoTileAlignedTerminalProfile_restrict_first realization
      hcubic hrotation htwoSided hunique offset color hcolor
  · exact sourceTwoTileAlignedTerminalProfile_restrict_second realization
      hcubic hrotation htwoSided hunique offset color hcolor

/-- After safely forgetting the two rail observations, the two existing
crossing-only restricted profiles still form a common-profile relation.  The
common crossing-only witness is the forgetful image of the real aligned slab
profile, not an invented equality between adjacent ambient interfaces. -/
theorem sourceTwoTileAlignedRestrictedRegionalProfiles_commonProfileRelation
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
    (offset : Fin (blockLength - 4))
    (color : G.edgeSet → Color)
    (hcolor : ∀ crossing,
      color ((sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).crossingEdge crossing) ≠ 0)
    (hfirst : ∀ crossing,
      color ((sourceTwoTileAlignedFirstRestrictedProfileDataAt realization
        hcubic hrotation htwoSided hunique offset).crossingEdge crossing) ≠ 0)
    (hsecond : ∀ crossing,
      color ((sourceTwoTileAlignedSecondRestrictedProfileDataAt realization
        hcubic hrotation htwoSided hunique offset).crossingEdge crossing) ≠ 0) :
    AlignedTwoTileCommonProfileRelation
      ((sourceTwoTileAlignedFirstRestrictedProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).regionalProfile color hfirst)
      ((sourceTwoTileAlignedSecondRestrictedProfileDataAt realization hcubic
        hrotation htwoSided hunique offset).regionalProfile color hsecond) := by
  have hterminal :=
    sourceTwoTileAlignedTerminalRegionalProfiles_commonProfileRelation
      realization hcubic hrotation htwoSided hunique offset color hcolor
  have hforgotten := hterminal.forgetTerminals
  rw [forgetTerminals_sourceTwoTileAlignedFirstTerminalRegionalProfile
      realization hcubic hrotation htwoSided hunique offset color
      (fun step => hcolor
        (sourceTwoTileAlignedFirstTerminalCrossingIndex step)) hfirst,
    forgetTerminals_sourceTwoTileAlignedSecondTerminalRegionalProfile
      realization hcubic hrotation htwoSided hunique offset color
      (fun step => hcolor
        (sourceTwoTileAlignedSecondTerminalCrossingIndex step)) hsecond]
    at hforgotten
  exact hforgotten

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
