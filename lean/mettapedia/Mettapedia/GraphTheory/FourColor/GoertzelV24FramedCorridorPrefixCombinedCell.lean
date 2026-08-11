import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementCombinedConnectivity
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementProfileBoundaryWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixFullProfileRelation
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalSourceSplice

/-!
# The literal combined Cell on cumulative source coordinates

The literal removed Cell carries one combined profile on four source-ordered
crossings.  The cumulative corridor state exposes two crossings before the
Cell and two after it.  This file records the exact embeddings of those two
moving cuts into the combined carrier.

Only source-coordinate alignment is established here.  In particular, the
literal removed region is not identified with the complete boundary of the
next hexagonal face; connectivity and face progress cross that boundary by
separate relational theorems.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24CorridorProfile
open GoertzelV24CorridorProfileRestriction
open GoertzelV24CorridorProfileSerialConnectivity
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationVertexCutProfile
open GoertzelV24WindingClassification
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixCombinedCellEdgeSetDecidableEq :
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

/-- The exact combined four-port profile carrier of the literal removed Cell
selected by one source-local layer pair. -/
abbrev LocalLayerPairCellCombinedProfile
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic) :=
  interface.separatedLocalLayerPair.SourceCrosscutComplementCombinedProfile
    embedded.cellulation.rotation
    (interface.localLayerPairSourceCrosscutBoundaryData hcubic)

/-- Embed the moving two-port cut before the Cell into the left block of the
combined four-port carrier. -/
noncomputable def localLayerPairCellLeftCombinedIndex
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic) :
    Fin 2 → Fin (Fintype.card (VertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem
      (interface.separatedLocalLayerPair.componentSide
        (interface.localLayerPairSourceCrosscutBoundaryData hcubic).component)ᶜ)) :=
  fun step =>
    interface.separatedLocalLayerPair.sourceCrosscutComplementLeftCombinedIndex
      embedded.cellulation.rotation
      (interface.localLayerPairSourceCrosscutBoundaryData hcubic)
      (Fin.cast interface.localLayer_walk_length_eq_two.symm step)

/-- Embed the moving two-port cut after the Cell into the aligned right block
of the same combined carrier. -/
noncomputable def localLayerPairCellRightCombinedIndex
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic) :
    Fin 2 → Fin (Fintype.card (VertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem
      (interface.separatedLocalLayerPair.componentSide
        (interface.localLayerPairSourceCrosscutBoundaryData hcubic).component)ᶜ)) :=
  fun step =>
    interface.separatedLocalLayerPair.sourceCrosscutComplementRightCombinedIndex
      embedded.cellulation.rotation
      (interface.localLayerPairSourceCrosscutBoundaryData hcubic)
      (Fin.cast interface.localLayer_walk_length_eq_two.symm step)

/-- The left embedding names exactly the two incoming cumulative-prefix cut
edges, not merely an equipotent boundary carrier. -/
@[simp]
theorem localLayerPairCellCombinedData_crossingEdge_left
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (step : Fin 2) :
    (interface.separatedLocalLayerPair
        |>.sourceCrosscutComplementBoundaryProfileData
          embedded.cellulation.rotation
          (interface.localLayerPairSourceCrosscutBoundaryData hcubic)
        |>.crossingEdge
          (interface.localLayerPairCellLeftCombinedIndex hcubic step)) =
      interface.localLayerPrefixCrossing step := by
  unfold localLayerPairCellLeftCombinedIndex localLayerPrefixCrossing
  rw [interface.separatedLocalLayerPair
    |>.sourceCrosscutComplementBoundaryProfileData_crossingEdge_left]
  rfl

/-- The right embedding names exactly the two newly exposed cumulative-prefix
cut edges. -/
@[simp]
theorem localLayerPairCellCombinedData_crossingEdge_right
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (step : Fin 2) :
    (interface.separatedLocalLayerPair
        |>.sourceCrosscutComplementBoundaryProfileData
          embedded.cellulation.rotation
          (interface.localLayerPairSourceCrosscutBoundaryData hcubic)
        |>.crossingEdge
          (interface.localLayerPairCellRightCombinedIndex hcubic step)) =
      interface.nextLocalLayerPrefixCrossing step := by
  unfold localLayerPairCellRightCombinedIndex nextLocalLayerPrefixCrossing
  rw [interface.separatedLocalLayerPair
    |>.sourceCrosscutComplementBoundaryProfileData_crossingEdge_right]
  rfl

/-- Restrict one ambient Tait coloring to the literal removed Cell and read
its complete combined four-port profile. -/
noncomputable def localLayerPairInheritedComplementCombinedProfile
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring
      Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring coloring) :
    interface.LocalLayerPairCellCombinedProfile hcubic :=
  let pair := interface.separatedLocalLayerPair
  let boundary := interface.localLayerPairSourceCrosscutBoundaryData hcubic
  let openColoring := pair.sourceCrosscutInheritedComplementOpenColoring
    embedded.cellulation.rotation boundary hcubic coloring
  pair.sourceCrosscutComplementLiteralOpenProfile
    embedded.cellulation.rotation boundary hcubic openColoring
    (pair.sourceCrosscutInheritedComplementOpenColoring_isTait
      embedded.cellulation.rotation boundary hcubic coloring hcoloring)

/-- The inherited combined state is realizable by construction; no finite
profile is postulated independently of its literal open coloring. -/
theorem localLayerPairInheritedComplementCombinedProfile_realizable
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring
      Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring coloring) :
    interface.separatedLocalLayerPair
      |>.SourceCrosscutComplementCombinedProfileRealizable
        embedded.cellulation.rotation
        (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic
        (interface.localLayerPairInheritedComplementCombinedProfile hcubic
          coloring hcoloring) := by
  let pair := interface.separatedLocalLayerPair
  let boundary := interface.localLayerPairSourceCrosscutBoundaryData hcubic
  let openColoring := pair.sourceCrosscutInheritedComplementOpenColoring
    embedded.cellulation.rotation boundary hcubic coloring
  let hopen := pair.sourceCrosscutInheritedComplementOpenColoring_isTait
    embedded.cellulation.rotation boundary hcubic coloring hcoloring
  exact ⟨⟨openColoring, hopen⟩, rfl⟩

/-- The left block of the inherited combined state carries exactly the
ambient colors of the incoming cumulative-prefix crossings. -/
theorem localLayerPairInheritedComplementCombinedProfile_edgeColor_left
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring
      Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring coloring)
    (step : Fin 2) :
    ((interface.localLayerPairInheritedComplementCombinedProfile hcubic
        coloring hcoloring).edgeColor
          (interface.localLayerPairCellLeftCombinedIndex hcubic step)).toColor =
      coloring (interface.localLayerPrefixCrossing step) := by
  let pair := interface.separatedLocalLayerPair
  let boundary := interface.localLayerPairSourceCrosscutBoundaryData hcubic
  let cutStep : Fin interface.localLayer.walk.length :=
    Fin.cast interface.localLayer_walk_length_eq_two.symm step
  let openColoring := pair.sourceCrosscutInheritedComplementOpenColoring
    embedded.cellulation.rotation boundary hcubic coloring
  let hopen := pair.sourceCrosscutInheritedComplementOpenColoring_isTait
    embedded.cellulation.rotation boundary hcubic coloring hcoloring
  let combined := pair.sourceCrosscutComplementLiteralOpenProfile
    embedded.cellulation.rotation boundary hcubic openColoring hopen
  have hrestrict := pair.sourceCrosscutComplementLiteralOpenProfile_restrict_left
    embedded.cellulation.rotation boundary hcubic openColoring hopen
  have hselected := congrArg
    (fun profile => (profile.edgeColor cutStep).toColor) hrestrict
  calc
    ((interface.localLayerPairInheritedComplementCombinedProfile hcubic
        coloring hcoloring).edgeColor
          (interface.localLayerPairCellLeftCombinedIndex hcubic step)).toColor =
        ((pair.sourceCrosscutComplementLiteralOpenLeftProfile
          embedded.cellulation.rotation boundary hcubic openColoring hopen
          ).edgeColor cutStep).toColor := by
      change (combined.edgeColor
          (pair.sourceCrosscutComplementLeftCombinedIndex
            embedded.cellulation.rotation boundary cutStep)).toColor = _
      exact hselected
    _ = pair.sourceCrosscutComplementLeftBoundaryWord
          embedded.cellulation.rotation boundary hcubic openColoring cutStep :=
      pair.sourceCrosscutComplementLiteralOpenLeftProfile_edgeColor_eq_boundaryWord
        embedded.cellulation.rotation boundary hcubic openColoring hopen cutStep
    _ = pair.sourceCrosscutOutsideBoundaryWord embedded.cellulation.rotation
          boundary hcubic openColoring (.inl cutStep) := rfl
    _ = coloring (embedded.cellulation.rotation.toRotationSystem.edgeOf
          (pair.sourceCrosscutBoundaryDartAt embedded.cellulation.rotation
            boundary (.inl cutStep)).1.1) :=
      pair.sourceCrosscutInheritedComplement_outsideBoundaryWord_eq_ambient
        embedded.cellulation.rotation boundary hcubic coloring (.inl cutStep)
    _ = coloring (interface.localLayerPrefixCrossing step) := by
      rw [pair.sourceCrosscutBoundaryDartAt_edgeOf
        embedded.cellulation.rotation boundary (.inl cutStep)]
      rfl

/-- The aligned right block likewise carries exactly the ambient colors of
the outgoing cumulative-prefix crossings. -/
theorem localLayerPairInheritedComplementCombinedProfile_edgeColor_right
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring
      Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring coloring)
    (step : Fin 2) :
    ((interface.localLayerPairInheritedComplementCombinedProfile hcubic
        coloring hcoloring).edgeColor
          (interface.localLayerPairCellRightCombinedIndex hcubic step)).toColor =
      coloring (interface.nextLocalLayerPrefixCrossing step) := by
  let pair := interface.separatedLocalLayerPair
  let boundary := interface.localLayerPairSourceCrosscutBoundaryData hcubic
  let cutStep : Fin interface.localLayer.walk.length :=
    Fin.cast interface.localLayer_walk_length_eq_two.symm step
  let rightStep : Fin pair.right.walk.length := Fin.cast pair.length_eq cutStep
  let openColoring := pair.sourceCrosscutInheritedComplementOpenColoring
    embedded.cellulation.rotation boundary hcubic coloring
  let hopen := pair.sourceCrosscutInheritedComplementOpenColoring_isTait
    embedded.cellulation.rotation boundary hcubic coloring hcoloring
  let combined := pair.sourceCrosscutComplementLiteralOpenProfile
    embedded.cellulation.rotation boundary hcubic openColoring hopen
  have hrestrict := pair.sourceCrosscutComplementLiteralOpenProfile_restrict_right
    embedded.cellulation.rotation boundary hcubic openColoring hopen
  have hselected := congrArg
    (fun profile => (profile.edgeColor cutStep).toColor) hrestrict
  calc
    ((interface.localLayerPairInheritedComplementCombinedProfile hcubic
        coloring hcoloring).edgeColor
          (interface.localLayerPairCellRightCombinedIndex hcubic step)).toColor =
        ((pair.sourceCrosscutComplementLiteralOpenRightProfile
          embedded.cellulation.rotation boundary hcubic openColoring hopen
          ).edgeColor cutStep).toColor := by
      change (combined.edgeColor
          (pair.sourceCrosscutComplementRightCombinedIndex
            embedded.cellulation.rotation boundary cutStep)).toColor = _
      exact hselected
    _ = pair.sourceCrosscutComplementRightBoundaryWord
          embedded.cellulation.rotation boundary hcubic openColoring rightStep :=
      pair.sourceCrosscutComplementLiteralOpenRightProfile_edgeColor_eq_boundaryWord
        embedded.cellulation.rotation boundary hcubic openColoring hopen cutStep
    _ = pair.sourceCrosscutOutsideBoundaryWord embedded.cellulation.rotation
          boundary hcubic openColoring (.inr rightStep) := rfl
    _ = coloring (embedded.cellulation.rotation.toRotationSystem.edgeOf
          (pair.sourceCrosscutBoundaryDartAt embedded.cellulation.rotation
            boundary (.inr rightStep)).1.1) :=
      pair.sourceCrosscutInheritedComplement_outsideBoundaryWord_eq_ambient
        embedded.cellulation.rotation boundary hcubic coloring (.inr rightStep)
    _ = coloring (interface.nextLocalLayerPrefixCrossing step) := by
      rw [pair.sourceCrosscutBoundaryDartAt_edgeOf
        embedded.cellulation.rotation boundary (.inr rightStep)]
      rfl

/-- The cumulative input profile and the literal combined Cell agree on the
two colors at their common left interface.  This is only the color coordinate
of the serial profile law; tracked connectivity is kept as a separate
obligation below. -/
theorem localLayerLeftPrefixProfile_edgeColor_eq_combinedCell
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring
      Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring coloring)
    (hleftColor : ∀ step,
      coloring (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (step : Fin 2) :
    (aligned.toInterface.localLayerLeftPrefixBoundedProfile coloring
        hleftColor).profile.edgeColor step =
      (aligned.toInterface.localLayerPairInheritedComplementCombinedProfile
          hcubic coloring hcoloring).edgeColor
        (aligned.toInterface.localLayerPairCellLeftCombinedIndex hcubic
          step) := by
  apply StrandColor.toColor_injective
  rw [aligned.localLayerLeftPrefixBoundedProfile_edgeColor_toColor,
    aligned.toInterface
      |>.localLayerPairInheritedComplementCombinedProfile_edgeColor_left]

/-- The cumulative output profile and the same combined Cell agree on the
two colors at their common right interface. -/
theorem localLayerRightPrefixProfile_edgeColor_eq_combinedCell
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring
      Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring coloring)
    (hrightColor : ∀ step,
      coloring (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0)
    (step : Fin 2) :
    (aligned.toInterface.localLayerRightPrefixBoundedProfile coloring
        hrightColor).profile.edgeColor step =
      (aligned.toInterface.localLayerPairInheritedComplementCombinedProfile
          hcubic coloring hcoloring).edgeColor
        (aligned.toInterface.localLayerPairCellRightCombinedIndex hcubic
          step) := by
  apply StrandColor.toColor_injective
  rw [aligned.localLayerRightPrefixBoundedProfile_edgeColor_toColor,
    aligned.toInterface
      |>.localLayerPairInheritedComplementCombinedProfile_edgeColor_right]

/-- The one remaining connectivity coordinate needed to identify the actual
cumulative-prefix update with finite serial profile composition.  Naming this
law prevents the already-proved color equalities from being mistaken for the
full connectivity transfer. -/
def LocalLayerPrefixCombinedStrandLaw
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring
      Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring coloring)
    (hleftColor : ∀ step,
      coloring (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (hrightColor : ∀ step,
      coloring (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0) :
    Prop :=
  ∀ (pair : TrackedColorPair) (first second : Fin 2),
    ((aligned.toInterface.localLayerRightPrefixBoundedProfile coloring
        hrightColor).profile.strandConnected pair (.inl first)
          (.inl second) = true) ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          ((aligned.toInterface.localLayerRightPrefixBoundedProfile coloring
            hrightColor).profile.edgeColor first).toColor ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          ((aligned.toInterface.localLayerRightPrefixBoundedProfile coloring
            hrightColor).profile.edgeColor second).toColor ∧
        Relation.ReflTransGen
          (serialProfileConnectivityStep
            (aligned.toInterface.localLayerLeftPrefixBoundedProfile coloring
              hleftColor).profile
            (aligned.toInterface
              |>.localLayerPairInheritedComplementCombinedProfile hcubic
                coloring hcoloring)
            (aligned.toInterface.localLayerPairCellLeftCombinedIndex hcubic)
            pair)
          (aligned.toInterface.localLayerPairCellRightCombinedIndex hcubic
            first)
          (aligned.toInterface.localLayerPairCellRightCombinedIndex hcubic
            second)

/-- Once the named strand law is proved, the actual two cumulative profiles
and the realizable combined Cell satisfy the complete finite connectivity
structure.  No geometric premise is hidden in this packaging theorem. -/
theorem localLayerPrefixCombinedSerialConnectivity_of_strandLaw
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring
      Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring coloring)
    (hleftColor : ∀ step,
      coloring (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (hrightColor : ∀ step,
      coloring (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0)
    (hstrand : LocalLayerPrefixCombinedStrandLaw aligned hcubic coloring
      hcoloring hleftColor hrightColor) :
    SerialProfileConnectivity
      (aligned.toInterface.localLayerLeftPrefixBoundedProfile coloring
        hleftColor).profile
      (aligned.toInterface.localLayerPairInheritedComplementCombinedProfile
        hcubic coloring hcoloring)
      (aligned.toInterface.localLayerRightPrefixBoundedProfile coloring
        hrightColor).profile
      (aligned.toInterface.localLayerPairCellLeftCombinedIndex hcubic)
      (aligned.toInterface.localLayerPairCellRightCombinedIndex hcubic) := by
  refine {
    leftColors := ?_
    rightColors := ?_
    strandConnected := hstrand }
  · exact localLayerLeftPrefixProfile_edgeColor_eq_combinedCell aligned
      hcubic coloring hcoloring hleftColor
  · exact localLayerRightPrefixProfile_edgeColor_eq_combinedCell aligned
      hcubic coloring hcoloring hrightColor

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
