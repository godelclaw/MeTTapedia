import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementProfileBoundaryWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorLocalSourceSplice

/-!
# `Count` support of the literal source Cell-3 region

A source Cell-3 layer pair cuts the ambient map into an outer retained side
and a complementary removed side.  The small corridor generator is the
*complementary* region between the two layers.  The retained side belongs to
the eventual shortened-map splice and must not be serially multiplied as if
it were a corridor cell.

This file states L2 on the already-computed full-profile `Count` matrix of
that literal complementary region.  A stay transition is positivity of a
diagonal full-profile entry.  Thus boundary colors, tracked connectivity, and
capped face progress all agree; equality of boundary color words alone is not
silently promoted to equality of source profiles.

The remaining source calculation is deliberately visible as
`localLayerPairCellSupportsProfileIdentityOn`: the relevant profiles must be
identified from the source formation and its finite stay-transition check.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24AnnularCrosscut
open GoertzelV24CorridorPumping
open GoertzelV24CorridorTransferMatrix
open GoertzelV24EarlyFalsifiers
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorLocalCountSupportEdgeSetDecidableEq :
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

/-- The finite full-profile carrier on either boundary of the literal
complementary Cell-3 region. -/
abbrev LocalLayerPairCellProfile
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic) :=
  interface.separatedLocalLayerPair.SourceCrosscutComplementInterfaceProfile
    embedded.cellulation.rotation
    (interface.localLayerPairSourceCrosscutBoundaryData hcubic)

/-- L2 in its source-faithful form for one literal Cell-3 region: every
relevant full profile has a positive diagonal entry in the removed-side
`Count` matrix. -/
def localLayerPairCellSupportsProfileIdentityOn
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (Relevant : LocalLayerPairCellProfile interface hcubic → Prop) : Prop :=
  ∀ profile, Relevant profile →
    0 < interface.separatedLocalLayerPair.sourceCrosscutComplementLiteralOpenProfileCount
      embedded.cellulation.rotation
      (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic
      profile profile

/-- The one-cell transfer relation is the support of the literal
complementary Cell-3 `Count` matrix.  This is the full source profile, not
only its boundary-color coordinate. -/
def localLayerPairCellProfileTransfer
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (leftProfile rightProfile : LocalLayerPairCellProfile interface hcubic) :
    Prop :=
  0 < (interface.separatedLocalLayerPair
    |>.sourceCrosscutComplementLiteralOpenProfileCount
      embedded.cellulation.rotation
      (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic
      leftProfile rightProfile)

/-- A one-cell transfer is exactly a literal Tait coloring of the removed
Cell-3 region realizing the named full profiles.  This gives the abstract
transfer relation its concrete open-tangle semantics. -/
theorem localLayerPairCellProfileTransfer_iff_exists_coloring
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (leftProfile rightProfile : LocalLayerPairCellProfile interface hcubic) :
    interface.localLayerPairCellProfileTransfer hcubic
        leftProfile rightProfile ↔
      ∃ coloring : interface.separatedLocalLayerPair
          |>.SourceCrosscutComplementLiteralOpenTaitColoring
            embedded.cellulation.rotation
            (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic,
        (interface.separatedLocalLayerPair
            |>.sourceCrosscutComplementLiteralOpenLeftProfile
              embedded.cellulation.rotation
              (interface.localLayerPairSourceCrosscutBoundaryData hcubic)
              hcubic coloring.1 coloring.2) = leftProfile ∧
          (interface.separatedLocalLayerPair
            |>.sourceCrosscutComplementLiteralOpenRightProfile
              embedded.cellulation.rotation
              (interface.localLayerPairSourceCrosscutBoundaryData hcubic)
              hcubic coloring.1 coloring.2) = rightProfile := by
  exact interface.separatedLocalLayerPair
    |>.sourceCrosscutComplementLiteralOpenProfileCount_pos_iff
      embedded.cellulation.rotation
      (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic
      leftProfile rightProfile

/-- Positive powers of the literal Cell-3 `Count` matrix are exactly paths
in its supported full-profile transfer relation.  The existing generic
composition, repetition, and periodic-padding theorems therefore apply to
the concrete source generator without a parallel pumping definition. -/
theorem localLayerPairCell_transferCount_pos_iff_exactRelationalTransfer
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (length : Nat)
    (startProfile finishProfile : LocalLayerPairCellProfile interface hcubic) :
    0 < transferCount
        (interface.separatedLocalLayerPair
          |>.sourceCrosscutComplementLiteralOpenProfileCount
            embedded.cellulation.rotation
            (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic)
        length startProfile finishProfile ↔
      ExactRelationalTransfer
        (interface.localLayerPairCellProfileTransfer hcubic)
        length startProfile finishProfile := by
  change 0 < transferCount
      (interface.separatedLocalLayerPair
        |>.sourceCrosscutComplementLiteralOpenProfileCount
          embedded.cellulation.rotation
          (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic)
      length startProfile finishProfile ↔
    ExactRelationalTransfer
      (fun leftProfile rightProfile =>
        0 < (interface.separatedLocalLayerPair
          |>.sourceCrosscutComplementLiteralOpenProfileCount
            embedded.cellulation.rotation
            (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic
            leftProfile rightProfile))
      length startProfile finishProfile
  exact transferCount_pos_iff_exactRelationalTransfer
    (interface.separatedLocalLayerPair
      |>.sourceCrosscutComplementLiteralOpenProfileCount
        embedded.cellulation.rotation
        (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic)
    length startProfile finishProfile

/-- The playbook's weak L2 conclusion for the literal full-profile transfer,
conditional only on the source audit that every relevant profile has a
relevant successor.  Eventual positive-period return and congruence-correct
padding are inherited from the finite transfer engine. -/
theorem localLayerPairCell_periodicPumping_of_serial
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (Relevant : LocalLayerPairCellProfile interface hcubic → Prop)
    (hserial : LiveTransferIsSerial Relevant
      (interface.localLayerPairCellProfileTransfer hcubic)) :
    PeriodicCorridorPumpingWithCongruence Relevant
      (ExactRelationalTransfer
        (interface.localLayerPairCellProfileTransfer hcubic)) :=
  finiteSerialTransfer_periodicCorridorPumpingWithCongruence
    Relevant (interface.localLayerPairCellProfileTransfer hcubic) hserial

/-- The source's stronger one-cell L2 audit implies the weak serial premise:
the profile itself is a relevant successor.  Keeping this implication named
lets a per-corridor-type stay audit and the periodic fallback share the same
finite transfer engine. -/
theorem localLayerPairCell_liveTransferIsSerial_of_profileIdentityOn
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (Relevant : LocalLayerPairCellProfile interface hcubic → Prop)
    (hstay : interface.localLayerPairCellSupportsProfileIdentityOn
      hcubic Relevant) :
    LiveTransferIsSerial Relevant
      (interface.localLayerPairCellProfileTransfer hcubic) := by
  intro profile hrelevant
  exact ⟨profile, hrelevant, hstay profile hrelevant⟩

/-- A successful finite stay-transition audit therefore inherits the
congruence-correct periodic pumping theorem without a second recurrence
construction. -/
theorem localLayerPairCell_periodicPumping_of_profileIdentityOn
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (Relevant : LocalLayerPairCellProfile interface hcubic → Prop)
    (hstay : interface.localLayerPairCellSupportsProfileIdentityOn
      hcubic Relevant) :
    PeriodicCorridorPumpingWithCongruence Relevant
      (ExactRelationalTransfer
        (interface.localLayerPairCellProfileTransfer hcubic)) :=
  interface.localLayerPairCell_periodicPumping_of_serial hcubic Relevant
    (interface.localLayerPairCell_liveTransferIsSerial_of_profileIdentityOn
      hcubic Relevant hstay)

/-- A positive diagonal full-profile entry yields a positive two-boundary
color-word entry for the same literal complementary Cell-3 region. -/
theorem localLayerPairCell_boundaryCount_pos_of_profileIdentity
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (profile : LocalLayerPairCellProfile interface hcubic)
    (hidentity :
      0 < interface.separatedLocalLayerPair.sourceCrosscutComplementLiteralOpenProfileCount
        embedded.cellulation.rotation
        (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic
        profile profile) :
    0 < interface.separatedLocalLayerPair.sourceCrosscutComplementBoundaryColorCount
      embedded.cellulation.rotation
      (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic
      (interface.separatedLocalLayerPair
        |>.sourceCrosscutComplementInterfaceProfileLeftColorWord
          embedded.cellulation.rotation
          (interface.localLayerPairSourceCrosscutBoundaryData hcubic) profile)
      (interface.separatedLocalLayerPair
        |>.sourceCrosscutComplementInterfaceProfileRightColorWord
          embedded.cellulation.rotation
          (interface.localLayerPairSourceCrosscutBoundaryData hcubic) profile) := by
  apply (interface.separatedLocalLayerPair
    |>.sourceCrosscutComplementBoundaryColorCount_pos_iff_exists_profilePair
      embedded.cellulation.rotation
      (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic _ _).2
  exact ⟨profile, profile, rfl, rfl, hidentity⟩

/-- The right color coordinate of one full profile is the source-width
transport of its left color coordinate. -/
theorem localLayerPairCell_profileRightColorWord_eq_cast_left
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (profile : LocalLayerPairCellProfile interface hcubic) :
    (interface.separatedLocalLayerPair
        |>.sourceCrosscutComplementInterfaceProfileRightColorWord
          embedded.cellulation.rotation
          (interface.localLayerPairSourceCrosscutBoundaryData hcubic) profile) =
      fun step =>
        interface.separatedLocalLayerPair
          |>.sourceCrosscutComplementInterfaceProfileLeftColorWord
            embedded.cellulation.rotation
            (interface.localLayerPairSourceCrosscutBoundaryData hcubic) profile
            (Fin.cast interface.separatedLocalLayerPair.length_eq.symm step) := by
  rfl

/-- A positive diagonal full-profile entry is therefore a genuine stay
transition in the one-word seam support used by the gluing theorem. -/
theorem localLayerPairCell_seamCount_pos_of_profileIdentity
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (profile : LocalLayerPairCellProfile interface hcubic)
    (hidentity :
      0 < interface.separatedLocalLayerPair.sourceCrosscutComplementLiteralOpenProfileCount
        embedded.cellulation.rotation
        (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic
        profile profile) :
    0 < interface.separatedLocalLayerPair.sourceCrosscutComplementSeamColorCount
      embedded.cellulation.rotation
      (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic
      (interface.separatedLocalLayerPair
        |>.sourceCrosscutComplementInterfaceProfileLeftColorWord
          embedded.cellulation.rotation
          (interface.localLayerPairSourceCrosscutBoundaryData hcubic) profile) := by
  rw [interface.separatedLocalLayerPair
    |>.sourceCrosscutComplementSeamColorCount_eq_boundaryColorCount_diagonal]
  simpa [interface.localLayerPairCell_profileRightColorWord_eq_cast_left
      hcubic profile] using
    interface.localLayerPairCell_boundaryCount_pos_of_profileIdentity hcubic
      profile hidentity

/-- The relevance-restricted L2 hypothesis discharges every relevant
profile's literal seam stay transition. -/
theorem localLayerPairCell_seamCount_pos_of_relevantProfile
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (Relevant : LocalLayerPairCellProfile interface hcubic → Prop)
    (hstay : interface.localLayerPairCellSupportsProfileIdentityOn hcubic Relevant)
    (profile : LocalLayerPairCellProfile interface hcubic)
    (hrelevant : Relevant profile) :
    0 < interface.separatedLocalLayerPair.sourceCrosscutComplementSeamColorCount
      embedded.cellulation.rotation
      (interface.localLayerPairSourceCrosscutBoundaryData hcubic) hcubic
      (interface.separatedLocalLayerPair
        |>.sourceCrosscutComplementInterfaceProfileLeftColorWord
          embedded.cellulation.rotation
          (interface.localLayerPairSourceCrosscutBoundaryData hcubic) profile) :=
  interface.localLayerPairCell_seamCount_pos_of_profileIdentity hcubic profile
    (hstay profile hrelevant)

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
