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
