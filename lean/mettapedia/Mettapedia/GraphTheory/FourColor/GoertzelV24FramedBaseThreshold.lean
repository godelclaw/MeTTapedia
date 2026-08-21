import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedBoundaryCleanCorridor
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorThreeFacePrefixProfileRepeat

/-!
# An explicit framed threshold for a separated profile repeat

Addenda XXIV--XXV bound the finite base by composing two effective numbers:
the length needed to repeat a corridor profile and the face count needed to
force a clean corridor of that length.  This module performs that numerical
composition for the source-layer profile already used by the annular splice
layer, using the proved three-face bound on its literal two-edge cut.

The result is deliberately conditional on a proposed bound for the number of
interior pentagons.  Spherical curvature alone does not supply the manuscript's
claimed bound of twelve when faces longer than six are allowed: the exact
identity is pentagons equals twelve plus negative-curvature weight.  Thus the
theorems below are an effective threshold interface, not a completed `V₀` and
not a `BaseVerified` construction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedBaseThreshold

open GoertzelV24ClosedWebProfileFiniteness
open GoertzelV24CleanHexCorridor
open GoertzelV24FramedCorridorThreeFacePrefixProfileRepeat
open GoertzelV24FramedTrail
open GoertzelV24WidthTwoPortIncidenceCompression

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedBaseThresholdEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The first block length whose modulo-four profile pigeonhole has enough
positions to return two source layers separated by more than three offsets. -/
def separatedSourceProfileBlockLength : Nat :=
  4 * boundedWidthTwoPortIncidenceProfileCount 3 + 4

/-- The semantic compression makes the actual block length a checked
numeral, rather than leaving the conservative raw profile formula opaque. -/
theorem separatedSourceProfileBlockLength_eq :
    separatedSourceProfileBlockLength = 764740 := by
  rw [separatedSourceProfileBlockLength,
    boundedWidthTwoPortIncidenceProfileCount_three]

theorem separatedSourceProfileBlockLength_pos :
    0 < separatedSourceProfileBlockLength := by
  unfold separatedSourceProfileBlockLength
  omega

/-- The chosen block length discharges the exact arithmetic premise of the
source-layer separated-profile theorem. -/
theorem separatedSourceProfileBlockLength_large :
    4 * boundedWidthTwoPortIncidenceProfileCount 3 + 1 ≤
      separatedSourceProfileBlockLength - 3 := by
  unfold separatedSourceProfileBlockLength
  omega

/-- Effective interior-face threshold obtained by asking the existing framed
L1 theorem for a corridor long enough to force a separated source-profile
repeat on the proved three-face carrier. -/
def pentagonBoundedSeparatedProfileFaceThreshold
    (source : SourceTrail G) (pentagonBound : Nat) : Nat :=
  SourceTrail.AnnularEmbedding.pentagonBoundedBoundaryCleanHexBlockThreshold
    source pentagonBound separatedSourceProfileBlockLength

/-- Quantitative L1/L7 entrance at a proposed pentagon bound.  Above the
displayed face threshold, either the proposed bound is false or an actual
clean corridor of the profile-repeat length exists. -/
theorem pentagonCount_exceeds_bound_or_nonempty_separatedProfileCorridor
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (pentagonBound : Nat)
    (hlarge :
      pentagonBoundedSeparatedProfileFaceThreshold source pentagonBound <
        embedded.cellulation.interiorFaces.card) :
    pentagonBound < embedded.interiorFaceLengths.count 5 ∨
      Nonempty (CleanOrbitHexCorridorSkeleton
        embedded.cellulation.rotation.toRotationSystem
          separatedSourceProfileBlockLength) := by
  exact embedded.pentagonCount_exceeds_bound_or_nonempty_cleanOrbitHexCorridorSkeleton
    hsource geometry pentagonBound separatedSourceProfileBlockLength
      separatedSourceProfileBlockLength_pos hlarge

/-- If a caller really supplies the pentagon bound, the same explicit face
threshold constructs the clean corridor.  The bound remains a visible input;
this theorem does not manufacture the missing uniform curvature estimate. -/
theorem nonempty_separatedProfileCorridor_of_pentagonCount_le
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (pentagonBound : Nat)
    (hpentagons : embedded.interiorFaceLengths.count 5 ≤ pentagonBound)
    (hlarge :
      pentagonBoundedSeparatedProfileFaceThreshold source pentagonBound <
        embedded.cellulation.interiorFaces.card) :
    Nonempty (CleanOrbitHexCorridorSkeleton
      embedded.cellulation.rotation.toRotationSystem
        separatedSourceProfileBlockLength) := by
  rcases pentagonCount_exceeds_bound_or_nonempty_separatedProfileCorridor
      hsource embedded geometry pentagonBound hlarge with hbad | hcorridor
  · omega
  · exact hcorridor

end

end GoertzelV24FramedBaseThreshold

end Mettapedia.GraphTheory.FourColor
