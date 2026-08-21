import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedBoundaryCleanCorridor
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixProfileCompression
import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoFragmentReindexCompression

/-!
# An explicit framed threshold for the literal serial profile word

The route-correct cumulative word is the union of the complementary source
Cells, not the older union of complete hexagonal boundaries.  Its lossless
width-two profile carrier has `1541184` states.  This module substitutes that
proved count into the existing framed clean-corridor threshold and records the
resulting exact block length.

The result remains conditional on a proposed interior-pentagon bound.  It is a
quantitative entrance to the literal serial `L1`/`L7` construction, not a
uniform graph-size threshold `V0`, a reachable-closure certificate, or a
verified finite base.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedSerialBaseThreshold

open GoertzelV24CleanHexCorridor
open GoertzelV24FramedTrail
open GoertzelV24WidthTwoFragmentReindexCompression
open GoertzelV24WidthTwoPortIncidenceCompression

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedSerialBaseThresholdEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The first clean block long enough to contain the serial profile word used
by the modulo-four separated pigeonhole theorem. -/
def separatedSerialProfileBlockLength : Nat :=
  4 * boundedWidthTwoPortIncidenceProfileCount 4 + 4

/-- The route-correct serial block length is a kernel-checked numeral. -/
theorem separatedSerialProfileBlockLength_eq :
    separatedSerialProfileBlockLength = 6164740 := by
  rw [separatedSerialProfileBlockLength,
    boundedWidthTwoPortIncidenceProfileCount_four]

theorem separatedSerialProfileBlockLength_pos :
    0 < separatedSerialProfileBlockLength := by
  unfold separatedSerialProfileBlockLength
  omega

/-- The chosen length supplies exactly the number of indexed serial positions
required by the gap-at-least-four repeat theorem. -/
theorem separatedSerialProfileBlockLength_large :
    4 * boundedWidthTwoPortIncidenceProfileCount 4 + 1 ≤
      separatedSerialProfileBlockLength - 3 := by
  unfold separatedSerialProfileBlockLength
  omega

/-- The shorter clean block obtained by forgetting only the arbitrary
enumeration of the at-most-four face fragments. -/
def separatedFragmentReindexSerialProfileBlockLength : Nat :=
  4 * boundedWidthTwoFragmentReindexProfileCount 4 + 4

theorem separatedFragmentReindexSerialProfileBlockLength_eq :
    separatedFragmentReindexSerialProfileBlockLength = 422980 := by
  rw [separatedFragmentReindexSerialProfileBlockLength,
    boundedWidthTwoFragmentReindexProfileCount_four]

theorem separatedFragmentReindexSerialProfileBlockLength_pos :
    0 < separatedFragmentReindexSerialProfileBlockLength := by
  unfold separatedFragmentReindexSerialProfileBlockLength
  omega

theorem separatedFragmentReindexSerialProfileBlockLength_large :
    4 * boundedWidthTwoFragmentReindexProfileCount 4 + 1 ≤
      separatedFragmentReindexSerialProfileBlockLength - 3 := by
  unfold separatedFragmentReindexSerialProfileBlockLength
  omega

/-- Effective interior-face threshold for a clean corridor long enough to
carry the complete literal serial profile word. -/
def pentagonBoundedSeparatedSerialProfileFaceThreshold
    (source : SourceTrail G) (pentagonBound : Nat) : Nat :=
  SourceTrail.AnnularEmbedding.pentagonBoundedBoundaryCleanHexBlockThreshold
    source pentagonBound separatedSerialProfileBlockLength

/-- Effective face threshold for the fragment-reindexed serial repeat. -/
def pentagonBoundedSeparatedFragmentReindexSerialProfileFaceThreshold
    (source : SourceTrail G) (pentagonBound : Nat) : Nat :=
  SourceTrail.AnnularEmbedding.pentagonBoundedBoundaryCleanHexBlockThreshold
    source pentagonBound separatedFragmentReindexSerialProfileBlockLength

/-- Above the displayed threshold, either the proposed pentagon bound fails
or the actual annular carrier contains a clean corridor of the serial-repeat
length.  The first branch stays explicit because curvature does not supply a
uniform pentagon bound when long faces are allowed. -/
theorem pentagonCount_exceeds_bound_or_nonempty_separatedSerialProfileCorridor
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (pentagonBound : Nat)
    (hlarge :
      pentagonBoundedSeparatedSerialProfileFaceThreshold source pentagonBound <
        embedded.cellulation.interiorFaces.card) :
    pentagonBound < embedded.interiorFaceLengths.count 5 ∨
      Nonempty (CleanOrbitHexCorridorSkeleton
        embedded.cellulation.rotation.toRotationSystem
          separatedSerialProfileBlockLength) := by
  exact embedded.pentagonCount_exceeds_bound_or_nonempty_cleanOrbitHexCorridorSkeleton
    hsource geometry pentagonBound separatedSerialProfileBlockLength
      separatedSerialProfileBlockLength_pos hlarge

/-- A supplied pentagon bound removes the alternative and constructs the
clean corridor.  This is still not a uniform `V0`: the bound and the later
literal serial realization/reduction remain visible obligations. -/
theorem nonempty_separatedSerialProfileCorridor_of_pentagonCount_le
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (pentagonBound : Nat)
    (hpentagons : embedded.interiorFaceLengths.count 5 ≤ pentagonBound)
    (hlarge :
      pentagonBoundedSeparatedSerialProfileFaceThreshold source pentagonBound <
        embedded.cellulation.interiorFaces.card) :
    Nonempty (CleanOrbitHexCorridorSkeleton
      embedded.cellulation.rotation.toRotationSystem
        separatedSerialProfileBlockLength) := by
  rcases
      pentagonCount_exceeds_bound_or_nonempty_separatedSerialProfileCorridor
        hsource embedded geometry pentagonBound hlarge with hbad | hcorridor
  · omega
  · exact hcorridor

/-- Above the shorter quotient threshold, either the proposed pentagon bound
fails or the annular carrier contains a clean corridor long enough for the
fragment-reindexed repeat theorem. -/
theorem pentagonCount_exceeds_bound_or_nonempty_fragmentReindexSerialProfileCorridor
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (pentagonBound : Nat)
    (hlarge :
      pentagonBoundedSeparatedFragmentReindexSerialProfileFaceThreshold
          source pentagonBound <
        embedded.cellulation.interiorFaces.card) :
    pentagonBound < embedded.interiorFaceLengths.count 5 ∨
      Nonempty (CleanOrbitHexCorridorSkeleton
        embedded.cellulation.rotation.toRotationSystem
          separatedFragmentReindexSerialProfileBlockLength) := by
  exact embedded.pentagonCount_exceeds_bound_or_nonempty_cleanOrbitHexCorridorSkeleton
    hsource geometry pentagonBound
      separatedFragmentReindexSerialProfileBlockLength
      separatedFragmentReindexSerialProfileBlockLength_pos hlarge

/-- A supplied pentagon bound constructs a corridor of the shorter quotient
length.  A uniform pentagon bound and the finite base remain separate
obligations. -/
theorem nonempty_fragmentReindexSerialProfileCorridor_of_pentagonCount_le
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding)
    (geometry : embedded.CorridorGeometry)
    (pentagonBound : Nat)
    (hpentagons : embedded.interiorFaceLengths.count 5 ≤ pentagonBound)
    (hlarge :
      pentagonBoundedSeparatedFragmentReindexSerialProfileFaceThreshold
          source pentagonBound <
        embedded.cellulation.interiorFaces.card) :
    Nonempty (CleanOrbitHexCorridorSkeleton
      embedded.cellulation.rotation.toRotationSystem
        separatedFragmentReindexSerialProfileBlockLength) := by
  rcases
      pentagonCount_exceeds_bound_or_nonempty_fragmentReindexSerialProfileCorridor
        hsource embedded geometry pentagonBound hlarge with hbad | hcorridor
  · omega
  · exact hcorridor

end

end GoertzelV24FramedSerialBaseThreshold

end Mettapedia.GraphTheory.FourColor
