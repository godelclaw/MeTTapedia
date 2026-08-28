import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierCapComposedProfileSemantics
import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedCorridorOpenProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedTerminalProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24SourceTerminalAwareProfileCompression

/-!
# The five-terminal cap view of the source corridor profile

The rolling Cell letter has one local terminal, whereas the cumulative source
crosscut profile has the five fixed cap-foot terminals.  The cap-restored Seed
test belongs to the latter carrier.  This file extracts exactly the part of a
five-terminal source profile used by that test:

* the five terminal colours, reconstructed from the two diagonal source-pair
  bits in the standard `(red, blue, purple)` gauge; and
* the two terminal connectivity relations named in the manuscript.

The same view is defined directly on the losslessly compressed carrier, and
compression is proved to preserve it exactly.  Thus cap acceptance is a
predicate of the existing compressed cumulative receipt; it does not enlarge
the one-Cell letter or add graph data to the finite state.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SourceTerminalCapView

open GoertzelV24AnnularFrontierCapComposedProfileSemantics
open GoertzelV24AnnularFrontierMenu
open GoertzelV24AnnularFrontierMenuCapComposed
open GoertzelV24AnnularFrontierMenuCapMatching
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24GraphDerivedTerminalProfile
open GoertzelV24SourceCorridorProfile
open GoertzelV24SourceTerminalAwareProfileCompression
open GoertzelV24WidthTwoProfileCompression

/-- The exact cap-facing projection of a five-terminal source profile. -/
@[ext] structure SourceTerminalCapView where
  word : CAP5BoundaryWord
  strand : SourceTrackedColorPair → Fin 5 → Fin 5 → Bool
  deriving DecidableEq

/-- Decode one terminal colour from membership in the two source pairs.
The impossible `false,false` pattern is sent to zero. -/
def terminalColorOfSourceBits (alphaBeta alphaGamma : Bool) : Color :=
  if alphaBeta then
    if alphaGamma then red else blue
  else if alphaGamma then purple else 0

/-- The two membership bits recover every nonzero Tait colour. -/
theorem terminalColorOfSourceBits_eq
    (alphaBeta alphaGamma : Bool) (color : Color)
    (hcolor : color ≠ 0)
    (hab : alphaBeta = true ↔ IsTrackedColor red blue color)
    (hac : alphaGamma = true ↔ IsTrackedColor red purple color) :
    terminalColorOfSourceBits alphaBeta alphaGamma = color := by
  revert alphaBeta alphaGamma color
  decide

/-- Read the five cap-foot colours and both source connectivity tables from
an uncompressed cumulative source profile. -/
def terminalCapViewOfSourceProfile
    {crossingEdgeCount faceFragmentCount : Nat}
    (profile : SourceCorridorCutProfile crossingEdgeCount 5 faceFragmentCount) :
    SourceTerminalCapView where
  word terminal :=
    terminalColorOfSourceBits
      (profile.strandConnected .alphaBeta (.inr terminal) (.inr terminal))
      (profile.strandConnected .alphaGamma (.inr terminal) (.inr terminal))
  strand pair first second :=
    profile.strandConnected pair (.inr first) (.inr second)

/-- Recover a terminal matrix entry from the compressed diagonal and
off-diagonal coordinates. -/
noncomputable def terminalStrandOfCompressed
    {crossingEdgeCount faceFragmentCount : Nat}
    (code : SourceTerminalAwareCompressedProfile crossingEdgeCount 5
      faceFragmentCount)
    (pair : SourceTrackedColorPair) (first second : Fin 5) : Bool := by
  classical
  exact if hsame : first = second then
    code.terminalStrandDiagonal pair first
  else
    code.strandConnected pair
      ⟨s((.inr first : CorridorPort crossingEdgeCount 5), .inr second), by
        simpa [Sym2.mk_isDiag_iff] using hsame⟩

/-- The cap-facing view read directly from a compressed source state. -/
noncomputable def terminalCapViewOfCompressed
    {crossingEdgeCount faceFragmentCount : Nat}
    (code : SourceTerminalAwareCompressedProfile crossingEdgeCount 5
      faceFragmentCount) : SourceTerminalCapView where
  word terminal :=
    terminalColorOfSourceBits
      (code.terminalStrandDiagonal .alphaBeta terminal)
      (code.terminalStrandDiagonal .alphaGamma terminal)
  strand := terminalStrandOfCompressed code

/-- Compression preserves every terminal connectivity entry. -/
theorem terminalStrand_compress
    {crossingEdgeCount faceFragmentCount : Nat}
    (profile : SourceCorridorCutProfile crossingEdgeCount 5 faceFragmentCount)
    (semantic : IsSourceTerminalGraphSemantic profile)
    (pair : SourceTrackedColorPair) (first second : Fin 5) :
    terminalStrandOfCompressed
        (GoertzelV24SourceTerminalAwareProfileCompression.compress
          profile semantic) pair first second =
      profile.strandConnected pair (.inr first) (.inr second) := by
  classical
  by_cases hsame : first = second
  · subst second
    simp [terminalStrandOfCompressed,
      GoertzelV24SourceTerminalAwareProfileCompression.compress]
  · simp [terminalStrandOfCompressed,
      GoertzelV24SourceTerminalAwareProfileCompression.compress, hsame]

/-- **The compressed receipt contains the complete cap-facing view.** -/
theorem terminalCapView_compress
    {crossingEdgeCount faceFragmentCount : Nat}
    (profile : SourceCorridorCutProfile crossingEdgeCount 5 faceFragmentCount)
    (semantic : IsSourceTerminalGraphSemantic profile) :
    terminalCapViewOfCompressed
        (GoertzelV24SourceTerminalAwareProfileCompression.compress
          profile semantic) =
      terminalCapViewOfSourceProfile profile := by
  apply SourceTerminalCapView.ext
  · funext terminal
    rfl
  · funext pair first second
    exact terminalStrand_compress profile semantic pair first second

/-- The two-pair cap-composed test for one source role. -/
def SourceTerminalCapView.capComposedMenuBForPair
    (view : SourceTerminalCapView) (pair : SourceTrackedColorPair) : Prop :=
  let colors := sourceTrackedColorPairColors red blue purple pair
  ∃ inactive : Fin 5,
    InactivePosition view.word colors.1 colors.2 inactive ∧
      CapComposedMenuB (fun first second =>
        view.strand pair first second = true) inactive

/-- The standard-gauge terminal acceptance predicate used by the source:
the boundary word is `(3,1,1)` with majority red, and one of the two named
majority pairs succeeds after the cap is restored. -/
def SourceTerminalCapView.standardGaugeCapComposedMenuBState
    (view : SourceTerminalCapView) : Prop :=
  AnnularFrontierMajorityTriple view.word red blue purple ∧
    (view.capComposedMenuBForPair .alphaBeta ∨
      view.capComposedMenuBForPair .alphaGamma)

/-- Cap acceptance is preserved exactly by source-profile compression. -/
theorem standardGaugeCapComposedMenuBState_compress_iff
    {crossingEdgeCount faceFragmentCount : Nat}
    (profile : SourceCorridorCutProfile crossingEdgeCount 5 faceFragmentCount)
    (semantic : IsSourceTerminalGraphSemantic profile) :
    (terminalCapViewOfCompressed
        (GoertzelV24SourceTerminalAwareProfileCompression.compress
          profile semantic)).standardGaugeCapComposedMenuBState ↔
      (terminalCapViewOfSourceProfile profile).standardGaugeCapComposedMenuBState := by
  rw [terminalCapView_compress]

/-- The cap view of a bounded source state ignores only its dependent face
count, as required by boundary locality. -/
def terminalCapViewOfBoundedSourceProfile
    {crossingEdgeCount faceFragmentBound : Nat}
    (profile : BoundedSourceCorridorCutProfile crossingEdgeCount 5
      faceFragmentBound) : SourceTerminalCapView :=
  terminalCapViewOfSourceProfile profile.profile

/-- Read the same view directly from the bounded compressed carrier. -/
noncomputable def terminalCapViewOfBoundedCompressed
    {crossingEdgeCount faceFragmentBound : Nat}
    (code : BoundedSourceTerminalAwareCompressedProfile crossingEdgeCount 5
      faceFragmentBound) : SourceTerminalCapView :=
  terminalCapViewOfCompressed code.profile

/-- Bounded compression also preserves the cap-facing view exactly. -/
theorem terminalCapView_compressBounded
    {crossingEdgeCount faceFragmentBound : Nat}
    (profile : BoundedSourceCorridorCutProfile crossingEdgeCount 5
      faceFragmentBound)
    (semantic : BoundedIsSourceTerminalGraphSemantic profile) :
    terminalCapViewOfBoundedCompressed
        (GoertzelV24SourceTerminalAwareProfileCompression.compressBounded
          profile semantic) =
      terminalCapViewOfBoundedSourceProfile profile := by
  exact terminalCapView_compress profile.profile semantic

/-- Therefore the terminal acceptance test is a predicate of the existing
finite bounded compressed state. -/
theorem standardGaugeCapComposedMenuBState_compressBounded_iff
    {crossingEdgeCount faceFragmentBound : Nat}
    (profile : BoundedSourceCorridorCutProfile crossingEdgeCount 5
      faceFragmentBound)
    (semantic : BoundedIsSourceTerminalGraphSemantic profile) :
    (terminalCapViewOfBoundedCompressed
        (GoertzelV24SourceTerminalAwareProfileCompression.compressBounded
          profile semantic)).standardGaugeCapComposedMenuBState ↔
      (terminalCapViewOfBoundedSourceProfile profile).standardGaugeCapComposedMenuBState := by
  rw [terminalCapView_compressBounded]

/-! ## The existing Cell-3 crosscut carrier -/

/-- Project one existing conservative Cell-3 state to the manuscript's two
roles and compress it losslessly.  This is a projection of the established
`BoundedCorridorCutProfile 2 5 8`, not a new terminal receipt. -/
noncomputable def sourceCompressedCodeOfCell3
    (profile : Cell3TerminalAwareProfile)
    (semantic : GoertzelV24TerminalAwareProfileCompression.BoundedIsTerminalGraphSemantic
      profile) :
    BoundedSourceTerminalAwareCompressedProfile 2 5 8 :=
  GoertzelV24SourceTerminalAwareProfileCompression.compressBounded
    (toBoundedSourceProfile profile)
    (isSourceTerminalGraphSemantic_toSourceProfile semantic)

/-- The source-compressed Cell-3 code has exactly the cap view of the original
five-terminal crosscut state. -/
theorem terminalCapView_sourceCompressedCodeOfCell3
    (profile : Cell3TerminalAwareProfile)
    (semantic : GoertzelV24TerminalAwareProfileCompression.BoundedIsTerminalGraphSemantic
      profile) :
    terminalCapViewOfBoundedCompressed
        (sourceCompressedCodeOfCell3 profile semantic) =
      terminalCapViewOfBoundedSourceProfile
        (toBoundedSourceProfile profile) := by
  exact terminalCapView_compressBounded
    (toBoundedSourceProfile profile)
    (isSourceTerminalGraphSemantic_toSourceProfile semantic)

/-- Consequently the cap-restored terminal test is already a predicate of
the finite source compression of the established Cell-3 carrier. -/
theorem standardGaugeCapComposedMenuBState_sourceCompressedCodeOfCell3_iff
    (profile : Cell3TerminalAwareProfile)
    (semantic : GoertzelV24TerminalAwareProfileCompression.BoundedIsTerminalGraphSemantic
      profile) :
    (terminalCapViewOfBoundedCompressed
      (sourceCompressedCodeOfCell3 profile semantic)).standardGaugeCapComposedMenuBState ↔
      (terminalCapViewOfBoundedSourceProfile
        (toBoundedSourceProfile profile)).standardGaugeCapComposedMenuBState := by
  rw [terminalCapView_sourceCompressedCodeOfCell3]

/-! ## Fidelity to literal graph-derived terminal colours -/

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- On a literal regional profile, the reconstructed five-word is exactly
the colour function on the five named terminal edges. -/
theorem terminalCapView_word_toSourceProfile_regionalProfile
    {RS : RotationSystem V E}
    {crossingEdgeCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount 5 faceFragmentCount)
    (hports : data.PortsInRegion)
    (color : E → Color)
    (hcrossing : ∀ crossing, color (data.crossingEdge crossing) ≠ 0)
    (hterminal : ∀ terminal, color (data.terminalEdge terminal) ≠ 0)
    (terminal : Fin 5) :
    (terminalCapViewOfSourceProfile
        (toSourceProfile (data.regionalProfile color hcrossing))).word terminal =
      color (data.terminalEdge terminal) := by
  apply terminalColorOfSourceBits_eq
  · exact hterminal terminal
  · simpa [terminalCapViewOfSourceProfile, toSourceProfile,
      SourceTrackedColorPair.toTrackedColorPair,
      GoertzelV24HexSlabConnectivityProfile.trackedColorPairColors,
      GraphCorridorCutData.portEdge] using
      (data.regionalProfile_strandConnected_self_eq_true_iff
        hports color hcrossing (.ab) (.inr terminal))
  · simpa [terminalCapViewOfSourceProfile, toSourceProfile,
      SourceTrackedColorPair.toTrackedColorPair,
      GoertzelV24HexSlabConnectivityProfile.trackedColorPairColors,
      GraphCorridorCutData.portEdge] using
      (data.regionalProfile_strandConnected_self_eq_true_iff
        hports color hcrossing (.ac) (.inr terminal))

/-- The reconstructed connectivity table is definitionally the two source
roles of the literal regional profile. -/
@[simp] theorem terminalCapView_strand_toSourceProfile_regionalProfile
    {RS : RotationSystem V E}
    {crossingEdgeCount faceFragmentCount : Nat}
    (data : GraphCorridorCutData RS crossingEdgeCount 5 faceFragmentCount)
    (color : E → Color)
    (hcrossing : ∀ crossing, color (data.crossingEdge crossing) ≠ 0)
    (pair : SourceTrackedColorPair) (first second : Fin 5) :
    (terminalCapViewOfSourceProfile
        (toSourceProfile (data.regionalProfile color hcrossing))).strand
        pair first second =
      (data.regionalProfile color hcrossing).strandConnected
        pair.toTrackedColorPair (.inr first) (.inr second) :=
  rfl

end GoertzelV24SourceTerminalCapView

end Mettapedia.GraphTheory.FourColor
