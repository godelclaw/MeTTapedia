import Mettapedia.GraphTheory.FourColor.GoertzelV24BulkCorridor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialLength

/-!
# The finite-local length/depth split on a closed-web radial path

The source's L6 argument starts from a long radial `B`-coordinate and a
bounded set of contaminated transversal positions.  At each transversal,
the actual majority-color same-path chords have a finite load: the number of
chord intervals spanning that cut.

This module proves the numerical pigeonhole at that exact interface.  Among
`defectBudget + 1` consecutive blocks, a defect set of cardinality at most
`defectBudget` misses one whole block.  Hence a sufficiently long actual
radial path has either

* a clean consecutive block on which every actual chord load is at most the
  proposed depth bound, or
* an actual transversal spanned by more chords than that bound.

The second branch is deliberately called a `DeepChordTransversal`, not yet a
laminar nest.  Turning its many spanning chords into the source's alternating
two-sector layers is the remaining geometric use of Sector Alternation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLengthDepthDichotomy

open GoertzelV24BulkCorridor
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChordDiagram
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- A same-path chord spans the transversal immediately after vertex
`cut`.  The endpoint convention is half-open: `left <= cut < right`. -/
def chordSpansCut {length : Nat}
    (chord : OrderedPathChord (length + 1)) (cut : Fin length) : Prop :=
  chord.left.val ≤ cut.val ∧ cut.val < chord.right.val

instance {length : Nat} (chord : OrderedPathChord (length + 1))
    (cut : Fin length) : Decidable (chordSpansCut chord cut) := by
  unfold chordSpansCut
  infer_instance

/-- The actual majority-chord load at a radial transversal. -/
def radialChordCutLoad
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (cut : Fin radial.path.length) : Nat :=
  ((majorityChordDiagram C majority first second radial).filter
    (fun chord => chordSpansCut chord cut)).card

/-- Embed one of the first `(defectBudget + 1) * blockLength` cuts into a
longer radial path. -/
def radialPrefixCut
    {radialLength defectBudget blockLength : Nat}
    (hprefix : (defectBudget + 1) * blockLength ≤ radialLength)
    (position : Fin ((defectBudget + 1) * blockLength)) :
    Fin radialLength :=
  ⟨position.val, position.isLt.trans_le hprefix⟩

theorem radialPrefixCut_injective
    {radialLength defectBudget blockLength : Nat}
    (hprefix : (defectBudget + 1) * blockLength ≤ radialLength) :
    Function.Injective (radialPrefixCut hprefix) := by
  intro left right heq
  apply Fin.ext
  simpa [radialPrefixCut] using
    congrArg (fun position : Fin radialLength => position.val) heq

/-- Position `offset` in radial block `block`, embedded in the actual long
path rather than merely its initial prefix. -/
def radialBlockCut
    {radialLength defectBudget blockLength : Nat}
    (hprefix : (defectBudget + 1) * blockLength ≤ radialLength)
    (block : Fin (defectBudget + 1)) (offset : Fin blockLength) :
    Fin radialLength :=
  radialPrefixCut hprefix (corridorBlockIndex block offset)

theorem radialBlockCut_injective_block
    {radialLength defectBudget blockLength : Nat}
    (hblockLength : 0 < blockLength)
    (hprefix : (defectBudget + 1) * blockLength ≤ radialLength)
    {left right : Fin (defectBudget + 1)}
    (leftOffset rightOffset : Fin blockLength)
    (hindex : radialBlockCut hprefix left leftOffset =
      radialBlockCut hprefix right rightOffset) :
    left = right := by
  apply corridorBlockIndex_injective_block hblockLength
    leftOffset rightOffset
  exact radialPrefixCut_injective hprefix hindex

/-- A bounded defect set misses one complete block in the long radial
prefix.  This is the defect-budget half of L6. -/
theorem exists_radialBlock_avoiding
    (radialLength defectBudget blockLength : Nat)
    (hblockLength : 0 < blockLength)
    (hprefix : (defectBudget + 1) * blockLength ≤ radialLength)
    (badPositions : Finset (Fin radialLength))
    (hbad : badPositions.card ≤ defectBudget) :
    ∃ block : Fin (defectBudget + 1),
      ∀ offset : Fin blockLength,
        radialBlockCut hprefix block offset ∉ badPositions := by
  classical
  by_contra hnoBlock
  push Not at hnoBlock
  choose badOffset hbadOffset using hnoBlock
  let selectedBad : Fin (defectBudget + 1) →
      {position // position ∈ badPositions} :=
    fun block =>
      ⟨radialBlockCut hprefix block (badOffset block), hbadOffset block⟩
  have hinjective : Function.Injective selectedBad := by
    intro left right hequal
    apply radialBlockCut_injective_block hblockLength hprefix
      (badOffset left) (badOffset right)
    exact congrArg Subtype.val hequal
  have hcard := Fintype.card_le_of_injective selectedBad hinjective
  have htooMany : defectBudget + 1 ≤ badPositions.card := by
    simpa using hcard
  omega

/-- An actual clean shallow corridor along a radial path: a consecutive
block avoids every declared contaminated cut and has bounded actual
majority-chord load at every transversal. -/
def HasShallowRadialCorridor
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (badPositions : Finset (Fin radial.path.length))
    (defectBudget depthBound blockLength : Nat) : Prop :=
  ∃ (hprefix : (defectBudget + 1) * blockLength ≤ radial.path.length)
      (block : Fin (defectBudget + 1)),
    ∀ offset : Fin blockLength,
      let cut := radialBlockCut hprefix block offset
      cut ∉ badPositions ∧
        radialChordCutLoad C majority first second radial cut ≤ depthBound

/-- The numerical entrance to the depth branch: one actual transversal is
spanned by more majority chords than the proposed depth bound. -/
def HasDeepChordTransversal
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (depthBound : Nat) : Prop :=
  ∃ cut : Fin radial.path.length,
    depthBound < radialChordCutLoad C majority first second radial cut

/-- The finite-local L6 pigeonhole on an actual closed-web radial path.

This theorem does not encode either conclusion as a premise.  Its only
inputs are the actual chord diagram, a declared finite contamination set,
the cardinality bound on that set, and enough actual radial positions. -/
theorem hasShallowRadialCorridor_or_hasDeepChordTransversal
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (badPositions : Finset (Fin radial.path.length))
    (defectBudget depthBound blockLength : Nat)
    (hblockLength : 0 < blockLength)
    (hbad : badPositions.card ≤ defectBudget)
    (hprefix : (defectBudget + 1) * blockLength ≤ radial.path.length) :
    HasShallowRadialCorridor C majority first second radial badPositions
        defectBudget depthBound blockLength ∨
      HasDeepChordTransversal C majority first second radial depthBound := by
  classical
  by_cases hdeep : ∃ cut : Fin radial.path.length,
      depthBound < radialChordCutLoad C majority first second radial cut
  · exact Or.inr hdeep
  · left
    have hshallow : ∀ cut : Fin radial.path.length,
        radialChordCutLoad C majority first second radial cut ≤ depthBound := by
      intro cut
      exact Nat.le_of_not_gt (by
        intro hload
        exact hdeep ⟨cut, hload⟩)
    obtain ⟨block, hblock⟩ := exists_radialBlock_avoiding
      radial.path.length defectBudget blockLength hblockLength hprefix
        badPositions hbad
    exact ⟨hprefix, block, fun offset =>
      ⟨hblock offset, hshallow (radialBlockCut hprefix block offset)⟩⟩

/-- Empty chord diagrams are uniformly shallow, so the clean-block branch
is automatic once the defect pigeonhole supplies a block. -/
theorem hasShallowRadialCorridor_of_chordDiagram_eq_empty
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (badPositions : Finset (Fin radial.path.length))
    (defectBudget depthBound blockLength : Nat)
    (hblockLength : 0 < blockLength)
    (hbad : badPositions.card ≤ defectBudget)
    (hprefix : (defectBudget + 1) * blockLength ≤ radial.path.length)
    (hempty : majorityChordDiagram C majority first second radial = ∅) :
    HasShallowRadialCorridor C majority first second radial badPositions
      defectBudget depthBound blockLength := by
  classical
  obtain ⟨block, hblock⟩ := exists_radialBlock_avoiding
    radial.path.length defectBudget blockLength hblockLength hprefix
      badPositions hbad
  refine ⟨hprefix, block, ?_⟩
  intro offset
  constructor
  · exact hblock offset
  · simp [radialChordCutLoad, hempty]

end

end GoertzelV24ClosedWebLengthDepthDichotomy

end Mettapedia.GraphTheory.FourColor
