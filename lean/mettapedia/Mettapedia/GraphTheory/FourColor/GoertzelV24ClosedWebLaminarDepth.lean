import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLengthDepthDichotomy
import Mettapedia.GraphTheory.PathChordNesting

/-!
# From a deep radial transversal to laminar chord depth

The L6 depth branch needs a real laminar family, not merely a large number.
This module isolates the exact remaining geometry.  Chords spanning one
radial cut cannot be disjoint: properness makes their endpoints distinct, so
every pair is either nested or strictly interleaving.  If the embedding gives
each actual chord one of the two genuine sectors and same-sector chords do not
interleave, the spanning chords in either sector are therefore laminar.

The finite factor is explicit.  A cut of load greater than `2 * depthBound`
has more than `depthBound` chords in one of the two sector fibers.  Thus the
high-load branch of the preceding module becomes a deep laminar family as
soon as the genuine two-sector noncrossing assignment is supplied.

No sector assignment is postulated for a closed web here.  Constructing it
from the rotation-system sector walls and the embedded Sector-Alternation
certificate is the remaining source-specific theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLaminarDepth

open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebLengthDepthDichotomy
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChordDiagram
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- The actual majority chords spanning one radial transversal. -/
def spanningChordsAtCut
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (cut : Fin radial.path.length) :
    Finset (OrderedPathChord (radial.path.length + 1)) :=
  (majorityChordDiagram C majority first second radial).filter
    (fun chord => chordSpansCut chord cut)

@[simp] theorem mem_spanningChordsAtCut_iff
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    {cut : Fin radial.path.length}
    {chord : OrderedPathChord (radial.path.length + 1)} :
    chord ∈ spanningChordsAtCut C majority first second radial cut ↔
      chord ∈ majorityChordDiagram C majority first second radial ∧
        chordSpansCut chord cut := by
  classical
  simp [spanningChordsAtCut]

theorem card_spanningChordsAtCut
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (cut : Fin radial.path.length) :
    (spanningChordsAtCut C majority first second radial cut).card =
      radialChordCutLoad C majority first second radial cut := by
  rfl

/-- Compatibility name for the graph-free laminar-family predicate. -/
abbrev PairwiseLaminar {length : Nat}
    (chords : Finset (OrderedPathChord length)) : Prop :=
  Mettapedia.GraphTheory.PairwiseLaminar chords

/-- The precise topological interface still required from the annular
embedding: actual chords receive one of two sector labels, and chords drawn
in the same sector never strictly interleave. -/
def SameSectorNoncrossing
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (sector : OrderedPathChord (radial.path.length + 1) → Bool) : Prop :=
  ∀ firstChord ∈ majorityChordDiagram C majority first second radial,
    ∀ secondChord ∈ majorityChordDiagram C majority first second radial,
      firstChord ≠ secondChord →
      sector firstChord = sector secondChord →
      ¬ firstChord.Crosses secondChord

/-- The spanning chords in one selected sector. -/
def sectorSpanningChords
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (sector : OrderedPathChord (radial.path.length + 1) → Bool)
    (side : Bool) (cut : Fin radial.path.length) :
    Finset (OrderedPathChord (radial.path.length + 1)) :=
  (spanningChordsAtCut C majority first second radial cut).filter
    (fun chord => sector chord = side)

@[simp] theorem mem_sectorSpanningChords_iff
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    {sector : OrderedPathChord (radial.path.length + 1) → Bool}
    {side : Bool} {cut : Fin radial.path.length}
    {chord : OrderedPathChord (radial.path.length + 1)} :
    chord ∈ sectorSpanningChords C majority first second radial
        sector side cut ↔
      chord ∈ majorityChordDiagram C majority first second radial ∧
        chordSpansCut chord cut ∧ sector chord = side := by
  classical
  simp [sectorSpanningChords, and_assoc]

/-- Two endpoint-disjoint chords spanning the same cut are either strictly
nested or strictly interleaving.  They cannot occupy disjoint path
intervals because both intervals contain the cut. -/
theorem nested_or_crosses_of_spansCut_of_endpointDisjoint
    {length : Nat} {cut : Fin length}
    {firstChord secondChord : OrderedPathChord (length + 1)}
    (hfirst : chordSpansCut firstChord cut)
    (hsecond : chordSpansCut secondChord cut)
    (hdisjoint :
      firstChord.left ≠ secondChord.left ∧
      firstChord.left ≠ secondChord.right ∧
      firstChord.right ≠ secondChord.left ∧
      firstChord.right ≠ secondChord.right) :
    firstChord.NestedIn secondChord ∨
      secondChord.NestedIn firstChord ∨
      firstChord.Crosses secondChord := by
  unfold chordSpansCut at hfirst hsecond
  unfold OrderedPathChord.NestedIn OrderedPathChord.Crosses
  have hfirstOrder := firstChord.left_lt_right
  have hsecondOrder := secondChord.left_lt_right
  omega

/-- The preceding interval trichotomy specialized to two distinct actual
majority chords at one actual radial cut. -/
theorem actual_spanningChords_nested_or_crosses
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    {cut : Fin radial.path.length}
    {firstChord secondChord :
      OrderedPathChord (radial.path.length + 1)}
    (hfirst : firstChord ∈
      spanningChordsAtCut C majority first second radial cut)
    (hsecond : secondChord ∈
      spanningChordsAtCut C majority first second radial cut)
    (hne : firstChord ≠ secondChord) :
    firstChord.NestedIn secondChord ∨
      secondChord.NestedIn firstChord ∨
      firstChord.Crosses secondChord := by
  rw [mem_spanningChordsAtCut_iff] at hfirst hsecond
  have hdisjoint := majorityChordDiagram_pairwiseEndpointDisjoint
    C majority first second radial firstChord hfirst.1
      secondChord hsecond.1 hne
  exact nested_or_crosses_of_spansCut_of_endpointDisjoint
    hfirst.2 hsecond.2 hdisjoint

/-- Once the two genuine sectors have been identified, each sector fiber at
a fixed cut is an actual laminar chord family. -/
theorem sectorSpanningChords_pairwiseLaminar
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (sector : OrderedPathChord (radial.path.length + 1) → Bool)
    (hnoncrossing : SameSectorNoncrossing
      C majority first second radial sector)
    (side : Bool) (cut : Fin radial.path.length) :
    PairwiseLaminar
      (sectorSpanningChords C majority first second radial
        sector side cut) := by
  intro firstChord hfirst secondChord hsecond hne
  rw [mem_sectorSpanningChords_iff] at hfirst hsecond
  rcases actual_spanningChords_nested_or_crosses
      C majority first second radial
      ((mem_spanningChordsAtCut_iff).2 ⟨hfirst.1, hfirst.2.1⟩)
      ((mem_spanningChordsAtCut_iff).2 ⟨hsecond.1, hsecond.2.1⟩)
      hne with hnested | hnested | hcross
  · exact Or.inl hnested
  · exact Or.inr hnested
  · exact False.elim <| hnoncrossing firstChord hfirst.1
      secondChord hsecond.1 hne (hfirst.2.2.trans hsecond.2.2.symm) hcross

/-- The two Boolean sector fibers partition the spanning chords, so their
cardinalities add to the actual cut load. -/
theorem card_sectorSpanningChords_false_add_true
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (sector : OrderedPathChord (radial.path.length + 1) → Bool)
    (cut : Fin radial.path.length) :
    (sectorSpanningChords C majority first second radial
        sector false cut).card +
      (sectorSpanningChords C majority first second radial
        sector true cut).card =
      radialChordCutLoad C majority first second radial cut := by
  classical
  let spanning := spanningChordsAtCut C majority first second radial cut
  have hpartition := spanning.card_filter_add_card_filter_not
    (fun chord => sector chord = false)
  rw [← card_spanningChordsAtCut C majority first second radial cut]
  simpa [sectorSpanningChords, spanning] using hpartition

/-- A high-load transversal yields a genuinely large laminar sector fiber,
with the factor two coming only from the two sectors. -/
theorem exists_large_laminar_sector_of_hasDeepChordTransversal
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (sector : OrderedPathChord (radial.path.length + 1) → Bool)
    (hnoncrossing : SameSectorNoncrossing
      C majority first second radial sector)
    (depthBound : Nat)
    (hdeep : HasDeepChordTransversal
      C majority first second radial (2 * depthBound)) :
    ∃ (cut : Fin radial.path.length) (side : Bool),
      depthBound <
        (sectorSpanningChords C majority first second radial
          sector side cut).card ∧
      PairwiseLaminar
        (sectorSpanningChords C majority first second radial
          sector side cut) := by
  rcases hdeep with ⟨cut, hload⟩
  have hpartition := card_sectorSpanningChords_false_add_true
    C majority first second radial sector cut
  by_cases hfalse : depthBound <
      (sectorSpanningChords C majority first second radial
        sector false cut).card
  · exact ⟨cut, false, hfalse,
      sectorSpanningChords_pairwiseLaminar
        C majority first second radial sector hnoncrossing false cut⟩
  · have htrue : depthBound <
        (sectorSpanningChords C majority first second radial
          sector true cut).card := by
      omega
    exact ⟨cut, true, htrue,
      sectorSpanningChords_pairwiseLaminar
        C majority first second radial sector hnoncrossing true cut⟩

end

end GoertzelV24ClosedWebLaminarDepth

end Mettapedia.GraphTheory.FourColor
