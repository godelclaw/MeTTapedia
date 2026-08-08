import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebChordRotationNoncrossing
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebProfileFiniteness

/-!
# Equal finite profiles inside a deep laminar chord family

The depth branch of Addendum XXVII ultimately needs two nested layer
boundaries carrying the same L7 profile.  It does not need an unproved claim
that the sector bit changes at every nesting step.  The intrinsic rotation
coordinate already supplies a large pairwise-laminar chord family.  Mapping
each member of that family to the finite depth-profile carrier and applying
pigeonhole produces two distinct, hence strictly nested, members with equal
profiles.

This module closes that finite bridge.  Constructing the actual vertex side
bounded by each chord, and proving the equal-profile depth splice checklist,
remain separate geometric obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLaminarProfileRepeat

open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebChordRotationNoncrossing
open GoertzelV24ClosedWebChordRotationSector
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebLaminarDepth
open GoertzelV24ClosedWebLengthDepthDichotomy
open GoertzelV24ClosedWebProfileFiniteness
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChordDiagram
open GoertzelV24ClosedWebRadialPathSectorAnchors
open SimpleGraph

/-- More pairwise-laminar chords than finite states force two strictly nested
chords with the same state.  This is the abstract combinatorial core of depth
profile repetition. -/
theorem exists_nested_equal_state_of_pairwiseLaminar
    {length : Nat} {State : Type*} [Fintype State]
    (chords : Finset (OrderedPathChord length))
    (hlaminar : PairwiseLaminar chords)
    (profile : { chord // chord ∈ chords } → State)
    (hcard : Fintype.card State < chords.card) :
    ∃ inner outer : { chord // chord ∈ chords },
      inner ≠ outer ∧ inner.1.NestedIn outer.1 ∧
        profile inner = profile outer := by
  have hcard' : Fintype.card State <
      Fintype.card { chord // chord ∈ chords } := by
    simpa using hcard
  obtain ⟨first, second, hne, hequal⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt profile hcard'
  have hvalueNe : first.1 ≠ second.1 := by
    intro heq
    exact hne (Subtype.ext heq)
  rcases hlaminar first.1 first.2 second.1 second.2 hvalueNe with
    hfirstInside | hsecondInside
  · exact ⟨first, second, hne, hfirstInside, hequal⟩
  · exact ⟨second, first, hne.symm, hsecondInside, hequal.symm⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- Source-facing depth repetition: a radial cut whose chord load exceeds
twice the explicit varying-width L7 count contains two nested same-sector
chords with equal assigned depth profiles.

The profile assignment is deliberately data, not a splice premise.  The next
geometric layer must compute it from each chord-bounded vertex side. -/
theorem exists_nested_equal_depthProfile_of_hasDeepChordTransversal
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second)
    (widthBound : Nat)
    (hdeep : HasDeepChordTransversal C majority first second
      pair.firstPath (2 * closedWebCutProfileCount widthBound))
    (profile :
      ∀ (cut : Fin pair.firstPath.path.length) (side : Bool),
        { chord // chord ∈
          sectorSpanningChords C majority first second pair.firstPath
            (positionRotationSector embedded hdata pair.firstPath htriple)
            side cut } →
          ClosedWebDepthProfile widthBound) :
    ∃ (cut : Fin pair.firstPath.path.length) (side : Bool)
        (inner outer : { chord // chord ∈
          sectorSpanningChords C majority first second pair.firstPath
            (positionRotationSector embedded hdata pair.firstPath htriple)
            side cut }),
      inner ≠ outer ∧ inner.1.NestedIn outer.1 ∧
        profile cut side inner = profile cut side outer := by
  rcases exists_large_laminar_rotationSector_of_hasDeepChordTransversal
      embedded hdata pair htriple
        (closedWebCutProfileCount widthBound) hdeep with
    ⟨cut, side, hlarge, hlaminar⟩
  let chords :=
    sectorSpanningChords C majority first second pair.firstPath
      (positionRotationSector embedded hdata pair.firstPath htriple)
      side cut
  have hstateCard : Fintype.card (ClosedWebDepthProfile widthBound) <
      chords.card := by
    rw [card_closedWebDepthProfile]
    exact hlarge
  obtain ⟨inner, outer, hne, hnested, hequal⟩ :=
    exists_nested_equal_state_of_pairwiseLaminar
      chords hlaminar (profile cut side) hstateCard
  exact ⟨cut, side, inner, outer, hne, hnested, hequal⟩

end

end GoertzelV24ClosedWebLaminarProfileRepeat

end Mettapedia.GraphTheory.FourColor
