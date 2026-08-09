import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryProfileFiniteState

/-!
# Explicit finite profiles for both closed-web pumping directions

Addendum XXVII uses the same observations on a length transversal and on a
depth-layer boundary: crossed-edge colors, bichromatic connectivity, and
partial face lengths capped at five.  The existing corridor profile contains
exactly those observations (with harmless extra Boolean incidence data and the
third bichromatic pair), while the graph-derived boundary construction proves
that at most twice as many face fragments as crossing ports are needed.

One additional finite packaging step is required for L7: local complexity
bounds the number of crossing ports rather than fixing it.  `ClosedWebCutProfile`
therefore stores the actual width below a supplied bound together with the
corresponding bounded corridor profile.  Its cardinality is an explicit finite
sum, and one more cut than that count forces a repeated profile in either
pumping direction.

This is only the finite-state part of L7.  It does not assert that the L6
laminar layers have already been constructed or that equal-profile splicing is
valid; those are separate geometric and splice obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebProfileFiniteness

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationVertexCutProfile
open GoertzelV24WindingClassification

/-- A closed-web cut profile whose actual crossing width may be any value up
to `widthBound`.  The payload is the existing finite L7 carrier at that exact
width.  Actual graph cuts map into this conservative carrier below. -/
structure ClosedWebCutProfile (widthBound : Nat) where
  crossingEdgeCount : Fin (widthBound + 1)
  profile : BoundedCorridorCutProfile crossingEdgeCount.val 0
    (2 * crossingEdgeCount.val)
  deriving DecidableEq

private def closedWebCutProfileEquiv (widthBound : Nat) :
    ClosedWebCutProfile widthBound ≃
      Σ crossingEdgeCount : Fin (widthBound + 1),
        BoundedCorridorCutProfile crossingEdgeCount.val 0
          (2 * crossingEdgeCount.val) where
  toFun state := ⟨state.crossingEdgeCount, state.profile⟩
  invFun state := ⟨state.1, state.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance closedWebCutProfileFintype (widthBound : Nat) :
    Fintype (ClosedWebCutProfile widthBound) :=
  Fintype.ofEquiv _ (closedWebCutProfileEquiv widthBound).symm

/-- The explicit L7 state bound after allowing every crossing width up to the
local-complexity bound. -/
def closedWebCutProfileCount (widthBound : Nat) : Nat :=
  ∑ crossingEdgeCount : Fin (widthBound + 1),
    vertexSetBoundaryProfileStateCount crossingEdgeCount.val

/-- The varying-width L7 carrier has exactly the displayed conservative state
count.  It is conservative because arbitrary Boolean matrices are retained;
actual planar cut profiles occupy a subset. -/
theorem card_closedWebCutProfile (widthBound : Nat) :
    Fintype.card (ClosedWebCutProfile widthBound) =
      closedWebCutProfileCount widthBound := by
  rw [Fintype.card_congr (closedWebCutProfileEquiv widthBound),
    Fintype.card_sigma]
  simp_rw [card_vertexSetBoundaryProfileCarrier]
  rfl

/-- An actual vertex-side boundary of width at most `widthBound` maps into the
single varying-width L7 carrier. -/
noncomputable def vertexSetClosedWebCutProfile
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (widthBound : Nat)
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (inside : Finset V) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C)
    (hwidth : Fintype.card (VertexSetCrossingEdge RS inside) ≤ widthBound) :
    ClosedWebCutProfile widthBound where
  crossingEdgeCount :=
    ⟨Fintype.card (VertexSetCrossingEdge RS inside),
      Nat.lt_succ_of_le hwidth⟩
  profile := vertexSetBoundaryBoundedProfile RS htwoSided inside C hC

/-- Occurrence-sensitive actual-cut packaging for framed closed webs.  This is
the preferred L7 construction when boundary stubs are bridges. -/
noncomputable def vertexSetClosedWebCutProfileOfDartOccurrences
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (widthBound : Nat)
    (RS : RotationSystem V E) (inside : Finset V)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (hwidth : Fintype.card (VertexSetCrossingEdge RS inside) ≤ widthBound) :
    ClosedWebCutProfile widthBound where
  crossingEdgeCount :=
    ⟨Fintype.card (VertexSetCrossingEdge RS inside),
      Nat.lt_succ_of_le hwidth⟩
  profile := vertexSetBoundaryBoundedProfileOfDartOccurrences RS inside C hC

/-- L7 packaging with a caller-selected crossing coordinate.  A future
geometric transversal may use this to retain its actual port order while
still entering exactly the same finite varying-width carrier. -/
noncomputable def vertexSetClosedWebCutProfileWithIndexing
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (widthBound : Nat)
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (inside : Finset V) (indexing : VertexSetCrossingIndexing RS inside)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (hwidth : Fintype.card (VertexSetCrossingEdge RS inside) ≤ widthBound) :
    ClosedWebCutProfile widthBound where
  crossingEdgeCount :=
    ⟨Fintype.card (VertexSetCrossingEdge RS inside),
      Nat.lt_succ_of_le hwidth⟩
  profile := vertexSetBoundaryBoundedProfileWithIndexing RS htwoSided inside
    indexing C hC

/-- Occurrence-sensitive L7 packaging with a caller-selected crossing
coordinate, for framed closed webs with bridge stubs. -/
noncomputable def vertexSetClosedWebCutProfileOfDartOccurrencesWithIndexing
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (widthBound : Nat)
    (RS : RotationSystem V E) (inside : Finset V)
    (indexing : VertexSetCrossingIndexing RS inside)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (hwidth : Fintype.card (VertexSetCrossingEdge RS inside) ≤ widthBound) :
    ClosedWebCutProfile widthBound where
  crossingEdgeCount :=
    ⟨Fintype.card (VertexSetCrossingEdge RS inside),
      Nat.lt_succ_of_le hwidth⟩
  profile := vertexSetBoundaryBoundedProfileOfDartOccurrencesWithIndexing
    RS inside indexing C hC

/-- Pigeonhole form of L7: any sequence containing one more boundary than the
explicit state count repeats a profile. -/
theorem exists_profile_repeat
    (widthBound : Nat)
    (profiles : Fin (closedWebCutProfileCount widthBound + 1) →
      ClosedWebCutProfile widthBound) :
    ∃ first second, first ≠ second ∧ profiles first = profiles second := by
  have hcard :
      Fintype.card (ClosedWebCutProfile widthBound) <
        Fintype.card (Fin (closedWebCutProfileCount widthBound + 1)) := by
    rw [card_closedWebCutProfile]
    simp
  exact Fintype.exists_ne_map_eq_of_card_lt profiles hcard

/-- The length-coordinate profile is the varying-width L7 carrier. -/
abbrev ClosedWebLengthProfile := ClosedWebCutProfile

/-- The depth-coordinate profile records the same observations on a layer
boundary. -/
abbrev ClosedWebDepthProfile := ClosedWebCutProfile

/-- The length-coordinate carrier has the explicit varying-width count. -/
theorem card_closedWebLengthProfile (widthBound : Nat) :
    Fintype.card (ClosedWebLengthProfile widthBound) =
      closedWebCutProfileCount widthBound :=
  card_closedWebCutProfile widthBound

/-- The depth-coordinate carrier has the same explicit count. -/
theorem card_closedWebDepthProfile (widthBound : Nat) :
    Fintype.card (ClosedWebDepthProfile widthBound) =
      closedWebCutProfileCount widthBound :=
  card_closedWebCutProfile widthBound

/-- Explicit profile repetition along the length coordinate. -/
theorem exists_lengthProfile_repeat
    (widthBound : Nat)
    (profiles : Fin (closedWebCutProfileCount widthBound + 1) →
      ClosedWebLengthProfile widthBound) :
    ∃ first second, first ≠ second ∧ profiles first = profiles second :=
  exists_profile_repeat widthBound profiles

/-- Explicit profile repetition along the depth coordinate. -/
theorem exists_depthProfile_repeat
    (widthBound : Nat)
    (profiles : Fin (closedWebCutProfileCount widthBound + 1) →
      ClosedWebDepthProfile widthBound) :
    ∃ first second, first ≠ second ∧ profiles first = profiles second :=
  exists_profile_repeat widthBound profiles

end GoertzelV24ClosedWebProfileFiniteness

end Mettapedia.GraphTheory.FourColor
