import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationBoundaryFaceCutProfile

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24BoundaryProfileFiniteState

open GoertzelV24CorridorProfile
open GoertzelV24CorridorPumping
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open GoertzelV24WindingClassification

/-- A single profile carrier for every face-fragment count up to a fixed
bound. The fragment count is data, not a validity proposition, and the
dependent payload is the existing finite Boolean/capped profile. -/
structure BoundedCorridorCutProfile
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) where
  faceFragmentCount : Fin (faceFragmentBound + 1)
  profile : CorridorCutProfile crossingEdgeCount terminalCount
    faceFragmentCount.val
  deriving DecidableEq

private def boundedCorridorCutProfileEquiv
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) :
    BoundedCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound ≃
      Σ faceFragmentCount : Fin (faceFragmentBound + 1),
        CorridorCutProfile crossingEdgeCount terminalCount
          faceFragmentCount.val where
  toFun state := ⟨state.faceFragmentCount, state.profile⟩
  invFun state := ⟨state.1, state.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance boundedCorridorCutProfileFintype
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) :
    Fintype (BoundedCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound) :=
  Fintype.ofEquiv _
    (boundedCorridorCutProfileEquiv crossingEdgeCount terminalCount
      faceFragmentBound).symm

/-- Explicit state count when the number of partial-face fragments may vary
from zero through the supplied bound. -/
def boundedCorridorCutProfileCount
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) : Nat :=
  ∑ faceFragmentCount : Fin (faceFragmentBound + 1),
    corridorCutProfileCount crossingEdgeCount terminalCount
      faceFragmentCount.val

/-- Exact L7 state count for the variable-fragment profile carrier. -/
theorem card_boundedCorridorCutProfile
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) :
    Fintype.card (BoundedCorridorCutProfile crossingEdgeCount terminalCount
      faceFragmentBound) =
      boundedCorridorCutProfileCount crossingEdgeCount terminalCount
        faceFragmentBound := by
  rw [Fintype.card_congr
    (boundedCorridorCutProfileEquiv crossingEdgeCount terminalCount
      faceFragmentBound),
    Fintype.card_sigma]
  simp_rw [card_corridorCutProfile]
  rfl

theorem card_finset_boundedCorridorCutProfile
    (crossingEdgeCount terminalCount faceFragmentBound : Nat) :
    Fintype.card (Finset (BoundedCorridorCutProfile crossingEdgeCount
      terminalCount faceFragmentBound)) =
      2 ^ boundedCorridorCutProfileCount crossingEdgeCount terminalCount
        faceFragmentBound := by
  rw [Fintype.card_finset, card_boundedCorridorCutProfile]

/-- Corrected finite-state rejection descent for transfers whose number of
open face fragments varies while the cut width remains bounded. -/
theorem finiteBoundedCorridorProfileTransfer_rejectionDescent
    (crossingEdgeCount terminalCount faceFragmentBound : Nat)
    (oneStep :
      BoundedCorridorCutProfile crossingEdgeCount terminalCount
          faceFragmentBound →
        BoundedCorridorCutProfile crossingEdgeCount terminalCount
          faceFragmentBound → Prop)
    [DecidableRel oneStep]
    (initial : Finset (BoundedCorridorCutProfile crossingEdgeCount
      terminalCount faceFragmentBound))
    (isAccepting :
      BoundedCorridorCutProfile crossingEdgeCount terminalCount
        faceFragmentBound → Prop) :
    ∃ preperiod period : Nat,
      preperiod <
        2 ^ boundedCorridorCutProfileCount crossingEdgeCount terminalCount
          faceFragmentBound + 1 ∧
      0 < period ∧
      period ≤
        2 ^ boundedCorridorCutProfileCount crossingEdgeCount terminalCount
          faceFragmentBound ∧
      ∀ length : Nat,
        preperiod + period ≤ length →
        ¬ TransferAcceptsInExactly oneStep initial isAccepting length →
        ∃ shorter : Nat,
          preperiod ≤ shorter ∧ shorter < length ∧
          ¬ TransferAcceptsInExactly oneStep initial isAccepting shorter := by
  obtain ⟨preperiod, period, hpreperiod, hperiod_pos, hperiod,
      hdescent⟩ :=
    finiteRelationalTransfer_rejectionDescentWithBounds
      oneStep initial isAccepting
  rw [card_finset_boundedCorridorCutProfile] at hpreperiod hperiod
  exact ⟨preperiod, period, hpreperiod, hperiod_pos, hperiod, hdescent⟩

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The explicit variable-fragment state bound for an actual vertex-side cut
of width `crossingEdgeCount`. -/
def vertexSetBoundaryProfileStateCount (crossingEdgeCount : Nat) : Nat :=
  boundedCorridorCutProfileCount crossingEdgeCount 0
    (2 * crossingEdgeCount)

/-- Package the graph-derived boundary profile of an actual vertex side into
the uniform finite carrier controlled only by its crossing-port count. -/
def vertexSetBoundaryBoundedProfile
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (inside : Finset V) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    BoundedCorridorCutProfile
      (Fintype.card (VertexSetCrossingEdge RS inside)) 0
      (2 * Fintype.card (VertexSetCrossingEdge RS inside)) where
  faceFragmentCount :=
    ⟨Fintype.card (BoundaryRegionalFragment RS
        (vertexSetCrossingEdges RS inside) (vertexSetRegionEdges RS inside)),
      Nat.lt_succ_of_le
        (vertexSetBoundaryGraphCutData_fragmentCount_le_two_mul_crossingPortCount
          RS htwoSided inside)⟩
  profile := (vertexSetBoundaryGraphCutData RS inside).profile C hC

@[simp]
theorem vertexSetBoundaryBoundedProfile_faceFragmentCount_val
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (inside : Finset V) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    (vertexSetBoundaryBoundedProfile RS htwoSided inside C hC).faceFragmentCount.val =
      Fintype.card (BoundaryRegionalFragment RS
        (vertexSetCrossingEdges RS inside)
        (vertexSetRegionEdges RS inside)) :=
  rfl

/-- The family containing all graph-derived boundary states at a fixed cut
width has the displayed exact finite cardinality. -/
theorem card_vertexSetBoundaryProfileCarrier (crossingEdgeCount : Nat) :
    Fintype.card (BoundedCorridorCutProfile crossingEdgeCount 0
      (2 * crossingEdgeCount)) =
      vertexSetBoundaryProfileStateCount crossingEdgeCount := by
  exact card_boundedCorridorCutProfile crossingEdgeCount 0
    (2 * crossingEdgeCount)

end


end GoertzelV24BoundaryProfileFiniteState

end Mettapedia.GraphTheory.FourColor
