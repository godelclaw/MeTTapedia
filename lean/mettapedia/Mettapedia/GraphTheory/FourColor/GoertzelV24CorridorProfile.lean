import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorPumping
import Mettapedia.GraphTheory.FourColor.GoertzelV24WindingClassification

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CorridorProfile

open GoertzelV24CorridorPumping
open GoertzelV24WindingClassification

/-- The three two-color subgraphs whose component data crosses a corridor
section. -/
inductive TrackedColorPair where
  | ab
  | ac
  | bc
  deriving DecidableEq, Fintype

/-- Ports visible to a corridor section: crossed edges and fixed terminals
carried from the already exposed side. -/
abbrev CorridorPort (crossingEdgeCount terminalCount : Nat) :=
  Fin crossingEdgeCount ⊕ Fin terminalCount

/-- A finite over-encoding of the data needed to splice equal corridor
sections. Connectivity, face continuation, and fragment-to-port incidence are
stored as complete Boolean matrices. Actual graph profiles occupy the valid
subset, but including invalid matrices gives a conservative finite bound
without assuming validity as a free proposition field. `Fin 6` stores a
partial face length capped at five. -/
structure CorridorCutProfile
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) where
  edgeColor : Fin crossingEdgeCount → StrandColor
  strandConnected :
    TrackedColorPair →
      CorridorPort crossingEdgeCount terminalCount →
      CorridorPort crossingEdgeCount terminalCount → Bool
  faceContinues :
    Fin faceFragmentCount → Fin faceFragmentCount → Bool
  fragmentContainsPort :
    Fin faceFragmentCount →
      CorridorPort crossingEdgeCount terminalCount → Bool
  faceLengthCap : Fin faceFragmentCount → Fin 6
  deriving DecidableEq

private def corridorCutProfileEquiv
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) :
    CorridorCutProfile crossingEdgeCount terminalCount faceFragmentCount ≃
      ((Fin crossingEdgeCount → StrandColor) ×
        (TrackedColorPair →
          CorridorPort crossingEdgeCount terminalCount →
          CorridorPort crossingEdgeCount terminalCount → Bool) ×
        (Fin faceFragmentCount → Fin faceFragmentCount → Bool) ×
        (Fin faceFragmentCount →
          CorridorPort crossingEdgeCount terminalCount → Bool) ×
        (Fin faceFragmentCount → Fin 6)) where
  toFun profile :=
    (profile.edgeColor, profile.strandConnected,
      profile.faceContinues, profile.fragmentContainsPort,
      profile.faceLengthCap)
  invFun data :=
    ⟨data.1, data.2.1, data.2.2.1, data.2.2.2.1, data.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance corridorCutProfileFintype
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) :
    Fintype (CorridorCutProfile
      crossingEdgeCount terminalCount faceFragmentCount) :=
  Fintype.ofEquiv _
    (corridorCutProfileEquiv
      crossingEdgeCount terminalCount faceFragmentCount).symm

/-- Explicit upper-state count for the profile over-encoding. -/
def corridorCutProfileCount
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) : Nat :=
  3 ^ crossingEdgeCount *
    (2 ^ ((crossingEdgeCount + terminalCount) *
      (crossingEdgeCount + terminalCount))) ^ 3 *
    2 ^ (faceFragmentCount * faceFragmentCount) *
    2 ^ (faceFragmentCount *
      (crossingEdgeCount + terminalCount)) *
    6 ^ faceFragmentCount

/-- L7 profile finiteness with an exact count for the chosen over-encoding. -/
theorem card_corridorCutProfile
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) :
    Fintype.card (CorridorCutProfile
      crossingEdgeCount terminalCount faceFragmentCount) =
      corridorCutProfileCount
        crossingEdgeCount terminalCount faceFragmentCount := by
  rw [Fintype.card_congr
    (corridorCutProfileEquiv
      crossingEdgeCount terminalCount faceFragmentCount)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Fintype.card_sum]
  have hcolor : Fintype.card StrandColor = 3 := by decide
  have hpair : Fintype.card TrackedColorPair = 3 := by decide
  rw [hcolor, hpair]
  unfold corridorCutProfileCount
  ring

/-- The deterministic reachable-set construction used by corrected L2 has
the powerset size of the explicit L7 profile count. -/
theorem card_finset_corridorCutProfile
    (crossingEdgeCount terminalCount faceFragmentCount : Nat) :
    Fintype.card (Finset (CorridorCutProfile
      crossingEdgeCount terminalCount faceFragmentCount)) =
      2 ^ corridorCutProfileCount
        crossingEdgeCount terminalCount faceFragmentCount := by
  rw [Fintype.card_finset,
    card_corridorCutProfile]

/-- L2 plus L7 in effective form. Any decidable transfer on the explicit
corridor profiles has a rejection descent whose preperiod and period are
bounded by the displayed profile-powerset count. -/
theorem finiteCorridorProfileTransfer_rejectionDescent
    (crossingEdgeCount terminalCount faceFragmentCount : Nat)
    (oneStep :
      CorridorCutProfile crossingEdgeCount terminalCount faceFragmentCount →
      CorridorCutProfile crossingEdgeCount terminalCount faceFragmentCount →
      Prop)
    [DecidableRel oneStep]
    (initial : Finset (CorridorCutProfile
      crossingEdgeCount terminalCount faceFragmentCount))
    (isAccepting :
      CorridorCutProfile crossingEdgeCount terminalCount faceFragmentCount →
      Prop) :
    ∃ preperiod period : Nat,
      preperiod <
        2 ^ corridorCutProfileCount crossingEdgeCount terminalCount
          faceFragmentCount + 1 ∧
      0 < period ∧
      period ≤
        2 ^ corridorCutProfileCount crossingEdgeCount terminalCount
          faceFragmentCount ∧
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
  rw [card_finset_corridorCutProfile] at hpreperiod hperiod
  exact ⟨preperiod, period, hpreperiod, hperiod_pos, hperiod, hdescent⟩

end GoertzelV24CorridorProfile

end Mettapedia.GraphTheory.FourColor
