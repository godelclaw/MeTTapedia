import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTangleJointKempeState
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPersistentKempeAdversary

/-!
# Boundary projection still loses joint Kempe incidence

The literal joint manifold triple uses one common interior dart carrier.  Its
restriction to the six ports, however, is determined by the boundary word
alone.  This file proves that the sixty-word persistent adversary satisfies
the resulting projected joint toggle law, including its deterministic mates
at every successor state.

Thus recording that both companion boundary supports toggle on the same port
set does not retain the source's shared interior edge incidence.  A faithful
bounded quotient needs strictly more than the boundary word and the three
boundary mates.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexagonProjectedJointAdversary

open scoped symmDiff

open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24HexagonPersistentKempeAdversary
open GoertzelV24PortTangleJointKempeState

/-- The three bichromatic supports after forgetting every interior dart. -/
def boundaryManifoldTriple (word : HexagonTaitWord) :
    ManifoldTriple (Fin 6) where
  redBlue := {port | activePort word .redBlue port}
  redPurple := {port | activePort word .redPurple port}
  bluePurple := {port | activePort word .bluePurple port}

/-- A physical selected region contains only ports active for the operated
colour pair. -/
def SelectedActive (word : HexagonTaitWord) (pair : TaitColorPair)
    (selected : Finset (Fin 6)) : Prop :=
  forall port, port ∈ selected -> activePort word pair port

/-- Projecting the exact joint idemposition identity to the ports gives the
same toggle law, provided the selected ports are active. -/
theorem boundaryManifoldTriple_swapBoundaryWord
    (word : HexagonTaitWord) (pair : TaitColorPair)
    (selected : Finset (Fin 6))
    (hselected : SelectedActive word pair selected) :
    boundaryManifoldTriple (swapBoundaryWord word pair selected) =
      (boundaryManifoldTriple word).toggle pair
        {port | port ∈ selected} := by
  cases pair <;> apply ManifoldTriple.ext <;> ext port
  all_goals
    simp only [boundaryManifoldTriple, ManifoldTriple.toggle,
      Set.mem_setOf_eq, Set.mem_symmDiff]
    by_cases hport : port ∈ selected
    · have hactive := hselected port hport
      rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero
          (word port).1 (word port).2 with hred | hblue | hpurple
      all_goals
        simp_all [activePort, swapBoundaryWord, TaitColorPair.colors,
          Color.swap, red, blue, purple]
    · simp [activePort, swapBoundaryWord, TaitColorPair.colors,
        hport, red, blue, purple]

/-- The persistent witness together with the boundary projection of the
common-carrier toggle law.  The persistent component already records closure
of the language and preservation of the operated mate at every successor. -/
def HasProjectedJointBoundaryWitness
    (word : HexagonTaitWord) (pair : TaitColorPair) : Prop :=
  PersistentCandidateKempeWitness word pair ∧
    forall selected : Finset (Fin 6),
      IsComponentUnion
          (candidateMate word pair (persistentPattern word pair)) selected ->
        SelectedActive word pair selected ->
          boundaryManifoldTriple (swapBoundaryWord word pair selected) =
            (boundaryManifoldTriple word).toggle pair
              {port | port ∈ selected}

/-- Every state and colour pair of the adversary satisfies the projected
joint law, not merely the three separate same-family closure laws. -/
theorem persistentAdversary_hasProjectedJointBoundaryWitness :
    ∀ word ∈ persistentAdversary, ∀ pair : TaitColorPair,
      HasProjectedJointBoundaryWitness word pair := by
  intro word hword pair
  refine ⟨persistentAdversary_hasPersistentCandidate word hword pair, ?_⟩
  intro selected _hunion hactive
  exact boundaryManifoldTriple_swapBoundaryWord word pair selected hactive

/-- **Projected joint idemposition is insufficient.**  A nonempty language
disjoint from the literal hexagon support satisfies the complete deterministic
boundary machine and the simultaneous projected toggle equation. -/
theorem persistentAdversary_survives_projectedJointBoundary :
    persistentAdversary.Nonempty ∧
      Disjoint persistentAdversary hexagonSupport ∧
      (∀ word ∈ persistentAdversary, ∀ pair : TaitColorPair,
        HasProjectedJointBoundaryWitness word pair) := by
  exact ⟨persistentAdversary_nonempty,
    persistentAdversary_disjoint_hexagonSupport,
    persistentAdversary_hasProjectedJointBoundaryWitness⟩

end GoertzelV24HexagonProjectedJointAdversary

end Mettapedia.GraphTheory.FourColor
