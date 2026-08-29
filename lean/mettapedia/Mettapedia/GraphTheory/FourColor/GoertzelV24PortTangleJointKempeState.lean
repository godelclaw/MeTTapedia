import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTanglePersistentKempe
import Mettapedia.GraphTheory.FourColor.GoertzelV24KempeIdemposition

/-!
# One shared carrier for the three Kempe manifolds

The three bichromatic supports of a Tait colouring live on one dart carrier.
They are therefore not independent boundary matchings: a switch selects one
literal subset of that carrier, leaves its own support fixed, and toggles both
companion supports by the same subset.  This file packages that exact joint
state and proves its transition law for a physical port-tangle switch.

This is deliberately not called a bounded interface compression.  The state
still remembers the whole common carrier; a later quotient must prove that it
retains enough of this shared incidence before it can replace the literal
state in a finite pumping argument.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PortTangleJointKempeState

open scoped symmDiff

open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCommonKempeWeb
open GoertzelV24HexagonPairingTargetAwareBoundary

universe u

variable {V I P : Type u}

/-- The three bichromatic edge sets, all indexed by one common carrier. -/
@[ext]
structure ManifoldTriple (D : Type u) where
  redBlue : Set D
  redPurple : Set D
  bluePurple : Set D

/-- Read all three manifold supports from one literal colouring. -/
def manifoldTriple (coloring : Coloring (T : PortTangle V I P)) :
    ManifoldTriple (I ⊕ P) where
  redBlue := {dart | pairActiveDart coloring .redBlue dart}
  redPurple := {dart | pairActiveDart coloring .redPurple dart}
  bluePurple := {dart | pairActiveDart coloring .bluePurple dart}

/-- The joint idemposition action of one selected subset.  The operated
support is fixed; the same subset toggles both companion supports. -/
def ManifoldTriple.toggle (state : ManifoldTriple D)
    (pair : TaitColorPair) (selected : Set D) : ManifoldTriple D :=
  match pair with
  | .redBlue =>
      ⟨state.redBlue, state.redPurple ∆ selected,
        state.bluePurple ∆ selected⟩
  | .redPurple =>
      ⟨state.redBlue ∆ selected, state.redPurple,
        state.bluePurple ∆ selected⟩
  | .bluePurple =>
      ⟨state.redBlue ∆ selected, state.redPurple ∆ selected,
        state.bluePurple⟩

private theorem color_ne_zero_of_pairActiveDart
    (coloring : Coloring (T : PortTangle V I P))
    (pair : TaitColorPair) (dart : I ⊕ P)
    (hactive : pairActiveDart coloring pair dart) :
    coloring.color dart ≠ 0 := by
  intro hzero
  cases pair with
  | redBlue =>
      have h : coloring.color dart = red ∨ coloring.color dart = blue := by
        simpa [pairActiveDart, pairActiveColor, TaitColorPair.colors,
          Color.twoColor] using hactive
      rcases h with hred | hblue
      · exact red_ne_zero (hred.symm.trans hzero)
      · exact blue_ne_zero (hblue.symm.trans hzero)
  | redPurple =>
      have h : coloring.color dart = red ∨ coloring.color dart = purple := by
        simpa [pairActiveDart, pairActiveColor, TaitColorPair.colors,
          Color.twoColor] using hactive
      rcases h with hred | hpurple
      · exact red_ne_zero (hred.symm.trans hzero)
      · exact purple_ne_zero (hpurple.symm.trans hzero)
  | bluePurple =>
      have h : coloring.color dart = blue ∨ coloring.color dart = purple := by
        simpa [pairActiveDart, pairActiveColor, TaitColorPair.colors,
          Color.twoColor] using hactive
      rcases h with hblue | hpurple
      · exact blue_ne_zero (hblue.symm.trans hzero)
      · exact purple_ne_zero (hpurple.symm.trans hzero)

/-- **Joint physical idemposition.**  A port-tangle Kempe switch realizes the
three-support update on one common selected dart set. -/
theorem manifoldTriple_switchRegion
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) (selected : I ⊕ P → Prop)
    [DecidablePred selected]
    (region : KempeRegion T coloring pair selected) :
    manifoldTriple (switchRegion T coloring pair selected region) =
      (manifoldTriple coloring).toggle pair {dart | selected dart} := by
  cases pair <;> apply ManifoldTriple.ext <;> ext dart
  all_goals
    simp only [manifoldTriple, ManifoldTriple.toggle, Set.mem_setOf_eq,
      Set.mem_symmDiff]
    by_cases hdart : selected dart
    · have hactive := region.active dart hdart
      have hnonzero := color_ne_zero_of_pairActiveDart
        coloring _ dart hactive
      rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero
          (coloring.color dart) hnonzero with hred | hblue | hpurple
      all_goals
        simp_all [pairActiveDart, pairActiveColor, TaitColorPair.colors,
          switchRegion, Color.twoColor, Color.swap, red, blue, purple]
    · simp [pairActiveDart, pairActiveColor, TaitColorPair.colors,
        switchRegion, Color.twoColor, Color.swap, hdart,
        red, blue, purple]

/-- The three supports on their common carrier retain the whole nonzero
colouring.  This is the exactness half of the joint carrier; it deliberately
does not assert that the carrier is a bounded boundary receipt. -/
theorem manifoldTriple_injective_of_proper
    (T : PortTangle V I P) {first second : Coloring T}
    (hfirst : IsProper first) (hsecond : IsProper second)
    (hstate : manifoldTriple first = manifoldTriple second) :
    first = second := by
  apply Coloring.ext'
  funext dart
  have hrb :
      pairActiveDart first .redBlue dart ↔
        pairActiveDart second .redBlue dart := by
    change dart ∈ (manifoldTriple first).redBlue ↔
      dart ∈ (manifoldTriple second).redBlue
    rw [hstate]
  have hrp :
      pairActiveDart first .redPurple dart ↔
        pairActiveDart second .redPurple dart := by
    change dart ∈ (manifoldTriple first).redPurple ↔
      dart ∈ (manifoldTriple second).redPurple
    rw [hstate]
  have hbp :
      pairActiveDart first .bluePurple dart ↔
        pairActiveDart second .bluePurple dart := by
    change dart ∈ (manifoldTriple first).bluePurple ↔
      dart ∈ (manifoldTriple second).bluePurple
    rw [hstate]
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero
      (first.color dart) (hfirst.1 dart) with hred | hblue | hpurple <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero
      (second.color dart) (hsecond.1 dart) with hred' | hblue' | hpurple' <;>
    simp_all [pairActiveDart, pairActiveColor, TaitColorPair.colors,
      Color.twoColor, red, blue, purple]

end GoertzelV24PortTangleJointKempeState

end Mettapedia.GraphTheory.FourColor
