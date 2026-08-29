import Mathlib.Data.Set.SymmDiff
import Mettapedia.GraphTheory.FourColor.ColorAlgebra

/-!
# Kempe idemposition on the three Tait manifolds

The three bichromatic subgraphs carried by one Tait colouring are not
independent.  If a red--blue component is switched, its own edge support is
unchanged, while the red--purple and blue--purple supports are each toggled
by exactly the switched edge set.  This is the source manuscript's
idemposition identity, stated without any graph or planarity assumptions.

The containment hypothesis says only that every selected edge really has
one of the two switched colours.  A genuine Kempe component supplies this
hypothesis automatically.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24KempeIdemposition

open scoped symmDiff

/-- Generic idemposition law for the first of the two companion colour
pairs. -/
theorem twoColorSupport_switch_left_companion
    {E : Type*} (C : E → Color) (D : Set E)
    {a b c : Color} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hD : D ⊆ twoColorSupport C a b) :
    twoColorSupport (switch a b D C) a c =
      twoColorSupport C a c ∆ D := by
  classical
  ext edge
  by_cases hedge : edge ∈ D
  · have hpair : C edge = a ∨ C edge = b := hD hedge
    rcases hpair with hcolor | hcolor
    · subst hcolor
      simp [twoColorSupport, twoColor, Color.twoColor, hedge, hab.symm,
        hac, hbc, Set.mem_symmDiff]
    · subst hcolor
      simp [twoColorSupport, twoColor, Color.twoColor, hedge, hab.symm,
        hac, hbc, Set.mem_symmDiff]
  · simp [twoColorSupport, twoColor, Color.twoColor, hedge,
      Set.mem_symmDiff]

/-- Generic idemposition law for the second companion colour pair. -/
theorem twoColorSupport_switch_right_companion
    {E : Type*} (C : E → Color) (D : Set E)
    {a b c : Color} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hD : D ⊆ twoColorSupport C a b) :
    twoColorSupport (switch a b D C) b c =
      twoColorSupport C b c ∆ D := by
  classical
  ext edge
  by_cases hedge : edge ∈ D
  · have hpair : C edge = a ∨ C edge = b := hD hedge
    rcases hpair with hcolor | hcolor
    · subst hcolor
      simp [twoColorSupport, twoColor, Color.twoColor, hedge, hab,
        hac, hbc, Set.mem_symmDiff]
    · subst hcolor
      simp [twoColorSupport, twoColor, Color.twoColor, hedge, hab,
        hac, hbc, Set.mem_symmDiff]
  · simp [twoColorSupport, twoColor, Color.twoColor, hedge,
      Set.mem_symmDiff]

/-- The source identity in the fixed red--blue--purple naming. -/
theorem redBlue_idemposition
    {E : Type*} (C : E → Color) (D : Set E)
    (hD : D ⊆ twoColorSupport C red blue) :
    twoColorSupport (switch red blue D C) red blue =
        twoColorSupport C red blue ∧
      twoColorSupport (switch red blue D C) red purple =
        twoColorSupport C red purple ∆ D ∧
      twoColorSupport (switch red blue D C) blue purple =
        twoColorSupport C blue purple ∆ D := by
  exact ⟨twoColorSupport_switch red blue D C,
    twoColorSupport_switch_left_companion C D red_ne_blue
      red_ne_purple blue_ne_purple hD,
    twoColorSupport_switch_right_companion C D red_ne_blue
      red_ne_purple blue_ne_purple hD⟩

end GoertzelV24KempeIdemposition

end Mettapedia.GraphTheory.FourColor
