import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTanglePhysicalKempeClosure

/-!
# Persistence of one physical Kempe web under its own switches

Switching a union of components of one bichromatic web changes the two
colours but not membership in their unordered pair.  Consequently the local
web relation, its connected components, and the induced physical boundary
mate are unchanged.  This is the same-family part of the source manuscript's
idemposition dynamics; the two companion families still change through the
common selected edge set.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PortTanglePersistentKempe

open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCutParity
open GoertzelV24PortTangleCommonKempeWeb
open GoertzelV24PortTanglePhysicalKempeClosure
open GoertzelV24HexagonPairingTargetAwareBoundary

universe u

variable {V I P : Type u}

/-- A switch of one bichromatic region preserves every local wire of that
same bichromatic web. -/
theorem kempeStep_switchRegion_iff
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) (selected : I ⊕ P → Prop)
    [DecidablePred selected]
    (region : KempeRegion T coloring pair selected)
    (first second : I ⊕ P) :
    KempeStep T (switchRegion T coloring pair selected region) pair
        first second ↔
      KempeStep T coloring pair first second := by
  simp only [KempeStep, pairActiveDart_switchRegion_iff]

/-- Hence switching a union of components preserves the entire connectedness
relation of the selected bichromatic web. -/
theorem kempeConnected_switchRegion_iff
    (T : PortTangle V I P) (coloring : Coloring T)
    (pair : TaitColorPair) (selected : I ⊕ P → Prop)
    [DecidablePred selected]
    (region : KempeRegion T coloring pair selected)
    (first second : I ⊕ P) :
    KempeConnected T (switchRegion T coloring pair selected region) pair
        first second ↔
      KempeConnected T coloring pair first second := by
  constructor
  · intro hconnected
    exact Relation.EqvGen.mono
      (fun x y hstep =>
        (kempeStep_switchRegion_iff T coloring pair selected region x y).1
          hstep)
      hconnected
  · intro hconnected
    exact Relation.EqvGen.mono
      (fun x y hstep =>
        (kempeStep_switchRegion_iff T coloring pair selected region x y).2
          hstep)
      hconnected

section Finite

variable [Fintype V] [Fintype I] [Fintype P]
  [DecidableEq V] [DecidableEq I] [DecidableEq P]

/-- **Same-family physical-mate persistence.**  The two boundary endpoints
of every component are unchanged when any union of components of that same
colour pair is switched. -/
theorem physicalMate_switchRegion_eq
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring)
    (pair : TaitColorPair) (selected : I ⊕ P → Prop)
    [DecidablePred selected]
    (region : KempeRegion T coloring pair selected) :
    physicalMate T hcubic
        (switchRegion T coloring pair selected region)
        (switchRegion_isProper T coloring hproper pair selected region) pair =
      physicalMate T hcubic coloring hproper pair := by
  funext root
  by_cases hroot : pairActiveDart coloring pair (Sum.inr root)
  · have hrootSwitched : pairActiveDart
        (switchRegion T coloring pair selected region) pair (Sum.inr root) :=
      (pairActiveDart_switchRegion_iff
        T coloring pair selected region (Sum.inr root)).2 hroot
    let other := physicalMate T hcubic coloring hproper pair root
    have hspec := (physicalMate_eq_iff_of_active
      T hcubic coloring hproper pair root other hroot).1 rfl
    apply (physicalMate_eq_iff_of_active T hcubic
      (switchRegion T coloring pair selected region)
      (switchRegion_isProper T coloring hproper pair selected region)
      pair root other hrootSwitched).2
    refine ⟨hspec.1, ?_, ?_⟩
    · exact (pairActiveDart_switchRegion_iff
        T coloring pair selected region (Sum.inr other)).2 hspec.2.1
    · exact (kempeConnected_switchRegion_iff
        T coloring pair selected region (Sum.inr root) (Sum.inr other)).2
          hspec.2.2
  · have hrootSwitched : ¬ pairActiveDart
        (switchRegion T coloring pair selected region) pair (Sum.inr root) :=
      fun hactive => hroot ((pairActiveDart_switchRegion_iff
        T coloring pair selected region (Sum.inr root)).1 hactive)
    rw [physicalMate_eq_self_of_inactive T hcubic coloring hproper pair
      root hroot]
    exact physicalMate_eq_self_of_inactive T hcubic
      (switchRegion T coloring pair selected region)
      (switchRegion_isProper T coloring hproper pair selected region)
      pair root hrootSwitched

end Finite

end GoertzelV24PortTanglePersistentKempe

end Mettapedia.GraphTheory.FourColor
