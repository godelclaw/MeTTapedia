import Mettapedia.GraphTheory.FourColor.Compositional.NoncrossingMatchingEar
import Mettapedia.GraphTheory.FourColor.CycleAdjacentBoundaryRepair

/-!
# A physical repair of a constant cyclic boundary

A noncrossing perfect physical matching has an adjacent pair. Switching its
whole bichromatic component changes exactly those two boundary colours and
retains a genuine proper colouring of the exterior. The choice is made from
the actual component matching, rather than an independently chosen pairing.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ConstantBoundaryKempeRepair

open BoundaryKempeSwitch CyclicBoundaryMatching
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24PortTangleCommonKempeWeb GoertzelV24PortTangleCutParity
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTanglePhysicalKempeClosure

universe u
variable {V I P : Type u} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Fintype P] [DecidableEq P]
  {n : ℕ} [NeZero n]

/-- Repair the actual exterior witness, with both changed ports chosen from
one complete physical component. Noncrossing is the explicit geometric
hypothesis consumed by this theorem. -/
theorem repair (hn : 3 ≤ n) (order : Fin n ≃ P)
    (T : PortTangle V I P) (hcubic : IsCubic T)
    (coloring : Coloring T) (hproper : IsProper coloring) {c : Color}
    (hconstant : ∀ j, coloring.color (.inr (order j)) = c)
    (hplanar : ∀ pair, IsNoncrossingMatching
      (physicalMateInCoordinates order T hcubic coloring hproper pair)) :
    ∃ (d : Color) (i : Fin n) (changed : Coloring T),
      IsProper changed ∧ d ≠ 0 ∧ d ≠ c ∧
        ∀ j, changed.color (.inr (order j)) = CycleAdjacentBoundaryRepair.word i c d j := by
  classical
  have hc0 : c ≠ 0 := by
    simpa only [hconstant] using hproper.1 (.inr (order 0))
  obtain ⟨pair,hactive,hswap⟩ : ∃ pair : TaitColorPair,
      (c = pair.colors.1 ∨ c = pair.colors.2) ∧
      Color.swap pair.colors.1 pair.colors.2 c ≠ c := by
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc0 with h | h | h
    · subst c
      exact ⟨.redBlue, by simp [TaitColorPair.colors],
        by simp [TaitColorPair.colors, Color.swap, red, blue]⟩
    · subst c
      exact ⟨.redBlue, by simp [TaitColorPair.colors],
        by simp [TaitColorPair.colors, Color.swap, red, blue]⟩
    · subst c
      exact ⟨.redPurple, by simp [TaitColorPair.colors],
        by simp [TaitColorPair.colors, Color.swap, red, purple]⟩
  let mate := physicalMateInCoordinates order T hcubic coloring hproper pair
  have hinv (j) : mate (mate j) = j :=
    physicalMateInCoordinates_involutive order T hcubic coloring hproper pair j
  have hfree (j) : mate j ≠ j := by
    intro he
    have hphysical := physicalMate_order_eq_of_coordinate_eq
      order T hcubic coloring hproper pair he
    apply physicalMate_ne_of_active T hcubic coloring hproper pair (order j) _ hphysical
    simpa [pairActiveDart, pairActiveColor, Color.twoColor, hconstant] using hactive
  obtain ⟨i,hi⟩ := exists_adjacent mate hinv hfree (hplanar pair)
  have hpair : mate i = i+1 := by
    apply Fin.ext
    have hl : i.val+1 < n := by rw [← hi]; exact (mate i).isLt
    simpa [Fin.val_add, Fin.val_ofNat,
      Nat.mod_eq_of_lt (show 1 < n by omega), Nat.mod_eq_of_lt hl] using hi
  have hreverse : mate (i+1) = i := by rw [← hpair, hinv]
  let selected : Finset (Fin n) := {i, i+1}
  have hunion (j) : j ∈ selected ↔ mate j ∈ selected := by
    have hmem (j) : j ∈ selected ↔ j=i ∨ j=i+1 := by simp [selected]
    rw [hmem, hmem]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inr hpair
      · exact Or.inl hreverse
    · rintro (h | h)
      · have he := congrArg mate h
        rw [hinv, hpair] at he
        exact Or.inr he
      · have he := congrArg mate h
        rw [hinv, hreverse] at he
        exact Or.inl he
  have hmem := switchBoundaryWord_mem_supportInCoordinates
    order T hcubic coloring hproper pair selected hunion
  obtain ⟨changed,hchanged,hword⟩ := hmem
  let d := Color.swap pair.colors.1 pair.colors.2 c
  refine ⟨d,i,changed,hchanged,pairSwap_ne_zero pair hc0,hswap,?_⟩
  intro j
  have he := congrFun hword (order j)
  by_cases h : j=i ∨ j=i+1
  · simpa [PortTangle.word, switchBoundaryWord, properBoundaryWordInCoordinates,
      properBoundaryWord, selected, hconstant, CycleAdjacentBoundaryRepair.word, d, h] using he
  · simpa [PortTangle.word, switchBoundaryWord, properBoundaryWordInCoordinates,
      properBoundaryWord, selected, hconstant, CycleAdjacentBoundaryRepair.word, d, h] using he

end Mettapedia.GraphTheory.FourColor.Compositional.ConstantBoundaryKempeRepair
