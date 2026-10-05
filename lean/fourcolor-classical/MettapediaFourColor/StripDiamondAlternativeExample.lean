import MettapediaFourColor.StripDiamondAlternative
import MettapediaFourColor.StripSixPhaseExample

/-! The existing phase-obstruction sphere also supplies a smaller diamond
pattern. Its failure of a selected strip repair does not exclude choosing
this alternative reduction. No new graph fixture is introduced. -/

namespace FourColor.StripDiamondAlternativeExample

open SimpleGraph StripSixPhaseExample

def reading : StripDiamondAlternative.Reading rotation where
  map := sourceHom
  degree := by
    intro i hi
    rw [degree_eq]
    revert hi
    fin_cases i <;> decide +kernel
  left := ⟨source_edges 12 11 (by decide +kernel),
    source_edges 12 8 (by decide +kernel),by apply Dart.ext; decide +kernel⟩
  right := ⟨source_edges 12 8 (by decide +kernel),
    source_edges 12 15 (by decide +kernel),by apply Dart.ext; decide +kernel⟩

theorem port_six : ambient.degree (reading.map 8) = 6 := by
  rw [degree_eq]
  decide +kernel

/-- The general source law supplies the mixed pattern on the actual sphere. -/
theorem mixed : RulePairDiamond.MixedAt rotation reading.root := by
  rcases reading.alternatives (by rw [port_six]; decide) (by rw [port_six]) with h | h
  · have five : ambient.degree (reading.map 8) = 5 := h.opposite
    rw [port_six] at five
    cases five
  · exact h

end FourColor.StripDiamondAlternativeExample
