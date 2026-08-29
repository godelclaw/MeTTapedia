import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPersistentKempeAdversaryCore

/-!
# The persistent adversary is already excluded by two planar caps

The sixty-word persistent adversary avoids the literal hexagon support and
meets the three smaller four-vertex tree supports.  It does not, however,
meet every planar pairing cap: it is disjoint from the supports of the caps
`(0,1)(2,3)(4,5)` and `(0,3)(1,2)(4,5)`.  So an exterior whose language were
exactly this adversary would already admit a zero-count cap replacement; the
adversary calibrates the persistence model, not the five-cap menu.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexagonPersistentAdversaryCapMenu

open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24HexagonPersistentKempeAdversary

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem persistentAdversary_avoids_planarPairing_zero :
    ∀ word ∈ persistentAdversaryFinset,
      ¬ (0 : HexagonPlanarPairing).Compatible (rawWord word) := by
  decide

theorem persistentAdversary_avoids_planarPairing_two :
    ∀ word ∈ persistentAdversaryFinset,
      ¬ (2 : HexagonPlanarPairing).Compatible (rawWord word) := by
  decide

theorem persistentAdversary_disjoint_planarPairingSupport_zero :
    Disjoint persistentAdversary (planarPairingSupport 0) := by
  rw [Set.disjoint_left]
  intro word hword hcap
  exact persistentAdversary_avoids_planarPairing_zero word
    ((mem_persistentAdversaryFinset_iff word).2 hword)
    ((mem_planarPairingSupport_iff 0 word).1 hcap)

theorem persistentAdversary_disjoint_planarPairingSupport_two :
    Disjoint persistentAdversary (planarPairingSupport 2) := by
  rw [Set.disjoint_left]
  intro word hword hcap
  exact persistentAdversary_avoids_planarPairing_two word
    ((mem_persistentAdversaryFinset_iff word).2 hword)
    ((mem_planarPairingSupport_iff 2 word).1 hcap)

/-- The adversary does not block the planar cap menu. -/
theorem persistentAdversary_not_meets_every_planarPairing :
    ¬ ∀ side : HexagonPlanarPairing,
      (persistentAdversary ∩ planarPairingSupport side).Nonempty := by
  intro h
  obtain ⟨word, hword, hcap⟩ := h 0
  exact Set.disjoint_left.1 persistentAdversary_disjoint_planarPairingSupport_zero hword hcap

end GoertzelV24HexagonPersistentAdversaryCapMenu

end Mettapedia.GraphTheory.FourColor
