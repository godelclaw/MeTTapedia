import Mettapedia.Combinatorics.Matching.FourthMatchingCoordinates
import PurePartner

/-!
# Krenn-specific consequence of the abstract fourth-matching theorem

The reusable construction of a mixed fourth matching from three involutions
lives in `Mettapedia.Combinatorics.Matching.FourthMatchingCoordinates`.
This file retains only its consequence for three-regular GHZ configurations.
-/

namespace CycleCoordinates

open Equiv MixedColouring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The rigid shape above four sites -/

open Amplitude MatchingSum

/-- **A three-regular solution is impossible above four sites.**  Its three matchings admit
a fourth, which is a non-constant colouring whose only contributing matching is itself, and
the no-rival lemma then makes that colouring constant. -/
theorem no_three_regular_uniform (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (hV : ∀ x : V, (Finset.univ.erase x).Nonempty)
    (hcard : 4 < Fintype.card V)
    (T : PurePartner.ThreeRegular W) : False := by
  classical
  obtain ⟨σ, hpair, -, -, -, hpart⟩ := PurePartner.three_matchings W hone hzero hV T
  obtain ⟨c, ⟨x, y, hxy⟩, hc⟩ := exists_mixed σ
    (fun k z => (Amplitude.mem_pairings_iff.mp (hpair k)).1 z)
    (fun k z => (Amplitude.mem_pairings_iff.mp (hpair k)).2 z) hcard
  have hinvτ : Function.Involutive (fun z : V => σ (c z) z) := by
    intro z
    show σ (c (σ (c z) z)) (σ (c z) z) = z
    rw [hc z]
    exact (Amplitude.mem_pairings_iff.mp (hpair (c z))).1 z
  refine PurePartner.no_three_regular W hone hzero hV T ⟨hinvτ.toPerm _, c, ?_, ?_, ?_⟩
  · refine Amplitude.mem_pairings_iff.mpr ⟨fun z => hinvτ z, fun z => ?_⟩
    exact (Amplitude.mem_pairings_iff.mp (hpair (c z))).2 z
  · intro z
    exact hpart (c z) z
  · rintro ⟨k, hk⟩
    exact hxy ((hk x).trans (hk y).symm)

end CycleCoordinates
