import Mathlib
import Amplitude
import PurePartner
import CycleCoordinates
import LiveDegree

/-!
# The conjecture, modulo one statement

Everything the programme has established assembles into a single implication in the official
formulation: if every GHZ system on more than four sites is three-regular, then no GHZ system
exists on more than four sites at all — for every vertex count, with no base case.

The six-vertex case is *not* used. `BaseSix` was carried as a sealed hypothesis while the
uniform argument was being built; the uniform argument does not need it, because the spread
case is settled for every even count above four rather than by descent to six.

What remains is the named hypothesis `ThreeRegularity`.

`NoCancellation` collects the tools aimed at that hypothesis and is deliberately *not* imported
here, so that nothing below depends on work that has not closed: certificates that survive
cancellation, the product formula for a colouring with no live edge between its classes, cut
results needing no monochromaticity, and the splitting of a matching along a set invariant under
two involutions.  It also states the hypothesis in positive form, as the existence of a
surviving mixed colouring.
-/

namespace MainTheorem

open Amplitude MatchingSum

/-- **The one remaining statement.**  Every GHZ system on more than four sites has exactly
three live partners at each site, one column-supported in each colour. -/
def ThreeRegularity : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (W : Sym2 (V × Fin 3) → ℂ),
    4 < Fintype.card V → KrennGu.IsGHZ W → Nonempty (PurePartner.ThreeRegular W)

/-- **The Krenn–Gu conjecture, modulo three-regularity.**  Uniform in the vertex count and
free of any base case. -/
theorem krenn_gu_of_three_regularity (h : ThreeRegularity) :
    ∀ n : ℕ, 3 ≤ n → ¬ KrennGu.Solvable n := by
  rintro n h3 ⟨W, hone, hzero⟩
  have hcard : 4 < Fintype.card (Fin (2 * n)) := by
    rw [Fintype.card_fin]; omega
  obtain ⟨T⟩ := h (Fin (2 * n)) W hcard ⟨hone, hzero⟩
  have hV : ∀ x : Fin (2 * n), (Finset.univ.erase x).Nonempty := by
    intro x
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ x)]
    have : Finset.univ.card = Fintype.card (Fin (2 * n)) := rfl
    omega
  exact CycleCoordinates.no_three_regular_uniform W hone hzero hV hcard T

/-- The same statement in the form the conjecture is usually quoted: no GHZ system in three
colours exists on more than four vertices. -/
theorem no_ghz_above_four (h : ThreeRegularity)
    (V : Type) [Fintype V] [DecidableEq V] (hcard : 4 < Fintype.card V)
    (W : Sym2 (V × Fin 3) → ℂ) : ¬ KrennGu.IsGHZ W := by
  rintro ⟨hone, hzero⟩
  obtain ⟨T⟩ := h V W hcard ⟨hone, hzero⟩
  have hV : ∀ x : V, (Finset.univ.erase x).Nonempty := by
    intro x
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ x)]
    have : (Finset.univ : Finset V).card = Fintype.card V := rfl
    omega
  exact CycleCoordinates.no_three_regular_uniform W hone hzero hV hcard T

/-! ### The hypothesis, stated about degree alone -/

/-- **The one remaining statement, in support terms.**  No site of a GHZ system on more than
four sites has a fourth live partner. -/
def LiveDegreeThree : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (W : Sym2 (V × Fin 3) → ℂ),
    4 < Fintype.card V → KrennGu.IsGHZ W → ∀ u : V, (LiveDegree.liveNbrs W u).card ≤ 3

/-- **The Krenn–Gu conjecture, modulo a degree bound.**  Uniform in the vertex count and free
of any base case; the loop weights, which appear in no matching, are normalised away inside
the proof. -/
theorem krenn_gu_of_liveDegree (h : LiveDegreeThree) :
    ∀ n : ℕ, 3 ≤ n → ¬ KrennGu.Solvable n := by
  rintro n h3 ⟨W, hone, hzero⟩
  have hcard : 4 < Fintype.card (Fin (2 * n)) := by rw [Fintype.card_fin]; omega
  have hone' : ∀ j : Fin 3,
      amplitude (LiveDegree.deloop W) (Amplitude.const (V := Fin (2 * n)) j) ≠ 0 := by
    intro j; rw [LiveDegree.amplitude_deloop]; exact hone j
  have hzero' : ∀ c : Fin (2 * n) → Fin 3, ¬ Amplitude.Monochromatic c →
      amplitude (LiveDegree.deloop W) c = 0 := by
    intro c hc; rw [LiveDegree.amplitude_deloop]; exact hzero c hc
  have hdeg : ∀ u : Fin (2 * n), (LiveDegree.liveNbrs (LiveDegree.deloop W) u).card ≤ 3 := by
    intro u
    rw [LiveDegree.liveNbrs_deloop]
    exact h (Fin (2 * n)) W hcard ⟨hone, hzero⟩ u
  obtain ⟨T⟩ := LiveDegree.threeRegular_of_liveDegree (LiveDegree.deloop W) hone' hzero'
    hcard (fun x a b => LiveDegree.deloop_loop W x a b) hdeg
  have hV : ∀ x : Fin (2 * n), (Finset.univ.erase x).Nonempty := by
    intro x
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ x)]
    have : (Finset.univ : Finset (Fin (2 * n))).card = Fintype.card (Fin (2 * n)) := rfl
    omega
  exact CycleCoordinates.no_three_regular_uniform _ hone' hzero' hV hcard T

end MainTheorem
