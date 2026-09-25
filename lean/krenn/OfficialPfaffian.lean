import Mathlib
import FermiKrenn
import OfficialCharTwo

/-!
# The Krenn–Gu conjecture for Pfaffian live graphs

Over every infinite field, in particular ℂ, the official equation system on `2n ≥ 6`
vertices has no solution whose live graph carries Pfaffian signs (`KrennFermi.PfaffianSigns`).
Such signs make every perfect matching of the live pairs count with the same total sign.

By Kasteleyn's theorem, not formalized here, every planar graph carries such signs.  The theorem
therefore covers every solution supported on a planar graph, including multiple entries per pair
and bicoloured entries.

The argument: with Pfaffian signs the matching sums become Pfaffians
(`KrennFermi.pfSum_signW`), for which contraction at a live pair is exact in every characteristic.
A GHZ system descends to six sites, and six sites are impossible (`KrennFermi.krennGu_fermi`).
-/

namespace KrennFermi

open Amplitude MatchingSum MonochromaticQuantumGraph GeneralOfficialBridge KrennCharTwo

/-- **Krenn–Gu for Pfaffian live graphs, in the official formulation.**  Over an infinite field,
no official solution on `2n ≥ 6` vertices in three colours has a live graph carrying Pfaffian
signs. -/
theorem krennGu_pfaffian (F : Type) [Field F] [Infinite F] :
    ∀ n : ℕ, 3 ≤ n → ∀ W : WeightsN (2 * n) 3 F, EqSystemN (2 * n) 3 W →
      ∀ (sg : Sym2 (Fin (2 * n)) → F) (ε : F), ¬ PfaffianSigns (symWeight W) sg ε := by
  intro n hn W hW sg ε hP
  exact not_isGHZOver_of_pfaffian hn (Fintype.card_fin _)
    (isGHZOver_of_eqSystemN (by omega) hW) hP

/-- **Over ℂ.** -/
theorem krennGu_pfaffian_complex :
    ∀ n : ℕ, 3 ≤ n → ∀ W : WeightsN (2 * n) 3 ℂ, EqSystemN (2 * n) 3 W →
      ∀ (sg : Sym2 (Fin (2 * n)) → ℂ) (ε : ℂ), ¬ PfaffianSigns (symWeight W) sg ε :=
  krennGu_pfaffian ℂ

#print axioms krennGu_pfaffian_complex

end KrennFermi
