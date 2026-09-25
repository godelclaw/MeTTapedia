import Mathlib
import FermiKrenn
import OfficialCharTwo
import OfficialConditional

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

/-! ## The heart, with non-Pfaffian live graphs

Combined with the tight-cut reduction (`official_of_heart`), a smallest counterexample now has a
live graph that is non-Pfaffian and has no shore-tight cut keeping five or more sites.  That is,
a non-Pfaffian brick or brace. -/

/-- **The non-Pfaffian heart.**  `Heart`, with the additional hypothesis that the live graph
carries no Pfaffian signs for any order of the sites. -/
def NonPfaffianHeart : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [LinearOrder V] (W : Sym2 (V × Fin 3) → ℂ),
    4 < Fintype.card V → MinimalSupport.IsSupportMinimal W →
    (∀ n : ℕ, 3 ≤ n → 2 * n < Fintype.card V → ¬ KrennGu.Solvable n) →
    (∀ S : Finset V, 5 ≤ S.card → 3 ≤ (Finset.univ \ S).card →
      ¬ KrennTightCut.ShoreTight W S) →
    (∀ (sg : Sym2 V → ℂ) (ε : ℂ), ¬ PfaffianSigns W sg ε) →
    False

/-- **The official conjecture, from the non-Pfaffian heart.**  A heart configuration whose live
graph carries Pfaffian signs is excluded outright (`not_isGHZOver_of_pfaffian`). -/
theorem official_of_nonPfaffianHeart (h : NonPfaffianHeart) : OfficialKrennGu := by
  refine official_of_heart fun V _ _ W hcard hmin hsmall htight => ?_
  classical
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  by_cases hP : ∃ (sg : Sym2 V → ℂ) (ε : ℂ), PfaffianSigns W sg ε
  · obtain ⟨sg, ε, hPs⟩ := hP
    obtain ⟨m, hm⟩ := NoCancellation.even_card_of_isGHZ W hmin.1
    exact not_isGHZOver_of_pfaffian (n := m) (by omega) (by omega) hmin.1 hPs
  · push Not at hP
    exact h V W hcard hmin hsmall htight hP

/-- **The non-Pfaffian heart is an equivalent structural target.** -/
theorem nonPfaffianHeart_iff_official : NonPfaffianHeart ↔ OfficialKrennGu := by
  constructor
  · exact official_of_nonPfaffianHeart
  · intro h V _ _ _ W hcard hmin _ _ _
    exact absurd hmin.1
      (NoCancellation.not_isGHZ_of_not_solvable (notSolvable_of_official h) hcard W)

#print axioms official_of_nonPfaffianHeart
#print axioms nonPfaffianHeart_iff_official

end KrennFermi
