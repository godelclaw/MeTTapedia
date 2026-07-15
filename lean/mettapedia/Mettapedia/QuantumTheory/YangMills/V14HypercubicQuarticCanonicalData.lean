import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticCensus

/-!
# Canonical stars-and-bars data for the dimension-eight quartic census

This module certifies a transparent 126-entry enumeration of homogeneous
quartic monomials in six two-form components.  The base-five code is proved
injective and the table is proved bijective by exact cardinality.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14HypercubicQuarticCensus

open SU2LatticeFDCensusNoGo

/-- Base-five code for the six multiplicities. -/
def quarticCode (monomial : QuarticMonomial) : Nat :=
  (monomial : Multiset OrientedPlane).count 0 +
    5 * (monomial : Multiset OrientedPlane).count 1 +
    25 * (monomial : Multiset OrientedPlane).count 2 +
    125 * (monomial : Multiset OrientedPlane).count 3 +
    625 * (monomial : Multiset OrientedPlane).count 4 +
    3125 * (monomial : Multiset OrientedPlane).count 5

/-- Peel one base-five digit from an equality of packed natural numbers. -/
theorem baseFive_peel {leftDigit rightDigit leftTail rightTail : Nat}
    (hleft : leftDigit < 5) (hright : rightDigit < 5)
    (hpacked : leftDigit + 5 * leftTail = rightDigit + 5 * rightTail) :
    leftDigit = rightDigit ∧ leftTail = rightTail := by
  have hmod := congrArg (fun value : Nat => value % 5) hpacked
  have hleftMod : leftDigit % 5 = leftDigit := Nat.mod_eq_of_lt hleft
  have hrightMod : rightDigit % 5 = rightDigit := Nat.mod_eq_of_lt hright
  simp [Nat.add_mod, Nat.mul_mod, hleftMod, hrightMod] at hmod
  constructor
  · exact hmod
  · omega

/-- The base-five code is injective because every multiplicity is at most four.
This proof is arithmetic, not finite enumeration. -/
theorem quarticCode_injective : Function.Injective quarticCode := by
  intro left right hcode
  apply Sym.coe_injective
  apply Multiset.ext.mpr
  intro plane
  have hl0 : (left : Multiset OrientedPlane).count 0 ≤ 4 := by
    simpa using Multiset.count_le_card 0 (left : Multiset OrientedPlane)
  have hl1 : (left : Multiset OrientedPlane).count 1 ≤ 4 := by
    simpa using Multiset.count_le_card 1 (left : Multiset OrientedPlane)
  have hl2 : (left : Multiset OrientedPlane).count 2 ≤ 4 := by
    simpa using Multiset.count_le_card 2 (left : Multiset OrientedPlane)
  have hl3 : (left : Multiset OrientedPlane).count 3 ≤ 4 := by
    simpa using Multiset.count_le_card 3 (left : Multiset OrientedPlane)
  have hl4 : (left : Multiset OrientedPlane).count 4 ≤ 4 := by
    simpa using Multiset.count_le_card 4 (left : Multiset OrientedPlane)
  have hl5 : (left : Multiset OrientedPlane).count 5 ≤ 4 := by
    simpa using Multiset.count_le_card 5 (left : Multiset OrientedPlane)
  have hr0 : (right : Multiset OrientedPlane).count 0 ≤ 4 := by
    simpa using Multiset.count_le_card 0 (right : Multiset OrientedPlane)
  have hr1 : (right : Multiset OrientedPlane).count 1 ≤ 4 := by
    simpa using Multiset.count_le_card 1 (right : Multiset OrientedPlane)
  have hr2 : (right : Multiset OrientedPlane).count 2 ≤ 4 := by
    simpa using Multiset.count_le_card 2 (right : Multiset OrientedPlane)
  have hr3 : (right : Multiset OrientedPlane).count 3 ≤ 4 := by
    simpa using Multiset.count_le_card 3 (right : Multiset OrientedPlane)
  have hr4 : (right : Multiset OrientedPlane).count 4 ≤ 4 := by
    simpa using Multiset.count_le_card 4 (right : Multiset OrientedPlane)
  have hr5 : (right : Multiset OrientedPlane).count 5 ≤ 4 := by
    simpa using Multiset.count_le_card 5 (right : Multiset OrientedPlane)
  have hpacked :
      (left : Multiset OrientedPlane).count 0 + 5 *
        ((left : Multiset OrientedPlane).count 1 + 5 *
          ((left : Multiset OrientedPlane).count 2 + 5 *
            ((left : Multiset OrientedPlane).count 3 + 5 *
              ((left : Multiset OrientedPlane).count 4 + 5 *
                (left : Multiset OrientedPlane).count 5)))) =
      (right : Multiset OrientedPlane).count 0 + 5 *
        ((right : Multiset OrientedPlane).count 1 + 5 *
          ((right : Multiset OrientedPlane).count 2 + 5 *
            ((right : Multiset OrientedPlane).count 3 + 5 *
              ((right : Multiset OrientedPlane).count 4 + 5 *
                (right : Multiset OrientedPlane).count 5)))) := by
    unfold quarticCode at hcode
    omega
  obtain ⟨h0, htail1⟩ := baseFive_peel (by omega) (by omega) hpacked
  obtain ⟨h1, htail2⟩ := baseFive_peel (by omega) (by omega) htail1
  obtain ⟨h2, htail3⟩ := baseFive_peel (by omega) (by omega) htail2
  obtain ⟨h3, htail4⟩ := baseFive_peel (by omega) (by omega) htail3
  obtain ⟨h4, h5⟩ := baseFive_peel (by omega) (by omega) htail4
  fin_cases plane
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa using h3
  · simpa using h4
  · simpa using h5

/-- The 126 valid base-five codes, in increasing order. -/
def validQuarticCodes : List Nat := [
  4, 8, 12, 16, 20, 28, 32, 36, 40, 52, 56, 60,
  76, 80, 100, 128, 132, 136, 140, 152, 156, 160, 176, 180,
  200, 252, 256, 260, 276, 280, 300, 376, 380, 400, 500, 628,
  632, 636, 640, 652, 656, 660, 676, 680, 700, 752, 756, 760,
  776, 780, 800, 876, 880, 900, 1000, 1252, 1256, 1260, 1276, 1280,
  1300, 1376, 1380, 1400, 1500, 1876, 1880, 1900, 2000, 2500, 3128, 3132,
  3136, 3140, 3152, 3156, 3160, 3176, 3180, 3200, 3252, 3256, 3260, 3276,
  3280, 3300, 3376, 3380, 3400, 3500, 3752, 3756, 3760, 3776, 3780, 3800,
  3876, 3880, 3900, 4000, 4376, 4380, 4400, 4500, 5000, 6252, 6256, 6260,
  6276, 6280, 6300, 6376, 6380, 6400, 6500, 6876, 6880, 6900, 7000, 7500,
  9376, 9380, 9400, 9500, 10000, 12500]

theorem validQuarticCodes_length : validQuarticCodes.length = 126 := by
  set_option maxRecDepth 10000 in
    decide

theorem validQuarticCodes_nodup : validQuarticCodes.Nodup := by
  set_option maxRecDepth 10000 in
    decide

def quarticCodeIndex (index : Fin 126) : Fin validQuarticCodes.length :=
  ⟨index.1, by simpa [validQuarticCodes_length] using index.2⟩

def canonicalQuarticCode (index : Fin 126) : Nat :=
  validQuarticCodes.get (quarticCodeIndex index)

/-- The 126 canonical stars-and-bars monomials. -/
def canonicalQuartic : Fin 126 → QuarticMonomial
  | 0 => quarticOfPlanes 0 0 0 0
  | 1 => quarticOfPlanes 0 0 0 1
  | 2 => quarticOfPlanes 0 0 1 1
  | 3 => quarticOfPlanes 0 1 1 1
  | 4 => quarticOfPlanes 1 1 1 1
  | 5 => quarticOfPlanes 0 0 0 2
  | 6 => quarticOfPlanes 0 0 1 2
  | 7 => quarticOfPlanes 0 1 1 2
  | 8 => quarticOfPlanes 1 1 1 2
  | 9 => quarticOfPlanes 0 0 2 2
  | 10 => quarticOfPlanes 0 1 2 2
  | 11 => quarticOfPlanes 1 1 2 2
  | 12 => quarticOfPlanes 0 2 2 2
  | 13 => quarticOfPlanes 1 2 2 2
  | 14 => quarticOfPlanes 2 2 2 2
  | 15 => quarticOfPlanes 0 0 0 3
  | 16 => quarticOfPlanes 0 0 1 3
  | 17 => quarticOfPlanes 0 1 1 3
  | 18 => quarticOfPlanes 1 1 1 3
  | 19 => quarticOfPlanes 0 0 2 3
  | 20 => quarticOfPlanes 0 1 2 3
  | 21 => quarticOfPlanes 1 1 2 3
  | 22 => quarticOfPlanes 0 2 2 3
  | 23 => quarticOfPlanes 1 2 2 3
  | 24 => quarticOfPlanes 2 2 2 3
  | 25 => quarticOfPlanes 0 0 3 3
  | 26 => quarticOfPlanes 0 1 3 3
  | 27 => quarticOfPlanes 1 1 3 3
  | 28 => quarticOfPlanes 0 2 3 3
  | 29 => quarticOfPlanes 1 2 3 3
  | 30 => quarticOfPlanes 2 2 3 3
  | 31 => quarticOfPlanes 0 3 3 3
  | 32 => quarticOfPlanes 1 3 3 3
  | 33 => quarticOfPlanes 2 3 3 3
  | 34 => quarticOfPlanes 3 3 3 3
  | 35 => quarticOfPlanes 0 0 0 4
  | 36 => quarticOfPlanes 0 0 1 4
  | 37 => quarticOfPlanes 0 1 1 4
  | 38 => quarticOfPlanes 1 1 1 4
  | 39 => quarticOfPlanes 0 0 2 4
  | 40 => quarticOfPlanes 0 1 2 4
  | 41 => quarticOfPlanes 1 1 2 4
  | 42 => quarticOfPlanes 0 2 2 4
  | 43 => quarticOfPlanes 1 2 2 4
  | 44 => quarticOfPlanes 2 2 2 4
  | 45 => quarticOfPlanes 0 0 3 4
  | 46 => quarticOfPlanes 0 1 3 4
  | 47 => quarticOfPlanes 1 1 3 4
  | 48 => quarticOfPlanes 0 2 3 4
  | 49 => quarticOfPlanes 1 2 3 4
  | 50 => quarticOfPlanes 2 2 3 4
  | 51 => quarticOfPlanes 0 3 3 4
  | 52 => quarticOfPlanes 1 3 3 4
  | 53 => quarticOfPlanes 2 3 3 4
  | 54 => quarticOfPlanes 3 3 3 4
  | 55 => quarticOfPlanes 0 0 4 4
  | 56 => quarticOfPlanes 0 1 4 4
  | 57 => quarticOfPlanes 1 1 4 4
  | 58 => quarticOfPlanes 0 2 4 4
  | 59 => quarticOfPlanes 1 2 4 4
  | 60 => quarticOfPlanes 2 2 4 4
  | 61 => quarticOfPlanes 0 3 4 4
  | 62 => quarticOfPlanes 1 3 4 4
  | 63 => quarticOfPlanes 2 3 4 4
  | 64 => quarticOfPlanes 3 3 4 4
  | 65 => quarticOfPlanes 0 4 4 4
  | 66 => quarticOfPlanes 1 4 4 4
  | 67 => quarticOfPlanes 2 4 4 4
  | 68 => quarticOfPlanes 3 4 4 4
  | 69 => quarticOfPlanes 4 4 4 4
  | 70 => quarticOfPlanes 0 0 0 5
  | 71 => quarticOfPlanes 0 0 1 5
  | 72 => quarticOfPlanes 0 1 1 5
  | 73 => quarticOfPlanes 1 1 1 5
  | 74 => quarticOfPlanes 0 0 2 5
  | 75 => quarticOfPlanes 0 1 2 5
  | 76 => quarticOfPlanes 1 1 2 5
  | 77 => quarticOfPlanes 0 2 2 5
  | 78 => quarticOfPlanes 1 2 2 5
  | 79 => quarticOfPlanes 2 2 2 5
  | 80 => quarticOfPlanes 0 0 3 5
  | 81 => quarticOfPlanes 0 1 3 5
  | 82 => quarticOfPlanes 1 1 3 5
  | 83 => quarticOfPlanes 0 2 3 5
  | 84 => quarticOfPlanes 1 2 3 5
  | 85 => quarticOfPlanes 2 2 3 5
  | 86 => quarticOfPlanes 0 3 3 5
  | 87 => quarticOfPlanes 1 3 3 5
  | 88 => quarticOfPlanes 2 3 3 5
  | 89 => quarticOfPlanes 3 3 3 5
  | 90 => quarticOfPlanes 0 0 4 5
  | 91 => quarticOfPlanes 0 1 4 5
  | 92 => quarticOfPlanes 1 1 4 5
  | 93 => quarticOfPlanes 0 2 4 5
  | 94 => quarticOfPlanes 1 2 4 5
  | 95 => quarticOfPlanes 2 2 4 5
  | 96 => quarticOfPlanes 0 3 4 5
  | 97 => quarticOfPlanes 1 3 4 5
  | 98 => quarticOfPlanes 2 3 4 5
  | 99 => quarticOfPlanes 3 3 4 5
  | 100 => quarticOfPlanes 0 4 4 5
  | 101 => quarticOfPlanes 1 4 4 5
  | 102 => quarticOfPlanes 2 4 4 5
  | 103 => quarticOfPlanes 3 4 4 5
  | 104 => quarticOfPlanes 4 4 4 5
  | 105 => quarticOfPlanes 0 0 5 5
  | 106 => quarticOfPlanes 0 1 5 5
  | 107 => quarticOfPlanes 1 1 5 5
  | 108 => quarticOfPlanes 0 2 5 5
  | 109 => quarticOfPlanes 1 2 5 5
  | 110 => quarticOfPlanes 2 2 5 5
  | 111 => quarticOfPlanes 0 3 5 5
  | 112 => quarticOfPlanes 1 3 5 5
  | 113 => quarticOfPlanes 2 3 5 5
  | 114 => quarticOfPlanes 3 3 5 5
  | 115 => quarticOfPlanes 0 4 5 5
  | 116 => quarticOfPlanes 1 4 5 5
  | 117 => quarticOfPlanes 2 4 5 5
  | 118 => quarticOfPlanes 3 4 5 5
  | 119 => quarticOfPlanes 4 4 5 5
  | 120 => quarticOfPlanes 0 5 5 5
  | 121 => quarticOfPlanes 1 5 5 5
  | 122 => quarticOfPlanes 2 5 5 5
  | 123 => quarticOfPlanes 3 5 5 5
  | 124 => quarticOfPlanes 4 5 5 5
  | 125 => quarticOfPlanes 5 5 5 5
  | _ => quarticOfPlanes 5 5 5 5

/-- The table of monomials and the table of codes agree entrywise. -/
theorem quarticCode_canonical :
    ∀ index : Fin 126,
      quarticCode (canonicalQuartic index) = canonicalQuarticCode index := by
  intro index
  fin_cases index <;> decide

theorem canonicalQuarticCode_injective :
    Function.Injective canonicalQuarticCode := by
  intro left right heq
  have hindex : quarticCodeIndex left = quarticCodeIndex right :=
    validQuarticCodes_nodup.injective_get heq
  exact Fin.ext (congrArg Fin.val hindex)

theorem canonicalQuartic_injective :
    Function.Injective canonicalQuartic := by
  intro left right heq
  apply canonicalQuarticCode_injective
  rw [← quarticCode_canonical, ← quarticCode_canonical, heq]

theorem canonicalQuartic_bijective :
    Function.Bijective canonicalQuartic := by
  apply (Fintype.bijective_iff_injective_and_card canonicalQuartic).2
  refine ⟨canonicalQuartic_injective, ?_⟩
  simp [card_quarticMonomial]

theorem canonicalQuartic_surjective :
    Function.Surjective canonicalQuartic :=
  canonicalQuartic_bijective.2


end V14HypercubicQuarticCensus
end YangMills
end QuantumTheory
end Mettapedia
