import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticBasis
import Mathlib.Data.Sym.Card

/-!
# Hypercubic Cartan field census at canonical dimension sixteen

This module defines the standard unpadded monomial carrier
`Sym OrientedPlane 8`: homogeneous degree-eight polynomials in the six
independent components of a two-form in four dimensions.  Since every field
strength has canonical dimension two, this is the derivative-free Cartan
sector of canonical dimension sixteen.

The literal signed `H(4)` action is inherited from the two-form
representation.  Seventeen explicit representatives are the admissible
signed orbits.  A separate generated certificate classifies all 1,287
monomials and is replayed by the Lean kernel.  This sector is an exact finite
census; it is not identified with the full noncommutative `F,D` relation
quotient.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CartanCensus

open SU2LatticeFDCensusNoGo
open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

/-! ## The degree-eight signed carrier -/

abbrev OcticMonomial := Sym OrientedPlane 8

theorem card_octicMonomial : Fintype.card OcticMonomial = 1287 := by
  rw [Sym.card_sym_eq_choose]
  decide

def OcticMonomial.act (h : Hypercubic4)
    (monomial : OcticMonomial) : OcticMonomial :=
  Sym.map (planeEquiv h) monomial

/-- Reflections change tensor signs but not exponent transport. -/
theorem OcticMonomial.act_eq_unsigned (h : Hypercubic4)
    (monomial : OcticMonomial) :
    monomial.act h = monomial.act (unsignedHypercubic h.perm) := by
  rfl

def OcticMonomial.tensorSign
    (h : Hypercubic4) (monomial : OcticMonomial) : ℤ :=
  ((monomial : Multiset OrientedPlane).map (planeTensorSign h)).prod

theorem OcticMonomial.act_compose (left right : Hypercubic4)
    (monomial : OcticMonomial) :
    (monomial.act right).act left =
      monomial.act (Hypercubic4.compose left right) := by
  apply Sym.ext
  simp [OcticMonomial.act, Sym.map, planeEquiv_compose,
    Multiset.map_map]

@[simp] theorem OcticMonomial.act_one (monomial : OcticMonomial) :
    monomial.act Hypercubic4.one = monomial := by
  apply Sym.ext
  simp [OcticMonomial.act, Sym.map, planeEquiv, planeAction_one]

theorem OcticMonomial.act_injective (h : Hypercubic4) :
    Function.Injective (OcticMonomial.act h) := by
  intro left right heq
  have hinverse := congrArg
    (OcticMonomial.act (Hypercubic4.inverse h)) heq
  simpa [OcticMonomial.act_compose] using hinverse

theorem OcticMonomial.tensorSign_compose (left right : Hypercubic4)
    (monomial : OcticMonomial) :
    monomial.tensorSign (Hypercubic4.compose left right) =
      monomial.tensorSign right * (monomial.act right).tensorSign left := by
  exact multiset_tensorSign_compose left right monomial

@[simp] theorem OcticMonomial.tensorSign_one
    (monomial : OcticMonomial) :
    monomial.tensorSign Hypercubic4.one = 1 := by
  unfold OcticMonomial.tensorSign
  have hplane (plane : OrientedPlane) :
      planeTensorSign Hypercubic4.one plane = 1 := by
    simp [planeTensorSign, planeReorderSign, OrientedPlane.ordered]
  simp [hplane]

def IsHypercubicOcticCoefficient
    (coefficients : OcticMonomial → ℚ) : Prop :=
  ∀ h monomial,
    coefficients (monomial.act h) =
      (monomial.tensorSign h : ℚ) * coefficients monomial

/-! ## Seventeen admissible representatives -/

def octicOfPlanes (p0 p1 p2 p3 p4 p5 p6 p7 : OrientedPlane) :
    OcticMonomial :=
  Sym.ofVector ⟨[p0, p1, p2, p3, p4, p5, p6, p7], rfl⟩

def octicRepresentative : Fin 17 → OcticMonomial
  | 0 => octicOfPlanes 5 5 5 5 5 5 5 5
  | 1 => octicOfPlanes 4 4 5 5 5 5 5 5
  | 2 => octicOfPlanes 4 4 4 4 5 5 5 5
  | 3 => octicOfPlanes 3 3 4 4 5 5 5 5
  | 4 => octicOfPlanes 2 2 4 4 5 5 5 5
  | 5 => octicOfPlanes 2 2 3 3 5 5 5 5
  | 6 => octicOfPlanes 2 2 3 3 4 4 5 5
  | 7 => octicOfPlanes 2 2 3 3 3 3 5 5
  | 8 => octicOfPlanes 2 2 3 3 3 3 3 3
  | 9 => octicOfPlanes 2 2 2 2 3 3 3 3
  | 10 => octicOfPlanes 1 2 3 4 5 5 5 5
  | 11 => octicOfPlanes 1 2 3 4 4 4 5 5
  | 12 => octicOfPlanes 1 2 3 4 4 4 4 4
  | 13 => octicOfPlanes 1 2 3 3 3 4 4 4
  | 14 => octicOfPlanes 1 2 2 2 3 3 3 4
  | 15 => octicOfPlanes 1 1 2 2 3 3 4 4
  | 16 => octicOfPlanes 0 1 2 2 3 3 4 5
  | _ => octicOfPlanes 5 5 5 5 5 5 5 5

def InSignedOcticOrbit
    (representative monomial : OcticMonomial) : Prop :=
  ∃ h : Hypercubic4, representative.act h = monomial

def HasNegativeOcticStabilizer (monomial : OcticMonomial) : Prop :=
  ∃ h : Hypercubic4,
    monomial.act h = monomial ∧ monomial.tensorSign h = -1

/-! ## Sparse certificate format -/

inductive OcticCertificate where
  | orbit (coordinate : Fin 17) (permutation : Fin 24)
      (reflectionMask : Fin 16)
  | killed (permutation : Fin 24) (reflectionMask : Fin 16)
deriving DecidableEq

def OcticCertificate.Valid (monomial : OcticMonomial) :
    OcticCertificate → Prop
  | .orbit coordinate permutation reflectionMask =>
      (octicRepresentative coordinate).act
          (decodeHypercubic permutation reflectionMask) = monomial
  | .killed permutation reflectionMask =>
      monomial.act (decodeHypercubic permutation reflectionMask) = monomial ∧
        monomial.tensorSign
          (decodeHypercubic permutation reflectionMask) = -1

instance OcticCertificate.instDecidableValid
    (monomial : OcticMonomial) (certificate : OcticCertificate) :
    Decidable (certificate.Valid monomial) := by
  cases certificate <;> unfold OcticCertificate.Valid <;> infer_instance

/-! ## Transparent monomial code -/

/-- Base-nine code for the six exponents. -/
def octicCode (monomial : OcticMonomial) : Nat :=
  (monomial : Multiset OrientedPlane).count 0 +
    9 * (monomial : Multiset OrientedPlane).count 1 +
    81 * (monomial : Multiset OrientedPlane).count 2 +
    729 * (monomial : Multiset OrientedPlane).count 3 +
    6561 * (monomial : Multiset OrientedPlane).count 4 +
    59049 * (monomial : Multiset OrientedPlane).count 5

theorem baseNine_peel {leftDigit rightDigit leftTail rightTail : Nat}
    (hleft : leftDigit < 9) (hright : rightDigit < 9)
    (hpacked : leftDigit + 9 * leftTail = rightDigit + 9 * rightTail) :
    leftDigit = rightDigit ∧ leftTail = rightTail := by
  have hmod := congrArg (fun value : Nat => value % 9) hpacked
  have hleftMod : leftDigit % 9 = leftDigit := Nat.mod_eq_of_lt hleft
  have hrightMod : rightDigit % 9 = rightDigit := Nat.mod_eq_of_lt hright
  simp [Nat.add_mod, hleftMod, hrightMod] at hmod
  constructor
  · exact hmod
  · omega

/-- The code is injective because an octic exponent is at most eight. -/
theorem octicCode_injective : Function.Injective octicCode := by
  intro left right hcode
  apply Sym.coe_injective
  apply Multiset.ext.mpr
  intro plane
  have hl0 : (left : Multiset OrientedPlane).count 0 ≤ 8 := by
    simpa using Multiset.count_le_card 0 (left : Multiset OrientedPlane)
  have hl1 : (left : Multiset OrientedPlane).count 1 ≤ 8 := by
    simpa using Multiset.count_le_card 1 (left : Multiset OrientedPlane)
  have hl2 : (left : Multiset OrientedPlane).count 2 ≤ 8 := by
    simpa using Multiset.count_le_card 2 (left : Multiset OrientedPlane)
  have hl3 : (left : Multiset OrientedPlane).count 3 ≤ 8 := by
    simpa using Multiset.count_le_card 3 (left : Multiset OrientedPlane)
  have hl4 : (left : Multiset OrientedPlane).count 4 ≤ 8 := by
    simpa using Multiset.count_le_card 4 (left : Multiset OrientedPlane)
  have hl5 : (left : Multiset OrientedPlane).count 5 ≤ 8 := by
    simpa using Multiset.count_le_card 5 (left : Multiset OrientedPlane)
  have hr0 : (right : Multiset OrientedPlane).count 0 ≤ 8 := by
    simpa using Multiset.count_le_card 0 (right : Multiset OrientedPlane)
  have hr1 : (right : Multiset OrientedPlane).count 1 ≤ 8 := by
    simpa using Multiset.count_le_card 1 (right : Multiset OrientedPlane)
  have hr2 : (right : Multiset OrientedPlane).count 2 ≤ 8 := by
    simpa using Multiset.count_le_card 2 (right : Multiset OrientedPlane)
  have hr3 : (right : Multiset OrientedPlane).count 3 ≤ 8 := by
    simpa using Multiset.count_le_card 3 (right : Multiset OrientedPlane)
  have hr4 : (right : Multiset OrientedPlane).count 4 ≤ 8 := by
    simpa using Multiset.count_le_card 4 (right : Multiset OrientedPlane)
  have hr5 : (right : Multiset OrientedPlane).count 5 ≤ 8 := by
    simpa using Multiset.count_le_card 5 (right : Multiset OrientedPlane)
  have hpacked :
      (left : Multiset OrientedPlane).count 0 + 9 *
        ((left : Multiset OrientedPlane).count 1 + 9 *
          ((left : Multiset OrientedPlane).count 2 + 9 *
            ((left : Multiset OrientedPlane).count 3 + 9 *
              ((left : Multiset OrientedPlane).count 4 + 9 *
                (left : Multiset OrientedPlane).count 5)))) =
      (right : Multiset OrientedPlane).count 0 + 9 *
        ((right : Multiset OrientedPlane).count 1 + 9 *
          ((right : Multiset OrientedPlane).count 2 + 9 *
            ((right : Multiset OrientedPlane).count 3 + 9 *
              ((right : Multiset OrientedPlane).count 4 + 9 *
                (right : Multiset OrientedPlane).count 5)))) := by
    unfold octicCode at hcode
    omega
  obtain ⟨h0, htail1⟩ := baseNine_peel (by omega) (by omega) hpacked
  obtain ⟨h1, htail2⟩ := baseNine_peel (by omega) (by omega) htail1
  obtain ⟨h2, htail3⟩ := baseNine_peel (by omega) (by omega) htail2
  obtain ⟨h3, htail4⟩ := baseNine_peel (by omega) (by omega) htail3
  obtain ⟨h4, h5⟩ := baseNine_peel (by omega) (by omega) htail4
  fin_cases plane
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa using h3
  · simpa using h4
  · simpa using h5

end HypercubicDimension16CartanCensus
end YangMills
end QuantumTheory
end Mettapedia
