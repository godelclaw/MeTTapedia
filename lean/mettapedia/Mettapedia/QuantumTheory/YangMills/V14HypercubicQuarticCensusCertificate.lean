import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticWitnessBlock0
import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticWitnessBlock1
import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticWitnessBlock2
import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticWitnessBlock3
import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticWitnessBlock4
import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticWitnessBlock5
import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticStabilizer0
import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticStabilizer1
import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticStabilizer2
import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticStabilizer3

/-!
# Sparse certificate for the dimension-eight hypercubic quartic census

This companion module separates the 126-entry stars-and-bars enumeration and
its supplied orbit witnesses from the reusable hypercubic action kernel.
Every entry is checked in Lean; no existential group search is trusted.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14HypercubicQuarticCensus

open V14HypercubicFDCensus

/-- Kernel check of the 126 supplied witnesses.  There is no group search and
no quotient enumeration in this theorem. -/
theorem canonicalQuarticCertificate_valid :
    ∀ index : Fin 126,
      (canonicalQuarticCertificate index).Valid (canonicalQuartic index) := by
  intro index
  by_cases h0 : index.1 < 21
  · let entry : Fin 21 := ⟨index.1, h0⟩
    have valid := canonicalQuarticCertificate_valid_block0 entry
    have hindex : quarticWitnessBlockIndex 0 (by decide) entry = index := by
      apply Fin.ext
      simp [quarticWitnessBlockIndex, entry]
    simpa only [hindex] using valid
  by_cases h1 : index.1 < 42
  · let entry : Fin 21 := ⟨index.1 - 21, by omega⟩
    have valid := canonicalQuarticCertificate_valid_block1 entry
    have hindex : quarticWitnessBlockIndex 21 (by decide) entry = index := by
      apply Fin.ext
      simp [quarticWitnessBlockIndex, entry]
      omega
    simpa only [hindex] using valid
  by_cases h2 : index.1 < 63
  · let entry : Fin 21 := ⟨index.1 - 42, by omega⟩
    have valid := canonicalQuarticCertificate_valid_block2 entry
    have hindex : quarticWitnessBlockIndex 42 (by decide) entry = index := by
      apply Fin.ext
      simp [quarticWitnessBlockIndex, entry]
      omega
    simpa only [hindex] using valid
  by_cases h3 : index.1 < 84
  · let entry : Fin 21 := ⟨index.1 - 63, by omega⟩
    have valid := canonicalQuarticCertificate_valid_block3 entry
    have hindex : quarticWitnessBlockIndex 63 (by decide) entry = index := by
      apply Fin.ext
      simp [quarticWitnessBlockIndex, entry]
      omega
    simpa only [hindex] using valid
  by_cases h4 : index.1 < 105
  · let entry : Fin 21 := ⟨index.1 - 84, by omega⟩
    have valid := canonicalQuarticCertificate_valid_block4 entry
    have hindex : quarticWitnessBlockIndex 84 (by decide) entry = index := by
      apply Fin.ext
      simp [quarticWitnessBlockIndex, entry]
      omega
    simpa only [hindex] using valid
  · let entry : Fin 21 := ⟨index.1 - 105, by omega⟩
    have valid := canonicalQuarticCertificate_valid_block5 entry
    have hindex : quarticWitnessBlockIndex 105 (by decide) entry = index := by
      apply Fin.ext
      simp [quarticWitnessBlockIndex, entry]
      omega
    simpa only [hindex] using valid


/-- Every one of the 126 monomials has a concrete positive-orbit or
negative-stabilizer certificate. -/
theorem quartic_signedOrbit_classification :
    ∀ monomial : QuarticMonomial,
      (∃ coordinate : Fin 4,
        InSignedOrbit (quarticRepresentative coordinate) monomial) ∨
      HasNegativeStabilizer monomial := by
  intro monomial
  obtain ⟨index, rfl⟩ := canonicalQuartic_surjective monomial
  have valid := canonicalQuarticCertificate_valid index
  generalize certificateEquation :
    canonicalQuarticCertificate index = certificate at valid
  cases certificate with
  | orbit coordinate permutation reflectionMask =>
      left
      exact ⟨coordinate, decodeHypercubic permutation reflectionMask, valid⟩
  | killed permutation reflectionMask =>
      right
      exact ⟨decodeHypercubic permutation reflectionMask, valid⟩

/-- The four admissible orbits are pairwise distinct.  Reflections are erased
before the finite check because exponent transport depends only on the 24
unsigned coordinate permutations. -/
theorem quartic_representative_orbits_disjoint :
    ∀ left right : Fin 4,
      InSignedOrbit (quarticRepresentative left)
          (quarticRepresentative right) →
        left = right := by
  simp only [InSignedOrbit]
  intro left right htransport
  obtain ⟨h, hh⟩ := htransport
  have unsignedCheck : ∀ left right : Fin 4,
      ∀ permutation : Equiv.Perm Axis,
        (quarticRepresentative left).act
            (unsignedHypercubic permutation) = quarticRepresentative right →
          left = right := by
    set_option maxRecDepth 10000 in
      decide
  apply unsignedCheck left right h.perm
  exact (QuarticMonomial.act_eq_unsigned h
    (quarticRepresentative left)).symm.trans hh

/-- Every stabilizer of an admissible representative has positive tensor
sign.  Hence transport signs inside one admissible orbit are consistent. -/
theorem quartic_representative_stabilizer_positive :
    ∀ coordinate : Fin 4, ∀ h : Hypercubic4,
      (quarticRepresentative coordinate).act h =
          quarticRepresentative coordinate →
        (quarticRepresentative coordinate).tensorSign h = 1 := by
  intro coordinate
  fin_cases coordinate
  · exact quartic_representative_0_stabilizer_positive
  · exact quartic_representative_1_stabilizer_positive
  · exact quartic_representative_2_stabilizer_positive
  · exact quartic_representative_3_stabilizer_positive


end V14HypercubicQuarticCensus
end YangMills
end QuantumTheory
end Mettapedia
