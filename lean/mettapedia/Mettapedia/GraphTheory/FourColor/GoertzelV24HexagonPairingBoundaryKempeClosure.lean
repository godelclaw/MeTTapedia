import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPairingKempeCertificateRedBlue
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPairingKempeCertificateRedPurple
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPairingKempeCertificateBluePurple

/-!
# Certified boundary for target-aware hexagon pairing reductions

The core module proves the generic parity law and verifies the Boolean decoder
for noncrossing boundary Kempe matchings.  Three separate modules check the
flat finite certificate, one colour pair at a time, so each kernel computation
has a bounded memory footprint.  This assembly exports the mathematical
conclusion: parity plus this abstract Kempe closure still does not force any
of the five planar pairing caps.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelV24HexagonPairingBoundaryKempeClosure

open GoertzelV24HexagonPairingTargetAwareBoundary

private theorem allSixCandidateCheck_eq_true (pair : TaitColorPair) :
    allSixCandidateCheck pair = true := by
  cases pair
  · exact allSixCandidateCheck_redBlue
  · exact allSixCandidateCheck_redPurple
  · exact allSixCandidateCheck_bluePurple

/-- The five Catalan candidates suffice for every word and colour pair in the
parity adversary. -/
theorem parityAdversary_certifiedPattern :
    ∀ word ∈ parityAdversary, ∀ pair : TaitColorPair,
      CandidateKempeWitness parityAdversary word pair
        (certifiedPattern word pair) := by
  intro word hword pair
  rw [← explicitWord_of_word word] at hword ⊢
  have hall : allSixCandidateCheck pair = true :=
    allSixCandidateCheck_eq_true pair
  have hrow := candidateRow_eq_true pair
    (word 0) (word 1) (word 2) (word 3) (word 4) (word 5) hall
  have hbool :
      candidateKempeWitnessBool parityAdversaryBool
        (explicitWord (word 0) (word 1) (word 2) (word 3) (word 4) (word 5)) pair
        (certifiedPattern
          (explicitWord (word 0) (word 1) (word 2) (word 3) (word 4) (word 5)) pair) = true := by
    have hwordBool :
        parityAdversaryBool
          (explicitWord (word 0) (word 1) (word 2) (word 3) (word 4) (word 5)) = true :=
      (parityAdversaryBool_eq_true_iff _).2 hword
    simpa [candidateRow, hwordBool] using hrow
  exact (candidateKempeWitnessBool_eq_true_iff
    parityAdversary parityAdversaryBool parityAdversaryBool_eq_true_iff
    (explicitWord (word 0) (word 1) (word 2) (word 3) (word 4) (word 5)) pair
    (certifiedPattern
      (explicitWord (word 0) (word 1) (word 2) (word 3) (word 4) (word 5)) pair)).1 hbool

/-- **Parity plus boundary Kempe closure still does not rescue pairing
reduction.**  The entire 120-word parity adversary is closed under the
noncrossing component switches above. -/
theorem parityAdversary_boundaryKempeClosed :
    BoundaryKempeClosed parityAdversary := by
  intro word hword pair
  refine ⟨candidateMate word pair (certifiedPattern word pair), ?_⟩
  simpa [CandidateKempeWitness] using
    parityAdversary_certifiedPattern word hword pair

end GoertzelV24HexagonPairingBoundaryKempeClosure
end Mettapedia.GraphTheory.FourColor
