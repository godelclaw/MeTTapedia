import Mettapedia.NARS.Bridges.PLN.RevisionWorldModel

/-!
# The finite evidence chart behind NARS count interpretations

Reading a finite binary count pair as a valid NARS value and interpreting that
value back as counts recovers both coordinates. No positive-count premise is
needed for this direction. Reading a NARS value back requires positive
confidence to retain its frequency. The stored PLN prior is ignored by the
NARS readout and is not recovered by either statement.
-/

set_option autoImplicit false

namespace Mettapedia.NARS.Bridges.PLN.FiniteEvidenceChart

open scoped ENNReal
open Mettapedia.NARS.Bridges.PLN.InformationAdjunction
open Mettapedia.NARS.Bridges.PLN.RevisionWorldModel
open Mettapedia.NARS.TruthFunctions
open Mettapedia.PLN.Evidence

/-- Count reconstruction, including the empty count pair. The prior context
is outside this equality and can be arbitrary. -/
theorem counts_round_trip (belief : PLNBelief) (finite : belief.evidence.total ≠ ⊤) :
    toCounts (U belief) = belief.evidence := by
  have positiveFinite : belief.evidence.pos ≠ ⊤ :=
    ne_top_of_le_ne_top finite (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0∞) ≤ belief.evidence.neg))
  have negativeFinite : belief.evidence.neg ≠ ⊤ :=
    ne_top_of_le_ne_top finite (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0∞) ≤ belief.evidence.pos))
  by_cases empty : belief.evidence.total = 0
  · have both : belief.evidence.pos = 0 ∧ belief.evidence.neg = 0 := by
      simpa only [BinaryEvidence.total, add_eq_zero] using empty
    apply BinaryEvidence.ext' <;>
      simp [toCounts, NARSTruthValue.toTV, U, EvidenceTranslation.TV.toEvidence,
        BinaryEvidence.total, both.1, both.2, c2w]
  · have totalNonzero : belief.evidence.total.toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨empty, finite⟩
    have proportion : (U belief).f =
        belief.evidence.pos.toReal / belief.evidence.total.toReal := by
      simp only [U, empty, if_false, ENNReal.toReal_div]
    have weight : c2w (U belief).c = belief.evidence.total.toReal := U_weight_eq_total belief finite
    apply BinaryEvidence.ext'
    · change ENNReal.ofReal ((U belief).f * c2w (U belief).c) = belief.evidence.pos
      rw [weight, proportion, div_mul_cancel₀ _ totalNonzero, ENNReal.ofReal_toReal positiveFinite]
    · change ENNReal.ofReal ((1 - (U belief).f) * c2w (U belief).c) = belief.evidence.neg
      rw [weight, proportion]
      have realTotal : belief.evidence.total.toReal =
          belief.evidence.pos.toReal + belief.evidence.neg.toReal :=
        ENNReal.toReal_add positiveFinite negativeFinite
      have recovery : (1 - belief.evidence.pos.toReal / belief.evidence.total.toReal) *
          belief.evidence.total.toReal = belief.evidence.neg.toReal := by
        calc
          _ = belief.evidence.total.toReal - belief.evidence.pos.toReal := by
            field_simp
          _ = _ := by linarith
      rw [recovery, ENNReal.ofReal_toReal negativeFinite]

private theorem count_readbacks_equal (first second : NARSTruthValue)
    (same : toCounts first = toCounts second) : U (L first) = U (L second) := by
  apply congrArg U
  change PLNBelief.mk (toCounts first) _ = PLNBelief.mk (toCounts second) _
  rw [same]

/-- Confidence is retained by the count chart even when frequency is
unsupported. The frequency reflection law needs its positive guard. -/
theorem toCounts_confidence_congr (first second : NARSTruthValue)
    (same : toCounts first = toCounts second) : first.c = second.c := by
  have confidence := congrArg NARSTruthValue.c (count_readbacks_equal first second same)
  simpa only [U_L_conf_round_trip] using confidence

/-- Positive confidence makes the count interpretation faithful on full
valid NARS values. Unsupported frequencies remain a separate boundary. -/
theorem toCounts_injective_on_supported (first second : NARSTruthValue)
    (firstSupported : 0 < first.c) (secondSupported : 0 < second.c)
    (same : toCounts first = toCounts second) : first = second := by
  have readback := count_readbacks_equal first second same
  have frequency := congrArg NARSTruthValue.f readback
  have confidence := congrArg NARSTruthValue.c readback
  rw [U_L_freq_round_trip first firstSupported, U_L_freq_round_trip second secondSupported] at frequency
  rw [U_L_conf_round_trip first, U_L_conf_round_trip second] at confidence
  cases first
  cases second
  cases frequency
  cases confidence
  rfl

end Mettapedia.NARS.Bridges.PLN.FiniteEvidenceChart
