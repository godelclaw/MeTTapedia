import Mettapedia.PLN.Evidence.RevisionMemory
import Mettapedia.NARS.Bridges.PLN.LedgerCountInterpretation

/-!
# The canonical finite NARS chart retains revision memory

The established count chart is injective, including at zero counts, and so
retains exactly the fresh-observation memory characterized by the PLN
revision theorem. This concerns the canonical finite chart with its fixed
unit evidence scale. Arbitrary zero-confidence frequencies and path-scoped
inference beliefs are outside this identification.
-/

set_option autoImplicit false

namespace Mettapedia.NARS.Bridges.PLN.RevisionMemory

open Mettapedia.PLN.Evidence.RevisionMemory
open Mettapedia.Logic.EvidenceStateInsufficiency
open Mettapedia.PLN.Evidence.CountRegimes
open Mettapedia.NARS.Bridges.PLN.LedgerCountInterpretation
open Mettapedia.NARS.Bridges.PLN.RevisionWorldModel
open Mettapedia.GSLT.TaskRelativeMemory

theorem fromCounts_injective : Function.Injective fromCounts := by
  intro first second same
  apply sampleEmbedding_injective
  simpa only [fromCounts_exact] using congrArg toCounts same

theorem chart_eq_iff_future_strengths (first second : Counts) :
    fromCounts (Fresh.sampleCounts first) = fromCounts (Fresh.sampleCounts second) ↔
      profile Counts.revise Fresh.observe first = profile Counts.revise Fresh.observe second := by
  rw [Fresh.profile_eq_iff_counts]
  exact fromCounts_injective.eq_iff.trans Fresh.countsEquiv.injective.eq_iff

/-- Chart revision agrees with the fresh-observation count update. -/
theorem chart_revision_counts (counts : Counts) (positive : Bool) :
    toCounts (coreState (fromCounts (Fresh.sampleCounts counts))
      (fromCounts (Mettapedia.PLN.WorldModel.EvidenceSpaces.sampleEvidence id positive))) =
        sampleEmbedding (Fresh.sampleCounts (counts.revise positive)) := by
  rw [core_revision_counts, Fresh.sampleCounts_revise]

theorem chart_frequency_nonempty (counts : Counts) (present : counts.total ≠ 0) :
    (fromCounts (Fresh.sampleCounts counts)).f = (counts.strength : ℝ) := by
  have nonzero : (sampleEmbedding (Fresh.sampleCounts counts)).total ≠ 0 := by
    rw [sampleEmbedding_total, Fresh.sampleCounts_total]
    exact_mod_cast present
  rw [← Fresh.binary_strength, Mettapedia.PLN.Evidence.BinaryEvidence.toStrength, if_neg nonzero]
  simp only [fromCounts, Mettapedia.NARS.Bridges.PLN.InformationAdjunction.U, nonzero, if_false]

/-- An empty canonical chart uses frequency one half, not the rational fixture's zero. -/
theorem empty_chart_frequency : (fromCounts (Fresh.sampleCounts ⟨0, 0⟩)).f = 1 / 2 := by
  norm_num [fromCounts, Mettapedia.NARS.Bridges.PLN.InformationAdjunction.U,
    sampleEmbedding_total, Fresh.sampleCounts_total, Counts.total]

theorem chart_confidence (counts : Counts) :
    (fromCounts (Fresh.sampleCounts counts)).c =
      (counts.total : ℝ) / ((counts.total : ℝ) + 1) := by
  simp only [fromCounts, Mettapedia.NARS.Bridges.PLN.InformationAdjunction.U,
    sampleEmbedding_total, Fresh.sampleCounts_total, ENNReal.toReal_div,
    ENNReal.toReal_add (ENNReal.natCast_ne_top _) ENNReal.one_ne_top,
    ENNReal.toReal_natCast, ENNReal.toReal_one]

theorem revised_total_positive (counts : Counts) (positive : Bool) :
    0 < (counts.revise positive).total := by
  cases positive <;> simp only [Counts.revise, Bool.false_eq_true, if_false, if_true, Counts.total] <;> omega

/-- The actual NARS core update agrees on full canonical chart values. -/
theorem chart_revision (counts : Counts) (positive : Bool) :
    coreState (fromCounts (Fresh.sampleCounts counts))
        (fromCounts (Mettapedia.PLN.WorldModel.EvidenceSpaces.sampleEvidence id positive)) =
      fromCounts (Fresh.sampleCounts (counts.revise positive)) := by
  have same := (chart_revision_counts counts positive).trans (fromCounts_exact _).symm
  have targetPositive : 0 < (fromCounts (Fresh.sampleCounts (counts.revise positive))).c := by
    rw [chart_confidence]
    exact div_pos (by exact_mod_cast revised_total_positive counts positive) (by positivity)
  apply FiniteEvidenceChart.toCounts_injective_on_supported _ _ _ targetPositive same
  rw [FiniteEvidenceChart.toCounts_confidence_congr _ _ same]
  exact targetPositive

noncomputable def chartObserve (_ : Unit) (counts : Counts) : ℝ := (fromCounts (Fresh.sampleCounts counts)).f

/-- Recursive realization through the actual core revision, with the empty-frequency convention retained. -/
noncomputable def chartRealization :
    Realization Counts.revise chartObserve (fun counts => fromCounts (Fresh.sampleCounts counts)) where
  update truth positive := coreState truth
    (fromCounts (Mettapedia.PLN.WorldModel.EvidenceSpaces.sampleEvidence id positive))
  read _ truth := truth.f
  update_agrees := chart_revision
  read_agrees _ _ := rfl

theorem chart_profile_eq_iff_counts (first second : Counts) :
    profile Counts.revise chartObserve first = profile Counts.revise chartObserve second ↔ first = second := by
  constructor
  · intro same
    apply Fresh.probes_injective
    have probe (positive : Bool) : (first.revise positive).strength = (second.revise positive).strength := by
      have equal := congrFun (congrFun same [positive]) ()
      change (fromCounts (Fresh.sampleCounts (first.revise positive))).f =
        (fromCounts (Fresh.sampleCounts (second.revise positive))).f at equal
      rw [chart_frequency_nonempty _ (Nat.ne_of_gt (revised_total_positive _ _)),
        chart_frequency_nonempty _ (Nat.ne_of_gt (revised_total_positive _ _))] at equal
      exact_mod_cast equal
    exact Prod.ext (probe true) (probe false)
  · rintro rfl
    rfl

end Mettapedia.NARS.Bridges.PLN.RevisionMemory
