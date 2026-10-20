import Mettapedia.NARS.Bridges.PLN.SecondOrderProbability
import Mettapedia.NARS.Evidence.EvidenceScopeIncoherence

/-!
# NARS core revision: valid values, counts, and retained paths

The evidence-additive core preserves valid truth values and transports to
addition of the existing binary counts. Source disjointness licenses using
that algebra on two evidence bodies; it is not a statistical independence
assumption. Candidate constructors retain the complete histories and scopes.
The capped runtime revision has a separate, observably different meaning.
-/

set_option autoImplicit false

namespace Mettapedia.NARS.Bridges.PLN.RevisionSemantics

open Mettapedia.NARS.TruthFunctions
open Mettapedia.NARS.Bridges.PLN.SecondOrderProbability
open Mettapedia.NARS.Evidence.EvidenceScopeIncoherence
open Mettapedia.NARS.Evidence.EvidenceScopeIncoherence.PathScopedBelief
open Mettapedia.PLN.Evidence

/-- The core's zero-weight convention also gives a valid truth value. -/
theorem core_valid (first second : TV) (firstValid : IsProbTV first)
    (secondValid : IsProbTV second) : IsProbTV (truthRevisionCore first second) := by
  have leftNonneg : 0 ≤ c2w first.c := div_nonneg firstValid.c_nonneg
    (le_of_lt (sub_pos.mpr firstValid.c_lt_one))
  have rightNonneg : 0 ≤ c2w second.c := div_nonneg secondValid.c_nonneg
    (le_of_lt (sub_pos.mpr secondValid.c_lt_one))
  have totalNonneg := add_nonneg leftNonneg rightNonneg
  have numeratorNonneg := add_nonneg (mul_nonneg leftNonneg firstValid.f_nonneg)
    (mul_nonneg rightNonneg secondValid.f_nonneg)
  have numeratorLe : c2w first.c * first.f + c2w second.c * second.f ≤
      c2w first.c + c2w second.c := by
    nlinarith [firstValid.f_le_one, secondValid.f_le_one]
  unfold IsProbTV truthRevisionCore w2c
  refine ⟨div_nonneg numeratorNonneg totalNonneg, ?_,
    div_nonneg totalNonneg (by linarith), ?_⟩
  · by_cases empty : c2w first.c + c2w second.c = 0
    · simp [empty]
    · exact (div_le_one (lt_of_le_of_ne totalNonneg (Ne.symm empty))).mpr numeratorLe
  · exact (div_lt_one (by linarith)).mpr (by linarith)

/-- Reuse the established count/prior interpretation, including the zero
weight branch. No approximation or runtime confidence cap is applied. -/
theorem core_counts (first second : TV) (firstValid : IsProbTV first)
    (secondValid : IsProbTV second) :
    EvidenceTranslation.TV.toEvidence (truthRevisionCore first second) =
      EvidenceTranslation.TV.toEvidence first + EvidenceTranslation.TV.toEvidence second := by
  rw [← toEvidenceWithK_one_eq_bridge_toEvidence _ (core_valid first second firstValid secondValid),
    truthRevisionCore_toEvidence first second firstValid secondValid,
    toEvidenceWithK_one_eq_bridge_toEvidence first firstValid,
    toEvidenceWithK_one_eq_bridge_toEvidence second secondValid]

variable {Statement Source : Type*} [DecidableEq Source]

theorem revisionCandidate_eq_licensed
    (beliefs : Resolution.CompetingBeliefs (Statement := Statement) (EvidenceId := Source))
    (licensed : beliefs.RevisionLicensed) :
    revisionCandidate beliefs.left beliefs.right = Resolution.revise beliefs licensed := rfl

theorem choiceCandidate_eq_existing
    (beliefs : Resolution.CompetingBeliefs (Statement := Statement) (EvidenceId := Source)) :
    choiceCandidate beliefs.left beliefs.right = Resolution.chooseMoreConfident beliefs := rfl

@[simp] theorem revisionCandidate_scope (first second : PathScopedBelief Statement Source) :
    (revisionCandidate first second).scope = first.scope ∪ second.scope := rfl

@[simp] theorem revisionCandidate_steps (first second : PathScopedBelief Statement Source) :
    (revisionCandidate first second).path.steps =
      first.path.steps ++ second.path.steps ++ [.revision first.statement] := rfl

theorem choiceCandidate_left (first second : PathScopedBelief Statement Source)
    (confidence : second.truth.c ≤ first.truth.c) : choiceCandidate first second = first := by
  simp [choiceCandidate, not_lt.mpr confidence]

theorem choiceCandidate_right (first second : PathScopedBelief Statement Source)
    (confidence : first.truth.c < second.truth.c) : choiceCandidate first second = second := by
  simp [choiceCandidate, confidence]

namespace Controls

/-- A runtime cap is an actual change of evidence, not an exact interpretation
of core revision. Each input has evidence weight 99; the capped result has 99. -/
theorem capped_revision_loses_counts :
    let truth : TV := ⟨1, 99/100⟩
    (EvidenceTranslation.TV.toEvidence (truthRevisionCore truth truth)).pos = 198 ∧
      (EvidenceTranslation.TV.toEvidence (truthRevision truth truth)).pos = 99 := by
  norm_num [EvidenceTranslation.TV.toEvidence, truthRevisionCore, truthRevision, c2w, w2c]

end Controls

end Mettapedia.NARS.Bridges.PLN.RevisionSemantics
