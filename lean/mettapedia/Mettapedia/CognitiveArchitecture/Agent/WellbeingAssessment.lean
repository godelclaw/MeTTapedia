import Mettapedia.CognitiveArchitecture.Agent.PatienthoodWellbeing
import Mettapedia.CategoryTheory.PartialSections

/-!
# Provenance-indexed wellbeing assessment views

Each assessment key retains an exact revision-scoped occurrence, an assessor,
an interpretation and a named quality. Values can be arbitrary structured
types. The view pairs a partial assignment with a ledger of value-indexed
witnesses from the existing wellbeing-judgment evidence family.

Every observed coordinate has a ledger witness, and every ledger entry agrees
with the assignment at its exact key. Restriction filters existing entries;
compatible composition appends both ledgers, including their entries on
overlaps. Neither operation converts copied evidence into independently
established corroboration. Different assessors or interpretations can retain
different values without contradicting an assignment at a single exact key.

Evidence here is relative to its supplied judgment family. The concrete
family below certifies membership in an authored report ledger. This is not
evidence that a report is experientially true, that an occurrence is a patient,
or that any scalar combines its independently named qualities appropriately.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.WellbeingAssessment

open Mettapedia.Machines Mettapedia.CategoryTheory
open PatienthoodWellbeing

universe uAssessor uInterpretation uQuality uValue uEvidence

/-- Coordinates retain provenance rather than identifying equal payloads. -/
structure Key (Owner Revision : Type) (Assessor : Type uAssessor)
    (Interpretation : Type uInterpretation) (Quality : Type uQuality) where
  occurrence : StoreOccurrenceId Owner Revision
  assessor : Assessor
  interpretation : Interpretation
  quality : Quality
  deriving DecidableEq

section Definitions

variable {Owner Revision : Type} {Assessor : Type uAssessor}
  {Interpretation : Type uInterpretation} {Quality : Type uQuality}

/-- The existing observer index is refined by interpretation and quality. -/
def Key.observer (key : Key Owner Revision Assessor Interpretation Quality) :
    Assessor × Interpretation × Quality :=
  (key.assessor, key.interpretation, key.quality)

variable {judgment : WellbeingJudgment.{max uAssessor uInterpretation uQuality, uValue, uEvidence}
  (Assessor × Interpretation × Quality) Owner Revision}

/-- A typed ledger entry contains the exact evidence witness rather than
only a payload or a claim that some witness could exist. -/
structure Attestation (judgment : WellbeingJudgment
    (Assessor × Interpretation × Quality) Owner Revision) where
  key : Key Owner Revision Assessor Interpretation Quality
  value : judgment.Value
  evidence : judgment.Evidence key.observer key.occurrence value

/-- Ledger coverage distinguishes observed values from absent coordinates.
Its soundness is agreement with the declared assignment, not a claim about
experienced wellbeing or the empirical adequacy of the judgment family. -/
structure View (judgment : WellbeingJudgment
    (Assessor × Interpretation × Quality) Owner Revision) where
  assigned : PartialSections.View (Key Owner Revision Assessor Interpretation Quality) judgment.Value
  ledger : List (Attestation judgment)
  sound : ∀ record, record ∈ ledger →
    ∃ known : record.key ∈ assigned.context, assigned.values ⟨record.key, known⟩ = record.value
  covered : ∀ key, key ∈ assigned.context →
    ∃ record ∈ ledger, record.key = key

namespace View

@[ext]
theorem ext {first second : View judgment}
    (sameAssignment : first.assigned = second.assigned) (sameLedger : first.ledger = second.ledger) :
    first = second := by
  cases first
  cases second
  cases sameAssignment
  cases sameLedger
  rfl

/-- No coordinate is observed and no evidence value is supplied by default. -/
def empty : View judgment where
  assigned := ⟨∅, fun key => False.elim key.property⟩
  ledger := []
  sound := by simp
  covered := by simp

/-- Acquire a single actual evidence-bearing entry, without other defaults. -/
def single (record : Attestation judgment) : View judgment where
  assigned := ⟨{record.key}, fun _ => record.value⟩
  ledger := [record]
  sound := by
    intro entry member
    have equal : entry = record := List.mem_singleton.mp member
    subst entry
    exact ⟨rfl, rfl⟩
  covered := by
    intro key known
    exact ⟨record, List.mem_singleton.mpr rfl, known.symm⟩

/-- An absent key returns none; an observed value is always tagged some,
even when the value carrier has its own absence or uncertainty constructor. -/
noncomputable def query (view : View judgment)
    (key : Key Owner Revision Assessor Interpretation Quality) : Option judgment.Value := by
  classical
  exact if known : key ∈ view.assigned.context then some (view.assigned.values ⟨key, known⟩) else none

theorem query_of_mem (view : View judgment)
    (key : Key Owner Revision Assessor Interpretation Quality)
    (known : key ∈ view.assigned.context) :
    query view key = some (view.assigned.values ⟨key, known⟩) := by
  classical
  simp [query, known]

theorem query_eq_none_iff (view : View judgment)
    (key : Key Owner Revision Assessor Interpretation Quality) :
    query view key = none ↔ key ∉ view.assigned.context := by
  classical
  by_cases known : key ∈ view.assigned.context <;> simp [query, known]

theorem query_single (record : Attestation judgment) :
    query (single record) record.key = some record.value := by
  classical
  simp [query, single]

/-- A successfully read value has an actual witness in its exact existing
wellbeing-evidence fibre. No patienthood evidence is introduced. -/
theorem query_supported (view : View judgment)
    (key : Key Owner Revision Assessor Interpretation Quality) (value : judgment.Value)
    (observed : query view key = some value) :
    Nonempty (judgment.Evidence key.observer key.occurrence value) := by
  classical
  have known : key ∈ view.assigned.context := by
    by_contra absent
    rw [(query_eq_none_iff view key).2 absent] at observed
    cases observed
  obtain ⟨record, member, equalKey⟩ := view.covered key known
  subst key
  obtain ⟨recorded, agrees⟩ := view.sound record member
  have valueEqual := Option.some.inj ((query_of_mem view record.key recorded).symm.trans observed)
  exact ⟨(agrees.symm.trans valueEqual) ▸ record.evidence⟩

/-- Refinement retains both assigned values and the existing ledger entries.
It permits additional evidence but does not call it independent evidence. -/
def Refines (first second : View judgment) : Prop :=
  first.assigned ≤ second.assigned ∧ first.ledger.Sublist second.ledger

theorem Refines.refl (view : View judgment) : Refines view view := ⟨le_rfl, .refl _⟩

theorem Refines.trans {first second third : View judgment}
    (firstSecond : Refines first second) (secondThird : Refines second third) :
    Refines first third :=
  ⟨firstSecond.1.trans secondThird.1, firstSecond.2.trans secondThird.2⟩

theorem Refines.query_retained {first second : View judgment} (refines : Refines first second)
    {key : Key Owner Revision Assessor Interpretation Quality} {value : judgment.Value}
    (observed : query first key = some value) : query second key = some value := by
  classical
  have known : key ∈ first.assigned.context := by
    by_contra absent
    rw [(query_eq_none_iff first key).2 absent] at observed
    cases observed
  rw [query_of_mem second key (refines.1.1 known)]
  have sameValue := refines.1.2 key known (refines.1.1 known)
  rw [← sameValue]
  exact (query_of_mem first key known).symm.trans observed

/-- Reporting filters the original typed ledger; it does not fabricate
evidence for the selected coordinates. -/
noncomputable def restrict (observed : Set (Key Owner Revision Assessor Interpretation Quality))
    (view : View judgment) : View judgment := by
  classical
  refine {
    assigned := PartialSections.restrict observed view.assigned
    ledger := view.ledger.filter (fun record => decide (record.key ∈ observed))
    sound := ?_
    covered := ?_ }
  · intro record member
    simp only [List.mem_filter, decide_eq_true_eq] at member
    obtain ⟨known, agrees⟩ := view.sound record member.1
    exact ⟨⟨known, member.2⟩, agrees⟩
  · intro key known
    obtain ⟨record, member, equalKey⟩ := view.covered key known.1
    refine ⟨record, ?_, equalKey⟩
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨member, equalKey ▸ known.2⟩

theorem restrict_refines (observed : Set (Key Owner Revision Assessor Interpretation Quality))
    (view : View judgment) : Refines (restrict observed view) view :=
  ⟨PartialSections.restrict_le _ _, List.filter_sublist⟩

theorem restrict_mono (observed : Set (Key Owner Revision Assessor Interpretation Quality))
    {first second : View judgment} (refines : Refines first second) :
    Refines (restrict observed first) (restrict observed second) :=
  ⟨PartialSections.restrict_mono observed refines.1, refines.2.filter _⟩

/-- Successive reports compose by intersection for both assignments and the
actual evidence entries, retaining their original order and witnesses. -/
theorem restrict_restrict
    (first second : Set (Key Owner Revision Assessor Interpretation Quality))
    (view : View judgment) :
    restrict first (restrict second view) = restrict (first ∩ second) view := by
  classical
  apply ext
  · exact PartialSections.restrict_restrict _ _ _
  · simp only [restrict, List.filter_filter]
    congr 1
    funext record
    by_cases inFirst : record.key ∈ first <;> by_cases inSecond : record.key ∈ second <;>
      simp [inFirst, inSecond]

theorem restrict_query_of_mem (observed : Set (Key Owner Revision Assessor Interpretation Quality))
    (view : View judgment) (key : Key Owner Revision Assessor Interpretation Quality)
    (visible : key ∈ observed) : query (restrict observed view) key = query view key := by
  classical
  by_cases known : key ∈ view.assigned.context <;>
    simp [query, restrict, PartialSections.restrict, LocalSections.restrict, visible, known]

theorem restrict_query_of_not_mem
    (observed : Set (Key Owner Revision Assessor Interpretation Quality))
    (view : View judgment) (key : Key Owner Revision Assessor Interpretation Quality)
    (absent : key ∉ observed) : query (restrict observed view) key = none :=
  (query_eq_none_iff _ _).2 (fun known => absent known.2)

/-- Values and typed evidence remain consistent after an assignment extension. -/
theorem sound_under_extension (view : View judgment)
    (larger : PartialSections.View (Key Owner Revision Assessor Interpretation Quality) judgment.Value)
    (included : view.assigned ≤ larger) (record : Attestation judgment)
    (member : record ∈ view.ledger) :
    ∃ known : record.key ∈ larger.context, larger.values ⟨record.key, known⟩ = record.value := by
  obtain ⟨known, agrees⟩ := view.sound record member
  exact ⟨included.1 known, (included.2 _ known (included.1 known)).symm.trans agrees⟩

/-- Compatible assignment composition retains both evidence ledgers, including
distinct witnesses of an agreeing claim. It makes no independence assertion. -/
noncomputable def glue (first second : View judgment)
    (compatible : PartialSections.Compatible first.assigned second.assigned) : View judgment where
  assigned := PartialSections.glue first.assigned second.assigned
  ledger := first.ledger ++ second.ledger
  sound := by
    intro record member
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact first.sound_under_extension _ (PartialSections.le_glue_left _ _) record inFirst
    · exact second.sound_under_extension _ (PartialSections.le_glue_right compatible) record inSecond
  covered := by
    intro key known
    rcases known with inFirst | inSecond
    · obtain ⟨record, member, equalKey⟩ := first.covered key inFirst
      exact ⟨record, List.mem_append.mpr (Or.inl member), equalKey⟩
    · obtain ⟨record, member, equalKey⟩ := second.covered key inSecond
      exact ⟨record, List.mem_append.mpr (Or.inr member), equalKey⟩

theorem first_refines_glue (first second : View judgment)
    (compatible : PartialSections.Compatible first.assigned second.assigned) :
    Refines first (glue first second compatible) :=
  ⟨PartialSections.le_glue_left _ _, List.sublist_append_left _ _⟩

theorem second_refines_glue (first second : View judgment)
    (compatible : PartialSections.Compatible first.assigned second.assigned) :
    Refines second (glue first second compatible) :=
  ⟨PartialSections.le_glue_right compatible, List.sublist_append_right _ _⟩

/-- A report retaining the whole second context and no first-context key
recovers the second view, including its evidence ledger. -/
theorem restrict_glue_right (first second : View judgment)
    (compatible : PartialSections.Compatible first.assigned second.assigned)
    (observed : Set (Key Owner Revision Assessor Interpretation Quality))
    (hidden : first.assigned.context ∩ observed = ∅)
    (visible : second.assigned.context ⊆ observed) :
    restrict observed (glue first second compatible) = second := by
  classical
  apply ext
  · apply PartialSections.View.ext
    · apply Set.Subset.antisymm
      · intro key known
        rcases known.1 with inFirst | inSecond
        · have impossible : key ∈ (∅ : Set _) := hidden ▸ ⟨inFirst, known.2⟩
          exact impossible.elim
        · exact inSecond
      · intro key inSecond
        exact ⟨Or.inr inSecond, visible inSecond⟩
    · intro key inRestricted _
      have absent : key ∉ first.assigned.context := by
        intro inFirst
        have impossible : key ∈ (∅ : Set _) := hidden ▸ ⟨inFirst, inRestricted.2⟩
        exact impossible.elim
      simp [restrict, glue, PartialSections.restrict, PartialSections.glue,
        LocalSections.restrict, LocalSections.glue, absent]
  · change (first.ledger ++ second.ledger).filter (fun record => decide (record.key ∈ observed)) = _
    rw [List.filter_append]
    have firstEmpty : first.ledger.filter (fun record => decide (record.key ∈ observed)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro record member
      simp only [decide_eq_true_eq]
      intro seen
      obtain ⟨known, _⟩ := first.sound record member
      have impossible : record.key ∈ (∅ : Set _) := hidden ▸ ⟨known, seen⟩
      exact impossible.elim
    have secondRetained : second.ledger.filter (fun record => decide (record.key ∈ observed)) =
        second.ledger := by
      apply List.filter_eq_self.mpr
      intro record member
      exact decide_eq_true_eq.mpr (visible (second.sound record member).choose)
    rw [firstEmpty, secondRetained, List.nil_append]

theorem restrict_single_glue_right (first second : Attestation judgment)
    (compatible : PartialSections.Compatible (single first).assigned (single second).assigned)
    (observed : Set (Key Owner Revision Assessor Interpretation Quality))
    (hidden : first.key ∉ observed) (visible : second.key ∈ observed) :
    restrict observed (glue (single first) (single second) compatible) = single second := by
  apply restrict_glue_right _ _ compatible observed
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro key known
    have equal : key = first.key := known.1
    subst key
    exact hidden known.2
  · intro key known
    have equal : key = second.key := known
    exact equal.symm ▸ visible

/-- One exact key cannot retain two unequal values in any common refinement. -/
theorem disagreement_blocks_refinement {first second : View judgment}
    {key : Key Owner Revision Assessor Interpretation Quality} {left right : judgment.Value}
    (firstReads : query first key = some left) (secondReads : query second key = some right)
    (different : left ≠ right) :
    ¬ ∃ whole, Refines first whole ∧ Refines second whole := by
  rintro ⟨whole, firstWhole, secondWhole⟩
  exact different (Option.some.inj
    ((firstWhole.query_retained firstReads).symm.trans (secondWhole.query_retained secondReads)))

theorem disagreement_blocks_glue {first second : View judgment}
    {key : Key Owner Revision Assessor Interpretation Quality} {left right : judgment.Value}
    (firstReads : query first key = some left) (secondReads : query second key = some right)
    (different : left ≠ right) : ¬ PartialSections.Compatible first.assigned second.assigned := by
  intro compatible
  exact disagreement_blocks_refinement firstReads secondReads different
    ⟨glue first second compatible, first_refines_glue _ _ compatible,
      second_refines_glue _ _ compatible⟩

/-- Distinct provenance coordinates can retain differing reports together. -/
theorem distinct_single_keys_compatible (first second : Attestation judgment)
    (different : first.key ≠ second.key) :
    PartialSections.Compatible (single first).assigned (single second).assigned := by
  intro key inFirst inSecond
  exact (different (inFirst.symm.trans inSecond)).elim

end View

/-! ## Evidence from an explicitly authored report ledger -/

/-- A judgment family certifying report retrieval, including exact provenance
and the reported structured value. Retrieval does not certify felt truth. -/
def recordedJudgment {Value : Type uValue}
    (records : List (Key Owner Revision Assessor Interpretation Quality × Value)) :
    WellbeingJudgment (Assessor × Interpretation × Quality) Owner Revision where
  Value := Value
  Evidence observer occurrence value :=
    {position : Fin records.length //
      (records[position]).1.observer = observer ∧
      (records[position]).1.occurrence = occurrence ∧ (records[position]).2 = value}

/-- Retrieving one ledger row constructs a real position-indexed witness. -/
def recordedAttestation {Value : Type uValue}
    (records : List (Key Owner Revision Assessor Interpretation Quality × Value))
    (position : Fin records.length) : Attestation (recordedJudgment records) where
  key := (records[position]).1
  value := (records[position]).2
  evidence := ⟨position, rfl, rfl, rfl⟩

end Definitions

/-! ## Concrete provenance, disagreement and missing-data controls -/

namespace Controls

open RevisionLineage.Canary

/-- Two arbitrary report qualities are named independently. The example
value has two fields; neither field is a universal wellbeing score. -/
abbrev AssessmentKey := Key Owner Revision Bool Bool Bool
abbrev ReportValue := Nat × Bool

def leftKey : AssessmentKey := ⟨leftCopy.id, false, false, false⟩
def externalKey : AssessmentKey := ⟨leftCopy.id, true, false, false⟩
def rightKey : AssessmentKey := ⟨rightCopy.id, false, false, false⟩
def anchorKey : AssessmentKey := ⟨leftCopy.id, true, false, true⟩
def alternateInterpretationKey : AssessmentKey := ⟨leftCopy.id, false, true, false⟩

/-- The authored ledger deliberately includes an exact-key disagreement.
Each report has retrieval evidence; the disagreement prevents a single
consistent assessment from accepting both values at that key. -/
def reports : List (AssessmentKey × ReportValue) :=
  [(leftKey, (2, false)), (externalKey, (5, true)), (leftKey, (7, false)),
   (rightKey, (2, false)), (anchorKey, (0, false)), (alternateInterpretationKey, (3, true))]

def judgment : WellbeingJudgment (Bool × Bool × Bool) Owner Revision := recordedJudgment reports
def row (position : Fin 6) : Attestation judgment := recordedAttestation reports position
def selfAssessment : View judgment := View.single (row 0)
def externalAssessment : View judgment := View.single (row 1)
def conflictingAssessment : View judgment := View.single (row 2)
def copiedAssessment : View judgment := View.single (row 3)
def anchorAssessment : View judgment := View.single (row 4)
def alternateInterpretationAssessment : View judgment := View.single (row 5)

theorem assessor_keys_distinct : (row 0).key ≠ (row 1).key := by decide
theorem occurrence_keys_distinct : (row 0).key ≠ (row 3).key := by decide
theorem interpretation_keys_distinct : (row 0).key ≠ (row 5).key := by decide
theorem anchor_distinct_self : (row 0).key ≠ (row 4).key := by decide
theorem anchor_distinct_copy : (row 3).key ≠ (row 4).key := by decide

noncomputable def assessorPair : View judgment :=
  View.glue selfAssessment externalAssessment
    (View.distinct_single_keys_compatible _ _ assessor_keys_distinct)

/-- Differing assessors retain their differing reports without an exact-key
conflict or a forced consensus value. -/
theorem assessor_disagreement_coexists :
    View.query assessorPair leftKey = some (2, false) ∧
      View.query assessorPair externalKey = some (5, true) := by
  constructor
  · exact (View.first_refines_glue _ _ _).query_retained (View.query_single (row 0))
  · exact (View.second_refines_glue _ _ _).query_retained (View.query_single (row 1))

theorem same_key_conflict_cannot_glue :
    ¬ PartialSections.Compatible selfAssessment.assigned conflictingAssessment.assigned :=
  View.disagreement_blocks_glue (View.query_single (row 0)) (View.query_single (row 2))
    (by decide : (2, false) ≠ (7, false))

theorem interpretation_disagreement_is_compatible :
    PartialSections.Compatible selfAssessment.assigned alternateInterpretationAssessment.assigned :=
  View.distinct_single_keys_compatible _ _ interpretation_keys_distinct

/-- Equal payloads do not transfer an assessment to a different occurrence. -/
theorem equal_payload_occurrences_remain_distinct :
    leftCopy.state = rightCopy.state ∧
      View.query selfAssessment leftKey = some (2, false) ∧
      View.query copiedAssessment leftKey = none := by
  refine ⟨equal_state_distinct_copies.1, View.query_single (row 0), ?_⟩
  exact (View.query_eq_none_iff _ _).2 (by change leftKey ≠ rightKey; decide)

theorem observed_zero_is_not_unobserved :
    View.query anchorAssessment anchorKey = some (0, false) ∧
      View.query (View.empty : View judgment) anchorKey = none := by
  refine ⟨View.query_single (row 4), ?_⟩
  exact (View.query_eq_none_iff _ _).2 (by simp [View.empty])

noncomputable def originalWithAnchor : View judgment :=
  View.glue selfAssessment anchorAssessment
    (View.distinct_single_keys_compatible _ _ anchor_distinct_self)

noncomputable def copyWithAnchor : View judgment :=
  View.glue copiedAssessment anchorAssessment
    (View.distinct_single_keys_compatible _ _ anchor_distinct_copy)

def qualityReport : Set AssessmentKey := {key | key.quality = true}
def externalReport : Set AssessmentKey := {key | key.assessor = true}

/-- The shared quality remains observed after restriction; the occurrence
distinction disappears from this report without being globally identified. -/
theorem restricted_quality_erases_occurrence_distinction :
    View.restrict qualityReport originalWithAnchor = anchorAssessment ∧
      View.restrict qualityReport copyWithAnchor = anchorAssessment ∧
      View.query anchorAssessment anchorKey = some (0, false) := by
  refine ⟨?_, ?_, View.query_single (row 4)⟩
  · exact View.restrict_single_glue_right _ _ _ qualityReport
      (by change (row 0).key.quality ≠ true; decide)
      (by change (row 4).key.quality = true; decide)
  · exact View.restrict_single_glue_right _ _ _ qualityReport
      (by change (row 3).key.quality ≠ true; decide)
      (by change (row 4).key.quality = true; decide)

/-- Restricting the assessor vocabulary likewise hides the self-assessor's
occurrence distinction, while retaining a real external assessment. -/
theorem restricted_provenance_erases_occurrence_distinction :
    View.restrict externalReport originalWithAnchor = anchorAssessment ∧
      View.restrict externalReport copyWithAnchor = anchorAssessment := by
  constructor
  · exact View.restrict_single_glue_right _ _ _ externalReport
      (by change (row 0).key.assessor ≠ true; decide)
      (by change (row 4).key.assessor = true; decide)
  · exact View.restrict_single_glue_right _ _ _ externalReport
      (by change (row 3).key.assessor ≠ true; decide)
      (by change (row 4).key.assessor = true; decide)

theorem full_views_still_differ : originalWithAnchor ≠ copyWithAnchor := by
  intro same
  have originalReads : View.query originalWithAnchor leftKey = some (2, false) :=
    (View.first_refines_glue _ _ _).query_retained (View.query_single (row 0))
  have copyAbsent : View.query copyWithAnchor leftKey = none :=
    (View.query_eq_none_iff _ _).2
      (by change ¬ (leftKey = rightKey ∨ leftKey = anchorKey); decide)
  rw [same, copyAbsent] at originalReads
  cases originalReads

/-- Appending a copied report preserves its original provenance and exact
witness, rather than manufacturing a different source or occurrence. -/
theorem repeated_report_keeps_the_same_witness :
    (View.glue selfAssessment selfAssessment (fun _ _ _ => rfl)).ledger =
      [row 0, row 0] := rfl

end Controls

end Mettapedia.CognitiveArchitecture.Agent.WellbeingAssessment
