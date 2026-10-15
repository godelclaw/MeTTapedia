import Mettapedia.CategoryTheory.PartialSections

/-!
# Interpretation-relative assessment from partial observations

An observation constrains operational states.  A separately authored relation
connects those states, interpretation indices, and candidate outcomes.  Outcomes
may retain independent qualities, occurrence identities, or an explicit
non-experiential alternative.  Neither an observation nor its provenance
supplies that interpretation relation.

Possible outcomes retain a single joint witness for all observed features.
Refinement removes possibilities; enlarging the admitted interpretations adds
them.  A robust judgment requires a possible outcome in addition to its
universal condition, so inconsistent or unsupported evidence cannot certify a
policy vacuously.  Compatible descriptions can be glued, but projecting their
possibilities before combining them can lose the joint-witness requirement.

The finite controls are independently specified mathematical models.  They
establish neither experiential adequacy nor wellbeing of a deployed agent.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Consciousness.InterpretationAssessment

open Mettapedia.CategoryTheory.PartialSections

universe uState uFeature uAnswer uHypothesis uOutcome uTarget

structure Model (State : Type uState) (Feature : Type uFeature)
    (Answer : Type uAnswer) (Hypothesis : Type uHypothesis)
    (Outcome : Type uOutcome) where
  observe : State → Feature → Answer
  interprets : Hypothesis → State → Outcome → Prop

variable {State : Type uState} {Feature : Type uFeature} {Answer : Type uAnswer}
  {Hypothesis : Type uHypothesis} {Outcome : Type uOutcome}

/-- All available coordinates agree with one operational state. -/
def CompatibleState (model : Model State Feature Answer Hypothesis Outcome)
    (view : View Feature Answer) (state : State) : Prop :=
  view ≤ total (model.observe state)

/-- One operational state and one interpretation witness the whole outcome. -/
def possible (model : Model State Feature Answer Hypothesis Outcome)
    (admitted : Set Hypothesis) (view : View Feature Answer) : Set Outcome :=
  {outcome | ∃ hypothesis state, hypothesis ∈ admitted ∧
    CompatibleState model view state ∧ model.interprets hypothesis state outcome}

/-- A universal policy judgment with an explicit non-vacuity obligation. -/
def Robust (model : Model State Feature Answer Hypothesis Outcome)
    (admitted : Set Hypothesis) (view : View Feature Answer)
    (condition : Outcome → Prop) : Prop :=
  (possible model admitted view).Nonempty ∧
    ∀ outcome ∈ possible model admitted view, condition outcome

/-- Global outcome support does not ensure that every admitted interpretation
is represented.  Use this additional obligation when claiming family coverage.
An unsupported interpretation remains distinct from a supported interpretation
that explicitly predicts a non-experiential outcome. -/
def SupportsFamily (model : Model State Feature Answer Hypothesis Outcome)
    (admitted : Set Hypothesis) (view : View Feature Answer) : Prop :=
  ∀ hypothesis ∈ admitted, (possible model {hypothesis} view).Nonempty

theorem compatibleState_mono
    (model : Model State Feature Answer Hypothesis Outcome)
    {first second : View Feature Answer} (refines : first ≤ second)
    {state : State} (compatible : CompatibleState model second state) :
    CompatibleState model first state := refines.trans compatible

/-- Information refinement is contravariant on candidate outcomes. -/
theorem possible_antitone_view
    (model : Model State Feature Answer Hypothesis Outcome)
    (admitted : Set Hypothesis) {first second : View Feature Answer}
    (refines : first ≤ second) :
    possible model admitted second ⊆ possible model admitted first := by
  rintro outcome ⟨hypothesis, state, member, compatible, interpreted⟩
  exact ⟨hypothesis, state, member,
    compatibleState_mono model refines compatible, interpreted⟩

theorem possible_mono_interpretations
    (model : Model State Feature Answer Hypothesis Outcome)
    {first second : Set Hypothesis} (included : first ⊆ second)
    (view : View Feature Answer) :
    possible model first view ⊆ possible model second view := by
  rintro outcome ⟨hypothesis, state, member, compatible, interpreted⟩
  exact ⟨hypothesis, state, included member, compatible, interpreted⟩

theorem supportsFamily_restrict_interpretations
    (model : Model State Feature Answer Hypothesis Outcome)
    {first second : Set Hypothesis} (included : first ⊆ second)
    {view : View Feature Answer} (supported : SupportsFamily model second view) :
    SupportsFamily model first view :=
  fun hypothesis member => supported hypothesis (included member)

/-- Forgetting evidence preserves existing interpretation witnesses. -/
theorem supportsFamily_coarsening
    (model : Model State Feature Answer Hypothesis Outcome)
    (admitted : Set Hypothesis) {first second : View Feature Answer}
    (refines : first ≤ second) (supported : SupportsFamily model admitted second) :
    SupportsFamily model admitted first := by
  intro hypothesis member
  obtain ⟨outcome, possibleOutcome⟩ := supported hypothesis member
  exact ⟨outcome, possible_antitone_view model {hypothesis} refines possibleOutcome⟩

/-- Removing observations never invents certainty by shrinking possibilities. -/
theorem possible_subset_restriction
    (model : Model State Feature Answer Hypothesis Outcome)
    (admitted : Set Hypothesis) (view : View Feature Answer)
    (observed : Set Feature) :
    possible model admitted view ⊆ possible model admitted (restrict observed view) :=
  possible_antitone_view model admitted (restrict_le observed view)

theorem robust_has_joint_witness
    {model : Model State Feature Answer Hypothesis Outcome}
    {admitted : Set Hypothesis} {view : View Feature Answer}
    {condition : Outcome → Prop} (robust : Robust model admitted view condition) :
    ∃ hypothesis state outcome, hypothesis ∈ admitted ∧
      CompatibleState model view state ∧ model.interprets hypothesis state outcome ∧
      condition outcome := by
  rcases robust.1 with ⟨outcome, hypothesis, state, member, compatible, interpreted⟩
  exact ⟨hypothesis, state, outcome, member, compatible, interpreted,
    robust.2 outcome ⟨hypothesis, state, member, compatible, interpreted⟩⟩

/-- A surviving witness is required when new evidence refines the view. -/
theorem robust_refinement
    (model : Model State Feature Answer Hypothesis Outcome)
    (admitted : Set Hypothesis) {first second : View Feature Answer}
    {condition : Outcome → Prop} (refines : first ≤ second)
    (robust : Robust model admitted first condition)
    (survives : (possible model admitted second).Nonempty) :
    Robust model admitted second condition :=
  ⟨survives, fun outcome member =>
    robust.2 outcome (possible_antitone_view model admitted refines member)⟩

/-- A judgment established for more interpretations survives restricting the
family only if at least one candidate survives. -/
theorem robust_restrict_interpretations
    (model : Model State Feature Answer Hypothesis Outcome)
    {first second : Set Hypothesis} (included : first ⊆ second)
    {view : View Feature Answer} {condition : Outcome → Prop}
    (robust : Robust model second view condition)
    (survives : (possible model first view).Nonempty) :
    Robust model first view condition :=
  ⟨survives, fun outcome member =>
    robust.2 outcome (possible_mono_interpretations model included view member)⟩

theorem robust_false_of_counterexample
    (model : Model State Feature Answer Hypothesis Outcome)
    {admitted : Set Hypothesis} {view : View Feature Answer}
    {condition : Outcome → Prop} {outcome : Outcome}
    (possibleOutcome : outcome ∈ possible model admitted view)
    (refused : ¬ condition outcome) : ¬ Robust model admitted view condition := by
  intro robust
  exact refused (robust.2 outcome possibleOutcome)

theorem robust_false_of_no_possibilities
    (model : Model State Feature Answer Hypothesis Outcome)
    (admitted : Set Hypothesis) (view : View Feature Answer)
    (empty : possible model admitted view = ∅) (condition : Outcome → Prop) :
    ¬ Robust model admitted view condition := by
  intro robust
  simpa [empty] using robust.1

/-- Independent protected conditions compose without a scalar exchange rate. -/
theorem robust_and_iff
    (model : Model State Feature Answer Hypothesis Outcome)
    (admitted : Set Hypothesis) (view : View Feature Answer)
    (first second : Outcome → Prop) :
    Robust model admitted view (fun outcome => first outcome ∧ second outcome) ↔
      Robust model admitted view first ∧ Robust model admitted view second := by
  constructor
  · intro robust
    exact ⟨⟨robust.1, fun outcome member => (robust.2 outcome member).1⟩,
      ⟨robust.1, fun outcome member => (robust.2 outcome member).2⟩⟩
  · rintro ⟨firstRobust, secondRobust⟩
    exact ⟨firstRobust.1, fun outcome member =>
      ⟨firstRobust.2 outcome member, secondRobust.2 outcome member⟩⟩

theorem robust_not_both
    (model : Model State Feature Answer Hypothesis Outcome)
    (admitted : Set Hypothesis) (view : View Feature Answer)
    (condition : Outcome → Prop) :
    ¬ (Robust model admitted view condition ∧
      Robust model admitted view (fun outcome => ¬ condition outcome)) := by
  rintro ⟨positive, negative⟩
  obtain ⟨outcome, member⟩ := positive.1
  exact negative.2 outcome member (positive.2 outcome member)

/-! ## Composition retains a joint operational witness -/

theorem compatibleState_glue
    (model : Model State Feature Answer Hypothesis Outcome)
    {first second : View Feature Answer} (compatible : Compatible first second)
    (state : State) :
    CompatibleState model (glue first second) state ↔
      CompatibleState model first state ∧ CompatibleState model second state :=
  glue_universal compatible (total (model.observe state))

theorem possible_glue_iff
    (model : Model State Feature Answer Hypothesis Outcome)
    (admitted : Set Hypothesis) {first second : View Feature Answer}
    (compatible : Compatible first second) (outcome : Outcome) :
    outcome ∈ possible model admitted (glue first second) ↔
      ∃ hypothesis state, hypothesis ∈ admitted ∧
        CompatibleState model first state ∧ CompatibleState model second state ∧
        model.interprets hypothesis state outcome := by
  constructor
  · rintro ⟨hypothesis, state, member, fits, interpreted⟩
    obtain ⟨fitsFirst, fitsSecond⟩ := (compatibleState_glue model compatible state).mp fits
    exact ⟨hypothesis, state, member, fitsFirst, fitsSecond, interpreted⟩
  · rintro ⟨hypothesis, state, member, fitsFirst, fitsSecond, interpreted⟩
    exact ⟨hypothesis, state, member,
      (compatibleState_glue model compatible state).mpr ⟨fitsFirst, fitsSecond⟩, interpreted⟩

/-- Projection to candidate outcomes can lose correlations.  The reverse
inclusion is deliberately absent and is refuted by the finite controls. -/
theorem possible_glue_subset
    (model : Model State Feature Answer Hypothesis Outcome)
    (admitted : Set Hypothesis) {first second : View Feature Answer}
    (compatible : Compatible first second) :
    possible model admitted (glue first second) ⊆
      possible model admitted first ∩ possible model admitted second := by
  intro outcome member
  rcases (possible_glue_iff model admitted compatible outcome).mp member with
    ⟨hypothesis, state, admittedHypothesis, fitsFirst, fitsSecond, interpreted⟩
  exact ⟨⟨hypothesis, state, admittedHypothesis, fitsFirst, interpreted⟩,
    ⟨hypothesis, state, admittedHypothesis, fitsSecond, interpreted⟩⟩

/-! ## Observation- and interpretation-respecting translations -/

/-- The state map must preserve independently specified observations and
carry each source interpretation witness to a target witness. -/
structure Translation {Target : Type uTarget}
    (source : Model State Feature Answer Hypothesis Outcome)
    (target : Model Target Feature Answer Hypothesis Outcome) where
  stateMap : State → Target
  observations : ∀ state feature,
    target.observe (stateMap state) feature = source.observe state feature
  interpretations : ∀ hypothesis state outcome,
    source.interprets hypothesis state outcome →
      target.interprets hypothesis (stateMap state) outcome

namespace Translation

variable {Target : Type uTarget}
  {source : Model State Feature Answer Hypothesis Outcome}
  {target : Model Target Feature Answer Hypothesis Outcome}

theorem compatible_map (translation : Translation source target)
    {view : View Feature Answer} {state : State}
    (fits : CompatibleState source view state) :
    CompatibleState target view (translation.stateMap state) := by
  have observes : target.observe (translation.stateMap state) = source.observe state :=
    funext (translation.observations state)
  simpa only [CompatibleState, observes] using fits

theorem possible_map (translation : Translation source target)
    (admitted : Set Hypothesis) (view : View Feature Answer) :
    possible source admitted view ⊆ possible target admitted view := by
  rintro outcome ⟨hypothesis, state, member, fits, interpreted⟩
  exact ⟨hypothesis, translation.stateMap state, member,
    translation.compatible_map fits,
    translation.interpretations hypothesis state outcome interpreted⟩

theorem supportsFamily_map (translation : Translation source target)
    (admitted : Set Hypothesis) (view : View Feature Answer)
    (supported : SupportsFamily source admitted view) :
    SupportsFamily target admitted view := by
  intro hypothesis member
  obtain ⟨outcome, possibleOutcome⟩ := supported hypothesis member
  exact ⟨outcome, translation.possible_map {hypothesis} view possibleOutcome⟩

/-- Every target interpretation witness must lift with the same outcome and
state image.  Preserving source witnesses alone does not imply this. -/
def Covers (translation : Translation source target) : Prop :=
  ∀ hypothesis state outcome, target.interprets hypothesis state outcome →
    ∃ original, translation.stateMap original = state ∧
      source.interprets hypothesis original outcome

theorem possible_eq (translation : Translation source target)
    (covers : translation.Covers) (admitted : Set Hypothesis)
    (view : View Feature Answer) :
    possible source admitted view = possible target admitted view := by
  apply Set.Subset.antisymm (translation.possible_map admitted view)
  rintro outcome ⟨hypothesis, state, member, fits, interpreted⟩
  obtain ⟨original, image, originalInterpreted⟩ := covers hypothesis state outcome interpreted
  subst state
  have observes : target.observe (translation.stateMap original) = source.observe original :=
    funext (translation.observations original)
  exact ⟨hypothesis, original, member,
    by simpa only [CompatibleState, observes] using fits, originalInterpreted⟩

theorem robust_iff (translation : Translation source target)
    (covers : translation.Covers) (admitted : Set Hypothesis)
    (view : View Feature Answer) (condition : Outcome → Prop) :
    Robust source admitted view condition ↔ Robust target admitted view condition := by
  unfold Robust
  rw [translation.possible_eq covers admitted view]

theorem supportsFamily_iff (translation : Translation source target)
    (covers : translation.Covers) (admitted : Set Hypothesis)
    (view : View Feature Answer) :
    SupportsFamily source admitted view ↔ SupportsFamily target admitted view := by
  constructor
  · exact translation.supportsFamily_map admitted view
  · intro supported hypothesis member
    simpa only [← translation.possible_eq covers {hypothesis} view] using
      supported hypothesis member

/-- Sequential translations preserve the same declared observation interface
and carry interpretation witnesses through both implementations. -/
def comp {Next : Type*}
    {next : Model Next Feature Answer Hypothesis Outcome}
    (first : Translation source target) (second : Translation target next) :
    Translation source next where
  stateMap := second.stateMap ∘ first.stateMap
  observations state feature :=
    (second.observations (first.stateMap state) feature).trans
      (first.observations state feature)
  interpretations hypothesis state outcome interpreted :=
    second.interpretations hypothesis (first.stateMap state) outcome
      (first.interpretations hypothesis state outcome interpreted)

theorem comp_covers {Next : Type*}
    {next : Model Next Feature Answer Hypothesis Outcome}
    (first : Translation source target) (second : Translation target next)
    (firstCovers : first.Covers) (secondCovers : second.Covers) :
    (first.comp second).Covers := by
  intro hypothesis state outcome interpreted
  obtain ⟨middle, middleImage, middleInterpreted⟩ :=
    secondCovers hypothesis state outcome interpreted
  obtain ⟨original, originalImage, originalInterpreted⟩ :=
    firstCovers hypothesis middle outcome middleInterpreted
  refine ⟨original, ?_, originalInterpreted⟩
  exact (congrArg second.stateMap originalImage).trans middleImage

end Translation

/-! ## Independent finite controls -/

namespace Controls

inductive Quality where
  | pain
  | suffering
  deriving DecidableEq

inductive Interpretation where
  | direct
  | reverseSuffering
  | nonExperiential
  deriving DecidableEq

/-- Two retained Boolean coordinates are a small qualitative carrier, not a
scalar welfare metric or a measurement of an actual experiencer. -/
abbrev Profile := Bool × Bool

def model : Model Profile Quality Bool Interpretation (Option Profile) where
  observe state
    | .pain => state.1
    | .suffering => state.2
  interprets hypothesis state outcome :=
    match hypothesis with
    | .direct => outcome = some state
    | .reverseSuffering => outcome = some (state.1, !state.2)
    | .nonExperiential => outcome = none

def baseline : Profile := (false, false)
def full : View Quality Bool := total (model.observe baseline)
def painOnly : View Quality Bool := restrict {Quality.pain} full
def unavailable : View Quality Bool := restrict ∅ full

/-- This particular policy explicitly admits a non-experiential alternative;
that alternative remains different from a neutral experiential profile. -/
def noSuffering (outcome : Option Profile) : Prop :=
  outcome ≠ some (false, true) ∧ outcome ≠ some (true, true)

theorem nonExperiential_is_not_neutral :
    (none : Option Profile) ≠ some baseline := by simp

theorem full_identifies_state {state : Profile}
    (fits : CompatibleState model full state) : state = baseline := by
  have pain := fits.2 Quality.pain (Set.mem_univ _) (Set.mem_univ _)
  have suffering := fits.2 Quality.suffering (Set.mem_univ _) (Set.mem_univ _)
  change false = state.1 at pain
  change false = state.2 at suffering
  exact Prod.ext pain.symm suffering.symm

theorem direct_full_outcomes (outcome : Option Profile) :
    outcome ∈ possible model {Interpretation.direct} full ↔ outcome = some baseline := by
  constructor
  · rintro ⟨hypothesis, state, member, fits, interpreted⟩
    have hypothesisEq : hypothesis = Interpretation.direct := member
    subst hypothesis
    have stateEq := full_identifies_state fits
    subst state
    exact interpreted
  · intro same
    exact ⟨Interpretation.direct, baseline, Set.mem_singleton _, le_rfl, same⟩

theorem direct_full_robust :
    Robust model {Interpretation.direct} full noSuffering := by
  refine ⟨⟨some baseline, (direct_full_outcomes _).mpr rfl⟩, ?_⟩
  intro outcome member
  rw [(direct_full_outcomes outcome).mp member]
  simp [noSuffering, baseline]

theorem suffering_profile_fits_pain_report :
    CompatibleState model painOnly (false, true) := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro feature member _
  have featureEq : feature = Quality.pain := member.2
  subst feature
  rfl

theorem pain_report_allows_suffering :
    some (false, true) ∈ possible model {Interpretation.direct} painOnly :=
  ⟨Interpretation.direct, (false, true), Set.mem_singleton _,
    suffering_profile_fits_pain_report, rfl⟩

theorem pain_report_does_not_certify_no_suffering :
    ¬ Robust model {Interpretation.direct} painOnly noSuffering := by
  apply robust_false_of_counterexample model pain_report_allows_suffering
  simp [noSuffering]

/-- Changing the admitted interpretation can change the assessment even when
the complete observational description and operational state stay fixed. -/
theorem additional_interpretation_blocks_judgment :
    ¬ Robust model {Interpretation.direct, Interpretation.reverseSuffering}
      full noSuffering := by
  apply robust_false_of_counterexample model
    (outcome := some (false, true))
  · exact ⟨Interpretation.reverseSuffering, baseline, by simp, le_rfl, rfl⟩
  · simp [noSuffering]

theorem unavailable_fits_every_state (state : Profile) :
    CompatibleState model unavailable state := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro _ member _
  exact False.elim member.2

/-- Missing observations leave both profiles possible; they do not record a
zero profile or a non-experiential outcome. -/
theorem unavailable_retains_distinct_profiles :
    some baseline ∈ possible model {Interpretation.direct} unavailable ∧
      some (true, true) ∈ possible model {Interpretation.direct} unavailable ∧
      some baseline ≠ some (true, true) := by
  refine ⟨⟨Interpretation.direct, baseline, Set.mem_singleton _,
    unavailable_fits_every_state _, rfl⟩,
    ⟨Interpretation.direct, (true, true), Set.mem_singleton _,
      unavailable_fits_every_state _, rfl⟩, ?_⟩
  decide

theorem unavailable_does_not_imply_nonExperiential :
    none ∉ possible model {Interpretation.direct} unavailable := by
  rintro ⟨hypothesis, state, member, _, interpreted⟩
  have hypothesisEq : hypothesis = Interpretation.direct := member
  subst hypothesis
  change (none : Option Profile) = some state at interpreted
  cases interpreted

/-! ### Unsupported interpretations are not non-experiential outcomes -/

/-- The second hypothesis deliberately has no interpretation witness.  It
stands for a missing interpretation, not a prediction of absent experience. -/
def partialModel : Model Profile Quality Bool Bool (Option Profile) where
  observe := model.observe
  interprets hypothesis state outcome :=
    if hypothesis then False else outcome = some state

theorem partial_full_outcomes (outcome : Option Profile) :
    outcome ∈ possible partialModel Set.univ full ↔ outcome = some baseline := by
  constructor
  · rintro ⟨hypothesis, state, _, fits, interpreted⟩
    cases hypothesis with
    | false =>
        have stateEq := full_identifies_state fits
        subst state
        exact interpreted
    | true => exact False.elim interpreted
  · intro same
    exact ⟨false, baseline, Set.mem_univ _, le_rfl, same⟩

/-- A supported outcome judgment alone does not certify support for each
hypothesis listed in the admitted family. -/
theorem global_robust_does_not_cover_unsupported_hypothesis :
    Robust partialModel Set.univ full noSuffering ∧
      ¬ SupportsFamily partialModel Set.univ full := by
  constructor
  · refine ⟨⟨some baseline, (partial_full_outcomes _).mpr rfl⟩, ?_⟩
    intro outcome member
    rw [(partial_full_outcomes outcome).mp member]
    simp [noSuffering, baseline]
  · intro supported
    obtain ⟨outcome, hypothesis, _, member, _, interpreted⟩ :=
      supported true (Set.mem_univ _)
    have same : hypothesis = true := member
    subst hypothesis
    exact False.elim interpreted

/-! ### Compatible local views with lost outcome correlations -/

def agreementModel : Model Profile Quality Bool Unit Bool where
  observe state
    | .pain => state.1
    | .suffering => state.2
  interprets _ state outcome := outcome = (state.1 == state.2)

def bothTrue : View Quality Bool := total (agreementModel.observe (true, true))
def firstTrue : View Quality Bool := restrict {Quality.pain} bothTrue
def secondTrue : View Quality Bool := restrict {Quality.suffering} bothTrue

theorem local_views_compatible : Compatible firstTrue secondTrue :=
  compatible_of_common_extension (restrict_le _ bothTrue) (restrict_le _ bothTrue)

theorem glue_local_views : glue firstTrue secondTrue = bothTrue := by
  rw [firstTrue, secondTrue, glue_restrictions]
  have cover : ({Quality.pain} ∪ {Quality.suffering} : Set Quality) = Set.univ := by
    ext quality
    cases quality <;> simp
  rw [cover, restrict_univ]

theorem first_locally_allows_disagreement :
    false ∈ possible agreementModel Set.univ firstTrue := by
  refine ⟨(), (true, false), Set.mem_univ _, ?_, rfl⟩
  refine ⟨Set.subset_univ _, ?_⟩
  intro feature member _
  have featureEq : feature = Quality.pain := member.2
  subst feature
  rfl

theorem second_locally_allows_disagreement :
    false ∈ possible agreementModel Set.univ secondTrue := by
  refine ⟨(), (false, true), Set.mem_univ _, ?_, rfl⟩
  refine ⟨Set.subset_univ _, ?_⟩
  intro feature member _
  have featureEq : feature = Quality.suffering := member.2
  subst feature
  rfl

theorem combined_refuses_disagreement :
    false ∉ possible agreementModel Set.univ (glue firstTrue secondTrue) := by
  rw [glue_local_views]
  rintro ⟨_, state, _, fits, interpreted⟩
  have pain := fits.2 Quality.pain (Set.mem_univ _) (Set.mem_univ _)
  have suffering := fits.2 Quality.suffering (Set.mem_univ _) (Set.mem_univ _)
  change true = state.1 at pain
  change true = state.2 at suffering
  change false = (state.1 == state.2) at interpreted
  rw [← pain, ← suffering] at interpreted
  cases interpreted

/-- Local outcome summaries intersect, but their retained witnesses cannot
be combined.  Existential projection therefore does not preserve this meet. -/
theorem outcome_intersection_loses_joint_witness :
    possible agreementModel Set.univ (glue firstTrue secondTrue) ≠
      possible agreementModel Set.univ firstTrue ∩
        possible agreementModel Set.univ secondTrue := by
  intro same
  apply combined_refuses_disagreement
  rw [same]
  exact ⟨first_locally_allows_disagreement, second_locally_allows_disagreement⟩

/-- The operational model imposes a relation between the two observation
coordinates.  The description category alone does not impose that relation. -/
def exclusiveModel : Model Bool Quality Bool Unit Bool where
  observe state
    | .pain => state
    | .suffering => !state
  interprets _ state outcome := outcome = state

theorem compatible_data_without_joint_realization :
    Compatible firstTrue secondTrue ∧
      possible exclusiveModel Set.univ (glue firstTrue secondTrue) = ∅ := by
  refine ⟨local_views_compatible, ?_⟩
  rw [glue_local_views]
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro outcome ⟨_, state, _, fits, _⟩
  have pain := fits.2 Quality.pain (Set.mem_univ _) (Set.mem_univ _)
  have suffering := fits.2 Quality.suffering (Set.mem_univ _) (Set.mem_univ _)
  change true = state at pain
  change true = !state at suffering
  rw [← pain] at suffering
  cases suffering

/-- Even compatible local reports do not certify a policy when no state of
the declared operational model realizes them jointly. -/
theorem unrealized_gluing_certifies_no_policy (condition : Bool → Prop) :
    ¬ Robust exclusiveModel Set.univ (glue firstTrue secondTrue) condition :=
  robust_false_of_no_possibilities exclusiveModel Set.univ _
    compatible_data_without_joint_realization.2 condition

/-! ### A genuine nonidentity coordinate recoding -/

def recodedModel : Model Profile Quality Bool Interpretation (Option Profile) where
  observe state
    | .pain => state.2
    | .suffering => state.1
  interprets hypothesis state outcome :=
    match hypothesis with
    | .direct => outcome = some (state.2, state.1)
    | .reverseSuffering => outcome = some (state.2, !state.1)
    | .nonExperiential => outcome = none

def recoding : Translation model recodedModel where
  stateMap state := (state.2, state.1)
  observations state feature := by cases feature <;> rfl
  interpretations hypothesis state outcome interpreted := by
    cases hypothesis <;> exact interpreted

theorem recoding_covers : recoding.Covers := by
  intro hypothesis state outcome interpreted
  refine ⟨(state.2, state.1), ?_, ?_⟩
  · exact Prod.ext rfl rfl
  · cases hypothesis <;> exact interpreted

theorem recoding_is_nonidentity : recoding.stateMap (true, false) ≠ (true, false) := by
  decide

theorem recoding_preserves_robust_assessments
    (admitted : Set Interpretation) (view : View Quality Bool)
    (condition : Option Profile → Prop) :
    Robust model admitted view condition ↔ Robust recodedModel admitted view condition :=
  recoding.robust_iff recoding_covers admitted view condition

/-- A target may keep every observation and every source interpretation but
admit an additional outcome.  This model is strictly more permissive. -/
def ambiguousRecodedModel : Model Profile Quality Bool Interpretation (Option Profile) where
  observe state
    | .pain => state.2
    | .suffering => state.1
  interprets hypothesis state outcome :=
    (match hypothesis with
    | .direct => outcome = some (state.2, state.1)
    | .reverseSuffering => outcome = some (state.2, !state.1)
    | .nonExperiential => outcome = none) ∨ outcome = some (false, true)

def forwardOnly : Translation model ambiguousRecodedModel where
  stateMap state := (state.2, state.1)
  observations state feature := by cases feature <;> rfl
  interpretations hypothesis state outcome interpreted := by
    apply Or.inl
    cases hypothesis <;> exact interpreted

theorem forward_target_refuses_source_policy :
    ¬ Robust ambiguousRecodedModel {Interpretation.direct} full noSuffering := by
  apply robust_false_of_counterexample ambiguousRecodedModel
    (outcome := some (false, true))
  · exact ⟨Interpretation.direct, baseline, Set.mem_singleton _, le_rfl, Or.inr rfl⟩
  · simp [noSuffering]

/-- Faithful source-witness transport is insufficient for a preservation
claim about all target possibilities: this missing coverage is substantive. -/
theorem forward_only_does_not_cover : ¬ forwardOnly.Covers := by
  intro covers
  apply forward_target_refuses_source_policy
  exact (forwardOnly.robust_iff covers {Interpretation.direct} full noSuffering).mp
    direct_full_robust

end Controls

end Mettapedia.CognitiveArchitecture.Consciousness.InterpretationAssessment
