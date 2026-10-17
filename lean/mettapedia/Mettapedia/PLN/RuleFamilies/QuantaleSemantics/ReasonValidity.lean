import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.Tetralemma
import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.DoubleNegationCorners
import Mettapedia.Logic.NonPerception
import Mettapedia.GSLT.Causality.StructuralModels

/-!
# Valid reasons: the three marks, the wheel and the three kinds

An inference proves that a subject has a property because it has a reason.  On
Dignāga's account the reason is valid when it has three marks (*trairūpya*): it belongs
to the subject (*pakṣadharmatā*), it occurs in some similar instance, where the property
holds (*anvaya*), and it occurs in no dissimilar instance, where the property fails
(*vyatireka*).

* **Soundness needs universal exclusion.**  If the reason belongs to the subject and no
  instance whatever carries the reason without the property, the subject has the
  property (`sound_of_marks`).  Exclusion on the examined instances is not enough: the
  right cell of the wheel is compatible with a subject lacking the property
  (`DoubleNegationCorners.right_cell_not_conclusive`).
* **Observed exclusion becomes universal under perceptibility.**  The examined
  instances and all instances are two stages of a frame in which a counterexample, an
  instance carrying the reason without the property, is perceived where it is found
  (`inductionFrame`).  The examination is perceptible exactly when a counterexample
  would have been among the examined instances (`inductionFrame_perceptible_iff`); then
  exclusion on the examined instances is universal (`universal_of_observed`).
  Otherwise an unexamined counterexample leaves the inference in doubt
  (`doubt_of_unexamined_counterexample`).  Turning observed into universal exclusion is
  thus an inference from non-perception: the non-perception of a perceptible
  counterexample.
* **The wheel as evidence.**  The counts of the reason among similar and among
  dissimilar instances are the evidence for the implication from reason to property
  (`DoubleNegationCorners.pervasionEvidence`).  A right reason is exactly one whose
  implication has strength one (`wheelOf_right_iff_strength`); an inverted reason has
  strength zero with some evidence (`wheelOf_inverted_iff_strength`); a too narrow
  reason has no evidence (`wheelOf_tooNarrow_iff_total`).  Finite counts have
  confidence below one (`pervasion_confidence_lt_one`): counting alone never certifies
  a pervasion.
* **Dharmakīrti's three kinds of reason** are three certificates of pervasion:
  - *essence* (*svabhāva*): the reason's concept entails the property's
    (`essence_pervasion`); over evidence, a conjunction is an essence reason for each
    conjunct (`essence_conj`) and a disjunction is not for its disjuncts
    (`not_essence_disj`);
  - *effect* (*kārya*): the reason is an effect whose mechanism produces it only where
    the cause is present; in every solution of the mechanisms the effect is pervaded by
    the cause (`effect_pervasion`).  An intervention on the effect, a smoke machine,
    breaks the inference (`Kitchen.smokeMachine_breaks_pervasion`);
  - *non-perception* (*anupalabdhi*): the non-perception of a perceptible thing
    certifies its absence (`Frame.absent_iff_not_perceived`); applied to the
    counterexample it is `universal_of_observed`.

References: Th. Stcherbatsky, *Buddhist Logic*, vol. 1 (1932), pp. 242ff. (the three
aspects of the reason) and pp. 320–324 (the wheel); Dharmakīrti, *Nyāyabindu* II,
translated in Stcherbatsky, vol. 2 (1930), pp. 60ff. ("Negation, identity and
causation"); Y. Kajiyama, *An Introduction to Buddhist Philosophy* (1966), on
Mokṣākaragupta's *Tarkabhāṣā*.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.RuleFamilies.QuantaleSemantics.ReasonValidity

open Mettapedia.Logic.NonPerception
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.RuleFamilies.QuantaleSemantics.DoubleNegationCorners

universe u

variable {α : Type u}

/-! ## The three marks -/

/-- **Soundness**: the reason belongs to the subject, and no instance carries the
reason without the property. -/
theorem sound_of_marks {subject : α} {reason property : α → Prop} (paksha : reason subject)
    (vyatireka : ∀ x, ¬ property x → ¬ reason x) : property subject :=
  Classical.byContradiction fun lacks => vyatireka subject lacks paksha

/-! ## From observed to universal exclusion -/

/-- Two stages, the examined instances (`false`) and all instances (`true`); a
counterexample is perceived at a stage where one is found. -/
def inductionFrame (examined : Set α) (reason property : α → Prop) : Frame Bool where
  Future early late := early = false ∨ early = late
  future_refl _ := Or.inr rfl
  Perceived
    | false => ∃ x ∈ examined, reason x ∧ ¬ property x
    | true => ∃ x, reason x ∧ ¬ property x

variable {examined : Set α} {reason property : α → Prop}

/-- **The examination is perceptible exactly when a counterexample would have been
examined.** -/
theorem inductionFrame_perceptible_iff :
    (inductionFrame examined reason property).Perceptible false ↔
      ((∃ x, reason x ∧ ¬ property x) → ∃ x ∈ examined, reason x ∧ ¬ property x) := by
  constructor
  · intro perceptible counter
    exact perceptible true (Or.inl rfl) counter
  · intro covers later _ perceived
    cases later with
    | false => exact perceived
    | true => exact covers perceived

/-- **Observed exclusion is universal under perceptibility**, by the non-perception
law. -/
theorem universal_of_observed (perceptible : (inductionFrame examined reason property).Perceptible false)
    (observed : ∀ x ∈ examined, ¬ property x → ¬ reason x) :
    ∀ x, ¬ property x → ¬ reason x := by
  have notPerceived : ¬ (inductionFrame examined reason property).Perceived false := by
    rintro ⟨x, member, carries, lacks⟩
    exact observed x member lacks carries
  have absent := (Frame.absent_iff_not_perceived perceptible).mpr notPerceived
  intro x lacks carries
  exact absent true (Or.inl rfl) ⟨x, carries, lacks⟩

/-- **An unexamined counterexample leaves the inference in doubt.** -/
theorem doubt_of_unexamined_counterexample (observed : ∀ x ∈ examined, ¬ property x → ¬ reason x)
    {c : α} (carries : reason c) (lacks : ¬ property c) :
    (inductionFrame examined reason property).Doubt false := by
  refine ⟨?_, fun absent => absent true (Or.inl rfl) ⟨c, carries, lacks⟩⟩
  rintro ⟨x, member, carriesX, lacksX⟩
  exact observed x member lacksX carriesX

/-- With a perceptible examination, the three marks on the examined instances prove the
property of the subject. -/
theorem sound_of_observed_marks (perceptible : (inductionFrame examined reason property).Perceptible false)
    {subject : α} (paksha : reason subject) (observed : ∀ x ∈ examined, ¬ property x → ¬ reason x) :
    property subject :=
  sound_of_marks paksha (universal_of_observed perceptible observed)

/-! ## The wheel as evidence -/

section Wheel

variable (similar dissimilar : Finset α) (reason : α → Prop) [DecidablePred reason]

theorem wheelOf_right_iff_counts :
    wheelOf similar dissimilar reason = .right ↔
      (similar.filter reason).card ≠ 0 ∧ (dissimilar.filter reason).card = 0 := by
  rw [wheelOf, wheel_right_iff, present_occurrenceOf, present_occurrenceOf]
  simp

/-- **A right reason is one whose implication has strength one.** -/
theorem wheelOf_right_iff_strength :
    wheelOf similar dissimilar reason = .right ↔
      (pervasionEvidence similar dissimilar reason).toStrength = 1 := by
  rw [wheelOf_right_iff_counts]
  set similarCount := ((similar.filter reason).card : ENNReal) with similarCount_def
  set dissimilarCount := ((dissimilar.filter reason).card : ENNReal) with dissimilarCount_def
  have strength : (pervasionEvidence similar dissimilar reason).toStrength =
      if similarCount + dissimilarCount = 0 then 0 else similarCount / (similarCount + dissimilarCount) :=
    rfl
  have similarFinite : similarCount ≠ ⊤ := ENNReal.natCast_ne_top _
  have dissimilarFinite : dissimilarCount ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [strength]
  constructor
  · rintro ⟨similarPresent, dissimilarAbsent⟩
    have similarNonzero : similarCount ≠ 0 := by
      rw [similarCount_def]
      exact_mod_cast similarPresent
    have dissimilarZero : dissimilarCount = 0 := by
      rw [dissimilarCount_def, dissimilarAbsent, Nat.cast_zero]
    rw [dissimilarZero, add_zero, if_neg similarNonzero]
    exact ENNReal.div_self similarNonzero similarFinite
  · intro one
    by_cases zero : similarCount + dissimilarCount = 0
    · rw [if_pos zero] at one
      exact absurd one zero_ne_one
    · rw [if_neg zero] at one
      have equal := (ENNReal.div_eq_one_iff zero (ENNReal.add_ne_top.mpr ⟨similarFinite,
        dissimilarFinite⟩)).mp one
      have dissimilarZero : dissimilarCount = 0 := by
        have := congrArg (fun t => t - similarCount) equal
        simpa [ENNReal.add_sub_cancel_left similarFinite] using this.symm
      refine ⟨?_, ?_⟩
      · intro similarAbsent
        apply zero
        rw [dissimilarZero, add_zero, similarCount_def, similarAbsent, Nat.cast_zero]
      · have : ((dissimilar.filter reason).card : ENNReal) = 0 := dissimilarZero
        exact_mod_cast this

theorem wheelOf_inverted_iff_counts :
    wheelOf similar dissimilar reason = .inverted ↔
      (similar.filter reason).card = 0 ∧ (dissimilar.filter reason).card ≠ 0 := by
  have quadrant := wheel_quadrant (occurrenceOf similar reason) (occurrenceOf dissimilar reason)
  rw [present_occurrenceOf, present_occurrenceOf] at quadrant
  unfold wheelOf
  constructor
  · intro inverted
    rw [inverted] at quadrant
    by_cases similarZero : (similar.filter reason).card = 0 <;>
      by_cases dissimilarZero : (dissimilar.filter reason).card = 0 <;>
      simp_all [WheelVerdict.quadrant, supportQuadrant]
  · rintro ⟨similarZero, dissimilarPresent⟩
    simp only [similarZero, ne_eq, not_true_eq_false, decide_false, dissimilarPresent,
      not_false_eq_true, decide_true] at quadrant
    cases verdict : wheel (occurrenceOf similar reason) (occurrenceOf dissimilar reason) <;>
      simp_all [WheelVerdict.quadrant, supportQuadrant]

/-- **An inverted reason has strength zero with some evidence.** -/
theorem wheelOf_inverted_iff_strength :
    wheelOf similar dissimilar reason = .inverted ↔
      (pervasionEvidence similar dissimilar reason).toStrength = 0 ∧
        (pervasionEvidence similar dissimilar reason).total ≠ 0 := by
  rw [wheelOf_inverted_iff_counts]
  set similarCount := ((similar.filter reason).card : ENNReal) with similarCount_def
  set dissimilarCount := ((dissimilar.filter reason).card : ENNReal) with dissimilarCount_def
  have total : (pervasionEvidence similar dissimilar reason).total = similarCount + dissimilarCount :=
    rfl
  have strength : (pervasionEvidence similar dissimilar reason).toStrength =
      if similarCount + dissimilarCount = 0 then 0 else similarCount / (similarCount + dissimilarCount) :=
    rfl
  have finite : similarCount + dissimilarCount ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ENNReal.natCast_ne_top _⟩
  rw [strength, total]
  constructor
  · rintro ⟨similarZero, dissimilarPresent⟩
    have similarCountZero : similarCount = 0 := by
      rw [similarCount_def, similarZero, Nat.cast_zero]
    have dissimilarNonzero : dissimilarCount ≠ 0 := by
      rw [dissimilarCount_def]
      exact_mod_cast dissimilarPresent
    have totalNonzero : similarCount + dissimilarCount ≠ 0 := by
      rw [similarCountZero, zero_add]
      exact dissimilarNonzero
    refine ⟨?_, totalNonzero⟩
    rw [if_neg totalNonzero, similarCountZero, ENNReal.zero_div]
  · rintro ⟨zeroStrength, totalNonzero⟩
    rw [if_neg totalNonzero, ENNReal.div_eq_zero_iff] at zeroStrength
    rcases zeroStrength with similarCountZero | infinite
    · have similarZero : (similar.filter reason).card = 0 := by
        rw [similarCount_def] at similarCountZero
        exact_mod_cast similarCountZero
      refine ⟨similarZero, ?_⟩
      intro dissimilarZero
      apply totalNonzero
      rw [similarCountZero, dissimilarCount_def, dissimilarZero]
      simp
    · exact absurd infinite finite

/-- **A too narrow reason has no evidence.** -/
theorem wheelOf_tooNarrow_iff_total :
    wheelOf similar dissimilar reason = .tooNarrow ↔
      (pervasionEvidence similar dissimilar reason).total = 0 := by
  have quadrant := wheel_quadrant (occurrenceOf similar reason) (occurrenceOf dissimilar reason)
  rw [present_occurrenceOf, present_occurrenceOf] at quadrant
  have total : (pervasionEvidence similar dissimilar reason).total =
      ((similar.filter reason).card : ENNReal) + ((dissimilar.filter reason).card : ENNReal) := rfl
  rw [total]
  unfold wheelOf
  constructor
  · intro narrow
    rw [narrow] at quadrant
    by_cases similarZero : (similar.filter reason).card = 0 <;>
      by_cases dissimilarZero : (dissimilar.filter reason).card = 0 <;>
      simp_all [WheelVerdict.quadrant, supportQuadrant]
  · intro zero
    rw [add_eq_zero] at zero
    have similarZero : (similar.filter reason).card = 0 := by exact_mod_cast zero.1
    have dissimilarZero : (dissimilar.filter reason).card = 0 := by exact_mod_cast zero.2
    simp only [similarZero, dissimilarZero, ne_eq, not_true_eq_false, decide_false] at quadrant
    cases verdict : wheel (occurrenceOf similar reason) (occurrenceOf dissimilar reason) <;>
      simp_all [WheelVerdict.quadrant, supportQuadrant]

/-- **Finite counts never reach full confidence.** -/
theorem pervasion_confidence_lt_one {κ : ENNReal} (prior : κ ≠ 0) :
    BinaryEvidence.toConfidence κ (pervasionEvidence similar dissimilar reason) < 1 := by
  have finite : (pervasionEvidence similar dissimilar reason).total ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ENNReal.natCast_ne_top _⟩
  unfold BinaryEvidence.toConfidence
  rw [ENNReal.div_lt_iff (Or.inl (fun zero => prior (add_eq_zero.mp zero).2)) (Or.inr finite),
    one_mul]
  exact ENNReal.lt_add_right finite prior

end Wheel

/-! ## Dharmakīrti's three kinds of reason -/

section Essence

open Mettapedia.Logic.TheoryModel

universe uStr uSent

variable {Str : Type uStr} {Sent : Type uSent} {Sat : Str → Sent → Prop}

/-- **An essence reason**: the reason's concept entails the property's, so the
pervasion holds in every structure. -/
theorem essence_pervasion {reasonSentence propertySentence : Sent}
    (entails : Entails Sat {reasonSentence} propertySentence) (m : Str)
    (carries : Sat m reasonSentence) : Sat m propertySentence :=
  entails fun _ member => (Set.mem_singleton_iff.mp member) ▸ carries

end Essence

section EssenceOverEvidence

open Mettapedia.Logic.TheoryModel
open Mettapedia.PLN.RuleFamilies.QuantaleSemantics.Tetralemma
open Mettapedia.GSLT.KripkeTruth

variable {Atom : Type u}

/-- Over evidence, a conjunction is an essence reason for each conjunct. -/
theorem essence_conj (first second : AtomFormula Atom) :
    Entails evidenceSat {.conj first second} first := by
  intro v model
  have holds : evidenceSat v (.conj first second) := model (Set.mem_singleton _)
  have support : min (evalEvidence v first).pos (evalEvidence v second).pos ≠ 0 := holds
  exact ((min_ne_zero_iff _ _).mp support).1

/-- A disjunction is not an essence reason for its disjuncts. -/
theorem not_essence_disj :
    ¬ Entails (evidenceSat (Atom := Bool)) {.disj (.truth true) (.truth false)} (.truth true) := by
  intro entails
  let v : Bool → BinaryEvidence := fun atom => if atom then PBit.pNeither else PBit.pTrue
  have model : v ∈ models evidenceSat
      {(.disj (.truth true) (.truth false) : AtomFormula Bool)} := by
    intro φ member
    rw [Set.mem_singleton_iff.mp member]
    show max (v true).pos (v false).pos ≠ 0
    simp [v, PBit.pNeither, PBit.pTrue]
  have holds : (v true).pos ≠ 0 := entails model
  exact holds (by simp [v, PBit.pNeither])

end EssenceOverEvidence

section Effect

open Mettapedia.GSLT.Causality.StructuralModels

variable {Key : Type}

/-- The effect's mechanism produces it only where the cause is present. -/
def RequiresCause (mechanisms : Mechanisms Key Bool) (effect cause : Key) : Prop :=
  ∀ store, mechanisms effect store = true → store cause = true

/-- **An effect reason is pervaded by its cause** in every solution. -/
theorem effect_pervasion {mechanisms : Mechanisms Key Bool} {effect cause : Key}
    (requires : RequiresCause mechanisms effect cause) {store : Key → Bool}
    (solution : IsSolution mechanisms store) (seen : store effect = true) :
    store cause = true :=
  requires store (by rw [← solution effect]; exact seen)

/-- Fire and smoke. -/
inductive Kitchen where
  | fire
  | smoke
  deriving DecidableEq

namespace Kitchen

/-- Smoke rises where there is fire; whether a fire is lit is given. -/
def mechanisms (lit : Bool) : Mechanisms Kitchen Bool
  | .fire => fun _ => lit
  | .smoke => fun store => store .fire

/-- Positive control: smoke requires fire. -/
theorem smoke_requires_fire (lit : Bool) : RequiresCause (mechanisms lit) .smoke .fire :=
  fun _ produced => produced

/-- The solution with no fire lit. -/
def unlit : Kitchen → Bool := fun _ => false

/-- A smoke machine: an intervention that produces smoke whatever the fire. -/
def smokeMachine : Kitchen → Option Bool
  | .fire => none
  | .smoke => some true

/-- The solution of the intervened model with no fire lit. -/
def machineSmoke : Kitchen → Bool
  | .fire => false
  | .smoke => true

theorem machineSmoke_solution : IsSolution (surgery smokeMachine (mechanisms false)) machineSmoke := by
  intro key
  cases key <;> rfl

/-- **Negative control: the intervention breaks the inference**: smoke without fire. -/
theorem smokeMachine_breaks_pervasion :
    ¬ RequiresCause (surgery smokeMachine (mechanisms false)) .smoke .fire ∧
      machineSmoke .smoke = true ∧ machineSmoke .fire = false :=
  ⟨fun requires => absurd (requires machineSmoke rfl) (by decide), rfl, rfl⟩

end Kitchen

end Effect

end Mettapedia.PLN.RuleFamilies.QuantaleSemantics.ReasonValidity
