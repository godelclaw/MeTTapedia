import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.CDLogic
import Mathlib.Order.Heyting.Regular

/-!
# Double negation on evidence: the four corners

`BinaryEvidence` is ordered by information: more evidence for and more evidence
against both count as more.  Its Heyting complement is the complement in that
order: `eᶜ` carries saturated evidence exactly in the channels where `e` carries
none (`compl_apply`), and `eᶜᶜ` saturates every channel that carries any evidence
(`compl_compl_apply`).

* **The regular elements are the four corners.**  An evidence value is fixed by
  double negation exactly when each channel is empty or saturated
  (`isRegular_iff`).  The Boolean algebra `Heyting.Regular BinaryEvidence` of
  Glivenko's theorem therefore has exactly four elements, the saturated corners
  (`regularEquivQuadrant`), ordered by Belnap's knowledge order: `neither` below
  everything, `both` above everything, `true` and `false` incomparable
  (`saturatedCorner_le_iff`).
* **Double negation is the quadrant readout.**  `eᶜᶜ` is the saturated corner of
  the quadrant of `e` (`compl_compl_eq_saturatedCorner`); two evidence values have
  the same double negation exactly when they lie in the same quadrant
  (`compl_compl_eq_iff_quadrant_eq`); Glivenko's map `Heyting.Regular.toRegular`
  is the quadrant (`toRegular_eq`).
* **The readout is a homomorphism.**  Double negation sends meet and tensor to the
  meet of corners, and join and additive revision to the join of corners
  (`compl_compl_inf`, `compl_compl_mul`, `compl_compl_sup`, `compl_compl_add`), and
  it commutes with the exchange of the two channels (`compl_compl_cdNeg`).  On the
  corners, revision is Belnap's accumulation of what has been told (the knowledge
  join) and the tensor is the knowledge meet.
* **Three involutions.**  On the corners the exchange of channels is Belnap's
  negation, the Heyting complement is the classical negation of the four-valued
  bilattice, and their composite is its conflation (`cdNeg_saturatedCorner`,
  `compl_saturatedCorner`, `compl_cdNeg_saturatedCorner`).

Double negation forgets every magnitude and keeps only which channels are touched.
The classical shadow of evidence counts is thus Belnap's four-valued square, whose
values Priest reads as the four corners (catuṣkoṭi) of Buddhist logic: true, false,
both, neither.

## Dignāga's wheel of reasons

Dignāga classified a candidate reason by its presence among the similar instances
(where the property to be proved holds) and among the dissimilar instances (where it
fails), each as present in all, in some, or in none.  Of the nine cells two are right
reasons, two are inverted, one is too wide (present in all similar and all dissimilar
instances), one is too narrow (present in none of either), and three are uncertain.
The right, inverted and inconclusive verdicts are exactly the quadrant of the evidence
whose positive channel records presence among similar instances and whose negative
channel records presence among dissimilar ones (`wheel_quadrant`): right is `true`,
inverted is `false`, too narrow is `neither`, and too wide and uncertain are `both`.
The four cells built from `all` and `none` are the saturated corners; `some` is a
magnitude that double negation forgets.  Over finite classes of instances the
channels are the counts of instances carrying the reason (`wheelOf_quadrant`).

A true pervasion with an attested similar instance always lands in a right cell
(`wheelOf_right_of_pervasion`), but the right cell does not settle the subject of the
inference, which belongs to neither class (`right_cell_not_conclusive`).

References: V. Glivenko, *Sur quelques points de la logique de M. Brouwer* (1929);
N. Belnap, *A Useful Four-Valued Logic* (1977); O. Arieli and A. Avron, *Reasoning
with logical bilattices*, J. Logic Lang. Inform. 5 (1996); G. Priest, *The Logic of
the Catuskoti*, Comparative Philosophy 1(2) (2010); T. Onishi, *The catuṣkoṭi in a
bilattice*, Prospectus 17 (2014); Th. Stcherbatsky, *Buddhist Logic*, vol. 1 (1932),
pp. 320–324, for Dignāga's table and its numbering.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.RuleFamilies.QuantaleSemantics.DoubleNegationCorners

open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit
open Mettapedia.PLN.RuleFamilies.QuantaleSemantics.CDLogic
open scoped ENNReal

/-! ## The complement and its double -/

/-- The Heyting complement saturates exactly the empty channels. -/
theorem compl_apply (e : BinaryEvidence) :
    eᶜ = ⟨if e.pos = 0 then ⊤ else 0, if e.neg = 0 then ⊤ else 0⟩ := by
  show BinaryEvidence.himp e ⊥ = _
  ext
  · show (if e.pos ≤ 0 then ⊤ else 0) = _
    simp only [nonpos_iff_eq_zero]
  · show (if e.neg ≤ 0 then ⊤ else 0) = _
    simp only [nonpos_iff_eq_zero]

/-- Double negation saturates every channel that carries evidence. -/
theorem compl_compl_apply (e : BinaryEvidence) :
    eᶜᶜ = ⟨if e.pos = 0 then 0 else ⊤, if e.neg = 0 then 0 else ⊤⟩ := by
  rw [compl_apply eᶜ, compl_apply e]
  ext
  · by_cases h : e.pos = 0 <;> simp [h]
  · by_cases h : e.neg = 0 <;> simp [h]

/-- **The regular elements**: each channel empty or saturated. -/
theorem isRegular_iff (e : BinaryEvidence) :
    Heyting.IsRegular e ↔ (e.pos = 0 ∨ e.pos = ⊤) ∧ (e.neg = 0 ∨ e.neg = ⊤) := by
  rw [Heyting.IsRegular, compl_compl_apply]
  constructor
  · intro fixed
    have pos := congrArg BinaryEvidence.pos fixed
    have neg := congrArg BinaryEvidence.neg fixed
    simp only at pos neg
    constructor
    · by_cases zero : e.pos = 0
      · exact Or.inl zero
      · rw [if_neg zero] at pos
        exact Or.inr pos.symm
    · by_cases zero : e.neg = 0
      · exact Or.inl zero
      · rw [if_neg zero] at neg
        exact Or.inr neg.symm
  · rintro ⟨pos, neg⟩
    ext
    · rcases pos with pos | pos <;> simp [pos]
    · rcases neg with neg | neg <;> simp [neg]

/-! ## The saturated corners -/

/-- The saturated representative of each quadrant. -/
def saturatedCorner : Quadrant → BinaryEvidence
  | .true => ⟨⊤, 0⟩
  | .false => ⟨0, ⊤⟩
  | .neither => ⟨0, 0⟩
  | .both => ⟨⊤, ⊤⟩

theorem quadrant_saturatedCorner (q : Quadrant) : quadrant (saturatedCorner q) = q := by
  cases q <;> simp [quadrant, saturatedCorner]

theorem isRegular_saturatedCorner (q : Quadrant) : Heyting.IsRegular (saturatedCorner q) := by
  rw [isRegular_iff]
  cases q <;> simp [saturatedCorner]

/-- **Double negation is the saturated corner of the quadrant.** -/
theorem compl_compl_eq_saturatedCorner (e : BinaryEvidence) :
    eᶜᶜ = saturatedCorner (quadrant e) := by
  rw [compl_compl_apply]
  unfold quadrant
  by_cases pos : e.pos = 0 <;> by_cases neg : e.neg = 0 <;> simp [pos, neg, saturatedCorner]

/-- Double negation keeps the quadrant. -/
theorem quadrant_compl_compl (e : BinaryEvidence) : quadrant eᶜᶜ = quadrant e := by
  rw [compl_compl_eq_saturatedCorner, quadrant_saturatedCorner]

/-- **Double negation and the quadrant have the same fibres.** -/
theorem compl_compl_eq_iff_quadrant_eq (e e' : BinaryEvidence) :
    eᶜᶜ = e'ᶜᶜ ↔ quadrant e = quadrant e' := by
  constructor
  · intro equal
    rw [← quadrant_compl_compl e, equal, quadrant_compl_compl]
  · intro equal
    rw [compl_compl_eq_saturatedCorner, compl_compl_eq_saturatedCorner, equal]

/-- **The Boolean algebra of regular evidence is the four corners.** -/
noncomputable def regularEquivQuadrant : Heyting.Regular BinaryEvidence ≃ Quadrant where
  toFun r := quadrant (r : BinaryEvidence)
  invFun q := ⟨saturatedCorner q, isRegular_saturatedCorner q⟩
  left_inv r := by
    apply Heyting.Regular.coe_injective
    show saturatedCorner (quadrant (r : BinaryEvidence)) = r
    rw [← compl_compl_eq_saturatedCorner]
    exact r.prop.eq
  right_inv q := quadrant_saturatedCorner q

/-- **Glivenko's map is the quadrant readout.** -/
theorem toRegular_eq (e : BinaryEvidence) :
    Heyting.Regular.toRegular e = regularEquivQuadrant.symm (quadrant e) := by
  apply Heyting.Regular.coe_injective
  rw [Heyting.Regular.coe_toRegular]
  exact compl_compl_eq_saturatedCorner e

/-- **The corners carry Belnap's knowledge order**: `neither` is below and `both`
above everything, and distinct `true` and `false` are incomparable. -/
theorem saturatedCorner_le_iff (q q' : Quadrant) :
    saturatedCorner q ≤ saturatedCorner q' ↔ q = q' ∨ q = .neither ∨ q' = .both := by
  cases q <;> cases q' <;> simp [saturatedCorner, BinaryEvidence.le_def]

/-! ## The readout is a homomorphism -/

theorem compl_compl_inf (a b : BinaryEvidence) : (a ⊓ b)ᶜᶜ = aᶜᶜ ⊓ bᶜᶜ :=
  compl_compl_inf_distrib a b

theorem compl_compl_sup (a b : BinaryEvidence) : (a ⊔ b)ᶜᶜ = aᶜᶜ ⊔ bᶜᶜ := by
  rw [compl_compl_apply, compl_compl_apply a, compl_compl_apply b]
  ext
  · show (if max a.pos b.pos = 0 then 0 else ⊤) =
      max (if a.pos = 0 then 0 else ⊤) (if b.pos = 0 then 0 else ⊤)
    by_cases ha : a.pos = 0 <;> by_cases hb : b.pos = 0 <;> simp [ha, hb]
  · show (if max a.neg b.neg = 0 then 0 else ⊤) =
      max (if a.neg = 0 then 0 else ⊤) (if b.neg = 0 then 0 else ⊤)
    by_cases ha : a.neg = 0 <;> by_cases hb : b.neg = 0 <;> simp [ha, hb]

/-- The tensor (sequential composition) descends to the knowledge meet. -/
theorem compl_compl_mul (a b : BinaryEvidence) : (a * b)ᶜᶜ = aᶜᶜ ⊓ bᶜᶜ := by
  rw [compl_compl_apply, compl_compl_apply a, compl_compl_apply b]
  ext
  · show (if a.pos * b.pos = 0 then 0 else ⊤) =
      min (if a.pos = 0 then 0 else ⊤) (if b.pos = 0 then 0 else ⊤)
    by_cases ha : a.pos = 0 <;> by_cases hb : b.pos = 0 <;> simp [ha, hb]
  · show (if a.neg * b.neg = 0 then 0 else ⊤) =
      min (if a.neg = 0 then 0 else ⊤) (if b.neg = 0 then 0 else ⊤)
    by_cases ha : a.neg = 0 <;> by_cases hb : b.neg = 0 <;> simp [ha, hb]

/-- Additive revision (pooling independent evidence) descends to the knowledge
join: on the corners it accumulates what has been told. -/
theorem compl_compl_add (a b : BinaryEvidence) : (a + b)ᶜᶜ = aᶜᶜ ⊔ bᶜᶜ := by
  rw [compl_compl_apply, compl_compl_apply a, compl_compl_apply b]
  ext
  · show (if a.pos + b.pos = 0 then 0 else ⊤) =
      max (if a.pos = 0 then 0 else ⊤) (if b.pos = 0 then 0 else ⊤)
    by_cases ha : a.pos = 0 <;> by_cases hb : b.pos = 0 <;> simp [ha, hb]
  · show (if a.neg + b.neg = 0 then 0 else ⊤) =
      max (if a.neg = 0 then 0 else ⊤) (if b.neg = 0 then 0 else ⊤)
    by_cases ha : a.neg = 0 <;> by_cases hb : b.neg = 0 <;> simp [ha, hb]

/-- The exchange of the two channels commutes with the Heyting complement. -/
theorem compl_cdNeg (e : BinaryEvidence) : (∼e)ᶜ = ∼(eᶜ) := by
  rw [compl_apply, compl_apply]
  rfl

theorem compl_compl_cdNeg (e : BinaryEvidence) : (∼e)ᶜᶜ = ∼(eᶜᶜ) := by
  rw [compl_cdNeg, compl_cdNeg]

/-! ## Three involutions of the corners

On the four corners the exchange of channels is Belnap's negation (it swaps `true`
and `false` and fixes `both` and `neither`), the Heyting complement is the classical
negation of the four-valued bilattice (it swaps `true` with `false` and `both` with
`neither`), and their composite is the conflation (it fixes `true` and `false` and
swaps `both` with `neither`). -/

/-- Belnap's negation on quadrants. -/
def negateQuadrant : Quadrant → Quadrant
  | .true => .false
  | .false => .true
  | .neither => .neither
  | .both => .both

/-- The conflation on quadrants. -/
def conflateQuadrant : Quadrant → Quadrant
  | .true => .true
  | .false => .false
  | .neither => .both
  | .both => .neither

theorem cdNeg_saturatedCorner (q : Quadrant) :
    ∼(saturatedCorner q) = saturatedCorner (negateQuadrant q) := by
  cases q <;> rfl

/-- **The Heyting complement is the classical negation of the corners.** -/
theorem compl_saturatedCorner (q : Quadrant) :
    (saturatedCorner q)ᶜ = saturatedCorner (conflateQuadrant (negateQuadrant q)) := by
  rw [compl_apply]
  cases q <;> simp [saturatedCorner, negateQuadrant, conflateQuadrant]

/-- The conflation is the complement of the exchange. -/
theorem compl_cdNeg_saturatedCorner (q : Quadrant) :
    (∼(saturatedCorner q))ᶜ = saturatedCorner (conflateQuadrant q) := by
  rw [cdNeg_saturatedCorner, compl_saturatedCorner]
  cases q <;> rfl

/-! ## Controls -/

/-- Positive control: three positive observations and no negative one have the
saturated `true` corner as double negation. -/
theorem compl_compl_three_zero : (⟨3, 0⟩ : BinaryEvidence)ᶜᶜ = ⟨⊤, 0⟩ := by
  rw [compl_compl_apply]
  simp

/-- Negative control: finite nonzero evidence is not regular. -/
theorem not_isRegular_one_zero : ¬ Heyting.IsRegular (⟨1, 0⟩ : BinaryEvidence) := by
  rw [isRegular_iff]
  simp

/-- Same quadrant, same double negation, although the counts and strengths differ. -/
theorem compl_compl_one_one_eq_two_five :
    (⟨1, 1⟩ : BinaryEvidence)ᶜᶜ = (⟨2, 5⟩ : BinaryEvidence)ᶜᶜ := by
  rw [compl_compl_apply, compl_compl_apply]
  simp

/-- Different quadrants, different double negations. -/
theorem compl_compl_one_zero_ne_zero_one :
    (⟨1, 0⟩ : BinaryEvidence)ᶜᶜ ≠ (⟨0, 1⟩ : BinaryEvidence)ᶜᶜ := by
  rw [compl_compl_apply, compl_compl_apply]
  intro equal
  have pos := congrArg BinaryEvidence.pos equal
  simp at pos

/-! ## Dignāga's wheel of reasons -/

/-- Presence of a candidate reason in a class of instances. -/
inductive Occurrence
  | all
  | none
  | some
  deriving DecidableEq, Repr

/-- The reason occurs in at least one instance of the class. -/
def Occurrence.present : Occurrence → Bool
  | .none => false
  | _ => true

/-- Dignāga's verdicts. -/
inductive WheelVerdict
  | right
  | inverted
  | tooWide
  | tooNarrow
  | uncertain
  deriving DecidableEq, Repr

/-- **Dignāga's table**, indexed by presence among similar and among dissimilar
instances.  The comments give Stcherbatsky's numbering of the nine positions. -/
def wheel : Occurrence → Occurrence → WheelVerdict
  | .all, .all => .tooWide       -- 1
  | .none, .all => .inverted     -- 2
  | .some, .all => .uncertain    -- 3
  | .all, .none => .right        -- 4
  | .none, .none => .tooNarrow   -- 5
  | .some, .none => .right       -- 6
  | .all, .some => .uncertain    -- 7
  | .none, .some => .inverted    -- 8
  | .some, .some => .uncertain   -- 9

/-- The quadrant of a verdict. -/
def WheelVerdict.quadrant : WheelVerdict → Quadrant
  | .right => .true
  | .inverted => .false
  | .tooNarrow => .neither
  | .tooWide => .both
  | .uncertain => .both

/-- The quadrant of a pair of support bits. -/
def supportQuadrant : Bool → Bool → Quadrant
  | true, false => .true
  | false, true => .false
  | false, false => .neither
  | true, true => .both

/-- The quadrant of evidence is the quadrant of its two support bits. -/
theorem quadrant_eq_supportQuadrant (e : BinaryEvidence) :
    quadrant e = supportQuadrant (decide (e.pos ≠ 0)) (decide (e.neg ≠ 0)) := by
  unfold quadrant
  by_cases pos : e.pos = 0 <;> by_cases neg : e.neg = 0 <;> simp [pos, neg, supportQuadrant]

/-- **The wheel is the quadrant of presence among similar and dissimilar
instances.** -/
theorem wheel_quadrant (similar dissimilar : Occurrence) :
    (wheel similar dissimilar).quadrant = supportQuadrant similar.present dissimilar.present := by
  cases similar <;> cases dissimilar <;> rfl

/-- The verdict is right exactly in the `true` quadrant: present among similar and
absent from dissimilar instances. -/
theorem wheel_right_iff (similar dissimilar : Occurrence) :
    wheel similar dissimilar = .right ↔
      similar.present = true ∧ dissimilar.present = false := by
  cases similar <;> cases dissimilar <;> simp [wheel, Occurrence.present]

section Instances

variable {α : Type*}

/-- The presence of a reason in a finite class of instances. -/
def occurrenceOf (instances : Finset α) (reason : α → Prop) [DecidablePred reason] :
    Occurrence :=
  if (instances.filter reason).card = 0 then .none
  else if (instances.filter reason).card = instances.card then .all
  else .some

theorem present_occurrenceOf (instances : Finset α) (reason : α → Prop) [DecidablePred reason] :
    (occurrenceOf instances reason).present = decide ((instances.filter reason).card ≠ 0) := by
  unfold occurrenceOf
  by_cases zero : (instances.filter reason).card = 0
  · simp [zero, Occurrence.present]
  · rw [if_neg zero]
    have present : decide ((instances.filter reason).card ≠ 0) = true := decide_eq_true zero
    rw [present]
    by_cases full : (instances.filter reason).card = instances.card
    · rw [if_pos full]
      rfl
    · rw [if_neg full]
      rfl

/-- The wheel position of a reason over finite similar and dissimilar instances. -/
def wheelOf (similar dissimilar : Finset α) (reason : α → Prop) [DecidablePred reason] :
    WheelVerdict :=
  wheel (occurrenceOf similar reason) (occurrenceOf dissimilar reason)

/-- The pervasion evidence of a reason: its count among similar instances and its
count among dissimilar instances. -/
def pervasionEvidence (similar dissimilar : Finset α) (reason : α → Prop)
    [DecidablePred reason] : BinaryEvidence :=
  ⟨((similar.filter reason).card : ℝ≥0∞), ((dissimilar.filter reason).card : ℝ≥0∞)⟩

/-- **Over finite instances, the wheel is the quadrant of the counts.** -/
theorem wheelOf_quadrant (similar dissimilar : Finset α) (reason : α → Prop)
    [DecidablePred reason] :
    (wheelOf similar dissimilar reason).quadrant =
      quadrant (pervasionEvidence similar dissimilar reason) := by
  rw [wheelOf, wheel_quadrant, present_occurrenceOf, present_occurrenceOf,
    quadrant_eq_supportQuadrant]
  simp [pervasionEvidence]

/-- A true pervasion (wherever the reason is, the property is) with a similar
instance carrying the reason always lands in a right cell, provided the dissimilar
instances are exactly those lacking the property. -/
theorem wheelOf_right_of_pervasion (similar dissimilar : Finset α) (reason property : α → Prop)
    [DecidablePred reason] (dissimilar_lacks : ∀ x ∈ dissimilar, ¬ property x)
    (pervasion : ∀ x, reason x → property x) (attested : ∃ x ∈ similar, reason x) :
    wheelOf similar dissimilar reason = .right := by
  rw [wheelOf, wheel_right_iff, present_occurrenceOf, present_occurrenceOf]
  obtain ⟨x, member, holds⟩ := attested
  constructor
  · simp only [ne_eq, decide_eq_true_eq]
    exact Finset.card_ne_zero.mpr ⟨x, Finset.mem_filter.mpr ⟨member, holds⟩⟩
  · simp only [ne_eq, decide_eq_false_iff_not, not_not, Finset.card_eq_zero]
    exact Finset.filter_eq_empty_iff.mpr fun y member' carries =>
      dissimilar_lacks y member' (pervasion y carries)

end Instances

/-- **The right cell does not settle the subject.**  The subject of an inference
belongs to neither class; here the reason occurs in the only similar instance and
in no dissimilar one, the subject carries the reason, and the subject lacks the
property. -/
theorem right_cell_not_conclusive :
    ∃ (similar dissimilar : Finset (Fin 3)) (subject : Fin 3) (reason property : Fin 3 → Prop)
      (_ : DecidablePred reason),
      subject ∉ similar ∧ subject ∉ dissimilar ∧
      (∀ x ∈ similar, property x) ∧ (∀ x ∈ dissimilar, ¬ property x) ∧
      wheelOf similar dissimilar reason = .right ∧ reason subject ∧ ¬ property subject := by
  refine ⟨{0}, {1}, 2, fun x => x ≠ 1, fun x => x = 0, inferInstance, ?_⟩
  refine ⟨by decide, by decide, ?_, ?_, ?_, by decide, by decide⟩
  · intro x member
    simpa using member
  · intro x member
    simp only [Finset.mem_singleton] at member
    subst member
    decide
  · decide

end Mettapedia.PLN.RuleFamilies.QuantaleSemantics.DoubleNegationCorners
