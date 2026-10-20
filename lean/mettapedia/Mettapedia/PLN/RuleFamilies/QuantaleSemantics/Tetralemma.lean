import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.TwistNegation
import Mettapedia.GSLT.Logic.KripkeFixedPoint
import Mettapedia.Logic.TheoryModel.DegenerateTop
import Mettapedia.Logic.TheoryModel.TwoTruths

/-!
# The four corners at the extremes of the theory lattice

Strong Kleene formulas over atoms, read in PLN evidence with the truth-order
connectives: negation exchanges the channels, conjunction and disjunction are the
truth meet and join (`evalEvidence`).  A formula is satisfied when it has support
(`evidenceSat`).

* **First degree entailment.**  Support and refutation of every formula are those of
  Dunn's evaluation of the supports of the atoms (`support_refutation_evalEvidence`,
  `evidenceSat_iff_held`): the logic of supported formulas over evidence is the
  four-valued logic of first degree entailment, whose values Priest reads as the four
  corners (catuṣkoṭi).  Magnitudes never matter for satisfaction (`evidenceSat_congr`).
* **The top theory.**  The valuations satisfying every formula, the degenerate
  structures of `Logic.TheoryModel.DegenerateTop`, are exactly those giving every atom
  both support and refutation (`degenerate_iff`); they are the models of the theory of
  all formulas (`models_univ_eq_both`).  At such a valuation all four corners of every
  claim are supported: the positive tetralemma (`corners_supported_of_degenerate`).
* **The empty theory.**  Exactly one valuation satisfies no formula, the one giving
  every atom neither support nor refutation (`theoryOf_singleton_eq_empty_iff`).  There
  the four corners of every claim are unsupported and all four are denied by
  intuitionistic negation: the negative tetralemma, Nāgārjuna's rejection of all four
  alternatives (`corners_unsupported_at_neither`, `corners_denied_at_neither`).
* **Classical evidence.**  Among valuations that never give an atom both support and
  refutation, the top theory has no model (`modelsIn_consistent_univ_eq_empty`): the
  four-valued reading supplies the "model where everything holds" that classical
  satisfaction lacks.
* **Two truths.**  Over bivalent evidence the convention that an atom holds and the
  convention that it fails cover every valuation (`covers_bivalent`); they disagree,
  so neither claim is ultimately true (`conventions_disagree`), while excluded middle
  is (`excludedMiddle_ultimate`).  Over all evidence excluded middle is not ultimate
  (`excludedMiddle_not_ultimate`): the valuation satisfying nothing lies in no carve by
  a nonempty convention (`neither_mem_models_iff`), so conventions cover all evidence
  only together with the empty convention, the ultimate itself
  (`exists_empty_of_covers_univ`).
* **Particulars and universals.**  Valuations with the same supports satisfy the same
  formulas, so no concept separates them (`no_concept_separates`), although their
  strengths differ (`strength_leaning_ne_doubting`): what evidence does in inference
  is finer than any concept of it.  Valuations with different supports are separated
  (`concept_separates_true_from_neither`).

References: J. M. Dunn, *Intuitive semantics for first-degree entailments and
"coupled trees"* (1976); G. Priest, *The Logic of the Catuskoti* (2010); Nāgārjuna,
*Mūlamadhyamakakārikā* I.1 and XXII.11.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.RuleFamilies.QuantaleSemantics.Tetralemma

open Set
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PBit
open Mettapedia.PLN.RuleFamilies.QuantaleSemantics.CDLogic
open Mettapedia.PLN.RuleFamilies.QuantaleSemantics.TwistNegation
open Mettapedia.GSLT.KripkeTruth
open Mettapedia.Logic.TheoryModel
open Mettapedia.Logic.TheoryModel.TwoTruths

universe u

variable {Atom : Type u}

/-- Strong Kleene formulas over atoms, with no base facts. -/
abbrev AtomFormula (Atom : Type u) := Formula Atom Empty

/-- **Evidence for a formula**, with the truth-order connectives. -/
noncomputable def evalEvidence (v : Atom → BinaryEvidence) : AtomFormula Atom → BinaryEvidence
  | .base fact => fact.elim
  | .truth atom => v atom
  | .neg formula => ∼(evalEvidence v formula)
  | .conj first second => tmeet (evalEvidence v first) (evalEvidence v second)
  | .disj first second => tjoin (evalEvidence v first) (evalEvidence v second)

/-- A formula is satisfied when it has support. -/
def evidenceSat (v : Atom → BinaryEvidence) (formula : AtomFormula Atom) : Prop :=
  Supported (evalEvidence v formula)

/-! ## First degree entailment -/

/-- A system with no base facts; its specifications play no role in evaluation. -/
def atomSystem : System Atom Empty where
  spec atom := .truth atom
  baseHolds fact := fact.elim
  baseFails fact := fact.elim
  base_consistent fact := fact.elim

/-- The supports of the atoms, as a Dunn valuation: held where supported, failed where
refuted. -/
def supportValuation (v : Atom → BinaryEvidence) : Valuation Atom :=
  ⟨{atom | (v atom).pos ≠ 0}, {atom | (v atom).neg ≠ 0}⟩

theorem max_ne_zero_iff (a b : ENNReal) : max a b ≠ 0 ↔ a ≠ 0 ∨ b ≠ 0 := by
  rw [Ne, ← bot_eq_zero, max_eq_bot, not_and_or]

theorem min_ne_zero_iff (a b : ENNReal) : min a b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  rw [Ne, ← bot_eq_zero, min_eq_bot, not_or]

/-- **Support and refutation are Dunn's evaluation of the supports.** -/
theorem support_refutation_evalEvidence (v : Atom → BinaryEvidence) :
    ∀ formula : AtomFormula Atom,
      ((evalEvidence v formula).pos ≠ 0 ↔ (atomSystem.eval (supportValuation v) formula).1) ∧
        ((evalEvidence v formula).neg ≠ 0 ↔ (atomSystem.eval (supportValuation v) formula).2)
  | .base fact => fact.elim
  | .truth _ => ⟨Iff.rfl, Iff.rfl⟩
  | .neg formula =>
      let ih := support_refutation_evalEvidence v formula
      ⟨ih.2, ih.1⟩
  | .conj first second => by
      have ihFirst := support_refutation_evalEvidence v first
      have ihSecond := support_refutation_evalEvidence v second
      constructor
      · show min (evalEvidence v first).pos (evalEvidence v second).pos ≠ 0 ↔ _
        rw [min_ne_zero_iff, ihFirst.1, ihSecond.1]
        rfl
      · show max (evalEvidence v first).neg (evalEvidence v second).neg ≠ 0 ↔ _
        rw [max_ne_zero_iff, ihFirst.2, ihSecond.2]
        rfl
  | .disj first second => by
      have ihFirst := support_refutation_evalEvidence v first
      have ihSecond := support_refutation_evalEvidence v second
      constructor
      · show max (evalEvidence v first).pos (evalEvidence v second).pos ≠ 0 ↔ _
        rw [max_ne_zero_iff, ihFirst.1, ihSecond.1]
        rfl
      · show min (evalEvidence v first).neg (evalEvidence v second).neg ≠ 0 ↔ _
        rw [min_ne_zero_iff, ihFirst.2, ihSecond.2]
        rfl

/-- **Satisfaction over evidence is first degree entailment's designation.** -/
theorem evidenceSat_iff_held (v : Atom → BinaryEvidence) (formula : AtomFormula Atom) :
    evidenceSat v formula ↔ (atomSystem.eval (supportValuation v) formula).1 :=
  (support_refutation_evalEvidence v formula).1

/-- Two valuations with the same supports satisfy the same formulas: magnitudes never
matter for satisfaction. -/
theorem evidenceSat_congr {v w : Atom → BinaryEvidence}
    (sameSupport : ∀ atom, ((v atom).pos ≠ 0 ↔ (w atom).pos ≠ 0) ∧
      ((v atom).neg ≠ 0 ↔ (w atom).neg ≠ 0))
    (formula : AtomFormula Atom) : evidenceSat v formula ↔ evidenceSat w formula := by
  have valuations : supportValuation v = supportValuation w := by
    unfold supportValuation
    congr 1
    · ext atom
      exact (sameSupport atom).1
    · ext atom
      exact (sameSupport atom).2
  rw [evidenceSat_iff_held, evidenceSat_iff_held, valuations]

/-! ## The top theory: both, everywhere -/

/-- Both channels nonzero is preserved by every connective. -/
theorem both_evalEvidence {v : Atom → BinaryEvidence}
    (both : ∀ atom, (v atom).pos ≠ 0 ∧ (v atom).neg ≠ 0) :
    ∀ formula : AtomFormula Atom,
      (evalEvidence v formula).pos ≠ 0 ∧ (evalEvidence v formula).neg ≠ 0
  | .base fact => fact.elim
  | .truth atom => both atom
  | .neg formula =>
      let ih := both_evalEvidence both formula
      ⟨ih.2, ih.1⟩
  | .conj first second => by
      have ihFirst := both_evalEvidence both first
      have ihSecond := both_evalEvidence both second
      exact ⟨(min_ne_zero_iff _ _).mpr ⟨ihFirst.1, ihSecond.1⟩,
        (max_ne_zero_iff _ _).mpr (Or.inl ihFirst.2)⟩
  | .disj first second => by
      have ihFirst := both_evalEvidence both first
      have ihSecond := both_evalEvidence both second
      exact ⟨(max_ne_zero_iff _ _).mpr (Or.inl ihFirst.1),
        (min_ne_zero_iff _ _).mpr ⟨ihFirst.2, ihSecond.2⟩⟩

/-- **The degenerate valuations give every atom both support and refutation.** -/
theorem degenerate_iff (v : Atom → BinaryEvidence) :
    Degenerate (evidenceSat (Atom := Atom)) v ↔ ∀ atom, (v atom).pos ≠ 0 ∧ (v atom).neg ≠ 0 := by
  constructor
  · intro degenerate atom
    exact ⟨degenerate (.truth atom), degenerate (.neg (.truth atom))⟩
  · intro both formula
    exact (both_evalEvidence both formula).1

/-- **The models of the theory of all formulas are the valuations in the `both`
corner at every atom.** -/
theorem models_univ_eq_both :
    models (evidenceSat (Atom := Atom)) univ =
      {v | ∀ atom, (v atom).pos ≠ 0 ∧ (v atom).neg ≠ 0} := by
  rw [models_univ_eq_degenerate]
  ext v
  exact degenerate_iff v

/-- **The positive tetralemma**: at a degenerate valuation all four corners of every
claim are supported. -/
theorem corners_supported_of_degenerate {v : Atom → BinaryEvidence}
    (degenerate : Degenerate (evidenceSat (Atom := Atom)) v) (formula : AtomFormula Atom) :
    ∀ corner ∈ corners (evalEvidence v formula), Supported corner := by
  have both := both_evalEvidence ((degenerate_iff v).mp degenerate) formula
  simp only [corners, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Supported, tmeet, cdNeg]
  exact ⟨both.1, both.2, (min_ne_zero_iff _ _).mpr ⟨both.1, both.2⟩,
    (min_ne_zero_iff _ _).mpr ⟨both.2, both.1⟩⟩

/-! ## The empty theory: neither, everywhere -/

/-- The valuation giving every atom neither support nor refutation. -/
def neitherValuation : Atom → BinaryEvidence := fun _ => pNeither

theorem evalEvidence_neither : ∀ formula : AtomFormula Atom,
    evalEvidence neitherValuation formula = pNeither
  | .base fact => fact.elim
  | .truth _ => rfl
  | .neg formula => by
      show ∼(evalEvidence neitherValuation formula) = pNeither
      rw [evalEvidence_neither formula]
      rfl
  | .conj first second => by
      show tmeet (evalEvidence neitherValuation first) (evalEvidence neitherValuation second) = _
      rw [evalEvidence_neither first, evalEvidence_neither second]
      ext <;> simp [tmeet, pNeither]
  | .disj first second => by
      show tjoin (evalEvidence neitherValuation first) (evalEvidence neitherValuation second) = _
      rw [evalEvidence_neither first, evalEvidence_neither second]
      ext <;> simp [tjoin, pNeither]

/-- **Exactly one valuation satisfies no formula**: neither, at every atom. -/
theorem theoryOf_singleton_eq_empty_iff (v : Atom → BinaryEvidence) :
    theoryOf (evidenceSat (Atom := Atom)) {v} = ∅ ↔ v = neitherValuation := by
  constructor
  · intro empty
    funext atom
    have notPos : ¬ evidenceSat v (.truth atom) := fun holds =>
      (eq_empty_iff_forall_notMem.mp empty) (.truth atom) (fun _ member => member ▸ holds)
    have notNeg : ¬ evidenceSat v (.neg (.truth atom)) := fun holds =>
      (eq_empty_iff_forall_notMem.mp empty) (.neg (.truth atom)) (fun _ member => member ▸ holds)
    simp only [evidenceSat, Supported, ne_eq, not_not] at notPos notNeg
    ext
    · exact notPos
    · exact notNeg
  · rintro rfl
    apply eq_empty_of_forall_notMem
    intro formula member
    have holds : evidenceSat (Atom := Atom) neitherValuation formula := member rfl
    simp [evidenceSat, Supported, evalEvidence_neither, pNeither] at holds

/-- **The negative tetralemma**: where nothing is satisfied, the four corners of every
claim are unsupported. -/
theorem corners_unsupported_at_neither (formula : AtomFormula Atom) :
    ∀ corner ∈ corners (evalEvidence (Atom := Atom) neitherValuation formula),
      ¬ Supported corner :=
  (corners_unsupported_iff _).mpr (by rw [evalEvidence_neither]; exact pNeither_isNeither)

/-- And all four are denied by intuitionistic negation. -/
theorem corners_denied_at_neither (formula : AtomFormula Atom) :
    ∀ corner ∈ corners (evalEvidence (Atom := Atom) neitherValuation formula),
      Supported (inot corner) :=
  (corners_denied_iff _).mpr (by rw [evalEvidence_neither]; exact pNeither_isNeither)

/-! ## Classical evidence -/

/-- Valuations that never give an atom both support and refutation. -/
def consistentValuations : Set (Atom → BinaryEvidence) :=
  {v | ∀ atom, (v atom).pos = 0 ∨ (v atom).neg = 0}

/-- **Among consistent valuations the top theory has no model.** -/
theorem modelsIn_consistent_univ_eq_empty [Nonempty Atom] :
    modelsIn (evidenceSat (Atom := Atom)) consistentValuations univ = ∅ := by
  apply eq_empty_of_forall_notMem
  rintro v ⟨consistent, model⟩
  obtain ⟨atom⟩ := ‹Nonempty Atom›
  have both := ((degenerate_iff v).mp fun formula => model (mem_univ formula)) atom
  rcases consistent atom with zero | zero
  · exact both.1 zero
  · exact both.2 zero

/-! ## Two truths over evidence -/

/-- Bivalent evidence: every atom is supported or refuted, and not both. -/
def bivalentValuations : Set (Atom → BinaryEvidence) :=
  {v | ∀ atom, ((v atom).pos ≠ 0 ∧ (v atom).neg = 0) ∨ ((v atom).pos = 0 ∧ (v atom).neg ≠ 0)}

/-- The convention that an atom holds (`true`) or that it fails (`false`). -/
def convention (atom : Atom) : Bool → Set (AtomFormula Atom)
  | true => {.truth atom}
  | false => {.neg (.truth atom)}

/-- The two conventions about an atom cover bivalent evidence. -/
theorem covers_bivalent (atom : Atom) :
    Covers (evidenceSat (Atom := Atom)) bivalentValuations (convention atom) := by
  intro v bivalent
  rcases bivalent atom with ⟨supported, _⟩ | ⟨_, refuted⟩
  · refine ⟨true, fun φ member => ?_⟩
    rw [show convention atom true = {.truth atom} from rfl, mem_singleton_iff] at member
    subst member
    exact supported
  · refine ⟨false, fun φ member => ?_⟩
    rw [show convention atom false = {.neg (.truth atom)} from rfl, mem_singleton_iff] at member
    subst member
    exact refuted

theorem pTrue_bivalent : (fun _ => pTrue : Atom → BinaryEvidence) ∈ bivalentValuations :=
  fun _ => Or.inl ⟨by simp [pTrue], rfl⟩

theorem pFalse_bivalent : (fun _ => pFalse : Atom → BinaryEvidence) ∈ bivalentValuations :=
  fun _ => Or.inr ⟨rfl, by simp [pFalse]⟩

theorem mem_models_empty (v : Atom → BinaryEvidence) :
    v ∈ models (evidenceSat (Atom := Atom)) ∅ :=
  fun _ member => absurd member (notMem_empty _)

/-- **The conventions disagree, and neither claim is ultimately true.** -/
theorem conventions_disagree (atom : Atom) :
    (.truth atom : AtomFormula Atom) ∈
        conventional evidenceSat bivalentValuations (convention atom true) ∅ ∧
      (.neg (.truth atom) : AtomFormula Atom) ∈
        conventional evidenceSat bivalentValuations (convention atom false) ∅ ∧
      (.truth atom : AtomFormula Atom) ∉ ultimate evidenceSat bivalentValuations ∅ ∧
      (.neg (.truth atom) : AtomFormula Atom) ∉ ultimate evidenceSat bivalentValuations ∅ := by
  have holdsTrue : (.truth atom : AtomFormula Atom) ∈
      conventional evidenceSat bivalentValuations (convention atom true) ∅ :=
    fun _ hosted => hosted.1.2 (mem_singleton _)
  have holdsFalse : (.neg (.truth atom) : AtomFormula Atom) ∈
      conventional evidenceSat bivalentValuations (convention atom false) ∅ :=
    fun _ hosted => hosted.1.2 (mem_singleton _)
  have hostedTrue : (modelsIn evidenceSat
      (carve evidenceSat bivalentValuations (convention atom true)) ∅).Nonempty :=
    ⟨fun _ => pTrue, ⟨pTrue_bivalent, fun φ member => by
      rw [show convention atom true = {.truth atom} from rfl, mem_singleton_iff] at member
      subst member
      show pTrue.pos ≠ 0
      simp [pTrue]⟩, mem_models_empty _⟩
  have hostedFalse : (modelsIn evidenceSat
      (carve evidenceSat bivalentValuations (convention atom false)) ∅).Nonempty :=
    ⟨fun _ => pFalse, ⟨pFalse_bivalent, fun φ member => by
      rw [show convention atom false = {.neg (.truth atom)} from rfl, mem_singleton_iff] at member
      subst member
      show pFalse.neg ≠ 0
      simp [pFalse]⟩, mem_models_empty _⟩
  have incompatible : ∀ v ∈ bivalentValuations, evidenceSat v (.truth atom) →
      evidenceSat v (.neg (.truth atom)) → False := by
    intro v bivalent supported refuted
    rcases bivalent atom with ⟨_, noRefutation⟩ | ⟨noSupport, _⟩
    · exact refuted noRefutation
    · exact supported noSupport
  exact ⟨holdsTrue, holdsFalse,
    not_mem_ultimate_of_disagree holdsTrue holdsFalse hostedTrue hostedFalse incompatible⟩

/-- **Over bivalent evidence excluded middle is ultimately true.** -/
theorem excludedMiddle_ultimate (atom : Atom) :
    (.disj (.truth atom) (.neg (.truth atom)) : AtomFormula Atom) ∈
      ultimate evidenceSat bivalentValuations ∅ := by
  intro v hosted
  show max (v atom).pos (v atom).neg ≠ 0
  rw [max_ne_zero_iff]
  rcases hosted.1 atom with ⟨supported, _⟩ | ⟨_, refuted⟩
  · exact Or.inl supported
  · exact Or.inr refuted

/-- **Over all evidence it is not.** -/
theorem excludedMiddle_not_ultimate (atom : Atom) :
    (.disj (.truth atom) (.neg (.truth atom)) : AtomFormula Atom) ∉
      ultimate evidenceSat univ ∅ := by
  intro ultimateTruth
  have holds := ultimateTruth ⟨mem_univ neitherValuation, mem_models_empty _⟩
  simp [evidenceSat, Supported, evalEvidence_neither, pNeither] at holds

/-- **The valuation satisfying nothing lies in no carve by a nonempty convention.** -/
theorem neither_mem_models_iff (Φ : Set (AtomFormula Atom)) :
    neitherValuation ∈ models evidenceSat Φ ↔ Φ = ∅ := by
  constructor
  · intro model
    apply eq_empty_of_forall_notMem
    intro φ member
    have holds := model member
    simp [evidenceSat, Supported, evalEvidence_neither, pNeither] at holds
  · rintro rfl
    exact mem_models_empty _

/-- **Conventions cover all evidence only together with the empty convention.** -/
theorem exists_empty_of_covers_univ {ι : Sort*} {conventions : ι → Set (AtomFormula Atom)}
    (covers : Covers evidenceSat univ conventions) : ∃ i, conventions i = ∅ := by
  obtain ⟨i, model⟩ := covers neitherValuation (mem_univ _)
  exact ⟨i, (neither_mem_models_iff _).mp model⟩

/-! ## Particulars and universals over evidence -/

/-- Evidence leaning towards the claim at every atom. -/
def leaning : Atom → BinaryEvidence := fun _ => ⟨2, 1⟩

/-- Evidence leaning against it, with the same supports. -/
def doubting : Atom → BinaryEvidence := fun _ => ⟨1, 2⟩

theorem theoryOf_leaning_eq_doubting :
    theoryOf (evidenceSat (Atom := Atom)) {leaning} = theoryOf evidenceSat {doubting} :=
  theoryOf_singleton_eq_iff.mpr (evidenceSat_congr fun _ =>
    ⟨⟨fun _ => one_ne_zero, fun _ => two_ne_zero⟩, ⟨fun _ => two_ne_zero, fun _ => one_ne_zero⟩⟩)

/-- **No concept separates them.** -/
theorem no_concept_separates {K : Set (Atom → BinaryEvidence)}
    (extent : Order.IsExtent evidenceSat K) (member : leaning ∈ K) : doubting ∈ K :=
  mem_of_isExtent_of_theoryOf_eq extent theoryOf_leaning_eq_doubting member

theorem strength_two_one : BinaryEvidence.toStrength ⟨2, 1⟩ = 2 / 3 := by
  have total : BinaryEvidence.total ⟨2, 1⟩ = 3 := by
    show (2 : ENNReal) + 1 = 3
    norm_num
  rw [BinaryEvidence.toStrength, total, if_neg (by norm_num)]

theorem strength_one_two : BinaryEvidence.toStrength ⟨1, 2⟩ = 1 / 3 := by
  have total : BinaryEvidence.total ⟨1, 2⟩ = 3 := by
    show (1 : ENNReal) + 2 = 3
    norm_num
  rw [BinaryEvidence.toStrength, total, if_neg (by norm_num)]

/-- **Their strengths differ.** -/
theorem strength_leaning_ne_doubting (atom : Atom) :
    (leaning atom).toStrength ≠ (doubting atom).toStrength := by
  show BinaryEvidence.toStrength ⟨2, 1⟩ ≠ BinaryEvidence.toStrength ⟨1, 2⟩
  rw [strength_two_one, strength_one_two]
  exact (ENNReal.div_lt_div_right (by norm_num) (by norm_num) (by norm_num)).ne'

/-- Positive control: valuations with different supports are separated by a concept. -/
theorem concept_separates_true_from_neither :
    ∃ K, Order.IsExtent (evidenceSat (Atom := Unit)) K ∧ (fun _ => pTrue) ∈ K ∧
      neitherValuation ∉ K :=
  exists_isExtent_separating_iff.mpr ⟨.truth (), by simp [evidenceSat, Supported, evalEvidence, pTrue],
    by simp [evidenceSat, Supported, evalEvidence, neitherValuation, pNeither]⟩

/-! ## Controls -/

/-- Positive control: a valuation in the `both` corner with unequal magnitudes is
degenerate. -/
theorem degenerate_example : Degenerate (evidenceSat (Atom := Unit)) (fun _ => ⟨3, 1⟩) :=
  (degenerate_iff _).mpr fun _ => ⟨by norm_num, by norm_num⟩

/-- Negative control: a supported but unrefuted atom is not degenerate; its strong
negation fails. -/
theorem not_degenerate_true : ¬ Degenerate (evidenceSat (Atom := Unit)) (fun _ => pTrue) := by
  rw [degenerate_iff]
  intro both
  exact (both ()).2 (by simp [pTrue])

end Mettapedia.PLN.RuleFamilies.QuantaleSemantics.Tetralemma
