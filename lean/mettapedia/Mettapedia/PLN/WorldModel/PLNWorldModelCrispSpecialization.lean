import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.PLN.WorldModel.WorldModelCalculus
import Mettapedia.PLN.WorldModel.WorldModelAdditive

/-!
# The world model of a crisp semantics

A crisp semantics is a relation `satisfies : Point → Query → Prop`.  Its world
model has multisets of points as states; the evidence for a query counts the
points that satisfy it and the points that do not (`crispEvidence`).  This is
the free additive extension of the one-point evidence `⟨1, 0⟩` or `⟨0, 1⟩`
(`crispEvidence_eq_additiveExtension`), and it is a `BinaryWorldModel`
(`crispWorldModel`).

Every logic bridge that counts satisfiers (first-order and infinitary
first-order sentences, Church/Henkin HOL, set-theoretic HOL, modal Kripke and
neighborhood models, predicate codes) is this world model for its own
`satisfies`.  The theorem family is proved here once:

- singleton states read truth as strength `1` and falsity as strength `0`
  (`singleton_adequacy_strength_one`);
- pointwise implication is singleton-strength consequence
  (`pointwiseImplies_iff_singletonStrengthLE`) and lifts to every state
  (`queryStrength_le_of_pointwise`);
- the same holds relative to an admissible class of points, such as the models
  of a theory or the frames of a class (`pointwiseImpliesOn_iff_singletonStrengthLEOn`,
  `queryStrength_le_of_pointwise_on`);
- pointwise equivalence is WM query equivalence (`pointwiseIff_iff_queryEq`);
- each of these gives a WM consequence rule (`wmConsequenceRule_of_pointwise`,
  `wmConsequenceRuleOn_of_pointwise`);
- an implication relation sound and complete for pointwise implication is
  singleton consequence, and a pointed counterexample refutes it
  (`externalImplication_iff_singletonStrengthLE_of_sound_complete`,
  `singletonStrengthLE_not_of_counterexample`).

The countably infinitary closure of a crisp semantics (`InfQuery`,
`SatisfiesInf`) is again a crisp semantics, with conjunction elimination and
disjunction introduction on every state.

What this module is not: it does not cover graded or fuzzy satisfaction, only
crisp `Prop`-valued satisfaction; and it states no proof theory.  A bridge adds
its own soundness and completeness theorem, which turns `provable (φ → ψ)` into
pointwise implication.
-/

namespace Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization

open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelAdditive
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open scoped ENNReal

universe u v

variable {Point : Type u} {Query : Type v}

/-- Multisets of points are states, revised by multiset sum. -/
instance instEvidenceTypeMultiset : EvidenceType (Multiset Point) :=
  multisetEvidenceType Point

/-- Count evidence of a multiset of points for a crisp semantics: `pos` counts
the points satisfying `q`, `neg` the points that do not. -/
noncomputable def crispEvidence
    (satisfies : Point → Query → Prop)
    (W : Multiset Point) (q : Query) : BinaryEvidence := by
  classical
  exact
    ⟨(Multiset.countP (fun x => satisfies x q) W : ℝ≥0∞),
     (Multiset.countP (fun x => ¬ satisfies x q) W : ℝ≥0∞)⟩

theorem crispEvidence_add
    (satisfies : Point → Query → Prop)
    (W₁ W₂ : Multiset Point) (q : Query) :
    crispEvidence satisfies (W₁ + W₂) q =
      crispEvidence satisfies W₁ q + crispEvidence satisfies W₂ q := by
  classical
  apply BinaryEvidence.ext'
  · simp [crispEvidence, Multiset.countP_add, BinaryEvidence.hplus_def]
  · simp [crispEvidence, Multiset.countP_add, BinaryEvidence.hplus_def]

theorem crispEvidence_zero
    (satisfies : Point → Query → Prop) (q : Query) :
    crispEvidence satisfies (0 : Multiset Point) q = 0 := by
  classical
  simp only [crispEvidence, Multiset.countP_zero, Nat.cast_zero]
  rfl

theorem crispEvidence_singleton_of_satisfies
    (satisfies : Point → Query → Prop)
    (x : Point) (q : Query) (h : satisfies x q) :
    crispEvidence satisfies ({x} : Multiset Point) q = ⟨1, 0⟩ := by
  classical
  ext <;> simp [crispEvidence, ← Multiset.cons_zero, h]

theorem crispEvidence_singleton_of_not_satisfies
    (satisfies : Point → Query → Prop)
    (x : Point) (q : Query) (h : ¬ satisfies x q) :
    crispEvidence satisfies ({x} : Multiset Point) q = ⟨0, 1⟩ := by
  classical
  ext <;> simp [crispEvidence, ← Multiset.cons_zero, h]

/-- The one-point evidence of a crisp semantics. -/
noncomputable def crispAtom (satisfies : Point → Query → Prop) :
    AtomicEvidenceContribution Point Query :=
  fun x q => crispEvidence satisfies {x} q

/-- Crisp counting is the free additive extension of its one-point evidence. -/
theorem crispEvidence_eq_additiveExtension
    (satisfies : Point → Query → Prop) (W : Multiset Point) (q : Query) :
    crispEvidence satisfies W q = additiveExtension (crispAtom satisfies) W q := by
  induction W using Multiset.induction_on with
  | empty => rw [crispEvidence_zero, additiveExtension_zero]
  | cons x W ih =>
      rw [additiveExtension_cons, ← ih, ← Multiset.singleton_add, crispEvidence_add]
      rfl

/-- The world model of a crisp semantics. -/
@[instance_reducible] noncomputable def crispWorldModel (satisfies : Point → Query → Prop) :
    BinaryWorldModel (Multiset Point) Query where
  evidence := crispEvidence satisfies
  evidence_add := crispEvidence_add satisfies
  evidence_zero := crispEvidence_zero satisfies

@[simp] theorem evidence_crispWorldModel
    (satisfies : Point → Query → Prop) (W : Multiset Point) (q : Query) :
    @BinaryWorldModel.evidence (Multiset Point) Query _ (crispWorldModel satisfies) W q =
      crispEvidence satisfies W q :=
  rfl

/-! ## Singleton states -/

/-- Singleton states recover crisp strength `1` from truth. -/
theorem queryStrength_singleton_of_satisfies
    (satisfies : Point → Query → Prop)
    (x : Point) (q : Query) (h : satisfies x q) :
    @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies)
      ({x} : Multiset Point) q = 1 := by
  unfold BinaryWorldModel.queryStrength
  rw [evidence_crispWorldModel, crispEvidence_singleton_of_satisfies satisfies x q h]
  simp [BinaryEvidence.toStrength, BinaryEvidence.total]

/-- Singleton states recover crisp strength `0` from refutation. -/
theorem queryStrength_singleton_of_not_satisfies
    (satisfies : Point → Query → Prop)
    (x : Point) (q : Query) (h : ¬ satisfies x q) :
    @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies)
      ({x} : Multiset Point) q = 0 := by
  unfold BinaryWorldModel.queryStrength
  rw [evidence_crispWorldModel, crispEvidence_singleton_of_not_satisfies satisfies x q h]
  simp [BinaryEvidence.toStrength, BinaryEvidence.total]

/-- Singleton adequacy: truth iff singleton strength is `1`. -/
theorem singleton_adequacy_strength_one
    (satisfies : Point → Query → Prop)
    (x : Point) (q : Query) :
    satisfies x q ↔
      @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies)
        ({x} : Multiset Point) q = 1 := by
  refine ⟨queryStrength_singleton_of_satisfies satisfies x q, fun h => ?_⟩
  by_contra hs
  rw [queryStrength_singleton_of_not_satisfies satisfies x q hs] at h
  exact zero_ne_one h

/-- At a single point, singleton-strength order is implication. -/
theorem singletonStrengthLE_singleton_iff_imp
    (satisfies : Point → Query → Prop) (x : Point) (q₁ q₂ : Query) :
    @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies)
        ({x} : Multiset Point) q₁ ≤
      @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies)
        ({x} : Multiset Point) q₂ ↔
      (satisfies x q₁ → satisfies x q₂) := by
  constructor
  · intro hle hq₁
    by_contra hq₂
    rw [queryStrength_singleton_of_satisfies satisfies x q₁ hq₁,
      queryStrength_singleton_of_not_satisfies satisfies x q₂ hq₂] at hle
    exact absurd hle (by simp)
  · intro himp
    by_cases hq₁ : satisfies x q₁
    · rw [queryStrength_singleton_of_satisfies satisfies x q₁ hq₁,
        queryStrength_singleton_of_satisfies satisfies x q₂ (himp hq₁)]
    · rw [queryStrength_singleton_of_not_satisfies satisfies x q₁ hq₁]
      exact zero_le

/-! ## Consequence relative to an admissible class of points -/

/-- Pointwise implication on the admissible points. -/
def pointwiseImpliesOn
    (satisfies : Point → Query → Prop) (admissible : Point → Prop)
    (q₁ q₂ : Query) : Prop :=
  ∀ x, admissible x → satisfies x q₁ → satisfies x q₂

/-- Singleton-strength consequence on the admissible points. -/
def singletonStrengthLEOn
    (satisfies : Point → Query → Prop) (admissible : Point → Prop)
    (q₁ q₂ : Query) : Prop :=
  ∀ x, admissible x →
    @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies)
        ({x} : Multiset Point) q₁ ≤
      @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies)
        ({x} : Multiset Point) q₂

/-- On the admissible points, pointwise implication is singleton-strength
consequence. -/
theorem pointwiseImpliesOn_iff_singletonStrengthLEOn
    (satisfies : Point → Query → Prop) (admissible : Point → Prop)
    (q₁ q₂ : Query) :
    pointwiseImpliesOn satisfies admissible q₁ q₂ ↔
      singletonStrengthLEOn satisfies admissible q₁ q₂ := by
  constructor
  · intro himp x hx
    by_cases hq₁ : satisfies x q₁
    · rw [queryStrength_singleton_of_satisfies satisfies x q₁ hq₁,
        queryStrength_singleton_of_satisfies satisfies x q₂ (himp x hx hq₁)]
    · rw [queryStrength_singleton_of_not_satisfies satisfies x q₁ hq₁]
      exact zero_le
  · intro hle x hx hq₁
    by_contra hq₂
    have h := hle x hx
    rw [queryStrength_singleton_of_satisfies satisfies x q₁ hq₁,
      queryStrength_singleton_of_not_satisfies satisfies x q₂ hq₂] at h
    exact absurd h (by simp)

private theorem countP_le_countP_of_imp_on
    (W : Multiset Point) {p q : Point → Prop} [DecidablePred p] [DecidablePred q]
    (himp : ∀ x ∈ W, p x → q x) :
    Multiset.countP p W ≤ Multiset.countP q W := by
  induction W using Multiset.induction_on with
  | empty => simp
  | @cons a W ih =>
      have himp_tail : ∀ x ∈ W, p x → q x := fun x hx hp => himp x (by simp [hx]) hp
      by_cases hp : p a
      · have hq : q a := himp a (by simp) hp
        simpa [Multiset.countP_cons_of_pos, hp, hq] using Nat.succ_le_succ (ih himp_tail)
      · by_cases hq : q a
        · have hstep : Multiset.countP p W ≤ Multiset.countP q W + 1 :=
            le_trans (ih himp_tail) (Nat.le_succ _)
          simpa [Multiset.countP_cons_of_neg, hp, Multiset.countP_cons_of_pos, hq] using hstep
        · simpa [Multiset.countP_cons_of_neg, hp, hq] using ih himp_tail

/-- The total count of crisp evidence is the size of the state. -/
theorem crispEvidence_total
    (satisfies : Point → Query → Prop) (W : Multiset Point) (q : Query) :
    (crispEvidence satisfies W q).total = (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP (fun x : Point => satisfies x q) W +
          Multiset.countP (fun x : Point => ¬ satisfies x q) W := by
    simpa using
      (Multiset.card_eq_countP_add_countP (p := fun x : Point => satisfies x q) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP (fun x : Point => satisfies x q) W : ℝ≥0∞) +
          (Multiset.countP (fun x : Point => ¬ satisfies x q) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold crispEvidence BinaryEvidence.total
  simpa using hcard.symm

/-- On a nonempty state, crisp strength is the fraction of points satisfying
the query. -/
theorem queryStrength_eq_countP_div
    (satisfies : Point → Query → Prop) (W : Multiset Point) (q : Query)
    [DecidablePred fun x => satisfies x q] (hW : W ≠ 0) :
    @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q =
      (Multiset.countP (fun x => satisfies x q) W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
  have hcard : (W.card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast fun h => hW (Multiset.card_eq_zero.mp h)
  unfold BinaryWorldModel.queryStrength BinaryEvidence.toStrength
  rw [evidence_crispWorldModel, crispEvidence_total, if_neg hcard]
  simp only [crispEvidence]
  congr

/-- Pointwise implication on the admissible points lifts to every state of
admissible points. -/
theorem queryStrength_le_of_pointwise_on
    (satisfies : Point → Query → Prop) (admissible : Point → Prop)
    (W : Multiset Point) (q₁ q₂ : Query)
    (hW : ∀ x ∈ W, admissible x)
    (himp : pointwiseImpliesOn satisfies admissible q₁ q₂) :
    @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q₁ ≤
      @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q₂ := by
  let p₁ : Point → Prop := fun x => satisfies x q₁
  let p₂ : Point → Prop := fun x => satisfies x q₂
  let : DecidablePred p₁ := Classical.decPred p₁
  let : DecidablePred p₂ := Classical.decPred p₂
  have hq₁ :
      @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q₁ =
        if (W.card : ℝ≥0∞) = 0 then 0
        else (Multiset.countP p₁ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold BinaryWorldModel.queryStrength BinaryEvidence.toStrength
    rw [evidence_crispWorldModel, crispEvidence_total satisfies W q₁]
    simp [crispEvidence, p₁]
  have hq₂ :
      @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q₂ =
        if (W.card : ℝ≥0∞) = 0 then 0
        else (Multiset.countP p₂ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold BinaryWorldModel.queryStrength BinaryEvidence.toStrength
    rw [evidence_crispWorldModel, crispEvidence_total satisfies W q₂]
    simp [crispEvidence, p₂]
  rw [hq₁, hq₂]
  by_cases hcard : (W.card : ℝ≥0∞) = 0
  · simp [hcard]
  · simp only [hcard, if_false]
    have hcount : (Multiset.countP p₁ W : ℝ≥0∞) ≤ (Multiset.countP p₂ W : ℝ≥0∞) := by
      exact_mod_cast countP_le_countP_of_imp_on W (fun x hx h => himp x (hW x hx) h)
    exact ENNReal.div_le_div_right hcount _

/-- Singleton-strength consequence on the admissible points lifts to every
state of admissible points. -/
theorem multiset_strength_le_of_singletonStrengthLEOn
    (satisfies : Point → Query → Prop) (admissible : Point → Prop)
    (W : Multiset Point) (q₁ q₂ : Query)
    (hW : ∀ x ∈ W, admissible x)
    (hsing : singletonStrengthLEOn satisfies admissible q₁ q₂) :
    @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q₁ ≤
      @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q₂ :=
  queryStrength_le_of_pointwise_on satisfies admissible W q₁ q₂ hW
    ((pointwiseImpliesOn_iff_singletonStrengthLEOn satisfies admissible q₁ q₂).mpr hsing)

/-- Evidence-relative WM consequence rule from pointwise implication on the
admissible points: its side condition is that every point of the state is
admissible. -/
def wmConsequenceRuleOn_of_pointwise
    (satisfies : Point → Query → Prop) (admissible : Point → Prop)
    (q₁ q₂ : Query) (himp : pointwiseImpliesOn satisfies admissible q₁ q₂) :
    @WMConsequenceRuleOn (Multiset Point) Query _ (crispWorldModel satisfies) :=
  letI := crispWorldModel satisfies
  { side := fun W => ∀ x ∈ W, admissible x
    premise := q₁
    conclusion := q₂
    sound := fun hW => queryStrength_le_of_pointwise_on satisfies admissible _ q₁ q₂ hW himp }

/-! ## Consequence on all points -/

/-- Singleton-strength consequence on all points. -/
def singletonStrengthLE
    (satisfies : Point → Query → Prop) (q₁ q₂ : Query) : Prop :=
  singletonStrengthLEOn satisfies (fun _ => True) q₁ q₂

/-- Pointwise implication is singleton-strength consequence. -/
theorem pointwiseImplies_iff_singletonStrengthLE
    (satisfies : Point → Query → Prop) (q₁ q₂ : Query) :
    (∀ x : Point, satisfies x q₁ → satisfies x q₂) ↔
      singletonStrengthLE satisfies q₁ q₂ := by
  rw [singletonStrengthLE, ← pointwiseImpliesOn_iff_singletonStrengthLEOn]
  exact ⟨fun h x _ => h x, fun h x => h x trivial⟩

/-- Pointwise implication lifts to every state. -/
theorem queryStrength_le_of_pointwise
    (satisfies : Point → Query → Prop)
    (W : Multiset Point) (q₁ q₂ : Query)
    (himp : ∀ x : Point, satisfies x q₁ → satisfies x q₂) :
    @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q₁ ≤
      @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q₂ :=
  queryStrength_le_of_pointwise_on satisfies (fun _ => True) W q₁ q₂ (fun _ _ => trivial)
    (fun x _ => himp x)

/-- Singleton-strength consequence lifts to every state. -/
theorem multiset_strength_le_of_singletonStrengthLE
    (satisfies : Point → Query → Prop)
    (W : Multiset Point) (q₁ q₂ : Query)
    (hsing : singletonStrengthLE satisfies q₁ q₂) :
    @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q₁ ≤
      @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q₂ :=
  queryStrength_le_of_pointwise satisfies W q₁ q₂
    ((pointwiseImplies_iff_singletonStrengthLE satisfies q₁ q₂).mpr hsing)

/-- Global WM consequence rule whose side condition is pointwise implication. -/
def wmConsequenceRule_of_pointwise
    (satisfies : Point → Query → Prop) (q₁ q₂ : Query) :
    @WMConsequenceRule (Multiset Point) Query _ (crispWorldModel satisfies) :=
  letI := crispWorldModel satisfies
  { side := ∀ x : Point, satisfies x q₁ → satisfies x q₂
    premise := q₁
    conclusion := q₂
    sound := fun himp W => queryStrength_le_of_pointwise satisfies W q₁ q₂ himp }

/-- Global WM consequence rule whose side condition is singleton-strength
consequence. -/
def wmConsequenceRule_of_singletonStrengthLE
    (satisfies : Point → Query → Prop) (q₁ q₂ : Query) :
    @WMConsequenceRule (Multiset Point) Query _ (crispWorldModel satisfies) :=
  letI := crispWorldModel satisfies
  { side := singletonStrengthLE satisfies q₁ q₂
    premise := q₁
    conclusion := q₂
    sound := fun hsing W => multiset_strength_le_of_singletonStrengthLE satisfies W q₁ q₂ hsing }

/-! ## Proof systems over a crisp semantics -/

/-- A pointed counterexample refutes singleton-strength consequence. -/
theorem singletonStrengthLE_not_of_counterexample
    (satisfies : Point → Query → Prop) (q₁ q₂ : Query) (x : Point)
    (hq₁ : satisfies x q₁) (hnq₂ : ¬ satisfies x q₂) :
    ¬ singletonStrengthLE satisfies q₁ q₂ := fun hsing =>
  hnq₂ ((pointwiseImplies_iff_singletonStrengthLE satisfies q₁ q₂).2 hsing x hq₁)

/-- An implication relation sound and complete for pointwise implication is
singleton-strength consequence. -/
theorem externalImplication_iff_singletonStrengthLE_of_sound_complete
    (satisfies : Point → Query → Prop) (ProvImp : Query → Query → Prop)
    (hSound : ∀ {q₁ q₂}, ProvImp q₁ q₂ → ∀ x, satisfies x q₁ → satisfies x q₂)
    (hComplete : ∀ {q₁ q₂}, (∀ x, satisfies x q₁ → satisfies x q₂) → ProvImp q₁ q₂)
    (q₁ q₂ : Query) :
    ProvImp q₁ q₂ ↔ singletonStrengthLE satisfies q₁ q₂ := by
  rw [← pointwiseImplies_iff_singletonStrengthLE]
  exact ⟨hSound, hComplete⟩

/-- A sound implication relation transfers to strength inequalities on every
state. -/
theorem multiset_strength_le_of_externalImplication_sound
    (satisfies : Point → Query → Prop) (ProvImp : Query → Query → Prop)
    (hSound : ∀ {q₁ q₂}, ProvImp q₁ q₂ → ∀ x, satisfies x q₁ → satisfies x q₂)
    (W : Multiset Point) (q₁ q₂ : Query) (hprov : ProvImp q₁ q₂) :
    @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q₁ ≤
      @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q₂ :=
  queryStrength_le_of_pointwise satisfies W q₁ q₂ (hSound hprov)

/-- An implication relation that misses a singleton consequence is not
equivalent to it. -/
theorem externalImplication_not_equiv_of_incomplete_witness
    (satisfies : Point → Query → Prop) (ProvImp : Query → Query → Prop)
    {q₁ q₂ : Query} (hsing : singletonStrengthLE satisfies q₁ q₂) (hnot : ¬ ProvImp q₁ q₂) :
    ¬ ∀ r₁ r₂, ProvImp r₁ r₂ ↔ singletonStrengthLE satisfies r₁ r₂ := fun hall =>
  hnot ((hall q₁ q₂).2 hsing)

/-- An implication relation that proves a pair with a pointed counterexample
is not equivalent to singleton consequence. -/
theorem externalImplication_not_equiv_of_unsound_witness
    (satisfies : Point → Query → Prop) (ProvImp : Query → Query → Prop)
    {q₁ q₂ : Query} (hprov : ProvImp q₁ q₂)
    (hcounter : ∃ x, satisfies x q₁ ∧ ¬ satisfies x q₂) :
    ¬ ∀ r₁ r₂, ProvImp r₁ r₂ ↔ singletonStrengthLE satisfies r₁ r₂ := fun hall => by
  obtain ⟨x, hq₁, hnq₂⟩ := hcounter
  exact singletonStrengthLE_not_of_counterexample satisfies q₁ q₂ x hq₁ hnq₂ ((hall q₁ q₂).1 hprov)

/-! ## Query equivalence -/

/-- Pointwise equivalence yields WM query equivalence. -/
theorem queryEq_of_pointwiseIff
    (satisfies : Point → Query → Prop)
    (q₁ q₂ : Query)
    (hiff : ∀ x : Point, satisfies x q₁ ↔ satisfies x q₂) :
    @WMQueryEq (Multiset Point) Query _ (crispWorldModel satisfies) q₁ q₂ := by
  intro W
  classical
  rw [evidence_crispWorldModel, evidence_crispWorldModel]
  ext <;> simp [crispEvidence, hiff]

/-- WM query equivalence transports strength. -/
theorem queryEq_to_queryStrength
    (satisfies : Point → Query → Prop)
    {q₁ q₂ : Query}
    (hEq : @WMQueryEq (Multiset Point) Query _ (crispWorldModel satisfies) q₁ q₂)
    (W : Multiset Point) :
    @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q₁ =
      @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q₂ := by
  unfold BinaryWorldModel.queryStrength
  rw [hEq W]

/-- Pointwise equivalence yields equality of strengths on every state. -/
theorem queryStrength_eq_of_pointwiseIff
    (satisfies : Point → Query → Prop)
    (W : Multiset Point) (q₁ q₂ : Query)
    (hiff : ∀ x : Point, satisfies x q₁ ↔ satisfies x q₂) :
    @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q₁ =
      @BinaryWorldModel.queryStrength (Multiset Point) Query _ (crispWorldModel satisfies) W q₂ :=
  queryEq_to_queryStrength satisfies (queryEq_of_pointwiseIff satisfies q₁ q₂ hiff) W

/-- Pointwise equivalence is exactly WM query equivalence. -/
theorem pointwiseIff_iff_queryEq
    (satisfies : Point → Query → Prop)
    (q₁ q₂ : Query) :
    (∀ x : Point, satisfies x q₁ ↔ satisfies x q₂) ↔
      @WMQueryEq (Multiset Point) Query _ (crispWorldModel satisfies) q₁ q₂ := by
  refine ⟨queryEq_of_pointwiseIff satisfies q₁ q₂, fun hEq x => ?_⟩
  rw [singleton_adequacy_strength_one satisfies x q₁, singleton_adequacy_strength_one satisfies x q₂,
    queryEq_to_queryStrength satisfies hEq ({x} : Multiset Point)]

/-! ## Countably infinitary closure -/

/-- Countable conjunctions and disjunctions over base queries. -/
inductive InfQuery (Base : Type v) where
  | atom : Base → InfQuery Base
  | iAnd : (Nat → InfQuery Base) → InfQuery Base
  | iOr : (Nat → InfQuery Base) → InfQuery Base

/-- Satisfaction of infinitary queries, generated by a base crisp semantics. -/
inductive SatisfiesInf {Base : Type v} (satisfies : Point → Base → Prop) :
    Point → InfQuery Base → Prop where
  | atom {x : Point} {q : Base} : satisfies x q → SatisfiesInf satisfies x (.atom q)
  | iAnd {x : Point} {F : Nat → InfQuery Base} :
      (∀ n, SatisfiesInf satisfies x (F n)) → SatisfiesInf satisfies x (.iAnd F)
  | iOr {x : Point} {F : Nat → InfQuery Base} {n : Nat} :
      SatisfiesInf satisfies x (F n) → SatisfiesInf satisfies x (.iOr F)

section Infinitary

variable {Base : Type v} (satisfies : Point → Base → Prop)

theorem satisfiesInf_atom_iff (x : Point) (q : Base) :
    SatisfiesInf satisfies x (.atom q) ↔ satisfies x q :=
  ⟨fun h => by cases h with | atom h => exact h, SatisfiesInf.atom⟩

theorem satisfiesInf_iAnd_iff (x : Point) (F : Nat → InfQuery Base) :
    SatisfiesInf satisfies x (.iAnd F) ↔ ∀ n, SatisfiesInf satisfies x (F n) :=
  ⟨fun h => by cases h with | iAnd h => exact h, SatisfiesInf.iAnd⟩

theorem satisfiesInf_iOr_iff (x : Point) (F : Nat → InfQuery Base) :
    SatisfiesInf satisfies x (.iOr F) ↔ ∃ n, SatisfiesInf satisfies x (F n) :=
  ⟨fun h => by cases h with | iOr h => exact ⟨_, h⟩, fun ⟨_, h⟩ => SatisfiesInf.iOr h⟩

/-- Countable conjunction elimination, pointwise. -/
theorem pointwise_iAnd_to_component (F : Nat → InfQuery Base) (n : Nat) :
    ∀ x, SatisfiesInf satisfies x (.iAnd F) → SatisfiesInf satisfies x (F n) :=
  fun x h => (satisfiesInf_iAnd_iff satisfies x F).1 h n

/-- Countable disjunction introduction, pointwise. -/
theorem pointwise_component_to_iOr (F : Nat → InfQuery Base) (n : Nat) :
    ∀ x, SatisfiesInf satisfies x (F n) → SatisfiesInf satisfies x (.iOr F) :=
  fun _ h => SatisfiesInf.iOr h

/-- Countable conjunction elimination on every state. -/
theorem queryStrength_le_iAnd_component (W : Multiset Point) (F : Nat → InfQuery Base) (n : Nat) :
    @BinaryWorldModel.queryStrength (Multiset Point) (InfQuery Base) _
        (crispWorldModel (SatisfiesInf satisfies)) W (.iAnd F) ≤
      @BinaryWorldModel.queryStrength (Multiset Point) (InfQuery Base) _
        (crispWorldModel (SatisfiesInf satisfies)) W (F n) :=
  queryStrength_le_of_pointwise _ W _ _ (pointwise_iAnd_to_component satisfies F n)

/-- Countable disjunction introduction on every state. -/
theorem queryStrength_le_iOr_of_component (W : Multiset Point) (F : Nat → InfQuery Base) (n : Nat) :
    @BinaryWorldModel.queryStrength (Multiset Point) (InfQuery Base) _
        (crispWorldModel (SatisfiesInf satisfies)) W (F n) ≤
      @BinaryWorldModel.queryStrength (Multiset Point) (InfQuery Base) _
        (crispWorldModel (SatisfiesInf satisfies)) W (.iOr F) :=
  queryStrength_le_of_pointwise _ W _ _ (pointwise_component_to_iOr satisfies F n)

end Infinitary

end Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
