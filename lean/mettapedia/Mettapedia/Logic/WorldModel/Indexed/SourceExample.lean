import Mathlib.Data.Multiset.Filter
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Category.Preord
import Mettapedia.Logic.WorldModel.Indexed.Survival

/-!
# An open-ended base: worlds of sources

Worlds are finite sets of sources, ordered by inclusion.  A state is a finitely
supported multiset of signed records `(source, sign)`.  At a world `W` the
questions are the aggregate positive and negative counts and, for every source
in `W`, its positive and negative counts.  Evidence is counts; an inclusion
widens the questions and reads counts back unchanged.

* The states `{a+, b−}` and `{a−, b+}` have equal profiles at the world without
  sources and different profiles at `{a}` (`swapped_profiles`).
* No function of the aggregate profile answers "evidence from `a`"
  (`evidenceFrom_not_factorsThrough_aggregate`).
* A world's profile is a sufficient record for all its extensions exactly when
  fewer than two sources lie outside it (`sufficientForExtensions_iff`).  So a
  world with exactly one source outside it is already sufficient
  (`one_outside_sufficient`): the outside source's counts are the aggregate
  minus the counts inside.  Some world is sufficient exactly when there are
  finitely many sources (`exists_sufficient_iff_finite`); over infinitely many
  sources the base has no final representation.
* Retained, the record answers every world's questions compatibly with every
  inclusion (`recordHom`, `answer_restrict`): a positive control.
-/

set_option autoImplicit false

open CategoryTheory Opposite

namespace Mettapedia.Logic.WorldModel.Indexed.Sources

variable {Src : Type} [DecidableEq Src]

/-- Signed records: a source and a sign, `true` for positive. -/
abbrev Records (Src : Type) := Multiset (Src × Bool)

/-- The questions of a world of sources. -/
inductive Question (W : Finset Src) : Type
  | aggregate (sign : Bool)
  | perSource (source : Src) (mem : source ∈ W) (sign : Bool)

/-- Widen a question along an inclusion of worlds. -/
def Question.widen {W W' : Finset Src} (h : W ⊆ W') : Question W → Question W'
  | .aggregate sign => .aggregate sign
  | .perSource source mem sign => .perSource source (h mem) sign

/-- The query functor of the source worlds. -/
def questions : Finset Src ⥤ Type where
  obj := Question
  map f := ↾(Question.widen (leOfHom f))
  map_id W := by
    ext q
    cases q <;> rfl
  map_comp f g := by
    ext q
    cases q <;> rfl

/-- Counts as evidence at every world. -/
def counts : (Finset Src)ᵒᵖ ⥤ AddCommMonCat := (Functor.const _).obj (AddCommMonCat.of ℕ)

/-- The profile functor of the source worlds. -/
abbrev sourceProfiles : (Finset Src)ᵒᵖ ⥤ AddCommMonCat :=
  profileFunctor (questions (Src := Src)) counts

/-- The answer of a record multiset to a question of a world. -/
def answerFun (W : Finset Src) (m : Records Src) : Question W → ℕ
  | .aggregate sign => (m.filter (fun r => r.2 = sign)).card
  | .perSource source _ sign => m.count (source, sign)

/-- Answers are additive in the records. -/
def answer (W : Finset Src) : Records Src →+ (Question W → ℕ) where
  toFun := answerFun W
  map_zero' := by
    funext q
    cases q <;> simp [answerFun]
  map_add' m m' := by
    funext q
    cases q <;> simp [answerFun, Multiset.filter_add]

/-- The record world model at a world. -/
def recordModel (W : Finset Src) : Over ((sourceProfiles (Src := Src)).obj (op W)) :=
  Over.mk (AddCommMonCat.ofHom (answer W) :
    AddCommMonCat.of (Records Src) ⟶ (sourceProfiles (Src := Src)).obj (op W))

/-- **Positive control.** Answers restrict compatibly along every inclusion. -/
theorem answer_restrict {W W' : Finset Src} (h : W ⟶ W') (m : Records Src) :
    restrictProfile (questions (Src := Src)) counts h (answer W' m) = answer W m := by
  funext q
  cases q <;> rfl

/-- **Positive control.** The retained record is a morphism over every
inclusion of worlds. -/
def recordHom {W W' : Finset Src} (h : W ⟶ W') :
    Total.mk sourceProfiles W (recordModel W) ⟶ Total.mk sourceProfiles W' (recordModel W') :=
  homOver sourceProfiles h (X := recordModel W) (Y := recordModel W') (𝟙 _)
    ((overArrow_iff questions counts h (recordModel W) (recordModel W') (𝟙 _)).2
      (fun (m : Records Src) q => congrFun (answer_restrict h m) q))

/-! ## Two states that only a finer world separates -/

/-- `{a+, b−}`. -/
def stateAB (a b : Src) : Records Src := {(a, true), (b, false)}

/-- `{a−, b+}`. -/
def stateBA (a b : Src) : Records Src := {(a, false), (b, true)}

omit [DecidableEq Src] in
theorem aggregate_stateAB (a b : Src) (sign : Bool) :
    ((stateAB a b).filter (fun r => r.2 = sign)).card = 1 := by
  cases sign <;> simp [stateAB, Multiset.filter_singleton]

omit [DecidableEq Src] in
theorem aggregate_stateBA (a b : Src) (sign : Bool) :
    ((stateBA a b).filter (fun r => r.2 = sign)).card = 1 := by
  cases sign <;> simp [stateBA, Multiset.filter_singleton]

/-- Two states with records only from sources outside `W` and equal aggregate
counts have equal profiles at `W`. -/
theorem answer_swap_eq_of_outside {W : Finset Src} {a b : Src} (ha : a ∉ W) (hb : b ∉ W) :
    answer W (stateAB a b) = answer W (stateBA a b) := by
  funext q
  cases q with
  | aggregate sign =>
      show ((stateAB a b).filter _).card = ((stateBA a b).filter _).card
      rw [aggregate_stateAB, aggregate_stateBA]
  | perSource source mem sign =>
      show (stateAB a b).count (source, sign) = (stateBA a b).count (source, sign)
      have hsa : source ≠ a := fun e => ha (e ▸ mem)
      have hsb : source ≠ b := fun e => hb (e ▸ mem)
      simp [stateAB, stateBA, hsa, hsb]

/-- The positive count of `a` in `{a+, b−}` is one and in `{a−, b+}` zero. -/
theorem count_a_true (a b : Src) (hab : a ≠ b) :
    (stateAB a b).count (a, true) = 1 ∧ (stateBA a b).count (a, true) = 0 := by
  constructor
  · simp [stateAB]
  · simp [stateBA, hab]

/-- The world without sources and the world `{a}` disagree on the two states. -/
theorem swapped_profiles (a b : Src) (hab : a ≠ b) :
    answer ∅ (stateAB a b) = answer ∅ (stateBA a b) ∧
      answer {a} (stateAB a b) ≠ answer {a} (stateBA a b) := by
  refine ⟨answer_swap_eq_of_outside (by simp) (by simp), fun same => ?_⟩
  have := congrFun same (.perSource a (by simp) true)
  change (stateAB a b).count (a, true) = (stateBA a b).count (a, true) at this
  rw [(count_a_true a b hab).1, (count_a_true a b hab).2] at this
  exact absurd this (by decide)

/-- The evidence from one source: its positive and negative counts. -/
def evidenceFrom (a : Src) (m : Records Src) : ℕ × ℕ := (m.count (a, true), m.count (a, false))

/-- **No function of the aggregate profile answers "evidence from `a`".** -/
theorem evidenceFrom_not_factorsThrough_aggregate (a b : Src) (hab : a ≠ b) :
    ¬ (evidenceFrom a).FactorsThrough (answer (∅ : Finset Src)) := by
  intro factors
  have := congrArg Prod.fst (factors (swapped_profiles a b hab).1)
  simp only [evidenceFrom] at this
  rw [(count_a_true a b hab).1, (count_a_true a b hab).2] at this
  exact absurd this (by decide)

/-! ## Sufficiency for extensions -/

/-- A world's profile is a sufficient record for all its extensions when every
extension's profile factors through it. -/
def SufficientForExtensions (W : Finset Src) : Prop :=
  ∀ W' : Finset Src, W ⊆ W' → (answer W' : Records Src → Question W' → ℕ).FactorsThrough (answer W)

/-- Two sources outside `W` separate two states that `W` identifies, at the
extension by one of them. -/
theorem not_sufficient_of_two_outside {W : Finset Src} {a b : Src} (hab : a ≠ b)
    (ha : a ∉ W) (hb : b ∉ W) : ¬ SufficientForExtensions W := by
  intro sufficient
  have same := sufficient (insert a W) (Finset.subset_insert a W)
    (answer_swap_eq_of_outside ha hb)
  have := congrFun same (.perSource a (Finset.mem_insert_self a W) true)
  change (stateAB a b).count (a, true) = (stateBA a b).count (a, true) at this
  rw [(count_a_true a b hab).1, (count_a_true a b hab).2] at this
  exact absurd this (by decide)

/-- Records inside a world are determined by that world's per-source answers. -/
theorem filter_inside_eq {W : Finset Src} {m m' : Records Src}
    (same : answer W m = answer W m') :
    m.filter (fun r => r.1 ∈ W) = m'.filter (fun r => r.1 ∈ W) := by
  ext r
  rw [Multiset.count_filter, Multiset.count_filter]
  split_ifs with h
  · exact congrFun same (.perSource r.1 h r.2)
  · rfl

/-- If at most one source lies outside `W`, the profile at `W` determines the
records. -/
theorem answer_injective_of_at_most_one_outside {W : Finset Src}
    (atMostOne : ¬ ∃ a b, a ≠ b ∧ a ∉ W ∧ b ∉ W) :
    Function.Injective (answer W : Records Src → Question W → ℕ) := by
  intro m m' same
  have inside := filter_inside_eq same
  ext ⟨s, sign⟩
  by_cases hs : s ∈ W
  · exact congrFun same (.perSource s hs sign)
  · -- every source outside `W` is `s`
    have outside : ∀ t, t ∉ W → t = s := by
      intro t ht
      by_contra hne
      exact atMostOne ⟨t, s, hne, ht, hs⟩
    have split : ∀ n : Records Src,
        (n.filter (fun r => r.2 = sign)).card =
          ((n.filter (fun r => r.1 ∈ W)).filter (fun r => r.2 = sign)).card +
            n.count (s, sign) := by
      intro n
      have decompose := Multiset.filter_add_not (fun r : Src × Bool => r.1 ∈ W) n
      conv_lhs => rw [← decompose]
      rw [Multiset.filter_add, Multiset.card_add]
      congr 1
      rw [Multiset.count_eq_card_filter_eq, Multiset.filter_filter]
      congr 1
      apply Multiset.filter_congr
      intro r _
      constructor
      · rintro ⟨hsign, hr⟩
        have := outside r.1 hr
        rcases r with ⟨t, sg⟩
        simp only at this hsign
        rw [this, hsign]
      · rintro rfl
        exact ⟨rfl, hs⟩
    have aggregate := congrFun same (.aggregate sign)
    change (m.filter (fun r => r.2 = sign)).card = (m'.filter (fun r => r.2 = sign)).card
      at aggregate
    rw [split m, split m', inside] at aggregate
    exact Nat.add_left_cancel aggregate

/-- **Sufficiency boundary.** A world's profile is a sufficient record for all
its extensions exactly when fewer than two sources lie outside it. -/
theorem sufficientForExtensions_iff (W : Finset Src) :
    SufficientForExtensions W ↔ ¬ ∃ a b, a ≠ b ∧ a ∉ W ∧ b ∉ W := by
  constructor
  · rintro sufficient ⟨a, b, hab, ha, hb⟩
    exact not_sufficient_of_two_outside hab ha hb sufficient
  · intro atMostOne W' _ m m' same
    rw [answer_injective_of_at_most_one_outside atMostOne same]

/-- The literal "one source outside suffices to separate" fails: with two
sources, the world containing one of them is already sufficient. -/
theorem one_outside_sufficient : SufficientForExtensions ({true} : Finset Bool) := by
  refine (sufficientForExtensions_iff _).2 ?_
  rintro ⟨a, b, hab, ha, hb⟩
  cases a <;> cases b <;> simp_all

/-- **No final representation over infinitely many sources.** Some world's
profile is sufficient for all its extensions exactly when there are finitely
many sources. -/
theorem exists_sufficient_iff_finite :
    (∃ W : Finset Src, SufficientForExtensions W) ↔ Finite Src := by
  constructor
  · rintro ⟨W, sufficient⟩
    by_contra notFinite
    have : Infinite Src := not_finite_iff_infinite.mp notFinite
    obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset W
    obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset (insert a W)
    have hab : a ≠ b := fun e => hb (e ▸ Finset.mem_insert_self a W)
    exact not_sufficient_of_two_outside hab ha (fun h => hb (Finset.mem_insert_of_mem h))
      sufficient
  · intro finite
    have : Fintype Src := Fintype.ofFinite Src
    refine ⟨Finset.univ, (sufficientForExtensions_iff _).2 ?_⟩
    rintro ⟨a, b, _, ha, _⟩
    exact ha (Finset.mem_univ a)

end Mettapedia.Logic.WorldModel.Indexed.Sources
