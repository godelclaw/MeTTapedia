import Mettapedia.Logic.HOL.SevenVirtues.Expressiveness
import Mettapedia.Logic.HOL.HOLLightBooleanDefinitions

/-!
# Three forms of Dedekind infinity agree

The tree states Dedekind infinity of a base type three times:

* `SevenVirtues.dedekindInfinite b`, a sentence with primitive connectives:
  `∃ f. (∀ x y. f x = f y → x = y) ∧ ¬ ∀ y. ∃ x. f x = y`;
* `HOLLightBooleanDefinitions.infinityFormula b`, HOL Light's
  `?f. ONE_ONE f /\ ~(ONTO f)` with its defined connectives;
* `HenkinModel.HasDedekindInfiniteBase M b`, a semantic witness: an admissible
  injection and a point outside its image.

This file proves that they agree: the first and third in every Henkin model
(`models_dedekindInfinite_iff_hasDedekindInfiniteBase`), and all three in
every full-domain model (`models_infinityFormula_iff_models_dedekindInfinite`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.SevenVirtues.DedekindInfinityForms

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

variable (M : HenkinModel.{u, v, w} Base Const) (b : Base)

/-- The primitive sentence is the semantic witness, in every Henkin model. -/
theorem models_dedekindInfinite_iff_hasDedekindInfiniteBase :
    M.models (dedekindInfinite b) ↔ M.HasDedekindInfiniteBase b := by
  classical
  rw [models_dedekindInfinite_iff_general]
  constructor
  · rintro ⟨f, hf, hinj, hsurj⟩
    obtain ⟨y, hy⟩ : ∃ y, ∀ x, f x ≠ y := by
      by_contra h
      push Not at h
      exact hsurj h
    exact ⟨⟨f, hf, hinj, y, hy⟩⟩
  · rintro ⟨witness⟩
    exact ⟨witness.successor, witness.successor_admissible, witness.successor_injective,
      fun hsurj => by
        obtain ⟨x, hx⟩ := hsurj witness.omitted
        exact witness.omitted_not_image x hx⟩

open HOLLightBooleanDefinitions in
/-- In a full-domain model, HOL Light's infinity sentence is the semantic
witness. -/
theorem models_infinityFormula_iff_hasDedekindInfiniteBase (full : M.FullDomains) :
    M.models (infinityFormula b) ↔ M.HasDedekindInfiniteBase b := by
  classical
  constructor
  · intro h
    simp only [infinityFormula, HenkinModel.models, PreModel.models,
      denote_ex M full, denote_conj M full, denote_applyClosed,
      M.denote_weakenCtx,
      denote_oneOne M full, denote_onto M full,
      HenkinModel.denote, PreModel.denote, PreModel.extend, PreModel.Eqv] at h
    obtain ⟨f, hf, hinj, hnot⟩ := h
    have negated := denote_negation M full (fun index => nomatch index)
      (ULift.up (∀ value : M.Carrier b, M.adm (.base b) value →
        ∃ preimage : M.Carrier b, M.adm (.base b) preimage ∧ value = f preimage))
    have hnotOnto : ¬ (∀ value : M.Carrier b, M.adm (.base b) value →
        ∃ preimage : M.Carrier b, M.adm (.base b) preimage ∧ value = f preimage) :=
      Eq.mp (congrArg ULift.down negated) hnot
    obtain ⟨y, hy⟩ : ∃ y, ∀ x, f x ≠ y := by
      by_contra hall
      push Not at hall
      exact hnotOnto fun value _ =>
        let ⟨x, hx⟩ := hall value
        ⟨x, M.base_mem b x, hx.symm⟩
    exact ⟨⟨f, hf, fun x x' hxx' => hinj x (M.base_mem b x) x' (M.base_mem b x') hxx', y, hy⟩⟩
  · rintro ⟨witness⟩
    exact models_infinityFormula M full b witness

open HOLLightBooleanDefinitions in
/-- **The three forms agree in full-domain models.** -/
theorem models_infinityFormula_iff_models_dedekindInfinite (full : M.FullDomains) :
    M.models (infinityFormula b) ↔ M.models (dedekindInfinite b) := by
  rw [models_infinityFormula_iff_hasDedekindInfiniteBase M b full,
    models_dedekindInfinite_iff_hasDedekindInfiniteBase]

/-! ## Controls -/

/-- Positive control: the standard model on the natural numbers has a witness. -/
theorem natural_hasDedekindInfiniteBase :
    (Examples.standardOn ℕ).HasDedekindInfiniteBase () :=
  (models_dedekindInfinite_iff_hasDedekindInfiniteBase _ _).mp Examples.natural_infinite

/-- Negative control: the standard model on the Booleans has none. -/
theorem bool_not_hasDedekindInfiniteBase :
    ¬ (Examples.standardOn Bool).HasDedekindInfiniteBase () :=
  fun h => Examples.bool_not_infinite
    ((models_dedekindInfinite_iff_hasDedekindInfiniteBase _ _).mpr h)

end Mettapedia.Logic.HOL.SevenVirtues.DedekindInfinityForms
