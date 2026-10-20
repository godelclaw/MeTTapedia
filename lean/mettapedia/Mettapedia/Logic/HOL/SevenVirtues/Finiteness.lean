import Mettapedia.Logic.HOL.SevenVirtues.Choice

/-!
# Dedekind and Kuratowski finiteness

Two sentences say that a base type `b` is finite.

* Dedekind: `finite b`, every injection of `b` into itself is onto
  (`Expressiveness`).
* Kuratowski: `kuratowskiFinite b`, every family of predicates that contains
  the empty predicate and is closed under adding one element contains the
  full predicate.

In a full-domain model both mean that the carrier of `b` is finite
(`models_kuratowskiFinite_iff_finite`, and `models_finite_iff`), so they agree
in standard semantics.  In the Fraenkel–Mostowski permutation model of
`Choice` they come apart: the atoms are Dedekind-finite
(`permutationModel_not_dedekindInfinite`) but not Kuratowski-finite
(`permutationModel_not_kuratowskiFinite`), because the predicate "is a finite
set of atoms" on predicates is admissible there.  Hence Dedekind finiteness
does not derive Kuratowski finiteness, even with excluded middle
(`dedekind_imp_kuratowski_not_provable`).  This is the type-theoretic form of
the fact that in set theory without choice an infinite Dedekind-finite set can
exist.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.SevenVirtues

open ClosedTheorySet

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

section HOL

variable (b : Base)

/-- Kuratowski finiteness of the base type `b`:
`∀ X : (b ⇒ prop) ⇒ prop. X (λx. ⊥) ∧ (∀ A a. X A → X (λx. A x ∨ x = a)) → X (λx. ⊤)`. -/
def kuratowskiFinite : ClosedFormula Const :=
  .all (σ := (.base b ⇒ .prop) ⇒ .prop) (.imp
    (.and (.app (.var .vz) (.lam (σ := .base b) .bot))
      (.all (σ := .base b ⇒ .prop) (.all (σ := .base b) (.imp
        (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
        (.app (.var (.vs (.vs .vz))) (.lam (σ := .base b)
          (.or (.app (.var (.vs (.vs .vz))) (.var .vz)) (.eq (.var .vz) (.var (.vs .vz))))))))))
    (.app (.var .vz) (.lam (σ := .base b) .top)))

variable (M : HenkinModel.{u, v, w} Base Const)

/-- In a Henkin model, the sentence quantifies over admissible families of
admissible predicates. -/
theorem models_kuratowskiFinite_iff :
    M.models (kuratowskiFinite b) ↔
      ∀ X : (M.Carrier b → ULift.{max (u + 1) w} Prop) → ULift.{max (u + 1) w} Prop,
        M.adm ((.base b ⇒ .prop) ⇒ .prop) X →
          (X (fun _ => ULift.up False)).down ∧
            (∀ A : M.Carrier b → ULift.{max (u + 1) w} Prop, M.adm (.base b ⇒ .prop) A →
              ∀ a : M.Carrier b, M.adm (.base b) a →
                (X A).down → (X fun x => ULift.up ((A x).down ∨ x = a)).down) →
            (X fun _ => ULift.up True).down :=
  Iff.rfl

/-- **Kuratowski finiteness in a full-domain model is finiteness.** -/
theorem models_kuratowskiFinite_iff_finite (full : M.FullDomains) :
    M.models (kuratowskiFinite b) ↔ Finite (M.Carrier b) := by
  classical
  rw [models_kuratowskiFinite_iff]
  constructor
  · intro h
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    let X : (M.Carrier b → ULift.{max (u + 1) w} Prop) → ULift.{max (u + 1) w} Prop :=
      fun A => ULift.up (Set.Finite {x | (A x).down})
    have hall := h X (full ((.base b ⇒ .prop) ⇒ .prop) X) ⟨by simp [X], fun A _ a _ hA => by
      have : {x | (A x).down ∨ x = a} = {x | (A x).down} ∪ {a} := by
        ext x
        simp [or_comm]
      show Set.Finite {x | (A x).down ∨ x = a}
      rw [this]
      exact hA.union (Set.finite_singleton a)⟩
    exact Set.infinite_univ (by simpa [X] using hall)
  · intro hfin X _ ⟨h0, hstep⟩
    have hFintype : Fintype (M.Carrier b) := Fintype.ofFinite _
    have key : ∀ s : Finset (M.Carrier b), (X fun x => ULift.up (x ∈ s)).down := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          have hempty : (fun x : M.Carrier b => ULift.up.{max (u + 1) w} (x ∈ (∅ : Finset (M.Carrier b)))) =
              fun _ => ULift.up False := by
            funext x
            simp
          rw [hempty]
          exact h0
      | insert a s _ ih =>
          have hins : (fun x : M.Carrier b => ULift.up.{max (u + 1) w} (x ∈ insert a s)) =
              fun x => ULift.up ((ULift.up.{max (u + 1) w} (x ∈ s)).down ∨ x = a) := by
            funext x
            simp [or_comm]
          rw [hins]
          exact hstep _ (full _ _) a (full _ _) ih
    have huniv : (fun x : M.Carrier b => ULift.up.{max (u + 1) w} (x ∈ (Finset.univ : Finset (M.Carrier b)))) =
        fun _ => ULift.up True := by
      funext x
      simp
    have := key Finset.univ
    rwa [huniv] at this

/-- In a full-domain model the two finiteness sentences agree. -/
theorem models_kuratowskiFinite_iff_models_finite (full : M.FullDomains) :
    M.models (kuratowskiFinite b) ↔ M.models (finite b) := by
  rw [models_kuratowskiFinite_iff_finite b M full, models_finite_iff b M full]

end HOL

/-! ## The permutation model -/

namespace Choice

/-- The predicate "is a finite set of atoms" on predicates. -/
def finitePred : D ((ι ⇒ .prop) ⇒ .prop) :=
  fun A => ULift.up (Set.Finite {x | (A x).down})

theorem finitePred_supported : Supported ((ι ⇒ .prop) ⇒ .prop) finitePred := by
  refine ⟨∅, fun π _ => ?_⟩
  funext A
  show finitePred (fun x => A (π⁻¹⁻¹ x)) = finitePred A
  rw [inv_inv]
  simp only [finitePred]
  congr 1
  apply propext
  show Set.Finite (π ⁻¹' {y : Atom | (A y).down}) ↔ Set.Finite {y : Atom | (A y).down}
  constructor
  · intro h
    have himage := h.image π
    rwa [Set.image_preimage_eq _ π.surjective] at himage
  · intro h
    exact h.preimage π.injective.injOn

theorem finitePred_adm : Adm ((ι ⇒ .prop) ⇒ .prop) finitePred := by
  refine (adm_arr finitePred).mpr ⟨fun _ _ => trivial, fun A B _ _ hAB => ?_, finitePred_supported⟩
  have hset : {x | (A x).down} = {x | (B x).down} := by
    ext x
    exact hAB x trivial
  show Set.Finite {x | (A x).down} ↔ Set.Finite {x | (B x).down}
  rw [hset]

/-- **The atoms are not Kuratowski-finite in the permutation model.** -/
theorem permutationModel_not_kuratowskiFinite :
    ¬ permutationModel.models (kuratowskiFinite ()) := by
  classical
  rw [models_kuratowskiFinite_iff.{0, 0, 0} () permutationModel]
  intro h
  have hall := h finitePred finitePred_adm ⟨by simp [finitePred], fun A _ a _ hA => by
    have : {x | (A x).down ∨ x = a} = {x | (A x).down} ∪ {a} := by
      ext x
      simp [or_comm]
    show Set.Finite {x | (A x).down ∨ x = a}
    rw [this]
    exact hA.union (Set.finite_singleton a)⟩
  have : Infinite (D ι) := inferInstanceAs (Infinite Atom)
  exact Set.infinite_univ (by simpa [finitePred] using hall)

/-- **Dedekind-finite but not Kuratowski-finite**: in the permutation model the
atoms satisfy `finite ι` and refute `kuratowskiFinite ι`. -/
theorem permutationModel_dedekind_not_kuratowski :
    permutationModel.models (finite ()) ∧ ¬ permutationModel.models (kuratowskiFinite ()) :=
  ⟨permutationModel_not_dedekindInfinite, permutationModel_not_kuratowskiFinite⟩

/-- **Dedekind finiteness does not derive Kuratowski finiteness**, even with
excluded middle. -/
theorem dedekind_imp_kuratowski_not_provable :
    ¬ Provable (Const := Pure) (insert excludedMiddle ∅)
      (.imp (finite ()) (kuratowskiFinite ())) := by
  intro h
  have hmodel := soundness.{0, 0, 0} h permutationModel permutationModel_extensional
    (fun _ hψ => absurd hψ (Set.notMem_empty _))
  exact permutationModel_not_kuratowskiFinite
    ((HenkinModel.models_imp _).mp hmodel permutationModel_not_dedekindInfinite)

end Choice

/-! ## Positive and negative instances in standard models -/

namespace Examples

theorem bool_kuratowskiFinite : (standardOn Bool).models (kuratowskiFinite ()) :=
  (models_kuratowskiFinite_iff_finite () (standardOn Bool)
    (HenkinModel.fullDomains_standard _ _)).mpr (inferInstanceAs (Finite (ULift.{1} Bool)))

theorem nat_not_kuratowskiFinite : ¬ (standardOn ℕ).models (kuratowskiFinite ()) := by
  rw [models_kuratowskiFinite_iff_finite () (standardOn ℕ) (HenkinModel.fullDomains_standard _ _)]
  exact not_finite_iff_infinite.mpr (inferInstanceAs (Infinite (ULift.{1} ℕ)))

end Examples

end Mettapedia.Logic.HOL.SevenVirtues
