import Mettapedia.Logic.HOL.SevenVirtues.Completeness

/-!
# Controls for the classical Henkin corollaries

Positive and negative instances for
`ClosedTheorySet.henkin_model_exists_of_consistent_classical` and its extensional form
`henkin_extensional_model_exists_of_consistent_classical`, over the parameter signature
`WithParams Const`.

Positive:
* `excludedMiddleTheory`, the theory whose only axiom is `∀ p : prop, p ∨ ¬ p`, over the
  propositional signature `PropositionalSlice.Atom`, meets every hypothesis of the
  corollaries (`excludedMiddleTheory_has_model`, `excludedMiddleTheory_has_extensional_model`);
* more generally, the parameter image of any theory over a countable signature with a
  closed term at each base type, consistent together with excluded middle, meets every
  hypothesis (`paramImage_has_extensional_model`).

Positive, original signature: `SevenVirtues.soundness`, `exists_model_of_consistent`,
`completeness` and `provable_iff_valid` applied to the theory `{p₀}` over `Atom`, which has
no base type (`atomTheory_soundness`, `atomTheory_has_model`,
`atomTheory_proves_excludedMiddle`, `atomTheory_provable_iff_valid`).

Negative:
* containing the excluded-middle schema, instead of proving it, is incompatible with
  parameter-freeness (`SevenVirtues.classical_corollary_hypotheses_unsatisfiable`);
* `excludedMiddleTheory` proves neither `p₀` nor `¬ p₀`: the standard models with `p₀`
  false and with `p₀` true both satisfy it (`excludedMiddleTheory_not_provable_atom`,
  `excludedMiddleTheory_not_provable_not_atom`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

deriving instance Countable for PropositionalSlice.Atom

namespace HenkinCompletenessControls

open ClosedTheorySet WithParams SevenVirtues PropositionalSlice

universe u v

/-! ## A concrete classical theory over the parameter signature -/

/-- A surjective enumeration of the one-variable bodies over `Atom`. -/
noncomputable def atomEnum : Nat → Body Atom :=
  Classical.choose (exists_body_enumeration (Const := Atom))

theorem atomEnum_surjective : ∀ b : Body Atom, ∃ n, atomEnum n = b :=
  Classical.choose_spec (exists_body_enumeration (Const := Atom))

/-- The theory whose only axiom is excluded middle, over the parameter signature. -/
def excludedMiddleTheory : ClosedTheorySet (WithParams Atom) := {excludedMiddle}

theorem excludedMiddle_paramFree {Const : Ty AtomBase → Type} (σ : Ty AtomBase) (k : Nat) :
    NoConstOccurrence (param σ k)
      (excludedMiddle : ClosedFormula (WithParams Const)) :=
  .all (.or .var (.not .var))

theorem excludedMiddleTheory_paramFree :
    ∀ ψ ∈ excludedMiddleTheory, ∀ (σ : Ty AtomBase) (k : Nat),
      NoConstOccurrence (param σ k) ψ := by
  intro ψ hψ σ k
  rw [excludedMiddleTheory, Set.mem_singleton_iff] at hψ
  subst hψ
  exact excludedMiddle_paramFree σ k

theorem excludedMiddleTheory_proves_emSchema :
    ∀ ψ ∈ EMSchema Atom, Provable (Const := WithParams Atom) excludedMiddleTheory ψ :=
  provable_emSchema_of_mem (Set.mem_singleton _)

/-- Soundness for `excludedMiddleTheory` in any extensional Henkin model. -/
theorem models_of_excludedMiddleTheory_provable {φ : ClosedFormula (WithParams Atom)}
    (h : Provable (Const := WithParams Atom) excludedMiddleTheory φ)
    (M : HenkinModel.{0, 0, 0} AtomBase (WithParams Atom)) (hExt : M.FunctionsRespectEqv) :
    M.models φ :=
  soundness (T := excludedMiddleTheory)
    (provable_mono (Const := WithParams Atom) (fun hψ => Set.mem_insert_of_mem _ hψ) h)
    M hExt (by
      intro ψ hψ
      rw [excludedMiddleTheory, Set.mem_singleton_iff] at hψ
      subst hψ
      exact models_excludedMiddle M)

theorem excludedMiddleTheory_consistent :
    Consistent (Const := WithParams Atom) excludedMiddleTheory := fun hBot =>
  HenkinModel.models_bot _
    (models_of_excludedMiddleTheory_provable hBot (standardModel fun _ => True)
      (standardModel_extensional _))

/-- **Positive control.** The corollary applies to `excludedMiddleTheory`. -/
theorem excludedMiddleTheory_has_model :
    ∃ N : HenkinModel.{0, 0, 0} AtomBase (WithParams Atom),
      ∀ ψ ∈ excludedMiddleTheory, N.models ψ :=
  henkin_model_exists_of_consistent_classical atomEnum atomEnum_surjective
    excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema

/-- **Positive control.** The extensional corollary applies to `excludedMiddleTheory`. -/
theorem excludedMiddleTheory_has_extensional_model :
    ∃ N : HenkinModel.{0, 0, 0} AtomBase (WithParams Atom),
      (∀ ψ ∈ excludedMiddleTheory, N.models ψ) ∧ N.FunctionsRespectEqv :=
  henkin_extensional_model_exists_of_consistent_classical atomEnum atomEnum_surjective
    excludedMiddleTheory_consistent excludedMiddleTheory_paramFree
    excludedMiddleTheory_proves_emSchema

/-! ## The parameter image of an original-signature theory -/

section ParamImage

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The parameter image of a theory that contains excluded middle proves the whole
excluded-middle schema. -/
theorem paramImage_proves_emSchema (T : ClosedTheorySet Const) :
    ∀ ψ ∈ EMSchema Const,
      Provable (Const := WithParams Const) (paramImage (insert excludedMiddle T)) ψ :=
  provable_emSchema_of_mem ⟨excludedMiddle, Set.mem_insert _ _, rfl⟩

/-- **Positive control, general form.** Over a countable signature with a closed term at
each base type, the parameter image of a theory that is consistent together with excluded
middle meets every hypothesis of the extensional corollary. -/
theorem paramImage_has_extensional_model [Countable Base] [∀ τ, Countable (Const τ)]
    (inh : ∀ b : Base, ClosedTerm Const (.base b)) {T : ClosedTheorySet Const}
    (hCons : Consistent (Const := Const) (insert excludedMiddle T)) :
    ∃ N : HenkinModel.{u, v, v} Base (WithParams Const),
      (∀ ψ ∈ paramImage (insert excludedMiddle T), N.models ψ) ∧ N.FunctionsRespectEqv :=
  henkin_extensional_model_exists_of_consistent_classical
    (Classical.choose (exists_body_enumeration (Const := Const)))
    (Classical.choose_spec (exists_body_enumeration (Const := Const)))
    (consistent_image_of_consistent inh hCons) (paramImage_paramFree _)
    (paramImage_proves_emSchema T)

end ParamImage

/-! ## Negative controls -/

/-- The atom `p₀` over the parameter signature. -/
abbrev atom0 : ClosedFormula (WithParams Atom) := embedP (.atom 0)

theorem atom0_paramFree (σ : Ty AtomBase) (k : Nat) :
    NoConstOccurrence (param σ k) atom0 := by
  by_cases h : σ = propTy
  · subst h
    exact .const_same_ne _ (inj_ne_param _ k)
  · exact .const_diff_type h _

theorem standardModel_models_atom0 (v : ℕ → Prop) :
    (standardModel v).models atom0 ↔ v 0 :=
  standardModel_denote v _ (.atom 0)

/-- `excludedMiddleTheory` does not prove `p₀`: the standard model with `p₀` false
satisfies the theory. -/
theorem excludedMiddleTheory_not_provable_atom :
    ¬ Provable (Const := WithParams Atom) excludedMiddleTheory atom0 := fun h =>
  (standardModel_models_atom0 fun _ => False).mp
    (models_of_excludedMiddleTheory_provable h _ (standardModel_extensional _))

/-- `excludedMiddleTheory` does not prove `¬ p₀`: the standard model with `p₀` true
satisfies the theory. -/
theorem excludedMiddleTheory_not_provable_not_atom :
    ¬ Provable (Const := WithParams Atom) excludedMiddleTheory (.not atom0) := fun h =>
  (HenkinModel.models_not _).mp
    (models_of_excludedMiddleTheory_provable h _ (standardModel_extensional _))
    ((standardModel_models_atom0 fun _ => True).mpr trivial)

/-! ## Completeness over the original signature

Positive instances of the original-signature theorems of `SevenVirtues.Completeness`
over the propositional signature, which has no base type, so the inhabitant hypothesis
is met by `PEmpty.elim`. -/

/-- No base type, so there is nothing to inhabit. -/
def atomInhabitants : ∀ b : AtomBase, ClosedTerm Atom (.base b) := fun b => b.elim

/-- The standard model of a valuation over the propositional signature itself. -/
def atomModel (v : ℕ → Prop) : HenkinModel.{0, 0, 0} AtomBase Atom :=
  HenkinModel.standard standardCarrier (fun {_} c => standardConst v (inj c))

theorem atomModel_extensional (v : ℕ → Prop) : (atomModel v).FunctionsRespectEqv :=
  (atomModel v).functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _)

theorem atomModel_models_atom (v : ℕ → Prop) :
    (atomModel v).models (embed (.atom 0)) ↔ v 0 := Iff.rfl

/-- The theory `{p₀}` over the original signature. -/
def atomTheory : ClosedTheorySet Atom := {embed (.atom 0)}

theorem atomTheory_models (v : ℕ → Prop) (h : v 0) :
    ∀ ψ ∈ atomTheory, (atomModel v).models ψ := by
  intro ψ hψ
  rw [atomTheory, Set.mem_singleton_iff] at hψ
  subst hψ
  exact (atomModel_models_atom v).mpr h

theorem atomTheory_consistent :
    Consistent (Const := Atom) (insert excludedMiddle atomTheory) := fun hBot =>
  HenkinModel.models_bot _ (soundness hBot (atomModel fun _ => True) (atomModel_extensional _)
    (atomTheory_models _ trivial))

/-- **Positive control** for `SevenVirtues.soundness`. -/
theorem atomTheory_soundness :
    (atomModel fun _ => True).models excludedMiddle :=
  soundness (T := atomTheory) (provable_of_mem (Set.mem_insert _ _)) _
    (atomModel_extensional _) (atomTheory_models _ trivial)

/-- **Positive control** for `SevenVirtues.exists_model_of_consistent`. -/
theorem atomTheory_has_model :
    ∃ M : HenkinModel.{0, 0, 0} AtomBase Atom,
      M.FunctionsRespectEqv ∧ ∀ ψ ∈ atomTheory, M.models ψ :=
  exists_model_of_consistent atomInhabitants atomTheory_consistent

/-- **Positive control** for `SevenVirtues.completeness`. -/
theorem atomTheory_proves_excludedMiddle :
    Provable (Const := Atom) (insert excludedMiddle atomTheory) excludedMiddle :=
  completeness atomInhabitants fun M _ _ => models_excludedMiddle M

/-- **Positive control** for `SevenVirtues.provable_iff_valid`. -/
theorem atomTheory_provable_iff_valid :
    Provable (Const := Atom) (insert excludedMiddle atomTheory) (embed (.atom 0)) ↔
      ∀ M : HenkinModel.{0, 0, 0} AtomBase Atom, M.FunctionsRespectEqv →
        (∀ ψ ∈ atomTheory, M.models ψ) → M.models (embed (.atom 0)) :=
  provable_iff_valid atomInhabitants atomTheory (embed (.atom 0))

#print axioms excludedMiddleTheory_has_model
#print axioms excludedMiddleTheory_has_extensional_model
#print axioms paramImage_has_extensional_model
#print axioms excludedMiddleTheory_not_provable_atom
#print axioms excludedMiddleTheory_not_provable_not_atom
#print axioms atomTheory_soundness
#print axioms atomTheory_has_model
#print axioms atomTheory_proves_excludedMiddle
#print axioms atomTheory_provable_iff_valid

end HenkinCompletenessControls

end Mettapedia.Logic.HOL
