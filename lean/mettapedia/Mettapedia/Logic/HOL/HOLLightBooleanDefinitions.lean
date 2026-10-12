import Mettapedia.Logic.HOL.ConstantSubstitutionSemantics
import Mettapedia.Logic.HOL.ImpredicativeConnectives
import Mettapedia.Logic.HOL.HOLLightStandardTheory
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Equality-based Boolean definitions of HOL Light

These are definition-erased images of the Boolean bodies in HOL Light
revision `924faf0c3471a04174ffdeb8576ce7cabcb92d64`. They use the shared
intrinsically typed STT terms, with equality, abstraction and application.
Quantification and implication are constructed terms, not primitive logical
constructors. Their denotations are proved in the existing full-domain models.

Source declaration identities and registered-history interpretation remain
separate from this elimination of their defining bodies.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.HOLLightBooleanDefinitions

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}
  {context : Ctx Base} {type domain codomain : Ty Base}

def applyClosed (function : ClosedTerm Const (domain ⇒ codomain))
    (argument : Term Const context domain) : Term Const context codomain :=
  .app (weakenCtx context function) argument

def truth : ClosedTerm Const .prop :=
  .eq (.lam (.var (.vz : Var [.prop] .prop))) (.lam (.var .vz))

def conjunction : ClosedTerm Const (.prop ⇒ .prop ⇒ .prop) :=
  .lam (.lam (.eq
    (.lam (.app (.app (.var .vz) (.var (.vs (.vs .vz)))) (.var (.vs .vz))) :
      Term Const [.prop, .prop] ((.prop ⇒ .prop ⇒ .prop) ⇒ .prop))
    (.lam (.app (.app (.var .vz) (weakenCtx _ truth)) (weakenCtx _ truth)))))

def conj (left right : Formula Const context) : Formula Const context :=
  .app (applyClosed conjunction left) right

def implication : ClosedTerm Const (.prop ⇒ .prop ⇒ .prop) :=
  .lam (.lam (.eq (conj (.var (.vs .vz)) (.var .vz)) (.var (.vs .vz))))

def imp (left right : Formula Const context) : Formula Const context :=
  .app (applyClosed implication left) right

def universal (type : Ty Base) : ClosedTerm Const ((type ⇒ .prop) ⇒ .prop) :=
  .lam (.eq (.var .vz) (.lam (weakenCtx _ truth)))

def all (body : Formula Const (type :: context)) : Formula Const context :=
  applyClosed (universal type) (.lam body)

def existential (type : Ty Base) : ClosedTerm Const ((type ⇒ .prop) ⇒ .prop) :=
  .lam (all (imp
    (all (imp (.app (.var (.vs (.vs .vz))) (.var .vz)) (.var (.vs .vz))))
    (.var .vz)))

def ex (body : Formula Const (type :: context)) : Formula Const context :=
  applyClosed (existential type) (.lam body)

def falsity : ClosedTerm Const .prop :=
  all (.var (.vz : Var [.prop] .prop))

def negation : ClosedTerm Const (.prop ⇒ .prop) :=
  .lam (imp (.var .vz) (weakenCtx _ falsity))

def oneOne (domain codomain : Ty Base) :
    ClosedTerm Const ((domain ⇒ codomain) ⇒ .prop) :=
  .lam (all (all (imp
    (.eq (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
      (.app (.var (.vs (.vs .vz))) (.var .vz)))
    (.eq (.var (.vs .vz)) (.var .vz)))))

def onto (domain codomain : Ty Base) :
    ClosedTerm Const ((domain ⇒ codomain) ⇒ .prop) :=
  .lam (all (ex (.eq (.var (.vs .vz))
    (.app (.var (.vs (.vs .vz))) (.var .vz)))))

theorem denote_applyClosed (model : HenkinModel.{u, v, w} Base Const)
    (function : ClosedTerm Const (domain ⇒ codomain))
    (argument : Term Const context domain) (valuation : model.Valuation context) :
    model.denote (applyClosed function argument) valuation =
      model.denote function (fun index => nomatch index) (model.denote argument valuation) := by
  exact congrFun (model.denote_weakenCtx context function valuation) _

theorem denote_truth (model : HenkinModel.{u, v, w} Base Const)
    (valuation : model.Valuation []) : model.denote truth valuation = .up True := by
  apply ULift.ext
  apply propext
  change (∀ value, model.adm .prop value → (value.down ↔ value.down)) ↔ True
  simp

theorem denote_conjunction (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (valuation : model.Valuation [])
    (left right : Ty.denote model.Carrier .prop) :
    model.denote conjunction valuation left right = .up (left.down ∧ right.down) := by
  apply ULift.ext
  apply propext
  have liftedTruth {gamma : Ctx Base} (rho : model.Valuation gamma) :
      model.denote (weakenCtx gamma truth) rho = ULift.up True :=
    (model.denote_weakenCtx gamma truth rho).trans (denote_truth model _)
  simp only [conjunction, HenkinModel.denote, PreModel.denote, liftedTruth,
    PreModel.Eqv, PreModel.extend]
  constructor
  · intro equal
    have first := equal (fun p _ => p) (full _ _)
    have second := equal (fun _ q => q) (full _ _)
    exact ⟨first.mpr True.intro, second.mpr True.intro⟩
  · rintro ⟨leftTrue, rightTrue⟩ function _
    have leftEq : left = ULift.up True := by
      apply ULift.ext
      exact propext (iff_true_intro leftTrue)
    have rightEq : right = ULift.up True := by
      apply ULift.ext
      exact propext (iff_true_intro rightTrue)
    rw [leftEq, rightEq]

theorem denote_conj (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (left right : Formula Const context)
    (valuation : model.Valuation context) :
    model.denote (conj left right) valuation =
      .up ((model.denote left valuation).down ∧ (model.denote right valuation).down) := by
  change model.denote (applyClosed conjunction left) valuation
    (model.denote right valuation) = _
  rw [denote_applyClosed]
  exact denote_conjunction model full _ _ _

theorem denote_implication (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (valuation : model.Valuation [])
    (left right : Ty.denote model.Carrier .prop) :
    model.denote implication valuation left right = .up (left.down → right.down) := by
  change ULift.up
    ((model.denote (conj (.var (.vs .vz)) (.var .vz))
      (model.extend (model.extend valuation left) right)).down ↔ left.down) = _
  rw [denote_conj model full]
  apply ULift.ext
  apply propext
  exact ⟨fun equal premise => (equal.mpr premise).2,
    fun implication => ⟨And.left, fun premise => ⟨premise, implication premise⟩⟩⟩

theorem denote_imp (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (left right : Formula Const context)
    (valuation : model.Valuation context) :
    model.denote (imp left right) valuation =
      .up ((model.denote left valuation).down → (model.denote right valuation).down) := by
  change model.denote (applyClosed implication left) valuation
    (model.denote right valuation) = _
  rw [denote_applyClosed]
  exact denote_implication model full _ _ _

theorem denote_universal (model : HenkinModel.{u, v, w} Base Const)
    (valuation : model.Valuation []) (predicate : Ty.denote model.Carrier (type ⇒ .prop)) :
    model.denote (universal type) valuation predicate =
      .up (∀ value, model.adm type value → (predicate value).down) := by
  apply ULift.ext
  apply propext
  have liftedTruth {gamma : Ctx Base} (rho : model.Valuation gamma) :
      model.denote (weakenCtx gamma truth) rho = ULift.up True :=
    (model.denote_weakenCtx gamma truth rho).trans (denote_truth model _)
  simp only [universal, HenkinModel.denote, PreModel.denote, liftedTruth,
    PreModel.Eqv, PreModel.extend]
  constructor
  · intro equal value admissible
    exact (equal value admissible).mpr True.intro
  · intro holds value admissible
    exact iff_true_intro (holds value admissible)

theorem denote_all (model : HenkinModel.{u, v, w} Base Const)
    (body : Formula Const (type :: context)) (valuation : model.Valuation context) :
    model.denote (all body) valuation =
      .up (∀ value, model.adm type value →
        (model.denote body (model.extend valuation value)).down) := by
  rw [all, denote_applyClosed]
  exact denote_universal model _ _

theorem denote_existential (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (valuation : model.Valuation [])
    (predicate : Ty.denote model.Carrier (type ⇒ .prop)) :
    model.denote (existential type) valuation predicate =
      .up (∃ value, model.adm type value ∧ (predicate value).down) := by
  have encoding := ImpredicativeConnectives.denote_existential model valuation type predicate
  rw [← encoding]
  simp only [existential, HenkinModel.denote, PreModel.denote,
    denote_all, denote_imp model full, ImpredicativeConnectives.existential,
    PreModel.extend]
  rfl

theorem denote_ex (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (body : Formula Const (type :: context))
    (valuation : model.Valuation context) :
    model.denote (ex body) valuation =
      .up (∃ value, model.adm type value ∧
        (model.denote body (model.extend valuation value)).down) := by
  rw [ex, denote_applyClosed]
  exact denote_existential model full _ _

theorem denote_falsity (model : HenkinModel.{u, v, w} Base Const)
    (valuation : model.Valuation []) : model.denote falsity valuation = .up False := by
  apply ULift.ext
  apply propext
  simp only [falsity, denote_all, HenkinModel.denote, PreModel.denote, PreModel.extend]
  exact ⟨fun holds => holds (.up False) (model.prop_mem _), False.elim⟩

theorem denote_negation (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (valuation : model.Valuation [])
    (proposition : Ty.denote model.Carrier .prop) :
    model.denote negation valuation proposition = .up (¬ proposition.down) := by
  change model.denote (imp (.var .vz) (weakenCtx _ falsity))
    (model.extend valuation proposition) = _
  rw [denote_imp model full, model.denote_weakenCtx, denote_falsity]
  rfl

theorem denote_oneOne (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (valuation : model.Valuation [])
    (function : Ty.denote model.Carrier (domain ⇒ codomain)) :
    model.denote (oneOne domain codomain) valuation function =
      .up (∀ left, model.adm domain left → ∀ right, model.adm domain right →
        model.Eqv codomain (function left) (function right) → model.Eqv domain left right) := by
  simp only [oneOne, HenkinModel.denote, PreModel.denote, denote_all,
    denote_imp model full, PreModel.extend]
  rfl

theorem denote_onto (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (valuation : model.Valuation [])
    (function : Ty.denote model.Carrier (domain ⇒ codomain)) :
    model.denote (onto domain codomain) valuation function =
      .up (∀ value, model.adm codomain value →
        ∃ preimage, model.adm domain preimage ∧ model.Eqv codomain value (function preimage)) := by
  simp only [onto, HenkinModel.denote, PreModel.denote, denote_all, denote_ex model full,
    PreModel.extend]
  rfl

/-- The definition-erased source eta formula uses the equality-based
universal operator rather than native universal quantification. -/
def etaFormula (domain codomain : Ty Base) : ClosedFormula Const :=
  all (.eq (.lam (.app (.var (.vs .vz)) (.var .vz)))
    (.var (.vz : Var [domain ⇒ codomain] (domain ⇒ codomain))))

theorem models_etaFormula (model : HenkinModel.{u, v, w} Base Const)
    (domain codomain : Ty Base) : model.models (etaFormula domain codomain) := by
  simp only [etaFormula, HenkinModel.models, PreModel.models, denote_all]
  exact HOLLightStandardTheory.models_eta_in model domain codomain

/-- This is the source `ONE_ONE f /\ ~(ONTO f)` reading, after expanding
those definitions. It does not silently replace non-surjectivity by a
different primitive axiom. -/
def infinityFormula (base : Base) : ClosedFormula Const :=
  ex (conj
    (applyClosed (oneOne (.base base) (.base base)) (.var .vz))
    (.app (weakenCtx _ negation)
      (applyClosed (onto (.base base) (.base base)) (.var .vz))))

theorem models_infinityFormula (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (base : Base)
    (witness : model.DedekindInfinityWitness base) :
    model.models (infinityFormula base) := by
  simp only [infinityFormula, HenkinModel.models, PreModel.models,
    denote_ex model full, denote_conj model full, denote_applyClosed,
    model.denote_weakenCtx,
    denote_oneOne model full, denote_onto model full,
    HenkinModel.denote, PreModel.denote, PreModel.extend, PreModel.Eqv]
  refine ⟨witness.successor, witness.successor_admissible, ?_, ?_⟩
  · intro left _ right _ sameImage
    exact witness.successor_injective sameImage
  · have notOnto : ¬ (∀ value : model.Carrier base, model.adm (.base base) value →
        ∃ preimage : model.Carrier base,
          model.adm (.base base) preimage ∧ value = witness.successor preimage) := by
      intro onto
      obtain ⟨preimage, _, sameImage⟩ := onto witness.omitted witness.omitted_admissible
      exact witness.omitted_not_image preimage sameImage.symm
    have negated := denote_negation model full (fun index => nomatch index)
      (ULift.up (∀ value : model.Carrier base, model.adm (.base base) value →
        ∃ preimage : model.Carrier base,
          model.adm (.base base) preimage ∧ value = witness.successor preimage))
    exact (congrArg ULift.down negated).symm ▸ notOnto

/-- The erased false definition is rejected in every existing Henkin model. -/
theorem not_models_falsity (model : HenkinModel.{u, v, w} Base Const) :
    ¬ model.models (falsity : ClosedFormula Const) := by
  change ¬ (model.denote falsity (fun index => nomatch index)).down
  rw [denote_falsity]
  exact False.elim

theorem conjunction_does_not_accept_one_true_input
    (model : HenkinModel.{u, v, w} Base Const) (full : model.FullDomains) :
    model.denote conjunction (fun index => nomatch index) (.up True) (.up False) =
      ULift.up False := by
  simpa only [and_false] using
    denote_conjunction model full (fun index => nomatch index) (.up True) (.up False)

end Mettapedia.Logic.HOL.HOLLightBooleanDefinitions
