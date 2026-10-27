import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Finite
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Transfer
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateEquations
import Mettapedia.OSLF.MeTTaIL.ReferenceStepAgreement

/-!
# Finite-model certificates for generated formulas

A finite-model certificate interprets a language's constructors, binders and collections over a finite
carrier, with a preorder that every rule goes down (`Framework/FiniteModelContextual`). It is also a
finite structure (`certificateStructure`):
- its steps are the preorder;
- a constructor builds the value the model computes, and the empty and one-element collections are the
  model's;
- bound variables are the model's junk value, and a term names its value;
- splits, bodies, types and relations are not constrained.

**A valid certificate maps the language's structure into its own** (`certificateHom`), for a language
whose rules both relations interpret alike (`ReferenceProfile`) and a model that respects the language's
equations (`RespectsEquations`, which the equation checks of `CertificateEquations` establish). Every reference step goes down
the preorder by the contextual rule check, and every shape goes to the value the model computes.

So the evaluator's verdict on the certificate's finite structure is a theorem about the language
(`proves_sound`, `refutes_sound`): a universal formula that holds at a term's value holds at the term,
and an existential formula that fails at a term's value fails at the term. The certificate compresses a
verdict about infinitely many terms and runs into a finite computation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.Framework.FiniteModels (Certificate value)

variable {A : Type} [DecidableEq A]

/-- **The finite structure of a certificate**: its preorder as steps, and the shapes its model computes. -/
def certificateStructure (certificate : Certificate A) : FiniteStructure A where
  elements := certificate.elements
  complete := certificate.complete
  step source _ target := certificate.below source target
  built element constructor parts := element == certificate.model.operation constructor parts
  split _ _ _ _ := true
  empty element kind := element == certificate.model.collectionUnit kind
  single element kind member :=
    element == certificate.model.collectionJoin kind member (certificate.model.collectionUnit kind)
  body _ _ := true
  multiBody _ _ _ := true
  bound element _ := element == certificate.model.junk
  typed _ _ := true
  named element term := element == value certificate.model term
  same first second := decide (first = second)
  apply inner _ := inner
  inRelation _ _ := true

/-- Every model respects the equations of an equation-free language. -/
theorem respectsEquations_of_isEquationFree (certificate : Certificate A) (relEnv : RelationEnv)
    {language : LanguageDef} (free : language.isEquationFree = true) :
    RespectsEquations certificate relEnv language :=
  fun _ _ equivalent => by rw [(objectEquivalent_iff_eq_of_isEquationFree free).mp equivalent]

variable {relEnv : RelationEnv} {language : LanguageDef} {reading : LanguageReading}

/-- **A valid certificate maps the language's structure into its own**, in a reading its model respects. -/
def certificateHom (certificate : Certificate A) (checked : certificate.contextualValid language = true)
    (profile : ReferenceProfile language) (respects : RespectsEquations certificate relEnv language reading)
    (reference : reading.rules = .reference := by rfl) :
    Hom (referenceStructure relEnv language reading) (certificateStructure certificate).native where
  map := value certificate.model
  step := by
    rintro source label target own ⟨-, -, redex, contractum, witness, before, redexState, valid, -, after, -⟩
    rw [placed_iff own] at before
    rw [reference] at valid
    obtain ⟨fuel, stepped⟩ := (contextualStep_iff_step relEnv language profile).mpr ⟨witness, valid⟩
    have down := certificate.contextual_below checked
      (Mettapedia.OSLF.Framework.FiniteModels.engine_extends relEnv language) fuel stepped redexState.2 []
    show certificate.below (value certificate.model source) (value certificate.model target) = true
    rw [respects _ _ before, ← respects _ _ after]
    exact down
  built := by
    rintro element constructor parts ⟨-, equivalent⟩
    show (value certificate.model element ==
      certificate.model.operation constructor (parts.map (value certificate.model))) = true
    rw [respects _ _ equivalent]
    simp only [value, Mettapedia.OSLF.Framework.FiniteModels.eval,
      Mettapedia.OSLF.Framework.FiniteModels.evalList_eq_map]
    exact beq_self_eq_true _
  split := fun _ => rfl
  empty := by
    rintro element kind ⟨-, equivalent⟩
    show (value certificate.model element == certificate.model.collectionUnit kind) = true
    rw [respects _ _ equivalent]
    simp [value, Mettapedia.OSLF.Framework.FiniteModels.eval, Mettapedia.OSLF.Framework.FiniteModels.evalList,
      Mettapedia.OSLF.Framework.FiniteModels.restValue]
  single := by
    rintro element kind member ⟨-, equivalent⟩
    show (value certificate.model element ==
      certificate.model.collectionJoin kind (value certificate.model member) (certificate.model.collectionUnit kind)) = true
    rw [respects _ _ equivalent]
    simp [value, Mettapedia.OSLF.Framework.FiniteModels.eval, Mettapedia.OSLF.Framework.FiniteModels.evalList,
      Mettapedia.OSLF.Framework.FiniteModels.restValue]
  body := fun _ => rfl
  multiBody := fun _ => rfl
  bound := by
    rintro element index ⟨-, equivalent⟩
    show (value certificate.model element == certificate.model.junk) = true
    rw [respects _ _ equivalent]
    simp [value, Mettapedia.OSLF.Framework.FiniteModels.eval]
  typed := fun _ => rfl
  named := by
    rintro element term ⟨-, equivalent⟩
    show (value certificate.model element == value certificate.model term) = true
    rw [respects _ _ equivalent]
    simp
  inRelation := fun _ => rfl

/-- The rules of the language are interpreted alike by the reference and the contextual relations. -/
def aligned (language : LanguageDef) : Bool := language.rewrites.all ruleAligned

theorem profile_of_aligned (checked : aligned language = true) : ReferenceProfile language :=
  fun rule member => List.all_eq_true.mp checked rule member

/-- **A certificate proves a universal formula at a term**: it is valid, it respects the equations, the
rules are aligned, and the formula holds at the term's value. -/
def proves (certificate : Certificate A) (language : LanguageDef) (formula : Formula 0) (term : Pattern) : Bool :=
  certificate.contextualValid language && Certificate.equationsValid certificate language && aligned language &&
    formula.universal && (certificateStructure certificate).check formula (value certificate.model term)

/-- **A certificate refutes an existential formula at a term**: it is valid, it respects the equations,
the rules are aligned, and the formula fails at the term's value. -/
def refutes (certificate : Certificate A) (language : LanguageDef) (formula : Formula 0) (term : Pattern) : Bool :=
  certificate.contextualValid language && Certificate.equationsValid certificate language && aligned language &&
    formula.existential && !(certificateStructure certificate).check formula (value certificate.model term)

/-- **What a certificate proves holds.** -/
theorem proves_sound {certificate : Certificate A} {formula : Formula 0} {term : Pattern}
    (checked : proves certificate language formula term = true) (reference : reading.rules = .reference := by rfl) :
    (referenceStructure relEnv language reading).sat Env.closed formula term := by
  simp only [proves, Bool.and_eq_true] at checked
  obtain ⟨⟨⟨⟨valid, equations⟩, isAligned⟩, universal⟩, holds⟩ := checked
  exact (certificateHom certificate valid (profile_of_aligned isAligned)
    ((respectsEquations_of_equationsValid valid equations).reading reading) reference).sat_of_hom_universal formula
    universal (sourceEnv := Env.closed) (targetEnv := Env.closed) (fun index => index.elim0) term
    (((certificateStructure certificate).check_iff formula _).mp holds)

/-- **What a certificate refutes fails.** -/
theorem refutes_sound {certificate : Certificate A} {formula : Formula 0} {term : Pattern}
    (checked : refutes certificate language formula term = true) (reference : reading.rules = .reference := by rfl) :
    ¬ (referenceStructure relEnv language reading).sat Env.closed formula term := by
  simp only [refutes, Bool.and_eq_true, Bool.not_eq_true'] at checked
  obtain ⟨⟨⟨⟨valid, equations⟩, isAligned⟩, existential⟩, fails⟩ := checked
  refine (certificateHom certificate valid (profile_of_aligned isAligned)
    ((respectsEquations_of_equationsValid valid equations).reading reading) reference).not_sat_of_hom existential
    (sourceEnv := Env.closed) (targetEnv := Env.closed) (fun index => index.elim0) fun holds => ?_
  rw [← (certificateStructure certificate).check_iff] at holds
  exact Bool.false_ne_true (fails.symm.trans holds)

/-- **A refutation is a proof of the dual.** -/
theorem refutes_sound_dual {certificate : Certificate A} {formula : Formula 0} {term : Pattern}
    (checked : refutes certificate language formula term = true) (reference : reading.rules = .reference := by rfl) :
    (referenceStructure relEnv language reading).sat Env.closed formula.dual term :=
  ((referenceStructure relEnv language reading).sat_dual_closed formula term).mpr (refutes_sound checked reference)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
