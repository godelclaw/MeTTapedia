import Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryEquationSoundness
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractEvidenceExtraction

/-!
# Actual evaluator readouts of equation-extended derivations

The independently authored rule trees prove successful raw evaluation. Their
sections and substitutions are extracted from that evaluation, and the local
declaration comparisons earn independence from all generated equations.
Complete dependent sections remain retained under substitution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryEquations

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Refinement.Abstract

universe a c s t m p
variable {S : Symbols.{a}} {C : CwfWithTerminal.{c, s, t, m}}
  {localModel : LocalModel.{c, s, t, m, p} C}
  {D : Signature S} {equations : Presentation S} {n : Nat}

namespace Evidence


variable (model : ModelData S C localModel) (realization : SignatureRealization model D)
  (qualified : Qualification localModel)
  (admitted : Admitted model equations)
  {context : ContextExpr S n} {term : TermExpr S n} {type : TypeExpr S n}

include model realization qualified admitted

theorem contextValue_isSome (derivation : TheoryEquations.Derivation D equations (.context context)) :
    (model.evaluateContext context).isSome :=
  Option.isSome_iff_exists.mpr (TheoryEquations.sound model realization qualified admitted derivation)

noncomputable def contextValue (derivation : TheoryEquations.Derivation D equations (.context context)) : ModelScope C localModel n :=
  (model.evaluateContext context).get (contextValue_isSome model realization qualified admitted derivation)

theorem contextValue_readout (derivation : TheoryEquations.Derivation D equations (.context context)) :
    model.evaluateContext context = some (contextValue model realization qualified admitted derivation) :=
  (Option.some_get _).symm

theorem contextValue_unique (derivation : TheoryEquations.Derivation D equations (.context context))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    contextValue model realization qualified admitted derivation = Γ :=
  Option.some.inj ((contextValue_readout model realization qualified admitted derivation).symm.trans contextRead)

theorem contextValue_derivation_independent
    (first second : TheoryEquations.Derivation D equations (.context context)) :
    contextValue model realization qualified admitted first = contextValue model realization qualified admitted second :=
  contextValue_unique model realization qualified admitted first _
    (contextValue_readout model realization qualified admitted second)

theorem contextValue_equation {other : ContextExpr S n}
    (first : TheoryEquations.Derivation D equations (.context context)) (second : TheoryEquations.Derivation D equations (.context other))
    (equation : TheoryEquations.Derivation D equations (.contextEq context other)) :
    contextValue model realization qualified admitted first = contextValue model realization qualified admitted second := by
  have read := (TheoryEquations.sound model realization qualified admitted equation).contextEqAt _
    (contextValue_readout model realization qualified admitted first)
  exact (contextValue_unique model realization qualified admitted second _ read).symm

theorem typeValue_isSome (derivation : TheoryEquations.Derivation D equations (.type context type))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    (model.evaluateType Γ type).isSome :=
  Option.isSome_iff_exists.mpr
    ((TheoryEquations.sound model realization qualified admitted derivation).typeAt Γ contextRead)

noncomputable def typeValue (derivation : TheoryEquations.Derivation D equations (.type context type))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) : C.toCwf.Ty Γ.1 :=
  (model.evaluateType Γ type).get
    (typeValue_isSome model realization qualified admitted derivation Γ contextRead)

theorem typeValue_readout (derivation : TheoryEquations.Derivation D equations (.type context type))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    model.evaluateType Γ type = some (typeValue model realization qualified admitted derivation Γ contextRead) :=
  (Option.some_get _).symm

theorem typeValue_unique (derivation : TheoryEquations.Derivation D equations (.type context type))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ)
    (A : C.toCwf.Ty Γ.1) (typeRead : model.evaluateType Γ type = some A) :
    typeValue model realization qualified admitted derivation Γ contextRead = A :=
  Option.some.inj ((typeValue_readout model realization qualified admitted derivation Γ contextRead).symm.trans typeRead)

theorem typeValue_derivation_independent (first second : TheoryEquations.Derivation D equations (.type context type))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    typeValue model realization qualified admitted first Γ contextRead =
      typeValue model realization qualified admitted second Γ contextRead :=
  typeValue_unique model realization qualified admitted first Γ contextRead _
    (typeValue_readout model realization qualified admitted second Γ contextRead)

theorem typeValue_equation {other : TypeExpr S n}
    (first : TheoryEquations.Derivation D equations (.type context type)) (second : TheoryEquations.Derivation D equations (.type context other))
    (equation : TheoryEquations.Derivation D equations (.typeEq context type other))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    typeValue model realization qualified admitted first Γ contextRead =
      typeValue model realization qualified admitted second Γ contextRead := by
  have read := (TheoryEquations.sound model realization qualified admitted equation).typeEqAt Γ _ contextRead
    (typeValue_readout model realization qualified admitted first Γ contextRead)
  exact (typeValue_unique model realization qualified admitted second Γ contextRead _ read).symm

/-- The generated judgment supplies the successful-check proof; the returned
value is read from the authored raw expression evaluator. -/
noncomputable def termSection (derivation : TheoryEquations.Derivation D equations (.term context term type))
    (Γ : ModelScope C localModel n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) : C.toCwf.Tm Γ.1 A :=
  (ModelData.check? (model.evaluateTerm Γ term) A).get
    ((TheoryEquations.sound model realization qualified admitted derivation).termChecked_isSome
      Γ A contextRead typeRead)

theorem termSection_checked (derivation : TheoryEquations.Derivation D equations (.term context term type))
    (Γ : ModelScope C localModel n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) :
    ModelData.check? (model.evaluateTerm Γ term) A =
      some (termSection model realization qualified admitted derivation Γ A contextRead typeRead) :=
  (Option.some_get _).symm

theorem termSection_readout (derivation : TheoryEquations.Derivation D equations (.term context term type))
    (Γ : ModelScope C localModel n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) :
    model.evaluateTerm Γ term = some ⟨A,
      termSection model realization qualified admitted derivation Γ A contextRead typeRead⟩ :=
  (ModelData.check?_eq_some_iff _ _ _).mp
    (termSection_checked model realization qualified admitted derivation Γ A contextRead typeRead)

theorem termSection_unique (derivation : TheoryEquations.Derivation D equations (.term context term type))
    (Γ : ModelScope C localModel n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) (value : C.toCwf.Tm Γ.1 A)
    (sectionRead : model.evaluateTerm Γ term = some ⟨A, value⟩) :
    termSection model realization qualified admitted derivation Γ A contextRead typeRead = value :=
  Option.some.inj
    ((termSection_checked model realization qualified admitted derivation Γ A contextRead typeRead).symm.trans
      ((ModelData.check?_eq_some_iff _ _ _).mpr sectionRead))

theorem termSection_derivation_independent
    (first second : TheoryEquations.Derivation D equations (.term context term type))
    (Γ : ModelScope C localModel n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) :
    termSection model realization qualified admitted first Γ A contextRead typeRead =
      termSection model realization qualified admitted second Γ A contextRead typeRead :=
  termSection_unique model realization qualified admitted first Γ A contextRead typeRead _
    (termSection_readout model realization qualified admitted second Γ A contextRead typeRead)

theorem termSection_annotation_independent {otherType : TypeExpr S n}
    (first : TheoryEquations.Derivation D equations (.term context term type))
    (second : TheoryEquations.Derivation D equations (.term context term otherType))
    (Γ : ModelScope C localModel n) (A B : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A)
    (otherTypeRead : model.evaluateType Γ otherType = some B) :
    A = B ∧ HEq (termSection model realization qualified admitted first Γ A contextRead typeRead)
      (termSection model realization qualified admitted second Γ B contextRead otherTypeRead) :=
  ModelData.checked_readout_unique
    (termSection_checked model realization qualified admitted first Γ A contextRead typeRead)
    (termSection_checked model realization qualified admitted second Γ B contextRead otherTypeRead)

theorem termSection_equation {other : TermExpr S n}
    (first : TheoryEquations.Derivation D equations (.term context term type))
    (second : TheoryEquations.Derivation D equations (.term context other type))
    (equation : TheoryEquations.Derivation D equations (.termEq context term other type))
    (Γ : ModelScope C localModel n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.evaluateContext context = some Γ)
    (typeRead : model.evaluateType Γ type = some A) :
    termSection model realization qualified admitted first Γ A contextRead typeRead =
      termSection model realization qualified admitted second Γ A contextRead typeRead := by
  rcases (TheoryEquations.sound model realization qualified admitted equation).termEqAt
    Γ A contextRead typeRead with ⟨value, firstRead, secondRead⟩
  exact (termSection_unique model realization qualified admitted first Γ A contextRead typeRead _ firstRead).trans
    (termSection_unique model realization qualified admitted second Γ A contextRead typeRead _ secondRead).symm

variable {predicate : PropExpr S n}

theorem predicateValue_isSome (derivation : TheoryEquations.Derivation D equations (.predicate context predicate))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    (model.evaluatePredicate Γ predicate).isSome :=
  Option.isSome_iff_exists.mpr
    ((TheoryEquations.sound model realization qualified admitted derivation).predicateAt Γ contextRead)

noncomputable def predicateValue (derivation : TheoryEquations.Derivation D equations (.predicate context predicate))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) : localModel.doctrine.Predicate Γ.1 :=
  (model.evaluatePredicate Γ predicate).get
    (predicateValue_isSome model realization qualified admitted derivation Γ contextRead)

theorem predicateValue_readout (derivation : TheoryEquations.Derivation D equations (.predicate context predicate))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    model.evaluatePredicate Γ predicate =
      some (predicateValue model realization qualified admitted derivation Γ contextRead) :=
  (Option.some_get _).symm

theorem predicateValue_unique (derivation : TheoryEquations.Derivation D equations (.predicate context predicate))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ)
    (φ : localModel.doctrine.Predicate Γ.1) (predicateRead : model.evaluatePredicate Γ predicate = some φ) :
    predicateValue model realization qualified admitted derivation Γ contextRead = φ :=
  Option.some.inj
    ((predicateValue_readout model realization qualified admitted derivation Γ contextRead).symm.trans predicateRead)

theorem predicateValue_derivation_independent
    (first second : TheoryEquations.Derivation D equations (.predicate context predicate))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    predicateValue model realization qualified admitted first Γ contextRead =
      predicateValue model realization qualified admitted second Γ contextRead :=
  predicateValue_unique model realization qualified admitted first Γ contextRead _
    (predicateValue_readout model realization qualified admitted second Γ contextRead)

theorem predicateValue_equation {other : PropExpr S n}
    (first : TheoryEquations.Derivation D equations (.predicate context predicate))
    (second : TheoryEquations.Derivation D equations (.predicate context other))
    (equation : TheoryEquations.Derivation D equations (.predicateEq context predicate other))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    predicateValue model realization qualified admitted first Γ contextRead =
      predicateValue model realization qualified admitted second Γ contextRead := by
  have read := (TheoryEquations.sound model realization qualified admitted equation).predicateEqAt Γ _ contextRead
    (predicateValue_readout model realization qualified admitted first Γ contextRead)
  exact (predicateValue_unique model realization qualified admitted second Γ contextRead _ read).symm

theorem predicateValue_entailment (formed : TheoryEquations.Derivation D equations (.predicate context predicate))
    (derivation : TheoryEquations.Derivation D equations (.entails context predicate))
    (Γ : ModelScope C localModel n) (contextRead : model.evaluateContext context = some Γ) :
    predicateValue model realization qualified admitted formed Γ contextRead = ⊤ :=
  predicateValue_unique model realization qualified admitted formed Γ contextRead _
    ((TheoryEquations.sound model realization qualified admitted derivation).entailsAt Γ contextRead)

variable {k : Nat} {source : ContextExpr S n} {target : ContextExpr S k}
  {substitution : Substitution S k n}

theorem substitutionArrow_isSome
    (derivation : TheoryEquations.Derivation D equations (.substitution source target substitution))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    (model.evaluateSubstitution Γ Δ substitution).isSome :=
  Option.isSome_iff_exists.mpr
    ((TheoryEquations.sound model realization qualified admitted derivation).substitutionAt Γ Δ sourceRead targetRead)

noncomputable def substitutionArrow
    (derivation : TheoryEquations.Derivation D equations (.substitution source target substitution))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) : C.toCwf.Sub Γ.1 Δ.1 :=
  (model.evaluateSubstitution Γ Δ substitution).get
    (substitutionArrow_isSome model realization qualified admitted derivation Γ Δ sourceRead targetRead)

theorem substitutionArrow_readout
    (derivation : TheoryEquations.Derivation D equations (.substitution source target substitution))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    model.evaluateSubstitution Γ Δ substitution =
      some (substitutionArrow model realization qualified admitted derivation Γ Δ sourceRead targetRead) :=
  (Option.some_get _).symm

theorem substitutionArrow_unique
    (derivation : TheoryEquations.Derivation D equations (.substitution source target substitution))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) (arrow : C.toCwf.Sub Γ.1 Δ.1)
    (arrowRead : model.evaluateSubstitution Γ Δ substitution = some arrow) :
    substitutionArrow model realization qualified admitted derivation Γ Δ sourceRead targetRead = arrow :=
  Option.some.inj
    ((substitutionArrow_readout model realization qualified admitted derivation Γ Δ sourceRead targetRead).symm.trans arrowRead)

theorem substitutionArrow_derivation_independent
    (first second : TheoryEquations.Derivation D equations (.substitution source target substitution))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    substitutionArrow model realization qualified admitted first Γ Δ sourceRead targetRead =
      substitutionArrow model realization qualified admitted second Γ Δ sourceRead targetRead :=
  substitutionArrow_unique model realization qualified admitted first Γ Δ sourceRead targetRead _
    (substitutionArrow_readout model realization qualified admitted second Γ Δ sourceRead targetRead)

theorem substitutionArrow_equation {other : Substitution S k n}
    (first : TheoryEquations.Derivation D equations (.substitution source target substitution))
    (second : TheoryEquations.Derivation D equations (.substitution source target other))
    (equation : TheoryEquations.Derivation D equations (.substitutionEq source target substitution other))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    substitutionArrow model realization qualified admitted first Γ Δ sourceRead targetRead =
      substitutionArrow model realization qualified admitted second Γ Δ sourceRead targetRead := by
  rcases (TheoryEquations.sound model realization qualified admitted equation).substitutionEqAt Γ Δ sourceRead targetRead
    with ⟨arrow, firstRead, secondRead⟩
  exact (substitutionArrow_unique model realization qualified admitted first Γ Δ sourceRead targetRead _ firstRead).trans
    (substitutionArrow_unique model realization qualified admitted second Γ Δ sourceRead targetRead _ secondRead).symm

theorem termSection_substitution {body : TermExpr S k} {annotation : TypeExpr S k}
    (original : TheoryEquations.Derivation D equations (.term target body annotation))
    (substituted : TheoryEquations.Derivation D equations (.term source (body.substitute substitution)
      (annotation.substitute substitution)))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k) (modelMap : ModelSubstitution model Γ Δ substitution)
    (A : C.toCwf.Ty Δ.1)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ)
    (typeRead : model.evaluateType Δ annotation = some A) :
    termSection model realization qualified admitted substituted Γ (C.toCwf.tySub A modelMap.arrow)
        sourceRead (model.evaluateType_substitute qualified.stableProducts annotation Γ Δ substitution modelMap A typeRead) =
      C.toCwf.tmSub (termSection model realization qualified admitted original Δ A targetRead typeRead)
        modelMap.arrow :=
  termSection_unique model realization qualified admitted substituted Γ _ sourceRead
    (model.evaluateType_substitute qualified.stableProducts annotation Γ Δ substitution modelMap A typeRead) _
    (model.evaluateTerm_substitute qualified.stableProducts body Γ Δ substitution modelMap
      ⟨A, termSection model realization qualified admitted original Δ A targetRead typeRead⟩
      (termSection_readout model realization qualified admitted original Δ A targetRead typeRead))

theorem typeValue_substitution {annotation : TypeExpr S k}
    (original : TheoryEquations.Derivation D equations (.type target annotation))
    (substituted : TheoryEquations.Derivation D equations (.type source (annotation.substitute substitution)))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k) (modelMap : ModelSubstitution model Γ Δ substitution)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    typeValue model realization qualified admitted substituted Γ sourceRead =
      C.toCwf.tySub (typeValue model realization qualified admitted original Δ targetRead) modelMap.arrow :=
  typeValue_unique model realization qualified admitted substituted Γ sourceRead _
    (model.evaluateType_substitute qualified.stableProducts annotation Γ Δ substitution modelMap _
      (typeValue_readout model realization qualified admitted original Δ targetRead))

theorem predicateValue_substitution {formula : PropExpr S k}
    (original : TheoryEquations.Derivation D equations (.predicate target formula))
    (substituted : TheoryEquations.Derivation D equations (.predicate source (formula.substitute substitution)))
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k) (modelMap : ModelSubstitution model Γ Δ substitution)
    (sourceRead : model.evaluateContext source = some Γ)
    (targetRead : model.evaluateContext target = some Δ) :
    predicateValue model realization qualified admitted substituted Γ sourceRead =
      localModel.doctrine.reindex modelMap.arrow
        (predicateValue model realization qualified admitted original Δ targetRead) :=
  predicateValue_unique model realization qualified admitted substituted Γ sourceRead _
    (model.evaluatePredicate_substitute qualified.stableProducts formula Γ Δ substitution modelMap _
      (predicateValue_readout model realization qualified admitted original Δ targetRead))

end Evidence

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryEquations
