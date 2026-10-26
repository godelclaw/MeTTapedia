import Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVec
import Mettapedia.Logic.HOL.IndexedConstructorTerms
import Mettapedia.Logic.HOL.ConstantSubstitutionSemantics

/-!
# HOL index terms for the authored Nat and Vector telescope language

The reading compiles length variables, zero, successor and addition to typed
HOL terms. The generic constructor compiler then produces the actual result-
and child-index functions. Arithmetic operations are explicit closed inputs;
their interpretation laws imply agreement with the source index evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms

open Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open IndexedInductiveNatVec

universe u v w
variable {Base : Type u} {Const : Ty Base → Type v}

structure Arithmetic (Const : Ty Base → Type v) where
  number : Ty Base
  element : Ty Base
  zero : ClosedTerm Const number
  successor : ClosedTerm Const (number ⇒ number)
  addition : ClosedTerm Const (number ⇒ number ⇒ number)

namespace Arithmetic

def emptyValuation (model : HenkinModel.{u,v,w} Base Const) : model.Valuation [] :=
  fun impossible => nomatch impossible

variable (arithmetic : Arithmetic Const)

def sort : Vectors.DataSort → Ty Base
  | .length => arithmetic.number
  | .payload => arithmetic.element

def reference : {context : List Vectors.DataSort} → Vectors.LengthVariable context →
    Var (context.map arithmetic.sort ++ []) arithmetic.number
  | _, .here => .vz
  | _, .there prior => .vs (reference prior)

def term : {context : List Vectors.DataSort} → Vectors.IndexExpr context →
    Term Const (context.map arithmetic.sort ++ []) arithmetic.number
  | _, .zero => weakenCtx _ arithmetic.zero
  | _, .variable referenceIndex => .var (arithmetic.reference referenceIndex)
  | _, .successor expression => .app (weakenCtx _ arithmetic.successor) (term expression)
  | _, .addition first second =>
      .app (.app (weakenCtx _ arithmetic.addition) (term first)) (term second)

def reading (A : Type) : IndexedConstructorTerms.Reading (Vectors.interface A) Const where
  sort := arithmetic.sort
  index := arithmetic.number
  parameters := []
  term := arithmetic.term

noncomputable def resultProgram (A : Type) := (arithmetic.reading A).resultProgram (Vectors.consCode A)
noncomputable def childProgram (A : Type) := (arithmetic.reading A).childProgram (Vectors.consCode A)
  ⟨0, by change 0 < 1; decide⟩

theorem resultProgram_body (A : Type) : arithmetic.resultProgram A =
    (.lam (.lam (.app (weakenCtx _ arithmetic.successor) (.var (.vs .vz)))) :
      ClosedTerm Const (arithmetic.number ⇒ arithmetic.element ⇒ arithmetic.number)) := by
  simp [resultProgram, reading, Vectors.interface, IndexedConstructorTerms.Reading.resultProgram,
    Vectors.consCode, term, sort, reference]
  rfl

theorem childProgram_body (A : Type) : arithmetic.childProgram A =
    (.lam (.lam (.var (.vs .vz))) :
      ClosedTerm Const (arithmetic.number ⇒ arithmetic.element ⇒ arithmetic.number)) := by
  simp [childProgram, reading, Vectors.interface, IndexedConstructorTerms.Reading.childProgram,
    IndexedConstructorTerms.Reading.constantProgram, Vectors.consCode, dataSorts,
    term, sort, reference]
  rfl

variable (A : Type) (model : HenkinModel.{u,v,w} Base Const)
  (encodeNatural : Natural.Carrier → Ty.denote model.Carrier arithmetic.number)
  (encodeElement : A → Ty.denote model.Carrier arithmetic.element)

def encodeData : ∀ sort, Vectors.value A sort → Ty.denote model.Carrier (arithmetic.sort sort)
  | .length, value => encodeNatural value
  | .payload, value => encodeElement value

theorem reference_denote {context : List Vectors.DataSort}
    (referenceIndex : Vectors.LengthVariable context) (environment : Env (Vectors.value A) context) :
    model.denote (.var (arithmetic.reference referenceIndex))
      ((arithmetic.reading A).valuation model
        (arithmetic.encodeData A model encodeNatural encodeElement)
        (emptyValuation model) environment) =
      encodeNatural (referenceIndex.lookup environment) := by
  induction referenceIndex with
  | here => rfl
  | there prior hypotheses => exact hypotheses environment.2

def denotes {type : Ty Base} (value : ClosedTerm Const type) : Ty.denote model.Carrier type :=
  model.denote value (fun impossible => nomatch impossible)

variable
  (zero_correct : denotes model arithmetic.zero = encodeNatural Natural.zero)
  (successor_correct : ∀ value, denotes model arithmetic.successor (encodeNatural value) =
    encodeNatural (Natural.succ value))
  (addition_correct : ∀ first second,
    denotes model arithmetic.addition (encodeNatural first) (encodeNatural second) =
      encodeNatural (Natural.add first second))

include zero_correct successor_correct addition_correct

set_option backward.isDefEq.respectTransparency false in
theorem term_denote {context : List Vectors.DataSort}
    (expression : Vectors.IndexExpr context) (environment : Env (Vectors.value A) context) :
    model.denote (arithmetic.term expression)
      ((arithmetic.reading A).valuation model
        (arithmetic.encodeData A model encodeNatural encodeElement)
        (emptyValuation model) environment) =
      encodeNatural (expression.eval environment) := by
  induction expression with
  | zero =>
      simpa only [term, Vectors.IndexExpr.eval, reading] using
        (model.denote_weakenCtx _ arithmetic.zero
          ((arithmetic.reading A).valuation model
            (arithmetic.encodeData A model encodeNatural encodeElement)
            (emptyValuation model) environment)).trans zero_correct
  | «variable» referenceIndex =>
      simpa only [term, Vectors.IndexExpr.eval] using
        arithmetic.reference_denote A model encodeNatural encodeElement referenceIndex environment
  | successor expression hypotheses =>
      simp only [term, HenkinModel.denote, PreModel.denote, Vectors.IndexExpr.eval]
      rw [← HenkinModel.denote, model.denote_weakenCtx, ← HenkinModel.denote, hypotheses]
      exact successor_correct _
  | addition first second firstHyp secondHyp =>
      simp only [term, HenkinModel.denote, PreModel.denote, Vectors.IndexExpr.eval]
      rw [← HenkinModel.denote, model.denote_weakenCtx, ← HenkinModel.denote, firstHyp,
        ← HenkinModel.denote, secondHyp]
      exact addition_correct _ _

theorem constructor_result_denote {context : List Vectors.DataSort}
    (code : Code (Vectors.interface A) context) (environment : Env (Vectors.value A) context)
    (data : ConstructorData code) :
    (arithmetic.reading A).applyData model
      (arithmetic.encodeData A model encodeNatural encodeElement) (dataSorts code)
      (model.denote ((arithmetic.reading A).resultProgram code)
        ((arithmetic.reading A).valuation model
          (arithmetic.encodeData A model encodeNatural encodeElement)
          (emptyValuation model) environment)) data =
      encodeNatural (dataResultIndex code environment data) :=
  (arithmetic.reading A).resultProgram_denote model
    (arithmetic.encodeData A model encodeNatural encodeElement) encodeNatural
    (emptyValuation model)
    (arithmetic.term_denote A model encodeNatural encodeElement zero_correct successor_correct addition_correct)
    code environment data

theorem constructor_child_denote {context : List Vectors.DataSort}
    (code : Code (Vectors.interface A) context) (environment : Env (Vectors.value A) context)
    (data : ConstructorData code) (position : Fin (recursiveCount code)) :
    (arithmetic.reading A).applyData model
      (arithmetic.encodeData A model encodeNatural encodeElement) (dataSorts code)
      (model.denote ((arithmetic.reading A).childProgram code position)
        ((arithmetic.reading A).valuation model
          (arithmetic.encodeData A model encodeNatural encodeElement)
          (emptyValuation model) environment)) data =
      encodeNatural (dataRecursiveIndexAt code environment data position) :=
  (arithmetic.reading A).childProgram_denote model
    (arithmetic.encodeData A model encodeNatural encodeElement) encodeNatural
    (emptyValuation model)
    (arithmetic.term_denote A model encodeNatural encodeElement zero_correct successor_correct addition_correct)
    code environment data position

#print axioms term_denote
#print axioms constructor_result_denote
#print axioms constructor_child_denote

end Arithmetic
end Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms
