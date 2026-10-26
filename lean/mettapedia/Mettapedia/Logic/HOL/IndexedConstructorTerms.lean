import Mettapedia.TypeTheory.IndexedPolynomialConstructorData
import Mettapedia.Logic.HOL.Soundness

/-!
# Typed HOL programs for constructor-telescope indices

A reading of the declared index expressions generates curried HOL programs
for each constructor's result index and every recursive child's index. Data
binders follow the source telescope; recursive fields do not enter the index
environment. Unused later data fields are abstracted explicitly.

The denotation theorems derive agreement with the independent constructor-data
evaluation from agreement of the index-expression reading. Source constant
admission and its interpretation are separate consumers of these terms.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.IndexedConstructorTerms

open Mettapedia.TypeTheory.IndexedPolynomial.Description
universe u v w x
variable {I : Interface.{u}} {Base : Type v} {Const : Ty Base → Type w}

structure Reading (I : Interface.{u}) (Const : Ty Base → Type w) where
  sort : I.SortCode → Ty Base
  index : Ty Base
  parameters : Ctx Base
  term : {context : List I.SortCode} → I.IndexExpr context →
    Term Const (context.map sort ++ parameters) index

namespace Reading
variable (reading : Reading I Const)

abbrev ResultType (sorts : List I.SortCode) : Ty Base :=
  (sorts.map reading.sort).foldr Ty.arr reading.index

def constantProgram {Γ : Ctx Base} : (sorts : List I.SortCode) →
    Term Const Γ reading.index → Term Const Γ (reading.ResultType sorts)
  | [], value => value
  | _ :: rest, value => .lam (constantProgram rest (weaken value))

def resultProgram : {context : List I.SortCode} → (code : Code I context) →
    Term Const (context.map reading.sort ++ reading.parameters) (reading.ResultType (dataSorts code))
  | _, .result expression => reading.term expression
  | _, .data _ body => .lam (resultProgram body)
  | _, .recursive _ rest => resultProgram rest

def childProgram : {context : List I.SortCode} → (code : Code I context) →
    Fin (recursiveCount code) →
      Term Const (context.map reading.sort ++ reading.parameters) (reading.ResultType (dataSorts code))
  | _, .result _, position => Fin.elim0 position
  | _, .data _ body, position => .lam (childProgram body position)
  | _, .recursive expression rest, position =>
      Fin.cases (reading.constantProgram (dataSorts rest) (reading.term expression))
        (childProgram rest) position

variable (model : HenkinModel.{v,w,x} Base Const)
  (encodeValue : ∀ sort, I.Value sort → Ty.denote model.Carrier (reading.sort sort))

def valuation (parameters : model.Valuation reading.parameters) :
    {context : List I.SortCode} → Env I.Value context →
      model.Valuation (context.map reading.sort ++ reading.parameters)
  | [], _ => parameters
  | sort :: _, environment => model.extend (valuation parameters environment.2)
      (encodeValue sort environment.1)

def applyData : (sorts : List I.SortCode) →
    Ty.denote model.Carrier (reading.ResultType sorts) → Env I.Value sorts →
      Ty.denote model.Carrier reading.index
  | [], value, _ => value
  | sort :: rest, function, data => applyData rest (function (encodeValue sort data.1)) data.2

theorem constantProgram_denote {Γ : Ctx Base} (sorts : List I.SortCode)
    (value : Term Const Γ reading.index) (values : model.Valuation Γ)
    (data : Env I.Value sorts) :
    reading.applyData model encodeValue sorts
      (model.denote (reading.constantProgram sorts value) values) data = model.denote value values := by
  induction sorts generalizing Γ with
  | nil => rfl
  | cons sort rest hypotheses =>
    change reading.applyData model encodeValue rest
      (model.denote (reading.constantProgram rest (weaken value))
        (model.extend values (encodeValue sort data.1))) data.2 = _
    rw [hypotheses, Soundness.denote_weaken]

variable (encodeIndex : I.Index → Ty.denote model.Carrier reading.index)
  (parameters : model.Valuation reading.parameters)
  (index_correct : ∀ {context} (expression : I.IndexExpr context) (environment : Env I.Value context),
    model.denote (reading.term expression) (reading.valuation model encodeValue parameters environment) =
      encodeIndex (I.evalIndex expression environment))

include index_correct

theorem resultProgram_denote {context : List I.SortCode} (code : Code I context)
    (environment : Env I.Value context) (data : ConstructorData code) :
    reading.applyData model encodeValue (dataSorts code)
      (model.denote (reading.resultProgram code)
        (reading.valuation model encodeValue parameters environment)) data =
      encodeIndex (dataResultIndex code environment data) := by
  induction code with
  | result expression => exact index_correct expression environment
  | data sort body hypotheses => exact hypotheses (data.1, environment) data.2
  | recursive expression rest hypotheses => exact hypotheses environment data

theorem childProgram_denote {context : List I.SortCode} (code : Code I context)
    (environment : Env I.Value context) (data : ConstructorData code)
    (position : Fin (recursiveCount code)) :
    reading.applyData model encodeValue (dataSorts code)
      (model.denote (reading.childProgram code position)
        (reading.valuation model encodeValue parameters environment)) data =
      encodeIndex (dataRecursiveIndexAt code environment data position) := by
  induction code with
  | result expression => exact Fin.elim0 position
  | data sort body hypotheses => exact hypotheses (data.1, environment) data.2 position
  | recursive expression rest hypotheses =>
    refine Fin.cases ?_ (fun prior => ?_) position
    · change reading.applyData model encodeValue (dataSorts rest)
        (model.denote (reading.constantProgram (dataSorts rest) (reading.term expression))
          (reading.valuation model encodeValue parameters environment)) data = _
      exact (constantProgram_denote reading model encodeValue (dataSorts rest)
        (reading.term expression) (reading.valuation model encodeValue parameters environment) data).trans
          (index_correct expression environment)
    · exact hypotheses environment data prior

#print axioms resultProgram_denote
#print axioms childProgram_denote

end Reading
end Mettapedia.Logic.HOL.IndexedConstructorTerms
