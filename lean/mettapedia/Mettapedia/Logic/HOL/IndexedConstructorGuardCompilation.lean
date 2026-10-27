import Mettapedia.Logic.HOL.IndexedConstructorGuards
import Mettapedia.Logic.HOL.IndexedConstructorTerms

/-!
# Guard inventories compiled from constructor descriptions

The original first-order telescope determines the field types, child count,
result program and every ordered child-index program. Only the reading of
index expressions, numerical literals and field-validity predicates are
supplied by the target interpretation. Result and child denotations reuse the
existing source evaluator agreement.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuardCompilation

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open FiniteConstructorEncoding CurriedPredicates
universe u v w x
variable {I : Interface.{u}} {Base : Type v} {Const : Ty Base → Type w}
variable {context : List I.SortCode}
variable (reading : IndexedConstructorTerms.Reading I Const)
  (constructors : List (NamedConstructor I context))

def fields : List (List (Ty Base)) :=
  constructors.map (fun constructor => (dataSorts constructor.body).map reading.sort)

def sourceOccurrence (occurrence : Fin (fields reading constructors).length) : Fin constructors.length :=
  ⟨occurrence.val, by simpa only [fields, List.length_map] using occurrence.isLt⟩

def codeAt (occurrence : Fin (fields reading constructors).length) : Code I context :=
  (constructors.get (sourceOccurrence reading constructors occurrence)).body

theorem fields_at (occurrence : Fin (fields reading constructors).length) :
    (fields reading constructors).get occurrence = (dataSorts (codeAt reading constructors occurrence)).map reading.sort := by
  exact List.getElem_map (fun constructor : NamedConstructor I context =>
    (dataSorts constructor.body).map reading.sort)

def result (occurrence : Fin (fields reading constructors).length) :
    Term Const (context.map reading.sort ++ reading.parameters)
      (FunctionType ((fields reading constructors).get occurrence) reading.index) :=
  (fields_at reading constructors occurrence).symm ▸ reading.resultProgram (codeAt reading constructors occurrence)

def childCount (occurrence : Fin (fields reading constructors).length) :=
  recursiveCount (codeAt reading constructors occurrence)

def child (occurrence : Fin (fields reading constructors).length)
    (position : Fin (childCount reading constructors occurrence)) :
    Term Const (context.map reading.sort ++ reading.parameters)
      (FunctionType ((fields reading constructors).get occurrence) reading.index) :=
  (fields_at reading constructors occurrence).symm ▸
    reading.childProgram (codeAt reading constructors occurrence) position

def inventory (number : Ty Base)
    (numeral : Nat → Term Const (context.map reading.sort ++ reading.parameters) number)
    (allowed : ConstructorDataPredicates.Conditions Const
      (context.map reading.sort ++ reading.parameters) (fields reading constructors)) :
    IndexedConstructorGuards.Inventory Const (context.map reading.sort ++ reading.parameters) where
  fields := fields reading constructors
  number := number
  index := reading.index
  numeral := numeral
  allowed := allowed
  result := result reading constructors
  childCount := childCount reading constructors
  child := child reading constructors

variable (model : HenkinModel.{v,w,x} Base Const)
  (encodeValue : ∀ sort, I.Value sort → Ty.denote model.Carrier (reading.sort sort))

def encodeData : (sorts : List I.SortCode) → Env I.Value sorts →
    Env (Ty.denote model.Carrier) (sorts.map reading.sort)
  | [], _ => PUnit.unit
  | sort :: rest, data => (encodeValue sort data.1, encodeData rest data.2)

theorem applyValues_encodeData (sorts : List I.SortCode)
    (function : Ty.denote model.Carrier (reading.ResultType sorts)) (data : Env I.Value sorts) :
    applyValues model (sorts.map reading.sort) function (encodeData reading model encodeValue sorts data) =
      reading.applyData model encodeValue sorts function data := by
  induction sorts with
  | nil => rfl
  | cons sort rest hypotheses => exact hypotheses (function (encodeValue sort data.1)) data.2

def nativeData (occurrence : Fin (fields reading constructors).length)
    (data : ConstructorData (codeAt reading constructors occurrence)) :
    Env (Ty.denote model.Carrier) ((fields reading constructors).get occurrence) :=
  (fields_at reading constructors occurrence).symm ▸
    encodeData reading model encodeValue _ data

theorem apply_cast {Γ : Ctx Base} {target : Ty Base} {first second : List (Ty Base)}
    (same : first = second) (program : Term Const Γ (FunctionType first target))
    (values : model.Valuation Γ) (data : Env (Ty.denote model.Carrier) first) :
    applyValues model second (model.denote (same ▸ program) values) (same ▸ data) =
      applyValues model first (model.denote program values) data := by
  cases same
  rfl

variable (encodeIndex : I.Index → Ty.denote model.Carrier reading.index)
  (parameters : model.Valuation reading.parameters)
  (index_correct : ∀ {context} (expression : I.IndexExpr context) (environment : Env I.Value context),
    model.denote (reading.term expression) (reading.valuation model encodeValue parameters environment) =
      encodeIndex (I.evalIndex expression environment))

include index_correct

theorem result_denote (occurrence : Fin (fields reading constructors).length)
    (environment : Env I.Value context) (data : ConstructorData (codeAt reading constructors occurrence)) :
    applyValues model _
      (model.denote (result reading constructors occurrence)
        (reading.valuation model encodeValue parameters environment))
      (nativeData reading constructors model encodeValue occurrence data) =
        encodeIndex (dataResultIndex (codeAt reading constructors occurrence) environment data) := by
  unfold result nativeData
  rw [apply_cast, applyValues_encodeData]
  exact reading.resultProgram_denote model encodeValue encodeIndex parameters index_correct _ environment data

theorem child_denote (occurrence : Fin (fields reading constructors).length)
    (position : Fin (childCount reading constructors occurrence))
    (environment : Env I.Value context) (data : ConstructorData (codeAt reading constructors occurrence)) :
    applyValues model _
      (model.denote (child reading constructors occurrence position)
        (reading.valuation model encodeValue parameters environment))
      (nativeData reading constructors model encodeValue occurrence data) =
        encodeIndex (dataRecursiveIndexAt (codeAt reading constructors occurrence) environment data position) := by
  unfold child nativeData
  rw [apply_cast, applyValues_encodeData]
  exact reading.childProgram_denote model encodeValue encodeIndex parameters index_correct _ environment data position

#print axioms fields_at
#print axioms result_denote
#print axioms child_denote

end Mettapedia.Logic.HOL.IndexedConstructorGuardCompilation
