import Mettapedia.Logic.HOL.Semantics.PredicateEquality
import Mettapedia.Logic.HOL.Semantics.LogicalRelationModel
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLPredicateEqualitySignature
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLSignatureDenotation

/-!
# Meaning of the actual native predicate-equality lambda

The lambda, quantifier and implication interpreter evaluates the displayed
native equality term independently of the alternative signature's equality
clause. On admitted endpoints, its value agrees with intrinsic equality when
admitted functions respect that equality. Literal equality of the whole binary
function additionally uses coverage of its endpoint type. Full domains are a
sufficient instance of that coverage; no full predicate space is required by
the admitted-value comparison.

The lambda-closed monotone model separates term closure from the required
argument congruence. These results compare model values, not native identity
types or equality of retained proof presentations.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLPredicateEqualitySemantics
open Presentation FormationSensitiveHOLInterface NativeHOLSignatureDenotation
open Mettapedia.Logic
universe u v w
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

theorem sourceEquality_denote (model : HOL.HenkinModel.{u,v,w} Base Const)
    (type : HOL.Ty Base) (valuation : model.Valuation [])
    (left right : HOL.Ty.denote model.Carrier type) :
    (model.denote (HOLPredicateEqualitySignature.sourceEquality type) valuation left right).down ↔
      model.PredicateEquality type left right := Iff.rfl

theorem sourceEquality_agreement_iff (model : HOL.HenkinModel.{u,v,w} Base Const) :
    model.FunctionsRespectEqv ↔
      ∀ (type : HOL.Ty Base) (left right : HOL.Ty.denote model.Carrier type),
        model.adm type left → model.adm type right →
        ((model.denote (HOLPredicateEqualitySignature.sourceEquality type)
          (fun index => nomatch index) left right).down ↔ model.Eqv type left right) :=
  model.functionsRespectEqv_iff_predicateEquality

theorem equality_agreement (model : HOL.HenkinModel.{u,v,w} Base Const)
    (respects : model.FunctionsRespectEqv) (type : HOL.Ty Base) (valuation : model.Valuation [])
    (left right : HOL.Ty.denote model.Carrier type)
    (leftAdmitted : model.adm type left) (rightAdmitted : model.adm type right) :
    (model.denote (HOLPredicateEqualitySignature.sourceEquality type) valuation left right).down ↔
      model.Eqv type left right :=
  model.predicateEquality_iff_eqv respects leftAdmitted rightAdmitted

theorem equality_value (model : HOL.HenkinModel.{u,v,w} Base Const)
    (respects : model.FunctionsRespectEqv) (type : HOL.Ty Base)
    (covered : ∀ value, model.adm type value) (valuation : model.Valuation []) :
    model.denote (HOLPredicateEqualitySignature.sourceEquality type) valuation =
      fun left right => ULift.up (model.Eqv type left right) := by
  funext left right
  apply ULift.ext
  exact propext (equality_agreement model respects type valuation left right (covered left) (covered right))

/-- The derivation comes from interpreting the actual lambda expression in
the original signature; the alternative equality clause is not used. -/
theorem native_equality_value (source : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u,v,w} Base Const) (respects : model.FunctionsRespectEqv)
    (type : HOL.Ty Base) (covered : ∀ value, model.adm type value) :
    Denotes source model (gamma := []) (type := .arr type (.arr type .prop))
      (HOLPredicateEqualitySignature.equality source type)
      (fun _ left right => ULift.up (model.Eqv type left right)) := by
  have interpreted := representation_square (signature := source) (model := model)
    (HOLPredicateEqualitySignature.sourceEquality type)
    (HOLPredicateEqualitySignature.sourceEquality_represented source type)
  have meanings : (fun valuation : model.Valuation [] =>
      model.denote (HOLPredicateEqualitySignature.sourceEquality type) valuation) =
      fun _ left right => ULift.up (model.Eqv type left right) := by
    funext valuation
    exact equality_value model respects type covered valuation
  rw [meanings] at interpreted
  exact interpreted

theorem monotone_counterexample :
    let model := HOL.MonotoneBooleanModel.model
    let type := HOL.MonotoneBooleanModel.endomapObservation
    let left := HOL.MonotoneBooleanModel.atFalse
    let right := HOL.MonotoneBooleanModel.andEndpoints
    model.adm type left ∧ model.adm type right ∧ model.Eqv type left right ∧
      ¬ model.PredicateEquality type left right := by
  refine ⟨HOL.MonotoneBooleanModel.atFalse_admissible,
    HOL.MonotoneBooleanModel.andEndpoints_admissible,
    HOL.MonotoneBooleanModel.atFalse_eqv_andEndpoints, ?_⟩
  intro equal
  have impossible := equal HOL.MonotoneBooleanModel.observesNegation
    HOL.MonotoneBooleanModel.observesNegation_admissible (by rfl)
  change false = true at impossible
  cases impossible

theorem monotone_refutes_equality_agreement :
    ¬ (∀ (type : HOL.Ty Unit)
      (left right : HOL.Ty.denote HOL.MonotoneBooleanModel.model.Carrier type),
      HOL.MonotoneBooleanModel.model.adm type left →
      HOL.MonotoneBooleanModel.model.adm type right →
      (HOL.MonotoneBooleanModel.model.PredicateEquality type left right ↔
        HOL.MonotoneBooleanModel.model.Eqv type left right)) := by
  intro agreement
  exact HOL.MonotoneBooleanModel.not_functionsRespectEqv
    ((HOL.HenkinModel.functionsRespectEqv_iff_predicateEquality _).mpr agreement)

#print axioms native_equality_value
#print axioms sourceEquality_agreement_iff
#print axioms monotone_counterexample
#print axioms monotone_refutes_equality_agreement
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLPredicateEqualitySemantics
