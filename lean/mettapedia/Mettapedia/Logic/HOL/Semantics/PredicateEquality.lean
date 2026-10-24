import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Predicate equality and extensional argument congruence

Quantifying over admitted unary predicates gives Leibniz equality on a Henkin
carrier. Lambda closure supplies the equality and image tests used below.
Agreement with intrinsic equality at every type is equivalent to the existing
condition that admitted functions respect equality of admitted arguments.
Full function spaces are a sufficient specialization, not a premise of the
characterization.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.HenkinModel
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v}

def PredicateEquality (model : HenkinModel.{u,v,w} Base Const) (type : Ty Base)
    (left right : Ty.denote model.Carrier type) : Prop :=
  ∀ predicate : Ty.denote model.Carrier (type ⇒ .prop),
    model.adm (type ⇒ .prop) predicate → (predicate left).down → (predicate right).down

theorem predicateEqualityTest_admissible (model : HenkinModel.{u,v,w} Base Const)
    {type : Ty Base} {left : Ty.denote model.Carrier type} (admitted : model.adm type left) :
    model.adm (type ⇒ .prop) (fun value => ULift.up (model.Eqv type left value)) := by
  let test : Term Const [type] (type ⇒ .prop) := .lam (.eq (.var (.vs .vz)) (.var .vz))
  let empty : model.Valuation [] := fun index => nomatch index
  let valuation : model.Valuation [type] := model.extend empty left
  have valuationAdmitted : model.ValuationAdmissible valuation := by
    apply model.extend_admissible
    · intro _ index; nomatch index
    · exact admitted
  exact model.term_closed test valuation valuationAdmitted

theorem eqv_of_predicateEquality (model : HenkinModel.{u,v,w} Base Const)
    {type : Ty Base} {left right : Ty.denote model.Carrier type}
    (admitted : model.adm type left) (equal : model.PredicateEquality type left right) :
    model.Eqv type left right :=
  equal _ (predicateEqualityTest_admissible model admitted) (model.eqv_refl admitted)

theorem predicateEquality_of_eqv (model : HenkinModel.{u,v,w} Base Const)
    (respects : model.FunctionsRespectEqv) {type : Ty Base} {left right : Ty.denote model.Carrier type}
    (leftAdmitted : model.adm type left) (rightAdmitted : model.adm type right)
    (equal : model.Eqv type left right) : model.PredicateEquality type left right := by
  intro predicate admitted holds
  exact (respects admitted leftAdmitted rightAdmitted equal).mp holds

theorem predicateImageTest_admissible (model : HenkinModel.{u,v,w} Base Const)
    {domain result : Ty Base} {function : Ty.denote model.Carrier (domain ⇒ result)}
    {left : Ty.denote model.Carrier domain}
    (functionAdmitted : model.adm (domain ⇒ result) function) (leftAdmitted : model.adm domain left) :
    model.adm (domain ⇒ .prop)
      (fun value => ULift.up (model.Eqv result (function left) (function value))) := by
  let test : Term Const [domain, domain ⇒ result] (domain ⇒ .prop) :=
    .lam (.eq (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
      (.app (.var (.vs (.vs .vz))) (.var .vz)))
  let empty : model.Valuation [] := fun index => nomatch index
  let valuation : model.Valuation [domain, domain ⇒ result] :=
    model.extend (model.extend empty function) left
  have valuationAdmitted : model.ValuationAdmissible valuation := by
    apply model.extend_admissible
    · apply model.extend_admissible
      · intro _ index; nomatch index
      · exact functionAdmitted
    · exact leftAdmitted
  exact model.term_closed test valuation valuationAdmitted

theorem functionsRespectEqv_iff_predicateEquality (model : HenkinModel.{u,v,w} Base Const) :
    model.FunctionsRespectEqv ↔ ∀ (type : Ty Base) (left right : Ty.denote model.Carrier type),
      model.adm type left → model.adm type right →
        (model.PredicateEquality type left right ↔ model.Eqv type left right) := by
  constructor
  · intro respects type left right leftAdmitted rightAdmitted
    exact ⟨eqv_of_predicateEquality model leftAdmitted,
      predicateEquality_of_eqv model respects leftAdmitted rightAdmitted⟩
  · intro agreement domain result function left right functionAdmitted leftAdmitted rightAdmitted equal
    have predicateEqual := (agreement domain left right leftAdmitted rightAdmitted).mpr equal
    exact predicateEqual _ (predicateImageTest_admissible model functionAdmitted leftAdmitted)
      (model.eqv_refl (model.app_mem functionAdmitted leftAdmitted))

theorem predicateEquality_iff_eqv (model : HenkinModel.{u,v,w} Base Const)
    (respects : model.FunctionsRespectEqv) {type : Ty Base}
    {left right : Ty.denote model.Carrier type}
    (leftAdmitted : model.adm type left) (rightAdmitted : model.adm type right) :
    model.PredicateEquality type left right ↔ model.Eqv type left right :=
  (functionsRespectEqv_iff_predicateEquality model).mp respects type left right
    leftAdmitted rightAdmitted

theorem predicateEquality_iff_eqv_of_fullDomains (model : HenkinModel.{u,v,w} Base Const)
    (full : model.FullDomains) (type : Ty Base) (left right : Ty.denote model.Carrier type) :
    model.PredicateEquality type left right ↔ model.Eqv type left right :=
  predicateEquality_iff_eqv model (model.functionsRespectEqv_of_fullDomains full)
    (full type left) (full type right)

#print axioms functionsRespectEqv_iff_predicateEquality
#print axioms predicateEquality_iff_eqv
end Mettapedia.Logic.HOL.HenkinModel
