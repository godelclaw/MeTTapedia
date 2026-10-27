import Mettapedia.Logic.HOL.PredicateFixedPoint
import Mettapedia.Logic.HOL.Soundness

/-!
# Interpretation of the least-predicate program

The object-language least predicate quantifies over admissible predicates and
tests closure at admissible values. The law retains those domain conditions;
full-domain clients can discharge them with their model's established theorem.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.PredicateFixedPoint
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {α : Ty Base}

theorem least_denote (model : HenkinModel.{u,v,w} Base Const)
    (operator : Term Const Γ (Operator α)) (values : model.Valuation Γ)
    (point : Ty.denote model.Carrier α) :
    (model.denote (least operator) values point).down ↔
      ∀ predicate : Ty.denote model.Carrier (Predicate α), model.adm _ predicate →
        (∀ value, model.adm α value → (model.denote operator values predicate value).down → (predicate value).down) →
        (predicate point).down := by
  simp only [least, leastBody, prefixed, included, weaken, rename,
    HenkinModel.denote, PreModel.denote, PreModel.extend]
  simp only [Soundness.denote_rename, Rename.weaken]
  rfl

#print axioms least_denote
end Mettapedia.Logic.HOL.PredicateFixedPoint
