import Mettapedia.Logic.HOL.ConstructorPositionEdges

/-!
# Position programs for a length-indexed Vector container

The constructor carries a length field. Its position graph tests the queried
slot against that field and retains the outer family's unit index as the
Boolean true value. The outer family is unindexed; the recursive position
fibre varies with the length. The comparison operation is an explicit typed
input whose interpretation is checked separately.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.VectorContainerPositionPrograms
open FiniteConstructorEncoding CurriedPredicates IndexedConstructorGuards
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}

def constructors (number : Ty Base) (numeral : Nat → Term Const Γ number) :
    ConstructorPrograms Const Γ where
  fields := [[number]]
  number := number
  index := .prop
  numeral := numeral
  allowed := fun occurrence => Fin.cases (.lam .top) (fun impossible => Fin.elim0 impossible) occurrence
  result := fun occurrence => Fin.cases (.lam .top) (fun impossible => Fin.elim0 impossible) occurrence

def graph {number : Ty Base} (less : Term Const Γ (number ⇒ number ⇒ .prop)) :
    Term Const Γ (number ⇒ .prop ⇒ number ⇒ .prop) :=
  .lam (.lam (.lam (.and
    (.app (.app (HOL.subst ConstructorPrograms.beneathThree less) (.var (.vs (.vs .vz)))) (.var .vz))
    (.eq (.var (.vs .vz)) .top))))

def positions (number : Ty Base) (numeral : Nat → Term Const Γ number)
    (less : Term Const Γ (number ⇒ number ⇒ .prop)) : PositionPrograms (constructors number numeral) where
  graph := fun occurrence => Fin.cases (graph less) (fun impossible => Fin.elim0 impossible) occurrence

variable (model : HenkinModel.{u,v,w} Base Const) (full : model.FullDomains)
include full

theorem graph_denote {number : Ty Base} (less : Term Const Γ (number ⇒ number ⇒ .prop))
    (values : model.Valuation Γ) (slot length : Ty.denote model.Carrier number)
    (index : Ty.denote model.Carrier .prop) :
    (model.denote (graph less) values slot index length).down ↔
      (model.denote less values slot length).down ∧ index = ULift.up True := by
  change (model.denote (HOL.subst ConstructorPrograms.beneathThree less)
    (model.extend (model.extend (model.extend values slot) index) length) slot length).down ∧
    model.Eqv .prop index (ULift.up True) ↔ _
  rw [Soundness.denote_subst]
  apply and_congr Iff.rfl (model.eqv_iff_eq_of_fullDomains full _ _)

theorem related_iff (number : Ty Base) (numeral : Nat → Term Const Γ number)
    (less : Term Const Γ (number ⇒ number ⇒ .prop)) (values : model.Valuation Γ)
    (length slot : Ty.denote model.Carrier number) (index : Ty.denote model.Carrier .prop) :
    (positions number numeral less).related model values
      ⟨⟨0, by change 0 < 1; decide⟩, length, PUnit.unit⟩ slot index ↔
      (model.denote less values slot length).down ∧ index = ULift.up True := by
  change (model.denote (graph less) values slot index length).down ↔ _
  exact graph_denote model full less values slot length index

#print axioms graph_denote
#print axioms related_iff
end Mettapedia.Logic.HOL.VectorContainerPositionPrograms
