import Mettapedia.Languages.Megalodon.HenkinEqualityInterpretation
import Mettapedia.Logic.HOL.Embedding.HypersetHenkinInterpretation
import Mettapedia.Logic.HOL.Embedding.CodedHypersetInterpretation

/-!
# Functional extensionality for Megalodon's defined equality

Over the existing Henkin-model interface, functional extensionality for
binary-relation equality is equivalent to extensional argument congruence.
The model's proposition carrier already validates propositional extensionality;
this fact belongs to that semantic interface, not to the native proof syntax.

The full set and hyperset interpretations satisfy the functional principle.
The existing lambda-closed monotone-Boolean model refutes it. The comparison
concerns the interpreted HOL fragment and selects no whole Prime calculus.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.RelationEqualityExtensionality

open Mettapedia.Logic.HOL
open HenkinEqualityInterpretation

universe u v w
variable {Base : Type u} {Const : Ty Base → Type v}

/-- Functional extensionality for the actual defined relation, restricted to
the model's admitted functions and arguments. -/
def FunctionalExtensionality (model : HenkinModel.{u, v, w} Base Const) : Prop :=
  ∀ (domain result : Ty Base) (first second : Ty.denote model.Carrier (domain ⇒ result)),
    model.adm (domain ⇒ result) first → model.adm (domain ⇒ result) second →
    (∀ argument, model.adm domain argument →
      RelationEquality model result (first argument) (second argument)) →
    RelationEquality model (domain ⇒ result) first second

theorem proposition_equality_iff (model : HenkinModel.{u, v, w} Base Const)
    (first second : Ty.denote model.Carrier .prop) :
    RelationEquality model .prop first second ↔ (first.down ↔ second.down) := by
  constructor
  · exact eqv_of_relationEquality model (model.prop_mem first)
  · intro equivalent
    have same : first = second := by
      apply ULift.ext
      exact propext equivalent
    subst second
    intro relation _ holds
    exact holds

theorem equality_agreement_of_functionalExtensionality
    (model : HenkinModel.{u, v, w} Base Const) (extensional : FunctionalExtensionality model) :
    ∀ (type : Ty Base) (first second : Ty.denote model.Carrier type),
      model.adm type first → model.adm type second →
      model.Eqv type first second → RelationEquality model type first second := by
  intro type
  induction type with
  | prop =>
      intro first second _ _ equivalent
      exact (proposition_equality_iff model first second).mpr equivalent
  | base index =>
      intro first second _ _ equivalent
      change first = second at equivalent
      subst second
      intro relation _ holds
      exact holds
  | arr domain result _domainInduction resultInduction =>
      intro first second firstAdmitted secondAdmitted equivalent
      apply extensional domain result first second firstAdmitted secondAdmitted
      intro argument admitted
      exact resultInduction _ _ (model.app_mem firstAdmitted admitted)
        (model.app_mem secondAdmitted admitted) (equivalent argument admitted)

theorem functionalExtensionality_iff_functionsRespectEqv
    (model : HenkinModel.{u, v, w} Base Const) :
    FunctionalExtensionality model ↔ model.FunctionsRespectEqv := by
  constructor
  · intro extensional
    apply (functionsRespectEqv_iff_equality_agreement model).mpr
    intro type first second firstAdmitted secondAdmitted
    exact ⟨eqv_of_relationEquality model firstAdmitted,
      equality_agreement_of_functionalExtensionality model extensional type first second
        firstAdmitted secondAdmitted⟩
  · intro respects domain result first second firstAdmitted secondAdmitted pointwise
    apply relationEquality_of_eqv model respects firstAdmitted secondAdmitted
    intro argument admitted
    exact eqv_of_relationEquality model (model.app_mem firstAdmitted admitted)
      (pointwise argument admitted)

theorem fullDomains_functionalExtensionality (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) : FunctionalExtensionality model :=
  (functionalExtensionality_iff_functionsRespectEqv model).mpr
    (model.functionsRespectEqv_of_fullDomains full)

theorem monotoneBoolean_refutes_functionalExtensionality :
    ¬ FunctionalExtensionality MonotoneBooleanModel.model := by
  intro extensional
  exact MonotoneBooleanModel.not_functionsRespectEqv
    ((functionalExtensionality_iff_functionsRespectEqv _).mp extensional)

theorem sets_functionalExtensionality :
    FunctionalExtensionality Embedding.ZFSetHenkinInterpretation.model.{w} :=
  fullDomains_functionalExtensionality _ Embedding.ZFSetHenkinInterpretation.fullDomains

theorem hypersets_functionalExtensionality
    (presentation : Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.Presentation.{w}) :
    FunctionalExtensionality (Embedding.HypersetHenkinInterpretation.model presentation) :=
  fullDomains_functionalExtensionality _ (Embedding.HypersetHenkinInterpretation.fullDomains presentation)

theorem codes_functionalExtensionality
    (presentation : Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.Presentation.{w}) :
    FunctionalExtensionality (Embedding.CodedHypersetInterpretation.model presentation) :=
  fullDomains_functionalExtensionality _ (Embedding.CodedHypersetInterpretation.fullDomains presentation)

end Mettapedia.Languages.Megalodon.RelationEqualityExtensionality
