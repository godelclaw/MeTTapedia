import Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryEquationDerivations
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractSoundness

/-!
# Sound theory-equation extensions in arbitrary local predicate models

Admission checks the two independent evaluator outputs of each authored
equation at its context. It is a local model condition on that declaration,
not a whole-rule or whole-derivation interpretation premise. The extended
rule fold interprets every original native rule and every added occurrence.
Context, substitution, type, term and predicate carrier sizes are independent.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryEquations

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateModel

universe a c s t m p

variable {S : Symbols.{a}} {C : CwfWithTerminal.{c, s, t, m}}
  {localModel : LocalModel.{c, s, t, m, p} C} {D : Signature S}

namespace Declaration

/-- Independently computed values of one declared equation must agree.
Both side-formation trees remain premises of its generated rule. -/
def Admitted (model : Abstract.ModelData S C localModel) : Declaration S → Prop
  | .type context first second =>
      ∀ Γ, model.evaluateContext context = some Γ →
        model.evaluateType Γ first = model.evaluateType Γ second
  | .term context _ first second =>
      ∀ Γ, model.evaluateContext context = some Γ →
        model.evaluateTerm Γ first = model.evaluateTerm Γ second
  | .predicate context first second =>
      ∀ Γ, model.evaluateContext context = some Γ →
        model.evaluatePredicate Γ first = model.evaluatePredicate Γ second
  | .substitution source target first second =>
      ∀ Γ Δ, model.evaluateContext source = some Γ → model.evaluateContext target = some Δ →
        model.evaluateSubstitution Γ Δ first = model.evaluateSubstitution Γ Δ second

theorem sound (model : Abstract.ModelData S C localModel) (declaration : Declaration S)
    (admitted : declaration.Admitted model)
    (premises : (position : Fin declaration.premises.length) →
      Abstract.Interprets model (declaration.premises.get position)) :
    Abstract.Interprets model declaration.conclusion := by
  cases declaration with
  | type context first second =>
      rcases premises ⟨0, by simp [Declaration.premises]⟩ with ⟨Γ, A, contextRead, firstRead⟩
      exact ⟨Γ, A, contextRead, firstRead, (admitted Γ contextRead).symm.trans firstRead⟩
  | term context result first second =>
      rcases premises ⟨0, by simp [Declaration.premises]⟩ with ⟨Γ, A, value, contextRead, typeRead, firstRead⟩
      exact ⟨Γ, A, value, contextRead, typeRead, firstRead,
        (admitted Γ contextRead).symm.trans firstRead⟩
  | predicate context first second =>
      rcases premises ⟨0, by simp [Declaration.premises]⟩ with ⟨Γ, predicate, contextRead, firstRead⟩
      exact ⟨Γ, predicate, contextRead, firstRead, (admitted Γ contextRead).symm.trans firstRead⟩
  | substitution source target first second =>
      rcases premises ⟨0, by simp [Declaration.premises]⟩ with ⟨Γ, Δ, arrow, sourceRead, targetRead, firstRead⟩
      exact ⟨Γ, Δ, arrow, sourceRead, targetRead, firstRead,
        (admitted Γ Δ sourceRead targetRead).symm.trans firstRead⟩

end Declaration

def Admitted (model : Abstract.ModelData S C localModel) (equations : Presentation S) : Prop :=
  ∀ origin, (equations.declaration origin).Admitted model

/-- Each of the original local rules is interpreted from its supplied
premise values and the model's independently checked primitive headers. -/
def originalAlgebra (model : Abstract.ModelData S C localModel)
    (realization : Abstract.SignatureRealization model D)
    (qualified : Qualification localModel) : JudgmentDerivation.Algebra (judgmentSignature D) where
  Carrier judgment := PLift (Abstract.Interprets model judgment)
  conclude := by
    intro judgment rule premises
    rcases rule with ⟨rule, rfl⟩
    exact ⟨model.rule_sound realization qualified.stableProducts
      qualified.productBeta qualified.productEta rule (fun position => (premises ⟨position⟩).down)⟩

/-- Complete interpretation is constructed by the extended rule fold. -/
def equationAlgebra (model : Abstract.ModelData S C localModel)
    (realization : Abstract.SignatureRealization model D)
    (qualified : Qualification localModel) (equations : Presentation S)
    (admitted : Admitted model equations) :
    JudgmentDerivation.Algebra (equations.extension D).signature :=
  (equations.extension D).extendAlgebra (originalAlgebra model realization qualified) (by
    intro judgment rule premises
    rcases rule with ⟨origin, rfl⟩
    exact ⟨(equations.declaration origin).sound model (admitted origin)
      (fun position => (premises ⟨position⟩).down)⟩)

theorem sound (model : Abstract.ModelData S C localModel)
    (realization : Abstract.SignatureRealization model D)
    (qualified : Qualification localModel) {equations : Presentation S}
    (admitted : Admitted model equations) {judgment : Judgment S}
    (tree : Derivation D equations judgment) : Abstract.Interprets model judgment :=
  (JudgmentDerivation.interpret (equationAlgebra model realization qualified equations admitted) tree).down

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryEquations
