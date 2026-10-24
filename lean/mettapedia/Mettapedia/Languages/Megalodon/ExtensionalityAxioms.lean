import Mettapedia.Languages.Megalodon.RelationEqualityExtensionality
import Mettapedia.Languages.Megalodon.RelationEqualityProofs
import Mettapedia.Languages.Megalodon.ImpredicativeLogicalProofs
import Mettapedia.Languages.Megalodon.HOLTermEncoding
import Mettapedia.Languages.Megalodon.HenkinNormalizationSemantics

/-!
# The extensionality axioms in the common Megalodon interpretation

The maintained Egal preamble declares `func_ext` and `prop_ext` separately
from its definition of equality. These formulas use that binary-relation
definition, with typed binders and the original implication directions.
Their interpretation exposes the admitted-value condition needed by a
forward extensional HOL proof translation. Neither axiom is a claim about
every type or proposition of an ambient host calculus.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.ExtensionalityAxioms

open Mettapedia.Logic.HOL
open HenkinEqualityInterpretation RelationEqualityExtensionality

universe u v w
variable {Base : Type u} {Const : Ty Base → Type v}

/-- The monomorphic instance of the maintained `func_ext` schema. -/
def functional (domain result : Ty Base) : ClosedFormula Const :=
  .all (.all (.imp
    (.all (equalityFormula
      (.app (.var (.vs (.vs .vz))) (.var .vz))
      (.app (.var (.vs .vz)) (.var .vz))))
    (equalityFormula (σ := domain ⇒ result) (.var (.vs .vz)) (.var .vz))))

/-- The maintained `prop_ext` axiom, before impredicative conjunction expansion. -/
def propositional : ClosedFormula Const :=
  .all (.all (.imp
    (.and (.imp (.var (.vs .vz)) (.var .vz))
      (.imp (.var .vz) (.var (.vs .vz))))
    (equalityFormula (σ := .prop) (.var (.vs .vz)) (.var .vz))))

/-- Interpreting every instance of the actual guest schema is exactly the
functional principle on admitted values. -/
theorem models_functional_iff (model : HenkinModel.{u, v, w} Base Const) :
    (∀ domain result, model.models (functional domain result)) ↔
      FunctionalExtensionality model := by
  constructor
  · intro valid domain result first second firstAdmitted secondAdmitted pointwise
    exact valid domain result first firstAdmitted second secondAdmitted pointwise
  · intro extensional domain result first firstAdmitted second secondAdmitted pointwise
    exact extensional domain result first second firstAdmitted secondAdmitted pointwise

/-- This Henkin proposition carrier already validates the guest's `prop_ext`.
This semantic fact does not manufacture a native proof of an undeclared axiom. -/
theorem models_propositional (model : HenkinModel.{u, v, w} Base Const) :
    model.models propositional := by
  intro first _ second _ equivalent
  exact (proposition_equality_iff model first second).mpr ⟨equivalent.1, equivalent.2⟩

theorem models_functional_iff_congruence (model : HenkinModel.{u, v, w} Base Const) :
    (∀ domain result, model.models (functional domain result)) ↔ model.FunctionsRespectEqv :=
  (models_functional_iff model).trans (functionalExtensionality_iff_functionsRespectEqv model)

namespace Native

open MathdataKernel

def functional (domain result : Tp) : Tm :=
  .all (.arr domain result) (.all (.arr domain result)
    (.imp (.all domain (RelationEqualityProofs.equality result
      (.app (.db 2) (.db 0)) (.app (.db 1) (.db 0))))
      (RelationEqualityProofs.equality (.arr domain result) (.db 1) (.db 0))))

def propositional : Tm :=
  .all .prop (.all .prop
    (.imp (ImpredicativeLogicalProofs.conjunction
      (.imp (.db 1) (.db 0)) (.imp (.db 0) (.db 1)))
      (RelationEqualityProofs.equality .prop (.db 1) (.db 0))))

set_option maxHeartbeats 1000000 in
/-- The native schema is the actual normalized erasure of its intrinsic
interpretation, including the preamble's binary equality expansion. -/
theorem functional_normalizes {environment : Environment}
    (domain result : Ty HenkinTermInterpretation.Base) :
    Tm.normalize 32 (HOLTermEncoding.native
      (ExtensionalityAxioms.functional (Const := HenkinTermInterpretation.Constant environment)
        domain result)) = some (functional
          (HenkinTermInterpretation.reifyType domain) (HenkinTermInterpretation.reifyType result)) := by
  simp [HOLTermEncoding.native, HOLTermEncoding.encode, HOLTermEncoding.expandEquality,
    ImpredicativeConnectives.expandInline, ExtensionalityAxioms.functional,
    HenkinEqualityInterpretation.equalityFormula, HenkinEqualityInterpretation.equality,
    HenkinTermInterpretation.erase, HenkinTermInterpretation.variableIndex,
    Tm.normalize, Tm.normalizeOne, Tm.instantiate, Tm.instantiateAt, Tm.shift,
    functional, RelationEqualityProofs.equality, RelationEqualityProofs.relationType,
    RelationEqualityProofs.relationApply, HenkinTermInterpretation.reifyType]

set_option maxHeartbeats 1000000 in
theorem propositional_normalizes {environment : Environment} :
    Tm.normalize 32 (HOLTermEncoding.native
      (ExtensionalityAxioms.propositional
        (Base := HenkinTermInterpretation.Base)
        (Const := HenkinTermInterpretation.Constant environment))) = some propositional := by
  simp [HOLTermEncoding.native, HOLTermEncoding.encode, HOLTermEncoding.expandEquality,
    ImpredicativeConnectives.expandInline, ImpredicativeConnectives.conjunctionFormula,
    ExtensionalityAxioms.propositional,
    HenkinEqualityInterpretation.equalityFormula, HenkinEqualityInterpretation.equality,
    HenkinTermInterpretation.erase, HenkinTermInterpretation.variableIndex,
    Tm.normalize, Tm.normalizeOne, Tm.instantiate, Tm.instantiateAt, Tm.shift,
    propositional, ImpredicativeLogicalProofs.conjunction,
    RelationEqualityProofs.equality, RelationEqualityProofs.relationType,
    RelationEqualityProofs.relationApply, HenkinTermInterpretation.reifyType,
    weaken, rename, Rename.weaken]

theorem functional_formed (environment : Environment) (depth : Nat)
    (domain result : Tp) (domainFormed : domain.plainWellFormed depth = true)
    (resultFormed : result.plainWellFormed depth = true) :
    inferTerm environment depth [] (functional domain result) = some .prop := by
  simp [functional, RelationEqualityProofs.equality, RelationEqualityProofs.relationType,
    RelationEqualityProofs.relationApply, inferTerm, Tm.shift,
    Tp.plainWellFormed, domainFormed, resultFormed]

theorem propositional_formed (environment : Environment) (depth : Nat) :
    inferTerm environment depth [] propositional = some .prop := by
  simp [propositional, ImpredicativeLogicalProofs.conjunction,
    RelationEqualityProofs.equality, RelationEqualityProofs.relationType,
    RelationEqualityProofs.relationApply, inferTerm, Tm.shift, Tp.plainWellFormed]

set_option maxHeartbeats 1000000 in
/-- The declared native functional axiom has an actual typed, valid reading
when the model satisfies extensional argument congruence. Full function
domains, choice and foundation are not hypotheses of this result. -/
theorem functional_valid {environment : Environment}
    (model : HenkinModel.{0, 0, w} HenkinTermInterpretation.Base
      (HenkinTermInterpretation.Constant environment))
    (respects : model.FunctionsRespectEqv)
    (domain result : Ty HenkinTermInterpretation.Base) :
    ∃ proposition : ClosedFormula (HenkinTermInterpretation.Constant environment),
      HenkinTermInterpretation.erase proposition = some
        (functional (HenkinTermInterpretation.reifyType domain)
          (HenkinTermInterpretation.reifyType result)) ∧ model.models proposition := by
  let formula := ExtensionalityAxioms.functional
    (Const := HenkinTermInterpretation.Constant environment) domain result
  obtain ⟨output, erased, meaning⟩ := HenkinTermInterpretation.betaEtaNormalize_interpretation
    (HOLTermEncoding.encode formula) (HOLTermEncoding.native_erased formula)
    (functional_normalizes domain result)
  refine ⟨output, erased, ?_⟩
  have originalValid := (models_functional_iff_congruence model).mpr respects domain result
  have encoded : HOLTermEncoding.encode formula = ImpredicativeConnectives.expandInline formula := rfl
  have agrees := (meaning model (fun index => nomatch index)).trans
    (encoded ▸ ImpredicativeConnectives.denote_expandInline model formula (fun index => nomatch index))
  have valid := (Iff.of_eq (congrArg ULift.down agrees)).mpr originalValid
  simp only [HenkinModel.models, PreModel.models]
  refine (Iff.of_eq ?_).mpr valid
  apply congrArg (fun valuation : model.Valuation [] => (model.denote output valuation).down)
  funext value index
  nomatch index

theorem propositional_valid {environment : Environment}
    (model : HenkinModel.{0, 0, w} HenkinTermInterpretation.Base
      (HenkinTermInterpretation.Constant environment)) :
    ∃ proposition : ClosedFormula (HenkinTermInterpretation.Constant environment),
      HenkinTermInterpretation.erase proposition = some propositional ∧ model.models proposition := by
  let formula := ExtensionalityAxioms.propositional
    (Base := HenkinTermInterpretation.Base) (Const := HenkinTermInterpretation.Constant environment)
  obtain ⟨output, erased, meaning⟩ := HenkinTermInterpretation.betaEtaNormalize_interpretation
    (HOLTermEncoding.encode formula) (HOLTermEncoding.native_erased formula) propositional_normalizes
  refine ⟨output, erased, ?_⟩
  have encoded : HOLTermEncoding.encode formula = ImpredicativeConnectives.expandInline formula := rfl
  have agrees := (meaning model (fun index => nomatch index)).trans
    (encoded ▸ ImpredicativeConnectives.denote_expandInline model formula (fun index => nomatch index))
  have valid := (Iff.of_eq (congrArg ULift.down agrees)).mpr (models_propositional model)
  simp only [HenkinModel.models, PreModel.models]
  refine (Iff.of_eq ?_).mpr valid
  apply congrArg (fun valuation : model.Valuation [] => (model.denote output valuation).down)
  funext value index
  nomatch index

/-- An axiom name has no authority when the environment does not declare it. -/
theorem undeclared_functional_refused (fuel depth : Nat) (terms : List Tp)
    (hypotheses : List Tm) :
    inferProof ({} : Environment) fuel depth terms hypotheses (.known "func_ext") = none := rfl

end Native

#print axioms models_functional_iff
#print axioms models_propositional
#print axioms models_functional_iff_congruence
#print axioms Native.undeclared_functional_refused
#print axioms Native.functional_normalizes
#print axioms Native.propositional_normalizes
#print axioms Native.functional_formed
#print axioms Native.propositional_formed
#print axioms Native.functional_valid
#print axioms Native.propositional_valid

end Mettapedia.Languages.Megalodon.ExtensionalityAxioms
