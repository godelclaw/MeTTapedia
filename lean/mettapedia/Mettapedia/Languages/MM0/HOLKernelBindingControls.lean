import Mettapedia.Languages.MM0.HOLKernelBindingProofs
import Mettapedia.Languages.MM0.HOLKernelTypingProofs
import Mettapedia.Languages.MM0.HOLKernelQuantifierProofs
import Mettapedia.Languages.MM0.HOLKernelInferenceProofs

/-!
# Distinct dependency policies of maintained HOL binder rules

A beta proof is constructed under a logical context containing its bound
variable. Generalization at that same context is refused. The application
typing proof is assembled from identity abstraction, context weakening and
variable typing, with no external logical hypotheses. Two-name abstraction
renaming also refuses identification of its bound images.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelBindingControls

open Kernel HOLKernelSyntax HOLKernelJudgment
open HOLKernelTypingRules (typed boolType functionType)
open HOLKernelInferenceRules (equality)
open HOLKernelStructuralRules (CheckedProof)

def baseAntecedent (references : Symbol → Nat) : Preterm :=
  holds references (applySymbol references .truth [])

def dependentAntecedent (references : Symbol → Nat) : Preterm :=
  conjunction references (baseAntecedent references) (hasType references (.var 0) (boolType references))

def identity (references : Symbol → Nat) : Preterm :=
  applySymbol references .lam [.var 0, boolType references, .var 0]

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {equivalenceReference : Nat}

theorem dependentAntecedent_occurs (references : Symbol → Nat) (sort : Nat) :
    Preterm.HasVar [.bound sort] 0 (dependentAntecedent references) :=
  .argument (.function (.argument (.bound rfl)))

def betaInDependentContext (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := [.bound signature.ids.object]) (hypotheses := [])
      (entails signature.symbol (dependentAntecedent signature.symbol)
        (holds signature.symbol (equality signature.symbol (boolType signature.symbol)
          (applySymbol signature.symbol .app [identity signature.symbol, .var 0]) (.var 0)))) := by
  let context : Context := [.bound signature.ids.object]
  let bool := boolType signature.symbol
  let base := baseAntecedent signature.symbol
  let variableType := hasType signature.symbol (.var 0) bool
  let extended := dependentAntecedent signature.symbol
  have boolSorted : Preterm.HasType terms context bool [] signature.ids.type :=
    signature.application context .bool [] .nil
  have variableSorted : Preterm.HasType terms context (.var 0) [] signature.ids.object :=
    Preterm.HasType.var (binder := .bound signature.ids.object) rfl
  have baseSorted : Preterm.HasType terms context base [] signature.ids.wff :=
    holds_sorted signature context (signature.application context .truth [] .nil)
  have variableTypeSorted := hasType_sorted signature context variableSorted boolSorted
  have extendedSorted := conjunction_sorted signature context baseSorted variableTypeSorted
  have variableTyping := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := [])
    signature structural base variableType baseSorted variableTypeSorted
  have baseIndependent : ¬ Preterm.HasVar context 0 base := by
    simp [base, baseAntecedent, holds, applySymbol, Preterm.applyArgs, Preterm.hasVar_app_iff]
  have boolIndependent : ¬ Preterm.HasVar context 0 bool := by
    simp [bool, boolType, applySymbol, Preterm.applyArgs]
  let identityTyping := HOLKernelTypingProofs.abstractionTyping signature typing base bool bool (.var 0) 0
    baseSorted boolSorted boolSorted rfl variableSorted baseIndependent boolIndependent boolIndependent variableTyping
  have identitySorted : Preterm.HasType terms context (identity signature.symbol) [] signature.ids.object :=
    signature.application context .lam _
      (.cons (.bound rfl) (.cons (.regular boolSorted) (.cons (.regular variableSorted) .nil)))
  have functionSorted := signature.application context .function _
    (.cons (.regular boolSorted) (.cons (.regular boolSorted) .nil))
  let weakenedIdentity := HOLKernelStructuralRules.weaken signature structural base variableType
    (hasType signature.symbol (identity signature.symbol) (functionType signature.symbol bool bool))
    baseSorted variableTypeSorted (hasType_sorted signature context identitySorted functionSorted) identityTyping
  let applicationTyping := HOLKernelTypingProofs.applicationTyping signature typing extended bool bool
    (identity signature.symbol) (.var 0) extendedSorted boolSorted boolSorted identitySorted variableSorted
    weakenedIdentity variableTyping
  exact HOLKernelBindingProofs.Native.variableBeta signature binding bool bool 0 extended (.var 0)
    boolSorted boolSorted rfl extendedSorted variableSorted boolIndependent boolIndependent applicationTyping

theorem generalization_refused_in_dependent_context (signature : Signature sorts terms)
    (formula : Preterm) :
    (HOLKernelBindingRules.Rule.declaration signature.symbol signature.ids equivalenceReference
      .universalIntroduction).instantiate? terms [.bound signature.ids.object]
      [dependentAntecedent signature.symbol, boolType signature.symbol, .var 0, formula] = none := by
  apply (TheoremDecl.instantiate_none_iff _ _ _ _).mpr
  rintro ⟨instantiation, admitted⟩
  exact admitted.admissible.single_bound_after_two_independence.1
    (dependentAntecedent_occurs signature.symbol signature.ids.object)

theorem abstraction_renaming_refuses_bound_collapse (signature : Signature sorts terms)
    (domain result antecedent first second : Preterm) :
    (HOLKernelBindingRules.Rule.declaration signature.symbol signature.ids equivalenceReference
      .abstractionRenaming).instantiate? terms [.bound signature.ids.object]
      [domain, result, antecedent, .var 0, .var 0, first, second] = none := by
  apply (TheoremDecl.instantiate_none_iff _ _ _ _).mpr
  rintro ⟨instantiation, admitted⟩
  exact admitted.admissible.bound_images_distinct
    (firstPosition := 3) (secondPosition := 4) rfl rfl (by decide) rfl rfl rfl rfl

def truthQuantifierProofs (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (inference : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := [.bound signature.ids.object]) (hypotheses := [])
      (entails signature.symbol (baseAntecedent signature.symbol)
        (holds signature.symbol (applySymbol signature.symbol .truth []))) ×
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := [.bound signature.ids.object]) (hypotheses := [])
      (entails signature.symbol (baseAntecedent signature.symbol)
        (holds signature.symbol (applySymbol signature.symbol .exc
          [.var 0, boolType signature.symbol, applySymbol signature.symbol .truth []]))) := by
  let context : Context := [.bound signature.ids.object]
  let bool := boolType signature.symbol
  let truth := applySymbol signature.symbol .truth []
  let base := baseAntecedent signature.symbol
  let extended := dependentAntecedent signature.symbol
  have boolSorted : Preterm.HasType terms context bool [] signature.ids.type :=
    signature.application context .bool [] .nil
  have truthSorted : Preterm.HasType terms context truth [] signature.ids.object :=
    signature.application context .truth [] .nil
  have variableSorted : Preterm.HasType terms context (.var 0) [] signature.ids.object :=
    Preterm.HasType.var (binder := .bound signature.ids.object) rfl
  have baseSorted := holds_sorted signature context truthSorted
  have extendedSorted := conjunction_sorted signature context baseSorted
    (hasType_sorted signature context variableSorted boolSorted)
  have baseIndependent : ¬ Preterm.HasVar context 0 base := by
    simp [base, baseAntecedent, holds, applySymbol, Preterm.applyArgs, Preterm.hasVar_app_iff]
  have boolIndependent : ¬ Preterm.HasVar context 0 bool := by
    simp [bool, boolType, applySymbol, Preterm.applyArgs]
  let truthTyping := HOLKernelTypingProofs.truthTyping (definitions := definitions) (hypotheses := [])
    signature typing base baseSorted
  let bodyTyping := HOLKernelTypingProofs.truthTyping (definitions := definitions) (hypotheses := [])
    signature typing extended extendedSorted
  let bodyTrue := HOLKernelInferenceProofs.Native.truth (definitions := definitions) (hypotheses := [])
    signature inference extended extendedSorted
  let instanceTrue := HOLKernelInferenceProofs.Native.truth (definitions := definitions) (hypotheses := [])
    signature inference base baseSorted
  let universal := HOLKernelBindingProofs.Native.universalIntroduction signature binding base bool 0 truth
    baseSorted boolSorted rfl truthSorted baseIndependent boolIndependent bodyTrue
  let equalityContext := conjunction signature.symbol base
    (holds signature.symbol (equality signature.symbol bool (.var 0) truth))
  have equalityContextSorted := conjunction_sorted signature context baseSorted
    (holds_sorted signature context (signature.application context .eqc _
      (.cons (.regular boolSorted) (.cons (.regular variableSorted) (.cons (.regular truthSorted) .nil)))))
  let resultTyping := HOLKernelTypingProofs.truthTyping (definitions := definitions) (hypotheses := [])
    signature typing equalityContext equalityContextSorted
  let substitutionEquation := HOLKernelInferenceProofs.Native.reflexivity signature inference
    equalityContext bool truth equalityContextSorted boolSorted truthSorted resultTyping
  exact ⟨HOLKernelQuantifierProofs.universalElimination signature abbreviation binding base bool truth truth truth 0
      baseSorted boolSorted rfl truthSorted truthSorted truthSorted baseIndependent boolIndependent
      truthTyping truthTyping substitutionEquation universal,
    HOLKernelQuantifierProofs.existentialIntroduction signature abbreviation binding base bool truth truth truth 0
      baseSorted boolSorted rfl truthSorted truthSorted truthSorted baseIndependent boolIndependent
      bodyTyping truthTyping substitutionEquation instanceTrue⟩

#print axioms dependentAntecedent_occurs
#print axioms betaInDependentContext
#print axioms generalization_refused_in_dependent_context
#print axioms abstraction_renaming_refuses_bound_collapse
#print axioms truthQuantifierProofs

end Mettapedia.Languages.MM0.HOLKernelBindingControls
