import Mettapedia.Languages.MM0.HOLKernelInferenceProofs

/-!
# Composed inference and retained proof identity in maintained MM0 HOL

Implication reflexivity is constructed from the actual discharge and context
projection rules. Propositional extensionality derives Boolean reflexivity
from two copies of that proof and a checked definition unfolding. The native
reflexivity rule reaches the same exact conclusion with a different submitted
witness. Acceptance of the judgment does not recover which witness was used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelInferenceControls

open Kernel HOLKernelSyntax HOLKernelJudgment
open HOLKernelTypingRules (typed boolType)
open HOLKernelInferenceRules HOLKernelInferenceProofs
open HOLKernelStructuralRules (CheckedProof)

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
variable {equivalenceReference : Nat}

def implicationReflexivity (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent formula : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (formulaSorted : Preterm.HasType terms context formula [] signature.ids.object)
    (typing : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent formula (boolType signature.symbol))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent
        (holds signature.symbol (applySymbol signature.symbol .impc [formula, formula]))) :=
  Native.implicationIntroduction signature rules antecedent formula formula
    antecedentSorted formulaSorted formulaSorted typing typing
    (HOLKernelStructuralRules.right signature structural antecedent (holds signature.symbol formula)
      antecedentSorted (holds_sorted signature context formulaSorted))

def derivedBooleanReflexivity (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (rules : Rules theorems signature.symbol signature.ids abbreviation.reference)
    (antecedent formula : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (formulaSorted : Preterm.HasType terms context formula [] signature.ids.object)
    (typing : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent formula (boolType signature.symbol))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent
        (holds signature.symbol (equality signature.symbol (boolType signature.symbol) formula formula))) :=
  let implication := implicationReflexivity signature structural rules antecedent formula
    antecedentSorted formulaSorted typing
  propositionalExtensionality signature abbreviation rules antecedent formula formula
    antecedentSorted formulaSorted formulaSorted implication implication

theorem distinct_reflexivity_witnesses (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (rules : Rules theorems signature.symbol signature.ids abbreviation.reference)
    (antecedent formula : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (formulaSorted : Preterm.HasType terms context formula [] signature.ids.object)
    (typing : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent formula (boolType signature.symbol))) :
    (derivedBooleanReflexivity signature abbreviation structural rules antecedent formula
      antecedentSorted formulaSorted typing).val ≠
    (Native.reflexivity signature rules antecedent (boolType signature.symbol) formula antecedentSorted
      (signature.application context .bool [] .nil) formulaSorted typing).val := by
  intro same
  cases same

theorem both_reflexivity_witnesses_accepted (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (rules : Rules theorems signature.symbol signature.ids abbreviation.reference)
    (antecedent formula : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (formulaSorted : Preterm.HasType terms context formula [] signature.ids.object)
    (typing : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent formula (boolType signature.symbol))) :
    let conclusion := entails signature.symbol antecedent
      (holds signature.symbol (equality signature.symbol (boolType signature.symbol) formula formula))
    ProofWitness.proof? terms definitions theorems context hypotheses
      (derivedBooleanReflexivity signature abbreviation structural rules antecedent formula
        antecedentSorted formulaSorted typing).val = some conclusion ∧
    ProofWitness.proof? terms definitions theorems context hypotheses
      (Native.reflexivity signature rules antecedent (boolType signature.symbol) formula antecedentSorted
        (signature.application context .bool [] .nil) formulaSorted typing).val = some conclusion :=
  ⟨(derivedBooleanReflexivity signature abbreviation structural rules antecedent formula
      antecedentSorted formulaSorted typing).property.eval,
    (Native.reflexivity signature rules antecedent (boolType signature.symbol) formula antecedentSorted
      (signature.application context .bool [] .nil) formulaSorted typing).property.eval⟩

#print axioms implicationReflexivity
#print axioms derivedBooleanReflexivity
#print axioms distinct_reflexivity_witnesses
#print axioms both_reflexivity_witnesses_accepted

end Mettapedia.Languages.MM0.HOLKernelInferenceControls
