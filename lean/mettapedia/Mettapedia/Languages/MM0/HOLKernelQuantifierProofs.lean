import Mettapedia.Languages.MM0.HOLKernelBindingProofs
import Mettapedia.Languages.MM0.HOLKernelBooleanEquality

/-!
# MM0 quantifier inference with source Boolean-equality premises

Universal elimination and existential introduction use an explicit equation
between a bound body and its proposed instance. The source equation is typed
Boolean equality. Checked definition conversion supplies the maintained
rules' Boolean-equivalence premise under the same equality assumption and
the same retained hypotheses. No simultaneous-substitution equation is
assumed merely from a syntactic rendering.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelQuantifierProofs

open Kernel HOLKernelSyntax HOLKernelJudgment
open HOLKernelTypingRules (typed boolType)
open HOLKernelInferenceRules (equality)
open HOLKernelStructuralRules (CheckedProof)

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}

private theorem substitutionContext_sorted (signature : Signature sorts terms)
    (antecedent domain argument : Preterm) (boundIndex : Nat)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (argumentSorted : Preterm.HasType terms context argument [] signature.ids.object)
    (bound : context[boundIndex]? = some (.bound signature.ids.object)) :
    Preterm.HasType terms context
      (conjunction signature.symbol antecedent
        (holds signature.symbol (equality signature.symbol domain (.var boundIndex) argument)))
      [] signature.ids.wff :=
  conjunction_sorted signature context antecedentSorted
    (holds_sorted signature context (signature.application context .eqc _
      (.cons (.regular domainSorted)
        (.cons (.regular (Preterm.HasType.var (binder := .bound signature.ids.object) bound))
          (.cons (.regular argumentSorted) .nil)))))

def universalElimination (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (rules : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (antecedent domain argument body result : Preterm) (boundIndex : Nat)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (bound : context[boundIndex]? = some (.bound signature.ids.object))
    (argumentSorted : Preterm.HasType terms context argument [] signature.ids.object)
    (bodySorted : Preterm.HasType terms context body [] signature.ids.object)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.object)
    (antecedentIndependent : ¬ Preterm.HasVar context boundIndex antecedent)
    (domainIndependent : ¬ Preterm.HasVar context boundIndex domain)
    (argumentTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses) (typed signature.symbol antecedent argument domain))
    (resultTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses) (typed signature.symbol antecedent result (boolType signature.symbol)))
    (substitutionEquation : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol antecedent
        (holds signature.symbol (equality signature.symbol domain (.var boundIndex) argument)))
        (holds signature.symbol (equality signature.symbol (boolType signature.symbol) body result))))
    (universal : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent
        (holds signature.symbol (applySymbol signature.symbol .allc [.var boundIndex, domain, body])))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol result)) :=
  let equalityContext := conjunction signature.symbol antecedent
    (holds signature.symbol (equality signature.symbol domain (.var boundIndex) argument))
  let converted := HOLKernelBooleanEquality.contractProof signature abbreviation equalityContext body result
    (substitutionContext_sorted signature antecedent domain argument boundIndex
      antecedentSorted domainSorted argumentSorted bound) bodySorted resultSorted substitutionEquation
  HOLKernelBindingProofs.Native.universalElimination signature rules
    antecedent domain boundIndex argument body result antecedentSorted domainSorted bound
    argumentSorted bodySorted resultSorted antecedentIndependent domainIndependent
    argumentTyping resultTyping converted universal

def existentialIntroduction (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (rules : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (antecedent domain argument body result : Preterm) (boundIndex : Nat)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (bound : context[boundIndex]? = some (.bound signature.ids.object))
    (argumentSorted : Preterm.HasType terms context argument [] signature.ids.object)
    (bodySorted : Preterm.HasType terms context body [] signature.ids.object)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.object)
    (antecedentIndependent : ¬ Preterm.HasVar context boundIndex antecedent)
    (domainIndependent : ¬ Preterm.HasVar context boundIndex domain)
    (bodyTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (conjunction signature.symbol antecedent
        (hasType signature.symbol (.var boundIndex) domain)) body (boolType signature.symbol)))
    (argumentTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses) (typed signature.symbol antecedent argument domain))
    (substitutionEquation : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol antecedent
        (holds signature.symbol (equality signature.symbol domain (.var boundIndex) argument)))
        (holds signature.symbol (equality signature.symbol (boolType signature.symbol) body result))))
    (instanceProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol result))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent
        (holds signature.symbol (applySymbol signature.symbol .exc [.var boundIndex, domain, body]))) :=
  let equalityContext := conjunction signature.symbol antecedent
    (holds signature.symbol (equality signature.symbol domain (.var boundIndex) argument))
  let converted := HOLKernelBooleanEquality.contractProof signature abbreviation equalityContext body result
    (substitutionContext_sorted signature antecedent domain argument boundIndex
      antecedentSorted domainSorted argumentSorted bound) bodySorted resultSorted substitutionEquation
  HOLKernelBindingProofs.Native.existentialIntroduction signature rules
    antecedent domain boundIndex argument body result antecedentSorted domainSorted bound
    argumentSorted bodySorted resultSorted antecedentIndependent domainIndependent
    bodyTyping argumentTyping converted instanceProof

#print axioms universalElimination
#print axioms existentialIntroduction

end Mettapedia.Languages.MM0.HOLKernelQuantifierProofs
