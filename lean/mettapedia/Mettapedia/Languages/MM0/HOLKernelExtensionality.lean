import Mettapedia.Languages.MM0.HOLKernelCongruence
import Mettapedia.Languages.MM0.HOLKernelQuantifierProofs
import Mettapedia.Languages.MM0.HOLKernelTypeSupport
import Mettapedia.Languages.MM0.HOLKernelTypingProofs

/-!
# Checked function extensionality in maintained MM0 HOL

Specialization at a second fresh variable yields a pointwise equality.
Abstraction congruence and the two maintained eta equations then identify
the functions. The substitution equation for specialization is constructed
from application and equality congruence, with no additional theorem schema.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelExtensionality
open Kernel HOLKernelSyntax HOLKernelJudgment
open HOLKernelTypingRules (typed boolType functionType)
open HOLKernelInferenceRules (equality)
open HOLKernelStructuralRules (CheckedProof)
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}

def functionExtensionality (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (antecedent domain result first second : Preterm) (quantified argument : Nat)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.type)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (quantifiedBound : context[quantified]? = some (.bound signature.ids.object))
    (argumentBound : context[argument]? = some (.bound signature.ids.object))
    (different : quantified ≠ argument)
    (antecedentQuantifiedIndependent : ¬ Preterm.HasVar context quantified antecedent)
    (antecedentArgumentIndependent : ¬ Preterm.HasVar context argument antecedent)
    (domainQuantifiedIndependent : ¬ Preterm.HasVar context quantified domain)
    (domainArgumentIndependent : ¬ Preterm.HasVar context argument domain)
    (resultArgumentIndependent : ¬ Preterm.HasVar context argument result)
    (firstTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent first (functionType signature.symbol domain result)))
    (secondTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent second (functionType signature.symbol domain result)))
    (pointwise : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (applySymbol signature.symbol .allc
        [.var quantified, domain, equality signature.symbol result
          (applySymbol signature.symbol .app [first, .var quantified])
          (applySymbol signature.symbol .app [second, .var quantified])])))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol (functionType signature.symbol domain result) first second))) := by
  have quantifiedSorted : Preterm.HasType terms context (.var quantified) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) quantifiedBound
  have argumentSorted : Preterm.HasType terms context (.var argument) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) argumentBound
  have typeSorted := signature.application context .function [domain, result]
    (.cons (.regular domainSorted) (.cons (.regular resultSorted) .nil))
  let extra := hasType signature.symbol (.var argument) domain
  have extraSorted := hasType_sorted signature context argumentSorted domainSorted
  let extended := conjunction signature.symbol antecedent extra
  have extendedSorted := conjunction_sorted signature context antecedentSorted extraSorted
  let argumentTyping := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := hypotheses) signature structural antecedent extra antecedentSorted extraSorted
  let firstExtended := HOLKernelStructuralRules.weaken signature structural antecedent extra _ antecedentSorted extraSorted
    (hasType_sorted signature context firstSorted typeSorted) firstTyping
  let secondExtended := HOLKernelStructuralRules.weaken signature structural antecedent extra _ antecedentSorted extraSorted
    (hasType_sorted signature context secondSorted typeSorted) secondTyping
  have firstQuantifiedSorted := signature.application context .app _
    (.cons (.regular firstSorted) (.cons (.regular quantifiedSorted) .nil))
  have firstArgumentSorted := signature.application context .app _
    (.cons (.regular firstSorted) (.cons (.regular argumentSorted) .nil))
  have secondQuantifiedSorted := signature.application context .app _
    (.cons (.regular secondSorted) (.cons (.regular quantifiedSorted) .nil))
  have secondArgumentSorted := signature.application context .app _
    (.cons (.regular secondSorted) (.cons (.regular argumentSorted) .nil))
  let firstApplication := HOLKernelTypingProofs.applicationTyping signature typing extended domain result first (.var argument)
    extendedSorted domainSorted resultSorted firstSorted argumentSorted firstExtended argumentTyping
  let secondApplication := HOLKernelTypingProofs.applicationTyping signature typing extended domain result second (.var argument)
    extendedSorted domainSorted resultSorted secondSorted argumentSorted secondExtended argumentTyping
  let resultTyping := HOLKernelTypingProofs.equalityTyping signature typing result extended _ _ resultSorted extendedSorted
    firstArgumentSorted secondArgumentSorted firstApplication secondApplication
  let body := equality signature.symbol result
    (applySymbol signature.symbol .app [first, .var quantified])
    (applySymbol signature.symbol .app [second, .var quantified])
  let instantiated := equality signature.symbol result
    (applySymbol signature.symbol .app [first, .var argument])
    (applySymbol signature.symbol .app [second, .var argument])
  have bodySorted := signature.application context .eqc _
    (.cons (.regular resultSorted) (.cons (.regular firstQuantifiedSorted) (.cons (.regular secondQuantifiedSorted) .nil)))
  have instantiatedSorted := signature.application context .eqc _
    (.cons (.regular resultSorted) (.cons (.regular firstArgumentSorted) (.cons (.regular secondArgumentSorted) .nil)))
  let equation := holds signature.symbol (equality signature.symbol domain (.var quantified) (.var argument))
  have equationSorted := holds_sorted signature context (signature.application context .eqc _
    (.cons (.regular domainSorted) (.cons (.regular quantifiedSorted) (.cons (.regular argumentSorted) .nil))))
  let equationContext := conjunction signature.symbol extended equation
  have equationContextSorted := conjunction_sorted signature context extendedSorted equationSorted
  let variableEquation := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := hypotheses) signature structural extended equation extendedSorted equationSorted
  let firstUnderEquation := HOLKernelStructuralRules.weaken signature structural extended equation _ extendedSorted equationSorted
    (hasType_sorted signature context firstSorted typeSorted) firstExtended
  let secondUnderEquation := HOLKernelStructuralRules.weaken signature structural extended equation _ extendedSorted equationSorted
    (hasType_sorted signature context secondSorted typeSorted) secondExtended
  let firstEquation := HOLKernelInferenceProofs.Native.applicationArgument signature rules domain result equationContext _ _ first
    domainSorted resultSorted equationContextSorted quantifiedSorted argumentSorted firstSorted firstUnderEquation variableEquation
  let secondEquation := HOLKernelInferenceProofs.Native.applicationArgument signature rules domain result equationContext _ _ second
    domainSorted resultSorted equationContextSorted quantifiedSorted argumentSorted secondSorted secondUnderEquation variableEquation
  let substitution := HOLKernelCongruence.equalityCongruence signature profile rules binding equationContext result _ _ _ _
    equationContextSorted resultSorted firstQuantifiedSorted firstArgumentSorted secondQuantifiedSorted secondArgumentSorted
    firstEquation secondEquation
  have quantifiedFormulaSorted := signature.application context .allc _
    (.cons (.bound quantifiedBound) (.cons (.regular domainSorted) (.cons (.regular bodySorted) .nil)))
  let weakenedPointwise := HOLKernelStructuralRules.weaken signature structural antecedent extra _ antecedentSorted extraSorted
    (holds_sorted signature context quantifiedFormulaSorted) pointwise
  have extendedIndependent := HOLKernelTypeSupport.contextExtension_independent context quantified argument signature.ids.object
    signature.symbol antecedent domain argumentBound different antecedentQuantifiedIndependent domainQuantifiedIndependent
  let pointwiseAtArgument := HOLKernelQuantifierProofs.universalElimination signature abbreviation binding extended domain
    (.var argument) body instantiated quantified extendedSorted domainSorted quantifiedBound argumentSorted bodySorted instantiatedSorted
    extendedIndependent domainQuantifiedIndependent argumentTyping resultTyping substitution weakenedPointwise
  let abstraction := HOLKernelBindingProofs.Native.abstractionCongruence signature binding antecedent domain result argument _ _
    antecedentSorted domainSorted resultSorted argumentBound firstArgumentSorted secondArgumentSorted
    antecedentArgumentIndependent domainArgumentIndependent resultArgumentIndependent pointwiseAtArgument
  let firstEta := HOLKernelBindingProofs.Native.eta signature binding antecedent domain result argument first
    antecedentSorted domainSorted resultSorted argumentBound firstSorted antecedentArgumentIndependent
    domainArgumentIndependent resultArgumentIndependent firstTyping
  let secondEta := HOLKernelBindingProofs.Native.eta signature binding antecedent domain result argument second
    antecedentSorted domainSorted resultSorted argumentBound secondSorted antecedentArgumentIndependent
    domainArgumentIndependent resultArgumentIndependent secondTyping
  have firstLambdaSorted := signature.application context .lam _
    (.cons (.bound argumentBound) (.cons (.regular domainSorted) (.cons (.regular firstArgumentSorted) .nil)))
  have secondLambdaSorted := signature.application context .lam _
    (.cons (.bound argumentBound) (.cons (.regular domainSorted) (.cons (.regular secondArgumentSorted) .nil)))
  let firstBack := HOLKernelInferenceProofs.Native.symmetry signature rules _ antecedent _ _ typeSorted antecedentSorted
    firstLambdaSorted firstSorted firstEta
  let joined := HOLKernelInferenceProofs.Native.transitivity signature rules antecedent _ _ _ _ antecedentSorted typeSorted
    firstSorted firstLambdaSorted secondLambdaSorted firstBack abstraction
  exact HOLKernelInferenceProofs.Native.transitivity signature rules antecedent _ _ _ _ antecedentSorted typeSorted
    firstSorted secondLambdaSorted secondSorted joined secondEta

#print axioms functionExtensionality
end Mettapedia.Languages.MM0.HOLKernelExtensionality
