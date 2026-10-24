import Mettapedia.Languages.MM0.HOLKernelBindingRules
import Mettapedia.Languages.MM0.Kernel.RegularSubstitution
import Mettapedia.Languages.MM0.Kernel.SingleBoundSubstitution
import Mettapedia.Languages.MM0.Kernel.TwoBoundSubstitution

/-!
# Checked MM0 HOL binding and substitution applications

Each construction supplies the exact native parameter vector, its declared
bound images, and ordered premise proofs. Independence is generated from the
actual dependency metadata: beta permits its context to depend on the bound
image, while generalization does not. Two-bound abstraction renaming retains
apart target names and both bodies. These are applications of the maintained
rules; constructing source alpha and simultaneous-substitution proofs is a
further step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelBindingProofs

open Kernel HOLKernelSyntax
open HOLKernelJudgment (hasType holds entails conjunction)
open HOLKernelTypingRules (typed boolType functionType)
open HOLKernelInferenceRules (equality equivalence)
open HOLKernelBindingRules
open HOLKernelStructuralRules (CheckedProof)

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
variable {equivalenceReference : Nat}

namespace Native

def universalIntroduction (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent : Preterm)
    (domain : Preterm)
    (boundIndex : Nat)
    (formula : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (boundIndexBound : context[boundIndex]? = some (.bound signature.ids.object))
    (formulaSorted : Preterm.HasType terms context formula [] signature.ids.object)
    (antecedentIndependent : ¬ Preterm.HasVar context boundIndex antecedent)
    (domainIndependent : ¬ Preterm.HasVar context boundIndex domain)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol (antecedent) (hasType signature.symbol (.var boundIndex) (domain))) (holds signature.symbol (formula))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .allc [.var boundIndex, domain, formula]))) := by
  refine ⟨.theoremApp (rules.index .universalIntroduction) [antecedent, domain, .var boundIndex, formula]
    [premise0.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (conjunction signature.symbol (antecedent) (hasType signature.symbol (.var boundIndex) (domain))) (holds signature.symbol (formula))],
      entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .allc [.var boundIndex, domain, formula]))⟩) (rules.declared .universalIntroduction) ?_
      (.cons premise0.property .nil)⟩
  refine ⟨?_, (.cons ?_ .nil), ?_⟩
  · apply (Substitution.admissible_single_bound_iff _ _ 2 signature.ids.object boundIndex rfl rfl ?_).mpr
    · refine ⟨(.cons (.regular antecedentSorted) (.cons (.regular domainSorted) (.cons (.bound boundIndexBound) (.cons (.regular formulaSorted) .nil)))), ?_⟩
      intro other member absent
      simp [Rule.declaration, Substitution.entries] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact antecedentIndependent
      · exact domainIndependent
      · exact (absent rfl).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
    · intro position sort found
      have member : (.bound sort, position) ∈
          (Rule.declaration signature.symbol signature.ids equivalenceReference .universalIntroduction).arguments.zipIdx := by
        simpa only [List.mem_zipIdx_iff_getElem?] using found
      simp [Rule.declaration] at member
      omega
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, entails, hasType, holds, conjunction, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def universalElimination (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent : Preterm)
    (domain : Preterm)
    (boundIndex : Nat)
    (argument : Preterm)
    (body : Preterm)
    (result : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (boundIndexBound : context[boundIndex]? = some (.bound signature.ids.object))
    (argumentSorted : Preterm.HasType terms context argument [] signature.ids.object)
    (bodySorted : Preterm.HasType terms context body [] signature.ids.object)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.object)
    (antecedentIndependent : ¬ Preterm.HasVar context boundIndex antecedent)
    (domainIndependent : ¬ Preterm.HasVar context boundIndex domain)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (argument) (domain)))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (result) (boolType signature.symbol)))
    (premise2 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (domain) (.var boundIndex) (argument)))) (holds signature.symbol (equivalence equivalenceReference (body) (result)))))
    (premise3 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .allc [.var boundIndex, domain, body]))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (result))) := by
  refine ⟨.theoremApp (rules.index .universalElimination) [antecedent, domain, .var boundIndex, argument, body, result]
    [premise0.val, premise1.val, premise2.val, premise3.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol (antecedent) (argument) (domain),
      typed signature.symbol (antecedent) (result) (boolType signature.symbol),
      entails signature.symbol (conjunction signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (domain) (.var boundIndex) (argument)))) (holds signature.symbol (equivalence equivalenceReference (body) (result))),
      entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .allc [.var boundIndex, domain, body]))],
      entails signature.symbol (antecedent) (holds signature.symbol (result))⟩) (rules.declared .universalElimination) ?_
      (.cons premise0.property (.cons premise1.property (.cons premise2.property (.cons premise3.property .nil))))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))), ?_⟩
  · apply (Substitution.admissible_single_bound_iff _ _ 2 signature.ids.object boundIndex rfl rfl ?_).mpr
    · refine ⟨(.cons (.regular antecedentSorted) (.cons (.regular domainSorted) (.cons (.bound boundIndexBound) (.cons (.regular argumentSorted) (.cons (.regular bodySorted) (.cons (.regular resultSorted) .nil)))))), ?_⟩
      intro other member absent
      simp [Rule.declaration, Substitution.entries] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · exact antecedentIndependent
      · exact domainIndependent
      · exact (absent rfl).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
    · intro position sort found
      have member : (.bound sort, position) ∈
          (Rule.declaration signature.symbol signature.ids equivalenceReference .universalElimination).arguments.zipIdx := by
        simpa only [List.mem_zipIdx_iff_getElem?] using found
      simp [Rule.declaration] at member
      omega
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equality, equivalence, typed, entails, holds, conjunction, boolType, hasType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def existentialIntroduction (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent : Preterm)
    (domain : Preterm)
    (boundIndex : Nat)
    (argument : Preterm)
    (body : Preterm)
    (result : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (boundIndexBound : context[boundIndex]? = some (.bound signature.ids.object))
    (argumentSorted : Preterm.HasType terms context argument [] signature.ids.object)
    (bodySorted : Preterm.HasType terms context body [] signature.ids.object)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.object)
    (antecedentIndependent : ¬ Preterm.HasVar context boundIndex antecedent)
    (domainIndependent : ¬ Preterm.HasVar context boundIndex domain)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (conjunction signature.symbol (antecedent) (hasType signature.symbol (.var boundIndex) (domain))) (body) (boolType signature.symbol)))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (argument) (domain)))
    (premise2 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (domain) (.var boundIndex) (argument)))) (holds signature.symbol (equivalence equivalenceReference (body) (result)))))
    (premise3 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (result))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .exc [.var boundIndex, domain, body]))) := by
  refine ⟨.theoremApp (rules.index .existentialIntroduction) [antecedent, domain, .var boundIndex, argument, body, result]
    [premise0.val, premise1.val, premise2.val, premise3.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol (conjunction signature.symbol (antecedent) (hasType signature.symbol (.var boundIndex) (domain))) (body) (boolType signature.symbol),
      typed signature.symbol (antecedent) (argument) (domain),
      entails signature.symbol (conjunction signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (domain) (.var boundIndex) (argument)))) (holds signature.symbol (equivalence equivalenceReference (body) (result))),
      entails signature.symbol (antecedent) (holds signature.symbol (result))],
      entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .exc [.var boundIndex, domain, body]))⟩) (rules.declared .existentialIntroduction) ?_
      (.cons premise0.property (.cons premise1.property (.cons premise2.property (.cons premise3.property .nil))))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))), ?_⟩
  · apply (Substitution.admissible_single_bound_iff _ _ 2 signature.ids.object boundIndex rfl rfl ?_).mpr
    · refine ⟨(.cons (.regular antecedentSorted) (.cons (.regular domainSorted) (.cons (.bound boundIndexBound) (.cons (.regular argumentSorted) (.cons (.regular bodySorted) (.cons (.regular resultSorted) .nil)))))), ?_⟩
      intro other member absent
      simp [Rule.declaration, Substitution.entries] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · exact antecedentIndependent
      · exact domainIndependent
      · exact (absent rfl).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
    · intro position sort found
      have member : (.bound sort, position) ∈
          (Rule.declaration signature.symbol signature.ids equivalenceReference .existentialIntroduction).arguments.zipIdx := by
        simpa only [List.mem_zipIdx_iff_getElem?] using found
      simp [Rule.declaration] at member
      omega
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equality, equivalence, typed, entails, hasType, holds, conjunction, boolType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def existentialElimination (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent : Preterm)
    (domain : Preterm)
    (boundIndex : Nat)
    (body : Preterm)
    (result : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (boundIndexBound : context[boundIndex]? = some (.bound signature.ids.object))
    (bodySorted : Preterm.HasType terms context body [] signature.ids.object)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.object)
    (antecedentIndependent : ¬ Preterm.HasVar context boundIndex antecedent)
    (domainIndependent : ¬ Preterm.HasVar context boundIndex domain)
    (resultIndependent : ¬ Preterm.HasVar context boundIndex result)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (result) (boolType signature.symbol)))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .exc [.var boundIndex, domain, body]))))
    (premise2 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol (conjunction signature.symbol (antecedent) (hasType signature.symbol (.var boundIndex) (domain))) (holds signature.symbol (body))) (holds signature.symbol (result))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (result))) := by
  refine ⟨.theoremApp (rules.index .existentialElimination) [antecedent, domain, .var boundIndex, body, result]
    [premise0.val, premise1.val, premise2.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol (antecedent) (result) (boolType signature.symbol),
      entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .exc [.var boundIndex, domain, body])),
      entails signature.symbol (conjunction signature.symbol (conjunction signature.symbol (antecedent) (hasType signature.symbol (.var boundIndex) (domain))) (holds signature.symbol (body))) (holds signature.symbol (result))],
      entails signature.symbol (antecedent) (holds signature.symbol (result))⟩) (rules.declared .existentialElimination) ?_
      (.cons premise0.property (.cons premise1.property (.cons premise2.property .nil)))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ (.cons ?_ .nil))), ?_⟩
  · apply (Substitution.admissible_single_bound_iff _ _ 2 signature.ids.object boundIndex rfl rfl ?_).mpr
    · refine ⟨(.cons (.regular antecedentSorted) (.cons (.regular domainSorted) (.cons (.bound boundIndexBound) (.cons (.regular bodySorted) (.cons (.regular resultSorted) .nil))))), ?_⟩
      intro other member absent
      simp [Rule.declaration, Substitution.entries] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · exact antecedentIndependent
      · exact domainIndependent
      · exact (absent rfl).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
      · exact resultIndependent
    · intro position sort found
      have member : (.bound sort, position) ∈
          (Rule.declaration signature.symbol signature.ids equivalenceReference .existentialElimination).arguments.zipIdx := by
        simpa only [List.mem_zipIdx_iff_getElem?] using found
      simp [Rule.declaration] at member
      omega
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, typed, entails, hasType, holds, conjunction, boolType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def abstractionCongruence (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent : Preterm)
    (domain : Preterm)
    (result : Preterm)
    (boundIndex : Nat)
    (first : Preterm)
    (second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.type)
    (boundIndexBound : context[boundIndex]? = some (.bound signature.ids.object))
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (antecedentIndependent : ¬ Preterm.HasVar context boundIndex antecedent)
    (domainIndependent : ¬ Preterm.HasVar context boundIndex domain)
    (resultIndependent : ¬ Preterm.HasVar context boundIndex result)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol (antecedent) (hasType signature.symbol (.var boundIndex) (domain))) (holds signature.symbol (equality signature.symbol (result) (first) (second)))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (functionType signature.symbol (domain) (result)) (applySymbol signature.symbol .lam [.var boundIndex, domain, first]) (applySymbol signature.symbol .lam [.var boundIndex, domain, second])))) := by
  refine ⟨.theoremApp (rules.index .abstractionCongruence) [antecedent, domain, result, .var boundIndex, first, second]
    [premise0.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (conjunction signature.symbol (antecedent) (hasType signature.symbol (.var boundIndex) (domain))) (holds signature.symbol (equality signature.symbol (result) (first) (second)))],
      entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (functionType signature.symbol (domain) (result)) (applySymbol signature.symbol .lam [.var boundIndex, domain, first]) (applySymbol signature.symbol .lam [.var boundIndex, domain, second])))⟩) (rules.declared .abstractionCongruence) ?_
      (.cons premise0.property .nil)⟩
  refine ⟨?_, (.cons ?_ .nil), ?_⟩
  · apply (Substitution.admissible_single_bound_iff _ _ 3 signature.ids.object boundIndex rfl rfl ?_).mpr
    · refine ⟨(.cons (.regular antecedentSorted) (.cons (.regular domainSorted) (.cons (.regular resultSorted) (.cons (.bound boundIndexBound) (.cons (.regular firstSorted) (.cons (.regular secondSorted) .nil)))))), ?_⟩
      intro other member absent
      simp [Rule.declaration, Substitution.entries] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · exact antecedentIndependent
      · exact domainIndependent
      · exact resultIndependent
      · exact (absent rfl).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
    · intro position sort found
      have member : (.bound sort, position) ∈
          (Rule.declaration signature.symbol signature.ids equivalenceReference .abstractionCongruence).arguments.zipIdx := by
        simpa only [List.mem_zipIdx_iff_getElem?] using found
      simp [Rule.declaration] at member
      omega
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equality, entails, hasType, holds, conjunction, functionType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def variableBeta (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (domain : Preterm)
    (result : Preterm)
    (boundIndex : Nat)
    (antecedent : Preterm)
    (body : Preterm)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.type)
    (boundIndexBound : context[boundIndex]? = some (.bound signature.ids.object))
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (bodySorted : Preterm.HasType terms context body [] signature.ids.object)
    (domainIndependent : ¬ Preterm.HasVar context boundIndex domain)
    (resultIndependent : ¬ Preterm.HasVar context boundIndex result)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (applySymbol signature.symbol .app [applySymbol signature.symbol .lam [.var boundIndex, domain, body], .var boundIndex]) (result)))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (result) (applySymbol signature.symbol .app [applySymbol signature.symbol .lam [.var boundIndex, domain, body], .var boundIndex]) (body)))) := by
  refine ⟨.theoremApp (rules.index .variableBeta) [domain, result, .var boundIndex, antecedent, body]
    [premise0.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol (antecedent) (applySymbol signature.symbol .app [applySymbol signature.symbol .lam [.var boundIndex, domain, body], .var boundIndex]) (result)],
      entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (result) (applySymbol signature.symbol .app [applySymbol signature.symbol .lam [.var boundIndex, domain, body], .var boundIndex]) (body)))⟩) (rules.declared .variableBeta) ?_
      (.cons premise0.property .nil)⟩
  refine ⟨?_, (.cons ?_ .nil), ?_⟩
  · apply (Substitution.admissible_single_bound_iff _ _ 2 signature.ids.object boundIndex rfl rfl ?_).mpr
    · refine ⟨(.cons (.regular domainSorted) (.cons (.regular resultSorted) (.cons (.bound boundIndexBound) (.cons (.regular antecedentSorted) (.cons (.regular bodySorted) .nil))))), ?_⟩
      intro other member absent
      simp [Rule.declaration, Substitution.entries] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · exact domainIndependent
      · exact resultIndependent
      · exact (absent rfl).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
    · intro position sort found
      have member : (.bound sort, position) ∈
          (Rule.declaration signature.symbol signature.ids equivalenceReference .variableBeta).arguments.zipIdx := by
        simpa only [List.mem_zipIdx_iff_getElem?] using found
      simp [Rule.declaration] at member
      omega
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equality, typed, entails, holds, hasType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def eta (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent : Preterm)
    (domain : Preterm)
    (result : Preterm)
    (boundIndex : Nat)
    (function : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.type)
    (boundIndexBound : context[boundIndex]? = some (.bound signature.ids.object))
    (functionSorted : Preterm.HasType terms context function [] signature.ids.object)
    (antecedentIndependent : ¬ Preterm.HasVar context boundIndex antecedent)
    (domainIndependent : ¬ Preterm.HasVar context boundIndex domain)
    (resultIndependent : ¬ Preterm.HasVar context boundIndex result)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (function) (functionType signature.symbol (domain) (result))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (functionType signature.symbol (domain) (result)) (applySymbol signature.symbol .lam [.var boundIndex, domain, applySymbol signature.symbol .app [function, .var boundIndex]]) (function)))) := by
  refine ⟨.theoremApp (rules.index .eta) [antecedent, domain, result, .var boundIndex, function]
    [premise0.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol (antecedent) (function) (functionType signature.symbol (domain) (result))],
      entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (functionType signature.symbol (domain) (result)) (applySymbol signature.symbol .lam [.var boundIndex, domain, applySymbol signature.symbol .app [function, .var boundIndex]]) (function)))⟩) (rules.declared .eta) ?_
      (.cons premise0.property .nil)⟩
  refine ⟨?_, (.cons ?_ .nil), ?_⟩
  · apply (Substitution.admissible_single_bound_iff _ _ 3 signature.ids.object boundIndex rfl rfl ?_).mpr
    · refine ⟨(.cons (.regular antecedentSorted) (.cons (.regular domainSorted) (.cons (.regular resultSorted) (.cons (.bound boundIndexBound) (.cons (.regular functionSorted) .nil))))), ?_⟩
      intro other member absent
      simp [Rule.declaration, Substitution.entries] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · exact antecedentIndependent
      · exact domainIndependent
      · exact resultIndependent
      · exact (absent rfl).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
    · intro position sort found
      have member : (.bound sort, position) ∈
          (Rule.declaration signature.symbol signature.ids equivalenceReference .eta).arguments.zipIdx := by
        simpa only [List.mem_zipIdx_iff_getElem?] using found
      simp [Rule.declaration] at member
      omega
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equality, typed, entails, holds, functionType, hasType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def constantAbstractionRenaming (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent : Preterm)
    (domain : Preterm)
    (result : Preterm)
    (firstIndex : Nat)
    (secondIndex : Nat)
    (body : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.type)
    (firstIndexBound : context[firstIndex]? = some (.bound signature.ids.object))
    (secondIndexBound : context[secondIndex]? = some (.bound signature.ids.object))
    (bodySorted : Preterm.HasType terms context body [] signature.ids.object)
    (antecedentFirstIndependent : ¬ Preterm.HasVar context firstIndex antecedent)
    (domainFirstIndependent : ¬ Preterm.HasVar context firstIndex domain)
    (resultFirstIndependent : ¬ Preterm.HasVar context firstIndex result)
    (antecedentSecondIndependent : ¬ Preterm.HasVar context secondIndex antecedent)
    (domainSecondIndependent : ¬ Preterm.HasVar context secondIndex domain)
    (resultSecondIndependent : ¬ Preterm.HasVar context secondIndex result)
    (different : firstIndex ≠ secondIndex)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (body) (result)))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (functionType signature.symbol (domain) (result)) (applySymbol signature.symbol .lam [.var firstIndex, domain, body]) (applySymbol signature.symbol .lam [.var secondIndex, domain, body])))) := by
  refine ⟨.theoremApp (rules.index .constantAbstractionRenaming) [antecedent, domain, result, .var firstIndex, .var secondIndex, body]
    [premise0.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol (antecedent) (body) (result)],
      entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (functionType signature.symbol (domain) (result)) (applySymbol signature.symbol .lam [.var firstIndex, domain, body]) (applySymbol signature.symbol .lam [.var secondIndex, domain, body])))⟩) (rules.declared .constantAbstractionRenaming) ?_
      (.cons premise0.property .nil)⟩
  refine ⟨?_, (.cons ?_ .nil), ?_⟩
  · apply (Substitution.admissible_iff_of_two_bound_positions _ _ 3 signature.ids.object firstIndex 4 signature.ids.object secondIndex rfl rfl rfl rfl ?_).mpr
    · refine ⟨(.cons (.regular antecedentSorted) (.cons (.regular domainSorted) (.cons (.regular resultSorted) (.cons (.bound firstIndexBound) (.cons (.bound secondIndexBound) (.cons (.regular bodySorted) .nil)))))), ?_, ?_⟩
      · intro other member absent
        simp [Rule.declaration, Substitution.entries] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl
        · exact antecedentFirstIndependent
        · exact domainFirstIndependent
        · exact resultFirstIndependent
        · exact (absent rfl).elim
        · simp [Preterm.hasVar_var_iff, secondIndexBound, different]
        · exact (absent (by simp [Binder.DependsOn])).elim
      · intro other member absent
        simp [Rule.declaration, Substitution.entries] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl
        · exact antecedentSecondIndependent
        · exact domainSecondIndependent
        · exact resultSecondIndependent
        · simp [Preterm.hasVar_var_iff, firstIndexBound, different, ne_comm]
        · exact (absent rfl).elim
        · exact (absent (by simp [Binder.DependsOn])).elim
    · intro position sort found
      have member : (.bound sort, position) ∈
          (Rule.declaration signature.symbol signature.ids equivalenceReference .constantAbstractionRenaming).arguments.zipIdx := by
        simpa only [List.mem_zipIdx_iff_getElem?] using found
      simp [Rule.declaration] at member
      omega
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equality, typed, entails, holds, functionType, hasType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def abstractionRenaming (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (domain : Preterm)
    (result : Preterm)
    (antecedent : Preterm)
    (firstIndex : Nat)
    (secondIndex : Nat)
    (first : Preterm)
    (second : Preterm)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.type)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstIndexBound : context[firstIndex]? = some (.bound signature.ids.object))
    (secondIndexBound : context[secondIndex]? = some (.bound signature.ids.object))
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (domainFirstIndependent : ¬ Preterm.HasVar context firstIndex domain)
    (resultFirstIndependent : ¬ Preterm.HasVar context firstIndex result)
    (antecedentFirstIndependent : ¬ Preterm.HasVar context firstIndex antecedent)
    (domainSecondIndependent : ¬ Preterm.HasVar context secondIndex domain)
    (resultSecondIndependent : ¬ Preterm.HasVar context secondIndex result)
    (antecedentSecondIndependent : ¬ Preterm.HasVar context secondIndex antecedent)
    (different : firstIndex ≠ secondIndex)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (conjunction signature.symbol (antecedent) (hasType signature.symbol (.var firstIndex) (domain))) (first) (result)))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (conjunction signature.symbol (antecedent) (hasType signature.symbol (.var secondIndex) (domain))) (second) (result)))
    (premise2 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (domain) (.var firstIndex) (.var secondIndex)))) (holds signature.symbol (equality signature.symbol (result) (first) (second)))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (functionType signature.symbol (domain) (result)) (applySymbol signature.symbol .lam [.var firstIndex, domain, first]) (applySymbol signature.symbol .lam [.var secondIndex, domain, second])))) := by
  refine ⟨.theoremApp (rules.index .abstractionRenaming) [domain, result, antecedent, .var firstIndex, .var secondIndex, first, second]
    [premise0.val, premise1.val, premise2.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol (conjunction signature.symbol (antecedent) (hasType signature.symbol (.var firstIndex) (domain))) (first) (result),
      typed signature.symbol (conjunction signature.symbol (antecedent) (hasType signature.symbol (.var secondIndex) (domain))) (second) (result),
      entails signature.symbol (conjunction signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (domain) (.var firstIndex) (.var secondIndex)))) (holds signature.symbol (equality signature.symbol (result) (first) (second)))],
      entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (functionType signature.symbol (domain) (result)) (applySymbol signature.symbol .lam [.var firstIndex, domain, first]) (applySymbol signature.symbol .lam [.var secondIndex, domain, second])))⟩) (rules.declared .abstractionRenaming) ?_
      (.cons premise0.property (.cons premise1.property (.cons premise2.property .nil)))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ (.cons ?_ .nil))), ?_⟩
  · apply (Substitution.admissible_iff_of_two_bound_positions _ _ 3 signature.ids.object firstIndex 4 signature.ids.object secondIndex rfl rfl rfl rfl ?_).mpr
    · refine ⟨(.cons (.regular domainSorted) (.cons (.regular resultSorted) (.cons (.regular antecedentSorted) (.cons (.bound firstIndexBound) (.cons (.bound secondIndexBound) (.cons (.regular firstSorted) (.cons (.regular secondSorted) .nil))))))), ?_, ?_⟩
      · intro other member absent
        simp [Rule.declaration, Substitution.entries] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact domainFirstIndependent
        · exact resultFirstIndependent
        · exact antecedentFirstIndependent
        · exact (absent rfl).elim
        · simp [Preterm.hasVar_var_iff, secondIndexBound, different]
        · exact (absent (by simp [Binder.DependsOn])).elim
        · exact (absent (by simp [Binder.DependsOn])).elim
      · intro other member absent
        simp [Rule.declaration, Substitution.entries] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact domainSecondIndependent
        · exact resultSecondIndependent
        · exact antecedentSecondIndependent
        · simp [Preterm.hasVar_var_iff, firstIndexBound, different, ne_comm]
        · exact (absent rfl).elim
        · exact (absent (by simp [Binder.DependsOn])).elim
        · exact (absent (by simp [Binder.DependsOn])).elim
    · intro position sort found
      have member : (.bound sort, position) ∈
          (Rule.declaration signature.symbol signature.ids equivalenceReference .abstractionRenaming).arguments.zipIdx := by
        simpa only [List.mem_zipIdx_iff_getElem?] using found
      simp [Rule.declaration] at member
      omega
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equality, typed, entails, hasType, holds, conjunction, functionType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def substitution (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent : Preterm)
    (domain : Preterm)
    (boundIndex : Nat)
    (argument : Preterm)
    (formula : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (boundIndexBound : context[boundIndex]? = some (.bound signature.ids.object))
    (argumentSorted : Preterm.HasType terms context argument [] signature.ids.object)
    (formulaSorted : Preterm.HasType terms context formula [] signature.ids.object)
    (antecedentIndependent : ¬ Preterm.HasVar context boundIndex antecedent)
    (domainIndependent : ¬ Preterm.HasVar context boundIndex domain)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (formula) (boolType signature.symbol)))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (argument) (domain)))
    (premise2 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (domain) (.var boundIndex) (argument)))) (holds signature.symbol (formula))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (formula))) := by
  refine ⟨.theoremApp (rules.index .substitution) [antecedent, domain, .var boundIndex, argument, formula]
    [premise0.val, premise1.val, premise2.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol (antecedent) (formula) (boolType signature.symbol),
      typed signature.symbol (antecedent) (argument) (domain),
      entails signature.symbol (conjunction signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (domain) (.var boundIndex) (argument)))) (holds signature.symbol (formula))],
      entails signature.symbol (antecedent) (holds signature.symbol (formula))⟩) (rules.declared .substitution) ?_
      (.cons premise0.property (.cons premise1.property (.cons premise2.property .nil)))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ (.cons ?_ .nil))), ?_⟩
  · apply (Substitution.admissible_single_bound_iff _ _ 2 signature.ids.object boundIndex rfl rfl ?_).mpr
    · refine ⟨(.cons (.regular antecedentSorted) (.cons (.regular domainSorted) (.cons (.bound boundIndexBound) (.cons (.regular argumentSorted) (.cons (.regular formulaSorted) .nil))))), ?_⟩
      intro other member absent
      simp [Rule.declaration, Substitution.entries] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · exact antecedentIndependent
      · exact domainIndependent
      · exact (absent rfl).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
    · intro position sort found
      have member : (.bound sort, position) ∈
          (Rule.declaration signature.symbol signature.ids equivalenceReference .substitution).arguments.zipIdx := by
        simpa only [List.mem_zipIdx_iff_getElem?] using found
      simp [Rule.declaration] at member
      omega
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equality, typed, entails, holds, conjunction, boolType, hasType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def beta (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent : Preterm)
    (domain : Preterm)
    (result : Preterm)
    (boundIndex : Nat)
    (argument : Preterm)
    (body : Preterm)
    (value : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.type)
    (boundIndexBound : context[boundIndex]? = some (.bound signature.ids.object))
    (argumentSorted : Preterm.HasType terms context argument [] signature.ids.object)
    (bodySorted : Preterm.HasType terms context body [] signature.ids.object)
    (valueSorted : Preterm.HasType terms context value [] signature.ids.object)
    (antecedentIndependent : ¬ Preterm.HasVar context boundIndex antecedent)
    (domainIndependent : ¬ Preterm.HasVar context boundIndex domain)
    (resultIndependent : ¬ Preterm.HasVar context boundIndex result)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (conjunction signature.symbol (antecedent) (hasType signature.symbol (.var boundIndex) (domain))) (body) (result)))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (argument) (domain)))
    (premise2 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (value) (result)))
    (premise3 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (domain) (.var boundIndex) (argument)))) (holds signature.symbol (equality signature.symbol (result) (body) (value)))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (result) (applySymbol signature.symbol .app [applySymbol signature.symbol .lam [.var boundIndex, domain, body], argument]) (value)))) := by
  refine ⟨.theoremApp (rules.index .beta) [antecedent, domain, result, .var boundIndex, argument, body, value]
    [premise0.val, premise1.val, premise2.val, premise3.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol (conjunction signature.symbol (antecedent) (hasType signature.symbol (.var boundIndex) (domain))) (body) (result),
      typed signature.symbol (antecedent) (argument) (domain),
      typed signature.symbol (antecedent) (value) (result),
      entails signature.symbol (conjunction signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (domain) (.var boundIndex) (argument)))) (holds signature.symbol (equality signature.symbol (result) (body) (value)))],
      entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (result) (applySymbol signature.symbol .app [applySymbol signature.symbol .lam [.var boundIndex, domain, body], argument]) (value)))⟩) (rules.declared .beta) ?_
      (.cons premise0.property (.cons premise1.property (.cons premise2.property (.cons premise3.property .nil))))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))), ?_⟩
  · apply (Substitution.admissible_single_bound_iff _ _ 3 signature.ids.object boundIndex rfl rfl ?_).mpr
    · refine ⟨(.cons (.regular antecedentSorted) (.cons (.regular domainSorted) (.cons (.regular resultSorted) (.cons (.bound boundIndexBound) (.cons (.regular argumentSorted) (.cons (.regular bodySorted) (.cons (.regular valueSorted) .nil))))))), ?_⟩
      intro other member absent
      simp [Rule.declaration, Substitution.entries] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact antecedentIndependent
      · exact domainIndependent
      · exact resultIndependent
      · exact (absent rfl).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
      · exact (absent (by simp [Binder.DependsOn])).elim
    · intro position sort found
      have member : (.bound sort, position) ∈
          (Rule.declaration signature.symbol signature.ids equivalenceReference .beta).arguments.zipIdx := by
        simpa only [List.mem_zipIdx_iff_getElem?] using found
      simp [Rule.declaration] at member
      omega
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equality, typed, entails, hasType, holds, conjunction, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def equalityLeftTyping (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (type : Preterm)
    (antecedent : Preterm)
    (first : Preterm)
    (second : Preterm)
    (typeSorted : Preterm.HasType terms context type [] signature.ids.type)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (type) (first) (second)))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (first) (type)) := by
  refine ⟨.theoremApp (rules.index .equalityLeftTyping) [type, antecedent, first, second]
    [premise0.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (type) (first) (second)))],
      typed signature.symbol (antecedent) (first) (type)⟩) (rules.declared .equalityLeftTyping) ?_
      (.cons premise0.property .nil)⟩
  refine ⟨?_, (.cons ?_ .nil), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.type, signature.ids.wff, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons typeSorted (.cons antecedentSorted (.cons firstSorted (.cons secondSorted .nil))))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equality, typed, entails, holds, hasType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def equalityRightTyping (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (type : Preterm)
    (antecedent : Preterm)
    (first : Preterm)
    (second : Preterm)
    (typeSorted : Preterm.HasType terms context type [] signature.ids.type)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (type) (first) (second)))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (second) (type)) := by
  refine ⟨.theoremApp (rules.index .equalityRightTyping) [type, antecedent, first, second]
    [premise0.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (type) (first) (second)))],
      typed signature.symbol (antecedent) (second) (type)⟩) (rules.declared .equalityRightTyping) ?_
      (.cons premise0.property .nil)⟩
  refine ⟨?_, (.cons ?_ .nil), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.type, signature.ids.wff, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons typeSorted (.cons antecedentSorted (.cons firstSorted (.cons secondSorted .nil))))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equality, typed, entails, holds, hasType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

end Native

#print axioms Native.universalIntroduction
#print axioms Native.universalElimination
#print axioms Native.existentialIntroduction
#print axioms Native.existentialElimination
#print axioms Native.abstractionCongruence
#print axioms Native.variableBeta
#print axioms Native.eta
#print axioms Native.constantAbstractionRenaming
#print axioms Native.abstractionRenaming
#print axioms Native.substitution
#print axioms Native.beta
#print axioms Native.equalityLeftTyping
#print axioms Native.equalityRightTyping

end Mettapedia.Languages.MM0.HOLKernelBindingProofs
