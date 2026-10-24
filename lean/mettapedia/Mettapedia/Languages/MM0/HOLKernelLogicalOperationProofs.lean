import Mettapedia.Languages.MM0.HOLKernelLogicalOperations
import Mettapedia.Languages.MM0.HOLKernelTypingRules

/-!
# Checked logical function typing and constructor unfolding in MM0 HOL

The typing witnesses instantiate the maintained declarations of the seven
logical function constants. The conversion witnesses unfold each stored
constructor abbreviation to its application expression. Quantifier unfolding
retains its bound image and body; it performs no alpha-renaming or substitution
inside that body. These constructions require actual stored definition bodies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelLogicalOperationProofs

open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelLogicalOperations
open HOLKernelTypingRules (typed boolType functionType)
open HOLKernelStructuralRules (CheckedProof)

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}

def equalityTyping (signature : Signature sorts terms)
    (profile : Profile sorts terms definitions theorems signature)
    (antecedent domain : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent (.app (.term (profile.reference .equality)) domain) (functionType signature.symbol domain (functionType signature.symbol domain (boolType signature.symbol)))) := by
  refine ⟨.theoremApp (profile.typingReference .equality) [antecedent, domain] [],
    .theoremApp (instantiation := ⟨[], typed signature.symbol antecedent (.app (.term (profile.reference .equality)) domain) (functionType signature.symbol domain (functionType signature.symbol domain (boolType signature.symbol)))⟩)
      (profile.typingDeclared .equality) ?_ .nil⟩
  refine ⟨?_, .nil, ?_⟩
  · exact Substitution.admissible_regular (.cons antecedentSorted (.cons domainSorted .nil))
  · apply Preterm.substitute_sound
    simp [Operator.typingDeclaration, typed, entails, hasType, boolType, functionType,
      applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def conjunctionTyping (signature : Signature sorts terms)
    (profile : Profile sorts terms definitions theorems signature)
    (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent (.term (profile.reference .conjunction)) (functionType signature.symbol (boolType signature.symbol) (functionType signature.symbol (boolType signature.symbol) (boolType signature.symbol)))) := by
  refine ⟨.theoremApp (profile.typingReference .conjunction) [antecedent] [],
    .theoremApp (instantiation := ⟨[], typed signature.symbol antecedent (.term (profile.reference .conjunction)) (functionType signature.symbol (boolType signature.symbol) (functionType signature.symbol (boolType signature.symbol) (boolType signature.symbol)))⟩)
      (profile.typingDeclared .conjunction) ?_ .nil⟩
  refine ⟨?_, .nil, ?_⟩
  · exact Substitution.admissible_regular (.cons antecedentSorted .nil)
  · apply Preterm.substitute_sound
    simp [Operator.typingDeclaration, typed, entails, hasType, boolType, functionType,
      applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def disjunctionTyping (signature : Signature sorts terms)
    (profile : Profile sorts terms definitions theorems signature)
    (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent (.term (profile.reference .disjunction)) (functionType signature.symbol (boolType signature.symbol) (functionType signature.symbol (boolType signature.symbol) (boolType signature.symbol)))) := by
  refine ⟨.theoremApp (profile.typingReference .disjunction) [antecedent] [],
    .theoremApp (instantiation := ⟨[], typed signature.symbol antecedent (.term (profile.reference .disjunction)) (functionType signature.symbol (boolType signature.symbol) (functionType signature.symbol (boolType signature.symbol) (boolType signature.symbol)))⟩)
      (profile.typingDeclared .disjunction) ?_ .nil⟩
  refine ⟨?_, .nil, ?_⟩
  · exact Substitution.admissible_regular (.cons antecedentSorted .nil)
  · apply Preterm.substitute_sound
    simp [Operator.typingDeclaration, typed, entails, hasType, boolType, functionType,
      applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def implicationTyping (signature : Signature sorts terms)
    (profile : Profile sorts terms definitions theorems signature)
    (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent (.term (profile.reference .implication)) (functionType signature.symbol (boolType signature.symbol) (functionType signature.symbol (boolType signature.symbol) (boolType signature.symbol)))) := by
  refine ⟨.theoremApp (profile.typingReference .implication) [antecedent] [],
    .theoremApp (instantiation := ⟨[], typed signature.symbol antecedent (.term (profile.reference .implication)) (functionType signature.symbol (boolType signature.symbol) (functionType signature.symbol (boolType signature.symbol) (boolType signature.symbol)))⟩)
      (profile.typingDeclared .implication) ?_ .nil⟩
  refine ⟨?_, .nil, ?_⟩
  · exact Substitution.admissible_regular (.cons antecedentSorted .nil)
  · apply Preterm.substitute_sound
    simp [Operator.typingDeclaration, typed, entails, hasType, boolType, functionType,
      applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def negationTyping (signature : Signature sorts terms)
    (profile : Profile sorts terms definitions theorems signature)
    (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent (.term (profile.reference .negation)) (functionType signature.symbol (boolType signature.symbol) (boolType signature.symbol))) := by
  refine ⟨.theoremApp (profile.typingReference .negation) [antecedent] [],
    .theoremApp (instantiation := ⟨[], typed signature.symbol antecedent (.term (profile.reference .negation)) (functionType signature.symbol (boolType signature.symbol) (boolType signature.symbol))⟩)
      (profile.typingDeclared .negation) ?_ .nil⟩
  refine ⟨?_, .nil, ?_⟩
  · exact Substitution.admissible_regular (.cons antecedentSorted .nil)
  · apply Preterm.substitute_sound
    simp [Operator.typingDeclaration, typed, entails, hasType, boolType, functionType,
      applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def universalTyping (signature : Signature sorts terms)
    (profile : Profile sorts terms definitions theorems signature)
    (antecedent domain : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent (.app (.term (profile.reference .universal)) domain) (functionType signature.symbol (functionType signature.symbol domain (boolType signature.symbol)) (boolType signature.symbol))) := by
  refine ⟨.theoremApp (profile.typingReference .universal) [antecedent, domain] [],
    .theoremApp (instantiation := ⟨[], typed signature.symbol antecedent (.app (.term (profile.reference .universal)) domain) (functionType signature.symbol (functionType signature.symbol domain (boolType signature.symbol)) (boolType signature.symbol))⟩)
      (profile.typingDeclared .universal) ?_ .nil⟩
  refine ⟨?_, .nil, ?_⟩
  · exact Substitution.admissible_regular (.cons antecedentSorted (.cons domainSorted .nil))
  · apply Preterm.substitute_sound
    simp [Operator.typingDeclaration, typed, entails, hasType, boolType, functionType,
      applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def existentialTyping (signature : Signature sorts terms)
    (profile : Profile sorts terms definitions theorems signature)
    (antecedent domain : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent (.app (.term (profile.reference .existential)) domain) (functionType signature.symbol (functionType signature.symbol domain (boolType signature.symbol)) (boolType signature.symbol))) := by
  refine ⟨.theoremApp (profile.typingReference .existential) [antecedent, domain] [],
    .theoremApp (instantiation := ⟨[], typed signature.symbol antecedent (.app (.term (profile.reference .existential)) domain) (functionType signature.symbol (functionType signature.symbol domain (boolType signature.symbol)) (boolType signature.symbol))⟩)
      (profile.typingDeclared .existential) ?_ .nil⟩
  refine ⟨?_, .nil, ?_⟩
  · exact Substitution.admissible_regular (.cons antecedentSorted (.cons domainSorted .nil))
  · apply Preterm.substitute_sound
    simp [Operator.typingDeclaration, typed, entails, hasType, boolType, functionType,
      applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def equalityUnfolding (signature : Signature sorts terms)
    (profile : Profile sorts terms definitions theorems signature)
    (domain first second : Preterm)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    : { witness : ConvWitness // ConvWitness.Checks terms definitions context witness
      (applySymbol signature.symbol .eqc [domain, first, second])
      (applySymbol signature.symbol .app [(applySymbol signature.symbol .app [(.app (.term (profile.reference .equality)) domain), first]), second]) signature.ids.object } := by
  have fitted : List.Forall₂ (Preterm.FitsBinder terms context) [domain, first, second]
      ((Operator.constructor .equality).profile signature.ids).arguments := (.cons (.regular domainSorted) (.cons (.regular firstSorted) (.cons (.regular secondSorted) .nil)))
  have unfolded : Definition.Unfolds terms definitions context (signature.symbol .eqc)
      [domain, first, second] [] (applySymbol signature.symbol .app [(applySymbol signature.symbol .app [(.app (.term (profile.reference .equality)) domain), first]), second]) := by
    refine .intro (signature.declared .eqc) (profile.defined .equality) fitted (.nil _) ?_
    apply Preterm.substitute_sound
    simp [Operator.body, Definition.substitutionValues, applySymbol, Preterm.applyArgs,
      Preterm.substitute, Substitution.ofList]
  have operatorSorted : Preterm.HasType terms context (.app (.term (profile.reference .equality)) domain) [] signature.ids.object :=
    .regular (by simpa [Operator.declaration] using Preterm.HasType.term (profile.declared .equality))
      domainSorted
  have partialSorted := signature.application context .app [(.app (.term (profile.reference .equality)) domain), first]
    (.cons (.regular operatorSorted) (.cons (.regular firstSorted) .nil))
  have expandedSorted := signature.application context .app [(applySymbol signature.symbol .app [(.app (.term (profile.reference .equality)) domain), first]), second]
    (.cons (.regular partialSorted) (.cons (.regular secondSorted) .nil))
  exact ⟨.unfold (signature.symbol .eqc) [domain, first, second] [],
    .unfold (signature.declared .eqc) unfolded expandedSorted⟩

def conjunctionUnfolding (signature : Signature sorts terms)
    (profile : Profile sorts terms definitions theorems signature)
    (first second : Preterm)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    : { witness : ConvWitness // ConvWitness.Checks terms definitions context witness
      (applySymbol signature.symbol .andc [first, second])
      (applySymbol signature.symbol .app [(applySymbol signature.symbol .app [(.term (profile.reference .conjunction)), first]), second]) signature.ids.object } := by
  have fitted : List.Forall₂ (Preterm.FitsBinder terms context) [first, second]
      ((Operator.constructor .conjunction).profile signature.ids).arguments := (.cons (.regular firstSorted) (.cons (.regular secondSorted) .nil))
  have unfolded : Definition.Unfolds terms definitions context (signature.symbol .andc)
      [first, second] [] (applySymbol signature.symbol .app [(applySymbol signature.symbol .app [(.term (profile.reference .conjunction)), first]), second]) := by
    refine .intro (signature.declared .andc) (profile.defined .conjunction) fitted (.nil _) ?_
    apply Preterm.substitute_sound
    simp [Operator.body, Definition.substitutionValues, applySymbol, Preterm.applyArgs,
      Preterm.substitute, Substitution.ofList]
  have operatorSorted : Preterm.HasType terms context (.term (profile.reference .conjunction)) [] signature.ids.object := by
    simpa [Operator.declaration] using Preterm.HasType.term (profile.declared .conjunction)
  have partialSorted := signature.application context .app [(.term (profile.reference .conjunction)), first]
    (.cons (.regular operatorSorted) (.cons (.regular firstSorted) .nil))
  have expandedSorted := signature.application context .app [(applySymbol signature.symbol .app [(.term (profile.reference .conjunction)), first]), second]
    (.cons (.regular partialSorted) (.cons (.regular secondSorted) .nil))
  exact ⟨.unfold (signature.symbol .andc) [first, second] [],
    .unfold (signature.declared .andc) unfolded expandedSorted⟩

def disjunctionUnfolding (signature : Signature sorts terms)
    (profile : Profile sorts terms definitions theorems signature)
    (first second : Preterm)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    : { witness : ConvWitness // ConvWitness.Checks terms definitions context witness
      (applySymbol signature.symbol .orc [first, second])
      (applySymbol signature.symbol .app [(applySymbol signature.symbol .app [(.term (profile.reference .disjunction)), first]), second]) signature.ids.object } := by
  have fitted : List.Forall₂ (Preterm.FitsBinder terms context) [first, second]
      ((Operator.constructor .disjunction).profile signature.ids).arguments := (.cons (.regular firstSorted) (.cons (.regular secondSorted) .nil))
  have unfolded : Definition.Unfolds terms definitions context (signature.symbol .orc)
      [first, second] [] (applySymbol signature.symbol .app [(applySymbol signature.symbol .app [(.term (profile.reference .disjunction)), first]), second]) := by
    refine .intro (signature.declared .orc) (profile.defined .disjunction) fitted (.nil _) ?_
    apply Preterm.substitute_sound
    simp [Operator.body, Definition.substitutionValues, applySymbol, Preterm.applyArgs,
      Preterm.substitute, Substitution.ofList]
  have operatorSorted : Preterm.HasType terms context (.term (profile.reference .disjunction)) [] signature.ids.object := by
    simpa [Operator.declaration] using Preterm.HasType.term (profile.declared .disjunction)
  have partialSorted := signature.application context .app [(.term (profile.reference .disjunction)), first]
    (.cons (.regular operatorSorted) (.cons (.regular firstSorted) .nil))
  have expandedSorted := signature.application context .app [(applySymbol signature.symbol .app [(.term (profile.reference .disjunction)), first]), second]
    (.cons (.regular partialSorted) (.cons (.regular secondSorted) .nil))
  exact ⟨.unfold (signature.symbol .orc) [first, second] [],
    .unfold (signature.declared .orc) unfolded expandedSorted⟩

def implicationUnfolding (signature : Signature sorts terms)
    (profile : Profile sorts terms definitions theorems signature)
    (first second : Preterm)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    : { witness : ConvWitness // ConvWitness.Checks terms definitions context witness
      (applySymbol signature.symbol .impc [first, second])
      (applySymbol signature.symbol .app [(applySymbol signature.symbol .app [(.term (profile.reference .implication)), first]), second]) signature.ids.object } := by
  have fitted : List.Forall₂ (Preterm.FitsBinder terms context) [first, second]
      ((Operator.constructor .implication).profile signature.ids).arguments := (.cons (.regular firstSorted) (.cons (.regular secondSorted) .nil))
  have unfolded : Definition.Unfolds terms definitions context (signature.symbol .impc)
      [first, second] [] (applySymbol signature.symbol .app [(applySymbol signature.symbol .app [(.term (profile.reference .implication)), first]), second]) := by
    refine .intro (signature.declared .impc) (profile.defined .implication) fitted (.nil _) ?_
    apply Preterm.substitute_sound
    simp [Operator.body, Definition.substitutionValues, applySymbol, Preterm.applyArgs,
      Preterm.substitute, Substitution.ofList]
  have operatorSorted : Preterm.HasType terms context (.term (profile.reference .implication)) [] signature.ids.object := by
    simpa [Operator.declaration] using Preterm.HasType.term (profile.declared .implication)
  have partialSorted := signature.application context .app [(.term (profile.reference .implication)), first]
    (.cons (.regular operatorSorted) (.cons (.regular firstSorted) .nil))
  have expandedSorted := signature.application context .app [(applySymbol signature.symbol .app [(.term (profile.reference .implication)), first]), second]
    (.cons (.regular partialSorted) (.cons (.regular secondSorted) .nil))
  exact ⟨.unfold (signature.symbol .impc) [first, second] [],
    .unfold (signature.declared .impc) unfolded expandedSorted⟩

def negationUnfolding (signature : Signature sorts terms)
    (profile : Profile sorts terms definitions theorems signature)
    (body : Preterm)
    (bodySorted : Preterm.HasType terms context body [] signature.ids.object)
    : { witness : ConvWitness // ConvWitness.Checks terms definitions context witness
      (applySymbol signature.symbol .notc [body])
      (applySymbol signature.symbol .app [(.term (profile.reference .negation)), body]) signature.ids.object } := by
  have fitted : List.Forall₂ (Preterm.FitsBinder terms context) [body]
      ((Operator.constructor .negation).profile signature.ids).arguments := (.cons (.regular bodySorted) .nil)
  have unfolded : Definition.Unfolds terms definitions context (signature.symbol .notc)
      [body] [] (applySymbol signature.symbol .app [(.term (profile.reference .negation)), body]) := by
    refine .intro (signature.declared .notc) (profile.defined .negation) fitted (.nil _) ?_
    apply Preterm.substitute_sound
    simp [Operator.body, Definition.substitutionValues, applySymbol, Preterm.applyArgs,
      Preterm.substitute, Substitution.ofList]
  have operatorSorted : Preterm.HasType terms context (.term (profile.reference .negation)) [] signature.ids.object := by
    simpa [Operator.declaration] using Preterm.HasType.term (profile.declared .negation)
  have expandedSorted := signature.application context .app [(.term (profile.reference .negation)), body]
    (.cons (.regular operatorSorted) (.cons (.regular bodySorted) .nil))
  exact ⟨.unfold (signature.symbol .notc) [body] [],
    .unfold (signature.declared .notc) unfolded expandedSorted⟩

def universalUnfolding (signature : Signature sorts terms)
    (profile : Profile sorts terms definitions theorems signature)
    (domain body : Preterm) (boundIndex : Nat)
    (bound : context[boundIndex]? = some (.bound signature.ids.object))
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (bodySorted : Preterm.HasType terms context body [] signature.ids.object)
    : { witness : ConvWitness // ConvWitness.Checks terms definitions context witness
      (applySymbol signature.symbol .allc [.var boundIndex, domain, body])
      (applySymbol signature.symbol .app [(.app (.term (profile.reference .universal)) domain), (applySymbol signature.symbol .lam [.var boundIndex, domain, body])]) signature.ids.object } := by
  have fitted : List.Forall₂ (Preterm.FitsBinder terms context) [.var boundIndex, domain, body]
      ((Operator.constructor .universal).profile signature.ids).arguments := (.cons (.bound bound) (.cons (.regular domainSorted) (.cons (.regular bodySorted) .nil)))
  have unfolded : Definition.Unfolds terms definitions context (signature.symbol .allc)
      [.var boundIndex, domain, body] [] (applySymbol signature.symbol .app [(.app (.term (profile.reference .universal)) domain), (applySymbol signature.symbol .lam [.var boundIndex, domain, body])]) := by
    refine .intro (signature.declared .allc) (profile.defined .universal) fitted (.nil _) ?_
    apply Preterm.substitute_sound
    simp [Operator.body, Definition.substitutionValues, applySymbol, Preterm.applyArgs,
      Preterm.substitute, Substitution.ofList]
  have operatorSorted : Preterm.HasType terms context (.app (.term (profile.reference .universal)) domain) [] signature.ids.object :=
    .regular (by simpa [Operator.declaration] using Preterm.HasType.term (profile.declared .universal))
      domainSorted
  have argumentSorted := signature.application context .lam
    [.var boundIndex, domain, body]
    (.cons (.bound bound) (.cons (.regular domainSorted) (.cons (.regular bodySorted) .nil)))
  have expandedSorted := signature.application context .app [(.app (.term (profile.reference .universal)) domain), (applySymbol signature.symbol .lam [.var boundIndex, domain, body])]
    (.cons (.regular operatorSorted) (.cons (.regular argumentSorted) .nil))
  exact ⟨.unfold (signature.symbol .allc) [.var boundIndex, domain, body] [],
    .unfold (signature.declared .allc) unfolded expandedSorted⟩

def existentialUnfolding (signature : Signature sorts terms)
    (profile : Profile sorts terms definitions theorems signature)
    (domain body : Preterm) (boundIndex : Nat)
    (bound : context[boundIndex]? = some (.bound signature.ids.object))
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (bodySorted : Preterm.HasType terms context body [] signature.ids.object)
    : { witness : ConvWitness // ConvWitness.Checks terms definitions context witness
      (applySymbol signature.symbol .exc [.var boundIndex, domain, body])
      (applySymbol signature.symbol .app [(.app (.term (profile.reference .existential)) domain), (applySymbol signature.symbol .lam [.var boundIndex, domain, body])]) signature.ids.object } := by
  have fitted : List.Forall₂ (Preterm.FitsBinder terms context) [.var boundIndex, domain, body]
      ((Operator.constructor .existential).profile signature.ids).arguments := (.cons (.bound bound) (.cons (.regular domainSorted) (.cons (.regular bodySorted) .nil)))
  have unfolded : Definition.Unfolds terms definitions context (signature.symbol .exc)
      [.var boundIndex, domain, body] [] (applySymbol signature.symbol .app [(.app (.term (profile.reference .existential)) domain), (applySymbol signature.symbol .lam [.var boundIndex, domain, body])]) := by
    refine .intro (signature.declared .exc) (profile.defined .existential) fitted (.nil _) ?_
    apply Preterm.substitute_sound
    simp [Operator.body, Definition.substitutionValues, applySymbol, Preterm.applyArgs,
      Preterm.substitute, Substitution.ofList]
  have operatorSorted : Preterm.HasType terms context (.app (.term (profile.reference .existential)) domain) [] signature.ids.object :=
    .regular (by simpa [Operator.declaration] using Preterm.HasType.term (profile.declared .existential))
      domainSorted
  have argumentSorted := signature.application context .lam
    [.var boundIndex, domain, body]
    (.cons (.bound bound) (.cons (.regular domainSorted) (.cons (.regular bodySorted) .nil)))
  have expandedSorted := signature.application context .app [(.app (.term (profile.reference .existential)) domain), (applySymbol signature.symbol .lam [.var boundIndex, domain, body])]
    (.cons (.regular operatorSorted) (.cons (.regular argumentSorted) .nil))
  exact ⟨.unfold (signature.symbol .exc) [.var boundIndex, domain, body] [],
    .unfold (signature.declared .exc) unfolded expandedSorted⟩

theorem unfolding_refused_without_body (signature : Signature sorts terms)
    (operator : Operator) (missing : Definition.Signature)
    (absent : missing (signature.symbol operator.constructor) = none) (arguments : List Preterm) :
    ConvWitness.conversion? terms missing context
      (.unfold (signature.symbol operator.constructor) arguments []) = none := by
  simp [ConvWitness.conversion?, Definition.unfold?, signature.declared, absent]

#print axioms unfolding_refused_without_body
#print axioms equalityTyping
#print axioms equalityUnfolding
#print axioms conjunctionTyping
#print axioms conjunctionUnfolding
#print axioms disjunctionTyping
#print axioms disjunctionUnfolding
#print axioms implicationTyping
#print axioms implicationUnfolding
#print axioms negationTyping
#print axioms negationUnfolding
#print axioms universalTyping
#print axioms universalUnfolding
#print axioms existentialTyping
#print axioms existentialUnfolding

end Mettapedia.Languages.MM0.HOLKernelLogicalOperationProofs
