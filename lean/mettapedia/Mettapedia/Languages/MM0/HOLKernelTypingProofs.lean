import Mettapedia.Languages.MM0.HOLKernelTypingRules

/-!
# Checked HOL typing proofs in the maintained MM0 theory

Each construction returns a native proof witness with its exact object-typing
conclusion. Applications retain the declaration's argument order and ordered
premise proofs. Abstraction and quantification require complete occurrence
independence of their context and type arguments from the bound variable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelTypingProofs

open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTypingRules
open HOLKernelStructuralRules (CheckedProof)

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}

def applicationTyping (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids)
    (antecedent domain result function argument : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.type)
    (functionSorted : Preterm.HasType terms context function [] signature.ids.object)
    (argumentSorted : Preterm.HasType terms context argument [] signature.ids.object)
    (functionProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent function (functionType signature.symbol domain result)))
    (argumentProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses) (typed signature.symbol antecedent argument domain)) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent (applySymbol signature.symbol .app [function, argument]) result) := by
  refine ⟨.theoremApp (rules.index .appT) [antecedent, domain, result, function, argument]
    [functionProof.val, argumentProof.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol antecedent function
      (functionType signature.symbol domain result), typed signature.symbol antecedent argument domain],
      typed signature.symbol antecedent (applySymbol signature.symbol .app [function, argument]) result⟩)
      (rules.declared .appT) ?_ (.cons functionProof.property (.cons argumentProof.property .nil))⟩
  refine ⟨?_, .cons ?_ (.cons ?_ .nil), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.type, signature.ids.type, signature.ids.object,
        signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons domainSorted
      (.cons resultSorted (.cons functionSorted (.cons argumentSorted .nil)))))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, typed, entails, hasType, functionType, applySymbol,
      Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def abstractionTyping (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids)
    (antecedent domain result body : Preterm) (boundIndex : Nat)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.type)
    (bound : context[boundIndex]? = some (.bound signature.ids.object))
    (bodySorted : Preterm.HasType terms context body [] signature.ids.object)
    (antecedentIndependent : ¬ Preterm.HasVar context boundIndex antecedent)
    (domainIndependent : ¬ Preterm.HasVar context boundIndex domain)
    (resultIndependent : ¬ Preterm.HasVar context boundIndex result)
    (bodyProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (conjunction signature.symbol antecedent
        (hasType signature.symbol (.var boundIndex) domain)) body result)) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent
        (applySymbol signature.symbol .lam [.var boundIndex, domain, body])
        (functionType signature.symbol domain result)) := by
  refine ⟨.theoremApp (rules.index .lamT) [antecedent, domain, result, .var boundIndex, body]
    [bodyProof.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol
      (conjunction signature.symbol antecedent (hasType signature.symbol (.var boundIndex) domain))
      body result], typed signature.symbol antecedent
      (applySymbol signature.symbol .lam [.var boundIndex, domain, body])
      (functionType signature.symbol domain result)⟩)
      (rules.declared .lamT) ?_ (.cons bodyProof.property .nil)⟩
  refine ⟨?_, .cons ?_ .nil, ?_⟩
  · exact Substitution.admissible_single_bound_after_three antecedent domain result body
      signature.ids.wff signature.ids.type signature.ids.type signature.ids.object boundIndex
      antecedentSorted domainSorted resultSorted bound bodySorted
      antecedentIndependent domainIndependent resultIndependent
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, typed, entails, hasType, conjunction, functionType, applySymbol,
      Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

private def constantTyping (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids)
    (rule : Rule) (symbol : Symbol)
    (schema : rule.declaration signature.symbol signature.ids =
      ⟨[.regular signature.ids.wff ∅], [],
        typed signature.symbol (.var 0) (applySymbol signature.symbol symbol [])
          (boolType signature.symbol)⟩)
    (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent (applySymbol signature.symbol symbol [])
        (boolType signature.symbol)) := by
  refine ⟨.theoremApp (rules.index rule) [antecedent] [],
    .theoremApp (instantiation := ⟨[], typed signature.symbol antecedent
      (applySymbol signature.symbol symbol []) (boolType signature.symbol)⟩)
      ((rules.declared rule).trans (congrArg some schema)) ?_ .nil⟩
  refine ⟨?_, .nil, ?_⟩
  · exact Substitution.admissible_regular (.cons antecedentSorted .nil)
  · apply Preterm.substitute_sound
    simp [typed, entails, hasType, boolType, applySymbol, Preterm.applyArgs,
      Preterm.substitute, Substitution.ofList]

def truthTyping (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids)
    (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff) :=
  constantTyping (definitions := definitions) (hypotheses := hypotheses)
    signature rules .truth .truth rfl antecedent antecedentSorted

def falsityTyping (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids)
    (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff) :=
  constantTyping (definitions := definitions) (hypotheses := hypotheses)
    signature rules .falsity .falsity rfl antecedent antecedentSorted

private def binaryTyping (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids)
    (rule : Rule) (symbol : Symbol)
    (schema : rule.declaration signature.symbol signature.ids = binaryDeclaration signature.symbol signature.ids symbol)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (firstProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent first (boolType signature.symbol)))
    (secondProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent second (boolType signature.symbol))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent (applySymbol signature.symbol symbol [first, second])
        (boolType signature.symbol)) := by
  refine ⟨.theoremApp (rules.index rule) [antecedent, first, second] [firstProof.val, secondProof.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol antecedent first (boolType signature.symbol),
      typed signature.symbol antecedent second (boolType signature.symbol)],
      typed signature.symbol antecedent (applySymbol signature.symbol symbol [first, second])
        (boolType signature.symbol)⟩)
      ((rules.declared rule).trans (congrArg some schema)) ?_
        (.cons firstProof.property (.cons secondProof.property .nil))⟩
  refine ⟨?_, .cons ?_ (.cons ?_ .nil), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons firstSorted (.cons secondSorted .nil)))
  all_goals
    apply Preterm.substitute_sound
    simp [binaryDeclaration, typed, entails, hasType, boolType, applySymbol,
      Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def conjunctionTyping (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids) :=
  binaryTyping (definitions := definitions) (context := context) (hypotheses := hypotheses)
    signature rules .andcT .andc rfl

def disjunctionTyping (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids) :=
  binaryTyping (definitions := definitions) (context := context) (hypotheses := hypotheses)
    signature rules .orcT .orc rfl

def implicationTyping (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids) :=
  binaryTyping (definitions := definitions) (context := context) (hypotheses := hypotheses)
    signature rules .impcT .impc rfl

def negationTyping (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids)
    (antecedent body : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (bodySorted : Preterm.HasType terms context body [] signature.ids.object)
    (bodyProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent body (boolType signature.symbol))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent (applySymbol signature.symbol .notc [body])
        (boolType signature.symbol)) := by
  refine ⟨.theoremApp (rules.index .notcT) [antecedent, body] [bodyProof.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol antecedent body (boolType signature.symbol)],
      typed signature.symbol antecedent (applySymbol signature.symbol .notc [body]) (boolType signature.symbol)⟩)
      (rules.declared .notcT) ?_ (.cons bodyProof.property .nil)⟩
  refine ⟨?_, .cons ?_ .nil, ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons bodySorted .nil))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, typed, entails, hasType, boolType, applySymbol,
      Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def equalityTyping (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids)
    (type antecedent first second : Preterm)
    (typeSorted : Preterm.HasType terms context type [] signature.ids.type)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (firstProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses) (typed signature.symbol antecedent first type))
    (secondProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses) (typed signature.symbol antecedent second type)) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent (applySymbol signature.symbol .eqc [type, first, second])
        (boolType signature.symbol)) := by
  refine ⟨.theoremApp (rules.index .eqcT) [type, antecedent, first, second] [firstProof.val, secondProof.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol antecedent first type,
      typed signature.symbol antecedent second type], typed signature.symbol antecedent
      (applySymbol signature.symbol .eqc [type, first, second]) (boolType signature.symbol)⟩)
      (rules.declared .eqcT) ?_ (.cons firstProof.property (.cons secondProof.property .nil))⟩
  refine ⟨?_, .cons ?_ (.cons ?_ .nil), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.type, signature.ids.wff, signature.ids.object, signature.ids.object].map
        (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular
      (.cons typeSorted (.cons antecedentSorted (.cons firstSorted (.cons secondSorted .nil))))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, typed, entails, hasType, boolType, applySymbol,
      Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

private def quantifierTyping (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids)
    (rule : Rule) (symbol : Symbol)
    (schema : rule.declaration signature.symbol signature.ids = quantifierDeclaration signature.symbol signature.ids symbol)
    (domain antecedent body : Preterm) (boundIndex : Nat)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (bound : context[boundIndex]? = some (.bound signature.ids.object))
    (bodySorted : Preterm.HasType terms context body [] signature.ids.object)
    (domainIndependent : ¬ Preterm.HasVar context boundIndex domain)
    (antecedentIndependent : ¬ Preterm.HasVar context boundIndex antecedent)
    (bodyProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (conjunction signature.symbol antecedent
        (hasType signature.symbol (.var boundIndex) domain)) body (boolType signature.symbol))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent
        (applySymbol signature.symbol symbol [.var boundIndex, domain, body]) (boolType signature.symbol)) := by
  refine ⟨.theoremApp (rules.index rule) [domain, antecedent, .var boundIndex, body] [bodyProof.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol
      (conjunction signature.symbol antecedent (hasType signature.symbol (.var boundIndex) domain))
      body (boolType signature.symbol)], typed signature.symbol antecedent
      (applySymbol signature.symbol symbol [.var boundIndex, domain, body]) (boolType signature.symbol)⟩)
      ((rules.declared rule).trans (congrArg some schema)) ?_ (.cons bodyProof.property .nil)⟩
  refine ⟨?_, .cons ?_ .nil, ?_⟩
  · exact Substitution.admissible_single_bound_after_two domain antecedent body
      signature.ids.type signature.ids.wff signature.ids.object boundIndex
      domainSorted antecedentSorted bound bodySorted domainIndependent antecedentIndependent
  all_goals
    apply Preterm.substitute_sound
    simp [quantifierDeclaration, typed, entails, hasType, conjunction, boolType, applySymbol,
      Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def universalTyping (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids) :=
  quantifierTyping (definitions := definitions) (context := context) (hypotheses := hypotheses)
    signature rules .allcT .allc rfl

def existentialTyping (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids) :=
  quantifierTyping (definitions := definitions) (context := context) (hypotheses := hypotheses)
    signature rules .excT .exc rfl

#print axioms applicationTyping
#print axioms abstractionTyping
#print axioms truthTyping
#print axioms falsityTyping
#print axioms conjunctionTyping
#print axioms disjunctionTyping
#print axioms implicationTyping
#print axioms negationTyping
#print axioms equalityTyping
#print axioms universalTyping
#print axioms existentialTyping

end Mettapedia.Languages.MM0.HOLKernelTypingProofs
