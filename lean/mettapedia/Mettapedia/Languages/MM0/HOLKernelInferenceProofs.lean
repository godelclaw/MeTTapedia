import Mettapedia.Languages.MM0.HOLKernelInferenceRules
import Mettapedia.Languages.MM0.Kernel.RegularSubstitution
import Mettapedia.Languages.MM0.HOLKernelBooleanEquality

/-!
# Checked logical and equality inference in maintained MM0 HOL

The native constructions instantiate twenty-one actual theorem schemas,
retain their ordered child proofs, and prove the precise kernel-checking
judgments. Source Boolean equality is joined to the native equivalence
abbreviation by explicit checked definition conversions. No implicit
identification of the two presentations is used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelInferenceProofs

open Kernel HOLKernelSyntax HOLKernelJudgment
open HOLKernelTypingRules (typed boolType functionType)
open HOLKernelInferenceRules
open HOLKernelStructuralRules (CheckedProof)

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
variable {equivalenceReference : Nat}

namespace Native

def truth (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .truth []))) := by
  refine ⟨.theoremApp (rules.index .truth) [antecedent]
    [],
    .theoremApp (instantiation := ⟨[],
      entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .truth []))⟩) (rules.declared .truth) ?_
      .nil⟩
  refine ⟨?_, .nil, ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted .nil)
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, entails, holds, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def contradiction (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent conclusion : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (conclusionSorted : Preterm.HasType terms context conclusion [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (conclusion) (boolType signature.symbol)))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .falsity []))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (conclusion))) := by
  refine ⟨.theoremApp (rules.index .contradiction) [antecedent, conclusion]
    [premise0.val, premise1.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol (antecedent) (conclusion) (boolType signature.symbol),
      entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .falsity []))],
      entails signature.symbol (antecedent) (holds signature.symbol (conclusion))⟩) (rules.declared .contradiction) ?_
      (.cons premise0.property (.cons premise1.property .nil))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ .nil)), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons conclusionSorted .nil))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, typed, entails, holds, boolType, hasType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def conjunctionIntroduction (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (first))))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (second))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .andc [first, second]))) := by
  refine ⟨.theoremApp (rules.index .conjunctionIntroduction) [antecedent, first, second]
    [premise0.val, premise1.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (first)),
      entails signature.symbol (antecedent) (holds signature.symbol (second))],
      entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .andc [first, second]))⟩) (rules.declared .conjunctionIntroduction) ?_
      (.cons premise0.property (.cons premise1.property .nil))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ .nil)), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons firstSorted (.cons secondSorted .nil)))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, entails, holds, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def conjunctionLeft (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .andc [first, second]))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (first))) := by
  refine ⟨.theoremApp (rules.index .conjunctionLeft) [antecedent, first, second]
    [premise0.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .andc [first, second]))],
      entails signature.symbol (antecedent) (holds signature.symbol (first))⟩) (rules.declared .conjunctionLeft) ?_
      (.cons premise0.property .nil)⟩
  refine ⟨?_, (.cons ?_ .nil), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons firstSorted (.cons secondSorted .nil)))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, entails, holds, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def conjunctionRight (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .andc [first, second]))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (second))) := by
  refine ⟨.theoremApp (rules.index .conjunctionRight) [antecedent, first, second]
    [premise0.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .andc [first, second]))],
      entails signature.symbol (antecedent) (holds signature.symbol (second))⟩) (rules.declared .conjunctionRight) ?_
      (.cons premise0.property .nil)⟩
  refine ⟨?_, (.cons ?_ .nil), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons firstSorted (.cons secondSorted .nil)))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, entails, holds, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def disjunctionLeft (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (first))))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (second) (boolType signature.symbol)))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .orc [first, second]))) := by
  refine ⟨.theoremApp (rules.index .disjunctionLeft) [antecedent, first, second]
    [premise0.val, premise1.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (first)),
      typed signature.symbol (antecedent) (second) (boolType signature.symbol)],
      entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .orc [first, second]))⟩) (rules.declared .disjunctionLeft) ?_
      (.cons premise0.property (.cons premise1.property .nil))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ .nil)), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons firstSorted (.cons secondSorted .nil)))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, typed, entails, holds, boolType, hasType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def disjunctionRight (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (first) (boolType signature.symbol)))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (second))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .orc [first, second]))) := by
  refine ⟨.theoremApp (rules.index .disjunctionRight) [antecedent, first, second]
    [premise0.val, premise1.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol (antecedent) (first) (boolType signature.symbol),
      entails signature.symbol (antecedent) (holds signature.symbol (second))],
      entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .orc [first, second]))⟩) (rules.declared .disjunctionRight) ?_
      (.cons premise0.property (.cons premise1.property .nil))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ .nil)), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons firstSorted (.cons secondSorted .nil)))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, typed, entails, holds, boolType, hasType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def disjunctionElimination (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent first second conclusion : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (conclusionSorted : Preterm.HasType terms context conclusion [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .orc [first, second]))))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (conclusion) (boolType signature.symbol)))
    (premise2 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol (antecedent) (holds signature.symbol (first))) (holds signature.symbol (conclusion))))
    (premise3 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol (antecedent) (holds signature.symbol (second))) (holds signature.symbol (conclusion))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (conclusion))) := by
  refine ⟨.theoremApp (rules.index .disjunctionElimination) [antecedent, first, second, conclusion]
    [premise0.val, premise1.val, premise2.val, premise3.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .orc [first, second])),
      typed signature.symbol (antecedent) (conclusion) (boolType signature.symbol),
      entails signature.symbol (conjunction signature.symbol (antecedent) (holds signature.symbol (first))) (holds signature.symbol (conclusion)),
      entails signature.symbol (conjunction signature.symbol (antecedent) (holds signature.symbol (second))) (holds signature.symbol (conclusion))],
      entails signature.symbol (antecedent) (holds signature.symbol (conclusion))⟩) (rules.declared .disjunctionElimination) ?_
      (.cons premise0.property (.cons premise1.property (.cons premise2.property (.cons premise3.property .nil))))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons firstSorted (.cons secondSorted (.cons conclusionSorted .nil))))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, typed, entails, holds, conjunction, boolType, hasType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def implicationIntroduction (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (first) (boolType signature.symbol)))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (second) (boolType signature.symbol)))
    (premise2 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol (antecedent) (holds signature.symbol (first))) (holds signature.symbol (second))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .impc [first, second]))) := by
  refine ⟨.theoremApp (rules.index .implicationIntroduction) [antecedent, first, second]
    [premise0.val, premise1.val, premise2.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol (antecedent) (first) (boolType signature.symbol),
      typed signature.symbol (antecedent) (second) (boolType signature.symbol),
      entails signature.symbol (conjunction signature.symbol (antecedent) (holds signature.symbol (first))) (holds signature.symbol (second))],
      entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .impc [first, second]))⟩) (rules.declared .implicationIntroduction) ?_
      (.cons premise0.property (.cons premise1.property (.cons premise2.property .nil)))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ (.cons ?_ .nil))), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons firstSorted (.cons secondSorted .nil)))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, typed, entails, holds, conjunction, boolType, hasType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def implicationElimination (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .impc [first, second]))))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (first))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (second))) := by
  refine ⟨.theoremApp (rules.index .implicationElimination) [antecedent, first, second]
    [premise0.val, premise1.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .impc [first, second])),
      entails signature.symbol (antecedent) (holds signature.symbol (first))],
      entails signature.symbol (antecedent) (holds signature.symbol (second))⟩) (rules.declared .implicationElimination) ?_
      (.cons premise0.property (.cons premise1.property .nil))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ .nil)), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons firstSorted (.cons secondSorted .nil)))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, entails, holds, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def negationIntroduction (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent formula : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (formulaSorted : Preterm.HasType terms context formula [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .impc [formula, applySymbol signature.symbol .falsity []]))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .notc [formula]))) := by
  refine ⟨.theoremApp (rules.index .negationIntroduction) [antecedent, formula]
    [premise0.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .impc [formula, applySymbol signature.symbol .falsity []]))],
      entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .notc [formula]))⟩) (rules.declared .negationIntroduction) ?_
      (.cons premise0.property .nil)⟩
  refine ⟨?_, (.cons ?_ .nil), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons formulaSorted .nil))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, entails, holds, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def negationElimination (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent formula : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (formulaSorted : Preterm.HasType terms context formula [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .notc [formula]))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .impc [formula, applySymbol signature.symbol .falsity []]))) := by
  refine ⟨.theoremApp (rules.index .negationElimination) [antecedent, formula]
    [premise0.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .notc [formula]))],
      entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .impc [formula, applySymbol signature.symbol .falsity []]))⟩) (rules.declared .negationElimination) ?_
      (.cons premise0.property .nil)⟩
  refine ⟨?_, (.cons ?_ .nil), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons formulaSorted .nil))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, entails, holds, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def reflexivity (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent type term : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (typeSorted : Preterm.HasType terms context type [] signature.ids.type)
    (termSorted : Preterm.HasType terms context term [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (term) (type)))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (type) (term) (term)))) := by
  refine ⟨.theoremApp (rules.index .reflexivity) [antecedent, type, term]
    [premise0.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol (antecedent) (term) (type)],
      entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (type) (term) (term)))⟩) (rules.declared .reflexivity) ?_
      (.cons premise0.property .nil)⟩
  refine ⟨?_, (.cons ?_ .nil), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.type, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons typeSorted (.cons termSorted .nil)))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equality, typed, entails, holds, hasType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def symmetry (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (type antecedent first second : Preterm)
    (typeSorted : Preterm.HasType terms context type [] signature.ids.type)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (type) (first) (second)))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (type) (second) (first)))) := by
  refine ⟨.theoremApp (rules.index .symmetry) [type, antecedent, first, second]
    [premise0.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (type) (first) (second)))],
      entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (type) (second) (first)))⟩) (rules.declared .symmetry) ?_
      (.cons premise0.property .nil)⟩
  refine ⟨?_, (.cons ?_ .nil), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.type, signature.ids.wff, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons typeSorted (.cons antecedentSorted (.cons firstSorted (.cons secondSorted .nil))))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equality, entails, holds, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def transitivity (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent type first middle last : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (typeSorted : Preterm.HasType terms context type [] signature.ids.type)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (middleSorted : Preterm.HasType terms context middle [] signature.ids.object)
    (lastSorted : Preterm.HasType terms context last [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (type) (first) (middle)))))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (type) (middle) (last)))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (type) (first) (last)))) := by
  refine ⟨.theoremApp (rules.index .transitivity) [antecedent, type, first, middle, last]
    [premise0.val, premise1.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (type) (first) (middle))),
      entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (type) (middle) (last)))],
      entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (type) (first) (last)))⟩) (rules.declared .transitivity) ?_
      (.cons premise0.property (.cons premise1.property .nil))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ .nil)), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.type, signature.ids.object, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons typeSorted (.cons firstSorted (.cons middleSorted (.cons lastSorted .nil)))))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equality, entails, holds, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def propositionalExtensionality (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .impc [first, second]))))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .impc [second, first]))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equivalence equivalenceReference (first) (second)))) := by
  refine ⟨.theoremApp (rules.index .propositionalExtensionality) [antecedent, first, second]
    [premise0.val, premise1.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .impc [first, second])),
      entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .impc [second, first]))],
      entails signature.symbol (antecedent) (holds signature.symbol (equivalence equivalenceReference (first) (second)))⟩) (rules.declared .propositionalExtensionality) ?_
      (.cons premise0.property (.cons premise1.property .nil))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ .nil)), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons firstSorted (.cons secondSorted .nil)))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equivalence, entails, holds, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def equalityImplicationLeft (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equivalence equivalenceReference (first) (second)))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .impc [first, second]))) := by
  refine ⟨.theoremApp (rules.index .equalityImplicationLeft) [antecedent, first, second]
    [premise0.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (equivalence equivalenceReference (first) (second)))],
      entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .impc [first, second]))⟩) (rules.declared .equalityImplicationLeft) ?_
      (.cons premise0.property .nil)⟩
  refine ⟨?_, (.cons ?_ .nil), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons firstSorted (.cons secondSorted .nil)))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equivalence, entails, holds, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def equalityImplicationRight (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equivalence equivalenceReference (first) (second)))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .impc [second, first]))) := by
  refine ⟨.theoremApp (rules.index .equalityImplicationRight) [antecedent, first, second]
    [premise0.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (equivalence equivalenceReference (first) (second)))],
      entails signature.symbol (antecedent) (holds signature.symbol (applySymbol signature.symbol .impc [second, first]))⟩) (rules.declared .equalityImplicationRight) ?_
      (.cons premise0.property .nil)⟩
  refine ⟨?_, (.cons ?_ .nil), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons firstSorted (.cons secondSorted .nil)))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equivalence, entails, holds, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def applicationFunction (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (domain result antecedent argument first second : Preterm)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.type)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (argumentSorted : Preterm.HasType terms context argument [] signature.ids.object)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (functionType signature.symbol (domain) (result)) (first) (second)))))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (argument) (domain)))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (result) (applySymbol signature.symbol .app [first, argument]) (applySymbol signature.symbol .app [second, argument])))) := by
  refine ⟨.theoremApp (rules.index .applicationFunction) [domain, result, antecedent, argument, first, second]
    [premise0.val, premise1.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (functionType signature.symbol (domain) (result)) (first) (second))),
      typed signature.symbol (antecedent) (argument) (domain)],
      entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (result) (applySymbol signature.symbol .app [first, argument]) (applySymbol signature.symbol .app [second, argument])))⟩) (rules.declared .applicationFunction) ?_
      (.cons premise0.property (.cons premise1.property .nil))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ .nil)), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.type, signature.ids.type, signature.ids.wff, signature.ids.object, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons domainSorted (.cons resultSorted (.cons antecedentSorted (.cons argumentSorted (.cons firstSorted (.cons secondSorted .nil))))))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equality, typed, entails, holds, functionType, hasType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def applicationArgument (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (domain result antecedent first second function : Preterm)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (resultSorted : Preterm.HasType terms context result [] signature.ids.type)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (functionSorted : Preterm.HasType terms context function [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol (antecedent) (function) (functionType signature.symbol (domain) (result))))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (domain) (first) (second)))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (result) (applySymbol signature.symbol .app [function, first]) (applySymbol signature.symbol .app [function, second])))) := by
  refine ⟨.theoremApp (rules.index .applicationArgument) [domain, result, antecedent, first, second, function]
    [premise0.val, premise1.val],
    .theoremApp (instantiation := ⟨[typed signature.symbol (antecedent) (function) (functionType signature.symbol (domain) (result)),
      entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (domain) (first) (second)))],
      entails signature.symbol (antecedent) (holds signature.symbol (equality signature.symbol (result) (applySymbol signature.symbol .app [function, first]) (applySymbol signature.symbol .app [function, second])))⟩) (rules.declared .applicationArgument) ?_
      (.cons premise0.property (.cons premise1.property .nil))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ .nil)), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.type, signature.ids.type, signature.ids.wff, signature.ids.object, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons domainSorted (.cons resultSorted (.cons antecedentSorted (.cons firstSorted (.cons secondSorted (.cons functionSorted .nil))))))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equality, typed, entails, holds, functionType, hasType, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

def booleanEqualityElimination (signature : Signature sorts terms)
    (rules : Rules theorems signature.symbol signature.ids equivalenceReference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (premise0 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (equivalence equivalenceReference (first) (second)))))
    (premise1 : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (first))))
    : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (antecedent) (holds signature.symbol (second))) := by
  refine ⟨.theoremApp (rules.index .booleanEqualityElimination) [antecedent, first, second]
    [premise0.val, premise1.val],
    .theoremApp (instantiation := ⟨[entails signature.symbol (antecedent) (holds signature.symbol (equivalence equivalenceReference (first) (second))),
      entails signature.symbol (antecedent) (holds signature.symbol (first))],
      entails signature.symbol (antecedent) (holds signature.symbol (second))⟩) (rules.declared .booleanEqualityElimination) ?_
      (.cons premise0.property (.cons premise1.property .nil))⟩
  refine ⟨?_, (.cons ?_ (.cons ?_ .nil)), ?_⟩
  · change Substitution.Admissible terms
      ([signature.ids.wff, signature.ids.object, signature.ids.object].map (fun sort => .regular sort ∅)) context _
    exact Substitution.admissible_regular (.cons antecedentSorted (.cons firstSorted (.cons secondSorted .nil)))
  all_goals
    apply Preterm.substitute_sound
    simp [Rule.declaration, equivalence, entails, holds, applySymbol, Preterm.applyArgs, Preterm.substitute, Substitution.ofList]

end Native

def propositionalExtensionality (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (rules : Rules theorems signature.symbol signature.ids abbreviation.reference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (forward : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (applySymbol signature.symbol .impc [first, second]))))
    (backward : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (applySymbol signature.symbol .impc [second, first])))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent
        (holds signature.symbol (equality signature.symbol (boolType signature.symbol) first second))) :=
  HOLKernelBooleanEquality.expandProof signature abbreviation antecedent first second
    antecedentSorted firstSorted secondSorted
    (Native.propositionalExtensionality signature rules antecedent first second
      antecedentSorted firstSorted secondSorted forward backward)

def equalityImplicationLeft (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (rules : Rules theorems signature.symbol signature.ids abbreviation.reference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent
        (holds signature.symbol (equality signature.symbol (boolType signature.symbol) first second)))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent
        (holds signature.symbol (applySymbol signature.symbol .impc [first, second]))) :=
  Native.equalityImplicationLeft signature rules antecedent first second
    antecedentSorted firstSorted secondSorted
    (HOLKernelBooleanEquality.contractProof signature abbreviation antecedent first second
      antecedentSorted firstSorted secondSorted source)

def equalityImplicationRight (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (rules : Rules theorems signature.symbol signature.ids abbreviation.reference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent
        (holds signature.symbol (equality signature.symbol (boolType signature.symbol) first second)))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent
        (holds signature.symbol (applySymbol signature.symbol .impc [second, first]))) :=
  Native.equalityImplicationRight signature rules antecedent first second
    antecedentSorted firstSorted secondSorted
    (HOLKernelBooleanEquality.contractProof signature abbreviation antecedent first second
      antecedentSorted firstSorted secondSorted source)

def booleanEqualityElimination (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (rules : Rules theorems signature.symbol signature.ids abbreviation.reference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (equal : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent
        (holds signature.symbol (equality signature.symbol (boolType signature.symbol) first second))))
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol first))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol second)) :=
  Native.booleanEqualityElimination signature rules antecedent first second
    antecedentSorted firstSorted secondSorted
    (HOLKernelBooleanEquality.contractProof signature abbreviation antecedent first second
      antecedentSorted firstSorted secondSorted equal) source

#print axioms Native.truth
#print axioms Native.contradiction
#print axioms Native.conjunctionIntroduction
#print axioms Native.conjunctionLeft
#print axioms Native.conjunctionRight
#print axioms Native.disjunctionLeft
#print axioms Native.disjunctionRight
#print axioms Native.disjunctionElimination
#print axioms Native.implicationIntroduction
#print axioms Native.implicationElimination
#print axioms Native.negationIntroduction
#print axioms Native.negationElimination
#print axioms Native.reflexivity
#print axioms Native.symmetry
#print axioms Native.transitivity
#print axioms Native.propositionalExtensionality
#print axioms Native.equalityImplicationLeft
#print axioms Native.equalityImplicationRight
#print axioms Native.applicationFunction
#print axioms Native.applicationArgument
#print axioms Native.booleanEqualityElimination
#print axioms propositionalExtensionality
#print axioms equalityImplicationLeft
#print axioms equalityImplicationRight
#print axioms booleanEqualityElimination

theorem booleanEqualityElimination_varsBelow (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (rules : Rules theorems signature.symbol signature.ids abbreviation.reference)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (equal : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent
        (holds signature.symbol (equality signature.symbol (boolType signature.symbol) first second))))
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol first)))
    (limit : Nat)
    (antecedentBound : Preterm.VarsBelow limit antecedent)
    (firstBound : Preterm.VarsBelow limit first)
    (secondBound : Preterm.VarsBelow limit second)
    (equalBound : equal.val.VarsBelow limit)
    (sourceBound : source.val.VarsBelow limit) :
    (booleanEqualityElimination signature abbreviation rules antecedent first second antecedentSorted firstSorted secondSorted equal source).val.VarsBelow limit := by
  simp_all [booleanEqualityElimination, ProofWitness.VarsBelow, ConvWitness.VarsBelow, Native.booleanEqualityElimination, HOLKernelBooleanEquality.contractProof, HOLKernelBooleanEquality.consequenceConversion, HOLKernelBooleanEquality.unfolding]


end Mettapedia.Languages.MM0.HOLKernelInferenceProofs
