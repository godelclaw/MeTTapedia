import Mettapedia.Languages.MM0.HOLKernelStructuralRules

/-!
# Checked unfolding of the maintained Boolean-equality abbreviation

The maintained HOL presentation uses `bi` in several rule headers. The
intrinsic HOL encoding uses equality at the Boolean type. The abbreviation's
actual declared arguments and stored definition body justify conversion
between these two native expressions, including inside an asserted
consequence. Neither a matching constructor profile nor an unrelated
propositional equality supplies this definition-unfolding authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelBooleanEquality

open Kernel HOLKernelSyntax HOLKernelJudgment
open HOLKernelStructuralRules (CheckedProof)

def declaration (ids : SortIds) : TermDecl :=
  ⟨[.regular ids.object ∅, .regular ids.object ∅], ids.object, ∅⟩

def expanded (references : Symbol → Nat) (first second : Preterm) : Preterm :=
  applySymbol references .eqc [applySymbol references .bool [], first, second]

def body (references : Symbol → Nat) : Definition.Body :=
  ⟨[], expanded references (.var 0) (.var 1)⟩

structure Abbreviation (terms : TermSignature) (definitions : Definition.Signature)
    (references : Symbol → Nat) (ids : SortIds) where
  reference : Nat
  declared : terms reference = some (declaration ids)
  defined : definitions reference = some (body references)

def Abbreviation.read? (terms : TermSignature) (definitions : Definition.Signature)
    (references : Symbol → Nat) (ids : SortIds) (reference : Nat) :
    Option (Abbreviation terms definitions references ids) :=
  if declared : terms reference = some (declaration ids) then
    if defined : definitions reference = some (body references) then
      some ⟨reference, declared, defined⟩
    else none
  else none

def code {terms : TermSignature} {definitions : Definition.Signature}
    {references : Symbol → Nat} {ids : SortIds}
    (abbreviation : Abbreviation terms definitions references ids) (first second : Preterm) : Preterm :=
  Preterm.applyArgs (.term abbreviation.reference) [first, second]

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}

theorem expanded_sorted (signature : Signature sorts terms) (first second : Preterm)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object) :
    Preterm.HasType terms context (expanded signature.symbol first second) [] signature.ids.object :=
  signature.application context .eqc _
    (.cons (.regular (signature.application context .bool [] .nil))
      (.cons (.regular firstSorted) (.cons (.regular secondSorted) .nil)))

theorem code_sorted (signature : Signature sorts terms)
    (abbreviation : Abbreviation terms definitions signature.symbol signature.ids) (first second : Preterm)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object) :
    Preterm.HasType terms context (code abbreviation first second) [] signature.ids.object := by
  apply (Preterm.HasType.applyArgs_iff terms context _ _ _ _).mpr
  exact ⟨(declaration signature.ids).arguments,
    by simpa [declaration] using Preterm.HasType.term abbreviation.declared,
    .cons (.regular firstSorted) (.cons (.regular secondSorted) .nil)⟩

theorem unfolds (signature : Signature sorts terms)
    (abbreviation : Abbreviation terms definitions signature.symbol signature.ids) (first second : Preterm)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object) :
    Definition.Unfolds terms definitions context abbreviation.reference [first, second] []
      (expanded signature.symbol first second) := by
  refine .intro abbreviation.declared abbreviation.defined
    (.cons (.regular firstSorted) (.cons (.regular secondSorted) .nil)) (.nil _) ?_
  apply Preterm.substitute_sound
  simp [body, expanded, Definition.substitutionValues, applySymbol, Preterm.applyArgs,
    Preterm.substitute, Substitution.ofList]

def unfolding (signature : Signature sorts terms)
    (abbreviation : Abbreviation terms definitions signature.symbol signature.ids) (first second : Preterm)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object) :
    { witness : ConvWitness // ConvWitness.Checks terms definitions context witness
      (code abbreviation first second) (expanded signature.symbol first second) signature.ids.object } :=
  ⟨.unfold abbreviation.reference [first, second] [],
    .unfold abbreviation.declared (unfolds signature abbreviation first second firstSorted secondSorted)
      (expanded_sorted signature first second firstSorted secondSorted)⟩

def consequenceConversion (signature : Signature sorts terms)
    (abbreviation : Abbreviation terms definitions signature.symbol signature.ids)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object) :
    { witness : ConvWitness // ConvWitness.Checks terms definitions context witness
      (entails signature.symbol antecedent (holds signature.symbol (code abbreviation first second)))
      (entails signature.symbol antecedent (holds signature.symbol (expanded signature.symbol first second)))
      signature.ids.wff } := by
  let inner := unfolding signature abbreviation first second firstSorted secondSorted
  have leftSorted := code_sorted signature abbreviation first second firstSorted secondSorted
  have rightSorted := expanded_sorted signature first second firstSorted secondSorted
  let asserted : ConvWitness := .congruence (signature.symbol .thm) [inner.val]
  have assertedChecked : ConvWitness.Checks terms definitions context asserted
      (holds signature.symbol (code abbreviation first second))
      (holds signature.symbol (expanded signature.symbol first second)) signature.ids.wff :=
    .congruence (signature.declared .thm)
      (.cons (.regular leftSorted) (.regular rightSorted) inner.property .nil)
  exact ⟨.congruence (signature.symbol .im) [.refl antecedent, asserted],
    .congruence (signature.declared .im)
      (.cons (.regular antecedentSorted) (.regular antecedentSorted) (.refl antecedentSorted)
        (.cons (.regular (holds_sorted signature context leftSorted))
          (.regular (holds_sorted signature context rightSorted)) assertedChecked .nil))⟩

def expandProof (signature : Signature sorts terms)
    (abbreviation : Abbreviation terms definitions signature.symbol signature.ids)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (code abbreviation first second)))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (expanded signature.symbol first second))) := by
  let converted := consequenceConversion signature abbreviation antecedent first second
    antecedentSorted firstSorted secondSorted
  exact ⟨.conversion converted.val source.val, .conversion converted.property source.property⟩

def contractProof (signature : Signature sorts terms)
    (abbreviation : Abbreviation terms definitions signature.symbol signature.ids)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (expanded signature.symbol first second)))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (code abbreviation first second))) := by
  let converted := consequenceConversion signature abbreviation antecedent first second
    antecedentSorted firstSorted secondSorted
  exact ⟨.conversion (.symm converted.val) source.val,
    .conversion (.symm converted.property) source.property⟩

theorem unfolding_refused_without_body (signature : Signature sorts terms)
    (abbreviation : Abbreviation terms definitions signature.symbol signature.ids)
    (missing : Definition.Signature) (absent : missing abbreviation.reference = none) (first second : Preterm) :
    ConvWitness.conversion? terms missing context (.unfold abbreviation.reference [first, second] []) = none := by
  simp [ConvWitness.conversion?, Definition.unfold?, abbreviation.declared, absent]

#print axioms Abbreviation.read?
#print axioms expanded_sorted
#print axioms code_sorted
#print axioms unfolds
#print axioms unfolding
#print axioms consequenceConversion
#print axioms expandProof
#print axioms contractProof
#print axioms unfolding_refused_without_body

theorem expandProof_varsBelow (signature : Signature sorts terms)
    (abbreviation : Abbreviation terms definitions signature.symbol signature.ids)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (code abbreviation first second))))
    (limit : Nat)
    (antecedentBound : Preterm.VarsBelow limit antecedent)
    (firstBound : Preterm.VarsBelow limit first)
    (secondBound : Preterm.VarsBelow limit second)
    (sourceBound : source.val.VarsBelow limit) :
    (expandProof signature abbreviation antecedent first second antecedentSorted firstSorted secondSorted source).val.VarsBelow limit := by
  simp_all [expandProof, ProofWitness.VarsBelow, ConvWitness.VarsBelow, consequenceConversion, unfolding]

theorem contractProof_varsBelow (signature : Signature sorts terms)
    (abbreviation : Abbreviation terms definitions signature.symbol signature.ids)
    (antecedent first second : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (source : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol (expanded signature.symbol first second))))
    (limit : Nat)
    (antecedentBound : Preterm.VarsBelow limit antecedent)
    (firstBound : Preterm.VarsBelow limit first)
    (secondBound : Preterm.VarsBelow limit second)
    (sourceBound : source.val.VarsBelow limit) :
    (contractProof signature abbreviation antecedent first second antecedentSorted firstSorted secondSorted source).val.VarsBelow limit := by
  simp_all [contractProof, ProofWitness.VarsBelow, ConvWitness.VarsBelow, consequenceConversion, unfolding]


end Mettapedia.Languages.MM0.HOLKernelBooleanEquality
