import Mettapedia.Languages.MM0.HOLKernelJudgment

/-!
# Occurrence independence of HOL type interpretations in MM0

Simple types introduce no object binding positions. Their complete MM0
occurrence support is inherited from the supplied base-type codes. Logical
context extension retains independence from a distinct future bound slot.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelTypeSupport

open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment

universe u
variable {Base : Type u}

theorem applySymbol_independent (context : Context) (index : Nat)
    (references : Symbol → Nat) (symbol : Symbol) (arguments : List Preterm)
    (independent : ∀ argument ∈ arguments, ¬ Preterm.HasVar context index argument) :
    ¬ Preterm.HasVar context index (applySymbol references symbol arguments) := by
  rw [applySymbol, Preterm.hasVar_applyArgs_iff]
  rintro (occurs | ⟨argument, member, occurs⟩)
  · exact Preterm.hasVar_term_iff _ _ _ occurs
  · exact independent argument member occurs

theorem encodeType_independent (context : Context) (index : Nat)
    (references : Symbol → Nat) (base : Base → Preterm)
    (independent : ∀ source, ¬ Preterm.HasVar context index (base source)) (source : Ty Base) :
    ¬ Preterm.HasVar context index (encodeType references base source) := by
  induction source with
  | prop => exact applySymbol_independent context index references .bool [] (by simp)
  | base source => exact independent source
  | arr domain result ihDomain ihResult =>
      apply applySymbol_independent context index references .function _
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> assumption

theorem boundVariable_independent (context : Context) (index sourceIndex sort : Nat)
    (bound : context[sourceIndex]? = some (.bound sort)) (different : index ≠ sourceIndex) :
    ¬ Preterm.HasVar context index (.var sourceIndex) := by
  simp [Preterm.hasVar_var_iff, bound, different]

theorem contextExtension_independent (context : Context) (index boundIndex sort : Nat)
    (references : Symbol → Nat) (antecedent domain : Preterm)
    (bound : context[boundIndex]? = some (.bound sort)) (different : index ≠ boundIndex)
    (antecedentIndependent : ¬ Preterm.HasVar context index antecedent)
    (domainIndependent : ¬ Preterm.HasVar context index domain) :
    ¬ Preterm.HasVar context index
      (conjunction references antecedent (hasType references (.var boundIndex) domain)) := by
  apply applySymbol_independent context index references .an _
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact antecedentIndependent
  · apply applySymbol_independent context index references .ty _
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact boundVariable_independent context index boundIndex sort bound different
    · exact domainIndependent

theorem substitutionContext_independent (context : Context) (observer boundIndex : Nat)
    (references : Symbol → Nat) (antecedent domain argument : Preterm)
    (antecedentIndependent : ¬ Preterm.HasVar context observer antecedent)
    (domainIndependent : ¬ Preterm.HasVar context observer domain)
    (variableIndependent : ¬ Preterm.HasVar context observer (.var boundIndex))
    (argumentIndependent : ¬ Preterm.HasVar context observer argument) :
    ¬ Preterm.HasVar context observer (conjunction references antecedent
      (holds references (applySymbol references .eqc [domain, .var boundIndex, argument]))) := by
  apply applySymbol_independent context observer references .an _
  intro expression member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact antecedentIndependent
  · apply applySymbol_independent context observer references .thm _
    intro expression member
    have same : expression = applySymbol references .eqc [domain, .var boundIndex, argument] := by simpa using member
    subst expression
    apply applySymbol_independent context observer references .eqc _
    intro expression member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> assumption

#print axioms applySymbol_independent
#print axioms encodeType_independent
#print axioms boundVariable_independent
#print axioms contextExtension_independent
#print axioms substitutionContext_independent

end Mettapedia.Languages.MM0.HOLKernelTypeSupport
