import Mettapedia.Languages.MM0.HOLKernelSyntax

/-!
# HOL judgments represented in MM0's provable sort

The maintained presentation distinguishes object typing (`ty`), assertion of
an object Boolean (`thm`), context conjunction (`an`), and consequence (`im`).
These are native `wff` expressions. Object Boolean conjunction and implication
remain the separate constructors `andc` and `impc`.

The sorting and statement-admission results below supply the formation part
of theorem instantiation. They grant no derivation merely from formation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelJudgment

open Kernel HOLKernelSyntax

def hasType (references : Symbol → Nat) (expression type : Preterm) : Preterm :=
  applySymbol references .ty [expression, type]

def holds (references : Symbol → Nat) (formula : Preterm) : Preterm :=
  applySymbol references .thm [formula]

def entails (references : Symbol → Nat) (premise conclusion : Preterm) : Preterm :=
  applySymbol references .im [premise, conclusion]

def conjunction (references : Symbol → Nat) (left right : Preterm) : Preterm :=
  applySymbol references .an [left, right]

variable {sorts : SortSignature} {terms : TermSignature}

theorem hasType_sorted (signature : Signature sorts terms) (context : Context)
    {expression type : Preterm}
    (expressionSorted : Preterm.HasType terms context expression [] signature.ids.object)
    (typeSorted : Preterm.HasType terms context type [] signature.ids.type) :
    Preterm.HasType terms context (hasType signature.symbol expression type) [] signature.ids.wff :=
  signature.application context .ty _ (.cons (.regular expressionSorted) (.cons (.regular typeSorted) .nil))

theorem holds_sorted (signature : Signature sorts terms) (context : Context) {formula : Preterm}
    (formed : Preterm.HasType terms context formula [] signature.ids.object) :
    Preterm.HasType terms context (holds signature.symbol formula) [] signature.ids.wff :=
  signature.application context .thm _ (.cons (.regular formed) .nil)

theorem entails_sorted (signature : Signature sorts terms) (context : Context)
    {premise conclusion : Preterm}
    (premiseSorted : Preterm.HasType terms context premise [] signature.ids.wff)
    (conclusionSorted : Preterm.HasType terms context conclusion [] signature.ids.wff) :
    Preterm.HasType terms context (entails signature.symbol premise conclusion) [] signature.ids.wff :=
  signature.application context .im _ (.cons (.regular premiseSorted) (.cons (.regular conclusionSorted) .nil))

theorem conjunction_sorted (signature : Signature sorts terms) (context : Context)
    {left right : Preterm}
    (leftSorted : Preterm.HasType terms context left [] signature.ids.wff)
    (rightSorted : Preterm.HasType terms context right [] signature.ids.wff) :
    Preterm.HasType terms context (conjunction signature.symbol left right) [] signature.ids.wff :=
  signature.application context .an _ (.cons (.regular leftSorted) (.cons (.regular rightSorted) .nil))

theorem wff_isStatement (signature : Signature sorts terms) {context : Context} {expression : Preterm}
    (sorted : Preterm.HasType terms context expression [] signature.ids.wff) :
    Preterm.IsStatement sorts terms context expression :=
  ⟨signature.ids.wff, _, sorted, signature.wffDeclared, rfl⟩

theorem object_is_not_statement (signature : Signature sorts terms)
    {context : Context} {expression : Preterm}
    (sorted : Preterm.HasType terms context expression [] signature.ids.object) :
    ¬ Preterm.IsStatement sorts terms context expression := by
  rintro ⟨sort, info, typed, declared, provable⟩
  have same := (sorted.deterministic typed).2
  subst sort
  rw [signature.objectDeclared] at declared
  cases declared
  cases provable

#print axioms hasType_sorted
#print axioms holds_sorted
#print axioms entails_sorted
#print axioms conjunction_sorted
#print axioms wff_isStatement
#print axioms object_is_not_statement

end Mettapedia.Languages.MM0.HOLKernelJudgment
