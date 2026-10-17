import Mettapedia.Languages.Megalodon.MathdataKernel
import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Presentation

/-!
# The intrinsic simple fragment in Megalodon's actual type checker

The source is the independent single-base, intrinsically typed lambda
calculus. Its base is read as one selected Mathdata base type, arrows as
arrows, and its terms as de Bruijn variables, applications and lambdas.
Every translated term is accepted by `MathdataKernel.inferTerm`, in every
signature and at every type depth. No declaration or proof authority is
introduced by this translation.

This is a common simple-function fragment, not an encoding of dependent
families, polymorphic propositions, a material set theory, or a complete
Prime candidate. In particular, the chosen base type does not determine its
inhabitants or any set-theoretic axioms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SimpleTypeFragment

open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT
open MathdataKernel

def type (base : Nat) : Ty → Tp
  | .atom => .base base
  | .arr domain codomain => .arr (type base domain) (type base codomain)

def index : {context : List Ty} → {selected : Ty} → Var context selected → Nat
  | _, _, .zero => 0
  | _, _, .succ prior => index prior + 1

def term (base : Nat) : {context : List Ty} → {selected : Ty} →
    Term context selected → Tm
  | _, _, .var typedVar => .db (index typedVar)
  | _, _, @Term.lam domain _ _ body => .lam (type base domain) (term base body)
  | _, _, .app function argument => .app (term base function) (term base argument)

theorem type_plain (base depth : Nat) (selected : Ty) :
    (type base selected).plainWellFormed depth = true := by
  induction selected with
  | atom => rfl
  | arr domain codomain domainIH codomainIH =>
      simp [type, Tp.plainWellFormed, domainIH, codomainIH]

theorem type_injective (base : Nat) : Function.Injective (type base) := by
  intro left
  induction left with
  | atom =>
      intro right equal
      cases right <;> simp_all [type]
  | arr domain codomain domainIH codomainIH =>
      intro right equal
      cases right with
      | atom => simp [type] at equal
      | arr otherDomain otherCodomain =>
          simp only [type, Tp.arr.injEq] at equal
          exact congrArg₂ Ty.arr (domainIH equal.1) (codomainIH equal.2)

theorem variable_lookup (base : Nat) {context : List Ty} {selected : Ty}
    (typedVar : Var context selected) :
    (context.map (type base))[index typedVar]? = some (type base selected) := by
  induction typedVar with
  | zero => rfl
  | succ prior ih => simpa [index] using ih

/-- The executable source checker validates the translated intrinsic typing. -/
theorem term_infers (base depth : Nat) (environment : Environment)
    {context : List Ty} {selected : Ty} (source : Term context selected) :
    inferTerm environment depth (context.map (type base)) (term base source) =
      some (type base selected) := by
  induction source with
  | var typedVar => exact variable_lookup base typedVar
  | lam body ih =>
      simp only [List.map_cons] at ih
      simp [term, inferTerm, type_plain, type, ih]
  | app function argument functionIH argumentIH =>
      simp [term, inferTerm, functionIH, argumentIH, type]

/-- This concrete image contains a real beta redex, with unequal raw endpoints. -/
theorem identity_beta (base : Nat) :
    let source : Term [.atom] .atom := .app (.lam (.var .zero)) (.var .zero)
    Tm.normalize 2 (term base source) = some (.db 0) ∧
      term base source ≠ .db 0 := by
  constructor
  · rfl
  · simp [term]

/-- A Boolean proposition cannot be passed to this base-typed identity. -/
theorem wrong_argument_refused (base : Nat) :
    inferTerm {} 0 [.prop]
      (.app (.lam (.base base) (.db 0)) (.db 0)) = none := by
  simp [inferTerm, Tp.plainWellFormed]

/-- Prefix polymorphism is additional syntax, outside this plain fragment. -/
theorem prefix_type_outside_fragment (base : Nat) (body : Tp) :
    ∀ selected, type base selected ≠ .all body := by
  intro selected
  cases selected <;> simp [type]

#print axioms term_infers
#print axioms type_injective
#print axioms identity_beta
#print axioms wrong_argument_refused

end Mettapedia.Languages.Megalodon.SimpleTypeFragment
