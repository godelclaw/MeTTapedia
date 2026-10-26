import Mettapedia.Languages.MM0.HOLKernelBindingInterpretation
import Mettapedia.Languages.MM0.HOLKernelSetOperationReadbackControls

/-!
# Lexical shadowing and fresh eigenvariables in native HOL readback

A lambda binder can shadow a displayed outer name. The application outside
that lambda still refers to the outer variable. The canonical distinct-name
encoding rejects this alternative spelling, and a binding inference cannot
reuse an occupied name as a fresh eigenvariable. Regular-parameter capture
remains separately refused by the term reader.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelBindingReadbackControls
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelBindingInterpretation
open NamedElaboration (BinderNames)
open HOLKernelSetOperationReadbackControls (references)
open Embedding.ZFSetHenkinInterpretation (Symbol)

def outerName : Names [.prop] := .cons 7 .nil

def variableBetaLeft : Preterm :=
  applySymbol references .app
    [applySymbol references .lam [.var 7, applySymbol references .bool [], .var 7], .var 7]

theorem lexical_shadowing_readback :
    readTerm references HOLKernelSetOperationReadback.readConstant 7 outerName variableBetaLeft =
      some ⟨.prop, (Term.app (.lam (.var .vz)) (.var .vz) : Term Symbol [.prop] .prop)⟩ := by
  simp [variableBetaLeft, outerName, applySymbol, Preterm.applyArgs, readTerm, readTermWith,
    readHead_reference references HOLKernelSetOperationReadbackControls.references_injective,
    readVariable, readType, application, expect, NamedElaboration.expectType, Except.toOption]

theorem shadowing_outside_canonical_image :
    HOLKernelSetOperationReadback.readCanonicalTerm references outerName 1 variableBetaLeft = none := by
  unfold HOLKernelSetOperationReadback.readCanonicalTerm HOLKernelSetOperationReadback.readTerm
  rw [lexical_shadowing_readback]
  simp [HOLKernelSetOperationReadback.encode,
    variableBetaLeft, outerName, encodeTerm, encodeType, BinderNames.nameOf,
    Positions.extend, applySymbol, Preterm.applyArgs,
    HOLKernelSetOperationInterpretation.binderName, HOLKernelSetOperationInterpretation.symbols]

theorem occupied_eigenvariable_refused : freshName 7 outerName 7 = false := by rfl
theorem fresh_eigenvariable_admitted : freshName 7 outerName 8 = true := by rfl
theorem parameter_eigenvariable_refused : freshName 7 outerName 3 = false := by rfl

#print axioms lexical_shadowing_readback
#print axioms shadowing_outside_canonical_image
end Mettapedia.Languages.MM0.HOLKernelBindingReadbackControls
