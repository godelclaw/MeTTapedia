import Mettapedia.Logic.HOL.FiniteConstructorEncoding
import Mettapedia.Languages.HOLLight.RetainedCompilation

/-!
# Primitive beta receipts for constructor payload observations

The actual typed encoder is observed with predicate handlers. Constructor
selection and field readout produce retained beta proofs, which compile to
primitive HOL Light graphs. The examples use Boolean fields; the encoder and
its denotation theorem are polymorphic in the field types.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ConstructorPayload

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open RetainedCompilation ReverseTranslation
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def signature : List (List (HOL.Ty AtomicTy)) := [[.prop, .prop], [.prop, .prop]]
abbrev handler := HOL.FiniteConstructorEncoding.handlerType ([.prop, .prop] : List (HOL.Ty AtomicTy))
abbrev payload := HOL.FiniteConstructorEncoding.payloadType signature

def first : HOL.ClosedTerm Symbol payload :=
  HOL.FiniteConstructorEncoding.encode signature ⟨0, by decide⟩ (.top, .bot, PUnit.unit)
def second : HOL.ClosedTerm Symbol payload :=
  HOL.FiniteConstructorEncoding.encode signature ⟨1, by decide⟩ (.top, .bot, PUnit.unit)
def changed : HOL.ClosedTerm Symbol payload :=
  HOL.FiniteConstructorEncoding.encode signature ⟨0, by decide⟩ (.bot, .top, PUnit.unit)

def yes : HOL.ClosedTerm Symbol handler := .lam (.lam .top)
def no : HOL.ClosedTerm Symbol handler := .lam (.lam .bot)
def firstField : HOL.ClosedTerm Symbol handler := .lam (.lam (.var (.vs .vz)))

def observe (value : HOL.ClosedTerm Symbol payload) (left right : HOL.ClosedTerm Symbol handler) :
    HOL.ClosedFormula Symbol := .app (.app value left) right

def betaTwo {firstType secondType resultType : HOL.Ty AtomicTy}
    (firstArgument : HOL.ClosedTerm Symbol firstType)
    (secondArgument : HOL.ClosedTerm Symbol secondType)
    (body : HOL.Term Symbol [secondType, firstType] resultType) :
    HOL.ProofSyntax Symbol []
      (.eq (.app (.app (.lam (.lam body)) firstArgument) secondArgument)
        (HOL.instantiate secondArgument (HOL.subst (HOL.Subst.lift (HOL.Subst.single firstArgument)) body))) :=
  .eqTrans (.eqApp secondArgument (.beta firstArgument (.lam body)))
    (.beta secondArgument (HOL.subst (HOL.Subst.lift (HOL.Subst.single firstArgument)) body))

def firstSelectionProof : HOL.ProofSyntax Symbol [] (.eq (observe first yes no) .top) :=
  .eqTrans (betaTwo yes no (.app (.app (.var (.vs .vz)) .top) .bot))
    (betaTwo .top .bot .top)

def secondSelectionProof : HOL.ProofSyntax Symbol [] (.eq (observe second yes no) .bot) :=
  .eqTrans (betaTwo yes no (.app (.app (.var .vz) .top) .bot))
    (betaTwo .top .bot .bot)

def firstReadoutProof : HOL.ProofSyntax Symbol [] (.eq (observe first firstField no) .top) :=
  .eqTrans (betaTwo firstField no (.app (.app (.var (.vs .vz)) .top) .bot))
    (betaTwo .top .bot (.var (.vs .vz)))

def changedReadoutProof : HOL.ProofSyntax Symbol [] (.eq (observe changed firstField no) .bot) :=
  .eqTrans (betaTwo firstField no (.app (.app (.var (.vs .vz)) .bot) .top))
    (betaTwo .bot .top (.var (.vs .vz)))

theorem firstSelection_free : HOL.ProofSyntax.FunctionExtensionalityFree firstSelectionProof := by
  simp [firstSelectionProof, betaTwo, HOL.ProofSyntax.FunctionExtensionalityFree]
theorem secondSelection_free : HOL.ProofSyntax.FunctionExtensionalityFree secondSelectionProof := by
  simp [secondSelectionProof, betaTwo, HOL.ProofSyntax.FunctionExtensionalityFree]
theorem firstReadout_free : HOL.ProofSyntax.FunctionExtensionalityFree firstReadoutProof := by
  simp [firstReadoutProof, betaTwo, HOL.ProofSyntax.FunctionExtensionalityFree]
theorem changedReadout_free : HOL.ProofSyntax.FunctionExtensionalityFree changedReadoutProof := by
  simp [changedReadoutProof, betaTwo, HOL.ProofSyntax.FunctionExtensionalityFree]

def firstSelectionNative := compileWithoutFunctionExtensionality emptyAxiomPolicy
  firstSelectionProof firstSelection_free Naming.empty ("payload-first-constructor", 0)
def secondSelectionNative := compileWithoutFunctionExtensionality emptyAxiomPolicy
  secondSelectionProof secondSelection_free Naming.empty ("payload-second-constructor", 0)
def firstReadoutNative := compileWithoutFunctionExtensionality emptyAxiomPolicy
  firstReadoutProof firstReadout_free Naming.empty ("payload-first-field", 0)
def changedReadoutNative := compileWithoutFunctionExtensionality emptyAxiomPolicy
  changedReadoutProof changedReadout_free Naming.empty ("payload-changed-field", 0)

#print axioms firstSelectionProof
#print axioms changedReadoutProof
#print axioms firstSelectionNative

end Mettapedia.Languages.HOLLight.ConstructorPayload
