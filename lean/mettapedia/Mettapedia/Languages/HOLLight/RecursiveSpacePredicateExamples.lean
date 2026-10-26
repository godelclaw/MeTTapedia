import Mettapedia.Languages.HOLLight.RecursiveSpacePredicate

/-!
# Typed input examples for positive-predicate proof generation

The data-only module keeps construction of the input signatures separate from
execution of the proof compiler and checkers.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.RecursiveSpacePredicate.Controls
open Mettapedia.Logic Mettapedia.Languages.OpenTheory

def number : HOL.Ty AtomicTy := (Ty.var (Name.global "RecursiveNumber")).toHOL
def payload : HOL.Ty AtomicTy := (Ty.var (Name.global "RecursivePayload")).toHOL
def space : HOL.Ty AtomicTy := (Ty.var (Name.global "RecursiveCarrier")).toHOL

def input (name : String) (type : HOL.Ty AtomicTy) : HOL.ClosedTerm Symbol type :=
  .const (.variable ⟨Name.global name,Ty.fromHOL type⟩ (by simp))

def signature : HOL.RecursiveSpacePredicate.Signature Symbol where
  number := number
  payload := payload
  space := space
  bottom := input "recursive_bottom" space
  construct := input "recursive_construct" (number.arr (payload.arr ((number.arr space).arr space)))
  validShape := input "recursive_valid_shape" (number.arr (payload.arr .prop))
  active := input "recursive_active" (payload.arr (number.arr .prop))
  validEdge := input "recursive_valid_edge" (payload.arr (number.arr (space.arr .prop)))

def mixedCode : HOL.PositivePredicate.Code Symbol .prop [.prop] :=
  .disj (.guard (.var .vz) (.member (.var .vz)))
    (.conj (.atom (.not (.var .vz)))
      (.ex (domain := .prop) (.all (domain := .prop)
        (.guard (.eq (.var .vz) (.var (.vs .vz))) (.member (.var (.vs (.vs .vz))))))))


end Mettapedia.Languages.HOLLight.RecursiveSpacePredicate.Controls
