import Mettapedia.Logic.HOL.FiniteConstructorEncoding

/-!
# Nonempty Boolean controls for the typed payload encoder

The constant-free Boolean fragment has distinct truth values and two distinct
constructor occurrences. Its well-typed constant-false payload is outside the
constructor image. No data carrier or source family is assumed inhabited.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding.Controls

abbrev Constants : Ty Empty → Type := fun _ => Empty
def model : HenkinModel.{0,0,0} Empty Constants :=
  .standard (fun impossible => nomatch impossible) (fun impossible => nomatch impossible)
def values : model.Valuation [] := fun impossible => nomatch impossible
def signature : List (List (Ty Empty)) := [[.prop, .prop], [.prop, .prop]]
def fields : Arguments Constants [] [.prop, .prop] := (.top, .bot, PUnit.unit)
def changedFields : Arguments Constants [] [.prop, .prop] := (.bot, .top, PUnit.unit)

theorem generated_denotation :
    payloadEquivalence model signature (model.denote (encode signature ⟨0, by decide⟩ fields) values) =
      TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) signature
        ⟨⟨0, by decide⟩, denoteArguments model _ fields values⟩ :=
  encode_denote model signature ⟨0, by decide⟩ fields values

theorem constructor_distinguished :
    model.denote (encode signature ⟨0, by decide⟩ fields) values ≠
      model.denote (encode signature ⟨1, by decide⟩ fields) values := by
  intro same
  have images := (encode_denote model signature ⟨0, by decide⟩ fields values).symm.trans
    ((congrArg (payloadEquivalence model signature) same).trans
      (encode_denote model signature ⟨1, by decide⟩ fields values))
  have inputs := TypeTheory.FiniteConstructorEncoding.encode_injective _ _ images
  have indices := congrArg (fun data => data.1.val) inputs
  change (0 : Nat) = 1 at indices
  cases indices

theorem field_distinguished :
    model.denote (encode signature ⟨0, by decide⟩ fields) values ≠
      model.denote (encode signature ⟨0, by decide⟩ changedFields) values := by
  intro same
  have images := (encode_denote model signature ⟨0, by decide⟩ fields values).symm.trans
    ((congrArg (payloadEquivalence model signature) same).trans
      (encode_denote model signature ⟨0, by decide⟩ changedFields values))
  have inputs := TypeTheory.FiniteConstructorEncoding.encode_injective _ _ images
  have data := eq_of_heq (Sigma.mk.inj inputs).2
  have truth := congrArg Prod.fst data
  exact (congrArg ULift.down truth).mp True.intro

def unused : ClosedTerm Constants (payloadType signature) := .lam (.lam .bot)

theorem unused_refused : ¬ TypeTheory.FiniteConstructorEncoding.Valid (Ty.denote model.Carrier) signature
    (payloadEquivalence model signature (model.denote unused values)) :=
  TypeTheory.FiniteConstructorEncoding.unused_not_valid _ _

#print axioms generated_denotation
#print axioms constructor_distinguished
#print axioms field_distinguished
#print axioms unused_refused

end Mettapedia.Logic.HOL.FiniteConstructorEncoding.Controls
