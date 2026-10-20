import Mettapedia.Languages.Megalodon.ApplicativeTyping
import Mettapedia.Logic.HOL.Syntax.FiniteApplicative

/-!
# Finite source contracts checked by Mathdata

Finite interning connects arbitrary named applicative signatures to the actual
Mathdata type checker. Both directions are proved: a source derivation has a
finite checking realization, and an accepted realization cannot invent a source
type. The inventory is justified by source signature lookups, independently of
Mathdata's checker. Inventory construction and term checking are separate costs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.FiniteApplicative

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration
open Mettapedia.Logic.HOL.NamedElaboration.FiniteApplicative

variable {Base Name : Type} [DecidableEq Base] [DecidableEq Name]

def internedSignature (types : List (Ty Base)) : List (Ty Nat) :=
  types.map (encodeType (allBases types))

def check (names : List Name) (types : List (Ty Base))
    (term : NamedTerm Base String Name) (type : Ty Base) : Bool :=
  (baseNames type).all (fun name => (allBases types).contains name) &&
    decide (ApplicativeTyping.infer (internedSignature types) (encodeTerm names term) =
      some (ApplicativeTyping.encodeType (encodeType (allBases types) type)))

theorem check_sound {typeOf : Name → Option (Ty Base)} {names : List Name}
    {types : List (Ty Base)} (support : Support typeOf names types)
    {term : NamedTerm Base String Name} {type : Ty Base}
    (accepted : check names types term type = true) : ApplicativeTyped typeOf term type := by
  simp only [check, Bool.and_eq_true] at accepted
  obtain ⟨covered, accepted⟩ := accepted
  have targetTyped := (ApplicativeTyping.infer_iff _ _ _).mp (of_decide_eq_true accepted)
  obtain ⟨found, same, foundCovered, sourceTyped⟩ :=
    decode_typed support (allBases types) (allBases_covers types) targetTyped
  have requestedCovered : Covered (allBases types) type := by
    simpa [List.all_eq_true, List.contains_iff_mem, Covered] using covered
  have equal := encodeType_injective_on (allBases types) requestedCovered foundCovered same
  simpa [equal] using sourceTyped

theorem check_complete {typeOf : Name → Option (Ty Base)} {names : List Name}
    {types : List (Ty Base)} (support : Support typeOf names types)
    {term : NamedTerm Base String Name} {type : Ty Base}
    (typed : ApplicativeTyped typeOf term type)
    (covered : ∀ name ∈ constantNames term, name ∈ names) :
    check names types term type = true := by
  have targetTyped := encode_typed support (allBases types) typed covered
  obtain ⟨found, _, foundCovered, sourceTyped⟩ :=
    decode_typed support (allBases types) (allBases_covers types) targetTyped
  have equal : found = type := sourceTyped.unique typed
  subst found
  simp only [check, Bool.and_eq_true]
  constructor
  · simpa [List.all_eq_true, List.contains_iff_mem, Covered] using foundCovered
  · exact decide_eq_true (ApplicativeTyping.typed_infers targetTyped)

/-- Complete finite checking realizations of the entire applicative contract,
not a selected example corpus. The source signature need not itself be finite. -/
theorem typing_iff (typeOf : Name → Option (Ty Base))
    (term : NamedTerm Base String Name) (type : Ty Base) :
    ApplicativeTyped typeOf term type ↔
      ∃ names types, Support typeOf names types ∧ check names types term type = true := by
  constructor
  · intro typed
    obtain ⟨names, types, support, covered⟩ := support_exists typed
    exact ⟨names, types, support, check_complete support typed covered⟩
  · rintro ⟨names, types, support, accepted⟩
    exact check_sound support accepted

namespace Controls

def names : List String := ["f", "a", "apply"]
def types : List (Ty String) :=
  [.base "flat-arrow(A,B)", .base "A",
    .arr (.base "flat-arrow(A,B)") (.arr (.base "A") (.base "B"))]
def source : NamedTerm String String String :=
  .app (.app (.constant "apply") (.constant "f")) (.constant "a")

example : check names types source (.base "B") = true := by decide
example : check names types source (.base "A") = false := by decide
example : check names types source (.base "missing") = false := by decide
example : check names types (.constant "missing") (.base "A") = false := by decide
example : check names types (.app (.constant "f") (.constant "a")) (.base "B") = false := by
  decide

end Controls

#print axioms typing_iff
#print axioms check_sound
#print axioms check_complete

end Mettapedia.Languages.Megalodon.FiniteApplicative
