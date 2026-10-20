import Mettapedia.Languages.MM0.Translation.ApplicativeTyping
import Mettapedia.Logic.HOL.Syntax.FiniteApplicative

/-!
# Named applicative contracts in MM0

Finite interning is shared with the Mathdata realization. MM0 receives ordinary
term declarations and a term with explicitly annotated application sites. Its
native sort checker validates the annotations. Source declaration lookups are
checked at inventory admission, separately from per-term checking.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FiniteApplicative

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration
open Mettapedia.Logic.HOL.NamedElaboration.FiniteApplicative

variable {Base Name : Type} [DecidableEq Base] [DecidableEq Name]

def internedSignature (types : List (Ty Base)) : List (Ty Nat) :=
  types.map (encodeType (allBases types))

def check (names : List Name) (types : List (Ty Base))
    (source : NamedTerm Base String Name) (type : Ty Base)
    (certificate : ApplicativeTyping.Certificate Nat) : Bool :=
  let constants := internedSignature types
  let sorts := ApplicativeTyping.typeInventory constants
  (baseNames type).all (fun name => (allBases types).contains name) &&
    decide (certificate.erase = encodeTerm names source) &&
    decide (ApplicativeTyping.infer constants sorts certificate =
      some ([], sorts.idxOf (encodeType (allBases types) type)))

theorem check_sound {typeOf : Name → Option (Ty Base)} {names : List Name}
    {types : List (Ty Base)} (support : Support typeOf names types)
    {source : NamedTerm Base String Name} {type : Ty Base}
    {certificate : ApplicativeTyping.Certificate Nat}
    (accepted : check names types source type certificate = true) :
    ApplicativeTyped typeOf source type := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨⟨covered, erased⟩, accepted⟩ := accepted
  obtain ⟨_, targetType, targetPresent, targetSame, certified⟩ :=
    ApplicativeTyping.infer_reflects accepted
  have sameTarget : targetType = encodeType (allBases types) type :=
    (List.idxOf_inj targetPresent).mp targetSame.symm
  have targetTyped := certified.typed
  rw [erased, sameTarget] at targetTyped
  obtain ⟨found, same, foundCovered, sourceTyped⟩ :=
    decode_typed support (allBases types) (allBases_covers types) targetTyped
  have requestedCovered : Covered (allBases types) type := by
    simpa [List.all_eq_true, List.contains_iff_mem, Covered] using covered
  have equal := encodeType_injective_on (allBases types) requestedCovered foundCovered same
  simpa [equal] using sourceTyped

theorem check_complete {typeOf : Name → Option (Ty Base)} {names : List Name}
    {types : List (Ty Base)} (support : Support typeOf names types)
    {source : NamedTerm Base String Name} {type : Ty Base}
    (typed : ApplicativeTyped typeOf source type)
    (covered : ∀ name ∈ constantNames source, name ∈ names) :
    ∃ certificate, check names types source type certificate = true := by
  have targetTyped := encode_typed support (allBases types) typed covered
  obtain ⟨found, _, foundCovered, sourceTyped⟩ :=
    decode_typed support (allBases types) (allBases_covers types) targetTyped
  have equal : found = type := sourceTyped.unique typed
  subst found
  obtain ⟨_, certificate, erased, checked⟩ := (ApplicativeTyping.typing_iff _ _ _).mp targetTyped
  refine ⟨certificate, ?_⟩
  simp only [check, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, erased⟩, checked⟩
  simpa [List.all_eq_true, List.contains_iff_mem, Covered] using foundCovered

theorem typing_iff (typeOf : Name → Option (Ty Base))
    (source : NamedTerm Base String Name) (type : Ty Base) :
    ApplicativeTyped typeOf source type ↔
      ∃ names types certificate, Support typeOf names types ∧
        check names types source type certificate = true := by
  constructor
  · intro typed
    obtain ⟨names, types, support, covered⟩ := support_exists typed
    obtain ⟨certificate, accepted⟩ := check_complete support typed covered
    exact ⟨names, types, certificate, support, accepted⟩
  · rintro ⟨names, types, certificate, support, accepted⟩
    exact check_sound support accepted

#print axioms typing_iff
#print axioms check_sound
#print axioms check_complete

end Mettapedia.Languages.MM0.Translation.FiniteApplicative
