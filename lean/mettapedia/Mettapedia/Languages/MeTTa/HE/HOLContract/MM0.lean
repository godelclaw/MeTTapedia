import Mettapedia.Languages.MeTTa.HE.HOLContract.Signature
import Mettapedia.Languages.MM0.Translation.FiniteApplicative

/-!
# The flat HE contract in MM0's native sort checker

The finite support of an existing HE contract derivation is interned. MM0
checks the resulting term using nullary constants and explicit application
constructors. Preserved arities, scheme instances, declaration occurrences and
tuple interpretation come from the original contract. No theorem axiom states
the requested typing conclusion.

As in the Mathdata realization, this covers `FirstOrderType`. It does not
identify that static relation with all gradual or mode-sensitive HE queries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract.MM0

open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration.FiniteApplicative

def Realized (space : Space) (expression type : Atom) : Prop :=
  ∃ (term : ContractTerm) (names : List Name) (types : List (Ty Atom))
      (certificate : Mettapedia.Languages.MM0.Translation.ApplicativeTyping.Certificate Nat),
    Annotates expression term ∧ Support (nameType space) names types ∧
      Mettapedia.Languages.MM0.Translation.FiniteApplicative.check
        names types term (.base type) certificate = true

theorem firstOrder_iff_realized (space : Space) (expression type : Atom) :
    FirstOrderType space expression type ↔ Realized space expression type := by
  constructor
  · intro typed
    obtain ⟨term, annotated, typed⟩ := annotated_of_firstOrder typed
    obtain ⟨names, types, certificate, support, accepted⟩ :=
      (Mettapedia.Languages.MM0.Translation.FiniteApplicative.typing_iff _ _ _).mp typed
    exact ⟨term, names, types, certificate, annotated, support, accepted⟩
  · rintro ⟨term, names, types, certificate, annotated, support, accepted⟩
    exact firstOrder_of_annotated annotated
      (Mettapedia.Languages.MM0.Translation.FiniteApplicative.check_sound support accepted)

theorem hol_contract_iff_realized (space : Space) (expression type : Atom) :
    Typed space expression type ↔ Realized space expression type :=
  typed_iff_firstOrder.trans (firstOrder_iff_realized space expression type)

#print axioms firstOrder_iff_realized
#print axioms hol_contract_iff_realized

end Mettapedia.Languages.MeTTa.HE.HOLContract.MM0
