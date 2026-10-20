import Mettapedia.Languages.MeTTa.HE.HOLContract.Signature
import Mettapedia.Languages.Megalodon.FiniteApplicative

/-!
# The flat HE contract in Megalodon's Mathdata type checker

The existing source contract supplies declarations, prenex scheme instances,
exact flat arities and structural tuple types. A finite inventory of its
constants and base types is checked by Mathdata, using an explicit application
constant for each flat arrow. This proof uses neither a new Megalodon logical
axiom nor a conversion of flat arrows to curried function values.

The theorem covers `FirstOrderType` in full. That relation explicitly excludes
HE's gradual wildcard, metatype and subtype rules. Their query semantics,
runtime declaration admission and implementation refinement remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract.Megalodon

open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration
open Mettapedia.Logic.HOL.NamedElaboration.FiniteApplicative

/-- The inventory is justified by the original source contract; Mathdata checks
the instantiated term itself. No declaration is authorized by its own payload. -/
def Realized (space : Space) (expression type : Atom) : Prop :=
  ∃ (term : ContractTerm) (names : List Name) (types : List (Ty Atom)),
    Annotates expression term ∧ Support (nameType space) names types ∧
      Mettapedia.Languages.Megalodon.FiniteApplicative.check names types term (.base type) = true

theorem firstOrder_iff_realized (space : Space) (expression type : Atom) :
    FirstOrderType space expression type ↔ Realized space expression type := by
  constructor
  · intro typed
    obtain ⟨term, annotated, typed⟩ := annotated_of_firstOrder typed
    obtain ⟨names, types, support, accepted⟩ :=
      (Mettapedia.Languages.Megalodon.FiniteApplicative.typing_iff _ _ _).mp typed
    exact ⟨term, names, types, annotated, support, accepted⟩
  · rintro ⟨term, names, types, annotated, support, accepted⟩
    exact firstOrder_of_annotated annotated
      (Mettapedia.Languages.Megalodon.FiniteApplicative.check_sound support accepted)

/-- HOL's existing flat contract and Mathdata's finite realization give the
same source type judgments, including overloaded and schematic declarations. -/
theorem hol_contract_iff_realized (space : Space) (expression type : Atom) :
    Typed space expression type ↔ Realized space expression type :=
  typed_iff_firstOrder.trans (firstOrder_iff_realized space expression type)

#print axioms firstOrder_iff_realized
#print axioms hol_contract_iff_realized

end Mettapedia.Languages.MeTTa.HE.HOLContract.Megalodon
