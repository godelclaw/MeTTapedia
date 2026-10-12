import Mettapedia.TypeTheory.ContextualProductSections

/-!
# Generic dependent bodies under equal source type presentations

Actual equal domains and dependent codomains transport the complete
generic-variable body of a source function. Equality of decoded families
alone is not used to identify distinct source type presentations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualProductSections

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPiEta

universe u v w w'
variable {C : Cwf.{u, v, w, w'}}

theorem genericSection_type_transport (products : StableProducts C)
    {Γ : C.Ctx} {A₀ A₁ : C.Ty Γ} (domains : A₀ = A₁)
    {B₀ : C.Ty (C.ext Γ A₀)} {B₁ : C.Ty (C.ext Γ A₁)}
    (codomains : HEq B₀ B₁)
    {function₀ : C.Tm Γ (products.operations.pi A₀ B₀)}
    {function₁ : C.Tm Γ (products.operations.pi A₁ B₁)}
    (functions : HEq function₀ function₁) :
    HEq (genericSection products.operations products.substitution.1 function₀)
      (genericSection products.operations products.substitution.1 function₁) := by
  cases domains
  cases eq_of_heq codomains
  cases eq_of_heq functions
  rfl

end Mettapedia.TypeTheory.ContextualProductSections
