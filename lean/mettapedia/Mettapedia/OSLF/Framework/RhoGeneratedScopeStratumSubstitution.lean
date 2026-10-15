import Mettapedia.OSLF.Framework.RhoGeneratedScopeStrata
import Mettapedia.OSLF.Framework.RhoGeneratedScopeSubstitution

/-!
# Substitution bounds the least derivation stratum

An actual transported certificate has the same depth. Hence substitution
sends a bounded member to a member within the same bound, and the target's
least derivation stratum is no greater. This comparison uses finite witness
transport, not an equality between unrelated parse-tree sizes.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoGeneratedScopeStratumSubstitution

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open BindingSubstitutionAlgebra
open RhoEquationGeneratedScope RhoGeneratedScopeSubstitution RhoGeneratedScopeStrata

theorem bounded_substitute {source target : Ctx sig}
    {left right : Process source → Prop} {left' right' : Process target → Prop}
    (env : Environment sig (TermQ rhoSourceE) source target)
    (leftMap : ∀ process, left process → left' (model.substitution.substitute env process))
    (rightMap : ∀ process, right process → right' (model.substitution.substitute env process))
    {bound : Nat} {name : Name source} (bounded : Bounded left right bound name) :
    Bounded left' right' bound (model.substitution.substitute env name) := by
  obtain ⟨certificate, small⟩ := bounded
  exact ⟨transport env leftMap rightMap certificate,
    (transport_depth env leftMap rightMap certificate).trans_le small⟩

theorem stratum_substitute_le {source target : Ctx sig}
    {left right : Process source → Prop} {left' right' : Process target → Prop}
    (env : Environment sig (TermQ rhoSourceE) source target)
    (leftMap : ∀ process, left process → left' (model.substitution.substitute env process))
    (rightMap : ∀ process, right process → right' (model.substitution.substitute env process))
    {name : Name source} (member : generated left right name) :
    stratum (generated_substitute env leftMap rightMap member) ≤ stratum member :=
  stratum_le _ (bounded_substitute env leftMap rightMap (stratum_attained member))

end Mettapedia.OSLF.Framework.RhoGeneratedScopeStratumSubstitution
