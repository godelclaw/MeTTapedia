import Mettapedia.OSLF.Syntax.RhoFiniteQuotationOrigins
import Mettapedia.OSLF.Framework.RhoGeneratedScopeSubstitution

/-!
# Actual quotation-origin receipts transport through substitution

Substituting an origin transports its actual process, its name readout and
its membership in the independently constructed finite target catalogue.
Complete source origins therefore form a genuine dependent family. This
map retains the supplied origin; it does not reconstruct additional future
origins from source object coverage.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoFiniteQuotationOriginTransport

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open BindingSubstitutionAlgebra FreeBindingTerms
open RhoGeneratedScopeSubstitution RhoFiniteQuotationOrigins

def transport {source target : Ctx sig}
    (env : Environment sig (TermQ rhoSourceE) source target) {name : Name source}
    (origin : Origin name) : Origin (model.substitution.substitute env name) where
  val := model.substitution.substitute env origin.val
  property := (substitute_quote env origin.val).symm.trans
    (congrArg (model.substitution.substitute env) origin.property)

theorem origin_catalogue_substitute {source target : Ctx sig}
    (env : Environment sig (TermQ rhoSourceE) source target) {name : Name source}
    {process : Process source} (member : process ∈ origins name) :
    model.substitution.substitute env process ∈ origins (model.substitution.substitute env name) := by
  apply (quotation_fibre_iff _ _).mp
  exact (transport env ⟨process, (quotation_fibre_iff _ _).mpr member⟩).property

end Mettapedia.OSLF.Framework.RhoFiniteQuotationOriginTransport
