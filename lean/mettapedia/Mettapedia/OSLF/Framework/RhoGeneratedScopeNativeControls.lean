import Mettapedia.OSLF.Framework.RhoGeneratedScopeInventory
import Mettapedia.OSLF.Syntax.BindingConstructorPredicatePresheaf

/-!
# A varying native scope and its complete future certificate

An open output contains a process variable in its payload. A supplied future
substitution installs another output there, increasing the actual inventory
from one to two. The two atomic premise occurrences of its scope certificate
remain ordered and retain their left/right roles. The future certificate
has the transported name and the same derivation depth and node count.

The generated family is instantiated as the existing genuine subfunctor on
all quotient-clone contexts. Null is excluded by the independent inventory
invariant. No runtime execution or scope decision procedure is inferred from
these native calculations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoGeneratedScopeNativeControls

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open BindingSubstitutionAlgebra BindingConstructorPredicates
open RhoEquationGeneratedScope RhoGeneratedScopeSubstitution RhoGeneratedScopeInventory

def openOutput : Term sig [Srt.pr] Srt.pr :=
  .op Op.out (.cons (quoteRaw null) (.cons (.var .zero) .nil))

def installedOutput : Term sig [] Srt.pr :=
  .op Op.out (.cons (quoteRaw null) (.cons RhoSourceOutputPredicate.output .nil))

def closeRaw : Sub sig [Srt.pr] [] := closeProcess RhoSourceOutputPredicate.output

def close : Environment sig (TermQ rhoSourceE) [Srt.pr] [] :=
  fun sort position => project (closeRaw sort position)

theorem supplied_substitution_readout :
    BindingEquationQuotientSubstitution.substitute rhoSourceE close (project openOutput) =
      project installedOutput := by
  rw [BindingEquationQuotientSubstitution.substitute_eq_bindQ rhoSourceE close closeRaw
    (fun _ _ => rfl)]
  rfl

theorem open_inventory : RhoSourceOutputPredicate.count (project openOutput) = 1 := rfl

theorem installed_inventory : RhoSourceOutputPredicate.count (project installedOutput) = 2 := rfl

theorem actual_future_inventory_changes :
    RhoSourceOutputPredicate.count
      (model.substitution.substitute close (project openOutput)) =
      RhoSourceOutputPredicate.count (project openOutput) + 1 := by
  change RhoSourceOutputPredicate.count
    (BindingEquationQuotientSubstitution.substitute rhoSourceE close (project openOutput)) = _
  rw [supplied_substitution_readout, open_inventory, installed_inventory]

def certificate : Certificate (RhoSourceOutputPredicate.positive Srt.pr).holds
    (RhoSourceOutputPredicate.positive Srt.pr).holds
    (quote (join (project openOutput) (project openOutput))) :=
  .atoms _ _ (by exact Nat.zero_lt_one) (by exact Nat.zero_lt_one)

def futureCertificate := transport close
  (fun process proof => (RhoSourceOutputPredicate.positive Srt.pr).substitute close process proof)
  (fun process proof => (RhoSourceOutputPredicate.positive Srt.pr).substitute close process proof)
  certificate

theorem future_atomic_origins : futureCertificate.atomicOrigins =
    [Sum.inl (project installedOutput), Sum.inr (project installedOutput)] := by
  rw [futureCertificate, transport_atomicOrigins]
  simp only [certificate, Certificate.atomicOrigins, List.map_cons, List.map_nil,
    Sum.map_inl, Sum.map_inr, supplied_substitution_readout]

theorem future_roles_remain_distinct :
    (Sum.inl (project installedOutput) : Sum (Process []) (Process [])) ≠
      Sum.inr (project installedOutput) := by
  intro same
  cases same

theorem future_certificate_depth : futureCertificate.depth = 0 := by
  rw [futureCertificate, transport_depth]
  rfl

theorem future_certificate_nodes : futureCertificate.nodes = 1 := by
  rw [futureCertificate, transport_nodes]
  rfl

def family := outputScope.subfunctor

theorem current_admitted : outputScope.holds
    (quote (join (project openOutput) (project openOutput))) := certificate_sound certificate

theorem future_admitted : outputScope.holds
    (model.substitution.substitute close
      (quote (join (project openOutput) (project openOutput)))) :=
  certificate_sound futureCertificate

end Mettapedia.OSLF.Framework.RhoGeneratedScopeNativeControls
