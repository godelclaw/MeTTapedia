import Mettapedia.OSLF.Framework.RhoEquationGeneratedScope
import Mettapedia.OSLF.Syntax.BindingConstructorPredicates

/-!
# Full substitution of generated rho scope certificates

Quotation, drop and parallel composition agree with the independently
constructed binding-clone operations on the source equation quotient. Their
substitution comparisons follow from that model's operator laws, including
arbitrary quotient-valued environments.

Substituting a finite certificate transports its entire derivation and atomic
premises. For substitution-stable native atoms this constructs the generated
name predicate as an actual native family. Certificate depth and occurrence
count are preserved by transport; the least depth of a name can decrease when
substitution admits a shorter certificate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoGeneratedScopeSubstitution

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open BindingSubstitutionAlgebra BindingConstructorPredicates FreeBindingTerms
open RhoEquationGeneratedScope

theorem quote_operation {context : Ctx sig} (process : Process context) :
    quote process = model.operation Op.quo (.cons process .nil) := by
  induction process using Quotient.inductionOn with
  | _ process =>
      exact (constructor_read Op.quo (.cons process .nil)).symm

theorem drop_operation {context : Ctx sig} (name : Name context) :
    drop name = model.operation Op.drp (.cons name .nil) := by
  induction name using Quotient.inductionOn with
  | _ name => exact (constructor_read Op.drp (.cons name .nil)).symm

theorem join_operation {context : Ctx sig} (first second : Process context) :
    join first second = model.operation Op.par (.cons first (.cons second .nil)) := by
  induction first using Quotient.inductionOn with
  | _ first =>
      induction second using Quotient.inductionOn with
      | _ second => exact (constructor_read Op.par (.cons first (.cons second .nil))).symm

theorem substitute_quote {source target : Ctx sig}
    (env : Environment sig (TermQ rhoSourceE) source target) (process : Process source) :
    model.substitution.substitute env (quote process) =
      quote (model.substitution.substitute env process) := by
  rw [quote_operation, model.operation_substitute]
  exact (quote_operation _).symm

theorem substitute_drop {source target : Ctx sig}
    (env : Environment sig (TermQ rhoSourceE) source target) (name : Name source) :
    model.substitution.substitute env (drop name) =
      drop (model.substitution.substitute env name) := by
  rw [drop_operation, model.operation_substitute]
  exact (drop_operation _).symm

theorem substitute_join {source target : Ctx sig}
    (env : Environment sig (TermQ rhoSourceE) source target)
    (first second : Process source) :
    model.substitution.substitute env (join first second) =
      join (model.substitution.substitute env first) (model.substitution.substitute env second) := by
  rw [join_operation, model.operation_substitute]
  exact (join_operation _ _).symm

def transport {source target : Ctx sig}
    {left right : Process source → Prop} {left' right' : Process target → Prop}
    (env : Environment sig (TermQ rhoSourceE) source target)
    (leftMap : ∀ process, left process → left' (model.substitution.substitute env process))
    (rightMap : ∀ process, right process → right' (model.substitution.substitute env process)) :
    {name : Name source} → Certificate left right name →
      Certificate left' right' (model.substitution.substitute env name)
  | _, .atoms first second firstAdmitted secondAdmitted => by
      have readout : model.substitution.substitute env (quote (join first second)) =
          quote (join (model.substitution.substitute env first)
            (model.substitution.substitute env second)) := by
        rw [substitute_quote, substitute_join]
      exact readout.symm ▸ Certificate.atoms _ _
        (leftMap first firstAdmitted) (rightMap second secondAdmitted)
  | _, .left name child second secondAdmitted => by
      have readout : model.substitution.substitute env (quote (join (drop name) second)) =
          quote (join (drop (model.substitution.substitute env name))
            (model.substitution.substitute env second)) := by
        rw [substitute_quote, substitute_join, substitute_drop]
      exact readout.symm ▸ Certificate.left _ (transport env leftMap rightMap child) _
        (rightMap second secondAdmitted)
  | _, .right first firstAdmitted name child => by
      have readout : model.substitution.substitute env (quote (join first (drop name))) =
          quote (join (model.substitution.substitute env first)
            (drop (model.substitution.substitute env name))) := by
        rw [substitute_quote, substitute_join, substitute_drop]
      exact readout.symm ▸ Certificate.right _ (leftMap first firstAdmitted) _
        (transport env leftMap rightMap child)
  | _, .both first second firstChild secondChild => by
      have readout : model.substitution.substitute env (quote (join (drop first) (drop second))) =
          quote (join (drop (model.substitution.substitute env first))
            (drop (model.substitution.substitute env second))) := by
        rw [substitute_quote, substitute_join, substitute_drop, substitute_drop]
      exact readout.symm ▸ Certificate.both _ _ (transport env leftMap rightMap firstChild)
        (transport env leftMap rightMap secondChild)

@[simp]
theorem depth_cast {context : Ctx sig} {left right : Process context → Prop}
    {first second : Name context} (same : first = second)
    (certificate : Certificate left right first) :
    (same ▸ certificate).depth = certificate.depth := by
  cases same
  rfl

@[simp]
theorem nodes_cast {context : Ctx sig} {left right : Process context → Prop}
    {first second : Name context} (same : first = second)
    (certificate : Certificate left right first) :
    (same ▸ certificate).nodes = certificate.nodes := by
  cases same
  rfl

theorem transport_depth {source target : Ctx sig}
    {left right : Process source → Prop} {left' right' : Process target → Prop}
    (env : Environment sig (TermQ rhoSourceE) source target)
    (leftMap : ∀ process, left process → left' (model.substitution.substitute env process))
    (rightMap : ∀ process, right process → right' (model.substitution.substitute env process))
    {name : Name source} (certificate : Certificate left right name) :
    (transport env leftMap rightMap certificate).depth = certificate.depth := by
  induction certificate <;> simp only [transport, depth_cast, Certificate.depth, *]

theorem transport_nodes {source target : Ctx sig}
    {left right : Process source → Prop} {left' right' : Process target → Prop}
    (env : Environment sig (TermQ rhoSourceE) source target)
    (leftMap : ∀ process, left process → left' (model.substitution.substitute env process))
    (rightMap : ∀ process, right process → right' (model.substitution.substitute env process))
    {name : Name source} (certificate : Certificate left right name) :
    (transport env leftMap rightMap certificate).nodes = certificate.nodes := by
  induction certificate <;> simp only [transport, nodes_cast, Certificate.nodes, *]

theorem transport_atomicOrigins {source target : Ctx sig}
    {left right : Process source → Prop} {left' right' : Process target → Prop}
    (env : Environment sig (TermQ rhoSourceE) source target)
    (leftMap : ∀ process, left process → left' (model.substitution.substitute env process))
    (rightMap : ∀ process, right process → right' (model.substitution.substitute env process))
    {name : Name source} (certificate : Certificate left right name) :
    (transport env leftMap rightMap certificate).atomicOrigins =
      certificate.atomicOrigins.map (Sum.map (model.substitution.substitute env)
        (model.substitution.substitute env)) := by
  induction certificate <;>
    simp only [transport, Certificate.atomicOrigins_cast, Certificate.atomicOrigins,
      List.map_cons, List.map_nil, List.map_append, Sum.map_inl, Sum.map_inr, *]

theorem generated_substitute {source target : Ctx sig}
    {left right : Process source → Prop} {left' right' : Process target → Prop}
    (env : Environment sig (TermQ rhoSourceE) source target)
    (leftMap : ∀ process, left process → left' (model.substitution.substitute env process))
    (rightMap : ∀ process, right process → right' (model.substitution.substitute env process))
    {name : Name source} (member : generated left right name) :
    generated left' right' (model.substitution.substitute env name) := by
  obtain ⟨certificate⟩ := (generated_iff_certificate _ _ _).mp member
  exact certificate_sound (transport env leftMap rightMap certificate)

def native (left right : Predicate model Srt.pr) : Predicate model Srt.nm where
  holds := fun name => generated left.holds right.holds name
  substitute := by
    intro source target env name member
    exact generated_substitute env
      (fun process proof => left.substitute env process proof)
      (fun process proof => right.substitute env process proof) member

theorem native_membership_iff_certificate (left right : Predicate model Srt.pr)
    {context : Ctx sig} (name : Name context) :
    (native left right).holds name ↔ Nonempty (Certificate left.holds right.holds name) :=
  generated_iff_certificate _ _ name

end Mettapedia.OSLF.Framework.RhoGeneratedScopeSubstitution
