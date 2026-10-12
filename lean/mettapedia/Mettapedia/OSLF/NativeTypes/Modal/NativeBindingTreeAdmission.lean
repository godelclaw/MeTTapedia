import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingMatchInstantiation
import Mettapedia.OSLF.NativeTypes.Modal.NativeEventDeclarations

/-!
# Computed admission of authored native modal source trees

The semantic schema reading supports ordinary constructors, bound variables,
metavariables and binders. This gate reads every selected declaration, rather
than treating an unsupported source form as an absent operational event.
Fixed-snapshot operational execution has its own, broader admission boundary.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingTreeAdmission

open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open NativeBindingMatchInstantiation

def check (plan : Plan) : Bool :=
  plan.rules.all fun declaration => treeSchema declaration.rule.left

def Admitted (plan : Plan) : Prop :=
  ∀ declaration ∈ plan.rules, treeSchema declaration.rule.left = true

theorem check_exact (plan : Plan) : check plan = true ↔ Admitted plan := by
  simp only [check, List.all_eq_true, Admitted]

theorem schema_tree {plan : Plan} (ready : Admitted plan) (schema : Rules.Schema plan) :
    treeSchema schema.declaration.rule.left = true :=
  ready schema.declaration (List.fst_mem_of_mem_zipIdx schema.declared)

theorem generated_schema_tree {plan : Plan} (checked : check plan = true)
    (index : NativeEventDeclarations.Index plan) :
    treeSchema (NativeEventDeclarations.schema plan index).declaration.rule.left = true :=
  schema_tree ((check_exact plan).mp checked) _

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingTreeAdmission
