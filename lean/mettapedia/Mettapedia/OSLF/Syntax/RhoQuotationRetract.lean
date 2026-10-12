import Mettapedia.OSLF.Syntax.RhoScopeQuotientControls

/-!
# The actual quotation retraction and its faithful subcarrier

Name eta earns a retraction of processes onto the image of drop. On this
fixed subcarrier, quotation and drop are inverse equivalences. The complete
process carrier does not have this equivalence: a visible output differs from
its projected suspended form.

The projection forgets distinctions between process origins of one name.
It does not preserve parallel composition. Accordingly, the faithful
subcarrier comparison repairs quotation faithfulness alone; it does not
license replacing process origins throughout a spatial specification.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoQuotationRetract

open RhoSchema RhoQuotationClassFibres RhoScopeQuotientControls

variable {context : Ctx sig}

def suspend (process : Process context) : Process context := drop (quote process)

theorem suspend_idempotent (process : Process context) :
    suspend (suspend process) = suspend process :=
  congrArg drop (quote_drop (quote process))

def FixedProcess (context : Ctx sig) :=
  {process : Process context // suspend process = process}

def dropped (name : Name context) : FixedProcess context :=
  ⟨drop name, congrArg drop (quote_drop name)⟩

def projectFixed (process : Process context) : FixedProcess context :=
  ⟨suspend process, suspend_idempotent process⟩

def nameEquivFixedProcess (context : Ctx sig) : Name context ≃ FixedProcess context where
  toFun := dropped
  invFun := fun process => quote process.val
  left_inv := quote_drop
  right_inv := fun process => Subtype.ext process.property

theorem quotation_faithful_on_fixed_processes :
    Function.Injective (fun process : FixedProcess context => quote process.val) :=
  (nameEquivFixedProcess context).symm.injective

theorem drop_injective : Function.Injective (drop : Name context → Process context) := by
  intro first second same
  exact (quote_drop first).symm.trans ((congrArg quote same).trans (quote_drop second))

theorem fixed_origin_unique {name : Name context} (first second : FixedProcess context)
    (firstReadout : quote first.val = name) (secondReadout : quote second.val = name) :
    first = second := quotation_faithful_on_fixed_processes (firstReadout.trans secondReadout.symm)

theorem projecting_recovers_fixed {process : FixedProcess context} :
    projectFixed process.val = process := Subtype.ext process.property

theorem actual_projection_changes_a_process : suspend visible ≠ visible := suspended_not_visible

theorem visible_not_fixed : ¬ suspend visible = visible := actual_projection_changes_a_process

theorem actual_origin_projection_collapses : projectFixed suspended = projectFixed visible := by
  apply Subtype.ext
  exact congrArg drop same_actual_name

theorem projection_not_injective :
    ¬ Function.Injective (projectFixed : Process [] → FixedProcess []) :=
  fun injective => suspended_not_visible (injective actual_origin_projection_collapses)

theorem projection_not_parallel_homomorphism :
    ¬ ∀ first second : Process [],
      suspend (join first second) = join (suspend first) (suspend second) := by
  intro preserves
  have sameSuspensions : suspend (join suspended visible) = suspend (join visible visible) := by
    rw [preserves suspended visible, preserves visible visible,
      show suspend suspended = suspended from suspend_idempotent visible]
    rfl
  apply quoted_equality_not_stable_under_parallel
  have quoted := congrArg quote sameSuspensions
  simpa only [suspend, quote_drop] using quoted

end Mettapedia.OSLF.Binding.RhoQuotationRetract
