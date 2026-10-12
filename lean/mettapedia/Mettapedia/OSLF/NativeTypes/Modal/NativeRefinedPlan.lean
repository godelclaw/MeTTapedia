import Mettapedia.OSLF.MeTTaIL.StructuralDescentPlan

/-!
# Proof-directed computational normalization of admitted recursive plans

The independently checked structural profile earns this branch of refinement.
The resulting plan is equal to the original generic refinement. Keeping the
branch selected explicitly avoids transporting dependent catalogue indices
through a run-time conditional during finite certificate computations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeRefinedPlan

open Mettapedia.OSLF.MeTTaIL GeneralExecutionAdmission

def normalize (plan : Plan) (_ready : StructuralDescent.Plan.structuralReady plan = true) : Plan :=
  {plan with obligations := plan.obligations.filter (· != .childStratification)}

theorem normalize_eq_refine (plan : Plan)
    (ready : StructuralDescent.Plan.structuralReady plan = true) :
    normalize plan ready = StructuralDescent.Plan.refine plan := by
  simp only [normalize, StructuralDescent.Plan.refine, ready, ite_true]

end Mettapedia.OSLF.NativeTypes.Modal.NativeRefinedPlan
