import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference

open Mettapedia.OSLF.Framework

/-!
# Binding admission of the unmodified authored rho declarations

The generic grammar inference is exercised on the original COMM and ParCong
rules. Their sources, targets, premises and declaration identities stay
unchanged. The elaborated context retains the inferred collection remainder
and the COMM body's actual Name dependency.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.BindingAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference

def comm : Option BindingPlan := compile? rhoCalc rhoCommRewrite
def parallel : Option BindingPlan := compile? rhoCalc rhoParCongRewrite

#guard comm.isSome
#guard parallel.isSome
#guard (comm.bind fun plan => dependencies? plan.spec "p") = some [.base "Name"]
#guard (comm.map BindingPlan.implicitTypes) = some [("rest", .bag (.base "Proc"))]
#guard (parallel.map BindingPlan.implicitTypes) =
  some [("S", .base "Proc"), ("rest", .bag (.base "Proc")), ("T", .base "Proc")]

theorem comm_admitted {plan : BindingPlan} (compiled : comm = some plan) :
    admittedFor (plan.elaborate rhoCommRewrite) plan.spec = true ∧
      dependencySortsDeclared rhoCalc plan.spec = true := compile_admitted compiled

theorem parallel_admitted {plan : BindingPlan} (compiled : parallel = some plan) :
    admittedFor (plan.elaborate rhoParCongRewrite) plan.spec = true ∧
      dependencySortsDeclared rhoCalc plan.spec = true := compile_admitted compiled

theorem comm_source {plan : BindingPlan} :
    (plan.elaborate rhoCommRewrite).left = rhoCommRewrite.left ∧
      (plan.elaborate rhoCommRewrite).right = rhoCommRewrite.right ∧
      (plan.elaborate rhoCommRewrite).premises = rhoCommRewrite.premises :=
  ⟨rfl, rfl, rfl⟩

theorem parallel_source {plan : BindingPlan} :
    (plan.elaborate rhoParCongRewrite).left = rhoParCongRewrite.left ∧
      (plan.elaborate rhoParCongRewrite).right = rhoParCongRewrite.right ∧
      (plan.elaborate rhoParCongRewrite).premises = rhoParCongRewrite.premises :=
  ⟨rfl, rfl, rfl⟩

#print axioms comm_admitted
#print axioms parallel_admitted

end Mettapedia.OSLF.NativeTypes.Instances.Rho.BindingAdmission
