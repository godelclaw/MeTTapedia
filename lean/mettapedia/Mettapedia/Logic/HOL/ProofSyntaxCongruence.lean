import Mettapedia.Logic.HOL.ContextualTrinity

/-!
# Retained congruence proofs for HOL term constructors

Checked equalities lift through application and the logical constructors
using the existing one-hole comparison. Each result is a retained source
proof at the same context and ordered assumptions. Universal and existential
congruence remain in ContextualTrinity, with their explicit weakened contexts.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.ProofSyntax
open ContextualTrinity
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {σ τ : Ty Base}
variable {assumptions : List (Formula Const Γ)}

def andCongr {left left' right right' : Formula Const Γ}
    (first : ProofSyntax Const assumptions (.eq left left'))
    (second : ProofSyntax Const assumptions (.eq right right')) :
    ProofSyntax Const assumptions (.eq (.and left right) (.and left' right')) :=
  .eqTrans
    (castEq (congrArg (Term.and left) (instantiate_weaken left right))
      (congrArg (Term.and left') (instantiate_weaken left' right))
      (holeCongr (.and (.var .vz) (weaken right)) first))
    (castEq (congrArg (fun hole => Term.and hole right) (instantiate_weaken right left'))
      (congrArg (fun hole => Term.and hole right') (instantiate_weaken right' left'))
      (holeCongr (.and (weaken left') (.var .vz)) second))

def orCongr {left left' right right' : Formula Const Γ}
    (first : ProofSyntax Const assumptions (.eq left left'))
    (second : ProofSyntax Const assumptions (.eq right right')) :
    ProofSyntax Const assumptions (.eq (.or left right) (.or left' right')) :=
  .eqTrans
    (castEq (congrArg (Term.or left) (instantiate_weaken left right))
      (congrArg (Term.or left') (instantiate_weaken left' right))
      (holeCongr (.or (.var .vz) (weaken right)) first))
    (castEq (congrArg (fun hole => Term.or hole right) (instantiate_weaken right left'))
      (congrArg (fun hole => Term.or hole right') (instantiate_weaken right' left'))
      (holeCongr (.or (weaken left') (.var .vz)) second))

def impCongr {left left' right right' : Formula Const Γ}
    (first : ProofSyntax Const assumptions (.eq left left'))
    (second : ProofSyntax Const assumptions (.eq right right')) :
    ProofSyntax Const assumptions (.eq (.imp left right) (.imp left' right')) :=
  .eqTrans
    (castEq (congrArg (Term.imp left) (instantiate_weaken left right))
      (congrArg (Term.imp left') (instantiate_weaken left' right))
      (holeCongr (.imp (.var .vz) (weaken right)) first))
    (castEq (congrArg (fun hole => Term.imp hole right) (instantiate_weaken right left'))
      (congrArg (fun hole => Term.imp hole right') (instantiate_weaken right' left'))
      (holeCongr (.imp (weaken left') (.var .vz)) second))

def eqCongr {left left' right right' : Term Const Γ τ}
    (first : ProofSyntax Const assumptions (.eq left left'))
    (second : ProofSyntax Const assumptions (.eq right right')) :
    ProofSyntax Const assumptions (.eq (.eq left right) (.eq left' right')) :=
  .eqTrans
    (castEq (congrArg (Term.eq left) (instantiate_weaken left right))
      (congrArg (Term.eq left') (instantiate_weaken left' right))
      (holeCongr (.eq (.var .vz) (weaken right)) first))
    (castEq (congrArg (fun hole => Term.eq hole right) (instantiate_weaken right left'))
      (congrArg (fun hole => Term.eq hole right') (instantiate_weaken right' left'))
      (holeCongr (.eq (weaken left') (.var .vz)) second))

def appCongr {first first' : Term Const Γ (σ ⇒ τ)} {second second' : Term Const Γ σ}
    (function : ProofSyntax Const assumptions (.eq first first'))
    (argument : ProofSyntax Const assumptions (.eq second second')) :
    ProofSyntax Const assumptions (.eq (.app first second) (.app first' second')) :=
  .eqTrans (.eqApp second function) (.eqAppArg first' argument)

def notCongr {first second : Formula Const Γ}
    (proof : ProofSyntax Const assumptions (.eq first second)) :
    ProofSyntax Const assumptions (.eq (.not first) (.not second)) :=
  castEq rfl rfl (holeCongr (.not (.var .vz)) proof)

#print axioms andCongr
#print axioms orCongr
#print axioms impCongr
#print axioms eqCongr
#print axioms appCongr
#print axioms notCongr
end Mettapedia.Logic.HOL.ProofSyntax
