import Mettapedia.Logic.HOL.Syntax.Subst

/-!
# Object-binder depth of intrinsic HOL terms

The depth counts simultaneous nested lambda, universal and existential
binders. It bounds the fresh binding slots needed by a named interpretation;
constants, variables and type annotations introduce no object binders.
Substitution is bounded by the source depth plus the maximum image depth;
renaming and lifting preserve that image bound.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Term

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {gamma delta : Ctx Base} {type : Ty Base}

def binderDepth : {gamma : Ctx Base} → {type : Ty Base} → Term Const gamma type → Nat
  | _, _, .var _ | _, _, .const _ | _, _, .top | _, _, .bot => 0
  | _, _, .app first second | _, _, .and first second | _, _, .or first second
  | _, _, .imp first second | _, _, .eq first second => max (binderDepth first) (binderDepth second)
  | _, _, .lam body | _, _, .all body | _, _, .ex body => binderDepth body + 1
  | _, _, .not body => binderDepth body

theorem binderDepth_rename (rho : Rename Base gamma delta) (source : Term Const gamma type) :
    binderDepth (HOL.rename rho source) = binderDepth source := by
  induction source generalizing delta <;> simp_all [HOL.rename, binderDepth]

#print axioms binderDepth_rename

end Mettapedia.Logic.HOL.Term

namespace Mettapedia.Logic.HOL
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

namespace Subst

def maxBinderDepth {delta : Ctx Base} : {gamma : Ctx Base} → Subst Const gamma delta → Nat
  | [], _ => 0
  | _ :: gamma, substitution =>
      max (substitution .vz).binderDepth
        (maxBinderDepth (gamma := gamma) (fun index => substitution (.vs index)))

theorem binderDepth_le_maxBinderDepth {delta : Ctx Base} :
    ∀ {gamma : Ctx Base} (substitution : Subst Const gamma delta) {type} (index : Var gamma type),
      (substitution index).binderDepth ≤ maxBinderDepth substitution := by
  intro gamma
  induction gamma with
  | nil => intro substitution type index; nomatch index
  | cons domain gamma ih =>
      intro substitution type index
      cases index with
      | vz => exact Nat.le_max_left _ _
      | vs index =>
          exact Nat.le_trans (ih (fun index => substitution (.vs index)) index) (Nat.le_max_right _ _)

theorem maxBinderDepth_rename {delta xi : Ctx Base} (rho : Rename Base delta xi) :
    ∀ {gamma : Ctx Base} (substitution : Subst Const gamma delta),
      maxBinderDepth (fun index => rename rho (substitution index)) = maxBinderDepth substitution := by
  intro gamma
  induction gamma with
  | nil => intro substitution; rfl
  | cons domain gamma ih =>
      intro substitution
      simpa only [maxBinderDepth, Term.binderDepth_rename] using
        congrArg (max (substitution .vz).binderDepth) (ih (fun index => substitution (.vs index)))

theorem maxBinderDepth_lift {gamma delta : Ctx Base} {domain : Ty Base}
    (substitution : Subst Const gamma delta) :
    maxBinderDepth (Subst.lift (σ := domain) substitution) = maxBinderDepth substitution := by
  change max 0 (maxBinderDepth (fun index => rename Rename.weaken (substitution index))) = _
  rw [maxBinderDepth_rename, Nat.zero_max]

end Subst

namespace Term

theorem binderDepth_subst_le {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ {delta : Ctx Base} (substitution : Subst Const gamma delta),
      (subst substitution source).binderDepth ≤ source.binderDepth + (Subst.maxBinderDepth substitution) := by
  induction source with
  | var index =>
      intro delta substitution
      simpa only [subst, binderDepth, Nat.zero_add] using
        Subst.binderDepth_le_maxBinderDepth substitution index
  | const _ | top | bot => intros; simp [subst, binderDepth]
  | app first second ihFirst ihSecond | and first second ihFirst ihSecond
  | or first second ihFirst ihSecond | imp first second ihFirst ihSecond
  | eq first second ihFirst ihSecond =>
      intro delta substitution
      have firstBound := ihFirst substitution
      have secondBound := ihSecond substitution
      change max (subst substitution first).binderDepth (subst substitution second).binderDepth ≤
        max first.binderDepth second.binderDepth + Subst.maxBinderDepth substitution
      omega
  | not body ih => exact ih
  | lam body ih | all body ih | ex body ih =>
      intro delta substitution
      have bodyBound := ih (Subst.lift substitution)
      rw [Subst.maxBinderDepth_lift] at bodyBound
      change (subst (Subst.lift substitution) body).binderDepth + 1 ≤
        body.binderDepth + 1 + (Subst.maxBinderDepth substitution)
      omega

theorem instantiation_can_increase_depth :
    let Const : Ty Empty → Type := fun _ => Empty
    let source : Term Const [.arr .prop .prop] (.arr .prop .prop) := .var .vz
    let image : Term Const [] (.arr .prop .prop) := .lam (.var .vz)
    source.binderDepth < (instantiate image source).binderDepth := by decide

end Term

#print axioms Subst.binderDepth_le_maxBinderDepth
#print axioms Subst.maxBinderDepth_rename
#print axioms Subst.maxBinderDepth_lift
#print axioms Term.binderDepth_subst_le
#print axioms Term.instantiation_can_increase_depth
end Mettapedia.Logic.HOL
