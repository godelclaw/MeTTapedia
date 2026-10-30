import Mettapedia.Logic.HOL.ProofSyntaxConstantSubstitution

/-!
# Renaming with a shared target hypothesis list

The target list is computed once per scope and passed through all non-binder
rules. The resulting retained proof is exactly the existing renaming.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.ProofSyntax
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

def renameAt {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)} {formula : Formula Const Γ}
    (rho : Rename Base Γ Ξ) (target : List (Formula Const Ξ))
    (matching : Δ.map (HOL.rename rho) = target) (proof : ProofSyntax Const Δ formula) :
    ProofSyntax Const target (HOL.rename rho formula) :=
  match proof with
  | .hyp occurrence => by
      let selected : Fin target.length := occurrence.cast (by rw [← matching, List.length_map])
      apply castIndices rfl ?_ (.hyp (Δ := target) selected)
      subst target
      simp [selected, List.get_eq_getElem]
  | .topI => .topI
  | .botE proof => .botE (renameAt rho target matching proof)
  | .andI first second => .andI (renameAt rho target matching first) (renameAt rho target matching second)
  | .andEL proof => .andEL (renameAt rho target matching proof)
  | .andER proof => .andER (renameAt rho target matching proof)
  | .orIL proof => .orIL (renameAt rho target matching proof)
  | .orIR proof => .orIR (renameAt rho target matching proof)
  | .orE cases first second => .orE (renameAt rho target matching cases)
      (renameAt rho (_ :: target) (by simp only [List.map_cons, matching]) first)
      (renameAt rho (_ :: target) (by simp only [List.map_cons, matching]) second)
  | .impI proof => .impI (renameAt rho (_ :: target) (by simp only [List.map_cons, matching]) proof)
  | .impE first second => .impE (renameAt rho target matching first) (renameAt rho target matching second)
  | .notI proof => .notI (renameAt rho (_ :: target) (by simp only [List.map_cons, matching]) proof)
  | .notE first second => .notE (renameAt rho target matching first) (renameAt rho target matching second)
  | .allI proof => .allI (renameAt (Rename.lift rho) (weakenHyps target)
      (by rw [← ExtDerivation.rename_weakenHyps, matching]) proof)
  | .allE term proof => castIndices rfl (ExtDerivation.rename_instantiate rho term _).symm
      (.allE (HOL.rename rho term) (renameAt rho target matching proof))
  | .exI term proof => .exI (HOL.rename rho term)
      (castIndices rfl (ExtDerivation.rename_instantiate rho term _) (renameAt rho target matching proof))
  | .exE first second => .exE (renameAt rho target matching first)
      (castIndices rfl (ExtDerivation.rename_weaken rho _)
        (renameAt (Rename.lift rho) (_ :: weakenHyps target)
          (by simp only [List.map_cons]; rw [← ExtDerivation.rename_weakenHyps, matching]) second))
  | .eqRefl term => .eqRefl (HOL.rename rho term)
  | .eqSymm proof => .eqSymm (renameAt rho target matching proof)
  | .eqTrans first second => .eqTrans (renameAt rho target matching first) (renameAt rho target matching second)
  | .eqPropI first second => .eqPropI (renameAt rho target matching first) (renameAt rho target matching second)
  | .eqPropEL proof => .eqPropEL (renameAt rho target matching proof)
  | .eqPropER proof => .eqPropER (renameAt rho target matching proof)
  | .eqApp term proof => .eqApp (HOL.rename rho term) (renameAt rho target matching proof)
  | .eqAppArg term proof => .eqAppArg (HOL.rename rho term) (renameAt rho target matching proof)
  | .eqLam proof => .eqLam (renameAt (Rename.lift rho) (weakenHyps target)
      (by rw [← ExtDerivation.rename_weakenHyps, matching]) proof)
  | .funExt proof => .funExt (castIndices rfl
      (by simp [HOL.rename, Rename.lift, ExtDerivation.rename_weaken]) (renameAt rho target matching proof))
  | .beta term body => castIndices rfl
      (by simp [HOL.rename, ExtDerivation.rename_instantiate])
      (.beta (Δ := target) (HOL.rename rho term) (HOL.rename (Rename.lift rho) body))
  | .eta function => castIndices rfl (by simp [HOL.rename, Rename.lift, ExtDerivation.rename_weaken])
      (.eta (Δ := target) (HOL.rename rho function))

theorem renameAt_eq {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)} {formula : Formula Const Γ}
    (rho : Rename Base Γ Ξ) (target : List (Formula Const Ξ))
    (matching : Δ.map (HOL.rename rho) = target) (proof : ProofSyntax Const Δ formula) :
    renameAt rho target matching proof = castIndices matching rfl (rename rho proof) := by
  induction proof generalizing Ξ with
  | _ =>
      cases matching
      simp_all only [renameAt, rename]
      try rfl
      all_goals
        congr 1
        apply eq_of_heq
        exact (castIndices_heq _ _ _).trans ((castIndices_heq _ _ _).trans
          (castIndices_heq _ _ _).symm)

def renameShared {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)} {formula : Formula Const Γ}
    (rho : Rename Base Γ Ξ) (proof : ProofSyntax Const Δ formula) :
    ProofSyntax Const (Δ.map (HOL.rename rho)) (HOL.rename rho formula) :=
  renameAt rho (Δ.map (HOL.rename rho)) rfl proof

theorem renameShared_eq {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)} {formula : Formula Const Γ}
    (rho : Rename Base Γ Ξ) (proof : ProofSyntax Const Δ formula) : renameShared rho proof = rename rho proof :=
  renameAt_eq rho _ rfl proof

end Mettapedia.Logic.HOL.ProofSyntax
