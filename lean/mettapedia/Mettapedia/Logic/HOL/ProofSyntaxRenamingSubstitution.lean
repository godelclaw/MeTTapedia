import Mettapedia.Logic.HOL.ProofSyntaxConstantSubstitution

/-!
# Renaming as retained-proof substitution

The two existing programs traverse the same retained inference constructors.
Their equality is heterogeneous only because their sequent indices are
propositionally equal. No proof is replaced by mere derivability.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ProofSyntax

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

theorem ofRename_lift {Γ Ξ : Ctx Base} (ρ : Rename Base Γ Ξ) (type : Ty Base) :
    (Subst.lift (σ := type) (Subst.ofRename (Const := Const) ρ) : Subst Const (type :: Γ) (type :: Ξ)) =
      (fun {τ} => Subst.ofRename (Const := Const) (Rename.lift (σ := type) ρ) (τ := τ)) := by
  funext τ index
  cases index <;> rfl

theorem ofRename_lift_apply {Γ Ξ : Ctx Base} (ρ : Rename Base Γ Ξ) {type τ : Ty Base}
    (index : Var (type :: Γ) τ) :
    Subst.lift (Subst.ofRename (Const := Const) ρ) index =
      Subst.ofRename (Rename.lift ρ) index := by
  cases index <;> rfl

theorem hypotheses_ofRename {Γ Ξ : Ctx Base} (ρ : Rename Base Γ Ξ) (Δ : List (Formula Const Γ)) :
    Δ.map (HOL.subst (Subst.ofRename ρ)) = Δ.map (HOL.rename ρ) := by
  apply List.map_congr_left
  intro term _
  exact HOL.subst_ofRename ρ term

/-- All rules, hypothesis occurrences and term arguments are retained. -/
theorem rename_subst_heq {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (ρ : Rename Base Γ Ξ) (proof : ProofSyntax Const Δ φ) :
    HEq (rename ρ proof) (subst (Subst.ofRename ρ) proof) := by
  induction proof generalizing Ξ with
  | _ =>
      simp only [rename, subst]
      try refine (castIndices_heq _ _ _).trans ?_
      try refine HEq.trans ?_ (mpr_heq _ _).symm
      try refine HEq.trans ?_ (mp_heq _ _).symm
      try refine HEq.trans ?_ (id_mp_heq _ _).symm
      all_goals congr 1
      all_goals try refine (castIndices_heq _ _ _).trans ?_
      all_goals try refine HEq.trans ?_ (id_mp_heq _ _).symm
      all_goals try rw [ofRename_lift]
      all_goals first
        | rfl
        | exact (HOL.subst_ofRename _ _).symm
        | exact (hypotheses_ofRename _ _).symm
        | exact fin_cast_heq _ _
        | exact (fin_cast_heq _ _).trans (fin_cast_heq _ _).symm
        | assumption
        | apply_assumption

/-- A commuting renaming/substitution square acts equally on the entire
retained proof, not just on its conclusion. -/
theorem subst_rename_square {Γ Γ' Ξ Ξ' : Ctx Base}
    (ρ : Rename Base Γ Γ') (ρ' : Rename Base Ξ Ξ')
    (θ : Subst Const Γ Ξ) (θ' : Subst Const Γ' Ξ')
    (commutes : ∀ {τ : Ty Base} (index : Var Γ τ), θ' (ρ index) = HOL.rename ρ' (θ index))
    {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} (proof : ProofSyntax Const Δ φ) :
    HEq (subst θ' (rename ρ proof)) (rename ρ' (subst θ proof)) := by
  refine (subst_heq_of_heq θ' (hypotheses_ofRename ρ Δ).symm
    (HOL.subst_ofRename ρ φ).symm (rename_subst_heq ρ proof)).trans ?_
  refine (subst_comp_heq proof θ' (Subst.ofRename ρ)).symm.trans ?_
  refine HEq.trans ?_ (rename_subst_heq ρ' (subst θ proof)).symm
  apply subst_subst_heq
  intro type index
  exact (commutes index).trans (HOL.subst_ofRename ρ' (θ index)).symm

#print axioms rename_subst_heq
#print axioms subst_rename_square

end Mettapedia.Logic.HOL.ProofSyntax
