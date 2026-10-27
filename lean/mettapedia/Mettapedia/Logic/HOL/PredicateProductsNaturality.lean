import Mettapedia.Logic.HOL.PredicateProducts
import Mettapedia.Logic.HOL.ProofSyntaxRenamingSubstitution

/-!
# Naturality of retained predicate-product congruence

Substitution preserves the concrete proof construction for dependent-product
predicates, including its two binders and ordered hypotheses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
    {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)}

namespace ProofSyntax

theorem subst_castIndices_heq (θ : Subst Const Γ Ξ)
    {Δ' : List (Formula Const Γ)} {φ ψ : Formula Const Γ}
    (hypotheses : Δ = Δ') (conclusion : φ = ψ) (proof : ProofSyntax Const Δ φ) :
    HEq (subst θ (castIndices hypotheses conclusion proof)) (subst θ proof) := by
  cases hypotheses
  cases conclusion
  rfl

theorem rename_castIndices_heq (ρ : Rename Base Γ Ξ)
    {Δ' : List (Formula Const Γ)} {φ ψ : Formula Const Γ}
    (hypotheses : Δ = Δ') (conclusion : φ = ψ) (proof : ProofSyntax Const Δ φ) :
    HEq (rename ρ (castIndices hypotheses conclusion proof)) (rename ρ proof) := by
  cases hypotheses
  cases conclusion
  rfl

theorem subst_impCongr_heq (θ : Subst Const Γ Ξ)
    {left left' right right' : Formula Const Γ}
    (first : ProofSyntax Const Δ (.eq left left'))
    (second : ProofSyntax Const Δ (.eq right right')) :
    HEq (subst θ (impCongr first second)) (impCongr (subst θ first) (subst θ second)) := by
  simp only [impCongr, ContextualTrinity.castEq, subst]
  congr 1
  all_goals apply eq_of_heq
  all_goals refine (ContextualTrinity.BetaStep.subst_castConclusion_heq _ _ _).trans ?_
  all_goals refine HEq.trans ?_ (ContextualTrinity.castConclusion_heq _ _).symm
  all_goals refine (ContextualTrinity.BetaStep.subst_holeCongr_heq _ _ _).trans ?_
  all_goals apply ContextualTrinity.BetaStep.holeCongr_heq rfl
  all_goals first
    | rfl
    | simp only [HOL.subst, HOL.subst_weaken, Subst.lift]

end ProofSyntax

namespace PredicateFixedPoint

theorem weakenProof_heq {Δ' : List (Formula Const Γ)} (hypotheses : Δ = Δ')
    {σ : Ty Base} {φ ψ : Formula Const Γ} (conclusion : φ = ψ)
    {first : ProofSyntax Const Δ φ} {second : ProofSyntax Const Δ' ψ}
    (same : HEq first second) : HEq (weakenProof (σ := σ) first) (weakenProof (σ := σ) second) := by
  cases hypotheses
  cases conclusion
  cases same
  rfl

theorem subst_weakenProof_heq (θ : Subst Const Γ Ξ) {σ : Ty Base} {φ : Formula Const Γ}
    (proof : ProofSyntax Const Δ φ) :
    HEq (ProofSyntax.subst (Subst.lift (σ := σ) θ) (weakenProof proof))
      (weakenProof (σ := σ) (ProofSyntax.subst θ proof)) := by
  unfold weakenProof
  refine (ProofSyntax.subst_castIndices_heq _ _ _ _).trans ?_
  refine HEq.trans ?_ (ProofSyntax.castIndices_heq _ _ _).symm
  exact ProofSyntax.subst_rename_square Rename.weaken Rename.weaken θ (Subst.lift θ)
    (fun _ => rfl) proof

end PredicateFixedPoint

namespace PredicateProducts

private theorem subst_pi_body (θ : Subst Const Γ Ξ) {σ τ : Ty Base}
    (domain : Term Const Γ (σ ⇒ .prop)) (family : Term Const (σ :: Γ) (τ ⇒ .prop)) :
    HOL.subst (Subst.lift θ)
      (.all (.imp (.app (weaken (weaken domain)) (.var .vz))
        (.app (HOL.rename (Rename.lift (Rename.weaken (σ := σ ⇒ τ))) family)
          (.app (.var (.vs .vz)) (.var .vz))))) =
      .all (.imp (.app (weaken (weaken (HOL.subst θ domain))) (.var .vz))
        (.app (HOL.rename (Rename.lift (Rename.weaken (σ := σ ⇒ τ)))
          (HOL.subst (Subst.lift θ) family)) (.app (.var (.vs .vz)) (.var .vz)))) := by
  simp only [HOL.subst, HOL.subst_weaken, ContextualTrinity.subst_lift_rename_lift_weaken,
    Subst.lift]
  rfl

private theorem allCongr_heq {Δ' : List (Formula Const Γ)} (hypotheses : Δ = Δ')
    {σ : Ty Base} {left left' right right' : Formula Const (σ :: Γ)}
    (sources : left = left') (targets : right = right')
    {first : ProofSyntax Const (weakenHyps Δ) (.eq left right)}
    {second : ProofSyntax Const (weakenHyps Δ') (.eq left' right')}
    (same : HEq first second) :
    HEq (ContextualTrinity.allCongr first) (ContextualTrinity.allCongr second) := by
  cases hypotheses
  cases sources
  cases targets
  cases same
  rfl

theorem subst_congruence_heq (θ : Subst Const Γ Ξ) {σ τ : Ty Base}
    {domain domain' : Term Const Γ (σ ⇒ .prop)}
    {family family' : Term Const (σ :: Γ) (τ ⇒ .prop)}
    (domains : ProofSyntax Const Δ (.eq domain domain'))
    (families : ProofSyntax Const (weakenHyps (σ := σ) Δ) (.eq family family')) :
    HEq (ProofSyntax.subst θ (congruence domains families))
      (congruence (ProofSyntax.subst θ domains)
        (ProofSyntax.castIndices (ProofSyntax.subst_weakenHyps θ Δ) rfl
          (ProofSyntax.subst (Subst.lift θ) families))) := by
  simp only [congruence, ProofSyntax.subst]
  congr 1
  all_goals first
    | exact subst_pi_body θ _ _
    | skip
  all_goals try refine (ProofSyntax.id_mp_heq _ _).trans ?_
  refine (ContextualTrinity.BetaStep.subst_allCongr_heq (Subst.lift θ) _
    (ProofSyntax.castIndices_heq (ProofSyntax.subst_weakenHyps (Subst.lift θ) _) rfl _).symm).trans ?_
  apply allCongr_heq (ProofSyntax.subst_weakenHyps θ Δ)
  · simp only [HOL.subst, HOL.subst_weaken, ContextualTrinity.subst_lift_rename_lift_weaken, Subst.lift]
    rfl
  · simp only [HOL.subst, HOL.subst_weaken, ContextualTrinity.subst_lift_rename_lift_weaken, Subst.lift]
    rfl
  · refine (ProofSyntax.castIndices_heq _ _ _).trans ?_
    refine (ProofSyntax.subst_impCongr_heq _ _ _).trans ?_
    congr 1
    all_goals try solve | simp only [ProofSyntax.subst_weakenHyps]
    all_goals simp only [ProofSyntax.subst]
    all_goals congr 1
    all_goals try solve | simp only [HOL.subst, HOL.subst_weaken, ProofSyntax.subst_weakenHyps,
      ContextualTrinity.subst_lift_rename_lift_weaken, Subst.lift, HOL.rename, Rename.weaken]
    · refine (PredicateFixedPoint.subst_weakenProof_heq _ _).trans ?_
      apply PredicateFixedPoint.weakenProof_heq (ProofSyntax.subst_weakenHyps θ Δ)
        (HOL.subst_weaken θ _)
      exact PredicateFixedPoint.subst_weakenProof_heq θ domains
    · refine (ProofSyntax.subst_castIndices_heq _ _ _ _).trans ?_
      refine HEq.trans ?_ (ProofSyntax.castIndices_heq _ _ _).symm
      refine HEq.trans ?_ (ProofSyntax.rename_castIndices_heq _ _ _ _).symm
      apply ProofSyntax.subst_rename_square
      intro type index
      cases index with
      | vz => rfl
      | vs index =>
          simpa only [Subst.lift, Rename.lift, Rename.weaken] using
            (HOL.rename_lift_weaken (Rename.weaken (σ := σ ⇒ τ)) (θ index)).symm

end PredicateProducts

#print axioms ProofSyntax.subst_impCongr_heq
#print axioms PredicateFixedPoint.subst_weakenProof_heq
#print axioms PredicateProducts.subst_congruence_heq

end Mettapedia.Logic.HOL
