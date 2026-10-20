import Mettapedia.TypeTheory.ContextualCBPVOperational

/-!
# Normalization of the recursion-free contextual CBPV calculus

Every closed returner of the recursion-free calculus has an operational
unfolding (`Comp.unfolds_exists`). With `Unfolds.sound` this makes the
agreement of the operational reading with the program semantics total on the
calculus: the operational tree exists and is observed exactly as the
denotation (`Comp.observe_operational`).

The proof is the classical computability argument (Tait, Plotkin; for CBPV
see Forster, Schäfer, Spies and Stark, CPP 2019): a logical relation on
closed terms (`GoodV`, `GoodC`), closed under backward steps and under every
effect operation, and a fundamental lemma over closing substitutions. The
substitution algebra it needs (`rename_rename`, `subst_rename`,
`rename_subst`, `subst_subst`, `subst_id`) is proved first, pointwise.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualDependentSequencing

variable {sig : Signature}

/-! ## Substitution algebra -/

theorem Ren.lift_comp_pointwise {Ground : Type} {source middle target : List (VTy Ground)}
    {ρ : Ren source middle} {ρ' : Ren middle target} {π : Ren source target}
    (agree : ∀ type index, π type index = ρ' type (ρ type index)) {bound : VTy Ground} :
    ∀ type index, (π.lift bound) type index = (ρ'.lift bound) type ((ρ.lift bound) type index)
  | _, .zero => rfl
  | _, .succ index => by simp only [Ren.lift]; rw [agree]

mutual
  theorem Val.rename_rename {source middle target : List (VTy sig.Ground)} (ρ : Ren source middle) (ρ' : Ren middle target) (π : Ren source target) (agree : ∀ type index, π type index = ρ' type (ρ type index)) :
      {type : VTy sig.Ground} → (term : Val sig source type) →
        (term.rename ρ).rename ρ' = term.rename π
    | _, .var x => by simp only [Val.rename]; rw [agree]
    | _, .const _ _ => rfl
    | _, .prim f a => by
        simp only [Val.rename]
        rw [Val.rename_rename (ρ) (ρ') (π) (agree) a]
    | _, .unit => rfl
    | _, .pair l r => by
        simp only [Val.rename]
        rw [Val.rename_rename (ρ) (ρ') (π) (agree) l, Val.rename_rename (ρ) (ρ') (π) (agree) r]
    | _, .thunk M => by
        simp only [Val.rename]
        rw [Comp.rename_rename (ρ) (ρ') (π) (agree) M]
  theorem Comp.rename_rename {source middle target : List (VTy sig.Ground)} (ρ : Ren source middle) (ρ' : Ren middle target) (π : Ren source target) (agree : ∀ type index, π type index = ρ' type (ρ type index)) :
      {type : CTy sig.Ground} → (term : Comp sig source type) →
        (term.rename ρ).rename ρ' = term.rename π
    | _, .ret v => by
        simp only [Comp.rename]
        rw [Val.rename_rename (ρ) (ρ') (π) (agree) v]
    | _, .bind M N => by
        simp only [Comp.rename]
        rw [Comp.rename_rename (ρ) (ρ') (π) (agree) M, Comp.rename_rename ((ρ).lift _) ((ρ').lift _) ((π).lift _) (Ren.lift_comp_pointwise (agree)) N]
    | _, .force v => by
        simp only [Comp.rename]
        rw [Val.rename_rename (ρ) (ρ') (π) (agree) v]
    | _, .lam N => by
        simp only [Comp.rename]
        rw [Comp.rename_rename ((ρ).lift _) ((ρ').lift _) ((π).lift _) (Ren.lift_comp_pointwise (agree)) N]
    | _, .app M v => by
        simp only [Comp.rename]
        rw [Comp.rename_rename (ρ) (ρ') (π) (agree) M, Val.rename_rename (ρ) (ρ') (π) (agree) v]
    | _, .split v N => by
        simp only [Comp.rename]
        rw [Val.rename_rename (ρ) (ρ') (π) (agree) v, Comp.rename_rename (((ρ).lift _).lift _) (((ρ').lift _).lift _) (((π).lift _).lift _) (Ren.lift_comp_pointwise (Ren.lift_comp_pointwise (agree))) N]
    | _, .choose M K => by
        simp only [Comp.rename]
        rw [Comp.rename_rename (ρ) (ρ') (π) (agree) M, Comp.rename_rename (ρ) (ρ') (π) (agree) K]
    | _, .read N => by
        simp only [Comp.rename]
        rw [Comp.rename_rename ((ρ).lift _) ((ρ').lift _) ((π).lift _) (Ren.lift_comp_pointwise (agree)) N]
    | _, .write v M => by
        simp only [Comp.rename]
        rw [Val.rename_rename (ρ) (ρ') (π) (agree) v, Comp.rename_rename (ρ) (ρ') (π) (agree) M]
    | _, .intent v M => by
        simp only [Comp.rename]
        rw [Val.rename_rename (ρ) (ρ') (π) (agree) v, Comp.rename_rename (ρ) (ρ') (π) (agree) M]
    | _, .raise _ v => by
        simp only [Comp.rename]
        rw [Val.rename_rename (ρ) (ρ') (π) (agree) v]
    | _, .handle M _ N H => by
        simp only [Comp.rename]
        rw [Comp.rename_rename (ρ) (ρ') (π) (agree) M, Comp.rename_rename ((ρ).lift _) ((ρ').lift _) ((π).lift _) (Ren.lift_comp_pointwise (agree)) N, Comp.rename_rename ((ρ).lift _) ((ρ').lift _) ((π).lift _) (Ren.lift_comp_pointwise (agree)) H]
end

theorem Subst.lift_ren_pointwise {source middle target : List (VTy sig.Ground)}
    {ρ : Ren source middle} {τ : Subst sig middle target} {π : Subst sig source target}
    (agree : ∀ type index, π type index = τ type (ρ type index)) {bound : VTy sig.Ground} :
    ∀ type index, (π.lift bound) type index = (τ.lift bound) type ((ρ.lift bound) type index)
  | _, .zero => rfl
  | _, .succ index => by simp only [Subst.lift, Ren.lift]; rw [agree]

theorem Subst.lift_rename_pointwise {source middle target : List (VTy sig.Ground)}
    {σ : Subst sig source middle} {ρ : Ren middle target} {π : Subst sig source target}
    (agree : ∀ type index, π type index = (σ type index).rename ρ) {bound : VTy sig.Ground} :
    ∀ type index, (π.lift bound) type index = ((σ.lift bound) type index).rename (ρ.lift bound)
  | _, .zero => rfl
  | _, .succ index => by
      simp only [Subst.lift]
      rw [agree, Val.rename_rename ρ (Ren.weaken bound) (fun _ found => .succ (ρ _ found))
          (fun _ _ => rfl),
        Val.rename_rename (Ren.weaken bound) (ρ.lift bound) (fun _ found => .succ (ρ _ found))
          (fun _ _ => rfl)]

mutual
  theorem Val.subst_rename {source middle target : List (VTy sig.Ground)} (ρ : Ren source middle) (τ : Subst sig middle target) (π : Subst sig source target) (agree : ∀ type index, π type index = τ type (ρ type index)) :
      {type : VTy sig.Ground} → (term : Val sig source type) →
        (term.rename ρ).subst τ = term.subst π
    | _, .var x => by simp only [Val.rename, Val.subst]; rw [agree]
    | _, .const _ _ => rfl
    | _, .prim f a => by
        simp only [Val.rename, Val.subst]
        rw [Val.subst_rename (ρ) (τ) (π) (agree) a]
    | _, .unit => rfl
    | _, .pair l r => by
        simp only [Val.rename, Val.subst]
        rw [Val.subst_rename (ρ) (τ) (π) (agree) l, Val.subst_rename (ρ) (τ) (π) (agree) r]
    | _, .thunk M => by
        simp only [Val.rename, Val.subst]
        rw [Comp.subst_rename (ρ) (τ) (π) (agree) M]
  theorem Comp.subst_rename {source middle target : List (VTy sig.Ground)} (ρ : Ren source middle) (τ : Subst sig middle target) (π : Subst sig source target) (agree : ∀ type index, π type index = τ type (ρ type index)) :
      {type : CTy sig.Ground} → (term : Comp sig source type) →
        (term.rename ρ).subst τ = term.subst π
    | _, .ret v => by
        simp only [Comp.rename, Comp.subst]
        rw [Val.subst_rename (ρ) (τ) (π) (agree) v]
    | _, .bind M N => by
        simp only [Comp.rename, Comp.subst]
        rw [Comp.subst_rename (ρ) (τ) (π) (agree) M, Comp.subst_rename ((ρ).lift _) ((τ).lift _) ((π).lift _) (Subst.lift_ren_pointwise (agree)) N]
    | _, .force v => by
        simp only [Comp.rename, Comp.subst]
        rw [Val.subst_rename (ρ) (τ) (π) (agree) v]
    | _, .lam N => by
        simp only [Comp.rename, Comp.subst]
        rw [Comp.subst_rename ((ρ).lift _) ((τ).lift _) ((π).lift _) (Subst.lift_ren_pointwise (agree)) N]
    | _, .app M v => by
        simp only [Comp.rename, Comp.subst]
        rw [Comp.subst_rename (ρ) (τ) (π) (agree) M, Val.subst_rename (ρ) (τ) (π) (agree) v]
    | _, .split v N => by
        simp only [Comp.rename, Comp.subst]
        rw [Val.subst_rename (ρ) (τ) (π) (agree) v, Comp.subst_rename (((ρ).lift _).lift _) (((τ).lift _).lift _) (((π).lift _).lift _) (Subst.lift_ren_pointwise (Subst.lift_ren_pointwise (agree))) N]
    | _, .choose M K => by
        simp only [Comp.rename, Comp.subst]
        rw [Comp.subst_rename (ρ) (τ) (π) (agree) M, Comp.subst_rename (ρ) (τ) (π) (agree) K]
    | _, .read N => by
        simp only [Comp.rename, Comp.subst]
        rw [Comp.subst_rename ((ρ).lift _) ((τ).lift _) ((π).lift _) (Subst.lift_ren_pointwise (agree)) N]
    | _, .write v M => by
        simp only [Comp.rename, Comp.subst]
        rw [Val.subst_rename (ρ) (τ) (π) (agree) v, Comp.subst_rename (ρ) (τ) (π) (agree) M]
    | _, .intent v M => by
        simp only [Comp.rename, Comp.subst]
        rw [Val.subst_rename (ρ) (τ) (π) (agree) v, Comp.subst_rename (ρ) (τ) (π) (agree) M]
    | _, .raise _ v => by
        simp only [Comp.rename, Comp.subst]
        rw [Val.subst_rename (ρ) (τ) (π) (agree) v]
    | _, .handle M _ N H => by
        simp only [Comp.rename, Comp.subst]
        rw [Comp.subst_rename (ρ) (τ) (π) (agree) M, Comp.subst_rename ((ρ).lift _) ((τ).lift _) ((π).lift _) (Subst.lift_ren_pointwise (agree)) N, Comp.subst_rename ((ρ).lift _) ((τ).lift _) ((π).lift _) (Subst.lift_ren_pointwise (agree)) H]
end

mutual
  theorem Val.rename_subst {source middle target : List (VTy sig.Ground)} (σ : Subst sig source middle) (ρ : Ren middle target) (π : Subst sig source target) (agree : ∀ type index, π type index = (σ type index).rename ρ) :
      {type : VTy sig.Ground} → (term : Val sig source type) →
        (term.subst σ).rename ρ = term.subst π
    | _, .var x => by simp only [Val.subst]; rw [agree]
    | _, .const _ _ => rfl
    | _, .prim f a => by
        simp only [Val.rename, Val.subst]
        rw [Val.rename_subst (σ) (ρ) (π) (agree) a]
    | _, .unit => rfl
    | _, .pair l r => by
        simp only [Val.rename, Val.subst]
        rw [Val.rename_subst (σ) (ρ) (π) (agree) l, Val.rename_subst (σ) (ρ) (π) (agree) r]
    | _, .thunk M => by
        simp only [Val.rename, Val.subst]
        rw [Comp.rename_subst (σ) (ρ) (π) (agree) M]
  theorem Comp.rename_subst {source middle target : List (VTy sig.Ground)} (σ : Subst sig source middle) (ρ : Ren middle target) (π : Subst sig source target) (agree : ∀ type index, π type index = (σ type index).rename ρ) :
      {type : CTy sig.Ground} → (term : Comp sig source type) →
        (term.subst σ).rename ρ = term.subst π
    | _, .ret v => by
        simp only [Comp.rename, Comp.subst]
        rw [Val.rename_subst (σ) (ρ) (π) (agree) v]
    | _, .bind M N => by
        simp only [Comp.rename, Comp.subst]
        rw [Comp.rename_subst (σ) (ρ) (π) (agree) M, Comp.rename_subst ((σ).lift _) ((ρ).lift _) ((π).lift _) (Subst.lift_rename_pointwise (agree)) N]
    | _, .force v => by
        simp only [Comp.rename, Comp.subst]
        rw [Val.rename_subst (σ) (ρ) (π) (agree) v]
    | _, .lam N => by
        simp only [Comp.rename, Comp.subst]
        rw [Comp.rename_subst ((σ).lift _) ((ρ).lift _) ((π).lift _) (Subst.lift_rename_pointwise (agree)) N]
    | _, .app M v => by
        simp only [Comp.rename, Comp.subst]
        rw [Comp.rename_subst (σ) (ρ) (π) (agree) M, Val.rename_subst (σ) (ρ) (π) (agree) v]
    | _, .split v N => by
        simp only [Comp.rename, Comp.subst]
        rw [Val.rename_subst (σ) (ρ) (π) (agree) v, Comp.rename_subst (((σ).lift _).lift _) (((ρ).lift _).lift _) (((π).lift _).lift _) (Subst.lift_rename_pointwise (Subst.lift_rename_pointwise (agree))) N]
    | _, .choose M K => by
        simp only [Comp.rename, Comp.subst]
        rw [Comp.rename_subst (σ) (ρ) (π) (agree) M, Comp.rename_subst (σ) (ρ) (π) (agree) K]
    | _, .read N => by
        simp only [Comp.rename, Comp.subst]
        rw [Comp.rename_subst ((σ).lift _) ((ρ).lift _) ((π).lift _) (Subst.lift_rename_pointwise (agree)) N]
    | _, .write v M => by
        simp only [Comp.rename, Comp.subst]
        rw [Val.rename_subst (σ) (ρ) (π) (agree) v, Comp.rename_subst (σ) (ρ) (π) (agree) M]
    | _, .intent v M => by
        simp only [Comp.rename, Comp.subst]
        rw [Val.rename_subst (σ) (ρ) (π) (agree) v, Comp.rename_subst (σ) (ρ) (π) (agree) M]
    | _, .raise _ v => by
        simp only [Comp.rename, Comp.subst]
        rw [Val.rename_subst (σ) (ρ) (π) (agree) v]
    | _, .handle M _ N H => by
        simp only [Comp.rename, Comp.subst]
        rw [Comp.rename_subst (σ) (ρ) (π) (agree) M, Comp.rename_subst ((σ).lift _) ((ρ).lift _) ((π).lift _) (Subst.lift_rename_pointwise (agree)) N, Comp.rename_subst ((σ).lift _) ((ρ).lift _) ((π).lift _) (Subst.lift_rename_pointwise (agree)) H]
end

theorem Subst.lift_subst_pointwise {source middle target : List (VTy sig.Ground)}
    {σ : Subst sig source middle} {τ : Subst sig middle target} {π : Subst sig source target}
    (agree : ∀ type index, π type index = (σ type index).subst τ) {bound : VTy sig.Ground} :
    ∀ type index, (π.lift bound) type index = ((σ.lift bound) type index).subst (τ.lift bound)
  | _, .zero => rfl
  | _, .succ index => by
      simp only [Subst.lift]
      rw [agree, Val.rename_subst τ (Ren.weaken bound)
          (fun _ found => (τ _ found).rename (Ren.weaken bound)) (fun _ _ => rfl),
        Val.subst_rename (Ren.weaken bound) (τ.lift bound)
          (fun _ found => (τ _ found).rename (Ren.weaken bound)) (fun _ _ => rfl)]

mutual
  theorem Val.subst_subst {source middle target : List (VTy sig.Ground)} (σ : Subst sig source middle) (τ : Subst sig middle target) (π : Subst sig source target) (agree : ∀ type index, π type index = (σ type index).subst τ) :
      {type : VTy sig.Ground} → (term : Val sig source type) →
        (term.subst σ).subst τ = term.subst π
    | _, .var x => by simp only [Val.subst]; rw [agree]
    | _, .const _ _ => rfl
    | _, .prim f a => by
        simp only [Val.subst]
        rw [Val.subst_subst (σ) (τ) (π) (agree) a]
    | _, .unit => rfl
    | _, .pair l r => by
        simp only [Val.subst]
        rw [Val.subst_subst (σ) (τ) (π) (agree) l, Val.subst_subst (σ) (τ) (π) (agree) r]
    | _, .thunk M => by
        simp only [Val.subst]
        rw [Comp.subst_subst (σ) (τ) (π) (agree) M]
  theorem Comp.subst_subst {source middle target : List (VTy sig.Ground)} (σ : Subst sig source middle) (τ : Subst sig middle target) (π : Subst sig source target) (agree : ∀ type index, π type index = (σ type index).subst τ) :
      {type : CTy sig.Ground} → (term : Comp sig source type) →
        (term.subst σ).subst τ = term.subst π
    | _, .ret v => by
        simp only [Comp.subst]
        rw [Val.subst_subst (σ) (τ) (π) (agree) v]
    | _, .bind M N => by
        simp only [Comp.subst]
        rw [Comp.subst_subst (σ) (τ) (π) (agree) M, Comp.subst_subst ((σ).lift _) ((τ).lift _) ((π).lift _) (Subst.lift_subst_pointwise (agree)) N]
    | _, .force v => by
        simp only [Comp.subst]
        rw [Val.subst_subst (σ) (τ) (π) (agree) v]
    | _, .lam N => by
        simp only [Comp.subst]
        rw [Comp.subst_subst ((σ).lift _) ((τ).lift _) ((π).lift _) (Subst.lift_subst_pointwise (agree)) N]
    | _, .app M v => by
        simp only [Comp.subst]
        rw [Comp.subst_subst (σ) (τ) (π) (agree) M, Val.subst_subst (σ) (τ) (π) (agree) v]
    | _, .split v N => by
        simp only [Comp.subst]
        rw [Val.subst_subst (σ) (τ) (π) (agree) v, Comp.subst_subst (((σ).lift _).lift _) (((τ).lift _).lift _) (((π).lift _).lift _) (Subst.lift_subst_pointwise (Subst.lift_subst_pointwise (agree))) N]
    | _, .choose M K => by
        simp only [Comp.subst]
        rw [Comp.subst_subst (σ) (τ) (π) (agree) M, Comp.subst_subst (σ) (τ) (π) (agree) K]
    | _, .read N => by
        simp only [Comp.subst]
        rw [Comp.subst_subst ((σ).lift _) ((τ).lift _) ((π).lift _) (Subst.lift_subst_pointwise (agree)) N]
    | _, .write v M => by
        simp only [Comp.subst]
        rw [Val.subst_subst (σ) (τ) (π) (agree) v, Comp.subst_subst (σ) (τ) (π) (agree) M]
    | _, .intent v M => by
        simp only [Comp.subst]
        rw [Val.subst_subst (σ) (τ) (π) (agree) v, Comp.subst_subst (σ) (τ) (π) (agree) M]
    | _, .raise _ v => by
        simp only [Comp.subst]
        rw [Val.subst_subst (σ) (τ) (π) (agree) v]
    | _, .handle M _ N H => by
        simp only [Comp.subst]
        rw [Comp.subst_subst (σ) (τ) (π) (agree) M, Comp.subst_subst ((σ).lift _) ((τ).lift _) ((π).lift _) (Subst.lift_subst_pointwise (agree)) N, Comp.subst_subst ((σ).lift _) ((τ).lift _) ((π).lift _) (Subst.lift_subst_pointwise (agree)) H]
end

theorem Subst.lift_id_pointwise {source : List (VTy sig.Ground)} {ι : Subst sig source source}
    (agree : ∀ type index, ι type index = .var index) {bound : VTy sig.Ground} :
    ∀ type index, (ι.lift bound) type index = .var index
  | _, .zero => rfl
  | _, .succ index => by simp only [Subst.lift]; rw [agree]; rfl

mutual
  theorem Val.subst_id {source : List (VTy sig.Ground)} (ι : Subst sig source source) (agree : ∀ type index, ι type index = .var index) :
      {type : VTy sig.Ground} → (term : Val sig source type) →
        term.subst ι = term
    | _, .var x => by simp only [Val.subst]; rw [agree]
    | _, .const _ _ => rfl
    | _, .prim f a => by
        simp only [Val.subst]
        rw [Val.subst_id (ι) (agree) a]
    | _, .unit => rfl
    | _, .pair l r => by
        simp only [Val.subst]
        rw [Val.subst_id (ι) (agree) l, Val.subst_id (ι) (agree) r]
    | _, .thunk M => by
        simp only [Val.subst]
        rw [Comp.subst_id (ι) (agree) M]
  theorem Comp.subst_id {source : List (VTy sig.Ground)} (ι : Subst sig source source) (agree : ∀ type index, ι type index = .var index) :
      {type : CTy sig.Ground} → (term : Comp sig source type) →
        term.subst ι = term
    | _, .ret v => by
        simp only [Comp.subst]
        rw [Val.subst_id (ι) (agree) v]
    | _, .bind M N => by
        simp only [Comp.subst]
        rw [Comp.subst_id (ι) (agree) M, Comp.subst_id ((ι).lift _) (Subst.lift_id_pointwise (agree)) N]
    | _, .force v => by
        simp only [Comp.subst]
        rw [Val.subst_id (ι) (agree) v]
    | _, .lam N => by
        simp only [Comp.subst]
        rw [Comp.subst_id ((ι).lift _) (Subst.lift_id_pointwise (agree)) N]
    | _, .app M v => by
        simp only [Comp.subst]
        rw [Comp.subst_id (ι) (agree) M, Val.subst_id (ι) (agree) v]
    | _, .split v N => by
        simp only [Comp.subst]
        rw [Val.subst_id (ι) (agree) v, Comp.subst_id (((ι).lift _).lift _) (Subst.lift_id_pointwise (Subst.lift_id_pointwise (agree))) N]
    | _, .choose M K => by
        simp only [Comp.subst]
        rw [Comp.subst_id (ι) (agree) M, Comp.subst_id (ι) (agree) K]
    | _, .read N => by
        simp only [Comp.subst]
        rw [Comp.subst_id ((ι).lift _) (Subst.lift_id_pointwise (agree)) N]
    | _, .write v M => by
        simp only [Comp.subst]
        rw [Val.subst_id (ι) (agree) v, Comp.subst_id (ι) (agree) M]
    | _, .intent v M => by
        simp only [Comp.subst]
        rw [Val.subst_id (ι) (agree) v, Comp.subst_id (ι) (agree) M]
    | _, .raise _ v => by
        simp only [Comp.subst]
        rw [Val.subst_id (ι) (agree) v]
    | _, .handle M _ N H => by
        simp only [Comp.subst]
        rw [Comp.subst_id (ι) (agree) M, Comp.subst_id ((ι).lift _) (Subst.lift_id_pointwise (agree)) N, Comp.subst_id ((ι).lift _) (Subst.lift_id_pointwise (agree)) H]
end

/-! ## Substitution facts behind the rewrites -/

/-- Extend a substitution by a value for a new newest variable. -/
def Subst.cons {source target : List (VTy sig.Ground)} {bound : VTy sig.Ground}
    (value : Val sig target bound) (σ : Subst sig source target) :
    Subst sig (bound :: source) target
  | _, .zero => value
  | type, .succ index => σ type index

theorem Val.weaken_instantiate {context : List (VTy sig.Ground)} {bound type : VTy sig.Ground}
    (value : Val sig context type) (replacement : Val sig context bound) :
    (value.rename (Ren.weaken bound)).subst (Subst.single replacement) = value := by
  rw [Val.subst_rename (Ren.weaken bound) (Subst.single replacement) (fun _ found => .var found)
      (fun _ _ => rfl),
    Val.subst_id (fun _ found => .var found) (fun _ _ => rfl)]

theorem Comp.instantiate_lift {source target : List (VTy sig.Ground)} {bound : VTy sig.Ground}
    {type : CTy sig.Ground} (body : Comp sig (bound :: source) type)
    (σ : Subst sig source target) (value : Val sig target bound) :
    (body.subst (σ.lift bound)).instantiate value = body.subst (Subst.cons value σ) :=
  Comp.subst_subst (σ.lift bound) (Subst.single value) (Subst.cons value σ)
    (fun
      | _, .zero => rfl
      | type, .succ index => (Val.weaken_instantiate (σ type index) value).symm) body

theorem Comp.double_lift {source target : List (VTy sig.Ground)} {first second : VTy sig.Ground}
    {type : CTy sig.Ground} (body : Comp sig (second :: first :: source) type)
    (σ : Subst sig source target) (left : Val sig target first) (right : Val sig target second) :
    (body.subst ((σ.lift first).lift second)).subst (Subst.double left right) =
      body.subst (Subst.cons right (Subst.cons left σ)) :=
  Comp.subst_subst ((σ.lift first).lift second) (Subst.double left right)
    (Subst.cons right (Subst.cons left σ))
    (fun
      | _, .zero => rfl
      | _, .succ .zero => rfl
      | type, .succ (.succ index) => by
          change σ type index =
            ((Val.rename (Ren.weaken first) (σ type index)).rename (Ren.weaken second)).subst
              (Subst.double left right)
          rw [Val.subst_rename (Ren.weaken second) (Subst.double left right)
              (Subst.single left) (fun _ found => by cases found <;> rfl),
            Val.weaken_instantiate]) body

theorem Comp.weakenUnder_instantiate {context : List (VTy sig.Ground)}
    {bound inner : VTy sig.Ground} {type : CTy sig.Ground} (body : Comp sig (inner :: context) type)
    (replacement : Val sig context bound) :
    (Comp.weakenUnder (bound := bound) body).subst ((Subst.single replacement).lift inner) = body := by
  rw [Comp.weakenUnder, Comp.subst_rename ((Ren.weaken bound).lift inner)
      ((Subst.single replacement).lift inner) (fun _ found => .var found)
      (fun
        | _, .zero => rfl
        | _, .succ _ => rfl),
    Comp.subst_id (fun _ found => .var found) (fun _ _ => rfl)]

/-! ## Computability -/

variable [DecidableEq sig.Kind]

/-- Every answered leaf of an operational tree satisfies a predicate. -/
inductive AllLeaves {answer : VTy sig.Ground} (good : Val sig [] answer → Prop) :
    Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig) → Prop where
  | ret {value : Val sig [] answer} : good value → AllLeaves good (.pure (.inl value))
  | raise (raised : Raised sig) : AllLeaves good (.pure (.inr raised))
  | choose {left right : Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig)} :
      AllLeaves good left → AllLeaves good right → AllLeaves good (.choose left right)
  | read {next : State sig → Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig)} :
      (∀ state, AllLeaves good (next state)) → AllLeaves good (.read next)
  | write (state : State sig)
      {next : Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig)} :
      AllLeaves good next → AllLeaves good (.write state next)
  | intent (request : Request sig)
      {next : Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig)} :
      AllLeaves good next → AllLeaves good (.intent request next)

mutual
  /-- Computable closed values. -/
  def GoodV : (type : VTy sig.Ground) → Val sig [] type → Prop
    | .ground _, _ => True
    | .unit, _ => True
    | .prod first second, value =>
        ∃ (left : Val sig [] first) (right : Val sig [] second),
          value = .pair left right ∧ GoodV first left ∧ GoodV second right
    | .thunk body, value => GoodC body (.force value)

  /-- Computable closed computations: a returner unfolds operationally with
  computable answers; a function maps computable arguments to computable
  applications. -/
  def GoodC : (type : CTy sig.Ground) → Comp sig [] type → Prop
    | .ret answer, code => ∃ tree, Unfolds code tree ∧ AllLeaves (GoodV answer) tree
    | .arrow domain codomain, code =>
        ∀ argument, GoodV domain argument → GoodC codomain (.app code argument)
end

theorem GoodC.expand : (type : CTy sig.Ground) → {source target : Comp sig [] type} →
    Step source target → GoodC type target → GoodC type source
  | .ret _, _, _, step, ⟨tree, unfolds, leaves⟩ => ⟨tree, .step step unfolds, leaves⟩
  | .arrow _ codomain, _, _, step, good => fun argument goodArgument =>
      GoodC.expand codomain (.appLeft argument step) (good argument goodArgument)

theorem GoodC.raise : (type : CTy sig.Ground) → (kind : sig.Kind) →
    (payload : Val sig [] (.ground sig.payloadSort)) → GoodC type (.raise kind payload)
  | .ret _, kind, payload => ⟨_, .raise kind payload, .raise _⟩
  | .arrow _ codomain, kind, payload => fun argument _ =>
      GoodC.expand codomain (.head (.appRaise kind payload argument))
        (GoodC.raise codomain kind payload)

theorem GoodC.choose : (type : CTy sig.Ground) → {left right : Comp sig [] type} →
    GoodC type left → GoodC type right → GoodC type (.choose left right)
  | .ret _, _, _, ⟨_, leftUnfolds, leftLeaves⟩, ⟨_, rightUnfolds, rightLeaves⟩ =>
      ⟨_, .choose leftUnfolds rightUnfolds, .choose leftLeaves rightLeaves⟩
  | .arrow _ codomain, left, right, goodLeft, goodRight => fun argument goodArgument =>
      GoodC.expand codomain (.head (.appChoose left right argument))
        (GoodC.choose codomain (goodLeft argument goodArgument) (goodRight argument goodArgument))

theorem GoodC.write : (type : CTy sig.Ground) → (state : Val sig [] (.ground sig.stateSort)) →
    {next : Comp sig [] type} → GoodC type next → GoodC type (.write state next)
  | .ret _, _, _, ⟨_, unfolds, leaves⟩ => ⟨_, .write unfolds, .write _ leaves⟩
  | .arrow _ codomain, state, next, good => fun argument goodArgument =>
      GoodC.expand codomain (.head (.appWrite state next argument))
        (GoodC.write codomain state (good argument goodArgument))

theorem GoodC.intent : (type : CTy sig.Ground) → (request : Val sig [] (.ground sig.intentSort)) →
    {next : Comp sig [] type} → GoodC type next → GoodC type (.intent request next)
  | .ret _, _, _, ⟨_, unfolds, leaves⟩ => ⟨_, .intent unfolds, .intent _ leaves⟩
  | .arrow _ codomain, request, next, good => fun argument goodArgument =>
      GoodC.expand codomain (.head (.appIntent request next argument))
        (GoodC.intent codomain request (good argument goodArgument))

theorem GoodC.read : (type : CTy sig.Ground) → {body : Comp sig [.ground sig.stateSort] type} →
    (∀ state : State sig, GoodC type (body.instantiate (.const _ state))) →
      GoodC type (.read body)
  | .ret answer, body, good => by
      have good' : ∀ state : State sig, ∃ tree,
          Unfolds (body.instantiate (.const _ state)) tree ∧ AllLeaves (GoodV answer) tree := good
      choose trees unfolds leaves using good'
      exact ⟨.read trees, .read unfolds, .read leaves⟩
  | .arrow _ codomain, body, good => fun argument goodArgument =>
      GoodC.expand codomain (.head (.appRead body argument))
        (GoodC.read codomain (fun state => by
          change GoodC codomain (Comp.app (body.instantiate (.const _ state))
            ((argument.rename (Ren.weaken _)).subst (Subst.single (.const _ state))))
          rw [Val.weaken_instantiate]
          exact good state argument goodArgument))

theorem GoodC.bind {answer : VTy sig.Ground} {type : CTy sig.Ground}
    {body : Comp sig [answer] type}
    (goodBody : ∀ value, GoodV answer value → GoodC type (body.instantiate value)) :
    ∀ {first : Comp sig [] (.ret answer)}
      {tree : Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig)},
      Unfolds first tree → AllLeaves (GoodV answer) tree → GoodC type (.bind first body) := by
  intro first tree unfolds
  induction unfolds with
  | step step _ ih =>
      intro leaves
      exact GoodC.expand type (.bindLeft body step) (ih leaves)
  | ret value =>
      intro leaves
      cases leaves with
      | ret good => exact GoodC.expand type (.head (.bindRet value body)) (goodBody value good)
  | raise kind payload =>
      intro _
      exact GoodC.expand type (.head (.bindRaise kind payload body)) (GoodC.raise type kind payload)
  | choose _ _ leftIH rightIH =>
      intro leaves
      cases leaves with
      | choose leftLeaves rightLeaves =>
          exact GoodC.expand type (.head (.bindChoose _ _ body))
            (GoodC.choose type (leftIH leftLeaves) (rightIH rightLeaves))
  | @read readBody trees _ ih =>
      intro leaves
      cases leaves with
      | read stateLeaves =>
          refine GoodC.expand type (.head (.bindRead readBody body)) (GoodC.read type ?_)
          intro state
          change GoodC type (Comp.bind (readBody.instantiate (.const _ state))
            ((Comp.weakenUnder body).subst ((Subst.single (.const _ state)).lift answer)))
          rw [Comp.weakenUnder_instantiate]
          exact ih state (stateLeaves state)
  | write _ ih =>
      intro leaves
      cases leaves with
      | write _ nextLeaves =>
          exact GoodC.expand type (.head (.bindWrite _ _ body)) (GoodC.write type _ (ih nextLeaves))
  | intent _ ih =>
      intro leaves
      cases leaves with
      | intent _ nextLeaves =>
          exact GoodC.expand type (.head (.bindIntent _ _ body)) (GoodC.intent type _ (ih nextLeaves))

theorem GoodC.handle {answer : VTy sig.Ground} {type : CTy sig.Ground} {kind : sig.Kind}
    {onReturn : Comp sig [answer] type} {onRaise : Comp sig [.ground sig.payloadSort] type}
    (goodReturn : ∀ value, GoodV answer value → GoodC type (onReturn.instantiate value))
    (goodRaise : ∀ payload, GoodC type (onRaise.instantiate payload)) :
    ∀ {first : Comp sig [] (.ret answer)}
      {tree : Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig)},
      Unfolds first tree → AllLeaves (GoodV answer) tree →
        GoodC type (.handle first kind onReturn onRaise) := by
  intro first tree unfolds
  induction unfolds with
  | step step _ ih =>
      intro leaves
      exact GoodC.expand type (.handleLeft kind onReturn onRaise step) (ih leaves)
  | ret value =>
      intro leaves
      cases leaves with
      | ret good =>
          exact GoodC.expand type (.head (.handleRet value kind onReturn onRaise))
            (goodReturn value good)
  | raise raised payload =>
      intro _
      by_cases same : raised = kind
      · subst same
        exact GoodC.expand type (.head (.handleCaught raised payload onReturn onRaise))
          (goodRaise payload)
      · exact GoodC.expand type (.head (.handleOther payload onReturn onRaise same))
          (GoodC.raise type raised payload)
  | choose _ _ leftIH rightIH =>
      intro leaves
      cases leaves with
      | choose leftLeaves rightLeaves =>
          exact GoodC.expand type (.head (.handleChoose _ _ kind onReturn onRaise))
            (GoodC.choose type (leftIH leftLeaves) (rightIH rightLeaves))
  | @read readBody trees _ ih =>
      intro leaves
      cases leaves with
      | read stateLeaves =>
          refine GoodC.expand type (.head (.handleRead readBody kind onReturn onRaise))
            (GoodC.read type ?_)
          intro state
          change GoodC type (Comp.handle (readBody.instantiate (.const _ state)) kind
            ((Comp.weakenUnder onReturn).subst ((Subst.single (.const _ state)).lift answer))
            ((Comp.weakenUnder onRaise).subst
              ((Subst.single (.const _ state)).lift (.ground sig.payloadSort))))
          rw [Comp.weakenUnder_instantiate, Comp.weakenUnder_instantiate]
          exact ih state (stateLeaves state)
  | write _ ih =>
      intro leaves
      cases leaves with
      | write _ nextLeaves =>
          exact GoodC.expand type (.head (.handleWrite _ _ kind onReturn onRaise))
            (GoodC.write type _ (ih nextLeaves))
  | intent _ ih =>
      intro leaves
      cases leaves with
      | intent _ nextLeaves =>
          exact GoodC.expand type (.head (.handleIntent _ _ kind onReturn onRaise))
            (GoodC.intent type _ (ih nextLeaves))

/-- A closing substitution by computable values. -/
def GoodSubst {source : List (VTy sig.Ground)} (σ : Subst sig source []) : Prop :=
  ∀ type index, GoodV type (σ type index)

theorem GoodSubst.cons {source : List (VTy sig.Ground)} {σ : Subst sig source []}
    (good : GoodSubst σ) {bound : VTy sig.Ground} {value : Val sig [] bound}
    (goodValue : GoodV bound value) : GoodSubst (Subst.cons value σ)
  | _, .zero => goodValue
  | _, .succ index => good _ index

mutual
  /-- **Fundamental lemma for values.** -/
  theorem Val.fundamental {source : List (VTy sig.Ground)} (σ : Subst sig source [])
      (good : GoodSubst σ) : {type : VTy sig.Ground} → (value : Val sig source type) →
        GoodV type (value.subst σ)
    | _, .var index => good _ index
    | _, .const _ _ => trivial
    | _, .prim _ _ => trivial
    | _, .unit => trivial
    | _, .pair left right =>
        ⟨_, _, rfl, Val.fundamental σ good left, Val.fundamental σ good right⟩
    | _, .thunk body =>
        GoodC.expand _ (.head (.forceThunk _)) (Comp.fundamental σ good body)

  /-- **Fundamental lemma for computations.** -/
  theorem Comp.fundamental {source : List (VTy sig.Ground)} (σ : Subst sig source [])
      (good : GoodSubst σ) : {type : CTy sig.Ground} → (code : Comp sig source type) →
        GoodC type (code.subst σ)
    | _, .ret value => ⟨_, .ret _, .ret (Val.fundamental σ good value)⟩
    | _, .bind first body => by
        obtain ⟨_, unfolds, leaves⟩ := Comp.fundamental σ good first
        refine GoodC.bind (fun value goodValue => ?_) unfolds leaves
        rw [Comp.instantiate_lift]
        exact Comp.fundamental (Subst.cons value σ) (good.cons goodValue) body
    | _, .force suspended => Val.fundamental σ good suspended
    | _, .lam body => fun argument goodArgument => by
        refine GoodC.expand _ (.head (.appLam _ argument)) ?_
        rw [Comp.instantiate_lift]
        exact Comp.fundamental (Subst.cons argument σ) (good.cons goodArgument) body
    | _, .app function argument =>
        Comp.fundamental σ good function _ (Val.fundamental σ good argument)
    | _, .split pair body => by
        obtain ⟨left, right, equal, goodLeft, goodRight⟩ := Val.fundamental σ good pair
        change GoodC _ (Comp.split (pair.subst σ) (body.subst ((σ.lift _).lift _)))
        rw [equal]
        refine GoodC.expand _ (.head (.splitPair left right _)) ?_
        rw [Comp.double_lift]
        exact Comp.fundamental _ ((good.cons goodLeft).cons goodRight) body
    | _, .choose left right =>
        GoodC.choose _ (Comp.fundamental σ good left) (Comp.fundamental σ good right)
    | _, .read body => GoodC.read _ (fun state => by
        rw [Comp.instantiate_lift]
        exact Comp.fundamental _ (good.cons (value := .const _ state) trivial) body)
    | _, .write state next => GoodC.write _ _ (Comp.fundamental σ good next)
    | _, .intent request next => GoodC.intent _ _ (Comp.fundamental σ good next)
    | _, .raise kind payload => GoodC.raise _ kind _
    | _, .handle first kind onReturn onRaise => by
        obtain ⟨_, unfolds, leaves⟩ := Comp.fundamental σ good first
        refine GoodC.handle (fun value goodValue => ?_) (fun payload => ?_) unfolds leaves
        · rw [Comp.instantiate_lift]
          exact Comp.fundamental (Subst.cons value σ) (good.cons goodValue) onReturn
        · rw [Comp.instantiate_lift]
          exact Comp.fundamental (Subst.cons payload σ) (good.cons trivial) onRaise
end

/-! ## Total agreement -/

/-- **Normalization.** Every closed returner of the recursion-free calculus
has an operational unfolding. -/
theorem Comp.unfolds_exists {answer : VTy sig.Ground} (code : Comp sig [] (.ret answer)) :
    ∃ tree, Unfolds code tree := by
  have good := Comp.fundamental (fun _ index => .var index) (fun _ index => nomatch index) code
  rw [Comp.subst_id (fun _ index => .var index) (fun _ _ => rfl)] at good
  obtain ⟨tree, unfolds, _⟩ := good
  exact ⟨tree, unfolds⟩

/-- **Total agreement of observations.** Every closed returner has an
operational effect tree, and the isolated-world observation of that tree is
the observation of the program denotation. -/
theorem Comp.observe_operational {answer : VTy sig.Ground} (code : Comp sig [] (.ret answer))
    (state : State sig) :
    ∃ tree, Unfolds code tree ∧
      runWorlds (code.den Env.empty) state =
        (runWorlds tree state).map (WorldResult.mapAnswer leafDen) := by
  obtain ⟨tree, unfolds⟩ := code.unfolds_exists
  exact ⟨tree, unfolds, unfolds.observe state⟩

/-- The operational observation of a closed returner, read through one of
its operational unfoldings. -/
noncomputable def Comp.operationalObservation {answer : VTy sig.Ground}
    (code : Comp sig [] (.ret answer)) (state : State sig) :
    List (WorldResult (State sig) (VTy.den sig answer ⊕ Raised sig) (Request sig)) :=
  (runWorlds (Classical.choose code.unfolds_exists) state).map (WorldResult.mapAnswer leafDen)

/-- **Certified realization on the whole recursion-free calculus.** Compiling
any closed returner to its program and observing it with `runWorlds` is its
operational observation. -/
noncomputable def operationalRealizationTotal (sig : Signature) [DecidableEq sig.Kind] :
    Mettapedia.GSLT.Realization (fun answer : VTy sig.Ground => Comp sig [] (.ret answer))
      (fun answer => Program (State sig) (VTy.den sig answer ⊕ Raised sig) (Request sig))
      (fun answer => State sig →
        List (WorldResult (State sig) (VTy.den sig answer ⊕ Raised sig) (Request sig))) where
  compile := fun _ code => code.den Env.empty
  observeSource := fun _ code state => code.operationalObservation state
  observeArtifact := fun _ program state => runWorlds program state
  adequate := by
    intro answer code
    funext state
    exact (Classical.choose_spec code.unfolds_exists).observe state

#print axioms Comp.subst_subst
#print axioms Comp.unfolds_exists
#print axioms Comp.observe_operational
#print axioms operationalRealizationTotal

end Mettapedia.TypeTheory.ContextualCBPV
