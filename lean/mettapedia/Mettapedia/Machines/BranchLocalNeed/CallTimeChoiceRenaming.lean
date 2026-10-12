import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSpec
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Nodup

/-!
# Renaming of cells

`ValRel φ v v'` relates a value over specification cells to a value over cells
of any type `C`: equal constructors, and specification cell `ℓ` named `φ[ℓ]`.
It relates the specification to the reference machine (`C` its cell names) and
the specification to itself (`C = Nat`, a transport of cells between stores).
A renaming without repetition is injective on values (`ValRel.injective`), so
structural comparisons by primitives are preserved and reflected
(`Prim.apply_rel`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

/-! ## Values -/

/-- Values equal up to the renaming `φ` of cells: specification cell `ℓ` is
cell `φ[ℓ]` of the other side, whose cells have any type `C`. -/
inductive ValRel {C : Type} (φ : List C) : Val Nat → Val C → Prop where
  | sym (c : Nat) : ValRel φ (.sym c) (.sym c)
  | app {f x : Val Nat} {f' x' : Val C} :
      ValRel φ f f' → ValRel φ x x' → ValRel φ (.app f x) (.app f' x')
  | need {ℓ : Nat} {c : C} : φ[ℓ]? = some c → ValRel φ (.need ℓ) (.need c)
  | thunk {ℓ : Nat} {c : C} : φ[ℓ]? = some c → ValRel φ (.thunk ℓ) (.thunk c)
  | code {ℓ : Nat} {c : C} : φ[ℓ]? = some c → ValRel φ (.code ℓ) (.code c)

abbrev EnvRel {C : Type} (φ : List C) (ρ : List (Val Nat)) (ρ' : List (Val C)) : Prop :=
  List.Forall₂ (ValRel φ) ρ ρ'

theorem prefix_getElem? {C : Type} {φ φ' : List C} (hp : φ <+: φ') {ℓ : Nat} {c : C}
    (hc : φ[ℓ]? = some c) : φ'[ℓ]? = some c := by
  obtain ⟨t, rfl⟩ := hp
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hc).1]
  exact hc

theorem ValRel.mono {C : Type} {φ φ' : List C} (hp : φ <+: φ') {v : Val Nat} {v' : Val C}
    (h : ValRel φ v v') : ValRel φ' v v' := by
  induction h with
  | sym c => exact .sym c
  | app _ _ ihf ihx => exact .app ihf ihx
  | need hc => exact .need (prefix_getElem? hp hc)
  | thunk hc => exact .thunk (prefix_getElem? hp hc)
  | code hc => exact .code (prefix_getElem? hp hc)

theorem EnvRel.mono {C : Type} {φ φ' : List C} (hp : φ <+: φ') {ρ : List (Val Nat)}
    {ρ' : List (Val C)} (h : EnvRel φ ρ ρ') : EnvRel φ' ρ ρ' :=
  h.imp fun _ _ hv => hv.mono hp

/-- Successive relocations compose when their cell lookups compose. Every
constructor, including the three distinct cell roles, keeps that relation. -/
theorem ValRel.comp {C : Type} {φ : List Nat} {ψ χ : List C}
    (lookup : ∀ (i j : Nat) (c : C), φ[i]? = some j → ψ[j]? = some c → χ[i]? = some c)
    {v v' : Val Nat} {v'' : Val C} (first : ValRel φ v v') (second : ValRel ψ v' v'') :
    ValRel χ v v'' := by
  induction first generalizing v'' with
  | sym c => cases second; exact .sym c
  | app _ _ ihf ihx => cases second with | app hf hx => exact .app (ihf hf) (ihx hx)
  | need hi => cases second with | need hj => exact .need (lookup _ _ _ hi hj)
  | thunk hi => cases second with | thunk hj => exact .thunk (lookup _ _ _ hi hj)
  | code hi => cases second with | code hj => exact .code (lookup _ _ _ hi hj)

theorem EnvRel.comp {C : Type} {φ : List Nat} {ψ χ : List C}
    (lookup : ∀ (i j : Nat) (c : C), φ[i]? = some j → ψ[j]? = some c → χ[i]? = some c)
    {ρ ρ' : List (Val Nat)} {ρ'' : List (Val C)}
    (first : EnvRel φ ρ ρ') (second : EnvRel ψ ρ' ρ'') : EnvRel χ ρ ρ'' := by
  induction first generalizing ρ'' with
  | nil => cases second; exact .nil
  | cons hv _ ih =>
      cases second with
      | cons hw hrest => exact .cons (hv.comp lookup hw) (ih hrest)

theorem ValRel.isCell_eq {C : Type} {φ : List C} {v : Val Nat} {v' : Val C}
    (h : ValRel φ v v') : v'.isCell = v.isCell := by
  cases h <;> rfl

/-- A related value with no cell is the same constructor term. -/
theorem ValRel.cellFree_eq {C : Type} {φ : List C} {v : Val Nat} {v' : Val C}
    (h : ValRel φ v v') (free : v.cellFree = true) (f : Nat → C) : v' = v.mapCells f := by
  induction h with
  | sym c => rfl
  | app _ _ ihf ihx =>
      simp only [Val.cellFree, Bool.and_eq_true] at free
      simp [Val.mapCells, ihf free.1, ihx free.2]
  | need _ => simp [Val.cellFree] at free
  | thunk _ => simp [Val.cellFree] at free
  | code _ => simp [Val.cellFree] at free

theorem EnvRel.length_eq {C : Type} {φ : List C} {ρ : List (Val Nat)} {ρ' : List (Val C)}
    (h : EnvRel φ ρ ρ') : ρ'.length = ρ.length :=
  (List.Forall₂.length_eq h).symm

theorem EnvRel.getD {C : Type} {φ : List C} {ρ : List (Val Nat)} {ρ' : List (Val C)}
    (h : EnvRel φ ρ ρ') (i : Nat) : ValRel φ (ρ.getD i (.sym 0)) (ρ'.getD i (.sym 0)) := by
  induction h generalizing i with
  | nil => exact .sym 0
  | cons hv _ ih =>
      cases i with
      | zero => simpa using hv
      | succ i => simpa using ih i

theorem VExp.eval_rel {C : Type} {φ : List C} {ρ : List (Val Nat)} {ρ' : List (Val C)}
    (h : EnvRel φ ρ ρ') (e : VExp) : ValRel φ (e.eval ρ) (e.eval ρ') := by
  induction e with
  | var i => exact h.getD i
  | sym c => exact .sym c
  | app f x ihf ihx => exact .app ihf ihx

theorem EnvRel.map_eval {C : Type} {φ : List C} {ρ : List (Val Nat)} {ρ' : List (Val C)}
    (h : EnvRel φ ρ ρ') (args : List VExp) :
    EnvRel φ (args.map (·.eval ρ)) (args.map (·.eval ρ')) := by
  induction args with
  | nil => exact .nil
  | cons a as ih => exact .cons (VExp.eval_rel h a) ih

theorem ValRel.spine {C : Type} {φ : List C} {v : Val Nat} {v' : Val C}
    (h : ValRel φ v v') :
    (v.spine = none ∧ v'.spine = none) ∨
      ∃ c args args', v.spine = some (c, args) ∧ v'.spine = some (c, args') ∧
        EnvRel φ args args' := by
  induction h with
  | sym c => exact Or.inr ⟨c, [], [], rfl, rfl, .nil⟩
  | @app f x f' x' _ hx ihf _ =>
      rcases ihf with ⟨hf, hf'⟩ | ⟨c, args, args', hf, hf', hargs⟩
      · exact Or.inl ⟨by simp [Val.spine, hf], by simp [Val.spine, hf']⟩
      · refine Or.inr ⟨c, args ++ [x], args' ++ [x'], by simp [Val.spine, hf],
          by simp [Val.spine, hf'], ?_⟩
        exact List.rel_append hargs (.cons hx .nil)
  | need _ => exact Or.inl ⟨rfl, rfl⟩
  | thunk _ => exact Or.inl ⟨rfl, rfl⟩
  | code _ => exact Or.inl ⟨rfl, rfl⟩

theorem ValRel.matchCon {C : Type} {φ : List C} {v : Val Nat} {v' : Val C}
    (h : ValRel φ v v') (c k : Nat) :
    (v.matchCon c k = none ∧ v'.matchCon c k = none) ∨
      ∃ args args', v.matchCon c k = some args ∧ v'.matchCon c k = some args' ∧
        EnvRel φ args args' := by
  rcases h.spine with ⟨hs, hs'⟩ | ⟨c', args, args', hs, hs', hargs⟩
  · exact Or.inl ⟨by simp [Val.matchCon, hs], by simp [Val.matchCon, hs']⟩
  · by_cases hm : c' = c ∧ args.length = k
    · have hm' : c' = c ∧ args'.length = k :=
        ⟨hm.1, (List.Forall₂.length_eq hargs) ▸ hm.2⟩
      exact Or.inr ⟨args, args', by simp [Val.matchCon, hs, hm], by simp [Val.matchCon, hs', hm'],
        hargs⟩
    · have hm' : ¬ (c' = c ∧ args'.length = k) := by
        rw [← List.Forall₂.length_eq hargs]; exact hm
      exact Or.inl ⟨by simp [Val.matchCon, hs, hm], by simp [Val.matchCon, hs', hm']⟩

theorem ValRel.matchApp {C : Type} {φ : List C} {v : Val Nat} {v' : Val C}
    (h : ValRel φ v v') :
    (v.matchApp = none ∧ v'.matchApp = none) ∨
      ∃ f x f' x', v.matchApp = some (f, x) ∧ v'.matchApp = some (f', x') ∧
        ValRel φ f f' ∧ ValRel φ x x' := by
  cases h with
  | sym c => exact Or.inl ⟨rfl, rfl⟩
  | app hf hx => exact Or.inr ⟨_, _, _, _, rfl, rfl, hf, hx⟩
  | need _ => exact Or.inl ⟨rfl, rfl⟩
  | thunk _ => exact Or.inl ⟨rfl, rfl⟩
  | code _ => exact Or.inl ⟨rfl, rfl⟩

theorem ValRel.functional {C : Type} {φ : List C} {v : Val Nat} {v₁ v₂ : Val C}
    (h₁ : ValRel φ v v₁) (h₂ : ValRel φ v v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | sym c => cases h₂; rfl
  | app _ _ ihf ihx => cases h₂ with | app hf hx => rw [ihf hf, ihx hx]
  | need hc => cases h₂ with | need hc' => rw [hc] at hc'; cases hc'; rfl
  | thunk hc => cases h₂ with | thunk hc' => rw [hc] at hc'; cases hc'; rfl
  | code hc => cases h₂ with | code hc' => rw [hc] at hc'; cases hc'; rfl

theorem nodup_index {C : Type} {φ : List C} (hφ : φ.Nodup) {ℓ₁ ℓ₂ : Nat} {c : C}
    (h₁ : φ[ℓ₁]? = some c) (h₂ : φ[ℓ₂]? = some c) : ℓ₁ = ℓ₂ := by
  obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.mp h₁
  obtain ⟨hj, hcj⟩ := List.getElem?_eq_some_iff.mp h₂
  exact (List.Nodup.getElem_inj_iff hφ (hi := hi) (hj := hj)).mp (hci.trans hcj.symm)

theorem ValRel.injective {C : Type} {φ : List C} (hφ : φ.Nodup) {v₁ v₂ : Val Nat}
    {v' : Val C} (h₁ : ValRel φ v₁ v') (h₂ : ValRel φ v₂ v') : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | sym c => cases h₂; rfl
  | app _ _ ihf ihx => cases h₂ with | app hf hx => rw [ihf hf, ihx hx]
  | need hc => cases h₂ with | need hc' => rw [nodup_index hφ hc hc']
  | thunk hc => cases h₂ with | thunk hc' => rw [nodup_index hφ hc hc']
  | code hc => cases h₂ with | code hc' => rw [nodup_index hφ hc hc']

/-- A primitive applied to related arguments under a renaming without
repetition: both fail, or both answer with related values. -/
theorem Prim.apply_rel {C : Type} [DecidableEq C] {φ : List C} (hφ : φ.Nodup) (op : Prim)
    {vs : List (Val Nat)} {vs' : List (Val C)} (h : EnvRel φ vs vs') :
    (op.apply vs = none ∧ op.apply vs' = none) ∨
      ∃ v v', op.apply vs = some v ∧ op.apply vs' = some v' ∧ ValRel φ v v' := by
  cases op with
  | eq yes no =>
      rcases h with _ | ⟨ha, h⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · rcases h with _ | ⟨hb, h⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · rcases h with _ | ⟨_, _⟩
          · rename_i a a' b b'
            have hiff : (a = b ↔ a' = b') :=
              ⟨fun e => by subst e; exact ha.functional hb,
               fun e => by subst e; exact ha.injective hφ hb⟩
            refine Or.inr ⟨_, _, rfl, rfl, ?_⟩
            by_cases e : a = b
            · rw [if_pos e, if_pos (hiff.mp e)]; exact .sym _
            · rw [if_neg e, if_neg (fun e' => e (hiff.mpr e'))]; exact .sym _
          · exact Or.inl ⟨rfl, rfl⟩

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
