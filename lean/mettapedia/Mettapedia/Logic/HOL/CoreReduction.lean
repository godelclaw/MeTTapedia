import Mettapedia.Logic.HOL.ProofSyntaxModuloStructural
import Mettapedia.Logic.HOL.BetaNormalization

/-!
# β-reduction of core terms

The retyping step of `ProofSyntaxModulo` converts along steps between core
terms (`Term.isCore`): variables, constants, application, abstraction,
implication, equality and universal quantification.  This module shows that
β-reduction stays among the core terms and is a conversion of the checker
there.

* Instantiating a core term with a core term gives a core term
  (`Term.isCore_instantiate`, from `Term.isCore_subst` of
  `ProofSyntaxModuloStructural`).
* A β-step of a core term is a definitional step of the checker, with no
  defining equation, to a core term (`SourceStep.of_betaStep`,
  `Term.isCore_of_betaStep`); so a β-reduction of a core term is a conversion
  article (`CoreConversion.of_reducesStar`).
* Renaming keeps a term β-normal (`BetaNormalization.normal_rename`) and is
  injective along injective renamings of the variables (`rename_injective`).

**Controls.**  The checker converts `(λ x. x) y` with `y`
(`identityRedex_coreConversion`).  A conjunction is not core, so no conversion
step of the checker starts there (`not_coreStep_and`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

open Mettapedia.Logic.HOL.ContextualTrinity (BetaStep)

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Core terms under instantiation -/

theorem Term.isCore_instantiate {Γ : Ctx Base} {σ τ : Ty Base} {t : Term Const Γ σ}
    {b : Term Const (σ :: Γ) τ} (coreT : t.isCore = true) (coreB : b.isCore = true) :
    (instantiate t b).isCore = true :=
  Term.isCore_subst (CoreSubst.single coreT) coreB

/-! ## β-steps of core terms -/

/-- **A β-step of a core term reaches a core term.** -/
theorem Term.isCore_of_betaStep {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ}
    (step : BetaStep s t) (core : s.isCore = true) : t.isCore = true := by
  induction step with
  | beta body argument =>
      simp only [Term.isCore, Bool.and_eq_true] at core
      exact Term.isCore_instantiate core.2 core.1
  | appFun _ _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core ⊢
      exact ⟨ih core.1, core.2⟩
  | appArg _ _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core ⊢
      exact ⟨core.1, ih core.2⟩
  | lam _ ih => exact ih core
  | impLeft _ _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core ⊢
      exact ⟨ih core.1, core.2⟩
  | impRight _ _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core ⊢
      exact ⟨core.1, ih core.2⟩
  | eqLeft _ _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core ⊢
      exact ⟨ih core.1, core.2⟩
  | eqRight _ _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core ⊢
      exact ⟨core.1, ih core.2⟩
  | all _ ih => exact ih core
  | andLeft _ _ _ | andRight _ _ _ | orLeft _ _ _ | orRight _ _ _ | not _ _ | ex _ _ =>
      simp [Term.isCore] at core

/-- **A β-step of a core term is a step of the checker**, with no defining
equation. -/
theorem SourceStep.of_betaStep {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ}
    (step : BetaStep s t) (core : s.isCore = true) : SourceStep [] s t := by
  induction step with
  | beta body argument => exact .beta body argument
  | appFun argument _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core
      exact .appFun argument (ih core.1)
  | appArg function _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core
      exact .appArg function (ih core.2)
  | lam _ ih => exact .lam (ih core)
  | impLeft right _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core
      exact .impLeft right (ih core.1)
  | impRight left _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core
      exact .impRight left (ih core.2)
  | eqLeft right _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core
      exact .eqLeft right (ih core.1)
  | eqRight left _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core
      exact .eqRight left (ih core.2)
  | all _ ih => exact .all (ih core)
  | andLeft _ _ _ | andRight _ _ _ | orLeft _ _ _ | orRight _ _ _ | not _ _ | ex _ _ =>
      simp [Term.isCore] at core

/-- β-reduction keeps a term core. -/
theorem Term.isCore_of_reducesStar {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ}
    (reduces : BetaNormalization.ReducesStar s t) (core : s.isCore = true) : t.isCore = true := by
  induction reduces with
  | refl => exact core
  | tail _ step ih =>
      obtain ⟨one⟩ := step
      exact Term.isCore_of_betaStep one ih

/-- **A β-reduction of a core term is a conversion article.** -/
theorem CoreConversion.of_reducesStar {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ}
    (reduces : BetaNormalization.ReducesStar s t) (core : s.isCore = true) :
    CoreConversion [] s t := by
  induction reduces with
  | refl => exact .refl _
  | tail steps step ih =>
      obtain ⟨one⟩ := step
      have middleCore := Term.isCore_of_reducesStar steps core
      exact .trans _ _ _ ih (.rel _ _ ⟨middleCore, Term.isCore_of_betaStep one middleCore,
        SourceStep.of_betaStep one middleCore⟩)

/-- **Core terms with one β-normal form are convertible by the checker.** -/
theorem CoreConversion.of_normalForm {Γ : Ctx Base} {τ : Ty Base} {s t n : Term Const Γ τ}
    (toS : BetaNormalization.ReducesStar s n) (toT : BetaNormalization.ReducesStar t n)
    (coreS : s.isCore = true) (coreT : t.isCore = true) : CoreConversion [] s t :=
  .trans _ _ _ (CoreConversion.of_reducesStar toS coreS)
    (.symm _ _ (CoreConversion.of_reducesStar toT coreT))

/-- `(λ x. x) y`, over no constant, in the context `y : prop`. -/
def coreIdentityRedex : Formula (fun _ : Ty Unit => Empty) [.prop] := .app (.lam (.var .vz)) (.var .vz)

/-- **The checker converts `(λ x. x) y` with `y`**: a β-reduction of a core
term. -/
theorem identityRedex_coreConversion :
    CoreConversion [] coreIdentityRedex (.var .vz : Formula (fun _ : Ty Unit => Empty) [.prop]) :=
  CoreConversion.of_reducesStar (.single ⟨.beta (.var .vz) (.var .vz)⟩) rfl

/-- A conjunction is not core, so no conversion step of the checker starts
there. -/
theorem not_coreStep_and {Γ : Ctx Base} (p q target : Formula Const Γ) :
    ¬ CoreStep [] (.and p q) target := fun step => by
  have core := step.1
  simp [Term.isCore] at core

/-! ## Renaming -/

/-- **Renaming keeps a term β-normal.** -/
theorem BetaNormalization.normal_rename {Γ Δ : Ctx Base} {τ : Ty Base} (ρ : Rename Base Γ Δ)
    {t : Term Const Γ τ} (normal : BetaNormalization.Normal t) :
    BetaNormalization.Normal (rename ρ t) := by
  intro target step
  obtain ⟨target', reduces, -⟩ := BetaNormalization.reduces_rename_inv t ρ step
  exact normal target' reduces

theorem Rename.lift_injective {Γ Δ : Ctx Base} {σ : Ty Base} {ρ : Rename Base Γ Δ}
    (injective : ∀ {τ : Ty Base} (v w : Var Γ τ), ρ v = ρ w → v = w) :
    ∀ {τ : Ty Base} (v w : Var (σ :: Γ) τ),
      Rename.lift (σ := σ) ρ v = Rename.lift (σ := σ) ρ w → v = w
  | _, .vz, .vz, _ => rfl
  | _, .vz, .vs _, same => by simp [Rename.lift] at same
  | _, .vs _, .vz, same => by simp [Rename.lift] at same
  | _, .vs v, .vs w, same => by
      simp only [Rename.lift, Var.vs.injEq] at same
      rw [injective v w same]

/-- **Renaming along an injective renaming is injective.** -/
theorem rename_injective : ∀ {Γ Δ : Ctx Base} {τ : Ty Base} (ρ : Rename Base Γ Δ),
    (∀ {σ : Ty Base} (v w : Var Γ σ), ρ v = ρ w → v = w) →
    ∀ (s t : Term Const Γ τ), rename ρ s = rename ρ t → s = t := by
  intro Γ Δ τ ρ injective s
  induction s generalizing Δ with
  | var v =>
      intro t same
      cases t with
      | var w =>
          simp only [rename, Term.var.injEq] at same
          rw [injective v w same]
      | _ => simp [rename] at same
  | const c =>
      intro t same
      cases t with
      | const c' => simpa [rename] using same
      | _ => simp [rename] at same
  | app f a ihf iha =>
      intro t same
      cases t with
      | app f' a' =>
          simp only [rename, Term.app.injEq] at same
          obtain ⟨rfl, sameF, sameA⟩ := same
          rw [ihf ρ injective f' (eq_of_heq sameF), iha ρ injective a' (eq_of_heq sameA)]
      | _ => simp [rename] at same
  | lam b ih =>
      intro t same
      cases t with
      | lam b' =>
          simp only [rename, Term.lam.injEq] at same
          rw [ih (Rename.lift ρ) (Rename.lift_injective injective) b' same]
      | _ => simp [rename] at same
  | top => intro t same; cases t <;> simp [rename] at same ⊢
  | bot => intro t same; cases t <;> simp [rename] at same ⊢
  | and p q ihp ihq =>
      intro t same
      cases t with
      | and p' q' =>
          simp only [rename, Term.and.injEq] at same
          rw [ihp ρ injective p' same.1, ihq ρ injective q' same.2]
      | _ => simp [rename] at same
  | or p q ihp ihq =>
      intro t same
      cases t with
      | or p' q' =>
          simp only [rename, Term.or.injEq] at same
          rw [ihp ρ injective p' same.1, ihq ρ injective q' same.2]
      | _ => simp [rename] at same
  | imp p q ihp ihq =>
      intro t same
      cases t with
      | imp p' q' =>
          simp only [rename, Term.imp.injEq] at same
          rw [ihp ρ injective p' same.1, ihq ρ injective q' same.2]
      | _ => simp [rename] at same
  | not p ih =>
      intro t same
      cases t with
      | not p' =>
          simp only [rename, Term.not.injEq] at same
          rw [ih ρ injective p' same]
      | _ => simp [rename] at same
  | eq l r ihl ihr =>
      intro t same
      cases t with
      | eq l' r' =>
          simp only [rename, Term.eq.injEq] at same
          obtain ⟨rfl, sameL, sameR⟩ := same
          rw [ihl ρ injective l' (eq_of_heq sameL), ihr ρ injective r' (eq_of_heq sameR)]
      | _ => simp [rename] at same
  | all b ih =>
      intro t same
      cases t with
      | all b' =>
          simp only [rename, Term.all.injEq] at same
          obtain ⟨rfl, sameB⟩ := same
          rw [ih (Rename.lift ρ) (Rename.lift_injective injective) b' (eq_of_heq sameB)]
      | _ => simp [rename] at same
  | ex b ih =>
      intro t same
      cases t with
      | ex b' =>
          simp only [rename, Term.ex.injEq] at same
          obtain ⟨rfl, sameB⟩ := same
          rw [ih (Rename.lift ρ) (Rename.lift_injective injective) b' (eq_of_heq sameB)]
      | _ => simp [rename] at same

#print axioms Term.isCore_instantiate
#print axioms CoreConversion.of_reducesStar
#print axioms identityRedex_coreConversion
#print axioms BetaNormalization.normal_rename
#print axioms rename_injective

end Mettapedia.Logic.HOL
