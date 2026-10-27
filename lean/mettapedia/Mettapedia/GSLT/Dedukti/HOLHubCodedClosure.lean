import Mettapedia.GSLT.Dedukti.HOLHubRoundTrip

/-!
# Every normal form of a compiled proof is coded
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.HOLHub

open Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 lookupBody)
open Mettapedia.Logic.Relation (Confluent IsNormal)
open Mettapedia.Logic.HOL (Ty Ctx Var Term Formula)
open TranslationTransport

universe u v

/-! ## Reduction under substitution -/

theorem reduces_subst {theory : Theory} (closed : theory.ClosedBodies) {a b : LF.Term}
    (reduces : Reduces theory a b) (index : Nat) (replacement : LF.Term) :
    Reduces theory (subst index replacement a) (subst index replacement b) := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.subst closed index replacement)

theorem reduces_subst_replacement {theory : Theory} (closed : theory.ClosedBodies) {a b : LF.Term}
    (reduces : Reduces theory a b) (index : Nat) (body : LF.Term) :
    Reduces theory (subst index a body) (subst index b body) := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih =>
      exact ih.trans ((Par.substTerm closed (Par.refl body) step.par index).reduces closed)

/-! ## The shape of the types of proofs under steps and substitution -/

theorem ProofShape.subst {t : LF.Term} (shape : ProofShape t) :
    ∀ (index : Nat) (replacement : LF.Term), ProofShape (LFTyping.subst index replacement t) := by
  induction shape with
  | eps proposition => intro index replacement; exact .eps _
  | pi _ ih => intro index replacement; exact .pi (ih _ _)

/-- **Types of proofs keep their shape along the steps of the hub.** -/
theorem ProofShape.step {t u : LF.Term} (shape : ProofShape t) (step : Step STTfa.theory t u) :
    ProofShape u := by
  have headed := STTfa.orthogonal.leftAlgebraic.headed
  induction shape generalizing u with
  | eps proposition =>
      rcases step.app_inv with root | ⟨_, inner, rfl⟩ | ⟨_, inner, rfl⟩
      · obtain ⟨rule, assignment, member, shape, rfl⟩ := rootStep_app_con_rule root
        rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl
        · simp [STTfa.etaDef] at shape
        · simp [STTfa.etapArrow, STTfa.etap] at shape
        · simp [STTfa.etapForall, STTfa.etap] at shape
        · simp only [STTfa.epsForall, STTfa.eps, STTfa.eta, inst, Dedukti.instantiate]
          exact .pi (.eps _)
        · simp only [STTfa.epsImpl, STTfa.eps, inst, Dedukti.instantiate]
          exact .pi (.eps _)
        · simp only [STTfa.epsForallP, STTfa.eps, inst, Dedukti.instantiate]
          exact .pi (.eps _)
      · exact absurd inner (sttfa_con_normal (by decide) _)
      · exact .eps _
  | pi _ ih =>
      rcases step.pi_inv with root | ⟨_, _, rfl⟩ | ⟨_, inner, rfl⟩
      · exact absurd root (RootStep.not_pi headed)
      · exact .pi ‹ProofShape _›
      · exact .pi (ih inner)

theorem ProofShape.reduces {t u : LF.Term} (shape : ProofShape t)
    (reduces : Reduces STTfa.theory t u) : ProofShape u := by
  induction reduces with
  | refl => exact shape
  | tail _ step ih => exact ih.step step

/-- A type of the shape of proofs converts with no object type. -/
theorem ProofShape.not_conv_objTree' {t C : LF.Term} (shape : ProofShape t) (tree : ObjTree C) :
    ¬ Conv STTfa.theory t C := by
  intro converted
  obtain ⟨common, fromT, fromC⟩ := (conv_iff_joinable STTfa.confluent).mp converted
  exact (shape.reduces fromT).not_objTree (tree.reduces fromC)

/-! ## Translations of placed terms -/

section Translations

variable {Base : Type u} {Const : Ty Base → Type v} (e : Encoding Base Const)

/-- Placing a term one position further, at `k`, lifts its translation at `k`. -/
theorem translate_rename_shift : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ)
    {Θ₁ Θ₂ : Ctx Base} (ρ₁ : HOL.Rename Base Γ Θ₁) (ρ₂ : HOL.Rename Base Γ Θ₂) (k : Nat),
    (∀ {σ : Ty Base} (v : Var Γ σ), varIndex (ρ₂ v) = shiftAt k (varIndex (ρ₁ v))) →
    e.translate (HOL.rename ρ₂ t) = lift 1 k (e.translate (HOL.rename ρ₁ t)) := by
  intro Γ τ t
  induction t with
  | var v =>
      intro Θ₁ Θ₂ ρ₁ ρ₂ k index
      simp only [HOL.rename, Encoding.translate, lift_var, index]
  | const c => intro Θ₁ Θ₂ ρ₁ ρ₂ k _; rfl
  | app f a ihf iha =>
      intro Θ₁ Θ₂ ρ₁ ρ₂ k index
      simp only [HOL.rename, Encoding.translate, LFTyping.lift]
      rw [ihf ρ₁ ρ₂ k index, iha ρ₁ ρ₂ k index]
  | @lam σ Γ τ body ih =>
      intro Θ₁ Θ₂ ρ₁ ρ₂ k index
      simp only [HOL.rename, Encoding.translate, LFTyping.lift]
      rw [(e.El_code_closed σ).lift, ih (HOL.Rename.lift ρ₁) (HOL.Rename.lift ρ₂) (k + 1) (by
        intro ρ v
        cases v with
        | vz => simp [HOL.Rename.lift, varIndex, shiftAt]
        | vs w => simp [HOL.Rename.lift, varIndex, index w, shiftAt_succ])]
  | top => intro Θ₁ Θ₂ ρ₁ ρ₂ k _; rfl
  | bot => intro Θ₁ Θ₂ ρ₁ ρ₂ k _; rfl
  | and p q ihp ihq =>
      intro Θ₁ Θ₂ ρ₁ ρ₂ k index
      simp only [HOL.rename, Encoding.translate, Encoding.binary, Encoding.sym, LFTyping.lift]
      rw [ihp ρ₁ ρ₂ k index, ihq ρ₁ ρ₂ k index]
  | or p q ihp ihq =>
      intro Θ₁ Θ₂ ρ₁ ρ₂ k index
      simp only [HOL.rename, Encoding.translate, Encoding.binary, Encoding.sym, LFTyping.lift]
      rw [ihp ρ₁ ρ₂ k index, ihq ρ₁ ρ₂ k index]
  | imp p q ihp ihq =>
      intro Θ₁ Θ₂ ρ₁ ρ₂ k index
      simp only [HOL.rename, Encoding.translate, Encoding.binary, Encoding.sym, LFTyping.lift]
      rw [ihp ρ₁ ρ₂ k index, ihq ρ₁ ρ₂ k index]
  | not p ih =>
      intro Θ₁ Θ₂ ρ₁ ρ₂ k index
      simp only [HOL.rename, Encoding.translate, Encoding.sym, LFTyping.lift]
      rw [ih ρ₁ ρ₂ k index]
  | @eq Γ τ l r ihl ihr =>
      intro Θ₁ Θ₂ ρ₁ ρ₂ k index
      simp only [HOL.rename, Encoding.translate, Encoding.equation, Encoding.sym, LFTyping.lift]
      rw [(e.code_closed τ).lift, ihl ρ₁ ρ₂ k index, ihr ρ₁ ρ₂ k index]
  | @all σ Γ body ih =>
      intro Θ₁ Θ₂ ρ₁ ρ₂ k index
      simp only [HOL.rename, Encoding.translate, Encoding.binder, Encoding.sym, LFTyping.lift]
      rw [(e.code_closed σ).lift, (e.El_code_closed σ).lift,
        ih (HOL.Rename.lift ρ₁) (HOL.Rename.lift ρ₂) (k + 1) (by
          intro ρ v
          cases v with
          | vz => simp [HOL.Rename.lift, varIndex, shiftAt]
          | vs w => simp [HOL.Rename.lift, varIndex, index w, shiftAt_succ])]
  | @ex σ Γ body ih =>
      intro Θ₁ Θ₂ ρ₁ ρ₂ k index
      simp only [HOL.rename, Encoding.translate, Encoding.binder, Encoding.sym, LFTyping.lift]
      rw [(e.code_closed σ).lift, (e.El_code_closed σ).lift,
        ih (HOL.Rename.lift ρ₁) (HOL.Rename.lift ρ₂) (k + 1) (by
          intro ρ v
          cases v with
          | vz => simp [HOL.Rename.lift, varIndex, shiftAt]
          | vs w => simp [HOL.Rename.lift, varIndex, index w, shiftAt_succ])]

/-- Opening a variable one binder further in. -/
theorem subst_succ_var (j index : Nat) (N : LF.Term) :
    subst (j + 1) (lift 1 0 N) (.var (index + 1)) = lift 1 0 (subst j N (.var index)) := by
  rw [Dedukti.lift_subst (.var index) 1 0 j N (Nat.zero_le j), lift_var, shiftAt_zero]

/-- The image of a substitution placed under one more hypothesis. -/
theorem image_vs_reduces {Γ Γ' Θ Θ' : Ctx Base} {σ : Ty Base} {θ : HOL.Subst Const Γ Γ'}
    {ρ : HOL.Rename Base Γ Θ} {ρ' : HOL.Rename Base Γ' Θ'} {j : Nat} {N : LF.Term}
    (image : ∀ {τ : Ty Base} (v : Var Γ τ), Reduces STTfa.theory
      (e.translate (HOL.rename ρ' (θ v))) (subst j N (.var (varIndex (ρ v))))) :
    ∀ {τ : Ty Base} (v : Var Γ τ), Reduces STTfa.theory
      (e.translate (HOL.rename (Δ := σ :: Θ') (fun w => .vs (ρ' w)) (θ v)))
      (subst (j + 1) (lift 1 0 N) (.var (varIndex (ρ v) + 1))) := by
  intro τ v
  rw [translate_rename_vs e ρ' (θ v), subst_succ_var]
  exact (image v).liftTerm sttfa_closedBodies 1 0

/-- The image of a substitution placed under one more object. -/
theorem image_lift_reduces {Γ Γ' Θ Θ' : Ctx Base} {σ : Ty Base} {θ : HOL.Subst Const Γ Γ'}
    {ρ : HOL.Rename Base Γ Θ} {ρ' : HOL.Rename Base Γ' Θ'} {j : Nat} {N : LF.Term}
    (image : ∀ {τ : Ty Base} (v : Var Γ τ), Reduces STTfa.theory
      (e.translate (HOL.rename ρ' (θ v))) (subst j N (.var (varIndex (ρ v))))) :
    ∀ {τ : Ty Base} (v : Var (σ :: Γ) τ), Reduces STTfa.theory
      (e.translate (HOL.rename (HOL.Rename.lift ρ') (HOL.Subst.lift θ v)))
      (subst (j + 1) (lift 1 0 N) (.var (varIndex (HOL.Rename.lift ρ v)))) := by
  intro τ v
  cases v with
  | vz =>
      show Reduces STTfa.theory (.var 0) (subst (j + 1) (lift 1 0 N) (.var 0))
      rw [show subst (j + 1) (lift 1 0 N) (.var 0) = .var 0 by simp [LFTyping.subst]]
  | vs w =>
      have composed : HOL.rename (HOL.Rename.lift (σ := σ) ρ') (HOL.Subst.lift (σ := σ) θ (.vs w)) =
          HOL.rename (Δ := σ :: Θ') (fun x => .vs (ρ' x)) (θ w) := by
        show HOL.rename _ (HOL.rename HOL.Rename.weaken (θ w)) = _
        rw [HOL.rename_comp]
        rfl
      rw [composed]
      exact image_vs_reduces e image w

/-- **Translation commutes with substitution, up to reduction**: when every
variable is sent to a term whose placed translation reduces to the substituted
placed variable, the placed translation of the substituted term reduces to the
substituted placed translation. -/
theorem translate_subst_reduces : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ)
    {Γ' Θ Θ' : Ctx Base} (θ : HOL.Subst Const Γ Γ') (ρ : HOL.Rename Base Γ Θ)
    (ρ' : HOL.Rename Base Γ' Θ') (j : Nat) (N : LF.Term),
    (∀ {σ : Ty Base} (v : Var Γ σ), Reduces STTfa.theory
      (e.translate (HOL.rename ρ' (θ v))) (subst j N (.var (varIndex (ρ v))))) →
    Reduces STTfa.theory (e.translate (HOL.rename ρ' (HOL.subst θ t)))
      (subst j N (e.translate (HOL.rename ρ t))) := by
  intro Γ τ t
  induction t with
  | var v => intro Γ' Θ Θ' θ ρ ρ' j N image; exact image v
  | const c => intro Γ' Θ Θ' θ ρ ρ' j N _; exact .refl
  | app f a ihf iha =>
      intro Γ' Θ Θ' θ ρ ρ' j N image
      exact Reduces.app (ihf θ ρ ρ' j N image) (iha θ ρ ρ' j N image)
  | @lam σ Γ τ body ih =>
      intro Γ' Θ Θ' θ ρ ρ' j N image
      simp only [HOL.subst, HOL.rename, Encoding.translate, LFTyping.subst]
      rw [(e.El_code_closed σ).subst]
      exact Reduces.lam .refl (ih (HOL.Subst.lift θ) (HOL.Rename.lift ρ) (HOL.Rename.lift ρ') (j + 1)
        (lift 1 0 N) (image_lift_reduces e image))
  | top => intro Γ' Θ Θ' θ ρ ρ' j N _; exact .refl
  | bot => intro Γ' Θ Θ' θ ρ ρ' j N _; exact .refl
  | and p q ihp ihq =>
      intro Γ' Θ Θ' θ ρ ρ' j N image
      simp only [HOL.subst, HOL.rename, Encoding.translate, Encoding.binary, Encoding.sym,
        LFTyping.subst]
      exact Reduces.app (Reduces.app .refl (ihp θ ρ ρ' j N image)) (ihq θ ρ ρ' j N image)
  | or p q ihp ihq =>
      intro Γ' Θ Θ' θ ρ ρ' j N image
      simp only [HOL.subst, HOL.rename, Encoding.translate, Encoding.binary, Encoding.sym,
        LFTyping.subst]
      exact Reduces.app (Reduces.app .refl (ihp θ ρ ρ' j N image)) (ihq θ ρ ρ' j N image)
  | imp p q ihp ihq =>
      intro Γ' Θ Θ' θ ρ ρ' j N image
      simp only [HOL.subst, HOL.rename, Encoding.translate, Encoding.binary, Encoding.sym,
        LFTyping.subst]
      exact Reduces.app (Reduces.app .refl (ihp θ ρ ρ' j N image)) (ihq θ ρ ρ' j N image)
  | not p ih =>
      intro Γ' Θ Θ' θ ρ ρ' j N image
      simp only [HOL.subst, HOL.rename, Encoding.translate, Encoding.sym, LFTyping.subst]
      exact Reduces.app .refl (ih θ ρ ρ' j N image)
  | @eq Γ τ l r ihl ihr =>
      intro Γ' Θ Θ' θ ρ ρ' j N image
      simp only [HOL.subst, HOL.rename, Encoding.translate, Encoding.equation, Encoding.sym,
        LFTyping.subst]
      rw [(e.code_closed τ).subst]
      exact Reduces.app (Reduces.app .refl (ihl θ ρ ρ' j N image)) (ihr θ ρ ρ' j N image)
  | @all σ Γ body ih =>
      intro Γ' Θ Θ' θ ρ ρ' j N image
      simp only [HOL.subst, HOL.rename, Encoding.translate, Encoding.binder, Encoding.sym,
        LFTyping.subst]
      rw [(e.code_closed σ).subst, (e.El_code_closed σ).subst]
      exact Reduces.app .refl (Reduces.lam .refl (ih (HOL.Subst.lift θ) (HOL.Rename.lift ρ)
        (HOL.Rename.lift ρ') (j + 1) (lift 1 0 N) (image_lift_reduces e image)))
  | @ex σ Γ body ih =>
      intro Γ' Θ Θ' θ ρ ρ' j N image
      simp only [HOL.subst, HOL.rename, Encoding.translate, Encoding.binder, Encoding.sym,
        LFTyping.subst]
      rw [(e.code_closed σ).subst, (e.El_code_closed σ).subst]
      exact Reduces.app .refl (Reduces.lam .refl (ih (HOL.Subst.lift θ) (HOL.Rename.lift ρ)
        (HOL.Rename.lift ρ') (j + 1) (lift 1 0 N) (image_lift_reduces e image)))

end Translations

/-! ## The coding of the reducts of compiled proofs -/

section PreCoding

variable {Base : Type u} {Const : Ty Base → Type v}

/-- **The coding of the reducts of compiled proofs.**  As `Coded`, except that an
object abstraction sits at any reduct of the decoding of the code of its type,
and an object application applies to any reduct of the placed translation of a
core HOL term.  A hypothesis is a variable at a position that holds no object;
the renaming `ρ` places the objects of the HOL context `Γ` among the variables
of the framework, which `Θ` lists, with `prop` for a hypothesis. -/
inductive PreCoded (e : Encoding Base Const) :
    {Γ Θ : Ctx Base} → HOL.Rename Base Γ Θ → LF.Term → Prop
  | hyp {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {index : Nat} :
      (∀ {σ : Ty Base} (v : Var Γ σ), varIndex (ρ v) ≠ index) → PreCoded e @ρ (.var index)
  | lamHyp {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {domain body : LF.Term} :
      ProofShape domain →
      PreCoded e (Θ := .prop :: Θ) (fun v => .vs (ρ v)) body → PreCoded e @ρ (.lam domain body)
  | lamObj {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} (σ : Ty Base) {domain body : LF.Term} :
      Reduces STTfa.theory (e.El (e.code σ)) domain →
      PreCoded e (HOL.Rename.lift (σ := σ) ρ) body → PreCoded e @ρ (.lam domain body)
  | appProof {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {function argument : LF.Term} :
      PreCoded e @ρ function → PreCoded e @ρ argument → PreCoded e @ρ (.app function argument)
  | appObj {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {function argument : LF.Term} {σ : Ty Base}
      (witness : Term Const Γ σ) : witness.isCore = true → PreCoded e @ρ function →
      Reduces STTfa.theory (e.translate (HOL.rename ρ witness)) argument →
      PreCoded e @ρ (.app function argument)

variable {e : Encoding Base Const}

/-- A coded reduct has no head constant. -/
theorem PreCoded.headConst_none {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {M : LF.Term}
    (coded : PreCoded e @ρ M) : headConst M = none := by
  induction coded with
  | hyp _ => rfl
  | lamHyp _ _ _ => rfl
  | lamObj _ _ _ _ => rfl
  | appProof _ _ ihFunction _ => exact ihFunction
  | appObj _ _ _ _ ihFunction => exact ihFunction

/-- **Weakening**: lifting a coded reduct at `k` codes it again, for any
placement that skips `k` on the images of the old objects and sends the new
objects to `k`. -/
theorem PreCoded.weaken : ∀ {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {M : LF.Term},
    PreCoded e @ρ M →
    ∀ {Γ' Θ' : Ctx Base} (r : HOL.Rename Base Γ Γ') (ρ' : HOL.Rename Base Γ' Θ') (k : Nat),
      (∀ {τ : Ty Base} (v : Var Γ τ), varIndex (ρ' (r v)) = shiftAt k (varIndex (ρ v))) →
      (∀ {τ : Ty Base} (w : Var Γ' τ), (∀ v : Var Γ τ, r v ≠ w) → varIndex (ρ' w) = k) →
      PreCoded e ρ' (lift 1 k M) := by
  intro Γ Θ ρ M coded
  induction coded with
  | @hyp Γ Θ ρ index notObject =>
      intro Γ' Θ' r ρ' k image fresh
      rw [lift_var]
      refine .hyp fun {τ} w same => ?_
      by_cases inImage : ∃ v : Var Γ τ, r v = w
      · obtain ⟨v, rfl⟩ := inImage
        rw [image v] at same
        exact notObject v (shiftAt_injective k same)
      · push_neg at inImage
        rw [fresh w inImage] at same
        exact shiftAt_ne k index same.symm
  | @lamHyp Γ Θ ρ domain body shape _ ih =>
      intro Γ' Θ' r ρ' k image fresh
      simp only [LFTyping.lift]
      refine .lamHyp (shape.lift 1 k) (ih r (Θ' := .prop :: Θ') (fun v => .vs (ρ' v)) (k + 1) ?_ ?_)
      · intro τ v
        simp only [varIndex, image v, shiftAt_succ]
      · intro τ w notImage
        simp only [varIndex, fresh w notImage]
  | @lamObj Γ Θ ρ σ domain body reduces _ ih =>
      intro Γ' Θ' r ρ' k image fresh
      simp only [LFTyping.lift]
      refine .lamObj σ ?_ (ih (HOL.Rename.lift r) (HOL.Rename.lift ρ') (k + 1) ?_ ?_)
      · have lifted := reduces.liftTerm sttfa_closedBodies 1 k
        rwa [(e.El_code_closed σ).lift] at lifted
      · intro τ v
        cases v with
        | vz => simp [HOL.Rename.lift, varIndex, shiftAt]
        | vs v => simp only [HOL.Rename.lift, varIndex, image v, shiftAt_succ]
      · intro τ w notImage
        cases w with
        | vz => exact absurd rfl (notImage .vz)
        | vs w =>
            simp only [HOL.Rename.lift, varIndex]
            rw [fresh w fun v same => notImage (.vs v) (by simp [HOL.Rename.lift, same])]
  | appProof _ _ ihFunction ihArgument =>
      intro Γ' Θ' r ρ' k image fresh
      exact .appProof (ihFunction r ρ' k image fresh) (ihArgument r ρ' k image fresh)
  | @appObj Γ Θ ρ function argument σ witness core _ reduces ihFunction =>
      intro Γ' Θ' r ρ' k image fresh
      refine .appObj (HOL.rename r witness) (by rw [HOL.Term.isCore_rename]; exact core)
        (ihFunction r ρ' k image fresh) ?_
      rw [HOL.rename_comp, translate_rename_shift e witness ρ (fun v => ρ' (r v)) k image]
      exact reduces.liftTerm sttfa_closedBodies 1 k

/-- **Substitution of a coded proof for a hypothesis.** -/
theorem PreCoded.substHyp : ∀ {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {B : LF.Term},
    PreCoded e @ρ B →
    ∀ {Θ' : Ctx Base} (ρ' : HOL.Rename Base Γ Θ') (j : Nat) (P : LF.Term), PreCoded e ρ' P →
      (∀ {τ : Ty Base} (v : Var Γ τ), subst j P (.var (varIndex (ρ v))) = .var (varIndex (ρ' v))) →
      (∀ index : Nat, (∀ {τ : Ty Base} (v : Var Γ τ), varIndex (ρ v) ≠ index) → index ≠ j →
        ∀ {τ : Ty Base} (v : Var Γ τ), varIndex (ρ' v) ≠ (if j < index then index - 1 else index)) →
      PreCoded e ρ' (subst j P B) := by
  intro Γ Θ ρ B coded
  induction coded with
  | @hyp Γ Θ ρ index notObject =>
      intro Θ' ρ' j P codedP objects hyps
      by_cases same : index = j
      · subst same
        simpa [LFTyping.subst] using codedP
      · have result : subst j P (.var index) = .var (if j < index then index - 1 else index) := by
          simp only [LFTyping.subst, same, if_false]
          split_ifs <;> rfl
        rw [result]
        exact .hyp fun v => hyps index notObject same v
  | @lamHyp Γ Θ ρ domain body shape _ ih =>
      intro Θ' ρ' j P codedP objects hyps
      simp only [LFTyping.subst]
      refine .lamHyp (shape.subst j P)
        (ih (Θ' := .prop :: Θ') (fun v => .vs (ρ' v)) (j + 1) (lift 1 0 P) ?_ ?_ ?_)
      · exact codedP.weaken HOL.Rename.id (fun v => .vs (ρ' v)) 0
          (fun v => by simp [HOL.Rename.id, varIndex, shiftAt_zero])
          (fun w notImage => absurd rfl (notImage w))
      · intro τ v
        show subst (j + 1) (lift 1 0 P) (.var (varIndex (ρ v) + 1)) = .var (varIndex (ρ' v) + 1)
        rw [subst_succ_var, objects v, lift_var, shiftAt_zero]
      · intro index notObject differs τ v
        cases index with
        | zero => simp [varIndex]
        | succ index =>
            have notPrior : ∀ {τ : Ty Base} (v : Var Γ τ), varIndex (ρ v) ≠ index :=
              fun v same => notObject v (by simp [varIndex, same])
            have prior := hyps index notPrior (fun same => differs (by rw [same])) v
            simp only [varIndex]
            split_ifs at prior ⊢ <;> omega
  | @lamObj Γ Θ ρ σ domain body reduces _ ih =>
      intro Θ' ρ' j P codedP objects hyps
      simp only [LFTyping.subst]
      refine .lamObj σ ?_ (ih (HOL.Rename.lift ρ') (j + 1) (lift 1 0 P) ?_ ?_ ?_)
      · have substituted := reduces_subst sttfa_closedBodies reduces j P
        rwa [(e.El_code_closed σ).subst] at substituted
      · exact codedP.weaken HOL.Rename.weaken (HOL.Rename.lift ρ') 0
          (fun v => by simp [HOL.Rename.weaken, HOL.Rename.lift, varIndex, shiftAt_zero])
          (fun w notImage => by
            cases w with
            | vz => rfl
            | vs w => exact absurd rfl (notImage w))
      · intro τ v
        cases v with
        | vz =>
            show subst (j + 1) (lift 1 0 P) (.var 0) = .var 0
            simp [LFTyping.subst]
        | vs w =>
            show subst (j + 1) (lift 1 0 P) (.var (varIndex (ρ w) + 1)) = .var (varIndex (ρ' w) + 1)
            rw [subst_succ_var, objects w, lift_var, shiftAt_zero]
      · intro index notObject differs τ v
        cases index with
        | zero => exact absurd rfl (notObject .vz)
        | succ index =>
            have notPrior : ∀ {τ : Ty Base} (v : Var Γ τ), varIndex (ρ v) ≠ index :=
              fun v same => notObject (.vs v) (by simp [HOL.Rename.lift, varIndex, same])
            cases v with
            | vz =>
                simp only [HOL.Rename.lift, varIndex]
                split_ifs <;> omega
            | vs w =>
                have prior := hyps index notPrior (fun same => differs (by rw [same])) w
                simp only [HOL.Rename.lift, varIndex]
                split_ifs at prior ⊢ <;> omega
  | appProof _ _ ihFunction ihArgument =>
      intro Θ' ρ' j P codedP objects hyps
      exact .appProof (ihFunction ρ' j P codedP objects hyps) (ihArgument ρ' j P codedP objects hyps)
  | @appObj Γ Θ ρ function argument σ witness core _ reduces ihFunction =>
      intro Θ' ρ' j P codedP objects hyps
      refine .appObj witness core (ihFunction ρ' j P codedP objects hyps) ?_
      have moved := translate_subst_reduces e witness HOL.Subst.id ρ ρ' j P (fun v => by
        rw [objects v]
        exact .refl)
      rw [HOL.subst_id] at moved
      exact moved.trans (reduces_subst sttfa_closedBodies reduces j P)

/-- **Substitution of the translation of a core term for an object.** -/
theorem PreCoded.substObj : ∀ {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {B : LF.Term},
    PreCoded e @ρ B →
    ∀ {Γ' Θ' : Ctx Base} (ρ' : HOL.Rename Base Γ' Θ') (θ : HOL.Subst Const Γ Γ') (j : Nat)
      (N : LF.Term), HOL.CoreSubst θ →
      (∀ {τ : Ty Base} (v : Var Γ τ), Reduces STTfa.theory
        (e.translate (HOL.rename ρ' (θ v))) (subst j N (.var (varIndex (ρ v))))) →
      (∀ index : Nat, (∀ {τ : Ty Base} (v : Var Γ τ), varIndex (ρ v) ≠ index) →
        index ≠ j ∧
          ∀ {τ : Ty Base} (v : Var Γ' τ), varIndex (ρ' v) ≠ (if j < index then index - 1 else index)) →
      PreCoded e ρ' (subst j N B) := by
  intro Γ Θ ρ B coded
  induction coded with
  | @hyp Γ Θ ρ index notObject =>
      intro Γ' Θ' ρ' θ j N _ _ hyps
      obtain ⟨differs, avoid⟩ := hyps index notObject
      have result : subst j N (.var index) = .var (if j < index then index - 1 else index) := by
        simp only [LFTyping.subst, differs, if_false]
        split_ifs <;> rfl
      rw [result]
      exact .hyp fun v => avoid v
  | @lamHyp Γ Θ ρ domain body shape _ ih =>
      intro Γ' Θ' ρ' θ j N coreθ image hyps
      simp only [LFTyping.subst]
      refine .lamHyp (shape.subst j N)
        (ih (Θ' := .prop :: Θ') (fun v => .vs (ρ' v)) θ (j + 1) (lift 1 0 N) coreθ
          (image_vs_reduces e image) ?_)
      intro index notObject
      cases index with
      | zero => exact ⟨by omega, fun v => by simp [varIndex]⟩
      | succ index =>
          have notPrior : ∀ {τ : Ty Base} (v : Var Γ τ), varIndex (ρ v) ≠ index :=
            fun v same => notObject v (by simp [varIndex, same])
          obtain ⟨differs, avoid⟩ := hyps index notPrior
          refine ⟨by omega, fun {τ} v => ?_⟩
          have prior := avoid v
          simp only [varIndex]
          split_ifs at prior ⊢ <;> omega
  | @lamObj Γ Θ ρ σ domain body reduces _ ih =>
      intro Γ' Θ' ρ' θ j N coreθ image hyps
      simp only [LFTyping.subst]
      refine .lamObj σ ?_ (ih (HOL.Rename.lift ρ') (HOL.Subst.lift θ) (j + 1) (lift 1 0 N)
        coreθ.lift (image_lift_reduces e image) ?_)
      · have substituted := reduces_subst sttfa_closedBodies reduces j N
        rwa [(e.El_code_closed σ).subst] at substituted
      · intro index notObject
        cases index with
        | zero => exact absurd rfl (notObject .vz)
        | succ index =>
            have notPrior : ∀ {τ : Ty Base} (v : Var Γ τ), varIndex (ρ v) ≠ index :=
              fun v same => notObject (.vs v) (by simp [HOL.Rename.lift, varIndex, same])
            obtain ⟨differs, avoid⟩ := hyps index notPrior
            refine ⟨by omega, fun {τ} v => ?_⟩
            cases v with
            | vz =>
                simp only [HOL.Rename.lift, varIndex]
                split_ifs <;> omega
            | vs w =>
                have prior := avoid w
                simp only [HOL.Rename.lift, varIndex]
                split_ifs at prior ⊢ <;> omega
  | appProof _ _ ihFunction ihArgument =>
      intro Γ' Θ' ρ' θ j N coreθ image hyps
      exact .appProof (ihFunction ρ' θ j N coreθ image hyps) (ihArgument ρ' θ j N coreθ image hyps)
  | @appObj Γ Θ ρ function argument σ witness core _ reduces ihFunction =>
      intro Γ' Θ' ρ' θ j N coreθ image hyps
      refine .appObj (HOL.subst θ witness) (HOL.Term.isCore_subst coreθ core)
        (ihFunction ρ' θ j N coreθ image hyps) ?_
      exact (translate_subst_reduces e witness θ ρ ρ' j N image).trans
        (reduces_subst sttfa_closedBodies reduces j N)

end PreCoding

/-! ## Types of the shape of proofs -/

/-- A type that reduces to the shape of the types of proofs. -/
def ProofLike (X : LF.Term) : Prop := ∃ P, ProofShape P ∧ Reduces STTfa.theory X P

theorem ProofLike.of_shape {X : LF.Term} (shape : ProofShape X) : ProofLike X := ⟨X, shape, .refl⟩

theorem ProofLike.of_conv {X Y : LF.Term} (converted : Conv STTfa.theory X Y) (like : ProofLike Y) :
    ProofLike X := by
  obtain ⟨P, shape, toP⟩ := like
  obtain ⟨R, toR, fromY⟩ := (conv_iff_joinable STTfa.confluent).mp converted
  obtain ⟨S, fromR, fromP⟩ := STTfa.confluent Y R P fromY toP
  exact ⟨S, shape.reduces fromP, toR.trans fromR⟩

theorem ProofLike.lift {X : LF.Term} (like : ProofLike X) : ProofLike (LFTyping.lift 1 0 X) := by
  obtain ⟨P, shape, toP⟩ := like
  exact ⟨LFTyping.lift 1 0 P, shape.lift 1 0, toP.liftTerm sttfa_closedBodies 1 0⟩

theorem ProofLike.subst {X : LF.Term} (like : ProofLike X) (index : Nat) (replacement : LF.Term) :
    ProofLike (subst index replacement X) := by
  obtain ⟨P, shape, toP⟩ := like
  exact ⟨_, shape.subst index replacement, reduces_subst sttfa_closedBodies toP index replacement⟩

theorem ProofLike.pi_body {A B : LF.Term} (like : ProofLike (.pi A B)) : ProofLike B := by
  obtain ⟨P, shape, toP⟩ := like
  obtain ⟨A', B', rfl, _, toB'⟩ := toP.pi_inv STTfa.orthogonal.leftAlgebraic.headed
  cases shape with
  | pi bodyShape => exact ⟨B', bodyShape, toB'⟩

/-- A type of the shape of proofs converts with no object type. -/
theorem ProofLike.not_conv_objTree {X C : LF.Term} (like : ProofLike X) (tree : ObjTree C) :
    ¬ Conv STTfa.theory X C := by
  obtain ⟨P, shape, toP⟩ := like
  exact fun converted => shape.not_conv_objTree' tree (.trans _ _ _ (.symm _ _ toP.conv) converted)

/-- Convertible products have convertible domains. -/
theorem conv_pi_domain {A B A' B' : LF.Term} (converted : Conv STTfa.theory (.pi A B) (.pi A' B')) :
    Conv STTfa.theory A A' := by
  have headed := STTfa.orthogonal.leftAlgebraic.headed
  obtain ⟨R, left, right⟩ := (conv_iff_joinable STTfa.confluent).mp converted
  obtain ⟨D, E, rfl, toD, _⟩ := left.pi_inv headed
  obtain ⟨D', E', same, toD', _⟩ := right.pi_inv headed
  cases same
  exact .trans _ _ _ toD.conv (.symm _ _ toD'.conv)

/-- A root step of a term with no head constant is a β-step. -/
theorem rootStep_headless {theory : Theory} (headed : theory.Headed) {source target : LF.Term}
    (root : RootStep theory source target) (headless : headConst source = none) :
    ∃ domain body argument, source = .app (.lam domain body) argument ∧
      target = subst0 argument body := by
  rcases rootStep_cases root with beta | ⟨name, rfl, _⟩ | ⟨rule, assignment, member, rfl, _⟩
  · exact beta
  · simp [headConst] at headless
  · obtain ⟨name, head⟩ := headed _ member
    have instantiated := headConst_instantiate assignment 0 head
    exact absurd (instantiated.symm.trans headless) (by simp)

/-! ## Contexts of hypotheses with objects, by shape -/

section Shaped

variable {Base : Type u} {Const : Ty Base → Type v}

/-- **A context of hypotheses with objects, by shape.**  Each object sits at its
place, at a type converting with the decoding of its type; every other variable
is a hypothesis, at a type that reduces to the shape of the types of proofs. -/
structure ShapedCtx (e : Encoding Base Const) {Γ Θ : Ctx Base} (ρ : HOL.Rename Base Γ Θ)
    (context : LFTyping.Ctx) : Prop where
  objects : ∀ {σ : Ty Base} (v : Var Γ σ), ∃ X, LFTyping.ctxLookup context (varIndex (ρ v)) = some X ∧
    Conv STTfa.theory X (e.El (e.code σ))
  hyps : ∀ (index : Nat) (X : LF.Term), (∀ {σ : Ty Base} (v : Var Γ σ), varIndex (ρ v) ≠ index) →
    LFTyping.ctxLookup context index = some X → ProofLike X

variable {e : Encoding Base Const}

theorem ShapedCtx.extendHyp {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {context : LFTyping.Ctx}
    (shaped : ShapedCtx e ρ context) {domain : LF.Term} (like : ProofLike domain) :
    ShapedCtx e (Θ := .prop :: Θ) (fun v => .vs (ρ v)) (domain :: context) where
  objects {σ} v := by
    obtain ⟨X, found, convX⟩ := shaped.objects v
    refine ⟨lift 1 0 X, ?_, ?_⟩
    · show LFTyping.ctxLookup (domain :: context) (varIndex (ρ v) + 1) = _
      rw [lookup_cons_succ, found]
      rfl
    · have lifted := convX.lift sttfa_closedBodies 1 0
      rwa [(e.El_code_closed σ).lift] at lifted
  hyps index X notObject found := by
    cases index with
    | zero =>
        rw [lookup_cons_zero] at found
        cases found
        exact like.lift
    | succ index =>
        rw [lookup_cons_succ] at found
        obtain ⟨prior, priorFound, rfl⟩ := Option.map_eq_some_iff.mp found
        exact (shaped.hyps index prior (fun v same => notObject v (by simp [varIndex, same]))
          priorFound).lift

theorem ShapedCtx.extendObj {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {context : LFTyping.Ctx}
    (shaped : ShapedCtx e ρ context) {domain : LF.Term} {σ : Ty Base}
    (converted : Conv STTfa.theory domain (e.El (e.code σ))) :
    ShapedCtx e (HOL.Rename.lift (σ := σ) ρ) (domain :: context) where
  objects {τ} v := by
    cases v with
    | vz =>
        refine ⟨lift 1 0 domain, lookup_cons_zero _ _, ?_⟩
        have lifted := converted.lift sttfa_closedBodies 1 0
        rwa [(e.El_code_closed σ).lift] at lifted
    | vs w =>
        obtain ⟨X, found, convX⟩ := shaped.objects w
        refine ⟨lift 1 0 X, ?_, ?_⟩
        · show LFTyping.ctxLookup (domain :: context) (varIndex (ρ w) + 1) = _
          rw [lookup_cons_succ, found]
          rfl
        · have lifted := convX.lift sttfa_closedBodies 1 0
          rwa [(e.El_code_closed τ).lift] at lifted
  hyps index X notObject found := by
    cases index with
    | zero => exact absurd rfl (notObject .vz)
    | succ index =>
        rw [lookup_cons_succ] at found
        obtain ⟨prior, priorFound, rfl⟩ := Option.map_eq_some_iff.mp found
        exact (shaped.hyps index prior
          (fun v same => notObject (.vs v) (by simp [HOL.Rename.lift, varIndex, same]))
          priorFound).lift

/-- The empty context is a context of hypotheses with objects. -/
theorem shapedCtx_nil : ShapedCtx e (HOL.Rename.id (Γ := [])) [] where
  objects v := nomatch v
  hyps index X _ found := by
    rw [ctxLookup_eq_getElem?] at found
    simp at found

/-- The decodings of the types of a HOL context form a context of objects. -/
theorem shapedCtx_objects (Γ : Ctx Base) : ShapedCtx e (HOL.Rename.id (Γ := Γ)) (e.ctx Γ) where
  objects v := ⟨_, e.ctxLookup_var v, .refl _⟩
  hyps index X notObject found := by
    rw [ctxLookup_eq_getElem?] at found
    have bound : index < Γ.length := by
      cases lookup : (e.ctx Γ)[index]? with
      | none => rw [lookup] at found; cases found
      | some _ =>
          have := (List.getElem?_eq_some_iff.mp lookup).1
          simpa [Encoding.ctx] using this
    obtain ⟨σ, v, same⟩ := exists_var_of_lt bound
    exact absurd same (notObject v)

/-- **The types of coded reducts have the shape of the types of proofs.** -/
theorem PreCoded.proofLike : ∀ {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {M : LF.Term},
    PreCoded e @ρ M → ∀ {context : LFTyping.Ctx} {A : LF.Term}, ShapedCtx e ρ context →
      LambdaPiModulo (sttfaProofTheory e) context M A → ProofLike A := by
  intro Γ Θ ρ M coded
  induction coded with
  | @hyp Γ Θ ρ index notObject =>
      intro context A shaped typed
      obtain ⟨declared, found, converted⟩ := typed.var_inv
      exact ProofLike.of_conv (.symm _ _ (conv_proofTheory converted))
        (shaped.hyps index declared notObject found)
  | @lamHyp Γ Θ ρ domain body shape _ ih =>
      intro context A shaped typed
      obtain ⟨bodyType, _, _, _, _, _, _, bodyTyped, converted⟩ := typed.lam_inv
      obtain ⟨P, bodyShape, toP⟩ := ih (shaped.extendHyp (ProofLike.of_shape shape)) bodyTyped
      exact ProofLike.of_conv (.symm _ _ (conv_proofTheory converted))
        ⟨.pi domain P, .pi bodyShape, Reduces.pi .refl toP⟩
  | @lamObj Γ Θ ρ σ domain body reduces _ ih =>
      intro context A shaped typed
      obtain ⟨bodyType, _, _, _, _, _, _, bodyTyped, converted⟩ := typed.lam_inv
      obtain ⟨P, bodyShape, toP⟩ := ih (shaped.extendObj (.symm _ _ reduces.conv)) bodyTyped
      exact ProofLike.of_conv (.symm _ _ (conv_proofTheory converted))
        ⟨.pi domain P, .pi bodyShape, Reduces.pi .refl toP⟩
  | @appProof Γ Θ ρ function argument _ _ ihFunction _ =>
      intro context A shaped typed
      obtain ⟨domain, bodyType, functionTyped, _, converted⟩ := typed.app_inv
      exact ProofLike.of_conv (.symm _ _ (conv_proofTheory converted))
        ((ihFunction shaped functionTyped).pi_body.subst 0 argument)
  | @appObj Γ Θ ρ function argument σ witness _ _ _ ihFunction =>
      intro context A shaped typed
      obtain ⟨domain, bodyType, functionTyped, _, converted⟩ := typed.app_inv
      exact ProofLike.of_conv (.symm _ _ (conv_proofTheory converted))
        ((ihFunction shaped functionTyped).pi_body.subst 0 argument)

end Shaped

/-! ## The coding is closed under reduction -/

section Closure

variable {Base : Type u} {Const : Ty Base → Type v}
variable {e : Encoding Base Const} (names : SttfaNames e)
include names

/-- **A placed translation has the decoding of the code of its type**, in a
context of hypotheses with objects. -/
theorem translate_typed_shaped : ∀ {Γ : Ctx Base} {σ : Ty Base} (t : Term Const Γ σ)
    {Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {context : LFTyping.Ctx},
    ShapedCtx e ρ context →
      LambdaPiModulo (sttfaProofTheory e) context (e.translate (HOL.rename ρ t)) (e.El (e.code σ)) := by
  have declares := proofTheory_declares names
  intro Γ σ t
  induction t with
  | var v =>
      intro Θ ρ context shaped
      obtain ⟨X, found, convX⟩ := shaped.objects v
      exact .conv (.var found) (conv_toProofTheory convX) (declares.El_code_typed _)
  | const c => intro Θ ρ context _; exact declares.sym_typed (.const c)
  | app f a ihf iha =>
      intro Θ ρ context shaped
      exact declares.apply_typed (ihf shaped) (iha shaped)
  | @lam σ Γ τ body ih =>
      intro Θ ρ context shaped
      exact declares.lam_typed (ih (shaped.extendObj (.refl _)))
  | top => intro Θ ρ context _; exact declares.sym_typed .top
  | bot => intro Θ ρ context _; exact declares.sym_typed .bot
  | and p q ihp ihq =>
      intro Θ ρ context shaped
      exact declares.apply_typed (σ := .prop)
        (declares.apply_typed (σ := .prop) (declares.sym_typed .and) (ihp shaped)) (ihq shaped)
  | or p q ihp ihq =>
      intro Θ ρ context shaped
      exact declares.apply_typed (σ := .prop)
        (declares.apply_typed (σ := .prop) (declares.sym_typed .or) (ihp shaped)) (ihq shaped)
  | imp p q ihp ihq =>
      intro Θ ρ context shaped
      exact declares.apply_typed (σ := .prop)
        (declares.apply_typed (σ := .prop) (declares.sym_typed .imp) (ihp shaped)) (ihq shaped)
  | not p ih =>
      intro Θ ρ context shaped
      exact declares.apply_typed (σ := .prop) (declares.sym_typed .not) (ih shaped)
  | @eq Γ τ l r ihl ihr =>
      intro Θ ρ context shaped
      exact declares.apply_typed (declares.apply_typed (declares.eq_typed τ) (ihl shaped)) (ihr shaped)
  | @all σ Γ body ih =>
      intro Θ ρ context shaped
      exact declares.apply_typed (declares.quantifier_typed (s := .all) rfl σ)
        (declares.lam_typed (ih (shaped.extendObj (.refl _))))
  | @ex σ Γ body ih =>
      intro Θ ρ context shaped
      exact declares.apply_typed (declares.quantifier_typed (s := .ex) rfl σ)
        (declares.lam_typed (ih (shaped.extendObj (.refl _))))

/-- **One step keeps the coding**, for a term typed in a well-formed context of
hypotheses with objects.  A β-step substitutes a proof for a hypothesis or the
translation of a core term for an object; typing excludes the other pairings. -/
theorem PreCoded.step : ∀ {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {M : LF.Term},
    PreCoded e @ρ M → ∀ {context : LFTyping.Ctx} {A M' : LF.Term}, ShapedCtx e ρ context →
      WellFormedCtx LFProfile.standardLF (sttfaProofTheory e) context →
      LambdaPiModulo (sttfaProofTheory e) context M A → Step STTfa.theory M M' →
      PreCoded e ρ M' := by
  have headed := STTfa.orthogonal.leftAlgebraic.headed
  intro Γ Θ ρ M coded
  induction coded with
  | hyp _ =>
      intro context A M' _ _ _ step
      exact absurd step.var_inv (RootStep.not_var headed)
  | @lamHyp Γ Θ ρ domain body shape bodyCoded ih =>
      intro context A M' shaped wellFormed typed step
      obtain ⟨_, _, _, _, domainTyped, _, _, bodyTyped, _⟩ := typed.lam_inv
      rcases step.lam_inv with root | ⟨domain', inner, rfl⟩ | ⟨body', inner, rfl⟩
      · exact absurd root (RootStep.not_lam headed)
      · exact .lamHyp (shape.step inner) bodyCoded
      · exact .lamHyp shape (ih (shaped.extendHyp (ProofLike.of_shape shape))
          (.cons wellFormed domainTyped) bodyTyped inner)
  | @lamObj Γ Θ ρ σ domain body reduces bodyCoded ih =>
      intro context A M' shaped wellFormed typed step
      obtain ⟨_, _, _, _, domainTyped, _, _, bodyTyped, _⟩ := typed.lam_inv
      rcases step.lam_inv with root | ⟨domain', inner, rfl⟩ | ⟨body', inner, rfl⟩
      · exact absurd root (RootStep.not_lam headed)
      · exact .lamObj σ (reduces.tail inner) bodyCoded
      · exact .lamObj σ reduces (ih (shaped.extendObj (.symm _ _ reduces.conv))
          (.cons wellFormed domainTyped) bodyTyped inner)
  | @appProof Γ Θ ρ function argument functionCoded argumentCoded ihFunction ihArgument =>
      intro context A M' shaped wellFormed typed step
      obtain ⟨domain, bodyType, functionTyped, argumentTyped, _⟩ := typed.app_inv
      rcases step.app_inv with root | ⟨function', inner, rfl⟩ | ⟨argument', inner, rfl⟩
      · obtain ⟨D, body, arg, same, rfl⟩ :=
          rootStep_headless headed root (by simp [headConst, functionCoded.headConst_none])
        cases same
        obtain ⟨_, _, _, _, _, _, _, _, lamConv⟩ := functionTyped.lam_inv
        have lamDomain := conv_pi_domain (conv_proofTheory lamConv)
        cases functionCoded with
        | lamHyp _ bodyCoded =>
            refine bodyCoded.substHyp ρ 0 argument argumentCoded (fun v => ?_) ?_
            · show subst 0 argument (.var (varIndex (ρ v) + 1)) = .var (varIndex (ρ v))
              simp [LFTyping.subst]
            · intro index notObject differs τ v same
              obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero differs
              have : varIndex (ρ v) = i := by simpa using same
              exact notObject v (by simp [varIndex, this])
        | lamObj σ toD _ =>
            exact absurd (.symm _ _ toD.conv)
              (((argumentCoded.proofLike shaped argumentTyped).of_conv lamDomain).not_conv_objTree
                (El_objTree names _))
      · exact .appProof (ihFunction shaped wellFormed functionTyped inner) argumentCoded
      · exact .appProof functionCoded (ihArgument shaped wellFormed argumentTyped inner)
  | @appObj Γ Θ ρ function argument σ witness core functionCoded reduces ihFunction =>
      intro context A M' shaped wellFormed typed step
      obtain ⟨domain, bodyType, functionTyped, argumentTyped, _⟩ := typed.app_inv
      have argumentObject : LambdaPiModulo (sttfaProofTheory e) context argument (e.El (e.code σ)) :=
        sttfa_typePreservation names wellFormed (translate_typed_shaped names witness shaped)
          (reduces_toProofTheory reduces)
      have domainConv : Conv STTfa.theory domain (e.El (e.code σ)) :=
        proofTheory_unique argumentTyped argumentObject
      rcases step.app_inv with root | ⟨function', inner, rfl⟩ | ⟨argument', inner, rfl⟩
      · obtain ⟨D, body, arg, same, rfl⟩ :=
          rootStep_headless headed root (by simp [headConst, functionCoded.headConst_none])
        cases same
        obtain ⟨_, _, _, _, _, _, _, _, lamConv⟩ := functionTyped.lam_inv
        have lamDomain := conv_pi_domain (conv_proofTheory lamConv)
        cases functionCoded with
        | lamHyp shape _ =>
            exact absurd (.trans _ _ _ lamDomain domainConv) (shape.not_conv_objTree' (El_objTree names _))
        | lamObj σ' toD bodyCoded =>
            have sameDecoding : Encoding.elNF names.base σ' = Encoding.elNF names.base σ :=
              sttfa_normal_conv_eq (names.hub.elNF_normal σ') (names.hub.elNF_normal σ)
                (.trans _ _ _ (.symm _ _ (El_conv_elNF names σ'))
                  (.trans _ _ _ toD.conv (.trans _ _ _ lamDomain
                    (.trans _ _ _ domainConv (El_conv_elNF names σ)))))
            obtain rfl := Encoding.elNF_injective names.base names.hub.elAt_injective
              names.hub.elAt_not_pi sameDecoding
            refine bodyCoded.substObj ρ (HOL.Subst.single witness) 0 argument (HOL.CoreSubst.single core)
              (fun v => ?_) ?_
            · cases v with
              | vz =>
                  show Reduces STTfa.theory (e.translate (HOL.rename ρ witness)) (subst 0 argument (.var 0))
                  simpa [LFTyping.subst] using reduces
              | vs w =>
                  show Reduces STTfa.theory (.var (varIndex (ρ w)))
                    (subst 0 argument (.var (varIndex (ρ w) + 1)))
                  rw [show subst 0 argument (.var (varIndex (ρ w) + 1)) = .var (varIndex (ρ w)) by
                    simp [LFTyping.subst]]
            · intro index notObject
              cases index with
              | zero => exact absurd rfl (notObject .vz)
              | succ index =>
                  refine ⟨by omega, fun {τ} v same => ?_⟩
                  have : varIndex (ρ v) = index := by simpa using same
                  exact notObject (.vs v) (by simp [HOL.Rename.lift, varIndex, this])
      · exact .appObj witness core (ihFunction shaped wellFormed functionTyped inner) reduces
      · exact .appObj witness core functionCoded (reduces.tail inner)

/-- **Reduction keeps the coding**, for a term typed in a well-formed context of
hypotheses with objects. -/
theorem PreCoded.reduces {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {M N : LF.Term}
    {context : LFTyping.Ctx} {A : LF.Term} (coded : PreCoded e ρ M) (shaped : ShapedCtx e ρ context)
    (wellFormed : WellFormedCtx LFProfile.standardLF (sttfaProofTheory e) context)
    (typed : LambdaPiModulo (sttfaProofTheory e) context M A)
    (reduces : Reduces STTfa.theory M N) : PreCoded e ρ N := by
  induction reduces with
  | refl => exact coded
  | tail first step ih =>
      exact ih.step names shaped wellFormed
        (sttfa_typePreservation names wellFormed typed (reduces_toProofTheory first)) step

/-- **A normal coded reduct is coded**: its object domains and witnesses are in
normal form. -/
theorem PreCoded.toCoded : ∀ {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {M : LF.Term},
    PreCoded e @ρ M → IsNormal (Step STTfa.theory) M → Coded names ρ M := by
  intro Γ Θ ρ M coded
  induction coded with
  | hyp notObject => intro _; exact .hyp notObject
  | lamHyp shape _ ih => intro normal; exact .lamHyp shape (ih (normal_lam_body normal))
  | @lamObj Γ Θ ρ σ domain body reduces _ ih =>
      intro normal
      have same : domain = Encoding.elNF names.base σ :=
        sttfa_normal_conv_eq (normal_lam_domain normal) (names.hub.elNF_normal σ)
          (.trans _ _ _ (.symm _ _ reduces.conv) (El_conv_elNF names σ))
      subst same
      exact .lamObj σ (ih (normal_lam_body normal))
  | appProof _ _ ihFunction ihArgument =>
      intro normal
      exact .appProof (ihFunction (normal_app_function normal)) (ihArgument (normal_app_argument normal))
  | @appObj Γ Θ ρ function argument σ witness core _ reduces ihFunction =>
      intro normal
      have normalForm := names.hub.translate_normalForm
        (HOL.BetaNormalization.star_rename ρ (nf_reduces witness))
        (HOL.BetaNormalization.normal_rename ρ (nf_normal witness))
      have same : argument = e.translateNF names.base (HOL.rename ρ (nf witness)) :=
        normal_form_unique STTfa.confluent reduces (normal_app_argument normal) normalForm.1 normalForm.2
      subst same
      exact .appObj (nf witness) (HOL.Term.isCore_of_reducesStar (nf_reduces witness) core)
        (ihFunction (normal_app_function normal))

end Closure

/-! ## Compiled proofs -/

section Compiled

variable {Base : Type u} {Const : Ty Base → Type v}
variable {e : Encoding Base Const}

/-- **Compiled proofs are coded reducts**, when their ∀-witnesses are core and
the hypotheses sit at no place of an object. -/
theorem compile_preCoded : ∀ {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (d : HOL.ProofSyntaxModulo [] Δ φ), CoreWitnesses d →
    ∀ (L : Layout Const Γ) (hypVar : Fin Δ.length → Nat),
      (∀ (i : Fin Δ.length) {σ : Ty Base} (v : Var Γ σ), varIndex (L.toRename v) ≠ hypVar i) →
      PreCoded e (@L.toRename) (compile e "eps" d L hypVar) := by
  intro Γ Δ φ d
  induction d with
  | hyp occurrence =>
      intro _ L hypVar avoid
      exact .hyp fun v same => avoid occurrence v same
  | @impI Γ Δ premise conclusion body ih =>
      intro core L hypVar avoid
      refine .lamHyp (.eps _) (ih core (L.hyp premise) _ ?_)
      intro i σ v
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Layout.toRename, varIndex]
      · simp only [Fin.cases_succ, Layout.toRename, varIndex]
        exact fun same => avoid j v (Nat.succ_injective same)
  | impE function argument ihFunction ihArgument =>
      intro core L hypVar avoid
      exact .appProof (ihFunction core.1 L hypVar avoid) (ihArgument core.2 L hypVar avoid)
  | @allI Γ Δ σ body inner ih =>
      intro core L hypVar avoid
      refine .lamObj σ .refl (ih core (L.obj σ) _ ?_)
      intro i τ v
      cases v with
      | vz => simp [Layout.toRename, HOL.Rename.lift, varIndex]
      | vs w =>
          simp only [Layout.toRename, HOL.Rename.lift, varIndex]
          exact fun same => avoid _ w (Nat.succ_injective same)
  | @allE Γ Δ σ body t function ih =>
      intro core L hypVar avoid
      refine .appObj t core.1 (ih core.2 L hypVar avoid) ?_
      rw [Layout.place_translate e L t]
  | convert _ inner ih =>
      intro core L hypVar avoid
      exact ih core L hypVar avoid

end Compiled

section RoundTrip

variable {Base : Type u} {Const : Ty Base → Type v}
variable {e : Encoding Base Const} (names : SttfaNames e)
include names

theorem reduces_fromProofTheory {a b : LF.Term} (reduces : Reduces (sttfaProofTheory e) a b) :
    Reduces STTfa.theory a b := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih =>
      rw [step_proofTheory] at step
      exact ih.tail step

/-- **Every normal form of a compiled proof is coded**, when its ∀-witnesses are
core: for proofs with free objects, in the context of the decodings of the
objects. -/
theorem compile_normalForms_coded_open {Γ : Ctx Base} {φ : Formula Const Γ}
    (d : HOL.ProofSyntaxModulo [] [] φ) (core : CoreWitnesses d) {N : LF.Term}
    (reduces : Reduces (sttfaProofTheory e) (compile e "eps" d (.base Γ) Fin.elim0) N)
    (normal : IsNormal (Step (sttfaProofTheory e)) N) :
    Coded names (HOL.Rename.id (Γ := Γ)) N := by
  have proofs := sttfaProofHub e names.el names.arrow names.imp names.all names.fresh names.typeFresh
  have typed := proofs.theorem_typed d
  have wellFormed : WellFormedCtx LFProfile.standardLF (sttfaProofTheory e) (e.ctx Γ) := by
    clear typed reduces normal core d φ
    induction Γ with
    | nil => exact .nil
    | cons σ Γ ih => exact .cons ih (proofs.toDeclares.El_code_typed σ)
  have coded := (compile_preCoded (e := e) d core (.base Γ) Fin.elim0 (fun i => i.elim0)).reduces
    names (shapedCtx_objects Γ) wellFormed typed (reduces_fromProofTheory names reduces)
  rw [step_proofTheory] at normal
  exact coded.toCoded names normal

/-- **Every normal form of a compiled theorem is coded**, when its ∀-witnesses
are core. -/
theorem compile_normalForms_coded {φ : Formula Const []} (d : HOL.ProofSyntaxModulo [] [] φ)
    (core : CoreWitnesses d) {N : LF.Term}
    (reduces : Reduces (sttfaProofTheory e) (compile e "eps" d (.base []) Fin.elim0) N)
    (normal : IsNormal (Step (sttfaProofTheory e)) N) :
    Coded names (HOL.Rename.id (Γ := [])) N :=
  compile_normalForms_coded_open names d core reduces normal

/-- **Compile, normalize, decode, for every proof**: every normal form of the
compiled proof of a core theorem whose ∀-witnesses are core is coded, has the
type of the proofs of the theorem, and decodes to a proof of it. -/
theorem sttfa_round_trip_normalForms {φ : Formula Const []} (coreφ : φ.isCore = true)
    (d : HOL.ProofSyntaxModulo [] [] φ) (core : CoreWitnesses d) {N : LF.Term}
    (reduces : Reduces (sttfaProofTheory e) (compile e "eps" d (.base []) Fin.elim0) N)
    (normal : IsNormal (Step (sttfaProofTheory e)) N) :
    Coded names (HOL.Rename.id (Γ := [])) N ∧
      LambdaPiModulo (sttfaProofTheory e) [] N (.app (.con "eps") (e.translate φ)) ∧
      Nonempty (HOL.ProofSyntaxModulo [] [] φ) := by
  have coded := compile_normalForms_coded names d core reduces normal
  have proofs := sttfaProofHub e names.el names.arrow names.imp names.all names.fresh names.typeFresh
  have typed := sttfa_typePreservation names .nil (proofs.theorem_typed d) reduces
  exact ⟨coded, typed,
    sttfa_adequate_coded names (Δ := []) (fun _ member => absurd member List.not_mem_nil) coreφ
      coded normal typed⟩

end RoundTrip

end Mettapedia.GSLT.Dedukti.HOLHub
