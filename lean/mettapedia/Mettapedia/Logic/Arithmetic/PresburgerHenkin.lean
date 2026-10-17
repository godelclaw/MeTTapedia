import Mettapedia.Logic.Arithmetic.PresburgerBubble
import Mettapedia.Logic.HOL.Semantics.Henkin
import Mettapedia.Logic.HOL.Soundness

/-!
# Presburger sentences in Henkin models

A Henkin model restricts quantifiers to an admissible subset of each type
(Leon Henkin, *Completeness in the Theory of Types*, 1950).
`PreModel.base_mem` puts every individual into that subset.

Sentences whose quantifiers bind a base type, and whose equalities compare
propositions or individuals, never read the admissible set of an arrow type.
Their truth in a premodel therefore agrees with truth in the standard model
of the same individual carrier and the same constant denotations.

The Presburger presentation embeds into that class. On the carrier `ULift ℕ`,
with zero, one, and addition, every formula denotes the same proposition as
`Formula.sat`. `presburgerBubble` decides every closed sentence, and that
verdict agrees with truth in `arithStandard` and with truth in every
admissible premodel on the same carrier, Henkin models included.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Arithmetic.PresburgerHenkin

open Mettapedia.Logic.HOL hiding Formula
open Mettapedia.Logic.Arithmetic.PresburgerBubble

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Equality of propositions or of base individuals. -/
def equalityIgnoresAdm : Ty Base → Bool
  | .prop => true
  | .base _ => true
  | .arr _ _ => false

/-- The quantified type is a base type. -/
def quantifierOverBase : Ty Base → Bool
  | .base _ => true
  | .prop => false
  | .arr _ _ => false

/-- Quantifiers over a base type and equalities at `prop` or a base type. -/
def baseOnly : {Γ : Ctx Base} → {τ : Ty Base} → (t : Term Const Γ τ) → Bool
  | _, _, .var _ => true
  | _, _, .const _ => true
  | _, _, .app f a => baseOnly f && baseOnly a
  | _, _, .lam body => baseOnly body
  | _, _, .top => true
  | _, _, .bot => true
  | _, _, .and p q => baseOnly p && baseOnly q
  | _, _, .or p q => baseOnly p && baseOnly q
  | _, _, .imp p q => baseOnly p && baseOnly q
  | _, _, .not p => baseOnly p
  | _, _, .eq (τ := σ) a b => equalityIgnoresAdm σ && baseOnly a && baseOnly b
  | _, _, .all (σ := σ) body => quantifierOverBase σ && baseOnly body
  | _, _, .ex (σ := σ) body => quantifierOverBase σ && baseOnly body
  termination_by structural _ _ t => t

def standardOf (M : PreModel Base Const) : PreModel Base Const :=
  (HenkinModel.standard M.Carrier M.constDen).toPreModel

theorem denote_baseOnly (M : PreModel Base Const) :
    {Γ : Ctx Base} → {τ : Ty Base} → (t : Term Const Γ τ) →
      baseOnly t = true → (ρ : PreModel.Valuation M Γ) →
        PreModel.denote M t ρ = PreModel.denote (standardOf M) t ρ
  | _, _, .var _, _, _ => rfl
  | _, _, .const _, _, _ => rfl
  | _, _, .app f a, ht, ρ => by
      simp only [baseOnly, Bool.and_eq_true] at ht
      have hf := denote_baseOnly M f ht.1 ρ
      have ha := denote_baseOnly M a ht.2 ρ
      show PreModel.denote M f ρ (PreModel.denote M a ρ) =
        PreModel.denote (standardOf M) f ρ (PreModel.denote (standardOf M) a ρ)
      rw [hf, ha]
  | _, _, .lam body, ht, ρ => by
      funext x
      exact denote_baseOnly M body ht (PreModel.extend M ρ x)
  | _, _, .top, _, _ => rfl
  | _, _, .bot, _, _ => rfl
  | _, _, .and p q, ht, ρ => by
      simp only [baseOnly, Bool.and_eq_true] at ht
      have hp := denote_baseOnly M p ht.1 ρ
      have hq := denote_baseOnly M q ht.2 ρ
      show ULift.up ((PreModel.denote M p ρ).down ∧ (PreModel.denote M q ρ).down) =
        ULift.up ((PreModel.denote (standardOf M) p ρ).down ∧
          (PreModel.denote (standardOf M) q ρ).down)
      apply congrArg ULift.up
      apply propext
      rw [hp, hq]
  | _, _, .or p q, ht, ρ => by
      simp only [baseOnly, Bool.and_eq_true] at ht
      have hp := denote_baseOnly M p ht.1 ρ
      have hq := denote_baseOnly M q ht.2 ρ
      show ULift.up ((PreModel.denote M p ρ).down ∨ (PreModel.denote M q ρ).down) =
        ULift.up ((PreModel.denote (standardOf M) p ρ).down ∨
          (PreModel.denote (standardOf M) q ρ).down)
      apply congrArg ULift.up
      apply propext
      rw [hp, hq]
  | _, _, .imp p q, ht, ρ => by
      simp only [baseOnly, Bool.and_eq_true] at ht
      have hp := denote_baseOnly M p ht.1 ρ
      have hq := denote_baseOnly M q ht.2 ρ
      show ULift.up ((PreModel.denote M p ρ).down → (PreModel.denote M q ρ).down) =
        ULift.up ((PreModel.denote (standardOf M) p ρ).down →
          (PreModel.denote (standardOf M) q ρ).down)
      apply congrArg ULift.up
      apply propext
      rw [hp, hq]
  | _, _, .not p, ht, ρ => by
      have hp := denote_baseOnly M p ht ρ
      show ULift.up (¬ (PreModel.denote M p ρ).down) =
        ULift.up (¬ (PreModel.denote (standardOf M) p ρ).down)
      apply congrArg ULift.up
      apply propext
      rw [hp]
  | _, _, .eq (τ := σ) a b, ht, ρ => by
      simp only [baseOnly, Bool.and_eq_true] at ht
      rcases ht with ⟨⟨hσ, ha⟩, hb⟩
      have hA := denote_baseOnly M a ha ρ
      have hB := denote_baseOnly M b hb ρ
      cases σ with
      | prop =>
          show ULift.up ((PreModel.denote M a ρ).down ↔ (PreModel.denote M b ρ).down) =
            ULift.up ((PreModel.denote (standardOf M) a ρ).down ↔
              (PreModel.denote (standardOf M) b ρ).down)
          apply congrArg ULift.up
          apply propext
          rw [hA, hB]
      | base _ =>
          show ULift.up (PreModel.denote M a ρ = PreModel.denote M b ρ) =
            ULift.up (PreModel.denote (standardOf M) a ρ = PreModel.denote (standardOf M) b ρ)
          rw [hA, hB]
          rfl
      | arr _ _ =>
          rw [equalityIgnoresAdm] at hσ
          exact absurd hσ Bool.false_ne_true
  | _, _, .all (σ := σ) body, ht, ρ => by
      simp only [baseOnly, Bool.and_eq_true] at ht
      have hσ : quantifierOverBase σ = true := ht.1
      have hbody : baseOnly body = true := ht.2
      have hden : ∀ x, PreModel.denote M body (PreModel.extend M ρ x) =
          PreModel.denote (standardOf M) body (PreModel.extend M ρ x) :=
        fun x => denote_baseOnly M body hbody (PreModel.extend M ρ x)
      cases σ with
      | base b =>
          show ULift.up (∀ x, M.adm (.base b) x →
              (PreModel.denote M body (PreModel.extend M ρ x)).down) =
            ULift.up (∀ x, True →
              (PreModel.denote (standardOf M) body (PreModel.extend M ρ x)).down)
          apply congrArg ULift.up
          apply propext
          constructor
          · intro h x hx
            exact (iff_of_eq (congrArg ULift.down (hden x))).mp (h x (M.base_mem b x))
          · intro h x hx
            exact (iff_of_eq (congrArg ULift.down (hden x))).mpr (h x True.intro)
      | prop =>
          rw [quantifierOverBase] at hσ
          exact absurd hσ Bool.false_ne_true
      | arr _ _ =>
          rw [quantifierOverBase] at hσ
          exact absurd hσ Bool.false_ne_true
  | _, _, .ex (σ := σ) body, ht, ρ => by
      simp only [baseOnly, Bool.and_eq_true] at ht
      have hσ : quantifierOverBase σ = true := ht.1
      have hbody : baseOnly body = true := ht.2
      have hden : ∀ x, PreModel.denote M body (PreModel.extend M ρ x) =
          PreModel.denote (standardOf M) body (PreModel.extend M ρ x) :=
        fun x => denote_baseOnly M body hbody (PreModel.extend M ρ x)
      cases σ with
      | base b =>
          show ULift.up (∃ x, M.adm (.base b) x ∧
              (PreModel.denote M body (PreModel.extend M ρ x)).down) =
            ULift.up (∃ x, True ∧
              (PreModel.denote (standardOf M) body (PreModel.extend M ρ x)).down)
          apply congrArg ULift.up
          apply propext
          constructor
          · rintro ⟨x, hx, hdown⟩
            exact ⟨x, True.intro, (iff_of_eq (congrArg ULift.down (hden x))).mp hdown⟩
          · rintro ⟨x, _, hdown⟩
            exact ⟨x, M.base_mem b x, (iff_of_eq (congrArg ULift.down (hden x))).mpr hdown⟩
      | prop =>
          rw [quantifierOverBase] at hσ
          exact absurd hσ Bool.false_ne_true
      | arr _ _ =>
          rw [quantifierOverBase] at hσ
          exact absurd hσ Bool.false_ne_true
  termination_by _ _ t _ _ => sizeOf t

theorem models_baseOnly (M : PreModel Base Const) (φ : ClosedFormula Const)
    (hφ : baseOnly φ = true) :
    PreModel.models M φ ↔ PreModel.models (standardOf M) φ := by
  unfold PreModel.models
  exact iff_of_eq (congrArg ULift.down
    (denote_baseOnly M φ hφ (fun v => nomatch v)))

theorem baseOnly_rename {Γ Δ : Ctx Base} (ρr : Rename Base Γ Δ) :
    {τ : Ty Base} → (t : Term Const Γ τ) → baseOnly (rename ρr t) = baseOnly t
  | _, .var _ => rfl
  | _, .const _ => rfl
  | _, .app f a => by
      simp only [rename, baseOnly, baseOnly_rename ρr f, baseOnly_rename ρr a]
  | _, .lam body => by
      simp only [rename, baseOnly, baseOnly_rename (Rename.lift ρr) body]
  | _, .top => rfl
  | _, .bot => rfl
  | _, .and p q => by
      simp only [rename, baseOnly, baseOnly_rename ρr p, baseOnly_rename ρr q]
  | _, .or p q => by
      simp only [rename, baseOnly, baseOnly_rename ρr p, baseOnly_rename ρr q]
  | _, .imp p q => by
      simp only [rename, baseOnly, baseOnly_rename ρr p, baseOnly_rename ρr q]
  | _, .not p => by
      simp only [rename, baseOnly, baseOnly_rename ρr p]
  | _, .eq a b => by
      simp only [rename, baseOnly, baseOnly_rename ρr a, baseOnly_rename ρr b]
  | _, .all body => by
      simp only [rename, baseOnly, baseOnly_rename (Rename.lift ρr) body]
  | _, .ex body => by
      simp only [rename, baseOnly, baseOnly_rename (Rename.lift ρr) body]
  termination_by structural _ t => t

theorem baseOnly_weaken {Γ : Ctx Base} {σ τ : Ty Base} (t : Term Const Γ τ) :
    baseOnly (weaken (Base := Base) (σ := σ) t) = baseOnly t := by
  simpa [weaken] using baseOnly_rename (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ)) t

/-! ## Standard model of addition -/

inductive ArithBase where
  | nat
deriving DecidableEq, Repr

inductive ArithConst : Ty ArithBase → Type where
  | zero : ArithConst (.base .nat)
  | one : ArithConst (.base .nat)
  | add : ArithConst (.base .nat ⇒ .base .nat ⇒ .base .nat)
deriving DecidableEq, Repr

abbrev arithCarrier : ArithBase → Type 1 := fun _ => ULift.{1, 0} Nat

abbrev arithConstDen {τ : Ty ArithBase} (c : ArithConst τ) : Ty.denote.{0, 0} arithCarrier τ :=
  match τ, c with
  | _, .zero => ULift.up 0
  | _, .one => ULift.up 1
  | _, .add => fun x y => ULift.up (x.down + y.down)

/-- Full admissibility on `ULift ℕ` with zero, one, and addition. -/
abbrev arithStandard : HenkinModel.{0, 0, 0} ArithBase ArithConst :=
  { toPreModel := {
      Carrier := arithCarrier
      adm := fun _ _ => True
      base_mem := fun _ _ => True.intro
      prop_mem := fun _ => True.intro
      app_mem := fun _ _ => True.intro
      constDen := arithConstDen
      const_mem := fun _ => True.intro }
    term_closed := fun _ _ _ => True.intro }

theorem arithStandard_standard :
    arithStandard = HenkinModel.standard arithCarrier arithConstDen := by
  unfold HenkinModel.standard
  rfl

abbrev arithCtx (n : Nat) : Ctx ArithBase := List.replicate n (.base ArithBase.nat)

@[reducible] def envAt :
    {n : Nat} → (env : Fin n → Nat) → HenkinModel.Valuation arithStandard (arithCtx n)
  | 0, _ => fun v => nomatch v
  | n + 1, env =>
      HenkinModel.extend (σ := .base ArithBase.nat) (Γ := arithCtx n) arithStandard
        (envAt (fun i => env i.succ)) (ULift.up (env 0))

theorem envAt_cons {n : Nat} (z : Nat) (env : Fin n → Nat) :
    @Eq (HenkinModel.Valuation arithStandard ((.base ArithBase.nat) :: arithCtx n))
      (envAt (envCons z env))
      (HenkinModel.extend (σ := .base ArithBase.nat) (Γ := arithCtx n) arithStandard
        (envAt env) (ULift.up z)) := rfl

def embedNumeral {Γ : Ctx ArithBase} : Nat → Term ArithConst Γ (.base .nat)
  | 0 => .const .zero
  | k + 1 => .app (.app (.const .add) (embedNumeral k)) (.const .one)

def embedScale {Γ : Ctx ArithBase} (k : Nat) (t : Term ArithConst Γ (.base .nat)) :
    Term ArithConst Γ (.base .nat) :=
  match k with
  | 0 => .const .zero
  | k + 1 => .app (.app (.const .add) t) (embedScale k t)

def embedAdd {Γ : Ctx ArithBase}
    (a b : Term ArithConst Γ (.base .nat)) : Term ArithConst Γ (.base .nat) :=
  .app (.app (.const .add) a) b

@[simp] theorem denote_zero {Γ : Ctx ArithBase}
    (ρ : HenkinModel.Valuation arithStandard Γ) :
    HenkinModel.denote arithStandard (.const .zero : Term _ Γ _) ρ = ULift.up 0 := rfl

@[simp] theorem denote_one {Γ : Ctx ArithBase}
    (ρ : HenkinModel.Valuation arithStandard Γ) :
    HenkinModel.denote arithStandard (.const .one : Term _ Γ _) ρ = ULift.up 1 := rfl

theorem denote_app {Γ : Ctx ArithBase} {σ τ : Ty ArithBase}
    (f : Term ArithConst Γ (σ ⇒ τ)) (a : Term ArithConst Γ σ)
    (ρ : HenkinModel.Valuation arithStandard Γ) :
    HenkinModel.denote arithStandard (.app f a) ρ =
      HenkinModel.denote arithStandard f ρ (HenkinModel.denote arithStandard a ρ) := rfl

theorem denote_addConst {Γ : Ctx ArithBase}
    (ρ : HenkinModel.Valuation arithStandard Γ) :
    HenkinModel.denote arithStandard
        (.const .add : Term _ Γ (.base ArithBase.nat ⇒ .base ArithBase.nat ⇒ .base ArithBase.nat)) ρ =
      fun x y => ULift.up (x.down + y.down) := rfl

theorem denote_bin_add {Γ : Ctx ArithBase}
    (a b : Term ArithConst Γ (.base ArithBase.nat))
    (ρ : HenkinModel.Valuation arithStandard Γ) :
    HenkinModel.denote arithStandard (embedAdd a b) ρ =
      ULift.up ((HenkinModel.denote arithStandard a ρ).down +
        (HenkinModel.denote arithStandard b ρ).down) := by
  unfold embedAdd
  rw [denote_app, denote_app, denote_addConst]

private theorem ulift_down_add_congr {a b a' b' : ULift Nat}
    (ha : a = a') (hb : b = b') :
    ULift.up (a.down + b.down) = ULift.up (a'.down + b'.down) := by
  rw [ha, hb]

private theorem numeral_step (a o : ULift Nat) (k : Nat)
    (ha : a = ULift.up k) (ho : o = ULift.up 1) :
    ULift.up (a.down + o.down) = ULift.up (k + 1) := by
  rw [ha, ho]

private theorem scale_step (d k : Nat) : d + k * d = (k + 1) * d :=
  (Nat.add_comm d (k * d)).trans (Nat.succ_mul k d).symm

private theorem scale_step_ulift (d s : ULift Nat) (k : Nat)
    (hs : s = ULift.up (k * d.down)) :
    ULift.up (d.down + s.down) = ULift.up ((k + 1) * d.down) := by
  rw [hs]
  exact congrArg ULift.up (scale_step d.down k)

private theorem mul_down_congr (c : Nat) {v : ULift Nat} {x : Nat} (hv : v = ULift.up x) :
    ULift.up (c * v.down) = ULift.up (c * x) := by
  rw [hv]

theorem embedNumeral_denote {Γ : Ctx ArithBase} (k : Nat)
    (ρ : HenkinModel.Valuation arithStandard Γ) :
    HenkinModel.denote arithStandard (embedNumeral k) ρ = ULift.up k := by
  induction k with
  | zero =>
      exact denote_zero ρ
  | succ k ih =>
      show HenkinModel.denote arithStandard (embedAdd (embedNumeral k) (.const .one)) ρ =
        ULift.up (k + 1)
      exact (denote_bin_add (embedNumeral k) (.const .one) ρ).trans
        (numeral_step _ _ k ih (denote_one ρ))

theorem embedScale_denote {Γ : Ctx ArithBase} (k : Nat)
    (t : Term ArithConst Γ (.base ArithBase.nat))
    (ρ : HenkinModel.Valuation arithStandard Γ) :
    HenkinModel.denote arithStandard (embedScale k t) ρ =
      ULift.up (k * (HenkinModel.denote arithStandard t ρ).down) := by
  induction k with
  | zero =>
      show HenkinModel.denote arithStandard (.const .zero) ρ =
        ULift.up (0 * (HenkinModel.denote arithStandard t ρ).down)
      exact (denote_zero ρ).trans (congrArg ULift.up (Nat.zero_mul _).symm)
  | succ k ih =>
      show HenkinModel.denote arithStandard (embedAdd t (embedScale k t)) ρ =
        ULift.up ((k + 1) * (HenkinModel.denote arithStandard t ρ).down)
      exact (denote_bin_add t (embedScale k t) ρ).trans
        (scale_step_ulift _ _ k ih)

def embedDot : {n : Nat} → Coeff n → Term ArithConst (arithCtx n) (.base ArithBase.nat)
  | _, .nil => .const .zero
  | n + 1, .cons c cs =>
      embedAdd
        (embedScale c
          (.var (Var.ofFinRepeat (.base ArithBase.nat) (n + 1) (0 : Fin (n + 1)))))
        (weaken (Base := ArithBase) (σ := .base ArithBase.nat) (embedDot cs))

theorem denote_headVar {n : Nat} (env : Fin (n + 1) → Nat) :
    HenkinModel.denote arithStandard
        (.var (Var.ofFinRepeat (.base ArithBase.nat) (n + 1) (0 : Fin (n + 1))))
        (envAt env) =
      ULift.up (env 0) := by
  unfold Var.ofFinRepeat envAt HenkinModel.denote PreModel.denote HenkinModel.extend PreModel.extend
  rfl

theorem embedDot_denote : {n : Nat} → (cs : Coeff n) → (env : Fin n → Nat) →
    HenkinModel.denote arithStandard (embedDot cs) (envAt env) = ULift.up (cs.dot env)
  | _, .nil, _ => by
      rw [embedDot, Coeff.dot, denote_zero]
  | _, .cons c cs, env => by
      have hweak :=
        Soundness.denote_weaken (M := arithStandard) (σ := .base ArithBase.nat)
          (t := embedDot cs) (ρ := envAt (fun i => env i.succ)) (x := ULift.up (env 0))
      rw [embedDot, Coeff.dot, denote_bin_add, embedScale_denote, denote_headVar, hweak,
        embedDot_denote cs (fun i => env i.succ)]
  termination_by structural _ cs => cs

def embedLin {n : Nat} (t : LinTerm n) : Term ArithConst (arithCtx n) (.base .nat) :=
  embedAdd (embedDot t.coeff) (embedNumeral t.const)

theorem embedLin_denote {n : Nat} (t : LinTerm n) (env : Fin n → Nat) :
    HenkinModel.denote arithStandard (embedLin t) (envAt env) =
      ULift.up (t.eval env) := by
  cases t with
  | mk coeff const =>
      rw [embedLin, LinTerm.eval, denote_bin_add, embedDot_denote, embedNumeral_denote]

def embedAtom {n : Nat} : Atom n → Term ArithConst (arithCtx n) propTy
  | .eq left right => .eq (embedLin left) (embedLin right)
  | .lt left right =>
      .ex (σ := .base ArithBase.nat)
        (.eq
          (embedAdd
            (weaken (Base := ArithBase) (σ := .base ArithBase.nat) (embedLin left))
            (embedAdd (.var .vz) (.const .one)))
          (weaken (Base := ArithBase) (σ := .base ArithBase.nat) (embedLin right)))
  | .dvd modulus term =>
      if modulus = 0 then .bot
      else
        .ex (σ := .base ArithBase.nat)
          (.eq
            (weaken (Base := ArithBase) (σ := .base ArithBase.nat) (embedLin term))
            (embedScale modulus (.var .vz)))

theorem denote_eq_base {Γ : Ctx ArithBase}
    (a b : Term ArithConst Γ (.base ArithBase.nat))
    (ρ : HenkinModel.Valuation arithStandard Γ) :
    (HenkinModel.denote arithStandard (.eq a b) ρ).down ↔
      HenkinModel.denote arithStandard a ρ = HenkinModel.denote arithStandard b ρ :=
  Iff.rfl

theorem denote_ex_nat {Γ : Ctx ArithBase}
    (body : Term ArithConst (.base ArithBase.nat :: Γ) propTy)
    (ρ : HenkinModel.Valuation arithStandard Γ) :
    (HenkinModel.denote arithStandard (.ex (σ := .base ArithBase.nat) body) ρ).down ↔
      ∃ z : Nat,
        (HenkinModel.denote arithStandard body
          (HenkinModel.extend (σ := .base ArithBase.nat) arithStandard ρ (ULift.up z))).down := by
  show (∃ x : ULift.{1, 0} Nat, True ∧
      (HenkinModel.denote arithStandard body
        (HenkinModel.extend (σ := .base ArithBase.nat) arithStandard ρ x)).down) ↔
    ∃ z : Nat,
      (HenkinModel.denote arithStandard body
        (HenkinModel.extend (σ := .base ArithBase.nat) arithStandard ρ (ULift.up z))).down
  constructor
  · rintro ⟨⟨z⟩, _, h⟩
    exact ⟨z, h⟩
  · rintro ⟨z, h⟩
    exact ⟨⟨z⟩, True.intro, h⟩

theorem denote_varHead {Γ : Ctx ArithBase}
    (ρ : HenkinModel.Valuation arithStandard Γ) (z : Nat) :
    HenkinModel.denote arithStandard
        (.var .vz : Term ArithConst (.base ArithBase.nat :: Γ) (.base ArithBase.nat))
        (HenkinModel.extend (σ := .base ArithBase.nat) arithStandard ρ (ULift.up z)) =
      ULift.up z := by
  unfold HenkinModel.denote PreModel.denote HenkinModel.extend PreModel.extend
  rfl

theorem denote_succHead {Γ : Ctx ArithBase}
    (ρ : HenkinModel.Valuation arithStandard Γ) (z : Nat) :
    HenkinModel.denote arithStandard
        (embedAdd (.var .vz) (.const .one) :
          Term ArithConst (.base ArithBase.nat :: Γ) (.base ArithBase.nat))
        (HenkinModel.extend (σ := .base ArithBase.nat) arithStandard ρ (ULift.up z)) =
      ULift.up (z + 1) := by
  rw [denote_bin_add, denote_varHead, denote_one]

theorem ulift_eq_down {a b : Nat} : ULift.up a = ULift.up b ↔ a = b := by
  constructor
  · exact congrArg ULift.down
  · exact congrArg ULift.up

private theorem eq_iff_of_ulift {a b : ULift Nat} {x y : Nat}
    (ha : a = ULift.up x) (hb : b = ULift.up y) : a = b ↔ x = y := by
  rw [ha, hb]
  exact ulift_eq_down

theorem lt_body_iff {n : Nat} (left right : LinTerm n) (env : Fin n → Nat) (z : Nat) :
    (HenkinModel.denote arithStandard
      (.eq
        (embedAdd
          (weaken (Base := ArithBase) (σ := .base ArithBase.nat) (embedLin left))
          (embedAdd (.var .vz) (.const .one)))
        (weaken (Base := ArithBase) (σ := .base ArithBase.nat) (embedLin right)))
      (HenkinModel.extend (σ := .base ArithBase.nat) arithStandard (envAt env)
        (ULift.up z))).down ↔
    left.eval env + (z + 1) = right.eval env := by
  show
      (HenkinModel.denote arithStandard
          (embedAdd
            (weaken (Base := ArithBase) (σ := .base ArithBase.nat) (embedLin left))
            (embedAdd (.var .vz) (.const .one)))
          (HenkinModel.extend (σ := .base ArithBase.nat) arithStandard (envAt env)
            (ULift.up z)) =
        HenkinModel.denote arithStandard
          (weaken (Base := ArithBase) (σ := .base ArithBase.nat) (embedLin right))
          (HenkinModel.extend (σ := .base ArithBase.nat) arithStandard (envAt env)
            (ULift.up z))) ↔
    left.eval env + (z + 1) = right.eval env
  exact eq_iff_of_ulift
    ((denote_bin_add _ _ _).trans
      (ulift_down_add_congr
        ((Soundness.denote_weaken (M := arithStandard) (σ := .base ArithBase.nat)
            (t := embedLin left) (ρ := envAt env) (x := ULift.up z)).trans
          (embedLin_denote left env))
        (denote_succHead (envAt env) z)))
    ((Soundness.denote_weaken (M := arithStandard) (σ := .base ArithBase.nat)
        (t := embedLin right) (ρ := envAt env) (x := ULift.up z)).trans
      (embedLin_denote right env))

theorem dvd_body_iff {n : Nat} (modulus : Nat) (term : LinTerm n)
    (env : Fin n → Nat) (z : Nat) :
    (HenkinModel.denote arithStandard
      (.eq
        (weaken (Base := ArithBase) (σ := .base ArithBase.nat) (embedLin term))
        (embedScale modulus (.var .vz)))
      (HenkinModel.extend (σ := .base ArithBase.nat) arithStandard (envAt env)
        (ULift.up z))).down ↔
    term.eval env = modulus * z := by
  show
      (HenkinModel.denote arithStandard
          (weaken (Base := ArithBase) (σ := .base ArithBase.nat) (embedLin term))
          (HenkinModel.extend (σ := .base ArithBase.nat) arithStandard (envAt env)
            (ULift.up z)) =
        HenkinModel.denote arithStandard (embedScale modulus (.var .vz))
          (HenkinModel.extend (σ := .base ArithBase.nat) arithStandard (envAt env)
            (ULift.up z))) ↔
    term.eval env = modulus * z
  exact eq_iff_of_ulift
    ((Soundness.denote_weaken (M := arithStandard) (σ := .base ArithBase.nat)
        (t := embedLin term) (ρ := envAt env) (x := ULift.up z)).trans
      (embedLin_denote term env))
    ((embedScale_denote modulus (.var .vz) _).trans
      (mul_down_congr modulus (denote_varHead (envAt env) z)))

theorem embedAtom_iff {n : Nat} (a : Atom n) (env : Fin n → Nat) :
    (HenkinModel.denote arithStandard (embedAtom a) (envAt env)).down ↔ a.sat env := by
  cases a with
  | eq left right =>
      show (HenkinModel.denote arithStandard (embedLin left) (envAt env) =
          HenkinModel.denote arithStandard (embedLin right) (envAt env)) ↔
        left.eval env = right.eval env
      exact eq_iff_of_ulift (embedLin_denote left env) (embedLin_denote right env)
  | lt left right =>
      show (HenkinModel.denote arithStandard
          (.ex (σ := .base ArithBase.nat)
            (.eq
              (embedAdd
                (weaken (Base := ArithBase) (σ := .base ArithBase.nat) (embedLin left))
                (embedAdd (.var .vz) (.const .one)))
              (weaken (Base := ArithBase) (σ := .base ArithBase.nat) (embedLin right))))
          (envAt env)).down ↔
        left.eval env < right.eval env
      refine (denote_ex_nat _ (envAt env)).trans ?_
      constructor
      · rintro ⟨z, hbody⟩
        exact (lt_iff_exists_add_succ _ _).mpr ⟨z, (lt_body_iff left right env z).mp hbody⟩
      · intro hlt
        obtain ⟨z, hz⟩ := (lt_iff_exists_add_succ _ _).mp hlt
        exact ⟨z, (lt_body_iff left right env z).mpr hz⟩
  | dvd modulus term =>
      by_cases hmodulus : modulus = 0
      · rw [embedAtom, if_pos hmodulus, Atom.sat, HenkinModel.denote, PreModel.denote]
        simp [hmodulus]
      · rw [embedAtom, if_neg hmodulus, Atom.sat]
        refine (denote_ex_nat _ (envAt env)).trans ?_
        constructor
        · rintro ⟨z, hbody⟩
          exact ⟨hmodulus, (dvd_iff_exists_mul _ _ hmodulus).mpr
            ⟨z, (dvd_body_iff modulus term env z).mp hbody⟩⟩
        · rintro ⟨_, z, hz⟩
          exact ⟨z, (dvd_body_iff modulus term env z).mpr hz⟩

def embed : {n : Nat} → Formula n → Term ArithConst (arithCtx n) propTy
  | _, .bot => .bot
  | _, .atom a => embedAtom a
  | _, .conj left right => .and (embed left) (embed right)
  | _, .neg body => .not (embed body)
  | _, .ex body => .ex (σ := .base ArithBase.nat) (embed body)

theorem embed_iff : {n : Nat} → (φ : Formula n) → (env : Fin n → Nat) →
    (HenkinModel.denote arithStandard (embed φ) (envAt env)).down ↔ φ.sat env
  | _, .bot, _ => by
      rw [embed, Formula.sat, HenkinModel.denote, PreModel.denote]
  | _, .atom a, env => by
      rw [embed]
      exact embedAtom_iff a env
  | _, .conj left right, env => by
      rw [embed, Formula.sat, HenkinModel.denote, PreModel.denote, embed_iff left, embed_iff right]
  | _, .neg body, env => by
      rw [embed, Formula.sat, HenkinModel.denote, PreModel.denote, embed_iff body]
  | _, .ex body, env => by
      rw [embed, Formula.sat, denote_ex_nat]
      constructor
      · rintro ⟨z, hbody⟩
        refine ⟨z, ?_⟩
        rw [← envAt_cons z env] at hbody
        exact (embed_iff body (envCons z env)).mp hbody
      · intro ⟨z, hz⟩
        refine ⟨z, ?_⟩
        rw [← envAt_cons z env]
        exact (embed_iff body (envCons z env)).mpr hz
  termination_by structural _ φ => φ

theorem valuation_nil_unique (ρ σ : HenkinModel.Valuation arithStandard []) :
    @Eq (HenkinModel.Valuation arithStandard []) ρ σ := by
  funext τ v
  cases v

theorem models_eq_envAt (t : Term ArithConst [] propTy) :
    arithStandard.models t = (HenkinModel.denote arithStandard t (envAt env0)).down := by
  unfold HenkinModel.models PreModel.models HenkinModel.denote
  exact congrArg ULift.down
    (congrArg (fun ρ : HenkinModel.Valuation arithStandard [] =>
      PreModel.denote arithStandard.toPreModel t ρ)
      (valuation_nil_unique _ _))

theorem embed_models_iff (φ : Formula 0) :
    arithStandard.models (embed φ) ↔ φ.sat env0 :=
  (Iff.of_eq (models_eq_envAt (embed φ))).trans (embed_iff φ env0)

theorem embedScale_baseOnly {Γ : Ctx ArithBase} (k : Nat)
    (t : Term ArithConst Γ (.base .nat)) (ht : baseOnly t = true) :
    baseOnly (embedScale k t) = true := by
  induction k with
  | zero => simp [embedScale, baseOnly]
  | succ k ih => simp [embedScale, baseOnly, ht, ih]

theorem embedNumeral_baseOnly {Γ : Ctx ArithBase} (k : Nat) :
    baseOnly (embedNumeral k : Term ArithConst Γ _) = true := by
  induction k with
  | zero => simp [embedNumeral, baseOnly]
  | succ k ih => simp [embedNumeral, baseOnly, ih]

theorem baseOnly_embedAdd {Γ : Ctx ArithBase}
    (a b : Term ArithConst Γ (.base ArithBase.nat))
    (ha : baseOnly a = true) (hb : baseOnly b = true) :
    baseOnly (embedAdd a b) = true := by
  unfold embedAdd
  change ((true && baseOnly a) && baseOnly b) = true
  rw [ha, hb]
  rfl

theorem baseOnly_eq_base {Γ : Ctx ArithBase}
    (a b : Term ArithConst Γ (.base ArithBase.nat))
    (ha : baseOnly a = true) (hb : baseOnly b = true) :
    baseOnly (.eq a b) = true := by
  change (equalityIgnoresAdm (.base ArithBase.nat) && baseOnly a && baseOnly b) = true
  rw [equalityIgnoresAdm, ha, hb]
  rfl

theorem baseOnly_ex_base {Γ : Ctx ArithBase}
    (body : Term ArithConst (.base ArithBase.nat :: Γ) propTy)
    (hbody : baseOnly body = true) :
    baseOnly (.ex (σ := .base ArithBase.nat) body) = true := by
  change (quantifierOverBase (.base ArithBase.nat) && baseOnly body) = true
  rw [quantifierOverBase, hbody]
  rfl

theorem embedDot_baseOnly : {n : Nat} → (cs : Coeff n) → baseOnly (embedDot cs) = true
  | _, .nil => by
      rw [embedDot]
      rfl
  | n + 1, .cons c cs => by
      rw [embedDot]
      exact baseOnly_embedAdd _ _
        (embedScale_baseOnly c
          (.var (Var.ofFinRepeat (.base ArithBase.nat) (n + 1) (0 : Fin (n + 1)))) rfl)
        (by rw [baseOnly_weaken, embedDot_baseOnly cs])

theorem embedLin_baseOnly {n : Nat} (t : LinTerm n) : baseOnly (embedLin t) = true := by
  cases t with
  | mk coeff const =>
      rw [embedLin]
      exact baseOnly_embedAdd _ _ (embedDot_baseOnly coeff) (embedNumeral_baseOnly const)

theorem embedAtom_baseOnly {n : Nat} (a : Atom n) : baseOnly (embedAtom a) = true := by
  cases a with
  | eq left right =>
      rw [embedAtom]
      exact baseOnly_eq_base _ _ (embedLin_baseOnly left) (embedLin_baseOnly right)
  | lt left right =>
      rw [embedAtom]
      exact baseOnly_ex_base _
        (baseOnly_eq_base _ _
          (baseOnly_embedAdd _ _
            (by rw [baseOnly_weaken, embedLin_baseOnly])
            (baseOnly_embedAdd _ _ rfl rfl))
          (by rw [baseOnly_weaken, embedLin_baseOnly]))
  | dvd modulus term =>
      by_cases hmodulus : modulus = 0
      · rw [embedAtom, if_pos hmodulus]
        rfl
      · rw [embedAtom, if_neg hmodulus]
        exact baseOnly_ex_base _
          (baseOnly_eq_base _ _
            (by rw [baseOnly_weaken, embedLin_baseOnly])
            (embedScale_baseOnly modulus (.var .vz) rfl))

theorem embed_baseOnly : {n : Nat} → (φ : Formula n) → baseOnly (embed φ) = true
  | _, .bot => by simp [embed, baseOnly]
  | _, .atom a => by simp [embed, embedAtom_baseOnly]
  | _, .conj left right => by
      simp [embed, baseOnly, embed_baseOnly left, embed_baseOnly right]
  | _, .neg body => by
      simp [embed, baseOnly, embed_baseOnly body]
  | _, .ex body => by
      simp [embed, baseOnly, quantifierOverBase, embed_baseOnly body]
  termination_by structural _ φ => φ

def natPremodel
    (adm : (τ : Ty ArithBase) → Ty.denote.{0, 0} arithCarrier τ → Prop)
    (base_mem : ∀ b (x : arithCarrier b), adm (.base b) x)
    (prop_mem : ∀ p : ULift.{1, 0} Prop, adm .prop p)
    (app_mem :
      ∀ {σ τ} {f : Ty.denote.{0, 0} arithCarrier (σ ⇒ τ)} {x},
        adm (σ ⇒ τ) f → adm σ x → adm τ (f x))
    (const_mem : ∀ {τ} (c : ArithConst τ), adm τ (arithConstDen c)) :
    PreModel.{0, 0, 0} ArithBase ArithConst where
  Carrier := arithCarrier
  adm := adm
  base_mem := base_mem
  prop_mem := prop_mem
  app_mem := app_mem
  constDen := arithConstDen
  const_mem := const_mem

theorem natPremodel_models_embed
    (adm : (τ : Ty ArithBase) → Ty.denote.{0, 0} arithCarrier τ → Prop)
    (base_mem : ∀ b (x : arithCarrier b), adm (.base b) x)
    (prop_mem : ∀ p : ULift.{1, 0} Prop, adm .prop p)
    (app_mem :
      ∀ {σ τ} {f : Ty.denote.{0, 0} arithCarrier (σ ⇒ τ)} {x},
        adm (σ ⇒ τ) f → adm σ x → adm τ (f x))
    (const_mem : ∀ {τ} (c : ArithConst τ), adm τ (arithConstDen c))
    (φ : Formula 0) :
    PreModel.models
        (natPremodel adm base_mem prop_mem app_mem const_mem) (embed φ) ↔
      arithStandard.models (embed φ) := by
  have hagree :=
    models_baseOnly (natPremodel adm base_mem prop_mem app_mem const_mem)
      (embed φ) (embed_baseOnly φ)
  refine hagree.trans ?_
  unfold standardOf natPremodel
  rfl

/-- On the standard carrier, the bubble agrees with every admissible family. -/
theorem presburgerBubble_iff_natPremodel
    (adm : (τ : Ty ArithBase) → Ty.denote.{0, 0} arithCarrier τ → Prop)
    (base_mem : ∀ b (x : arithCarrier b), adm (.base b) x)
    (prop_mem : ∀ p : ULift.{1, 0} Prop, adm .prop p)
    (app_mem :
      ∀ {σ τ} {f : Ty.denote.{0, 0} arithCarrier (σ ⇒ τ)} {x},
        adm (σ ⇒ τ) f → adm σ x → adm τ (f x))
    (const_mem : ∀ {τ} (c : ArithConst τ), adm τ (arithConstDen c))
    (φ : Formula 0) {b : Bool}
    (h : presburgerBubble.decide φ = some b) :
    (b = true) ↔
      PreModel.models (natPremodel adm base_mem prop_mem app_mem const_mem) (embed φ) := by
  have hsat := presburgerBubble_decides φ h
  have hstd := embed_models_iff φ
  have hhen := natPremodel_models_embed adm base_mem prop_mem app_mem const_mem φ
  exact hsat.trans (hstd.symm.trans hhen.symm)

theorem presburgerBubble_iff_arithStandard (φ : Formula 0) {b : Bool}
    (h : presburgerBubble.decide φ = some b) :
    (b = true) ↔ arithStandard.models (embed φ) :=
  (presburgerBubble_decides φ h).trans (embed_models_iff φ).symm

/-- Every closed sentence: `some true` is truth in the standard model. -/
theorem presburgerBubble_iff_arithStandard_all (φ : Formula 0) :
    presburgerBubble.decide φ = some true ↔ arithStandard.models (embed φ) :=
  (presburgerBubble_iff_sat φ).trans (embed_models_iff φ).symm

/-- Every closed sentence agrees with every admissible family on `ULift ℕ`. -/
theorem presburgerBubble_iff_natPremodel_all
    (adm : (τ : Ty ArithBase) → Ty.denote.{0, 0} arithCarrier τ → Prop)
    (base_mem : ∀ b (x : arithCarrier b), adm (.base b) x)
    (prop_mem : ∀ p : ULift.{1, 0} Prop, adm .prop p)
    (app_mem :
      ∀ {σ τ} {f : Ty.denote.{0, 0} arithCarrier (σ ⇒ τ)} {x},
        adm (σ ⇒ τ) f → adm σ x → adm τ (f x))
    (const_mem : ∀ {τ} (c : ArithConst τ), adm τ (arithConstDen c))
    (φ : Formula 0) :
    presburgerBubble.decide φ = some true ↔
      PreModel.models
        (natPremodel adm base_mem prop_mem app_mem const_mem) (embed φ) :=
  (presburgerBubble_iff_arithStandard_all φ).trans
    (natPremodel_models_embed adm base_mem prop_mem app_mem const_mem φ).symm

/-! ## Controls -/

theorem control_prop_quantifier_not_baseOnly :
    baseOnly (Term.all (σ := .prop) (Term.var Var.vz) : Term ArithConst [] propTy) = false := by
  simp [baseOnly, quantifierOverBase]

theorem control_standard_zero_eq_zero :
    arithStandard.models (embed (closedEq 0 0)) :=
  (embed_models_iff (closedEq 0 0)).mpr (by
    simp [closedEq, Formula.sat, Atom.sat, LinTerm.eval, Coeff.dot])

theorem control_standard_zero_eq_one :
    ¬ arithStandard.models (embed (closedEq 0 1)) := by
  intro h
  have hsat := (embed_models_iff (closedEq 0 1)).mp h
  simp [closedEq, Formula.sat, Atom.sat, LinTerm.eval, Coeff.dot] at hsat

theorem control_bubble_exists_one :
    arithStandard.models (embed (exEqConst 1)) :=
  (presburgerBubble_iff_arithStandard (exEqConst 1) control_exists_one).mp rfl

theorem control_bubble_succ_eq_zero :
    ¬ arithStandard.models (embed exSuccEqZero) := by
  intro h
  have hdecide :=
    (presburgerBubble_iff_arithStandard exSuccEqZero control_succ_eq_zero).mpr h
  simp at hdecide

def fullNatPremodel : PreModel.{0, 0, 0} ArithBase ArithConst :=
  natPremodel (fun _ _ => True)
    (fun _ _ => True.intro)
    (fun _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ => True.intro)

theorem control_full_premodel_exists_one :
    PreModel.models fullNatPremodel (embed (exEqConst 1)) :=
  (presburgerBubble_iff_natPremodel (fun _ _ => True)
      (fun _ _ => True.intro) (fun _ => True.intro)
      (fun _ _ => True.intro) (fun _ => True.intro)
      (exEqConst 1) control_exists_one).mp rfl

theorem control_standard_nested_exists_zero :
    arithStandard.models (embed nestedExistsZero) :=
  (presburgerBubble_iff_arithStandard_all nestedExistsZero).mp
    control_nested_exists_zero

theorem control_standard_nested_double_odd :
    ¬ arithStandard.models (embed nestedDoubleOdd) := by
  intro h
  have htrue := (presburgerBubble_iff_arithStandard_all nestedDoubleOdd).mpr h
  rw [control_nested_double_odd, Option.some.injEq] at htrue
  simp at htrue

theorem control_full_premodel_nested_exists_zero :
    PreModel.models fullNatPremodel (embed nestedExistsZero) :=
  (presburgerBubble_iff_natPremodel_all (fun _ _ => True)
      (fun _ _ => True.intro) (fun _ => True.intro)
      (fun _ _ => True.intro) (fun _ => True.intro)
      nestedExistsZero).mp control_nested_exists_zero

theorem control_full_premodel_nested_exists :
    ¬ PreModel.models fullNatPremodel (embed nestedExists) := by
  intro h
  have htrue :=
    (presburgerBubble_iff_natPremodel_all (fun _ _ => True)
      (fun _ _ => True.intro) (fun _ => True.intro)
      (fun _ _ => True.intro) (fun _ => True.intro)
      nestedExists).mpr h
  rw [control_nested_exists_false, Option.some.injEq] at htrue
  simp at htrue

end Mettapedia.Logic.Arithmetic.PresburgerHenkin

#print axioms Mettapedia.Logic.Arithmetic.PresburgerHenkin.denote_baseOnly
#print axioms Mettapedia.Logic.Arithmetic.PresburgerHenkin.models_baseOnly
#print axioms Mettapedia.Logic.Arithmetic.PresburgerHenkin.embed_iff
#print axioms Mettapedia.Logic.Arithmetic.PresburgerHenkin.presburgerBubble_iff_natPremodel
#print axioms Mettapedia.Logic.Arithmetic.PresburgerHenkin.presburgerBubble_iff_arithStandard
#print axioms Mettapedia.Logic.Arithmetic.PresburgerHenkin.presburgerBubble_iff_natPremodel_all
#print axioms Mettapedia.Logic.Arithmetic.PresburgerHenkin.presburgerBubble_iff_arithStandard_all
