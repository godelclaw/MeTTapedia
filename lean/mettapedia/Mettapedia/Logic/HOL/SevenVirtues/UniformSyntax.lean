import Mettapedia.Logic.HOL.HOLLightBooleanDefinitions
import Mettapedia.Logic.HOL.WitnessedExtension
import Mettapedia.Logic.HOL.ImpredicativeProofModulo

/-!
# Virtue 1: a simple and highly uniform syntax

The calculus of the tree has thirteen term constructors. Four of them suffice:
variables, constants, application and abstraction, together with equality
(Henkin 1963; Andrews' `Q0`; Farmer's Section 4). The logical constants are
defined from equality in the style of HOL Light:

* `T := (λp. p) = (λp. p)`, `∀x. A := (λx. A) = (λx. T)`,
* `A ∧ B := (λf. f A B) = (λf. f T T)`, `A ⇒ B := (A ∧ B) = A`,
* `F := ∀p. p`, `¬A := A ⇒ F`, `A ∨ B := ∀r. (A ⇒ r) ⇒ (B ⇒ r) ⇒ r`,
* `∃x. A := ∀q. (∀x. A ⇒ q) ⇒ q`.

`eqExpand` replaces every logical constructor by its definition.

* `eqExpand_isEqCore`: the result uses only variables, constants, application,
  abstraction and equality.
* `denote_eqExpand`: it denotes the same value as the input in every Henkin
  model, at every type and valuation, standard or not.
* `provable_eq_eqExpand`: the calculus proves `t = eqExpand t` for every term,
  from no hypotheses, without excluded middle.
* `extDerivation_iff_eqExpand`: hence a sequent is derivable exactly when its
  expanded form is.

The same reasoning frees the existing HOL Light Boolean definitions
(`HOLLightBooleanDefinitions`) from their full-domain hypothesis: their
denotations are the intended connectives in every Henkin model
(`denote_conjunction_general` and the lemmas after it).

Negative example: equality cannot be dropped. Without equality or logical
constructors and with no constants there is no sentence at all
(`no_pure_lambda_sentence`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.SevenVirtues

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

namespace UniformSyntax

/-! ## The definitions -/

variable {Γ : Ctx Base}

/-- `T := (λp. p) = (λp. p)`. -/
def trueF : Formula Const Γ :=
  .eq (.lam (.var (.vz : Var (propTy :: Γ) propTy))) (.lam (.var .vz))

/-- `∀x. b := (λx. b) = (λx. T)`. -/
def allF {σ : Ty Base} (b : Formula Const (σ :: Γ)) : Formula Const Γ :=
  .eq (.lam b) (.lam trueF)

/-- `p ∧ q := (λf. f p q) = (λf. f T T)`. -/
def andF (p q : Formula Const Γ) : Formula Const Γ :=
  .eq (.lam (.app (.app (.var (.vz : Var ((propTy ⇒ propTy ⇒ propTy) :: Γ) _)) (weaken p))
      (weaken q)))
    (.lam (.app (.app (.var .vz) trueF) trueF))

/-- `p ⇒ q := (p ∧ q) = p`. -/
def impF (p q : Formula Const Γ) : Formula Const Γ := .eq (andF p q) p

/-- `F := ∀p. p`. -/
def falseF : Formula Const Γ := allF (σ := propTy) (.var .vz)

/-- `¬p := p ⇒ F`. -/
def notF (p : Formula Const Γ) : Formula Const Γ := impF p falseF

/-- `p ∨ q := ∀r. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r`. -/
def orF (p q : Formula Const Γ) : Formula Const Γ :=
  allF (σ := propTy)
    (impF (impF (weaken p) (.var .vz)) (impF (impF (weaken q) (.var .vz)) (.var .vz)))

/-- `∃x. b := ∀q. (∀x. b ⇒ q) ⇒ q`. -/
def exF {σ : Ty Base} (b : Formula Const (σ :: Γ)) : Formula Const Γ :=
  allF (σ := propTy)
    (impF (allF (σ := σ) (impF (rename (Rename.lift (Rename.weaken (σ := propTy))) b)
      (.var (.vs .vz)))) (.var .vz))

/-- Replace every logical constructor by its definition from equality. -/
def eqExpand : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Term Const Γ τ
  | _, _, .var v => .var v
  | _, _, .const c => .const c
  | _, _, .app f a => .app (eqExpand f) (eqExpand a)
  | _, _, .lam b => .lam (eqExpand b)
  | _, _, .top => trueF
  | _, _, .bot => falseF
  | _, _, .and p q => andF (eqExpand p) (eqExpand q)
  | _, _, .or p q => orF (eqExpand p) (eqExpand q)
  | _, _, .imp p q => impF (eqExpand p) (eqExpand q)
  | _, _, .not p => notF (eqExpand p)
  | _, _, .eq t s => .eq (eqExpand t) (eqExpand s)
  | _, _, .all b => allF (eqExpand b)
  | _, _, .ex b => exF (eqExpand b)

/-- The equality fragment: variables, constants, application, abstraction and
equality only. -/
def IsEqCore : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Prop
  | _, _, .var _ => True
  | _, _, .const _ => True
  | _, _, .app f a => IsEqCore f ∧ IsEqCore a
  | _, _, .lam b => IsEqCore b
  | _, _, .eq t s => IsEqCore t ∧ IsEqCore s
  | _, _, .top => False
  | _, _, .bot => False
  | _, _, .and _ _ => False
  | _, _, .or _ _ => False
  | _, _, .imp _ _ => False
  | _, _, .not _ => False
  | _, _, .all _ => False
  | _, _, .ex _ => False

theorem isEqCore_rename {Γ Δ : Ctx Base} (ρ : Rename Base Γ Δ) {τ : Ty Base}
    (t : Term Const Γ τ) (h : IsEqCore t) : IsEqCore (rename ρ t) := by
  induction t generalizing Δ with
  | var v => trivial
  | const c => trivial
  | app f a ihf iha => exact ⟨ihf ρ h.1, iha ρ h.2⟩
  | lam b ih => exact ih (Rename.lift ρ) h
  | eq t s iht ihs => exact ⟨iht ρ h.1, ihs ρ h.2⟩
  | top | bot | and | or | imp | not | all | ex => exact h.elim

theorem isEqCore_weaken {σ τ : Ty Base} (t : Term Const Γ τ) (h : IsEqCore t) :
    IsEqCore (weaken (σ := σ) t) :=
  isEqCore_rename _ t h

theorem isEqCore_trueF : IsEqCore (trueF : Formula Const Γ) := ⟨trivial, trivial⟩

theorem isEqCore_allF {σ : Ty Base} {b : Formula Const (σ :: Γ)} (h : IsEqCore b) :
    IsEqCore (allF b) := ⟨h, isEqCore_trueF⟩

theorem isEqCore_andF {p q : Formula Const Γ} (hp : IsEqCore p) (hq : IsEqCore q) :
    IsEqCore (andF p q) :=
  ⟨⟨⟨trivial, isEqCore_weaken p hp⟩, isEqCore_weaken q hq⟩,
    ⟨⟨trivial, isEqCore_trueF⟩, isEqCore_trueF⟩⟩

theorem isEqCore_impF {p q : Formula Const Γ} (hp : IsEqCore p) (hq : IsEqCore q) :
    IsEqCore (impF p q) := ⟨isEqCore_andF hp hq, hp⟩

theorem isEqCore_falseF : IsEqCore (falseF : Formula Const Γ) := isEqCore_allF trivial

theorem isEqCore_notF {p : Formula Const Γ} (hp : IsEqCore p) : IsEqCore (notF p) :=
  isEqCore_impF hp isEqCore_falseF

theorem isEqCore_orF {p q : Formula Const Γ} (hp : IsEqCore p) (hq : IsEqCore q) :
    IsEqCore (orF p q) :=
  isEqCore_allF (isEqCore_impF (isEqCore_impF (isEqCore_weaken p hp) trivial)
    (isEqCore_impF (isEqCore_impF (isEqCore_weaken q hq) trivial) trivial))

theorem isEqCore_exF {σ : Ty Base} {b : Formula Const (σ :: Γ)} (h : IsEqCore b) :
    IsEqCore (exF b) :=
  isEqCore_allF (isEqCore_impF (isEqCore_allF (isEqCore_impF (isEqCore_rename _ b h) trivial))
    trivial)

/-- **The expansion lands in the equality fragment.** -/
theorem eqExpand_isEqCore {τ : Ty Base} (t : Term Const Γ τ) : IsEqCore (eqExpand t) := by
  induction t with
  | var v => trivial
  | const c => trivial
  | app f a ihf iha => exact ⟨ihf, iha⟩
  | lam b ih => exact ih
  | top => exact isEqCore_trueF
  | bot => exact isEqCore_falseF
  | and p q ihp ihq => exact isEqCore_andF ihp ihq
  | or p q ihp ihq => exact isEqCore_orF ihp ihq
  | imp p q ihp ihq => exact isEqCore_impF ihp ihq
  | not p ih => exact isEqCore_notF ih
  | eq t s iht ihs => exact ⟨iht, ihs⟩
  | all b ih => exact isEqCore_allF ih
  | ex b ih => exact isEqCore_exF ih

/-- On the equality fragment the expansion is the identity. -/
theorem eqExpand_of_isEqCore {τ : Ty Base} (t : Term Const Γ τ) (h : IsEqCore t) :
    eqExpand t = t := by
  induction t with
  | var v => rfl
  | const c => rfl
  | app f a ihf iha => simp only [eqExpand, ihf h.1, iha h.2]
  | lam b ih => simp only [eqExpand, ih h]
  | eq t s iht ihs => simp only [eqExpand, iht h.1, ihs h.2]
  | top | bot | and | or | imp | not | all | ex => exact h.elim

/-! ## Meaning in every Henkin model -/

section Semantics

variable (M : HenkinModel.{u, v, w} Base Const)

theorem denote_trueF (ρ : M.Valuation Γ) : M.denote (trueF : Formula Const Γ) ρ = .up True := by
  apply ULift.ext
  apply propext
  change (∀ x, M.adm .prop x → (x.down ↔ x.down)) ↔ True
  exact ⟨fun _ => trivial, fun _ _ _ => Iff.rfl⟩

theorem denote_allF {σ : Ty Base} (b : Formula Const (σ :: Γ)) (ρ : M.Valuation Γ) :
    M.denote (allF b) ρ = .up (∀ x, M.adm σ x → (M.denote b (M.extend ρ x)).down) := by
  apply ULift.ext
  apply propext
  change (∀ x, M.adm σ x → ((M.denote b (M.extend ρ x)).down ↔
    (M.denote (trueF : Formula Const (σ :: Γ)) (M.extend ρ x)).down)) ↔ _
  simp only [denote_trueF, iff_true]

/-- The first projection on truth values is admissible: it is denoted by a
closed term. -/
theorem first_admissible :
    M.adm (propTy ⇒ propTy ⇒ propTy) (fun p _ => p) :=
  M.denote_admissible (Γ := []) (ρ := fun v => nomatch v) (by intro _ v; nomatch v)
    (.lam (.lam (.var (.vs .vz))) : ClosedTerm Const (propTy ⇒ propTy ⇒ propTy))

/-- The second projection on truth values is admissible. -/
theorem second_admissible :
    M.adm (propTy ⇒ propTy ⇒ propTy) (fun _ q => q) :=
  M.denote_admissible (Γ := []) (ρ := fun v => nomatch v) (by intro _ v; nomatch v)
    (.lam (.lam (.var .vz)) : ClosedTerm Const (propTy ⇒ propTy ⇒ propTy))

/-- Conjunction from equality is conjunction, in every Henkin model: the two
projections that separate the arguments are admissible. -/
theorem conj_iff (p q : Ty.denote M.Carrier propTy) :
    (∀ f : Ty.denote M.Carrier (propTy ⇒ propTy ⇒ propTy), M.adm _ f →
        ((f p q).down ↔ (f (.up True) (.up True)).down)) ↔ (p.down ∧ q.down) := by
  constructor
  · intro h
    exact ⟨(h _ (first_admissible M)).mpr trivial, (h _ (second_admissible M)).mpr trivial⟩
  · rintro ⟨hp, hq⟩ f _
    have ep : p = .up True := ULift.ext _ _ (propext (iff_true_intro hp))
    have eq : q = .up True := ULift.ext _ _ (propext (iff_true_intro hq))
    rw [ep, eq]

theorem denote_andF (p q : Formula Const Γ) (ρ : M.Valuation Γ) :
    M.denote (andF p q) ρ = .up ((M.denote p ρ).down ∧ (M.denote q ρ).down) := by
  apply ULift.ext
  apply propext
  change (∀ f, M.adm (propTy ⇒ propTy ⇒ propTy) f →
      ((f (M.denote (weaken p) (M.extend ρ f)) (M.denote (weaken q) (M.extend ρ f))).down ↔
        (f (M.denote (trueF : Formula Const ((propTy ⇒ propTy ⇒ propTy) :: Γ)) (M.extend ρ f))
          (M.denote (trueF : Formula Const ((propTy ⇒ propTy ⇒ propTy) :: Γ))
            (M.extend ρ f))).down)) ↔ _
  simp only [Soundness.denote_weaken, denote_trueF]
  exact conj_iff M _ _

theorem denote_impF (p q : Formula Const Γ) (ρ : M.Valuation Γ) :
    M.denote (impF p q) ρ = .up ((M.denote p ρ).down → (M.denote q ρ).down) := by
  apply ULift.ext
  apply propext
  change ((M.denote (andF p q) ρ).down ↔ (M.denote p ρ).down) ↔ _
  rw [denote_andF]
  exact ⟨fun h hp => (h.mpr hp).2, fun h => ⟨And.left, fun hp => ⟨hp, h hp⟩⟩⟩

theorem denote_falseF (ρ : M.Valuation Γ) : M.denote (falseF : Formula Const Γ) ρ = .up False := by
  rw [falseF, denote_allF]
  apply ULift.ext
  apply propext
  exact ⟨fun h => h (.up False) (M.prop_mem _), False.elim⟩

theorem denote_notF (p : Formula Const Γ) (ρ : M.Valuation Γ) :
    M.denote (notF p) ρ = .up (¬ (M.denote p ρ).down) := by
  rw [notF, denote_impF, denote_falseF]

theorem denote_orF (p q : Formula Const Γ) (ρ : M.Valuation Γ) :
    M.denote (orF p q) ρ = .up ((M.denote p ρ).down ∨ (M.denote q ρ).down) := by
  rw [orF, denote_allF]
  apply ULift.ext
  apply propext
  simp only [denote_impF, Soundness.denote_weaken]
  constructor
  · intro h
    exact h (.up ((M.denote p ρ).down ∨ (M.denote q ρ).down)) (M.prop_mem _) Or.inl Or.inr
  · intro h r _ hpr hqr
    exact h.elim hpr hqr

theorem denote_exF {σ : Ty Base} (b : Formula Const (σ :: Γ)) (ρ : M.Valuation Γ) :
    M.denote (exF b) ρ = .up (∃ x, M.adm σ x ∧ (M.denote b (M.extend ρ x)).down) := by
  rw [exF, denote_allF]
  apply ULift.ext
  apply propext
  have hRename : ∀ (r : Ty.denote M.Carrier propTy) (x : Ty.denote M.Carrier σ),
      M.denote (rename (Rename.lift (Rename.weaken (σ := propTy))) b)
        (M.extend (M.extend ρ r) x) = M.denote b (M.extend ρ x) := by
    intro r x
    rw [Soundness.denote_rename, Soundness.renameVal_lift, Soundness.renameVal_weaken_extend]
  simp only [denote_impF, denote_allF, hRename]
  constructor
  · intro h
    exact h (.up (∃ x, M.adm σ x ∧ (M.denote b (M.extend ρ x)).down)) (M.prop_mem _)
      (fun x hx hb => ⟨x, hx, hb⟩)
  · rintro ⟨x, hx, hb⟩ r _ h
    exact h x hx hb

/-- **The definitions mean the logical constants in every Henkin model**, at
every type and valuation. -/
theorem denote_eqExpand {τ : Ty Base} (t : Term Const Γ τ) (ρ : M.Valuation Γ) :
    M.denote (eqExpand t) ρ = M.denote t ρ := by
  induction t with
  | var v => rfl
  | const c => rfl
  | app f a ihf iha =>
      change M.denote (eqExpand f) ρ (M.denote (eqExpand a) ρ) = M.denote f ρ (M.denote a ρ)
      rw [ihf, iha]
  | lam b ih =>
      funext x
      exact ih _
  | top => exact denote_trueF M ρ
  | bot => exact denote_falseF M ρ
  | and p q ihp ihq =>
      rw [eqExpand, denote_andF, ihp, ihq]
      rfl
  | or p q ihp ihq =>
      rw [eqExpand, denote_orF, ihp, ihq]
      rfl
  | imp p q ihp ihq =>
      rw [eqExpand, denote_impF, ihp, ihq]
      rfl
  | not p ih =>
      rw [eqExpand, denote_notF, ih]
      rfl
  | eq t s iht ihs =>
      change ULift.up (M.Eqv _ (M.denote (eqExpand t) ρ) (M.denote (eqExpand s) ρ)) =
        ULift.up (M.Eqv _ (M.denote t ρ) (M.denote s ρ))
      rw [iht, ihs]
  | all b ih =>
      rw [eqExpand, denote_allF]
      apply ULift.ext
      apply propext
      change _ ↔ ∀ x, M.adm _ x → (M.denote b (M.extend ρ x)).down
      simp only [ih]
  | ex b ih =>
      rw [eqExpand, denote_exF]
      apply ULift.ext
      apply propext
      change _ ↔ ∃ x, M.adm _ x ∧ (M.denote b (M.extend ρ x)).down
      simp only [ih]

theorem models_eqExpand (φ : ClosedFormula Const) : M.models (eqExpand φ) ↔ M.models φ :=
  Iff.of_eq (congrArg ULift.down (denote_eqExpand M φ (fun v => nomatch v)))

end Semantics

/-! ## Commutation with renaming and substitution -/

section Commutation

variable {Δ' : Ctx Base}

theorem rename_trueF (ρ : Rename Base Γ Δ') : rename ρ (trueF : Formula Const Γ) = trueF := rfl

theorem rename_allF {σ : Ty Base} (ρ : Rename Base Γ Δ') (b : Formula Const (σ :: Γ)) :
    rename ρ (allF b) = allF (rename (Rename.lift ρ) b) := rfl

theorem rename_andF (ρ : Rename Base Γ Δ') (p q : Formula Const Γ) :
    rename ρ (andF p q) = andF (rename ρ p) (rename ρ q) := by
  change Term.eq (.lam (.app (.app (.var .vz) (rename (Rename.lift ρ) (weaken p)))
      (rename (Rename.lift ρ) (weaken q)))) (.lam (.app (.app (.var .vz) trueF) trueF)) = _
  simp only [weaken, rename_lift_weaken]
  rfl

theorem rename_impF (ρ : Rename Base Γ Δ') (p q : Formula Const Γ) :
    rename ρ (impF p q) = impF (rename ρ p) (rename ρ q) := by
  change Term.eq (rename ρ (andF p q)) (rename ρ p) = _
  rw [rename_andF]
  rfl

theorem rename_exF {σ : Ty Base} (ρ : Rename Base Γ Δ') (b : Formula Const (σ :: Γ)) :
    rename ρ (exF b) = exF (rename (Rename.lift ρ) b) := by
  rw [exF, rename_allF, rename_impF, rename_allF, rename_impF]
  have hb : rename (Rename.lift (Rename.lift ρ))
      (rename (Rename.lift (Rename.weaken (σ := propTy))) b) =
      rename (Rename.lift (Rename.weaken (σ := propTy))) (rename (Rename.lift ρ) b) := by
    rw [rename_comp, rename_comp]
    apply rename_ext
    intro _ v
    cases v <;> rfl
  rw [hb]
  rfl

theorem subst_andF (σs : Subst Const Γ Δ') (p q : Formula Const Γ) :
    subst σs (andF p q) = andF (subst σs p) (subst σs q) := by
  change Term.eq (.lam (.app (.app (.var .vz) (subst (Subst.lift σs) (weaken p)))
      (subst (Subst.lift σs) (weaken q)))) (.lam (.app (.app (.var .vz) trueF) trueF)) = _
  rw [subst_weaken, subst_weaken]
  rfl

theorem subst_impF (σs : Subst Const Γ Δ') (p q : Formula Const Γ) :
    subst σs (impF p q) = impF (subst σs p) (subst σs q) := by
  change Term.eq (subst σs (andF p q)) (subst σs p) = _
  rw [subst_andF]
  rfl

theorem subst_allF {σ : Ty Base} (σs : Subst Const Γ Δ') (b : Formula Const (σ :: Γ)) :
    subst σs (allF b) = allF (subst (Subst.lift σs) b) := rfl

/-- Instantiating the weakened term in the lifted weakening of a body. -/
theorem instantiate_weaken_rename_lift_weaken {σ τ : Ty Base} (t : Term Const Γ σ)
    (b : Term Const (σ :: Γ) τ) :
    instantiate (weaken (σ := propTy) t) (rename (Rename.lift (Rename.weaken (σ := propTy))) b) =
      weaken (σ := propTy) (instantiate t b) := by
  unfold instantiate weaken
  rw [subst_rename, rename_subst]
  apply subst_ext
  intro _ v
  cases v <;> rfl

end Commutation

/-! ## Derived rules for the defined constants -/

section Derivations

variable {Δ : List (Formula Const Γ)}

theorem monoNil {φ : Formula Const Γ} (h : ExtDerivation Const [] φ) :
    ExtDerivation Const Δ φ :=
  ExtDerivation.mono (fun hχ => absurd hχ List.not_mem_nil) h

theorem trueF_intro : ExtDerivation Const Δ (trueF : Formula Const Γ) := .eqRefl _

theorem eq_trueF_of {p : Formula Const Γ} (h : ExtDerivation Const Δ p) :
    ExtDerivation Const Δ (.eq p trueF) :=
  .eqPropI (.impI trueF_intro) (.impI (ExtDerivation.mono (fun hχ => List.mem_cons_of_mem _ hχ) h))

theorem of_eq_trueF {p : Formula Const Γ} (h : ExtDerivation Const Δ (.eq p trueF)) :
    ExtDerivation Const Δ p :=
  ExtDerivation.eqProp_mp_right h trueF_intro

theorem allF_intro {σ : Ty Base} {b : Formula Const (σ :: Γ)}
    (h : ExtDerivation Const (weakenHyps (σ := σ) Δ) b) : ExtDerivation Const Δ (allF b) :=
  .eqLam (eq_trueF_of h)

theorem allF_elim {σ : Ty Base} {b : Formula Const (σ :: Γ)} (t : Term Const Γ σ)
    (h : ExtDerivation Const Δ (allF b)) : ExtDerivation Const Δ (instantiate t b) := by
  have h1 : ExtDerivation Const Δ (.eq (.app (.lam b) t) (.app (.lam trueF) t)) := .eqApp t h
  have h2 : ExtDerivation Const Δ (.eq (instantiate t b) (instantiate t trueF)) :=
    .eqTrans (.eqSymm (.beta t b)) (.eqTrans h1 (.beta t trueF))
  exact of_eq_trueF h2

/-- `λx y. x`. -/
def first : Term Const Γ (propTy ⇒ propTy ⇒ propTy) := .lam (.lam (.var (.vs .vz)))

/-- `λx y. y`. -/
def second : Term Const Γ (propTy ⇒ propTy ⇒ propTy) := .lam (.lam (.var .vz))

theorem first_beta (a c : Formula Const Γ) :
    ExtDerivation Const Δ (.eq (.app (.app first a) c) a) := by
  have h1 : ExtDerivation Const Δ (.eq (.app (.app first a) c) (.app (.lam (weaken a)) c)) :=
    .eqApp c (.beta a (.lam (.var (.vs .vz))))
  have h2 : ExtDerivation Const Δ (.eq (.app (.lam (weaken a)) c) a) := by
    have := ExtDerivation.beta (Δ := Δ) c (weaken (σ := propTy) a)
    rwa [instantiate_weaken] at this
  exact .eqTrans h1 h2

theorem second_beta (a c : Formula Const Γ) :
    ExtDerivation Const Δ (.eq (.app (.app second a) c) c) := by
  have h1 : ExtDerivation Const Δ (.eq (.app (.app second a) c) (.app (.lam (.var .vz)) c)) :=
    .eqApp c (.beta a (.lam (.var .vz)))
  exact .eqTrans h1 (.beta c (.var .vz))

theorem instantiate_pair (t : Term Const Γ (propTy ⇒ propTy ⇒ propTy)) (p q : Formula Const Γ) :
    instantiate t (.app (.app (.var .vz) (weaken p)) (weaken q)) = .app (.app t p) q := by
  change Term.app (.app t (instantiate t (weaken p))) (instantiate t (weaken q)) = _
  rw [instantiate_weaken, instantiate_weaken]

theorem andF_intro {p q : Formula Const Γ} (hp : ExtDerivation Const Δ p)
    (hq : ExtDerivation Const Δ q) : ExtDerivation Const Δ (andF p q) := by
  have wp : ExtDerivation Const (weakenHyps (σ := propTy ⇒ propTy ⇒ propTy) Δ)
      (.eq (weaken p) trueF) := ExtDerivation.rename Rename.weaken (eq_trueF_of hp)
  have wq : ExtDerivation Const (weakenHyps (σ := propTy ⇒ propTy ⇒ propTy) Δ)
      (.eq (weaken q) trueF) := ExtDerivation.rename Rename.weaken (eq_trueF_of hq)
  exact .eqLam (ExtDerivation.eqAppCongr (ExtDerivation.eqAppCongr (.eqRefl _) wp) wq)

theorem andF_left {p q : Formula Const Γ} (h : ExtDerivation Const Δ (andF p q)) :
    ExtDerivation Const Δ p := by
  have h1 := ExtDerivation.eqApp (first : Term Const Γ _) h
  have hL : ExtDerivation Const Δ
      (.eq (.app (.lam (.app (.app (.var .vz) (weaken p)) (weaken q))) first)
        (.app (.app first p) q)) := by
    have := ExtDerivation.beta (Δ := Δ) (first : Term Const Γ _)
      (.app (.app (.var .vz) (weaken p)) (weaken q))
    rwa [instantiate_pair] at this
  have hR : ExtDerivation Const Δ
      (.eq (.app (.lam (.app (.app (.var .vz) trueF) trueF)) first)
        (.app (.app first trueF) trueF)) :=
    ExtDerivation.beta (first : Term Const Γ _) (.app (.app (.var .vz) trueF) trueF)
  exact of_eq_trueF (.eqTrans (.eqSymm (first_beta p q))
    (.eqTrans (.eqSymm hL) (.eqTrans h1 (.eqTrans hR (first_beta trueF trueF)))))

theorem andF_right {p q : Formula Const Γ} (h : ExtDerivation Const Δ (andF p q)) :
    ExtDerivation Const Δ q := by
  have h1 := ExtDerivation.eqApp (second : Term Const Γ _) h
  have hL : ExtDerivation Const Δ
      (.eq (.app (.lam (.app (.app (.var .vz) (weaken p)) (weaken q))) second)
        (.app (.app second p) q)) := by
    have := ExtDerivation.beta (Δ := Δ) (second : Term Const Γ _)
      (.app (.app (.var .vz) (weaken p)) (weaken q))
    rwa [instantiate_pair] at this
  have hR : ExtDerivation Const Δ
      (.eq (.app (.lam (.app (.app (.var .vz) trueF) trueF)) second)
        (.app (.app second trueF) trueF)) :=
    ExtDerivation.beta (second : Term Const Γ _) (.app (.app (.var .vz) trueF) trueF)
  exact of_eq_trueF (.eqTrans (.eqSymm (second_beta p q))
    (.eqTrans (.eqSymm hL) (.eqTrans h1 (.eqTrans hR (second_beta trueF trueF)))))

theorem impF_intro {p q : Formula Const Γ} (h : ExtDerivation Const (p :: Δ) q) :
    ExtDerivation Const Δ (impF p q) :=
  .eqPropI (.impI (andF_left (.hyp List.mem_cons_self))) (.impI (andF_intro (.hyp List.mem_cons_self) h))

theorem impF_elim {p q : Formula Const Γ} (h : ExtDerivation Const Δ (impF p q))
    (hp : ExtDerivation Const Δ p) : ExtDerivation Const Δ q :=
  andF_right (ExtDerivation.eqProp_mp_right h hp)

theorem falseF_elim {φ : Formula Const Γ} (h : ExtDerivation Const Δ falseF) :
    ExtDerivation Const Δ φ :=
  allF_elim (b := (.var .vz : Formula Const (propTy :: Γ))) φ h

theorem orF_inl {p q : Formula Const Γ} (hp : ExtDerivation Const Δ p) :
    ExtDerivation Const Δ (orF p q) := by
  refine allF_intro (impF_intro (impF_intro ?_))
  refine impF_elim (.hyp (List.mem_cons_of_mem _ List.mem_cons_self)) ?_
  refine ExtDerivation.mono (fun hχ => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hχ)) ?_
  exact ExtDerivation.rename Rename.weaken hp

theorem orF_inr {p q : Formula Const Γ} (hq : ExtDerivation Const Δ q) :
    ExtDerivation Const Δ (orF p q) := by
  refine allF_intro (impF_intro (impF_intro ?_))
  refine impF_elim (.hyp List.mem_cons_self) ?_
  refine ExtDerivation.mono (fun hχ => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hχ)) ?_
  exact ExtDerivation.rename Rename.weaken hq

theorem orF_elim {p q χ : Formula Const Γ} (h : ExtDerivation Const Δ (orF p q))
    (hp : ExtDerivation Const (p :: Δ) χ) (hq : ExtDerivation Const (q :: Δ) χ) :
    ExtDerivation Const Δ χ := by
  have hInst := allF_elim χ h
  rw [instantiate, subst_impF, subst_impF, subst_impF, subst_impF] at hInst
  change ExtDerivation Const Δ (impF (impF (instantiate χ (weaken p)) χ)
    (impF (impF (instantiate χ (weaken q)) χ) χ)) at hInst
  rw [instantiate_weaken, instantiate_weaken] at hInst
  exact impF_elim (impF_elim hInst (impF_intro hp)) (impF_intro hq)

theorem exF_intro {σ : Ty Base} {b : Formula Const (σ :: Γ)} (t : Term Const Γ σ)
    (h : ExtDerivation Const Δ (instantiate t b)) : ExtDerivation Const Δ (exF b) := by
  refine allF_intro (impF_intro ?_)
  have hInst := allF_elim (weaken (σ := propTy) t) (.hyp List.mem_cons_self :
    ExtDerivation Const (allF (σ := σ) (impF (rename (Rename.lift (Rename.weaken (σ := propTy))) b)
      (.var (.vs .vz))) :: weakenHyps (σ := propTy) Δ) _)
  rw [instantiate, subst_impF] at hInst
  change ExtDerivation Const _ (impF (instantiate (weaken (σ := propTy) t)
    (rename (Rename.lift (Rename.weaken (σ := propTy))) b)) (.var .vz)) at hInst
  rw [instantiate_weaken_rename_lift_weaken] at hInst
  refine impF_elim hInst ?_
  refine ExtDerivation.mono (fun hχ => List.mem_cons_of_mem _ hχ) ?_
  exact ExtDerivation.rename Rename.weaken h

theorem exF_elim {σ : Ty Base} {b : Formula Const (σ :: Γ)} {χ : Formula Const Γ}
    (h : ExtDerivation Const Δ (exF b))
    (hb : ExtDerivation Const (b :: weakenHyps (σ := σ) Δ) (weaken χ)) :
    ExtDerivation Const Δ χ := by
  have hInst := allF_elim χ h
  rw [instantiate, subst_impF, subst_allF, subst_impF,
    ImpredicativeConnectives.Modulo.subst_lift_single_rename_lift_weaken] at hInst
  change ExtDerivation Const Δ (impF (allF (impF b (weaken χ))) χ) at hInst
  exact impF_elim hInst (allF_intro (impF_intro hb))

/-! ## Primitive and defined constants are provably equal -/

theorem eq_congr {τ : Ty Base} {t t' s s' : Term Const Γ τ}
    (ht : ExtDerivation Const [] (.eq t t')) (hs : ExtDerivation Const [] (.eq s s')) :
    ExtDerivation Const Δ (.eq (.eq t s) (.eq t' s')) :=
  .eqPropI
    (.impI (.eqTrans (.eqTrans (.eqSymm (monoNil ht)) (.hyp List.mem_cons_self)) (monoNil hs)))
    (.impI (.eqTrans (.eqTrans (monoNil ht) (.hyp List.mem_cons_self)) (.eqSymm (monoNil hs))))

/-- From a provable equation between formulas, each implies the other under any
hypotheses. -/
theorem mp_of_eq {p p' : Formula Const Γ} (h : ExtDerivation Const [] (.eq p p'))
    (hp : ExtDerivation Const Δ p) : ExtDerivation Const Δ p' :=
  ExtDerivation.eqProp_mp_left (monoNil h) hp

theorem mpr_of_eq {p p' : Formula Const Γ} (h : ExtDerivation Const [] (.eq p p'))
    (hp : ExtDerivation Const Δ p') : ExtDerivation Const Δ p :=
  ExtDerivation.eqProp_mp_right (monoNil h) hp

/-- **Every term is provably equal to its expansion**, from no hypotheses and
without excluded middle. -/
theorem provable_eq_eqExpand : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ),
    ExtDerivation Const ([] : List (Formula Const Γ)) (.eq t (eqExpand t))
  | _, _, .var v => .eqRefl _
  | _, _, .const c => .eqRefl _
  | _, _, .app f a => ExtDerivation.eqAppCongr (provable_eq_eqExpand f) (provable_eq_eqExpand a)
  | _, _, .lam b => .eqLam (provable_eq_eqExpand b)
  | _, _, .top => .eqPropI (.impI trueF_intro) (.impI .topI)
  | _, _, .bot => .eqPropI (.impI (.botE (.hyp List.mem_cons_self)))
      (.impI (falseF_elim (.hyp List.mem_cons_self)))
  | _, _, .and p q => by
      have ihp := provable_eq_eqExpand p
      have ihq := provable_eq_eqExpand q
      exact .eqPropI
        (.impI (andF_intro (mp_of_eq ihp (.andEL (.hyp List.mem_cons_self)))
          (mp_of_eq ihq (.andER (.hyp List.mem_cons_self)))))
        (.impI (.andI (mpr_of_eq ihp (andF_left (.hyp List.mem_cons_self)))
          (mpr_of_eq ihq (andF_right (.hyp List.mem_cons_self)))))
  | _, _, .or p q => by
      have ihp := provable_eq_eqExpand p
      have ihq := provable_eq_eqExpand q
      exact .eqPropI
        (.impI (.orE (.hyp List.mem_cons_self)
          (orF_inl (mp_of_eq ihp (.hyp List.mem_cons_self)))
          (orF_inr (mp_of_eq ihq (.hyp List.mem_cons_self)))))
        (.impI (orF_elim (.hyp List.mem_cons_self)
          (.orIL (mpr_of_eq ihp (.hyp List.mem_cons_self)))
          (.orIR (mpr_of_eq ihq (.hyp List.mem_cons_self)))))
  | _, _, .imp p q => by
      have ihp := provable_eq_eqExpand p
      have ihq := provable_eq_eqExpand q
      exact .eqPropI
        (.impI (impF_intro (mp_of_eq ihq (.impE (.hyp (List.mem_cons_of_mem _ List.mem_cons_self))
          (mpr_of_eq ihp (.hyp List.mem_cons_self))))))
        (.impI (.impI (mpr_of_eq ihq (impF_elim (.hyp (List.mem_cons_of_mem _ List.mem_cons_self))
          (mp_of_eq ihp (.hyp List.mem_cons_self))))))
  | _, _, .not p => by
      have ihp := provable_eq_eqExpand p
      exact .eqPropI
        (.impI (impF_intro (.botE (.notE (.hyp (List.mem_cons_of_mem _ List.mem_cons_self))
          (mpr_of_eq ihp (.hyp List.mem_cons_self))))))
        (.impI (.notI (falseF_elim (impF_elim (.hyp (List.mem_cons_of_mem _ List.mem_cons_self))
          (mp_of_eq ihp (.hyp List.mem_cons_self))))))
  | _, _, .eq t s => eq_congr (provable_eq_eqExpand t) (provable_eq_eqExpand s)
  | Γ, _, .all (σ := σ) b => by
      have ihb := provable_eq_eqExpand b
      refine .eqPropI (.impI (allF_intro ?_)) (.impI (.allI ?_))
      · have hAll : ExtDerivation Const (weakenHyps (σ := σ) ([Term.all b] : List (Formula Const Γ)))
            (.all (rename (Rename.lift Rename.weaken) b)) := .hyp List.mem_cons_self
        have hb := ExtDerivation.allE (.var .vz) hAll
        rw [instantiate_vz_rename_lift_weaken] at hb
        exact mp_of_eq ihb hb
      · have hAll : ExtDerivation Const
            (weakenHyps (σ := σ) ([allF (eqExpand b)] : List (Formula Const Γ)))
            (allF (rename (Rename.lift Rename.weaken) (eqExpand b))) := .hyp List.mem_cons_self
        have hb := allF_elim (.var .vz) hAll
        rw [instantiate_vz_rename_lift_weaken] at hb
        exact mpr_of_eq ihb hb
  | Γ, _, .ex (σ := σ) b => by
      have ihb := provable_eq_eqExpand b
      refine .eqPropI (.impI ?_) (.impI ?_)
      · refine .exE (.hyp List.mem_cons_self) ?_
        change ExtDerivation Const _ (rename Rename.weaken (exF (eqExpand b)))
        rw [rename_exF]
        refine exF_intro (.var .vz) ?_
        rw [instantiate_vz_rename_lift_weaken]
        exact mp_of_eq ihb (.hyp List.mem_cons_self)
      · refine exF_elim (.hyp List.mem_cons_self) ?_
        change ExtDerivation Const _ (.ex (rename (Rename.lift Rename.weaken) b))
        refine .exI (.var .vz) ?_
        rw [instantiate_vz_rename_lift_weaken]
        exact mpr_of_eq ihb (.hyp List.mem_cons_self)

/-- A formula is derivable exactly when its expansion is. -/
theorem extDerivation_iff_eqExpand {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    ExtDerivation Const Δ φ ↔ ExtDerivation Const Δ (eqExpand φ) :=
  ⟨mp_of_eq (provable_eq_eqExpand φ), mpr_of_eq (provable_eq_eqExpand φ)⟩

/-- Cut against a list of derivable hypotheses. -/
theorem cut_list {Δ' : List (Formula Const Γ)} :
    ∀ {Δ : List (Formula Const Γ)} {φ : Formula Const Γ},
      (∀ δ ∈ Δ, ExtDerivation Const Δ' δ) → ExtDerivation Const Δ φ → ExtDerivation Const Δ' φ
  | [], _, _, d => ExtDerivation.mono (fun hχ => absurd hχ List.not_mem_nil) d
  | δ :: _, _, hΔ, d =>
      .impE (cut_list (fun δ' hδ' => hΔ δ' (List.mem_cons_of_mem _ hδ')) (.impI d))
        (hΔ δ List.mem_cons_self)

/-- **A sequent is derivable exactly when its expansion is.** -/
theorem extDerivation_iff_eqExpand_sequent {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    ExtDerivation Const Δ φ ↔ ExtDerivation Const (Δ.map eqExpand) (eqExpand φ) := by
  constructor
  · intro d
    refine cut_list (Δ := Δ) (fun δ hδ => mpr_of_eq (provable_eq_eqExpand δ)
      (.hyp (List.mem_map_of_mem hδ))) (extDerivation_iff_eqExpand.mp d)
  · intro d
    refine cut_list (Δ := Δ.map eqExpand) (fun δ hδ => ?_) (extDerivation_iff_eqExpand.mpr d)
    obtain ⟨δ', hδ', rfl⟩ := List.mem_map.mp hδ
    exact mp_of_eq (provable_eq_eqExpand δ') (.hyp hδ')

end Derivations

/-! ## The HOL Light definitions in every Henkin model -/

section HOLLight

open HOLLightBooleanDefinitions

variable (M : HenkinModel.{u, v, w} Base Const)

private theorem liftedTruth {Γ' : Ctx Base} (ρ : M.Valuation Γ') :
    M.denote (weakenCtx Γ' (truth : ClosedTerm Const .prop)) ρ = ULift.up True :=
  (M.denote_weakenCtx Γ' truth ρ).trans (denote_truth M _)

/-- HOL Light's conjunction denotes conjunction in every Henkin model, not only
in full-domain ones (`HOLLightBooleanDefinitions.denote_conjunction`). -/
theorem denote_conjunction_general (ρ : M.Valuation []) (p q : Ty.denote M.Carrier .prop) :
    M.denote (conjunction : ClosedTerm Const _) ρ p q = .up (p.down ∧ q.down) := by
  apply ULift.ext
  apply propext
  simp only [conjunction, HenkinModel.denote, PreModel.denote, liftedTruth,
    PreModel.Eqv, PreModel.extend]
  exact conj_iff M p q

theorem denote_conj_general {Γ' : Ctx Base} (p q : Formula Const Γ') (ρ : M.Valuation Γ') :
    M.denote (conj p q) ρ = .up ((M.denote p ρ).down ∧ (M.denote q ρ).down) := by
  change M.denote (applyClosed conjunction p) ρ (M.denote q ρ) = _
  rw [denote_applyClosed]
  exact denote_conjunction_general M _ _ _

theorem denote_implication_general (ρ : M.Valuation []) (p q : Ty.denote M.Carrier .prop) :
    M.denote (implication : ClosedTerm Const _) ρ p q = .up (p.down → q.down) := by
  change ULift.up ((M.denote (conj (.var (.vs .vz)) (.var .vz))
    (M.extend (M.extend ρ p) q)).down ↔ p.down) = _
  rw [denote_conj_general]
  apply ULift.ext
  apply propext
  exact ⟨fun equal premise => (equal.mpr premise).2,
    fun implication => ⟨And.left, fun premise => ⟨premise, implication premise⟩⟩⟩

theorem denote_imp_general {Γ' : Ctx Base} (p q : Formula Const Γ') (ρ : M.Valuation Γ') :
    M.denote (HOLLightBooleanDefinitions.imp p q) ρ =
      .up ((M.denote p ρ).down → (M.denote q ρ).down) := by
  change M.denote (applyClosed implication p) ρ (M.denote q ρ) = _
  rw [denote_applyClosed]
  exact denote_implication_general M _ _ _

theorem denote_existential_general {σ : Ty Base} (ρ : M.Valuation [])
    (predicate : Ty.denote M.Carrier (σ ⇒ .prop)) :
    M.denote (existential σ : ClosedTerm Const _) ρ predicate =
      .up (∃ x, M.adm σ x ∧ (predicate x).down) := by
  have encoding := ImpredicativeConnectives.denote_existential M ρ σ predicate
  rw [← encoding]
  simp only [existential, HenkinModel.denote, PreModel.denote,
    HOLLightBooleanDefinitions.denote_all, denote_imp_general,
    ImpredicativeConnectives.existential, PreModel.extend]
  rfl

theorem denote_negation_general (ρ : M.Valuation []) (p : Ty.denote M.Carrier .prop) :
    M.denote (negation : ClosedTerm Const _) ρ p = .up (¬ p.down) := by
  change M.denote (HOLLightBooleanDefinitions.imp (.var .vz) (weakenCtx _ falsity))
    (M.extend ρ p) = _
  rw [denote_imp_general, M.denote_weakenCtx, HOLLightBooleanDefinitions.denote_falsity]
  rfl

end HOLLight

/-! ## Negative example: equality cannot be dropped -/

section Lambda

/-- The pure λ-fragment: variables, application and abstraction. -/
def IsLamCore : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Prop
  | _, _, .var _ => True
  | _, _, .app f a => IsLamCore f ∧ IsLamCore a
  | _, _, .lam b => IsLamCore b
  | _, _, _ => False

/-- A value at every type over one-point base carriers. -/
def pointValue : (τ : Ty Base) → Ty.denote.{u, 0} (fun _ => PUnit.{u + 2}) τ
  | .prop => .up True
  | .base _ => PUnit.unit
  | .arr _ τ => fun _ => pointValue τ

/-- The one-point standard model; its constants are never consulted below. -/
def pointModel : HenkinModel.{u, v, 0} Base Const :=
  HenkinModel.standard (fun _ => PUnit.{u + 2}) (fun {τ} _ => pointValue τ)

/-- The logical predicate that is empty at `prop`. -/
def Inhabits : (τ : Ty Base) → Ty.denote.{u, 0} (fun _ => PUnit.{u + 2}) τ → Prop
  | .prop, _ => False
  | .base _, _ => True
  | .arr σ τ, f => ∀ x, Inhabits σ x → Inhabits τ (f x)

theorem inhabits_denote {τ : Ty Base} (t : Term Const Γ τ) (h : IsLamCore t)
    (ρ : (pointModel (Const := Const)).Valuation Γ)
    (hρ : ∀ {σ : Ty Base} (v : Var Γ σ), Inhabits σ (ρ v)) :
    Inhabits τ ((pointModel (Const := Const)).denote t ρ) := by
  induction t with
  | var v => exact hρ v
  | app f a ihf iha => exact ihf h.1 ρ hρ _ (iha h.2 ρ hρ)
  | lam b ih =>
      intro x hx
      refine ih h (pointModel.extend ρ x) ?_
      intro σ v
      cases v with
      | vz => exact hx
      | vs v => exact hρ v
  | const | top | bot | and | or | imp | not | eq | all | ex => exact h.elim

/-- **No sentence without equality.** Every closed term of type `prop` uses a
constant, equality or a logical constructor: the pure λ-fragment has no
sentences, so equality is the one logical primitive the uniform syntax needs. -/
theorem no_lambda_sentence (t : ClosedFormula Const) : ¬ IsLamCore t := fun h =>
  inhabits_denote t h (fun v => nomatch v) (fun v => nomatch v)

/-- With equality there are sentences: `T` is in the equality fragment. -/
theorem trueF_sentence : IsEqCore (trueF : ClosedFormula Const) := isEqCore_trueF

end Lambda

#print axioms eqExpand_isEqCore
#print axioms denote_eqExpand
#print axioms provable_eq_eqExpand
#print axioms extDerivation_iff_eqExpand_sequent
#print axioms denote_conjunction_general
#print axioms denote_existential_general
#print axioms denote_negation_general
#print axioms no_lambda_sentence

end UniformSyntax

end Mettapedia.Logic.HOL.SevenVirtues
