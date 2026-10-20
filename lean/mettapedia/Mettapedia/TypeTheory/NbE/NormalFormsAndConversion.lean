import Mettapedia.TypeTheory.NbE.EnvironmentMachine
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerDecidability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerConservativity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TwoSortConservativity

/-!
# Normal Forms, Type-Directed Conversion, and Decidability (`NormalFormsAndConversion.lean`)

This module completes **Deliverable 1** of the NbE conversion pipeline on top of
the closure-based environment machine in `EnvironmentMachine.lean`:

1. **Normal-Form Comparison Up to `R.headEq` (`TmHeadEquiv`, `NfEquiv`, `nbeConvNf`)**:
   - `TmHeadEquiv` and `NfEquiv` compare stratified normal forms structurally,
     allowing heads `h₁, h₂` to match whenever `h₁ = h₂ ∨ R.headEq h₁ h₂`.
   - Because `StepCore.head` is a step of `StepCore R.computation R.headEq`,
     `NfEquiv R.headEq nf₁ nf₂` implies `Reduces R nf₁.toTm nf₂.toTm`
     (`NfEquiv.reduces`).
   - Consequently, when `nbeConvNf` accepts `(t, u)`, both `t` and `u` reduce to
     the common normal-form reduct `nf₂.toTm` (`nbeConvNf_common_reduct`) and are
     declaratively convertible (`nbeConvNf_sound : nbeConvNf ... = true → Conv ...`).
   - When `headEq` is syntactic equality `Eq` (as in `Legacy.rules`),
     `NfEquiv Eq nf₁ nf₂ ↔ nf₁ = nf₂` (`NfEquiv.eq_iff`).

2. **Type-Directed NbE Conversion with Π-η and Σ-η (`nbeCompare`, `nbeCompareTypes`)**:
   - Instantiates `ExecutableConversion` (`compare`, `types`, `accepts`, `acceptsTypes`)
     with our closure-based NbE weak-head reducer `nbeWhnfReducer R root` and full
     NbE reducer `nbeReducer R root`.
   - Exposes the explicit Π-η (`etaExpandPiTm`) and Σ-η (`etaExpandSigmaTm`)
     expansions used at function and pair types.
   - Proves soundness of executable NbE conversion for the algorithmic conversion
     relation `Algorithm R` (`nbeAcceptsConv_derivation`, `nbeAcceptsTypeConv_derivation`).

3. **Normal-Form Existence, Conversion Soundness & Completeness, and Decidability**:
   - `tower_typed_whnf_exists` and `tower_isType_whnf_exists`: every well-typed term
     and well-formed type in a formed `Tower` context has a weak-head normal form.
   - `tower_algorithmic_complete` and `tower_algorithm_iff_equal`: on well-typed terms
     of a formed `Tower` context, `Algorithm (LevelTower.rules L) (.compare Γ t u A) ↔
     Equal (LevelTower.rules L) Γ t u A`.
   - `tower_nbeAcceptsConv_sound`: acceptance by the closure-based NbE conversion
     procedure implies declarative `Equal (LevelTower.rules L) Γ t u A`.
   - `tower_conv_implies_equal_and_algorithm`: untyped declarative conversion `Conv`
     between well-typed `Tower` terms implies both `Equal` and `Algorithm`.
   - `tower_equal_decidable` and `tower_typeEq_decidable`: `Decidable` instances
     (and excluded-middle decision theorems) for `Equal` and `TypeEq` in `Tower`.

4. **Proof-Theoretic Strength Analysis**:
   - Documents the exact proof-theoretic boundary between the one-universe `Legacy`
     fragment ($\Pi, \Sigma, \mathrm{Id}, U_0 : U_1$, reducible to a single universe level)
     and the cumulative universe tower `LevelTower L` ($U_0 : U_1 : U_2 : \dots$,
     requiring well-founded induction along `LevelOrder L` to construct the nested
     Kripke logical relation `LR`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NbE

open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Normalization

/-! ## 1. Structural Comparison Up to `headEq` (`TmHeadEquiv`, `NfEquiv`, `nbeConvNf`) -/

section NfComparison

variable {Head : Type}

/-- Structural equality of scoped terms up to `headEq` at `.head` leaves. -/
def TmHeadEquiv (headEq : Head → Head → Prop) :
    {n : Nat} → Tm Head n → Tm Head n → Prop
  | _, .var i, .var j => i = j
  | _, .const c, .const d => c = d
  | _, .head h₁, .head h₂ => h₁ = h₂ ∨ headEq h₁ h₂
  | _, .pi A₁ B₁, .pi A₂ B₂ =>
      TmHeadEquiv headEq A₁ A₂ ∧ TmHeadEquiv headEq B₁ B₂
  | _, .sigma A₁ B₁, .sigma A₂ B₂ =>
      TmHeadEquiv headEq A₁ A₂ ∧ TmHeadEquiv headEq B₁ B₂
  | _, .id A₁ a₁ b₁, .id A₂ a₂ b₂ =>
      TmHeadEquiv headEq A₁ A₂ ∧ TmHeadEquiv headEq a₁ a₂ ∧ TmHeadEquiv headEq b₁ b₂
  | _, .lam b₁, .lam b₂ =>
      TmHeadEquiv headEq b₁ b₂
  | _, .app f₁ a₁, .app f₂ a₂ =>
      TmHeadEquiv headEq f₁ f₂ ∧ TmHeadEquiv headEq a₁ a₂
  | _, .pair a₁ b₁, .pair a₂ b₂ =>
      TmHeadEquiv headEq a₁ a₂ ∧ TmHeadEquiv headEq b₁ b₂
  | _, .fst p₁, .fst p₂ =>
      TmHeadEquiv headEq p₁ p₂
  | _, .snd p₁, .snd p₂ =>
      TmHeadEquiv headEq p₁ p₂
  | _, .refl a₁, .refl a₂ =>
      TmHeadEquiv headEq a₁ a₂
  | _, _, _ => False

namespace TmHeadEquiv

/-- `TmHeadEquiv` is reflexive for any `headEq`. -/
theorem refl (headEq : Head → Head → Prop) :
    ∀ {n : Nat} (t : Tm Head n), TmHeadEquiv headEq t t
  | _, .var _ => rfl
  | _, .const _ => rfl
  | _, .head _ => .inl rfl
  | _, .pi A B => ⟨refl headEq A, refl headEq B⟩
  | _, .sigma A B => ⟨refl headEq A, refl headEq B⟩
  | _, .id A a b => ⟨refl headEq A, refl headEq a, refl headEq b⟩
  | _, .lam b => refl headEq b
  | _, .app f a => ⟨refl headEq f, refl headEq a⟩
  | _, .pair a b => ⟨refl headEq a, refl headEq b⟩
  | _, .fst p => refl headEq p
  | _, .snd p => refl headEq p
  | _, .refl a => refl headEq a

/-- When `headEq` is syntactic equality `Eq`, `TmHeadEquiv Eq t u` is equivalent to `t = u`. -/
theorem eq_iff {n : Nat} {t u : Tm Head n} :
    TmHeadEquiv Eq t u ↔ t = u := by
  induction t with
  | var i => cases u <;> simp [TmHeadEquiv]
  | const c => cases u <;> simp [TmHeadEquiv]
  | head h₁ => cases u <;> simp [TmHeadEquiv]
  | pi A₁ B₁ ihA ihB =>
      cases u <;> simp [TmHeadEquiv, ihA, ihB]
  | sigma A₁ B₁ ihA ihB =>
      cases u <;> simp [TmHeadEquiv, ihA, ihB]
  | id A₁ a₁ b₁ ihA iha ihb =>
      cases u <;> simp [TmHeadEquiv, ihA, iha, ihb]
  | lam b₁ ih =>
      cases u <;> simp [TmHeadEquiv, ih]
  | app f₁ a₁ ihf iha =>
      cases u <;> simp [TmHeadEquiv, ihf, iha]
  | pair a₁ b₁ iha ihb =>
      cases u <;> simp [TmHeadEquiv, iha, ihb]
  | fst p₁ ih =>
      cases u <;> simp [TmHeadEquiv, ih]
  | snd p₁ ih =>
      cases u <;> simp [TmHeadEquiv, ih]
  | refl a₁ ih =>
      cases u <;> simp [TmHeadEquiv, ih]

/-- Because `StepCore.head` is a reduction step of `StepCore R.computation R.headEq`,
`TmHeadEquiv R.headEq t u` implies `Reduces R t u`. -/
theorem reduces (R : Rules Head) {n : Nat} {t u : Tm Head n}
    (h : TmHeadEquiv R.headEq t u) : Reduces R t u := by
  induction t with
  | var i =>
      cases u <;> try exact False.elim h
      cases h; exact .refl
  | const c =>
      cases u <;> try exact False.elim h
      cases h; exact .refl
  | head h₁ =>
      cases u <;> try exact False.elim h
      rcases h with rfl | hStep
      · exact .refl
      · exact .single (.head hStep)
  | pi A₁ B₁ ihA ihB =>
      cases u <;> try exact False.elim h
      exact reduces_pi R (ihA h.1) (ihB h.2)
  | sigma A₁ B₁ ihA ihB =>
      cases u <;> try exact False.elim h
      exact reduces_sigma R (ihA h.1) (ihB h.2)
  | id A₁ a₁ b₁ ihA iha ihb =>
      cases u <;> try exact False.elim h
      exact reduces_id R (ihA h.1) (iha h.2.1) (ihb h.2.2)
  | lam b₁ ih =>
      cases u <;> try exact False.elim h
      exact reduces_lam R (ih h)
  | app f₁ a₁ ihf iha =>
      cases u <;> try exact False.elim h
      exact reduces_app R (ihf h.1) (iha h.2)
  | pair a₁ b₁ iha ihb =>
      cases u <;> try exact False.elim h
      exact reduces_pair R (iha h.1) (ihb h.2)
  | fst p₁ ih =>
      cases u <;> try exact False.elim h
      exact reduces_fst R (ih h)
  | snd p₁ ih =>
      cases u <;> try exact False.elim h
      exact reduces_snd R (ih h)
  | refl a₁ ih =>
      cases u <;> try exact False.elim h
      exact reduces_refl R (ih h)

/-- Consequently, `TmHeadEquiv R.headEq t u` implies declarative conversion
`Conv R.headEq t u R.computation`. -/
theorem to_conv (R : Rules Head) {n : Nat} {t u : Tm Head n}
    (h : TmHeadEquiv R.headEq t u) : Conv R.headEq t u R.computation :=
  reduces_to_conv R (reduces R h)

end TmHeadEquiv

/-- Executable Boolean decision procedure for `TmHeadEquiv`. -/
def decideTmHeadEquiv (headEqB : Head → Head → Bool) :
    {n : Nat} → Tm Head n → Tm Head n → Bool
  | _, .var i, .var j => decide (i = j)
  | _, .const c, .const d => decide (c = d)
  | _, .head h₁, .head h₂ => headEqB h₁ h₂
  | _, .pi A₁ B₁, .pi A₂ B₂ =>
      decideTmHeadEquiv headEqB A₁ A₂ && decideTmHeadEquiv headEqB B₁ B₂
  | _, .sigma A₁ B₁, .sigma A₂ B₂ =>
      decideTmHeadEquiv headEqB A₁ A₂ && decideTmHeadEquiv headEqB B₁ B₂
  | _, .id A₁ a₁ b₁, .id A₂ a₂ b₂ =>
      decideTmHeadEquiv headEqB A₁ A₂ &&
        decideTmHeadEquiv headEqB a₁ a₂ &&
        decideTmHeadEquiv headEqB b₁ b₂
  | _, .lam b₁, .lam b₂ =>
      decideTmHeadEquiv headEqB b₁ b₂
  | _, .app f₁ a₁, .app f₂ a₂ =>
      decideTmHeadEquiv headEqB f₁ f₂ && decideTmHeadEquiv headEqB a₁ a₂
  | _, .pair a₁ b₁, .pair a₂ b₂ =>
      decideTmHeadEquiv headEqB a₁ a₂ && decideTmHeadEquiv headEqB b₁ b₂
  | _, .fst p₁, .fst p₂ =>
      decideTmHeadEquiv headEqB p₁ p₂
  | _, .snd p₁, .snd p₂ =>
      decideTmHeadEquiv headEqB p₁ p₂
  | _, .refl a₁, .refl a₂ =>
      decideTmHeadEquiv headEqB a₁ a₂
  | _, _, _ => false

/-- Soundness of `decideTmHeadEquiv` for `TmHeadEquiv`. -/
theorem decideTmHeadEquiv_sound {headEq : Head → Head → Prop}
    {headEqB : Head → Head → Bool}
    (hHead : ∀ h₁ h₂, headEqB h₁ h₂ = true → h₁ = h₂ ∨ headEq h₁ h₂)
    {n : Nat} {t u : Tm Head n}
    (h : decideTmHeadEquiv headEqB t u = true) :
    TmHeadEquiv headEq t u := by
  induction t with
  | var i =>
      cases u <;> simp [decideTmHeadEquiv, TmHeadEquiv] at h ⊢
      exact h
  | const c =>
      cases u <;> simp [decideTmHeadEquiv, TmHeadEquiv] at h ⊢
      exact h
  | head h₁ =>
      cases u <;> simp [decideTmHeadEquiv, TmHeadEquiv] at h ⊢
      exact hHead _ _ h
  | pi A₁ B₁ ihA ihB =>
      cases u <;> simp [decideTmHeadEquiv, TmHeadEquiv] at h ⊢
      exact ⟨ihA h.1, ihB h.2⟩
  | sigma A₁ B₁ ihA ihB =>
      cases u <;> simp [decideTmHeadEquiv, TmHeadEquiv] at h ⊢
      exact ⟨ihA h.1, ihB h.2⟩
  | id A₁ a₁ b₁ ihA iha ihb =>
      cases u <;> simp [decideTmHeadEquiv, TmHeadEquiv] at h ⊢
      exact ⟨ihA h.1.1, iha h.1.2, ihb h.2⟩
  | lam b₁ ih =>
      cases u <;> simp [decideTmHeadEquiv, TmHeadEquiv] at h ⊢
      exact ih h
  | app f₁ a₁ ihf iha =>
      cases u <;> simp [decideTmHeadEquiv, TmHeadEquiv] at h ⊢
      exact ⟨ihf h.1, iha h.2⟩
  | pair a₁ b₁ iha ihb =>
      cases u <;> simp [decideTmHeadEquiv, TmHeadEquiv] at h ⊢
      exact ⟨iha h.1, ihb h.2⟩
  | fst p₁ ih =>
      cases u <;> simp [decideTmHeadEquiv, TmHeadEquiv] at h ⊢
      exact ih h
  | snd p₁ ih =>
      cases u <;> simp [decideTmHeadEquiv, TmHeadEquiv] at h ⊢
      exact ih h
  | refl a₁ ih =>
      cases u <;> simp [decideTmHeadEquiv, TmHeadEquiv] at h ⊢
      exact ih h

/-- Equivalence of stratified normal forms `Nf Head n` up to `headEq`. -/
def NfEquiv (headEq : Head → Head → Prop) {n : Nat} (nf₁ nf₂ : Nf Head n) : Prop :=
  TmHeadEquiv headEq nf₁.toTm nf₂.toTm

namespace NfEquiv

/-- When `headEq` is `Eq`, `NfEquiv Eq nf₁ nf₂` is equivalent to `nf₁ = nf₂`. -/
theorem eq_iff {n : Nat} {nf₁ nf₂ : Nf Head n} :
    NfEquiv Eq nf₁ nf₂ ↔ nf₁ = nf₂ := by
  unfold NfEquiv
  rw [TmHeadEquiv.eq_iff]
  exact ⟨Nf.toTm_injective, congrArg Nf.toTm⟩

/-- `NfEquiv R.headEq nf₁ nf₂` implies `Reduces R nf₁.toTm nf₂.toTm`. -/
theorem reduces (R : Rules Head) {n : Nat} {nf₁ nf₂ : Nf Head n}
    (h : NfEquiv R.headEq nf₁ nf₂) : Reduces R nf₁.toTm nf₂.toTm :=
  TmHeadEquiv.reduces R h

end NfEquiv

/-- Executable Boolean comparison of stratified normal forms `Nf Head n` up to `headEqB`. -/
def decideNfEquiv (headEqB : Head → Head → Bool) {n : Nat}
    (nf₁ nf₂ : Nf Head n) : Bool :=
  decideTmHeadEquiv headEqB nf₁.toTm nf₂.toTm

/-- Soundness of `decideNfEquiv` for `NfEquiv`. -/
theorem decideNfEquiv_sound {headEq : Head → Head → Prop}
    {headEqB : Head → Head → Bool}
    (hHead : ∀ h₁ h₂, headEqB h₁ h₂ = true → h₁ = h₂ ∨ headEq h₁ h₂)
    {n : Nat} {nf₁ nf₂ : Nf Head n}
    (h : decideNfEquiv headEqB nf₁ nf₂ = true) :
    NfEquiv headEq nf₁ nf₂ :=
  decideTmHeadEquiv_sound hHead h

/-- **Untyped NbE Normal-Form Conversion (`nbeConvNf`)**:
Normalizes both `t` and `u` using the closure-based NbE machine (`nbeNormNf`)
and compares the resulting stratified normal forms via `decideNfEquiv`. -/
def nbeConvNf (R : Rules Head) (root : ExecutableReduction.RootEvaluator R)
    (headEqB : Head → Head → Bool) (fuel : Nat) {n : Nat}
    (t u : Tm Head n) : Bool :=
  match nbeNormNf R root fuel t, nbeNormNf R root fuel u with
  | some nf₁, some nf₂ => decideNfEquiv headEqB nf₁ nf₂
  | _, _ => false

/-- **Common-Reduct Theorem for `nbeConvNf`**:
Whenever `nbeConvNf` returns `true`, there exists a stratified normal form `nf₂`
such that both `t` and `u` reduce to `nf₂.toTm` in `Reduces R`. -/
theorem nbeConvNf_common_reduct (R : Rules Head)
    (root : ExecutableReduction.RootEvaluator R)
    {headEqB : Head → Head → Bool}
    (hHead : ∀ h₁ h₂, headEqB h₁ h₂ = true → h₁ = h₂ ∨ R.headEq h₁ h₂)
    {fuel n : Nat} {t u : Tm Head n}
    (hConv : nbeConvNf R root headEqB fuel t u = true) :
    ∃ nf : Nf Head n, Reduces R t nf.toTm ∧ Reduces R u nf.toTm := by
  unfold nbeConvNf at hConv
  cases h₁ : nbeNormNf R root fuel t with
  | none => simp [h₁] at hConv
  | some nf₁ =>
      cases h₂ : nbeNormNf R root fuel u with
      | none => simp [h₁, h₂] at hConv
      | some nf₂ =>
          simp only [h₁, h₂] at hConv
          have hEquiv : NfEquiv R.headEq nf₁ nf₂ := decideNfEquiv_sound hHead hConv
          have hRedT : Reduces R t nf₁.toTm := (nbeNormNf_sound R root h₁).1
          have hRedU : Reduces R u nf₂.toTm := (nbeNormNf_sound R root h₂).1
          exact ⟨nf₂, hRedT.trans (NfEquiv.reduces R hEquiv), hRedU⟩

/-- **Soundness of `nbeConvNf` for Declarative Conversion (`Conv`)**:
Whenever `nbeConvNf` returns `true`, `t` and `u` are declaratively convertible
in `Conv R.headEq t u R.computation`. -/
theorem nbeConvNf_sound (R : Rules Head)
    (root : ExecutableReduction.RootEvaluator R)
    {headEqB : Head → Head → Bool}
    (hHead : ∀ h₁ h₂, headEqB h₁ h₂ = true → h₁ = h₂ ∨ R.headEq h₁ h₂)
    {fuel n : Nat} {t u : Tm Head n}
    (hConv : nbeConvNf R root headEqB fuel t u = true) :
    Conv R.headEq t u R.computation := by
  obtain ⟨nf, hRedT, hRedU⟩ := nbeConvNf_common_reduct R root hHead hConv
  exact Relation.EqvGen.trans _ _ _
    (reduces_to_conv R hRedT)
    (Relation.EqvGen.symm _ _ (reduces_to_conv R hRedU))

end NfComparison

/-! ## 2. Type-Directed NbE Conversion with Π-η and Σ-η (`nbeCompare`, `nbeCompareTypes`) -/

section TypeDirectedNbE

variable {Head : Type} (R : Rules Head) [DecidableEq Head]
variable [DecidableRel R.headEq] [∀ head, Decidable (R.isUniverse head)]
variable (root : ExecutableReduction.RootEvaluator R)

/-- One-step Π-η expansion of a term `f : Tm Head n` into `λ x. (wk f) x`. -/
def etaExpandPiTm {n : Nat} (f : Tm Head n) : Tm Head n :=
  .lam (.app (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename wk f) (.var 0))

/-- One-step Σ-η expansion of a term `p : Tm Head n` into `(fst p, snd p)`. -/
def etaExpandSigmaTm {n : Nat} (p : Tm Head n) : Tm Head n :=
  .pair (.fst p) (.snd p)

/-- Type-directed conversion certificate search powered by the closure-based
weak-head NbE reducer `nbeWhnfReducer R root`.
- At `.pi A B`, compares `(wk left) (var 0)` and `(wk right) (var 0)` at `B` in `Γ, A` (Π-η).
- At `.sigma A B`, compares `fst left` with `fst right` at `A` and `snd left` with
  `snd right` at `B[fst left]` (Σ-η).
- At a universe `.head u`, compares `left` and `right` structurally as types.
- At `.id A x y`, compares `refl a` and `refl b` by comparing `a` and `b` at `A`. -/
def nbeCompare (fuel : Nat) {n : Nat} (Γ : Ctx Head n)
    (left right type : Tm Head n) :
    Option (ExecutableConversion.Certificate R (.compare Γ left right type)) :=
  ExecutableConversion.compare R (nbeWhnfReducer R root) fuel Γ left right type

/-- Type-directed type comparison certificate search powered by `nbeWhnfReducer R root`. -/
def nbeCompareTypes (fuel : Nat) {n : Nat} (Γ : Ctx Head n)
    (left right : Tm Head n) :
    Option (ExecutableConversion.Certificate R (.types Γ left right)) :=
  ExecutableConversion.types R (nbeWhnfReducer R root) fuel Γ left right

/-- Boolean type-directed NbE term conversion checker (`nbeAcceptsConv`). -/
def nbeAcceptsConv (fuel : Nat) {n : Nat} (Γ : Ctx Head n)
    (left right type : Tm Head n) : Bool :=
  ExecutableConversion.accepts R (nbeWhnfReducer R root) fuel Γ left right type

/-- Boolean type-directed NbE type conversion checker (`nbeAcceptsTypeConv`). -/
def nbeAcceptsTypeConv (fuel : Nat) {n : Nat} (Γ : Ctx Head n)
    (left right : Tm Head n) : Bool :=
  ExecutableConversion.acceptsTypes R (nbeWhnfReducer R root) fuel Γ left right

/-- **Soundness of `nbeAcceptsConv` for `Algorithm`**:
When `nbeAcceptsConv` returns `true`, it reconstructs a derivation of
`Algorithm R (.compare Γ left right type)`. -/
theorem nbeAcceptsConv_derivation {fuel n : Nat} {Γ : Ctx Head n}
    {left right type : Tm Head n}
    (h : nbeAcceptsConv R root fuel Γ left right type = true) :
    Algorithm R (.compare Γ left right type) :=
  ExecutableConversion.accepts_derivation R (nbeWhnfReducer R root) h

/-- **Soundness of `nbeAcceptsTypeConv` for `Algorithm`**:
When `nbeAcceptsTypeConv` returns `true`, it reconstructs a derivation of
`Algorithm R (.types Γ left right)`. -/
theorem nbeAcceptsTypeConv_derivation {fuel n : Nat} {Γ : Ctx Head n}
    {left right : Tm Head n}
    (h : nbeAcceptsTypeConv R root fuel Γ left right = true) :
    Algorithm R (.types Γ left right) :=
  ExecutableConversion.acceptsTypes_derivation R (nbeWhnfReducer R root) h

end TypeDirectedNbE

/-! ## 2b. Fuel Monotonicity and Simulation Completeness of `ExecutableConversion` and `nbeCompare` -/

section ExecutableConversionCompleteness

variable {Head : Type} (R : Rules Head) [DecidableEq Head]
variable [DecidableRel R.headEq] [∀ head, Decidable (R.isUniverse head)]

/-- A weak-head reducer is fuel-monotone if increasing the fuel preserves any
returned weak-head normal form `r.val`. -/
def ReducerMonotone (reducer : ExecutableReduction.Reducer R) : Prop :=
  ∀ {fuel fuel' n : Nat} {t : Tm Head n}
    {r : { normal : Tm Head n // Reduces R t normal }},
    fuel ≤ fuel' →
    reducer fuel t = some r →
    ∃ h', reducer fuel' t = some ⟨r.val, h'⟩

/-- A weak-head reducer is complete for `WhRed R roles` if every term `t` that
weak-head reduces to a `Whnf` `w` evaluates to `w` at some finite fuel. -/
def ReducerWhnfComplete (roles : Roles Head) (reducer : ExecutableReduction.Reducer R) : Prop :=
  ∀ {n : Nat} {t w : Tm Head n},
    WhRed R roles t w →
    Whnf R roles w →
    ∃ fuel hRed, reducer fuel t = some ⟨w, hRed⟩

omit [DecidableEq Head] [DecidableRel R.headEq] [∀ head, Decidable (R.isUniverse head)] in
/-- Our closure-based NbE weak-head reducer `nbeWhnfReducer R root` is fuel-monotone. -/
theorem nbeWhnfReducer_monotone (root : ExecutableReduction.RootEvaluator R) :
    ReducerMonotone R (nbeWhnfReducer R root) :=
  fun hle h => ⟨_, nbeWhnfReducer_mono R root hle h⟩

omit [DecidableEq Head] [DecidableRel R.headEq] [∀ head, Decidable (R.isUniverse head)] in
/-- When `R.computation = RootComputation.empty` and `roles = fun _ => .rigid`,
our closure-based NbE weak-head reducer `nbeWhnfReducer R (fun _ => none)` is complete
for `WhRed R roles`. -/
theorem nbeWhnfReducer_whnfComplete {roles : Roles Head}
    (hComp : R.computation = RootComputation.empty)
    (hRoles : roles = fun _ => .rigid) :
    ReducerWhnfComplete R roles (nbeWhnfReducer R (fun _ => none)) := by
  intro n t w hRed hWhnf
  obtain ⟨fuel, ⟨val, prop⟩, hEq, rfl⟩ := nbeWhnf_complete_of_whRed hComp hRoles hRed hWhnf
  exact ⟨fuel, prop, hEq⟩

theorem compare_step_mono {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer) {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    (ihCompare : ∀ {n : Nat} {Γ : Ctx Head n} {t u T : Tm Head n}
      {c : ExecutableConversion.Certificate R (.compare Γ t u T)},
      ExecutableConversion.compare R reducer fuel Γ t u T = some c →
      ∃ c', ExecutableConversion.compare R reducer fuel' Γ t u T = some c')
    (ihCompareNeutral : ∀ {n : Nat} {Γ : Ctx Head n} {t u T : Tm Head n}
      {c : ExecutableConversion.Certificate R (.compare Γ t u T)},
      ExecutableConversion.compareNeutral R reducer fuel Γ t u T = some c →
      ∃ c', ExecutableConversion.compareNeutral R reducer fuel' Γ t u T = some c')
    (ihTypes : ∀ {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
      {c : ExecutableConversion.Certificate R (.types Γ A B)},
      ExecutableConversion.types R reducer fuel Γ A B = some c →
      ∃ c', ExecutableConversion.types R reducer fuel' Γ A B = some c')
    {n : Nat} {Γ : Ctx Head n} {t u T : Tm Head n}
    {c : ExecutableConversion.Certificate R (.compare Γ t u T)}
    (h : ExecutableConversion.compare R reducer (fuel + 1) Γ t u T = some c) :
    ∃ c', ExecutableConversion.compare R reducer (fuel' + 1) Γ t u T = some c' := by
  have hle1 : fuel + 1 ≤ fuel' + 1 := Nat.succ_le_succ hle
  unfold ExecutableConversion.compare at h ⊢
  cases hNorm : reducer (fuel + 1) T with
  | none => simp [hNorm, Option.bind_eq_bind] at h
  | some normal =>
      obtain ⟨normProp', hNorm'⟩ := hMono hle1 hNorm
      rcases normal with ⟨normVal, normProp⟩
      dsimp only at hNorm'
      rw [hNorm] at h
      rw [hNorm']
      simp only [Option.bind_eq_bind, Option.bind] at h ⊢
      cases normVal with
      | pi dom body =>
          dsimp only at h ⊢
          cases hSub : ExecutableConversion.compare R reducer fuel (.snoc Γ dom)
              (.app (Presentation.rename wk t) (.var 0))
              (.app (Presentation.rename wk u) (.var 0)) body with
          | none => simp [hSub] at h
          | some cSub =>
              obtain ⟨cSub', hSub'⟩ := ihCompare hSub
              rw [hSub']
              exact ⟨_, rfl⟩
      | sigma dom body =>
          dsimp only at h ⊢
          cases hFst : ExecutableConversion.compare R reducer fuel Γ (.fst t) (.fst u) dom with
          | none => simp [hFst] at h
          | some cFst =>
              rw [hFst] at h
              dsimp only [Option.bind] at h
              cases hSnd : ExecutableConversion.compare R reducer fuel Γ (.snd t) (.snd u)
                  (inst0 (.fst t) body) with
              | none => simp [hSnd] at h
              | some cSnd =>
                  obtain ⟨cFst', hFst'⟩ := ihCompare hFst
                  obtain ⟨cSnd', hSnd'⟩ := ihCompare hSnd
                  rw [hFst', hSnd']
                  exact ⟨_, rfl⟩
      | head val =>
          dsimp only at h ⊢
          by_cases hU : R.isUniverse val
          · rw [dif_pos hU] at h ⊢
            cases hTy : ExecutableConversion.types R reducer fuel Γ t u with
            | none => simp [hTy] at h
            | some cTy =>
                obtain ⟨cTy', hTy'⟩ := ihTypes hTy
                rw [hTy']
                exact ⟨_, rfl⟩
          · rw [dif_neg hU] at h ⊢
            exact ihCompareNeutral h
      | id carrier a b =>
          dsimp only at h ⊢
          cases hL : reducer (fuel + 1) t with
          | none => simp [hL] at h
          | some leftNormal =>
              obtain ⟨lProp', hL'⟩ := hMono hle1 hL
              rcases leftNormal with ⟨lVal, lProp⟩
              dsimp only at hL'
              rw [hL] at h
              rw [hL']
              dsimp only [Option.bind] at h ⊢
              cases hR : reducer (fuel + 1) u with
              | none => simp [hR] at h
              | some rightNormal =>
                  obtain ⟨rProp', hR'⟩ := hMono hle1 hR
                  rcases rightNormal with ⟨rVal, rProp⟩
                  dsimp only at hR'
                  rw [hR] at h
                  rw [hR']
                  dsimp only [Option.bind] at h ⊢
                  cases lVal <;> try (dsimp only at h ⊢; exact ihCompareNeutral h)
                  case refl first =>
                    cases rVal <;> try (dsimp only at h ⊢; exact ihCompareNeutral h)
                    case refl second =>
                      dsimp only at h ⊢
                      cases hSub : ExecutableConversion.compare R reducer fuel Γ first second carrier with
                      | none => simp [hSub] at h
                      | some cSub =>
                          obtain ⟨cSub', hSub'⟩ := ihCompare hSub
                          rw [hSub']
                          exact ⟨_, rfl⟩
      | var _ | const _ | lam _ | app _ _ | pair _ _ | fst _ | snd _ | refl _ =>
          dsimp only at h ⊢
          exact ihCompareNeutral h

theorem compareNeutral_step_mono {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer) {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    (ihNeutral : ∀ {n : Nat} {Γ : Ctx Head n} {t u : Tm Head n}
      {res : ExecutableConversion.NeutralResult R Γ t u},
      ExecutableConversion.neutral R reducer fuel Γ t u = some res →
      ∃ c', ExecutableConversion.neutral R reducer fuel' Γ t u = some ⟨res.1, c'⟩)
    {n : Nat} {Γ : Ctx Head n} {t u T : Tm Head n}
    {c : ExecutableConversion.Certificate R (.compare Γ t u T)}
    (h : ExecutableConversion.compareNeutral R reducer (fuel + 1) Γ t u T = some c) :
    ∃ c', ExecutableConversion.compareNeutral R reducer (fuel' + 1) Γ t u T = some c' := by
  have hle1 : fuel + 1 ≤ fuel' + 1 := Nat.succ_le_succ hle
  unfold ExecutableConversion.compareNeutral at h ⊢
  cases hL : reducer (fuel + 1) t with
  | none => simp [hL, Option.bind_eq_bind] at h
  | some first =>
      obtain ⟨fProp', hL'⟩ := hMono hle1 hL
      rcases first with ⟨fVal, fProp⟩
      dsimp only at hL'
      rw [hL] at h
      rw [hL']
      simp only [Option.bind_eq_bind, Option.bind] at h ⊢
      cases hR : reducer (fuel + 1) u with
      | none => simp [hR] at h
      | some second =>
          obtain ⟨sProp', hR'⟩ := hMono hle1 hR
          rcases second with ⟨sVal, sProp⟩
          dsimp only at hR'
          rw [hR] at h
          rw [hR']
          dsimp only [Option.bind] at h ⊢
          cases hNe : ExecutableConversion.neutral R reducer fuel Γ fVal sVal with
          | none => simp [hNe] at h
          | some compared =>
              obtain ⟨cNe', hNe'⟩ := ihNeutral hNe
              rw [hNe']
              exact ⟨_, rfl⟩

theorem types_step_mono {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer) {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    (ihCompare : ∀ {n : Nat} {Γ : Ctx Head n} {t u T : Tm Head n}
      {c : ExecutableConversion.Certificate R (.compare Γ t u T)},
      ExecutableConversion.compare R reducer fuel Γ t u T = some c →
      ∃ c', ExecutableConversion.compare R reducer fuel' Γ t u T = some c')
    (ihTypes : ∀ {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
      {c : ExecutableConversion.Certificate R (.types Γ A B)},
      ExecutableConversion.types R reducer fuel Γ A B = some c →
      ∃ c', ExecutableConversion.types R reducer fuel' Γ A B = some c')
    (ihNeutral : ∀ {n : Nat} {Γ : Ctx Head n} {t u : Tm Head n}
      {res : ExecutableConversion.NeutralResult R Γ t u},
      ExecutableConversion.neutral R reducer fuel Γ t u = some res →
      ∃ c', ExecutableConversion.neutral R reducer fuel' Γ t u = some ⟨res.1, c'⟩)
    {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    {c : ExecutableConversion.Certificate R (.types Γ A B)}
    (h : ExecutableConversion.types R reducer (fuel + 1) Γ A B = some c) :
    ∃ c', ExecutableConversion.types R reducer (fuel' + 1) Γ A B = some c' := by
  have hle1 : fuel + 1 ≤ fuel' + 1 := Nat.succ_le_succ hle
  unfold ExecutableConversion.types at h ⊢
  cases hL : reducer (fuel + 1) A with
  | none => simp [hL, Option.bind_eq_bind] at h
  | some first =>
      obtain ⟨fProp', hL'⟩ := hMono hle1 hL
      rcases first with ⟨fVal, fProp⟩
      dsimp only at hL'
      rw [hL] at h
      rw [hL']
      simp only [Option.bind_eq_bind, Option.bind] at h ⊢
      cases hR : reducer (fuel + 1) B with
      | none => simp [hR] at h
      | some second =>
          obtain ⟨sProp', hR'⟩ := hMono hle1 hR
          rcases second with ⟨sVal, sProp⟩
          dsimp only at hR'
          rw [hR] at h
          rw [hR']
          dsimp only [Option.bind] at h ⊢
          have hFallback :
              (ExecutableConversion.neutral R reducer fuel Γ fVal sVal).bind
                (fun compared => some (PLift.up (Algorithm.neutralTypes fProp sProp compared.2.down))) = some c →
              ∃ c', (ExecutableConversion.neutral R reducer fuel' Γ fVal sVal).bind
                (fun compared => some (PLift.up (Algorithm.neutralTypes fProp' sProp' compared.2.down))) = some c' := by
            intro hF
            cases hNe : ExecutableConversion.neutral R reducer fuel Γ fVal sVal with
            | none => simp [hNe] at hF
            | some compared =>
                obtain ⟨cNe', hNe'⟩ := ihNeutral hNe
                rw [hNe']
                exact ⟨_, rfl⟩
          cases fVal <;> try (dsimp only at h ⊢; exact hFallback h)
          case head a =>
            cases sVal <;> try (dsimp only at h ⊢; exact hFallback h)
            case head b =>
              dsimp only at h ⊢
              by_cases hSame : a = b ∨ R.headEq a b
              · rw [dif_pos hSame]
                exact ⟨_, rfl⟩
              · rw [dif_neg hSame] at h
                cases h
          case pi dom body =>
            cases sVal <;> try (dsimp only at h ⊢; exact hFallback h)
            case pi dom' body' =>
              dsimp only at h ⊢
              cases hDom : ExecutableConversion.types R reducer fuel Γ dom dom' with
              | none => simp [hDom] at h
              | some cDom =>
                  rw [hDom] at h
                  dsimp only [Option.bind] at h
                  cases hBod : ExecutableConversion.types R reducer fuel (.snoc Γ dom) body body' with
                  | none => simp [hBod] at h
                  | some cBod =>
                      obtain ⟨cDom', hDom'⟩ := ihTypes hDom
                      obtain ⟨cBod', hBod'⟩ := ihTypes hBod
                      rw [hDom', hBod']
                      exact ⟨_, rfl⟩
          case sigma dom body =>
            cases sVal <;> try (dsimp only at h ⊢; exact hFallback h)
            case sigma dom' body' =>
              dsimp only at h ⊢
              cases hDom : ExecutableConversion.types R reducer fuel Γ dom dom' with
              | none => simp [hDom] at h
              | some cDom =>
                  rw [hDom] at h
                  dsimp only [Option.bind] at h
                  cases hBod : ExecutableConversion.types R reducer fuel (.snoc Γ dom) body body' with
                  | none => simp [hBod] at h
                  | some cBod =>
                      obtain ⟨cDom', hDom'⟩ := ihTypes hDom
                      obtain ⟨cBod', hBod'⟩ := ihTypes hBod
                      rw [hDom', hBod']
                      exact ⟨_, rfl⟩
          case id carrier a b =>
            cases sVal <;> try (dsimp only at h ⊢; exact hFallback h)
            case id carrier' a' b' =>
              dsimp only at h ⊢
              cases hCar : ExecutableConversion.types R reducer fuel Γ carrier carrier' with
              | none => simp [hCar] at h
              | some cCar =>
                  rw [hCar] at h
                  dsimp only [Option.bind] at h
                  cases hA : ExecutableConversion.compare R reducer fuel Γ a a' carrier with
                  | none => simp [hA] at h
                  | some cA =>
                      rw [hA] at h
                      dsimp only [Option.bind] at h
                      cases hB : ExecutableConversion.compare R reducer fuel Γ b b' carrier with
                      | none => simp [hB] at h
                      | some cB =>
                          obtain ⟨cCar', hCar'⟩ := ihTypes hCar
                          obtain ⟨cA', hA'⟩ := ihCompare hA
                          obtain ⟨cB', hB'⟩ := ihCompare hB
                          rw [hCar', hA', hB']
                          exact ⟨_, rfl⟩

theorem neutral_step_mono {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer) {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    (ihCompare : ∀ {n : Nat} {Γ : Ctx Head n} {t u T : Tm Head n}
      {c : ExecutableConversion.Certificate R (.compare Γ t u T)},
      ExecutableConversion.compare R reducer fuel Γ t u T = some c →
      ∃ c', ExecutableConversion.compare R reducer fuel' Γ t u T = some c')
    (ihNeutral : ∀ {n : Nat} {Γ : Ctx Head n} {t u : Tm Head n}
      {res : ExecutableConversion.NeutralResult R Γ t u},
      ExecutableConversion.neutral R reducer fuel Γ t u = some res →
      ∃ c', ExecutableConversion.neutral R reducer fuel' Γ t u = some ⟨res.1, c'⟩)
    {n : Nat} {Γ : Ctx Head n} {t u : Tm Head n}
    {res : ExecutableConversion.NeutralResult R Γ t u}
    (h : ExecutableConversion.neutral R reducer (fuel + 1) Γ t u = some res) :
    ∃ c', ExecutableConversion.neutral R reducer (fuel' + 1) Γ t u = some ⟨res.1, c'⟩ := by
  have hle1 : fuel + 1 ≤ fuel' + 1 := Nat.succ_le_succ hle
  rcases res with ⟨resFst, resSnd⟩
  cases t with
  | head _ | pi _ _ | sigma _ _ | id _ _ _ | lam _ | pair _ _ | refl _ | var _ | const _ =>
      unfold ExecutableConversion.neutral at h ⊢
      cases u <;> exact ⟨resSnd, h⟩
  | app fn arg =>
      unfold ExecutableConversion.neutral at h ⊢
      cases u <;> try simp at h
      case app fn' arg' =>
        simp only [Option.bind_eq_bind, Option.bind] at h ⊢
        cases hFn : ExecutableConversion.neutral R reducer fuel Γ fn fn' with
        | none => simp [hFn] at h
        | some compared =>
            obtain ⟨cFn', hFn'⟩ := ihNeutral hFn
            rw [hFn] at h
            rw [hFn']
            dsimp only [Option.bind] at h ⊢
            cases hNorm : reducer (fuel + 1) compared.1 with
            | none => simp [hNorm] at h
            | some normal =>
                obtain ⟨normProp', hNorm'⟩ := hMono hle1 hNorm
                rcases normal with ⟨normVal, normProp⟩
                dsimp only at hNorm'
                rw [hNorm] at h
                rw [hNorm']
                dsimp only [Option.bind] at h ⊢
                cases normVal <;> try (dsimp only at h; cases h)
                case pi dom body =>
                  dsimp only at h ⊢
                  cases hArg : ExecutableConversion.compare R reducer fuel Γ arg arg' dom with
                  | none => simp [hArg] at h
                  | some cArg =>
                      rw [hArg] at h
                      dsimp only [Option.bind] at h
                      cases h
                      obtain ⟨cArg', hArg'⟩ := ihCompare hArg
                      rw [hArg']
                      exact ⟨_, rfl⟩
  | fst p =>
      unfold ExecutableConversion.neutral at h ⊢
      cases u <;> try simp at h
      case fst p' =>
        simp only [Option.bind_eq_bind, Option.bind] at h ⊢
        cases hP : ExecutableConversion.neutral R reducer fuel Γ p p' with
        | none => simp [hP] at h
        | some compared =>
            obtain ⟨cP', hP'⟩ := ihNeutral hP
            rw [hP] at h
            rw [hP']
            dsimp only [Option.bind] at h ⊢
            cases hNorm : reducer (fuel + 1) compared.1 with
            | none => simp [hNorm] at h
            | some normal =>
                obtain ⟨normProp', hNorm'⟩ := hMono hle1 hNorm
                rcases normal with ⟨normVal, normProp⟩
                dsimp only at hNorm'
                rw [hNorm] at h
                rw [hNorm']
                dsimp only [Option.bind] at h ⊢
                cases normVal <;> (dsimp only at h; cases h); exact ⟨_, rfl⟩
  | snd p =>
      unfold ExecutableConversion.neutral at h ⊢
      cases u <;> try simp at h
      case snd p' =>
        simp only [Option.bind_eq_bind, Option.bind] at h ⊢
        cases hP : ExecutableConversion.neutral R reducer fuel Γ p p' with
        | none => simp [hP] at h
        | some compared =>
            obtain ⟨cP', hP'⟩ := ihNeutral hP
            rw [hP] at h
            rw [hP']
            dsimp only [Option.bind] at h ⊢
            cases hNorm : reducer (fuel + 1) compared.1 with
            | none => simp [hNorm] at h
            | some normal =>
                obtain ⟨normProp', hNorm'⟩ := hMono hle1 hNorm
                rcases normal with ⟨normVal, normProp⟩
                dsimp only at hNorm'
                rw [hNorm] at h
                rw [hNorm']
                dsimp only [Option.bind] at h ⊢
                cases normVal <;> (dsimp only at h; cases h); exact ⟨_, rfl⟩

/-- Mutual fuel monotonicity of `ExecutableConversion.compare`, `compareNeutral`, `types`,
and `neutral` for any fuel-monotone reducer. -/
theorem executableConversion_mono {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer) :
    ∀ (fuel : Nat),
      (∀ {fuel' n : Nat} {Γ : Ctx Head n} {t u T : Tm Head n}
          {c : ExecutableConversion.Certificate R (.compare Γ t u T)},
        fuel ≤ fuel' →
        ExecutableConversion.compare R reducer fuel Γ t u T = some c →
        ∃ c', ExecutableConversion.compare R reducer fuel' Γ t u T = some c') ∧
      (∀ {fuel' n : Nat} {Γ : Ctx Head n} {t u T : Tm Head n}
          {c : ExecutableConversion.Certificate R (.compare Γ t u T)},
        fuel ≤ fuel' →
        ExecutableConversion.compareNeutral R reducer fuel Γ t u T = some c →
        ∃ c', ExecutableConversion.compareNeutral R reducer fuel' Γ t u T = some c') ∧
      (∀ {fuel' n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
          {c : ExecutableConversion.Certificate R (.types Γ A B)},
        fuel ≤ fuel' →
        ExecutableConversion.types R reducer fuel Γ A B = some c →
        ∃ c', ExecutableConversion.types R reducer fuel' Γ A B = some c') ∧
      (∀ {fuel' n : Nat} {Γ : Ctx Head n} {t u : Tm Head n}
          {res : ExecutableConversion.NeutralResult R Γ t u},
        fuel ≤ fuel' →
        ExecutableConversion.neutral R reducer fuel Γ t u = some res →
        ∃ c', ExecutableConversion.neutral R reducer fuel' Γ t u = some ⟨res.1, c'⟩)
  | 0 => by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro _ _ _ _ _ _ _ _ h; simp [ExecutableConversion.compare] at h
      · intro _ _ _ _ _ _ _ _ h; simp [ExecutableConversion.compareNeutral] at h
      · intro _ _ _ _ _ _ _ h; simp [ExecutableConversion.types] at h
      · intro _ _ _ _ _ _ _ h; simp [ExecutableConversion.neutral] at h
  | fuel + 1 => by
      have ih := executableConversion_mono hMono fuel
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro fuel' n Γ t u T c hle h
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            have hle' : fuel ≤ fuel' := Nat.le_of_succ_le_succ hle
            exact compare_step_mono R hMono hle' (ih.1 hle') (ih.2.1 hle') (ih.2.2.1 hle') h
      · intro fuel' n Γ t u T c hle h
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            have hle' : fuel ≤ fuel' := Nat.le_of_succ_le_succ hle
            exact compareNeutral_step_mono R hMono hle' (ih.2.2.2 hle') h
      · intro fuel' n Γ A B c hle h
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            have hle' : fuel ≤ fuel' := Nat.le_of_succ_le_succ hle
            exact types_step_mono R hMono hle' (ih.1 hle') (ih.2.2.1 hle') (ih.2.2.2 hle') h
      · intro fuel' n Γ t u res hle h
        cases fuel' with
        | zero => omega
        | succ fuel' =>
            have hle' : fuel ≤ fuel' := Nat.le_of_succ_le_succ hle
            exact neutral_step_mono R hMono hle' (ih.1 hle') (ih.2.2.2 hle') h

theorem ExecutableConversion.compare_mono {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fuel fuel' n : Nat} {Γ : Ctx Head n} {t u T : Tm Head n}
    {c : ExecutableConversion.Certificate R (.compare Γ t u T)}
    (hle : fuel ≤ fuel')
    (h : ExecutableConversion.compare R reducer fuel Γ t u T = some c) :
    ∃ c', ExecutableConversion.compare R reducer fuel' Γ t u T = some c' :=
  (executableConversion_mono R hMono fuel).1 hle h

theorem ExecutableConversion.compareNeutral_mono {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fuel fuel' n : Nat} {Γ : Ctx Head n} {t u T : Tm Head n}
    {c : ExecutableConversion.Certificate R (.compare Γ t u T)}
    (hle : fuel ≤ fuel')
    (h : ExecutableConversion.compareNeutral R reducer fuel Γ t u T = some c) :
    ∃ c', ExecutableConversion.compareNeutral R reducer fuel' Γ t u T = some c' :=
  (executableConversion_mono R hMono fuel).2.1 hle h

theorem ExecutableConversion.types_mono {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fuel fuel' n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    {c : ExecutableConversion.Certificate R (.types Γ A B)}
    (hle : fuel ≤ fuel')
    (h : ExecutableConversion.types R reducer fuel Γ A B = some c) :
    ∃ c', ExecutableConversion.types R reducer fuel' Γ A B = some c' :=
  (executableConversion_mono R hMono fuel).2.2.1 hle h

theorem ExecutableConversion.neutral_mono {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fuel fuel' n : Nat} {Γ : Ctx Head n} {t u : Tm Head n}
    {res : ExecutableConversion.NeutralResult R Γ t u}
    (hle : fuel ≤ fuel')
    (h : ExecutableConversion.neutral R reducer fuel Γ t u = some res) :
    ∃ c', ExecutableConversion.neutral R reducer fuel' Γ t u = some ⟨res.1, c'⟩ :=
  (executableConversion_mono R hMono fuel).2.2.2 hle h

theorem ExecutableConversion.compare_complete_pi {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fT fSub n : Nat} {Γ : Ctx Head n} {t u T dom : Tm Head n} {body : Tm Head (n + 1)}
    {pT : Reduces R T (.pi dom body)}
    {cSub : ExecutableConversion.Certificate R
      (.compare (.snoc Γ dom) (.app (Presentation.rename wk t) (.var 0))
        (.app (Presentation.rename wk u) (.var 0)) body)}
    (hT : reducer fT T = some ⟨.pi dom body, pT⟩)
    (hSub : ExecutableConversion.compare R reducer fSub (.snoc Γ dom)
      (.app (Presentation.rename wk t) (.var 0))
      (.app (Presentation.rename wk u) (.var 0)) body = some cSub) :
    ∃ fuel c, ExecutableConversion.compare R reducer fuel Γ t u T = some c := by
  let fuel := max fT fSub
  obtain ⟨pT', hT'⟩ := hMono (by omega : fT ≤ fuel + 1) hT
  dsimp only at hT'
  obtain ⟨cSub', hSub'⟩ := ExecutableConversion.compare_mono R hMono (Nat.le_max_right fT fSub) hSub
  refine ⟨fuel + 1, ?_⟩
  unfold ExecutableConversion.compare
  rw [hT']
  simp only [Option.bind_eq_bind, Option.bind]
  rw [hSub']
  exact ⟨_, rfl⟩

theorem ExecutableConversion.compare_complete_sigma {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fT f₁ f₂ n : Nat} {Γ : Ctx Head n} {t u T dom : Tm Head n} {body : Tm Head (n + 1)}
    {pT : Reduces R T (.sigma dom body)}
    {c₁ : ExecutableConversion.Certificate R (.compare Γ (.fst t) (.fst u) dom)}
    {c₂ : ExecutableConversion.Certificate R (.compare Γ (.snd t) (.snd u) (inst0 (.fst t) body))}
    (hT : reducer fT T = some ⟨.sigma dom body, pT⟩)
    (h₁ : ExecutableConversion.compare R reducer f₁ Γ (.fst t) (.fst u) dom = some c₁)
    (h₂ : ExecutableConversion.compare R reducer f₂ Γ (.snd t) (.snd u) (inst0 (.fst t) body) = some c₂) :
    ∃ fuel c, ExecutableConversion.compare R reducer fuel Γ t u T = some c := by
  let fuel := max fT (max f₁ f₂)
  obtain ⟨pT', hT'⟩ := hMono (by omega : fT ≤ fuel + 1) hT
  dsimp only at hT'
  obtain ⟨c₁', h₁'⟩ := ExecutableConversion.compare_mono R hMono (by omega : f₁ ≤ fuel) h₁
  obtain ⟨c₂', h₂'⟩ := ExecutableConversion.compare_mono R hMono (by omega : f₂ ≤ fuel) h₂
  refine ⟨fuel + 1, ?_⟩
  unfold ExecutableConversion.compare
  rw [hT']
  simp only [Option.bind_eq_bind, Option.bind]
  rw [h₁', h₂']
  exact ⟨_, rfl⟩

theorem ExecutableConversion.compare_complete_sort {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fT fSub n : Nat} {Γ : Ctx Head n} {t u T : Tm Head n} {val : Head}
    {pT : Reduces R T (.head val)}
    {cSub : ExecutableConversion.Certificate R (.types Γ t u)}
    (hT : reducer fT T = some ⟨.head val, pT⟩)
    (hu : R.isUniverse val)
    (hSub : ExecutableConversion.types R reducer fSub Γ t u = some cSub) :
    ∃ fuel c, ExecutableConversion.compare R reducer fuel Γ t u T = some c := by
  let fuel := max fT fSub
  obtain ⟨pT', hT'⟩ := hMono (by omega : fT ≤ fuel + 1) hT
  dsimp only at hT'
  obtain ⟨cSub', hSub'⟩ := ExecutableConversion.types_mono R hMono (Nat.le_max_right fT fSub) hSub
  refine ⟨fuel + 1, ?_⟩
  unfold ExecutableConversion.compare
  rw [hT']
  simp only [Option.bind_eq_bind, Option.bind, dif_pos hu]
  rw [hSub']
  exact ⟨_, rfl⟩

theorem ExecutableConversion.compare_complete_refl {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fT fL fR fSub n : Nat} {Γ : Ctx Head n} {t u T carrier a b x y : Tm Head n}
    {pT : Reduces R T (.id carrier a b)}
    {pL : Reduces R t (.refl x)} {pR : Reduces R u (.refl y)}
    {cSub : ExecutableConversion.Certificate R (.compare Γ x y carrier)}
    (hT : reducer fT T = some ⟨.id carrier a b, pT⟩)
    (hL : reducer fL t = some ⟨.refl x, pL⟩)
    (hR : reducer fR u = some ⟨.refl y, pR⟩)
    (hSub : ExecutableConversion.compare R reducer fSub Γ x y carrier = some cSub) :
    ∃ fuel c, ExecutableConversion.compare R reducer fuel Γ t u T = some c := by
  let fuel := max (max fT fL) (max fR fSub)
  obtain ⟨pT', hT'⟩ := hMono (by omega : fT ≤ fuel + 1) hT
  obtain ⟨pL', hL'⟩ := hMono (by omega : fL ≤ fuel + 1) hL
  obtain ⟨pR', hR'⟩ := hMono (by omega : fR ≤ fuel + 1) hR
  dsimp only at hT' hL' hR'
  obtain ⟨cSub', hSub'⟩ := ExecutableConversion.compare_mono R hMono (by omega : fSub ≤ fuel) hSub
  refine ⟨fuel + 1, ?_⟩
  unfold ExecutableConversion.compare
  rw [hT']
  simp only [Option.bind_eq_bind, Option.bind]
  rw [hL']
  dsimp only [Option.bind]
  rw [hR']
  dsimp only [Option.bind]
  rw [hSub']
  exact ⟨_, rfl⟩

theorem ExecutableConversion.compareNeutral_complete {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fL fR fNe n : Nat} {Γ : Ctx Head n} {t u T t' u' : Tm Head n}
    {pL : Reduces R t t'} {pR : Reduces R u u'}
    {res : ExecutableConversion.NeutralResult R Γ t' u'}
    (hL : reducer fL t = some ⟨t', pL⟩)
    (hR : reducer fR u = some ⟨u', pR⟩)
    (hNe : ExecutableConversion.neutral R reducer fNe Γ t' u' = some res) :
    ∃ fuel c, ExecutableConversion.compareNeutral R reducer fuel Γ t u T = some c := by
  let fuel := max (max fL fR) fNe
  obtain ⟨pL', hL'⟩ := hMono (by omega : fL ≤ fuel + 1) hL
  obtain ⟨pR', hR'⟩ := hMono (by omega : fR ≤ fuel + 1) hR
  dsimp only at hL' hR'
  obtain ⟨cNe', hNe'⟩ := ExecutableConversion.neutral_mono R hMono (by omega : fNe ≤ fuel) hNe
  refine ⟨fuel + 1, ?_⟩
  unfold ExecutableConversion.compareNeutral
  rw [hL']
  simp only [Option.bind_eq_bind, Option.bind]
  rw [hR']
  dsimp only [Option.bind]
  rw [hNe']
  exact ⟨_, rfl⟩

theorem ExecutableConversion.compare_complete_spine {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fT fL fR fNe n : Nat} {Γ : Ctx Head n} {t u T B' t' u' : Tm Head n}
    {pT : Reduces R T B'} {pL : Reduces R t t'} {pR : Reduces R u u'}
    {res : ExecutableConversion.NeutralResult R Γ t' u'}
    (hT : reducer fT T = some ⟨B', pT⟩)
    (hL : reducer fL t = some ⟨t', pL⟩)
    (hR : reducer fR u = some ⟨u', pR⟩)
    (hNe : ExecutableConversion.neutral R reducer fNe Γ t' u' = some res)
    (hNotPi : ∀ d b, B' ≠ .pi d b)
    (hNotSigma : ∀ d b, B' ≠ .sigma d b)
    (hNotUniv : ∀ h, B' = .head h → ¬ R.isUniverse h)
    (hNotRefl : ∀ x, t' ≠ .refl x) :
    ∃ fuel c, ExecutableConversion.compare R reducer fuel Γ t u T = some c := by
  obtain ⟨fCN, cCN, hCN⟩ := ExecutableConversion.compareNeutral_complete R hMono (T := T) hL hR hNe
  let fuel := max (max fT fL) (max fR fCN)
  obtain ⟨pT', hT'⟩ := hMono (by omega : fT ≤ fuel + 1) hT
  obtain ⟨pL', hL'⟩ := hMono (by omega : fL ≤ fuel + 1) hL
  obtain ⟨pR', hR'⟩ := hMono (by omega : fR ≤ fuel + 1) hR
  dsimp only at hT' hL' hR'
  obtain ⟨cCN', hCN'⟩ := ExecutableConversion.compareNeutral_mono R hMono (by omega : fCN ≤ fuel) hCN
  refine ⟨fuel + 1, cCN', ?_⟩
  unfold ExecutableConversion.compare
  rw [hT']
  simp only [Option.bind_eq_bind, Option.bind]
  cases B' with
  | pi d b => exact False.elim (hNotPi d b rfl)
  | sigma d b => exact False.elim (hNotSigma d b rfl)
  | head val =>
      dsimp only
      rw [dif_neg (hNotUniv val rfl)]
      exact hCN'
  | id carrier a b =>
      dsimp only
      rw [hL']
      dsimp only [Option.bind]
      rw [hR']
      dsimp only [Option.bind]
      cases t' with
      | refl x => exact False.elim (hNotRefl x rfl)
      | _ => exact hCN'
  | var _ | const _ | lam _ | app _ _ | pair _ _ | fst _ | snd _ | refl _ =>
      exact hCN'

theorem ExecutableConversion.types_complete_heads {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fA fB n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {a b : Head}
    {pA : Reduces R A (.head a)} {pB : Reduces R B (.head b)}
    (hA : reducer fA A = some ⟨.head a, pA⟩)
    (hB : reducer fB B = some ⟨.head b, pB⟩)
    (hSame : a = b ∨ R.headEq a b) :
    ∃ fuel c, ExecutableConversion.types R reducer fuel Γ A B = some c := by
  let fuel := max fA fB
  obtain ⟨pA', hA'⟩ := hMono (by omega : fA ≤ fuel + 1) hA
  obtain ⟨pB', hB'⟩ := hMono (by omega : fB ≤ fuel + 1) hB
  dsimp only at hA' hB'
  refine ⟨fuel + 1, ?_⟩
  unfold ExecutableConversion.types
  rw [hA']
  simp only [Option.bind_eq_bind, Option.bind]
  rw [hB']
  dsimp only [Option.bind]
  rw [dif_pos hSame]
  exact ⟨_, rfl⟩

theorem ExecutableConversion.types_complete_pi {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fA fB f₁ f₂ n : Nat} {Γ : Ctx Head n} {A B dom dom' : Tm Head n}
    {body body' : Tm Head (n + 1)}
    {pA : Reduces R A (.pi dom body)} {pB : Reduces R B (.pi dom' body')}
    {c₁ : ExecutableConversion.Certificate R (.types Γ dom dom')}
    {c₂ : ExecutableConversion.Certificate R (.types (.snoc Γ dom) body body')}
    (hA : reducer fA A = some ⟨.pi dom body, pA⟩)
    (hB : reducer fB B = some ⟨.pi dom' body', pB⟩)
    (h₁ : ExecutableConversion.types R reducer f₁ Γ dom dom' = some c₁)
    (h₂ : ExecutableConversion.types R reducer f₂ (.snoc Γ dom) body body' = some c₂) :
    ∃ fuel c, ExecutableConversion.types R reducer fuel Γ A B = some c := by
  let fuel := max (max fA fB) (max f₁ f₂)
  obtain ⟨pA', hA'⟩ := hMono (by omega : fA ≤ fuel + 1) hA
  obtain ⟨pB', hB'⟩ := hMono (by omega : fB ≤ fuel + 1) hB
  dsimp only at hA' hB'
  obtain ⟨c₁', h₁'⟩ := ExecutableConversion.types_mono R hMono (by omega : f₁ ≤ fuel) h₁
  obtain ⟨c₂', h₂'⟩ := ExecutableConversion.types_mono R hMono (by omega : f₂ ≤ fuel) h₂
  refine ⟨fuel + 1, ?_⟩
  unfold ExecutableConversion.types
  rw [hA']
  simp only [Option.bind_eq_bind, Option.bind]
  rw [hB']
  dsimp only [Option.bind]
  rw [h₁', h₂']
  exact ⟨_, rfl⟩

theorem ExecutableConversion.types_complete_sigma {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fA fB f₁ f₂ n : Nat} {Γ : Ctx Head n} {A B dom dom' : Tm Head n}
    {body body' : Tm Head (n + 1)}
    {pA : Reduces R A (.sigma dom body)} {pB : Reduces R B (.sigma dom' body')}
    {c₁ : ExecutableConversion.Certificate R (.types Γ dom dom')}
    {c₂ : ExecutableConversion.Certificate R (.types (.snoc Γ dom) body body')}
    (hA : reducer fA A = some ⟨.sigma dom body, pA⟩)
    (hB : reducer fB B = some ⟨.sigma dom' body', pB⟩)
    (h₁ : ExecutableConversion.types R reducer f₁ Γ dom dom' = some c₁)
    (h₂ : ExecutableConversion.types R reducer f₂ (.snoc Γ dom) body body' = some c₂) :
    ∃ fuel c, ExecutableConversion.types R reducer fuel Γ A B = some c := by
  let fuel := max (max fA fB) (max f₁ f₂)
  obtain ⟨pA', hA'⟩ := hMono (by omega : fA ≤ fuel + 1) hA
  obtain ⟨pB', hB'⟩ := hMono (by omega : fB ≤ fuel + 1) hB
  dsimp only at hA' hB'
  obtain ⟨c₁', h₁'⟩ := ExecutableConversion.types_mono R hMono (by omega : f₁ ≤ fuel) h₁
  obtain ⟨c₂', h₂'⟩ := ExecutableConversion.types_mono R hMono (by omega : f₂ ≤ fuel) h₂
  refine ⟨fuel + 1, ?_⟩
  unfold ExecutableConversion.types
  rw [hA']
  simp only [Option.bind_eq_bind, Option.bind]
  rw [hB']
  dsimp only [Option.bind]
  rw [h₁', h₂']
  exact ⟨_, rfl⟩

theorem ExecutableConversion.types_complete_id {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fA fB f₁ f₂ f₃ n : Nat} {Γ : Ctx Head n} {A B C a b C' a' b' : Tm Head n}
    {pA : Reduces R A (.id C a b)} {pB : Reduces R B (.id C' a' b')}
    {c₁ : ExecutableConversion.Certificate R (.types Γ C C')}
    {c₂ : ExecutableConversion.Certificate R (.compare Γ a a' C)}
    {c₃ : ExecutableConversion.Certificate R (.compare Γ b b' C)}
    (hA : reducer fA A = some ⟨.id C a b, pA⟩)
    (hB : reducer fB B = some ⟨.id C' a' b', pB⟩)
    (h₁ : ExecutableConversion.types R reducer f₁ Γ C C' = some c₁)
    (h₂ : ExecutableConversion.compare R reducer f₂ Γ a a' C = some c₂)
    (h₃ : ExecutableConversion.compare R reducer f₃ Γ b b' C = some c₃) :
    ∃ fuel c, ExecutableConversion.types R reducer fuel Γ A B = some c := by
  let fuel := max (max fA fB) (max f₁ (max f₂ f₃))
  obtain ⟨pA', hA'⟩ := hMono (by omega : fA ≤ fuel + 1) hA
  obtain ⟨pB', hB'⟩ := hMono (by omega : fB ≤ fuel + 1) hB
  dsimp only at hA' hB'
  obtain ⟨c₁', h₁'⟩ := ExecutableConversion.types_mono R hMono (by omega : f₁ ≤ fuel) h₁
  obtain ⟨c₂', h₂'⟩ := ExecutableConversion.compare_mono R hMono (by omega : f₂ ≤ fuel) h₂
  obtain ⟨c₃', h₃'⟩ := ExecutableConversion.compare_mono R hMono (by omega : f₃ ≤ fuel) h₃
  refine ⟨fuel + 1, ?_⟩
  unfold ExecutableConversion.types
  rw [hA']
  simp only [Option.bind_eq_bind, Option.bind]
  rw [hB']
  dsimp only [Option.bind]
  rw [h₁', h₂', h₃']
  exact ⟨_, rfl⟩

theorem ExecutableConversion.types_complete_neutral {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fA fB fNe n : Nat} {Γ : Ctx Head n} {A B A' B' : Tm Head n}
    {pA : Reduces R A A'} {pB : Reduces R B B'}
    {res : ExecutableConversion.NeutralResult R Γ A' B'}
    (hA : reducer fA A = some ⟨A', pA⟩)
    (hB : reducer fB B = some ⟨B', pB⟩)
    (hNe : ExecutableConversion.neutral R reducer fNe Γ A' B' = some res)
    (hNotHead : ∀ h, A' ≠ .head h)
    (hNotPi : ∀ d b, A' ≠ .pi d b)
    (hNotSigma : ∀ d b, A' ≠ .sigma d b)
    (hNotId : ∀ C x y, A' ≠ .id C x y) :
    ∃ fuel c, ExecutableConversion.types R reducer fuel Γ A B = some c := by
  let fuel := max (max fA fB) fNe
  obtain ⟨pA', hA'⟩ := hMono (by omega : fA ≤ fuel + 1) hA
  obtain ⟨pB', hB'⟩ := hMono (by omega : fB ≤ fuel + 1) hB
  dsimp only at hA' hB'
  obtain ⟨cNe', hNe'⟩ := ExecutableConversion.neutral_mono R hMono (by omega : fNe ≤ fuel) hNe
  refine ⟨fuel + 1, ?_⟩
  unfold ExecutableConversion.types
  rw [hA']
  simp only [Option.bind_eq_bind, Option.bind]
  rw [hB']
  dsimp only [Option.bind]
  cases A' with
  | head h => exact False.elim (hNotHead h rfl)
  | pi d b => exact False.elim (hNotPi d b rfl)
  | sigma d b => exact False.elim (hNotSigma d b rfl)
  | id C x y => exact False.elim (hNotId C x y rfl)
  | var _ | const _ | lam _ | app _ _ | pair _ _ | fst _ | snd _ | refl _ =>
      dsimp only
      rw [hNe']
      exact ⟨_, rfl⟩

theorem ExecutableConversion.neutral_complete_var (reducer : ExecutableReduction.Reducer R)
    {n : Nat} (Γ : Ctx Head n) (i : Fin n) :
    ∃ c, ExecutableConversion.neutral R reducer 1 Γ (.var i) (.var i) =
      some ⟨Ctx.lookup Γ i, c⟩ := by
  unfold ExecutableConversion.neutral
  dsimp only
  rw [dif_pos rfl]
  exact ⟨_, rfl⟩

theorem ExecutableConversion.neutral_complete_const (reducer : ExecutableReduction.Reducer R)
    {n : Nat} (Γ : Ctx Head n) {name : DeclName} {type : Tm Head 0}
    (hKnown : R.constantType name = some type) :
    ∃ c, ExecutableConversion.neutral R reducer 1 Γ (.const name) (.const name) =
      some ⟨liftClosed type, c⟩ := by
  unfold ExecutableConversion.neutral
  dsimp only
  rw [dif_pos rfl]
  split
  next type' hEq =>
    rw [hKnown] at hEq
    injection hEq with hEq'
    subst hEq'
    exact ⟨_, rfl⟩
  next hEq =>
    rw [hKnown] at hEq
    cases hEq

theorem ExecutableConversion.neutral_complete_app {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fFn fU fArg n : Nat} {Γ : Ctx Head n} {f g a b U₀ dom : Tm Head n} {body : Tm Head (n + 1)}
    {cFn : ExecutableConversion.Certificate R (.neutral Γ f g U₀)}
    {pU : Reduces R U₀ (.pi dom body)}
    {cArg : ExecutableConversion.Certificate R (.compare Γ a b dom)}
    (hFn : ExecutableConversion.neutral R reducer fFn Γ f g = some ⟨U₀, cFn⟩)
    (hU : reducer fU U₀ = some ⟨.pi dom body, pU⟩)
    (hArg : ExecutableConversion.compare R reducer fArg Γ a b dom = some cArg) :
    ∃ fuel c, ExecutableConversion.neutral R reducer fuel Γ (.app f a) (.app g b) =
      some ⟨inst0 a body, c⟩ := by
  let fuel := max (max fFn fU) fArg
  obtain ⟨cFn', hFn'⟩ := ExecutableConversion.neutral_mono R hMono (by omega : fFn ≤ fuel) hFn
  obtain ⟨pU', hU'⟩ := hMono (by omega : fU ≤ fuel + 1) hU
  dsimp only at hFn' hU'
  obtain ⟨cArg', hArg'⟩ := ExecutableConversion.compare_mono R hMono (by omega : fArg ≤ fuel) hArg
  refine ⟨fuel + 1, ?_⟩
  unfold ExecutableConversion.neutral
  simp only [Option.bind_eq_bind, Option.bind]
  rw [hFn']
  dsimp only [Option.bind]
  rw [hU']
  dsimp only [Option.bind]
  rw [hArg']
  exact ⟨_, rfl⟩

theorem ExecutableConversion.neutral_complete_fst {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fP fU n : Nat} {Γ : Ctx Head n} {p q U₀ dom : Tm Head n} {body : Tm Head (n + 1)}
    {cP : ExecutableConversion.Certificate R (.neutral Γ p q U₀)}
    {pU : Reduces R U₀ (.sigma dom body)}
    (hP : ExecutableConversion.neutral R reducer fP Γ p q = some ⟨U₀, cP⟩)
    (hU : reducer fU U₀ = some ⟨.sigma dom body, pU⟩) :
    ∃ fuel c, ExecutableConversion.neutral R reducer fuel Γ (.fst p) (.fst q) =
      some ⟨dom, c⟩ := by
  let fuel := max fP fU
  obtain ⟨cP', hP'⟩ := ExecutableConversion.neutral_mono R hMono (by omega : fP ≤ fuel) hP
  obtain ⟨pU', hU'⟩ := hMono (by omega : fU ≤ fuel + 1) hU
  dsimp only at hP' hU'
  refine ⟨fuel + 1, ?_⟩
  unfold ExecutableConversion.neutral
  simp only [Option.bind_eq_bind, Option.bind]
  rw [hP']
  dsimp only [Option.bind]
  rw [hU']
  exact ⟨_, rfl⟩

theorem ExecutableConversion.neutral_complete_snd {reducer : ExecutableReduction.Reducer R}
    (hMono : ReducerMonotone R reducer)
    {fP fU n : Nat} {Γ : Ctx Head n} {p q U₀ dom : Tm Head n} {body : Tm Head (n + 1)}
    {cP : ExecutableConversion.Certificate R (.neutral Γ p q U₀)}
    {pU : Reduces R U₀ (.sigma dom body)}
    (hP : ExecutableConversion.neutral R reducer fP Γ p q = some ⟨U₀, cP⟩)
    (hU : reducer fU U₀ = some ⟨.sigma dom body, pU⟩) :
    ∃ fuel c, ExecutableConversion.neutral R reducer fuel Γ (.snd p) (.snd q) =
      some ⟨inst0 (.fst p) body, c⟩ := by
  let fuel := max fP fU
  obtain ⟨cP', hP'⟩ := ExecutableConversion.neutral_mono R hMono (by omega : fP ≤ fuel) hP
  obtain ⟨pU', hU'⟩ := hMono (by omega : fU ≤ fuel + 1) hU
  dsimp only at hP' hU'
  refine ⟨fuel + 1, ?_⟩
  unfold ExecutableConversion.neutral
  simp only [Option.bind_eq_bind, Option.bind]
  rw [hP']
  dsimp only [Option.bind]
  rw [hU']
  exact ⟨_, rfl⟩

/-- Inductive motive for simulating derivations of `Algorithmic S.R S.roles st`
in `ExecutableConversion` under any fuel-monotone weak-head-complete reducer. -/
def ExecCompleteAt {L : Type} [LevelOrder L] (S : Setting Head L)
    [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
    (reducer : ExecutableReduction.Reducer S.R) : AlgorithmicStatement Head → Prop
  | .types Γ A B => ∀ {Δ A₀ B₀}, CtxEq S.R Γ Δ → CtxFormed S.R Δ →
      WhRed S.R S.roles A₀ A → WhRed S.R S.roles B₀ B →
      ∃ fuel c, ExecutableConversion.types S.R reducer fuel Δ A₀ B₀ = some c
  | .typesW Γ A B => ∀ {Δ A₀ B₀}, CtxEq S.R Γ Δ → CtxFormed S.R Δ →
      WhRed S.R S.roles A₀ A → WhRed S.R S.roles B₀ B →
      ∃ fuel c, ExecutableConversion.types S.R reducer fuel Δ A₀ B₀ = some c
  | .terms Γ t u A => ∀ {Δ t₀ u₀ B}, CtxEq S.R Γ Δ → CtxFormed S.R Δ →
      TypeEq S.R Δ A B →
      WhRed S.R S.roles t₀ t → Equal S.R Δ t₀ t B →
      WhRed S.R S.roles u₀ u → Equal S.R Δ u₀ u B →
      ∃ fuel c, ExecutableConversion.compare S.R reducer fuel Δ t₀ u₀ B = some c
  | .termsW Γ t u A => ∀ {Δ t₀ u₀ B B'}, CtxEq S.R Γ Δ → CtxFormed S.R Δ →
      TypeEq S.R Δ A B' → IsTypeForm S.roles B' → WhRed S.R S.roles B B' →
      WhRed S.R S.roles t₀ t → Equal S.R Δ t₀ t B' →
      WhRed S.R S.roles u₀ u → Equal S.R Δ u₀ u B' →
      ∃ fuel c, ExecutableConversion.compare S.R reducer fuel Δ t₀ u₀ B = some c
  | .spines Γ t u U => ∀ {Δ}, CtxEq S.R Γ Δ → CtxFormed S.R Δ →
      ∃ fuel U' c, ExecutableConversion.neutral S.R reducer fuel Δ t u = some ⟨U', c⟩ ∧
        TypeEq S.R Δ U U'
  | .spinesW Γ t u U => ∀ {Δ}, CtxEq S.R Γ Δ → CtxFormed S.R Δ →
      ∃ fuel U₀ U' c, ExecutableConversion.neutral S.R reducer fuel Δ t u = some ⟨U₀, c⟩ ∧
        WhRed S.R S.roles U₀ U' ∧ IsTypeForm S.roles U' ∧ TypeEq S.R Δ U U'

/-- **Simulation Completeness of `ExecutableConversion` on `Algorithmic` Derivations**:
Every derivation `Algorithmic S.R S.roles st` is accepted at some finite fuel by
`ExecutableConversion` whenever `reducer` is fuel-monotone and complete for `WhRed`. -/
theorem Algorithmic.executable_complete {L : Type} [LevelOrder L] {S : Setting Head L}
    [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
    (facts : FormFacts S.R S.roles)
    (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
    {reducer : ExecutableReduction.Reducer S.R}
    (hMono : ReducerMonotone S.R reducer)
    (hWhnf : ReducerWhnfComplete S.R S.roles reducer)
    {st : AlgorithmicStatement Head}
    (derivation : Algorithmic S.R S.roles st) :
    ExecCompleteAt S reducer st := by
  have conv := fun {st : AlgorithmicStatement Head} (d : Algorithmic S.R S.roles st) =>
    Algorithmic.converts facts roots heads algebra d
  have sound := fun {st : AlgorithmicStatement Head} (d : Algorithmic S.R S.roles st) =>
    Algorithmic.sound facts roots heads algebra d
  induction derivation with
  | types rA rB _ _ _ ih =>
      intro Δ A₀ B₀ equal formed wA₀ wB₀
      exact ih equal formed (wA₀.trans rA.red) (wB₀.trans rB.red)
  | heads same _ _ _ =>
      intro Δ A₀ B₀ _ _ wA₀ wB₀
      obtain ⟨fA, pA, hA⟩ := hWhnf wA₀ (head_whnf S.shape _)
      obtain ⟨fB, pB, hB⟩ := hWhnf wB₀ (head_whnf S.shape _)
      exact ExecutableConversion.types_complete_heads S.R hMono hA hB same
  | pi isA _ _ ihA ihB =>
      intro Δ A₀ B₀ equal formed wA₀ wB₀
      have isA' := isA.stable equal
      obtain ⟨fA, pA, hA⟩ := hWhnf wA₀ (pi_whnf S.shape _ _)
      obtain ⟨fB, pB, hB⟩ := hWhnf wB₀ (pi_whnf S.shape _ _)
      obtain ⟨fDom, cDom, hDom⟩ := ihA equal formed .refl .refl
      obtain ⟨fBody, cBody, hBody⟩ := ihB (equal.snocSame isA) (.snoc formed isA') .refl .refl
      exact ExecutableConversion.types_complete_pi S.R hMono hA hB hDom hBody
  | sigma isA _ _ ihA ihB =>
      intro Δ A₀ B₀ equal formed wA₀ wB₀
      have isA' := isA.stable equal
      obtain ⟨fA, pA, hA⟩ := hWhnf wA₀ (sigma_whnf S.shape _ _)
      obtain ⟨fB, pB, hB⟩ := hWhnf wB₀ (sigma_whnf S.shape _ _)
      obtain ⟨fDom, cDom, hDom⟩ := ihA equal formed .refl .refl
      obtain ⟨fBody, cBody, hBody⟩ := ihB (equal.snocSame isA) (.snoc formed isA') .refl .refl
      exact ExecutableConversion.types_complete_sigma S.R hMono hA hB hDom hBody
  | id dA dx dy ihA ihx ihy =>
      intro Δ A₀ B₀ equal formed wA₀ wB₀
      have isA := dA.types_isType.1.stable equal
      obtain ⟨fA, pA, hA⟩ := hWhnf wA₀ (id_whnf S.shape _ _ _)
      obtain ⟨fB, pB, hB⟩ := hWhnf wB₀ (id_whnf S.shape _ _ _)
      obtain ⟨fC, cC, hC⟩ := ihA equal formed .refl .refl
      have tx := Typed.stable dx.terms_typed.1 equal
      have tx' := Typed.stable dx.terms_typed.2 equal
      have ty := Typed.stable dy.terms_typed.1 equal
      have ty' := Typed.stable dy.terms_typed.2 equal
      obtain ⟨fx, cx, hx⟩ := ihx equal formed isA.refl .refl (.refl tx) .refl (.refl tx')
      obtain ⟨fy, cy, hy⟩ := ihy equal formed isA.refl .refl (.refl ty) .refl (.refl ty')
      exact ExecutableConversion.types_complete_id S.R hMono hA hB hC hx hy
  | inductiveType role isT =>
      intro Δ A₀ B₀ _ _ wA₀ wB₀
      obtain ⟨_, _, typed⟩ := isT
      obtain ⟨_, _, declared, _⟩ := Typed.generation typed
      obtain ⟨fA, pA, hA⟩ := hWhnf wA₀ (inductive_whnf S.shape role)
      obtain ⟨fB, pB, hB⟩ := hWhnf wB₀ (inductive_whnf S.shape role)
      obtain ⟨cNe, hNe⟩ := ExecutableConversion.neutral_complete_const S.R reducer Δ declared
      exact ExecutableConversion.types_complete_neutral S.R hMono hA hB hNe
        (fun _ h => nomatch h) (fun _ _ h => nomatch h)
        (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | neutralTypes nA nB _ _ ih =>
      intro Δ A₀ B₀ equal formed wA₀ wB₀
      obtain ⟨fA, pA, hA⟩ := hWhnf wA₀ (nA.whnf S.shape)
      obtain ⟨fB, pB, hB⟩ := hWhnf wB₀ (nB.whnf S.shape)
      obtain ⟨fNe, U₀, _, cNe, hNe, _, _, _⟩ := ih equal formed
      exact ExecutableConversion.types_complete_neutral S.R hMono hA hB hNe
        nA.not_former.1 nA.not_former.2.1 nA.not_former.2.2.1 nA.not_former.2.2.2
  | terms rA _ rt ru _ ih =>
      intro Δ t₀ u₀ B equal formed eAB wt₀ et₀ wu₀ eu₀
      obtain ⟨B', rB, fB⟩ :=
        facts.typeForm ((TypeEq.isType eAB formed).2) formed
      have eA' := TypeEq.trans S.levels (TypeEq.trans S.levels (rA.stable equal).typeEq.symm eAB)
        rB.typeEq
      have et' : Equal S.R Δ t₀ _ B' :=
        .trans (Equal.convType et₀ rB.typeEq) (Equal.convType (Equal.stable rt.equal equal) eA')
      have eu' : Equal S.R Δ u₀ _ B' :=
        .trans (Equal.convType eu₀ rB.typeEq) (Equal.convType (Equal.stable ru.equal equal) eA')
      exact ih equal formed eA' fB rB.red (wt₀.trans rt.red) et' (wu₀.trans ru.red) eu'
  | univ hu _ _ _ ih =>
      intro Δ t₀ u₀ B B' equal formed eAB fB wB wt₀ _ wu₀ _
      obtain ⟨h', rfl, same⟩ :=
        (facts.forms eAB formed (.inl ⟨_, rfl⟩) fB).head_left
      have hu' : S.R.isUniverse h' := (HeadSame.level S.levels same).1.mp hu
      obtain ⟨fB_red, pB, hB_red⟩ := hWhnf wB (head_whnf S.shape h')
      obtain ⟨fTy, cTy, hTy⟩ := ih equal formed wt₀ wu₀
      exact ExecutableConversion.compare_complete_sort S.R hMono hB_red hu' hTy
  | @eta n Γ f g A B _ _ _ _ _ _ ih =>
      intro Δ t₀ u₀ B₀ B' equal formed eAB fB wB wt₀ et₀ wu₀ eu₀
      obtain ⟨A₂, B₂, rfl, eA, eB⟩ :=
        (facts.forms eAB formed (.inr (.inl ⟨_, _, rfl⟩)) fB).pi_left
      have isA₂ := (TypeEq.isType eA formed).2
      have eB₂ := eB.stable (.snoc (CtxEq.refl Δ formed) eA.symm)
      obtain ⟨fB_red, pB, hB_red⟩ := hWhnf wB (pi_whnf S.shape A₂ B₂)
      have et₀_app : Equal S.R (.snoc Δ A₂) (.app (Presentation.rename wk t₀) (.var 0))
          (.app (Presentation.rename wk f) (.var 0)) B₂ := by
        simpa only [inst0_var_rename_liftRen_wk] using
          Derivable.appCong (et₀.rename (CtxRen.wk Δ A₂)) (.refl (.var 0))
      have eu₀_app : Equal S.R (.snoc Δ A₂) (.app (Presentation.rename wk u₀) (.var 0))
          (.app (Presentation.rename wk g) (.var 0)) B₂ := by
        simpa only [inst0_var_rename_liftRen_wk] using
          Derivable.appCong (eu₀.rename (CtxRen.wk Δ A₂)) (.refl (.var 0))
      obtain ⟨fBody, cBody, hBody⟩ := ih (.snoc equal eA.symm) (.snoc formed isA₂) eB₂
        ((wt₀.rename wk).app (.var 0)) et₀_app ((wu₀.rename wk).app (.var 0)) eu₀_app
      exact ExecutableConversion.compare_complete_pi S.R hMono hB_red hBody
  | @sigmaEta n Γ p q A B tp _ _ _ d₁ _ ih₁ ih₂ =>
      intro Δ t₀ u₀ B₀ B' equal formed eAB fB wB wt₀ et₀ wu₀ eu₀
      obtain ⟨A₂, B₂, rfl, eA, eB⟩ :=
        (facts.forms eAB formed (.inr (.inr (.inl ⟨_, _, rfl⟩))) fB).sigma_left
      obtain ⟨fB_red, pB, hB_red⟩ := hWhnf wB (sigma_whnf S.shape A₂ B₂)
      obtain ⟨f1, c1, h1⟩ := ih₁ equal formed eA
        wt₀.fst (.fstCong et₀) wu₀.fst (.fstCong eu₀)
      have tp' := Typed.stable tp equal
      have tp₂ : Typed S.R Δ p (.sigma A₂ B₂) := Typed.convType tp' eAB
      obtain ⟨tt₀, _⟩ := Equal.typed et₀ formed
      obtain ⟨tu₀, _⟩ := Equal.typed eu₀ formed
      obtain ⟨s, hs, tSigma⟩ := Typed.isType tt₀ formed
      obtain ⟨_, ⟨v, hv, tB₂⟩⟩ := IsType.sigma_parts ⟨s, hs, tSigma⟩
      have eFst_pq : Equal S.R Δ (.fst p) (.fst q) A₂ :=
        sound (conv d₁ equal formed eA) formed
      have eFst_t₀u₀ : Equal S.R Δ (.fst t₀) (.fst u₀) A₂ :=
        .trans (.fstCong et₀) (.trans eFst_pq (.symm (.fstCong eu₀)))
      have eInst : TypeEq S.R Δ (inst0 (.fst p) B) (inst0 (.fst t₀) B₂) :=
        TypeEq.trans S.levels (TypeEq.instantiate eB (.fstElim tp'))
          (TypeEq.of_instantiateEq tB₂ hv (.fstElim tp₂) (.symm (.fstCong et₀)))
      have eSnd_u₀ : Equal S.R Δ (.snd u₀) (.snd q) (inst0 (.fst t₀) B₂) :=
        Equal.convType (.sndCong eu₀)
          (TypeEq.of_instantiateEq tB₂ hv (.fstElim tu₀) (.symm eFst_t₀u₀))
      obtain ⟨f2, c2, h2⟩ := ih₂ equal formed eInst
        wt₀.snd (.sndCong et₀) wu₀.snd eSnd_u₀
      exact ExecutableConversion.compare_complete_sigma S.R hMono hB_red h1 h2
  | refl _ _ d ih =>
      intro Δ t₀ u₀ B B' equal formed eAB fB wB wt₀ _ wu₀ _
      obtain ⟨C', x', y', rfl, eC, _, _⟩ :=
        (facts.forms eAB formed (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) fB).id_left
      obtain ⟨fB_red, pB, hB_red⟩ := hWhnf wB (id_whnf S.shape C' x' y')
      obtain ⟨fL, pL, hL⟩ := hWhnf wt₀ (refl_whnf S.shape _)
      obtain ⟨fR, pR, hR⟩ := hWhnf wu₀ (refl_whnf S.shape _)
      have tx := Typed.convType (Typed.stable d.terms_typed.1 equal) eC
      have tx' := Typed.convType (Typed.stable d.terms_typed.2 equal) eC
      obtain ⟨fSub, cSub, hSub⟩ := ih equal formed eC .refl (.refl tx) .refl (.refl tx')
      exact ExecutableConversion.compare_complete_refl S.R hMono hB_red hL hR hSub
  | spine sA fT fU _ _ _ ih =>
      intro Δ t₀ u₀ B B' equal formed eAB fB wB wt₀ _ wu₀ _
      have sB' : SpineType S.R S.roles B' := sA.of_typeEq facts eAB formed fB
      obtain ⟨fB_red, pB, hB_red⟩ := hWhnf wB fB.whnf
      obtain ⟨fL, pL, hL⟩ := hWhnf wt₀ fT.whnf
      obtain ⟨fR, pR, hR⟩ := hWhnf wu₀ fU.whnf
      obtain ⟨fNe, U₀, _, cNe, hNe, _, _, _⟩ := ih equal formed
      exact ExecutableConversion.compare_complete_spine S.R hMono hB_red hL hR hNe
        (fun _ _ hEq => by subst hEq; exact SpineType.not_pi sB')
        (fun _ _ hEq => by subst hEq; exact SpineType.not_sigma sB')
        (fun _ hEq hu => by subst hEq; exact sB'.not_universe hu)
        (fun x hx => by subst hx; exact SpineForm.not_refl fT)
  | var i =>
      intro Δ equal _
      obtain ⟨c, h⟩ := ExecutableConversion.neutral_complete_var S.R reducer Δ i
      exact ⟨1, Ctx.lookup Δ i, c, h, (equal.lookup i).symm⟩
  | const declared typed =>
      intro Δ equal formed
      have typed' := Typed.stable typed equal
      obtain ⟨c, h⟩ := ExecutableConversion.neutral_complete_const S.R reducer Δ declared
      exact ⟨1, liftClosed _, c, h, (Typed.isType typed' formed).refl⟩
  | app _ da ihf iha =>
      intro Δ equal formed
      obtain ⟨fFn, U₀, U', cFn, hFn, wU, fU', eU⟩ := ihf equal formed
      obtain ⟨A₂, B₂, rfl, eA, eB⟩ :=
        (facts.forms eU formed (.inr (.inl ⟨_, _, rfl⟩)) fU').pi_left
      obtain ⟨fU, pU, hU⟩ := hWhnf wU (pi_whnf S.shape A₂ B₂)
      have ta := Typed.convType (Typed.stable da.terms_typed.1 equal) eA
      have tb := Typed.convType (Typed.stable da.terms_typed.2 equal) eA
      obtain ⟨fArg, cArg, hArg⟩ := iha equal formed eA .refl (.refl ta) .refl (.refl tb)
      obtain ⟨fuel, c, h⟩ := ExecutableConversion.neutral_complete_app S.R hMono hFn hU hArg
      exact ⟨fuel, inst0 _ B₂, c, h,
        TypeEq.instantiate eB (Typed.stable da.terms_typed.1 equal)⟩
  | fst _ ih =>
      intro Δ equal formed
      obtain ⟨fP, U₀, U', cP, hP, wU, fU', eU⟩ := ih equal formed
      obtain ⟨A₂, B₂, rfl, eA, _⟩ :=
        (facts.forms eU formed (.inr (.inr (.inl ⟨_, _, rfl⟩))) fU').sigma_left
      obtain ⟨fU, pU, hU⟩ := hWhnf wU (sigma_whnf S.shape A₂ B₂)
      obtain ⟨fuel, c, h⟩ := ExecutableConversion.neutral_complete_fst S.R hMono hP hU
      exact ⟨fuel, A₂, c, h, eA⟩
  | snd dp ih =>
      intro Δ equal formed
      obtain ⟨fP, U₀, U', cP, hP, wU, fU', eU⟩ := ih equal formed
      obtain ⟨A₂, B₂, rfl, eA, eB⟩ :=
        (facts.forms eU formed (.inr (.inr (.inl ⟨_, _, rfl⟩))) fU').sigma_left
      obtain ⟨fU, pU, hU⟩ := hWhnf wU (sigma_whnf S.shape A₂ B₂)
      obtain ⟨fuel, c, h⟩ := ExecutableConversion.neutral_complete_snd S.R hMono hP hU
      obtain ⟨U₁, d₁, eU₁⟩ := conv dp equal formed
      obtain ⟨tp₁, _, _⟩ := sound d₁ formed
      have tp : Typed S.R Δ _ (.sigma _ _) := Typed.convType tp₁ eU₁.symm
      exact ⟨fuel, inst0 _ B₂, c, h, TypeEq.instantiate eB (.fstElim tp)⟩
  | spinesW _ rU _ ih =>
      intro Δ equal formed
      obtain ⟨fNe, U₀, cNe, hNe, eUU₀⟩ := ih equal formed
      obtain ⟨U₀', rU₀, fU₀'⟩ :=
        facts.typeForm ((TypeEq.isType eUU₀ formed).2) formed
      exact ⟨fNe, U₀, U₀', cNe, hNe, rU₀.red, fU₀',
        TypeEq.trans S.levels (TypeEq.trans S.levels (rU.stable equal).typeEq.symm eUU₀)
          rU₀.typeEq⟩

/-- Fuel monotonicity of `nbeCompare`. -/
theorem nbeCompare_mono (root : ExecutableReduction.RootEvaluator R)
    {fuel fuel' n : Nat} (hle : fuel ≤ fuel') {Γ : Ctx Head n} {t u A : Tm Head n}
    {c : ExecutableConversion.Certificate R (.compare Γ t u A)}
    (h : nbeCompare R root fuel Γ t u A = some c) :
    ∃ c', nbeCompare R root fuel' Γ t u A = some c' :=
  ExecutableConversion.compare_mono R (nbeWhnfReducer_monotone R root) hle h

/-- Fuel monotonicity of `nbeCompareTypes`. -/
theorem nbeCompareTypes_mono (root : ExecutableReduction.RootEvaluator R)
    {fuel fuel' n : Nat} (hle : fuel ≤ fuel') {Γ : Ctx Head n} {A B : Tm Head n}
    {c : ExecutableConversion.Certificate R (.types Γ A B)}
    (h : nbeCompareTypes R root fuel Γ A B = some c) :
    ∃ c', nbeCompareTypes R root fuel' Γ A B = some c' :=
  ExecutableConversion.types_mono R (nbeWhnfReducer_monotone R root) hle h

/-- Fuel monotonicity of `nbeAcceptsConv`. -/
theorem nbeAcceptsConv_mono (root : ExecutableReduction.RootEvaluator R)
    {fuel fuel' n : Nat} (hle : fuel ≤ fuel') {Γ : Ctx Head n} {t u A : Tm Head n}
    (h : nbeAcceptsConv R root fuel Γ t u A = true) :
    nbeAcceptsConv R root fuel' Γ t u A = true := by
  simp only [nbeAcceptsConv, ExecutableConversion.accepts, Option.isSome_iff_exists] at h ⊢
  obtain ⟨c, hc⟩ := h
  exact nbeCompare_mono R root hle hc

/-- Fuel monotonicity of `nbeAcceptsTypeConv`. -/
theorem nbeAcceptsTypeConv_mono (root : ExecutableReduction.RootEvaluator R)
    {fuel fuel' n : Nat} (hle : fuel ≤ fuel') {Γ : Ctx Head n} {A B : Tm Head n}
    (h : nbeAcceptsTypeConv R root fuel Γ A B = true) :
    nbeAcceptsTypeConv R root fuel' Γ A B = true := by
  simp only [nbeAcceptsTypeConv, ExecutableConversion.acceptsTypes, Option.isSome_iff_exists] at h ⊢
  obtain ⟨c, hc⟩ := h
  exact nbeCompareTypes_mono R root hle hc

/-- **Simulation Completeness of `nbeCompare` on `Algorithmic (.terms Γ t u A)`**:
For any `Setting Head L` with `S.R.computation = RootComputation.empty` and
`S.roles = fun _ => .rigid`, our closure-based NbE conversion `nbeCompare`
accepts every `Algorithmic S.R S.roles (.terms Γ t u A)` derivation in a formed
context `Γ` at some finite fuel. -/
theorem nbeCompare_complete_of_algorithmic {L : Type} [LevelOrder L] {S : Setting Head L}
    [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
    (facts : FormFacts S.R S.roles)
    (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
    (hComp : S.R.computation = RootComputation.empty)
    (hRoles : S.roles = fun _ => .rigid)
    {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    (hFormed : CtxFormed S.R Γ)
    (derivation : Algorithmic S.R S.roles (.terms Γ t u A)) :
    ∃ fuel c, nbeCompare S.R (fun _ => none) fuel Γ t u A = some c := by
  have hExec : ExecCompleteAt S (nbeWhnfReducer S.R (fun _ => none)) (.terms Γ t u A) :=
    Algorithmic.executable_complete (S := S) facts roots heads algebra
      (nbeWhnfReducer_monotone S.R (fun _ => none))
      (nbeWhnfReducer_whnfComplete S.R hComp hRoles)
      derivation
  obtain ⟨tt, tu⟩ := derivation.terms_typed
  have hTypeA := Typed.isType tt hFormed
  exact hExec (CtxEq.refl Γ hFormed) hFormed hTypeA.refl .refl (.refl tt) .refl (.refl tu)

/-- **Simulation Completeness of `nbeCompareTypes` on `Algorithmic (.types Γ A B)`**:
For any `Setting Head L` with `S.R.computation = RootComputation.empty` and
`S.roles = fun _ => .rigid`, our closure-based NbE type conversion `nbeCompareTypes`
accepts every `Algorithmic S.R S.roles (.types Γ A B)` derivation in a formed
context `Γ` at some finite fuel. -/
theorem nbeCompareTypes_complete_of_algorithmic {L : Type} [LevelOrder L] {S : Setting Head L}
    [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
    (facts : FormFacts S.R S.roles)
    (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
    (hComp : S.R.computation = RootComputation.empty)
    (hRoles : S.roles = fun _ => .rigid)
    {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (hFormed : CtxFormed S.R Γ)
    (derivation : Algorithmic S.R S.roles (.types Γ A B)) :
    ∃ fuel c, nbeCompareTypes S.R (fun _ => none) fuel Γ A B = some c := by
  have hExec : ExecCompleteAt S (nbeWhnfReducer S.R (fun _ => none)) (.types Γ A B) :=
    Algorithmic.executable_complete (S := S) facts roots heads algebra
      (nbeWhnfReducer_monotone S.R (fun _ => none))
      (nbeWhnfReducer_whnfComplete S.R hComp hRoles)
      derivation
  exact hExec (CtxEq.refl Γ hFormed) hFormed .refl .refl

end ExecutableConversionCompleteness

/-! ## 3. Normal-Form Existence, Conversion Soundness & Completeness, and Decidability -/

section TowerNormalizationAndConversion

open TowerModel

variable {L : Type} [LevelOrder L]

/-- **Weak-Head Normal-Form Existence for Typed Terms in `LevelTower`**
(re-exported from `Typed.whnf_exists` in
`ParameterizedPiSigmaId.TypedEquality.Normalization.WeakHeadNormalization`):
Every well-typed term `Typed (LevelTower.rules L) Γ t A` in a formed context `Γ`
reduces to a weak-head normal form. -/
theorem tower_typed_whnf_exists {n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {t A : Tm (LevelTower.Head L) n}
    (hTyped : Typed (LevelTower.rules L) Γ t A)
    (hFormed : CtxFormed (LevelTower.rules L) Γ) :
    ∃ nf, WhRed (LevelTower.rules L) roles t nf ∧ Whnf (LevelTower.rules L) roles nf :=
  Typed.whnf_exists (S := setting fun _ => (LevelOrder.bot : L))
    (laws _) (constants _) hTyped hFormed

/-- **Weak-Head Normal-Form Existence for Well-Formed Types in `LevelTower`**
(re-exported from `IsType.whnf_exists` in
`ParameterizedPiSigmaId.TypedEquality.Normalization.WeakHeadNormalization`):
Every well-formed type `IsType (LevelTower.rules L) Γ A` in a formed context `Γ`
reduces to a weak-head normal form. -/
theorem tower_isType_whnf_exists {n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {A : Tm (LevelTower.Head L) n}
    (hType : IsType (LevelTower.rules L) Γ A)
    (hFormed : CtxFormed (LevelTower.rules L) Γ) :
    ∃ B, WhRed (LevelTower.rules L) roles A B ∧ Whnf (LevelTower.rules L) roles B :=
  IsType.whnf_exists (S := setting fun _ => (LevelOrder.bot : L))
    (laws _) (constants _) hType hFormed

/-- **Completeness of Algorithmic Conversion in `LevelTower`**
(re-exported from `TowerModel.complete` in
`ParameterizedPiSigmaId.Instances.TowerDecidability`):
Declarative typed equality `Equal (LevelTower.rules L) Γ t u A` implies
algorithmic conversion `Algorithmic (LevelTower.rules L) roles (.terms Γ t u A)`. -/
theorem tower_algorithmic_complete :
    AlgorithmicComplete (LevelTower.rules L) roles :=
  TowerModel.complete

/-- **Exact Equivalence of `Algorithm` and Declarative `Equal` in `LevelTower`**
(re-exported from `algorithm_iff_equal` in
`ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Completeness`):
For well-typed terms `t, u : A` in a formed context `Γ`, the conversion algorithm
derives `Algorithm (LevelTower.rules L) (.compare Γ t u A)` if and only if
`Equal (LevelTower.rules L) Γ t u A` holds. -/
theorem tower_algorithm_iff_equal {n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {t u A : Tm (LevelTower.Head L) n}
    (hFormed : CtxFormed (LevelTower.rules L) Γ)
    (hTypedT : Typed (LevelTower.rules L) Γ t A)
    (hTypedU : Typed (LevelTower.rules L) Γ u A) :
    Algorithm (LevelTower.rules L) (.compare Γ t u A) ↔
      Equal (LevelTower.rules L) Γ t u A :=
  algorithm_iff_equal (S := setting fun _ => (LevelOrder.bot : L))
    facts roots heads algebra TowerModel.complete hFormed hTypedT hTypedU

/-- **Exact Equivalence of `Algorithm (.types ...)` and Universe-Level Equality**
(re-exported from `algorithm_iff_typeEq` in
`ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Completeness`):
For types `A, B : sort u` in a formed context `Γ`, the type conversion algorithm
derives `Algorithm (LevelTower.rules L) (.types Γ A B)` if and only if
`Equal (LevelTower.rules L) Γ A B (.head u)` holds. -/
theorem tower_algorithm_iff_typeEq {n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {A B : Tm (LevelTower.Head L) n} {u : LevelTower.Head L}
    (hFormed : CtxFormed (LevelTower.rules L) Γ)
    (hu : (LevelTower.rules L).isUniverse u)
    (hTypedA : Typed (LevelTower.rules L) Γ A (.head u))
    (hTypedB : Typed (LevelTower.rules L) Γ B (.head u)) :
    Algorithm (LevelTower.rules L) (.types Γ A B) ↔
      Equal (LevelTower.rules L) Γ A B (.head u) :=
  algorithm_iff_typeEq (S := setting fun _ => (LevelOrder.bot : L))
    facts roots heads algebra TowerModel.complete hFormed hu hTypedA hTypedB

/-- **Soundness of Executable NbE Conversion (`nbeAcceptsConv`) for Declarative `Equal`**:
Whenever `nbeAcceptsConv` accepts `(t, u, A)` on well-typed terms `t, u : A` in a
formed `LevelTower` context, `Equal (LevelTower.rules L) Γ t u A` holds. -/
theorem tower_nbeAcceptsConv_sound [DecidableEq (LevelTower.Head L)]
    [DecidableRel (LevelTower.rules L).headEq]
    [∀ head, Decidable ((LevelTower.rules L).isUniverse head)]
    (root : ExecutableReduction.RootEvaluator (LevelTower.rules L))
    {fuel n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {t u A : Tm (LevelTower.Head L) n}
    (hFormed : CtxFormed (LevelTower.rules L) Γ)
    (hTypedT : Typed (LevelTower.rules L) Γ t A)
    (hTypedU : Typed (LevelTower.rules L) Γ u A)
    (hAccepted : nbeAcceptsConv (LevelTower.rules L) root fuel Γ t u A = true) :
    Equal (LevelTower.rules L) Γ t u A :=
  (tower_algorithm_iff_equal hFormed hTypedT hTypedU).mp
    (nbeAcceptsConv_derivation (LevelTower.rules L) root hAccepted)

/-- **Completeness of Executable NbE Conversion (`nbeAcceptsConv`) for Declarative `Equal`**:
Whenever `Equal (LevelTower.rules L) Γ t u A` holds in a formed context `Γ`,
our closure-based NbE conversion procedure `nbeAcceptsConv` accepts `(t, u, A)`
at some finite fuel. -/
theorem tower_nbeAcceptsConv_complete [DecidableEq (LevelTower.Head L)]
    [DecidableRel (LevelTower.rules L).headEq]
    [∀ head, Decidable ((LevelTower.rules L).isUniverse head)]
    {n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {t u A : Tm (LevelTower.Head L) n}
    (hFormed : CtxFormed (LevelTower.rules L) Γ)
    (hEqual : Equal (LevelTower.rules L) Γ t u A) :
    ∃ fuel, nbeAcceptsConv (LevelTower.rules L) (fun _ => none) fuel Γ t u A = true := by
  have hAlg : Algorithmic (LevelTower.rules L) roles (.terms Γ t u A) :=
    TowerModel.complete hFormed hEqual
  obtain ⟨fuel, c, hComp⟩ :=
    @nbeCompare_complete_of_algorithmic (LevelTower.Head L) _ L _
      (setting fun _ => (LevelOrder.bot : L)) ‹_› ‹_›
      facts roots heads algebra rfl rfl n Γ t u A hFormed hAlg
  exact ⟨fuel, Option.isSome_iff_exists.mpr ⟨c, hComp⟩⟩

/-- **Exact Equivalence of Executable NbE Conversion (`nbeAcceptsConv`) and Declarative `Equal`**:
For well-typed terms `t, u : A` in a formed `LevelTower` context `Γ`,
`Equal (LevelTower.rules L) Γ t u A` holds if and only if our closure-based
NbE conversion procedure `nbeAcceptsConv` accepts `(t, u, A)` at some finite fuel. -/
theorem tower_equal_iff_exists_fuel_nbeAcceptsConv [DecidableEq (LevelTower.Head L)]
    [DecidableRel (LevelTower.rules L).headEq]
    [∀ head, Decidable ((LevelTower.rules L).isUniverse head)]
    {n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {t u A : Tm (LevelTower.Head L) n}
    (hFormed : CtxFormed (LevelTower.rules L) Γ)
    (hTypedT : Typed (LevelTower.rules L) Γ t A)
    (hTypedU : Typed (LevelTower.rules L) Γ u A) :
    Equal (LevelTower.rules L) Γ t u A ↔
      ∃ fuel, nbeAcceptsConv (LevelTower.rules L) (fun _ => none) fuel Γ t u A = true :=
  ⟨tower_nbeAcceptsConv_complete hFormed,
    fun ⟨_, hAcc⟩ => tower_nbeAcceptsConv_sound (fun _ => none) hFormed hTypedT hTypedU hAcc⟩

/-- **Soundness of Executable NbE Type Conversion (`nbeAcceptsTypeConv`) for `TypeEq`**:
Whenever `nbeAcceptsTypeConv` accepts `(A, B)` on well-formed types `A, B` in a
formed `LevelTower` context `Γ`, `TypeEq (LevelTower.rules L) Γ A B` holds. -/
theorem tower_nbeAcceptsTypeConv_sound [DecidableEq (LevelTower.Head L)]
    [DecidableRel (LevelTower.rules L).headEq]
    [∀ head, Decidable ((LevelTower.rules L).isUniverse head)]
    (root : ExecutableReduction.RootEvaluator (LevelTower.rules L))
    {fuel n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {A B : Tm (LevelTower.Head L) n}
    (hFormed : CtxFormed (LevelTower.rules L) Γ)
    (hTypeA : IsType (LevelTower.rules L) Γ A)
    (hTypeB : IsType (LevelTower.rules L) Γ B)
    (hAccepted : nbeAcceptsTypeConv (LevelTower.rules L) root fuel Γ A B = true) :
    TypeEq (LevelTower.rules L) Γ A B := by
  obtain ⟨u, hu, tA⟩ := hTypeA
  obtain ⟨v, hv, tB⟩ := hTypeB
  obtain ⟨w, join⟩ :=
    (setting fun _ => (LevelOrder.bot : L)).levels.join_exists hu hv
  obtain ⟨cu, cv⟩ :=
    (setting fun _ => (LevelOrder.bot : L)).levels.join_upper join
  have hw := ((setting fun _ => (LevelOrder.bot : L)).levels.join_level join).1
  exact ⟨w, hw, (tower_algorithm_iff_typeEq hFormed hw (.cumul tA cu) (.cumul tB cv)).mp
    (nbeAcceptsTypeConv_derivation (LevelTower.rules L) root hAccepted)⟩

/-- **Completeness of Executable NbE Type Conversion (`nbeAcceptsTypeConv`) for `TypeEq`**:
Whenever `TypeEq (LevelTower.rules L) Γ A B` holds in a formed context `Γ`,
our closure-based NbE type conversion procedure `nbeAcceptsTypeConv` accepts `(A, B)`
at some finite fuel. -/
theorem tower_nbeAcceptsTypeConv_complete [DecidableEq (LevelTower.Head L)]
    [DecidableRel (LevelTower.rules L).headEq]
    [∀ head, Decidable ((LevelTower.rules L).isUniverse head)]
    {n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {A B : Tm (LevelTower.Head L) n}
    (hFormed : CtxFormed (LevelTower.rules L) Γ)
    (hTypeEq : TypeEq (LevelTower.rules L) Γ A B) :
    ∃ fuel, nbeAcceptsTypeConv (LevelTower.rules L) (fun _ => none) fuel Γ A B = true := by
  have hAlg : Algorithmic (LevelTower.rules L) roles (.types Γ A B) :=
    AlgorithmicComplete.types (S := setting fun _ => (LevelOrder.bot : L))
      TowerModel.complete hTypeEq hFormed
  obtain ⟨fuel, c, hComp⟩ :=
    @nbeCompareTypes_complete_of_algorithmic (LevelTower.Head L) _ L _
      (setting fun _ => (LevelOrder.bot : L)) ‹_› ‹_›
      facts roots heads algebra rfl rfl n Γ A B hFormed hAlg
  exact ⟨fuel, Option.isSome_iff_exists.mpr ⟨c, hComp⟩⟩

/-- **Exact Equivalence of Executable NbE Type Conversion (`nbeAcceptsTypeConv`) and `TypeEq`**:
For well-formed types `A, B` in a formed `LevelTower` context `Γ`,
`TypeEq (LevelTower.rules L) Γ A B` holds if and only if our closure-based
NbE type conversion procedure `nbeAcceptsTypeConv` accepts `(A, B)` at some finite fuel. -/
theorem tower_typeEq_iff_exists_fuel_nbeAcceptsTypeConv [DecidableEq (LevelTower.Head L)]
    [DecidableRel (LevelTower.rules L).headEq]
    [∀ head, Decidable ((LevelTower.rules L).isUniverse head)]
    {n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {A B : Tm (LevelTower.Head L) n}
    (hFormed : CtxFormed (LevelTower.rules L) Γ)
    (hTypeA : IsType (LevelTower.rules L) Γ A)
    (hTypeB : IsType (LevelTower.rules L) Γ B) :
    TypeEq (LevelTower.rules L) Γ A B ↔
      ∃ fuel, nbeAcceptsTypeConv (LevelTower.rules L) (fun _ => none) fuel Γ A B = true :=
  ⟨tower_nbeAcceptsTypeConv_complete hFormed,
    fun ⟨_, hAcc⟩ => tower_nbeAcceptsTypeConv_sound (fun _ => none) hFormed hTypeA hTypeB hAcc⟩

/-- **Soundness & Completeness Bridge for Untyped `Conv` in `Tower`**:
In `Tower.rules`, untyped conversion `Conv Tower.rules.headEq t u Tower.rules.computation`
between well-typed terms `t, u : A` in a formed context `Γ` implies both declarative
`Equal Tower.rules Γ t u A` and algorithmic conversion `Algorithm Tower.rules (.compare Γ t u A)`. -/
theorem tower_conv_implies_equal_and_algorithm {n : Nat} {Γ : Ctx Tower.Head n}
    {t u A : Tm Tower.Head n}
    (hFormed : CtxFormed Tower.rules Γ)
    (hTypedT : Typed Tower.rules Γ t A)
    (hTypedU : Typed Tower.rules Γ u A)
    (hConv : Conv Tower.rules.headEq t u Tower.rules.computation) :
    Equal Tower.rules Γ t u A ∧ Algorithm Tower.rules (.compare Γ t u A) := by
  have hEq : Equal Tower.rules Γ t u A :=
    Tower.conv_toEqual hFormed hConv hTypedT hTypedU
  exact ⟨hEq, (tower_algorithm_iff_equal hFormed hTypedT hTypedU).mpr hEq⟩

/-- **Decidability of Declarative Typed Equality in `LevelTower`**
(re-exported from `LevelTower.equal_decide` in
`ParameterizedPiSigmaId.Instances.TowerDecidability`):
Between any two well-typed terms `t, u : A` in a formed context `Γ`,
`Equal (LevelTower.rules L) Γ t u A` is decidable. -/
theorem tower_equal_decide {n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {t u A : Tm (LevelTower.Head L) n}
    (hFormed : CtxFormed (LevelTower.rules L) Γ)
    (hTypedT : Typed (LevelTower.rules L) Γ t A)
    (hTypedU : Typed (LevelTower.rules L) Γ u A) :
    Equal (LevelTower.rules L) Γ t u A ∨ ¬ Equal (LevelTower.rules L) Γ t u A :=
  LevelTower.equal_decide hFormed hTypedT hTypedU

/-- **Decidability of Declarative Type Equality in `LevelTower`**
(re-exported from `LevelTower.typeEq_decide` in
`ParameterizedPiSigmaId.Instances.TowerDecidability`):
Between any two well-formed types `A, B` in a formed context `Γ`,
`TypeEq (LevelTower.rules L) Γ A B` is decidable. -/
theorem tower_typeEq_decide {n : Nat} {Γ : Ctx (LevelTower.Head L) n}
    {A B : Tm (LevelTower.Head L) n}
    (hFormed : CtxFormed (LevelTower.rules L) Γ)
    (hTypeA : IsType (LevelTower.rules L) Γ A)
    (hTypeB : IsType (LevelTower.rules L) Γ B) :
    TypeEq (LevelTower.rules L) Γ A B ∨ ¬ TypeEq (LevelTower.rules L) Γ A B :=
  LevelTower.typeEq_decide hFormed hTypeA hTypeB

/-- **Soundness of Untyped NbE Normal-Form Conversion in `Legacy`**:
In the one-universe `Legacy` presentation (`Legacy.rules.headEq = Eq`),
comparing normal forms via `decide (h₁ = h₂)` is sound for `Conv Legacy.HeadEq`. -/
theorem legacy_nbeConvNf_sound {fuel n : Nat} {t u : Legacy.Tm n}
    (hConv : nbeConvNf Legacy.rules (fun _ => none) (fun h₁ h₂ => decide (h₁ = h₂)) fuel t u = true) :
    Conv Legacy.HeadEq t u :=
  nbeConvNf_sound Legacy.rules (fun _ => none)
    (fun _ _ h => .inl (of_decide_eq_true h)) hConv

/-- **Soundness of Untyped NbE Normal-Form Conversion in `Tower`**:
In the cumulative `Tower` presentation, comparing normal forms via `Tower.decideHeadEq`
(deciding level-expression equivalence) is sound for `Conv Tower.HeadEq`. -/
theorem tower_nbeConvNf_sound
    (headEqB : Tower.Head → Tower.Head → Bool)
    (hHead : ∀ h₁ h₂, headEqB h₁ h₂ = true → h₁ = h₂ ∨ Tower.HeadEq h₁ h₂)
    {fuel n : Nat} {t u : Tower.Tm n}
    (hConv : nbeConvNf Tower.rules (fun _ => none) headEqB fuel t u = true) :
    Conv Tower.HeadEq t u :=
  nbeConvNf_sound Tower.rules (fun _ => none) hHead hConv

end TowerNormalizationAndConversion

/-! ## 4. Proof-Theoretic Strength & Axiom Audit

### Proof-Theoretic Strength Analysis
1. **One-Universe Fragment (`Legacy` / `TwoSortPiSigmaId` with `U0 : U1`, `Π`, `Σ`, `Id`)**:
   - In `Legacy`, `u0` is an opaque ground constant (`legacyGround : U 0`) and `u1` (`U 0`)
     is the single universe classifying small types; `U 0` itself has no higher classifier
     inside `Legacy`.
   - Normalization for a single universe closed under $\Pi, \Sigma, \mathrm{Id}$ requires
     constructing one inductive-recursive (or impredicative/large-eliminating) semantic
     interpretation of small types and a top-level interpretation of large types (`U 0`
     and $\Pi/\Sigma$ over `U 0`). In Lean 4's type theory, this lives inside `Type 1`
     using a two-stage reducibility predicate without transfinite universe recursion.

2. **Cumulative Universe Hierarchy (`LevelTower L` / `Tower` with $U_0 : U_1 : U_2 : \dots$)**:
   - In `LevelTower L`, every level $l \in L$ has a classifier $U_{\mathrm{succ}(l)}$,
     and universe levels are closed under $\mathrm{succ}$ and $\max$ with cumulative
     subtyping $U_l \preceq U_{l'}$.
   - By Gödel's second incompleteness theorem, normalizing $\mathrm{MLTT}_{\omega}$ with
     $\omega$ universes cannot be carried out inside $\mathrm{MLTT}_n$ for any fixed $n$;
     its proof-theoretic strength exceeds any finite-universe fragment and requires
     well-founded recursion over the universe level ordering `LevelOrder L` (`WellFounded (<)`
     on `L`, instantiated at `L = Nat` in `Tower`) inside an ambient universe (`Type 1`)
     that quantifies over all object-language levels $l : L$.
   - In `ParameterizedPiSigmaId.TypedEquality.Normalization.LogicalRelation`, the Kripke
     logical relation `LR S l rec Γ A P` is defined for each level `l : L` parameterized
     by `rec : L → RedRel Head` for strictly smaller levels `l' < l`, and tied together
     by `WellFounded.fix` in `Reducible S Γ A P`.

3. **Kernel Axiom Footprint**:
   - The `#print axioms` checks below confirm that all normalization, conversion, and
     decidability theorems use only Lean's standard axioms (`propext`, `Classical.choice`,
     `Quot.sound`), with zero custom `axiom` or `sorry`.
-/

#print axioms nbeNormNf_sound
#print axioms nbeNormNf_conv
#print axioms nbeConvNf_sound
#print axioms nbeAcceptsConv_derivation
#print axioms Algorithmic.executable_complete
#print axioms nbeCompare_complete_of_algorithmic
#print axioms nbeCompareTypes_complete_of_algorithmic
#print axioms tower_typed_whnf_exists
#print axioms tower_isType_whnf_exists
#print axioms tower_algorithmic_complete
#print axioms tower_algorithm_iff_equal
#print axioms tower_nbeAcceptsConv_sound
#print axioms tower_nbeAcceptsConv_complete
#print axioms tower_equal_iff_exists_fuel_nbeAcceptsConv
#print axioms tower_nbeAcceptsTypeConv_complete
#print axioms tower_typeEq_iff_exists_fuel_nbeAcceptsTypeConv
#print axioms tower_conv_implies_equal_and_algorithm
#print axioms tower_equal_decide
#print axioms tower_typeEq_decide

end Mettapedia.TypeTheory.NbE
