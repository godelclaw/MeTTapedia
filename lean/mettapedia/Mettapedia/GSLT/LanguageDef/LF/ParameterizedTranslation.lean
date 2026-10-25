import Mettapedia.GSLT.LanguageDef.LF.ProfileChecker
import Mettapedia.GSLT.Dedukti.Metatheory
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralLaws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationSignature
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-!
# LF in every parameterized Π/Σ/identity package that realizes its sorts

The framework of a proof system presented in LF is the λΠ-calculus over the
signature of the system.  This module interprets it in the parameterized
dependent calculus `TypeTheory.Calculi.ParameterizedPiSigmaId`, whose packages
share one grammar and one typing judgment and differ in their universe heads,
declared constants and computation.  A package with a dependent product and
declared constants is enough; no package-specific reasoning is used.

* `ProfileRealization profile R`: the heads of the package `R` realize the LF
  profile.  Each LF sort is a universe head, the sort axiom is a head typing,
  and each product rule is a join followed by a cumulative step.
* `translate`: an LF term at depth `n` becomes a package term in scope `n`, by
  structural recursion.  Sorts go to their heads, constants to declared
  constants, and abstraction drops its domain annotation.
* The translation commutes with the de Bruijn operations of LF: lifting
  (`translate_lift`), substitution (`translate_subst`, `translate_subst0`),
  context lookup (`translate_ctxLookup`) and closed weakening
  (`translate_liftClosed`).
* **Typing is preserved** (`typed`): a conversion-free LF derivation over a
  signature whose constants the package declares at their translated types is
  sent to a derivation of the package's typing judgment.
* **The cumulative tower** (the heads of `CumulativePiSigmaId`) realizes
  `standardLF` with `type` at level zero and `kind` at level one
  (`towerRealization`).  Every LF signature with closed declared types becomes
  a declaration package over the tower (`towerSignature`), and every LF
  derivation over it is typed there (`tower_typed`).
* **Negative control**: the sealed legacy heads, which re-present the two-sort
  calculus, realize no LF profile with the `type : kind` axiom: only the marker
  is a universe and no head types it (`legacy_no_realization`).  So families
  into types are the obstruction, as the two-sort calculus shows.

The translation forgets the domains of abstractions.  It is therefore a
statement about the image of LF in the package; whether the package proves
more inhabitants of translated types than the signature does is the separate
question of conservativity on the image (`Logic.InstitutionBorrowing`
`TheoryRoute.conservative_comp_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.LFParameterizedTranslation

open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule standardLF typeAxiom
  typeTypeType typeKindKind)
open Mettapedia.GSLT.LanguageDef.LFProfileChecker (Deriv)
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

variable {Head : Type}

/-! ## Realizing an LF profile by universe heads -/

/-- The heads of a package realize an LF profile: every LF sort is a universe,
the sort axiom is a head typing, and every product rule is a join followed by
a cumulative step. -/
structure ProfileRealization (profile : Profile) (R : Rules Head) where
  sort : Srt → Head
  sort_isUniverse : ∀ s, R.isUniverse (sort s)
  sort_axiom : ∀ {source target : Srt}, profile.sortAxiom source = some target →
    R.headTyping (sort source) (sort target)
  product : ∀ rule ∈ profile.products, ∃ joined,
    R.join (sort rule.domain) (sort rule.codomain) joined ∧
      R.cumulative joined (sort rule.result)

/-- A declaration package keeps the heads of its base, so it keeps every
realization. -/
def ProfileRealization.extend {profile : Profile} {base : Rules Head}
    (realization : ProfileRealization profile base) (signature : Declaration.Signature Head) :
    ProfileRealization profile (Declaration.extendRules base signature) where
  sort := realization.sort
  sort_isUniverse := realization.sort_isUniverse
  sort_axiom := realization.sort_axiom
  product := realization.product

/-! ## The translation -/

section Translation

variable (sort : Srt → Head) (names : String → DeclName)

/-- An LF term at depth `n` as a package term in scope `n`. -/
def translate : (n : Nat) → Term → Option (Tm Head n)
  | _, .srt s => some (.head (sort s))
  | _, .con c => some (.const (names c))
  | n, .var i => if h : i < n then some (.var ⟨i, h⟩) else none
  | n, .pi A B =>
      (translate n A).bind fun A' => (translate (n + 1) B).map fun B' => .pi A' B'
  | n, .lam _ body => (translate (n + 1) body).map .lam
  | n, .app f a =>
      (translate n f).bind fun f' => (translate n a).map fun a' => .app f' a'

/-- An LF context as a package telescope: its head is the innermost entry. -/
def translateCtx : (Γ : LFTyping.Ctx) → Option (Ctx Head Γ.length)
  | [] => some .nil
  | A :: Γ => (translateCtx Γ).bind fun Γ' => (translate sort names Γ.length A).map (.snoc Γ')

end Translation

section Lemmas

variable {sort : Srt → Head} {names : String → DeclName}

theorem translate_var_of_lt {n i : Nat} (h : i < n) :
    translate sort names n (.var i) = some (.var ⟨i, h⟩) := by
  simp [translate, h]

theorem translate_var_eq_some {n i : Nat} {t : Tm Head n} :
    translate sort names n (.var i) = some t ↔ ∃ h : i < n, t = .var ⟨i, h⟩ := by
  by_cases h : i < n
  · simp [translate, h, eq_comm]
  · simp [translate, h]

theorem translate_pi_eq_some {n : Nat} {A B : Term} {t : Tm Head n} :
    translate sort names n (.pi A B) = some t ↔
      ∃ A' B', translate sort names n A = some A' ∧
        translate sort names (n + 1) B = some B' ∧ t = .pi A' B' := by
  simp only [translate, Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨A', hA, B', hB, rfl⟩
    exact ⟨A', B', hA, hB, rfl⟩
  · rintro ⟨A', B', hA, hB, rfl⟩
    exact ⟨A', hA, B', hB, rfl⟩

theorem translate_lam_eq_some {n : Nat} {A body : Term} {t : Tm Head n} :
    translate sort names n (.lam A body) = some t ↔
      ∃ body', translate sort names (n + 1) body = some body' ∧ t = .lam body' := by
  simp only [translate, Option.map_eq_some_iff]
  constructor
  · rintro ⟨body', h, rfl⟩
    exact ⟨body', h, rfl⟩
  · rintro ⟨body', h, rfl⟩
    exact ⟨body', h, rfl⟩

theorem translate_app_eq_some {n : Nat} {f a : Term} {t : Tm Head n} :
    translate sort names n (.app f a) = some t ↔
      ∃ f' a', translate sort names n f = some f' ∧
        translate sort names n a = some a' ∧ t = .app f' a' := by
  simp only [translate, Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨f', hf, a', ha, rfl⟩
    exact ⟨f', a', hf, ha, rfl⟩
  · rintro ⟨f', a', hf, ha, rfl⟩
    exact ⟨f', hf, a', ha, rfl⟩

/-- Well-scoped terms translate. -/
theorem translate_isSome_of_wellScoped {n : Nat} {t : Term} (wellScoped : WellScoped n t) :
    ∃ t', translate sort names n t = some t' := by
  induction wellScoped with
  | srt => exact ⟨_, rfl⟩
  | con => exact ⟨_, rfl⟩
  | var h => exact ⟨_, translate_var_of_lt h⟩
  | pi _ _ ihA ihB =>
      obtain ⟨A', hA⟩ := ihA
      obtain ⟨B', hB⟩ := ihB
      exact ⟨_, translate_pi_eq_some.mpr ⟨A', B', hA, hB, rfl⟩⟩
  | lam _ _ _ ihb =>
      obtain ⟨b', hb⟩ := ihb
      exact ⟨_, translate_lam_eq_some.mpr ⟨b', hb, rfl⟩⟩
  | app _ _ ihf iha =>
      obtain ⟨f', hf⟩ := ihf
      obtain ⟨a', ha⟩ := iha
      exact ⟨_, translate_app_eq_some.mpr ⟨f', a', hf, ha, rfl⟩⟩

/-- **Lifting is renaming.**  An LF lift by `amount` above `cutoff` is the
package renaming that agrees with it on every variable in scope. -/
theorem translate_lift (amount : Nat) :
    ∀ (t : Term) (cutoff : Nat) {n m : Nat} (ρ : Ren n m),
      (∀ i : Fin n, (ρ i).val = if i.val < cutoff then i.val else i.val + amount) →
      ∀ {t' : Tm Head n}, translate sort names n t = some t' →
        translate sort names m (LFTyping.lift amount cutoff t) = some (rename ρ t') := by
  intro t
  induction t with
  | srt s =>
      intro cutoff n m ρ _ t' h
      simp only [translate, Option.some.injEq] at h
      subst h
      rfl
  | con c =>
      intro cutoff n m ρ _ t' h
      simp only [translate, Option.some.injEq] at h
      subst h
      rfl
  | var i =>
      intro cutoff n m ρ agrees t' h
      obtain ⟨hi, rfl⟩ := translate_var_eq_some.mp h
      have image := agrees ⟨i, hi⟩
      simp only at image
      have lifted : LFTyping.lift amount cutoff (.var i) = .var (ρ ⟨i, hi⟩).val := by
        simp only [LFTyping.lift, image]
      rw [lifted, translate_var_of_lt (ρ ⟨i, hi⟩).isLt]
      rfl
  | pi A B ihA ihB =>
      intro cutoff n m ρ agrees t' h
      obtain ⟨A', B', hA, hB, rfl⟩ := translate_pi_eq_some.mp h
      have liftedAgrees : ∀ i : Fin (n + 1), (liftRen ρ i).val =
          if i.val < cutoff + 1 then i.val else i.val + amount := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [liftRen]
        · have image := agrees j
          simp only [liftRen, Fin.cases_succ, Fin.val_succ, image]
          split_ifs <;> omega
      exact translate_pi_eq_some.mpr
        ⟨_, _, ihA cutoff ρ agrees hA, ihB (cutoff + 1) (liftRen ρ) liftedAgrees hB, rfl⟩
  | lam A body _ ihb =>
      intro cutoff n m ρ agrees t' h
      obtain ⟨body', hb, rfl⟩ := translate_lam_eq_some.mp h
      have liftedAgrees : ∀ i : Fin (n + 1), (liftRen ρ i).val =
          if i.val < cutoff + 1 then i.val else i.val + amount := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [liftRen]
        · have image := agrees j
          simp only [liftRen, Fin.cases_succ, Fin.val_succ, image]
          split_ifs <;> omega
      exact translate_lam_eq_some.mpr ⟨_, ihb (cutoff + 1) (liftRen ρ) liftedAgrees hb, rfl⟩
  | app f a ihf iha =>
      intro cutoff n m ρ agrees t' h
      obtain ⟨f', a', hf, ha, rfl⟩ := translate_app_eq_some.mp h
      exact translate_app_eq_some.mpr
        ⟨_, _, ihf cutoff ρ agrees hf, iha cutoff ρ agrees ha, rfl⟩

/-- Lifting by one at cutoff zero is weakening. -/
theorem translate_lift_wk {n : Nat} {t : Term} {t' : Tm Head n}
    (h : translate sort names n t = some t') :
    translate sort names (n + 1) (LFTyping.lift 1 0 t) = some (rename wk t') :=
  translate_lift 1 t 0 wk (fun i => by simp [wk]) h

/-- A closed term translates in every scope to the weakening of its closed
translation. -/
theorem translate_liftClosed {T : Term} {T₀ : Tm Head 0}
    (h : translate sort names 0 T = some T₀) (n : Nat) :
    translate sort names n T = some (liftClosed T₀) := by
  have lifted := translate_lift 0 T 0 (Fin.elim0 : Ren 0 n) (fun i => Fin.elim0 i) h
  rwa [Mettapedia.GSLT.Dedukti.lift_zero] at lifted

/-- The variable case of LF substitution under a binder. -/
theorem subst_var_succ (j k : Nat) (s : Term) :
    LFTyping.subst (j + 1) (LFTyping.lift 1 0 s) (.var (k + 1)) =
      LFTyping.lift 1 0 (LFTyping.subst j s (.var k)) := by
  by_cases same : k = j
  · subst same
    simp [LFTyping.subst]
  · by_cases above : j < k
    · have positive : k - 1 + 1 = k := by omega
      simp [LFTyping.subst, LFTyping.lift, same, above, positive]
    · have notAbove : ¬ j + 1 < k + 1 := by omega
      simp [LFTyping.subst, LFTyping.lift, same, above, notAbove]

/-- **Substitution is substitution.**  An LF substitution is the package
substitution that agrees with it on every variable in scope. -/
theorem translate_subst :
    ∀ (t : Term) (j : Nat) (s : Term) {n m : Nat} (σ : Sub Head n m),
      (∀ i : Fin n, translate sort names m (LFTyping.subst j s (.var i.val)) = some (σ i)) →
      ∀ {t' : Tm Head n}, translate sort names n t = some t' →
        translate sort names m (LFTyping.subst j s t) = some (subst σ t') := by
  intro t
  induction t with
  | srt s =>
      intro j u n m σ _ t' h
      simp only [translate, Option.some.injEq] at h
      subst h
      rfl
  | con c =>
      intro j u n m σ _ t' h
      simp only [translate, Option.some.injEq] at h
      subst h
      rfl
  | var i =>
      intro j u n m σ agrees t' h
      obtain ⟨hi, rfl⟩ := translate_var_eq_some.mp h
      exact agrees ⟨i, hi⟩
  | pi A B ihA ihB =>
      intro j u n m σ agrees t' h
      obtain ⟨A', B', hA, hB, rfl⟩ := translate_pi_eq_some.mp h
      have liftedAgrees : ∀ i : Fin (n + 1),
          translate sort names (m + 1)
            (LFTyping.subst (j + 1) (LFTyping.lift 1 0 u) (.var i.val)) = some (liftSub σ i) := by
        intro i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp [LFTyping.subst, translate]
        · simp only [Fin.val_succ, liftSub_succ]
          rw [subst_var_succ]
          exact translate_lift_wk (agrees k)
      exact translate_pi_eq_some.mpr
        ⟨_, _, ihA j u σ agrees hA, ihB (j + 1) (LFTyping.lift 1 0 u) (liftSub σ) liftedAgrees hB,
          rfl⟩
  | lam A body _ ihb =>
      intro j u n m σ agrees t' h
      obtain ⟨body', hb, rfl⟩ := translate_lam_eq_some.mp h
      have liftedAgrees : ∀ i : Fin (n + 1),
          translate sort names (m + 1)
            (LFTyping.subst (j + 1) (LFTyping.lift 1 0 u) (.var i.val)) = some (liftSub σ i) := by
        intro i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp [LFTyping.subst, translate]
        · simp only [Fin.val_succ, liftSub_succ]
          rw [subst_var_succ]
          exact translate_lift_wk (agrees k)
      exact translate_lam_eq_some.mpr
        ⟨_, ihb (j + 1) (LFTyping.lift 1 0 u) (liftSub σ) liftedAgrees hb, rfl⟩
  | app f a ihf iha =>
      intro j u n m σ agrees t' h
      obtain ⟨f', a', hf, ha, rfl⟩ := translate_app_eq_some.mp h
      exact translate_app_eq_some.mpr
        ⟨_, _, ihf j u σ agrees hf, iha j u σ agrees ha, rfl⟩

/-- **Instantiating the innermost variable.** -/
theorem translate_subst0 {n : Nat} {a B : Term} {a' : Tm Head n} {B' : Tm Head (n + 1)}
    (ha : translate sort names n a = some a') (hB : translate sort names (n + 1) B = some B') :
    translate sort names n (LFTyping.subst0 a B) = some (inst0 a' B') := by
  apply translate_subst B 0 a (Presentation.subst0 a') _ hB
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · simpa [LFTyping.subst] using ha
  · simp [LFTyping.subst, translate]

/-- Context lookup in closed form: crossing `i + 1` binders lifts by `i + 1`. -/
theorem ctxLookupAux_eq :
    ∀ (Γ : LFTyping.Ctx) (depth i : Nat),
      LFTyping.ctxLookupAux depth Γ i = (Γ[i]?).map (LFTyping.lift (depth + i + 1) 0) := by
  intro Γ
  induction Γ with
  | nil => intro depth i; simp [LFTyping.ctxLookupAux]
  | cons A Γ ih =>
      intro depth i
      cases i with
      | zero => rfl
      | succ i =>
          simp only [LFTyping.ctxLookupAux, ih, List.getElem?_cons_succ]
          congr 2
          omega

/-- **Context lookup is lookup in the telescope.** -/
theorem translate_ctxLookup :
    ∀ {Γ : LFTyping.Ctx} {Γ' : Ctx Head Γ.length},
      translateCtx sort names Γ = some Γ' →
      ∀ {i : Nat} {T : Term}, LFTyping.ctxLookup Γ i = some T →
        ∃ h : i < Γ.length, translate sort names Γ.length T = some (Γ'.lookup ⟨i, h⟩) := by
  intro Γ
  induction Γ with
  | nil =>
      intro Γ' _ i T lookup
      simp [LFTyping.ctxLookup, LFTyping.ctxLookupAux] at lookup
  | cons A Γ ih =>
      intro Γ' hΓ i T lookup
      simp only [translateCtx, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hΓ
      obtain ⟨Γ₀, hΓ₀, A', hA, rfl⟩ := hΓ
      rw [LFTyping.ctxLookup, ctxLookupAux_eq] at lookup
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at lookup
          subst lookup
          exact ⟨Nat.succ_pos _, translate_lift_wk hA⟩
      | succ k =>
          simp only [List.getElem?_cons_succ, Option.map_eq_some_iff] at lookup
          obtain ⟨B, hB, rfl⟩ := lookup
          have inner : LFTyping.ctxLookup Γ k = some (LFTyping.lift (k + 1) 0 B) := by
            rw [LFTyping.ctxLookup, ctxLookupAux_eq, hB]
            simp
          obtain ⟨hk, hT⟩ := ih hΓ₀ inner
          refine ⟨Nat.succ_lt_succ hk, ?_⟩
          have merged : LFTyping.lift (0 + (k + 1) + 1) 0 B =
              LFTyping.lift 1 0 (LFTyping.lift (k + 1) 0 B) := by
            rw [Mettapedia.GSLT.Dedukti.lift_lift_same]
            congr 1
            omega
          rw [merged]
          exact translate_lift_wk hT

end Lemmas

/-! ## Typing is preserved -/

/-- **LF typing is preserved in every package that realizes the profile.**
A conversion-free LF derivation over a signature whose constants the package
declares at their translated types becomes a derivation of the package's
typing judgment, in the translated context. -/
theorem typed {profile : Profile} {R : Rules Head} (realization : ProfileRealization profile R)
    (names : String → DeclName) {signature : LFTyping.Sig}
    (constants : ∀ {c : String} {T : Term}, LFTyping.sigT signature c = some T →
      ∃ T₀, translate realization.sort names 0 T = some T₀ ∧
        R.constantType (names c) = some T₀)
    {Γ : LFTyping.Ctx} {t T : Term} (derivation : Deriv profile signature Γ t T) :
    ∀ {Γ' : Ctx Head Γ.length}, translateCtx realization.sort names Γ = some Γ' →
      ∃ t' T', translate realization.sort names Γ.length t = some t' ∧
        translate realization.sort names Γ.length T = some T' ∧ HasType R Γ' t' T' := by
  induction derivation with
  | sort sortAxiom =>
      intro Γ' _
      exact ⟨_, _, rfl, rfl, .headType (realization.sort_axiom sortAxiom)⟩
  | var lookup =>
      intro Γ' hΓ
      obtain ⟨h, hT⟩ := translate_ctxLookup hΓ lookup
      exact ⟨_, _, translate_var_of_lt h, hT, .var _⟩
  | con lookup =>
      intro Γ' _
      obtain ⟨T₀, hT₀, declared⟩ := constants lookup
      exact ⟨_, _, rfl, translate_liftClosed hT₀ _, .const declared⟩
  | @pi context domain body domainSort codomainSort resultSort _ _ member ihDomain ihBody =>
      intro Γ' hΓ
      obtain ⟨A', S, hA, hS, typedA⟩ := ihDomain hΓ
      have hΓA : translateCtx realization.sort names (domain :: context) = some (.snoc Γ' A') := by
        simp [translateCtx, hΓ, hA]
      obtain ⟨B', S', hB, hS', typedB⟩ := ihBody hΓA
      simp only [translate, Option.some.injEq] at hS hS'
      subst hS hS'
      obtain ⟨joined, join, cumulative⟩ := realization.product _ member
      refine ⟨_, _, translate_pi_eq_some.mpr ⟨A', B', hA, hB, rfl⟩, rfl, ?_⟩
      exact .cumul (.piForm typedA (realization.sort_isUniverse _) typedB
        (realization.sort_isUniverse _) join) cumulative
  | @lam context domain body bodyType domainSort codomainSort resultSort _ _ _ _
      ihDomain ihBody _ =>
      intro Γ' hΓ
      obtain ⟨A', _, hA, _, _⟩ := ihDomain hΓ
      have hΓA : translateCtx realization.sort names (domain :: context) = some (.snoc Γ' A') := by
        simp [translateCtx, hΓ, hA]
      obtain ⟨b', B', hb, hB, typedBody⟩ := ihBody hΓA
      exact ⟨_, _, translate_lam_eq_some.mpr ⟨b', hb, rfl⟩,
        translate_pi_eq_some.mpr ⟨A', B', hA, hB, rfl⟩, .lamIntro typedBody⟩
  | @app context function argument domain bodyType _ _ ihFunction ihArgument =>
      intro Γ' hΓ
      obtain ⟨f', P, hf, hP, typedFunction⟩ := ihFunction hΓ
      obtain ⟨a', A', ha, hA, typedArgument⟩ := ihArgument hΓ
      obtain ⟨A'', B', hA'', hB', rfl⟩ := translate_pi_eq_some.mp hP
      rw [hA''] at hA
      cases hA
      exact ⟨_, _, translate_app_eq_some.mpr ⟨f', a', hf, ha, rfl⟩, translate_subst0 ha hB',
        .appElim typedFunction typedArgument⟩

/-- **The formation-sensitive judgment.**  In a package whose declared types are
themselves formed at a universe, as in a formed declaration signature
(`Declaration.Signature.Formed`), LF typing lands in the formation-sensitive
judgment that the cumulative packages use.  LF abstraction carries the
formation of its product, which is what that judgment asks. -/
theorem typedFormation {profile : Profile} {R : Rules Head}
    (realization : ProfileRealization profile R)
    (names : String → DeclName) {signature : LFTyping.Sig}
    (constants : ∀ {c : String} {T : Term}, LFTyping.sigT signature c = some T →
      ∃ T₀, translate realization.sort names 0 T = some T₀ ∧
        R.constantType (names c) = some T₀)
    (constantsFormed : ∀ {name : DeclName} {T₀ : Tm Head 0}, R.constantType name = some T₀ →
      ∃ u, FormationSensitive.Typing R .nil T₀ (.head u) ∧ R.isUniverse u)
    {Γ : LFTyping.Ctx} {t T : Term} (derivation : Deriv profile signature Γ t T) :
    ∀ {Γ' : Ctx Head Γ.length}, translateCtx realization.sort names Γ = some Γ' →
      ∃ t' T', translate realization.sort names Γ.length t = some t' ∧
        translate realization.sort names Γ.length T = some T' ∧
        FormationSensitive.Typing R Γ' t' T' := by
  induction derivation with
  | sort sortAxiom =>
      intro Γ' _
      exact ⟨_, _, rfl, rfl, .headType (realization.sort_axiom sortAxiom)⟩
  | var lookup =>
      intro Γ' hΓ
      obtain ⟨h, hT⟩ := translate_ctxLookup hΓ lookup
      exact ⟨_, _, translate_var_of_lt h, hT, .var _⟩
  | con lookup =>
      intro Γ' _
      obtain ⟨T₀, hT₀, declared⟩ := constants lookup
      obtain ⟨u, formed, isUniverse⟩ := constantsFormed declared
      exact ⟨_, _, rfl, translate_liftClosed hT₀ _, .const declared formed isUniverse⟩
  | @pi context domain body domainSort codomainSort resultSort _ _ member ihDomain ihBody =>
      intro Γ' hΓ
      obtain ⟨A', S, hA, hS, typedA⟩ := ihDomain hΓ
      have hΓA : translateCtx realization.sort names (domain :: context) = some (.snoc Γ' A') := by
        simp [translateCtx, hΓ, hA]
      obtain ⟨B', S', hB, hS', typedB⟩ := ihBody hΓA
      simp only [translate, Option.some.injEq] at hS hS'
      subst hS hS'
      obtain ⟨joined, join, cumulative⟩ := realization.product _ member
      refine ⟨_, _, translate_pi_eq_some.mpr ⟨A', B', hA, hB, rfl⟩, rfl, ?_⟩
      exact .cumul (.piForm typedA (realization.sort_isUniverse _) typedB
        (realization.sort_isUniverse _) join) cumulative
  | @lam context domain body bodyType domainSort codomainSort resultSort _ _ _ member
      ihDomain ihBody ihBodyType =>
      intro Γ' hΓ
      obtain ⟨A', S, hA, hS, typedA⟩ := ihDomain hΓ
      have hΓA : translateCtx realization.sort names (domain :: context) = some (.snoc Γ' A') := by
        simp [translateCtx, hΓ, hA]
      obtain ⟨b', B', hb, hB, typedBody⟩ := ihBody hΓA
      obtain ⟨B'', S', hB'', hS', typedB⟩ := ihBodyType hΓA
      rw [hB] at hB''
      cases hB''
      simp only [translate, Option.some.injEq] at hS hS'
      subst hS hS'
      obtain ⟨joined, join, cumulative⟩ := realization.product _ member
      refine ⟨_, _, translate_lam_eq_some.mpr ⟨b', hb, rfl⟩,
        translate_pi_eq_some.mpr ⟨A', B', hA, hB, rfl⟩, ?_⟩
      exact .lamIntro (.cumul (.piForm typedA (realization.sort_isUniverse _) typedB
        (realization.sort_isUniverse _) join) cumulative) (realization.sort_isUniverse _)
        typedBody
  | @app context function argument domain bodyType _ _ ihFunction ihArgument =>
      intro Γ' hΓ
      obtain ⟨f', P, hf, hP, typedFunction⟩ := ihFunction hΓ
      obtain ⟨a', A', ha, hA, typedArgument⟩ := ihArgument hΓ
      obtain ⟨A'', B', hA'', hB', rfl⟩ := translate_pi_eq_some.mp hP
      rw [hA''] at hA
      cases hA
      exact ⟨_, _, translate_app_eq_some.mpr ⟨f', a', hf, ha, rfl⟩, translate_subst0 ha hB',
        .appElim typedFunction typedArgument⟩

/-! ## The cumulative tower -/

open Mettapedia.TypeTheory.UniverseLevel

/-- `type` at level zero and `kind` at level one. -/
def towerSort : Srt → Tower.Head
  | .type => .sort Tower.zero
  | .kind => .sort (.succ Tower.zero)

/-- **The tower realizes `standardLF`.** -/
def towerRealization : ProfileRealization standardLF Tower.rules where
  sort := towerSort
  sort_isUniverse s := by cases s <;> exact .sort _
  sort_axiom := by
    intro source target sortAxiom
    cases source <;> cases target <;> simp [standardLF, typeAxiom] at sortAxiom
    exact .sort _
  product := by
    intro rule member
    simp only [standardLF, typeTypeType, typeKindKind, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl
    · refine ⟨_, .sorts _ _, fun v => ?_⟩
      simp [LevelExpr.eval, LevelTower.zero]
    · refine ⟨_, .sorts _ _, fun v => ?_⟩
      simp [LevelExpr.eval, LevelTower.zero]

/-- LF constant names as declaration names. -/
def lfName (c : String) : DeclName := .str .anonymous c

/-- **The declaration package of an LF signature over the tower**: every
constant whose declared type translates is declared at its translation. -/
def towerSignature (signature : LFTyping.Sig) : Declaration.Signature Tower.Head where
  entries
    | .str .anonymous c => (LFTyping.sigT signature c).bind fun T =>
        (translate towerSort lfName 0 T).map fun T₀ => { type := T₀ }
    | _ => none

/-- **Every LF derivation over a signature with closed declared types is typed
in its declaration package over the tower.** -/
theorem tower_typed {signature : LFTyping.Sig}
    (closed : ∀ {c : String} {T : Term}, LFTyping.sigT signature c = some T → WellScoped 0 T)
    {Γ : LFTyping.Ctx} {t T : Term} (derivation : Deriv standardLF signature Γ t T)
    {Γ' : Ctx Tower.Head Γ.length} (hΓ : translateCtx towerSort lfName Γ = some Γ') :
    ∃ t' T', translate towerSort lfName Γ.length t = some t' ∧
      translate towerSort lfName Γ.length T = some T' ∧
      HasType (Declaration.extendRules Tower.rules (towerSignature signature)) Γ' t' T' := by
  refine typed (towerRealization.extend (towerSignature signature)) lfName ?_ derivation hΓ
  intro c T lookup
  obtain ⟨T₀, hT₀⟩ := translate_isSome_of_wellScoped (sort := towerSort) (names := lfName)
    (closed lookup)
  refine ⟨T₀, hT₀, ?_⟩
  simp [Declaration.extendRules, Declaration.combinedType, Declaration.Signature.typeOf?,
    towerSignature, lfName, lookup, hT₀]
  rfl

/-! ## Negative control: the sealed legacy heads -/

/-- **The legacy heads realize no LF profile with the `type : kind` axiom**:
only the marker is a universe, and no head types it.  The legacy heads
re-present the two-sort calculus (`Legacy.ofTwoSort`), which therefore has no
families into types. -/
theorem legacy_no_realization (profile : Profile)
    (typeAxiom : profile.sortAxiom .type = some .kind) :
    ¬ Nonempty (ProfileRealization profile Legacy.rules) := by
  rintro ⟨realization⟩
  have typing := realization.sort_axiom typeAxiom
  have typeUniverse := realization.sort_isUniverse .type
  generalize realization.sort .type = typeHead at typing typeUniverse
  generalize realization.sort .kind = kindHead at typing
  cases typeUniverse
  cases typing

#print axioms translate_lift
#print axioms translate_subst0
#print axioms translate_ctxLookup
#print axioms typed
#print axioms typedFormation
#print axioms towerRealization
#print axioms tower_typed
#print axioms legacy_no_realization

end Mettapedia.GSLT.LanguageDef.LFParameterizedTranslation
