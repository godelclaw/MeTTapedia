import Mettapedia.Logic.HOL.Semantics.KripkeHenkin
import Mettapedia.Logic.HOL.Syntax.ConstMap

/-!
# Varying-domain substitutional Kripke semantics

The substitutional `KripkeHenkin` structures quantify over the same closed
terms at every world, so they validate the constant-domain schema
(`ConstantDomain`).  Here the quantifier domain grows with the world.

A structure interprets the formulas of a signature `Const` over the closed
terms of a domain signature `Dom`, through an inclusion of constants.  At each
world only some `Dom`-constants are available; a term is *in the language* of
a world when every constant it contains is available there.  Availability
grows along the preorder and includes every constant of `Const`.  The
disjunction, existential and universal clauses, and functional
extensionality, are required for formulas in the language of the world;
quantifiers range over the closed terms in the language of the world at
which they are evaluated.

Soundness (`sound`) holds for derivations over `Const`: their instantiation
terms are `Const`-terms, which are in every language.  Every substitutional
`KripkeHenkin` structure is a varying-domain structure in which every constant
is available everywhere (`ofKripkeHenkin`).  `KripkeVaryingCanonical` proves
completeness.
-/

namespace Mettapedia.Logic.HOL

universe u v v' w

variable {Base : Type u}

/-- A term is in the language of an availability predicate when every
unavailable constant is absent from it. -/
def InLang {Dom : Ty Base → Type v'} (avail : ∀ {τ : Ty Base}, Dom τ → Prop)
    {Γ : Ctx Base} {τ : Ty Base} (t : Term Dom Γ τ) : Prop :=
  ∀ {σ : Ty Base} (c : Dom σ), ¬ avail c → NoConstOccurrence c t

namespace InLang

variable {Dom : Ty Base → Type v'} {avail : ∀ {τ : Ty Base}, Dom τ → Prop}

theorem mono {avail' : ∀ {τ : Ty Base}, Dom τ → Prop}
    (h : ∀ {τ : Ty Base} {c : Dom τ}, avail c → avail' c)
    {Γ : Ctx Base} {τ : Ty Base} {t : Term Dom Γ τ} (ht : InLang avail t) :
    InLang avail' t :=
  fun c hc => ht c (fun hc' => hc (h hc'))

theorem var {Γ : Ctx Base} {τ : Ty Base} (v : Var Γ τ) :
    InLang avail (.var v : Term Dom Γ τ) :=
  fun _ _ => .var

theorem const {Γ : Ctx Base} {τ : Ty Base} {d : Dom τ} (hd : avail d) :
    InLang avail (.const d : Term Dom Γ τ) := by
  classical
  intro σ c hc
  by_cases hστ : σ = τ
  · subst hστ
    exact .const_same_ne d (fun h => hc (h ▸ hd))
  · exact .const_diff_type hστ d

theorem rename {Γ Δ : Ctx Base} {τ : Ty Base} (r : Rename Base Γ Δ)
    {t : Term Dom Γ τ} (ht : InLang avail t) : InLang avail (HOL.rename r t) :=
  fun c hc => noConstOccurrence_rename r t (ht c hc)

theorem subst {Γ Δ : Ctx Base} {τ : Ty Base} {s : Subst Dom Γ Δ}
    (hs : ∀ {σ : Ty Base} (v : Var Γ σ), InLang avail (s v))
    {t : Term Dom Γ τ} (ht : InLang avail t) : InLang avail (HOL.subst s t) :=
  fun c hc => noConstOccurrence_subst (fun v => hs v c hc) t (ht c hc)

theorem instantiate {σ τ : Ty Base} {t : ClosedTerm Dom σ} {u : Term Dom [σ] τ}
    (ht : InLang avail t) (hu : InLang avail u) :
    InLang avail (HOL.instantiate t u) :=
  fun c hc => noConstOccurrence_instantiate (ht c hc) (hu c hc)

theorem or_left {Γ : Ctx Base} {φ ψ : Formula Dom Γ} (h : InLang avail (.or φ ψ)) :
    InLang avail φ := fun c hc => by cases h c hc with | or h₁ _ => exact h₁

theorem or_right {Γ : Ctx Base} {φ ψ : Formula Dom Γ} (h : InLang avail (.or φ ψ)) :
    InLang avail ψ := fun c hc => by cases h c hc with | or _ h₂ => exact h₂

theorem all_body {Γ : Ctx Base} {σ : Ty Base} {φ : Formula Dom (σ :: Γ)}
    (h : InLang avail (.all φ)) : InLang avail φ :=
  fun c hc => by cases h c hc with | all h₁ => exact h₁

theorem ex_body {Γ : Ctx Base} {σ : Ty Base} {φ : Formula Dom (σ :: Γ)}
    (h : InLang avail (.ex φ)) : InLang avail φ :=
  fun c hc => by cases h c hc with | ex h₁ => exact h₁

/-- The image of a term along a constant map whose constants are available
has no unavailable constant. -/
theorem mapConst {Const : Ty Base → Type v} {incl : ∀ {τ : Ty Base}, Const τ → Dom τ}
    (hincl : ∀ {τ : Ty Base} (c : Const τ), avail (incl c)) :
    ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ), InLang avail (HOL.mapConst incl t)
  | _, _, .var v => InLang.var v
  | _, _, .const d => InLang.const (hincl d)
  | _, _, .app f t => fun c hc => .app (mapConst hincl f c hc) (mapConst hincl t c hc)
  | _, _, .lam t => fun c hc => .lam (mapConst hincl t c hc)
  | _, _, .top => fun _ _ => .top
  | _, _, .bot => fun _ _ => .bot
  | _, _, .and φ ψ => fun c hc => .and (mapConst hincl φ c hc) (mapConst hincl ψ c hc)
  | _, _, .or φ ψ => fun c hc => .or (mapConst hincl φ c hc) (mapConst hincl ψ c hc)
  | _, _, .imp φ ψ => fun c hc => .imp (mapConst hincl φ c hc) (mapConst hincl ψ c hc)
  | _, _, .not φ => fun c hc => .not (mapConst hincl φ c hc)
  | _, _, .eq t u => fun c hc => .eq (mapConst hincl t c hc) (mapConst hincl u c hc)
  | _, _, .all φ => fun c hc => .all (mapConst hincl φ c hc)
  | _, _, .ex φ => fun c hc => .ex (mapConst hincl φ c hc)

/-- The image of a term along a constant map whose constants are available is
in the language, once its variables are closed by terms in the language. -/
theorem subst_mapConst {Const : Ty Base → Type v} {incl : ∀ {τ : Ty Base}, Const τ → Dom τ}
    (hincl : ∀ {τ : Ty Base} (c : Const τ), avail (incl c))
    {Γ Δ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) {s : Subst Dom Γ Δ}
    (hs : ∀ {σ : Ty Base} (v : Var Γ σ), InLang avail (s v)) :
    InLang avail (HOL.subst s (HOL.mapConst incl t)) :=
  InLang.subst hs (InLang.mapConst hincl t)

end InLang

/-- A varying-domain substitutional Kripke structure for the formulas of
`Const`, with domain elements drawn from the closed terms of `Dom`. -/
structure KripkeVarying (Base : Type u) (Const : Ty Base → Type v) where
  Dom : Ty Base → Type v
  incl : ∀ {τ : Ty Base}, Const τ → Dom τ
  World : Type w
  le : World → World → Prop
  le_refl : ∀ W, le W W
  le_trans : ∀ {U V W}, le U V → le V W → le U W
  avail : World → ∀ {τ : Ty Base}, Dom τ → Prop
  avail_mono : ∀ {U V : World} {τ : Ty Base} {c : Dom τ}, le U V → avail U c → avail V c
  avail_incl : ∀ (W : World) {τ : Ty Base} (c : Const τ), avail W (incl c)
  forces : World → ClosedFormula Dom → Prop
  eqVal : {τ : Ty Base} → World → ClosedTerm Dom τ → ClosedTerm Dom τ → Prop
  forces_mono : ∀ {U V : World} {φ : ClosedFormula Dom}, le U V → forces U φ → forces V φ
  forces_top : ∀ {W : World}, forces W .top
  forces_bot : ∀ {W : World}, ¬ forces W .bot
  forces_and : ∀ {W : World} {φ ψ : ClosedFormula Dom},
    forces W (.and φ ψ) ↔ forces W φ ∧ forces W ψ
  forces_or : ∀ {W : World} {φ ψ : ClosedFormula Dom}, InLang (avail W) (.or φ ψ) →
    (forces W (.or φ ψ) ↔ forces W φ ∨ forces W ψ)
  forces_imp : ∀ {W : World} {φ ψ : ClosedFormula Dom},
    forces W (.imp φ ψ) ↔ ∀ V, le W V → forces V φ → forces V ψ
  forces_not : ∀ {W : World} {φ : ClosedFormula Dom},
    forces W (.not φ) ↔ ∀ V, le W V → ¬ forces V φ
  forces_eq : ∀ {W : World} {τ : Ty Base} {s t : ClosedTerm Dom τ},
    forces W (.eq s t) ↔ eqVal W s t
  eq_refl : ∀ {τ : Ty Base} (W : World) (t : ClosedTerm Dom τ), eqVal W t t
  eq_symm : ∀ {τ : Ty Base} {W : World} {s t : ClosedTerm Dom τ}, eqVal W s t → eqVal W t s
  eq_trans : ∀ {τ : Ty Base} {W : World} {r s t : ClosedTerm Dom τ},
    eqVal W r s → eqVal W s t → eqVal W r t
  eq_app_congr : ∀ {σ τ : Ty Base} {W : World}
      {f g : ClosedTerm Dom (σ ⇒ τ)} {s t : ClosedTerm Dom σ},
    eqVal W f g → eqVal W s t → eqVal W (.app f s) (.app g t)
  eq_funext : ∀ {σ τ : Ty Base} {W : World} {f g : ClosedTerm Dom (σ ⇒ τ)},
    InLang (avail W) f → InLang (avail W) g →
      (∀ V, le W V → ∀ t : ClosedTerm Dom σ, InLang (avail V) t →
        eqVal V (.app f t) (.app g t)) → eqVal W f g
  eq_beta : ∀ {σ τ : Ty Base} {W : World} (t : ClosedTerm Dom σ) (u : Term Dom [σ] τ),
    eqVal W (.app (.lam u) t) (instantiate t u)
  eq_eta : ∀ {σ τ : Ty Base} {W : World} (f : ClosedTerm Dom (σ ⇒ τ)),
    eqVal W (.lam (.app (weaken (σ := σ) f) (.var .vz))) f
  eq_prop_intro : ∀ {W : World} {p q : ClosedFormula Dom},
    forces W (.imp p q) → forces W (.imp q p) → eqVal W p q
  eq_prop_elim_left : ∀ {W : World} {p q : ClosedFormula Dom},
    eqVal W p q → forces W (.imp p q)
  eq_prop_elim_right : ∀ {W : World} {p q : ClosedFormula Dom},
    eqVal W p q → forces W (.imp q p)
  forces_all : ∀ {W : World} {σ : Ty Base} {φ : Formula Dom [σ]}, InLang (avail W) (.all φ) →
    (forces W (.all φ) ↔
      ∀ V, le W V → ∀ t : ClosedTerm Dom σ, InLang (avail V) t → forces V (instantiate t φ))
  forces_ex : ∀ {W : World} {σ : Ty Base} {φ : Formula Dom [σ]}, InLang (avail W) (.ex φ) →
    (forces W (.ex φ) ↔
      ∃ t : ClosedTerm Dom σ, InLang (avail W) t ∧ forces W (instantiate t φ))

namespace KripkeVarying

variable {Const : Ty Base → Type v}
variable (M : KripkeVarying.{u, v, w} Base Const)

/-- The interpretation of an open `Const`-term under a closing substitution
into the domain. -/
abbrev interp {Γ : Ctx Base} {τ : Ty Base} (ρ : Subst M.Dom Γ []) (t : Term Const Γ τ) :
    ClosedTerm M.Dom τ :=
  subst ρ (mapConst M.incl t)

/-- A closing substitution is admissible at a world when its terms are in the
language of the world. -/
def AdmSubst {Γ : Ctx Base} (W : M.World) (ρ : Subst M.Dom Γ []) : Prop :=
  ∀ {σ : Ty Base} (v : Var Γ σ), InLang (M.avail W) (ρ v)

variable {M}

theorem inLang_mono {W V : M.World} (hWV : M.le W V) {Γ : Ctx Base} {τ : Ty Base}
    {t : Term M.Dom Γ τ} (ht : InLang (M.avail W) t) : InLang (M.avail V) t :=
  InLang.mono (fun hc => M.avail_mono hWV hc) ht

theorem admSubst_mono {W V : M.World} (hWV : M.le W V) {Γ : Ctx Base}
    {ρ : Subst M.Dom Γ []} (hρ : M.AdmSubst W ρ) : M.AdmSubst V ρ :=
  fun v => inLang_mono hWV (hρ v)

theorem admSubst_extend {W : M.World} {Γ : Ctx Base} {σ : Ty Base}
    {ρ : Subst M.Dom Γ []} (hρ : M.AdmSubst W ρ) {t : ClosedTerm M.Dom σ}
    (ht : InLang (M.avail W) t) :
    M.AdmSubst W (KripkeHenkin.ClosedEnv.extend (Base := Base) (Const := M.Dom) ρ t) := by
  intro τ v
  cases v with
  | vz => exact ht
  | vs v => exact hρ v

theorem inLang_interp {W : M.World} {Γ : Ctx Base} {τ : Ty Base}
    {ρ : Subst M.Dom Γ []} (hρ : M.AdmSubst W ρ) (t : Term Const Γ τ) :
    InLang (M.avail W) (M.interp ρ t) :=
  InLang.subst_mapConst (fun c => M.avail_incl W c) t hρ

theorem instantiate_lift_interp {Γ : Ctx Base} {σ τ : Ty Base}
    (ρ : Subst M.Dom Γ []) (t : ClosedTerm M.Dom σ) (u : Term Const (σ :: Γ) τ) :
    instantiate t (subst (Subst.lift ρ) (mapConst M.incl u)) =
      M.interp (KripkeHenkin.ClosedEnv.extend (Base := Base) (Const := M.Dom) ρ t) u :=
  KripkeHenkin.ClosedEnv.instantiate_subst_lift_extend ρ t _

theorem interp_instantiate {Γ : Ctx Base} {σ τ : Ty Base}
    (ρ : Subst M.Dom Γ []) (t : Term Const Γ σ) (u : Term Const (σ :: Γ) τ) :
    M.interp ρ (instantiate t u) =
      instantiate (M.interp ρ t) (subst (Subst.lift ρ) (mapConst M.incl u)) := by
  rw [interp, mapConst_instantiate]
  exact KripkeHenkin.ClosedEnv.subst_instantiate_lift ρ _ _

theorem interp_weaken_extend {Γ : Ctx Base} {σ τ : Ty Base}
    (ρ : Subst M.Dom Γ []) (t : ClosedTerm M.Dom σ) (ψ : Term Const Γ τ) :
    M.interp (KripkeHenkin.ClosedEnv.extend (Base := Base) (Const := M.Dom) ρ t)
        (weaken (σ := σ) ψ) = M.interp ρ ψ := by
  rw [interp, mapConst_weaken]
  unfold weaken
  rw [subst_rename]
  rfl

/-- All hypotheses are forced. -/
def ForcesHyps {Γ : Ctx Base} (W : M.World) (ρ : Subst M.Dom Γ [])
    (Δ : List (Formula Const Γ)) : Prop :=
  ∀ ψ ∈ Δ, M.forces W (M.interp ρ ψ)

theorem forcesHyps_mono {W V : M.World} (hWV : M.le W V) {Γ : Ctx Base}
    {ρ : Subst M.Dom Γ []} {Δ : List (Formula Const Γ)} (h : ForcesHyps W ρ Δ) :
    ForcesHyps V ρ Δ :=
  fun ψ hψ => M.forces_mono hWV (h ψ hψ)

theorem forcesHyps_cons {W : M.World} {Γ : Ctx Base} {ρ : Subst M.Dom Γ []}
    {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} (hφ : M.forces W (M.interp ρ φ))
    (h : ForcesHyps W ρ Δ) : ForcesHyps W ρ (φ :: Δ) := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact hφ
  · exact h ψ hψ

theorem forcesHyps_weaken_extend {W : M.World} {Γ : Ctx Base} {σ : Ty Base}
    {ρ : Subst M.Dom Γ []} {Δ : List (Formula Const Γ)} (h : ForcesHyps W ρ Δ)
    (t : ClosedTerm M.Dom σ) :
    ForcesHyps W (KripkeHenkin.ClosedEnv.extend (Base := Base) (Const := M.Dom) ρ t)
      (weakenHyps (σ := σ) Δ) := by
  intro φ hφ
  rcases List.mem_map.mp hφ with ⟨ψ, hψ, rfl⟩
  rw [interp_weaken_extend]
  exact h ψ hψ

theorem inLang_interp_or {W : M.World} {Γ : Ctx Base} {ρ : Subst M.Dom Γ []}
    (hρ : M.AdmSubst W ρ) (φ ψ : Formula Const Γ) :
    InLang (M.avail W) (Term.or (M.interp ρ φ) (M.interp ρ ψ)) :=
  inLang_interp hρ (.or φ ψ)

theorem inLang_interp_all {W : M.World} {Γ : Ctx Base} {σ : Ty Base}
    {ρ : Subst M.Dom Γ []} (hρ : M.AdmSubst W ρ) (φ : Formula Const (σ :: Γ)) :
    InLang (M.avail W) (Term.all (subst (Subst.lift ρ) (mapConst M.incl φ))) :=
  inLang_interp hρ (.all φ)

theorem inLang_interp_ex {W : M.World} {Γ : Ctx Base} {σ : Ty Base}
    {ρ : Subst M.Dom Γ []} (hρ : M.AdmSubst W ρ) (φ : Formula Const (σ :: Γ)) :
    InLang (M.avail W) (Term.ex (subst (Subst.lift ρ) (mapConst M.incl φ))) :=
  inLang_interp hρ (.ex φ)

theorem inLang_interp_lam {W : M.World} {Γ : Ctx Base} {σ τ : Ty Base}
    {ρ : Subst M.Dom Γ []} (hρ : M.AdmSubst W ρ) (t : Term Const (σ :: Γ) τ) :
    InLang (M.avail W) (Term.lam (subst (Subst.lift ρ) (mapConst M.incl t))) :=
  inLang_interp hρ (.lam t)

/-- **Soundness** of the EM-free extensional calculus over `Const` for every
varying-domain structure, under every closing substitution in the language of
the world. -/
theorem sound {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (d : ExtDerivation Const Δ φ) :
    ∀ {M : KripkeVarying.{u, v, w} Base Const} {W : M.World} {ρ : Subst M.Dom Γ []},
      M.AdmSubst W ρ → ForcesHyps W ρ Δ → M.forces W (M.interp ρ φ) := by
  induction d with
  | hyp hmem =>
      intro M W ρ _ hΔ
      exact hΔ _ hmem
  | topI =>
      intro M W ρ _ _
      exact M.forces_top
  | botE h ih =>
      intro M W ρ hρ hΔ
      exact (M.forces_bot (ih hρ hΔ)).elim
  | andI hφ hψ ihφ ihψ =>
      intro M W ρ hρ hΔ
      exact M.forces_and.mpr ⟨ihφ hρ hΔ, ihψ hρ hΔ⟩
  | andEL h ih =>
      intro M W ρ hρ hΔ
      exact (M.forces_and.mp (ih hρ hΔ)).1
  | andER h ih =>
      intro M W ρ hρ hΔ
      exact (M.forces_and.mp (ih hρ hΔ)).2
  | @orIL Γ' Δ' φ' ψ' h ih =>
      intro M W ρ hρ hΔ
      exact (M.forces_or (inLang_interp_or hρ φ' ψ')).mpr (.inl (ih hρ hΔ))
  | @orIR Γ' Δ' φ' ψ' h ih =>
      intro M W ρ hρ hΔ
      exact (M.forces_or (inLang_interp_or hρ φ' ψ')).mpr (.inr (ih hρ hΔ))
  | @orE Γ' Δ' φ' ψ' χ' hor hφ hψ ihor ihφ ihψ =>
      intro M W ρ hρ hΔ
      rcases (M.forces_or (inLang_interp_or hρ φ' ψ')).mp (ihor hρ hΔ) with h | h
      · exact ihφ hρ (forcesHyps_cons h hΔ)
      · exact ihψ hρ (forcesHyps_cons h hΔ)
  | impI h ih =>
      intro M W ρ hρ hΔ
      exact M.forces_imp.mpr fun V hWV hφ =>
        ih (admSubst_mono hWV hρ) (forcesHyps_cons hφ (forcesHyps_mono hWV hΔ))
  | impE himp hφ ihimp ihφ =>
      intro M W ρ hρ hΔ
      exact M.forces_imp.mp (ihimp hρ hΔ) W (M.le_refl W) (ihφ hρ hΔ)
  | notI h ih =>
      intro M W ρ hρ hΔ
      exact M.forces_not.mpr fun V hWV hφ =>
        M.forces_bot (ih (admSubst_mono hWV hρ) (forcesHyps_cons hφ (forcesHyps_mono hWV hΔ)))
  | notE hnot hφ ihnot ihφ =>
      intro M W ρ hρ hΔ
      exact (M.forces_not.mp (ihnot hρ hΔ) W (M.le_refl W) (ihφ hρ hΔ)).elim
  | @allI Γ' Δ' σ' φ' h ih =>
      intro M W ρ hρ hΔ
      refine (M.forces_all (inLang_interp_all hρ φ')).mpr fun V hWV t ht => ?_
      rw [instantiate_lift_interp]
      exact ih (admSubst_extend (admSubst_mono hWV hρ) ht)
        (forcesHyps_weaken_extend (forcesHyps_mono hWV hΔ) t)
  | @allE Γ' Δ' σ' φ' t h ih =>
      intro M W ρ hρ hΔ
      have hall := (M.forces_all (inLang_interp_all hρ φ')).mp (ih hρ hΔ)
        W (M.le_refl W) (M.interp ρ t) (inLang_interp hρ t)
      rw [interp_instantiate]
      exact hall
  | @exI Γ' Δ' σ' φ' t h ih =>
      intro M W ρ hρ hΔ
      refine (M.forces_ex (inLang_interp_ex hρ φ')).mpr
        ⟨M.interp ρ t, inLang_interp hρ t, ?_⟩
      have hbody := ih hρ hΔ
      rw [interp_instantiate] at hbody
      exact hbody
  | @exE Γ' Δ' σ' φ' ψ' hex hbody ihex ihbody =>
      intro M W ρ hρ hΔ
      obtain ⟨t, ht, htφ⟩ := (M.forces_ex (inLang_interp_ex hρ φ')).mp (ihex hρ hΔ)
      rw [instantiate_lift_interp] at htφ
      have hψ := ihbody (admSubst_extend hρ ht)
        (forcesHyps_cons htφ (forcesHyps_weaken_extend hΔ t))
      rw [interp_weaken_extend] at hψ
      exact hψ
  | eqRefl t =>
      intro M W ρ _ _
      exact M.forces_eq.mpr (M.eq_refl W _)
  | eqSymm h ih =>
      intro M W ρ hρ hΔ
      exact M.forces_eq.mpr (M.eq_symm (M.forces_eq.mp (ih hρ hΔ)))
  | eqTrans htu huv ihtu ihuv =>
      intro M W ρ hρ hΔ
      exact M.forces_eq.mpr
        (M.eq_trans (M.forces_eq.mp (ihtu hρ hΔ)) (M.forces_eq.mp (ihuv hρ hΔ)))
  | eqPropI hpq hqp ihpq ihqp =>
      intro M W ρ hρ hΔ
      exact M.forces_eq.mpr (M.eq_prop_intro (ihpq hρ hΔ) (ihqp hρ hΔ))
  | eqPropEL hpq ihpq =>
      intro M W ρ hρ hΔ
      exact M.eq_prop_elim_left (M.forces_eq.mp (ihpq hρ hΔ))
  | eqPropER hpq ihpq =>
      intro M W ρ hρ hΔ
      exact M.eq_prop_elim_right (M.forces_eq.mp (ihpq hρ hΔ))
  | eqApp t h ih =>
      intro M W ρ hρ hΔ
      exact M.forces_eq.mpr (M.eq_app_congr (M.forces_eq.mp (ih hρ hΔ)) (M.eq_refl W _))
  | eqAppArg f h ih =>
      intro M W ρ hρ hΔ
      exact M.forces_eq.mpr (M.eq_app_congr (M.eq_refl W _) (M.forces_eq.mp (ih hρ hΔ)))
  | @eqLam Γ' Δ' σ' τ' t₁ t₂ h ih =>
      intro M W ρ hρ hΔ
      refine M.forces_eq.mpr (M.eq_funext (inLang_interp_lam hρ t₁)
        (inLang_interp_lam hρ t₂) fun V hWV t ht => ?_)
      have hbody := M.forces_eq.mp
        (ih (admSubst_extend (admSubst_mono hWV hρ) ht)
          (forcesHyps_weaken_extend (forcesHyps_mono hWV hΔ) t))
      refine M.eq_trans (M.eq_beta t _) (M.eq_trans ?_ (M.eq_symm (M.eq_beta t _)))
      rw [instantiate_lift_interp, instantiate_lift_interp]
      exact hbody
  | @funExt Γ' Δ' σ' τ' f g h ih =>
      intro M W ρ hρ hΔ
      refine M.forces_eq.mpr (M.eq_funext (inLang_interp hρ f) (inLang_interp hρ g)
        fun V hWV t ht => ?_)
      have hall := (M.forces_all (inLang_interp_all hρ _)).mp (ih hρ hΔ) V hWV t ht
      rw [instantiate_lift_interp] at hall
      have hshape : M.interp (KripkeHenkin.ClosedEnv.extend (Base := Base) (Const := M.Dom) ρ t)
          (.eq (.app (weaken (σ := σ') f) (.var .vz)) (.app (weaken (σ := σ') g) (.var .vz))) =
          .eq (.app (M.interp ρ f) t) (.app (M.interp ρ g) t) := by
        show Term.eq (Term.app (M.interp _ (weaken (σ := σ') f)) t)
          (Term.app (M.interp _ (weaken (σ := σ') g)) t) = _
        rw [interp_weaken_extend, interp_weaken_extend]
      rw [hshape] at hall
      exact M.forces_eq.mp hall
  | @beta Γ' Δ' σ' τ' t u =>
      intro M W ρ _ _
      refine M.forces_eq.mpr ?_
      have h := M.eq_beta (W := W) (M.interp ρ t) (subst (Subst.lift ρ) (mapConst M.incl u))
      rw [← interp_instantiate] at h
      exact h
  | @eta Γ' Δ' σ' τ' f =>
      intro M W ρ _ _
      refine M.forces_eq.mpr ?_
      have h := M.eq_eta (W := W) (M.interp ρ f)
      have hshape : (Term.lam (Term.app (weaken (σ := σ') (M.interp ρ f)) (.var .vz)) :
            ClosedTerm M.Dom (σ' ⇒ τ')) =
          M.interp ρ (.lam (.app (weaken (σ := σ') f) (.var .vz))) := by
        show _ = Term.lam (Term.app (subst (Subst.lift ρ) (mapConst M.incl (weaken f)))
          (.var .vz))
        rw [mapConst_weaken, subst_weaken]
      rw [hshape] at h
      exact h

/-- Semantic consequence over the varying-domain class. -/
def Consequence (T : ClosedTheorySet Const) (θ : ClosedFormula Const) : Prop :=
  ∀ (M : KripkeVarying.{u, v, w} Base Const) (W : M.World),
    (∀ ψ ∈ T, M.forces W (mapConst M.incl ψ)) → M.forces W (mapConst M.incl θ)

theorem interp_empty (M : KripkeVarying.{u, v, w} Base Const)
    (ρ : Subst M.Dom [] []) (φ : ClosedFormula Const) :
    M.interp ρ φ = mapConst M.incl φ :=
  KripkeHenkin.ClosedEnv.subst_empty (Base := Base) (Const := M.Dom) ρ _

/-- Derivability implies consequence over the varying-domain class. -/
theorem consequence_of_provable {T : ClosedTheorySet Const} {θ : ClosedFormula Const}
    (h : ClosedTheorySet.Provable (Const := Const) T θ) :
    Consequence.{u, v, w} T θ := by
  intro M W hT
  obtain ⟨Γ, hΓ, d⟩ := h
  have hs := sound d (M := M) (W := W) (ρ := fun v => nomatch v)
    (fun v => nomatch v)
    (fun ψ hψ => by rw [interp_empty]; exact hT ψ (hΓ ψ hψ))
  rw [interp_empty] at hs
  exact hs

/-! ## Substitutional Kripke-Henkin structures are varying-domain structures -/

/-- A substitutional Kripke-Henkin structure, with every constant available at
every world. -/
def ofKripkeHenkin (K : KripkeHenkin.{u, v, w} Base Const) :
    KripkeVarying.{u, v, w} Base Const where
  Dom := Const
  incl := fun c => c
  World := K.World
  le := K.le
  le_refl := K.le_refl
  le_trans := K.le_trans
  avail := fun _ _ _ => True
  avail_mono := fun _ h => h
  avail_incl := fun _ _ _ => trivial
  forces := K.forces
  eqVal := K.eqVal
  forces_mono := K.forces_mono
  forces_top := K.forces_top
  forces_bot := K.forces_bot
  forces_and := K.forces_and
  forces_or := fun _ => K.forces_or
  forces_imp := K.forces_imp
  forces_not := K.forces_not
  forces_eq := K.forces_eq
  eq_refl := K.eq_refl
  eq_symm := K.eq_symm
  eq_trans := K.eq_trans
  eq_app_congr := K.eq_app_congr
  eq_funext := fun _ _ h => K.eq_funext fun t => h _ (K.le_refl _) t (fun _ hc => (hc trivial).elim)
  eq_beta := K.eq_beta
  eq_eta := K.eq_eta
  eq_prop_intro := K.eq_prop_intro
  eq_prop_elim_left := K.eq_prop_elim_left
  eq_prop_elim_right := K.eq_prop_elim_right
  forces_all := by
    intro W σ φ _
    rw [K.forces_all]
    exact ⟨fun h V hWV t _ => h V hWV t,
      fun h V hWV t => h V hWV t (fun _ hc => (hc trivial).elim)⟩
  forces_ex := by
    intro W σ φ _
    rw [K.forces_ex]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, fun _ hc => (hc trivial).elim, ht W (K.le_refl W)⟩
    · rintro ⟨t, _, ht⟩
      exact ⟨t, fun V hWV => K.forces_mono hWV ht⟩

/-- A consequence over the varying-domain class is a consequence over the
substitutional class. -/
theorem kripkeHenkin_consequence_of_consequence {T : ClosedTheorySet Const}
    {θ : ClosedFormula Const} (h : Consequence.{u, v, w} T θ) :
    KripkeHenkin.Consequence.{u, v, w} T θ := by
  intro K W hT
  have hθ := h (ofKripkeHenkin K) W (fun ψ hψ => by
    show K.forces W (mapConst (fun c => c) ψ)
    rw [mapConst_id]
    exact hT hψ)
  change K.forces W (mapConst (fun c => c) θ) at hθ
  rw [mapConst_id] at hθ
  exact hθ


end KripkeVarying

end Mettapedia.Logic.HOL
