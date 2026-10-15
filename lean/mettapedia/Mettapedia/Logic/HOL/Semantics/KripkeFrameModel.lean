import Mettapedia.Logic.HOL.Semantics.KripkeHenkinGeneral

/-!
# The full Kripke-Henkin model over a frame

Every preordered set of worlds, with a carrier for each base type and an
interpretation of the constants, gives a Kripke-Henkin general model. The
admissible values of a type are defined by recursion on the type, not on
formulas: a proposition is admissible when it is upward closed, a function
when it sends admissible values to admissible values and respects the
world-indexed equality. Quantifiers range over all admissible values, so
quantification over propositions and over predicates is impredicative and
needs no recursion through formulas.

`model` is the result. It is sound for the EM-free extensional calculus by
`KripkeHenkinGeneral.sound`. The only condition on the data is that every
constant denotes an admissible value (`constAdm`).

The hand-built countermodels of `ForkedFrameCountermodel` follow this
construction at one fixed frame.
-/

namespace Mettapedia.Logic.HOL

namespace KripkeFrameModel

universe u v x

/-- Worlds under a preorder, and a carrier for each base type. -/
structure Frame (Base : Type u) where
  World : Type x
  le : World → World → Prop
  le_refl : ∀ W, le W W
  le_trans : ∀ {U V W : World}, le U V → le V W → le U W
  Carrier : Base → Type x

variable {Base : Type u}

namespace Frame

variable (F : Frame.{u, x} Base)

/-- Ambient values over the frame. -/
abbrev Val (τ : Ty Base) : Type x := Ty.denoteK F.Carrier F.World τ

mutual

/-- Hereditarily upward-closed and extensional values. -/
def Adm : (τ : Ty Base) → F.Val τ → Prop
  | .prop, S => ∀ {U V : F.World}, F.le U V → S U → S V
  | .base _, _ => True
  | .arr σ τ, f =>
      (∀ d, Adm σ d → Adm τ (f d)) ∧
      (∀ (W : F.World) (d e : F.Val σ), Adm σ d → Adm σ e →
        Eqv W σ d e → Eqv W τ (f d) (f e))

/-- World-indexed observational equality. -/
def Eqv : F.World → (τ : Ty Base) → F.Val τ → F.Val τ → Prop
  | W, .prop, S, T => ∀ V, F.le W V → (S V ↔ T V)
  | _, .base _, d, e => d = e
  | W, .arr σ τ, f, g => ∀ V, F.le W V → ∀ d, Adm σ d → Eqv V τ (f d) (g d)

end

variable {F}

theorem eqv_mono {τ : Ty Base} {U V : F.World} {d e : F.Val τ} (hUV : F.le U V)
    (h : F.Eqv U τ d e) : F.Eqv V τ d e := by
  cases τ with
  | prop => exact fun V' hV' => h V' (F.le_trans hUV hV')
  | base b => exact h
  | arr σ τ => exact fun V' hV' => h V' (F.le_trans hUV hV')

theorem eqv_refl : ∀ {τ : Ty Base} {W : F.World} {d : F.Val τ}, F.Adm τ d → F.Eqv W τ d d
  | .prop, _, _, _ => fun _ _ => Iff.rfl
  | .base _, _, _, _ => rfl
  | .arr _ _, _, _, hf => fun _V _hV d hd => eqv_refl (hf.1 d hd)

theorem eqv_symm : ∀ {τ : Ty Base} {W : F.World} {d e : F.Val τ},
    F.Eqv W τ d e → F.Eqv W τ e d
  | .prop, _, _, _, h => fun V hV => (h V hV).symm
  | .base _, _, _, _, h => h.symm
  | .arr _ _, _, _, _, h => fun V hV d hd => eqv_symm (h V hV d hd)

theorem eqv_trans : ∀ {τ : Ty Base} {W : F.World} {d e k : F.Val τ},
    F.Eqv W τ d e → F.Eqv W τ e k → F.Eqv W τ d k
  | .prop, _, _, _, _, h₁, h₂ => fun V hV => (h₁ V hV).trans (h₂ V hV)
  | .base _, _, _, _, _, h₁, h₂ => h₁.trans h₂
  | .arr _ _, _, _, _, _, h₁, h₂ => fun V hV d hd =>
      eqv_trans (h₁ V hV d hd) (h₂ V hV d hd)

end Frame

variable {Const : Ty Base → Type v} (F : Frame.{u, x} Base)
  (constDen : {τ : Ty Base} → Const τ → F.Val τ)
  (constAdm : ∀ {τ : Ty Base} (c : Const τ), F.Adm τ (constDen c))

/-- The premodel of a frame and an interpretation of the constants. -/
def preModel : KripkePreModel Base Const where
  World := F.World
  le := F.le
  le_refl := F.le_refl
  le_trans := F.le_trans
  Carrier := F.Carrier
  baseEq := fun _ _ d e => d = e
  baseEq_mono := fun _ h => h
  baseEq_refl := fun _ _ _ => rfl
  baseEq_symm := fun h => h.symm
  baseEq_trans := fun h₁ h₂ => h₁.trans h₂
  adm := fun _ τ d => F.Adm τ d
  adm_mono := fun _ h => h
  prop_adm_upset := fun h => h
  base_mem := fun _ _ _ => trivial
  app_mem := fun hf hd => hf.1 _ hd
  constDen := constDen
  const_mem := fun _ {_} c => constAdm c

/-- The model's typed equality is the observational equality of the frame. -/
theorem eqvK_iff_eqv :
    ∀ (τ : Ty Base) (W : F.World) (d e : F.Val τ),
      (preModel F constDen constAdm).EqvK W τ d e ↔ F.Eqv W τ d e
  | .prop, _, _, _ => Iff.rfl
  | .base _, _, _, _ => Iff.rfl
  | .arr σ τ, W, f, g => by
      constructor
      · intro h V hV d hd
        exact (eqvK_iff_eqv τ V (f d) (g d)).mp (h V hV d hd)
      · intro h V hV d hd
        exact (eqvK_iff_eqv τ V (f d) (g d)).mpr (h V hV d hd)

/-- Admissible environments. -/
abbrev EnvAdm {Γ : Ctx Base} (ρ : (preModel F constDen constAdm).Valuation Γ) : Prop :=
  ∀ {σ : Ty Base} (v : Var Γ σ), F.Adm σ (ρ v)

/-- Pointwise observational equality of environments. -/
abbrev EnvEqv {Γ : Ctx Base} (W : F.World)
    (ρ₁ ρ₂ : (preModel F constDen constAdm).Valuation Γ) : Prop :=
  ∀ {σ : Ty Base} (v : Var Γ σ), F.Eqv W σ (ρ₁ v) (ρ₂ v)

theorem envAdm_extend {Γ : Ctx Base} {σ : Ty Base}
    {ρ : (preModel F constDen constAdm).Valuation Γ} {d : F.Val σ}
    (hρ : EnvAdm F constDen constAdm ρ) (hd : F.Adm σ d) :
    EnvAdm F constDen constAdm ((preModel F constDen constAdm).extend ρ d) := by
  intro σ' v
  cases v with
  | vz => exact hd
  | vs v => exact hρ v

theorem envEqv_extend {Γ : Ctx Base} {σ : Ty Base} {W : F.World}
    {ρ₁ ρ₂ : (preModel F constDen constAdm).Valuation Γ} {d e : F.Val σ}
    (hρ : EnvEqv F constDen constAdm W ρ₁ ρ₂) (hde : F.Eqv W σ d e) :
    EnvEqv F constDen constAdm W ((preModel F constDen constAdm).extend ρ₁ d)
      ((preModel F constDen constAdm).extend ρ₂ e) := by
  intro σ' v
  cases v with
  | vz => exact hde
  | vs v => exact hρ v

/-- **The fundamental lemma.** Denotations of terms at admissible
environments are admissible, and observationally equal environments give
observationally equal denotations. -/
theorem fundamental {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    (∀ (ρ : (preModel F constDen constAdm).Valuation Γ), EnvAdm F constDen constAdm ρ →
      F.Adm τ ((preModel F constDen constAdm).denote t ρ)) ∧
    (∀ (W : F.World) (ρ₁ ρ₂ : (preModel F constDen constAdm).Valuation Γ),
      EnvAdm F constDen constAdm ρ₁ → EnvAdm F constDen constAdm ρ₂ →
        EnvEqv F constDen constAdm W ρ₁ ρ₂ →
          F.Eqv W τ ((preModel F constDen constAdm).denote t ρ₁)
            ((preModel F constDen constAdm).denote t ρ₂)) := by
  induction t with
  | var v => exact ⟨fun ρ hρ => hρ v, fun W ρ₁ ρ₂ _ _ hEq => hEq v⟩
  | const c => exact ⟨fun _ _ => constAdm c, fun _ _ _ _ _ _ => Frame.eqv_refl (constAdm c)⟩
  | app f t ihf iht =>
      constructor
      · intro ρ hρ
        exact (ihf.1 ρ hρ).1 _ (iht.1 ρ hρ)
      · intro W ρ₁ ρ₂ h₁ h₂ hEq
        have hff := ihf.2 W ρ₁ ρ₂ h₁ h₂ hEq W (F.le_refl W)
          ((preModel F constDen constAdm).denote t ρ₁) (iht.1 ρ₁ h₁)
        have hresp := (ihf.1 ρ₂ h₂).2 W
          ((preModel F constDen constAdm).denote t ρ₁)
          ((preModel F constDen constAdm).denote t ρ₂)
          (iht.1 ρ₁ h₁) (iht.1 ρ₂ h₂) (iht.2 W ρ₁ ρ₂ h₁ h₂ hEq)
        exact Frame.eqv_trans hff hresp
  | lam t iht =>
      constructor
      · intro ρ hρ
        constructor
        · intro d hd
          exact iht.1 _ (envAdm_extend F constDen constAdm hρ hd)
        · intro W d e hd he hde
          exact iht.2 W _ _ (envAdm_extend F constDen constAdm hρ hd)
            (envAdm_extend F constDen constAdm hρ he)
            (envEqv_extend F constDen constAdm (fun v => Frame.eqv_refl (hρ v)) hde)
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV d hd
        exact iht.2 V _ _ (envAdm_extend F constDen constAdm h₁ hd)
          (envAdm_extend F constDen constAdm h₂ hd)
          (envEqv_extend F constDen constAdm (fun v => Frame.eqv_mono hV (hEq v))
            (Frame.eqv_refl hd))
  | top => exact ⟨fun _ _ _ _ _ h => h, fun _ _ _ _ _ _ _ _ => Iff.rfl⟩
  | bot => exact ⟨fun _ _ _ _ _ h => h, fun _ _ _ _ _ _ _ _ => Iff.rfl⟩
  | and φ ψ ihφ ihψ =>
      constructor
      · intro ρ hρ U V hUV h
        exact ⟨ihφ.1 ρ hρ hUV h.1, ihψ.1 ρ hρ hUV h.2⟩
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        exact and_congr (ihφ.2 W ρ₁ ρ₂ h₁ h₂ hEq V hV) (ihψ.2 W ρ₁ ρ₂ h₁ h₂ hEq V hV)
  | or φ ψ ihφ ihψ =>
      constructor
      · intro ρ hρ U V hUV h
        rcases h with h | h
        · exact Or.inl (ihφ.1 ρ hρ hUV h)
        · exact Or.inr (ihψ.1 ρ hρ hUV h)
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        exact or_congr (ihφ.2 W ρ₁ ρ₂ h₁ h₂ hEq V hV) (ihψ.2 W ρ₁ ρ₂ h₁ h₂ hEq V hV)
  | imp φ ψ ihφ ihψ =>
      constructor
      · intro ρ hρ U V hUV h V' hV' hφ
        exact h V' (F.le_trans hUV hV') hφ
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        constructor
        · intro h V' hV' hφ
          exact (ihψ.2 W ρ₁ ρ₂ h₁ h₂ hEq V' (F.le_trans hV hV')).mp
            (h V' hV' ((ihφ.2 W ρ₁ ρ₂ h₁ h₂ hEq V' (F.le_trans hV hV')).mpr hφ))
        · intro h V' hV' hφ
          exact (ihψ.2 W ρ₁ ρ₂ h₁ h₂ hEq V' (F.le_trans hV hV')).mpr
            (h V' hV' ((ihφ.2 W ρ₁ ρ₂ h₁ h₂ hEq V' (F.le_trans hV hV')).mp hφ))
  | not φ ihφ =>
      constructor
      · intro ρ hρ U V hUV h V' hV' hφ
        exact h V' (F.le_trans hUV hV') hφ
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        constructor
        · intro h V' hV' hφ
          exact h V' hV' ((ihφ.2 W ρ₁ ρ₂ h₁ h₂ hEq V' (F.le_trans hV hV')).mpr hφ)
        · intro h V' hV' hφ
          exact h V' hV' ((ihφ.2 W ρ₁ ρ₂ h₁ h₂ hEq V' (F.le_trans hV hV')).mp hφ)
  | eq t u iht ihu =>
      constructor
      · intro ρ hρ U V hUV h
        exact (preModel F constDen constAdm).eqvK_mono hUV h
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        have ht := Frame.eqv_mono hV (iht.2 W ρ₁ ρ₂ h₁ h₂ hEq)
        have hu := Frame.eqv_mono hV (ihu.2 W ρ₁ ρ₂ h₁ h₂ hEq)
        constructor
        · intro h
          refine (eqvK_iff_eqv F constDen constAdm _ _ _ _).mpr ?_
          exact Frame.eqv_trans (Frame.eqv_symm ht)
            (Frame.eqv_trans ((eqvK_iff_eqv F constDen constAdm _ _ _ _).mp h) hu)
        · intro h
          refine (eqvK_iff_eqv F constDen constAdm _ _ _ _).mpr ?_
          exact Frame.eqv_trans ht
            (Frame.eqv_trans ((eqvK_iff_eqv F constDen constAdm _ _ _ _).mp h)
              (Frame.eqv_symm hu))
  | all φ ihφ =>
      constructor
      · intro ρ hρ U V hUV h V' hV' d hd
        exact h V' (F.le_trans hUV hV') d hd
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        have step : ∀ V', F.le V V' → ∀ d, F.Adm _ d →
            ((preModel F constDen constAdm).denote φ
                ((preModel F constDen constAdm).extend ρ₁ d) V' ↔
              (preModel F constDen constAdm).denote φ
                ((preModel F constDen constAdm).extend ρ₂ d) V') := by
          intro V' hV' d hd
          exact ihφ.2 V' _ _ (envAdm_extend F constDen constAdm h₁ hd)
            (envAdm_extend F constDen constAdm h₂ hd)
            (envEqv_extend F constDen constAdm
              (fun v => Frame.eqv_mono (F.le_trans hV hV') (hEq v)) (Frame.eqv_refl hd))
            V' (F.le_refl V')
        constructor
        · intro h V' hV' d hd
          exact (step V' hV' d hd).mp (h V' hV' d hd)
        · intro h V' hV' d hd
          exact (step V' hV' d hd).mpr (h V' hV' d hd)
  | ex φ ihφ =>
      constructor
      · intro ρ hρ U V hUV h
        obtain ⟨d, hd, hbody⟩ := h
        exact ⟨d, hd, ihφ.1 _ (envAdm_extend F constDen constAdm hρ hd) hUV hbody⟩
      · intro W ρ₁ ρ₂ h₁ h₂ hEq V hV
        have step : ∀ d, F.Adm _ d →
            ((preModel F constDen constAdm).denote φ
                ((preModel F constDen constAdm).extend ρ₁ d) V ↔
              (preModel F constDen constAdm).denote φ
                ((preModel F constDen constAdm).extend ρ₂ d) V) := by
          intro d hd
          exact ihφ.2 V _ _ (envAdm_extend F constDen constAdm h₁ hd)
            (envAdm_extend F constDen constAdm h₂ hd)
            (envEqv_extend F constDen constAdm (fun v => Frame.eqv_mono hV (hEq v))
              (Frame.eqv_refl hd))
            V (F.le_refl V)
        constructor
        · rintro ⟨d, hd, hbody⟩
          exact ⟨d, hd, (step d hd).mp hbody⟩
        · rintro ⟨d, hd, hbody⟩
          exact ⟨d, hd, (step d hd).mpr hbody⟩

/-- **The full Kripke-Henkin model over a frame.** -/
def model : KripkeHenkinGeneral Base Const where
  toKripkePreModel := preModel F constDen constAdm
  term_closed := fun t _W ρ hρ => (fundamental F constDen constAdm t).1 ρ (fun v => hρ v)
  app_congr_arg := fun hf hd he hde =>
    (eqvK_iff_eqv F constDen constAdm _ _ _ _).mpr
      (hf.2 _ _ _ hd he ((eqvK_iff_eqv F constDen constAdm _ _ _ _).mp hde))

@[simp] theorem model_le (U V : F.World) : (model F constDen constAdm).le U V ↔ F.le U V :=
  Iff.rfl

@[simp] theorem model_constDen {τ : Ty Base} (c : Const τ) :
    (model F constDen constAdm).constDen c = constDen c := rfl

end KripkeFrameModel

end Mettapedia.Logic.HOL
