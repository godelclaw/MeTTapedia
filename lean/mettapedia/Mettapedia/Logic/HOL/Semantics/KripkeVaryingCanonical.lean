import Mettapedia.Logic.HOL.Semantics.KripkeVarying
import Mettapedia.Logic.HOL.Semantics.KripkeHenkinCanonicalObstruction

/-!
# Completeness of the varying-domain Kripke semantics

The supported presented worlds of `KripkeHenkinCanonical`, ordered by
`LevelLe`, form a varying-domain structure: a parameter is available at a
world when its layer is below the world's level.  Disjunction primeness and
existential witnesses are only known for formulas in the language of a world
(`supported_prime_or`, `supported_exists_witness`), and that is exactly what
the varying-domain clauses require.

* `model`: the canonical varying-domain structure, for a scheduler provider
  and a choice of closed terms at every type.
* `provable_of_consequence_of_provider`: completeness from any scheduler
  provider, for a signature with a closed term at every base type.
* `provable_iff_consequence`: for a countable signature with a closed term at
  every base type, EM-free derivability over `Const` coincides with
  consequence over the varying-domain class.
* `constantDomain_not_consequence`: the constant-domain sentence, valid in
  every substitutional `KripkeHenkin` structure, is not a varying-domain
  consequence.
* `consequence_iff_heytingConsequence`: on such signatures the varying-domain
  Kripke consequence and the Heyting-valued consequence agree.

The canonical existential clause needs a witness in the language of the
world; `exists_witness_inLang` obtains it by replacing every unavailable
constant of a witness by the image of a closed `Const`-term.
-/

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

open Mettapedia.Logic.HOL.WithParams

namespace KripkeVarying

namespace Canonical

open KripkeHenkin.SupportedCanonicalFrame ClosedTheorySet

/-! ## Availability by layer -/

/-- At level `ℓ`: original constants, and parameters of layers below `ℓ`. -/
def availAt (ℓ : Nat) : ∀ {τ : Ty Base}, WithParams Const τ → Prop
  | _, Sum.inl _ => True
  | _, Sum.inr p => (Nat.unpair p).1 < ℓ

theorem availAt_mono {ℓ ℓ' : Nat} (h : ℓ ≤ ℓ') {τ : Ty Base} {c : WithParams Const τ}
    (hc : availAt ℓ c) : availAt ℓ' c := by
  cases c with
  | inl _ => trivial
  | inr p => exact lt_of_lt_of_le hc h

theorem availAt_param_pair {ℓ m k : Nat} {σ : Ty Base} :
    availAt (Const := Const) ℓ (param σ (Nat.pair m k)) ↔ m < ℓ := by
  show (Nat.unpair (Nat.pair m k)).1 < ℓ ↔ m < ℓ
  rw [Nat.unpair_pair]

/-- In the language of level `ℓ` means avoiding every parameter of layer `ℓ`
or above. -/
theorem inLang_availAt_iff {ℓ : Nat} {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (WithParams Const) Γ τ) :
    InLang (availAt ℓ) t ↔
      ∀ (σ : Ty Base) (m k : Nat), ℓ ≤ m → NoConstOccurrence (param σ (Nat.pair m k)) t := by
  constructor
  · intro h σ m k hm
    exact h _ (fun hc => absurd (availAt_param_pair.mp hc) (not_lt.mpr hm))
  · intro h σ c hc
    cases c with
    | inl _ => exact absurd trivial hc
    | inr p =>
        have hp : ℓ ≤ (Nat.unpair p).1 := not_lt.mp hc
        have := h σ (Nat.unpair p).1 (Nat.unpair p).2 hp
        rwa [Nat.pair_unpair] at this

theorem inLang_mapConst_inj {ℓ : Nat} {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    InLang (availAt ℓ) (mapConst (fun c => (inj c : WithParams Const _)) t) :=
  InLang.mapConst (fun _ => trivial) t

/-- The image of a `Const`-term mentions no parameter. -/
theorem noConstOccurrence_param_mapConst_inj {Γ : Ctx Base} {τ : Ty Base}
    (t : Term Const Γ τ) (σ : Ty Base) (n : Nat) :
    NoConstOccurrence (param σ n) (mapConst (fun c => (inj c : WithParams Const _)) t) :=
  (inLang_mapConst_inj (ℓ := 0) t) _
    (fun hc => absurd hc (by show ¬ (Nat.unpair n).1 < 0; exact Nat.not_lt_zero _))

/-! ## Witnesses in the language of a world -/

section Retract

variable (inh : ∀ τ : Ty Base, ClosedTerm Const τ)

open Classical in
/-- Keep the constants available at level `ℓ`; send every other constant to
the image of the chosen closed `Const`-term of its type. -/
noncomputable def retract (ℓ : Nat) {τ : Ty Base} (c : WithParams Const τ) :
    ClosedTerm (WithParams Const) τ :=
  if availAt ℓ c then .const c else mapConst (fun c => inj c) (inh τ)

theorem retract_of_avail {ℓ : Nat} {τ : Ty Base} {c : WithParams Const τ}
    (hc : availAt ℓ c) : retract inh ℓ c = .const c := by
  classical
  simp only [retract, if_pos hc]

theorem inLang_retract (ℓ : Nat) {τ : Ty Base} (c : WithParams Const τ) :
    InLang (availAt ℓ) (retract inh ℓ c) := by
  classical
  unfold retract
  split_ifs with hc
  · exact InLang.const hc
  · exact inLang_mapConst_inj _

/-- Substituting closed terms for constants fixes a term when every constant
that is moved is absent. -/
theorem substConst_eq_self {K : Ty Base → Type v}
    (f : ∀ {τ : Ty Base}, K τ → ClosedTerm K τ) :
    ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term K Γ τ),
      (∀ {σ : Ty Base} (c : K σ), f c ≠ .const c → NoConstOccurrence c t) →
        substConst f t = t
  | _, _, .var _, _ => rfl
  | Γ, _, .const d, h => by
      have hd : f d = .const d := by
        by_contra hne
        have hno := h d hne
        cases hno with
        | const_diff_type hne' _ => exact hne' rfl
        | const_same_ne _ hne' => exact hne' rfl
      show weakenCtx Γ (f d) = _
      rw [hd, weakenCtx_const]
  | _, _, .app g t, h => by
      show Term.app (substConst f g) (substConst f t) = _
      rw [substConst_eq_self f g (fun c hc => by cases h c hc with | app h₁ _ => exact h₁),
        substConst_eq_self f t (fun c hc => by cases h c hc with | app _ h₂ => exact h₂)]
  | _, _, .lam t, h => by
      show Term.lam (substConst f t) = _
      rw [substConst_eq_self f t (fun c hc => by cases h c hc with | lam h₁ => exact h₁)]
  | _, _, .top, _ => rfl
  | _, _, .bot, _ => rfl
  | _, _, .and φ ψ, h => by
      show Term.and (substConst f φ) (substConst f ψ) = _
      rw [substConst_eq_self f φ (fun c hc => by cases h c hc with | and h₁ _ => exact h₁),
        substConst_eq_self f ψ (fun c hc => by cases h c hc with | and _ h₂ => exact h₂)]
  | _, _, .or φ ψ, h => by
      show Term.or (substConst f φ) (substConst f ψ) = _
      rw [substConst_eq_self f φ (fun c hc => by cases h c hc with | or h₁ _ => exact h₁),
        substConst_eq_self f ψ (fun c hc => by cases h c hc with | or _ h₂ => exact h₂)]
  | _, _, .imp φ ψ, h => by
      show Term.imp (substConst f φ) (substConst f ψ) = _
      rw [substConst_eq_self f φ (fun c hc => by cases h c hc with | imp h₁ _ => exact h₁),
        substConst_eq_self f ψ (fun c hc => by cases h c hc with | imp _ h₂ => exact h₂)]
  | _, _, .not φ, h => by
      show Term.not (substConst f φ) = _
      rw [substConst_eq_self f φ (fun c hc => by cases h c hc with | not h₁ => exact h₁)]
  | _, _, .eq t u, h => by
      show Term.eq (substConst f t) (substConst f u) = _
      rw [substConst_eq_self f t (fun c hc => by cases h c hc with | eq h₁ _ => exact h₁),
        substConst_eq_self f u (fun c hc => by cases h c hc with | eq _ h₂ => exact h₂)]
  | _, _, .all φ, h => by
      show Term.all (substConst f φ) = _
      rw [substConst_eq_self f φ (fun c hc => by cases h c hc with | all h₁ => exact h₁)]
  | _, _, .ex φ, h => by
      show Term.ex (substConst f φ) = _
      rw [substConst_eq_self f φ (fun c hc => by cases h c hc with | ex h₁ => exact h₁)]

/-- The retraction fixes every term in the language of its level. -/
theorem substConst_retract_of_inLang {ℓ : Nat} {Γ : Ctx Base} {τ : Ty Base}
    {t : Term (WithParams Const) Γ τ} (ht : InLang (availAt ℓ) t) :
    substConst (retract inh ℓ) t = t := by
  classical
  refine substConst_eq_self _ t fun c hc => ht c fun hav => hc ?_
  exact retract_of_avail inh hav

/-- Weakening to a context keeps a term in the language. -/
theorem inLang_weakenCtx {Dom : Ty Base → Type v} {avail : ∀ {τ : Ty Base}, Dom τ → Prop}
    {τ : Ty Base} {t : ClosedTerm Dom τ} (ht : InLang avail t) :
    ∀ Γ : Ctx Base, InLang avail (weakenCtx Γ t)
  | [] => ht
  | _ :: Γ => InLang.rename _ (inLang_weakenCtx ht Γ)

/-- After the retraction, every term is in the language of the level. -/
theorem inLang_substConst_retract (ℓ : Nat) :
    ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term (WithParams Const) Γ τ),
      InLang (availAt ℓ) (substConst (retract inh ℓ) t)
  | _, _, .var v => InLang.var v
  | Γ, _, .const d => inLang_weakenCtx (inLang_retract inh ℓ d) Γ
  | _, _, .app f t => fun c hc =>
      .app (inLang_substConst_retract ℓ f c hc) (inLang_substConst_retract ℓ t c hc)
  | _, _, .lam t => fun c hc => .lam (inLang_substConst_retract ℓ t c hc)
  | _, _, .top => fun _ _ => .top
  | _, _, .bot => fun _ _ => .bot
  | _, _, .and φ ψ => fun c hc =>
      .and (inLang_substConst_retract ℓ φ c hc) (inLang_substConst_retract ℓ ψ c hc)
  | _, _, .or φ ψ => fun c hc =>
      .or (inLang_substConst_retract ℓ φ c hc) (inLang_substConst_retract ℓ ψ c hc)
  | _, _, .imp φ ψ => fun c hc =>
      .imp (inLang_substConst_retract ℓ φ c hc) (inLang_substConst_retract ℓ ψ c hc)
  | _, _, .not φ => fun c hc => .not (inLang_substConst_retract ℓ φ c hc)
  | _, _, .eq t u => fun c hc =>
      .eq (inLang_substConst_retract ℓ t c hc) (inLang_substConst_retract ℓ u c hc)
  | _, _, .all φ => fun c hc => .all (inLang_substConst_retract ℓ φ c hc)
  | _, _, .ex φ => fun c hc => .ex (inLang_substConst_retract ℓ φ c hc)

/-- The raw base of a supported world is in the language of its level. -/
theorem inLang_of_mem_raw (W : SupportedPresentedIntuitionisticWorld Const)
    {ψ : ClosedFormula (WithParams Const)} (hψ : ψ ∈ W.raw) :
    InLang (availAt W.level) ψ :=
  (inLang_availAt_iff ψ).mpr fun σ m k hm => W.raw_avoids_future ψ hψ σ m k hm

include inh in
/-- **Witnesses in the language.**  If a supported world contains an instance
of a body in its language, it contains an instance at a witness in its
language. -/
theorem exists_witness_inLang (W : SupportedPresentedIntuitionisticWorld Const)
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]} (hφ : InLang (availAt W.level) φ)
    {t : ClosedTerm (WithParams Const) σ} (ht : instantiate t φ ∈ W.carrier) :
    ∃ t' : ClosedTerm (WithParams Const) σ,
      InLang (availAt W.level) t' ∧ instantiate t' φ ∈ W.carrier := by
  obtain ⟨Γ, hΓ, d⟩ := ht
  refine ⟨substConst (retract inh W.level) t, inLang_substConst_retract inh _ t, ?_⟩
  have d' := ExtDerivation.substConst_derivation (retract inh W.level) d
  rw [substConst_instantiate, substConst_retract_of_inLang inh hφ] at d'
  have hΓ' : Γ.map (substConst (retract inh W.level)) = Γ := by
    conv_rhs => rw [← List.map_id Γ]
    exact List.map_congr_left fun ψ hψ =>
      substConst_retract_of_inLang inh (inLang_of_mem_raw W (hΓ ψ hψ))
  rw [hΓ'] at d'
  exact ⟨Γ, hΓ, d'⟩

end Retract

/-! ## The canonical varying-domain structure -/

theorem pair_avoids_of_inLang {W : SupportedPresentedIntuitionisticWorld Const}
    {φ ψ : ClosedFormula (WithParams Const)} (h : InLang (availAt W.level) (.or φ ψ)) :
    FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const) W.level (φ, ψ) :=
  fun σ m k hm =>
    ⟨(inLang_availAt_iff φ).mp (InLang.or_left h) σ m k hm,
      (inLang_availAt_iff ψ).mp (InLang.or_right h) σ m k hm⟩

/-- **The canonical varying-domain structure.** -/
noncomputable def model (P : SchedulerProvider (Base := Base) Const)
    (inh : ∀ τ : Ty Base, ClosedTerm Const τ) :
    KripkeVarying.{u, v, max u v} Base Const where
  Dom := WithParams Const
  incl := fun c => inj c
  World := SupportedPresentedIntuitionisticWorld Const
  le := LevelLe (Base := Base) (Const := Const)
  le_refl := levelLe_refl (Base := Base) (Const := Const)
  le_trans := fun hUV hVW => levelLe_trans (Base := Base) (Const := Const) hUV hVW
  avail := fun W => availAt W.level
  avail_mono := fun hUV hc => availAt_mono hUV.1 hc
  avail_incl := fun _ _ _ => trivial
  forces := Forces (Base := Base) (Const := Const)
  eqVal := fun W s t => EqVal (Base := Base) (Const := Const) W s t
  forces_mono := fun hUV h =>
    KripkeHenkin.SupportedCanonicalFrame.forces_mono (Base := Base) (Const := Const) hUV.2 h
  forces_top := KripkeHenkin.SupportedCanonicalFrame.forces_top (Base := Base) (Const := Const) _
  forces_bot := KripkeHenkin.SupportedCanonicalFrame.forces_bot (Base := Base) (Const := Const) _
  forces_and := KripkeHenkin.SupportedCanonicalFrame.forces_and (Base := Base) (Const := Const)
  forces_or := fun h => forces_or_supported (Base := Base) (Const := Const)
    (pair_avoids_of_inLang h)
  forces_imp := forces_imp_level_provider (Base := Base) (Const := Const) P _
  forces_not := forces_not_level_provider (Base := Base) (Const := Const) P _
  forces_eq := KripkeHenkin.SupportedCanonicalFrame.forces_eq (Base := Base) (Const := Const)
  eq_refl := fun W t =>
    KripkeHenkin.SupportedCanonicalFrame.eq_refl (Base := Base) (Const := Const) W t
  eq_symm := fun h =>
    KripkeHenkin.SupportedCanonicalFrame.eq_symm (Base := Base) (Const := Const) h
  eq_trans := fun h₁ h₂ =>
    KripkeHenkin.SupportedCanonicalFrame.eq_trans (Base := Base) (Const := Const) h₁ h₂
  eq_app_congr := fun h₁ h₂ =>
    KripkeHenkin.SupportedCanonicalFrame.eq_app_congr (Base := Base) (Const := Const) h₁ h₂
  eq_funext := by
    intro σ τ W f g hf hg h
    -- the universal closure of the pointwise equation is in the language
    let φ : Formula (WithParams Const) [σ] :=
      .eq (.app (weaken (σ := σ) f) (.var .vz)) (.app (weaken (σ := σ) g) (.var .vz))
    have hshape : ∀ t : ClosedTerm (WithParams Const) σ,
        instantiate t φ = .eq (.app f t) (.app g t) := by
      intro t
      show Term.eq (Term.app (instantiate t (weaken f)) t)
        (Term.app (instantiate t (weaken g)) t) = _
      rw [instantiate_weaken, instantiate_weaken]
    have hφ : InLang (availAt W.level) φ := fun c hc =>
      .eq (.app (InLang.rename _ hf c hc) .var) (.app (InLang.rename _ hg c hc) .var)
    have hall : (.all φ : ClosedFormula (WithParams Const)) ∈ W.carrier := by
      by_contra hNot
      have hfresh : NoConstOccurrence (param σ (Nat.pair W.level 0)) φ :=
        (inLang_availAt_iff φ).mp hφ σ W.level 0 le_rfl
      have hfuture : ∀ (ρ : Ty Base) (r j : Nat), W.level + 1 ≤ r →
          NoConstOccurrence (param ρ (Nat.pair r j)) φ :=
        fun ρ r j hr => (inLang_availAt_iff φ).mp hφ ρ r j (by omega)
      obtain ⟨W', hLevel, hRaw, hOmit⟩ :=
        SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_all
          (Base := Base) (Const := Const) W (m := W.level) (k := 0)
          (P.scheduler (W.level + 1)) le_rfl hfresh hfuture hNot
      have hle : LevelLe (Base := Base) (Const := Const) W W' :=
        levelLe_of_raw_subset (Base := Base) (Const := Const) (by omega) hRaw
      have hin : InLang (availAt W'.level)
          (.const (param σ (Nat.pair W.level 0)) : ClosedTerm (WithParams Const) σ) :=
        InLang.const (availAt_param_pair.mpr (by omega))
      apply hOmit
      rw [hshape]
      exact h W' hle _ hin
    exact KripkeHenkin.SupportedCanonicalFrame.eq_funext (Base := Base) (Const := Const)
      fun t => by
      have := KripkeHenkin.SupportedCanonicalMembership.all_elim_mem (Base := Base) (Const := Const)
        (W := W) t hall
      rw [hshape] at this
      exact this
  eq_beta := fun t u =>
    KripkeHenkin.SupportedCanonicalFrame.eq_beta (Base := Base) (Const := Const) _ t u
  eq_eta := fun f =>
    KripkeHenkin.SupportedCanonicalFrame.eq_eta (Base := Base) (Const := Const) _ f
  eq_prop_intro := fun hpq hqp =>
    KripkeHenkin.SupportedCanonicalMembership.eq_prop_intro_mem (Base := Base) (Const := Const) hpq hqp
  eq_prop_elim_left := fun h =>
    KripkeHenkin.SupportedCanonicalMembership.eq_prop_elim_left_mem (Base := Base) (Const := Const) h
  eq_prop_elim_right := fun h =>
    KripkeHenkin.SupportedCanonicalMembership.eq_prop_elim_right_mem (Base := Base) (Const := Const) h
  forces_all := by
    intro W σ φ hL
    have hφ : InLang (availAt W.level) φ := InLang.all_body hL
    constructor
    · intro h V hWV t _
      exact KripkeHenkin.SupportedCanonicalMembership.all_elim_mem (Base := Base) (Const := Const)
        (W := V) t (hWV.2 h)
    · intro h
      by_contra hNot
      have hfresh : NoConstOccurrence (param σ (Nat.pair W.level 0)) φ :=
        (inLang_availAt_iff φ).mp hφ σ W.level 0 le_rfl
      have hfuture : ∀ (ρ : Ty Base) (r j : Nat), W.level + 1 ≤ r →
          NoConstOccurrence (param ρ (Nat.pair r j)) φ :=
        fun ρ r j hr => (inLang_availAt_iff φ).mp hφ ρ r j (by omega)
      obtain ⟨W', hLevel, hRaw, hOmit⟩ :=
        SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_all
          (Base := Base) (Const := Const) W (m := W.level) (k := 0)
          (P.scheduler (W.level + 1)) le_rfl hfresh hfuture hNot
      have hle : LevelLe (Base := Base) (Const := Const) W W' :=
        levelLe_of_raw_subset (Base := Base) (Const := Const) (by omega) hRaw
      have hin : InLang (availAt W'.level)
          (.const (param σ (Nat.pair W.level 0)) : ClosedTerm (WithParams Const) σ) :=
        InLang.const (availAt_param_pair.mpr (by omega))
      exact hOmit (h W' hle _ hin)
  forces_ex := by
    intro W σ φ hL
    have hφ : InLang (availAt W.level) φ := InLang.ex_body hL
    constructor
    · intro h
      have hBody : BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) W.level
          (⟨σ, φ⟩ : Body Const) :=
        fun ρ m k hm => (inLang_availAt_iff φ).mp hφ ρ m k hm
      obtain ⟨t, ht⟩ := (forces_ex_supported (Base := Base) (Const := Const) hBody).mp h
      exact exists_witness_inLang inh W hφ ht
    · rintro ⟨t, _, ht⟩
      exact KripkeHenkin.SupportedCanonicalMembership.ex_intro_mem (Base := Base) (Const := Const)
        (W := W) t ht

/-! ## Completeness -/

/-- A closed term at every type, from a closed term at every base type. -/
def inhabitant (inhBase : ∀ b : Base, ClosedTerm Const (.base b)) :
    ∀ τ : Ty Base, ClosedTerm Const τ
  | .prop => .top
  | .base b => inhBase b
  | .arr _ τ => .lam (weaken (inhabitant inhBase τ))

/-- Over a signature with a closed term at every type, parameters do not add
derivable `Const`-sequents. -/
theorem provable_of_provable_withParams (inh : ∀ τ : Ty Base, ClosedTerm Const τ)
    {T : ClosedTheorySet Const} {θ : ClosedFormula Const}
    (h : ClosedTheorySet.Provable (Const := WithParams Const)
      ((mapConst (fun c => (inj c : WithParams Const _))) '' T)
      (mapConst (fun c => (inj c : WithParams Const _)) θ)) :
    ClosedTheorySet.Provable (Const := Const) T θ := by
  classical
  obtain ⟨Γ, hΓ, d⟩ := h
  let g : ∀ {τ : Ty Base}, WithParams Const τ → ClosedTerm Const τ := fun {τ} c =>
    Sum.elim (fun c => .const c) (fun _ => inh τ) c
  have hback : ∀ ψ : ClosedFormula Const,
      substConst g (mapConst (fun c => (inj c : WithParams Const _)) ψ) = ψ := by
    intro ψ
    rw [substConst_mapConst]
    exact substConst_id ψ
  have d' := ExtDerivation.substConst_derivation g d
  rw [hback] at d'
  refine ⟨Γ.map (substConst g), ?_, d'⟩
  intro ψ hψ
  obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hψ
  obtain ⟨ψ', hψ', rfl⟩ := hΓ χ hχ
  rw [hback]
  exact hψ'

/-- **Completeness of the varying-domain Kripke semantics** from any scheduler
provider, for a signature with a closed term at every base type.  The provider
is the only enumeration data the construction consumes. -/
theorem provable_of_consequence_of_provider (P : SchedulerProvider (Base := Base) Const)
    (inhBase : ∀ b : Base, ClosedTerm Const (.base b))
    {T : ClosedTheorySet Const} {θ : ClosedFormula Const}
    (h : Consequence.{u, v, max u v} T θ) : ClosedTheorySet.Provable (Const := Const) T θ := by
  classical
  by_contra hNot
  let ι : ∀ {τ : Ty Base}, Const τ → WithParams Const τ := fun c => inj c
  have hNot' : ¬ ClosedTheorySet.Provable (Const := WithParams Const)
      ((mapConst ι) '' T) (mapConst ι θ) :=
    fun hP => hNot (provable_of_provable_withParams (inhabitant inhBase) hP)
  have hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (0 + 1)
      ((mapConst ι) '' T) := by
    rintro _ ⟨ψ, _, rfl⟩ σ m k _
    exact noConstOccurrence_param_mapConst_inj ψ σ _
  have hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) 0 0
      ((mapConst ι) '' T) := by
    rintro _ ⟨ψ, _, rfl⟩ σ r k _
    exact noConstOccurrence_param_mapConst_inj ψ σ _
  have hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) 0 0
      (mapConst ι θ) := fun σ r k _ => noConstOccurrence_param_mapConst_inj θ σ _
  obtain ⟨W, _, hT, hθ⟩ :=
    exists_supported_presented_rawAlternatingScheduledStageLimit_separating
      (Base := Base) (Const := Const) (ℓ := 0)
      (P.scheduler 0) hLayer hStage hθStage hNot'
  let M := model P (inhabitant inhBase)
  exact hθ (h M (show M.World from W) fun ψ hψ => hT ⟨ψ, hψ, rfl⟩)

/-- **Completeness of the varying-domain Kripke semantics** for a countable
signature with a closed term at every base type. -/
theorem provable_of_consequence [Countable Base] [∀ τ, Countable (Const τ)]
    (inhBase : ∀ b : Base, ClosedTerm Const (.base b))
    {T : ClosedTheorySet Const} {θ : ClosedFormula Const}
    (h : Consequence.{u, v, max u v} T θ) : ClosedTheorySet.Provable (Const := Const) T θ :=
  provable_of_consequence_of_provider schedulerProviderOfCountable inhBase h

/-- **Soundness and completeness of the varying-domain Kripke semantics** for a
countable signature with a closed term at every base type. -/
theorem provable_iff_consequence [Countable Base] [∀ τ, Countable (Const τ)]
    (inhBase : ∀ b : Base, ClosedTerm Const (.base b))
    {T : ClosedTheorySet Const} {θ : ClosedFormula Const} :
    ClosedTheorySet.Provable (Const := Const) T θ ↔ Consequence.{u, v, max u v} T θ :=
  ⟨consequence_of_provable, provable_of_consequence inhBase⟩

/-! ## Consequences -/

/-- Derivability over `Const` transfers to the parameter signature. -/
theorem provable_withParams_of_provable {T : ClosedTheorySet Const} {θ : ClosedFormula Const}
    (h : ClosedTheorySet.Provable (Const := Const) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const)
      ((mapConst (fun c => (inj c : WithParams Const _))) '' T)
      (mapConst (fun c => (inj c : WithParams Const _)) θ) := by
  obtain ⟨Γ, hΓ, d⟩ := h
  refine ⟨Γ.map (mapConst fun c => (inj c : WithParams Const _)), ?_, ?_⟩
  · intro ψ hψ
    obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hψ
    exact ⟨χ, hΓ χ hχ, rfl⟩
  · exact ExtDerivation.mapConst (fun c => (inj c : WithParams Const _)) d

/-- **The varying-domain class refutes the constant-domain sentence** over a
countable signature with a closed term at every base type. -/
theorem constantDomain_not_consequence [Countable Base] [∀ τ, Countable (Const τ)]
    (inhBase : ∀ b : Base, ClosedTerm Const (.base b)) (b : Base) :
    ¬ Consequence.{u, v, max u v} (Base := Base) (Const := Const) ∅ (constantDomain (.base b)) :=
  fun h => constantDomain_not_provable b ((provable_iff_consequence inhBase).mpr h)

/-- **The constant-domain sentence separates the substitutional and the
varying-domain Kripke classes.** -/
theorem constantDomain_separates [Countable Base] [∀ τ, Countable (Const τ)]
    (inhBase : ∀ b : Base, ClosedTerm Const (.base b)) (b : Base) :
    KripkeHenkin.Consequence.{u, v, max u v} (Base := Base) (Const := Const) ∅
        (constantDomain (.base b)) ∧
      ¬ Consequence.{u, v, max u v} (Base := Base) (Const := Const) ∅
        (constantDomain (.base b)) :=
  ⟨KripkeHenkin.consequence_constantDomain _, constantDomain_not_consequence inhBase b⟩

/-- **Kripke and Heyting consequence agree** on a countable signature with a
closed term at every base type: a `Const`-sequent is a varying-domain Kripke
consequence exactly when its image over the parameter signature is a
Heyting-valued consequence. -/
theorem consequence_iff_heytingConsequence [Countable Base] [∀ τ, Countable (Const τ)]
    (inhBase : ∀ b : Base, ClosedTerm Const (.base b))
    {T : ClosedTheorySet Const} {θ : ClosedFormula Const} :
    Consequence.{u, v, max u v} T θ ↔
      HeytingSem.HeytingConsequence (Base := Base) (Const := WithParams Const)
        ((mapConst (fun c => (inj c : WithParams Const _))) '' T)
        (mapConst (fun c => (inj c : WithParams Const _)) θ) := by
  rw [← provable_iff_consequence inhBase]
  constructor
  · intro h
    exact HeytingSem.heytingConsequence_of_provable (provable_withParams_of_provable h)
  · intro h
    refine provable_of_provable_withParams (inhabitant inhBase)
      (HeytingSem.provable_of_heytingConsequence_param_free ?_ h)
    rintro _ ⟨ψ, _, rfl⟩ σ k
    exact noConstOccurrence_param_mapConst_inj ψ σ k

/-! ## Examples -/

/-- One base type with one constant `o`. -/
inductive PointConst : Ty Unit → Type
  | o : PointConst (.base ())
  deriving DecidableEq

instance (τ : Ty Unit) : Countable (PointConst τ) := by
  refine Function.Injective.countable (f := fun _ => ()) ?_
  intro a b _
  cases a; cases b; rfl

/-- The closed term `o` at the base type. -/
def pointInhabitant : ∀ b : Unit, ClosedTerm PointConst (.base b)
  | () => .const .o

/-- The sentence `∃ x : base, x = o` over `PointConst`. -/
def pointExistsEqO : ClosedFormula PointConst :=
  .ex (.eq (.var .vz) (.const .o))

/-- Positive control with a base type, semantic side: `∃ x, x = o` is forced
at every world of every varying-domain structure, with witness `o`. -/
theorem pointExistsEqO_consequence :
    Consequence.{0, 0, 0} (∅ : ClosedTheorySet PointConst) pointExistsEqO := by
  intro M W _
  have hIn : InLang (M.avail W) (mapConst M.incl pointExistsEqO) :=
    InLang.mapConst (Dom := M.Dom) (avail := fun d => M.avail W d)
      (incl := fun c => M.incl c) (fun c => M.avail_incl W c) pointExistsEqO
  show M.forces W (.ex (.eq (.var .vz) (.const (M.incl .o))))
  refine (M.forces_ex hIn).mpr ⟨.const (M.incl .o), InLang.const (M.avail_incl W _), ?_⟩
  show M.forces W (.eq (.const (M.incl .o)) (.const (M.incl .o)))
  exact M.forces_eq.mpr (M.eq_refl W _)

/-- Positive control with a base type, completeness side:
`provable_iff_consequence` turns the semantic fact into a derivation. -/
theorem pointExistsEqO_provable :
    ClosedTheorySet.Provable (Const := PointConst) ∅ pointExistsEqO :=
  (provable_iff_consequence pointInhabitant).mpr pointExistsEqO_consequence

/-- Positive control with a base type, soundness side: the derivation of `o = o`
gives a varying-domain consequence. -/
theorem pointEqRefl_consequence :
    Consequence.{0, 0, 0} (∅ : ClosedTheorySet PointConst)
      (.eq (.const .o) (.const .o) : ClosedFormula PointConst) :=
  (provable_iff_consequence pointInhabitant).mp
    ⟨[], fun _ h => absurd h List.not_mem_nil, .eqRefl _⟩

/-- Positive instance: the varying-domain class has a member and a world that
refute the constant-domain sentence. -/
theorem exists_world_not_forces_constantDomain :
    ∃ (M : KripkeVarying.{0, 0, 0} Unit PointConst) (W : M.World),
      ¬ M.forces W (mapConst M.incl (constantDomain (.base ()))) := by
  by_contra h
  exact constantDomain_not_consequence pointInhabitant () fun M W _ =>
    Classical.byContradiction fun hW => h ⟨M, W, hW⟩

/-- Negative instance: the same sentence is forced at every world of every
substitutional `KripkeHenkin` structure of this signature. -/
theorem kripkeHenkin_forces_constantDomain_point
    (K : KripkeHenkin.{0, 0, 0} Unit PointConst) (W : K.World) :
    K.forces W (constantDomain (.base ())) :=
  KripkeHenkin.forces_constantDomain K W _


end Canonical

end KripkeVarying

end Mettapedia.Logic.HOL
