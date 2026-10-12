import Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionFrame

/-!
# Template scope: `unify`, and a both-sides `let`

How the model's `unify` relates to a `let` that fills both sides.

`unify` and the matching direction are two axes.  `unify` says *which names a
pattern introduces*: none.  The direction says *which side a match may fill*.

## Main results

* `elabMS_letToUnify`, `answersDirCfg_letToUnify` — **under rule M a plain
  `let` is `unify`**: writing every plain `let` as `unify` changes no elaborated
  term, so no answer, at either direction.  Under lexical fresh they differ: a
  `let` introduces its pattern's names and `unify` refines the names in scope
  (`MatchDirectionExamples.let_is_not_unify_LF`).
* `matchT2_data_left` — **the exchange law**: against a pattern that is data
  (symbols and data application), the both-sides matcher is the pattern-only
  matcher with the sides exchanged, for every store and every value.
* `stepDir_let_data_exchange` — **one unfolding**: a both-sides `let` with a
  data pattern unfolds exactly as the pattern-only `let` with pattern and value
  exchanged, for every runner that returns the value and the pattern unchanged.
  So where the pattern is data, a both-sides `let` is a spelling of `unify` with
  the sides exchanged.
* `letCont_nonground_store` — pattern-only never writes a store name when the
  value is not ground.  A match that must fill names on both sides at once
  therefore has no pattern-only spelling at the `let` itself
  (`MatchDirectionExamples.mixedFill_*`).
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

variable {S : Type u} {X : Type v}

/-! ## Under rule M a plain `let` is `unify` -/

namespace Src

/-- Write every plain `let` as `unify`.  A `let` with a crossing set, and
quoted code, are left as written. -/
def letToUnify : Src S X → Src S X
  | .lam z xs b => .lam z xs (letToUnify b)
  | .app f a => .app (letToUnify f) (letToUnify a)
  | .letS p w b none => .unify (letToUnify p) (letToUnify w) (letToUnify b)
  | .letS p w b (some sh) => .letS (letToUnify p) (letToUnify w) (letToUnify b) (some sh)
  | .unify p w b => .unify (letToUnify p) (letToUnify w) (letToUnify b)
  | .alt t₁ t₂ => .alt (letToUnify t₁) (letToUnify t₂)
  | .new ys b => .new ys (letToUnify b)
  | .form z b => .form z (letToUnify b)
  | t => t

theorem direct_letToUnify : ∀ t : Src S X, direct (letToUnify t) = direct t
  | .sym _ | .fn _ | .sv _ | .par _ | .quote _ | .pquote _ => rfl
  | .lam _ _ _ => rfl
  | .app f a => by simp only [letToUnify, direct, direct_letToUnify f, direct_letToUnify a]
  | .letS p w b none => by
      simp only [letToUnify, direct, direct_letToUnify p, direct_letToUnify w, direct_letToUnify b]
  | .letS p w b (some _) => by
      simp only [letToUnify, direct, direct_letToUnify p, direct_letToUnify w, direct_letToUnify b]
  | .unify p w b => by
      simp only [letToUnify, direct, direct_letToUnify p, direct_letToUnify w, direct_letToUnify b]
  | .alt t₁ t₂ => by simp only [letToUnify, direct, direct_letToUnify t₁, direct_letToUnify t₂]
  | .new _ b => by simp only [letToUnify, direct, direct_letToUnify b]
  | .form _ b => by simp only [letToUnify, direct, direct_letToUnify b]

theorem sharedUp_letToUnify : ∀ t : Src S X, sharedUp (letToUnify t) = sharedUp t
  | .sym _ | .fn _ | .sv _ | .par _ | .quote _ | .pquote _ => rfl
  | .lam _ _ _ => rfl
  | .app f a => by
      simp only [letToUnify, sharedUp, sharedUp_letToUnify f, sharedUp_letToUnify a]
  | .letS p w b none => by
      simp only [letToUnify, sharedUp, sharedUp_letToUnify p, sharedUp_letToUnify w,
        sharedUp_letToUnify b]
  | .letS p w b (some _) => by
      simp only [letToUnify, sharedUp, sharedUp_letToUnify p, sharedUp_letToUnify w,
        sharedUp_letToUnify b]
  | .unify p w b => by
      simp only [letToUnify, sharedUp, sharedUp_letToUnify p, sharedUp_letToUnify w,
        sharedUp_letToUnify b]
  | .alt t₁ t₂ => by
      simp only [letToUnify, sharedUp, sharedUp_letToUnify t₁, sharedUp_letToUnify t₂]
  | .new _ b => by simp only [letToUnify, sharedUp, sharedUp_letToUnify b]
  | .form _ b => by simp only [letToUnify, sharedUp, sharedUp_letToUnify b]

theorem uses_letToUnify (t : Src S X) : uses (letToUnify t) = uses t := by
  simp only [uses, direct_letToUnify, sharedUp_letToUnify]

theorem patNames_letToUnify : ∀ t : Src S X, patNames (letToUnify t) = patNames t
  | .sym _ | .fn _ | .sv _ | .par _ | .quote _ | .pquote _ => rfl
  | .lam _ _ _ => rfl
  | .app f a => by
      simp only [letToUnify, patNames, patNames_letToUnify f, patNames_letToUnify a]
  | .letS _ _ _ none => rfl
  | .letS _ _ _ (some _) => rfl
  | .unify _ _ _ => rfl
  | .alt _ _ => rfl
  | .new _ _ => rfl
  | .form _ _ => rfl

theorem names_letToUnify : ∀ t : Src S X, names (letToUnify t) = names t
  | .sym _ | .fn _ | .sv _ | .par _ | .quote _ | .pquote _ => rfl
  | .lam _ _ b => by simp only [letToUnify, names, names_letToUnify b]
  | .app f a => by simp only [letToUnify, names, names_letToUnify f, names_letToUnify a]
  | .letS p w b none => by
      simp only [letToUnify, names, names_letToUnify p, names_letToUnify w, names_letToUnify b]
  | .letS p w b (some _) => by
      simp only [letToUnify, names, names_letToUnify p, names_letToUnify w, names_letToUnify b]
  | .unify p w b => by
      simp only [letToUnify, names, names_letToUnify p, names_letToUnify w, names_letToUnify b]
  | .alt t₁ t₂ => by simp only [letToUnify, names, names_letToUnify t₁, names_letToUnify t₂]
  | .new _ b => by simp only [letToUnify, names, names_letToUnify b]
  | .form _ b => by simp only [letToUnify, names, names_letToUnify b]

end Src

section RuleM

variable [DecidableEq X]

/-- **Under rule M a plain `let` is `unify`**, term for term: rule M's `let`
introduces no name, which is what `unify` says. -/
theorem elabMS_letToUnify (R : Owner) : ∀ (t : Src S X) (E : List X) (env : REnv X) (pos : Owner),
    elabMS R E env pos (Src.letToUnify t) = elabMS R E env pos t
  | .sym _, _, _, _ | .fn _, _, _, _ | .sv _, _, _, _ | .par _, _, _, _ | .quote _, _, _, _
  | .pquote _, _, _, _ => rfl
  | .lam z xs b, E, env, pos => by
      simp only [Src.letToUnify, elabMS, Src.uses_letToUnify, Src.direct_letToUnify,
        ownRuleMDefault, elabMS_letToUnify R b]
  | .app f a, E, env, pos => by
      simp only [Src.letToUnify, elabMS, elabMS_letToUnify R f, elabMS_letToUnify R a]
  | .letS p w b none, E, env, pos => by
      simp only [Src.letToUnify, elabMS, crossOwn_none, elabMS_letToUnify R p, elabMS_letToUnify R w,
        elabMS_letToUnify R b]
  | .letS p w b (some sh), E, env, pos => by
      simp only [Src.letToUnify, elabMS, Src.patNames_letToUnify, elabMS_letToUnify R p,
        elabMS_letToUnify R w, elabMS_letToUnify R b]
  | .unify p w b, E, env, pos => by
      simp only [Src.letToUnify, elabMS, elabMS_letToUnify R p, elabMS_letToUnify R w,
        elabMS_letToUnify R b]
  | .alt t₁ t₂, E, env, pos => by
      simp only [Src.letToUnify, elabMS, elabMS_letToUnify R t₁, elabMS_letToUnify R t₂]
  | .new [] b, E, env, pos => by
      simp only [Src.letToUnify, elabMS, elabMS_letToUnify R b]
  | .new (y₀ :: ys) b, E, env, pos => by
      simp only [Src.letToUnify, elabMS, elabMS_letToUnify R b]
  | .form z b, E, env, pos => by
      simp only [Src.letToUnify, elabMS, elabMS_letToUnify R b]

/-- Rule M's elaboration of a form does not see whether a plain `let` is
written `let` or `unify`. -/
theorem elabCfg_cfgM_letToUnify (root : Owner) (t : Src S X) :
    elabCfg cfgM root (Src.letToUnify t) = elabCfg cfgM root t := by
  simp only [elabCfg, elabCfgX, cfgM, elabForm, Src.direct_letToUnify, elabMS_letToUnify]

/-- Nor does a clause. -/
theorem clauseOf_cfgM_letToUnify (root : Owner) (u : X) (unit : S) (body : Src S X) :
    clauseOf cfgM root u unit (Src.letToUnify body) = clauseOf cfgM root u unit body := by
  simp only [clauseOf, rootSpellings, Src.names_letToUnify, elabCfg_cfgM_letToUnify]
  simp only [elabCfgX, cfgM]

variable [DecidableEq S]

/-- **Under rule M, at either direction, `let` and `unify` are one form.**
Writing every plain `let` of the query and of the equations as `unify` changes
no answer. -/
theorem answersDirCfg_letToUnify (dir : Direction) (u : X) (unit : S)
    (cl : S → Option (Src S X)) (n : ℕ) (t : Src S X) :
    answersDirCfg ⟨cfgM, dir⟩
        (IdSlot.progSlot cfgM u unit fun F => (cl F).map Src.letToUnify) n (Src.letToUnify t) =
      answersDirCfg ⟨cfgM, dir⟩ (IdSlot.progSlot cfgM u unit cl) n t := by
  have hp : (IdSlot.progSlot cfgM u unit fun F => (cl F).map Src.letToUnify) =
      IdSlot.progSlot cfgM u unit cl := by
    funext F
    simp only [IdSlot.progSlot, Option.map_map, Function.comp_def, clauseOf_cfgM_letToUnify]
  simp only [answersDirCfg, hp, elabCfg_cfgM_letToUnify]

end RuleM

/-! ## The exchange law -/

/-- Data: symbols and data application.  No code. -/
def GVal.isData : GVal S X → Bool
  | .sym _ => true
  | .app f a => f.isData && a.isData
  | _ => false

variable [DecidableEq S] [DecidableEq X] [CodeId X]

/-- A data pattern matches a ground value exactly when they are equal, and
binds nothing. -/
theorem matchT_data_ground : ∀ (gP : GVal S X), gP.isData = true → ∀ (g : GVal S X)
    (σ : GStore S X), matchT σ gP.toTm g.toTm = if gP = g then some σ else Option.none
  | .sym s, _, g, σ => by
      cases g <;> simp [GVal.toTm, matchT]
  | .app f₁ a₁, h, g, σ => by
      simp only [GVal.isData, Bool.and_eq_true] at h
      cases g with
      | app f a =>
          simp only [GVal.toTm, matchT, matchT_data_ground f₁ h.1 f σ]
          by_cases hf : f₁ = f
          · simp only [hf, if_true, matchT_data_ground a₁ h.2 a σ]
            by_cases ha : a₁ = a <;> simp [ha]
          · simp [hf]
      | sym _ => simp [GVal.toTm, matchT]
      | quote _ => simp [GVal.toTm, matchT]
      | ctx _ _ => simp [GVal.toTm, matchT]
  | .quote _, h, _, _ => by simp [GVal.isData] at h
  | .ctx _ _, h, _, _ => by simp [GVal.isData] at h

/-- A ground pattern matches data exactly when they are equal, and binds
nothing. -/
theorem matchT_ground_data : ∀ (g gP : GVal S X), gP.isData = true → ∀ (σ : GStore S X),
    matchT σ g.toTm gP.toTm = if g = gP then some σ else Option.none
  | .sym s, gP, h, σ => by
      cases gP with
      | sym _ => simp [GVal.toTm, matchT]
      | app _ _ => simp [GVal.toTm, matchT]
      | quote _ => simp [GVal.isData] at h
      | ctx _ _ => simp [GVal.isData] at h
  | .app f a, gP, h, σ => by
      cases gP with
      | app f₁ a₁ =>
          simp only [GVal.isData, Bool.and_eq_true] at h
          simp only [GVal.toTm, matchT, matchT_ground_data f f₁ h.1 σ]
          by_cases hf : f = f₁
          · simp only [hf, if_true, matchT_ground_data a a₁ h.2 σ]
            by_cases ha : a = a₁ <;> simp [ha]
          · simp [hf]
      | sym _ => simp [GVal.toTm, matchT]
      | quote _ => simp [GVal.isData] at h
      | ctx _ _ => simp [GVal.isData] at h
  | .quote c, gP, h, σ => by
      cases gP with
      | sym _ => simp [GVal.toTm, matchT]
      | app _ _ => simp [GVal.toTm, matchT]
      | quote _ => simp [GVal.isData] at h
      | ctx _ _ => simp [GVal.isData] at h
  | .ctx ks c, gP, h, σ => by
      cases gP with
      | sym _ => simp [GVal.toTm, matchT]
      | app _ _ => simp [GVal.toTm, matchT]
      | quote _ => simp [GVal.isData] at h
      | ctx _ _ => simp [GVal.isData] at h

/-- **Against data, a term matches as its reading under an earlier store.**
Reading the bound names of the pattern first changes nothing. -/
theorem matchT_act_data : ∀ (t : Tm S X) (gP : GVal S X), gP.isData = true →
    ∀ (σ₀ σ : GStore S X), σ₀ ⊑ σ → matchT σ (act σ₀ t) gP.toTm = matchT σ t gP.toTm
  | .sym _, _, _, _, _, _ | .fn _, _, _, _, _, _ | .pvar _, _, _, _, _, _
  | .quote _, _, _, _, _, _ | .ctx _ _, _, _, _, _, _ => rfl
  | .var n, gP, h, σ₀, σ, hle => by
      rw [act_var]
      cases hσ : σ₀ n with
      | none => rfl
      | some g' =>
          simp only [matchT_ground_data g' gP h σ, matchT, GVal.toTm_toGVal?, refineStep,
            hle n g' hσ]
  | .lam x own b, gP, h, σ₀, σ, _ => by
      rw [act_lam]
      cases gP with
      | sym _ => simp [GVal.toTm, matchT]
      | app _ _ => simp [GVal.toTm, matchT]
      | quote _ => simp [GVal.isData] at h
      | ctx _ _ => simp [GVal.isData] at h
  | .app a b, gP, h, σ₀, σ, hle => by
      rw [act_app]
      cases gP with
      | sym _ => simp [GVal.toTm, matchT]
      | app f₁ a₁ =>
          simp only [GVal.isData, Bool.and_eq_true] at h
          simp only [GVal.toTm, matchT, matchT_act_data a f₁ h.1 σ₀ σ hle]
          cases h₁ : matchT σ a f₁.toTm with
          | none => rfl
          | some σ₁ =>
              exact matchT_act_data b a₁ h.2 σ₀ σ₁ (hle.trans (matchT_mono _ _ _ _ h₁))
      | quote _ => simp [GVal.isData] at h
      | ctx _ _ => simp [GVal.isData] at h
  | .pquote c, gP, h, σ₀, σ, _ => by
      rw [act_pquote]
      cases gP with
      | sym _ => simp [GVal.toTm, matchT]
      | app _ _ => simp [GVal.toTm, matchT]
      | quote _ => simp [GVal.isData] at h
      | ctx _ _ => simp [GVal.isData] at h
  | .letP p w b, gP, h, σ₀, σ, _ => by
      rw [act_letP]
      cases gP with
      | sym _ => simp [GVal.toTm, matchT]
      | app _ _ => simp [GVal.toTm, matchT]
      | quote _ => simp [GVal.isData] at h
      | ctx _ _ => simp [GVal.isData] at h
  | .alt t₁ t₂, gP, h, σ₀, σ, _ => by
      rw [act_alt]
      cases gP with
      | sym _ => simp [GVal.toTm, matchT]
      | app _ _ => simp [GVal.toTm, matchT]
      | quote _ => simp [GVal.isData] at h
      | ctx _ _ => simp [GVal.isData] at h

/-- On a data pattern, `exchange` is the pattern-only matcher with the sides
exchanged. -/
theorem exchange_data_left (gP : GVal S X) (h : gP.isData = true) (σ : GStore S X) (t : Tm S X) :
    exchange σ gP.toTm t = matchT σ t gP.toTm := by
  unfold exchange
  cases hg : (act σ t).toGVal? with
  | some g =>
      have e : g.toTm = act σ t := CloTable.toGVal?_toTm hg
      dsimp only
      rw [← matchT_act_data t gP h σ σ (Store.LE.refl σ), ← e, matchT_data_ground gP h g σ,
        matchT_ground_data g gP h σ]
      by_cases hgg : gP = g
      · simp [hgg]
      · have hgg' : ¬ g = gP := fun e => hgg e.symm
        simp [hgg, hgg']
  | none =>
      dsimp only
      rw [act_toTm, GVal.toTm_toGVal?]
      exact matchT_act_data t gP h σ σ (Store.LE.refl σ)

/-- **The exchange law.**  Against a pattern that is data, the both-sides
matcher is the pattern-only matcher with the sides exchanged: the value is the
pattern, and its unbound names are refined.  For every store and every value. -/
theorem matchT2_data_left : ∀ (gP : GVal S X), gP.isData = true → ∀ (t : Tm S X)
    (σ : GStore S X), matchT2 σ gP.toTm t = matchT σ t gP.toTm
  | .sym s, h, t, σ => by
      have e : matchT2 σ (GVal.sym s).toTm t = exchange σ (GVal.sym s).toTm t := by
        cases t <;> rfl
      rw [e, exchange_data_left _ h]
  | .app f₁ a₁, h, .app t₁ t₂, σ => by
      have h' := h
      simp only [GVal.isData, Bool.and_eq_true] at h'
      simp only [GVal.toTm, matchT2, matchT, matchT2_data_left f₁ h'.1 t₁ σ]
      cases matchT σ t₁ f₁.toTm with
      | none => rfl
      | some σ₁ => exact matchT2_data_left a₁ h'.2 t₂ σ₁
  | .app f₁ a₁, h, .sym _, σ | .app f₁ a₁, h, .fn _, σ | .app f₁ a₁, h, .var _, σ
  | .app f₁ a₁, h, .pvar _, σ | .app f₁ a₁, h, .lam _ _ _, σ | .app f₁ a₁, h, .quote _, σ
  | .app f₁ a₁, h, .pquote _, σ | .app f₁ a₁, h, .ctx _ _, σ | .app f₁ a₁, h, .letP _ _ _, σ
  | .app f₁ a₁, h, .alt _ _, σ => exchange_data_left (.app f₁ a₁) h σ _
  | .quote _, h, _, _ => by simp [GVal.isData] at h
  | .ctx _ _, h, _, _ => by simp [GVal.isData] at h

/-! ## One unfolding of a both-sides `let` with a data pattern -/

omit [DecidableEq S] [DecidableEq X] [CodeId X] in
theorem letLam?_data_left (gP : GVal S X) (V : Tm S X) : letLam? gP.toTm V = Option.none := by
  cases gP <;> rfl

omit [DecidableEq S] [DecidableEq X] [CodeId X] in
theorem letLam?_ground_right (V : Tm S X) (gP : GVal S X) : letLam? V gP.toTm = Option.none := by
  cases V <;> cases gP <;> rfl

/-- **One unfolding.**  A both-sides `let` whose pattern is data unfolds
exactly as the pattern-only `let` with pattern and value exchanged, under one
and the same runner for the sub-evaluations, whenever that runner returns the
value and the pattern unchanged (as every runner does on data at enough fuel).
The pattern-only `let` on the right is `(unify V P B)`: the value-side filling
of the left is written as a `unify` with the sides exchanged. -/
theorem stepDir_let_data_exchange (d : Disc) (prog : S → Option (Tm S X)) (rec : Runner S X)
    (π : Path) (σ : GStore S X) (gP : GVal S X) (hP : gP.isData = true) (V B : Tm S X)
    (hV : rec (π ++ [0]) σ V = some [(V, σ)])
    (hPv : rec (π ++ [0]) σ gP.toTm = some [(gP.toTm, σ)]) :
    stepDir .bothSides d prog rec π σ (.letP gP.toTm V B) =
      step d prog rec π σ (.letP V gP.toTm B) := by
  rw [stepDir_bothSides_letP d prog rec π σ (letLam?_data_left gP V), hV, bindOpt_some_singleton,
    IdSlot.step_letP_none (letLam?_ground_right V gP), hPv, bindOpt_some_singleton]
  have hR : IdSlot.letCont rec π V B (gP.toTm, σ) = letBody rec π B (matchT σ V gP.toTm) := by
    unfold IdSlot.letCont
    simp only [act_toTm, GVal.toTm_toGVal?]
    cases matchT σ V gP.toTm <;> rfl
  have hL : letCont2 rec π gP.toTm B (V, σ) = letBody rec π B (matchT σ V gP.toTm) := by
    have hm : ∀ t, act σ V = t → matchT2 σ gP.toTm t = matchT σ V gP.toTm := by
      rintro t rfl
      rw [matchT2_data_left gP hP, matchT_act_data V gP hP σ σ (Store.LE.refl σ)]
    unfold letCont2
    cases hg : (act σ V).toGVal? with
    | some g =>
        dsimp only
        rw [hm g.toTm (CloTable.toGVal?_toTm hg).symm]
    | none =>
        dsimp only
        cases gP with
        | sym _ => exact congrArg (letBody rec π B) (hm _ rfl)
        | app _ _ => exact congrArg (letBody rec π B) (hm _ rfl)
        | quote _ => simp [GVal.isData] at hP
        | ctx _ _ => simp [GVal.isData] at hP
  rw [hL, hR]

/-! ## What pattern-only cannot write -/

/-- **Pattern-only never writes a store name when the value is not ground.**
The `let` continuation then gives no answer, or enters the body at the store
the value left. -/
theorem letCont_nonground_store (rec : Runner S X) (π : Path) (p b : Tm S X)
    (r : Tm S X × GStore S X) (hg : (act r.2 r.1).toGVal? = Option.none) :
    IdSlot.letCont rec π p b r = some [] ∨
      ∃ b' : Tm S X, IdSlot.letCont rec π p b r = rec (π ++ [1]) r.2 b' := by
  unfold IdSlot.letCont
  rw [hg]
  dsimp only
  cases p with
  | var f =>
      dsimp only
      cases hf : r.2 f with
      | none => exact Or.inr ⟨_, rfl⟩
      | some _ => exact Or.inl rfl
  | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
  | alt _ _ => exact Or.inl rfl

end Mettapedia.GSLT.LanguageDef.TemplateScope
