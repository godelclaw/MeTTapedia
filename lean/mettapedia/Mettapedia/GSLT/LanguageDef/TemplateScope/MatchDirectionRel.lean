import Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirection

/-!
# Template scope: the both-sides matcher on related terms

The simulation between two name disciplines (`IdSlot.Rel`, `IdSlot.sim`) meets
the matcher in one lemma, `Rel.matchT`: related patterns match related ground
values alike, with related stores.  This module proves that lemma for the
first-order part of the both-sides matcher, for every setting.

## Main results

* `Rel.exchange` — related parts are exchanged alike: `exchange` on a related
  pattern part and a related value part returns related stores, or nothing, on
  both sides together.
* `Rel.matchT2` — **related patterns without a quotation pattern on their data
  spine match related values alike under `matchT2`**, ground or not, with
  related stores.  The value-side filling of data keeps the renaming relation.

The hypothesis excludes the one rule this does not cover: a pattern quotation
against a quotation, where `matchCode2` writes holes of the value code.  Those
holes are not free names of the pattern or of the value, so the domain `D` of
`Setting.PatAgree` does not hold them (`IdSlot.not_SC_patAgree2`).  The
simulation itself (`IdSlot.sim`, `IdSlot.simI`) is stated for the pattern-only
evaluator `run`; this module does not restate it for `runDir`.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

section Shapes

variable {S : Type u} {X : Type v} [DecidableEq S] [DecidableEq X] [CodeId X]

/-- No pattern quotation on the data spine of a pattern. -/
def noSpinePQuote : Tm S X → Bool
  | .pquote _ => false
  | .app f a => noSpinePQuote f && noSpinePQuote a
  | _ => true

/-- A lambda in pattern position matches nothing, under both sides. -/
theorem matchT2_lam_none (σ : GStore S X) (x : Nm X) (own : List X) (b t : Tm S X) :
    matchT2 σ (.lam x own b) t = Option.none := by
  have e : matchT2 σ (.lam x own b) t = exchange σ (.lam x own b) t := by cases t <;> rfl
  rw [e]
  unfold exchange
  cases hg : (act σ t).toGVal? with
  | some g =>
      dsimp only
      cases g <;> rfl
  | none =>
      dsimp only
      rw [act_lam]
      rfl

/-- A `let` in pattern position matches nothing, under both sides. -/
theorem matchT2_letP_none (σ : GStore S X) (p w b t : Tm S X) :
    matchT2 σ (.letP p w b) t = Option.none := by
  have e : matchT2 σ (.letP p w b) t = exchange σ (.letP p w b) t := by cases t <;> rfl
  rw [e]
  unfold exchange
  cases hg : (act σ t).toGVal? with
  | some g =>
      dsimp only
      cases g <;> rfl
  | none => rfl

/-- An application of a lambda in pattern position matches nothing, under both
sides. -/
theorem matchT2_app_lam_none (σ : GStore S X) (x : Nm X) (own : List X) (b w t : Tm S X) :
    matchT2 σ (.app (.lam x own b) w) t = Option.none := by
  have hx : exchange σ (.app (.lam x own b) w) t = Option.none := by
    unfold exchange
    cases hg : (act σ t).toGVal? with
    | some g =>
        dsimp only
        cases g with
        | app gf ga =>
            have e : matchT σ (.lam x own b) gf.toTm = Option.none := by cases gf <;> rfl
            show (match matchT σ (.lam x own b) gf.toTm with
              | some σ' => matchT σ' w ga.toTm
              | Option.none => Option.none) = Option.none
            rw [e]
        | sym _ => rfl
        | quote _ => rfl
        | ctx _ _ => rfl
    | none =>
        dsimp only
        rw [act_app, act_lam]
        rfl
  cases t with
  | app tf ta =>
      show (match matchT2 σ (.lam x own b) tf with
        | some σ' => matchT2 σ' w ta
        | Option.none => Option.none) = Option.none
      rw [matchT2_lam_none]
  | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
  | alt _ _ => exact hx

end Shapes

namespace IdSlot

variable {S : Type u} {X₁ X₂ : Type v} [DecidableEq X₁] [DecidableEq X₂]
variable {C : Setting S X₁ X₂}

omit [DecidableEq X₂] in
/-- Applying a store adds no free name. -/
theorem freeNames_act_sub {σ : GStore S X₁} {t : Tm S X₁} {m : Nm X₁}
    (h : m ∈ freeNames (act σ t)) : m ∈ freeNames t := by
  rcases mem_freeNames_subst' t (envSub σ) Sub.none m h with ⟨h1, -⟩ | ⟨n, -, w, hw, hm⟩ |
    ⟨x, -, w, hw, -⟩
  · exact h1
  · simp only [envSub, Option.map_eq_some_iff] at hw
    obtain ⟨g, -, rfl⟩ := hw
    rw [freeNames_toTm] at hm
    cases hm
  · cases hw

/-- A value has no reserved name. -/
theorem Rel.val_res {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ .val Res ok t₁ t₂) : Res = [] := by
  generalize hk : Kd.val = k at h
  induction h with
  | sym _ => rfl
  | fn _ => rfl
  | var _ _ => rfl
  | pvar _ _ => rfl
  | quote _ => rfl
  | ctx _ _ _ => rfl
  | pquote _ _ _ => rfl
  | app _ _ ihf iha => rw [ihf hk, iha hk]; rfl
  | letP hk' => exact absurd hk.symm hk'
  | alt hk' => exact absurd hk.symm hk'
  | lam => rfl
  | letAct hk' => exact absurd hk.symm hk'
  | newAct => cases hk

/-- **Related patterns read back as related ground values**, or as none
together. -/
theorem Rel.toGVal?_pat {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂}
    (h : Rel C ν μ .pat Res ok t₁ t₂) : OptRel (GRel C ν) t₁.toGVal? t₂.toGVal? := by
  generalize hk : Kd.pat = k at h
  induction h with
  | sym s => exact .sym s
  | fn F => trivial
  | var _ _ => trivial
  | pvar _ _ => trivial
  | quote hq => exact .quote hq
  | ctx ho hks hc => exact .ctx ho hks hc
  | pquote _ _ _ =>
      simp only [Tm.toGVal?]
      trivial
  | app _ _ ihf iha =>
      have hf := ihf hk
      have ha := iha hk
      simp only [Tm.toGVal?]
      rcases OptRel.cases hf with ⟨e1, e2⟩ | ⟨f₁, f₂, e1, e2, hf'⟩
      · rw [e1, e2]; trivial
      · rcases OptRel.cases ha with ⟨e3, e4⟩ | ⟨a₁, a₂, e3, e4, ha'⟩
        · rw [e1, e2, e3, e4]; trivial
        · rw [e1, e2, e3, e4]; exact .app hf' ha'
  | letP _ _ _ _ =>
      simp only [Tm.toGVal?]
      trivial
  | alt _ _ _ =>
      simp only [Tm.toGVal?]
      trivial
  | lam => trivial
  | letAct _ _ _ _ _ _ _ _ _ _ =>
      simp only [Tm.toGVal?]
      trivial
  | newAct => cases hk

variable [DecidableEq S] [CodeId X₁] [CodeId X₂]

/-- **Related parts are exchanged alike.**  On a related pattern part and a
related value part, `exchange` returns related stores, or nothing, on both
sides together. -/
theorem Rel.exchange (hC : C.CodeAgree) (hP : C.PatAgree)
    {ν μ : Nm X₁ → Nm X₂} {Rp Rt : List (Nm X₂)} {op ot : Bool} {p₁ t₁ : Tm S X₁}
    {p₂ t₂ : Tm S X₂} (hp : Rel C ν μ .pat Rp op p₁ p₂) (ht : Rel C ν μ .val Rt ot t₁ t₂)
    {D : Set (Nm X₁)} (hDp : ∀ n ∈ freeNames p₁, n ∈ D) (hDt : ∀ n ∈ freeNames t₁, n ∈ D)
    (hSp : SealOK C D p₁) (hSt : SealOK C D t₁)
    (hinj : Set.InjOn ν D) (hI : HoleInj C ν D) (hok : ∀ n ∈ D, OK₁ C n)
    {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} (hσ : StoreRel C ν D σ₁ σ₂)
    (hres : ∀ m ∈ Rp, σ₂ m = Option.none) :
    OptRel (StoreRel C ν D) (TemplateScope.exchange σ₁ p₁ t₁)
      (TemplateScope.exchange σ₂ p₂ t₂) := by
  have hRt := ht.val_res
  subst hRt
  have hat := ht.applyStore hDt hσ hok (fun m hm => by cases hm)
  unfold TemplateScope.exchange
  rcases OptRel.cases hat.toGVal? with ⟨e1, e2⟩ | ⟨g₁, g₂, e1, e2, hgg⟩
  · rw [e1, e2]
    dsimp only
    have hap := hp.applyStore hDp hσ hok hres
    rcases OptRel.cases hap.toGVal?_pat with ⟨e3, e4⟩ | ⟨gp₁, gp₂, e3, e4, hgp⟩
    · rw [e3, e4]
      trivial
    · rw [e3, e4]
      dsimp only
      have hgps : SealOK C D gp₁.toTm := by
        rw [CloTable.toGVal?_toTm e3]
        exact hSp.act hσ.sealOK
      exact (hat.mono (k' := .pat) trivial).matchT hC hP
        (fun n hn => hDt n (freeNames_act_sub hn)) hinj hI (hSt.act hσ.sealOK) hgp hgps hσ
  · rw [e1, e2]
    dsimp only
    have hgs : SealOK C D g₁.toTm := by
      rw [CloTable.toGVal?_toTm e1]
      exact hSt.act hσ.sealOK
    exact hp.matchT hC hP hDp hinj hI hSp hgg hgs hσ

omit [DecidableEq X₂] [DecidableEq S] [CodeId X₁] [CodeId X₂] in
/-- A name the store does not relate to a name in play is unbound. -/
theorem StoreRel.res_unbound {ν : Nm X₁ → Nm X₂} {D : Set (Nm X₁)} {σ₁ : GStore S X₁}
    {σ₂ : GStore S X₂} (hσ : StoreRel C ν D σ₁ σ₂) {R : List (Nm X₂)}
    (hdisj : ∀ n ∈ D, ν n ∉ R) : ∀ m ∈ R, σ₂ m = Option.none := by
  intro m hm
  by_contra hc
  obtain ⟨n, hn, rfl⟩ := hσ.only m hc
  exact hdisj n hn hm

/-- **Related patterns match related values alike under the both-sides
matcher**, when the pattern has no quotation pattern on its data spine: with
related stores, or no match on both sides together.  The value need not be
ground.  `D` holds the free names of the pattern and of the value, `ν` is
injective on it, and no name in play is a reserved name of the pattern. -/
theorem Rel.matchT2 (hC : C.CodeAgree) (hP : C.PatAgree)
    {ν μ : Nm X₁ → Nm X₂} {Rp : List (Nm X₂)} {op : Bool} {p₁ : Tm S X₁} {p₂ : Tm S X₂}
    (hp : Rel C ν μ .pat Rp op p₁ p₂) (hnq : noSpinePQuote p₁ = true) {D : Set (Nm X₁)}
    (hDp : ∀ n ∈ freeNames p₁, n ∈ D) (hSp : SealOK C D p₁) (hinj : Set.InjOn ν D)
    (hI : HoleInj C ν D) (hok : ∀ n ∈ D, OK₁ C n) (hdisj : ∀ n ∈ D, ν n ∉ Rp) :
    ∀ {Rt : List (Nm X₂)} {ot : Bool} {t₁ : Tm S X₁} {t₂ : Tm S X₂},
      Rel C ν μ .val Rt ot t₁ t₂ → (∀ n ∈ freeNames t₁, n ∈ D) → SealOK C D t₁ →
      ∀ {σ₁ : GStore S X₁} {σ₂ : GStore S X₂}, StoreRel C ν D σ₁ σ₂ →
        OptRel (StoreRel C ν D) (TemplateScope.matchT2 σ₁ p₁ t₁)
          (TemplateScope.matchT2 σ₂ p₂ t₂) := by
  generalize hk : Kd.pat = k at hp
  induction hp with
  | sym s =>
      intro Rt ot t₁ t₂ ht hDt hSt σ₁ σ₂ hσ
      have key := Rel.exchange hC hP (.sym (k := .pat) s) ht hDp hDt hSp hSt hinj hI hok hσ
        (fun m hm => by cases hm)
      cases ht <;> exact key
  | fn F =>
      intro Rt ot t₁ t₂ ht hDt hSt σ₁ σ₂ hσ
      have key := Rel.exchange hC hP (.fn (k := .pat) F) ht hDp hDt hSp hSt hinj hI hok hσ
        (fun m hm => by cases hm)
      cases ht <;> exact key
  | var n hv =>
      intro Rt ot t₁ t₂ ht hDt hSt σ₁ σ₂ hσ
      have key := Rel.exchange hC hP (.var (k := .pat) n hv) ht hDp hDt hSp hSt hinj hI hok hσ
        (fun m hm => by cases hm)
      cases ht with
      | var m hm =>
          have hnD : n ∈ D := hDp n (by simp [freeNames])
          have hmD : m ∈ D := hDt m (by simp [freeNames])
          simp only [TemplateScope.matchT2]
          by_cases hnm : n = m
          · rw [if_pos hnm, if_pos (by rw [hnm])]
            exact hσ
          · rw [if_neg hnm, if_neg (fun e => hnm (hinj hnD hmD e))]
            exact key
      | sym _ | fn _ | pvar _ _ | quote _ | pquote _ _ _ | app _ _ | lam | ctx _ _ _ => exact key
      | letP hk' | alt hk' | letAct hk' => exact absurd rfl hk'
  | pvar x hx =>
      intro Rt ot t₁ t₂ ht hDt hSt σ₁ σ₂ hσ
      have key := Rel.exchange hC hP (.pvar (k := .pat) x hx) ht hDp hDt hSp hSt hinj hI hok hσ
        (fun m hm => by cases hm)
      cases ht <;> exact key
  | @quote ν μ k c₁ c₂ hq =>
      intro Rt ot t₁ t₂ ht hDt hSt σ₁ σ₂ hσ
      have key := Rel.exchange hC hP (.quote (k := .pat) hq) ht hDp hDt hSp hSt hinj hI hok hσ
        (fun m hm => by cases hm)
      cases ht with
      | @quote _ _ _ q₁ q₂ hq' =>
          have hinjq := holeRead_injOn hI hq.2.1 hq'.2.1
            (fun n hn => (hSp n (by simpa [sealedFree] using hn)).elim Or.inr
              fun ⟨s, e, _⟩ => Or.inl ⟨s, e⟩)
            (fun n hn => (hSt n (by simpa [sealedFree] using hn)).elim Or.inr
              fun ⟨s, e, _⟩ => Or.inl ⟨s, e⟩)
          simp only [TemplateScope.matchT2]
          cases hce : codeEq c₁ q₁ with
          | true =>
              rw [if_pos rfl, if_pos ((hC ν c₁ c₂ q₁ q₂ hq hq' hinjq).1 hce)]
              exact hσ
          | false =>
              simp only [Bool.false_eq_true, if_false]
              have hne : ¬ codeEq c₂ q₂ = true :=
                fun h => Bool.false_ne_true (hce.symm ▸ (hC ν c₁ c₂ q₁ q₂ hq hq' hinjq).2 h)
              rw [if_neg hne]
              trivial
      | sym _ | fn _ | var _ _ | pvar _ _ | pquote _ _ _ | app _ _ | lam | ctx _ _ _ => exact key
      | letP hk' | alt hk' | letAct hk' => exact absurd rfl hk'
  | pquote _ _ _ => simp [noSpinePQuote] at hnq
  | @app ν μ k R₁ R₂ o₁ o₂ f₁ a₁ f₂ a₂ hf ha ihf iha =>
      intro Rt ot t₁ t₂ ht hDt hSt σ₁ σ₂ hσ
      subst hk
      simp only [noSpinePQuote, Bool.and_eq_true] at hnq
      have hDf : ∀ n ∈ freeNames f₁, n ∈ D := fun n hn => hDp n (by simp [freeNames, hn])
      have hDa : ∀ n ∈ freeNames a₁, n ∈ D := fun n hn => hDp n (by simp [freeNames, hn])
      have hSf : SealOK C D f₁ := fun n hn => hSp n (by simp [sealedFree, hn])
      have hSa : SealOK C D a₁ := fun n hn => hSp n (by simp [sealedFree, hn])
      have hdf : ∀ n ∈ D, ν n ∉ R₁ := fun n hn hm => hdisj n hn (List.mem_append_left _ hm)
      have hda : ∀ n ∈ D, ν n ∉ R₂ := fun n hn hm => hdisj n hn (List.mem_append_right _ hm)
      have key := Rel.exchange hC hP (.app hf ha) ht hDp hDt hSp hSt hinj hI hok hσ
        (hσ.res_unbound hdisj)
      cases ht with
      | @app _ _ _ _ _ _ _ tf ta tf₂ ta₂ htf hta =>
          have hDtf : ∀ n ∈ freeNames tf, n ∈ D := fun n hn => hDt n (by simp [freeNames, hn])
          have hDta : ∀ n ∈ freeNames ta, n ∈ D := fun n hn => hDt n (by simp [freeNames, hn])
          have hStf : SealOK C D tf := fun n hn => hSt n (by simp [sealedFree, hn])
          have hSta : SealOK C D ta := fun n hn => hSt n (by simp [sealedFree, hn])
          simp only [TemplateScope.matchT2]
          rcases OptRel.cases (ihf hnq.1 hDf hSf hinj hI hdf rfl htf hDtf hStf hσ) with
              ⟨e1, e2⟩ | ⟨τ₁, τ₂, e1, e2, hτ⟩
          · rw [e1, e2]
            trivial
          · rw [e1, e2]
            exact iha hnq.2 hDa hSa hinj hI hda rfl hta hDta hSta hτ
      | sym _ | fn _ | var _ _ | pvar _ _ | quote _ | pquote _ _ _ | lam | ctx _ _ _ => exact key
      | letP hk' | alt hk' | letAct hk' => exact absurd rfl hk'
  | @letP ν μ k Rp' Rw Rb op' ow ob p₁' w₁ b₁ p₂' w₂ b₂ hk' hp' hw hb =>
      intro Rt ot t₁ t₂ ht hDt hSt σ₁ σ₂ hσ
      rw [matchT2_letP_none, matchT2_letP_none]
      trivial
  | @alt ν μ k R₁ R₂ o₁ o₂ t₁' u₁ t₂' u₂ hk' h₁ h₂ =>
      intro Rt ot t₁ t₂ ht hDt hSt σ₁ σ₂ hσ
      subst hk
      have key := Rel.exchange hC hP (.alt hk' h₁ h₂) ht hDp hDt hSp hSt hinj hI hok hσ
        (hσ.res_unbound hdisj)
      cases ht <;> exact key
  | lam =>
      intro Rt ot t₁ t₂ ht hDt hSt σ₁ σ₂ hσ
      rw [matchT2_lam_none, matchT2_lam_none]
      trivial
  | letAct =>
      intro Rt ot t₁ t₂ ht hDt hSt σ₁ σ₂ hσ
      rw [matchT2_app_lam_none, matchT2_letP_none]
      trivial
  | @ctx ν μ k ks₁ c₁ ks₂ c₂ ho hks hc =>
      intro Rt ot t₁ t₂ ht hDt hSt σ₁ σ₂ hσ
      have key := Rel.exchange hC hP (.ctx (k := .pat) ho hks hc) ht hDp hDt hSp hSt hinj hI hok hσ
        (fun m hm => by cases hm)
      cases ht <;> exact key
  | newAct => cases hk

end IdSlot

end Mettapedia.GSLT.LanguageDef.TemplateScope
