import Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirection
import Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotRenaming

/-!
# Template scope: the frame of a `let`

Which store names a `let` may write, under each matching direction.

## Pattern-only

* `matchT_frame` — **the frame of a pattern-only match**: the store after the
  match differs from the store before only at the store names the matcher
  reaches in the pattern (`matchHoles`: the pattern's data spine and the code of
  its pattern quotations).  For every store, pattern and value.
* `letCont_frame` — hence, for every runner, the `let` continuation enters the
  body at a store that differs from the store its value left only at those
  names, or gives no answer.  Every `let` of every program is an instance.
* `matchHoles_elabLF`, `matchHoles_subst`, `let_frame_LF` — **under lexical
  fresh**: a name the match of a `let` writes is the current copy of a slot the
  pattern introduced, or of a slot the pattern shares (a name in force, or a
  hole of a quotation pattern that the pattern does not also write on its
  spine), or a store name of the value passed in for a parameter the pattern
  writes.
* `let_frame_LF_introduced` — the statement asked for: when every name the
  pattern writes is introduced and no parameter of the pattern is instantiated,
  the store differs only at the copies of the names the pattern introduced.
  Both side conditions are needed: `MatchDirectionExamples.frame_needs_*`.

## Both sides

* `matchT2_frame` — the store after a both-sides match differs from the store
  before only at names the matcher reaches in the pattern or names written in
  the value.  The pattern-only frame fails: `matchT2_writes_value_name`.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

/-! ## Refinement writes one name -/

section Refine

variable {N V : Type*} [DecidableEq N] [DecidableEq V]

/-- A refinement step changes the store at most at its name. -/
theorem refineStep_frame {s s' : Store N V} {p : N × V} (h : refineStep s p = some s') {m : N}
    (hm : m ≠ p.1) : s' m = s m := by
  unfold refineStep at h
  cases hs : s p.1 with
  | none =>
      rw [hs] at h
      injection h with h
      subst h
      simp [hm]
  | some w =>
      rw [hs] at h
      by_cases hw : w = p.2
      · simp only [hw, if_true] at h
        injection h with h
        rw [h]
      · simp [hw] at h

end Refine

variable {S : Type u} {X : Type v}

/-! ## The names a match reaches -/

/-- **The store names `matchT` reaches in a pattern**: those on its data spine,
and those of the code of its pattern quotations. -/
def matchHoles : Tm S X → List (Nm X)
  | .var n => [n]
  | .app p₁ p₂ => matchHoles p₁ ++ matchHoles p₂
  | .pquote c => codeHoles c
  | _ => []

/-- The parameters written in pattern code, bound or free. -/
def codeParams : Tm S X → List (Nm X)
  | .pvar x => [x]
  | .lam _ _ b => codeParams b
  | .app f a => codeParams f ++ codeParams a
  | .letP p w b => codeParams p ++ codeParams w ++ codeParams b
  | .alt a b => codeParams a ++ codeParams b
  | .pquote c => codeParams c
  | _ => []

/-- **The parameters `matchT` reaches in a pattern**: on its data spine, and in
the code of its pattern quotations.  A value passed in for one of them stands
where the matcher writes. -/
def matchParams : Tm S X → List (Nm X)
  | .pvar x => [x]
  | .app p₁ p₂ => matchParams p₁ ++ matchParams p₂
  | .pquote c => codeParams c
  | _ => []

theorem codeHoles_sub_vars {n : Nm X} : ∀ {c : Tm S X}, n ∈ codeHoles c → n ∈ Tm.vars c
  | .var _, h => by simpa [codeHoles, Tm.vars] using h
  | .lam _ _ b, h => by
      simp only [codeHoles] at h
      simp only [Tm.vars]
      exact codeHoles_sub_vars h
  | .app f a, h => by
      simp only [codeHoles, List.mem_append] at h
      simp only [Tm.vars, List.mem_append]
      exact h.imp codeHoles_sub_vars codeHoles_sub_vars
  | .letP p w b, h => by
      simp only [codeHoles, List.mem_append] at h
      simp only [Tm.vars, List.mem_append]
      exact h.imp (Or.imp codeHoles_sub_vars codeHoles_sub_vars) codeHoles_sub_vars
  | .alt a b, h => by
      simp only [codeHoles, List.mem_append] at h
      simp only [Tm.vars, List.mem_append]
      exact h.imp codeHoles_sub_vars codeHoles_sub_vars
  | .pquote c, h => by
      simp only [codeHoles] at h
      simp only [Tm.vars]
      exact codeHoles_sub_vars h
  | .sym _, h | .fn _, h | .pvar _, h | .quote _, h | .ctx _ _, h => by simp [codeHoles] at h

theorem matchHoles_sub_vars {n : Nm X} : ∀ {p : Tm S X}, n ∈ matchHoles p → n ∈ Tm.vars p
  | .var _, h => by simpa [matchHoles, Tm.vars] using h
  | .app f a, h => by
      simp only [matchHoles, List.mem_append] at h
      simp only [Tm.vars, List.mem_append]
      exact h.imp matchHoles_sub_vars matchHoles_sub_vars
  | .pquote c, h => by
      simp only [matchHoles] at h
      simp only [Tm.vars]
      exact codeHoles_sub_vars h
  | .sym _, h | .fn _, h | .pvar _, h | .lam _ _ _, h | .quote _, h | .ctx _ _, h
  | .letP _ _ _, h | .alt _ _, h => by simp [matchHoles] at h

/-- A ground value has no store name the matcher reaches. -/
theorem codeHoles_toTm : ∀ g : GVal S X, codeHoles g.toTm = []
  | .sym _ => rfl
  | .app f a => by simp [GVal.toTm, codeHoles, codeHoles_toTm f, codeHoles_toTm a]
  | .quote _ => rfl
  | .ctx _ _ => rfl

theorem matchHoles_toTm : ∀ g : GVal S X, matchHoles g.toTm = []
  | .sym _ => rfl
  | .app f a => by simp [GVal.toTm, matchHoles, matchHoles_toTm f, matchHoles_toTm a]
  | .quote _ => rfl
  | .ctx _ _ => rfl

variable [DecidableEq X]

/-- Applying a store adds no store name to code. -/
theorem codeHoles_act {n : Nm X} : ∀ (c : Tm S X) (σ : GStore S X),
    n ∈ codeHoles (act σ c) → n ∈ codeHoles c
  | .var m, σ, h => by
      rw [act_var] at h
      cases hσ : σ m with
      | none => rw [hσ] at h; exact h
      | some g =>
          rw [hσ] at h
          simp only [codeHoles_toTm] at h
          cases h
  | .lam x own b, σ, h => by
      rw [act_lam] at h
      simp only [codeHoles] at h ⊢
      exact codeHoles_act b _ h
  | .app f a, σ, h => by
      simp only [act_app, codeHoles, List.mem_append] at h ⊢
      exact h.imp (codeHoles_act f σ) (codeHoles_act a σ)
  | .letP p w b, σ, h => by
      simp only [act_letP, codeHoles, List.mem_append] at h ⊢
      exact h.imp (Or.imp (codeHoles_act p σ) (codeHoles_act w σ)) (codeHoles_act b σ)
  | .alt a b, σ, h => by
      simp only [act_alt, codeHoles, List.mem_append] at h ⊢
      exact h.imp (codeHoles_act a σ) (codeHoles_act b σ)
  | .pquote c, σ, h => by
      simp only [act_pquote, codeHoles] at h ⊢
      exact codeHoles_act c σ h
  | .sym _, _, h | .fn _, _, h | .pvar _, _, h | .quote _, _, h | .ctx _ _, _, h => h

/-- Applying a store adds no store name to a pattern. -/
theorem matchHoles_act {n : Nm X} : ∀ (p : Tm S X) (σ : GStore S X),
    n ∈ matchHoles (act σ p) → n ∈ matchHoles p
  | .var m, σ, h => by
      rw [act_var] at h
      cases hσ : σ m with
      | none => rw [hσ] at h; exact h
      | some g =>
          rw [hσ] at h
          simp only [matchHoles_toTm] at h
          cases h
  | .app f a, σ, h => by
      simp only [act_app, matchHoles, List.mem_append] at h ⊢
      exact h.imp (matchHoles_act f σ) (matchHoles_act a σ)
  | .pquote c, σ, h => by
      simp only [act_pquote, matchHoles] at h ⊢
      exact codeHoles_act c σ h
  | .lam x own b, σ, h => by
      rw [act_lam] at h
      simp [matchHoles] at h
  | .sym _, _, h | .fn _, _, h | .pvar _, _, h | .quote _, _, h | .ctx _ _, _, h
  | .letP _ _ _, _, h | .alt _ _, _, h => h

variable [DecidableEq S] [CodeId X]

/-! ## The frame of a pattern-only match -/

/-- **The frame of pattern-only code matching.**  The store changes only at
store names the matcher reaches in the pattern code. -/
theorem matchCodeIn_frame {n : Nm X} : ∀ (bound : List (Nm X)) (p t : Tm S X) (σ σ' : GStore S X),
    matchCodeIn σ bound p t = some σ' → n ∉ codeHoles p → σ' n = σ n
  | bound, .var m, t, σ, σ', h, hn => by
      simp only [matchCodeIn] at h
      have hnm : n ≠ m := fun e => hn (by simp [codeHoles, e])
      cases hhm : CodeId.hole m with
      | true =>
          simp only [hhm, if_true] at h
          cases hg : contextualVal bound t with
          | none => simp [hg] at h
          | some g =>
              simp only [hg] at h
              exact refineStep_frame h hnm
      | false =>
          simp only [hhm, Bool.false_eq_true, if_false] at h
          cases t with
          | var k =>
              simp only at h
              split at h
              · injection h with h; rw [h]
              · cases h
          | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
          | alt _ _ => cases h
  | _, .pvar x, t, σ, σ', h, _ => by
      cases t with
      | pvar y =>
          simp only [matchCodeIn] at h
          split at h
          · injection h with h; rw [h]
          · cases h
      | sym _ | fn _ | var _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCodeIn] at h
  | bound, .lam x₁ own₁ b₁, t, σ, σ', h, hn => by
      cases t with
      | lam x₂ own₂ b₂ =>
          simp only [matchCodeIn] at h
          split at h
          · exact matchCodeIn_frame (bound ++ [x₂]) b₁ b₂ σ σ' h (by simpa [codeHoles] using hn)
          · cases h
      | sym _ | fn _ | var _ | pvar _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCodeIn] at h
  | bound, .app p₁ p₂, t, σ, σ', h, hn => by
      simp only [codeHoles, List.mem_append, not_or] at hn
      cases t with
      | app t₁ t₂ =>
          simp only [matchCodeIn] at h
          cases h₁ : matchCodeIn σ bound p₁ t₁ with
          | none => simp [h₁] at h
          | some σ₁ =>
              simp only [h₁] at h
              rw [matchCodeIn_frame bound p₂ t₂ σ₁ σ' h hn.2,
                matchCodeIn_frame bound p₁ t₁ σ σ₁ h₁ hn.1]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCodeIn] at h
  | bound, .letP p₁ w₁ b₁, t, σ, σ', h, hn => by
      simp only [codeHoles, List.mem_append, not_or] at hn
      cases t with
      | letP p₂ w₂ b₂ =>
          simp only [matchCodeIn] at h
          cases h₁ : matchCodeIn σ bound p₁ p₂ with
          | none => simp [h₁] at h
          | some σ₁ =>
              simp only [h₁] at h
              cases h₂ : matchCodeIn σ₁ bound w₁ w₂ with
              | none => simp [h₂] at h
              | some σ₂ =>
                  simp only [h₂] at h
                  rw [matchCodeIn_frame bound b₁ b₂ σ₂ σ' h hn.2,
                    matchCodeIn_frame bound w₁ w₂ σ₁ σ₂ h₂ hn.1.2,
                    matchCodeIn_frame bound p₁ p₂ σ σ₁ h₁ hn.1.1]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _
      | alt _ _ => simp [matchCodeIn] at h
  | bound, .alt p₁ p₂, t, σ, σ', h, hn => by
      simp only [codeHoles, List.mem_append, not_or] at hn
      cases t with
      | alt t₁ t₂ =>
          simp only [matchCodeIn] at h
          cases h₁ : matchCodeIn σ bound p₁ t₁ with
          | none => simp [h₁] at h
          | some σ₁ =>
              simp only [h₁] at h
              rw [matchCodeIn_frame bound p₂ t₂ σ₁ σ' h hn.2,
                matchCodeIn_frame bound p₁ t₁ σ σ₁ h₁ hn.1]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _
      | letP _ _ _ => simp [matchCodeIn] at h
  | _, .sym _, t, σ, σ', h, _ => by
      cases t with
      | sym _ =>
          simp only [matchCodeIn] at h
          split at h
          · injection h with h; rw [h]
          · cases h
      | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCodeIn] at h
  | _, .fn _, t, σ, σ', h, _ => by
      cases t with
      | fn _ =>
          simp only [matchCodeIn] at h
          split at h
          · injection h with h; rw [h]
          · cases h
      | sym _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCodeIn] at h
  | _, .quote _, t, σ, σ', h, _ => by
      cases t with
      | quote _ =>
          simp only [matchCodeIn] at h
          split at h
          · injection h with h; rw [h]
          · cases h
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCodeIn] at h
  | bound, .pquote pc, t, σ, σ', h, hn => by
      cases t with
      | quote c =>
          simp only [matchCodeIn] at h
          exact matchCodeIn_frame bound pc c σ σ' h (by simpa [codeHoles] using hn)
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCodeIn] at h
  | _, .ctx _ _, t, σ, σ', h, _ => by simp [matchCodeIn] at h

/-- **The frame of a pattern-only match.**  For every store, pattern and value:
the store after the match differs from the store before only at the store names
the matcher reaches in the pattern. -/
theorem matchT_frame {n : Nm X} : ∀ (p t : Tm S X) (σ σ' : GStore S X),
    matchT σ p t = some σ' → n ∉ matchHoles p → σ' n = σ n
  | .var m, t, σ, σ', h, hn => by
      simp only [matchT] at h
      have hnm : n ≠ m := fun e => hn (by simp [matchHoles, e])
      cases hg : t.toGVal? with
      | none => simp [hg] at h
      | some g =>
          simp only [hg] at h
          exact refineStep_frame h hnm
  | .app p₁ p₂, .app t₁ t₂, σ, σ', h, hn => by
      simp only [matchHoles, List.mem_append, not_or] at hn
      simp only [matchT] at h
      cases h₁ : matchT σ p₁ t₁ with
      | none => simp [h₁] at h
      | some σ₁ =>
          simp only [h₁] at h
          rw [matchT_frame p₂ t₂ σ₁ σ' h hn.2, matchT_frame p₁ t₁ σ σ₁ h₁ hn.1]
  | .pquote pc, .quote c, σ, σ', h, hn => by
      simp only [matchT] at h
      exact matchCodeIn_frame [] pc c σ σ' h (by simpa [matchHoles] using hn)
  | .quote c₁, .quote c₂, σ, σ', h, _ => by
      simp only [matchT] at h
      split at h
      · injection h with h; rw [h]
      · cases h
  | .app _ _, .sym _, σ, σ', h, _ | .app _ _, .fn _, σ, σ', h, _ | .app _ _, .var _, σ, σ', h, _
  | .app _ _, .pvar _, σ, σ', h, _ | .app _ _, .lam _ _ _, σ, σ', h, _
  | .app _ _, .quote _, σ, σ', h, _ | .app _ _, .pquote _, σ, σ', h, _
  | .app _ _, .letP _ _ _, σ, σ', h, _ | .app _ _, .alt _ _, σ, σ', h, _
  | .app _ _, .ctx _ _, σ, σ', h, _
  | .pquote _, .sym _, σ, σ', h, _ | .pquote _, .fn _, σ, σ', h, _ | .pquote _, .var _, σ, σ', h, _
  | .pquote _, .pvar _, σ, σ', h, _ | .pquote _, .lam _ _ _, σ, σ', h, _
  | .pquote _, .app _ _, σ, σ', h, _ | .pquote _, .pquote _, σ, σ', h, _
  | .pquote _, .letP _ _ _, σ, σ', h, _ | .pquote _, .alt _ _, σ, σ', h, _
  | .pquote _, .ctx _ _, σ, σ', h, _
  | .quote _, .sym _, σ, σ', h, _ | .quote _, .fn _, σ, σ', h, _ | .quote _, .var _, σ, σ', h, _
  | .quote _, .pvar _, σ, σ', h, _ | .quote _, .lam _ _ _, σ, σ', h, _
  | .quote _, .app _ _, σ, σ', h, _ | .quote _, .pquote _, σ, σ', h, _
  | .quote _, .letP _ _ _, σ, σ', h, _ | .quote _, .alt _ _, σ, σ', h, _
  | .quote _, .ctx _ _, σ, σ', h, _
  | .sym _, _, σ, σ', h, _ | .fn _, _, σ, σ', h, _ | .pvar _, _, σ, σ', h, _
  | .lam _ _ _, _, σ, σ', h, _ | .letP _ _ _, _, σ, σ', h, _ | .alt _ _, _, σ, σ', h, _
  | .ctx _ _, _, σ, σ', h, _ => by
      simp only [matchT] at h
      split at h
      · injection h with h; rw [h]
      · cases h

/-- **The frame of a pattern-only `let`, for every runner.**  On one value of
its right-hand side, the `let` continuation gives no answer, or enters the body
at a store that differs from the store the value left only at the store names
the matcher reaches in the pattern.  When the value is not ground the store is
unchanged. -/
theorem letCont_frame (rec : Runner S X) (π : Path) (p b : Tm S X) (r : Tm S X × GStore S X) :
    IdSlot.letCont rec π p b r = some [] ∨
      ∃ (σ₂ : GStore S X) (b' : Tm S X), IdSlot.letCont rec π p b r = rec (π ++ [1]) σ₂ b' ∧
        ∀ n, n ∉ matchHoles p → σ₂ n = r.2 n := by
  unfold IdSlot.letCont
  cases hg : (act r.2 r.1).toGVal? with
  | some g =>
      dsimp only
      cases hm : matchT r.2 p g.toTm with
      | some σ₂ => exact Or.inr ⟨σ₂, b, rfl, fun n hn => matchT_frame p g.toTm r.2 σ₂ hm hn⟩
      | none => exact Or.inl rfl
  | none =>
      dsimp only
      cases p with
      | var f =>
          dsimp only
          cases hf : r.2 f with
          | none => exact Or.inr ⟨r.2, _, rfl, fun _ _ => rfl⟩
          | some _ => exact Or.inl rfl
      | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => exact Or.inl rfl

/-! ## The frame of a both-sides match -/

/-- The frame of `exchange`: names the matcher reaches in either part. -/
theorem exchange_frame {n : Nm X} (σ σ' : GStore S X) (p t : Tm S X)
    (h : exchange σ p t = some σ') (hp : n ∉ matchHoles p) (ht : n ∉ matchHoles t) :
    σ' n = σ n := by
  unfold exchange at h
  cases hg : (act σ t).toGVal? with
  | some g =>
      rw [hg] at h
      exact matchT_frame p g.toTm σ σ' h hp
  | none =>
      rw [hg] at h
      cases hg' : (act σ p).toGVal? with
      | some g =>
          rw [hg'] at h
          exact matchT_frame (act σ t) g.toTm σ σ' h (fun hn => ht (matchHoles_act t σ hn))
      | none => rw [hg'] at h; cases h

/-- **The frame of both-sides code matching.**  The store changes only at store
names the matcher reaches in the pattern code, or names written in the value
code. -/
theorem matchCode2In_frame {n : Nm X} : ∀ (bound : List (Nm X)) (p t : Tm S X) (σ σ' : GStore S X),
    matchCode2In σ bound p t = some σ' → n ∉ codeHoles p → n ∉ Tm.vars t → σ' n = σ n
  | bound, .var m, t, σ, σ', h, hn, ht => by
      simp only [matchCode2In] at h
      have hnm : n ≠ m := fun e => hn (by simp [codeHoles, e])
      cases hhm : CodeId.hole m with
      | true =>
          simp only [hhm, if_true] at h
          cases hg : contextualVal bound t with
          | some g =>
              simp only [hg] at h
              exact refineStep_frame h hnm
          | none =>
              simp only [hg] at h
              cases t with
              | var k =>
                  have hnk : n ≠ k := fun e => ht (by simp [Tm.vars, e])
                  simp only at h
                  split at h
                  · cases hk : σ k with
                    | some g =>
                        simp only [hk] at h
                        exact refineStep_frame h hnm
                    | none =>
                        simp only [hk] at h
                        cases hm' : σ m with
                        | some g =>
                            simp only [hm'] at h
                            exact refineStep_frame h hnk
                        | none =>
                            simp only [hm'] at h
                            split at h
                            · injection h with h; rw [h]
                            · cases h
                  · cases h
              | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _
              | letP _ _ _ | alt _ _ => cases h
      | false =>
          simp only [hhm, Bool.false_eq_true, if_false] at h
          cases t with
          | var k =>
              simp only at h
              split at h
              · injection h with h; rw [h]
              · cases h
          | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
          | alt _ _ => cases h
  | bound, .pvar x, t, σ, σ', h, _, ht => by
      cases t with
      | pvar y =>
          simp only [matchCode2In] at h
          split at h
          · injection h with h; rw [h]
          · cases h
      | var k =>
          have hnk : n ≠ k := fun e => ht (by simp [Tm.vars, e])
          simp only [matchCode2In] at h
          split at h
          · cases hf : holeFill σ bound (.pvar x : Tm S X) with
            | none => simp [hf] at h
            | some g =>
                simp only [hf] at h
                exact refineStep_frame h hnk
          · cases h
      | sym _ | fn _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCode2In] at h
  | bound, .lam x₁ own₁ b₁, t, σ, σ', h, hn, ht => by
      cases t with
      | lam x₂ own₂ b₂ =>
          simp only [matchCode2In] at h
          split at h
          · exact matchCode2In_frame (bound ++ [x₂]) b₁ b₂ σ σ' h (by simpa [codeHoles] using hn)
              (by simpa [Tm.vars] using ht)
          · cases h
      | var k =>
          have hnk : n ≠ k := fun e => ht (by simp [Tm.vars, e])
          simp only [matchCode2In] at h
          split at h
          · cases hf : holeFill σ bound (.lam x₁ own₁ b₁ : Tm S X) with
            | none => simp [hf] at h
            | some g =>
                simp only [hf] at h
                exact refineStep_frame h hnk
          · cases h
      | sym _ | fn _ | pvar _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCode2In] at h
  | bound, .app p₁ p₂, t, σ, σ', h, hn, ht => by
      simp only [codeHoles, List.mem_append, not_or] at hn
      cases t with
      | app t₁ t₂ =>
          simp only [Tm.vars, List.mem_append, not_or] at ht
          simp only [matchCode2In] at h
          cases h₁ : matchCode2In σ bound p₁ t₁ with
          | none => simp [h₁] at h
          | some σ₁ =>
              simp only [h₁] at h
              rw [matchCode2In_frame bound p₂ t₂ σ₁ σ' h hn.2 ht.2,
                matchCode2In_frame bound p₁ t₁ σ σ₁ h₁ hn.1 ht.1]
      | var k =>
          have hnk : n ≠ k := fun e => ht (by simp [Tm.vars, e])
          simp only [matchCode2In] at h
          split at h
          · cases hf : holeFill σ bound (.app p₁ p₂ : Tm S X) with
            | none => simp [hf] at h
            | some g =>
                simp only [hf] at h
                exact refineStep_frame h hnk
          · cases h
      | sym _ | fn _ | pvar _ | lam _ _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCode2In] at h
  | bound, .letP p₁ w₁ b₁, t, σ, σ', h, hn, ht => by
      simp only [codeHoles, List.mem_append, not_or] at hn
      cases t with
      | letP p₂ w₂ b₂ =>
          simp only [Tm.vars, List.mem_append, not_or] at ht
          simp only [matchCode2In] at h
          cases h₁ : matchCode2In σ bound p₁ p₂ with
          | none => simp [h₁] at h
          | some σ₁ =>
              simp only [h₁] at h
              cases h₂ : matchCode2In σ₁ bound w₁ w₂ with
              | none => simp [h₂] at h
              | some σ₂ =>
                  simp only [h₂] at h
                  rw [matchCode2In_frame bound b₁ b₂ σ₂ σ' h hn.2 ht.2,
                    matchCode2In_frame bound w₁ w₂ σ₁ σ₂ h₂ hn.1.2 ht.1.2,
                    matchCode2In_frame bound p₁ p₂ σ σ₁ h₁ hn.1.1 ht.1.1]
      | var k =>
          have hnk : n ≠ k := fun e => ht (by simp [Tm.vars, e])
          simp only [matchCode2In] at h
          split at h
          · cases hf : holeFill σ bound (.letP p₁ w₁ b₁ : Tm S X) with
            | none => simp [hf] at h
            | some g =>
                simp only [hf] at h
                exact refineStep_frame h hnk
          · cases h
      | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _
      | alt _ _ => simp [matchCode2In] at h
  | bound, .alt p₁ p₂, t, σ, σ', h, hn, ht => by
      simp only [codeHoles, List.mem_append, not_or] at hn
      cases t with
      | alt t₁ t₂ =>
          simp only [Tm.vars, List.mem_append, not_or] at ht
          simp only [matchCode2In] at h
          cases h₁ : matchCode2In σ bound p₁ t₁ with
          | none => simp [h₁] at h
          | some σ₁ =>
              simp only [h₁] at h
              rw [matchCode2In_frame bound p₂ t₂ σ₁ σ' h hn.2 ht.2,
                matchCode2In_frame bound p₁ t₁ σ σ₁ h₁ hn.1 ht.1]
      | var k =>
          have hnk : n ≠ k := fun e => ht (by simp [Tm.vars, e])
          simp only [matchCode2In] at h
          split at h
          · cases hf : holeFill σ bound (.alt p₁ p₂ : Tm S X) with
            | none => simp [hf] at h
            | some g =>
                simp only [hf] at h
                exact refineStep_frame h hnk
          · cases h
      | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _
      | letP _ _ _ => simp [matchCode2In] at h
  | bound, .sym s, t, σ, σ', h, _, ht => by
      cases t with
      | sym _ =>
          simp only [matchCode2In] at h
          split at h
          · injection h with h; rw [h]
          · cases h
      | var k =>
          have hnk : n ≠ k := fun e => ht (by simp [Tm.vars, e])
          simp only [matchCode2In] at h
          split at h
          · cases hf : holeFill σ bound (.sym s : Tm S X) with
            | none => simp [hf] at h
            | some g =>
                simp only [hf] at h
                exact refineStep_frame h hnk
          · cases h
      | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCode2In] at h
  | bound, .fn F, t, σ, σ', h, _, ht => by
      cases t with
      | fn _ =>
          simp only [matchCode2In] at h
          split at h
          · injection h with h; rw [h]
          · cases h
      | var k =>
          have hnk : n ≠ k := fun e => ht (by simp [Tm.vars, e])
          simp only [matchCode2In] at h
          split at h
          · cases hf : holeFill σ bound (.fn F : Tm S X) with
            | none => simp [hf] at h
            | some g =>
                simp only [hf] at h
                exact refineStep_frame h hnk
          · cases h
      | sym _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCode2In] at h
  | bound, .quote c₁, t, σ, σ', h, _, ht => by
      cases t with
      | quote _ =>
          simp only [matchCode2In] at h
          split at h
          · injection h with h; rw [h]
          · cases h
      | var k =>
          have hnk : n ≠ k := fun e => ht (by simp [Tm.vars, e])
          simp only [matchCode2In] at h
          split at h
          · cases hf : holeFill σ bound (.quote c₁ : Tm S X) with
            | none => simp [hf] at h
            | some g =>
                simp only [hf] at h
                exact refineStep_frame h hnk
          · cases h
      | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCode2In] at h
  | bound, .pquote pc, t, σ, σ', h, hn, ht => by
      cases t with
      | quote c =>
          simp only [matchCode2In] at h
          exact matchCode2In_frame bound pc c σ σ' h (by simpa [codeHoles] using hn)
            (by simpa [Tm.vars] using ht)
      | var k =>
          have hnk : n ≠ k := fun e => ht (by simp [Tm.vars, e])
          simp only [matchCode2In] at h
          split at h
          · cases hf : holeFill σ bound (.pquote pc : Tm S X) with
            | none => simp [hf] at h
            | some g =>
                simp only [hf] at h
                exact refineStep_frame h hnk
          · cases h
      | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCode2In] at h
  | bound, .ctx ks c, t, σ, σ', h, _, ht => by
      cases t with
      | var k =>
          have hnk : n ≠ k := fun e => ht (by simp [Tm.vars, e])
          simp only [matchCode2In] at h
          split at h
          · cases hf : holeFill σ bound (.ctx ks c : Tm S X) with
            | none => simp [hf] at h
            | some g =>
                simp only [hf] at h
                exact refineStep_frame h hnk
          · cases h
      | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCode2In] at h

/-- **The frame of a both-sides match.**  The store after the match differs
from the store before only at store names the matcher reaches in the pattern,
or names written in the value. -/
theorem matchT2_frame {n : Nm X} : ∀ (p t : Tm S X) (σ σ' : GStore S X),
    matchT2 σ p t = some σ' → n ∉ matchHoles p → n ∉ Tm.vars t → σ' n = σ n
  | .app p₁ p₂, .app t₁ t₂, σ, σ', h, hn, ht => by
      simp only [matchHoles, List.mem_append, not_or] at hn
      simp only [Tm.vars, List.mem_append, not_or] at ht
      simp only [matchT2] at h
      cases h₁ : matchT2 σ p₁ t₁ with
      | none => simp [h₁] at h
      | some σ₁ =>
          simp only [h₁] at h
          rw [matchT2_frame p₂ t₂ σ₁ σ' h hn.2 ht.2, matchT2_frame p₁ t₁ σ σ₁ h₁ hn.1 ht.1]
  | .pquote pc, .quote c, σ, σ', h, hn, ht => by
      simp only [matchT2] at h
      exact matchCode2In_frame [] pc c σ σ' h (by simpa [matchHoles] using hn)
        (by simpa [Tm.vars] using ht)
  | .quote c₁, .quote c₂, σ, σ', h, _, _ => by
      simp only [matchT2] at h
      split at h
      · injection h with h; rw [h]
      · cases h
  | .var k, .var m, σ, σ', h, hn, ht => by
      simp only [matchT2] at h
      split at h
      · injection h with h; rw [h]
      · exact exchange_frame σ σ' _ _ h hn (fun hm => ht (matchHoles_sub_vars hm))
  | .app p₁ p₂, .sym s, σ, σ', h, hn, ht | .app p₁ p₂, .fn s, σ, σ', h, hn, ht
  | .app p₁ p₂, .var s, σ, σ', h, hn, ht | .app p₁ p₂, .pvar s, σ, σ', h, hn, ht
  | .app p₁ p₂, .lam _ _ _, σ, σ', h, hn, ht | .app p₁ p₂, .quote _, σ, σ', h, hn, ht
  | .app p₁ p₂, .pquote _, σ, σ', h, hn, ht | .app p₁ p₂, .letP _ _ _, σ, σ', h, hn, ht
  | .app p₁ p₂, .alt _ _, σ, σ', h, hn, ht | .app p₁ p₂, .ctx _ _, σ, σ', h, hn, ht
  | .pquote pc, .sym _, σ, σ', h, hn, ht | .pquote pc, .fn _, σ, σ', h, hn, ht
  | .pquote pc, .var _, σ, σ', h, hn, ht | .pquote pc, .pvar _, σ, σ', h, hn, ht
  | .pquote pc, .lam _ _ _, σ, σ', h, hn, ht | .pquote pc, .app _ _, σ, σ', h, hn, ht
  | .pquote pc, .pquote _, σ, σ', h, hn, ht | .pquote pc, .letP _ _ _, σ, σ', h, hn, ht
  | .pquote pc, .alt _ _, σ, σ', h, hn, ht | .pquote pc, .ctx _ _, σ, σ', h, hn, ht
  | .quote c₁, .sym _, σ, σ', h, hn, ht | .quote c₁, .fn _, σ, σ', h, hn, ht
  | .quote c₁, .var _, σ, σ', h, hn, ht | .quote c₁, .pvar _, σ, σ', h, hn, ht
  | .quote c₁, .lam _ _ _, σ, σ', h, hn, ht | .quote c₁, .app _ _, σ, σ', h, hn, ht
  | .quote c₁, .pquote _, σ, σ', h, hn, ht | .quote c₁, .letP _ _ _, σ, σ', h, hn, ht
  | .quote c₁, .alt _ _, σ, σ', h, hn, ht | .quote c₁, .ctx _ _, σ, σ', h, hn, ht
  | .var k, .sym _, σ, σ', h, hn, ht | .var k, .fn _, σ, σ', h, hn, ht
  | .var k, .pvar _, σ, σ', h, hn, ht | .var k, .lam _ _ _, σ, σ', h, hn, ht
  | .var k, .app _ _, σ, σ', h, hn, ht | .var k, .quote _, σ, σ', h, hn, ht
  | .var k, .pquote _, σ, σ', h, hn, ht | .var k, .letP _ _ _, σ, σ', h, hn, ht
  | .var k, .alt _ _, σ, σ', h, hn, ht | .var k, .ctx _ _, σ, σ', h, hn, ht
  | .sym _, _, σ, σ', h, hn, ht | .fn _, _, σ, σ', h, hn, ht | .pvar _, _, σ, σ', h, hn, ht
  | .lam _ _ _, _, σ, σ', h, hn, ht | .letP _ _ _, _, σ, σ', h, hn, ht
  | .alt _ _, _, σ, σ', h, hn, ht | .ctx _ _, _, σ, σ', h, hn, ht => by
      simp only [matchT2] at h
      exact exchange_frame σ σ' _ _ h hn (fun hm => ht (matchHoles_sub_vars hm))

/-- **The pattern-only frame fails for both sides.**  For every store, every
ground pattern and every unbound name: matching the pattern against that name
binds the name, which the matcher does not reach in the pattern. -/
theorem matchT2_writes_value_name (σ : GStore S X) (g : GVal S X) (m : Nm X)
    (hm : σ m = Option.none) :
    ∃ σ', matchT2 σ g.toTm (.var m) = some σ' ∧ σ' m ≠ σ m ∧ m ∉ matchHoles g.toTm := by
  refine ⟨fun k => if k = m then some g else σ k, ?_, ?_, ?_⟩
  · rw [matchT2_ground_var σ g m hm]
    simp only [refineStep, hm]
  · simp [hm]
  · simp [matchHoles_toTm]

/-! ## Substitution instances of a pattern -/

omit [DecidableEq S] [CodeId X] in
theorem hideOwn_nil (θ : Sub S X) : θ.hideOwn [] = θ := by
  funext n
  cases n <;> simp [Sub.hideOwn, ownKey]

/-- The code of every pattern quotation on the spine has lambdas that own
nothing. -/
def spineOwnNil : Tm S X → Prop
  | .app f a => spineOwnNil f ∧ spineOwnNil a
  | .pquote c => IdSlot.ownNil c
  | _ => True

omit [DecidableEq S] [CodeId X] in
/-- **The store names the matcher reaches in an instance of pattern code**: each
is written in the instance of a store name it reaches in the code, or in the
value passed for a parameter of the code. -/
theorem codeHoles_subst {n : Nm X} : ∀ (c : Tm S X) (θ φ : Sub S X), IdSlot.ownNil c →
    n ∈ codeHoles (subst θ φ c) →
      (∃ m ∈ codeHoles c, n ∈ Tm.vars (subst θ φ (.var m))) ∨
        ∃ x ∈ codeParams c, ∃ u, φ x = some u ∧ n ∈ Tm.vars u
  | .var m, θ, φ, _, h => Or.inl ⟨m, by simp [codeHoles], codeHoles_sub_vars h⟩
  | .pvar x, θ, φ, _, h => by
      simp only [subst] at h
      cases hφ : φ x with
      | none => rw [hφ] at h; simp [codeHoles] at h
      | some u =>
          rw [hφ] at h
          exact Or.inr ⟨x, by simp [codeParams], u, hφ, codeHoles_sub_vars h⟩
  | .lam x own b, θ, φ, ho, h => by
      obtain ⟨rfl, hb⟩ := ho
      simp only [subst, hideOwn_nil, codeHoles] at h
      rcases codeHoles_subst b θ (φ.hideParam x) hb h with ⟨m, hm, hn⟩ | ⟨y, hy, u, hu, hn⟩
      · exact Or.inl ⟨m, by simpa [codeHoles] using hm, hn⟩
      · refine Or.inr ⟨y, by simpa [codeParams] using hy, u, ?_, hn⟩
        unfold Sub.hideParam at hu
        split at hu
        · cases hu
        · exact hu
  | .app f a, θ, φ, ho, h => by
      simp only [subst, codeHoles, List.mem_append] at h
      rcases h with h | h
      · rcases codeHoles_subst f θ φ ho.1 h with ⟨m, hm, hn⟩ | ⟨y, hy, u, hu, hn⟩
        · exact Or.inl ⟨m, by simp [codeHoles, hm], hn⟩
        · exact Or.inr ⟨y, by simp [codeParams, hy], u, hu, hn⟩
      · rcases codeHoles_subst a θ φ ho.2 h with ⟨m, hm, hn⟩ | ⟨y, hy, u, hu, hn⟩
        · exact Or.inl ⟨m, by simp [codeHoles, hm], hn⟩
        · exact Or.inr ⟨y, by simp [codeParams, hy], u, hu, hn⟩
  | .letP p w b, θ, φ, ho, h => by
      simp only [subst, codeHoles, List.mem_append] at h
      rcases h with (h | h) | h
      · rcases codeHoles_subst p θ φ ho.1 h with ⟨m, hm, hn⟩ | ⟨y, hy, u, hu, hn⟩
        · exact Or.inl ⟨m, by simp [codeHoles, hm], hn⟩
        · exact Or.inr ⟨y, by simp [codeParams, hy], u, hu, hn⟩
      · rcases codeHoles_subst w θ φ ho.2.1 h with ⟨m, hm, hn⟩ | ⟨y, hy, u, hu, hn⟩
        · exact Or.inl ⟨m, by simp [codeHoles, hm], hn⟩
        · exact Or.inr ⟨y, by simp [codeParams, hy], u, hu, hn⟩
      · rcases codeHoles_subst b θ φ ho.2.2 h with ⟨m, hm, hn⟩ | ⟨y, hy, u, hu, hn⟩
        · exact Or.inl ⟨m, by simp [codeHoles, hm], hn⟩
        · exact Or.inr ⟨y, by simp [codeParams, hy], u, hu, hn⟩
  | .alt a b, θ, φ, ho, h => by
      simp only [subst, codeHoles, List.mem_append] at h
      rcases h with h | h
      · rcases codeHoles_subst a θ φ ho.1 h with ⟨m, hm, hn⟩ | ⟨y, hy, u, hu, hn⟩
        · exact Or.inl ⟨m, by simp [codeHoles, hm], hn⟩
        · exact Or.inr ⟨y, by simp [codeParams, hy], u, hu, hn⟩
      · rcases codeHoles_subst b θ φ ho.2 h with ⟨m, hm, hn⟩ | ⟨y, hy, u, hu, hn⟩
        · exact Or.inl ⟨m, by simp [codeHoles, hm], hn⟩
        · exact Or.inr ⟨y, by simp [codeParams, hy], u, hu, hn⟩
  | .pquote c, θ, φ, ho, h => by
      simp only [subst, codeHoles] at h
      rcases codeHoles_subst c θ φ ho h with ⟨m, hm, hn⟩ | ⟨y, hy, u, hu, hn⟩
      · exact Or.inl ⟨m, by simpa [codeHoles] using hm, hn⟩
      · exact Or.inr ⟨y, by simpa [codeParams] using hy, u, hu, hn⟩
  | .sym _, _, _, _, h | .fn _, _, _, _, h | .quote _, _, _, _, h | .ctx _ _, _, _, _, h => by
      simp [subst, codeHoles] at h

omit [DecidableEq S] [CodeId X] in
/-- **The store names the matcher reaches in an instance of a pattern**: each
is written in the instance of a store name it reaches in the pattern, or in the
value passed for a parameter the pattern writes. -/
theorem matchHoles_subst {n : Nm X} : ∀ (P : Tm S X) (θ φ : Sub S X), spineOwnNil P →
    n ∈ matchHoles (subst θ φ P) →
      (∃ m ∈ matchHoles P, n ∈ Tm.vars (subst θ φ (.var m))) ∨
        ∃ x ∈ matchParams P, ∃ u, φ x = some u ∧ n ∈ Tm.vars u
  | .var m, θ, φ, _, h => Or.inl ⟨m, by simp [matchHoles], matchHoles_sub_vars h⟩
  | .pvar x, θ, φ, _, h => by
      simp only [subst] at h
      cases hφ : φ x with
      | none => rw [hφ] at h; simp [matchHoles] at h
      | some u =>
          rw [hφ] at h
          exact Or.inr ⟨x, by simp [matchParams], u, hφ, matchHoles_sub_vars h⟩
  | .app f a, θ, φ, ho, h => by
      simp only [subst, matchHoles, List.mem_append] at h
      rcases h with h | h
      · rcases matchHoles_subst f θ φ ho.1 h with ⟨m, hm, hn⟩ | ⟨y, hy, u, hu, hn⟩
        · exact Or.inl ⟨m, by simp [matchHoles, hm], hn⟩
        · exact Or.inr ⟨y, by simp [matchParams, hy], u, hu, hn⟩
      · rcases matchHoles_subst a θ φ ho.2 h with ⟨m, hm, hn⟩ | ⟨y, hy, u, hu, hn⟩
        · exact Or.inl ⟨m, by simp [matchHoles, hm], hn⟩
        · exact Or.inr ⟨y, by simp [matchParams, hy], u, hu, hn⟩
  | .pquote c, θ, φ, ho, h => by
      simp only [subst, matchHoles] at h
      rcases codeHoles_subst c θ φ ho h with ⟨m, hm, hn⟩ | ⟨y, hy, u, hu, hn⟩
      · exact Or.inl ⟨m, by simpa [matchHoles] using hm, hn⟩
      · exact Or.inr ⟨y, by simpa [matchParams] using hy, u, hu, hn⟩
  | .sym _, _, _, _, h | .fn _, _, _, _, h | .quote _, _, _, _, h | .ctx _ _, _, _, _, h
  | .lam _ _ _, _, _, _, h | .letP _ _ _, _, _, _, h | .alt _ _, _, _, _, h => by
      simp [subst, matchHoles] at h

/-! ## Lexical fresh: which names the pattern of a `let` writes -/

section LexicalFresh

variable {S : Type u} {X : Type v}

theorem codeHoles_foldr_lam {Y : Type v} (ps : List (Nm Y)) (t : Tm S Y) :
    codeHoles (ps.foldr (fun p acc => .lam p [] acc) t) = codeHoles t := by
  induction ps with
  | nil => rfl
  | cons _ _ ih => simpa [codeHoles] using ih

/-- Sealing the free parameters of code adds no store name. -/
theorem codeHoles_sealParams {Y : Type v} [DecidableEq Y] (t : Tm S Y) :
    codeHoles (sealParams t) = codeHoles t :=
  codeHoles_foldr_lam _ t

variable [DecidableEq X]

/- The root of the form being elaborated: the holes of its sealed quotations
are the root's head slots. -/
variable (R : Owner)

/-- The store names of a pattern quotation's code are the slots the scope gives
the store spellings its code writes. -/
theorem codeHoles_codeAt (env : REnv X) {n : Nm (Slot X)} :
    ∀ (c : Src S X) (penv senv : List (X × Owner)) (pos : Owner),
      n ∈ codeHoles (codeAt R (some env) penv senv pos c) →
        ∃ y ∈ Src.codeSvs c, n = .src (env y, y)
  | .sym _, _, _, _, h => by simp [codeAt, codeHoles] at h
  | .fn _, _, _, _, h => by simp [codeAt, codeHoles] at h
  | .par z, penv, _, _, h => by
      simp only [codeAt] at h
      split at h <;> simp [codeHoles] at h
  | .sv y, _, senv, _, h => by
      simp only [codeAt] at h
      cases hl : codeLookup senv y with
      | some o => rw [hl] at h; simp [codeHoles] at h
      | none =>
          rw [hl] at h
          simp only [codeHoles, List.mem_singleton] at h
          exact ⟨y, by simp [Src.codeSvs], h⟩
  | .lam z _ b, penv, senv, pos, h => by
      simp only [codeAt, codeHoles] at h
      obtain ⟨y, hy, e⟩ := codeHoles_codeAt env b _ _ _ h
      exact ⟨y, by simpa [Src.codeSvs] using hy, e⟩
  | .form z b, penv, senv, pos, h => by
      simp only [codeAt, codeHoles] at h
      obtain ⟨y, hy, e⟩ := codeHoles_codeAt env b _ _ _ h
      exact ⟨y, by simpa [Src.codeSvs] using hy, e⟩
  | .app f a, penv, senv, pos, h => by
      simp only [codeAt, codeHoles, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨y, hy, e⟩ := codeHoles_codeAt env f _ _ _ h
        exact ⟨y, by simp [Src.codeSvs, hy], e⟩
      · obtain ⟨y, hy, e⟩ := codeHoles_codeAt env a _ _ _ h
        exact ⟨y, by simp [Src.codeSvs, hy], e⟩
  | .quote _, _, _, _, h => by simp [codeAt, codeHoles] at h
  | .pquote c, _, _, _, h => by
      simp only [codeAt, codeHoles] at h
      obtain ⟨y, hy, e⟩ := codeHoles_codeAt env c _ _ _ h
      exact ⟨y, by simpa [Src.codeSvs] using hy, e⟩
  | .letS p w b _, penv, senv, pos, h => by
      simp only [codeAt, codeHoles, List.mem_append] at h
      rcases h with (h | h) | h
      · obtain ⟨y, hy, e⟩ := codeHoles_codeAt env p _ _ _ h
        exact ⟨y, by simp [Src.codeSvs, hy], e⟩
      · obtain ⟨y, hy, e⟩ := codeHoles_codeAt env w _ _ _ h
        exact ⟨y, by simp [Src.codeSvs, hy], e⟩
      · obtain ⟨y, hy, e⟩ := codeHoles_codeAt env b _ _ _ h
        exact ⟨y, by simp [Src.codeSvs, hy], e⟩
  | .unify p w b, penv, senv, pos, h => by
      simp only [codeAt, codeHoles, List.mem_append] at h
      rcases h with (h | h) | h
      · obtain ⟨y, hy, e⟩ := codeHoles_codeAt env p _ _ _ h
        exact ⟨y, by simp [Src.codeSvs, hy], e⟩
      · obtain ⟨y, hy, e⟩ := codeHoles_codeAt env w _ _ _ h
        exact ⟨y, by simp [Src.codeSvs, hy], e⟩
      · obtain ⟨y, hy, e⟩ := codeHoles_codeAt env b _ _ _ h
        exact ⟨y, by simp [Src.codeSvs, hy], e⟩
  | .alt t₁ t₂, penv, senv, pos, h => by
      simp only [codeAt, codeHoles, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨y, hy, e⟩ := codeHoles_codeAt env t₁ _ _ _ h
        exact ⟨y, by simp [Src.codeSvs, hy], e⟩
      · obtain ⟨y, hy, e⟩ := codeHoles_codeAt env t₂ _ _ _ h
        exact ⟨y, by simp [Src.codeSvs, hy], e⟩
  | .new _ b, penv, senv, pos, h => by
      simp only [codeAt] at h
      obtain ⟨y, hy, e⟩ := codeHoles_codeAt env b _ _ _ h
      exact ⟨y, by simpa [Src.codeSvs] using hy, e⟩

/-- **The store names the matcher reaches in a pattern, under lexical fresh**:
the slots the scope gives the spellings the pattern writes at its own level. -/
theorem matchHoles_elabLF {n : Nm (Slot X)} :
    ∀ (p : Src S X) (env : REnv X) (cr : List X) (pos : Owner),
      n ∈ matchHoles (elabLF R env cr pos p) → ∃ y ∈ Src.direct p, n = .src (env y, y)
  | .sym _, _, _, _, h => by simp [elabLF, matchHoles] at h
  | .fn _, _, _, _, h => by simp [elabLF, matchHoles] at h
  | .sv y, env, _, _, h => by
      simp only [elabLF, slotVar, matchHoles, List.mem_singleton] at h
      exact ⟨y, by simp [Src.direct], h⟩
  | .par _, _, _, _, h => by simp [elabLF, matchHoles] at h
  | .lam _ _ _, _, _, _, h => by simp [elabLF, matchHoles] at h
  | .app f a, env, cr, pos, h => by
      simp only [elabLF, matchHoles, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨y, hy, e⟩ := matchHoles_elabLF f env cr _ h
        exact ⟨y, by simp [Src.direct, hy], e⟩
      · obtain ⟨y, hy, e⟩ := matchHoles_elabLF a env cr _ h
        exact ⟨y, by simp [Src.direct, hy], e⟩
  | .quote _, _, _, _, h => by simp [elabLF, matchHoles] at h
  | .pquote c, env, _, _, h => by
      simp only [elabLF, matchHoles, codeHoles_sealParams] at h
      obtain ⟨y, hy, e⟩ := codeHoles_codeAt R env c _ _ _ h
      exact ⟨y, by simpa [Src.direct] using hy, e⟩
  | .letS p w b xs, env, cr, pos, h => by
      simp only [elabLF] at h
      split at h
      · simp [matchHoles] at h
      · simp only [matchHoles, List.nil_append] at h
        obtain ⟨y, hy, e⟩ := matchHoles_elabLF w env cr _ h
        exact ⟨y, by simp [Src.direct, hy], e⟩
  | .unify _ _ _, _, _, _, h => by simp [elabLF, matchHoles] at h
  | .alt _ _, _, _, _, h => by simp [elabLF, matchHoles] at h
  | .new [] b, env, cr, pos, h => by
      simp only [elabLF] at h
      obtain ⟨y, hy, e⟩ := matchHoles_elabLF b env cr _ h
      exact ⟨y, by simpa [Src.direct] using hy, e⟩
  | .new (_ :: _) _, _, _, _, h => by simp [elabLF, newBlock, matchHoles] at h
  | .form _ _, _, _, _, h => by simp [elabLF, formedLam, matchHoles] at h

/-- Under lexical fresh the code of a pattern quotation owns nothing. -/
theorem spineOwnNil_elabLF :
    ∀ (p : Src S X) (env : REnv X) (cr : List X) (pos : Owner),
      spineOwnNil (elabLF R env cr pos p)
  | .sym _, _, _, _ => by simp [elabLF, spineOwnNil]
  | .fn _, _, _, _ => by simp [elabLF, spineOwnNil]
  | .sv _, _, _, _ => by simp [elabLF, slotVar, spineOwnNil]
  | .par _, _, _, _ => by simp [elabLF, spineOwnNil]
  | .lam _ _ _, _, _, _ => by simp [elabLF, spineOwnNil]
  | .app f a, env, cr, pos => by
      simp only [elabLF, spineOwnNil]
      exact ⟨spineOwnNil_elabLF f env cr _, spineOwnNil_elabLF a env cr _⟩
  | .quote _, _, _, _ => by simp [elabLF, spineOwnNil]
  | .pquote c, env, _, _ => by
      simp only [elabLF, spineOwnNil]
      exact IdSlot.ownNil_seal (IdSlot.ownNil_codeAt R (some env) [] [] [] c)
  | .letS p w b xs, env, cr, pos => by
      simp only [elabLF]
      split
      · simp [spineOwnNil]
      · simp only [spineOwnNil, true_and]
        exact spineOwnNil_elabLF w env cr _
  | .unify _ _ _, _, _, _ => by simp [elabLF, spineOwnNil]
  | .alt _ _, _, _, _ => by simp [elabLF, spineOwnNil]
  | .new [] b, env, cr, pos => by
      simp only [elabLF]
      exact spineOwnNil_elabLF b env cr _
  | .new (_ :: _) _, _, _, _ => by simp [elabLF, newBlock, spineOwnNil]
  | .form _ _, _, _, _ => by simp [elabLF, formedLam, spineOwnNil]

/-- **The pattern of a `let`, as lexical fresh elaborates it**: the names the
`let` introduces (`lfIntro`) point at the `let`'s own owner, the position of its
body; every other name keeps the slot it has in the scope. -/
def lfPattern (env : REnv X) (cr : List X) (pos : Owner) (p : Src S X) (xs : Option (List X)) :
    Tm S (Slot X) :=
  elabLF R (env.update (lfIntro xs p cr) (pos ++ [2])) (crossIn xs (lfIntro xs p cr) cr)
    (pos ++ [0]) p

/-- A `let` that introduces names is the activation of a lambda that owns them,
over a `let` with the pattern `lfPattern`. -/
theorem elabLF_letS_intro (env : REnv X) (cr : List X) (pos : Owner) (p w b : Src S X)
    (xs : Option (List X)) {y₀ : X} {ys : List X} (h : lfIntro xs p cr = y₀ :: ys) :
    elabLF R env cr pos (.letS p w b xs) =
      .app (.lam (letParam (pos ++ [2]) y₀) ((y₀ :: ys).map fun y => (pos ++ [2], y))
          (.letP (lfPattern R env cr pos p xs) (.pvar (letParam (pos ++ [2]) y₀))
            (elabLF R (env.update (y₀ :: ys) (pos ++ [2])) (crossIn xs (y₀ :: ys) cr) (pos ++ [2])
              b)))
        (elabLF R env cr (pos ++ [1]) w) := by
  simp only [elabLF, lfPattern, h]

/-- A `let` that introduces nothing is a `let` with the pattern `lfPattern`. -/
theorem elabLF_letS_plain (env : REnv X) (cr : List X) (pos : Owner) (p w b : Src S X)
    (xs : Option (List X)) (h : lfIntro xs p cr = []) :
    elabLF R env cr pos (.letS p w b xs) =
      .letP (lfPattern R env cr pos p xs) (elabLF R env cr (pos ++ [1]) w)
        (elabLF R env (crossIn xs [] cr) (pos ++ [2]) b) := by
  have hu : env.update [] (pos ++ [2]) = env := by
    funext y
    simp [REnv.update]
  simp only [elabLF, lfPattern, h, hu]

variable [DecidableEq S]

/-- **The frame of a `let` under lexical fresh, pattern-only, over all
programs.**  Take any `let`, at any position and scope, any instance of its
elaborated pattern under substitutions `θ` (store names: the copies activations
make, and names a `let` substituted) and `φ` (parameters), any store and any
value.  A name at which the store after the match differs from the store before
is written in

* the instance of a slot the pattern introduced: `(pos ++ [2], y)`, `y` in
  `lfIntro`; or
* the instance of a slot the pattern writes and does not introduce: a name in
  force (a crossing name), or a hole of a quotation pattern whose spelling the
  pattern does not also write on its spine; or
* the value passed for a parameter the pattern writes. -/
theorem let_frame_LF (env : REnv X) (cr : List X) (pos : Owner) (p : Src S X)
    (xs : Option (List X)) (θ φ : Sub S (Slot X)) (σ σ' : GStore S (Slot X)) (t : Tm S (Slot X))
    (h : matchT σ (subst θ φ (lfPattern R env cr pos p xs)) t = some σ') (n : Nm (Slot X))
    (hn : σ' n ≠ σ n) :
    (∃ y ∈ lfIntro xs p cr, n ∈ Tm.vars (subst θ φ (.var (.src (pos ++ [2], y))))) ∨
      (∃ y ∈ Src.direct p, y ∉ lfIntro xs p cr ∧
        n ∈ Tm.vars (subst θ φ (.var (.src (env y, y))))) ∨
      ∃ x ∈ matchParams (lfPattern R env cr pos p xs), ∃ u, φ x = some u ∧ n ∈ Tm.vars u := by
  by_cases hmem : n ∈ matchHoles (subst θ φ (lfPattern R env cr pos p xs))
  · rcases matchHoles_subst _ θ φ (spineOwnNil_elabLF R p _ _ _) hmem with
      ⟨m, hm, hv⟩ | ⟨x, hx, u, hu, hv⟩
    · obtain ⟨y, hy, rfl⟩ := matchHoles_elabLF R p _ _ _ hm
      by_cases hI : y ∈ lfIntro xs p cr
      · left
        refine ⟨y, hI, ?_⟩
        simpa [REnv.update, hI] using hv
      · right
        left
        refine ⟨y, hy, hI, ?_⟩
        simpa [REnv.update, hI] using hv
    · exact Or.inr (Or.inr ⟨x, hx, u, hu, hv⟩)
  · exact absurd (matchT_frame _ t σ σ' h hmem) hn

/-- **The frame of a `let` under lexical fresh, pattern-only: only the names
the pattern introduced.**  When every name the pattern writes is introduced by
the `let`, and no parameter the pattern writes is instantiated, the store after
the match differs from the store before only at the activation's copies of the
names the pattern introduced.  `ρ` is the path of the `let`'s activation, which
renames the names the `let` owns. -/
theorem let_frame_LF_introduced (env : REnv X) (cr : List X) (pos : Owner) (p : Src S X)
    (xs : Option (List X)) (ρ : Path) (φ : Sub S (Slot X)) (σ σ' : GStore S (Slot X))
    (t : Tm S (Slot X)) (hall : ∀ y ∈ Src.direct p, y ∈ lfIntro xs p cr)
    (hφ : ∀ x ∈ matchParams (lfPattern R env cr pos p xs), φ x = Option.none)
    (h : matchT σ (subst (renameOwn ρ ((lfIntro xs p cr).map fun y => (pos ++ [2], y))) φ
      (lfPattern R env cr pos p xs)) t = some σ') (n : Nm (Slot X)) (hn : σ' n ≠ σ n) :
    ∃ y ∈ lfIntro xs p cr, n = .inst ρ (.src (pos ++ [2], y)) := by
  rcases let_frame_LF R env cr pos p xs _ φ σ σ' t h n hn with
    ⟨y, hy, hv⟩ | ⟨y, hy, hI, -⟩ | ⟨x, hx, u, hu, -⟩
  · refine ⟨y, hy, ?_⟩
    have hk : ownKey ((lfIntro xs p cr).map fun y => (pos ++ [2], y))
        (.src (pos ++ [2], y) : Nm (Slot X)) = true := by
      rw [IdSlot.ownKey_map_src]
      exact decide_eq_true ⟨rfl, hy⟩
    simpa [subst, renameOwn, hk, Tm.vars] using hv
  · exact absurd (hall y hy) hI
  · rw [hφ x hx] at hu
    cases hu

end LexicalFresh

end Mettapedia.GSLT.LanguageDef.TemplateScope
