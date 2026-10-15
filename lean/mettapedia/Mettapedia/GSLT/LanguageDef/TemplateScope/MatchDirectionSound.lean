import Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionUnify
import Mettapedia.Logic.LP.TotalUnification

/-!
# Template scope: a both-sides match is a ground unifier

The first-order part of the both-sides matcher, stated against the
Martelli–Montanari unifier of `Mettapedia.Logic.LP`.

First-order terms (symbols, store names, data application) are terms of the
signature `dataSig`: symbols are constants, store names are variables, and data
application is one binary function symbol.  A store is a substitution
(`storeSubst`): a bound name goes to its value, an unbound name to itself.

## Main results

* `matchT2_sound_fo` — on first-order terms and a store of data, a successful
  both-sides match returns a store that refines the first and makes pattern and
  value equal.
* `matchT2_unifies` — hence the returned store is a unifier in the sense of
  `LP.Unifies`.
* `matchT2_instance_of_mgu` — and an instance of the most general unifier that
  `LP.unifyTotal` computes.
* `unifyTotal_two_names` — the converse fails: unification succeeds on two
  different names, where the both-sides matcher answers `none`
  (`matchT2_var_var_unbound`).  The both-sides matcher is unification restricted
  to ground bindings.

The code part is not stated against `Mettapedia.OSLF.Syntax.ScopedMatching`:
that matcher is one-sided by design (rule variables and contextual
metavariables occur in the schema only, the target is closed), and it works on
intrinsically scoped terms of a binding signature, with no store.  The
both-sides code rule (`holeFill`) is the mirror image of its `setMeta` step, in
another term language.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.Logic.LP

universe u v

variable {S : Type u} {X : Type v}

/-! ## Data stores and first-order terms -/

/-- A store whose values are data. -/
def DataStore (σ : GStore S X) : Prop := ∀ n g, σ n = some g → g.isData = true

theorem DataStore.empty : DataStore (Store.empty : GStore S X) := fun _ _ h => by cases h

/-- A store that holds code is not a store of data. -/
theorem not_dataStore_of_quote {σ : GStore S X} {n : Nm X} {c : Tm S X}
    (h : σ n = some (.quote c)) : ¬ DataStore σ := fun hσ => by
  have := hσ n _ h
  simp [GVal.isData] at this

theorem GVal.isData_firstOrder : ∀ g : GVal S X, g.isData = true → g.toTm.FirstOrder = true
  | .sym _, _ => rfl
  | .app f a, h => by
      simp only [GVal.isData, Bool.and_eq_true] at h
      simp only [GVal.toTm, Tm.FirstOrder, Bool.and_eq_true]
      exact ⟨GVal.isData_firstOrder f h.1, GVal.isData_firstOrder a h.2⟩
  | .quote _, h => by simp [GVal.isData] at h
  | .ctx _ _, h => by simp [GVal.isData] at h

/-- A first-order term that is ground is data. -/
theorem firstOrder_toGVal_isData : ∀ {t : Tm S X} {g : GVal S X}, t.FirstOrder = true →
    t.toGVal? = some g → g.isData = true
  | .sym _, g, _, h => by
      simp only [Tm.toGVal?, Option.some.injEq] at h
      subst h
      rfl
  | .var _, _, _, h => by simp [Tm.toGVal?] at h
  | .app f a, g, hfo, h => by
      simp only [Tm.FirstOrder, Bool.and_eq_true] at hfo
      simp only [Tm.toGVal?] at h
      cases hf : f.toGVal? with
      | none => simp [hf] at h
      | some f' =>
          cases ha : a.toGVal? with
          | none => simp [hf, ha] at h
          | some a' =>
              simp only [hf, ha, Option.some.injEq] at h
              subst h
              simp only [GVal.isData, Bool.and_eq_true]
              exact ⟨firstOrder_toGVal_isData hfo.1 hf, firstOrder_toGVal_isData hfo.2 ha⟩
  | .fn _, _, h, _ | .pvar _, _, h, _ | .lam _ _ _, _, h, _ | .quote _, _, h, _
  | .pquote _, _, h, _ | .ctx _ _, _, h, _ | .letP _ _ _, _, h, _ | .alt _ _, _, h, _ => by
      simp [Tm.FirstOrder] at h

section

variable [DecidableEq X]

/-- A first-order term read under a store of data is first-order. -/
theorem firstOrder_act {σ : GStore S X} (hσ : DataStore σ) : ∀ t : Tm S X,
    t.FirstOrder = true → (act σ t).FirstOrder = true
  | .sym _, _ => rfl
  | .var n, _ => by
      rw [act_var]
      cases h : σ n with
      | none => rfl
      | some g => exact GVal.isData_firstOrder g (hσ n g h)
  | .app f a, h => by
      simp only [Tm.FirstOrder, Bool.and_eq_true] at h
      simp only [act_app, Tm.FirstOrder, Bool.and_eq_true]
      exact ⟨firstOrder_act hσ f h.1, firstOrder_act hσ a h.2⟩
  | .fn _, h | .pvar _, h | .lam _ _ _, h | .quote _, h | .pquote _, h | .ctx _ _, h
  | .letP _ _ _, h | .alt _ _, h => by simp [Tm.FirstOrder] at h

variable [DecidableEq S]

theorem refineStep_dataStore {σ σ' : GStore S X} (hσ : DataStore σ) {n : Nm X} {g : GVal S X}
    (hg : g.isData = true) (h : refineStep σ (n, g) = some σ') : DataStore σ' := by
  unfold refineStep at h
  cases hs : σ n with
  | none =>
      simp only [hs, Option.some.injEq] at h
      subst h
      intro m w hw
      by_cases hm : m = n
      · simp only [hm, if_true, Option.some.injEq] at hw
        rw [← hw]
        exact hg
      · simp only [hm, if_false] at hw
        exact hσ m w hw
  | some w =>
      simp only [hs] at h
      split at h
      · injection h with h
        rw [← h]
        exact hσ
      · cases h

variable [CodeId X]

/-- **A pattern-only match of a first-order pattern is sound**: under the
returned store the pattern reads as the value. -/
theorem matchT_sound_fo : ∀ (p : Tm S X), p.FirstOrder = true → ∀ (g : GVal S X)
    (σ σ' : GStore S X), matchT σ p g.toTm = some σ' → act σ' p = g.toTm
  | .sym s, _, g, σ, σ', h => by
      cases g <;> simp [GVal.toTm, matchT] at h
      rw [h.1]
      rfl
  | .var n, _, g, σ, σ', h => by
      simp only [matchT, GVal.toTm_toGVal?] at h
      rw [act_var, refineStep_binds h]
  | .app p₁ p₂, hp, g, σ, σ', h => by
      simp only [Tm.FirstOrder, Bool.and_eq_true] at hp
      cases g with
      | app f a =>
          simp only [GVal.toTm, matchT] at h
          cases h₁ : matchT σ p₁ f.toTm with
          | none => simp [h₁] at h
          | some σ₁ =>
              simp only [h₁] at h
              have e₁ := matchT_sound_fo p₁ hp.1 f σ σ₁ h₁
              have e₂ := matchT_sound_fo p₂ hp.2 a σ₁ σ' h
              have hle := matchT_mono _ _ _ _ h
              simp only [act_app, GVal.toTm, e₂]
              rw [← act_absorb hle p₁, e₁, act_toTm]
      | sym _ => simp [GVal.toTm, matchT] at h
      | quote _ => simp [GVal.toTm, matchT] at h
      | ctx _ _ => simp [GVal.toTm, matchT] at h
  | .fn _, h, _, _, _, _ | .pvar _, h, _, _, _, _ | .lam _ _ _, h, _, _, _, _
  | .quote _, h, _, _, _, _ | .pquote _, h, _, _, _, _ | .ctx _ _, h, _, _, _, _
  | .letP _ _ _, h, _, _, _, _ | .alt _ _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h

/-- A pattern-only match of a first-order pattern against data keeps a store of
data. -/
theorem matchT_dataStore_fo : ∀ (p : Tm S X), p.FirstOrder = true → ∀ (g : GVal S X),
    g.isData = true → ∀ (σ σ' : GStore S X), DataStore σ → matchT σ p g.toTm = some σ' →
      DataStore σ'
  | .sym s, _, g, _, σ, σ', hσ, h => by
      cases g <;> simp [GVal.toTm, matchT] at h
      rw [← h.2]
      exact hσ
  | .var n, _, g, hg, σ, σ', hσ, h => by
      simp only [matchT, GVal.toTm_toGVal?] at h
      exact refineStep_dataStore hσ hg h
  | .app p₁ p₂, hp, g, hg, σ, σ', hσ, h => by
      simp only [Tm.FirstOrder, Bool.and_eq_true] at hp
      cases g with
      | app f a =>
          simp only [GVal.isData, Bool.and_eq_true] at hg
          simp only [GVal.toTm, matchT] at h
          cases h₁ : matchT σ p₁ f.toTm with
          | none => simp [h₁] at h
          | some σ₁ =>
              simp only [h₁] at h
              exact matchT_dataStore_fo p₂ hp.2 a hg.2 σ₁ σ'
                (matchT_dataStore_fo p₁ hp.1 f hg.1 σ σ₁ hσ h₁) h
      | sym _ => simp [GVal.toTm, matchT] at h
      | quote _ => simp [GVal.toTm, matchT] at h
      | ctx _ _ => simp [GVal.toTm, matchT] at h
  | .fn _, h, _, _, _, _, _, _ | .pvar _, h, _, _, _, _, _, _ | .lam _ _ _, h, _, _, _, _, _, _
  | .quote _, h, _, _, _, _, _, _ | .pquote _, h, _, _, _, _, _, _
  | .ctx _ _, h, _, _, _, _, _, _ | .letP _ _ _, h, _, _, _, _, _, _
  | .alt _ _, h, _, _, _, _, _, _ => by simp [Tm.FirstOrder] at h

/-- `exchange` on first-order parts: the returned store refines the first, is a
store of data, and makes the two parts equal. -/
theorem exchange_sound_fo {p t : Tm S X} (hp : p.FirstOrder = true) (ht : t.FirstOrder = true)
    {σ σ' : GStore S X} (hσ : DataStore σ) (h : exchange σ p t = some σ') :
    σ ⊑ σ' ∧ DataStore σ' ∧ act σ' p = act σ' t := by
  unfold exchange at h
  cases hg : (act σ t).toGVal? with
  | some g =>
      rw [hg] at h
      dsimp only at h
      have hle := matchT_mono _ _ _ _ h
      have hd : g.isData = true := firstOrder_toGVal_isData (firstOrder_act hσ t ht) hg
      refine ⟨hle, matchT_dataStore_fo p hp g hd σ σ' hσ h, ?_⟩
      rw [matchT_sound_fo p hp g σ σ' h, ← act_absorb hle t, ← CloTable.toGVal?_toTm hg, act_toTm]
  | none =>
      rw [hg] at h
      dsimp only at h
      cases hg' : (act σ p).toGVal? with
      | none => rw [hg'] at h; cases h
      | some gp =>
          rw [hg'] at h
          dsimp only at h
          have hle := matchT_mono _ _ _ _ h
          have hfo := firstOrder_act hσ t ht
          have hd : gp.isData = true := firstOrder_toGVal_isData (firstOrder_act hσ p hp) hg'
          refine ⟨hle, matchT_dataStore_fo _ hfo gp hd σ σ' hσ h, ?_⟩
          have e := matchT_sound_fo _ hfo gp σ σ' h
          rw [act_absorb hle t] at e
          rw [e, ← act_absorb hle p, ← CloTable.toGVal?_toTm hg', act_toTm]

/-- **A both-sides match of first-order terms is sound.**  From a store of
data, the returned store refines the first, is a store of data, and makes
pattern and value equal: it is a unifier, and every binding it adds is
ground. -/
theorem matchT2_sound_fo : ∀ (p t : Tm S X), p.FirstOrder = true → t.FirstOrder = true →
    ∀ (σ σ' : GStore S X), DataStore σ → matchT2 σ p t = some σ' →
      σ ⊑ σ' ∧ DataStore σ' ∧ act σ' p = act σ' t
  | .app p₁ p₂, .app t₁ t₂, hp, ht, σ, σ', hσ, h => by
      simp only [Tm.FirstOrder, Bool.and_eq_true] at hp ht
      simp only [matchT2] at h
      cases h₁ : matchT2 σ p₁ t₁ with
      | none => simp [h₁] at h
      | some σ₁ =>
          simp only [h₁] at h
          obtain ⟨hle₁, hσ₁, e₁⟩ := matchT2_sound_fo p₁ t₁ hp.1 ht.1 σ σ₁ hσ h₁
          obtain ⟨hle₂, hσ₂, e₂⟩ := matchT2_sound_fo p₂ t₂ hp.2 ht.2 σ₁ σ' hσ₁ h
          refine ⟨hle₁.trans hle₂, hσ₂, ?_⟩
          simp only [act_app, e₂]
          rw [← act_absorb hle₂ p₁, e₁, act_absorb hle₂ t₁]
  | .var n, .var m, hp, ht, σ, σ', hσ, h => by
      simp only [matchT2] at h
      split at h
      · next hnm =>
          injection h with h
          subst h
          subst hnm
          exact ⟨Store.LE.refl σ, hσ, rfl⟩
      · exact exchange_sound_fo hp ht hσ h
  | .sym _, .sym _, hp, ht, σ, σ', hσ, h | .sym _, .var _, hp, ht, σ, σ', hσ, h
  | .sym _, .app _ _, hp, ht, σ, σ', hσ, h | .var _, .sym _, hp, ht, σ, σ', hσ, h
  | .var _, .app _ _, hp, ht, σ, σ', hσ, h | .app _ _, .sym _, hp, ht, σ, σ', hσ, h
  | .app _ _, .var _, hp, ht, σ, σ', hσ, h => by
      simp only [matchT2] at h
      exact exchange_sound_fo hp ht hσ h
  | .sym _, .fn _, _, ht, _, _, _, _ | .sym _, .pvar _, _, ht, _, _, _, _
  | .sym _, .lam _ _ _, _, ht, _, _, _, _ | .sym _, .quote _, _, ht, _, _, _, _
  | .sym _, .pquote _, _, ht, _, _, _, _ | .sym _, .ctx _ _, _, ht, _, _, _, _
  | .sym _, .letP _ _ _, _, ht, _, _, _, _ | .sym _, .alt _ _, _, ht, _, _, _, _
  | .var _, .fn _, _, ht, _, _, _, _ | .var _, .pvar _, _, ht, _, _, _, _
  | .var _, .lam _ _ _, _, ht, _, _, _, _ | .var _, .quote _, _, ht, _, _, _, _
  | .var _, .pquote _, _, ht, _, _, _, _ | .var _, .ctx _ _, _, ht, _, _, _, _
  | .var _, .letP _ _ _, _, ht, _, _, _, _ | .var _, .alt _ _, _, ht, _, _, _, _
  | .app _ _, .fn _, _, ht, _, _, _, _ | .app _ _, .pvar _, _, ht, _, _, _, _
  | .app _ _, .lam _ _ _, _, ht, _, _, _, _ | .app _ _, .quote _, _, ht, _, _, _, _
  | .app _ _, .pquote _, _, ht, _, _, _, _ | .app _ _, .ctx _ _, _, ht, _, _, _, _
  | .app _ _, .letP _ _ _, _, ht, _, _, _, _ | .app _ _, .alt _ _, _, ht, _, _, _, _ => by
      simp [Tm.FirstOrder] at ht
  | .fn _, _, hp, _, _, _, _, _ | .pvar _, _, hp, _, _, _, _, _ | .lam _ _ _, _, hp, _, _, _, _, _
  | .quote _, _, hp, _, _, _, _, _ | .pquote _, _, hp, _, _, _, _, _
  | .ctx _ _, _, hp, _, _, _, _, _ | .letP _ _ _, _, hp, _, _, _, _, _
  | .alt _ _, _, hp, _, _, _, _, _ => by simp [Tm.FirstOrder] at hp

end

/-! ## Against the first-order unifier of `Mettapedia.Logic.LP` -/

section LP

variable {S X : Type u}

/-- **The signature of first-order terms**: symbols are constants (with one
more constant for a term that is not first-order), store names are variables,
and data application is one binary function symbol.  `LP.Term` asks for symbols
and names in one universe. -/
abbrev dataSig (S X : Type u) : LPSignature.{u, u, 0, u} where
  constants := Option S
  vars := Nm X
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := PUnit
  functionArity := fun _ => 2

/-- A term, as a term of `dataSig`.  On first-order terms it loses nothing. -/
def encFO : Tm S X → Term (dataSig S X)
  | .sym s => .const (some s)
  | .var n => .var n
  | .app f a => .app PUnit.unit fun i => if i = 0 then encFO f else encFO a
  | _ => .const none

/-- **A store, as a substitution**: a bound name goes to its value, an unbound
name to itself. -/
def storeSubst (σ : GStore S X) : Subst (dataSig S X) :=
  fun n => match σ n with
    | some g => encFO g.toTm
    | Option.none => .var n

section

variable [DecidableEq X]

/-- Reading a first-order term under a store is applying the store's
substitution. -/
theorem encFO_act (σ : GStore S X) : ∀ t : Tm S X, t.FirstOrder = true →
    encFO (act σ t) = (storeSubst σ).applyTerm (encFO t)
  | .sym _, _ => rfl
  | .var n, _ => by
      rw [act_var]
      simp only [encFO, Subst.applyTerm_var, storeSubst]
      cases σ n <;> rfl
  | .app f a, h => by
      simp only [Tm.FirstOrder, Bool.and_eq_true] at h
      simp only [act_app, encFO, Subst.applyTerm_app, encFO_act σ f h.1, encFO_act σ a h.2]
      congr 1
      funext i
      split <;> rfl
  | .fn _, h | .pvar _, h | .lam _ _ _, h | .quote _, h | .pquote _, h | .ctx _ _, h
  | .letP _ _ _, h | .alt _ _, h => by simp [Tm.FirstOrder] at h

variable [DecidableEq S] [CodeId X]

/-- **A both-sides match returns a unifier**, in the sense of `LP.Unifies`: on
first-order terms, from a store of data, the returned store, read as a
substitution, makes pattern and value equal. -/
theorem matchT2_unifies {p t : Tm S X} (hp : p.FirstOrder = true) (ht : t.FirstOrder = true)
    {σ σ' : GStore S X} (hσ : DataStore σ) (h : matchT2 σ p t = some σ') :
    Unifies (storeSubst σ') [(encFO p, encFO t)] := by
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  rw [← encFO_act σ' p hp, ← encFO_act σ' t ht, (matchT2_sound_fo p t hp ht σ σ' hσ h).2.2]

/-- **And an instance of the most general unifier**: `LP.unifyTotal` succeeds on
the pair, and its unifier is more general than the returned store. -/
theorem matchT2_instance_of_mgu {p t : Tm S X} (hp : p.FirstOrder = true)
    (ht : t.FirstOrder = true) {σ σ' : GStore S X} (hσ : DataStore σ)
    (h : matchT2 σ p t = some σ') :
    ∃ θ, unifyTotal [(encFO p, encFO t)] = some θ ∧ θ.moreGeneral (storeSubst σ') := by
  have hu := matchT2_unifies hp ht hσ h
  obtain ⟨θ, hθ⟩ := unifyTotal_complete ⟨_, hu⟩
  exact ⟨θ, hθ, unifyTotal_mgu _ θ hθ _ hu⟩

omit [CodeId X] in
/-- **The converse fails.**  Two store names are unifiable, and `LP.unifyTotal`
unifies them; the both-sides matcher answers `none` on two different unbound
names (`matchT2_var_var_unbound`).  It is unification restricted to ground
bindings. -/
theorem unifyTotal_two_names (n m : Nm X) :
    ∃ θ, unifyTotal [((encFO (.var n : Tm S X)), encFO (.var m : Tm S X))] = some θ := by
  refine unifyTotal_complete ⟨fun _ => .var m, ?_⟩
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  rfl

end

end LP

end Mettapedia.GSLT.LanguageDef.TemplateScope
