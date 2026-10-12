import Mettapedia.GSLT.LanguageDef.TemplateScope.Defunctionalization

/-!
# Template scope: relating two name disciplines of one evaluator

Two elaborations of one program into the evaluator's terms (`Tm S X₁` and
`Tm S X₂`) can differ in three ways that a plain renaming does not cover:

* **store names**: an injective map `ν` from the first side's names to the
  second side's;
* **parameters**: a binder-respecting map `μ`, so that parameters may be named
  by spelling on one side (shadowing) and by binder position on the other;
* **allocation**: a `let` or a `new` block may be an *activation* on the first
  side, `((lam ℓ own (let p ℓ b)) w)` or `((lam ℓ own b) (lam ℓ [] ℓ))`, which
  renames its own slots when it runs, and a plain `let` (or nothing) on the
  second side, whose slots belong to the enclosing frame and were renamed when
  that frame was activated.  Until the first side's activation runs, the
  second side's slots are **reserved**: free, unbound, and used only inside the
  construct.  `Rel` carries them as a list, split among subterms, so that each
  reserved name belongs to exactly one pending construct.

`Rel C ν μ k Res ok t₁ t₂` is that relation.  The kind `k` says where the pair
sits: a value (`val`: no pending construct outside lambdas), a pattern (`pat`:
no `new` block along the matched spine), or code.  `ok = true` when no pending
activation sits where matching of code can enter.

## Main results

* `Rel.congr` — the relation reads `ν` and `μ` only on free names and
  parameters.
* `Rel.substitute` — **substitution preserves the relation**: renaming slots on
  one side or both, instantiating parameters, substituting values for store
  names, and applying a store are all instances.
* `Rel.mem_freeNames`, `Rel.mem_freeParams` — free names and parameters
  correspond.
* `Rel.toGVal?` — related values read back as related ground values.
* `Rel.matchT` — matching related patterns against related ground values
  succeeds together, with related stores.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

namespace IdSlot

variable {S : Type u} {X₁ X₂ : Type v}

/-- Where a related pair of terms sits. -/
inductive Kd where
  /-- A value: no pending construct outside lambdas. -/
  | val
  /-- A pattern: no `new` block along the matched spine. -/
  | pat
  /-- Code. -/
  | code
  deriving DecidableEq, Repr

/-- The order of kinds: `val ≤ pat ≤ code`. -/
def Kd.le : Kd → Kd → Prop
  | .val, _ => True
  | .pat, .pat => True
  | .pat, .code => True
  | .code, .code => True
  | _, _ => False

/-- The parameters of the relation. -/
structure Setting (S : Type u) (X₁ X₂ : Type v) where
  /-- Related sealed code. -/
  Q : Tm S X₁ → Tm S X₂ → Prop
  /-- Base names of the first side that may occur free outside activations: no
  binder owns them. -/
  root₁ : X₁ → Prop
  /-- The same on the second side. -/
  root₂ : X₂ → Prop
  /-- A store name and its image are holes together, or binders of code together. -/
  varHole : Nm X₁ → Nm X₂ → Prop
  /-- A parameter and its image are parameters of code together, or of the
  surrounding scope together. -/
  parOK : Nm X₁ → Nm X₂ → Prop
  /-- Binders a related lambda may carry. Scope binders are holes, at any own
  lists. Binders of code are not holes, own nothing, and share an owner. -/
  bareLam : Nm X₁ → List X₁ → Nm X₂ → List X₂ → Prop
  /-- Binders `matchCode` may enter against code: not holes. -/
  enterLam : Nm X₁ → Nm X₂ → Prop
  /-- Entered binders own nothing. -/
  enter_nil : ∀ {x₁ own₁ x₂ own₂}, bareLam x₁ own₁ x₂ own₂ → enterLam x₁ x₂ →
    own₁ = [] ∧ own₂ = []
  /-- Second-side names that compare alike after a renaming. -/
  preserve : Nm X₂ → Nm X₂ → Prop
  /-- A name compares as itself. -/
  preserve_refl : ∀ m, preserve m m
  /-- An activation copy compares as the name it copies. -/
  preserve_inst : ∀ (ρ : Path) (m : Nm X₂), preserve m (.inst ρ m)
  /-- Copying the first side's name keeps a hole comparison. -/
  varHole_instL : ∀ {n m} (ρ : Path), varHole n m → varHole (.inst ρ n) m
  /-- Renaming the second side's name keeps a hole comparison. -/
  varHole_rename : ∀ {n m m'}, varHole n m → preserve m m' → varHole n m'
  /-- Reading of code names as written. -/
  codeMap : Nm X₁ → Nm X₂
  /-- `codeMap` does not identify distinct names. -/
  codeMap_inj : Function.Injective codeMap
  /-- The code image of a name as written is a name as written. -/
  codeMap_src : ∀ s, ∃ s', codeMap (.src s) = .src s'
  /-- The code image of a root name is a root name. -/
  codeMap_root : ∀ s, root₁ s → ∃ s', codeMap (.src s) = .src s' ∧ root₂ s'
  /-- Base names a hole of sealed code may have.  An activation copies such a name
  inside a quotation of its body when its frame owns it. -/
  hole : X₁ → Prop

/-- Rename every name. Own lists are dropped: a term with `ownNil` keeps them empty. -/
def mapCode {Y Z : Type v} (f : Nm Y → Nm Z) : Tm S Y → Tm S Z
  | .sym s => .sym s
  | .fn F => .fn F
  | .var n => .var (f n)
  | .pvar n => .pvar (f n)
  | .lam x _ b => .lam (f x) [] (mapCode f b)
  | .app a b => .app (mapCode f a) (mapCode f b)
  | .quote c => .quote (mapCode f c)
  | .ctx ks c => .ctx (ks.map f) (mapCode f c)
  | .pquote c => .pquote (mapCode f c)
  | .letP p w b => .letP (mapCode f p) (mapCode f w) (mapCode f b)
  | .alt t₁ t₂ => .alt (mapCode f t₁) (mapCode f t₂)

/-- Every lambda in the term has an empty own list. -/
def ownNil {Y : Type v} : Tm S Y → Prop
  | .lam _ own b => own = [] ∧ ownNil b
  | .app f a => ownNil f ∧ ownNil a
  | .quote c => ownNil c
  | .ctx _ c => ownNil c
  | .pquote c => ownNil c
  | .letP p w b => ownNil p ∧ ownNil w ∧ ownNil b
  | .alt t₁ t₂ => ownNil t₁ ∧ ownNil t₂
  | _ => True

/-- The term holds no contextual code, at any depth (elaborated text holds
none). -/
def ctxFree {Y : Type v} : Tm S Y → Prop
  | .ctx _ _ => False
  | .lam _ _ b => ctxFree b
  | .app f a => ctxFree f ∧ ctxFree a
  | .quote c => ctxFree c
  | .pquote c => ctxFree c
  | .letP p w b => ctxFree p ∧ ctxFree w ∧ ctxFree b
  | .alt t₁ t₂ => ctxFree t₁ ∧ ctxFree t₂
  | _ => True

theorem codeVars_mapCode {Y Z : Type v} (f : Nm Y → Nm Z) :
    ∀ t : Tm S Y, codeVars (mapCode f t) = (codeVars t).map f
  | .sym _ => rfl
  | .fn _ => rfl
  | .var _ => rfl
  | .pvar _ => rfl
  | .lam _ _ b => by simp only [mapCode, codeVars, codeVars_mapCode f b]
  | .app a b => by simp only [mapCode, codeVars, codeVars_mapCode f a, codeVars_mapCode f b,
      List.map_append]
  | .quote c => by simp only [mapCode, codeVars, codeVars_mapCode f c]
  | .ctx _ c => by simp only [mapCode, codeVars, codeVars_mapCode f c]
  | .pquote c => by simp only [mapCode, codeVars, codeVars_mapCode f c]
  | .letP p w b => by simp only [mapCode, codeVars, codeVars_mapCode f p, codeVars_mapCode f w,
      codeVars_mapCode f b, List.map_append]
  | .alt t u => by simp only [mapCode, codeVars, codeVars_mapCode f t, codeVars_mapCode f u,
      List.map_append]

theorem ctxFree_mapCode {Y Z : Type v} (f : Nm Y → Nm Z) :
    ∀ {t : Tm S Y}, ctxFree t → ctxFree (mapCode f t)
  | .sym _, _ | .fn _, _ | .var _, _ | .pvar _, _ => trivial
  | .lam _ _ b, h => ctxFree_mapCode f (t := b) h
  | .app _ _, h => ⟨ctxFree_mapCode f h.1, ctxFree_mapCode f h.2⟩
  | .quote c, h => ctxFree_mapCode f (t := c) h
  | .ctx _ _, h => h.elim
  | .pquote c, h => ctxFree_mapCode f (t := c) h
  | .letP _ _ _, h => ⟨ctxFree_mapCode f h.1, ctxFree_mapCode f h.2.1, ctxFree_mapCode f h.2.2⟩
  | .alt _ _, h => ⟨ctxFree_mapCode f h.1, ctxFree_mapCode f h.2⟩

theorem list_map_injective {α β : Type v} {f : α → β} (hf : Function.Injective f) :
    ∀ {l₁ l₂ : List α}, List.map f l₁ = List.map f l₂ → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by
      simp only [List.map] at h
      cases h
  | _ :: _, [], h => by
      simp only [List.map] at h
      cases h
  | _ :: l₁, _ :: l₂, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hf h.1, list_map_injective hf h.2]

/-- On terms whose lambdas own nothing, renaming along an injective map is injective. -/
theorem mapCode_injective_ownNil {Y Z : Type v} {f : Nm Y → Nm Z}
    (hf : Function.Injective f) {t₁ : Tm S Y} :
    ∀ {t₂ : Tm S Y}, ownNil t₁ → ownNil t₂ → mapCode f t₁ = mapCode f t₂ → t₁ = t₂ := by
  induction t₁ with
  | sym s =>
      intro t₂ _ _ h
      cases t₂ with
      | sym _ =>
          simp only [mapCode, Tm.sym.injEq] at h
          rw [h]
      | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | fn F =>
      intro t₂ _ _ h
      cases t₂ with
      | fn _ =>
          simp only [mapCode, Tm.fn.injEq] at h
          rw [h]
      | sym _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | var n =>
      intro t₂ _ _ h
      cases t₂ with
      | var _ =>
          simp only [mapCode, Tm.var.injEq] at h
          rw [hf h]
      | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | pvar n =>
      intro t₂ _ _ h
      cases t₂ with
      | pvar _ =>
          simp only [mapCode, Tm.pvar.injEq] at h
          rw [hf h]
      | sym _ | fn _ | var _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | lam x own b ih =>
      intro t₂ h₁ h₂ h
      cases t₂ with
      | lam x' own' b' =>
          simp only [ownNil] at h₁ h₂
          rcases h₁ with ⟨rfl, hb⟩
          rcases h₂ with ⟨rfl, hb'⟩
          simp only [mapCode, Tm.lam.injEq] at h
          rcases h with ⟨hx, _, hbdy⟩
          rw [hf hx, ih hb hb' hbdy]
      | sym _ | fn _ | var _ | pvar _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | app f₁ a₁ ihf iha =>
      intro t₂ h₁ h₂ h
      cases t₂ with
      | app f₂ a₂ =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.app.injEq] at h
          rw [ihf h₁.1 h₂.1 h.1, iha h₁.2 h₂.2 h.2]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | quote c ih =>
      intro t₂ h₁ h₂ h
      cases t₂ with
      | quote c' =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.quote.injEq] at h
          rw [ih h₁ h₂ h]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | ctx ks c ih =>
      intro t₂ h₁ h₂ h
      cases t₂ with
      | ctx ks' c' =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.ctx.injEq] at h
          rcases h with ⟨hks, hc⟩
          rw [list_map_injective hf hks, ih h₁ h₂ hc]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | pquote c ih =>
      intro t₂ h₁ h₂ h
      cases t₂ with
      | pquote c' =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.pquote.injEq] at h
          rw [ih h₁ h₂ h]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | letP p w b ihp ihw ihb =>
      intro t₂ h₁ h₂ h
      cases t₂ with
      | letP p' w' b' =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.letP.injEq] at h
          rcases h with ⟨hp, hw, hb⟩
          rw [ihp h₁.1 h₂.1 hp, ihw h₁.2.1 h₂.2.1 hw, ihb h₁.2.2 h₂.2.2 hb]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | alt a b iha ihb =>
      intro t₂ h₁ h₂ h
      cases t₂ with
      | alt a' b' =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.alt.injEq] at h
          rw [iha h₁.1 h₂.1 h.1, ihb h₁.2 h₂.2 h.2]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ =>
          simp only [mapCode] at h
          cases h

/-! ## Sealed code read through the name map -/

/-- Every name of code: holes, binders, parameters, and the binders of contextual
code. -/
def codeNames {Y : Type v} : Tm S Y → List (Nm Y)
  | .var n => [n]
  | .pvar n => [n]
  | .lam x _ b => x :: codeNames b
  | .app f a => codeNames f ++ codeNames a
  | .quote c => codeNames c
  | .ctx ks c => ks ++ codeNames c
  | .pquote c => codeNames c
  | .letP p w b => codeNames p ++ codeNames w ++ codeNames b
  | .alt t u => codeNames t ++ codeNames u
  | _ => []

/-- The binders and parameters of code, and the binders of contextual code. -/
def codeBinders {Y : Type v} : Tm S Y → List (Nm Y)
  | .pvar n => [n]
  | .lam x _ b => x :: codeBinders b
  | .app f a => codeBinders f ++ codeBinders a
  | .quote c => codeBinders c
  | .ctx ks c => ks ++ codeBinders c
  | .pquote c => codeBinders c
  | .letP p w b => codeBinders p ++ codeBinders w ++ codeBinders b
  | .alt t u => codeBinders t ++ codeBinders u
  | _ => []

theorem mem_codeNames {Y : Type v} :
    ∀ (c : Tm S Y) {n : Nm Y}, n ∈ codeNames c ↔ n ∈ codeVars c ∨ n ∈ codeBinders c
  | .var m, n => by simp [codeNames, codeVars, codeBinders]
  | .pvar m, n => by simp [codeNames, codeVars, codeBinders]
  | .lam x _ b, n => by
      simp only [codeNames, codeVars, codeBinders, List.mem_cons, mem_codeNames b]
      tauto
  | .app f a, n => by
      simp only [codeNames, codeVars, codeBinders, List.mem_append, mem_codeNames f,
        mem_codeNames a]
      tauto
  | .quote c, n => by simp only [codeNames, codeVars, codeBinders, mem_codeNames c]
  | .ctx ks c, n => by
      simp only [codeNames, codeVars, codeBinders, List.mem_append, mem_codeNames c]
      tauto
  | .pquote c, n => by simp only [codeNames, codeVars, codeBinders, mem_codeNames c]
  | .letP p w b, n => by
      simp only [codeNames, codeVars, codeBinders, List.mem_append, mem_codeNames p,
        mem_codeNames w, mem_codeNames b]
      tauto
  | .alt t u, n => by
      simp only [codeNames, codeVars, codeBinders, List.mem_append, mem_codeNames t,
        mem_codeNames u]
      tauto
  | .sym _, n => by simp [codeNames, codeVars, codeBinders]
  | .fn _, n => by simp [codeNames, codeVars, codeBinders]

/-- A map injective on the elements of two lists maps them alike only when they
are equal. -/
theorem list_map_injOn {α β : Type v} {f : α → β} :
    ∀ {l₁ l₂ : List α}, Set.InjOn f {a | a ∈ l₁ ∨ a ∈ l₂} → List.map f l₁ = List.map f l₂ →
      l₁ = l₂
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l₁, b :: l₂, hf, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hf (by simp) (by simp) h.1, list_map_injOn (fun x hx y hy e => hf
        (by rcases hx with hx | hx <;> simp [hx]) (by rcases hy with hy | hy <;> simp [hy]) e) h.2]

/-- **On terms whose lambdas own nothing, renaming along a map injective on the
names of both terms is injective.** -/
theorem mapCode_injOn_ownNil {Y Z : Type v} {f : Nm Y → Nm Z} :
    ∀ {t₁ t₂ : Tm S Y}, ownNil t₁ → ownNil t₂ →
      Set.InjOn f {n | n ∈ codeNames t₁ ∨ n ∈ codeNames t₂} → mapCode f t₁ = mapCode f t₂ →
        t₁ = t₂
  | .sym s, t₂, _, _, _, h => by cases t₂ <;> simp_all [mapCode]
  | .fn F, t₂, _, _, _, h => by cases t₂ <;> simp_all [mapCode]
  | .var n, t₂, _, _, hf, h => by
      cases t₂ with
      | var m =>
          simp only [mapCode, Tm.var.injEq] at h
          rw [hf (by simp [codeNames]) (by simp [codeNames]) h]
      | _ => simp [mapCode] at h
  | .pvar n, t₂, _, _, hf, h => by
      cases t₂ with
      | pvar m =>
          simp only [mapCode, Tm.pvar.injEq] at h
          rw [hf (by simp [codeNames]) (by simp [codeNames]) h]
      | _ => simp [mapCode] at h
  | .lam x own b, t₂, h₁, h₂, hf, h => by
      cases t₂ with
      | lam x' own' b' =>
          simp only [ownNil] at h₁ h₂
          rcases h₁ with ⟨rfl, hb⟩
          rcases h₂ with ⟨rfl, hb'⟩
          simp only [mapCode, Tm.lam.injEq] at h
          rcases h with ⟨hx, _, hbdy⟩
          rw [hf (by simp [codeNames]) (by simp [codeNames]) hx,
            mapCode_injOn_ownNil hb hb' (fun a ha a' ha' e => hf (by
              rcases ha with ha | ha <;> simp [codeNames, ha]) (by
              rcases ha' with ha' | ha' <;> simp [codeNames, ha']) e) hbdy]
      | _ => simp [mapCode] at h
  | .app f₁ a₁, t₂, h₁, h₂, hf, h => by
      cases t₂ with
      | app f₂ a₂ =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.app.injEq] at h
          have hinj : ∀ (u u' : Tm S Y), (∀ n ∈ codeNames u, n ∈ codeNames (.app f₁ a₁)) →
              (∀ n ∈ codeNames u', n ∈ codeNames (.app f₂ a₂)) →
              Set.InjOn f {n | n ∈ codeNames u ∨ n ∈ codeNames u'} := by
            intro u u' hu hu' a ha a' ha' e
            exact hf (ha.elim (fun h => Or.inl (hu a h)) (fun h => Or.inr (hu' a h)))
              (ha'.elim (fun h => Or.inl (hu a' h)) (fun h => Or.inr (hu' a' h))) e
          rw [mapCode_injOn_ownNil h₁.1 h₂.1 (hinj f₁ f₂ (fun n hn => by simp [codeNames, hn])
              (fun n hn => by simp [codeNames, hn])) h.1,
            mapCode_injOn_ownNil h₁.2 h₂.2 (hinj a₁ a₂ (fun n hn => by simp [codeNames, hn])
              (fun n hn => by simp [codeNames, hn])) h.2]
      | _ => simp [mapCode] at h
  | .quote c, t₂, h₁, h₂, hf, h => by
      cases t₂ with
      | quote c' =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.quote.injEq] at h
          rw [mapCode_injOn_ownNil h₁ h₂ (fun a ha a' ha' e => hf (by simpa [codeNames] using ha)
            (by simpa [codeNames] using ha') e) h]
      | _ => simp [mapCode] at h
  | .ctx ks c, t₂, h₁, h₂, hf, h => by
      cases t₂ with
      | ctx ks' c' =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.ctx.injEq] at h
          rcases h with ⟨hks, hc⟩
          have hks' : ks = ks' := list_map_injOn (fun a ha a' ha' e => hf
            (by rcases ha with ha | ha <;> simp [codeNames, ha])
            (by rcases ha' with ha' | ha' <;> simp [codeNames, ha']) e) hks
          rw [hks', mapCode_injOn_ownNil h₁ h₂ (fun a ha a' ha' e => hf
            (by rcases ha with ha | ha <;> simp [codeNames, ha])
            (by rcases ha' with ha' | ha' <;> simp [codeNames, ha']) e) hc]
      | _ => simp [mapCode] at h
  | .pquote c, t₂, h₁, h₂, hf, h => by
      cases t₂ with
      | pquote c' =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.pquote.injEq] at h
          rw [mapCode_injOn_ownNil h₁ h₂ (fun a ha a' ha' e => hf (by simpa [codeNames] using ha)
            (by simpa [codeNames] using ha') e) h]
      | _ => simp [mapCode] at h
  | .letP p w b, t₂, h₁, h₂, hf, h => by
      cases t₂ with
      | letP p' w' b' =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.letP.injEq] at h
          have hinj : ∀ (u u' : Tm S Y), (∀ n ∈ codeNames u, n ∈ codeNames (.letP p w b)) →
              (∀ n ∈ codeNames u', n ∈ codeNames (.letP p' w' b')) →
              Set.InjOn f {n | n ∈ codeNames u ∨ n ∈ codeNames u'} := by
            intro u u' hu hu' a ha a' ha' e
            exact hf (ha.elim (fun h => Or.inl (hu a h)) (fun h => Or.inr (hu' a h)))
              (ha'.elim (fun h => Or.inl (hu a' h)) (fun h => Or.inr (hu' a' h))) e
          rw [mapCode_injOn_ownNil h₁.1 h₂.1 (hinj p p' (fun n hn => by simp [codeNames, hn])
              (fun n hn => by simp [codeNames, hn])) h.1,
            mapCode_injOn_ownNil h₁.2.1 h₂.2.1 (hinj w w' (fun n hn => by simp [codeNames, hn])
              (fun n hn => by simp [codeNames, hn])) h.2.1,
            mapCode_injOn_ownNil h₁.2.2 h₂.2.2 (hinj b b' (fun n hn => by simp [codeNames, hn])
              (fun n hn => by simp [codeNames, hn])) h.2.2]
      | _ => simp [mapCode] at h
  | .alt t u, t₂, h₁, h₂, hf, h => by
      cases t₂ with
      | alt t' u' =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.alt.injEq] at h
          have hinj : ∀ (v v' : Tm S Y), (∀ n ∈ codeNames v, n ∈ codeNames (.alt t u)) →
              (∀ n ∈ codeNames v', n ∈ codeNames (.alt t' u')) →
              Set.InjOn f {n | n ∈ codeNames v ∨ n ∈ codeNames v'} := by
            intro v v' hv hv' a ha a' ha' e
            exact hf (ha.elim (fun h => Or.inl (hv a h)) (fun h => Or.inr (hv' a h)))
              (ha'.elim (fun h => Or.inl (hv a' h)) (fun h => Or.inr (hv' a' h))) e
          rw [mapCode_injOn_ownNil h₁.1 h₂.1 (hinj t t' (fun n hn => by simp [codeNames, hn])
              (fun n hn => by simp [codeNames, hn])) h.1,
            mapCode_injOn_ownNil h₁.2 h₂.2 (hinj u u' (fun n hn => by simp [codeNames, hn])
              (fun n hn => by simp [codeNames, hn])) h.2]
      | _ => simp [mapCode] at h

/-- The name as written, under any activation copies. -/
def nmBase {Y : Type v} : Nm Y → Nm Y
  | .src s => .src s
  | .inst _ n => nmBase n

/-- The outermost activation tag of a name; `ρ` when it has none. -/
def tagOr {Y : Type v} (ρ : Path) : Nm Y → Path
  | .src _ => ρ
  | .inst ρ' _ => ρ'

/-- Code with every activation copy tag stripped: the code as written. -/
def stripCode {Y : Type v} (c : Tm S Y) : Tm S Y := mapCode nmBase c

/-- A name that may be a hole of sealed code: a hole base as written, or the copy
of one made by an activation. -/
def holeName (C : Setting S X₁ X₂) : Nm X₁ → Prop
  | .src s => C.hole s
  | .inst _ (.src s) => C.hole s
  | .inst _ (.inst _ _) => False

/-- The copy of a hole base made by an activation. -/
def holeCopy (C : Setting S X₁ X₂) : Nm X₁ → Prop
  | .inst _ (.src s) => C.hole s
  | _ => False

/-- **The form of sealed code** the relation reads: its lambdas own nothing, each
hole is a hole name, and each binder and parameter is a name as written. -/
def CodeForm (C : Setting S X₁ X₂) (c : Tm S X₁) : Prop :=
  ownNil c ∧ (∀ n ∈ codeVars c, holeName C n) ∧ ∀ n ∈ codeBinders c, ∃ s, n = .src s

/-- **The reading of a first-side name of sealed code under the name map `ν`.**  A
name as written is read by `codeMap`.  A copy made by an activation is the copy of
its code image made by the activation `ν` pairs with it, whose path is the tag of
`ν`'s image of the copy. -/
def holeRead (C : Setting S X₁ X₂) (ν : Nm X₁ → Nm X₂) : Nm X₁ → Nm X₂
  | .src s => C.codeMap (.src s)
  | .inst ρ m => .inst (tagOr ρ (ν (.inst ρ m))) (C.codeMap m)

/-- **Related sealed code under the name map `ν`.**  The code as written is
related by `C.Q`, the first side has the code form, and the second side is the
first read through `holeRead`.  Before an activation renames a hole the reading is
`codeMap`; after it, a copy is read as the copy the paired activation made of the
second side's hole. -/
def QR (C : Setting S X₁ X₂) (ν : Nm X₁ → Nm X₂) (c₁ : Tm S X₁) (c₂ : Tm S X₂) : Prop :=
  C.Q (stripCode c₁) (stripCode c₂) ∧ CodeForm C c₁ ∧ c₂ = mapCode (holeRead C ν) c₁

/-- Related ground values: the same data, with related code in quotations.
Contextual code is the same open code read through `holeRead`. -/
inductive GRel (C : Setting S X₁ X₂) (ν : Nm X₁ → Nm X₂) : GVal S X₁ → GVal S X₂ → Prop
  | sym (s : S) : GRel C ν (.sym s) (.sym s)
  | app {f₁ a₁ f₂ a₂} : GRel C ν f₁ f₂ → GRel C ν a₁ a₂ → GRel C ν (.app f₁ a₁) (.app f₂ a₂)
  | quote {c₁ c₂} : QR C ν c₁ c₂ → GRel C ν (.quote c₁) (.quote c₂)
  /-- Open code under the binders it mentions, read through `holeRead`. -/
  | ctx {ks₁ : List (Nm X₁)} {c₁ : Tm S X₁} {ks₂ : List (Nm X₂)} {c₂ : Tm S X₂}
      (hf : CodeForm C (.ctx ks₁ c₁)) (hks : ks₂ = ks₁.map (holeRead C ν))
      (hc : c₂ = mapCode (holeRead C ν) c₁) :
      GRel C ν (.ctx ks₁ c₁) (.ctx ks₂ c₂)

/-- Names that may occur free: activation copies, and root names. -/
def OK₁ (C : Setting S X₁ X₂) : Nm X₁ → Prop
  | .src s => C.root₁ s
  | .inst _ _ => True

/-- The same on the second side. -/
def OK₂ (C : Setting S X₁ X₂) : Nm X₂ → Prop
  | .src s => C.root₂ s
  | .inst _ _ => True

/-- Same outer shape, with the setting's reading of names; sealed code is read
through `ν`. A lambda contributes its binders only: a body is read by `matchCode`
only after `enterLam`, and that permission is recorded on the relation, not
here. -/
def ShapeParallel (C : Setting S X₁ X₂) (ν : Nm X₁ → Nm X₂) : Tm S X₁ → Tm S X₂ → Prop
  | .sym s₁, .sym s₂ => s₁ = s₂
  | .fn f₁, .fn f₂ => f₁ = f₂
  | .var n₁, .var n₂ => C.varHole n₁ n₂
  | .pvar x₁, .pvar x₂ => C.parOK x₁ x₂
  | .lam x₁ o₁ _, .lam x₂ o₂ _ => C.bareLam x₁ o₁ x₂ o₂
  | .app f₁ a₁, .app f₂ a₂ => ShapeParallel C ν f₁ f₂ ∧ ShapeParallel C ν a₁ a₂
  | .quote c₁, .quote c₂ => QR C ν c₁ c₂
  | .pquote c₁, .pquote c₂ => ShapeParallel C ν c₁ c₂
  | .letP p₁ w₁ b₁, .letP p₂ w₂ b₂ =>
      ShapeParallel C ν p₁ p₂ ∧ ShapeParallel C ν w₁ w₂ ∧ ShapeParallel C ν b₁ b₂
  | .alt t₁ u₁, .alt t₂ u₂ => ShapeParallel C ν t₁ t₂ ∧ ShapeParallel C ν u₁ u₂
  | .ctx ks₁ c₁, .ctx ks₂ c₂ =>
      CodeForm C (.ctx ks₁ c₁) ∧ ks₂ = ks₁.map (holeRead C ν) ∧ c₂ = mapCode (holeRead C ν) c₁
  | _, _ => False

variable [DecidableEq X₁] [DecidableEq X₂]

/-- **The relation.**  `ν` maps store names, `μ` parameters; `Res` lists the
reserved names of the second side that the pair's pending constructs own.
`ok = true` when no pending activation sits where matching of code can enter.
A lambda's own result is stable even when its body is not: matching enters
that body only when `enterLam` holds, and then the body is stable too. -/
inductive Rel (C : Setting S X₁ X₂) :
    (Nm X₁ → Nm X₂) → (Nm X₁ → Nm X₂) → Kd → List (Nm X₂) → Bool →
      Tm S X₁ → Tm S X₂ → Prop
  | sym {ν μ k} (s : S) : Rel C ν μ k [] true (.sym s) (.sym s)
  | fn {ν μ k} (F : S) : Rel C ν μ k [] true (.fn F) (.fn F)
  | var {ν μ k} (n : Nm X₁) (hv : C.varHole n (ν n)) :
      Rel C ν μ k [] true (.var n) (.var (ν n))
  | pvar {ν μ k} (x : Nm X₁) (hp : C.parOK x (μ x)) :
      Rel C ν μ k [] true (.pvar x) (.pvar (μ x))
  /-- Sealed code, read through `ν` (`QR`). -/
  | quote {ν μ k c₁ c₂} (h : QR C ν c₁ c₂) : Rel C ν μ k [] true (.quote c₁) (.quote c₂)
  /-- A pattern quotation. The body is stable code of one shape: a hole is a
  free name of that code, and a binder of the code is named inside the body. -/
  | pquote {ν μ k c₁ c₂ ob}
      (h : Rel C ν μ .code [] ob c₁ c₂) (hp : ShapeParallel C ν c₁ c₂) (hok : ob = true) :
      Rel C ν μ k [] true (.pquote c₁) (.pquote c₂)
  | app {ν μ k R₁ R₂ o₁ o₂ f₁ a₁ f₂ a₂}
      (hf : Rel C ν μ k R₁ o₁ f₁ f₂) (ha : Rel C ν μ k R₂ o₂ a₁ a₂) :
      Rel C ν μ k (R₁ ++ R₂) (o₁ && o₂) (.app f₁ a₁) (.app f₂ a₂)
  | letP {ν μ k Rp Rw Rb op ow ob p₁ w₁ b₁ p₂ w₂ b₂} (hk : k ≠ .val)
      (hp : Rel C ν μ .pat Rp op p₁ p₂) (hw : Rel C ν μ .code Rw ow w₁ w₂)
      (hb : Rel C ν μ .code Rb ob b₁ b₂) :
      Rel C ν μ k (Rp ++ Rw ++ Rb) (op && ow && ob) (.letP p₁ w₁ b₁) (.letP p₂ w₂ b₂)
  | alt {ν μ k R₁ R₂ o₁ o₂ t₁ u₁ t₂ u₂} (hk : k ≠ .val)
      (h₁ : Rel C ν μ .code R₁ o₁ t₁ t₂) (h₂ : Rel C ν μ .code R₂ o₂ u₁ u₂) :
      Rel C ν μ k (R₁ ++ R₂) (o₁ && o₂) (.alt t₁ u₁) (.alt t₂ u₂)
  | lam {ν μ k x₁ own₁ b₁ x₂ own₂ b₂ νb μb Rb ob}
      (hνb : ∀ n, ownKey own₁ n = false → νb n = ν n)
      (hμb : ∀ x, x ≠ x₁ → μb x = μ x) (hμx : μb x₁ = x₂)
      (hr₁ : ∀ s ∈ own₁, ¬ C.root₁ s) (hr₂ : ∀ s ∈ own₂, ¬ C.root₂ s)
      (hb : Rel C νb μb .code Rb ob b₁ b₂)
      (hown : ∀ n ∈ freeNames b₁, ownKey own₂ (νb n) = ownKey own₁ n)
      (hres : ∀ m ∈ Rb, ownKey own₂ m = true)
      (hinj : ∀ n ∈ freeNames b₁ ++ sealedFree b₁, ∀ n' ∈ freeNames b₁ ++ sealedFree b₁,
        ownKey own₁ n = true → ownKey own₁ n' = true → νb n = νb n' → n = n')
      (hdisj : ∀ n ∈ freeNames b₁ ++ sealedFree b₁, ownKey own₁ n = true → νb n ∉ Rb)
      (hnd : Rb.Nodup)
      (hpar : ∀ x ∈ freeParams b₁, x ≠ x₁ → μ x ≠ x₂)
      (hbare : C.bareLam x₁ own₁ x₂ own₂)
      (hseen : C.enterLam x₁ x₂ → ob = true)
      (hsealO : ∀ s, Nm.src s ∈ sealedFree b₁ →
        ownKey own₂ (C.codeMap (.src s)) = ownKey own₁ (.src s))
      (hsealK : ∀ n ∈ sealedFree b₁, ownKey own₁ n = true → ∃ s, νb n = .src s) :
      Rel C ν μ k [] true (.lam x₁ own₁ b₁) (.lam x₂ own₂ b₂)
  | letAct {ν μ k ℓ own p₁ w₁ b₁ p₂ w₂ b₂ νi Rh Rw Rp Rb ow op ob} (hk : k ≠ .val)
      (hνi : ∀ n, ownKey own n = false → νi n = ν n)
      (hr : ∀ s ∈ own, ¬ C.root₁ s ∧ ¬ C.hole s)
      (hℓp : ℓ ∉ freeParams p₁) (hℓb : ℓ ∉ freeParams b₁)
      (hw : Rel C ν μ .code Rw ow w₁ w₂) (hp : Rel C νi μ .pat Rp op p₁ p₂)
      (hb : Rel C νi μ .code Rb ob b₁ b₂)
      (hlive : ∀ n ∈ freeNames p₁ ++ freeNames b₁, ownKey own n = true → νi n ∈ Rh)
      (hinj : ∀ n ∈ freeNames p₁ ++ freeNames b₁, ∀ n' ∈ freeNames p₁ ++ freeNames b₁,
        ownKey own n = true → ownKey own n' = true → νi n = νi n' → n = n') :
      Rel C ν μ k (Rh ++ Rw ++ Rp ++ Rb) false
        (.app (.lam ℓ own (.letP p₁ (.pvar ℓ) b₁)) w₁) (.letP p₂ w₂ b₂)
  | newAct {ν μ ℓ own b₁ b₂ νi Rh Rb ob}
      (hνi : ∀ n, ownKey own n = false → νi n = ν n)
      (hr : ∀ s ∈ own, ¬ C.root₁ s ∧ ¬ C.hole s)
      (hℓ : ℓ ∉ freeParams b₁)
      (hb : Rel C νi μ .code Rb ob b₁ b₂)
      (hlive : ∀ n ∈ freeNames b₁, ownKey own n = true → νi n ∈ Rh)
      (hinj : ∀ n ∈ freeNames b₁, ∀ n' ∈ freeNames b₁,
        ownKey own n = true → ownKey own n' = true → νi n = νi n' → n = n') :
      Rel C ν μ .code (Rh ++ Rb) false (.app (.lam ℓ own b₁) (.lam ℓ [] (.pvar ℓ))) b₂
  /-- Contextual code, a value. The body is read through `holeRead`. -/
  | ctx {ν μ k ks₁ c₁ ks₂ c₂}
      (hf : CodeForm C (.ctx ks₁ c₁)) (hks : ks₂ = ks₁.map (holeRead C ν))
      (hc : c₂ = mapCode (holeRead C ν) c₁) :
      Rel C ν μ k [] true (.ctx ks₁ c₁) (.ctx ks₂ c₂)

variable {C : Setting S X₁ X₂}

/-! ## Basic facts -/

theorem Kd.le_refl : ∀ k : Kd, k.le k
  | .val => trivial
  | .pat => trivial
  | .code => trivial

theorem Kd.le_code : ∀ k : Kd, k.le .code
  | .val => trivial
  | .pat => trivial
  | .code => trivial

theorem Kd.ne_val_of_le {k k' : Kd} (h : k.le k') (hk : k ≠ .val) : k' ≠ .val := by
  cases k <;> cases k' <;> simp_all [Kd.le]

theorem Kd.eq_code_of_le {k : Kd} (h : Kd.code.le k) : k = .code := by
  cases k <;> simp_all [Kd.le]

/-- Only a value sits at or below a value. -/
theorem Kd.eq_val_of_le {k : Kd} (h : k.le .val) : k = .val := by
  cases k <;> simp_all [Kd.le]

/-- A larger kind admits more. The stability bit is unchanged. -/
theorem Rel.mono {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {k'}, k.le k' → Rel C ν μ k' Res ok t₁ t₂ := by
  induction h with
  | sym s => intro _ _; exact .sym s
  | fn F => intro _ _; exact .fn F
  | var n hv => intro _ _; exact .var n hv
  | pvar x hp => intro _ _; exact .pvar x hp
  | quote hq => intro _ _; exact .quote hq
  | ctx ho hks hc => intro _ _; exact .ctx ho hks hc
  | pquote h hp hok => intro _ _; exact .pquote h hp hok
  | app _ _ ihf iha => intro _ hk; exact .app (ihf hk) (iha hk)
  | letP hk' hp hw hb => intro _ hk; exact .letP (Kd.ne_val_of_le hk hk') hp hw hb
  | alt hk' h₁ h₂ => intro _ hk; exact .alt (Kd.ne_val_of_le hk hk') h₁ h₂
  | lam hνb hμb hμx hr₁ hr₂ hb hown hres hinj hdisj hnd hpar hbare hseen hsealO hsealK =>
      intro _ _
      exact .lam hνb hμb hμx hr₁ hr₂ hb hown hres hinj hdisj hnd hpar hbare hseen hsealO hsealK
  | letAct hk' hνi hr hℓp hℓb hw hp hb hlive hinj =>
      intro _ hk; exact .letAct (Kd.ne_val_of_le hk hk') hνi hr hℓp hℓb hw hp hb hlive hinj
  | newAct hνi hr hℓ hb hlive hinj =>
      intro _ hk
      rw [Kd.eq_code_of_le hk]
      exact .newAct hνi hr hℓ hb hlive hinj

/-- A value is related as anything. Its stability bit is `true`. -/
theorem Rel.of_val {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁} {t₂ : Tm S X₂}
    (h : Rel C ν μ .val Res true t₁ t₂) (k : Kd) : Rel C ν μ k Res true t₁ t₂ :=
  h.mono trivial

omit [DecidableEq X₂] in
/-- A name that may occur free is owned by no binder of the first side. -/
theorem ownKey_of_OK₁ {own : List X₁} (hr : ∀ s ∈ own, ¬ C.root₁ s) :
    ∀ {n : Nm X₁}, OK₁ C n → ownKey own n = false
  | .src s, h => by
      simp only [ownKey, List.contains_eq_mem, decide_eq_false_iff_not]
      exact fun hs => hr s hs h
  | .inst _ _, _ => rfl

omit [DecidableEq X₁] in
/-- The same on the second side. -/
theorem ownKey_of_OK₂ {own : List X₂} (hr : ∀ s ∈ own, ¬ C.root₂ s) :
    ∀ {n : Nm X₂}, OK₂ C n → ownKey own n = false
  | .src s, h => by
      simp only [ownKey, List.contains_eq_mem, decide_eq_false_iff_not]
      exact fun hs => hr s hs h
  | .inst _ _, _ => rfl

theorem mem_freeNames_lam {x : Nm X₁} {own : List X₁} {b : Tm S X₁} {n : Nm X₁} :
    n ∈ freeNames (.lam x own b : Tm S X₁) ↔ n ∈ freeNames b ∧ ownKey own n = false := by
  simp [freeNames]

theorem mem_freeParams_lam {x : Nm X₁} {own : List X₁} {b : Tm S X₁} {y : Nm X₁} :
    y ∈ freeParams (.lam x own b : Tm S X₁) ↔ y ∈ freeParams b ∧ y ≠ x := by
  simp [freeParams]

/-! ## Free names and parameters correspond -/

/-- Every free name of the first side is sent to a free name of the second. -/
theorem Rel.mem_freeNames {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {n}, n ∈ freeNames t₁ → ν n ∈ freeNames t₂ := by
  induction h with
  | sym s => intro n hn; simp [freeNames] at hn
  | fn F => intro n hn; simp [freeNames] at hn
  | var m _ => intro n hn; simp only [freeNames, List.mem_singleton] at hn ⊢; rw [hn]
  | pvar x _ => intro n hn; simp [freeNames] at hn
  | quote _ => intro n hn; simp [freeNames] at hn
  | ctx _ _ _ => intro n hn; simp [freeNames] at hn
  | pquote _ _ _ ih =>
      intro n hn
      simp only [freeNames] at hn ⊢
      exact ih hn
  | app _ _ ihf iha =>
      intro n hn
      simp only [freeNames, List.mem_append] at hn ⊢
      exact hn.imp ihf iha
  | letP _ _ _ _ ihp ihw ihb =>
      intro n hn
      simp only [freeNames, List.mem_append] at hn ⊢
      rcases hn with (hn | hn) | hn
      · exact Or.inl (Or.inl (ihp hn))
      · exact Or.inl (Or.inr (ihw hn))
      · exact Or.inr (ihb hn)
  | alt _ _ _ ih₁ ih₂ =>
      intro n hn
      simp only [freeNames, List.mem_append] at hn ⊢
      exact hn.imp ih₁ ih₂
  | lam hνb _ _ _ _ _ hown _ _ _ _ _ _ _ _ _ ihb =>
      intro n hn
      rw [mem_freeNames_lam] at hn ⊢
      obtain ⟨hn, hk⟩ := hn
      have e := hνb n hk
      refine ⟨e ▸ ihb hn, ?_⟩
      rw [← e, hown n hn, hk]
  | letAct _ hνi _ _ _ _ _ _ _ _ ihw ihp ihb =>
      intro n hn
      simp only [freeNames, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.not_mem_nil, or_false] at hn ⊢
      rcases hn with ⟨hn | hn, hk⟩ | hn
      · rw [← hνi n hk]; exact Or.inl (Or.inl (ihp hn))
      · rw [← hνi n hk]; exact Or.inr (ihb hn)
      · exact Or.inl (Or.inr (ihw hn))
  | newAct hνi _ _ _ _ _ ihb =>
      intro n hn
      simp only [freeNames, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.not_mem_nil] at hn
      rcases hn with ⟨hn, hk⟩ | ⟨hf, _⟩
      · rw [← hνi n hk]
        exact ihb hn
      · exact hf.elim

omit [DecidableEq X₂] in
/-- `holeRead` reads the name map only at activation copies, which no own list
owns. -/
theorem holeRead_of_unowned {ν ν' : Nm X₁ → Nm X₂} {own : List X₁}
    (h : ∀ n, ownKey own n = false → ν' n = ν n) (n : Nm X₁) :
    holeRead C ν' n = holeRead C ν n := by
  cases n with
  | src _ => rfl
  | inst ρ m => simp only [holeRead, h (.inst ρ m) rfl]

/-- **A free name of sealed code is read into the other side's sealed code**,
through `holeRead`. -/
theorem Rel.holeRead_mem_sealedFree {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)}
    {ok : Bool} {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {n}, n ∈ sealedFree t₁ → holeRead C ν n ∈ sealedFree t₂ := by
  induction h with
  | sym s => intro n hn; simp [sealedFree] at hn
  | fn F => intro n hn; simp [sealedFree] at hn
  | var m _ => intro n hn; simp [sealedFree] at hn
  | pvar x _ => intro n hn; simp [sealedFree] at hn
  | quote hq =>
      intro n hn
      obtain ⟨-, -, rfl⟩ := hq
      simp only [sealedFree] at hn ⊢
      rw [codeVars_mapCode]
      exact List.mem_map_of_mem hn
  | ctx _ _ hc =>
      intro n hn
      subst hc
      simp only [sealedFree] at hn ⊢
      rw [codeVars_mapCode]
      exact List.mem_map_of_mem hn
  | pquote _ _ _ ih =>
      intro n hn
      simp only [sealedFree] at hn ⊢
      exact ih hn
  | app _ _ ihf iha =>
      intro n hn
      simp only [sealedFree, List.mem_append] at hn ⊢
      exact hn.imp ihf iha
  | letP _ _ _ _ ihp ihw ihb =>
      intro n hn
      simp only [sealedFree, List.mem_append] at hn ⊢
      rcases hn with (hn | hn) | hn
      · exact Or.inl (Or.inl (ihp hn))
      · exact Or.inl (Or.inr (ihw hn))
      · exact Or.inr (ihb hn)
  | alt _ _ _ ih₁ ih₂ =>
      intro n hn
      simp only [sealedFree, List.mem_append] at hn ⊢
      exact hn.imp ih₁ ih₂
  | lam hνb _ _ _ _ _ _ _ _ _ _ _ _ _ hsealO _ ihb =>
      intro n hn
      simp only [sealedFree, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hn ⊢
      obtain ⟨hn, hk⟩ := hn
      refine ⟨holeRead_of_unowned hνb n ▸ ihb hn, ?_⟩
      cases n with
      | src s => exact (hsealO s hn).trans hk
      | inst _ _ => rfl
  | letAct _ hνi _ _ _ _ _ _ _ _ ihw ihp ihb =>
      intro n hn
      simp only [sealedFree, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.not_mem_nil, or_false] at hn ⊢
      rcases hn with ⟨hn | hn, hk⟩ | hn
      · rw [← holeRead_of_unowned hνi n]; exact Or.inl (Or.inl (ihp hn))
      · rw [← holeRead_of_unowned hνi n]; exact Or.inr (ihb hn)
      · exact Or.inl (Or.inr (ihw hn))
  | newAct hνi _ _ _ _ _ ihb =>
      intro n hn
      simp only [sealedFree, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.not_mem_nil] at hn
      rcases hn with ⟨hn, -⟩ | ⟨hf, -⟩
      · rw [← holeRead_of_unowned hνi n]
        exact ihb hn
      · exact hf.elim

/-- **A term without contextual code is related to one without contextual
code.** -/
theorem Rel.ctxFree {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ctxFree t₁ → ctxFree t₂ := by
  induction h with
  | sym _ | fn _ | var _ _ | pvar _ _ => intro _; trivial
  | quote hq =>
      intro hc
      obtain ⟨-, -, rfl⟩ := hq
      exact ctxFree_mapCode _ (t := _) hc
  | ctx _ _ _ => intro hc; exact hc.elim
  | pquote _ _ _ ih => exact ih
  | app _ _ ihf iha => intro hc; exact ⟨ihf hc.1, iha hc.2⟩
  | letP _ _ _ _ ihp ihw ihb => intro hc; exact ⟨ihp hc.1, ihw hc.2.1, ihb hc.2.2⟩
  | alt _ _ _ ih₁ ih₂ => intro hc; exact ⟨ih₁ hc.1, ih₂ hc.2⟩
  | lam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihb => exact ihb
  | letAct _ _ _ _ _ _ _ _ _ _ ihw ihp ihb =>
      intro hc
      exact ⟨ihp hc.1.1, ihw hc.2, ihb hc.1.2.2⟩
  | newAct _ _ _ _ _ _ ihb => intro hc; exact ihb hc.1

/-- Every free parameter of the first side is sent to a free parameter of the
second. -/
theorem Rel.mem_freeParams {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {x}, x ∈ freeParams t₁ → μ x ∈ freeParams t₂ := by
  induction h with
  | sym s => intro x hx; simp [freeParams] at hx
  | fn F => intro x hx; simp [freeParams] at hx
  | var m _ => intro x hx; simp [freeParams] at hx
  | pvar y _ => intro x hx; simp only [freeParams, List.mem_singleton] at hx ⊢; rw [hx]
  | quote _ => intro x hx; simp [freeParams] at hx
  | ctx _ _ _ => intro x hx; simp [freeParams] at hx
  | pquote _ _ _ ih =>
      intro x hx
      simp only [freeParams] at hx ⊢
      exact ih hx
  | app _ _ ihf iha =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx ⊢
      exact hx.imp ihf iha
  | letP _ _ _ _ ihp ihw ihb =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx ⊢
      rcases hx with (hx | hx) | hx
      · exact Or.inl (Or.inl (ihp hx))
      · exact Or.inl (Or.inr (ihw hx))
      · exact Or.inr (ihb hx)
  | alt _ _ _ ih₁ ih₂ =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx ⊢
      exact hx.imp ih₁ ih₂
  | lam _ hμb hμx _ _ _ _ _ _ _ _ hpar _ _ _ _ ihb =>
      intro x hx
      rw [mem_freeParams_lam] at hx ⊢
      obtain ⟨hx, hne⟩ := hx
      have e := hμb x hne
      exact ⟨e ▸ ihb hx, hpar x hx hne⟩
  | letAct _ _ _ _ _ _ _ _ _ _ ihw ihp ihb =>
      intro x hx
      simp only [freeParams, List.mem_append, List.mem_filter, decide_eq_true_eq,
        List.mem_singleton] at hx ⊢
      rcases hx with ⟨(hx | hx) | hx, hne⟩ | hx
      · exact Or.inl (Or.inl (ihp hx))
      · exact absurd hx hne
      · exact Or.inr (ihb hx)
      · exact Or.inl (Or.inr (ihw hx))
  | newAct _ _ _ _ _ _ ihb =>
      intro x hx
      simp only [freeParams, List.mem_append, List.mem_filter, decide_eq_true_eq,
        List.mem_singleton] at hx
      rcases hx with ⟨hx, _⟩ | ⟨hx, hne⟩
      · exact ihb hx
      · exact absurd hx hne


/-! ## Free names and parameters of the two pending constructs -/

theorem mem_freeNames_letAct {ℓ : Nm X₁} {own : List X₁} {p b w : Tm S X₁} {n : Nm X₁} :
    n ∈ freeNames (.app (.lam ℓ own (.letP p (.pvar ℓ) b)) w : Tm S X₁) ↔
      ((n ∈ freeNames p ∨ n ∈ freeNames b) ∧ ownKey own n = false) ∨ n ∈ freeNames w := by
  simp only [freeNames, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.not_mem_nil, or_false]

theorem mem_freeParams_letAct {ℓ : Nm X₁} {own : List X₁} {p b w : Tm S X₁} {x : Nm X₁} :
    x ∈ freeParams (.app (.lam ℓ own (.letP p (.pvar ℓ) b)) w : Tm S X₁) ↔
      ((x ∈ freeParams p ∨ x ∈ freeParams b) ∧ x ≠ ℓ) ∨ x ∈ freeParams w := by
  simp only [freeParams, List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_singleton]
  constructor
  · rintro (⟨(h | h) | h, hne⟩ | h)
    · exact Or.inl ⟨Or.inl h, hne⟩
    · exact absurd h hne
    · exact Or.inl ⟨Or.inr h, hne⟩
    · exact Or.inr h
  · rintro (⟨h | h, hne⟩ | h)
    · exact Or.inl ⟨Or.inl (Or.inl h), hne⟩
    · exact Or.inl ⟨Or.inr h, hne⟩
    · exact Or.inr h

theorem mem_freeNames_newAct {ℓ : Nm X₁} {own : List X₁} {b : Tm S X₁} {n : Nm X₁} :
    n ∈ freeNames (.app (.lam ℓ own b) (.lam ℓ [] (.pvar ℓ)) : Tm S X₁) ↔
      n ∈ freeNames b ∧ ownKey own n = false := by
  simp only [freeNames, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.not_mem_nil, false_and, or_false]

theorem mem_freeParams_newAct {ℓ : Nm X₁} {own : List X₁} {b : Tm S X₁} {x : Nm X₁} :
    x ∈ freeParams (.app (.lam ℓ own b) (.lam ℓ [] (.pvar ℓ)) : Tm S X₁) ↔
      x ∈ freeParams b ∧ x ≠ ℓ := by
  simp only [freeParams, List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_singleton]
  constructor
  · rintro (h | ⟨h, hne⟩)
    · exact h
    · exact absurd h hne
  · intro h
    exact Or.inl h

/-! ## Congruence -/

/-- **The names of a term the relation reads**: its free names, and the free names
of its sealed code. -/
def relNames {Y : Type v} [DecidableEq Y] (t : Tm S Y) : List (Nm Y) := freeNames t ++ sealedFree t

omit [DecidableEq X₁] [DecidableEq X₂] in
theorem mapCode_congr {Y Z : Type v} {f g : Nm Y → Nm Z} :
    ∀ (t : Tm S Y), (∀ n ∈ codeNames t, f n = g n) → mapCode f t = mapCode g t
  | .sym _, _ => rfl
  | .fn _, _ => rfl
  | .var n, h => by simp [mapCode, h n (by simp [codeNames])]
  | .pvar n, h => by simp [mapCode, h n (by simp [codeNames])]
  | .lam x _ b, h => by
      simp only [mapCode, h x (by simp [codeNames]),
        mapCode_congr b (fun n hn => h n (by simp [codeNames, hn]))]
  | .app a b, h => by
      simp only [mapCode, mapCode_congr a (fun n hn => h n (by simp [codeNames, hn])),
        mapCode_congr b (fun n hn => h n (by simp [codeNames, hn]))]
  | .quote c, h => by
      simp only [mapCode, mapCode_congr c (fun n hn => h n (by simp [codeNames, hn]))]
  | .ctx ks c, h => by
      simp only [mapCode, mapCode_congr c (fun n hn => h n (by simp [codeNames, hn]))]
      congr 1
      exact List.map_congr_left (fun n hn => h n (by simp [codeNames, hn]))
  | .pquote c, h => by
      simp only [mapCode, mapCode_congr c (fun n hn => h n (by simp [codeNames, hn]))]
  | .letP p w b, h => by
      simp only [mapCode, mapCode_congr p (fun n hn => h n (by simp [codeNames, hn])),
        mapCode_congr w (fun n hn => h n (by simp [codeNames, hn])),
        mapCode_congr b (fun n hn => h n (by simp [codeNames, hn]))]
  | .alt t₁ t₂, h => by
      simp only [mapCode, mapCode_congr t₁ (fun n hn => h n (by simp [codeNames, hn])),
        mapCode_congr t₂ (fun n hn => h n (by simp [codeNames, hn]))]

omit [DecidableEq X₁] [DecidableEq X₂] in
/-- The reading of code reads the name map only at the hole copies of the code. -/
theorem holeRead_congr {ν ν' : Nm X₁ → Nm X₂} {c : Tm S X₁} (hf : CodeForm C c)
    (h : ∀ n ∈ codeVars c, (∃ s, n = .src s) ∨ ν n = ν' n) :
    ∀ n ∈ codeNames c, holeRead C ν n = holeRead C ν' n := by
  intro n hn
  rcases (mem_codeNames c).1 hn with hv | hb
  · cases n with
    | src s => rfl
    | inst ρ m =>
        rcases h _ hv with ⟨s, hs⟩ | e
        · cases hs
        · simp only [holeRead, e]
  · obtain ⟨s, rfl⟩ := hf.2.2 n hb
    rfl

omit [DecidableEq X₁] [DecidableEq X₂] in
/-- **Related sealed code depends on the name map only at its hole copies.** -/
theorem QR.congr {ν ν' : Nm X₁ → Nm X₂} {c₁ : Tm S X₁} {c₂ : Tm S X₂} (h : QR C ν c₁ c₂)
    (hν : ∀ n ∈ codeVars c₁, (∃ s, n = .src s) ∨ ν n = ν' n) : QR C ν' c₁ c₂ := by
  obtain ⟨hq, hf, rfl⟩ := h
  exact ⟨hq, hf, mapCode_congr c₁ (holeRead_congr hf hν)⟩

omit [DecidableEq X₁] [DecidableEq X₂] in
/-- Contextual code depends on the name map only at its hole copies. -/
theorem ctx_congr {ν ν' : Nm X₁ → Nm X₂} {ks₁ : List (Nm X₁)} {c₁ : Tm S X₁}
    (hf : CodeForm C (.ctx ks₁ c₁)) (hν : ∀ n ∈ codeVars c₁, (∃ s, n = .src s) ∨ ν n = ν' n) :
    ks₁.map (holeRead C ν) = ks₁.map (holeRead C ν') ∧
      mapCode (holeRead C ν) c₁ = mapCode (holeRead C ν') c₁ := by
  have e := holeRead_congr (c := .ctx ks₁ c₁) hf (by simpa [codeVars] using hν)
  exact ⟨List.map_congr_left fun n hn => e n (by simp [codeNames, hn]),
    mapCode_congr c₁ fun n hn => e n (by simp [codeNames, hn])⟩

omit [DecidableEq X₂] in
/-- Weak shape reads the name map only at the hole copies of free sealed code. -/
theorem ShapeParallel.congr {ν ν' : Nm X₁ → Nm X₂} {t₁ : Tm S X₁} :
    ∀ {t₂ : Tm S X₂}, ShapeParallel C ν t₁ t₂ →
      (∀ n ∈ sealedFree t₁, (∃ s, n = .src s) ∨ ν n = ν' n) → ShapeParallel C ν' t₁ t₂ := by
  induction t₁ with
  | sym _ => intro t₂ h _; cases t₂ <;> exact h
  | fn _ => intro t₂ h _; cases t₂ <;> exact h
  | var _ => intro t₂ h _; cases t₂ <;> exact h
  | pvar _ => intro t₂ h _; cases t₂ <;> exact h
  | lam _ _ _ _ => intro t₂ h _; cases t₂ <;> exact h
  | app f₁ a₁ ihf iha =>
      intro t₂ h hν
      cases t₂ with
      | app f₂ a₂ =>
          exact ⟨ihf h.1 (fun n hn => hν n (by simp [sealedFree, hn])),
            iha h.2 (fun n hn => hν n (by simp [sealedFree, hn]))⟩
      | _ => exact h
  | quote c₁ _ =>
      intro t₂ h hν
      cases t₂ with
      | quote c₂ => exact QR.congr h (fun n hn => hν n (by simpa [sealedFree] using hn))
      | _ => exact h
  | pquote c₁ ih =>
      intro t₂ h hν
      cases t₂ with
      | pquote c₂ => exact ih h (fun n hn => hν n (by simpa [sealedFree] using hn))
      | _ => exact h
  | letP p₁ w₁ b₁ ihp ihw ihb =>
      intro t₂ h hν
      cases t₂ with
      | letP p₂ w₂ b₂ =>
          exact ⟨ihp h.1 (fun n hn => hν n (by simp [sealedFree, hn])),
            ihw h.2.1 (fun n hn => hν n (by simp [sealedFree, hn])),
            ihb h.2.2 (fun n hn => hν n (by simp [sealedFree, hn]))⟩
      | _ => exact h
  | alt t₁ u₁ ih₁ ih₂ =>
      intro t₂ h hν
      cases t₂ with
      | alt t₂ u₂ =>
          exact ⟨ih₁ h.1 (fun n hn => hν n (by simp [sealedFree, hn])),
            ih₂ h.2 (fun n hn => hν n (by simp [sealedFree, hn]))⟩
      | _ => exact h
  | ctx ks₁ c₁ _ =>
      intro t₂ h hν
      cases t₂ with
      | ctx ks₂ c₂ =>
          obtain ⟨hf, hks, hc⟩ := h
          obtain ⟨e₁, e₂⟩ := ctx_congr hf (ν' := ν')
            (fun n hn => hν n (by simpa [sealedFree] using hn))
          exact ⟨hf, hks.trans e₁, hc.trans e₂⟩
      | _ => exact h

/-- **The relation reads `ν` only on free names and on the hole copies of free
sealed code, and `μ` only on free parameters.** -/
theorem Rel.congr {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {ν' μ' : Nm X₁ → Nm X₂}, (∀ n ∈ freeNames t₁, ν n = ν' n) →
      (∀ n ∈ sealedFree t₁, (∃ s, n = .src s) ∨ ν n = ν' n) →
      (∀ x ∈ freeParams t₁, μ x = μ' x) → Rel C ν' μ' k Res ok t₁ t₂ := by
  induction h with
  | sym s => intro _ _ _ _ _; exact .sym s
  | fn F => intro _ _ _ _ _; exact .fn F
  | var n hv =>
      intro ν' μ' hν _ _
      have e := hν n (by simp [freeNames])
      have hv' : C.varHole n (ν' n) := by
        rw [← e]
        exact hv
      rw [e]
      exact .var n hv'
  | pvar x hp =>
      intro ν' μ' _ _ hμ
      have hp' : C.parOK x (μ' x) := by
        rw [← hμ x (by simp [freeParams])]
        exact hp
      rw [hμ x (by simp [freeParams])]
      exact .pvar x hp'
  | quote hq =>
      intro _ _ _ hs _
      exact .quote (hq.congr fun n hn => hs n (by simpa [sealedFree] using hn))
  | @ctx ν μ k ks₁ c₁ ks₂ c₂ hf hks hc =>
      intro ν' μ' _ hs _
      obtain ⟨e₁, e₂⟩ := ctx_congr hf (ν' := ν') fun n hn => hs n (by simpa [sealedFree] using hn)
      exact .ctx hf (hks.trans e₁) (hc.trans e₂)
  | pquote _ hp hok ih =>
      intro ν' μ' hν hs hμ
      exact .pquote (ih (fun n hn => hν n (by simpa [freeNames] using hn))
          (fun n hn => hs n (by simpa [sealedFree] using hn))
          (fun x hx => hμ x (by simpa [freeParams] using hx)))
        (hp.congr fun n hn => hs n (by simpa [sealedFree] using hn)) hok
  | app _ _ ihf iha =>
      intro ν' μ' hν hs hμ
      simp only [freeNames, sealedFree, freeParams, List.mem_append] at hν hs hμ
      exact .app (ihf (fun n h => hν n (Or.inl h)) (fun n h => hs n (Or.inl h))
          (fun x h => hμ x (Or.inl h)))
        (iha (fun n h => hν n (Or.inr h)) (fun n h => hs n (Or.inr h)) (fun x h => hμ x (Or.inr h)))
  | letP hk _ _ _ ihp ihw ihb =>
      intro ν' μ' hν hs hμ
      simp only [freeNames, sealedFree, freeParams, List.mem_append] at hν hs hμ
      exact .letP hk
        (ihp (fun n h => hν n (Or.inl (Or.inl h))) (fun n h => hs n (Or.inl (Or.inl h)))
          (fun x h => hμ x (Or.inl (Or.inl h))))
        (ihw (fun n h => hν n (Or.inl (Or.inr h))) (fun n h => hs n (Or.inl (Or.inr h)))
          (fun x h => hμ x (Or.inl (Or.inr h))))
        (ihb (fun n h => hν n (Or.inr h)) (fun n h => hs n (Or.inr h)) (fun x h => hμ x (Or.inr h)))
  | alt hk _ _ ih₁ ih₂ =>
      intro ν' μ' hν hs hμ
      simp only [freeNames, sealedFree, freeParams, List.mem_append] at hν hs hμ
      exact .alt hk (ih₁ (fun n h => hν n (Or.inl h)) (fun n h => hs n (Or.inl h))
          (fun x h => hμ x (Or.inl h)))
        (ih₂ (fun n h => hν n (Or.inr h)) (fun n h => hs n (Or.inr h)) (fun x h => hμ x (Or.inr h)))
  | @lam ν μ k x₁ own₁ b₁ x₂ own₂ b₂ νb μb Rb _ hνb hμb hμx hr₁ hr₂ _ hown hres hinj hdisj hnd hpar
      hbare hseen hsealO hsealK ihb =>
      intro ν' μ' hν hs hμ
      have hνf : ∀ n ∈ freeNames b₁,
          νb n = if ownKey own₁ n = true then νb n else ν' n := by
        intro n hn
        by_cases ho : ownKey own₁ n = true
        · simp [ho]
        · have ho' : ownKey own₁ n = false := by simpa using ho
          simp only [ho]
          rw [hνb n ho']
          exact hν n (mem_freeNames_lam.2 ⟨hn, ho'⟩)
      have hνs : ∀ n ∈ sealedFree b₁, (∃ s, n = .src s) ∨
          νb n = if ownKey own₁ n = true then νb n else ν' n := by
        intro n hn
        by_cases ho : ownKey own₁ n = true
        · exact Or.inr (by simp [ho])
        · have ho' : ownKey own₁ n = false := by simpa using ho
          simp only [ho]
          rw [hνb n ho']
          exact hs n (by simp [sealedFree, hn, ho'])
      have hμbb : ∀ x ∈ freeParams b₁,
          μb x = if x = x₁ then x₂ else μ' x := by
        intro x hx
        by_cases hxx : x = x₁
        · simp [hxx, hμx]
        · simp only [hxx, if_false]
          rw [hμb x hxx]
          exact hμ x (mem_freeParams_lam.2 ⟨hx, hxx⟩)
      refine .lam (νb := fun m => if ownKey own₁ m = true then νb m else ν' m)
        (μb := fun y => if y = x₁ then x₂ else μ' y) ?_ ?_ (by simp) hr₁ hr₂
        (ihb hνf hνs hμbb) ?_ hres ?_ ?_ hnd ?_ hbare hseen hsealO ?_
      · intro n hn
        simp [hn]
      · intro x hx
        simp [hx]
      · intro n hn
        rw [← hνf n hn]
        exact hown n hn
      · intro n hn n' hn' ho ho' he
        simp only [ho, ho', if_true] at he
        exact hinj n hn n' hn' ho ho' he
      · intro n hn ho
        simp only [ho, if_true]
        exact hdisj n hn ho
      · intro x hx hne
        rw [← hμ x (mem_freeParams_lam.2 ⟨hx, hne⟩)]
        exact hpar x hx hne
      · intro n hn ho
        simp only [ho, if_true]
        exact hsealK n hn ho
  | @letAct ν μ k ℓ own p₁ w₁ b₁ p₂ w₂ b₂ νi Rh Rw Rp Rb _ _ _ hk hνi hr hℓp hℓb _ _ _ hlive hinj
      ihw ihp ihb =>
      intro ν' μ' hν hs hμ
      have hνf : ∀ n ∈ freeNames p₁ ++ freeNames b₁,
          νi n = if ownKey own n = true then νi n else ν' n := by
        intro n hn
        by_cases ho : ownKey own n = true
        · simp [ho]
        · have ho' : ownKey own n = false := by simpa using ho
          simp only [ho]
          rw [hνi n ho']
          refine hν n ?_
          rcases List.mem_append.1 hn with hn | hn
          · exact mem_freeNames_letAct.2 (Or.inl ⟨Or.inl hn, ho'⟩)
          · exact mem_freeNames_letAct.2 (Or.inl ⟨Or.inr hn, ho'⟩)
      have hνs : ∀ n ∈ sealedFree p₁ ++ sealedFree b₁, (∃ s, n = .src s) ∨
          νi n = if ownKey own n = true then νi n else ν' n := by
        intro n hn
        by_cases ho : ownKey own n = true
        · exact Or.inr (by simp [ho])
        · have ho' : ownKey own n = false := by simpa using ho
          simp only [ho]
          rw [hνi n ho']
          refine hs n ?_
          rcases List.mem_append.1 hn with hn | hn <;> simp [sealedFree, hn, ho']
      have hμp : ∀ x ∈ freeParams p₁, μ x = μ' x := fun x hx =>
        hμ x (mem_freeParams_letAct.2 (Or.inl ⟨Or.inl hx, fun e => hℓp (e ▸ hx)⟩))
      have hμb' : ∀ x ∈ freeParams b₁, μ x = μ' x := fun x hx =>
        hμ x (mem_freeParams_letAct.2 (Or.inl ⟨Or.inr hx, fun e => hℓb (e ▸ hx)⟩))
      refine .letAct (νi := fun m => if ownKey own m = true then νi m else ν' m) hk ?_ hr hℓp hℓb
        (ihw (fun n h => hν n (mem_freeNames_letAct.2 (Or.inr h)))
          (fun n h => hs n (by simp [sealedFree, h]))
          (fun x h => hμ x (mem_freeParams_letAct.2 (Or.inr h))))
        (ihp (fun n h => hνf n (List.mem_append_left _ h)) (fun n h => hνs n (List.mem_append_left _ h))
          hμp)
        (ihb (fun n h => hνf n (List.mem_append_right _ h)) (fun n h => hνs n (List.mem_append_right _ h))
          hμb') ?_ ?_
      · intro n hn
        simp [hn]
      · intro n hn ho
        simp only [ho, if_true]
        exact hlive n hn ho
      · intro n hn n' hn' ho ho' he
        simp only [ho, ho', if_true] at he
        exact hinj n hn n' hn' ho ho' he
  | @newAct ν μ ℓ own b₁ b₂ νi Rh Rb _ hνi hr hℓ _ hlive hinj ihb =>
      intro ν' μ' hν hs hμ
      have hνf : ∀ n ∈ freeNames b₁,
          νi n = if ownKey own n = true then νi n else ν' n := by
        intro n hn
        by_cases ho : ownKey own n = true
        · simp [ho]
        · have ho' : ownKey own n = false := by simpa using ho
          simp only [ho]
          rw [hνi n ho']
          exact hν n (mem_freeNames_newAct.2 ⟨hn, ho'⟩)
      have hνs : ∀ n ∈ sealedFree b₁, (∃ s, n = .src s) ∨
          νi n = if ownKey own n = true then νi n else ν' n := by
        intro n hn
        by_cases ho : ownKey own n = true
        · exact Or.inr (by simp [ho])
        · have ho' : ownKey own n = false := by simpa using ho
          simp only [ho]
          rw [hνi n ho']
          exact hs n (by simp [sealedFree, hn, ho'])
      refine .newAct (νi := fun m => if ownKey own m = true then νi m else ν' m) ?_ hr hℓ
        (ihb hνf hνs (fun x hx => hμ x (mem_freeParams_newAct.2 ⟨hx, fun e => hℓ (e ▸ hx)⟩))) ?_ ?_
      · intro n hn
        simp [hn]
      · intro n hn ho
        simp only [ho, if_true]
        exact hlive n hn ho
      · intro n hn n' hn' ho ho' he
        simp only [ho, ho', if_true] at he
        exact hinj n hn n' hn' ho ho' he

/-- A relation transported to a map that agrees on the tracked names `D`, when the
free names lie in `D` and the sealed code is tracked by `D`. -/
theorem Rel.congr_on {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) {D : Set (Nm X₁)}
    (hfv : ∀ n ∈ freeNames t₁, n ∈ D)
    (hsv : ∀ n ∈ sealedFree t₁, n ∈ D ∨ ∃ s, n = .src s ∧ C.root₁ s)
    {ν' : Nm X₁ → Nm X₂} (hag : ∀ n ∈ D, ν' n = ν n) : Rel C ν' μ k Res ok t₁ t₂ :=
  h.congr (fun n hn => (hag n (hfv n hn)).symm)
    (fun n hn => (hsv n hn).elim (fun hD => Or.inr (hag n hD).symm) fun ⟨s, e, _⟩ => Or.inl ⟨s, e⟩)
    (fun _ _ => rfl)


/-! ## Where free names of a substituted term come from -/

section Track

variable {Y : Type v} [DecidableEq Y]

/-- A free name of a substituted term is a kept free name, or a free name of
what replaced a free name or a free parameter. -/
theorem mem_freeNames_subst' (t : Tm S Y) (θ φ : Sub S Y) (m : Nm Y)
    (hm : m ∈ freeNames (subst θ φ t)) :
    (m ∈ freeNames t ∧ θ m = none) ∨ (∃ n ∈ freeNames t, ∃ w, θ n = some w ∧ m ∈ freeNames w) ∨
      ∃ x ∈ freeParams t, ∃ w, φ x = some w ∧ m ∈ freeNames w := by
  let θ' : Sub S Y := fun n => if n ∈ freeNames t then θ n else none
  let φ' : Sub S Y := fun x => if x ∈ freeParams t then φ x else none
  have e : subst θ φ t = subst θ' φ' t :=
    subst_eq_of_agree t θ θ' φ φ' (fun n hn => by simp [θ', hn]) (fun x hx => by simp [φ', hx])
  rw [e] at hm
  rcases mem_freeNames_subst t θ' φ' m hm with ⟨h1, h2⟩ | ⟨n, w, hn, hw⟩ | ⟨x, w, hx, hw⟩
  · exact Or.inl ⟨h1, by simpa [θ', h1] using h2⟩
  · by_cases hnt : n ∈ freeNames t
    · exact Or.inr (Or.inl ⟨n, hnt, w, by simpa [θ', hnt] using hn, hw⟩)
    · simp [θ', hnt] at hn
  · by_cases hxt : x ∈ freeParams t
    · exact Or.inr (Or.inr ⟨x, hxt, w, by simpa [φ', hxt] using hx, hw⟩)
    · simp [φ', hxt] at hx

/-- The same for free parameters. -/
theorem mem_freeParams_subst' (t : Tm S Y) (θ φ : Sub S Y) (q : Nm Y)
    (hq : q ∈ freeParams (subst θ φ t)) :
    (q ∈ freeParams t ∧ φ q = none) ∨ (∃ n ∈ freeNames t, ∃ w, θ n = some w ∧ q ∈ freeParams w) ∨
      ∃ x ∈ freeParams t, ∃ w, φ x = some w ∧ q ∈ freeParams w := by
  let θ' : Sub S Y := fun n => if n ∈ freeNames t then θ n else none
  let φ' : Sub S Y := fun x => if x ∈ freeParams t then φ x else none
  have e : subst θ φ t = subst θ' φ' t :=
    subst_eq_of_agree t θ θ' φ φ' (fun n hn => by simp [θ', hn]) (fun x hx => by simp [φ', hx])
  rw [e] at hq
  rcases mem_freeParams_subst t θ' φ' q hq with ⟨h1, h2⟩ | ⟨n, w, hn, hw⟩ | ⟨x, w, hx, hw⟩
  · exact Or.inl ⟨h1, by simpa [φ', h1] using h2⟩
  · by_cases hnt : n ∈ freeNames t
    · exact Or.inr (Or.inl ⟨n, hnt, w, by simpa [θ', hnt] using hn, hw⟩)
    · simp [θ', hnt] at hn
  · by_cases hxt : x ∈ freeParams t
    · exact Or.inr (Or.inr ⟨x, hxt, w, by simpa [φ', hxt] using hx, hw⟩)
    · simp [φ', hxt] at hx

/-- Where the free sealed names of a substituted term come from: substitution never
enters sealed code, so they are the term's own, or those of an inserted value. -/
theorem mem_sealedFree_subst : ∀ (t : Tm S Y) (θ φ : Sub S Y) (m : Nm Y),
    m ∈ sealedFree (subst θ φ t) →
      m ∈ sealedFree t ∨ (∃ n ∈ freeNames t, ∃ w, θ n = some w ∧ m ∈ sealedFree w) ∨
        ∃ x ∈ freeParams t, ∃ w, φ x = some w ∧ m ∈ sealedFree w
  | .sym _, _, _, _, h | .fn _, _, _, _, h => by simp [subst, sealedFree] at h
  | .quote _, _, _, _, h => Or.inl h
  | .ctx _ _, _, _, _, h => Or.inl h
  | .var n, θ, _, m, h => by
      cases hn : θ n with
      | none => simp [subst, hn, sealedFree] at h
      | some w =>
          simp only [subst, hn, Option.getD_some] at h
          exact Or.inr (Or.inl ⟨n, by simp [freeNames], w, hn, h⟩)
  | .pvar x, _, φ, m, h => by
      cases hx : φ x with
      | none => simp [subst, hx, sealedFree] at h
      | some w =>
          simp only [subst, hx, Option.getD_some] at h
          exact Or.inr (Or.inr ⟨x, by simp [freeParams], w, hx, h⟩)
  | .lam x own b, θ, φ, m, h => by
      simp only [subst, sealedFree, List.mem_filter] at h
      obtain ⟨hm, ho⟩ := h
      rcases mem_sealedFree_subst b _ _ m hm with hb | ⟨n, hn, w, hw, hmw⟩ | ⟨y, hy, w, hw, hmw⟩
      · exact Or.inl (by simp [sealedFree, hb, ho])
      · have hno : ownKey own n = false := by
          cases hk : ownKey own n
          · rfl
          · simp [Sub.hideOwn, hk] at hw
        simp only [Sub.hideOwn, hno, Bool.false_eq_true, if_false] at hw
        exact Or.inr (Or.inl ⟨n, by simp [freeNames, hn, hno], w, hw, hmw⟩)
      · have hyx : y ≠ x := by
          rintro rfl
          simp [Sub.hideParam] at hw
        simp only [Sub.hideParam, hyx, if_false] at hw
        exact Or.inr (Or.inr ⟨y, by simp [freeParams, hy, hyx], w, hw, hmw⟩)
  | .app f a, θ, φ, m, h => by
      simp only [subst, sealedFree, List.mem_append] at h
      rcases h with h | h
      · rcases mem_sealedFree_subst f θ φ m h with h | ⟨n, hn, h⟩ | ⟨x, hx, h⟩
        · exact Or.inl (by simp [sealedFree, h])
        · exact Or.inr (Or.inl ⟨n, by simp [freeNames, hn], h⟩)
        · exact Or.inr (Or.inr ⟨x, by simp [freeParams, hx], h⟩)
      · rcases mem_sealedFree_subst a θ φ m h with h | ⟨n, hn, h⟩ | ⟨x, hx, h⟩
        · exact Or.inl (by simp [sealedFree, h])
        · exact Or.inr (Or.inl ⟨n, by simp [freeNames, hn], h⟩)
        · exact Or.inr (Or.inr ⟨x, by simp [freeParams, hx], h⟩)
  | .pquote c, θ, φ, m, h => by
      simp only [subst, sealedFree] at h
      rcases mem_sealedFree_subst c θ φ m h with h | ⟨n, hn, h⟩ | ⟨x, hx, h⟩
      · exact Or.inl (by simpa [sealedFree] using h)
      · exact Or.inr (Or.inl ⟨n, by simpa [freeNames] using hn, h⟩)
      · exact Or.inr (Or.inr ⟨x, by simpa [freeParams] using hx, h⟩)
  | .letP p w b, θ, φ, m, h => by
      simp only [subst, sealedFree, List.mem_append] at h
      rcases h with (h | h) | h
      · rcases mem_sealedFree_subst p θ φ m h with h | ⟨n, hn, h⟩ | ⟨x, hx, h⟩
        · exact Or.inl (by simp [sealedFree, h])
        · exact Or.inr (Or.inl ⟨n, by simp [freeNames, hn], h⟩)
        · exact Or.inr (Or.inr ⟨x, by simp [freeParams, hx], h⟩)
      · rcases mem_sealedFree_subst w θ φ m h with h | ⟨n, hn, h⟩ | ⟨x, hx, h⟩
        · exact Or.inl (by simp [sealedFree, h])
        · exact Or.inr (Or.inl ⟨n, by simp [freeNames, hn], h⟩)
        · exact Or.inr (Or.inr ⟨x, by simp [freeParams, hx], h⟩)
      · rcases mem_sealedFree_subst b θ φ m h with h | ⟨n, hn, h⟩ | ⟨x, hx, h⟩
        · exact Or.inl (by simp [sealedFree, h])
        · exact Or.inr (Or.inl ⟨n, by simp [freeNames, hn], h⟩)
        · exact Or.inr (Or.inr ⟨x, by simp [freeParams, hx], h⟩)
  | .alt t₁ t₂, θ, φ, m, h => by
      simp only [subst, sealedFree, List.mem_append] at h
      rcases h with h | h
      · rcases mem_sealedFree_subst t₁ θ φ m h with h | ⟨n, hn, h⟩ | ⟨x, hx, h⟩
        · exact Or.inl (by simp [sealedFree, h])
        · exact Or.inr (Or.inl ⟨n, by simp [freeNames, hn], h⟩)
        · exact Or.inr (Or.inr ⟨x, by simp [freeParams, hx], h⟩)
      · rcases mem_sealedFree_subst t₂ θ φ m h with h | ⟨n, hn, h⟩ | ⟨x, hx, h⟩
        · exact Or.inl (by simp [sealedFree, h])
        · exact Or.inr (Or.inl ⟨n, by simp [freeNames, hn], h⟩)
        · exact Or.inr (Or.inr ⟨x, by simp [freeParams, hx], h⟩)

end Track

/-! ## Free sealed names are hole names -/

/-- **A free name of the sealed code of a related term is a hole name**: a hole
base as written, or the copy of one. -/
theorem Rel.sealedFree_holeName {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ n ∈ sealedFree t₁, holeName C n := by
  induction h with
  | sym _ | fn _ | var _ _ | pvar _ _ => intro n hn; simp [sealedFree] at hn
  | quote hq => intro n hn; exact hq.2.1.2.1 n hn
  | ctx hf _ _ => intro n hn; exact hf.2.1 n hn
  | pquote _ _ _ ih => intro n hn; exact ih n hn
  | app _ _ ihf iha =>
      intro n hn
      simp only [sealedFree, List.mem_append] at hn
      exact hn.elim (ihf n) (iha n)
  | letP _ _ _ _ ihp ihw ihb =>
      intro n hn
      simp only [sealedFree, List.mem_append] at hn
      rcases hn with (hn | hn) | hn
      · exact ihp n hn
      · exact ihw n hn
      · exact ihb n hn
  | alt _ _ _ ih₁ ih₂ =>
      intro n hn
      simp only [sealedFree, List.mem_append] at hn
      exact hn.elim (ih₁ n) (ih₂ n)
  | lam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihb =>
      intro n hn
      simp only [sealedFree, List.mem_filter] at hn
      exact ihb n hn.1
  | letAct _ _ _ _ _ _ _ _ _ _ ihw ihp ihb =>
      intro n hn
      simp only [sealedFree, List.mem_append, List.mem_filter] at hn
      rcases hn with ⟨(hn | hn) | hn, -⟩ | hn
      · exact ihp n hn
      · simp at hn
      · exact ihb n hn
      · exact ihw n hn
  | newAct _ _ _ _ _ _ ihb =>
      intro n hn
      simp only [sealedFree, List.mem_append, List.mem_filter] at hn
      rcases hn with ⟨hn, -⟩ | ⟨hn, -⟩
      · exact ihb n hn
      · simp at hn

omit [DecidableEq X₂] in
/-- A hole name is owned by no list of names that are not hole bases. -/
theorem ownKey_of_holeName {own : List X₁} (hr : ∀ s ∈ own, ¬ C.hole s) :
    ∀ {n : Nm X₁}, holeName C n → ownKey own n = false
  | .src s, h => by
      simp only [ownKey, List.contains_eq_mem, decide_eq_false_iff_not]
      exact fun hs => hr s hs h
  | .inst _ _, _ => rfl

/-! ## Inversion -/

theorem Rel.var_left {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {n : Nm X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok (.var n) t₂) : t₂ = .var (ν n) := by
  cases h
  rfl

theorem Rel.pvar_left {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {x : Nm X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok (.pvar x) t₂) : t₂ = .pvar (μ x) := by
  cases h
  rfl

/-! ## Substitution -/

/-- **Related substitutions** on a term: each free name or parameter is kept,
or replaced, by related values; reserved names are renamed along `rn`,
injectively; whatever is inserted has free names that may occur free and no
free parameter. -/
structure SubOK (C : Setting S X₁ X₂) (ν μ : Nm X₁ → Nm X₂) (Res : List (Nm X₂))
    (t₁ : Tm S X₁) (θ₁ φ₁ : Sub S X₁) (θ₂ φ₂ : Sub S X₂) (ν' μ' : Nm X₁ → Nm X₂)
    (rn : Nm X₂ → Nm X₂) : Prop where
  names : ∀ n ∈ freeNames t₁,
    Rel C ν' μ' .val [] true ((θ₁ n).getD (.var n)) ((θ₂ (ν n)).getD (.var (ν n)))
  params : ∀ x ∈ freeParams t₁,
    Rel C ν' μ' .val [] true ((φ₁ x).getD (.pvar x)) ((φ₂ (μ x)).getD (.pvar (μ x)))
  res : ∀ m ∈ Res, (θ₂ m).getD (.var m) = .var (rn m)
  resInj : ∀ m ∈ Res, ∀ m' ∈ Res, rn m = rn m' → m = m'
  /-- `rn` keeps hole comparisons. -/
  rnPres : ∀ m, C.preserve m (rn m)
  cap₁ : ∀ n ∈ freeNames t₁, ∀ w, θ₁ n = some w →
    (∀ m ∈ freeNames w, OK₁ C m) ∧ freeParams w = []
  capφ₁ : ∀ x ∈ freeParams t₁, ∀ w, φ₁ x = some w →
    (∀ m ∈ freeNames w, OK₁ C m) ∧ freeParams w = []
  cap₂ : ∀ n ∈ freeNames t₁, ∀ w, θ₂ (ν n) = some w →
    (∀ m ∈ freeNames w, OK₂ C m) ∧ freeParams w = []
  capφ₂ : ∀ x ∈ freeParams t₁, ∀ w, φ₂ (μ x) = some w →
    (∀ m ∈ freeNames w, OK₂ C m) ∧ freeParams w = []
  capR : ∀ m ∈ Res, ∀ w, θ₂ m = some w → (∀ m' ∈ freeNames w, OK₂ C m') ∧ freeParams w = []
  /-- The sealed code the substitution keeps is read alike: its hole copies keep
  their images. -/
  sealed : ∀ n ∈ sealedFree t₁, (∃ s, n = .src s) ∨ ν' n = ν n
  /-- What is inserted for a name has free sealed names that may occur free. -/
  sealCap₁ : ∀ n ∈ freeNames t₁, ∀ w, θ₁ n = some w → ∀ m ∈ sealedFree w, OK₁ C m
  /-- The same for a parameter. -/
  sealCapφ₁ : ∀ x ∈ freeParams t₁, ∀ w, φ₁ x = some w → ∀ m ∈ sealedFree w, OK₁ C m

theorem SubOK.restrict {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂}
    (h : SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn) {Res' : List (Nm X₂)} {u : Tm S X₁}
    (hn : ∀ n ∈ freeNames u, n ∈ freeNames t₁) (hx : ∀ x ∈ freeParams u, x ∈ freeParams t₁)
    (hR : ∀ m ∈ Res', m ∈ Res) (hs : ∀ n ∈ sealedFree u, n ∈ sealedFree t₁) :
    SubOK C ν μ Res' u θ₁ φ₁ θ₂ φ₂ ν' μ' rn where
  names n h' := h.names n (hn n h')
  params x h' := h.params x (hx x h')
  res m h' := h.res m (hR m h')
  resInj m h' m' h'' := h.resInj m (hR m h') m' (hR m' h'')
  rnPres := h.rnPres
  cap₁ n h' := h.cap₁ n (hn n h')
  capφ₁ x h' := h.capφ₁ x (hx x h')
  cap₂ n h' := h.cap₂ n (hn n h')
  capφ₂ x h' := h.capφ₂ x (hx x h')
  capR m h' := h.capR m (hR m h')
  sealed n h' := h.sealed n (hs n h')
  sealCap₁ n h' := h.sealCap₁ n (hn n h')
  sealCapφ₁ x h' := h.sealCapφ₁ x (hx x h')

/-- The replacement of a free name, if any, carries only names that may occur
free; the name itself is kept otherwise. -/
theorem SubOK.replacement_names {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂}
    (h : SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn) {n : Nm X₁} (hn : n ∈ freeNames t₁)
    {m : Nm X₁} (hm : m ∈ freeNames ((θ₁ n).getD (.var n))) :
    (θ₁ n = none ∧ m = n) ∨ OK₁ C m := by
  cases hθ : θ₁ n with
  | none =>
      rw [hθ] at hm
      simp only [Option.getD_none, freeNames, List.mem_singleton] at hm
      exact Or.inl ⟨rfl, hm⟩
  | some w =>
      rw [hθ] at hm
      exact Or.inr ((h.cap₁ n hn w hθ).1 m hm)

theorem SubOK.replacement_params {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂}
    (h : SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn) {n : Nm X₁} (hn : n ∈ freeNames t₁) :
    freeParams ((θ₁ n).getD (.var n)) = [] := by
  cases hθ : θ₁ n with
  | none => rfl
  | some w => exact (h.cap₁ n hn w hθ).2

theorem SubOK.param_names {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂}
    (h : SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn) {x : Nm X₁} (hx : x ∈ freeParams t₁)
    {m : Nm X₁} (hm : m ∈ freeNames ((φ₁ x).getD (.pvar x))) : OK₁ C m := by
  cases hφ : φ₁ x with
  | none =>
      rw [hφ] at hm
      simp [freeNames] at hm
  | some w =>
      rw [hφ] at hm
      exact (h.capφ₁ x hx w hφ).1 m hm

theorem SubOK.param_params {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂}
    (h : SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn) {x : Nm X₁} (hx : x ∈ freeParams t₁)
    {y : Nm X₁} (hy : y ∈ freeParams ((φ₁ x).getD (.pvar x))) : φ₁ x = none ∧ y = x := by
  cases hφ : φ₁ x with
  | none =>
      rw [hφ] at hy
      simp only [Option.getD_none, freeParams, List.mem_singleton] at hy
      exact ⟨rfl, hy⟩
  | some w =>
      rw [hφ, Option.getD_some, (h.capφ₁ x hx w hφ).2] at hy
      cases hy

/-- The identity image of a name the first side keeps is one the second side
may not capture, unless it is the kept image itself. -/
theorem SubOK.kept_image {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂}
    (h : SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn) {n : Nm X₁} (hn : n ∈ freeNames t₁)
    (hθ : θ₁ n = none) : (θ₂ (ν n) = none ∧ ν' n = ν n) ∨ OK₂ C (ν' n) := by
  have hr := h.names n hn
  rw [hθ, Option.getD_none] at hr
  have e := hr.var_left
  cases h2 : θ₂ (ν n) with
  | none =>
      rw [h2, Option.getD_none] at e
      exact Or.inl ⟨rfl, (Tm.var.inj e).symm⟩
  | some w =>
      rw [h2, Option.getD_some] at e
      subst e
      exact Or.inr ((h.cap₂ n hn _ h2).1 (ν' n) (by simp [freeNames]))

/-- A free name inserted by the first side has an image the second side may
not capture: it comes from the second side's replacement, or is the kept
image of the replaced name. -/
theorem SubOK.inserted_image {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂}
    (h : SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn) {n : Nm X₁} (hn : n ∈ freeNames t₁)
    {w : Tm S X₁} (hθ : θ₁ n = some w) {m : Nm X₁} (hm : m ∈ freeNames w) :
    OK₂ C (ν' m) ∨ (θ₂ (ν n) = none ∧ ν' m = ν n) := by
  have hr := h.names n hn
  rw [hθ, Option.getD_some] at hr
  have hm' := hr.mem_freeNames hm
  cases h2 : θ₂ (ν n) with
  | none =>
      rw [h2, Option.getD_none] at hm'
      simp only [freeNames, List.mem_singleton] at hm'
      exact Or.inr ⟨rfl, hm'⟩
  | some w₂ =>
      rw [h2, Option.getD_some] at hm'
      exact Or.inl ((h.cap₂ n hn w₂ h2).1 _ hm')

/-- The same for a free name inserted for a parameter. -/
theorem SubOK.inserted_param_image {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂}
    (h : SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn) {x : Nm X₁} (hx : x ∈ freeParams t₁)
    {w : Tm S X₁} (hφ : φ₁ x = some w) {m : Nm X₁} (hm : m ∈ freeNames w) : OK₂ C (ν' m) := by
  have hr := h.params x hx
  rw [hφ, Option.getD_some] at hr
  have hm' := hr.mem_freeNames hm
  cases h2 : φ₂ (μ x) with
  | none =>
      rw [h2, Option.getD_none] at hm'
      simp [freeNames] at hm'
  | some w₂ =>
      rw [h2, Option.getD_some] at hm'
      exact (h.capφ₂ x hx w₂ h2).1 _ hm'


/-! ## Holes, parameters, and weak shape -/

/-- A free store name and its image are related by `varHole`. -/
theorem Rel.varHole_free {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {n}, n ∈ freeNames t₁ → C.varHole n (ν n) := by
  induction h with
  | sym _ => intro n hn; simp [freeNames] at hn
  | fn _ => intro n hn; simp [freeNames] at hn
  | var m hv =>
      intro n hn
      simp only [freeNames, List.mem_singleton] at hn
      subst hn
      exact hv
  | pvar _ _ => intro n hn; simp [freeNames] at hn
  | quote _ => intro n hn; simp [freeNames] at hn
  | ctx _ _ _ => intro n hn; simp [freeNames] at hn
  | pquote _ _ _ ih =>
      intro n hn
      simp only [freeNames] at hn
      exact ih hn
  | app _ _ ihf iha =>
      intro n hn
      simp only [freeNames, List.mem_append] at hn
      exact hn.elim ihf iha
  | letP _ _ _ _ ihp ihw ihb =>
      intro n hn
      simp only [freeNames, List.mem_append] at hn
      rcases hn with (hn | hn) | hn
      · exact ihp hn
      · exact ihw hn
      · exact ihb hn
  | alt _ _ _ ih₁ ih₂ =>
      intro n hn
      simp only [freeNames, List.mem_append] at hn
      exact hn.elim ih₁ ih₂
  | lam hνb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihb =>
      intro n hn
      rw [mem_freeNames_lam] at hn
      obtain ⟨hn, hk⟩ := hn
      exact hνb n hk ▸ ihb hn
  | letAct _ hνi _ _ _ _ _ _ _ _ ihw ihp ihb =>
      intro n hn
      simp only [freeNames, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.not_mem_nil, or_false] at hn
      rcases hn with ⟨hn | hn, hk⟩ | hn
      · exact hνi n hk ▸ ihp hn
      · exact hνi n hk ▸ ihb hn
      · exact ihw hn
  | newAct hνi _ _ _ _ _ ihb =>
      intro n hn
      simp only [freeNames, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.not_mem_nil] at hn
      rcases hn with ⟨hn, hk⟩ | ⟨hf, _⟩
      · exact hνi n hk ▸ ihb hn
      · exact hf.elim

/-- A free parameter and its image are related by `parOK`. -/
theorem Rel.parOK_free {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {x}, x ∈ freeParams t₁ → C.parOK x (μ x) := by
  induction h with
  | sym _ => intro x hx; simp [freeParams] at hx
  | fn _ => intro x hx; simp [freeParams] at hx
  | var _ _ => intro x hx; simp [freeParams] at hx
  | pvar y hp =>
      intro x hx
      simp only [freeParams, List.mem_singleton] at hx
      subst hx
      exact hp
  | quote _ => intro x hx; simp [freeParams] at hx
  | ctx _ _ _ => intro x hx; simp [freeParams] at hx
  | pquote _ _ _ ih =>
      intro x hx
      simp only [freeParams] at hx
      exact ih hx
  | app _ _ ihf iha =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx
      exact hx.elim ihf iha
  | letP _ _ _ _ ihp ihw ihb =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact ihp hx
      · exact ihw hx
      · exact ihb hx
  | alt _ _ _ ih₁ ih₂ =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx
      exact hx.elim ih₁ ih₂
  | lam _ hμb _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihb =>
      intro x hx
      rw [mem_freeParams_lam] at hx
      obtain ⟨hx, hne⟩ := hx
      exact hμb x hne ▸ ihb hx
  | letAct _ _ _ _ _ _ _ _ _ _ ihw ihp ihb =>
      intro x hx
      simp only [freeParams, List.mem_append, List.mem_filter, decide_eq_true_eq,
        List.mem_singleton] at hx
      rcases hx with ⟨(hx | hx) | hx, hne⟩ | hx
      · exact ihp hx
      · exact absurd hx hne
      · exact ihb hx
      · exact ihw hx
  | newAct _ _ _ _ _ _ ihb =>
      intro x hx
      simp only [freeParams, List.mem_append, List.mem_filter, decide_eq_true_eq,
        List.mem_singleton] at hx
      rcases hx with ⟨hx, _⟩ | ⟨hx, hne⟩
      · exact ihb hx
      · exact absurd hx hne

/-- A value carries no pending activation. -/
theorem Rel.val_ok {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ .val Res ok t₁ t₂) : ok = true := by
  generalize hk : Kd.val = k at h
  induction h with
  | sym _ => rfl
  | fn _ => rfl
  | var _ _ => rfl
  | pvar _ _ => rfl
  | quote _ => rfl
  | ctx _ _ _ => rfl
  | pquote _ _ _ => rfl
  | app _ _ ihf iha =>
      rw [ihf hk, iha hk]
      rfl
  | letP hk' => exact absurd hk.symm hk'
  | alt hk' => exact absurd hk.symm hk'
  | lam => rfl
  | letAct hk' => exact absurd hk.symm hk'
  | newAct => cases hk

/-- Stable related terms have the same weak shape. -/
theorem Rel.shape_of {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ok = true → ShapeParallel C ν t₁ t₂ := by
  induction h with
  | sym _ => intro _; rfl
  | fn _ => intro _; rfl
  | var _ hv => intro _; exact hv
  | pvar _ hp => intro _; exact hp
  | quote hq => intro _; exact hq
  | ctx hf hks hc => intro _; exact ⟨hf, hks, hc⟩
  | pquote _ hp _ => intro _; exact hp
  | app _ _ ihf iha =>
      intro hok
      simp only [Bool.and_eq_true] at hok
      exact ⟨ihf hok.1, iha hok.2⟩
  | letP _ _ _ _ ihp ihw ihb =>
      intro hok
      simp only [Bool.and_eq_true] at hok
      obtain ⟨⟨hop, how⟩, hob⟩ := hok
      exact ⟨ihp hop, ihw how, ihb hob⟩
  | alt _ _ _ ih₁ ih₂ =>
      intro hok
      simp only [Bool.and_eq_true] at hok
      exact ⟨ih₁ hok.1, ih₂ hok.2⟩
  | lam _ _ _ _ _ _ _ _ _ _ _ _ hbare _ =>
      intro _
      exact hbare
  | letAct =>
      intro hok
      cases hok
  | newAct =>
      intro hok
      cases hok

/-- A related value has the weak shape of its two terms. -/
theorem Rel.shape_of_val {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ .val Res true t₁ t₂) :
    ShapeParallel C ν t₁ t₂ :=
  h.shape_of rfl

/-- Weak shape survives substitution. A pending activation is not stable, so it
is excluded; a lambda contributes its binders only. -/
theorem Rel.shape_preserved {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂},
      SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn → ok = true →
        ShapeParallel C ν' (subst θ₁ φ₁ t₁) (subst θ₂ φ₂ t₂) := by
  induction h with
  | sym _ =>
      intro _ _ _ _ _ _ _ _ _
      simp only [subst, ShapeParallel]
  | fn _ =>
      intro _ _ _ _ _ _ _ _ _
      simp only [subst, ShapeParallel]
  | var n _ =>
      intro _ _ _ _ _ _ _ hS _
      simpa [subst] using (hS.names n (by simp [freeNames])).shape_of_val
  | pvar x _ =>
      intro _ _ _ _ _ _ _ hS _
      simpa [subst] using (hS.params x (by simp [freeParams])).shape_of_val
  | quote hq =>
      intro _ _ _ _ _ _ _ hS _
      simp only [subst, ShapeParallel]
      exact hq.congr (fun n hn => (hS.sealed n (by simpa [sealedFree] using hn)).imp_right Eq.symm)
  | ctx hf hks hc =>
      intro _ _ _ _ ν' _ _ hS _
      simp only [subst, ShapeParallel]
      obtain ⟨e₁, e₂⟩ := ctx_congr hf (ν' := ν')
        (fun n hn => (hS.sealed n (by simpa [sealedFree] using hn)).imp_right Eq.symm)
      exact ⟨hf, hks.trans e₁, hc.trans e₂⟩
  | pquote _ _ hbok ih =>
      intro _ _ _ _ _ _ _ hS _
      simp only [subst, ShapeParallel]
      exact ih (hS.restrict (fun n h => by simp [freeNames, h])
        (fun x h => by simp [freeParams, h]) (fun _ h => by cases h) (fun n h => by simp [sealedFree, h])) hbok
  | app _ _ ihf iha =>
      intro _ _ _ _ _ _ _ hS hok
      simp only [Bool.and_eq_true] at hok
      simp only [subst, ShapeParallel]
      exact ⟨ihf (hS.restrict (fun n h => by simp [freeNames, h])
            (fun x h => by simp [freeParams, h])
            (fun m h => List.mem_append_left _ h) (fun n h => by simp [sealedFree, h])) hok.1,
          iha (hS.restrict (fun n h => by simp [freeNames, h])
            (fun x h => by simp [freeParams, h])
            (fun m h => List.mem_append_right _ h) (fun n h => by simp [sealedFree, h])) hok.2⟩
  | letP _ _ _ _ ihp ihw ihb =>
      intro _ _ _ _ _ _ _ hS hok
      simp only [Bool.and_eq_true] at hok
      obtain ⟨⟨hop, how⟩, hob⟩ := hok
      simp only [subst, ShapeParallel]
      exact ⟨ihp (hS.restrict (fun n h => by simp [freeNames, h])
            (fun x h => by simp [freeParams, h]) (fun m h => by simp [h]) (fun n h => by simp [sealedFree, h])) hop,
          ihw (hS.restrict (fun n h => by simp [freeNames, h])
            (fun x h => by simp [freeParams, h]) (fun m h => by simp [h]) (fun n h => by simp [sealedFree, h])) how,
          ihb (hS.restrict (fun n h => by simp [freeNames, h])
            (fun x h => by simp [freeParams, h]) (fun m h => by simp [h]) (fun n h => by simp [sealedFree, h])) hob⟩
  | alt _ _ _ ih₁ ih₂ =>
      intro _ _ _ _ _ _ _ hS hok
      simp only [Bool.and_eq_true] at hok
      simp only [subst, ShapeParallel]
      exact ⟨ih₁ (hS.restrict (fun n h => by simp [freeNames, h])
            (fun x h => by simp [freeParams, h])
            (fun m h => List.mem_append_left _ h) (fun n h => by simp [sealedFree, h])) hok.1,
          ih₂ (hS.restrict (fun n h => by simp [freeNames, h])
            (fun x h => by simp [freeParams, h])
            (fun m h => List.mem_append_right _ h) (fun n h => by simp [sealedFree, h])) hok.2⟩
  | lam _ _ _ _ _ _ _ _ _ _ _ _ hbare _ =>
      intro _ _ _ _ _ _ _ _ _
      simp only [subst, ShapeParallel]
      exact hbare
  | letAct =>
      intro _ _ _ _ _ _ _ _ hok
      cases hok
  | newAct =>
      intro _ _ _ _ _ _ _ _ hok
      cases hok

/-- **Substitution preserves the relation.**  Renaming slots on one side or on
both, instantiating parameters, substituting values for store names and
applying a store are instances. The stability bit is unchanged: a replacement
is a value, and a value is stable. -/
theorem Rel.substitute {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂},
      SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn →
      Rel C ν' μ' k (Res.map rn) ok (subst θ₁ φ₁ t₁) (subst θ₂ φ₂ t₂) := by
  induction h with
  | sym s => intro _ _ _ _ _ _ _ _; exact .sym s
  | fn F => intro _ _ _ _ _ _ _ _; exact .fn F
  | var n _ =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      exact (hS.names n (by simp [freeNames])).of_val _
  | pvar x _ =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      exact (hS.params x (by simp [freeParams])).of_val _
  | quote hq =>
      intro _ _ _ _ _ _ _ hS
      exact .quote (hq.congr (fun n hn =>
        (hS.sealed n (by simpa [sealedFree] using hn)).imp_right Eq.symm))
  | ctx hf hks hc =>
      intro _ _ _ _ ν' _ _ hS
      obtain ⟨e₁, e₂⟩ := ctx_congr hf (ν' := ν')
        (fun n hn => (hS.sealed n (by simpa [sealedFree] using hn)).imp_right Eq.symm)
      exact .ctx hf (hks.trans e₁) (hc.trans e₂)
  | pquote hb _ hok ih =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      simp only [subst, List.map_nil]
      exact .pquote
        (ih (hS.restrict (fun n h => by simp [freeNames, h])
          (fun x h => by simp [freeParams, h]) (fun _ hm => hm) (fun n h => by simp [sealedFree, h])))
        (hb.shape_preserved (hS.restrict (fun n h => by simp [freeNames, h])
          (fun x h => by simp [freeParams, h]) (fun _ hm => hm) (fun n h => by simp [sealedFree, h])) hok)
        hok
  | app _ _ ihf iha =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      rw [List.map_append]
      exact .app
        (ihf (hS.restrict (fun n h => by simp [freeNames, h]) (fun x h => by simp [freeParams, h])
          (fun m h => List.mem_append_left _ h) (fun n h => by simp [sealedFree, h])))
        (iha (hS.restrict (fun n h => by simp [freeNames, h]) (fun x h => by simp [freeParams, h])
          (fun m h => List.mem_append_right _ h) (fun n h => by simp [sealedFree, h])))
  | letP hk _ _ _ ihp ihw ihb =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      rw [List.map_append, List.map_append]
      exact .letP hk
        (ihp (hS.restrict (fun n h => by simp [freeNames, h]) (fun x h => by simp [freeParams, h])
          (fun m h => by simp [h]) (fun n h => by simp [sealedFree, h])))
        (ihw (hS.restrict (fun n h => by simp [freeNames, h]) (fun x h => by simp [freeParams, h])
          (fun m h => by simp [h]) (fun n h => by simp [sealedFree, h])))
        (ihb (hS.restrict (fun n h => by simp [freeNames, h]) (fun x h => by simp [freeParams, h])
          (fun m h => by simp [h]) (fun n h => by simp [sealedFree, h])))
  | alt hk _ _ ih₁ ih₂ =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      rw [List.map_append]
      exact .alt hk
        (ih₁ (hS.restrict (fun n h => by simp [freeNames, h]) (fun x h => by simp [freeParams, h])
          (fun m h => List.mem_append_left _ h) (fun n h => by simp [sealedFree, h])))
        (ih₂ (hS.restrict (fun n h => by simp [freeNames, h]) (fun x h => by simp [freeParams, h])
          (fun m h => List.mem_append_right _ h) (fun n h => by simp [sealedFree, h])))
  | @lam ν μ k x₁ own₁ b₁ x₂ own₂ b₂ νb μb Rb _ hνb hμb hμx hr₁ hr₂ hb hown hres hinj hdisj hnd hpar
      hbare hseen hsealO hsealK ihb =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      simp only [subst, List.map_nil]
      let νb' : Nm X₁ → Nm X₂ := fun m => if ownKey own₁ m = true then νb m else ν' m
      let μb' : Nm X₁ → Nm X₂ := fun y => if y = x₁ then x₂ else μ' y
      have hνb'o : ∀ m, ownKey own₁ m = true → νb' m = νb m := fun m h => by simp [νb', h]
      have hνb'n : ∀ m, ownKey own₁ m = false → νb' m = ν' m := fun m h => by simp [νb', h]
      have hμb'x : μb' x₁ = x₂ := by simp [μb']
      have hμb'n : ∀ y, y ≠ x₁ → μb' y = μ' y := fun y h => by simp [μb', h]
      have hfv : ∀ n, n ∈ freeNames b₁ → ownKey own₁ n = false →
          n ∈ freeNames (.lam x₁ own₁ b₁ : Tm S X₁) := fun n hn ho => mem_freeNames_lam.2 ⟨hn, ho⟩
      have hfp : ∀ x, x ∈ freeParams b₁ → x ≠ x₁ →
          x ∈ freeParams (.lam x₁ own₁ b₁ : Tm S X₁) := fun x hx hne => mem_freeParams_lam.2 ⟨hx, hne⟩
      have hcongN : ∀ n ∈ freeNames b₁, ∀ (ho : ownKey own₁ n = false),
          Rel C νb' μb' .val [] true ((θ₁ n).getD (.var n)) ((θ₂ (ν n)).getD (.var (ν n))) := by
        intro n hn ho
        refine (hS.names n (hfv n hn ho)).congr ?_ ?_ ?_
        · intro m hm
          rcases hS.replacement_names (hfv n hn ho) hm with ⟨_, rfl⟩ | hok
          · exact (hνb'n m ho).symm
          · exact (hνb'n m (ownKey_of_OK₁ hr₁ hok)).symm
        · intro m hm
          refine Or.inr ?_
          cases hθ : θ₁ n with
          | none => rw [hθ] at hm; simp [sealedFree] at hm
          | some w =>
              rw [hθ, Option.getD_some] at hm
              exact (hνb'n m (ownKey_of_OK₁ hr₁ (hS.sealCap₁ n (hfv n hn ho) w hθ m hm))).symm
        · intro y hy
          rw [hS.replacement_params (hfv n hn ho)] at hy
          cases hy
      have hcongP : ∀ x ∈ freeParams b₁, ∀ (hne : x ≠ x₁),
          Rel C νb' μb' .val [] true ((φ₁ x).getD (.pvar x)) ((φ₂ (μ x)).getD (.pvar (μ x))) := by
        intro x hx hne
        refine (hS.params x (hfp x hx hne)).congr ?_ ?_ ?_
        · intro m hm
          exact (hνb'n m (ownKey_of_OK₁ hr₁ (hS.param_names (hfp x hx hne) hm))).symm
        · intro m hm
          refine Or.inr ?_
          cases hφ : φ₁ x with
          | none => rw [hφ] at hm; simp [sealedFree] at hm
          | some w =>
              rw [hφ, Option.getD_some] at hm
              exact (hνb'n m (ownKey_of_OK₁ hr₁ (hS.sealCapφ₁ x (hfp x hx hne) w hφ m hm))).symm
        · intro y hy
          obtain ⟨-, rfl⟩ := hS.param_params (hfp x hx hne) hy
          exact (hμb'n y hne).symm
      have hSb : SubOK C νb μb Rb b₁ (θ₁.hideOwn own₁) (φ₁.hideParam x₁) (θ₂.hideOwn own₂)
          (φ₂.hideParam x₂) νb' μb' id := {
        names := by
          intro n hn
          by_cases ho : ownKey own₁ n = true
          · have h2 : ownKey own₂ (νb n) = true := by rw [hown n hn]; exact ho
            simp only [Sub.hideOwn, ho, h2, if_true, Option.getD_none]
            rw [← hνb'o n ho]
            exact .var n ((hνb'o n ho).symm ▸ hb.varHole_free hn)
          · have ho' : ownKey own₁ n = false := by simpa using ho
            have h2 : ownKey own₂ (νb n) = false := by rw [hown n hn]; exact ho'
            simp only [Sub.hideOwn, ho', h2, Bool.false_eq_true, if_false]
            rw [hνb n ho']
            exact hcongN n hn ho'
        params := by
          intro x hx
          by_cases hxx : x = x₁
          · have hp₁ : C.parOK x (μb x) := hb.parOK_free hx
            rw [hxx, hμx]
            simp only [Sub.hideParam, if_true, Option.getD_none]
            rw [← hμb'x]
            exact .pvar x₁ ((hμb'x).symm ▸ (hμx.symm ▸ (hxx ▸ hp₁)))
          · have hne2 : μ x ≠ x₂ := hpar x hx hxx
            simp only [Sub.hideParam, hxx, if_false, hμb x hxx, hne2]
            exact hcongP x hx hxx
        res := by
          intro m hm
          simp [Sub.hideOwn, hres m hm]
        resInj := fun _ _ _ _ h => h
        rnPres := C.preserve_refl
        cap₁ := by
          intro n hn w hw
          by_cases ho : ownKey own₁ n = true
          · simp [Sub.hideOwn, ho] at hw
          · have ho' : ownKey own₁ n = false := by simpa using ho
            simp only [Sub.hideOwn, ho', Bool.false_eq_true, if_false] at hw
            exact hS.cap₁ n (hfv n hn ho') w hw
        capφ₁ := by
          intro x hx w hw
          by_cases hxx : x = x₁
          · rw [hxx] at hw
            simp [Sub.hideParam] at hw
          · simp only [Sub.hideParam, hxx, if_false] at hw
            exact hS.capφ₁ x (hfp x hx hxx) w hw
        cap₂ := by
          intro n hn w hw
          by_cases ho : ownKey own₁ n = true
          · have h2 : ownKey own₂ (νb n) = true := by rw [hown n hn]; exact ho
            simp [Sub.hideOwn, h2] at hw
          · have ho' : ownKey own₁ n = false := by simpa using ho
            have h2 : ownKey own₂ (νb n) = false := by rw [hown n hn]; exact ho'
            simp only [Sub.hideOwn, h2, Bool.false_eq_true, if_false] at hw
            rw [hνb n ho'] at hw
            exact hS.cap₂ n (hfv n hn ho') w hw
        capφ₂ := by
          intro x hx w hw
          by_cases hxx : x = x₁
          · rw [hxx, hμx] at hw
            simp [Sub.hideParam] at hw
          · have hne2 : μ x ≠ x₂ := hpar x hx hxx
            simp only [Sub.hideParam, hμb x hxx, hne2, if_false] at hw
            exact hS.capφ₂ x (hfp x hx hxx) w hw
        capR := by
          intro m hm w hw
          simp [Sub.hideOwn, hres m hm] at hw
        sealed := by
          intro n hn
          by_cases ho : ownKey own₁ n = true
          · exact Or.inr (hνb'o n ho)
          · have ho' : ownKey own₁ n = false := by simpa using ho
            rw [hνb'n n ho', hνb n ho']
            exact hS.sealed n (by simp [sealedFree, hn, ho'])
        sealCap₁ := by
          intro n hn w hw
          by_cases ho : ownKey own₁ n = true
          · simp [Sub.hideOwn, ho] at hw
          · have ho' : ownKey own₁ n = false := by simpa using ho
            simp only [Sub.hideOwn, ho', Bool.false_eq_true, if_false] at hw
            exact hS.sealCap₁ n (hfv n hn ho') w hw
        sealCapφ₁ := by
          intro x hx w hw
          by_cases hxx : x = x₁
          · rw [hxx] at hw
            simp [Sub.hideParam] at hw
          · simp only [Sub.hideParam, hxx, if_false] at hw
            exact hS.sealCapφ₁ x (hfp x hx hxx) w hw }
      have IH := ihb hSb
      rw [List.map_id] at IH
      have hownFV : ∀ n ∈ freeNames (subst (θ₁.hideOwn own₁) (φ₁.hideParam x₁) b₁),
          ownKey own₁ n = true → n ∈ freeNames b₁ := by
        intro n hn ho
        rcases mem_freeNames_subst' b₁ _ _ n hn with ⟨h1, _⟩ | ⟨n₀, hn₀, w, hw, hm⟩ |
            ⟨y, hy, w, hw, hm⟩
        · exact h1
        · rw [ownKey_of_OK₁ hr₁ ((hSb.cap₁ n₀ hn₀ w hw).1 n hm)] at ho
          cases ho
        · rw [ownKey_of_OK₁ hr₁ ((hSb.capφ₁ y hy w hw).1 n hm)] at ho
          cases ho
      have hownSF : ∀ n ∈ sealedFree (subst (θ₁.hideOwn own₁) (φ₁.hideParam x₁) b₁),
          ownKey own₁ n = true → n ∈ sealedFree b₁ := by
        intro n hn ho
        rcases mem_sealedFree_subst b₁ _ _ n hn with h1 | ⟨n₀, hn₀, w, hw, hm⟩ |
            ⟨y, hy, w, hw, hm⟩
        · exact h1
        · rw [ownKey_of_OK₁ hr₁ (hSb.sealCap₁ n₀ hn₀ w hw n hm)] at ho
          cases ho
        · rw [ownKey_of_OK₁ hr₁ (hSb.sealCapφ₁ y hy w hw n hm)] at ho
          cases ho
      have hownAll : ∀ n ∈ freeNames (subst (θ₁.hideOwn own₁) (φ₁.hideParam x₁) b₁) ++
          sealedFree (subst (θ₁.hideOwn own₁) (φ₁.hideParam x₁) b₁),
          ownKey own₁ n = true → n ∈ freeNames b₁ ++ sealedFree b₁ := by
        intro n hn ho
        rcases List.mem_append.1 hn with h | h
        · exact List.mem_append_left _ (hownFV n h ho)
        · exact List.mem_append_right _ (hownSF n h ho)
      have hroot : ∀ s, OK₁ C (.src s) →
          ownKey own₂ (C.codeMap (.src s)) = ownKey own₁ (.src s) := by
        intro s hs
        obtain ⟨s', e, hs'⟩ := C.codeMap_root s hs
        rw [e, ownKey_of_OK₁ hr₁ hs, ownKey_of_OK₂ hr₂ (n := .src s') hs']
      refine .lam (νb := νb') (μb := μb') hνb'n hμb'n hμb'x hr₁ hr₂ IH ?_ hres ?_ ?_ hnd ?_
        hbare hseen ?_ ?_
      · intro n hn
        rcases mem_freeNames_subst' b₁ _ _ n hn with ⟨h1, h2⟩ | ⟨n₀, hn₀, w, hw, hm⟩ |
            ⟨y, hy, w, hw, hm⟩
        · by_cases ho : ownKey own₁ n = true
          · rw [hνb'o n ho, hown n h1]
          · have ho' : ownKey own₁ n = false := by simpa using ho
            rw [hνb'n n ho', ho']
            simp only [Sub.hideOwn, ho', Bool.false_eq_true, if_false] at h2
            rcases hS.kept_image (hfv n h1 ho') h2 with ⟨_, e⟩ | hok
            · rw [e, ← hνb n ho', hown n h1, ho']
            · exact ownKey_of_OK₂ hr₂ hok
        · have ho₀ : ownKey own₁ n₀ = false := by
            cases hk₀ : ownKey own₁ n₀
            · rfl
            · simp [Sub.hideOwn, hk₀] at hw
          simp only [Sub.hideOwn, ho₀, Bool.false_eq_true, if_false] at hw
          have ho : ownKey own₁ n = false :=
            ownKey_of_OK₁ hr₁ ((hS.cap₁ n₀ (hfv n₀ hn₀ ho₀) w hw).1 n hm)
          rw [hνb'n n ho, ho]
          rcases hS.inserted_image (hfv n₀ hn₀ ho₀) hw hm with hok | ⟨_, e⟩
          · exact ownKey_of_OK₂ hr₂ hok
          · rw [e, ← hνb n₀ ho₀, hown n₀ hn₀, ho₀]
        · have hyx : y ≠ x₁ := by
            rintro rfl
            simp [Sub.hideParam] at hw
          simp only [Sub.hideParam, hyx, if_false] at hw
          have ho : ownKey own₁ n = false :=
            ownKey_of_OK₁ hr₁ ((hS.capφ₁ y (hfp y hy hyx) w hw).1 n hm)
          rw [hνb'n n ho, ho]
          exact ownKey_of_OK₂ hr₂ (hS.inserted_param_image (hfp y hy hyx) hw hm)
      · intro n hn n' hn' ho ho' he
        rw [hνb'o n ho, hνb'o n' ho'] at he
        exact hinj n (hownAll n hn ho) n' (hownAll n' hn' ho') ho ho' he
      · intro n hn ho
        rw [hνb'o n ho]
        exact hdisj n (hownAll n hn ho) ho
      · intro x hx hne
        rcases mem_freeParams_subst' b₁ _ _ x hx with ⟨h1, h2⟩ | ⟨n₀, hn₀, w, hw, hm⟩ |
            ⟨y, hy, w, hw, hm⟩
        · simp only [Sub.hideParam, hne, if_false] at h2
          have hr := hS.params x (hfp x h1 hne)
          rw [h2, Option.getD_none] at hr
          have e := hr.pvar_left
          cases h3 : φ₂ (μ x) with
          | none =>
              rw [h3, Option.getD_none] at e
              rw [← Tm.pvar.inj e]
              exact hpar x h1 hne
          | some w₂ =>
              rw [h3, Option.getD_some] at e
              have hc := (hS.capφ₂ x (hfp x h1 hne) w₂ h3).2
              rw [e] at hc
              simp [freeParams] at hc
        · rw [(hSb.cap₁ n₀ hn₀ w hw).2] at hm
          cases hm
        · rw [(hSb.capφ₁ y hy w hw).2] at hm
          cases hm
      · intro s hs
        rcases mem_sealedFree_subst b₁ _ _ _ hs with h1 | ⟨n₀, hn₀, w, hw, hm⟩ |
            ⟨y, hy, w, hw, hm⟩
        · exact hsealO s h1
        · exact hroot s (hSb.sealCap₁ n₀ hn₀ w hw _ hm)
        · exact hroot s (hSb.sealCapφ₁ y hy w hw _ hm)
      · intro n hn ho
        rw [hνb'o n ho]
        exact hsealK n (hownSF n hn ho) ho
  | @letAct ν μ k ℓ own p₁ w₁ b₁ p₂ w₂ b₂ νi Rh Rw Rp Rb _ _ _ hk hνi hr hℓp hℓb _ hp hb hlive hinj
      ihw ihp ihb =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      have hr₁ : ∀ s ∈ own, ¬ C.root₁ s := fun s hs => (hr s hs).1
      have hrh : ∀ s ∈ own, ¬ C.hole s := fun s hs => (hr s hs).2
      have e₁ : (subst θ₁ φ₁ (.app (.lam ℓ own (.letP p₁ (.pvar ℓ) b₁)) w₁) : Tm S X₁) =
          .app (.lam ℓ own (.letP (subst (θ₁.hideOwn own) (φ₁.hideParam ℓ) p₁) (.pvar ℓ)
            (subst (θ₁.hideOwn own) (φ₁.hideParam ℓ) b₁))) (subst θ₁ φ₁ w₁) := by
        simp [subst, Sub.hideParam]
      rw [e₁]
      simp only [subst]
      rw [List.map_append, List.map_append, List.map_append]
      let νi' : Nm X₁ → Nm X₂ := fun m => if ownKey own m = true then rn (νi m) else ν' m
      have hνi'o : ∀ m, ownKey own m = true → νi' m = rn (νi m) := fun m h => by simp [νi', h]
      have hνi'n : ∀ m, ownKey own m = false → νi' m = ν' m := fun m h => by simp [νi', h]
      have hRes : ∀ m, m ∈ Rh ∨ m ∈ Rp ∨ m ∈ Rb → m ∈ Rh ++ Rw ++ Rp ++ Rb := by
        intro m hm
        simp only [List.mem_append]
        rcases hm with hm | hm | hm
        · exact Or.inl (Or.inl (Or.inl hm))
        · exact Or.inl (Or.inr hm)
        · exact Or.inr hm
      have hfv : ∀ n, n ∈ freeNames p₁ ∨ n ∈ freeNames b₁ → ownKey own n = false →
          n ∈ freeNames (.app (.lam ℓ own (.letP p₁ (.pvar ℓ) b₁)) w₁ : Tm S X₁) :=
        fun n hn ho => mem_freeNames_letAct.2 (Or.inl ⟨hn, ho⟩)
      have hfp : ∀ x, x ∈ freeParams p₁ ∨ x ∈ freeParams b₁ →
          x ∈ freeParams (.app (.lam ℓ own (.letP p₁ (.pvar ℓ) b₁)) w₁ : Tm S X₁) := by
        intro x hx
        refine mem_freeParams_letAct.2 (Or.inl ⟨hx, ?_⟩)
        rintro rfl
        rcases hx with hx | hx
        · exact hℓp hx
        · exact hℓb hx
      have hxℓ : ∀ x, x ∈ freeParams p₁ ∨ x ∈ freeParams b₁ → x ≠ ℓ := by
        rintro x hx rfl
        rcases hx with hx | hx
        · exact hℓp hx
        · exact hℓb hx
      have hSi : ∀ (u : Tm S X₁) (Ru : List (Nm X₂)),
          (∀ n ∈ freeNames u, n ∈ freeNames p₁ ∨ n ∈ freeNames b₁) →
          (∀ x ∈ freeParams u, x ∈ freeParams p₁ ∨ x ∈ freeParams b₁) →
          (∀ m ∈ Ru, m ∈ Rp ∨ m ∈ Rb) →
          (∀ n ∈ sealedFree u, n ∈ sealedFree p₁ ∨ n ∈ sealedFree b₁) →
          SubOK C νi μ Ru u (θ₁.hideOwn own) (φ₁.hideParam ℓ) θ₂ φ₂ νi' μ' rn := by
        intro u Ru hun hux huR hus
        exact {
          names := by
            intro n hn
            have hn' := hun n hn
            by_cases ho : ownKey own n = true
            · have hl : νi n ∈ Rh := hlive n (List.mem_append.2 hn') ho
              have hv : C.varHole n (νi n) := by
                rcases hn' with h | h
                · exact hp.varHole_free h
                · exact hb.varHole_free h
              have hv' : C.varHole n (rn (νi n)) := C.varHole_rename hv (hS.rnPres (νi n))
              simp only [Sub.hideOwn, ho, if_true, Option.getD_none]
              rw [hS.res (νi n) (hRes _ (Or.inl hl)), ← hνi'o n ho]
              exact .var n ((hνi'o n ho).symm ▸ hv')
            · have ho' : ownKey own n = false := by simpa using ho
              simp only [Sub.hideOwn, ho', Bool.false_eq_true, if_false]
              rw [hνi n ho']
              refine (hS.names n (hfv n hn' ho')).congr ?_ ?_ (fun _ _ => rfl)
              · intro m hm
                rcases hS.replacement_names (hfv n hn' ho') hm with ⟨_, rfl⟩ | hok
                · exact (hνi'n m ho').symm
                · exact (hνi'n m (ownKey_of_OK₁ hr₁ hok)).symm
              · intro m hm
                refine Or.inr ?_
                cases hθ : θ₁ n with
                | none => rw [hθ] at hm; simp [sealedFree] at hm
                | some w =>
                    rw [hθ, Option.getD_some] at hm
                    exact (hνi'n m (ownKey_of_OK₁ hr₁
                      (hS.sealCap₁ n (hfv n hn' ho') w hθ m hm))).symm
          params := by
            intro x hx
            have hx' := hux x hx
            simp only [Sub.hideParam, hxℓ x hx', if_false]
            refine (hS.params x (hfp x hx')).congr ?_ ?_ (fun _ _ => rfl)
            · intro m hm
              exact (hνi'n m (ownKey_of_OK₁ hr₁ (hS.param_names (hfp x hx') hm))).symm
            · intro m hm
              refine Or.inr ?_
              cases hφ : φ₁ x with
              | none => rw [hφ] at hm; simp [sealedFree] at hm
              | some w =>
                  rw [hφ, Option.getD_some] at hm
                  exact (hνi'n m (ownKey_of_OK₁ hr₁
                    (hS.sealCapφ₁ x (hfp x hx') w hφ m hm))).symm
          res := fun m hm => hS.res m (hRes m (Or.inr (huR m hm)))
          resInj := fun m hm m' hm' he =>
            hS.resInj m (hRes m (Or.inr (huR m hm))) m' (hRes m' (Or.inr (huR m' hm'))) he
          rnPres := hS.rnPres
          cap₁ := by
            intro n hn w hw
            by_cases ho : ownKey own n = true
            · simp [Sub.hideOwn, ho] at hw
            · have ho' : ownKey own n = false := by simpa using ho
              simp only [Sub.hideOwn, ho', Bool.false_eq_true, if_false] at hw
              exact hS.cap₁ n (hfv n (hun n hn) ho') w hw
          capφ₁ := by
            intro x hx w hw
            simp only [Sub.hideParam, hxℓ x (hux x hx), if_false] at hw
            exact hS.capφ₁ x (hfp x (hux x hx)) w hw
          cap₂ := by
            intro n hn w hw
            by_cases ho : ownKey own n = true
            · exact hS.capR (νi n) (hRes _ (Or.inl (hlive n (List.mem_append.2 (hun n hn)) ho))) w hw
            · have ho' : ownKey own n = false := by simpa using ho
              rw [hνi n ho'] at hw
              exact hS.cap₂ n (hfv n (hun n hn) ho') w hw
          capφ₂ := fun x hx w hw => hS.capφ₂ x (hfp x (hux x hx)) w hw
          capR := fun m hm w hw => hS.capR m (hRes m (Or.inr (huR m hm))) w hw
          sealed := by
            intro n hn
            have hn' := hus n hn
            have ho : ownKey own n = false := ownKey_of_holeName hrh (by
              rcases hn' with h | h
              · exact hp.sealedFree_holeName n h
              · exact hb.sealedFree_holeName n h)
            rw [hνi'n n ho, hνi n ho]
            refine hS.sealed n ?_
            rcases hn' with h | h <;> simp [sealedFree, h, ho]
          sealCap₁ := by
            intro n hn w hw
            by_cases ho : ownKey own n = true
            · simp [Sub.hideOwn, ho] at hw
            · have ho' : ownKey own n = false := by simpa using ho
              simp only [Sub.hideOwn, ho', Bool.false_eq_true, if_false] at hw
              exact hS.sealCap₁ n (hfv n (hun n hn) ho') w hw
          sealCapφ₁ := by
            intro x hx w hw
            simp only [Sub.hideParam, hxℓ x (hux x hx), if_false] at hw
            exact hS.sealCapφ₁ x (hfp x (hux x hx)) w hw }
      have hSp := hSi p₁ Rp (fun n h => Or.inl h) (fun x h => Or.inl h) (fun m h => Or.inl h)
        (fun n h => Or.inl h)
      have hSb := hSi b₁ Rb (fun n h => Or.inr h) (fun x h => Or.inr h) (fun m h => Or.inr h)
        (fun n h => Or.inr h)
      have hownFV : ∀ u : Tm S X₁, ∀ Ru : List (Nm X₂), (∀ n ∈ freeNames u, n ∈ freeNames p₁ ∨ n ∈ freeNames b₁) →
          (∀ x ∈ freeParams u, x ∈ freeParams p₁ ∨ x ∈ freeParams b₁) →
          (∀ m ∈ Ru, m ∈ Rp ∨ m ∈ Rb) →
          (∀ n ∈ sealedFree u, n ∈ sealedFree p₁ ∨ n ∈ sealedFree b₁) →
          ∀ n ∈ freeNames (subst (θ₁.hideOwn own) (φ₁.hideParam ℓ) u), ownKey own n = true →
            n ∈ freeNames u := by
        intro u Ru hun hux huR hus n hn ho
        have hSu := hSi u Ru hun hux huR hus
        rcases mem_freeNames_subst' u _ _ n hn with ⟨h1, _⟩ | ⟨n₀, hn₀, w, hw, hm⟩ |
            ⟨y, hy, w, hw, hm⟩
        · exact h1
        · rw [ownKey_of_OK₁ hr₁ ((hSu.cap₁ n₀ hn₀ w hw).1 n hm)] at ho
          cases ho
        · rw [ownKey_of_OK₁ hr₁ ((hSu.capφ₁ y hy w hw).1 n hm)] at ho
          cases ho
      have hpFV := hownFV p₁ Rp (fun n h => Or.inl h) (fun x h => Or.inl h) (fun m h => Or.inl h)
        (fun n h => Or.inl h)
      have hbFV := hownFV b₁ Rb (fun n h => Or.inr h) (fun x h => Or.inr h) (fun m h => Or.inr h)
        (fun n h => Or.inr h)
      have hℓ' : ∀ u : Tm S X₁, ∀ Ru : List (Nm X₂), (∀ n ∈ freeNames u, n ∈ freeNames p₁ ∨ n ∈ freeNames b₁) →
          (∀ x ∈ freeParams u, x ∈ freeParams p₁ ∨ x ∈ freeParams b₁) →
          (∀ m ∈ Ru, m ∈ Rp ∨ m ∈ Rb) →
          (∀ n ∈ sealedFree u, n ∈ sealedFree p₁ ∨ n ∈ sealedFree b₁) →
          ℓ ∉ freeParams (subst (θ₁.hideOwn own) (φ₁.hideParam ℓ) u) := by
        intro u Ru hun hux huR hus hm
        have hSu := hSi u Ru hun hux huR hus
        rcases mem_freeParams_subst' u _ _ ℓ hm with ⟨h1, _⟩ | ⟨n₀, hn₀, w, hw, hm'⟩ |
            ⟨y, hy, w, hw, hm'⟩
        · exact hxℓ ℓ (hux ℓ h1) rfl
        · rw [(hSu.cap₁ n₀ hn₀ w hw).2] at hm'
          cases hm'
        · rw [(hSu.capφ₁ y hy w hw).2] at hm'
          cases hm'
      refine .letAct (νi := νi') (Rh := Rh.map rn) hk hνi'n hr
        (hℓ' p₁ Rp (fun n h => Or.inl h) (fun x h => Or.inl h) (fun m h => Or.inl h)
          (fun n h => Or.inl h))
        (hℓ' b₁ Rb (fun n h => Or.inr h) (fun x h => Or.inr h) (fun m h => Or.inr h)
          (fun n h => Or.inr h))
        (ihw (hS.restrict (fun n h => mem_freeNames_letAct.2 (Or.inr h))
          (fun x h => mem_freeParams_letAct.2 (Or.inr h)) (fun m h => by simp [h]) (fun n h => by simp [sealedFree, h])))
        (ihp hSp) (ihb hSb) ?_ ?_
      · intro n hn ho
        have hn' : n ∈ freeNames p₁ ++ freeNames b₁ := by
          rcases List.mem_append.1 hn with h | h
          · exact List.mem_append_left _ (hpFV n h ho)
          · exact List.mem_append_right _ (hbFV n h ho)
        rw [hνi'o n ho]
        exact List.mem_map_of_mem (hlive n hn' ho)
      · intro n hn n' hn' ho ho' he
        have h1 : n ∈ freeNames p₁ ++ freeNames b₁ := by
          rcases List.mem_append.1 hn with h | h
          · exact List.mem_append_left _ (hpFV n h ho)
          · exact List.mem_append_right _ (hbFV n h ho)
        have h2 : n' ∈ freeNames p₁ ++ freeNames b₁ := by
          rcases List.mem_append.1 hn' with h | h
          · exact List.mem_append_left _ (hpFV n' h ho')
          · exact List.mem_append_right _ (hbFV n' h ho')
        rw [hνi'o n ho, hνi'o n' ho'] at he
        have l1 := hlive n h1 ho
        have l2 := hlive n' h2 ho'
        exact hinj n h1 n' h2 ho ho'
          (hS.resInj _ (hRes _ (Or.inl l1)) _ (hRes _ (Or.inl l2)) he)
  | @newAct ν μ ℓ own b₁ b₂ νi Rh Rb _ hνi hr hℓ hb hlive hinj ihb =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      have hr₁ : ∀ s ∈ own, ¬ C.root₁ s := fun s hs => (hr s hs).1
      have hrh : ∀ s ∈ own, ¬ C.hole s := fun s hs => (hr s hs).2
      have e₁ : (subst θ₁ φ₁ (.app (.lam ℓ own b₁) (.lam ℓ [] (.pvar ℓ))) : Tm S X₁) =
          .app (.lam ℓ own (subst (θ₁.hideOwn own) (φ₁.hideParam ℓ) b₁)) (.lam ℓ [] (.pvar ℓ)) := by
        simp [subst, Sub.hideParam]
      rw [e₁, List.map_append]
      let νi' : Nm X₁ → Nm X₂ := fun m => if ownKey own m = true then rn (νi m) else ν' m
      have hνi'o : ∀ m, ownKey own m = true → νi' m = rn (νi m) := fun m h => by simp [νi', h]
      have hνi'n : ∀ m, ownKey own m = false → νi' m = ν' m := fun m h => by simp [νi', h]
      have hfv : ∀ n, n ∈ freeNames b₁ → ownKey own n = false →
          n ∈ freeNames (.app (.lam ℓ own b₁) (.lam ℓ [] (.pvar ℓ)) : Tm S X₁) :=
        fun n hn ho => mem_freeNames_newAct.2 ⟨hn, ho⟩
      have hxℓ : ∀ x, x ∈ freeParams b₁ → x ≠ ℓ := by
        rintro x hx rfl
        exact hℓ hx
      have hfp : ∀ x, x ∈ freeParams b₁ →
          x ∈ freeParams (.app (.lam ℓ own b₁) (.lam ℓ [] (.pvar ℓ)) : Tm S X₁) :=
        fun x hx => mem_freeParams_newAct.2 ⟨hx, hxℓ x hx⟩
      have hRes : ∀ m, m ∈ Rh ∨ m ∈ Rb → m ∈ Rh ++ Rb := fun m hm => List.mem_append.2 hm
      have hSb : SubOK C νi μ Rb b₁ (θ₁.hideOwn own) (φ₁.hideParam ℓ) θ₂ φ₂ νi' μ' rn := {
        names := by
          intro n hn
          by_cases ho : ownKey own n = true
          · have hl : νi n ∈ Rh := hlive n hn ho
            have hv' : C.varHole n (rn (νi n)) :=
              C.varHole_rename (hb.varHole_free hn) (hS.rnPres (νi n))
            simp only [Sub.hideOwn, ho, if_true, Option.getD_none]
            rw [hS.res (νi n) (hRes _ (Or.inl hl)), ← hνi'o n ho]
            exact .var n ((hνi'o n ho).symm ▸ hv')
          · have ho' : ownKey own n = false := by simpa using ho
            simp only [Sub.hideOwn, ho', Bool.false_eq_true, if_false]
            rw [hνi n ho']
            refine (hS.names n (hfv n hn ho')).congr ?_ ?_ (fun _ _ => rfl)
            · intro m hm
              rcases hS.replacement_names (hfv n hn ho') hm with ⟨_, rfl⟩ | hok
              · exact (hνi'n m ho').symm
              · exact (hνi'n m (ownKey_of_OK₁ hr₁ hok)).symm
            · intro m hm
              refine Or.inr ?_
              cases hθ : θ₁ n with
              | none => rw [hθ] at hm; simp [sealedFree] at hm
              | some w =>
                  rw [hθ, Option.getD_some] at hm
                  exact (hνi'n m (ownKey_of_OK₁ hr₁ (hS.sealCap₁ n (hfv n hn ho') w hθ m hm))).symm
        params := by
          intro x hx
          simp only [Sub.hideParam, hxℓ x hx, if_false]
          refine (hS.params x (hfp x hx)).congr ?_ ?_ (fun _ _ => rfl)
          · intro m hm
            exact (hνi'n m (ownKey_of_OK₁ hr₁ (hS.param_names (hfp x hx) hm))).symm
          · intro m hm
            refine Or.inr ?_
            cases hφ : φ₁ x with
            | none => rw [hφ] at hm; simp [sealedFree] at hm
            | some w =>
                rw [hφ, Option.getD_some] at hm
                exact (hνi'n m (ownKey_of_OK₁ hr₁ (hS.sealCapφ₁ x (hfp x hx) w hφ m hm))).symm
        res := fun m hm => hS.res m (hRes m (Or.inr hm))
        resInj := fun m hm m' hm' he =>
          hS.resInj m (hRes m (Or.inr hm)) m' (hRes m' (Or.inr hm')) he
        rnPres := hS.rnPres
        cap₁ := by
          intro n hn w hw
          by_cases ho : ownKey own n = true
          · simp [Sub.hideOwn, ho] at hw
          · have ho' : ownKey own n = false := by simpa using ho
            simp only [Sub.hideOwn, ho', Bool.false_eq_true, if_false] at hw
            exact hS.cap₁ n (hfv n hn ho') w hw
        capφ₁ := by
          intro x hx w hw
          simp only [Sub.hideParam, hxℓ x hx, if_false] at hw
          exact hS.capφ₁ x (hfp x hx) w hw
        cap₂ := by
          intro n hn w hw
          by_cases ho : ownKey own n = true
          · exact hS.capR (νi n) (hRes _ (Or.inl (hlive n hn ho))) w hw
          · have ho' : ownKey own n = false := by simpa using ho
            rw [hνi n ho'] at hw
            exact hS.cap₂ n (hfv n hn ho') w hw
        capφ₂ := fun x hx w hw => hS.capφ₂ x (hfp x hx) w hw
        capR := fun m hm w hw => hS.capR m (hRes m (Or.inr hm)) w hw
        sealed := by
          intro n hn
          have ho : ownKey own n = false := ownKey_of_holeName hrh (hb.sealedFree_holeName n hn)
          rw [hνi'n n ho, hνi n ho]
          exact hS.sealed n (by simp [sealedFree, hn, ho])
        sealCap₁ := by
          intro n hn w hw
          by_cases ho : ownKey own n = true
          · simp [Sub.hideOwn, ho] at hw
          · have ho' : ownKey own n = false := by simpa using ho
            simp only [Sub.hideOwn, ho', Bool.false_eq_true, if_false] at hw
            exact hS.sealCap₁ n (hfv n hn ho') w hw
        sealCapφ₁ := by
          intro x hx w hw
          simp only [Sub.hideParam, hxℓ x hx, if_false] at hw
          exact hS.sealCapφ₁ x (hfp x hx) w hw }
      have hbFV : ∀ n ∈ freeNames (subst (θ₁.hideOwn own) (φ₁.hideParam ℓ) b₁),
          ownKey own n = true → n ∈ freeNames b₁ := by
        intro n hn ho
        rcases mem_freeNames_subst' b₁ _ _ n hn with ⟨h1, _⟩ | ⟨n₀, hn₀, w, hw, hm⟩ |
            ⟨y, hy, w, hw, hm⟩
        · exact h1
        · rw [ownKey_of_OK₁ hr₁ ((hSb.cap₁ n₀ hn₀ w hw).1 n hm)] at ho
          cases ho
        · rw [ownKey_of_OK₁ hr₁ ((hSb.capφ₁ y hy w hw).1 n hm)] at ho
          cases ho
      refine .newAct (νi := νi') (Rh := Rh.map rn) hνi'n hr ?_ (ihb hSb) ?_ ?_
      · intro hm
        rcases mem_freeParams_subst' b₁ _ _ ℓ hm with ⟨h1, _⟩ | ⟨n₀, hn₀, w, hw, hm'⟩ |
            ⟨y, hy, w, hw, hm'⟩
        · exact hℓ h1
        · rw [(hSb.cap₁ n₀ hn₀ w hw).2] at hm'
          cases hm'
        · rw [(hSb.capφ₁ y hy w hw).2] at hm'
          cases hm'
      · intro n hn ho
        rw [hνi'o n ho]
        exact List.mem_map_of_mem (hlive n (hbFV n hn ho) ho)
      · intro n hn n' hn' ho ho' he
        rw [hνi'o n ho, hνi'o n' ho'] at he
        have l1 := hlive n (hbFV n hn ho) ho
        have l2 := hlive n' (hbFV n' hn' ho') ho'
        exact hinj n (hbFV n hn ho) n' (hbFV n' hn' ho') ho ho'
          (hS.resInj _ (hRes _ (Or.inl l1)) _ (hRes _ (Or.inl l2)) he)


/-! ## Renaming a frame's names inside sealed code -/

section SealRenTerm

variable {Y : Type v} [DecidableEq Y]

/-- An own list with the names of `o` removed. -/
theorem ownKey_filter_not (own o : List Y) (n : Nm Y) :
    ownKey (own.filter fun y => decide (y ∉ o)) n = (ownKey own n && !ownKey o n) := by
  cases n with
  | src y =>
      simp only [ownKey, List.contains_eq_mem, List.mem_filter, decide_eq_true_eq]
      by_cases h1 : y ∈ own <;> by_cases h2 : y ∈ o <;> simp [h1, h2]
  | inst _ _ => rfl

/-- The sealed renaming keeps the free parameters. -/
theorem freeParams_sealRen (ρ : Path) : ∀ (own : List Y) (t : Tm S Y),
    freeParams (TemplateScope.sealRen ρ own t) = freeParams t
  | _, .sym _ => rfl
  | _, .fn _ => rfl
  | _, .var _ => rfl
  | _, .pvar _ => rfl
  | own, .lam x o b => by
      simp only [TemplateScope.sealRen, freeParams, freeParams_sealRen ρ _ b]
  | own, .app f a => by
      simp only [TemplateScope.sealRen, freeParams, freeParams_sealRen ρ own f,
        freeParams_sealRen ρ own a]
  | _, .quote _ => rfl
  | _, .ctx _ _ => rfl
  | own, .pquote c => by simp only [TemplateScope.sealRen, freeParams, freeParams_sealRen ρ own c]
  | own, .letP p w b => by
      simp only [TemplateScope.sealRen, freeParams, freeParams_sealRen ρ own p,
        freeParams_sealRen ρ own w, freeParams_sealRen ρ own b]
  | own, .alt t u => by
      simp only [TemplateScope.sealRen, freeParams, freeParams_sealRen ρ own t,
        freeParams_sealRen ρ own u]

/-- **A free name of renamed sealed code** is one the term had and `own` does not
own, or the copy of an own name it had. -/
theorem mem_sealedFree_sealRen (ρ : Path) :
    ∀ (own : List Y) (t : Tm S Y) {m : Nm Y}, m ∈ sealedFree (TemplateScope.sealRen ρ own t) →
      (m ∈ sealedFree t ∧ ownKey own m = false) ∨
        ∃ n ∈ sealedFree t, ownKey own n = true ∧ m = .inst ρ n
  | _, .sym _, _, h => by simp [TemplateScope.sealRen, sealedFree] at h
  | _, .fn _, _, h => by simp [TemplateScope.sealRen, sealedFree] at h
  | _, .var _, _, h => by simp [TemplateScope.sealRen, sealedFree] at h
  | _, .pvar _, _, h => by simp [TemplateScope.sealRen, sealedFree] at h
  | own, .lam x o b, m, h => by
      simp only [TemplateScope.sealRen, sealedFree, List.mem_filter] at h
      obtain ⟨hm, ho⟩ := h
      have ho' : ownKey o m = false := by simpa using ho
      rcases mem_sealedFree_sealRen ρ _ b hm with ⟨hb, hk⟩ | ⟨n, hn, hk, rfl⟩
      · rw [ownKey_filter_not, ho'] at hk
        simp only [Bool.not_false, Bool.and_true] at hk
        exact Or.inl ⟨by simp only [sealedFree, List.mem_filter]; exact ⟨hb, ho⟩, hk⟩
      · rw [ownKey_filter_not, Bool.and_eq_true] at hk
        refine Or.inr ⟨n, ?_, hk.1, rfl⟩
        simp only [sealedFree, List.mem_filter]
        exact ⟨hn, hk.2⟩
  | own, .app f a, m, h => by
      simp only [TemplateScope.sealRen, sealedFree, List.mem_append] at h ⊢
      rcases h with h | h
      · rcases mem_sealedFree_sealRen ρ own f h with ⟨h, hk⟩ | ⟨n, hn, hk, e⟩
        · exact Or.inl ⟨Or.inl h, hk⟩
        · exact Or.inr ⟨n, Or.inl hn, hk, e⟩
      · rcases mem_sealedFree_sealRen ρ own a h with ⟨h, hk⟩ | ⟨n, hn, hk, e⟩
        · exact Or.inl ⟨Or.inr h, hk⟩
        · exact Or.inr ⟨n, Or.inr hn, hk, e⟩
  | own, .quote c, m, h => by
      simp only [TemplateScope.sealRen, sealedFree] at h ⊢
      exact mem_codeVars_renCode ρ own c h
  | own, .ctx _ c, m, h => by
      simp only [TemplateScope.sealRen, sealedFree] at h ⊢
      exact mem_codeVars_renCode ρ own c h
  | own, .pquote c, m, h => by
      simp only [TemplateScope.sealRen, sealedFree] at h ⊢
      exact mem_sealedFree_sealRen ρ own c h
  | own, .letP p w b, m, h => by
      simp only [TemplateScope.sealRen, sealedFree, List.mem_append] at h ⊢
      rcases h with (h | h) | h
      · rcases mem_sealedFree_sealRen ρ own p h with ⟨h, hk⟩ | ⟨n, hn, hk, e⟩
        · exact Or.inl ⟨Or.inl (Or.inl h), hk⟩
        · exact Or.inr ⟨n, Or.inl (Or.inl hn), hk, e⟩
      · rcases mem_sealedFree_sealRen ρ own w h with ⟨h, hk⟩ | ⟨n, hn, hk, e⟩
        · exact Or.inl ⟨Or.inl (Or.inr h), hk⟩
        · exact Or.inr ⟨n, Or.inl (Or.inr hn), hk, e⟩
      · rcases mem_sealedFree_sealRen ρ own b h with ⟨h, hk⟩ | ⟨n, hn, hk, e⟩
        · exact Or.inl ⟨Or.inr h, hk⟩
        · exact Or.inr ⟨n, Or.inr hn, hk, e⟩
  | own, .alt t u, m, h => by
      simp only [TemplateScope.sealRen, sealedFree, List.mem_append] at h ⊢
      rcases h with h | h
      · rcases mem_sealedFree_sealRen ρ own t h with ⟨h, hk⟩ | ⟨n, hn, hk, e⟩
        · exact Or.inl ⟨Or.inl h, hk⟩
        · exact Or.inr ⟨n, Or.inl hn, hk, e⟩
      · rcases mem_sealedFree_sealRen ρ own u h with ⟨h, hk⟩ | ⟨n, hn, hk, e⟩
        · exact Or.inl ⟨Or.inr h, hk⟩
        · exact Or.inr ⟨n, Or.inr hn, hk, e⟩

/-- Renaming holes to copies keeps the code as written. -/
theorem stripCode_renCode (ρ : Path) (own : List Y) :
    ∀ c : Tm S Y, stripCode (renCode ρ own c) = stripCode c
  | .sym _ => rfl
  | .fn _ => rfl
  | .var n => by
      by_cases hk : ownKey own n = true
      · simp only [renCode, hk, if_true, stripCode, mapCode, nmBase]
      · simp only [renCode, hk, Bool.false_eq_true, if_false]
  | .pvar _ => rfl
  | .lam x o b => by
      have := stripCode_renCode ρ own b
      simp only [stripCode] at this ⊢
      simp only [renCode, mapCode, this]
  | .app f a => by
      have h1 := stripCode_renCode ρ own f
      have h2 := stripCode_renCode ρ own a
      simp only [stripCode] at h1 h2 ⊢
      simp only [renCode, mapCode, h1, h2]
  | .quote c => by
      have := stripCode_renCode ρ own c
      simp only [stripCode] at this ⊢
      simp only [renCode, mapCode, this]
  | .ctx _ c => by
      have := stripCode_renCode ρ own c
      simp only [stripCode] at this ⊢
      simp only [renCode, mapCode, this]
  | .pquote c => by
      have := stripCode_renCode ρ own c
      simp only [stripCode] at this ⊢
      simp only [renCode, mapCode, this]
  | .letP p w b => by
      have h1 := stripCode_renCode ρ own p
      have h2 := stripCode_renCode ρ own w
      have h3 := stripCode_renCode ρ own b
      simp only [stripCode] at h1 h2 h3 ⊢
      simp only [renCode, mapCode, h1, h2, h3]
  | .alt t u => by
      have h1 := stripCode_renCode ρ own t
      have h2 := stripCode_renCode ρ own u
      simp only [stripCode] at h1 h2 ⊢
      simp only [renCode, mapCode, h1, h2]

theorem ownNil_renCode (ρ : Path) (own : List Y) : ∀ c : Tm S Y, ownNil c → ownNil (renCode ρ own c)
  | .sym _, h => h
  | .fn _, h => h
  | .var n, _ => by
      by_cases hk : ownKey own n = true
      · simp [renCode, hk, ownNil]
      · simp [renCode, hk, ownNil]
  | .pvar _, h => h
  | .lam _ _ b, h => ⟨h.1, ownNil_renCode ρ own b h.2⟩
  | .app f a, h => ⟨ownNil_renCode ρ own f h.1, ownNil_renCode ρ own a h.2⟩
  | .quote c, h => ownNil_renCode ρ own c h
  | .ctx _ c, h => ownNil_renCode ρ own c h
  | .pquote c, h => ownNil_renCode ρ own c h
  | .letP p w b, h =>
      ⟨ownNil_renCode ρ own p h.1, ownNil_renCode ρ own w h.2.1, ownNil_renCode ρ own b h.2.2⟩
  | .alt t u, h => ⟨ownNil_renCode ρ own t h.1, ownNil_renCode ρ own u h.2⟩

theorem codeBinders_renCode (ρ : Path) (own : List Y) :
    ∀ c : Tm S Y, codeBinders (renCode ρ own c) = codeBinders c
  | .sym _ => rfl
  | .fn _ => rfl
  | .var n => by
      by_cases hk : ownKey own n = true
      · simp [renCode, hk, codeBinders]
      · simp [renCode, hk]
  | .pvar _ => rfl
  | .lam x o b => by simp only [renCode, codeBinders, codeBinders_renCode ρ own b]
  | .app f a => by simp only [renCode, codeBinders, codeBinders_renCode ρ own f,
      codeBinders_renCode ρ own a]
  | .quote c => by simp only [renCode, codeBinders, codeBinders_renCode ρ own c]
  | .ctx _ c => by simp only [renCode, codeBinders, codeBinders_renCode ρ own c]
  | .pquote c => by simp only [renCode, codeBinders, codeBinders_renCode ρ own c]
  | .letP p w b => by simp only [renCode, codeBinders, codeBinders_renCode ρ own p,
      codeBinders_renCode ρ own w, codeBinders_renCode ρ own b]
  | .alt t u => by simp only [renCode, codeBinders, codeBinders_renCode ρ own t,
      codeBinders_renCode ρ own u]

end SealRenTerm

omit [DecidableEq X₂] in
/-- Renaming own holes to copies keeps the code form. -/
theorem CodeForm.renCode {c : Tm S X₁} (hf : CodeForm C c) (ρ : Path) (own : List X₁) :
    CodeForm C (TemplateScope.renCode ρ own c) := by
  refine ⟨ownNil_renCode ρ own c hf.1, ?_, ?_⟩
  · intro n hn
    rcases mem_codeVars_renCode ρ own c hn with ⟨h, -⟩ | ⟨m, hm, hk, rfl⟩
    · exact hf.2.1 n h
    · obtain ⟨s, rfl⟩ : ∃ s, m = .src s := by
        cases m with
        | src s => exact ⟨s, rfl⟩
        | inst _ _ => simp [ownKey] at hk
      exact hf.2.1 (.src s) hm
  · intro n hn
    rw [codeBinders_renCode] at hn
    exact hf.2.2 n hn

omit [DecidableEq X₁] [DecidableEq X₂] in
/-- **Reading renamed code**: renaming the code image of the own holes at `ρ'` is
reading the renamed code through a map whose copy at `ρ` has tag `ρ'`. -/
theorem renCode_holeRead {ν ν' : Nm X₁ → Nm X₂} {ρ ρ' : Path} {own₁ : List X₁}
    {own₂ : List X₂} [DecidableEq X₁] [DecidableEq X₂] :
    ∀ (c : Tm S X₁), (∀ n ∈ codeBinders c, ∃ s, n = .src s) →
      (∀ s, Nm.src s ∈ codeVars c → ownKey own₂ (C.codeMap (.src s)) = ownKey own₁ (.src s)) →
      (∀ m ∈ codeVars c, ownKey own₁ m = true → tagOr ρ (ν' (.inst ρ m)) = ρ') →
      (∀ n ∈ codeVars c, (∃ s, n = .src s) ∨ ν' n = ν n) →
      TemplateScope.renCode ρ' own₂ (mapCode (holeRead C ν) c) =
        mapCode (holeRead C ν') (TemplateScope.renCode ρ own₁ c)
  | .sym _, _, _, _, _ => rfl
  | .fn _, _, _, _, _ => rfl
  | .var n, _, hO, hT, hK => by
      cases n with
      | src s =>
          have hO' := hO s (by simp [codeVars])
          by_cases ho : ownKey own₁ (.src s) = true
          · have ho2 : ownKey own₂ (C.codeMap (.src s)) = true := by rw [hO']; exact ho
            have hT' := hT (.src s) (by simp [codeVars]) ho
            simp only [mapCode, TemplateScope.renCode, holeRead, ho, ho2, if_true, hT']
          · have ho' : ownKey own₁ (.src s) = false := by simpa using ho
            have ho2 : ownKey own₂ (C.codeMap (.src s)) = false := by rw [hO']; exact ho'
            simp only [mapCode, TemplateScope.renCode, holeRead, ho', ho2, Bool.false_eq_true,
              if_false]
      | inst ρ₀ m =>
          rcases hK (.inst ρ₀ m) (by simp [codeVars]) with ⟨s, hs⟩ | e
          · cases hs
          · simp only [mapCode, TemplateScope.renCode, holeRead, ownKey, Bool.false_eq_true,
              if_false, e]
  | .pvar x, hB, _, _, _ => by
      obtain ⟨s, rfl⟩ := hB x (by simp [codeBinders])
      rfl
  | .lam x o b, hB, hO, hT, hK => by
      obtain ⟨s, rfl⟩ := hB x (by simp [codeBinders])
      simp only [mapCode, TemplateScope.renCode]
      rw [renCode_holeRead b (fun n hn => hB n (by simp [codeBinders, hn]))
        (fun s hs => hO s (by simpa [codeVars] using hs))
        (fun m hm ho => hT m (by simpa [codeVars] using hm) ho)
        (fun n hn => hK n (by simpa [codeVars] using hn))]
      rfl
  | .app f a, hB, hO, hT, hK => by
      simp only [mapCode, TemplateScope.renCode]
      rw [renCode_holeRead f (fun n hn => hB n (by simp [codeBinders, hn]))
          (fun s hs => hO s (by simp [codeVars, hs])) (fun m hm ho => hT m (by simp [codeVars, hm]) ho)
          (fun n hn => hK n (by simp [codeVars, hn])),
        renCode_holeRead a (fun n hn => hB n (by simp [codeBinders, hn]))
          (fun s hs => hO s (by simp [codeVars, hs])) (fun m hm ho => hT m (by simp [codeVars, hm]) ho)
          (fun n hn => hK n (by simp [codeVars, hn]))]
  | .quote c, hB, hO, hT, hK => by
      simp only [mapCode, TemplateScope.renCode]
      rw [renCode_holeRead c (fun n hn => hB n (by simpa [codeBinders] using hn))
        (fun s hs => hO s (by simpa [codeVars] using hs))
        (fun m hm ho => hT m (by simpa [codeVars] using hm) ho)
        (fun n hn => hK n (by simpa [codeVars] using hn))]
  | .ctx ks c, hB, hO, hT, hK => by
      have hks : ks.map (holeRead C ν) = ks.map (holeRead C ν') :=
        List.map_congr_left fun n hn => by
          obtain ⟨s, rfl⟩ := hB n (by simp [codeBinders, hn])
          rfl
      simp only [mapCode, TemplateScope.renCode]
      rw [hks, renCode_holeRead c (fun n hn => hB n (by simp [codeBinders, hn]))
        (fun s hs => hO s (by simpa [codeVars] using hs))
        (fun m hm ho => hT m (by simpa [codeVars] using hm) ho)
        (fun n hn => hK n (by simpa [codeVars] using hn))]
  | .pquote c, hB, hO, hT, hK => by
      simp only [mapCode, TemplateScope.renCode]
      rw [renCode_holeRead c (fun n hn => hB n (by simpa [codeBinders] using hn))
        (fun s hs => hO s (by simpa [codeVars] using hs))
        (fun m hm ho => hT m (by simpa [codeVars] using hm) ho)
        (fun n hn => hK n (by simpa [codeVars] using hn))]
  | .letP p w b, hB, hO, hT, hK => by
      simp only [mapCode, TemplateScope.renCode]
      rw [renCode_holeRead p (fun n hn => hB n (by simp [codeBinders, hn]))
          (fun s hs => hO s (by simp [codeVars, hs])) (fun m hm ho => hT m (by simp [codeVars, hm]) ho)
          (fun n hn => hK n (by simp [codeVars, hn])),
        renCode_holeRead w (fun n hn => hB n (by simp [codeBinders, hn]))
          (fun s hs => hO s (by simp [codeVars, hs])) (fun m hm ho => hT m (by simp [codeVars, hm]) ho)
          (fun n hn => hK n (by simp [codeVars, hn])),
        renCode_holeRead b (fun n hn => hB n (by simp [codeBinders, hn]))
          (fun s hs => hO s (by simp [codeVars, hs])) (fun m hm ho => hT m (by simp [codeVars, hm]) ho)
          (fun n hn => hK n (by simp [codeVars, hn]))]
  | .alt t u, hB, hO, hT, hK => by
      simp only [mapCode, TemplateScope.renCode]
      rw [renCode_holeRead t (fun n hn => hB n (by simp [codeBinders, hn]))
          (fun s hs => hO s (by simp [codeVars, hs])) (fun m hm ho => hT m (by simp [codeVars, hm]) ho)
          (fun n hn => hK n (by simp [codeVars, hn])),
        renCode_holeRead u (fun n hn => hB n (by simp [codeBinders, hn]))
          (fun s hs => hO s (by simp [codeVars, hs])) (fun m hm ho => hT m (by simp [codeVars, hm]) ho)
          (fun n hn => hK n (by simp [codeVars, hn]))]

omit [DecidableEq X₁] [DecidableEq X₂] in
/-- **Related sealed code stays related when a frame renames its own holes on both
sides**, read through a map whose copy at `ρ` has tag `ρ'`. -/
theorem QR.renCode [DecidableEq X₁] [DecidableEq X₂] {ν ν' : Nm X₁ → Nm X₂} {ρ ρ' : Path}
    {own₁ : List X₁} {own₂ : List X₂} {c₁ : Tm S X₁} {c₂ : Tm S X₂} (h : QR C ν c₁ c₂)
    (hO : ∀ s, Nm.src s ∈ codeVars c₁ → ownKey own₂ (C.codeMap (.src s)) = ownKey own₁ (.src s))
    (hT : ∀ m ∈ codeVars c₁, ownKey own₁ m = true → tagOr ρ (ν' (.inst ρ m)) = ρ')
    (hK : ∀ n ∈ codeVars c₁, (∃ s, n = .src s) ∨ ν' n = ν n) :
    QR C ν' (TemplateScope.renCode ρ own₁ c₁) (TemplateScope.renCode ρ' own₂ c₂) := by
  obtain ⟨hq, hf, rfl⟩ := h
  refine ⟨?_, hf.renCode ρ own₁, renCode_holeRead c₁ hf.2.2 hO hT hK⟩
  rw [stripCode_renCode, stripCode_renCode]
  exact hq

omit [DecidableEq X₂] in
/-- Weak shape survives the renaming of a frame's own holes on both sides. -/
theorem ShapeParallel.sealRen {ν ν' : Nm X₁ → Nm X₂} {ρ ρ' : Path} [DecidableEq X₂] :
    ∀ {t₁ : Tm S X₁} {t₂ : Tm S X₂} (own₁ : List X₁) (own₂ : List X₂),
      ShapeParallel C ν t₁ t₂ →
      (∀ s, Nm.src s ∈ sealedFree t₁ → ownKey own₂ (C.codeMap (.src s)) = ownKey own₁ (.src s)) →
      (∀ m ∈ sealedFree t₁, ownKey own₁ m = true → tagOr ρ (ν' (.inst ρ m)) = ρ') →
      (∀ n ∈ sealedFree t₁, (∃ s, n = .src s) ∨ ν' n = ν n) →
      ShapeParallel C ν' (TemplateScope.sealRen ρ own₁ t₁) (TemplateScope.sealRen ρ' own₂ t₂) := by
  intro t₁
  induction t₁ with
  | sym _ => intro t₂ _ _ h _ _ _; cases t₂ <;> exact h
  | fn _ => intro t₂ _ _ h _ _ _; cases t₂ <;> exact h
  | var _ => intro t₂ _ _ h _ _ _; cases t₂ <;> exact h
  | pvar _ => intro t₂ _ _ h _ _ _; cases t₂ <;> exact h
  | lam _ _ _ _ => intro t₂ _ _ h _ _ _; cases t₂ <;> exact h
  | app f₁ a₁ ihf iha =>
      intro t₂ own₁ own₂ h hO hT hK
      cases t₂ with
      | app f₂ a₂ =>
          exact ⟨ihf own₁ own₂ h.1 (fun s hs => hO s (by simp [sealedFree, hs]))
              (fun m hm ho => hT m (by simp [sealedFree, hm]) ho)
              (fun n hn => hK n (by simp [sealedFree, hn])),
            iha own₁ own₂ h.2 (fun s hs => hO s (by simp [sealedFree, hs]))
              (fun m hm ho => hT m (by simp [sealedFree, hm]) ho)
              (fun n hn => hK n (by simp [sealedFree, hn]))⟩
      | _ => exact h
  | quote c₁ _ =>
      intro t₂ own₁ own₂ h hO hT hK
      cases t₂ with
      | quote c₂ =>
          exact QR.renCode h (fun s hs => hO s (by simpa [sealedFree] using hs))
            (fun m hm ho => hT m (by simpa [sealedFree] using hm) ho)
            (fun n hn => hK n (by simpa [sealedFree] using hn))
      | _ => exact h
  | pquote c₁ ih =>
      intro t₂ own₁ own₂ h hO hT hK
      cases t₂ with
      | pquote c₂ =>
          exact ih own₁ own₂ h (fun s hs => hO s (by simpa [sealedFree] using hs))
            (fun m hm ho => hT m (by simpa [sealedFree] using hm) ho)
            (fun n hn => hK n (by simpa [sealedFree] using hn))
      | _ => exact h
  | letP p₁ w₁ b₁ ihp ihw ihb =>
      intro t₂ own₁ own₂ h hO hT hK
      cases t₂ with
      | letP p₂ w₂ b₂ =>
          exact ⟨ihp own₁ own₂ h.1 (fun s hs => hO s (by simp [sealedFree, hs]))
              (fun m hm ho => hT m (by simp [sealedFree, hm]) ho)
              (fun n hn => hK n (by simp [sealedFree, hn])),
            ihw own₁ own₂ h.2.1 (fun s hs => hO s (by simp [sealedFree, hs]))
              (fun m hm ho => hT m (by simp [sealedFree, hm]) ho)
              (fun n hn => hK n (by simp [sealedFree, hn])),
            ihb own₁ own₂ h.2.2 (fun s hs => hO s (by simp [sealedFree, hs]))
              (fun m hm ho => hT m (by simp [sealedFree, hm]) ho)
              (fun n hn => hK n (by simp [sealedFree, hn]))⟩
      | _ => exact h
  | alt t₁ u₁ ih₁ ih₂ =>
      intro t₂ own₁ own₂ h hO hT hK
      cases t₂ with
      | alt t₂ u₂ =>
          exact ⟨ih₁ own₁ own₂ h.1 (fun s hs => hO s (by simp [sealedFree, hs]))
              (fun m hm ho => hT m (by simp [sealedFree, hm]) ho)
              (fun n hn => hK n (by simp [sealedFree, hn])),
            ih₂ own₁ own₂ h.2 (fun s hs => hO s (by simp [sealedFree, hs]))
              (fun m hm ho => hT m (by simp [sealedFree, hm]) ho)
              (fun n hn => hK n (by simp [sealedFree, hn]))⟩
      | _ => exact h
  | ctx ks₁ c₁ _ =>
      intro t₂ own₁ own₂ h hO hT hK
      cases t₂ with
      | ctx ks₂ c₂ =>
          obtain ⟨hf, hks, hc⟩ := h
          have e := renCode_holeRead (C := C) (ν := ν) (ν' := ν') (ρ := ρ) (ρ' := ρ')
            (own₁ := own₁) (own₂ := own₂) (.ctx ks₁ c₁) hf.2.2
            (fun s hs => hO s (by simpa [sealedFree, codeVars] using hs))
            (fun m hm ho => hT m (by simpa [sealedFree, codeVars] using hm) ho)
            (fun n hn => hK n (by simpa [sealedFree, codeVars] using hn))
          simp only [mapCode, TemplateScope.renCode, Tm.ctx.injEq] at e
          subst hks
          subst hc
          exact ⟨hf.renCode ρ own₁, e.1, e.2⟩
      | _ => exact h

/-- **Renaming a frame's own names inside sealed code keeps the relation.**  The
first side renames `own₁` at `ρ`, the second `own₂` at `ρ'`.  The renamed holes
are read through a map `ν'` whose copy at `ρ` has tag `ρ'`, and `ν'` agrees with
`ν` on the names the relation reads.  An own name and its code image are owned
together. -/
theorem Rel.sealRen {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) (ρ ρ' : Path) :
    ∀ (own₁ : List X₁) (own₂ : List X₂) (ν' : Nm X₁ → Nm X₂),
      (∀ n ∈ relNames t₁, ν' n = ν n) →
      (∀ s, Nm.src s ∈ sealedFree t₁ → ownKey own₂ (C.codeMap (.src s)) = ownKey own₁ (.src s)) →
      (∀ m ∈ sealedFree t₁, ownKey own₁ m = true → tagOr ρ (ν' (.inst ρ m)) = ρ') →
      Rel C ν' μ k Res ok (TemplateScope.sealRen ρ own₁ t₁) (TemplateScope.sealRen ρ' own₂ t₂) := by
  induction h with
  | sym s => intro _ _ _ _ _ _; exact .sym s
  | fn F => intro _ _ _ _ _ _; exact .fn F
  | var n hv =>
      intro own₁ own₂ ν' hν _ _
      have e := hν n (by simp [relNames, freeNames])
      show Rel C ν' _ _ [] true (.var n) (.var _)
      rw [← e]
      exact .var n (by rw [e]; exact hv)
  | pvar x hp =>
      intro _ _ _ _ _ _
      exact .pvar x hp
  | quote hq =>
      intro own₁ own₂ ν' hν hO hT
      exact .quote (hq.renCode (fun s hs => hO s (by simpa [sealedFree] using hs))
        (fun m hm ho => hT m (by simpa [sealedFree] using hm) ho)
        (fun n hn => Or.inr (hν n (by simp [relNames, sealedFree, hn]))))
  | @ctx ν μ k ks₁ c₁ ks₂ c₂ hf hks hc =>
      intro own₁ own₂ ν' hν hO hT
      have e := renCode_holeRead (C := C) (ν := ν) (ν' := ν') (ρ := ρ) (ρ' := ρ')
        (own₁ := own₁) (own₂ := own₂) (.ctx ks₁ c₁) hf.2.2
        (fun s hs => hO s (by simpa [sealedFree, codeVars] using hs))
        (fun m hm ho => hT m (by simpa [sealedFree, codeVars] using hm) ho)
        (fun n hn => Or.inr (hν n (by simp only [codeVars] at hn; simp [relNames, sealedFree, hn])))
      simp only [mapCode, TemplateScope.renCode, Tm.ctx.injEq] at e
      subst hks
      subst hc
      exact .ctx (hf.renCode ρ own₁) e.1 e.2
  | pquote _ hp hok ih =>
      intro own₁ own₂ ν' hν hO hT
      exact .pquote (ih own₁ own₂ ν' (fun n hn => hν n (by simpa [relNames, freeNames, sealedFree] using hn))
          (fun s hs => hO s (by simpa [sealedFree] using hs))
          (fun m hm ho => hT m (by simpa [sealedFree] using hm) ho))
        (hp.sealRen own₁ own₂ (fun s hs => hO s (by simpa [sealedFree] using hs))
          (fun m hm ho => hT m (by simpa [sealedFree] using hm) ho)
          (fun n hn => Or.inr (hν n (by simp [relNames, sealedFree, hn])))) hok
  | app _ _ ihf iha =>
      intro own₁ own₂ ν' hν hO hT
      simp only [relNames, freeNames, sealedFree, List.mem_append] at hν hO hT
      exact .app
        (ihf own₁ own₂ ν' (fun n h => hν n (by simp only [relNames, List.mem_append] at h; tauto))
          (fun s hs => hO s (Or.inl hs)) (fun m hm ho => hT m (Or.inl hm) ho))
        (iha own₁ own₂ ν' (fun n h => hν n (by simp only [relNames, List.mem_append] at h; tauto))
          (fun s hs => hO s (Or.inr hs)) (fun m hm ho => hT m (Or.inr hm) ho))
  | letP hk _ _ _ ihp ihw ihb =>
      intro own₁ own₂ ν' hν hO hT
      simp only [relNames, freeNames, sealedFree, List.mem_append] at hν hO hT
      exact .letP hk
        (ihp own₁ own₂ ν' (fun n h => hν n (by simp only [relNames, List.mem_append] at h; tauto))
          (fun s hs => hO s (Or.inl (Or.inl hs))) (fun m hm ho => hT m (Or.inl (Or.inl hm)) ho))
        (ihw own₁ own₂ ν' (fun n h => hν n (by simp only [relNames, List.mem_append] at h; tauto))
          (fun s hs => hO s (Or.inl (Or.inr hs))) (fun m hm ho => hT m (Or.inl (Or.inr hm)) ho))
        (ihb own₁ own₂ ν' (fun n h => hν n (by simp only [relNames, List.mem_append] at h; tauto))
          (fun s hs => hO s (Or.inr hs)) (fun m hm ho => hT m (Or.inr hm) ho))
  | alt hk _ _ ih₁ ih₂ =>
      intro own₁ own₂ ν' hν hO hT
      simp only [relNames, freeNames, sealedFree, List.mem_append] at hν hO hT
      exact .alt hk
        (ih₁ own₁ own₂ ν' (fun n h => hν n (by simp only [relNames, List.mem_append] at h; tauto))
          (fun s hs => hO s (Or.inl hs)) (fun m hm ho => hT m (Or.inl hm) ho))
        (ih₂ own₁ own₂ ν' (fun n h => hν n (by simp only [relNames, List.mem_append] at h; tauto))
          (fun s hs => hO s (Or.inr hs)) (fun m hm ho => hT m (Or.inr hm) ho))
  | @lam ν μ k x₁ o₁ b₁ x₂ o₂ b₂ νb μb Rb ob hνb hμb hμx hr₁ hr₂ _ hown hres hinj hdisj hnd hpar
      hbare hseen hsealO hsealK ihb =>
      intro own₁ own₂ ν' hν hO hT
      let νb' : Nm X₁ → Nm X₂ := fun m => if ownKey o₁ m = true then νb m else ν' m
      have hagree : ∀ n ∈ relNames b₁, νb' n = νb n := by
        intro n hn
        by_cases ho : ownKey o₁ n = true
        · simp [νb', ho]
        · have ho' : ownKey o₁ n = false := by simpa using ho
          simp only [νb', ho', Bool.false_eq_true, if_false]
          rw [hνb n ho']
          refine hν n ?_
          simp only [relNames, List.mem_append] at hn ⊢
          rcases hn with hn | hn
          · exact Or.inl (mem_freeNames_lam.2 ⟨hn, ho'⟩)
          · exact Or.inr (by simp [sealedFree, hn, ho'])
      have hbody := ihb (own₁.filter fun y => decide (y ∉ o₁)) (own₂.filter fun y => decide (y ∉ o₂))
        νb' hagree
        (by
          intro s hs
          rw [ownKey_filter_not, ownKey_filter_not, hsealO s hs]
          cases hk : ownKey o₁ (.src s)
          · rw [hO s (by simp [sealedFree, hs, hk])]
          · simp)
        (by
          intro m hm ho
          rw [ownKey_filter_not, Bool.and_eq_true, Bool.not_eq_true'] at ho
          have e : νb' (.inst ρ m) = ν' (.inst ρ m) := by simp [νb', ownKey]
          rw [e]
          exact hT m (by simp [sealedFree, hm, ho.2]) ho.1)
      have hsrc : ∀ n ∈ sealedFree (TemplateScope.sealRen ρ (own₁.filter fun y => decide (y ∉ o₁)) b₁),
          ownKey o₁ n = true → n ∈ sealedFree b₁ := by
        intro n hn ho
        rcases mem_sealedFree_sealRen ρ _ b₁ hn with ⟨h, -⟩ | ⟨m, -, -, rfl⟩
        · exact h
        · simp [ownKey] at ho
      have hmem : ∀ n ∈ freeNames (TemplateScope.sealRen ρ (own₁.filter fun y => decide (y ∉ o₁)) b₁) ++
          sealedFree (TemplateScope.sealRen ρ (own₁.filter fun y => decide (y ∉ o₁)) b₁),
          ownKey o₁ n = true → n ∈ freeNames b₁ ++ sealedFree b₁ := by
        intro n hn ho
        rw [List.mem_append, freeNames_sealRen] at hn
        rcases hn with hn | hn
        · exact List.mem_append_left _ hn
        · exact List.mem_append_right _ (hsrc n hn ho)
      have hown' : ∀ n, n ∈ freeNames b₁ ++ sealedFree b₁ → ownKey o₁ n = true → νb' n = νb n := by
        intro n _ ho
        simp [νb', ho]
      refine .lam (νb := νb') (μb := μb) ?_ hμb hμx hr₁ hr₂ hbody ?_ hres ?_ ?_ hnd ?_ hbare hseen ?_ ?_
      · intro n hn
        simp [νb', hn]
      · intro n hn
        rw [freeNames_sealRen] at hn
        rw [hagree n (by simp [relNames, hn])]
        exact hown n hn
      · intro n hn n' hn' ho ho' he
        rw [hown' n (hmem n hn ho) ho, hown' n' (hmem n' hn' ho') ho'] at he
        exact hinj n (hmem n hn ho) n' (hmem n' hn' ho') ho ho' he
      · intro n hn ho
        rw [hown' n (hmem n hn ho) ho]
        exact hdisj n (hmem n hn ho) ho
      · intro x hx hne
        rw [freeParams_sealRen] at hx
        exact hpar x hx hne
      · intro s hs
        rcases mem_sealedFree_sealRen ρ _ b₁ hs with ⟨h, -⟩ | ⟨m, -, -, e⟩
        · exact hsealO s h
        · cases e
      · intro n hn ho
        rw [hown' n (List.mem_append_right _ (hsrc n hn ho)) ho]
        exact hsealK n (hsrc n hn ho) ho
  | @letAct ν μ k ℓ own p₁ w₁ b₁ p₂ w₂ b₂ νi Rh Rw Rp Rb ow op ob hk hνi hr hℓp hℓb hw hp hb hlive
      hinj ihw ihp ihb =>
      intro own₁ own₂ ν' hν hO hT
      let νi' : Nm X₁ → Nm X₂ := fun m => if ownKey own m = true then νi m else ν' m
      have hagree : ∀ n ∈ relNames p₁ ++ relNames b₁, νi' n = νi n := by
        intro n hn
        by_cases ho : ownKey own n = true
        · simp [νi', ho]
        · have ho' : ownKey own n = false := by simpa using ho
          simp only [νi', ho', Bool.false_eq_true, if_false]
          rw [hνi n ho']
          refine hν n ?_
          simp only [relNames, List.mem_append] at hn ⊢
          rcases hn with (hn | hn) | (hn | hn)
          · exact Or.inl (mem_freeNames_letAct.2 (Or.inl ⟨Or.inl hn, ho'⟩))
          · exact Or.inr (by simp [sealedFree, hn, ho'])
          · exact Or.inl (mem_freeNames_letAct.2 (Or.inl ⟨Or.inr hn, ho'⟩))
          · exact Or.inr (by simp [sealedFree, hn, ho'])
      have hhp : ∀ n ∈ sealedFree p₁, ownKey own n = false := fun n hn =>
        ownKey_of_holeName (fun s hs => (hr s hs).2) (hp.sealedFree_holeName n hn)
      have hhb : ∀ n ∈ sealedFree b₁, ownKey own n = false := fun n hn =>
        ownKey_of_holeName (fun s hs => (hr s hs).2) (hb.sealedFree_holeName n hn)
      have hO' : ∀ s, (Nm.src s ∈ sealedFree p₁ ∨ Nm.src s ∈ sealedFree b₁) →
          ownKey own₂ (C.codeMap (.src s)) =
            ownKey (own₁.filter fun y => decide (y ∉ own)) (.src s) := by
        intro s hs
        have ho : ownKey own (.src s) = false := hs.elim (hhp _) (hhb _)
        rw [ownKey_filter_not, ho, Bool.not_false, Bool.and_true]
        exact hO s (by rcases hs with hs | hs <;> simp [sealedFree, hs, ho])
      have hT' : ∀ m, (m ∈ sealedFree p₁ ∨ m ∈ sealedFree b₁) →
          ownKey (own₁.filter fun y => decide (y ∉ own)) m = true →
          tagOr ρ (νi' (.inst ρ m)) = ρ' := by
        intro m hm ho
        have hmo : ownKey own m = false := hm.elim (hhp _) (hhb _)
        rw [ownKey_filter_not, hmo, Bool.not_false, Bool.and_true] at ho
        have e : νi' (.inst ρ m) = ν' (.inst ρ m) := by simp [νi', ownKey]
        rw [e]
        exact hT m (by rcases hm with hm | hm <;> simp [sealedFree, hm, hmo]) ho
      have hp' := ihp (own₁.filter fun y => decide (y ∉ own)) own₂ νi'
        (fun n hn => hagree n (List.mem_append_left _ hn)) (fun s hs => hO' s (Or.inl hs))
        (fun m hm ho => hT' m (Or.inl hm) ho)
      have hb' := ihb (own₁.filter fun y => decide (y ∉ own)) own₂ νi'
        (fun n hn => hagree n (List.mem_append_right _ hn)) (fun s hs => hO' s (Or.inr hs))
        (fun m hm ho => hT' m (Or.inr hm) ho)
      have hw' := ihw own₁ own₂ ν'
        (fun n hn => hν n (by
          simp only [relNames, List.mem_append] at hn ⊢
          rcases hn with hn | hn
          · exact Or.inl (mem_freeNames_letAct.2 (Or.inr hn))
          · exact Or.inr (by simp [sealedFree, hn])))
        (fun s hs => hO s (by simp [sealedFree, hs]))
        (fun m hm ho => hT m (by simp [sealedFree, hm]) ho)
      refine .letAct (νi := νi') hk ?_ hr (by rw [freeParams_sealRen]; exact hℓp)
        (by rw [freeParams_sealRen]; exact hℓb) hw' hp' hb' ?_ ?_
      · intro n hn
        simp [νi', hn]
      · intro n hn ho
        rw [List.mem_append, freeNames_sealRen, freeNames_sealRen] at hn
        have e : νi' n = νi n := by simp [νi', ho]
        rw [e]
        exact hlive n (List.mem_append.2 hn) ho
      · intro n hn n' hn' ho ho' he
        rw [List.mem_append, freeNames_sealRen, freeNames_sealRen] at hn hn'
        have e : νi' n = νi n := by simp [νi', ho]
        have e' : νi' n' = νi n' := by simp [νi', ho']
        rw [e, e'] at he
        exact hinj n (List.mem_append.2 hn) n' (List.mem_append.2 hn') ho ho' he
  | @newAct ν μ ℓ own b₁ b₂ νi Rh Rb ob hνi hr hℓ hb hlive hinj ihb =>
      intro own₁ own₂ ν' hν hO hT
      let νi' : Nm X₁ → Nm X₂ := fun m => if ownKey own m = true then νi m else ν' m
      have hagree : ∀ n ∈ relNames b₁, νi' n = νi n := by
        intro n hn
        by_cases ho : ownKey own n = true
        · simp [νi', ho]
        · have ho' : ownKey own n = false := by simpa using ho
          simp only [νi', ho', Bool.false_eq_true, if_false]
          rw [hνi n ho']
          refine hν n ?_
          simp only [relNames, List.mem_append] at hn ⊢
          rcases hn with hn | hn
          · exact Or.inl (mem_freeNames_newAct.2 ⟨hn, ho'⟩)
          · exact Or.inr (by simp [sealedFree, hn, ho'])
      have hhb : ∀ n ∈ sealedFree b₁, ownKey own n = false := fun n hn =>
        ownKey_of_holeName (fun s hs => (hr s hs).2) (hb.sealedFree_holeName n hn)
      have hb' := ihb (own₁.filter fun y => decide (y ∉ own)) own₂ νi' hagree
        (by
          intro s hs
          rw [ownKey_filter_not, hhb _ hs, Bool.not_false, Bool.and_true]
          exact hO s (by simp [sealedFree, hs, hhb _ hs]))
        (by
          intro m hm ho
          rw [ownKey_filter_not, hhb _ hm, Bool.not_false, Bool.and_true] at ho
          have e : νi' (.inst ρ m) = ν' (.inst ρ m) := by simp [νi', ownKey]
          rw [e]
          exact hT m (by simp [sealedFree, hm, hhb _ hm]) ho)
      refine .newAct (νi := νi') ?_ hr (by rw [freeParams_sealRen]; exact hℓ) hb' ?_ ?_
      · intro n hn
        simp [νi', hn]
      · intro n hn ho
        rw [freeNames_sealRen] at hn
        have e : νi' n = νi n := by simp [νi', ho]
        rw [e]
        exact hlive n hn ho
      · intro n hn n' hn' ho ho' he
        rw [freeNames_sealRen] at hn hn'
        have e : νi' n = νi n := by simp [νi', ho]
        have e' : νi' n' = νi n' := by simp [νi', ho']
        rw [e, e'] at he
        exact hinj n hn n' hn' ho ho' he


/-! ## Ground values -/

/-- The code relation is bi-unique: related pairs agree on equality. -/
def Setting.BiUnique (C : Setting S X₁ X₂) : Prop :=
  ∀ c₁ c₂ c₁' c₂', C.Q c₁ c₂ → C.Q c₁' c₂' → (c₁ = c₁' ↔ c₂ = c₂')

/-- **`holeRead` separates the hole copies in `A`.** -/
def HoleInj (C : Setting S X₁ X₂) (ν : Nm X₁ → Nm X₂) (A : Set (Nm X₁)) : Prop :=
  ∀ n ∈ A, ∀ n' ∈ A, holeCopy C n → holeCopy C n' → holeRead C ν n = holeRead C ν n' → n = n'

/-- Every hole of `t` is a name as written, or lies in `A`. -/
def CopiesIn (A : Set (Nm X₁)) (t : Tm S X₁) : Prop :=
  ∀ n ∈ codeVars t, (∃ s, n = .src s) ∨ n ∈ A

omit [DecidableEq X₁] [DecidableEq X₂] in
/-- A name of code in the code form is a name as written, or a hole copy among the
holes. -/
theorem CodeForm.name_cases {c : Tm S X₁} (hf : CodeForm C c) {n : Nm X₁}
    (hn : n ∈ codeNames c) : (∃ s, n = .src s) ∨ (holeCopy C n ∧ n ∈ codeVars c) := by
  rcases (mem_codeNames c).1 hn with hv | hb
  · cases n with
    | src s => exact Or.inl ⟨s, rfl⟩
    | inst ρ m =>
        refine Or.inr ⟨?_, hv⟩
        have h := hf.2.1 _ hv
        cases m with
        | src s => exact h
        | inst _ _ => exact h.elim
  · exact Or.inl (hf.2.2 n hb)

omit [DecidableEq X₁] [DecidableEq X₂] in
/-- **`holeRead` is injective on the names of two pieces of code** in the code form
whose hole copies it separates. -/
theorem holeRead_injOn {ν : Nm X₁ → Nm X₂} {A : Set (Nm X₁)} (hI : HoleInj C ν A)
    {c c' : Tm S X₁} (hf : CodeForm C c) (hf' : CodeForm C c') (hA : CopiesIn A c)
    (hA' : CopiesIn A c') :
    Set.InjOn (holeRead C ν) {n | n ∈ codeNames c ∨ n ∈ codeNames c'} := by
  have hcl : ∀ n, (n ∈ codeNames c ∨ n ∈ codeNames c') →
      (∃ s, n = .src s) ∨ (holeCopy C n ∧ n ∈ A) := by
    intro n hn
    rcases hn with hn | hn
    · rcases hf.name_cases hn with h | ⟨hc, hv⟩
      · exact Or.inl h
      · rcases hA n hv with h | h
        · exact Or.inl h
        · exact Or.inr ⟨hc, h⟩
    · rcases hf'.name_cases hn with h | ⟨hc, hv⟩
      · exact Or.inl h
      · rcases hA' n hv with h | h
        · exact Or.inl h
        · exact Or.inr ⟨hc, h⟩
  have hsi : ∀ (s : X₁) (b : Nm X₁), holeCopy C b → holeRead C ν (.src s) ≠ holeRead C ν b := by
    intro s b hb e
    obtain ⟨s₀, hs₀⟩ := C.codeMap_src s
    cases b with
    | src _ => exact hb
    | inst ρ m => simp [holeRead, hs₀] at e
  intro a ha b hb e
  rcases hcl a ha with ⟨s, rfl⟩ | ⟨hca, haA⟩ <;> rcases hcl b hb with ⟨s', rfl⟩ | ⟨hcb, hbA⟩
  · exact C.codeMap_inj e
  · exact absurd e (hsi s b hcb)
  · exact absurd e.symm (hsi s' a hca)
  · exact hI a haA b hbA hca hcb e

omit [DecidableEq X₁] [DecidableEq X₂] in
/-- **Related ground values agree on equality**, when `holeRead` separates their hole
copies. -/
theorem GRel.eq_iff {ν : Nm X₁ → Nm X₂} {A : Set (Nm X₁)} (hI : HoleInj C ν A)
    {g₁ : GVal S X₁} {g₂ : GVal S X₂} (h : GRel C ν g₁ g₂) :
    CopiesIn A g₁.toTm → ∀ {g₁' : GVal S X₁} {g₂' : GVal S X₂}, GRel C ν g₁' g₂' →
      CopiesIn A g₁'.toTm → (g₁ = g₁' ↔ g₂ = g₂') := by
  induction h with
  | sym s =>
      intro _ g₁' g₂' h' _
      cases h' <;> simp
  | app _ _ ihf iha =>
      intro hA g₁' g₂' h' hA'
      cases h' with
      | app hf' ha' =>
          simp only [CopiesIn, GVal.toTm, codeVars, List.mem_append] at hA hA'
          simp [ihf (fun n hn => hA n (Or.inl hn)) hf' (fun n hn => hA' n (Or.inl hn)),
            iha (fun n hn => hA n (Or.inr hn)) ha' (fun n hn => hA' n (Or.inr hn))]
      | sym _ => simp
      | quote _ => simp
      | ctx _ _ _ => simp
  | quote hq =>
      intro hA g₁' g₂' h' hA'
      cases h' with
      | quote hq' =>
          obtain ⟨-, hf, rfl⟩ := hq
          obtain ⟨-, hf', rfl⟩ := hq'
          simp only [GVal.quote.injEq]
          constructor
          · rintro rfl
            rfl
          · exact mapCode_injOn_ownNil hf.1 hf'.1
              (holeRead_injOn hI hf hf' (fun n hn => hA n (by simpa [GVal.toTm, codeVars] using hn))
                (fun n hn => hA' n (by simpa [GVal.toTm, codeVars] using hn)))
      | sym _ => simp
      | app _ _ => simp
      | ctx _ _ _ => simp
  | ctx hf hks hc =>
      intro hA g₁' g₂' h' hA'
      cases h' with
      | ctx hf' hks' hc' =>
          subst hks'; subst hc'; subst hks; subst hc
          simp only [GVal.ctx.injEq]
          have hinj := holeRead_injOn hI hf hf'
            (fun n hn => hA n (by simpa [GVal.toTm, codeVars] using hn))
            (fun n hn => hA' n (by simpa [GVal.toTm, codeVars] using hn))
          constructor
          · rintro ⟨rfl, rfl⟩
            exact ⟨rfl, rfl⟩
          · rintro ⟨hk, hb⟩
            refine ⟨list_map_injOn (fun a ha a' ha' e => hinj ?_ ?_ e) hk,
              mapCode_injOn_ownNil hf.1 hf'.1 (fun a ha a' ha' e => hinj ?_ ?_ e) hb⟩
            · rcases ha with ha | ha
              · exact Or.inl (by simp [codeNames, ha])
              · exact Or.inr (by simp [codeNames, ha])
            · rcases ha' with ha' | ha'
              · exact Or.inl (by simp [codeNames, ha'])
              · exact Or.inr (by simp [codeNames, ha'])
            · rcases ha with ha | ha
              · exact Or.inl (by simp [codeNames, ha])
              · exact Or.inr (by simp [codeNames, ha])
            · rcases ha' with ha' | ha'
              · exact Or.inl (by simp [codeNames, ha'])
              · exact Or.inr (by simp [codeNames, ha'])
      | sym _ => simp
      | app _ _ => simp
      | quote _ => simp

/-- A ground value is related to a related ground value as a term. -/
theorem GRel.toTm {ν : Nm X₁ → Nm X₂} {g₁ : GVal S X₁} {g₂ : GVal S X₂} (h : GRel C ν g₁ g₂)
    (μ : Nm X₁ → Nm X₂) (k : Kd) : Rel C ν μ k [] true g₁.toTm g₂.toTm := by
  induction h with
  | sym s => exact .sym s
  | app _ _ ihf iha => exact .app ihf iha
  | quote hq => exact .quote hq
  | ctx ho hks hc => exact .ctx ho hks hc

omit [DecidableEq X₁] [DecidableEq X₂] in
/-- **Related ground values depend on the name map only at their hole copies.** -/
theorem GRel.congr {ν ν' : Nm X₁ → Nm X₂} {g₁ : GVal S X₁} {g₂ : GVal S X₂}
    (h : GRel C ν g₁ g₂) :
    (∀ n ∈ codeVars g₁.toTm, (∃ s, n = .src s) ∨ ν n = ν' n) → GRel C ν' g₁ g₂ := by
  induction h with
  | sym s => intro _; exact .sym s
  | app _ _ ihf iha =>
      intro hν
      simp only [GVal.toTm, codeVars, List.mem_append] at hν
      exact .app (ihf fun n hn => hν n (Or.inl hn)) (iha fun n hn => hν n (Or.inr hn))
  | quote hq =>
      intro hν
      exact .quote (hq.congr fun n hn => hν n (by simpa [GVal.toTm, codeVars] using hn))
  | ctx hf hks hc =>
      intro hν
      obtain ⟨e₁, e₂⟩ := ctx_congr hf (ν' := ν') fun n hn =>
        hν n (by simpa [GVal.toTm, codeVars] using hn)
      exact .ctx hf (hks.trans e₁) (hc.trans e₂)

/-- **Related values read back as related ground values.** -/
theorem Rel.toGVal? {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂}
    (h : Rel C ν μ .val Res ok t₁ t₂) : OptRel (GRel C ν) t₁.toGVal? t₂.toGVal? := by
  generalize hk : Kd.val = k at h
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
  | letP hk' => exact absurd hk.symm hk'
  | alt hk' => exact absurd hk.symm hk'
  | lam => trivial
  | letAct hk' => exact absurd hk.symm hk'
  | newAct => cases hk

/-! ## Tracked sealed code -/

/-- **The names of sealed code in play are tracked**: each free name of the sealed
code of `t` lies in `D`, or is a root name as written. -/
def SealOK (C : Setting S X₁ X₂) (D : Set (Nm X₁)) (t : Tm S X₁) : Prop :=
  ∀ n ∈ sealedFree t, n ∈ D ∨ ∃ s, n = .src s ∧ C.root₁ s

omit [DecidableEq X₂] in
theorem SealOK.mono {D D' : Set (Nm X₁)} {t : Tm S X₁} (h : SealOK C D t) (hD : D ⊆ D') :
    SealOK C D' t := fun n hn => (h n hn).imp_left (@hD n)

omit [DecidableEq X₂] in
/-- A tracked sealed name may occur free. -/
theorem SealOK.ok₁ {D : Set (Nm X₁)} {t : Tm S X₁} (h : SealOK C D t) (hok : ∀ n ∈ D, OK₁ C n) :
    ∀ n ∈ sealedFree t, OK₁ C n := by
  intro n hn
  rcases h n hn with hD | ⟨s, rfl, hs⟩
  · exact hok n hD
  · exact hs

omit [DecidableEq X₂] in
/-- The sealed code of a ground value is all of its code. -/
theorem sealedFree_toTm : ∀ g : GVal S X₁, sealedFree g.toTm = codeVars g.toTm
  | .sym _ => rfl
  | .app f a => by simp only [GVal.toTm, sealedFree, codeVars, sealedFree_toTm f, sealedFree_toTm a]
  | .quote _ => rfl
  | .ctx _ _ => rfl

omit [DecidableEq X₂] in
theorem SealOK.copiesIn_toTm {D : Set (Nm X₁)} {g : GVal S X₁} (h : SealOK C D g.toTm) :
    CopiesIn D g.toTm := by
  intro n hn
  rcases h n (by rw [sealedFree_toTm]; exact hn) with hD | ⟨s, rfl, -⟩
  · exact Or.inr hD
  · exact Or.inl ⟨s, rfl⟩

/-! ## Stores -/

/-- **Stores related along `ν` on the names `D`**: bindings correspond, the
first store binds only names in `D`, the second binds only their images, and the
sealed code of every stored value is tracked. -/
structure StoreRel (C : Setting S X₁ X₂) (ν : Nm X₁ → Nm X₂) (D : Set (Nm X₁))
    (σ₁ : GStore S X₁) (σ₂ : GStore S X₂) : Prop where
  rel : ∀ n ∈ D, OptRel (GRel C ν) (σ₁ n) (σ₂ (ν n))
  dom : ∀ n, σ₁ n ≠ none → n ∈ D
  only : ∀ m, σ₂ m ≠ none → ∃ n ∈ D, ν n = m
  sealOK : ∀ n g, σ₁ n = some g → SealOK C D g.toTm

omit [DecidableEq X₂] in
theorem StoreRel.empty (ν : Nm X₁ → Nm X₂) (D : Set (Nm X₁)) :
    StoreRel C ν D (Store.empty : GStore S X₁) (Store.empty : GStore S X₂) where
  rel _ _ := trivial
  dom _ h := absurd rfl h
  only _ h := absurd rfl h
  sealOK _ _ h := by simp [Store.empty] at h

omit [DecidableEq X₂] in
theorem StoreRel.mono {ν ν' : Nm X₁ → Nm X₂} {D D' : Set (Nm X₁)} {σ₁ : GStore S X₁}
    {σ₂ : GStore S X₂} (h : StoreRel C ν D σ₁ σ₂) (hD : D ⊆ D') (hν : ∀ n ∈ D, ν' n = ν n)
    (hnew : ∀ n ∈ D', n ∉ D → σ₁ n = none ∧ σ₂ (ν' n) = none) : StoreRel C ν' D' σ₁ σ₂ where
  rel n hn := by
    by_cases hnD : n ∈ D
    · rw [hν n hnD]
      rcases OptRel.cases (h.rel n hnD) with ⟨e1, e2⟩ | ⟨g₁, g₂, e1, e2, hg⟩
      · rw [e1, e2]; trivial
      · rw [e1, e2]
        refine hg.congr fun m hm => ?_
        rcases h.sealOK n g₁ e1 m (by rw [sealedFree_toTm]; exact hm) with hmD | ⟨s, rfl, -⟩
        · exact Or.inr (hν m hmD).symm
        · exact Or.inl ⟨s, rfl⟩
    · obtain ⟨e1, e2⟩ := hnew n hn hnD
      rw [e1, e2]; trivial
  dom n hn := hD (h.dom n hn)
  only m hm := by
    obtain ⟨n, hnD, rfl⟩ := h.only m hm
    exact ⟨n, hD hnD, hν n hnD⟩
  sealOK n g hg := (h.sealOK n g hg).mono hD

/-! ## Matching -/

theorem freeNames_toTm {Y : Type v} [DecidableEq Y] : ∀ g : GVal S Y, freeNames g.toTm = []
  | .sym _ => rfl
  | .app f a => by simp [GVal.toTm, freeNames, freeNames_toTm f, freeNames_toTm a]
  | .quote _ => rfl
  | .ctx _ _ => rfl

theorem freeParams_toTm {Y : Type v} [DecidableEq Y] : ∀ g : GVal S Y, freeParams g.toTm = []
  | .sym _ => rfl
  | .app f a => by simp [GVal.toTm, freeParams, freeParams_toTm f, freeParams_toTm a]
  | .quote _ => rfl
  | .ctx _ _ => rfl

theorem GVal.toTm_ne_var {Y : Type v} (g : GVal S Y) (n : Nm Y) : g.toTm ≠ .var n := by
  cases g <;> simp [GVal.toTm]

variable [DecidableEq S]

/-- One refinement step, on related stores and related values, at a name in
`D` where `ν` is injective and `holeRead` separates the hole copies. -/
theorem StoreRel.refine {ν : Nm X₁ → Nm X₂} {D : Set (Nm X₁)} (hI : HoleInj C ν D)
    (hinj : Set.InjOn ν D) {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} (h : StoreRel C ν D σ₁ σ₂)
    {n : Nm X₁} (hn : n ∈ D) {g₁ : GVal S X₁} {g₂ : GVal S X₂} (hg : GRel C ν g₁ g₂)
    (hgs : SealOK C D g₁.toTm) :
    OptRel (StoreRel C ν D) (refineStep σ₁ (n, g₁)) (refineStep σ₂ (ν n, g₂)) := by
  have hr := h.rel n hn
  unfold SequentialBindingDiscipline.refineStep
  rcases OptRel.cases hr with ⟨e1, e2⟩ | ⟨w₁, w₂, e1, e2, hw⟩
  · simp only [e1, e2]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro m hm
      by_cases hmn : m = n
      · subst hmn
        simp only [if_true]
        exact hg
      · have hνm : ν m ≠ ν n := fun e => hmn (hinj hm hn e)
        simp only [hmn, hνm, if_false]
        exact h.rel m hm
    · intro m hm
      by_cases hmn : m = n
      · subst hmn; exact hn
      · simp only [hmn, if_false] at hm
        exact h.dom m hm
    · intro m hm
      by_cases hmn : m = ν n
      · exact ⟨n, hn, hmn.symm⟩
      · simp only [hmn, if_false] at hm
        exact h.only m hm
    · intro m g hm
      by_cases hmn : m = n
      · subst hmn
        simp only [if_true, Option.some.injEq] at hm
        subst hm
        exact hgs
      · simp only [hmn, if_false] at hm
        exact h.sealOK m g hm
  · simp only [e1, e2]
    have hiff := hw.eq_iff hI (h.sealOK n w₁ e1).copiesIn_toTm hg hgs.copiesIn_toTm
    by_cases heq : w₁ = g₁
    · have heq2 : w₂ = g₂ := hiff.1 heq
      simp only [heq, heq2, if_true]
      exact h
    · have heq2 : ¬ w₂ = g₂ := fun e => heq (hiff.2 e)
      simp only [heq, heq2, if_false]
      trivial

variable [CodeId X₁] [CodeId X₂]

/-- **Related sealed code agrees under `codeEq`**, when `holeRead` is injective on
the names of the two pieces of code compared. Structural equality of code is the
special case of the default comparison; a model that stores binder positions
compares those positions. -/
def Setting.CodeAgree (C : Setting S X₁ X₂) : Prop :=
  ∀ (ν : Nm X₁ → Nm X₂) (c₁ : Tm S X₁) (c₂ : Tm S X₂) (c₁' : Tm S X₁) (c₂' : Tm S X₂),
    QR C ν c₁ c₂ → QR C ν c₁' c₂' →
    Set.InjOn (holeRead C ν) {n | n ∈ codeNames c₁ ∨ n ∈ codeNames c₁'} →
    (codeEq c₁ c₁' = true ↔ codeEq c₂ c₂' = true)

/-- Related pattern code matches related quotations on both sides together.
The code is stable and of one weak shape. A hole binds a ground value; a
binder of the code is compared by `CodeId`. The sealed code in play is
tracked, and `holeRead` separates its hole copies. -/
def Setting.PatAgree (C : Setting S X₁ X₂) : Prop :=
  ∀ {ν μ : Nm X₁ → Nm X₂} {ok : Bool} {c₁ : Tm S X₁} {c₂ : Tm S X₂}
    {q₁ : Tm S X₁} {q₂ : Tm S X₂}
    {D : Set (Nm X₁)} {σ₁ : GStore S X₁} {σ₂ : GStore S X₂},
    Rel C ν μ .code [] ok c₁ c₂ →
    ok = true →
    ShapeParallel C ν c₁ c₂ →
    QR C ν q₁ q₂ →
    (∀ n ∈ freeNames c₁, n ∈ D) →
    Set.InjOn ν D →
    HoleInj C ν D →
    SealOK C D c₁ →
    SealOK C D (.quote q₁) →
    StoreRel C ν D σ₁ σ₂ →
    OptRel (StoreRel C ν D) (matchCode σ₁ c₁ q₁) (matchCode σ₂ c₂ q₂)

/-- **Related patterns match related ground values alike**, with related
stores. Two quotations match when `codeEq` says they are the same code. A
pattern quotation matches the quoted code by `matchCode`. -/
theorem Rel.matchT (hC : C.CodeAgree) (hP : C.PatAgree) {ν μ : Nm X₁ → Nm X₂}
    {ok : Bool} {Res : List (Nm X₂)}
    {p₁ : Tm S X₁} {p₂ : Tm S X₂} (h : Rel C ν μ .pat Res ok p₁ p₂) {D : Set (Nm X₁)}
    (hD : ∀ n ∈ freeNames p₁, n ∈ D) (hinj : Set.InjOn ν D) (hI : HoleInj C ν D)
    (hpS : SealOK C D p₁) :
    ∀ {g₁ : GVal S X₁} {g₂ : GVal S X₂}, GRel C ν g₁ g₂ → SealOK C D g₁.toTm →
      ∀ {σ₁ : GStore S X₁} {σ₂ : GStore S X₂}, StoreRel C ν D σ₁ σ₂ →
      OptRel (StoreRel C ν D) (TemplateScope.matchT σ₁ p₁ g₁.toTm)
        (TemplateScope.matchT σ₂ p₂ g₂.toTm) := by
  generalize hk : Kd.pat = k at h
  induction h with
  | sym s =>
      intro g₁ g₂ hg _ σ₁ σ₂ hσ
      have e1 : TemplateScope.matchT σ₁ (.sym s) g₁.toTm =
          if Tm.sym s = g₁.toTm then some σ₁ else none := by cases g₁ <;> rfl
      have e2 : TemplateScope.matchT σ₂ (.sym s) g₂.toTm =
          if Tm.sym s = g₂.toTm then some σ₂ else none := by cases g₂ <;> rfl
      rw [e1, e2]
      have hiff : (Tm.sym s : Tm S X₁) = g₁.toTm ↔ (Tm.sym s : Tm S X₂) = g₂.toTm := by
        cases hg <;> simp [GVal.toTm]
      by_cases hs : (Tm.sym s : Tm S X₁) = g₁.toTm
      · rw [if_pos hs, if_pos (hiff.1 hs)]; exact hσ
      · rw [if_neg hs, if_neg (fun e => hs (hiff.2 e))]; trivial
  | fn F =>
      intro g₁ g₂ hg _ σ₁ σ₂ hσ
      have e1 : TemplateScope.matchT σ₁ (.fn F) g₁.toTm = none := by cases g₁ <;> rfl
      have e2 : TemplateScope.matchT σ₂ (.fn F) g₂.toTm = none := by cases g₂ <;> rfl
      rw [e1, e2]; trivial
  | var n _ =>
      intro g₁ g₂ hg hgs σ₁ σ₂ hσ
      simp only [TemplateScope.matchT, GVal.toTm_toGVal?]
      exact hσ.refine hI hinj (hD n (by simp [freeNames])) hg hgs
  | @pvar ν' μ' k' x _ =>
      intro g₁ g₂ hg _ σ₁ σ₂ hσ
      have e1 : TemplateScope.matchT σ₁ (.pvar x) g₁.toTm = none := by cases g₁ <;> rfl
      have e2 : TemplateScope.matchT σ₂ (.pvar (μ' x)) g₂.toTm = none := by cases g₂ <;> rfl
      rw [e1, e2]; trivial
  | @quote ν μ k c₁ c₂ hq =>
      intro g₁ g₂ hg hgs σ₁ σ₂ hσ
      cases g₁ with
      | sym _ =>
          cases hg
          simp [GVal.toTm, TemplateScope.matchT]
          trivial
      | app _ _ =>
          cases hg
          simp [GVal.toTm, TemplateScope.matchT]
          trivial
      | ctx _ _ =>
          cases hg
          simp [GVal.toTm, TemplateScope.matchT]
          trivial
      | quote q₁ =>
          cases g₂ with
          | sym _ => cases hg
          | app _ _ => cases hg
          | ctx _ _ => cases hg
          | quote q₂ =>
              cases hg with
              | quote hq' =>
                  have hinjq := holeRead_injOn hI hq.2.1 hq'.2.1
                    (fun n hn => (hpS n (by simpa [sealedFree] using hn)).elim Or.inr
                      fun ⟨s, e, _⟩ => Or.inl ⟨s, e⟩)
                    (fun n hn => (hgs n (by simpa [GVal.toTm, sealedFree] using hn)).elim Or.inr
                      fun ⟨s, e, _⟩ => Or.inl ⟨s, e⟩)
                  simp only [GVal.toTm, TemplateScope.matchT]
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
  | @pquote ν μ k c₁ c₂ _ hbody hp hok =>
      intro g₁ g₂ hg hgs σ₁ σ₂ hσ
      cases g₁ with
      | sym _ =>
          cases hg
          simp [GVal.toTm, TemplateScope.matchT]
          trivial
      | app _ _ =>
          cases hg
          simp [GVal.toTm, TemplateScope.matchT]
          trivial
      | ctx _ _ =>
          cases hg
          simp [GVal.toTm, TemplateScope.matchT]
          trivial
      | quote q₁ =>
          cases g₂ with
          | sym _ => cases hg
          | app _ _ => cases hg
          | ctx _ _ => cases hg
          | quote q₂ =>
              cases hg with
              | quote hq =>
                  simp only [GVal.toTm, TemplateScope.matchT]
                  exact hP hbody hok hp hq (fun n hn => hD n (by simp [freeNames, hn])) hinj hI
                    (fun n hn => hpS n (by simpa [sealedFree] using hn)) hgs hσ
  | @app _ _ _ _ _ _ _ f₁ a₁ _ _ _ _ ihf iha =>
      intro g₁ g₂ hg hgs σ₁ σ₂ hσ
      simp only [freeNames, List.mem_append] at hD
      have hpS₁ : SealOK C D f₁ := fun n hn => hpS n (by simp [sealedFree, hn])
      have hpS₂ : SealOK C D a₁ := fun n hn => hpS n (by simp [sealedFree, hn])
      cases hg with
      | @app gf ga _ _ hf ha =>
          have hgs₁ : SealOK C D gf.toTm := fun n hn => hgs n (by simp [GVal.toTm, sealedFree, hn])
          have hgs₂ : SealOK C D ga.toTm := fun n hn => hgs n (by simp [GVal.toTm, sealedFree, hn])
          simp only [GVal.toTm, TemplateScope.matchT]
          rcases OptRel.cases (ihf (fun n h => hD n (Or.inl h)) hinj hI hpS₁ hk hf hgs₁ hσ) with
              ⟨e1, e2⟩ | ⟨τ₁, τ₂, e1, e2, hτ⟩
          · rw [e1, e2]; trivial
          · rw [e1, e2]
            exact iha (fun n h => hD n (Or.inr h)) hinj hI hpS₂ hk ha hgs₂ hτ
      | sym s => simp [GVal.toTm, TemplateScope.matchT]; trivial
      | quote _ => simp [GVal.toTm, TemplateScope.matchT]; trivial
      | ctx _ _ _ => simp [GVal.toTm, TemplateScope.matchT]; trivial
  | letP =>
      intro g₁ g₂ hg _ σ₁ σ₂ hσ
      have e1 : ∀ (p w b : Tm S X₁), TemplateScope.matchT σ₁ (.letP p w b) g₁.toTm = none := by
        intro p w b; cases g₁ <;> rfl
      have e2 : ∀ (p w b : Tm S X₂), TemplateScope.matchT σ₂ (.letP p w b) g₂.toTm = none := by
        intro p w b; cases g₂ <;> rfl
      rw [e1, e2]; trivial
  | alt =>
      intro g₁ g₂ hg _ σ₁ σ₂ hσ
      have e1 : ∀ (t u : Tm S X₁), TemplateScope.matchT σ₁ (.alt t u) g₁.toTm = none := by
        intro t u; cases g₁ <;> rfl
      have e2 : ∀ (t u : Tm S X₂), TemplateScope.matchT σ₂ (.alt t u) g₂.toTm = none := by
        intro t u; cases g₂ <;> rfl
      rw [e1, e2]; trivial
  | lam =>
      intro g₁ g₂ hg _ σ₁ σ₂ hσ
      have e1 : ∀ x own (b : Tm S X₁), TemplateScope.matchT σ₁ (.lam x own b) g₁.toTm = none := by
        intro x own b; cases g₁ <;> rfl
      have e2 : ∀ x own (b : Tm S X₂), TemplateScope.matchT σ₂ (.lam x own b) g₂.toTm = none := by
        intro x own b; cases g₂ <;> rfl
      rw [e1, e2]; trivial
  | @ctx ν μ k ks₁ c₁ ks₂ c₂ hf hks hc =>
      intro g₁ g₂ hg hgs σ₁ σ₂ hσ
      have e1 : TemplateScope.matchT σ₁ (.ctx ks₁ c₁) g₁.toTm =
          if Tm.ctx ks₁ c₁ = g₁.toTm then some σ₁ else none := by cases g₁ <;> rfl
      have e2 : TemplateScope.matchT σ₂ (.ctx ks₂ c₂) g₂.toTm =
          if Tm.ctx ks₂ c₂ = g₂.toTm then some σ₂ else none := by cases g₂ <;> rfl
      rw [e1, e2]
      have hiff : (Tm.ctx ks₁ c₁ = g₁.toTm) ↔ (Tm.ctx ks₂ c₂ = g₂.toTm) := by
        cases hg with
        | @ctx ks₁' c₁' ks₂' c₂' hf' hks' hc' =>
            have hiffg := (GRel.ctx (C := C) (ν := ν) hf hks hc).eq_iff hI
              (fun n hn => (hpS n (by simpa [GVal.toTm, codeVars, sealedFree] using hn)).elim
                Or.inr fun ⟨s, e, _⟩ => Or.inl ⟨s, e⟩)
              (GRel.ctx hf' hks' hc') (SealOK.copiesIn_toTm hgs)
            simp only [GVal.toTm]
            constructor
            · intro e
              simp only [Tm.ctx.injEq] at e
              have := hiffg.1 (by rw [e.1, e.2])
              simp only [GVal.ctx.injEq] at this
              rw [this.1, this.2]
            · intro e
              simp only [Tm.ctx.injEq] at e
              have := hiffg.2 (by rw [e.1, e.2])
              simp only [GVal.ctx.injEq] at this
              rw [this.1, this.2]
        | sym _ =>
            constructor <;> intro heq <;> cases heq
        | app _ _ =>
            constructor <;> intro heq <;> cases heq
        | quote _ =>
            constructor <;> intro heq <;> cases heq
      by_cases hs : Tm.ctx ks₁ c₁ = g₁.toTm
      · rw [if_pos hs, if_pos (hiff.1 hs)]; exact hσ
      · rw [if_neg hs, if_neg (fun e => hs (hiff.2 e))]; trivial
  | letAct =>
      intro g₁ g₂ hg _ σ₁ σ₂ hσ
      have e2 : ∀ (p w b : Tm S X₂), TemplateScope.matchT σ₂ (.letP p w b) g₂.toTm = none := by
        intro p w b; cases g₂ <;> rfl
      rw [e2]
      cases g₁ with
      | app gf ga =>
          have e : ∀ x own (b : Tm S X₁), TemplateScope.matchT σ₁ (.lam x own b) gf.toTm = none := by
            intro x own b; cases gf <;> rfl
          have e' : ∀ x own (b w : Tm S X₁),
              TemplateScope.matchT σ₁ (.app (.lam x own b) w) (GVal.app gf ga).toTm = none := by
            intro x own b w
            show (match TemplateScope.matchT σ₁ (.lam x own b) gf.toTm with
              | some σ' => TemplateScope.matchT σ' w ga.toTm | none => none) = none
            rw [e]
          rw [e']
          trivial
      | sym s => exact trivial
      | quote c => exact trivial
      | ctx _ _ =>
          cases hg
          exact trivial
  | newAct => cases hk

omit [DecidableEq S] [CodeId X₁] [CodeId X₂] in
/-- **Applying related stores to related terms gives related terms.** -/
theorem Rel.applyStore {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂}
    (h : Rel C ν μ k Res ok t₁ t₂) {D : Set (Nm X₁)} (hD : ∀ n ∈ freeNames t₁, n ∈ D)
    {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} (hσ : StoreRel C ν D σ₁ σ₂)
    (hok : ∀ n ∈ D, OK₁ C n) (hres : ∀ m ∈ Res, σ₂ m = none) :
    Rel C ν μ k Res ok (TemplateScope.act σ₁ t₁) (TemplateScope.act σ₂ t₂) := by
  have h' := h.substitute (θ₁ := envSub σ₁) (φ₁ := Sub.none) (θ₂ := envSub σ₂) (φ₂ := Sub.none)
    (ν' := ν) (μ' := μ) (rn := id) {
      names := by
        intro n hn
        rcases OptRel.cases (hσ.rel n (hD n hn)) with ⟨e1, e2⟩ | ⟨g₁, g₂, e1, e2, hg⟩
        · simp only [envSub, e1, e2, Option.map_none, Option.getD_none]
          exact .var n (h.varHole_free hn)
        · simp only [envSub, e1, e2, Option.map_some, Option.getD_some]
          exact hg.toTm μ .val
      params := by
        intro x hx
        exact .pvar x (h.parOK_free hx)
      res := by
        intro m hm
        simp [envSub, hres m hm]
      resInj := fun _ _ _ _ h => h
      rnPres := C.preserve_refl
      cap₁ := by
        intro n _ w hw
        simp only [envSub, Option.map_eq_some_iff] at hw
        obtain ⟨g, -, rfl⟩ := hw
        exact ⟨by simp [freeNames_toTm], freeParams_toTm g⟩
      capφ₁ := by
        intro x _ w hw
        cases hw
      cap₂ := by
        intro n _ w hw
        simp only [envSub, Option.map_eq_some_iff] at hw
        obtain ⟨g, -, rfl⟩ := hw
        exact ⟨by simp [freeNames_toTm], freeParams_toTm g⟩
      capφ₂ := by
        intro x _ w hw
        cases hw
      capR := by
        intro m hm w hw
        simp [envSub, hres m hm] at hw
      sealed := fun _ _ => Or.inr rfl
      sealCap₁ := by
        intro n _ w hw
        simp only [envSub, Option.map_eq_some_iff] at hw
        obtain ⟨g, hg, rfl⟩ := hw
        exact (hσ.sealOK n g hg).ok₁ hok
      sealCapφ₁ := by
        intro x _ w hw
        cases hw }
  simpa [TemplateScope.act] using h'

end IdSlot

end Mettapedia.GSLT.LanguageDef.TemplateScope
