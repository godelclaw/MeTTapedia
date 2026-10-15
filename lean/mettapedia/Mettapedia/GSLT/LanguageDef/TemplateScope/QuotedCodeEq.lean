import Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFresh

/-!
# Code equality agrees for the two name disciplines

A binder inside quoted code is compared by its quotation-relative position, and
a free parameter by its spelling. The slot model stores that position as the
owner of a slot; the identity model stores it on a code name. `codeEq` gives
the same answer either way.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v

variable {S : Type u} {X : Type v} [DecidableEq S] [DecidableEq X]

omit [DecidableEq S] [DecidableEq X] in
private theorem decide_eq_of_iff {p q : Prop} [Decidable p] [Decidable q]
    (h : p ↔ q) : decide p = decide q := by
  by_cases hp : p
  · rw [decide_eq_true hp, decide_eq_true (h.mp hp)]
  · rw [decide_eq_false hp, decide_eq_false (fun hq => hp (h.mpr hq))]

omit [DecidableEq S] in
/-- A slot `(owner, spelling)` and the code name of that spelling at that
owner are the same name to `CodeId`. -/
private theorem same_slot_code (o₁ o₂ : Owner) (y₁ y₂ : X) :
    CodeId.same (.src (o₁, y₁) : Nm (Slot X)) (.src (o₂, y₂)) =
      CodeId.same (.src (.code y₁ o₁) : Nm (BId X)) (.src (.code y₂ o₂)) := by
  have hiff :
      ((.src (o₁, y₁) : Nm (Slot X)) = .src (o₂, y₂)) ↔
        ((.src (.code y₁ o₁) : Nm (BId X)) = .src (.code y₂ o₂)) := by
    simp only [Nm.src.injEq, Prod.mk.injEq, BId.code.injEq]
    exact and_comm
  simp only [CodeId.same]
  by_cases hb : (codeBound o₁ && codeBound o₂) = true
  · simp_rw [hb]; rfl
  · have hb' : (codeBound o₁ && codeBound o₂) = false := Bool.eq_false_iff.mpr hb
    simp_rw [hb']
    by_cases hf : (decide (o₁ = codeFreeParam) && decide (o₂ = codeFreeParam)) = true
    · simp_rw [hf]; rfl
    · have hf' : (decide (o₁ = codeFreeParam) && decide (o₂ = codeFreeParam)) = false :=
        Bool.eq_false_iff.mpr hf
      simp_rw [hf']
      exact decide_eq_of_iff hiff

omit [DecidableEq S] [DecidableEq X] in
/-- A slot read as an identity: a name of code (a binder, or a free parameter)
keeps its owner as a code name; any other owner is a scope's head slot, so a
hole of sealed code is the head slot of the form that wrote the code. -/
private def codeFwd : Nm (Slot X) → Nm (BId X)
  | .src (o, y) =>
      if codeBound o = true ∨ o = codeFreeParam then .src (.code y o)
      else .src (.slot ⟨y, o, o, .head⟩)
  | .inst ρ n => .inst ρ (codeFwd n)

omit [DecidableEq S] [DecidableEq X] in
private def codeBack : Nm (BId X) → Nm (Slot X)
  | .src (.slot k) => .src (k.frame, k.spell)
  | .src (.code y o) => .src (o, y)
  | .src (.par z _) => .src ([], z)
  | .inst ρ n => .inst ρ (codeBack n)

omit [DecidableEq S] [DecidableEq X] in
private theorem codeFwd_code {o : Owner} {y : X} (h : codeBound o = true ∨ o = codeFreeParam) :
    codeFwd (.src (o, y)) = .src (.code y o) := by
  simp only [codeFwd, if_pos h]

omit [DecidableEq S] [DecidableEq X] in
private theorem codeFwd_scope {o : Owner} {y : X}
    (h : ¬ (codeBound o = true ∨ o = codeFreeParam)) :
    codeFwd (.src (o, y)) = .src (.slot ⟨y, o, o, .head⟩) := by
  simp only [codeFwd, if_neg h]

omit [DecidableEq S] [DecidableEq X] in
private theorem codeBack_codeFwd : ∀ n : Nm (Slot X), codeBack (codeFwd n) = n
  | .src (o, y) => by
      by_cases h : codeBound o = true ∨ o = codeFreeParam
      · rw [codeFwd_code h]
        rfl
      · rw [codeFwd_scope h]
        rfl
  | .inst _ n => by simp only [codeFwd, codeBack, codeBack_codeFwd n]

omit [DecidableEq S] [DecidableEq X] in
private theorem codeFwd_eq_iff (n₁ n₂ : Nm (Slot X)) :
    codeFwd n₁ = codeFwd n₂ ↔ n₁ = n₂ := by
  constructor
  · intro h
    rw [← codeBack_codeFwd n₁, h, codeBack_codeFwd]
  · exact fun h => congrArg codeFwd h

omit [DecidableEq S] [DecidableEq X] in
private theorem codeFwd_binder (pos : Owner) (z : X) :
    codeFwd (.src (codeBinder pos, z)) = .src (.code z (codeBinder pos)) :=
  codeFwd_code (Or.inl rfl)

omit [DecidableEq S] in
/-- Two slots that are not both names of code compare as written. -/
private theorem same_slot_plain {o₁ o₂ : Owner} {y₁ y₂ : X}
    (h : ¬ (codeBound o₁ = true ∨ o₁ = codeFreeParam) ∨
      ¬ (codeBound o₂ = true ∨ o₂ = codeFreeParam)) :
    CodeId.same (.src (o₁, y₁) : Nm (Slot X)) (.src (o₂, y₂)) =
      decide ((.src (o₁, y₁) : Nm (Slot X)) = .src (o₂, y₂)) := by
  have hb : (codeBound o₁ && codeBound o₂) = false := by
    rcases h with h | h
    · have h' : codeBound o₁ = false := by
        cases hc : codeBound o₁
        · rfl
        · exact absurd (Or.inl hc) h
      rw [h', Bool.false_and]
    · have h' : codeBound o₂ = false := by
        cases hc : codeBound o₂
        · rfl
        · exact absurd (Or.inl hc) h
      rw [h', Bool.and_false]
  have hf : (decide (o₁ = codeFreeParam) && decide (o₂ = codeFreeParam)) = false := by
    rcases h with h | h
    · rw [decide_eq_false (fun e => h (Or.inr e)), Bool.false_and]
    · rw [decide_eq_false (fun e => h (Or.inr e)), Bool.and_false]
  simp only [CodeId.same]
  simp_rw [hb, hf]
  rfl

omit [DecidableEq S] in
/-- An identity slot compares as written, on either side. -/
private theorem same_slot_left (k : SlotId X) (b : Nm (BId X)) :
    CodeId.same (.src (.slot k) : Nm (BId X)) b = decide (.src (.slot k) = b) := by
  cases b with
  | src b => cases b <;> rfl
  | inst _ _ => rfl

omit [DecidableEq S] in
private theorem same_slot_right (a : Nm (BId X)) (k : SlotId X) :
    CodeId.same a (.src (.slot k) : Nm (BId X)) = decide (a = .src (.slot k)) := by
  cases a with
  | src a => cases a <;> rfl
  | inst _ _ => rfl

omit [DecidableEq S] in
/-- The images of two slots that are not both names of code compare as the
slots are written. -/
private theorem same_fwd_plain {o₁ o₂ : Owner} {y₁ y₂ : X}
    (h : ¬ (codeBound o₁ = true ∨ o₁ = codeFreeParam) ∨
      ¬ (codeBound o₂ = true ∨ o₂ = codeFreeParam)) :
    CodeId.same (codeFwd (.src (o₁, y₁))) (codeFwd (.src (o₂, y₂)) : Nm (BId X)) =
      decide ((.src (o₁, y₁) : Nm (Slot X)) = .src (o₂, y₂)) := by
  rcases h with h | h
  · rw [codeFwd_scope (y := y₁) h, same_slot_left, ← codeFwd_scope (y := y₁) h]
    exact decide_eq_of_iff (codeFwd_eq_iff _ _)
  · rw [codeFwd_scope (y := y₂) h, same_slot_right, ← codeFwd_scope (y := y₂) h]
    exact decide_eq_of_iff (codeFwd_eq_iff _ _)

omit [DecidableEq S] in
private theorem same_fwd (n₁ n₂ : Nm (Slot X)) :
    CodeId.same n₁ n₂ = CodeId.same (codeFwd n₁) (codeFwd n₂) := by
  cases n₁ with
  | src p =>
      obtain ⟨o₁, y₁⟩ := p
      cases n₂ with
      | src q =>
          obtain ⟨o₂, y₂⟩ := q
          by_cases h₁ : codeBound o₁ = true ∨ o₁ = codeFreeParam
          · by_cases h₂ : codeBound o₂ = true ∨ o₂ = codeFreeParam
            · rw [codeFwd_code h₁, codeFwd_code h₂]
              exact same_slot_code o₁ o₂ y₁ y₂
            · rw [same_slot_plain (Or.inr h₂), same_fwd_plain (Or.inr h₂)]
          · rw [same_slot_plain (Or.inl h₁), same_fwd_plain (Or.inl h₁)]
      | inst ρ m =>
          show CodeId.same (.src (o₁, y₁) : Nm (Slot X)) (.inst ρ m) =
            CodeId.same (codeFwd (.src (o₁, y₁))) (.inst ρ (codeFwd m))
          by_cases h₁ : codeBound o₁ = true ∨ o₁ = codeFreeParam
          · rw [codeFwd_code h₁]
            rfl
          · rw [codeFwd_scope h₁]
            rfl
  | inst ρ n =>
      cases n₂ with
      | src q =>
          obtain ⟨o₂, y₂⟩ := q
          show CodeId.same (.inst ρ n : Nm (Slot X)) (.src (o₂, y₂)) =
            CodeId.same (.inst ρ (codeFwd n)) (codeFwd (.src (o₂, y₂)))
          by_cases h₂ : codeBound o₂ = true ∨ o₂ = codeFreeParam
          · rw [codeFwd_code h₂]
            rfl
          · rw [codeFwd_scope h₂]
            rfl
      | inst ρ' m =>
          simp only [CodeId.same, codeFwd]
          exact decide_eq_of_iff (codeFwd_eq_iff _ _).symm

omit [DecidableEq S] [DecidableEq X] in
private def mapC {Y Z : Type v} (f : Nm Y → Nm Z) : Tm S Y → Tm S Z
  | .sym s => .sym s
  | .fn F => .fn F
  | .var n => .var (f n)
  | .pvar n => .pvar (f n)
  | .lam x _ b => .lam (f x) [] (mapC f b)
  | .app a b => .app (mapC f a) (mapC f b)
  | .quote c => .quote (mapC f c)
  | .ctx ks c => .ctx (ks.map f) (mapC f c)
  | .pquote c => .pquote (mapC f c)
  | .letP p w b => .letP (mapC f p) (mapC f w) (mapC f b)
  | .alt t₁ t₂ => .alt (mapC f t₁) (mapC f t₂)

omit [DecidableEq S] [DecidableEq X] in
/-- Every lambda produced as code has an empty own list, including under a
quotation. -/
private def ownEmpty : Tm S X → Prop
  | .lam _ own b => own = [] ∧ ownEmpty b
  | .app f a => ownEmpty f ∧ ownEmpty a
  | .quote c => ownEmpty c
  | .pquote c => ownEmpty c
  | .letP p w b => ownEmpty p ∧ ownEmpty w ∧ ownEmpty b
  | .alt t₁ t₂ => ownEmpty t₁ ∧ ownEmpty t₂
  | _ => True

omit [DecidableEq S] [DecidableEq X] in
private theorem codeFwd_injective :
    Function.Injective (codeFwd : Nm (Slot X) → Nm (BId X)) :=
  fun a b h => (codeFwd_eq_iff a b).1 h

omit [DecidableEq S] [DecidableEq X] in
private theorem ownEmpty_fold {Y : Type v} (ps : List (Nm Y)) {t : Tm S Y}
    (h : ownEmpty t) : ownEmpty (ps.foldr (fun p acc => .lam p [] acc) t) := by
  induction ps with
  | nil => exact h
  | cons _ _ ih => exact ⟨rfl, ih⟩

omit [DecidableEq S] in
private theorem ownEmpty_seal {Y : Type v} [DecidableEq Y] {t : Tm S Y}
    (h : ownEmpty t) : ownEmpty (sealParams t) := by
  unfold sealParams
  exact ownEmpty_fold _ h

omit [DecidableEq S] [DecidableEq X] in
private theorem map_filter_binder {α β : Type v} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) (x : α) (l : List α) :
    ((l.filter fun y => decide (y ≠ x)).map f) =
      ((l.map f).filter fun z => decide (z ≠ f x)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases ha : a = x
      · have hd : decide (a ≠ x) = false := decide_eq_false (fun h => h ha)
        have hdf : decide (f a ≠ f x) = false :=
          decide_eq_false (fun h => h (congrArg f ha))
        rw [List.filter_cons_of_neg (p := fun y => decide (y ≠ x))
            (by rw [hd]; exact Bool.false_ne_true),
          List.map_cons,
          List.filter_cons_of_neg (p := fun z => decide (z ≠ f x))
            (by rw [hdf]; exact Bool.false_ne_true),
          ih]
      · have hk : decide (a ≠ x) = true := decide_eq_true ha
        have hkf : decide (f a ≠ f x) = true := decide_eq_true (hf.ne ha)
        rw [List.filter_cons_of_pos (p := fun y => decide (y ≠ x)) hk,
          List.map_cons, List.map_cons,
          List.filter_cons_of_pos (p := fun z => decide (z ≠ f x)) hkf, ih]

omit [DecidableEq S] in
private theorem paramOcc_mapC {Y Z : Type v} [DecidableEq Y] [DecidableEq Z]
    {f : Nm Y → Nm Z} (hf : Function.Injective f) :
    ∀ t : Tm S Y, paramOcc (mapC f t) = (paramOcc t).map f
  | .sym _ => rfl
  | .fn _ => rfl
  | .var _ => rfl
  | .pvar _ => rfl
  | .lam x _ b => by
      simp only [mapC, paramOcc, paramOcc_mapC hf b, map_filter_binder hf x]
  | .app a b => by
      simp only [mapC, paramOcc, paramOcc_mapC hf a, paramOcc_mapC hf b, List.map_append]
  | .quote _ => rfl
  | .ctx _ _ => rfl
  | .pquote c => by
      simp only [mapC, paramOcc, paramOcc_mapC hf c]
  | .letP p w b => by
      simp only [mapC, paramOcc, paramOcc_mapC hf p, paramOcc_mapC hf w, paramOcc_mapC hf b,
        List.map_append]
  | .alt t₁ t₂ => by
      simp only [mapC, paramOcc, paramOcc_mapC hf t₁, paramOcc_mapC hf t₂, List.map_append]

omit [DecidableEq S] in
private theorem mapC_fold {Y Z : Type v} [DecidableEq Y] [DecidableEq Z]
    (f : Nm Y → Nm Z) (ps : List (Nm Y)) (t : Tm S Y) :
    mapC f (ps.foldr (fun p acc => .lam p [] acc) t) =
      (ps.map f).foldr (fun p acc => .lam p [] acc) (mapC f t) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.foldr, List.map, mapC, ih]

omit [DecidableEq S] in
private theorem mapC_seal {Y Z : Type v} [DecidableEq Y] [DecidableEq Z]
    {f : Nm Y → Nm Z} (hf : Function.Injective f) (t : Tm S Y) :
    mapC f (sealParams t) = sealParams (mapC f t) := by
  unfold sealParams
  rw [mapC_fold, paramOcc_mapC hf]

omit [DecidableEq S] in
private theorem codeAt_ownEmpty (R : Owner) (holes : Option (X → Owner))
    (penv senv : List (X × Owner)) (pos : Owner) (s : Src S X) :
    ownEmpty (codeAt R holes penv senv pos s) := by
  induction s generalizing holes penv senv pos with
  | sym _ => simp [codeAt, ownEmpty]
  | fn _ => simp [codeAt, ownEmpty]
  | sv y =>
      simp only [codeAt]
      cases codeLookup senv y with
      | some _ => simp [ownEmpty]
      | none => cases holes <;> simp [ownEmpty]
  | par _ =>
      simp only [codeAt]
      split <;> simp [ownEmpty]
  | lam z _ _ ih =>
      unfold codeAt
      exact ⟨rfl, ih holes ((z, codeBinder pos) :: penv) senv (pos ++ [0])⟩
  | form z _ ih =>
      unfold codeAt
      exact ⟨rfl, ih holes ((z, codeBinder pos) :: penv) senv (pos ++ [0])⟩
  | app _ _ ihf iha =>
      simp only [codeAt, ownEmpty]
      exact ⟨ihf _ _ _ _, iha _ _ _ _⟩
  | quote _ ih =>
      simp only [codeAt, ownEmpty]
      exact ownEmpty_seal (ih none [] [] [])
  | pquote _ ih =>
      simp only [codeAt, ownEmpty]
      exact ih _ _ _ _
  | letS _ _ _ _ ihp ihw ihb =>
      simp only [codeAt, ownEmpty]
      exact ⟨ihp _ _ _ _, ihw _ _ _ _, ihb _ _ _ _⟩
  | unify _ _ _ ihp ihw ihb =>
      simp only [codeAt, ownEmpty]
      exact ⟨ihp _ _ _ _, ihw _ _ _ _, ihb _ _ _ _⟩
  | alt _ _ iht ihu =>
      simp only [codeAt, ownEmpty]
      exact ⟨iht _ _ _ _, ihu _ _ _ _⟩
  | new _ _ ih =>
      simpa [codeAt] using ih holes penv senv (pos ++ [0])

omit [DecidableEq S] [DecidableEq X] in
private theorem nil_bound : ∀ p ∈ ([] : List (X × Owner)), codeBound p.2 = true := by
  intro _ h
  simp at h

omit [DecidableEq S] [DecidableEq X] in
private theorem cons_bound {z : X} {o : Owner} {l : List (X × Owner)}
    (ho : codeBound o = true) (hl : ∀ p ∈ l, codeBound p.2 = true) :
    ∀ p ∈ (z, o) :: l, codeBound p.2 = true := by
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact ho
  · exact hl p hp

omit [DecidableEq S] [DecidableEq X] in
private theorem append_bound {l₁ l₂ : List (X × Owner)}
    (h₁ : ∀ p ∈ l₁, codeBound p.2 = true) (h₂ : ∀ p ∈ l₂, codeBound p.2 = true) :
    ∀ p ∈ l₁ ++ l₂, codeBound p.2 = true := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h₁ p hp
  · exact h₂ p hp

omit [DecidableEq S] in
private theorem lookup_bound {l : List (X × Owner)} (hl : ∀ p ∈ l, codeBound p.2 = true)
    {y : X} {o : Owner} (h : codeLookup l y = some o) : codeBound o = true := by
  induction l with
  | nil => simp [codeLookup] at h
  | cons p rest ih =>
      obtain ⟨z, oz⟩ := p
      have hoz : codeBound oz = true := hl (z, oz) (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rest, codeBound q.2 = true := fun q hq => hl q (List.mem_cons_of_mem _ hq)
      simp only [codeLookup] at h
      by_cases hz : z = y
      · simp only [hz, if_true, Option.some.injEq] at h
        exact h ▸ hoz
      · simp only [hz, if_false] at h
        exact ih hrest h

omit [DecidableEq S] [DecidableEq X] in
private theorem binds_bound (pos : Owner) :
    ∀ (s : Src S X), ∀ p ∈ svBinds pos s, codeBound p.2 = true
  | .sv _, _, h => by
      simp only [svBinds, List.mem_singleton] at h
      subst h
      rfl
  | .app f a, _, h => by
      simp only [svBinds, List.mem_append] at h
      rcases h with h | h
      · exact binds_bound (pos ++ [0]) f _ h
      · exact binds_bound (pos ++ [1]) a _ h
  | .alt t₁ t₂, _, h => by
      simp only [svBinds, List.mem_append] at h
      rcases h with h | h
      · exact binds_bound (pos ++ [0]) t₁ _ h
      · exact binds_bound (pos ++ [1]) t₂ _ h
  | .sym _, _, h | .fn _, _, h | .par _, _, h | .lam _ _ _, _, h | .quote _, _, h
    | .pquote _, _, h | .letS _ _ _ _, _, h | .unify _ _ _, _, h | .new _ _, _, h
    | .form _ _, _, h => by
      simp [svBinds] at h

omit [DecidableEq S] in
/-- Sealed code written in a form rooted at a scope owner `R`, read in the
identity model, is its slot elaboration with every name read by `codeFwd`. -/
private theorem codeIAt_eq_map (R : Owner) (hR : scopeOwner R)
    (penv senv : List (X × Owner)) (pos : Owner)
    (hpenv : ∀ p ∈ penv, codeBound p.2 = true) (hsenv : ∀ p ∈ senv, codeBound p.2 = true) :
    ∀ s : Src S X,
      mapC codeFwd (codeAt R none penv senv pos s) = codeIAt R none penv senv pos s
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv y => by
      simp only [codeAt, codeIAt]
      cases h : codeLookup senv y with
      | none =>
          simp only [mapC, iVar]
          rw [codeFwd_scope (not_code_of_scopeOwner hR)]
      | some p =>
          simp only [mapC]
          rw [codeFwd_code (Or.inl (lookup_bound hsenv h))]
  | .par z => by
      simp only [codeAt, codeIAt]
      cases h : codeLookup penv z with
      | none =>
          simp only [mapC]
          rw [codeFwd_code (Or.inr rfl)]
      | some p =>
          simp only [mapC]
          rw [codeFwd_code (Or.inl (lookup_bound hpenv h))]
  | .lam z _ b => by
      simp only [codeAt, codeIAt, mapC,
        codeIAt_eq_map R hR ((z, codeBinder pos) :: penv) senv (pos ++ [0])
          (cons_bound rfl hpenv) hsenv b]
      rw [codeFwd_binder]
  | .form z b => by
      simp only [codeAt, codeIAt, mapC,
        codeIAt_eq_map R hR ((z, codeBinder pos) :: penv) senv (pos ++ [0])
          (cons_bound rfl hpenv) hsenv b]
      rw [codeFwd_binder]
  | .app f a => by
      simp only [codeAt, codeIAt, mapC,
        codeIAt_eq_map R hR penv senv (pos ++ [0]) hpenv hsenv f,
        codeIAt_eq_map R hR penv senv (pos ++ [1]) hpenv hsenv a]
  | .quote c => by
      simp only [codeAt, codeIAt, mapC]
      rw [mapC_seal codeFwd_injective]
      exact congrArg Tm.quote (congrArg sealParams
        (codeIAt_eq_map R hR [] [] [] nil_bound nil_bound c))
  | .pquote c => by
      simp only [codeAt, codeIAt, mapC, codeIAt_eq_map R hR [] [] [] nil_bound nil_bound c]
  | .letS p w b _ => by
      simp only [codeAt, codeIAt, mapC,
        codeIAt_eq_map R hR penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) hpenv
          (append_bound (binds_bound (pos ++ [0]) p) hsenv) p,
        codeIAt_eq_map R hR penv senv (pos ++ [1]) hpenv hsenv w,
        codeIAt_eq_map R hR penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) hpenv
          (append_bound (binds_bound (pos ++ [0]) p) hsenv) b]
  | .unify p w b => by
      simp only [codeAt, codeIAt, mapC,
        codeIAt_eq_map R hR penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) hpenv
          (append_bound (binds_bound (pos ++ [0]) p) hsenv) p,
        codeIAt_eq_map R hR penv senv (pos ++ [1]) hpenv hsenv w,
        codeIAt_eq_map R hR penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) hpenv
          (append_bound (binds_bound (pos ++ [0]) p) hsenv) b]
  | .alt t₁ t₂ => by
      simp only [codeAt, codeIAt, mapC,
        codeIAt_eq_map R hR penv senv (pos ++ [0]) hpenv hsenv t₁,
        codeIAt_eq_map R hR penv senv (pos ++ [1]) hpenv hsenv t₂]
  | .new _ b => by
      simp only [codeAt, codeIAt, codeIAt_eq_map R hR penv senv (pos ++ [0]) hpenv hsenv b]

private theorem codeEq_map (t₁ t₂ : Tm S (Slot X)) (h₁ : ownEmpty t₁) (h₂ : ownEmpty t₂) :
    codeEq t₁ t₂ = codeEq (mapC codeFwd t₁) (mapC codeFwd t₂) := by
  induction t₁ generalizing t₂ with
  | sym _ =>
      cases h₁
      cases t₂ with
      | sym _ =>
          cases h₂
          simp [codeEq, mapC]
      | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp [codeEq, mapC]
  | fn _ =>
      cases h₁
      cases t₂ with
      | fn _ =>
          cases h₂
          simp [codeEq, mapC]
      | sym _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp [codeEq, mapC]
  | var _ =>
      cases h₁
      cases t₂ with
      | var _ =>
          cases h₂
          simp [codeEq, mapC, same_fwd]
      | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp [codeEq, mapC]
  | pvar _ =>
      cases h₁
      cases t₂ with
      | pvar _ =>
          cases h₂
          simp [codeEq, mapC, same_fwd]
      | sym _ | fn _ | var _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp [codeEq, mapC]
  | lam _ _ _ ih =>
      cases t₂ with
      | lam _ _ b' =>
          rcases h₁ with ⟨rfl, hb⟩
          rcases h₂ with ⟨rfl, hb'⟩
          simp only [codeEq, mapC]
          rw [same_fwd, ih b' hb hb']
      | sym _ | fn _ | var _ | pvar _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp [codeEq, mapC]
  | app _ _ ihf iha =>
      cases t₂ with
      | app f' a' =>
          rcases h₁ with ⟨hf, ha⟩
          rcases h₂ with ⟨hf', ha'⟩
          simp only [codeEq, mapC]
          rw [ihf f' hf hf', iha a' ha ha']
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp [codeEq, mapC]
  | quote _ ih =>
      cases t₂ with
      | quote c' =>
          simp only [codeEq, mapC]
          rw [ih c' h₁ h₂]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp [codeEq, mapC]
  | pquote _ ih =>
      cases t₂ with
      | pquote c' =>
          simp only [codeEq, mapC]
          rw [ih c' h₁ h₂]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp [codeEq, mapC]
  | letP _ _ _ ihp ihw ihb =>
      cases t₂ with
      | letP p' w' b' =>
          rcases h₁ with ⟨hp, hw, hb⟩
          rcases h₂ with ⟨hp', hw', hb'⟩
          simp only [codeEq, mapC]
          rw [ihp p' hp hp', ihw w' hw hw', ihb b' hb hb']
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | alt _ _ =>
          simp [codeEq, mapC]
  | alt _ _ iht ihu =>
      cases t₂ with
      | alt t' u' =>
          rcases h₁ with ⟨ht, hu⟩
          rcases h₂ with ⟨ht', hu'⟩
          simp only [codeEq, mapC]
          rw [iht t' ht ht', ihu u' hu hu']
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ =>
          simp [codeEq, mapC]
  | ctx _ _ _ => cases t₂ <;> simp [codeEq, mapC]

/-- `codeEq` gives the same answer for the slot elaboration and the identity
elaboration of two pieces of code, at any quotation-relative positions, written
in forms rooted at scope owners `R₁` and `R₂`, when every binder in force is a
binder of code.  A `new` block contributes the code of its body. -/
theorem codeEq_at (R₁ R₂ : Owner) (hR₁ : scopeOwner R₁) (hR₂ : scopeOwner R₂)
    (penv₁ penv₂ senv₁ senv₂ : List (X × Owner)) (pos₁ pos₂ : Owner)
    (hp₁ : ∀ p ∈ penv₁, codeBound p.2 = true) (hp₂ : ∀ p ∈ penv₂, codeBound p.2 = true)
    (hs₁ : ∀ p ∈ senv₁, codeBound p.2 = true) (hs₂ : ∀ p ∈ senv₂, codeBound p.2 = true)
    (s s' : Src S X) :
    codeEq (codeAt R₁ none penv₁ senv₁ pos₁ s) (codeAt R₂ none penv₂ senv₂ pos₂ s') =
      codeEq (codeIAt R₁ none penv₁ senv₁ pos₁ s) (codeIAt R₂ none penv₂ senv₂ pos₂ s') := by
  rw [← codeIAt_eq_map R₁ hR₁ penv₁ senv₁ pos₁ hp₁ hs₁ s,
    ← codeIAt_eq_map R₂ hR₂ penv₂ senv₂ pos₂ hp₂ hs₂ s']
  exact codeEq_map (codeAt R₁ none penv₁ senv₁ pos₁ s) (codeAt R₂ none penv₂ senv₂ pos₂ s')
    (codeAt_ownEmpty R₁ none penv₁ senv₁ pos₁ s) (codeAt_ownEmpty R₂ none penv₂ senv₂ pos₂ s')

/-- Sealed code agrees: `(lam w w)` and `(lam z z)` compare alike in both models,
for quotations written in forms rooted at scope owners `R` and `R'`. -/
theorem codeEq_codeOf_codeI (R R' : Owner) (hR : scopeOwner R) (hR' : scopeOwner R')
    (s s' : Src S X) :
    codeEq (codeOf R s) (codeOf R' s') = codeEq (codeI R s) (codeI R' s') := by
  simp only [codeOf, codeI]
  have hs : mapC codeFwd (sealParams (codeAt R none [] [] [] s)) =
      sealParams (codeIAt R none [] [] [] s) := by
    rw [mapC_seal codeFwd_injective]
    exact congrArg sealParams (codeIAt_eq_map R hR [] [] [] nil_bound nil_bound s)
  have hs' : mapC codeFwd (sealParams (codeAt R' none [] [] [] s')) =
      sealParams (codeIAt R' none [] [] [] s') := by
    rw [mapC_seal codeFwd_injective]
    exact congrArg sealParams (codeIAt_eq_map R' hR' [] [] [] nil_bound nil_bound s')
  rw [← hs, ← hs']
  exact codeEq_map _ _
    (ownEmpty_seal (codeAt_ownEmpty R none [] [] [] s))
    (ownEmpty_seal (codeAt_ownEmpty R' none [] [] [] s'))

end Mettapedia.GSLT.LanguageDef.TemplateScope
