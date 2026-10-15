import Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotConverse
import Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotProfiles
import Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshConnections
import Mettapedia.GSLT.LanguageDef.TemplateScope.QuotedCodeEq

/-!
# Template scope: the identity model is the slot model, up to renaming

The slot model (`TemplateScope.Spectrum`: names are slots `(owner, spelling)`,
a `let` that introduces names and a `new` block are activations) and the
identity model (`TemplateScope.LexicalFresh`: names are binder identities,
every binder is allocated in its frame) run the same programs to the same
observations, up to a renaming of names, under rule M and under lexical fresh.

## Main results

* `renaming_M`, `renaming_LF` — **the renaming theorem**: on admissible
  programs, the slot model's run and the identity model's run are defined
  together, and when both are defined their bags of results correspond in
  order, each pair of results related by its own injective renaming of the
  names in play: the answers are related values and the final stores are
  related (`Renamed`).
* `transfer` — **the translator's correctness in the slot model**: the slot
  model's lexical fresh on the translated program is defined exactly when the
  slot model's rule M on the source is, and both bags are renamings, result by
  result, of the identity model's bag of rule M on the source (which is the
  identity model's bag of lexical fresh on the translation, `run_toLexical`).

## Admissible text

No `new` block with names on the spine of a pattern, every parameter bound
(`Src.Admissible`). A quotation may stand in pattern position. Each condition
is needed: `newPat_needed` and `freePar_needed` name a program violating it
on which the two models differ.

## What the renaming is not

The renaming is per result: the two models may share a name across two results
of one bag in different ways (the identity model allocates in the frame, the
slot model at each activation), so the printed bag, which numbers names across
the whole bag, can differ.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

namespace Src

variable {S : Type u} {X : Type v} [DecidableEq X]

/-- **Admissible authored text**: no `new` block with names on the spine of a
pattern, every parameter bound. A quotation may stand in pattern position. -/
def Admissible (t : Src S X) : Prop :=
  t.patsNewFree = true ∧ t.freePars = []

instance (t : Src S X) : Decidable t.Admissible :=
  inferInstanceAs (Decidable (_ ∧ _))

end Src

namespace IdSlot

variable {S : Type u} {X : Type v} [DecidableEq X]

/-- **Sealed code is related bi-uniquely**: the two code maps forget the same
information (crossing sets, `new` declarations, `let` versus `unify`). -/
theorem SC_biUnique : (SC : Setting S (Slot X) (BId X)).BiUnique := by
  rintro _ _ _ _ ⟨R, s, hR, rfl, rfl⟩ ⟨R', s', hR', rfl, rfl⟩
  constructor
  · intro h
    rw [← mapCode_codeOf hR s, h, mapCode_codeOf hR']
  · intro h
    rw [← mapCode_codeI hR s, h, mapCode_codeI hR']


/-! ## Reading sealed code through `holeRead` -/

omit [DecidableEq X] in
theorem mapCode_comp {Y Z W : Type v} (f : Nm Z → Nm W) (g : Nm Y → Nm Z) :
    ∀ t : Tm S Y, mapCode f (mapCode g t) = mapCode (f ∘ g) t
  | .sym _ => rfl
  | .fn _ => rfl
  | .var _ => rfl
  | .pvar _ => rfl
  | .lam x _ b => by simp only [mapCode, mapCode_comp f g b, Function.comp]
  | .app a b => by simp only [mapCode, mapCode_comp f g a, mapCode_comp f g b]
  | .quote c => by simp only [mapCode, mapCode_comp f g c]
  | .ctx ks c => by simp only [mapCode, mapCode_comp f g c, List.map_map]
  | .pquote c => by simp only [mapCode, mapCode_comp f g c]
  | .letP p w b => by
      simp only [mapCode, mapCode_comp f g p, mapCode_comp f g w, mapCode_comp f g b]
  | .alt t u => by simp only [mapCode, mapCode_comp f g t, mapCode_comp f g u]

omit [DecidableEq X] in
/-- **Renaming keeps `codeEq`** on code whose lambdas own nothing, when the
renaming keeps `CodeId.same` on the names compared. -/
theorem codeEq_mapCode {Y Z : Type v} [DecidableEq S] [DecidableEq Y] [DecidableEq Z]
    [CodeId Y] [CodeId Z]
    {f : Nm Y → Nm Z} :
    ∀ (c c' : Tm S Y), ownNil c → ownNil c' →
      (∀ a ∈ codeNames c, ∀ b ∈ codeNames c', CodeId.same (f a) (f b) = CodeId.same a b) →
      codeEq (mapCode f c) (mapCode f c') = codeEq c c'
  | .sym _, c', _, _, _ => by cases c' <;> rfl
  | .fn _, c', _, _, _ => by cases c' <;> rfl
  | .var n, c', _, _, h => by
      cases c' with
      | var m => exact h n (by simp [codeNames]) m (by simp [codeNames])
      | _ => rfl
  | .pvar n, c', _, _, h => by
      cases c' with
      | pvar m => exact h n (by simp [codeNames]) m (by simp [codeNames])
      | _ => rfl
  | .lam x o b, c', ho, ho', h => by
      cases c' with
      | lam x' o' b' =>
          obtain ⟨rfl, hb⟩ := ho
          obtain ⟨rfl, hb'⟩ := ho'
          simp only [mapCode, codeEq, h x (by simp [codeNames]) x' (by simp [codeNames]),
            codeEq_mapCode b b' hb hb' fun a ha a' ha' =>
              h a (by simp [codeNames, ha]) a' (by simp [codeNames, ha'])]
      | _ => rfl
  | .app f₁ a₁, c', ho, ho', h => by
      cases c' with
      | app f₂ a₂ =>
          simp only [mapCode, codeEq,
            codeEq_mapCode f₁ f₂ ho.1 ho'.1 fun a ha a' ha' =>
              h a (by simp [codeNames, ha]) a' (by simp [codeNames, ha']),
            codeEq_mapCode a₁ a₂ ho.2 ho'.2 fun a ha a' ha' =>
              h a (by simp [codeNames, ha]) a' (by simp [codeNames, ha'])]
      | _ => rfl
  | .quote c₁, c', ho, ho', h => by
      cases c' with
      | quote c₂ =>
          simp only [mapCode, codeEq]
          exact codeEq_mapCode c₁ c₂ ho ho' fun a ha a' ha' =>
            h a (by simpa [codeNames] using ha) a' (by simpa [codeNames] using ha')
      | _ => rfl
  | .ctx _ _, c', _, _, _ => by cases c' <;> rfl
  | .pquote c₁, c', ho, ho', h => by
      cases c' with
      | pquote c₂ =>
          simp only [mapCode, codeEq]
          exact codeEq_mapCode c₁ c₂ ho ho' fun a ha a' ha' =>
            h a (by simpa [codeNames] using ha) a' (by simpa [codeNames] using ha')
      | _ => rfl
  | .letP p₁ w₁ b₁, c', ho, ho', h => by
      cases c' with
      | letP p₂ w₂ b₂ =>
          simp only [mapCode, codeEq,
            codeEq_mapCode p₁ p₂ ho.1 ho'.1 fun a ha a' ha' =>
              h a (by simp [codeNames, ha]) a' (by simp [codeNames, ha']),
            codeEq_mapCode w₁ w₂ ho.2.1 ho'.2.1 fun a ha a' ha' =>
              h a (by simp [codeNames, ha]) a' (by simp [codeNames, ha']),
            codeEq_mapCode b₁ b₂ ho.2.2 ho'.2.2 fun a ha a' ha' =>
              h a (by simp [codeNames, ha]) a' (by simp [codeNames, ha'])]
      | _ => rfl
  | .alt t₁ u₁, c', ho, ho', h => by
      cases c' with
      | alt t₂ u₂ =>
          simp only [mapCode, codeEq,
            codeEq_mapCode t₁ t₂ ho.1 ho'.1 fun a ha a' ha' =>
              h a (by simp [codeNames, ha]) a' (by simp [codeNames, ha']),
            codeEq_mapCode u₁ u₂ ho.2 ho'.2 fun a ha a' ha' =>
              h a (by simp [codeNames, ha]) a' (by simp [codeNames, ha'])]
      | _ => rfl

theorem holeRead_src_SC {ν : Nm (Slot X) → Nm (BId X)} (s : Slot X) :
    holeRead (SC : Setting S (Slot X) (BId X)) ν (.src s) = codeFwd (.src s) := rfl

/-- Stripping the copies of read code is reading the stripped code. -/
theorem strip_holeRead {ν : Nm (Slot X) → Nm (BId X)} {c : Tm S (Slot X)}
    (hf : CodeForm (SC : Setting S (Slot X) (BId X)) c) :
    stripCode (mapCode (holeRead (SC : Setting S (Slot X) (BId X)) ν) c) =
      mapCode codeFwd (stripCode c) := by
  simp only [stripCode, mapCode_comp]
  refine mapCode_congr c fun n hn => ?_
  rcases hf.name_cases hn with ⟨s, rfl⟩ | ⟨hc, -⟩
  · obtain ⟨s', hs'⟩ := codeFwd_src s
    show nmBase (codeFwd (.src s)) = codeFwd (nmBase (.src s))
    rw [hs']
    exact hs'.symm
  · cases n with
    | src _ => exact hc.elim
    | inst ρ m =>
        cases m with
        | inst _ _ => exact hc.elim
        | src s =>
            obtain ⟨s', hs'⟩ := codeFwd_src s
            show nmBase (Nm.inst _ (codeFwd (.src s))) = codeFwd (nmBase (.inst ρ (.src s)))
            simp only [nmBase, hs']

/-! ## Pattern code matches sealed code -/

theorem codeBound_ne_free {o : Owner} (h : codeBound o = true) : o ≠ codeFreeParam := by
  intro e
  subst e
  exact Bool.false_ne_true h

theorem codeBound_nil : codeBound [] = false := rfl

omit [DecidableEq X] in
theorem codeFreeS_param (y : X) : codeFreeS (.src (codeFreeParam, y)) = true := rfl

omit [DecidableEq X] in
theorem codeFreeI_param (y : X) : codeFreeI (.src (.code y codeFreeParam)) = true := rfl

omit [DecidableEq X] in
theorem codeFreeS_bound {o : Owner} {y : X} (h : codeBound o = true) :
    codeFreeS (.src (o, y)) = false := by
  simp only [codeFreeS]
  exact decide_eq_false (codeBound_ne_free h)

omit [DecidableEq X] in
theorem codeFreeI_bound {o : Owner} {y : X} (h : codeBound o = true) :
    codeFreeI (.src (.code y o)) = false := by
  simp only [codeFreeI]
  exact decide_eq_false (codeBound_ne_free h)

omit [DecidableEq X] in
theorem ne_of_codeFree {a b : Nm (Slot X)} (ha : codeFreeS a = false)
    (hb : codeFreeS b = true) : a ≠ b := by
  intro h
  rw [h] at ha
  exact Bool.false_ne_true (ha.symm.trans hb)

/-- `if` on a `Bool` is `ite (c = true)`, so `cond` does not rewrite it. -/
theorem ite_bool_false {α : Sort u} {a b : α} : (if false then a else b) = b :=
  if_neg Bool.false_ne_true

theorem ite_bool_true {α : Sort u} {a b : α} : (if true then a else b) = a :=
  if_pos rfl

/-- The spelling test in `CodeId.same` is a `Bool` conjunction. -/
theorem ite_bool_and_left {α : Sort u} {p q : Prop} [Decidable p] [Decidable q]
    {a b : α} (h : ¬ p) : (if decide p && decide q then a else b) = b := by
  simp only [decide_eq_false h, Bool.false_and, ite_bool_false]

theorem ite_bool_and_right {α : Sort u} {p q : Prop} [Decidable p] [Decidable q]
    {a b : α} (h : ¬ q) : (if decide p && decide q then a else b) = b := by
  simp only [decide_eq_false h, Bool.and_false, ite_bool_false]

theorem freeNames_lam_nil {Y : Type v} [DecidableEq Y] (x : Nm Y) (b : Tm S Y) :
    freeNames (.lam x [] b) = freeNames b := by
  simp only [freeNames]
  induction freeNames b with
  | nil => rfl
  | cons n ns ih =>
      simp only [List.filter, ownKey_nil n, Bool.not_false, ih]

/-- `CodeId.same` on two slot names, as the instance writes it. -/
theorem same_src_eq (o₁ o₂ : Owner) (y₁ y₂ : X) :
    CodeId.same (.src (o₁, y₁) : Nm (Slot X)) (.src (o₂, y₂)) =
      if codeBound o₁ && codeBound o₂ then decide (o₁ = o₂)
      else if o₁ = codeFreeParam && o₂ = codeFreeParam then decide (y₁ = y₂)
      else decide ((.src (o₁, y₁) : Nm (Slot X)) = .src (o₂, y₂)) := rfl

/-- `CodeId.same` on two code names, as the instance writes it. -/
theorem same_code_eq (y₁ y₂ : X) (o₁ o₂ : Owner) :
    CodeId.same (.src (.code y₁ o₁) : Nm (BId X)) (.src (.code y₂ o₂)) =
      if codeBound o₁ && codeBound o₂ then decide (o₁ = o₂)
      else if o₁ = codeFreeParam && o₂ = codeFreeParam then decide (y₁ = y₂)
      else decide ((.src (.code y₁ o₁) : Nm (BId X)) = .src (.code y₂ o₂)) := rfl

theorem same_instL_src {ρ : Path} {n : Nm (Slot X)} {o : Owner} {y : X} :
    CodeId.same (.inst ρ n) (.src (o, y)) = false :=
  decide_eq_false fun h => by cases h

theorem same_instI_src {ρ : Path} {n : Nm (BId X)} {b : BId X} :
    CodeId.same (.inst ρ n) (.src b) = false :=
  decide_eq_false fun h => by cases h

theorem same_slot_code {k : SlotId X} {y : X} {o : Owner} :
    CodeId.same (.src (.slot k) : Nm (BId X)) (.src (.code y o)) = false :=
  decide_eq_false fun h => by cases h

theorem same_par_code {z : X} {pos o : Owner} {y : X} :
    CodeId.same (.src (.par z pos) : Nm (BId X)) (.src (.code y o)) = false :=
  decide_eq_false fun h => by cases h

theorem decide_src_owner_ne {o₁ o₂ : Owner} {y₁ y₂ : X} (h : o₁ ≠ o₂) :
    decide ((.src (o₁, y₁) : Nm (Slot X)) = .src (o₂, y₂)) = false :=
  decide_eq_false fun he => by
    simp only [Nm.src.injEq, Prod.mk.injEq] at he
    exact h he.1

theorem decide_code_owner_ne {y₁ y₂ : X} {o₁ o₂ : Owner} (h : o₁ ≠ o₂) :
    decide ((.src (.code y₁ o₁) : Nm (BId X)) = .src (.code y₂ o₂)) = false :=
  decide_eq_false fun he => by
    simp only [Nm.src.injEq, BId.code.injEq] at he
    exact h he.2

/-- A binder of code is not `CodeId.same` a hole of a scope owner. -/
theorem same_bound_scope {n : Nm (Slot X)} (hn : holeRecS n = false) {o' : Owner}
    (ho' : scopeOwner o') (y : X) :
    CodeId.same n (.src (o', y)) = false := by
  cases n with
  | inst _ _ => exact same_instL_src
  | src p =>
      obtain ⟨o, z⟩ := p
      have hb : codeBound o = true := by
        simp only [holeRecS] at hn
        cases hc : codeBound o with
        | true => rfl
        | false =>
            simp only [hc, Bool.not_false] at hn
            exact absurd hn Bool.false_ne_true.symm
      have hne : o ≠ o' := fun h => by
        rw [h, ho'.1] at hb
        exact Bool.false_ne_true hb
      have hnf : o ≠ codeFreeParam := codeBound_ne_free hb
      rw [same_src_eq]
      simp only [hb, ho'.1, Bool.and_false, ite_bool_false,
        decide_eq_false hnf, Bool.false_and, ite_bool_false, decide_src_owner_ne hne]

/-- A binder of code is not `CodeId.same` a query hole, on the identity side. -/
theorem same_bound_queryI {n : Nm (BId X)} (hn : holeRecI n = false) (y : X) :
    CodeId.same n (.src (.code y [])) = false := by
  cases n with
  | inst _ _ => exact same_instI_src
  | src b =>
      cases b with
      | slot _ =>
          simp only [holeRecI] at hn
          exact absurd hn Bool.false_ne_true.symm
      | par _ _ =>
          simp only [holeRecI] at hn
          exact absurd hn Bool.false_ne_true.symm
      | code z o =>
          have hb : codeBound o = true := by
            simp only [holeRecI] at hn
            cases hc : codeBound o with
            | true => rfl
            | false =>
                simp only [hc, Bool.not_false] at hn
                exact absurd hn Bool.false_ne_true.symm
          have hne : o ≠ [] := fun h => by
            rw [h, codeBound_nil] at hb
            exact Bool.false_ne_true hb
          have hnf : o ≠ codeFreeParam := codeBound_ne_free hb
          rw [same_code_eq]
          simp only [hb, codeBound_nil, Bool.and_false, ite_bool_false,
            decide_eq_false hnf, Bool.false_and, ite_bool_false, decide_code_owner_ne hne]

/-- A binder of code is not `CodeId.same` a head slot. A root hole reads as
that slot, and a non-hole is a code binder. -/
theorem same_bound_head {n : Nm (BId X)} (hn : holeRecI n = false) (k : SlotId X) :
    CodeId.same n (.src (.slot k)) = false := by
  cases n with
  | inst _ _ => exact same_instI_src
  | src b =>
      cases b with
      | slot _ =>
          simp only [holeRecI] at hn
          exact absurd hn Bool.false_ne_true.symm
      | par _ _ =>
          simp only [holeRecI] at hn
          exact absurd hn Bool.false_ne_true.symm
      | code _ _ => exact decide_eq_false fun h => by cases h

/-- Free parameters of code still free in a term: a parameter `matchCode` compares
by spelling, not under a lambda of this term and not inside a sealed quotation. -/
def codeFreePvars : Tm S (Slot X) → List (Nm (Slot X))
  | .sym _ => []
  | .fn _ => []
  | .var _ => []
  | .pvar n => if codeFreeS n then [n] else []
  | .lam x _ b => (codeFreePvars b).filter fun p => decide (p ≠ x)
  | .app f a => codeFreePvars f ++ codeFreePvars a
  | .quote _ => []
  | .ctx _ _ => []
  | .pquote c => codeFreePvars c
  | .letP p w b => codeFreePvars p ++ codeFreePvars w ++ codeFreePvars b
  | .alt t₁ t₂ => codeFreePvars t₁ ++ codeFreePvars t₂

theorem codeFreePvars_free {t : Tm S (Slot X)} {n : Nm (Slot X)}
    (h : n ∈ codeFreePvars t) : codeFreeS n = true := by
  induction t with
  | pvar x =>
      cases hc : codeFreeS x with
      | true =>
          simp only [codeFreePvars, hc, ite_true, List.mem_singleton] at h
          exact h ▸ hc
      | false =>
          simp only [codeFreePvars, hc, ite_bool_false, List.mem_nil_iff] at h
  | lam _ _ _ ih =>
      simp only [codeFreePvars, List.mem_filter, decide_eq_true_eq] at h
      exact ih h.1
  | app _ _ ihf iha =>
      simp only [codeFreePvars, List.mem_append] at h
      rcases h with h | h
      · exact ihf h
      · exact iha h
  | pquote _ ih =>
      simp only [codeFreePvars] at h
      exact ih h
  | letP _ _ _ ihp ihw ihb =>
      simp only [codeFreePvars] at h
      rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h
        · exact ihp h
        · exact ihw h
      · exact ihb h
  | alt _ _ iht ihu =>
      simp only [codeFreePvars, List.mem_append] at h
      rcases h with h | h
      · exact iht h
      · exact ihu h
  | sym _ | fn _ | var _ | quote _ | ctx _ _ =>
      simp only [codeFreePvars, List.mem_nil_iff] at h

theorem codeFreePvars_sub {t : Tm S (Slot X)} {n : Nm (Slot X)}
    (h : n ∈ codeFreePvars t) : n ∈ paramOcc t := by
  induction t with
  | pvar x =>
      cases hc : codeFreeS x with
      | true =>
          simp only [codeFreePvars, hc, ite_true, List.mem_singleton] at h
          simp [paramOcc, h]
      | false =>
          simp only [codeFreePvars, hc, ite_bool_false, List.mem_nil_iff] at h
  | lam x _ b ih =>
      simp only [codeFreePvars, List.mem_filter, decide_eq_true_eq] at h
      simp only [paramOcc, List.mem_filter, decide_eq_true_eq]
      exact ⟨ih h.1, h.2⟩
  | app _ _ ihf iha =>
      simp only [codeFreePvars, List.mem_append] at h
      simp only [paramOcc, List.mem_append]
      rcases h with h | h
      · exact Or.inl (ihf h)
      · exact Or.inr (iha h)
  | pquote _ ih =>
      simp only [codeFreePvars] at h
      simpa [paramOcc] using ih h
  | letP _ _ _ ihp ihw ihb =>
      simp only [codeFreePvars] at h
      simp only [paramOcc, List.mem_append]
      rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl (Or.inl (ihp h))
        · exact Or.inl (Or.inr (ihw h))
      · exact Or.inr (ihb h)
  | alt _ _ iht ihu =>
      simp only [codeFreePvars, List.mem_append] at h
      simp only [paramOcc, List.mem_append]
      rcases h with h | h
      · exact Or.inl (iht h)
      · exact Or.inr (ihu h)
  | sym _ | fn _ | var _ | quote _ | ctx _ _ =>
      simp only [codeFreePvars, List.mem_nil_iff] at h

theorem codeFreePvars_fold (ps : List (Nm (Slot X))) (t : Tm S (Slot X)) :
    ∀ n ∈ codeFreePvars (ps.foldr (fun p acc => .lam p [] acc) t),
      n ∈ codeFreePvars t ∧ n ∉ ps := by
  induction ps with
  | nil =>
      intro n hn
      exact ⟨hn, fun h => by cases h⟩
  | cons p ps ih =>
      intro n hn
      simp only [List.foldr] at hn
      have hmem : n ∈ codeFreePvars (ps.foldr (fun q acc => .lam q [] acc) t) ∧ n ≠ p := by
        simpa [codeFreePvars, List.mem_filter, decide_eq_true_eq] using hn
      obtain ⟨ht, hps⟩ := ih n hmem.1
      refine ⟨ht, ?_⟩
      intro hmem'
      rcases List.mem_cons.1 hmem' with rfl | hmem'
      · exact hmem.2 rfl
      · exact hps hmem'

theorem codeFreePvars_seal (t : Tm S (Slot X)) : codeFreePvars (sealParams t) = [] := by
  unfold sealParams
  apply List.eq_nil_iff_forall_not_mem.2
  intro n hn
  obtain ⟨ht, hnot⟩ := codeFreePvars_fold (paramOcc t) t n hn
  exact hnot (codeFreePvars_sub ht)

theorem codeFreePvars_codeOf (R : Owner) (s : Src S X) : codeFreePvars (codeOf R s) = [] := by
  simp only [codeOf]
  exact codeFreePvars_seal _

theorem codeNames_codeOf (R : Owner) (c : Src S X) :
    ∀ n ∈ codeNames (codeOf R c), ∃ s, n = .src s :=
  fun n hn => codeNames_codeAt R none [] [] [] c n (codeNames_sealParams _ hn)

theorem stripCode_codeOf (R : Owner) (c : Src S X) : stripCode (codeOf R c) = codeOf R c :=
  mapCode_nmBase_self _ (ownNil_seal (ownNil_codeAt R none [] [] [] c)) (codeNames_codeOf R c)

omit [DecidableEq X] in
theorem nmBase_nmBase {Y : Type v} : ∀ n : Nm Y, nmBase (nmBase n) = nmBase n
  | .src _ => rfl
  | .inst _ n => nmBase_nmBase n

omit [DecidableEq X] in
theorem stripCode_stripCode {Y : Type v} (c : Tm S Y) : stripCode (stripCode c) = stripCode c := by
  simp only [stripCode, mapCode_comp]
  exact mapCode_congr c fun n _ => nmBase_nmBase n

/-- The base of a hole name is a hole name. -/
theorem holeName_nmBase {n : Nm (Slot X)} (h : holeName (SC : Setting S (Slot X) (BId X)) n) :
    holeName (SC : Setting S (Slot X) (BId X)) (nmBase n) := by
  cases n with
  | src _ => exact h
  | inst ρ m =>
      cases m with
      | src _ => exact h
      | inst _ _ => exact h.elim

omit [DecidableEq X] in
/-- A free name of sealed code is a hole of the code. -/
theorem sealedFree_sub_codeVars {Y : Type v} [DecidableEq Y] :
    ∀ (t : Tm S Y) {n : Nm Y}, n ∈ sealedFree t → n ∈ codeVars t
  | .quote _, _, h => h
  | .ctx _ _, _, h => h
  | .lam _ _ b, n, h => by
      simp only [sealedFree, List.mem_filter] at h
      exact sealedFree_sub_codeVars b h.1
  | .app f a, n, h => by
      simp only [sealedFree, codeVars, List.mem_append] at h ⊢
      exact h.imp (sealedFree_sub_codeVars f) (sealedFree_sub_codeVars a)
  | .pquote c, _, h => sealedFree_sub_codeVars c h
  | .letP p w b, n, h => by
      simp only [sealedFree, codeVars, List.mem_append] at h ⊢
      exact h.imp (fun h => h.imp (sealedFree_sub_codeVars p) (sealedFree_sub_codeVars w))
        (sealedFree_sub_codeVars b)
  | .alt t u, n, h => by
      simp only [sealedFree, codeVars, List.mem_append] at h ⊢
      exact h.imp (sealedFree_sub_codeVars t) (sealedFree_sub_codeVars u)
  | .sym _, _, h | .fn _, _, h | .var _, _, h | .pvar _, _, h => by simp [sealedFree] at h

/-- A binder of code is not `CodeId.same` a hole copy. -/
theorem same_bound_copyS {n : Nm (Slot X)} (hn : holeRecS n = false) {ρ : Path}
    {k : Nm (Slot X)} (hk : holeRecS k = true) : CodeId.same n (.inst ρ k) = false := by
  cases n with
  | src _ => exact decide_eq_false fun h => by cases h
  | inst ρ' n' =>
      refine decide_eq_false fun h => ?_
      injection h with _ h2
      subst h2
      simp only [holeRecS] at hn
      rw [hn] at hk
      exact Bool.false_ne_true hk

/-- The same on the identity side. -/
theorem same_bound_copyI {m : Nm (BId X)} (hm : holeRecI m = false) {ρ : Path}
    {k : Nm (BId X)} (hk : holeRecI k = true) : CodeId.same m (.inst ρ k) = false := by
  cases m with
  | src b => cases b <;> exact decide_eq_false fun h => by cases h
  | inst ρ' m' =>
      refine decide_eq_false fun h => ?_
      injection h with _ h2
      subst h2
      simp only [holeRecI] at hm
      rw [hm] at hk
      exact Bool.false_ne_true hk

/-- Stripping copies keeps the free parameters of code whose binders and
parameters are names as written. -/
theorem codeFreePvars_strip :
    ∀ (c : Tm S (Slot X)), (∀ n ∈ codeBinders c, ∃ s, n = .src s) →
      codeFreePvars (stripCode c) = codeFreePvars c
  | .sym _, _ => rfl
  | .fn _, _ => rfl
  | .var _, _ => rfl
  | .pvar n, h => by
      obtain ⟨s, rfl⟩ := h n (by simp [codeBinders])
      rfl
  | .lam x _ b, h => by
      obtain ⟨s, rfl⟩ := h x (by simp [codeBinders])
      have hb := codeFreePvars_strip b fun n hn => h n (by simp [codeBinders, hn])
      simp only [stripCode, mapCode, codeFreePvars, nmBase] at hb ⊢
      rw [hb]
  | .app f a, h => by
      have h1 := codeFreePvars_strip f fun n hn => h n (by simp [codeBinders, hn])
      have h2 := codeFreePvars_strip a fun n hn => h n (by simp [codeBinders, hn])
      simp only [stripCode, mapCode, codeFreePvars] at h1 h2 ⊢
      rw [h1, h2]
  | .quote _, _ => rfl
  | .ctx _ _, _ => rfl
  | .pquote c, h => by
      have h1 := codeFreePvars_strip c fun n hn => h n (by simpa [codeBinders] using hn)
      simp only [stripCode, mapCode, codeFreePvars] at h1 ⊢
      exact h1
  | .letP p w b, h => by
      have h1 := codeFreePvars_strip p fun n hn => h n (by simp [codeBinders, hn])
      have h2 := codeFreePvars_strip w fun n hn => h n (by simp [codeBinders, hn])
      have h3 := codeFreePvars_strip b fun n hn => h n (by simp [codeBinders, hn])
      simp only [stripCode, mapCode, codeFreePvars] at h1 h2 h3 ⊢
      rw [h1, h2, h3]
  | .alt t u, h => by
      have h1 := codeFreePvars_strip t fun n hn => h n (by simp [codeBinders, hn])
      have h2 := codeFreePvars_strip u fun n hn => h n (by simp [codeBinders, hn])
      simp only [stripCode, mapCode, codeFreePvars] at h1 h2 ⊢
      rw [h1, h2]

/-- A slot name written for a binder or a free parameter of code. -/
def codeNamed (n : Nm (Slot X)) : Prop :=
  ∃ o y, n = .src (o, y) ∧ (codeBound o = true ∨ o = codeFreeParam)

/-- A fragment of sealed code. Variables are holes (slots of a form root, as
written or copied by an activation), parameters and binders are code names,
own lists are empty, and a quotation holds sealed code: code written at a scope
owner, its holes possibly copied. -/
def frag : Tm S (Slot X) → Prop
  | .sym _ => True
  | .fn _ => True
  | .var n => holeName (SC : Setting S (Slot X) (BId X)) n
  | .pvar n => codeNamed n
  | .lam n own b => own = [] ∧ codeNamed n ∧ frag b
  | .app f a => frag f ∧ frag a
  | .quote c => ∃ (R : Owner) (s : Src S X), scopeOwner R ∧ stripCode c = codeOf R s ∧
      CodeForm (SC : Setting S (Slot X) (BId X)) c
  | .ctx _ _ => False
  | .pquote c => frag c
  | .letP p w b => frag p ∧ frag w ∧ frag b
  | .alt t₁ t₂ => frag t₁ ∧ frag t₂

/-- `μ` sends each free parameter of the subject to its code image, and no other
free parameter of the pattern is sent there. -/
def Align (μ : Nm (Slot X) → Nm (BId X)) (c q : Tm S (Slot X)) : Prop :=
  (∀ m ∈ codeFreePvars q, μ m = codeFwd m) ∧
  (∀ x ∈ freeParams c, ∀ m ∈ codeFreePvars q, μ x = codeFwd m → x = m)

theorem frag_fold {ps : List (Nm (Slot X))} {t : Tm S (Slot X)} (ht : frag t)
    (hps : ∀ p ∈ ps, codeNamed p) :
    frag (ps.foldr (fun p acc => .lam p [] acc) t) := by
  induction ps with
  | nil => exact ht
  | cons p ps ih =>
      exact ⟨rfl, hps p List.mem_cons_self,
        ih fun q hq => hps q (List.mem_cons_of_mem _ hq)⟩

theorem frag_codeAt {R : Owner} (hR : scopeOwner R) (penv senv : List (X × Owner)) (pos : Owner)
    (s : Src S X)
    (hpenv : ∀ p ∈ penv, codeBound p.2 = true) (hsenv : ∀ p ∈ senv, codeBound p.2 = true)
    (hh : ∀ n ∈ codeVars (codeAt R none penv senv pos s),
      holeName (SC : Setting S (Slot X) (BId X)) n) :
    frag (codeAt R none penv senv pos s) := by
  induction s generalizing penv senv pos with
  | sym _ => simp [codeAt, frag]
  | fn _ => simp [codeAt, frag]
  | sv y =>
      simp only [codeAt]
      cases hl : codeLookup senv y with
      | some o =>
          have hb := codeLookup_bound senv hsenv hl
          simp only [frag, codeNamed]
          exact ⟨o, y, rfl, Or.inl hb⟩
      | none =>
          simp only [codeAt, hl] at hh
          exact hh _ (by simp [codeVars])
  | par z =>
      simp only [codeAt]
      cases hl : codeLookup penv z with
      | some o =>
          have hb := codeLookup_bound penv hpenv hl
          simp only [frag, codeNamed]
          exact ⟨o, z, rfl, Or.inl hb⟩
      | none =>
          simp only [frag, codeNamed, codeFreeParam]
          exact ⟨codeFreeParam, z, rfl, Or.inr rfl⟩
  | lam z _ _ ih =>
      simp only [codeAt, codeVars] at hh
      simp only [codeAt, frag, codeNamed]
      exact ⟨trivial, ⟨codeBinder pos, z, rfl, Or.inl (codeBound_binder _)⟩,
        ih ((z, codeBinder pos) :: penv) senv (pos ++ [0])
          (fun p hp => by
            rcases List.mem_cons.1 hp with rfl | hp
            · exact codeBound_binder _
            · exact hpenv p hp) hsenv hh⟩
  | form z _ ih =>
      simp only [codeAt, codeVars] at hh
      simp only [codeAt, frag, codeNamed]
      exact ⟨trivial, ⟨codeBinder pos, z, rfl, Or.inl (codeBound_binder _)⟩,
        ih ((z, codeBinder pos) :: penv) senv (pos ++ [0])
          (fun p hp => by
            rcases List.mem_cons.1 hp with rfl | hp
            · exact codeBound_binder _
            · exact hpenv p hp) hsenv hh⟩
  | app _ _ ihf iha =>
      simp only [codeAt, codeVars, List.mem_append] at hh
      simp only [codeAt, frag]
      exact ⟨ihf penv senv (pos ++ [0]) hpenv hsenv (fun n h => hh n (Or.inl h)),
        iha penv senv (pos ++ [1]) hpenv hsenv (fun n h => hh n (Or.inr h))⟩
  | quote c _ =>
      simp only [codeAt, frag]
      refine ⟨R, c, hR, stripCode_codeOf R c, ownNil_seal (ownNil_codeAt R none [] [] [] c),
        fun n hn => hh n (by simpa [codeAt, codeVars] using hn), fun n hn => ?_⟩
      exact codeNames_codeOf R c n ((mem_codeNames _).2 (Or.inr hn))
  | pquote _ ih =>
      simp only [codeAt, codeVars] at hh
      simp only [codeAt, frag]
      exact ih [] [] [] (fun _ h => by cases h) (fun _ h => by cases h) hh
  | letS p _ _ _ ihp ihw ihb =>
      have hs : ∀ q ∈ svBinds (pos ++ [0]) p ++ senv, codeBound q.2 = true := by
        intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact svBinds_bound _ _ _ hq
        · exact hsenv _ hq
      simp only [codeAt, codeVars, List.mem_append] at hh
      simp only [codeAt, frag]
      exact ⟨ihp penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) hpenv hs
          (fun n h => hh n (Or.inl (Or.inl h))),
        ihw penv senv (pos ++ [1]) hpenv hsenv (fun n h => hh n (Or.inl (Or.inr h))),
        ihb penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) hpenv hs
          (fun n h => hh n (Or.inr h))⟩
  | unify p _ _ ihp ihw ihb =>
      have hs : ∀ q ∈ svBinds (pos ++ [0]) p ++ senv, codeBound q.2 = true := by
        intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact svBinds_bound _ _ _ hq
        · exact hsenv _ hq
      simp only [codeAt, codeVars, List.mem_append] at hh
      simp only [codeAt, frag]
      exact ⟨ihp penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) hpenv hs
          (fun n h => hh n (Or.inl (Or.inl h))),
        ihw penv senv (pos ++ [1]) hpenv hsenv (fun n h => hh n (Or.inl (Or.inr h))),
        ihb penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) hpenv hs
          (fun n h => hh n (Or.inr h))⟩
  | alt _ _ iht ihu =>
      simp only [codeAt, codeVars, List.mem_append] at hh
      simp only [codeAt, frag]
      exact ⟨iht penv senv (pos ++ [0]) hpenv hsenv (fun n h => hh n (Or.inl h)),
        ihu penv senv (pos ++ [1]) hpenv hsenv (fun n h => hh n (Or.inr h))⟩
  | new _ _ ih =>
      simp only [codeAt] at hh
      simpa [codeAt] using ih penv senv (pos ++ [0]) hpenv hsenv hh

theorem paramOcc_codeAt (R : Owner) (penv senv : List (X × Owner)) (pos : Owner) (s : Src S X)
    (hpenv : ∀ p ∈ penv, codeBound p.2 = true) (hsenv : ∀ p ∈ senv, codeBound p.2 = true) :
    ∀ n ∈ paramOcc (codeAt R none penv senv pos s), codeNamed n := by
  induction s generalizing penv senv pos with
  | sym _ => simp [codeAt, paramOcc]
  | fn _ => simp [codeAt, paramOcc]
  | sv y =>
      simp only [codeAt]
      cases hl : codeLookup senv y with
      | some o =>
          have hb := codeLookup_bound senv hsenv hl
          simp only [paramOcc, List.mem_singleton]
          intro n hn
          exact ⟨o, y, hn, Or.inl hb⟩
      | none =>
          simp [paramOcc]
  | par z =>
      simp only [codeAt]
      cases hl : codeLookup penv z with
      | some o =>
          have hb := codeLookup_bound penv hpenv hl
          simp only [paramOcc, List.mem_singleton]
          intro n hn
          exact ⟨o, z, hn, Or.inl hb⟩
      | none =>
          simp only [paramOcc, List.mem_singleton]
          intro n hn
          exact ⟨codeFreeParam, z, hn, Or.inr rfl⟩
  | lam z _ _ ih =>
      simp only [codeAt, paramOcc, List.mem_filter, decide_eq_true_eq]
      intro n hn
      exact ih ((z, codeBinder pos) :: penv) senv (pos ++ [0])
        (fun p hp => by
          rcases List.mem_cons.1 hp with rfl | hp
          · exact codeBound_binder _
          · exact hpenv p hp) hsenv n hn.1
  | form z _ ih =>
      simp only [codeAt, paramOcc, List.mem_filter, decide_eq_true_eq]
      intro n hn
      exact ih ((z, codeBinder pos) :: penv) senv (pos ++ [0])
        (fun p hp => by
          rcases List.mem_cons.1 hp with rfl | hp
          · exact codeBound_binder _
          · exact hpenv p hp) hsenv n hn.1
  | app _ _ ihf iha =>
      simp only [codeAt, paramOcc, List.mem_append]
      intro n hn
      rcases hn with hn | hn
      · exact ihf penv senv (pos ++ [0]) hpenv hsenv n hn
      · exact iha penv senv (pos ++ [1]) hpenv hsenv n hn
  | quote _ _ => simp [codeAt, paramOcc]
  | pquote _ ih =>
      simp only [codeAt, paramOcc]
      exact ih [] [] [] (fun _ h => by cases h) (fun _ h => by cases h)
  | letS p _ _ _ ihp ihw ihb =>
      have hs : ∀ q ∈ svBinds (pos ++ [0]) p ++ senv, codeBound q.2 = true := by
        intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact svBinds_bound _ _ _ hq
        · exact hsenv _ hq
      intro n hn
      simp only [codeAt, paramOcc, List.mem_append] at hn
      rcases hn with hn | hn
      · rcases hn with hn | hn
        · exact ihp penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) hpenv hs n hn
        · exact ihw penv senv (pos ++ [1]) hpenv hsenv n hn
      · exact ihb penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) hpenv hs n hn
  | unify p _ _ ihp ihw ihb =>
      have hs : ∀ q ∈ svBinds (pos ++ [0]) p ++ senv, codeBound q.2 = true := by
        intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact svBinds_bound _ _ _ hq
        · exact hsenv _ hq
      intro n hn
      simp only [codeAt, paramOcc, List.mem_append] at hn
      rcases hn with hn | hn
      · rcases hn with hn | hn
        · exact ihp penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) hpenv hs n hn
        · exact ihw penv senv (pos ++ [1]) hpenv hsenv n hn
      · exact ihb penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) hpenv hs n hn
  | alt _ _ iht ihu =>
      simp only [codeAt, paramOcc, List.mem_append]
      intro n hn
      rcases hn with hn | hn
      · exact iht penv senv (pos ++ [0]) hpenv hsenv n hn
      · exact ihu penv senv (pos ++ [1]) hpenv hsenv n hn
  | new _ _ ih =>
      simpa [codeAt] using ih penv senv (pos ++ [0]) hpenv hsenv

theorem frag_codeOf {R : Owner} (hR : scopeOwner R) (s : Src S X)
    (hh : ∀ n ∈ codeVars (codeOf R s), holeName (SC : Setting S (Slot X) (BId X)) n) :
    frag (codeOf R s) := by
  simp only [codeOf, codeVars_sealParams] at hh ⊢
  exact frag_fold (frag_codeAt hR [] [] [] s (fun _ h => by cases h) (fun _ h => by cases h) hh)
    (paramOcc_codeAt R [] [] [] s (fun _ h => by cases h) (fun _ h => by cases h))

/-- Ground readings of a code fragment agree, and a quotation is related sealed
code. -/
theorem grel_toGVal? {ν : Nm (Slot X) → Nm (BId X)} :
    ∀ q : Tm S (Slot X), frag q →
      OptRel (GRel (SC : Setting S (Slot X) (BId X)) ν) q.toGVal?
        (mapCode (holeRead (SC : Setting S (Slot X) (BId X)) ν) q).toGVal? := by
  intro q
  induction q with
  | sym s =>
      intro _
      simp only [Tm.toGVal?, mapCode]
      exact GRel.sym s
  | fn _ | var _ | pvar _ | lam _ _ _ | letP _ _ _ | alt _ _ | pquote _ =>
      intro _
      simp only [Tm.toGVal?, mapCode]
      trivial
  | quote c =>
      intro hf
      obtain ⟨R, s, hR, hs, hcf⟩ := hf
      simp only [Tm.toGVal?, mapCode]
      exact GRel.quote ⟨⟨R, s, hR, hs, by rw [strip_holeRead hcf, hs, mapCode_codeOf hR]⟩, hcf, rfl⟩
  | ctx _ _ =>
      intro h
      cases h
  | app _ _ ihf iha =>
      intro hf
      obtain ⟨hff, hfa⟩ := hf
      have hf' := ihf hff
      have ha' := iha hfa
      simp only [Tm.toGVal?, mapCode]
      rcases OptRel.cases hf' with ⟨e1, e2⟩ | ⟨_, _, e1, e2, hfg⟩
      · simp [e1, e2]
        exact trivial
      · rcases OptRel.cases ha' with ⟨e3, e4⟩ | ⟨_, _, e3, e4, hag⟩
        · simp [e1, e2, e3, e4]
          exact trivial
        · simp [e1, e2, e3, e4]
          exact GRel.app hfg hag

theorem var_binder_none [DecidableEq S] {ν : Nm (Slot X) → Nm (BId X)} {n : Nm (Slot X)}
    {m : Nm (BId X)}
    (hn : CodeId.hole n = false) (hm : CodeId.hole m = false) {q : Tm S (Slot X)}
    (hf : frag q) (bound₁ : List (Nm (Slot X))) (bound₂ : List (Nm (BId X)))
    (σ₁ : GStore S (Slot X)) (σ₂ : GStore S (BId X)) :
    matchCodeIn σ₁ bound₁ (.var n) q = none ∧
      matchCodeIn σ₂ bound₂ (.var m) (mapCode (holeRead (SC : Setting S (Slot X) (BId X)) ν) q) = none := by
  have hn' : holeRecS n = false := by rw [← hole_eq_holeRecS]; exact hn
  have hm' : holeRecI m = false := by rw [← hole_eq_holeRecI]; exact hm
  cases q with
  | var k =>
      cases k with
      | src p =>
          obtain ⟨o, y⟩ := p
          have ho : scopeOwner o := formRoot.scopeOwner (show formRoot o from hf)
          refine ⟨?_, ?_⟩
          · have hs := same_bound_scope hn' ho y
            simp only [matchCodeIn, hn, hs]
            rfl
          · have hs := same_bound_head hm' ⟨y, o, o, .head⟩
            simp only [matchCodeIn, mapCode, holeRead_src_SC, codeFwd_scope ho, hm, hs,
              ite_bool_false]
      | inst ρ k' =>
          cases k' with
          | inst _ _ => exact (show False from hf).elim
          | src p =>
              obtain ⟨o, y⟩ := p
              have ho : scopeOwner o := formRoot.scopeOwner (show formRoot o from hf)
              refine ⟨?_, ?_⟩
              · have hs : CodeId.same n (.inst ρ (.src (o, y))) = false :=
                  same_bound_copyS hn' (by simp [holeRecS, ho.1])
                simp only [matchCodeIn, hn, hs]
                rfl
              · have hs : CodeId.same m (holeRead (SC : Setting S (Slot X) (BId X)) ν
                    (.inst ρ (.src (o, y)))) = false := by
                  show CodeId.same m (.inst _ (codeFwd (.src (o, y)))) = false
                  rw [codeFwd_scope ho]
                  exact same_bound_copyI hm' rfl
                simp only [matchCodeIn, mapCode, hm, hs, ite_bool_false]
  | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
      simp only [matchCodeIn, mapCode, hn, hm]
      exact ⟨rfl, rfl⟩

theorem opt_seq {D : Set (Nm (Slot X))} {ν : Nm (Slot X) → Nm (BId X)}
    {a₁ : Option (GStore S (Slot X))} {a₂ : Option (GStore S (BId X))}
    {f₁ : GStore S (Slot X) → Option (GStore S (Slot X))}
    {f₂ : GStore S (BId X) → Option (GStore S (BId X))}
    (h1 : OptRel (StoreRel SC ν D) a₁ a₂)
    (h2 : ∀ σ₁ σ₂, StoreRel SC ν D σ₁ σ₂ → OptRel (StoreRel SC ν D) (f₁ σ₁) (f₂ σ₂)) :
    OptRel (StoreRel SC ν D) (a₁.bind f₁) (a₂.bind f₂) := by
  rcases OptRel.cases h1 with ⟨e1, e2⟩ | ⟨τ₁, τ₂, e1, e2, hτ⟩
  · simp [e1, e2]
    exact trivial
  · simp [e1, e2]
    exact h2 τ₁ τ₂ hτ

/-- `matchCode` on an application is `Option.bind`, up to the equation. -/
theorem matchCode_app_bind {Y : Type v} [DecidableEq S] [DecidableEq Y] [CodeId Y]
    (σ : GStore S Y) (p₁ p₂ t₁ t₂ : Tm S Y) :
    matchCode σ (.app p₁ p₂) (.app t₁ t₂) =
      (matchCode σ p₁ t₁).bind fun σ' => matchCode σ' p₂ t₂ := by
  simp only [matchCode, matchCodeIn]
  cases matchCodeIn σ [] p₁ t₁ <;> rfl

theorem matchCode_alt_bind {Y : Type v} [DecidableEq S] [DecidableEq Y] [CodeId Y]
    (σ : GStore S Y) (p₁ p₂ t₁ t₂ : Tm S Y) :
    matchCode σ (.alt p₁ p₂) (.alt t₁ t₂) =
      (matchCode σ p₁ t₁).bind fun σ' => matchCode σ' p₂ t₂ := by
  simp only [matchCode, matchCodeIn]
  cases matchCodeIn σ [] p₁ t₁ <;> rfl

theorem matchCode_letP_bind {Y : Type v} [DecidableEq S] [DecidableEq Y] [CodeId Y]
    (σ : GStore S Y) (p w b p' w' b' : Tm S Y) :
    matchCode σ (.letP p w b) (.letP p' w' b') =
      ((matchCode σ p p').bind fun σ₁ =>
        (matchCode σ₁ w w').bind fun σ₂ => matchCode σ₂ b b') := by
  simp only [matchCode, matchCodeIn]
  cases h1 : matchCodeIn σ [] p p' with
  | none => simp only [Option.bind]
  | some σ₁ =>
      simp only [Option.bind]
      cases h2 : matchCodeIn σ₁ [] w w' with
      | none => rfl
      | some σ₂ => rfl

/-- Two slots that are not both names of code compare as written. -/
theorem same_src_plain {o₁ o₂ : Owner} {y₁ y₂ : X}
    (h : ¬ (codeBound o₁ = true ∨ o₁ = codeFreeParam) ∨
      ¬ (codeBound o₂ = true ∨ o₂ = codeFreeParam)) :
    CodeId.same (.src (o₁, y₁) : Nm (Slot X)) (.src (o₂, y₂)) =
      decide ((.src (o₁, y₁) : Nm (Slot X)) = .src (o₂, y₂)) := by
  rw [same_src_eq]
  rcases h with h | h
  · have hb : codeBound o₁ = false := Bool.eq_false_iff.mpr fun hc => h (Or.inl hc)
    have hf : o₁ ≠ codeFreeParam := fun e => h (Or.inr e)
    rw [hb, Bool.false_and, ite_bool_false, ite_bool_and_left hf]
  · have hb : codeBound o₂ = false := Bool.eq_false_iff.mpr fun hc => h (Or.inl hc)
    have hf : o₂ ≠ codeFreeParam := fun e => h (Or.inr e)
    rw [hb, Bool.and_false, ite_bool_false, ite_bool_and_right hf]

/-- A slot identity compares as written, on either side. -/
theorem same_slot_left (k : SlotId X) (b : Nm (BId X)) :
    CodeId.same (.src (.slot k) : Nm (BId X)) b = decide (.src (.slot k) = b) := by
  cases b with
  | src b => cases b <;> rfl
  | inst _ _ => rfl

theorem same_slot_right (a : Nm (BId X)) (k : SlotId X) :
    CodeId.same a (.src (.slot k) : Nm (BId X)) = decide (a = .src (.slot k)) := by
  cases a with
  | src a => cases a <;> rfl
  | inst _ _ => rfl

/-- The images of two slots that are not both names of code compare as the slots
are written: at least one image is a head slot. -/
theorem same_fwd_plain {o₁ o₂ : Owner} {y₁ y₂ : X}
    (h : ¬ (codeBound o₁ = true ∨ o₁ = codeFreeParam) ∨
      ¬ (codeBound o₂ = true ∨ o₂ = codeFreeParam)) :
    CodeId.same (codeFwd (.src (o₁, y₁))) (codeFwd (.src (o₂, y₂)) : Nm (BId X)) =
      decide ((.src (o₁, y₁) : Nm (Slot X)) = .src (o₂, y₂)) := by
  have hiff : codeFwd (.src (o₁, y₁)) = (codeFwd (.src (o₂, y₂)) : Nm (BId X)) ↔
      (.src (o₁, y₁) : Nm (Slot X)) = .src (o₂, y₂) :=
    ⟨fun e => codeFwd_injective e, fun e => congrArg codeFwd e⟩
  rcases h with h | h
  · have e : codeFwd (.src (o₁, y₁)) = (.src (.slot ⟨y₁, o₁, o₁, .head⟩) : Nm (BId X)) := by
      simp only [codeFwd, if_neg h]
    rw [e, same_slot_left, ← e]
    exact decide_eq_decide.mpr hiff
  · have e : codeFwd (.src (o₂, y₂)) = (.src (.slot ⟨y₂, o₂, o₂, .head⟩) : Nm (BId X)) := by
      simp only [codeFwd, if_neg h]
    rw [e, same_slot_right, ← e]
    exact decide_eq_decide.mpr hiff

/-- `CodeId.same` is unchanged by reading a slot name as a code name. -/
theorem same_codeFwd (a b : Nm (Slot X)) :
    CodeId.same (codeFwd a) (codeFwd b) = CodeId.same a b := by
  cases a with
  | src pa =>
      obtain ⟨o₁, y₁⟩ := pa
      cases b with
      | src pb =>
          obtain ⟨o₂, y₂⟩ := pb
          by_cases h₁ : codeBound o₁ = true ∨ o₁ = codeFreeParam
          · by_cases h₂ : codeBound o₂ = true ∨ o₂ = codeFreeParam
            · rw [codeFwd_code h₁, codeFwd_code h₂, same_src_eq, same_code_eq]
              by_cases hb : codeBound o₁ && codeBound o₂
              · simp only [hb, ite_true]
              · simp only [hb]
                by_cases hf : o₁ = codeFreeParam && o₂ = codeFreeParam
                · simp only [hf, ite_true]
                · simp only [hf]
                  by_cases he : o₁ = o₂ ∧ y₁ = y₂
                  · rcases he with ⟨ho, rfl⟩
                    simp only [ho, ite_bool_false]
                  · have hs :
                        ¬ ((.src (o₁, y₁) : Nm (Slot X)) = .src (o₂, y₂)) := by
                      intro h; cases h; exact he ⟨rfl, rfl⟩
                    have hc : ¬ ((.src (.code y₁ o₁) : Nm (BId X)) =
                        .src (.code y₂ o₂)) := by
                      intro h; cases h; exact he ⟨rfl, rfl⟩
                    rw [decide_eq_false hs, decide_eq_false hc]
            · rw [same_fwd_plain (Or.inr h₂), same_src_plain (Or.inr h₂)]
          · rw [same_fwd_plain (Or.inl h₁), same_src_plain (Or.inl h₁)]
      | inst ρ m =>
          show CodeId.same (codeFwd (.src (o₁, y₁))) (.inst ρ (codeFwd m)) =
            CodeId.same (.src (o₁, y₁) : Nm (Slot X)) (.inst ρ m)
          by_cases h₁ : codeBound o₁ = true ∨ o₁ = codeFreeParam
          · rw [codeFwd_code h₁]
            rfl
          · simp only [codeFwd, if_neg h₁]
            rfl
  | inst ρ n =>
      cases b with
      | src pb =>
          obtain ⟨o₂, y₂⟩ := pb
          show CodeId.same (.inst ρ (codeFwd n)) (codeFwd (.src (o₂, y₂))) =
            CodeId.same (.inst ρ n : Nm (Slot X)) (.src (o₂, y₂))
          by_cases h₂ : codeBound o₂ = true ∨ o₂ = codeFreeParam
          · rw [codeFwd_code h₂]
            rfl
          · simp only [codeFwd, if_neg h₂]
            rfl
      | inst ρ' m =>
          simp only [codeFwd, CodeId.same]
          by_cases he : ρ = ρ' ∧ n = m
          · rcases he with ⟨rfl, rfl⟩
            simp
          · have h1 : ¬ (Nm.inst ρ n = Nm.inst ρ' m) := by
              intro h; cases h; exact he ⟨rfl, rfl⟩
            have h2 : ¬ (Nm.inst ρ (codeFwd n) = Nm.inst ρ' (codeFwd m)) := by
              intro h
              simp only [Nm.inst.injEq] at h
              exact he ⟨h.1, codeFwd_injective h.2⟩
            rw [decide_eq_false h1, decide_eq_false h2]

theorem same_src_inst_slot (p : Slot X) (ρ : Path) (m : Nm (Slot X)) :
    CodeId.same (Nm.src p) (Nm.inst ρ m) = false :=
  decide_eq_false fun h => by cases h

theorem same_inst_src_slot (p : Slot X) (ρ : Path) (m : Nm (Slot X)) :
    CodeId.same (Nm.inst ρ m) (Nm.src p) = false :=
  decide_eq_false fun h => by cases h

theorem same_src_inst_bid (b : BId X) (ρ : Path) (m : Nm (BId X)) :
    CodeId.same (Nm.src b) (Nm.inst ρ m) = false := by
  cases b <;> exact decide_eq_false fun h => by cases h

theorem same_inst_src_bid (b : BId X) (ρ : Path) (m : Nm (BId X)) :
    CodeId.same (Nm.inst ρ m) (Nm.src b) = false := by
  cases b <;> exact decide_eq_false fun h => by cases h

/-- **Reading names of code keeps `CodeId.same`**, on names as written and hole
copies that `holeRead` keeps apart. -/
theorem same_holeRead {ν : Nm (Slot X) → Nm (BId X)} {a b : Nm (Slot X)}
    (ha : (∃ s, a = .src s) ∨ holeCopy (SC : Setting S (Slot X) (BId X)) a)
    (hb : (∃ s, b = .src s) ∨ holeCopy (SC : Setting S (Slot X) (BId X)) b)
    (hinj : holeRead (SC : Setting S (Slot X) (BId X)) ν a =
      holeRead (SC : Setting S (Slot X) (BId X)) ν b → a = b) :
    CodeId.same (holeRead (SC : Setting S (Slot X) (BId X)) ν a)
      (holeRead (SC : Setting S (Slot X) (BId X)) ν b) = CodeId.same a b := by
  rcases ha with ⟨s, rfl⟩ | ha <;> rcases hb with ⟨s', rfl⟩ | hb
  · exact same_codeFwd _ _
  · cases b with
    | src _ => exact hb.elim
    | inst ρ m =>
        obtain ⟨s₀, hs₀⟩ := codeFwd_src s
        rw [holeRead_src_SC, hs₀]
        show CodeId.same (Nm.src s₀) (Nm.inst _ _) = CodeId.same (Nm.src s) (Nm.inst ρ m)
        rw [same_src_inst_bid, same_src_inst_slot]
  · cases a with
    | src _ => exact ha.elim
    | inst ρ m =>
        obtain ⟨s₀, hs₀⟩ := codeFwd_src s'
        rw [holeRead_src_SC, hs₀]
        show CodeId.same (Nm.inst _ _) (Nm.src s₀) = CodeId.same (Nm.inst ρ m) (Nm.src s')
        rw [same_inst_src_bid, same_inst_src_slot]
  · cases a with
    | src _ => exact ha.elim
    | inst ρ m =>
        cases b with
        | src _ => exact hb.elim
        | inst ρ' m' =>
            show decide (_ = _) = decide (_ = _)
            exact decide_eq_decide.2 ⟨fun e => hinj e, fun e => e ▸ rfl⟩

/-- **Reading related sealed code keeps `codeEq`.** -/
theorem codeEq_holeRead [DecidableEq S] {ν : Nm (Slot X) → Nm (BId X)} {c c' : Tm S (Slot X)}
    (hf : CodeForm (SC : Setting S (Slot X) (BId X)) c)
    (hf' : CodeForm (SC : Setting S (Slot X) (BId X)) c')
    (hinj : Set.InjOn (holeRead (SC : Setting S (Slot X) (BId X)) ν)
      {n | n ∈ codeNames c ∨ n ∈ codeNames c'}) :
    codeEq (mapCode (holeRead (SC : Setting S (Slot X) (BId X)) ν) c)
      (mapCode (holeRead (SC : Setting S (Slot X) (BId X)) ν) c') = codeEq c c' :=
  codeEq_mapCode c c' hf.1 hf'.1 fun _ ha _ hb =>
    same_holeRead ((hf.name_cases ha).imp_right (·.1)) ((hf'.name_cases hb).imp_right (·.1))
      (fun e => hinj (Or.inl ha) (Or.inr hb) e)

/-- Sealed code compares alike: binders by position, free parameters by spelling,
and hole copies by identity, which `holeRead` keeps apart. -/
theorem SC_codeAgree [DecidableEq S] : (SC : Setting S (Slot X) (BId X)).CodeAgree := by
  rintro ν c₁ _ c₁' _ ⟨-, hf, rfl⟩ ⟨-, hf', rfl⟩ hinj
  rw [codeEq_holeRead hf hf' hinj]

/-- Mentioning a binder survives the code-name reading. -/
theorem mentionsBinder_map {ν : Nm (Slot X) → Nm (BId X)} (k : Nm (Slot X)) :
    ∀ (q : Tm S (Slot X)), frag q →
      mentionsBinder (codeFwd k) (mapCode (holeRead (SC : Setting S (Slot X) (BId X)) ν) q) = mentionsBinder k q := by
  intro q
  induction q with
  | pvar y =>
      intro hq
      obtain ⟨o, z, rfl, -⟩ := hq
      simp only [mentionsBinder, mapCode, holeRead_src_SC]
      exact same_codeFwd k _
  | lam x _ b ih =>
      intro hq
      obtain ⟨-, ⟨o, z, rfl, -⟩, hb⟩ := hq
      simp only [mentionsBinder, mapCode, holeRead_src_SC, same_codeFwd, ih hb]
  | app _ _ ihf iha =>
      intro hq
      simp only [mentionsBinder, mapCode, ihf hq.1, iha hq.2]
  | letP _ _ _ ihp ihw ihb =>
      intro hq
      simp only [mentionsBinder, mapCode, ihp hq.1, ihw hq.2.1, ihb hq.2.2]
  | alt _ _ iha ihb =>
      intro hq
      simp only [mentionsBinder, mapCode, iha hq.1, ihb hq.2]
  | pquote _ ih =>
      intro hq
      simp only [mentionsBinder, mapCode, ih hq]
  | sym _ | fn _ | var _ | quote _ | ctx _ _ =>
      intro _
      simp only [mentionsBinder, mapCode]

/-- The binders a fragment mentions, read as code names. -/
theorem mentioned_codeFwd {ν : Nm (Slot X) → Nm (BId X)} (bound : List (Nm (Slot X)))
    (q : Tm S (Slot X)) (hq : frag q) :
    mentioned (bound.map codeFwd) (mapCode (holeRead (SC : Setting S (Slot X) (BId X)) ν) q) =
      (mentioned bound q).map codeFwd := by
  induction bound with
  | nil => simp [mentioned]
  | cons k ks ih =>
      have hk : mentionsBinder (codeFwd k) (mapCode (holeRead (SC : Setting S (Slot X) (BId X)) ν) q) = mentionsBinder k q :=
        mentionsBinder_map k q hq
      cases h : mentionsBinder k q with
      | true =>
          simp only [mentioned, List.map_cons, List.filter, h, hk]
          simp only [mentioned] at ih
          rw [ih]
      | false =>
          simp only [mentioned, List.map_cons, List.filter, h, hk]
          simp only [mentioned] at ih
          exact ih

/-- A fragment's lambdas own nothing. -/
theorem frag_ownNil {q : Tm S (Slot X)} (h : frag q) : ownNil q := by
  induction q with
  | lam _ _ _ ih =>
      rcases h with ⟨rfl, _, hb⟩
      exact ⟨rfl, ih hb⟩
  | app _ _ ihf iha =>
      exact ⟨ihf h.1, iha h.2⟩
  | quote _ =>
      obtain ⟨_, _, _, _, hcf⟩ := h
      exact hcf.1
  | pquote _ ih => exact ih h
  | letP _ _ _ ihp ihw ihb =>
      exact ⟨ihp h.1, ihw h.2.1, ihb h.2.2⟩
  | alt _ _ iha ihb =>
      exact ⟨iha h.1, ihb h.2⟩
  | ctx _ _ => cases h
  | sym _ | fn _ | var _ | pvar _ => exact trivial

/-- A fragment's holes are hole names. -/
theorem frag_codeVars (q : Tm S (Slot X)) (h : frag q) :
    ∀ n ∈ codeVars q, holeName (SC : Setting S (Slot X) (BId X)) n := by
  induction q with
  | var _ =>
      intro n hn
      simp only [codeVars, List.mem_singleton] at hn
      subst hn
      exact h
  | lam _ _ b ih => intro n hn; exact ih h.2.2 n (by simpa [codeVars] using hn)
  | app f a ihf iha =>
      intro n hn
      simp only [codeVars, List.mem_append] at hn
      exact hn.elim (ihf h.1 n) (iha h.2 n)
  | quote _ =>
      intro n hn
      obtain ⟨_, _, _, _, hcf⟩ := h
      exact hcf.2.1 n (by simpa [codeVars] using hn)
  | pquote _ ih => intro n hn; exact ih h n (by simpa [codeVars] using hn)
  | letP p w b ihp ihw ihb =>
      intro n hn
      simp only [codeVars, List.mem_append] at hn
      rcases hn with (hn | hn) | hn
      · exact ihp h.1 n hn
      · exact ihw h.2.1 n hn
      · exact ihb h.2.2 n hn
  | alt t u iht ihu =>
      intro n hn
      simp only [codeVars, List.mem_append] at hn
      exact hn.elim (iht h.1 n) (ihu h.2 n)
  | ctx _ _ => exact h.elim
  | sym _ | fn _ | pvar _ => intro n hn; simp [codeVars] at hn

/-- A fragment's binders and parameters are names as written. -/
theorem frag_codeBinders (q : Tm S (Slot X)) (h : frag q) :
    ∀ n ∈ codeBinders q, ∃ s, n = .src s := by
  induction q with
  | pvar _ =>
      intro n hn
      simp only [codeBinders, List.mem_singleton] at hn
      subst hn
      obtain ⟨o, y, rfl, -⟩ := h
      exact ⟨_, rfl⟩
  | lam x _ b ih =>
      intro n hn
      simp only [codeBinders, List.mem_cons] at hn
      rcases hn with rfl | hn
      · obtain ⟨o, y, rfl, -⟩ := h.2.1
        exact ⟨_, rfl⟩
      · exact ih h.2.2 n hn
  | app f a ihf iha =>
      intro n hn
      simp only [codeBinders, List.mem_append] at hn
      exact hn.elim (ihf h.1 n) (iha h.2 n)
  | quote _ =>
      intro n hn
      obtain ⟨_, _, _, _, hcf⟩ := h
      exact hcf.2.2 n (by simpa [codeBinders] using hn)
  | pquote _ ih => intro n hn; exact ih h n (by simpa [codeBinders] using hn)
  | letP p w b ihp ihw ihb =>
      intro n hn
      simp only [codeBinders, List.mem_append] at hn
      rcases hn with (hn | hn) | hn
      · exact ihp h.1 n hn
      · exact ihw h.2.1 n hn
      · exact ihb h.2.2 n hn
  | alt t u iht ihu =>
      intro n hn
      simp only [codeBinders, List.mem_append] at hn
      exact hn.elim (iht h.1 n) (ihu h.2 n)
  | ctx _ _ => exact h.elim
  | sym _ | fn _ | var _ => intro n hn; simp [codeBinders] at hn

/-- **Copying holes keeps a fragment**: code in the code form whose stripped code is
a fragment is a fragment. -/
theorem frag_of_strip (c : Tm S (Slot X)) (hf : CodeForm (SC : Setting S (Slot X) (BId X)) c)
    (h : frag (stripCode c)) : frag c := by
  induction c with
  | sym _ => trivial
  | fn _ => trivial
  | var n => exact hf.2.1 n (by simp [codeVars])
  | pvar n =>
      obtain ⟨s, rfl⟩ := hf.2.2 n (by simp [codeBinders])
      exact h
  | lam x o b ih =>
      obtain ⟨s, rfl⟩ := hf.2.2 x (by simp [codeBinders])
      obtain ⟨ho, hb⟩ := hf.1
      exact ⟨ho, h.2.1, ih ⟨hb, fun n hn => hf.2.1 n (by simpa [codeVars] using hn),
        fun n hn => hf.2.2 n (by simp [codeBinders, hn])⟩ h.2.2⟩
  | app a b iha ihb =>
      simp only [CodeForm, ownNil, codeVars, codeBinders, List.mem_append] at hf
      exact ⟨iha ⟨hf.1.1, fun n hn => hf.2.1 n (Or.inl hn), fun n hn => hf.2.2 n (Or.inl hn)⟩
          h.1,
        ihb ⟨hf.1.2, fun n hn => hf.2.1 n (Or.inr hn), fun n hn => hf.2.2 n (Or.inr hn)⟩ h.2⟩
  | quote c _ =>
      obtain ⟨R, s, hR, hs, -⟩ := h
      refine ⟨R, s, hR, ?_, hf.1, fun n hn => hf.2.1 n (by simpa [codeVars] using hn),
        fun n hn => hf.2.2 n (by simpa [codeBinders] using hn)⟩
      rw [← hs]
      exact (stripCode_stripCode c).symm
  | ctx _ _ _ => exact h.elim
  | pquote c ih =>
      exact ih ⟨hf.1, fun n hn => hf.2.1 n (by simpa [codeVars] using hn),
        fun n hn => hf.2.2 n (by simpa [codeBinders] using hn)⟩ h
  | letP p w b ihp ihw ihb =>
      simp only [CodeForm, ownNil, codeVars, codeBinders, List.mem_append] at hf
      exact ⟨ihp ⟨hf.1.1, fun n hn => hf.2.1 n (Or.inl (Or.inl hn)),
          fun n hn => hf.2.2 n (Or.inl (Or.inl hn))⟩ h.1,
        ihw ⟨hf.1.2.1, fun n hn => hf.2.1 n (Or.inl (Or.inr hn)),
          fun n hn => hf.2.2 n (Or.inl (Or.inr hn))⟩ h.2.1,
        ihb ⟨hf.1.2.2, fun n hn => hf.2.1 n (Or.inr hn),
          fun n hn => hf.2.2 n (Or.inr hn)⟩ h.2.2⟩
  | alt t u iht ihu =>
      simp only [CodeForm, ownNil, codeVars, codeBinders, List.mem_append] at hf
      exact ⟨iht ⟨hf.1.1, fun n hn => hf.2.1 n (Or.inl hn), fun n hn => hf.2.2 n (Or.inl hn)⟩
          h.1,
        ihu ⟨hf.1.2, fun n hn => hf.2.1 n (Or.inr hn), fun n hn => hf.2.2 n (Or.inr hn)⟩ h.2⟩

/-- Sealed code in the code form whose stripped code is written at a scope owner is
a fragment, with no free parameter of code. -/
theorem frag_of_codeForm {c : Tm S (Slot X)} {R : Owner} {s : Src S X} (hR : scopeOwner R)
    (hs : stripCode c = codeOf R s) (hf : CodeForm (SC : Setting S (Slot X) (BId X)) c) :
    frag c ∧ codeFreePvars c = [] := by
  refine ⟨frag_of_strip c hf ?_, ?_⟩
  · rw [hs]
    refine frag_codeOf hR s fun n hn => ?_
    rw [← hs, stripCode, codeVars_mapCode] at hn
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hn
    exact holeName_nmBase (hf.2.1 m hm)
  · rw [← codeFreePvars_strip c hf.2.2, hs, codeFreePvars_codeOf]

theorem matchCodeIn_app_bind {Y : Type v} [DecidableEq S] [DecidableEq Y] [CodeId Y]
    (bound : List (Nm Y)) (σ : GStore S Y) (p₁ p₂ t₁ t₂ : Tm S Y) :
    matchCodeIn σ bound (.app p₁ p₂) (.app t₁ t₂) =
      (matchCodeIn σ bound p₁ t₁).bind fun σ' => matchCodeIn σ' bound p₂ t₂ := by
  simp only [matchCodeIn]
  cases matchCodeIn σ bound p₁ t₁ <;> rfl

theorem matchCodeIn_alt_bind {Y : Type v} [DecidableEq S] [DecidableEq Y] [CodeId Y]
    (bound : List (Nm Y)) (σ : GStore S Y) (p₁ p₂ t₁ t₂ : Tm S Y) :
    matchCodeIn σ bound (.alt p₁ p₂) (.alt t₁ t₂) =
      (matchCodeIn σ bound p₁ t₁).bind fun σ' => matchCodeIn σ' bound p₂ t₂ := by
  simp only [matchCodeIn]
  cases matchCodeIn σ bound p₁ t₁ <;> rfl

theorem matchCodeIn_letP_bind {Y : Type v} [DecidableEq S] [DecidableEq Y] [CodeId Y]
    (bound : List (Nm Y)) (σ : GStore S Y) (p w b p' w' b' : Tm S Y) :
    matchCodeIn σ bound (.letP p w b) (.letP p' w' b') =
      ((matchCodeIn σ bound p p').bind fun σ₁ =>
        (matchCodeIn σ₁ bound w w').bind fun σ₂ => matchCodeIn σ₂ bound b b') := by
  simp only [matchCodeIn]
  cases h1 : matchCodeIn σ bound p p' with
  | none => simp only [Option.bind]
  | some σ₁ =>
      simp only [Option.bind]
      cases h2 : matchCodeIn σ₁ bound w w' with
      | none => rfl
      | some σ₂ => rfl

/-- A hole under code binders binds related values: a ground value when the
fragment mentions none of them, and contextual code read through `holeRead`
otherwise. -/
theorem hole_refine [DecidableEq S] {ν : Nm (Slot X) → Nm (BId X)}
    {D : Set (Nm (Slot X))} {σ₁ : GStore S (Slot X)} {σ₂ : GStore S (BId X)}
    (hσ : StoreRel SC ν D σ₁ σ₂) (hinj : Set.InjOn ν D) (hI : HoleInj (SC : Setting S (Slot X) (BId X)) ν D) {n : Nm (Slot X)}
    (hn : n ∈ D) (hb : CodeId.hole n = true) (hb2 : CodeId.hole (ν n) = true)
    {q : Tm S (Slot X)} (hq : frag q)
    (hqs : ∀ m ∈ codeVars q, m ∈ D ∨ ∃ s, m = .src s ∧ (SC : Setting S (Slot X) (BId X)).root₁ s)
    (bound : List (Nm (Slot X))) (hbd : ∀ k ∈ bound, ∃ s, k = .src s) :
    OptRel (StoreRel SC ν D) (matchCodeIn σ₁ bound (.var n) q)
      (matchCodeIn σ₂ (bound.map codeFwd) (.var (ν n)) (mapCode (holeRead (SC : Setting S (Slot X) (BId X)) ν) q)) := by
  have hment := mentioned_codeFwd (ν := ν) bound q hq
  have ho := frag_ownNil hq
  cases hks : mentioned bound q with
  | nil =>
      have hg := grel_toGVal? (ν := ν) q hq
      have hment0 : mentioned (bound.map codeFwd) (mapCode (holeRead (SC : Setting S (Slot X) (BId X)) ν) q) = [] := by
        rw [hment, hks]
        rfl
      simp only [matchCodeIn, hb, hb2, contextualVal, hks, hment0]
      rcases OptRel.cases hg with ⟨e1, e2⟩ | ⟨g₁, g₂, e1, e2, hgg⟩
      · simp [e1, e2]
        exact trivial
      · rw [e1, e2]
        refine hσ.refine hI hinj hn hgg fun m hm => ?_
        rw [CloTable.toGVal?_toTm e1] at hm
        exact hqs m (sealedFree_sub_codeVars q hm)
  | cons k ks =>
      simp only [matchCodeIn, hb, hb2, contextualVal, hks, hment, List.map_cons]
      have hks' : ∀ k' ∈ k :: ks, ∃ s, k' = .src s := by
        intro k' hk'
        rw [← hks] at hk'
        exact hbd k' (List.mem_filter.1 hk').1
      refine hσ.refine hI hinj hn (.ctx ⟨ho, frag_codeVars q hq, ?_⟩ ?_ rfl) ?_
      · intro m hm
        simp only [codeBinders, List.mem_append] at hm
        rcases hm with hm | hm
        · exact hks' m hm
        · exact frag_codeBinders q hq m hm
      · show List.map codeFwd (k :: ks) =
          List.map (holeRead (SC : Setting S (Slot X) (BId X)) ν) (k :: ks)
        exact List.map_congr_left fun m hm => by
          obtain ⟨s, rfl⟩ := hks' m hm
          rfl
      · intro m hm
        exact hqs m (by simpa [GVal.toTm, sealedFree] using hm)

/-- Entering a lambda of sealed code agrees on the two sides, or neither side
enters. A free parameter that does enter is the subject's binder. -/
theorem gate_split {x₁ : Nm (Slot X)} {own₁ : List (Slot X)} {x₂ : Nm (BId X)}
    {own₂ : List (BId X)} {o : Owner} {y : X} (hb : scBare x₁ own₁ x₂ own₂)
    (hbo : codeBound o = true ∨ o = codeFreeParam) :
    ((CodeId.same x₁ (.src (o, y)) && decide (own₁ = [])) = false ∧
        (CodeId.same x₂ (codeFwd (.src (o, y))) && decide (own₂ = [])) = false) ∨
    ((CodeId.same x₁ (.src (o, y)) && decide (own₁ = [])) = true ∧
        (CodeId.same x₂ (codeFwd (.src (o, y))) && decide (own₂ = [])) = true ∧
        own₁ = [] ∧ own₂ = [] ∧ scEnter x₁ x₂ ∧
        (codeFreeS x₁ = true → x₁ = .src (o, y) ∧ x₂ = codeFwd (.src (o, y))) ∧
        (codeFreeS x₁ = true ∨ codeFreeS (.src (o, y)) = false) ∧
        (codeFreeS x₁ = false → ∀ m : Nm (Slot X), codeFreeS m = true →
          x₂ ≠ codeFwd m)) := by
  have hact : actSrcS x₁ = actSrcI x₂ := by
    rcases hb with ⟨_, _, _, _, hact⟩ | ⟨_, _, _, _, _, hact⟩
    · exact hact
    · exact hact
  cases hsrc : actSrcS x₁ with
  | false =>
      have hsrcI : actSrcI x₂ = false := by rw [← hact, hsrc]
      have hL : CodeId.same x₁ (.src (o, y)) = false := by
        cases x₁ with
        | src _ => simp [actSrcS] at hsrc
        | inst _ _ => exact same_instL_src
      have hR : CodeId.same x₂ (codeFwd (.src (o, y))) = false := by
        cases x₂ with
        | src _ => simp [actSrcI] at hsrcI
        | inst _ _ =>
            rw [codeFwd_code hbo]
            exact same_instI_src
      refine Or.inl ⟨?_, ?_⟩
      · rw [hL, Bool.false_and]
      · rw [hR, Bool.false_and]
  | true =>
      have hsrcI : actSrcI x₂ = true := by rw [← hact, hsrc]
      rcases hb with ⟨hS, hI, hm, hown, _⟩ | ⟨hS, hI, e₁, e₂, ho, _⟩
      · rcases hm with ⟨hf₁, hf₂, hs⟩ | ⟨hcS, hcI⟩
        · obtain ⟨y₁, hy₁⟩ : ∃ y₁, x₁ = .src (codeFreeParam, y₁) := by
            cases x₁ with
            | inst _ _ => simp [actSrcS] at hsrc
            | src p =>
                obtain ⟨o₁, y₁⟩ := p
                have ho1 : o₁ = codeFreeParam := of_decide_eq_true (by simpa [codeFreeS] using hf₁)
                exact ⟨y₁, by simp [ho1]⟩
          subst hy₁
          obtain ⟨y₂, hy₂⟩ : ∃ y₂, x₂ = .src (.code y₂ codeFreeParam) := by
            cases x₂ with
            | inst _ _ => simp [actSrcI] at hsrcI
            | src b =>
                cases b with
                | slot _ => simp [codeFreeI] at hf₂
                | par _ _ => simp [codeFreeI] at hf₂
                | code y₂ o₂ =>
                    have ho2 : o₂ = codeFreeParam :=
                      of_decide_eq_true (by simpa [codeFreeI] using hf₂)
                    exact ⟨y₂, by simp [ho2]⟩
          subst hy₂
          have hy : y₁ = y₂ := by simpa [spellS, spellI] using hs
          subst hy
          obtain ⟨eown₁, eown₂⟩ := hown ⟨hf₁, hf₂⟩
          rcases hbo with hbb | rfl
          · have hne : o ≠ codeFreeParam := codeBound_ne_free hbb
            have hLs : CodeId.same (.src (codeFreeParam, y₁)) (.src (o, y)) = false := by
              rw [same_src_eq]
              unfold codeFreeParam at hne ⊢
              simp only [codeBound, Bool.false_and, ite_bool_false, decide_eq_false hne,
                Bool.and_false, ite_bool_false, decide_src_owner_ne hne.symm]
            have hRs : CodeId.same (.src (.code y₁ codeFreeParam)) (codeFwd (.src (o, y))) = false := by
              rw [codeFwd_code (Or.inl hbb)]
              simp only [same_code_eq]
              unfold codeFreeParam at hne ⊢
              simp only [codeBound, Bool.false_and, ite_bool_false, decide_eq_false hne,
                Bool.and_false, ite_bool_false, decide_code_owner_ne hne.symm]
            refine Or.inl ⟨?_, ?_⟩
            · rw [hLs, Bool.false_and]
            · rw [hRs, Bool.false_and]
          · by_cases hey : y₁ = y
            · refine Or.inr ⟨?_, ?_, eown₁, eown₂, Or.inr ⟨hf₁, hf₂, hs⟩, ?_, Or.inl hf₁, ?_⟩
              · rw [hey, eown₁, same_src_eq]
                simp only [codeBound, codeFreeParam, Bool.false_and, ite_bool_false]
                decide
              · rw [hey, eown₂, codeFwd_code (Or.inr rfl)]
                simp only [same_code_eq, codeBound, codeFreeParam, Bool.false_and,
                  ite_bool_false]
                decide
              · intro _
                exact ⟨by simp [hey], by rw [hey, codeFwd_code (Or.inr rfl)]⟩
              · intro hf
                rw [codeFreeS_param] at hf
                exact absurd hf Bool.false_ne_true.symm
            · have hLs : CodeId.same (.src (codeFreeParam, y₁)) (.src (codeFreeParam, y)) = false := by
                rw [same_src_eq]
                simp only [codeFreeParam, codeBound, Bool.false_and, ite_bool_false]
                exact decide_eq_false hey
              have hRs :
                  CodeId.same (.src (.code y₁ codeFreeParam))
                    (codeFwd (.src (codeFreeParam, y))) = false := by
                rw [codeFwd_code (Or.inr rfl)]
                simp only [same_code_eq, codeFreeParam, codeBound, Bool.false_and,
                  ite_bool_false]
                exact decide_eq_false hey
              refine Or.inl ⟨?_, ?_⟩
              · rw [hLs, Bool.false_and]
              · rw [hRs, Bool.false_and]
        · have hLs : CodeId.same x₁ (.src (o, y)) = false := by
            cases x₁ with
            | inst _ _ => simp [actSrcS] at hsrc
            | src p =>
                obtain ⟨o₁, y₁⟩ := p
                have hb1 : codeBound o₁ = false := by
                  simp only [holeRecS] at hS
                  cases hc : codeBound o₁ with
                  | false => rfl
                  | true =>
                      simp only [hc, Bool.not_true] at hS
                      exact absurd hS Bool.false_ne_true
                have hf1 : o₁ ≠ codeFreeParam := by
                  intro e
                  rw [e, codeFreeS_param] at hcS
                  exact Bool.false_ne_true hcS.symm
                rw [same_src_eq, hb1, Bool.false_and, ite_bool_false]
                rw [ite_bool_and_left hf1]
                exact decide_src_owner_ne fun he => by
                  rcases hbo with hbo | rfl
                  · rw [he] at hb1
                    exact Bool.false_ne_true (hb1.symm.trans hbo)
                  · exact hf1 he
          have hRs : CodeId.same x₂ (codeFwd (.src (o, y))) = false := by
            rw [codeFwd_code hbo]
            cases x₂ with
            | inst _ _ => simp [actSrcI] at hsrcI
            | src b =>
                cases b with
                | slot k =>
                    exact same_slot_code
                | par z pos =>
                    exact same_par_code
                | code y₂ o₂ =>
                    have hb2 : codeBound o₂ = false := by
                      simp only [holeRecI] at hI
                      cases hc : codeBound o₂ with
                      | false => rfl
                      | true =>
                          simp only [hc, Bool.not_true] at hI
                          exact absurd hI Bool.false_ne_true
                    have hf2 : o₂ ≠ codeFreeParam := by
                      intro e
                      rw [e, codeFreeI_param] at hcI
                      exact Bool.false_ne_true hcI.symm
                    rw [same_code_eq, hb2, Bool.false_and, ite_bool_false]
                    rw [ite_bool_and_left hf2]
                    exact decide_code_owner_ne fun he => by
                      rcases hbo with hbo | rfl
                      · rw [he] at hb2
                        exact Bool.false_ne_true (hb2.symm.trans hbo)
                      · exact hf2 he
          refine Or.inl ⟨?_, ?_⟩
          · rw [hLs, Bool.false_and]
          · rw [hRs, Bool.false_and]
      · obtain ⟨o₁, y₁, hx₁, hb1⟩ :
            ∃ o₁ y₁, x₁ = .src (o₁, y₁) ∧ codeBound o₁ = true := by
          cases x₁ with
          | inst _ _ => simp [actSrcS] at hsrc
          | src p =>
              obtain ⟨o₁, y₁⟩ := p
              refine ⟨o₁, y₁, rfl, ?_⟩
              simp only [holeRecS] at hS
              cases hc : codeBound o₁ with
              | true => rfl
              | false =>
                  simp only [hc, Bool.not_false] at hS
                  exact absurd hS Bool.false_ne_true.symm
        subst hx₁
        obtain ⟨y₂, o₂, hx₂, hb2⟩ :
            ∃ y₂ o₂, x₂ = .src (.code y₂ o₂) ∧ codeBound o₂ = true := by
          cases x₂ with
          | inst _ _ => simp [actSrcI] at hsrcI
          | src b =>
              cases b with
              | slot _ => simp [holeRecI] at hI
              | par _ _ => simp [holeRecI] at hI
              | code y₂ o₂ =>
                  refine ⟨y₂, o₂, rfl, ?_⟩
                  simp only [holeRecI] at hI
                  cases hc : codeBound o₂ with
                  | true => rfl
                  | false =>
                      simp only [hc, Bool.not_false] at hI
                      exact absurd hI Bool.false_ne_true.symm
        subst hx₂
        have ho12 : o₁ = o₂ := by simpa [ownerS, ownerI] using ho
        subst ho12
        rcases hbo with hbb | rfl
        · by_cases heo : o₁ = o
          · refine Or.inr ⟨?_, ?_, e₁, e₂, Or.inl ⟨hS, hI⟩, ?_, Or.inr (codeFreeS_bound hbb), ?_⟩
            · rw [heo, e₁, same_src_eq, hbb]
              simp only [eq_self, Bool.and_self, decide_eq_true trivial, if_pos trivial]
            · rw [heo, e₂, codeFwd_code (Or.inl hbb)]
              simp only [same_code_eq, hbb, eq_self, Bool.and_self,
                decide_eq_true trivial, if_pos trivial]
            · intro hf
              rw [codeFreeS_bound hb1] at hf
              exact absurd hf Bool.false_ne_true
            · intro _ m hm heq
              cases m with
              | inst _ _ =>
                  simp only [codeFwd] at heq
                  cases heq
              | src p =>
                  obtain ⟨om, ym⟩ := p
                  have hom : om = codeFreeParam :=
                    of_decide_eq_true (by simpa [codeFreeS] using hm)
                  subst hom
                  rw [codeFwd_code (o := codeFreeParam) (y := ym) (Or.inr rfl)] at heq
                  cases heq
                  simp only [codeFreeParam, codeBound] at hb1
                  exact Bool.false_ne_true hb1
          · have hLs : CodeId.same (.src (o₁, y₁)) (.src (o, y)) = false := by
              rw [same_src_eq, hb1, hbb]
              simp only [Bool.and_self]
              exact decide_eq_false heo
            have hRs : CodeId.same (.src (.code y₂ o₁)) (codeFwd (.src (o, y))) = false := by
              rw [codeFwd_code (Or.inl hbb)]
              simp only [same_code_eq, hb1, hbb, Bool.and_self]
              exact decide_eq_false heo
            refine Or.inl ⟨?_, ?_⟩
            · rw [hLs, Bool.false_and]
            · rw [hRs, Bool.false_and]
        · have hne : o₁ ≠ codeFreeParam := codeBound_ne_free hb1
          have hLs : CodeId.same (.src (o₁, y₁)) (.src (codeFreeParam, y)) = false := by
            rw [same_src_eq, hb1]
            unfold codeFreeParam at hne ⊢
            simp only [codeBound, Bool.and_false, ite_bool_false, decide_eq_false hne,
              Bool.false_and, ite_bool_false, decide_src_owner_ne hne]
          have hRs :
              CodeId.same (.src (.code y₂ o₁)) (codeFwd (.src (codeFreeParam, y))) = false := by
            rw [codeFwd_code (o := codeFreeParam) (y := y) (Or.inr rfl)]
            simp only [same_code_eq, hb1]
            unfold codeFreeParam at hne ⊢
            simp only [codeBound, Bool.and_false, ite_bool_false, decide_eq_false hne,
              Bool.false_and, ite_bool_false, decide_code_owner_ne hne]
          refine Or.inl ⟨?_, ?_⟩
          · rw [hLs, Bool.false_and]
          · rw [hRs, Bool.false_and]

theorem align_lam {μ μb : Nm (Slot X) → Nm (BId X)} {x₁ sb : Nm (Slot X)}
    {x₂ : Nm (BId X)} {b qb : Tm S (Slot X)}
    (hμb : ∀ x, x ≠ x₁ → μb x = μ x) (hμx : μb x₁ = x₂)
    (hpar : ∀ x ∈ freeParams b, x ≠ x₁ → μ x ≠ x₂)
    (hxe : codeFreeS x₁ = true → x₁ = sb ∧ x₂ = codeFwd x₁)
    (hcov : codeFreeS x₁ = true ∨ codeFreeS sb = false)
    (hsep : codeFreeS x₁ = false → ∀ m, codeFreeS m = true → x₂ ≠ codeFwd m)
    (ha : Align μ (.lam x₁ [] b) (.lam sb [] qb)) : Align μb b qb := by
  obtain ⟨hpins, hexact⟩ := ha
  refine ⟨?_, ?_⟩
  · intro m hm
    have hmf := codeFreePvars_free hm
    cases hf : codeFreeS x₁ with
    | true =>
        obtain ⟨rfl, hx2⟩ := hxe hf
        by_cases hm1 : m = x₁
        · rw [hm1, hμx, hx2]
        · rw [hμb m hm1]
          apply hpins
          simp only [codeFreePvars, List.mem_filter, decide_eq_true_eq]
          exact ⟨hm, hm1⟩
    | false =>
        have hm1 := ne_of_codeFree hf hmf
        have hsb : codeFreeS sb = false := by
          rcases hcov with h | h
          · rw [hf] at h
            exact absurd h Bool.false_ne_true
          · exact h
        have hmsb := ne_of_codeFree hsb hmf
        rw [hμb m hm1.symm]
        apply hpins
        simp only [codeFreePvars, List.mem_filter, decide_eq_true_eq]
        exact ⟨hm, hmsb.symm⟩
  · intro x hx m hm hμeq
    have hmf := codeFreePvars_free hm
    cases hf : codeFreeS x₁ with
    | true =>
        obtain ⟨rfl, hx2⟩ := hxe hf
        by_cases hx1 : x = x₁
        · rw [hx1, hμx, hx2] at hμeq
          exact hx1.trans (codeFwd_injective hμeq)
        · rw [hμb x hx1] at hμeq
          by_cases hm1 : m = x₁
          · rw [hm1, ← hx2] at hμeq
            exact absurd hμeq (hpar x hx hx1)
          · apply hexact x ?_ m ?_ hμeq
            · simp only [freeParams, List.mem_filter, decide_eq_true_eq]
              exact ⟨hx, hx1⟩
            · simp only [codeFreePvars, List.mem_filter, decide_eq_true_eq]
              exact ⟨hm, hm1⟩
    | false =>
        have hm1 := ne_of_codeFree hf hmf
        have hsb : codeFreeS sb = false := by
          rcases hcov with h | h
          · rw [hf] at h
            exact absurd h Bool.false_ne_true
          · exact h
        have hmsb := ne_of_codeFree hsb hmf
        by_cases hx1 : x = x₁
        · rw [hx1, hμx] at hμeq
          exact absurd hμeq (hsep hf m hmf)
        · rw [hμb x hx1] at hμeq
          apply hexact x ?_ m ?_ hμeq
          · simp only [freeParams, List.mem_filter, decide_eq_true_eq]
            exact ⟨hx, hx1⟩
          · simp only [codeFreePvars, List.mem_filter, decide_eq_true_eq]
            exact ⟨hm, hmsb.symm⟩

/-- Related code matches a fragment of sealed code on both sides together.
Free parameters of the subject are pinned by `Align`: a sealed `codeOf` has
none until a lambda is entered. -/
theorem match_frag [DecidableEq S] {ν μ : Nm (Slot X) → Nm (BId X)} {k : Kd}
    {Res : List (Nm (BId X))} {ok : Bool} {c₁ : Tm S (Slot X)} {c₂ : Tm S (BId X)}
    (h : Rel SC ν μ k Res ok c₁ c₂) (bound : List (Nm (Slot X)) := []) :
    ok = true → (∀ b ∈ bound, ∃ s, b = .src s) →
    ∀ (q : Tm S (Slot X)), frag q → Align μ c₁ q →
    ∀ (D : Set (Nm (Slot X))) (σ₁ : GStore S (Slot X)) (σ₂ : GStore S (BId X)),
      (∀ n ∈ freeNames c₁, n ∈ D) → Set.InjOn ν D → HoleInj (SC : Setting S (Slot X) (BId X)) ν D → SealOK (SC : Setting S (Slot X) (BId X)) D c₁ →
      (∀ n ∈ codeVars q, n ∈ D ∨ ∃ s, n = .src s ∧ (SC : Setting S (Slot X) (BId X)).root₁ s) →
      StoreRel SC ν D σ₁ σ₂ →
      OptRel (StoreRel SC ν D) (matchCodeIn σ₁ bound c₁ q)
        (matchCodeIn σ₂ (bound.map codeFwd) c₂ (mapCode (holeRead (SC : Setting S (Slot X) (BId X)) ν) q)) := by
  induction h generalizing bound with
  | sym s =>
      intro _ _ q _ _ _ σ₁ σ₂ _ _ _ _ _ hσ
      cases q with
      | sym s' =>
          simp only [matchCodeIn, mapCode]
          by_cases hs : s = s'
          · simp only [if_pos hs]
            exact hσ
          · simp only [if_neg hs]
            trivial
      | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | fn F =>
      intro _ _ q _ _ _ σ₁ σ₂ _ _ _ _ _ hσ
      cases q with
      | fn F' =>
          simp only [matchCodeIn, mapCode]
          by_cases hs : F = F'
          · simp only [if_pos hs]
            exact hσ
          · simp only [if_neg hs]
            trivial
      | sym _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | @var ν _ _ n hv =>
      intro _ hbd q hq _ D σ₁ σ₂ hD hinj hI _ hqs hσ
      simp only [SC, scVarHole] at hv
      have hbit : CodeId.hole n = CodeId.hole (ν n) := by
        rw [hole_eq_holeRecS, hv, ← hole_eq_holeRecI]
      cases hb : CodeId.hole n with
      | false =>
          have hb2 : CodeId.hole (ν n) = false := by rw [← hbit, hb]
          obtain ⟨e1, e2⟩ :=
            var_binder_none (ν := ν) hb hb2 hq bound (bound.map codeFwd) σ₁ σ₂
          rw [e1, e2]
          trivial
      | true =>
          have hb2 : CodeId.hole (ν n) = true := by rw [← hbit, hb]
          exact hole_refine hσ hinj hI (hD n (by simp [freeNames])) hb hb2 hq hqs bound hbd
  | @pvar _ μ _ x hp =>
      intro _ _ q hq ha _ σ₁ σ₂ _ _ _ _ _ hσ
      simp only [SC] at hp
      cases q with
      | pvar m =>
          obtain ⟨om, ym, rfl, hbm⟩ := hq
          rcases hp with ⟨hc1, hc2, ho⟩ | ⟨hn1, hn2⟩
          · obtain ⟨ox, yx, hx, hbx⟩ :
                ∃ ox yx, x = .src (ox, yx) ∧ (codeBound ox = true ∨ ox = codeFreeParam) := by
              cases x with
              | inst _ _ => simp [codeParamS] at hc1
              | src p =>
                  obtain ⟨ox, yx⟩ := p
                  exact ⟨ox, yx, rfl, by simpa [codeParamS] using hc1⟩
            subst hx
            obtain ⟨yμ, oμ, hμx, hbμ⟩ :
                ∃ yμ oμ, μ (.src (ox, yx)) = .src (.code yμ oμ) ∧
                  (codeBound oμ = true ∨ oμ = codeFreeParam) := by
              cases hμ : μ (.src (ox, yx)) with
              | inst _ _ => simp [codeParamI, hμ] at hc2
              | src b =>
                  cases b with
                  | slot _ => simp [codeParamI, hμ] at hc2
                  | par _ _ => simp [codeParamI, hμ] at hc2
                  | code yμ oμ =>
                      exact ⟨yμ, oμ, rfl, by simpa [codeParamI, hμ] using hc2⟩
            rw [hμx] at ho ⊢
            have hox : ox = oμ := by simpa [ownerS, ownerI] using ho
            subst hox
            simp only [matchCodeIn, mapCode, holeRead_src_SC]
            rw [codeFwd_code hbm]
            rcases hbx with hbx | rfl
            · rcases hbm with hbm | rfl
              · rw [same_src_eq, same_code_eq, hbx, hbm]
                simp only [Bool.and_self]
                by_cases heo : ox = om
                · simp only [heo]
                  exact hσ
                · simp only [decide_eq_false heo]
                  trivial
              · have hne : ox ≠ codeFreeParam := codeBound_ne_free hbx
                rw [same_src_eq, same_code_eq, hbx]
                unfold codeFreeParam at hne ⊢
                simp only [codeBound, Bool.and_false, ite_bool_false, decide_eq_false hne,
                  Bool.false_and, ite_bool_false, decide_src_owner_ne hne,
                  decide_code_owner_ne hne]
                trivial
            · rcases hbm with hbm | rfl
              · have hne : om ≠ codeFreeParam := codeBound_ne_free hbm
                rw [same_src_eq, same_code_eq, hbm]
                unfold codeFreeParam at hne ⊢
                simp only [codeBound, Bool.false_and, ite_bool_false, decide_eq_false hne,
                  Bool.and_false, ite_bool_false, decide_src_owner_ne hne.symm,
                  decide_code_owner_ne hne.symm]
                trivial
              · rw [same_src_eq, same_code_eq]
                by_cases hey : yx = ym
                · rw [hey] at hμx ⊢
                  have hpin : μ (.src (codeFreeParam, ym)) =
                      codeFwd (.src (codeFreeParam, ym)) := by
                    refine ha.1 _ ?_
                    simp [codeFreePvars, codeFreeS_param]
                  have hym : yμ = ym := by
                    have hfwd : codeFwd (.src (codeFreeParam, ym)) =
                        .src (.code ym codeFreeParam) := codeFwd_code (Or.inr rfl)
                    have h := hμx.symm.trans (hpin.trans hfwd)
                    simp only [Nm.src.injEq, BId.code.injEq] at h
                    exact h.1
                  rw [hym]
                  simp only [codeFreeParam, codeBound, eq_self, decide_eq_true trivial]
                  exact hσ
                · by_cases hyμ : yμ = ym
                  · exfalso
                    rw [hyμ] at hμx
                    have hxeq : (Nm.src (codeFreeParam, yx) : Nm (Slot X)) =
                        Nm.src (codeFreeParam, ym) := by
                      refine ha.2 _ ?_ _ ?_ ?_
                      · simp [freeParams]
                      · simp [codeFreePvars, codeFreeS_param]
                      · rw [codeFwd_code (Or.inr rfl)]
                        exact hμx
                    simp only [Nm.src.injEq, Prod.mk.injEq] at hxeq
                    exact hey hxeq.2
                  · simp only [codeFreeParam, codeBound, decide_eq_false hey, decide_eq_false hyμ]
                    trivial
          · have hLs : CodeId.same x (.src (om, ym)) = false := by
              cases x with
              | inst _ _ => exact same_instL_src
              | src p =>
                  obtain ⟨ox, yx⟩ := p
                  have hb1 : codeBound ox = false := by
                    by_cases hc : codeBound ox = true
                    · exact absurd (Or.inl hc) hn1
                    · exact Bool.eq_false_iff.mpr hc
                  have hf1 : ox ≠ codeFreeParam := fun h => hn1 (Or.inr h)
                  rw [same_src_eq, hb1, Bool.false_and, ite_bool_false]
                  rw [ite_bool_and_left hf1]
                  exact decide_src_owner_ne fun he => by
                    rcases hbm with hbm | rfl
                    · rw [he] at hb1
                      exact Bool.false_ne_true (hb1.symm.trans hbm)
                    · exact hf1 he
            have hRs : CodeId.same (μ x) (codeFwd (.src (om, ym))) = false := by
              rw [codeFwd_code hbm]
              cases hx : μ x with
              | inst _ _ =>
                  exact same_instI_src
              | src b =>
                  cases b with
                  | slot _ =>
                      exact same_slot_code
                  | par _ _ =>
                      exact same_par_code
                  | code yμ oμ =>
                      have hnot : ¬ (codeBound oμ = true ∨ oμ = codeFreeParam) := by
                        intro h
                        exact hn2 (by simp [codeParamI, hx, h])
                      have hb2 : codeBound oμ = false := Bool.eq_false_iff.mpr fun h => hnot (Or.inl h)
                      have hf2 : oμ ≠ codeFreeParam := fun h => hnot (Or.inr h)
                      rw [same_code_eq, hb2, Bool.false_and, ite_bool_false]
                      rw [ite_bool_and_left hf2]
                      exact decide_code_owner_ne fun he => by
                        rcases hbm with hbm | rfl
                        · rw [he] at hb2
                          exact Bool.false_ne_true (hb2.symm.trans hbm)
                        · exact hf2 he
            simp only [matchCodeIn, mapCode, holeRead_src_SC, hLs, hRs, ite_bool_false]
            trivial
      | sym _ | fn _ | var _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | @quote _ _ _ c _ hq =>
      intro _ _ q hqf _ D σ₁ σ₂ _ _ hI hS hqs hσ
      cases q with
      | quote cq =>
          obtain ⟨_, _, _, _, hcf⟩ := hqf
          obtain ⟨-, hcf₁, rfl⟩ := hq
          have hinjq := holeRead_injOn hI hcf₁ hcf
            (fun n hn => (hS n (by simpa [sealedFree] using hn)).elim Or.inr
              fun ⟨s, e, _⟩ => Or.inl ⟨s, e⟩)
            (fun n hn => (hqs n (by simpa [codeVars] using hn)).elim Or.inr
              fun ⟨s, e, _⟩ => Or.inl ⟨s, e⟩)
          simp only [matchCodeIn, mapCode, codeEq_holeRead hcf₁ hcf hinjq]
          cases hce : codeEq c cq with
          | false =>
              simp only [ite_bool_false]
              trivial
          | true => exact hσ
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | @pquote _ μ _ pc₁ _ _ hbody _ hokb ih =>
      intro _ hbd q hq ha D σ₁ σ₂ hD hinj hI hS hqs hσ
      cases q with
      | quote cq =>
          obtain ⟨Rq, s, hRq, hs, hcf⟩ := hq
          obtain ⟨hfr, hfp⟩ := frag_of_codeForm hRq hs hcf
          have hAl : Align μ pc₁ cq :=
            ⟨fun m hm => by simp [hfp] at hm,
             fun _ _ m hm => by simp [hfp] at hm⟩
          simp only [matchCodeIn, mapCode]
          exact ih bound hokb hbd cq hfr hAl D σ₁ σ₂
            (fun n hn => hD n (by simpa [freeNames] using hn)) hinj hI
            (fun n hn => hS n (by simpa [sealedFree] using hn))
            (fun n hn => hqs n (by simpa [codeVars] using hn)) hσ
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | app _ _ ihf iha =>
      intro hok hbd q hq ha D σ₁ σ₂ hD hinj hI hS hqs hσ
      have ho := Bool.and_eq_true_iff.mp hok
      cases q with
      | app qf qa =>
          obtain ⟨hqf, hqa⟩ := hq
          obtain ⟨hpins, hexact⟩ := ha
          have hAf : Align _ _ qf :=
            ⟨fun m hm => hpins m (List.mem_append_left _ hm),
             fun x hx m hm hμ => hexact x (List.mem_append_left _ hx) m
               (List.mem_append_left _ hm) hμ⟩
          have hAa : Align _ _ qa :=
            ⟨fun m hm => hpins m (List.mem_append_right _ hm),
             fun x hx m hm hμ => hexact x (List.mem_append_right _ hx) m
               (List.mem_append_right _ hm) hμ⟩
          simp only [mapCode]
          rw [matchCodeIn_app_bind (bound := bound) (σ := σ₁),
            matchCodeIn_app_bind (bound := bound.map codeFwd) (σ := σ₂)]
          exact opt_seq (ihf bound ho.1 hbd qf hqf hAf D σ₁ σ₂
              (fun n hn => hD n (List.mem_append_left _ hn)) hinj hI
              (fun n hn => hS n (by simp [sealedFree, hn]))
              (fun n hn => hqs n (by simp [codeVars, hn])) hσ)
            (fun σ₁' σ₂' hσ' => iha bound ho.2 hbd qa hqa hAa D σ₁' σ₂'
              (fun n hn => hD n (List.mem_append_right _ hn)) hinj hI
              (fun n hn => hS n (by simp [sealedFree, hn]))
              (fun n hn => hqs n (by simp [codeVars, hn])) hσ')
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | letP _ hp hw hb ihp ihw ihb =>
      intro hok hbd q hq ha D σ₁ σ₂ hD hinj hI hS hqs hσ
      have h3 := Bool.and_eq_true_iff.mp hok
      have h12 := Bool.and_eq_true_iff.mp h3.1
      cases q with
      | letP qp qw qb =>
          obtain ⟨hqp, hqw, hqb⟩ := hq
          obtain ⟨hpins, hexact⟩ := ha
          have memL {n : Nm (Slot X)} {a b c : List (Nm (Slot X))}
              (h : n ∈ a) : n ∈ a ++ b ++ c :=
            List.mem_append_left _ (List.mem_append_left _ h)
          have memM {n : Nm (Slot X)} {a b c : List (Nm (Slot X))}
              (h : n ∈ b) : n ∈ a ++ b ++ c :=
            List.mem_append_left _ (List.mem_append_right _ h)
          have memR {n : Nm (Slot X)} {a b c : List (Nm (Slot X))}
              (h : n ∈ c) : n ∈ a ++ b ++ c :=
            List.mem_append_right _ h
          simp only [mapCode]
          rw [matchCodeIn_letP_bind (bound := bound) (σ := σ₁),
            matchCodeIn_letP_bind (bound := bound.map codeFwd) (σ := σ₂)]
          exact opt_seq (ihp bound h12.1 hbd qp hqp
              ⟨fun m hm => hpins m (memL hm),
               fun x hx m hm hμ => hexact x (memL hx) m (memL hm) hμ⟩
              D σ₁ σ₂ (fun n hn => hD n (memL hn)) hinj hI (fun n hn => hS n (memL hn))
              (fun n hn => hqs n (memL hn)) hσ)
            (fun σa σb hσab =>
              opt_seq (ihw bound h12.2 hbd qw hqw
                  ⟨fun m hm => hpins m (memM hm),
                   fun x hx m hm hμ => hexact x (memM hx) m (memM hm) hμ⟩
                  D σa σb (fun n hn => hD n (memM hn)) hinj hI (fun n hn => hS n (memM hn))
                  (fun n hn => hqs n (memM hn)) hσab)
                (fun σc σd hσcd => ihb bound h3.2 hbd qb hqb
                  ⟨fun m hm => hpins m (memR hm),
                   fun x hx m hm hμ => hexact x (memR hx) m (memR hm) hμ⟩
                  D σc σd (fun n hn => hD n (memR hn)) hinj hI (fun n hn => hS n (memR hn))
                  (fun n hn => hqs n (memR hn)) hσcd))
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | alt _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | alt _ _ _ ih1 ih2 =>
      intro hok hbd q hq ha D σ₁ σ₂ hD hinj hI hS hqs hσ
      have ho := Bool.and_eq_true_iff.mp hok
      cases q with
      | alt q1 q2 =>
          obtain ⟨hq1, hq2⟩ := hq
          obtain ⟨hpins, hexact⟩ := ha
          simp only [mapCode]
          rw [matchCodeIn_alt_bind (bound := bound) (σ := σ₁),
            matchCodeIn_alt_bind (bound := bound.map codeFwd) (σ := σ₂)]
          exact opt_seq (ih1 bound ho.1 hbd q1 hq1
              ⟨fun m hm => hpins m (List.mem_append_left _ hm),
               fun x hx m hm hμ => hexact x (List.mem_append_left _ hx) m
                 (List.mem_append_left _ hm) hμ⟩
              D σ₁ σ₂ (fun n hn => hD n (List.mem_append_left _ hn)) hinj hI
              (fun n hn => hS n (by simp [sealedFree, hn]))
              (fun n hn => hqs n (by simp [codeVars, hn])) hσ)
            (fun σa σb hσab => ih2 bound ho.2 hbd q2 hq2
              ⟨fun m hm => hpins m (List.mem_append_right _ hm),
               fun x hx m hm hμ => hexact x (List.mem_append_right _ hx) m
                 (List.mem_append_right _ hm) hμ⟩
              D σa σb (fun n hn => hD n (List.mem_append_right _ hn)) hinj hI
              (fun n hn => hS n (by simp [sealedFree, hn]))
              (fun n hn => hqs n (by simp [codeVars, hn])) hσab)
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | @lam ν _ _ x₁ own₁ b₁ x₂ own₂ _ νb μb _ _ hνb hμb hμx _ _ hb _ _ _ _ _ hpar hbare hseen _ _
      ih =>
      intro _ hbd q hq ha D σ₁ σ₂ hD hinj hI hS hqs hσ
      simp only [SC] at hbare
      cases q with
      | lam sb _ qb =>
          obtain ⟨rfl, hnamed, hqb⟩ := hq
          obtain ⟨o, y, rfl, hbo⟩ := hnamed
          simp only [matchCodeIn, mapCode, holeRead_src_SC]
          rcases gate_split hbare hbo with ⟨hL, hR⟩ | ⟨hL, hR, hown1, _, hent, hxe, hcov, hsep⟩
          · rw [hL, hR]
            simp only [ite_bool_false]
            trivial
          · rw [hL, hR]
            have hob : _ = true := hseen hent
            have hν : νb = ν := by
              funext n
              exact hνb n (by rw [hown1]; exact ownKey_nil n)
            have hxe' : codeFreeS x₁ = true → x₁ = .src (o, y) ∧ x₂ = codeFwd x₁ := by
              intro hf
              obtain ⟨rfl, hx2⟩ := hxe hf
              exact ⟨rfl, hx2⟩
            have hAl := align_lam hμb hμx hpar hxe' hcov hsep (by
              simpa [hown1] using ha)
            have hbd' : ∀ b ∈ bound ++ [.src (o, y)], ∃ s, b = Nm.src s := by
              intro b hb
              rcases List.mem_append.1 hb with hb | hb
              · exact hbd b hb
              · simp only [List.mem_singleton] at hb
                exact ⟨_, hb⟩
            have hih := ih (bound ++ [.src (o, y)]) hob hbd' qb hqb hAl D σ₁ σ₂
              (by simpa [hown1, freeNames_lam_nil] using hD)
              (by simpa [hν] using hinj) (by simpa [hν] using hI)
              (fun n hn => hS n (by simp [sealedFree, hn, hown1, ownKey_nil]))
              (fun n hn => hqs n (by simpa [codeVars] using hn)) (by simpa [hν] using hσ)
            rw [List.map_append, List.map_singleton] at hih
            simpa [hν, hown1, freeNames_lam_nil] using hih
      | sym _ | fn _ | var _ | pvar _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | ctx _ _ _ =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _
      simp only [matchCodeIn]
      trivial
  | letAct _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro hok
      exact absurd hok Bool.false_ne_true
  | newAct _ _ _ _ _ _ _ =>
      intro hok
      exact absurd hok Bool.false_ne_true

/-- **Related pattern code matches related sealed code.** A hole binds a ground
value on both sides together. A binder of code is entered only when both sides
name that binder, and then the body matches. -/
theorem SC_patAgree [DecidableEq S] : (SC : Setting S (Slot X) (BId X)).PatAgree := by
  intro ν μ _ c₁ c₂ q₁ q₂ D σ₁ σ₂ hrel hok _ hQ hD hinj hI hS hSq hσ
  obtain ⟨⟨R, s, hR, hs, -⟩, hcf, rfl⟩ := hQ
  obtain ⟨hfr, hfp⟩ := frag_of_codeForm hR hs hcf
  have hAl : Align μ c₁ q₁ :=
    ⟨fun m hm => by simp [hfp] at hm, fun _ _ m hm => by simp [hfp] at hm⟩
  simpa [matchCode] using
    match_frag (bound := []) hrel hok (fun _ h => by cases h) q₁ hfr hAl D σ₁ σ₂ hD hinj hI hS
      (fun n hn => hSq n (by simpa [sealedFree] using hn)) hσ

/-! ## The root of a form -/

/-- An admissible identity is apart from every reserved name, when a free
name of its spelling is live. -/
theorem ResOK.key_not_mem {F : Owner} {A : Ann S X} {t₁ : Tm S (Slot X)} {t₂ : Tm S (BId X)}
    {Res : List (Nm (BId X))} (hres : ResOK F F A t₁ t₂ Res) {k : SlotId X} (hk : KeyOK F A k)
    {n : Nm (Slot X)} (hn : n ∈ freeNames t₁) (hsp : spellS n = k.spell) :
    (.src (.slot k) : Nm (BId X)) ∉ Res := by
  intro hm
  obtain ⟨k', hk', -, hkh, q, hq, hpat⟩ := hres.shape _ hm
  injection hk' with hk'
  injection hk' with hk'
  subst hk'
  rcases hk with hh | ⟨hn', hs⟩ | ⟨hp, P, hP, hnot⟩
  · exact hkh hh
  · exact hres.news k hm hn' hs n hn hsp
  · rw [hP] at hq
    have hPq : P = q := List.append_cancel_left hq
    subst hPq
    exact hnot (hpat hp)

/-- **The query's configuration**: at the root `[]`, with the root's
identities, the two elaborations of well-formed annotated text start related,
with empty stores. -/
theorem root_config {A : Ann S X} {rk : X → SlotId X} (hwf : A.WF []) (hpars : A.freePars = [])
    (hrk : ∀ y, (rk y).spell = y ∧ (rk y).frame = [] ∧ KeyOK [] A (rk y)) :
    ∃ (ν μ : Nm (Slot X) → Nm (BId X)) (Res : List (Nm (BId X))) (D : Set (Nm (Slot X)))
      (ok : Bool),
      Rel SC ν μ .code Res ok (A.slotOf [] (fun _ => []) []) (A.idOf [] rk (fun _ => []) [] []) ∧
      freeParams (A.slotOf [] (fun _ => []) []) = [] ∧
      (∀ x ∈ freeNames (A.slotOf [] (fun _ => []) []), x ∈ D) ∧
      SealOK (SC : Setting S (Slot X) (BId X)) D (A.slotOf [] (fun _ => []) []) ∧
      CI (SC : Setting S (Slot X) (BId X)) ν D (Res ++ []) Store.empty Store.empty ∧ Fresh [] [] ν D (Res ++ []) := by
  obtain ⟨Res, hrel, hres⟩ := rel_ann (Or.inl rfl) A (k := .code) (env := fun _ => []) (posS := [])
    (envI := rk)
    (pv := fun _ => []) (fr := []) (posI := []) (ν := fun n => .src (.slot (rk (spellS n))))
    (μ := fun n => .src (.par (spellS n) [])) hwf (by decide) (fun h => by cases h)
    (fun _ _ => rfl) (fun y _ => ⟨(hrk y).1, by rw [(hrk y).2.1]; exact List.prefix_refl _⟩)
    (List.prefix_refl _)
    (by intro z hz; rw [hpars] at hz; cases hz) scopeOwners_nil PosSafe.root
  have hfree : ∀ n ∈ freeNames (A.slotOf [] (fun _ => []) []), ∃ y, n = .src ([], y) := by
    intro n hn
    obtain ⟨y, _, rfl⟩ := Ann.freeNames_slotOf [] A _ _ n (Ann.Open.of_WF hwf) hn
    exact ⟨y, rfl⟩
  refine ⟨_, _, Res, {n | n ∈ freeNames (A.slotOf [] (fun _ => []) [])}, annOK A, hrel, ?_,
    fun x hx => hx, ?_, ?_, ?_⟩
  · apply List.eq_nil_iff_forall_not_mem.2
    intro x hx
    obtain ⟨z, hz, _⟩ := Ann.freeParams_slotOf [] A _ _ x (Ann.Open.of_WF hwf) hx
    rw [hpars] at hz
    cases hz
  · intro n hn
    obtain ⟨y, rfl⟩ := Ann.sealedFree_slotOf [] A _ _ n hn
    exact Or.inr ⟨_, rfl, rfl⟩
  · rw [List.append_nil]
    refine ⟨?_, hres.nodup, ?_, StoreRel.empty _ _, ?_, ?_, ?_, ?_, ?_⟩
    · intro n hn n' hn' he
      obtain ⟨y, rfl⟩ := hfree n hn
      obtain ⟨y', rfl⟩ := hfree n' hn'
      simp only [spellS] at he
      injection he with he
      injection he with he
      have hyy : y = y' := by rw [← (hrk y).1, ← (hrk y').1, he]
      rw [hyy]
    · intro n hn hm
      obtain ⟨y, rfl⟩ := hfree n hn
      exact hres.key_not_mem (hrk y).2.2 hn (by simp [spellS, (hrk y).1]) hm
    · intro n hn
      obtain ⟨y, rfl⟩ := hfree n hn
      rfl
    · intro n _
      exact ⟨rk (spellS n), rfl, (hrk _).2.1⟩
    · intro m hm
      obtain ⟨k, rfl, hk, -⟩ := hres.shape m hm
      exact ⟨k, rfl, hk⟩
    · intro n hn hc
      obtain ⟨y, rfl⟩ := hfree n hn
      exact False.elim hc
    · intro n hn _ _ hc
      obtain ⟨y, rfl⟩ := hfree n hn
      exact False.elim hc
  · rw [List.append_nil]
    refine ⟨fun n hn => ?_, fun _ _ => oldAt_src _ _, fun m hm => ?_⟩
    · obtain ⟨y, rfl⟩ := hfree n hn
      exact oldAt_src _ _
    · obtain ⟨k, rfl, -⟩ := hres.shape m hm
      exact oldAt_src _ _

/-- **A clause**: rooted at `[5]`, its wrapper activation owns the root's
names and the holes of its sealed code on both sides; the two clause terms are
closed, their sealed code included, and related under every name map. -/
theorem clause_rel {A : Ann S X} {rk : X → SlotId X} {own : List X} (u : X) (unit : S)
    (hwf : A.WF [5]) (hpars : A.freePars = []) (hown : ∀ y ∈ A.names, y ∈ own)
    (hrk : ∀ y, (rk y).spell = y ∧ (rk y).frame = [5] ∧ KeyOK [5] A (rk y))
    (hnew : ∀ y, (rk y).intro ≠ .new) :
    freeNames (.app (.lam (.src ([5] ++ [9], u))
      ((own ++ holeSpellings [5] (A.slotOf [5] (fun _ => [5]) [5])).map fun y => ([5], y))
      (A.slotOf [5] (fun _ => [5]) [5])) (.sym unit) : Tm S (Slot X)) = [] ∧
    freeParams (.app (.lam (.src ([5] ++ [9], u))
      ((own ++ holeSpellings [5] (A.slotOf [5] (fun _ => [5]) [5])).map fun y => ([5], y))
      (A.slotOf [5] (fun _ => [5]) [5])) (.sym unit) : Tm S (Slot X)) = [] ∧
    sealedFree (.app (.lam (.src ([5] ++ [9], u))
      ((own ++ holeSpellings [5] (A.slotOf [5] (fun _ => [5]) [5])).map fun y => ([5], y))
      (A.slotOf [5] (fun _ => [5]) [5])) (.sym unit) : Tm S (Slot X)) = [] ∧
    ∀ ν μ, Rel SC ν μ .code [] true
      (.app (.lam (.src ([5] ++ [9], u))
        ((own ++ holeSpellings [5] (A.slotOf [5] (fun _ => [5]) [5])).map fun y => ([5], y))
        (A.slotOf [5] (fun _ => [5]) [5])) (.sym unit))
      (.app (.lam (.src (.par u ([5] ++ [9]))) (frameSlots [5] (A.idOf [5] rk (fun _ => [5]) [5] [5]))
        (A.idOf [5] rk (fun _ => [5]) [5] [5])) (.sym unit)) := by
  set H := holeSpellings [5] (A.slotOf [5] (fun _ => [5]) [5]) with hH
  have hfp : freeParams (A.slotOf [5] (fun _ => [5]) [5]) = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro x hx
    obtain ⟨z, hz, _⟩ := Ann.freeParams_slotOf [5] A _ _ x (Ann.Open.of_WF hwf) hx
    rw [hpars] at hz
    cases hz
  have hown' : ∀ y ∈ A.names, y ∈ own ++ H := fun y hy => List.mem_append_left _ (hown y hy)
  have hhole : ∀ n ∈ sealedFree (A.slotOf [5] (fun _ => [5]) [5]),
      ∃ y ∈ own ++ H, n = .src ([5], y) := by
    intro n hn
    obtain ⟨y, rfl⟩ := Ann.sealedFree_slotOf [5] A _ _ n hn
    exact ⟨y, List.mem_append_right _ (mem_holeSpellings hn), rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [freeNames, List.append_nil]
    apply List.eq_nil_iff_forall_not_mem.2
    intro n hn
    obtain ⟨hn, ho⟩ := List.mem_filter.1 hn
    obtain ⟨y, hy, rfl⟩ := Ann.freeNames_slotOf [5] A _ _ n (Ann.Open.of_WF hwf) hn
    rw [ownKey_map_src] at ho
    simp [hown' y hy] at ho
  · simp [freeParams, hfp]
  · simp only [sealedFree, List.append_nil]
    apply List.eq_nil_iff_forall_not_mem.2
    intro n hn
    obtain ⟨hn, ho⟩ := List.mem_filter.1 hn
    obtain ⟨y, hy, rfl⟩ := hhole n hn
    rw [ownKey_map_src] at ho
    simp [hy] at ho
  · intro ν μ
    obtain ⟨Rb, hrel, hres⟩ := rel_ann (Or.inr rfl) A (k := .code) (env := fun _ => [5])
      (posS := [5]) (envI := rk) (pv := fun _ => [5]) (fr := [5]) (posI := [5])
      (ν := bindν ν [5] (own ++ H) rk)
      (μ := Function.update μ (.src ([5] ++ [9], u)) (.src (.par u ([5] ++ [9])))) hwf (by decide)
      (fun h => by cases h) (fun y hy => bindν_on (hown' y hy))
      (fun y _ => ⟨(hrk y).1, by rw [(hrk y).2.1]; exact List.prefix_refl _⟩) (List.prefix_refl _)
      (by intro z hz; rw [hpars] at hz; cases hz) scopeOwners_five PosSafe.clause
    obtain ⟨hownk, hresb, -, -⟩ := frame_conds (key := rk) hrel hres (fun _ _ _ => rfl)
      (fun y hy => bindν_on hy) (fun y hy hyo => absurd (hown' y hy) hyo) (fun y _ => hrk y)
      (Ann.Open.of_WF hwf)
    have hoK : ∀ n, ownKey ((own ++ H).map fun y => ([5], y)) n = true →
        ∃ y, n = .src ([5], y) ∧ bindν ν [5] (own ++ H) rk n = .src (.slot (rk y)) := by
      intro n ho
      obtain ⟨y, hy, rfl⟩ := ownKey_map_true ho
      exact ⟨y, rfl, bindν_on hy⟩
    refine .app (.lam (fun n hn => bindν_off hn) (fun x hx => Function.update_of_ne hx _ _)
      (Function.update_self _ _ _) ?_ ?_ hrel hownk hresb ?_ ?_ hres.nodup ?_
      (by
        refine Or.inl ⟨?_, rfl, Or.inr ⟨?_, rfl⟩, fun hcf => ?_, rfl⟩
        · simp only [holeRecS, codeBound]
          rfl
        · simp only [codeFreeS, codeFreeParam]
          rfl
        · have hc : codeFreeS (.src ([5] ++ [9], u)) = false := by
            simp only [codeFreeS, codeFreeParam]
            rfl
          exact absurd (hc.symm.trans hcf.1) Bool.false_ne_true)
      (by
        intro hent
        simp only [SC, scEnter, holeRecS, holeRecI, codeFreeS, codeFreeI, codeBound,
          codeFreeParam] at hent
        rcases hent with hent | hent
        · exact absurd hent.1 Bool.false_ne_true.symm
        · exact absurd hent.1 Bool.false_ne_true) ?_ ?_) (.sym unit)
    · intro s hs h
      obtain ⟨y, _, rfl⟩ := List.mem_map.1 hs
      exact (by simp : ([5] : Owner) ≠ []) h
    · intro s hs h
      obtain ⟨k', rfl, hkF⟩ := frame_of_mem_frameSlots hs
      obtain ⟨k'', hk'', hk0⟩ := h
      injection hk'' with hk''
      subst hk''
      rw [hkF] at hk0
      simp at hk0
    · intro n _ n' _ ho ho' he
      obtain ⟨y, rfl, hy⟩ := hoK n ho
      obtain ⟨y', rfl, hy'⟩ := hoK n' ho'
      rw [hy, hy'] at he
      have hkk : rk y = rk y' := by
        injection he with he
        injection he
      have hyy : y = y' := by rw [← (hrk y).1, ← (hrk y').1, hkk]
      rw [hyy]
    · intro n _ ho hmem
      obtain ⟨y, rfl, hy⟩ := hoK n ho
      rw [hy] at hmem
      obtain ⟨k, hk, -, hkh, q, hq, hpat⟩ := hres.shape _ hmem
      have hkk : rk y = k := by
        injection hk with hk
        injection hk
      subst hkk
      rcases (hrk y).2.2 with hh | ⟨hn', -⟩ | ⟨hp, P, hP, hnot⟩
      · exact hkh hh
      · exact hnew y hn'
      · rw [hP] at hq
        have hPq : P = q := List.append_cancel_left hq
        subst hPq
        exact hnot (hpat hp)
    · intro x hx
      rw [hfp] at hx
      cases hx
    · intro s hs
      obtain ⟨y, hy⟩ := Ann.sealedFree_slotOf [5] A _ _ _ hs
      injection hy with hy
      subst hy
      have h1 : ownKey ((own ++ H).map fun y => ([5], y)) (.src ([5], y) : Nm (Slot X)) = true := by
        rw [ownKey_map_src]
        exact decide_eq_true ⟨rfl, List.mem_append_right _ (mem_holeSpellings hs)⟩
      rw [h1]
      change ownKey _ (codeFwd (.src ([5], y))) = true
      rw [codeFwd_scope (formRoot.scopeOwner (Or.inr rfl))]
      simpa only [ownKey, List.contains_eq_mem, decide_eq_true_eq] using
        Ann.hole_mem_frameSlots (Or.inr rfl) hrel hs
    · intro n _ ho
      obtain ⟨y, -, hy⟩ := hoK n ho
      exact ⟨_, hy⟩

/-! ## Rule M's and lexical fresh's roots -/

theorem mRootEnv_ok (R : Owner) (t : Src S X) (E cr : List X) (env : IEnv X) (y : X) :
    (mRootEnv R t y).spell = y ∧ (mRootEnv R t y).frame = R ∧
      KeyOK R (annM E cr env R R t) (mRootEnv R t y) := by
  unfold mRootEnv
  cases h : findCover (Src.direct t) y false t with
  | none => exact ⟨rfl, rfl, Or.inl rfl⟩
  | some P =>
      exact ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, P, rfl, findCover_not_letA t _ y _ P h _ _ _ _ _⟩)⟩

omit [DecidableEq X] in
theorem lfRootEnv_ok (R : Owner) (A : Ann S X) (y : X) :
    (lfRootEnv R y).spell = y ∧ (lfRootEnv R y).frame = R ∧ KeyOK R A (lfRootEnv R y) :=
  ⟨rfl, rfl, Or.inl rfl⟩

/-- Rule M's root identities are made by the root or by a pattern, never by a
`new` block. -/
theorem mRootEnv_intro (R : Owner) (t : Src S X) (y : X) : (mRootEnv R t y).intro ≠ .new := by
  unfold mRootEnv
  cases findCover (Src.direct t) y false t <;> simp

omit [DecidableEq X] in
theorem lfRootEnv_intro (R : Owner) (y : X) : (lfRootEnv R y).intro ≠ .new := by
  simp [lfRootEnv]

/-! ## Programs -/

/-- The equations of a program in the slot model, each clause elaborated as its
own form at the root `[5]` (as `SpectrumCorpus.progOf` does). -/
def progSlot (c : Config) (u : X) (unit : S) (cl : S → Option (Src S X)) :
    S → Option (Tm S (Slot X)) :=
  fun F => (cl F).map (clauseOf c [5] u unit)

/-- **Rule M's programs are related.** -/
theorem progRel_M (u : X) (unit : S) (cl : S → Option (Src S X))
    (hcl : ∀ F body, cl F = some body → body.Admissible) :
    ProgRel SC (progSlot cfgM u unit cl) (progM u unit cl) := by
  intro F
  simp only [progSlot, progM]
  cases h : cl F with
  | none => trivial
  | some body =>
      obtain ⟨h₂, h₃⟩ := hcl F body h
      have e₁ : clauseOf cfgM [5] u unit body =
          .app (.lam (.src ([5] ++ [9], u))
            (((Src.names body).dedup ++ holeSpellings [5]
              ((annM (Src.direct body) [] (mRootEnv [5] body) [5] [5] body).slotOf [5]
                (fun _ => [5]) [5])).map fun y => ([5], y))
            ((annM (Src.direct body) [] (mRootEnv [5] body) [5] [5] body).slotOf [5] (fun _ => [5]) [5]))
            (.sym unit) := by
        simp only [clauseOf, rootSpellings, elabCfgX, elabCfg, cfgM, elabForm, List.append_nil]
        rw [elabMS_eq_slotOf [5] body _ [] (mRootEnv [5] body) [5] [5]]
      have e₂ : clauseId [5] u unit (elabMFormAt [5] body) =
          .app (.lam (.src (.par u ([5] ++ [9])))
            (frameSlots [5] ((annM (Src.direct body) [] (mRootEnv [5] body) [5] [5] body).idOf
              [5] (mRootEnv [5] body) (fun _ => [5]) [5] [5]))
            ((annM (Src.direct body) [] (mRootEnv [5] body) [5] [5] body).idOf
              [5] (mRootEnv [5] body) (fun _ => [5]) [5] [5])) (.sym unit) := by
        simp only [clauseId, elabMFormAt]
        rw [elabMId_eq_idOf]
        rfl
      simp only [Option.map_some]
      rw [e₁, e₂]
      exact clause_rel u unit (annM_WF body _ _ _ _ _ h₂) (by rw [freePars_annM]; exact h₃)
        (fun y hy => List.mem_dedup.2 (by rwa [names_annM] at hy))
        (fun y => mRootEnv_ok [5] body _ _ _ y) (mRootEnv_intro [5] body)

/-- **Lexical fresh's programs are related.** -/
theorem progRel_LF (u : X) (unit : S) (cl : S → Option (Src S X))
    (hcl : ∀ F body, cl F = some body → body.Admissible) :
    ProgRel SC (progSlot cfgLF u unit cl) (progLF u unit cl) := by
  intro F
  simp only [progSlot, progLF]
  cases h : cl F with
  | none => trivial
  | some body =>
      obtain ⟨h₂, h₃⟩ := hcl F body h
      have e₁ : clauseOf cfgLF [5] u unit body =
          .app (.lam (.src ([5] ++ [9], u))
            (((Src.names body).dedup ++ holeSpellings [5]
              ((annLF [] [5] [5] body).slotOf [5] (fun _ => [5]) [5])).map fun y => ([5], y))
            ((annLF [] [5] [5] body).slotOf [5] (fun _ => [5]) [5])) (.sym unit) := by
        simp only [clauseOf, rootSpellings, elabCfgX, elabCfg, cfgLF, elabForm, List.append_nil]
        rw [elabLF_eq_slotOf [5] body [] [5] [5]]
      have e₂ : clauseId [5] u unit (elabLFFormAt [5] body) =
          .app (.lam (.src (.par u ([5] ++ [9])))
            (frameSlots [5] ((annLF [] [5] [5] body).idOf [5] (lfRootEnv [5]) (fun _ => [5]) [5] [5]))
            ((annLF [] [5] [5] body).idOf [5] (lfRootEnv [5]) (fun _ => [5]) [5] [5])) (.sym unit) := by
        simp only [clauseId, elabLFFormAt]
        rw [elabLFId_eq_idOf]
        rfl
      simp only [Option.map_some]
      rw [e₁, e₂]
      exact clause_rel u unit (annLF_WF body _ _ _ h₂) (by rw [freePars_annLF]; exact h₃)
        (fun y hy => List.mem_dedup.2 (by rwa [names_annLF] at hy))
        (fun y => lfRootEnv_ok [5] _ y) (lfRootEnv_intro [5])

/-! ## The renaming theorem -/

/-- **One result of each model, related by a renaming**: an injective map on
the names in play (the answer's free names, every name either store binds, and
the copies of holes in stored sealed code, which it reads one to one) under
which the answers are related values and the final stores are related (each
binding of one store is a binding of the other at the renamed name, with
related ground values, and nothing else is bound). -/
def Renamed (r₁ : Tm S (Slot X) × GStore S (Slot X)) (r₂ : Tm S (BId X) × GStore S (BId X)) :
    Prop :=
  ∃ (ν μ : Nm (Slot X) → Nm (BId X)) (D : Set (Nm (Slot X))), (∀ n ∈ freeNames r₁.1, n ∈ D) ∧
    Set.InjOn ν D ∧ HoleInj (SC : Setting S (Slot X) (BId X)) ν D ∧ Rel SC ν μ .val [] true r₁.1 r₂.1 ∧
      StoreRel SC ν D r₁.2 r₂.2

omit [DecidableEq X] in
theorem Out.renamed [DecidableEq X] {π π' : Path} {ν μ : Nm (Slot X) → Nm (BId X)}
    {D : Set (Nm (Slot X))} {Res Rc : List (Nm (BId X))} {r₁ : Tm S (Slot X) × GStore S (Slot X)}
    {r₂ : Tm S (BId X) × GStore S (BId X)} (h : Out SC π π' ν μ D Res Rc r₁ r₂) : Renamed r₁ r₂ := by
  obtain ⟨ν', D', hfv, -, -, hrel, -, hci⟩ := h
  exact ⟨ν', μ, D', hfv, hci.inj, hci.holeInj, hrel, hci.store⟩

variable [DecidableEq S]

/-- The renaming theorem from a related start. -/
theorem renaming_of {P₁ : S → Option (Tm S (Slot X))} {P₂ : S → Option (Tm S (BId X))}
    {t₁ : Tm S (Slot X)} {t₂ : Tm S (BId X)} (hP : ProgRel SC P₁ P₂)
    (hroot : ∃ (ν μ : Nm (Slot X) → Nm (BId X)) (Res : List (Nm (BId X))) (D : Set (Nm (Slot X)))
      (ok : Bool),
      Rel SC ν μ .code Res ok t₁ t₂ ∧ freeParams t₁ = [] ∧ (∀ x ∈ freeNames t₁, x ∈ D) ∧
      SealOK (SC : Setting S (Slot X) (BId X)) D t₁ ∧
      CI (SC : Setting S (Slot X) (BId X)) ν D (Res ++ []) Store.empty Store.empty ∧ Fresh [] [] ν D (Res ++ [])) :
    ((∃ n L₁, run .static P₁ n [] Store.empty t₁ = some L₁) ↔
        ∃ m L₂, run .static P₂ m [] Store.empty t₂ = some L₂) ∧
      ∀ {n m : ℕ} {L₁ : Result S (Slot X)} {L₂ : Result S (BId X)},
        run .static P₁ n [] Store.empty t₁ = some L₁ → run .static P₂ m [] Store.empty t₂ = some L₂ →
          List.Forall₂ Renamed L₁ L₂ := by
  obtain ⟨ν, μ, Res, D, _, hR, hfp, hfv, hsv, hci, hF⟩ := hroot
  exact ⟨defined_iff SC_codeAgree SC_patAgree hP hR hfp hfv hsv hci hF,
    fun h₁ h₂ => (bags_rel SC_codeAgree SC_patAgree hP hR hfp hfv hsv hci hF h₁ h₂).imp
      fun _ _ h => h.renamed⟩

/-- **The renaming theorem, rule M.**  On an admissible program and query, the
slot model's run (`cfgM`) and the identity model's run (`elabMFormAt`,
`progM`) are defined together, and their bags correspond result by result,
each pair related by an injective renaming of its names, answers and final
stores together. -/
theorem renaming_M (u : X) (unit : S) (cl : S → Option (Src S X)) (t : Src S X)
    (hcl : ∀ F body, cl F = some body → body.Admissible) (ht : t.Admissible) :
    ((∃ n L₁, run .static (progSlot cfgM u unit cl) n [] Store.empty (elabCfg cfgM [] t) = some L₁) ↔
        ∃ m L₂, run .static (progM u unit cl) m [] Store.empty (elabMFormAt [] t) = some L₂) ∧
      ∀ {n m : ℕ} {L₁ : Result S (Slot X)} {L₂ : Result S (BId X)},
        run .static (progSlot cfgM u unit cl) n [] Store.empty (elabCfg cfgM [] t) = some L₁ →
        run .static (progM u unit cl) m [] Store.empty (elabMFormAt [] t) = some L₂ →
          List.Forall₂ Renamed L₁ L₂ := by
  obtain ⟨h₂, h₃⟩ := ht
  have e₁ : elabCfg cfgM [] t =
      (annM (Src.direct t) [] (mRootEnv [] t) [] [] t).slotOf [] (fun _ => []) [] :=
    elabMS_eq_slotOf _ t _ _ _ _ _ _ _
  have e₂ : elabMFormAt [] t =
      (annM (Src.direct t) [] (mRootEnv [] t) [] [] t).idOf [] (mRootEnv [] t) (fun _ => []) [] [] :=
    elabMId_eq_idOf _ t _ _ _ _ _ _
  rw [e₁, e₂]
  exact renaming_of (progRel_M u unit cl hcl)
    (root_config (annM_WF t _ _ _ _ _ h₂) (by rw [freePars_annM]; exact h₃)
      (fun y => mRootEnv_ok [] t _ _ _ y))

/-- **The renaming theorem, lexical fresh.** -/
theorem renaming_LF (u : X) (unit : S) (cl : S → Option (Src S X)) (t : Src S X)
    (hcl : ∀ F body, cl F = some body → body.Admissible) (ht : t.Admissible) :
    ((∃ n L₁, run .static (progSlot cfgLF u unit cl) n [] Store.empty (elabCfg cfgLF [] t) = some L₁) ↔
        ∃ m L₂, run .static (progLF u unit cl) m [] Store.empty (elabLFFormAt [] t) = some L₂) ∧
      ∀ {n m : ℕ} {L₁ : Result S (Slot X)} {L₂ : Result S (BId X)},
        run .static (progSlot cfgLF u unit cl) n [] Store.empty (elabCfg cfgLF [] t) = some L₁ →
        run .static (progLF u unit cl) m [] Store.empty (elabLFFormAt [] t) = some L₂ →
          List.Forall₂ Renamed L₁ L₂ := by
  obtain ⟨h₂, h₃⟩ := ht
  have e₁ : elabCfg cfgLF [] t = (annLF [] [] [] t).slotOf [] (fun _ => []) [] :=
    elabLF_eq_slotOf _ t _ _ _ _ _
  have e₂ : elabLFFormAt [] t = (annLF [] [] [] t).idOf [] (lfRootEnv []) (fun _ => []) [] [] :=
    elabLFId_eq_idOf _ t _ _ _ _ _
  rw [e₁, e₂]
  exact renaming_of (progRel_LF u unit cl hcl)
    (root_config (annLF_WF t _ _ _ h₂) (by rw [freePars_annLF]; exact h₃)
      (fun y => lfRootEnv_ok [] _ y))

/-! ## The translator, in the slot model -/

omit [DecidableEq S] [DecidableEq X] in
theorem patsNewFree_wrapNew (ys : List X) (b : Src S X) :
    (wrapNew ys b).patsNewFree = b.patsNewFree := by
  cases ys <;> rfl

omit [DecidableEq S] in
theorem freePars_wrapNew (ys : List X) (b : Src S X) :
    (wrapNew ys b).freePars = b.freePars := by
  cases ys <;> rfl

omit [DecidableEq S] in
/-- The translation keeps the spine of a pattern. -/
theorem spineNewFree_toLexAt : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    (toLexAt E cr env fr pos t).spineNewFree = t.spineNewFree
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .quote _, _, _, _, _, _ => rfl
  | .lam _ none _, _, _, _, _, _ => rfl
  | .lam _ (some _) _, _, _, _, _, _ => rfl
  | .app f a, _, _, _, _, _ => by
      simp only [toLexAt, Src.spineNewFree, spineNewFree_toLexAt f, spineNewFree_toLexAt a]
  | .pquote _, _, _, _, _, _ => by simp only [toLexAt, Src.spineNewFree]
  | .letS p _ _ none, _, _, _, _, _ => by
      simp only [toLexAt, Src.spineNewFree, spineNewFree_toLexAt p]
  | .letS p _ _ (some _), _, _, _, _, _ => by
      simp only [toLexAt, Src.spineNewFree, spineNewFree_toLexAt p]
  | .unify p _ _, _, _, _, _, _ => by simp only [toLexAt, Src.spineNewFree, spineNewFree_toLexAt p]
  | .alt _ _, _, _, _, _, _ => rfl
  | .form _ _, _, _, _, _, _ => rfl
  | .new [] b, _, _, _, _, _ => by simp only [toLexAt, Src.spineNewFree, spineNewFree_toLexAt b]
  | .new (_ :: _) _, _, _, _, _, _ => rfl

omit [DecidableEq S] in
/-- The translation puts `new` blocks only around lambda bodies, off every
pattern's spine. -/
theorem patsNewFree_toLexAt : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    (toLexAt E cr env fr pos t).patsNewFree = t.patsNewFree
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .quote _, _, _, _, _, _ => rfl
  | .lam _ none b, _, _, _, _, _ => by
      simp only [toLexAt, Src.patsNewFree, patsNewFree_wrapNew, patsNewFree_toLexAt b]
  | .lam _ (some _) b, _, _, _, _, _ => by
      simp only [toLexAt, Src.patsNewFree, patsNewFree_toLexAt b]
  | .app f a, _, _, _, _, _ => by
      simp only [toLexAt, Src.patsNewFree, patsNewFree_toLexAt f, patsNewFree_toLexAt a]
  | .pquote _, _, _, _, _, _ => by simp only [toLexAt, Src.patsNewFree]
  | .letS p w b none, _, _, _, _, _ => by
      simp only [toLexAt, Src.patsNewFree, spineNewFree_toLexAt p, patsNewFree_toLexAt p,
        patsNewFree_toLexAt w, patsNewFree_toLexAt b]
  | .letS p w b (some _), _, _, _, _, _ => by
      simp only [toLexAt, Src.patsNewFree, spineNewFree_toLexAt p, patsNewFree_toLexAt p,
        patsNewFree_toLexAt w, patsNewFree_toLexAt b]
  | .unify p w b, _, _, _, _, _ => by
      simp only [toLexAt, Src.patsNewFree, spineNewFree_toLexAt p, patsNewFree_toLexAt p,
        patsNewFree_toLexAt w, patsNewFree_toLexAt b]
  | .alt t₁ t₂, _, _, _, _, _ => by
      simp only [toLexAt, Src.patsNewFree, patsNewFree_toLexAt t₁, patsNewFree_toLexAt t₂]
  | .new _ b, _, _, _, _, _ => by simp only [toLexAt, Src.patsNewFree, patsNewFree_toLexAt b]
  | .form _ b, _, _, _, _, _ => by
      simp only [toLexAt, Src.patsNewFree, patsNewFree_toLexAt b]

omit [DecidableEq S] in
/-- The translation binds no parameter and frees none. -/
theorem freePars_toLexAt : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    (toLexAt E cr env fr pos t).freePars = t.freePars
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .quote _, _, _, _, _, _ => rfl
  | .lam _ none b, _, _, _, _, _ => by
      simp only [toLexAt, Src.freePars, freePars_wrapNew, freePars_toLexAt b]
  | .lam _ (some _) b, _, _, _, _, _ => by
      simp only [toLexAt, Src.freePars, freePars_toLexAt b]
  | .app f a, _, _, _, _, _ => by
      simp only [toLexAt, Src.freePars, freePars_toLexAt f, freePars_toLexAt a]
  | .pquote _, _, _, _, _, _ => by simp only [toLexAt, Src.freePars]
  | .letS p w b none, _, _, _, _, _ => by
      simp only [toLexAt, Src.freePars, freePars_toLexAt p, freePars_toLexAt w, freePars_toLexAt b]
  | .letS p w b (some _), _, _, _, _, _ => by
      simp only [toLexAt, Src.freePars, freePars_toLexAt p, freePars_toLexAt w, freePars_toLexAt b]
  | .unify p w b, _, _, _, _, _ => by
      simp only [toLexAt, Src.freePars, freePars_toLexAt p, freePars_toLexAt w, freePars_toLexAt b]
  | .alt t₁ t₂, _, _, _, _, _ => by
      simp only [toLexAt, Src.freePars, freePars_toLexAt t₁, freePars_toLexAt t₂]
  | .new _ b, _, _, _, _, _ => by simp only [toLexAt, Src.freePars, freePars_toLexAt b]
  | .form _ b, _, _, _, _, _ => by
      simp only [toLexAt, Src.freePars, freePars_toLexAt b]

omit [DecidableEq S] in
/-- **The translation of admissible text is admissible.** -/
theorem admissible_toLexAt {t : Src S X} (h : t.Admissible) (E cr : List X) (env : IEnv X)
    (fr pos : Owner) : (toLexAt E cr env fr pos t).Admissible :=
  ⟨by rw [patsNewFree_toLexAt]; exact h.1, by rw [freePars_toLexAt]; exact h.2⟩

/-- **The translator's correctness, in the slot model.**  On an admissible
program and query, the slot model's lexical fresh on the translated program and
query is defined exactly when the slot model's rule M on the source is; and
both bags are renamings, result by result, of one bag: the identity model's
bag of rule M on the source (which is, exactly, the identity model's bag of
lexical fresh on the translation, `run_toLexical`). -/
theorem transfer (u : X) (unit : S) (cl : S → Option (Src S X)) (t : Src S X)
    (hcl : ∀ F body, cl F = some body → body.Admissible) (ht : t.Admissible) :
    ((∃ n L, run .static (progSlot cfgLF u unit (toLexicalProg cl)) n [] Store.empty
        (elabCfg cfgLF [] (toLexical t)) = some L) ↔
      ∃ n L, run .static (progSlot cfgM u unit cl) n [] Store.empty (elabCfg cfgM [] t) = some L) ∧
    ∀ {n n' : ℕ} {L L' : Result S (Slot X)},
      run .static (progSlot cfgLF u unit (toLexicalProg cl)) n [] Store.empty
        (elabCfg cfgLF [] (toLexical t)) = some L →
      run .static (progSlot cfgM u unit cl) n' [] Store.empty (elabCfg cfgM [] t) = some L' →
      ∃ (k : ℕ) (L₂ : Result S (BId X)),
        run .static (progM u unit cl) k [] Store.empty (elabMFormAt [] t) = some L₂ ∧
        List.Forall₂ Renamed L L₂ ∧ List.Forall₂ Renamed L' L₂ := by
  have hclT : ∀ F body, toLexicalProg cl F = some body → body.Admissible := by
    intro F body h
    simp only [toLexicalProg, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rfl⟩ := h
    exact admissible_toLexAt (hcl F b hb) _ _ _ _ _
  have htT : (toLexical t).Admissible := admissible_toLexAt ht _ _ _ _ _
  obtain ⟨hLF₁, hLF₂⟩ := renaming_LF u unit (toLexicalProg cl) (toLexical t) hclT htT
  obtain ⟨hM₁, hM₂⟩ := renaming_M u unit cl t hcl ht
  have heq : ∀ n, run .static (progLF u unit (toLexicalProg cl)) n [] Store.empty
      (elabLFFormAt [] (toLexical t)) = run .static (progM u unit cl) n [] Store.empty
        (elabMFormAt [] t) :=
    fun n => run_toLexical u unit cl t .static n [] Store.empty
  refine ⟨?_, ?_⟩
  · rw [hLF₁, hM₁]
    simp only [heq]
  · intro n n' L L' h₁ h₂
    obtain ⟨m, L₂, hm⟩ := hLF₁.1 ⟨n, L, h₁⟩
    exact ⟨m, L₂, by rw [← heq]; exact hm, hLF₂ h₁ hm, hM₂ h₂ (by rw [← heq]; exact hm)⟩

/-! ## First-order answers: the slot model's two profiles, directly -/

/-- First-order terms of the same shape, their store names corresponding by
`R`. -/
def FOCorr {Y₁ Y₂ : Type v} (R : Nm Y₁ → Nm Y₂ → Prop) : Tm S Y₁ → Tm S Y₂ → Prop
  | .sym s, .sym s' => s = s'
  | .var n, .var m => R n m
  | .app f a, .app f' a' => FOCorr R f f' ∧ FOCorr R a a'
  | _, _ => False

/-- **Two terms equal up to a correspondence `K` of names**: one shape and one
own list at each lambda, each name of the first paired by `K` with the name of
the second at the same place. -/
inductive TmCorr {Y : Type v} (K : Nm Y → Nm Y → Prop) : Tm S Y → Tm S Y → Prop
  | sym (s : S) : TmCorr K (.sym s) (.sym s)
  | fn (F : S) : TmCorr K (.fn F) (.fn F)
  | var {n m : Nm Y} : K n m → TmCorr K (.var n) (.var m)
  | pvar {n m : Nm Y} : K n m → TmCorr K (.pvar n) (.pvar m)
  | lam {x x' : Nm Y} {o : List Y} {b b' : Tm S Y} :
      K x x' → TmCorr K b b' → TmCorr K (.lam x o b) (.lam x' o b')
  | app {f a f' a' : Tm S Y} : TmCorr K f f' → TmCorr K a a' → TmCorr K (.app f a) (.app f' a')
  | quote {c c' : Tm S Y} : TmCorr K c c' → TmCorr K (.quote c) (.quote c')
  | ctx {ks ks' : List (Nm Y)} {c c' : Tm S Y} :
      List.Forall₂ K ks ks' → TmCorr K c c' → TmCorr K (.ctx ks c) (.ctx ks' c')
  | pquote {c c' : Tm S Y} : TmCorr K c c' → TmCorr K (.pquote c) (.pquote c')
  | letP {p w b p' w' b' : Tm S Y} :
      TmCorr K p p' → TmCorr K w w' → TmCorr K b b' → TmCorr K (.letP p w b) (.letP p' w' b')
  | alt {t u t' u' : Tm S Y} :
      TmCorr K t t' → TmCorr K u u' → TmCorr K (.alt t u) (.alt t' u')

omit [DecidableEq S] [DecidableEq X] in
theorem TmCorr.refl {Y : Type v} : ∀ t : Tm S Y, TmCorr (fun n m => n = m) t t
  | .sym s => .sym s
  | .fn F => .fn F
  | .var _ => .var rfl
  | .pvar _ => .pvar rfl
  | .lam _ _ b => .lam rfl (TmCorr.refl b)
  | .app f a => .app (TmCorr.refl f) (TmCorr.refl a)
  | .quote c => .quote (TmCorr.refl c)
  | .ctx ks c => .ctx (List.forall₂_refl ks) (TmCorr.refl c)
  | .pquote c => .pquote (TmCorr.refl c)
  | .letP p w b => .letP (TmCorr.refl p) (TmCorr.refl w) (TmCorr.refl b)
  | .alt t u => .alt (TmCorr.refl t) (TmCorr.refl u)

omit [DecidableEq S] [DecidableEq X] in
theorem TmCorr.symm {Y : Type v} {K : Nm Y → Nm Y → Prop} {t t' : Tm S Y}
    (h : TmCorr K t t') : TmCorr (fun m n => K n m) t' t := by
  induction h with
  | sym s => exact .sym s
  | fn F => exact .fn F
  | var h => exact .var h
  | pvar h => exact .pvar h
  | lam hx _ ih => exact .lam hx ih
  | app _ _ ihf iha => exact .app ihf iha
  | quote _ ih => exact .quote ih
  | ctx hks _ ih => exact .ctx hks.flip ih
  | pquote _ ih => exact .pquote ih
  | letP _ _ _ ihp ihw ihb => exact .letP ihp ihw ihb
  | alt _ _ iht ihu => exact .alt iht ihu

omit [DecidableEq S] [DecidableEq X] in
theorem forall₂_comp {α : Type*} {K K' : α → α → Prop} :
    ∀ {l l' l'' : List α}, List.Forall₂ K l l' → List.Forall₂ K' l' l'' →
      List.Forall₂ (fun a c => ∃ b, K a b ∧ K' b c) l l''
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h hs, .cons h' hs' => .cons ⟨_, h, h'⟩ (forall₂_comp hs hs')

omit [DecidableEq S] [DecidableEq X] in
theorem TmCorr.trans {Y : Type v} {K K' : Nm Y → Nm Y → Prop} {t t' : Tm S Y}
    (h : TmCorr K t t') : ∀ {t'' : Tm S Y}, TmCorr K' t' t'' →
      TmCorr (fun n k => ∃ m, K n m ∧ K' m k) t t'' := by
  induction h with
  | sym s => intro t'' h'; cases h'; exact .sym s
  | fn F => intro t'' h'; cases h'; exact .fn F
  | var h => intro t'' h'; cases h' with | var h' => exact .var ⟨_, h, h'⟩
  | pvar h => intro t'' h'; cases h' with | pvar h' => exact .pvar ⟨_, h, h'⟩
  | lam hx _ ih => intro t'' h'; cases h' with | lam hx' hb' => exact .lam ⟨_, hx, hx'⟩ (ih hb')
  | app _ _ ihf iha => intro t'' h'; cases h' with | app hf' ha' => exact .app (ihf hf') (iha ha')
  | quote _ ih => intro t'' h'; cases h' with | quote hc' => exact .quote (ih hc')
  | ctx hks _ ih =>
      intro t'' h'
      cases h' with
      | ctx hks' hc' => exact .ctx (forall₂_comp hks hks') (ih hc')
  | pquote _ ih => intro t'' h'; cases h' with | pquote hc' => exact .pquote (ih hc')
  | letP _ _ _ ihp ihw ihb =>
      intro t'' h'
      cases h' with
      | letP hp' hw' hb' => exact .letP (ihp hp') (ihw hw') (ihb hb')
  | alt _ _ iht ihu => intro t'' h'; cases h' with | alt ht' hu' => exact .alt (iht ht') (ihu hu')

/-- **Two ground values equal up to a correspondence `K` of the names of their
sealed code.** -/
def GCorr {Y : Type v} (K : Nm Y → Nm Y → Prop) (g g' : GVal S Y) : Prop :=
  TmCorr K g.toTm g'.toTm

/-- **Two results of the slot model, equal up to a one-to-one correspondence of
their names**: `R` pairs store names and `K` the names of stored sealed code
(a name as written with itself, a copy of a hole with a copy), each one to one;
the answers have the same shape with corresponding names, corresponding names
hold values equal up to `K`, and every name either store binds has a partner. -/
def FOMatch (r₁ r₃ : Tm S (Slot X) × GStore S (Slot X)) : Prop :=
  ∃ R K : Nm (Slot X) → Nm (Slot X) → Prop,
    (∀ n m m', R n m → R n m' → m = m') ∧ (∀ n n' m, R n m → R n' m → n = n') ∧
    (∀ n m m', K n m → K n m' → m = m') ∧ (∀ n n' m, K n m → K n' m → n = n') ∧
    FOCorr R r₁.1 r₃.1 ∧ (∀ n m, R n m → OptRel (GCorr K) (r₁.2 n) (r₃.2 m)) ∧
    (∀ n, r₁.2 n ≠ none → ∃ m, R n m) ∧ (∀ m, r₃.2 m ≠ none → ∃ n, R n m)

omit [DecidableEq S] in
/-- A value related to a first-order value is its renaming. -/
theorem Rel.val_firstOrder {X₁ X₂ : Type v} [DecidableEq X₁] [DecidableEq X₂]
    {C : Setting S X₁ X₂} {ν μ : Nm X₁ → Nm X₂} :
    ∀ {t₁ : Tm S X₁} {R : List (Nm X₂)} {ok : Bool} {t₂ : Tm S X₂}, Rel C ν μ .val R ok t₁ t₂ →
      t₁.FirstOrder = true → t₂ = mapCode ν t₁
  | .sym _, _, _, _, h, _ => by cases h; rfl
  | .var _, _, _, _, h, _ => by cases h; rfl
  | .app f a, _, _, _, h, hfo => by
      simp only [Tm.FirstOrder, Bool.and_eq_true] at hfo
      cases h with
      | app hf ha => rw [Rel.val_firstOrder hf hfo.1, Rel.val_firstOrder ha hfo.2]; rfl
      | letAct hk => exact absurd rfl hk
  | .fn _, _, _, _, _, hfo => by simp [Tm.FirstOrder] at hfo
  | .pvar _, _, _, _, _, hfo => by simp [Tm.FirstOrder] at hfo
  | .lam _ _ _, _, _, _, _, hfo => by simp [Tm.FirstOrder] at hfo
  | .quote _, _, _, _, _, hfo => by simp [Tm.FirstOrder] at hfo
  | .ctx _ _, _, _, _, _, hfo => by simp [Tm.FirstOrder] at hfo
  | .pquote _, _, _, _, _, hfo => by simp [Tm.FirstOrder] at hfo
  | .letP _ _ _, _, _, _, _, hfo => by simp [Tm.FirstOrder] at hfo
  | .alt _ _, _, _, _, _, hfo => by simp [Tm.FirstOrder] at hfo

omit [DecidableEq S] in
/-- A value related to a first-order value is first-order. -/
theorem Rel.val_firstOrder_left {X₁ X₂ : Type v} [DecidableEq X₁] [DecidableEq X₂]
    {C : Setting S X₁ X₂} {ν μ : Nm X₁ → Nm X₂} :
    ∀ {t₁ : Tm S X₁} {R : List (Nm X₂)} {ok : Bool} {t₂ : Tm S X₂}, Rel C ν μ .val R ok t₁ t₂ →
      t₂.FirstOrder = true → t₁.FirstOrder = true
  | .sym _, _, _, _, _, _ => rfl
  | .var _, _, _, _, _, _ => rfl
  | .app f a, _, _, _, h, hfo => by
      cases h with
      | app hf ha =>
          simp only [Tm.FirstOrder, Bool.and_eq_true] at hfo ⊢
          exact ⟨Rel.val_firstOrder_left hf hfo.1, Rel.val_firstOrder_left ha hfo.2⟩
      | letAct hk => exact absurd rfl hk
  | .fn _, _, _, _, h, hfo => by cases h; simp [Tm.FirstOrder] at hfo
  | .pvar _, _, _, _, h, hfo => by cases h; simp [Tm.FirstOrder] at hfo
  | .lam _ _ _, _, _, _, h, hfo => by cases h; simp [Tm.FirstOrder] at hfo
  | .quote _, _, _, _, h, hfo => by cases h; simp [Tm.FirstOrder] at hfo
  | .ctx _ _, _, _, _, h, hfo => by
      cases h
      simp [Tm.FirstOrder] at hfo
  | .pquote _, _, _, _, h, hfo => by
      cases h
      simp [Tm.FirstOrder] at hfo
  | .letP _ _ _, _, _, _, h, _ => by
      cases h with
      | letP hk => exact absurd rfl hk
  | .alt _ _, _, _, _, h, _ => by
      cases h with
      | alt hk => exact absurd rfl hk

omit [DecidableEq S] in
/-- Two first-order terms with the same image correspond, name by name. -/
theorem focorr_of_mapCode {ν₁ ν₃ : Nm (Slot X) → Nm (BId X)} {D₁ D₃ : Set (Nm (Slot X))} :
    ∀ {t₁ t₃ : Tm S (Slot X)}, t₁.FirstOrder = true → t₃.FirstOrder = true →
      mapCode ν₁ t₁ = mapCode ν₃ t₃ → (∀ n ∈ freeNames t₁, n ∈ D₁) → (∀ m ∈ freeNames t₃, m ∈ D₃) →
      FOCorr (fun n m => n ∈ D₁ ∧ m ∈ D₃ ∧ ν₁ n = ν₃ m) t₁ t₃
  | .sym s, .sym s', _, _, he, _, _ => by
      simp only [mapCode, Tm.sym.injEq] at he
      exact he
  | .var n, .var m, _, _, he, h₁, h₃ => by
      simp only [mapCode, Tm.var.injEq] at he
      exact ⟨h₁ n (by simp [freeNames]), h₃ m (by simp [freeNames]), he⟩
  | .app f a, .app f' a', hfo₁, hfo₃, he, h₁, h₃ => by
      simp only [Tm.FirstOrder, Bool.and_eq_true] at hfo₁ hfo₃
      simp only [mapCode, Tm.app.injEq] at he
      exact ⟨focorr_of_mapCode hfo₁.1 hfo₃.1 he.1 (fun n hn => h₁ n (by simp [freeNames, hn]))
          (fun m hm => h₃ m (by simp [freeNames, hm])),
        focorr_of_mapCode hfo₁.2 hfo₃.2 he.2 (fun n hn => h₁ n (by simp [freeNames, hn]))
          (fun m hm => h₃ m (by simp [freeNames, hm]))⟩
  | .sym _, .var _, _, _, he, _, _ => by simp [mapCode] at he
  | .sym _, .app _ _, _, _, he, _, _ => by simp [mapCode] at he
  | .var _, .sym _, _, _, he, _, _ => by simp [mapCode] at he
  | .var _, .app _ _, _, _, he, _, _ => by simp [mapCode] at he
  | .app _ _, .sym _, _, _, he, _, _ => by simp [mapCode] at he
  | .app _ _, .var _, _, _, he, _, _ => by simp [mapCode] at he
  | .fn _, _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h
  | .pvar _, _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h
  | .lam _ _ _, _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h
  | .quote _, _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h
  | .pquote _, _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h
  | .letP _ _ _, _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h
  | .alt _ _, _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h
  | .ctx _ _, _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h
  | .sym _, .fn _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .sym _, .pvar _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .sym _, .lam _ _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .sym _, .quote _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .sym _, .pquote _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .sym _, .ctx _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .sym _, .letP _ _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .sym _, .alt _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .var _, .fn _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .var _, .pvar _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .var _, .lam _ _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .var _, .quote _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .var _, .pquote _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .var _, .ctx _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .var _, .letP _ _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .var _, .alt _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .app _ _, .fn _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .app _ _, .pvar _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .app _ _, .lam _ _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .app _ _, .quote _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .app _ _, .pquote _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .app _ _, .ctx _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .app _ _, .letP _ _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .app _ _, .alt _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h

omit [DecidableEq S] [DecidableEq X] in
theorem firstOrder_mapCode {Y Z : Type v} {f : Nm Y → Nm Z} :
    ∀ {t : Tm S Y}, t.FirstOrder = true → (mapCode f t).FirstOrder = true
  | .sym _, _ => rfl
  | .var _, _ => rfl
  | .app a b, h => by
      simp only [Tm.FirstOrder, Bool.and_eq_true] at h
      simp only [mapCode, Tm.FirstOrder, Bool.and_eq_true]
      exact ⟨firstOrder_mapCode h.1, firstOrder_mapCode h.2⟩
  | .fn _, h => by simp [Tm.FirstOrder] at h
  | .pvar _, h => by simp [Tm.FirstOrder] at h
  | .lam _ _ _, h => by simp [Tm.FirstOrder] at h
  | .quote _, h => by simp [Tm.FirstOrder] at h
  | .pquote _, h => by simp [Tm.FirstOrder] at h
  | .ctx _ _, h => by simp [Tm.FirstOrder] at h
  | .letP _ _ _, h => by simp [Tm.FirstOrder] at h
  | .alt _ _, h => by simp [Tm.FirstOrder] at h

omit [DecidableEq S] [DecidableEq X] in
theorem forall₂_of_map_eq {α β : Type*} {h₁ h₃ : α → β} {K : α → α → Prop} :
    ∀ {l₁ l₃ : List α}, l₃.map h₃ = l₁.map h₁ → (∀ n ∈ l₁, ∀ m ∈ l₃, h₃ m = h₁ n → K n m) →
      List.Forall₂ K l₁ l₃
  | [], [], _, _ => .nil
  | [], _ :: _, he, _ => by simp at he
  | _ :: _, [], he, _ => by simp at he
  | n :: l₁, m :: l₃, he, hf => by
      simp only [List.map_cons, List.cons.injEq] at he
      exact .cons (hf n (by simp) m (by simp) he.1)
        (forall₂_of_map_eq he.2 fun n' hn' m' hm' => hf n' (by simp [hn']) m' (by simp [hm']))

omit [DecidableEq S] [DecidableEq X] in
/-- **Two codes with one image correspond name by name**: when `h₃` on `c₃` and
`h₁` on `c₁` give the same code, the two codes have one shape, and each name of
`c₁` corresponds to the name of `c₃` at its place, which has the same image. -/
theorem tmCorr_of_mapCode_eq {Y Z : Type v} {h₁ h₃ : Nm Y → Nm Z} {K : Nm Y → Nm Y → Prop}
    (c₁ : Tm S Y) : ∀ {c₃ : Tm S Y}, ownNil c₁ → ownNil c₃ → mapCode h₃ c₃ = mapCode h₁ c₁ →
      (∀ n ∈ codeNames c₁, ∀ m ∈ codeNames c₃, h₃ m = h₁ n → K n m) → TmCorr K c₁ c₃ := by
  induction c₁ with
  | sym _ =>
      intro c₃ _ _ he _
      cases c₃ <;> simp only [mapCode, reduceCtorEq] at he
      injection he with he
      subst he
      exact .sym _
  | fn _ =>
      intro c₃ _ _ he _
      cases c₃ <;> simp only [mapCode, reduceCtorEq] at he
      injection he with he
      subst he
      exact .fn _
  | var n =>
      intro c₃ hn₁ hn₃ he hf
      cases c₃ <;> simp only [mapCode, reduceCtorEq] at he
      rename_i m
      injection he with he
      exact .var (hf n (by simp [codeNames]) m (by simp [codeNames]) he)
  | pvar n =>
      intro c₃ hn₁ hn₃ he hf
      cases c₃ <;> simp only [mapCode, reduceCtorEq] at he
      rename_i m
      injection he with he
      exact .pvar (hf n (by simp [codeNames]) m (by simp [codeNames]) he)
  | lam x _ b ih =>
      intro c₃ hn₁ hn₃ he hf
      cases c₃ <;> simp only [mapCode, reduceCtorEq] at he
      rename_i x' o' b'
      injection he with hx _ hb
      obtain ⟨rfl, hn₁'⟩ := hn₁
      obtain ⟨rfl, hn₃'⟩ := hn₃
      exact .lam (hf x (by simp [codeNames]) x' (by simp [codeNames]) hx)
        (ih hn₁' hn₃' hb fun n hn m hm => hf n (by simp [codeNames, hn]) m (by simp [codeNames, hm]))
  | app a b iha ihb =>
      intro c₃ hn₁ hn₃ he hf
      cases c₃ <;> simp only [mapCode, reduceCtorEq] at he
      rename_i a' b'
      injection he with ha hb
      exact .app
        (iha hn₁.1 hn₃.1 ha fun n hn m hm => hf n (by simp [codeNames, hn]) m (by simp [codeNames, hm]))
        (ihb hn₁.2 hn₃.2 hb fun n hn m hm => hf n (by simp [codeNames, hn]) m (by simp [codeNames, hm]))
  | quote c ih =>
      intro c₃ hn₁ hn₃ he hf
      cases c₃ <;> simp only [mapCode, reduceCtorEq] at he
      rename_i c'
      injection he with hc
      have hn₁' : ownNil c := hn₁
      have hn₃' : ownNil c' := hn₃
      exact .quote (ih hn₁' hn₃' hc fun n hn m hm => hf n (by simpa only [codeNames] using hn) m
        (by simpa only [codeNames] using hm))
  | ctx ks c ih =>
      intro c₃ hn₁ hn₃ he hf
      cases c₃ <;> simp only [mapCode, reduceCtorEq] at he
      rename_i ks' c'
      injection he with hks hc
      have hn₁' : ownNil c := hn₁
      have hn₃' : ownNil c' := hn₃
      exact .ctx (forall₂_of_map_eq hks fun n hn m hm =>
          hf n (by simp [codeNames, hn]) m (by simp [codeNames, hm]))
        (ih hn₁' hn₃' hc fun n hn m hm => hf n (by simp [codeNames, hn]) m (by simp [codeNames, hm]))
  | pquote c ih =>
      intro c₃ hn₁ hn₃ he hf
      cases c₃ <;> simp only [mapCode, reduceCtorEq] at he
      rename_i c'
      injection he with hc
      have hn₁' : ownNil c := hn₁
      have hn₃' : ownNil c' := hn₃
      exact .pquote (ih hn₁' hn₃' hc fun n hn m hm => hf n (by simpa only [codeNames] using hn) m
        (by simpa only [codeNames] using hm))
  | letP p w b ihp ihw ihb =>
      intro c₃ hn₁ hn₃ he hf
      cases c₃ <;> simp only [mapCode, reduceCtorEq] at he
      rename_i p' w' b'
      injection he with hp hw hb
      exact .letP
        (ihp hn₁.1 hn₃.1 hp fun n hn m hm => hf n (by simp [codeNames, hn]) m (by simp [codeNames, hm]))
        (ihw hn₁.2.1 hn₃.2.1 hw fun n hn m hm =>
          hf n (by simp [codeNames, hn]) m (by simp [codeNames, hm]))
        (ihb hn₁.2.2 hn₃.2.2 hb fun n hn m hm =>
          hf n (by simp [codeNames, hn]) m (by simp [codeNames, hm]))
  | alt t u iht ihu =>
      intro c₃ hn₁ hn₃ he hf
      cases c₃ <;> simp only [mapCode, reduceCtorEq] at he
      rename_i t' u'
      injection he with ht hu
      exact .alt
        (iht hn₁.1 hn₃.1 ht fun n hn m hm => hf n (by simp [codeNames, hn]) m (by simp [codeNames, hm]))
        (ihu hn₁.2 hn₃.2 hu fun n hn m hm => hf n (by simp [codeNames, hn]) m (by simp [codeNames, hm]))

omit [DecidableEq S] in
/-- A related ground value is the first one read through `holeRead`. -/
theorem GRel.toTm_eq_mapCode {X₁ X₂ : Type v} {C : Setting S X₁ X₂} {ν : Nm X₁ → Nm X₂}
    {g₁ : GVal S X₁} {g₂ : GVal S X₂} (h : GRel C ν g₁ g₂) :
    g₂.toTm = mapCode (holeRead C ν) g₁.toTm := by
  induction h with
  | sym _ => rfl
  | app _ _ ihf iha => simp only [GVal.toTm, mapCode, ihf, iha]
  | quote hq =>
      obtain ⟨-, -, rfl⟩ := hq
      rfl
  | ctx _ hks hc =>
      subst hks hc
      rfl

omit [DecidableEq S] in
/-- The code of a related ground value is in the code form. -/
theorem GRel.codeForm {X₁ X₂ : Type v} {C : Setting S X₁ X₂} {ν : Nm X₁ → Nm X₂}
    {g₁ : GVal S X₁} {g₂ : GVal S X₂} (h : GRel C ν g₁ g₂) : CodeForm C g₁.toTm := by
  induction h with
  | sym _ =>
      exact ⟨trivial, fun n hn => by simp [GVal.toTm, codeVars] at hn,
        fun n hn => by simp [GVal.toTm, codeBinders] at hn⟩
  | app _ _ ihf iha =>
      refine ⟨⟨ihf.1, iha.1⟩, fun n hn => ?_, fun n hn => ?_⟩
      · simp only [GVal.toTm, codeVars, List.mem_append] at hn
        exact hn.elim (ihf.2.1 n) (iha.2.1 n)
      · simp only [GVal.toTm, codeBinders, List.mem_append] at hn
        exact hn.elim (ihf.2.2 n) (iha.2.2 n)
  | quote hq => exact hq.2.1
  | ctx hf _ _ => exact hf

/-- The correspondence of the names of sealed code that two slot renamings into one
identity result give: a name as written with itself, a copy of a hole with the
copy that the identity side reads alike. -/
def copyCorr (ν₁ ν₃ : Nm (Slot X) → Nm (BId X)) (D₁ D₃ : Set (Nm (Slot X))) (n m : Nm (Slot X)) :
    Prop :=
  (∃ s, n = .src s ∧ m = n) ∨
    (holeCopy (SC : Setting S (Slot X) (BId X)) n ∧ holeCopy (SC : Setting S (Slot X) (BId X)) m ∧
      n ∈ D₁ ∧ m ∈ D₃ ∧
      holeRead (SC : Setting S (Slot X) (BId X)) ν₁ n = holeRead (SC : Setting S (Slot X) (BId X)) ν₃ m)

omit [DecidableEq S] in
/-- **Two slot values related to one identity value are equal up to the copies
of their holes**: each copy of the first corresponds to the copy of the second
that the identity side reads alike. -/
theorem gcorr_of_grel {ν₁ ν₃ : Nm (Slot X) → Nm (BId X)} {D₁ D₃ : Set (Nm (Slot X))}
    {g₁ g₃ : GVal S (Slot X)} {g₂ : GVal S (BId X)} (hg₁ : GRel SC ν₁ g₁ g₂)
    (hg₃ : GRel SC ν₃ g₃ g₂) (hc₁ : CopiesIn D₁ g₁.toTm) (hc₃ : CopiesIn D₃ g₃.toTm) :
    GCorr (copyCorr (S := S) ν₁ ν₃ D₁ D₃) g₁ g₃ := by
  have hsrc : ∀ (ν : Nm (Slot X) → Nm (BId X)) s,
      ∃ s', holeRead (SC : Setting S (Slot X) (BId X)) ν (.src s) = .src s' :=
    fun _ s => codeFwd_src s
  have hcopy : ∀ (ν : Nm (Slot X) → Nm (BId X)) m, holeCopy (SC : Setting S (Slot X) (BId X)) m →
      ∃ ρ k, holeRead (SC : Setting S (Slot X) (BId X)) ν m = .inst ρ k := by
    intro ν m hm
    cases m with
    | src _ => exact hm.elim
    | inst ρ k => exact ⟨_, _, rfl⟩
  have hcf₁ := hg₁.codeForm
  have hcf₃ := hg₃.codeForm
  have hcls : ∀ {D : Set (Nm (Slot X))} {g : GVal S (Slot X)},
      CodeForm (SC : Setting S (Slot X) (BId X)) g.toTm → CopiesIn D g.toTm →
      ∀ n ∈ codeNames g.toTm, (∃ s, n = .src s) ∨
        (holeCopy (SC : Setting S (Slot X) (BId X)) n ∧ n ∈ D) := by
    intro D g hcf hc n hn
    rcases hcf.name_cases hn with h | ⟨hh, hv⟩
    · exact Or.inl h
    · rcases hc n hv with ⟨s, rfl⟩ | hD
      · exact Or.inl ⟨s, rfl⟩
      · exact Or.inr ⟨hh, hD⟩
  refine tmCorr_of_mapCode_eq _ hcf₁.1 hcf₃.1
    (by rw [← hg₃.toTm_eq_mapCode, ← hg₁.toTm_eq_mapCode]) ?_
  intro n hn m hm he
  rcases hcls hcf₁ hc₁ n hn with ⟨s, rfl⟩ | ⟨hcn, hn1⟩ <;>
    rcases hcls hcf₃ hc₃ m hm with ⟨t, rfl⟩ | ⟨hcm, hm3⟩
  · exact Or.inl ⟨s, rfl, (SC : Setting S (Slot X) (BId X)).codeMap_inj he⟩
  · obtain ⟨s', hs'⟩ := hsrc ν₁ s
    obtain ⟨ρ, k, hk⟩ := hcopy ν₃ m hcm
    rw [hs', hk] at he
    cases he
  · obtain ⟨t', ht'⟩ := hsrc ν₃ t
    obtain ⟨ρ, k, hk⟩ := hcopy ν₁ n hcn
    rw [ht', hk] at he
    cases he
  · exact Or.inr ⟨hcn, hcm, hn1, hm3, he.symm⟩

omit [DecidableEq S] in
/-- **Two slot results renamed into one identity result, with a first-order
answer, are equal up to a one-to-one correspondence of names**, stores
included: store names correspond by the renamings, and the copies of holes in
stored sealed code by the identity names they are read as. -/
theorem fomatch_of_renamed {r₁ r₃ : Tm S (Slot X) × GStore S (Slot X)}
    {r₂ : Tm S (BId X) × GStore S (BId X)} (h₁ : Renamed r₁ r₂) (h₃ : Renamed r₃ r₂)
    (hfo : r₁.1.FirstOrder = true) : FOMatch r₁ r₃ := by
  obtain ⟨ν₁, μ₁, D₁, hfv₁, hinj₁, hI₁, hrel₁, hst₁⟩ := h₁
  obtain ⟨ν₃, μ₃, D₃, hfv₃, hinj₃, hI₃, hrel₃, hst₃⟩ := h₃
  have e₁ := hrel₁.val_firstOrder hfo
  have hfo₂ : r₂.1.FirstOrder = true := by
    rw [e₁]
    exact firstOrder_mapCode hfo
  have hfo₃ := hrel₃.val_firstOrder_left hfo₂
  have e₃ := hrel₃.val_firstOrder hfo₃
  refine ⟨fun n m => n ∈ D₁ ∧ m ∈ D₃ ∧ ν₁ n = ν₃ m, copyCorr (S := S) ν₁ ν₃ D₁ D₃, ?_, ?_, ?_, ?_,
    focorr_of_mapCode hfo hfo₃ (e₁.symm.trans e₃) hfv₁ hfv₃, ?_, ?_, ?_⟩
  · rintro n m m' ⟨-, hm, he⟩ ⟨-, hm', he'⟩
    exact hinj₃ hm hm' (he.symm.trans he')
  · rintro n n' m ⟨hn, -, he⟩ ⟨hn', -, he'⟩
    exact hinj₁ hn hn' (he.trans he'.symm)
  · intro n m m' h h'
    rcases h with ⟨s, rfl, rfl⟩ | ⟨hn, hm, -, hm3, he⟩ <;>
      rcases h' with ⟨s', hs', rfl⟩ | ⟨hn', hm', -, hm3', he'⟩
    · rfl
    · exact False.elim hn'
    · subst hs'
      exact False.elim hn
    · exact hI₃ m hm3 m' hm3' hm hm' (he.symm.trans he')
  · intro n n' m h h'
    rcases h with ⟨s, rfl, rfl⟩ | ⟨hn, hm, hn1, -, he⟩ <;>
      rcases h' with ⟨s', rfl, he'⟩ | ⟨hn', hm', hn1', -, he'⟩
    · exact he'
    · exact False.elim hm'
    · subst he'
      exact False.elim hm
    · exact hI₁ n hn1 n' hn1' hn hn' (he.trans he'.symm)
  · rintro n m ⟨hn, hm, he⟩
    have o₁ := hst₁.rel n hn
    have o₃ := hst₃.rel m hm
    rw [he] at o₁
    rcases OptRel.cases o₁ with ⟨a₁, b₁⟩ | ⟨g₁, g₂, a₁, b₁, hg₁⟩ <;>
      rcases OptRel.cases o₃ with ⟨a₃, b₃⟩ | ⟨g₃, g₂', a₃, b₃, hg₃⟩
    · rw [a₁, a₃]
      trivial
    · rw [b₁] at b₃; cases b₃
    · rw [b₁] at b₃; cases b₃
    · rw [b₁] at b₃
      injection b₃ with b₃
      subst b₃
      rw [a₁, a₃]
      exact gcorr_of_grel hg₁ hg₃ (hst₁.sealOK n g₁ a₁).copiesIn_toTm
        (hst₃.sealOK m g₃ a₃).copiesIn_toTm
  · intro n hn
    have hnD := hst₁.dom n hn
    have o₁ := hst₁.rel n hnD
    rcases OptRel.cases o₁ with ⟨a₁, -⟩ | ⟨g₁, g₂, -, b₁, -⟩
    · exact absurd a₁ hn
    · obtain ⟨m, hm, he⟩ := hst₃.only (ν₁ n) (by rw [b₁]; simp)
      exact ⟨m, hnD, hm, he.symm⟩
  · intro m hm
    have hmD := hst₃.dom m hm
    have o₃ := hst₃.rel m hmD
    rcases OptRel.cases o₃ with ⟨a₃, -⟩ | ⟨g₃, g₂, -, b₃, -⟩
    · exact absurd a₃ hm
    · obtain ⟨n, hn, he⟩ := hst₁.only (ν₃ m) (by rw [b₃]; simp)
      exact ⟨n, hn, hmD, he⟩

omit [DecidableEq S] [DecidableEq X] in
theorem forall₂_through {α β γ : Type*} {R₁ : α → β → Prop} {R₃ : γ → β → Prop} :
    ∀ {L : List α} {L' : List γ} {L₂ : List β}, List.Forall₂ R₁ L L₂ → List.Forall₂ R₃ L' L₂ →
      List.Forall₂ (fun a c => ∃ b, R₁ a b ∧ R₃ c b) L L'
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ hs₁, .cons h₃ hs₃ => .cons ⟨_, h₁, h₃⟩ (forall₂_through hs₁ hs₃)

/-- **The translator's correctness on first-order answers, in the slot model,
directly**: result by result, when the answer is first-order, the slot model's
lexical fresh on the translation and its rule M on the source are equal up to a
one-to-one correspondence of names, answers and final stores together. -/
theorem transfer_firstOrder (u : X) (unit : S) (cl : S → Option (Src S X)) (t : Src S X)
    (hcl : ∀ F body, cl F = some body → body.Admissible) (ht : t.Admissible) {n n' : ℕ}
    {L L' : Result S (Slot X)}
    (h₁ : run .static (progSlot cfgLF u unit (toLexicalProg cl)) n [] Store.empty
      (elabCfg cfgLF [] (toLexical t)) = some L)
    (h₂ : run .static (progSlot cfgM u unit cl) n' [] Store.empty (elabCfg cfgM [] t) = some L') :
    List.Forall₂ (fun r r' => r.1.FirstOrder = true → FOMatch r r') L L' := by
  obtain ⟨_, _, _, hA, hB⟩ := (transfer u unit cl t hcl ht).2 h₁ h₂
  exact (forall₂_through hA hB).imp fun _ _ ⟨_, ha, hb⟩ hfo => fomatch_of_renamed ha hb hfo

end IdSlot

end Mettapedia.GSLT.LanguageDef.TemplateScope
