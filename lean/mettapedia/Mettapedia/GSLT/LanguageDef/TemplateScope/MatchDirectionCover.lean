import Mettapedia.GSLT.LanguageDef.TemplateScope.MatchDirectionExamples

/-!
# Template scope: rule M's covering patterns, with both sides

A hole of sealed code is the head cell of the form that writes the quotation:
the query's cell of its spelling for the query's own quotations, a cell of the
equation's frame for an equation's.  Under pattern-only a hole is never
written.  Under both sides a `let` may write it.  The slot model has one name
for a form's hole and the form's `$y` of the same spelling; rule M's identity
elaboration then has to name the form's `$y` as that same cell whenever a hole
spelled `y` can be written, where `findCover` may have named it after a
covering pattern.

## Definitions

* `Src.quoteOcc` — the count of holes inside quotations: occurrences of `$y`
  inside the quotations of authored text.  `occMQ` adds it to rule M's count
  `occM`.
* `findCoverQ H` — the covering pattern for the both-sides configurations: the
  one `findCover` finds, when the cover count finds no hole of the spelling
  inside a quotation of the form (`occMQ = occM`) and the spelling is not among
  the listed spellings `H` (the hole spellings of the program's other forms,
  when those are to keep the root's cell as well).  `mRootEnvQ`,
  `elabMFormAtQ`, `toLexicalAtQ`, `toLexicalQ` are the root environment, rule
  M's elaboration and the translator built on it.

## Main results

* `runDir_toLexical`, `runDir_toLexicalQ` — **the translation is exact at
  either direction**: lexical fresh on the translated program and rule M on the
  source run to the same bag of results with final stores, under pattern-only
  and under both sides, with `findCover` and with `findCoverQ`.  The translation
  keeps the direction.
* `renaming_MQ`, `transferQ` — under pattern-only, rule M's identity model with
  `findCoverQ` is the slot model up to renaming, and the translator is correct
  in the slot model, for every list `H`.  `RenamingStatement` and
  `TransferStatement` are the two statements, for any runs.
* `not_SC_patAgree2` — `Setting.PatAgree`, read with the both-sides code
  matcher, is false for `SC`: the matcher binds a hole of the value code, which
  the statement's domain does not hold.

The kernel-checked programs are in `MatchDirectionCoverExamples`.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

variable {S : Type u} {X : Type v}

/-! ## The count of holes inside quotations -/

namespace Src

variable [DecidableEq X]

/-- Occurrences of the store spelling `y` in authored text, quotations
included. -/
def svOcc (y : X) : Src S X → ℕ
  | .sv y' => if y' = y then 1 else 0
  | .lam _ _ b => svOcc y b
  | .app f a => svOcc y f + svOcc y a
  | .quote c => svOcc y c
  | .pquote c => svOcc y c
  | .letS p w b _ => svOcc y p + svOcc y w + svOcc y b
  | .unify p w b => svOcc y p + svOcc y w + svOcc y b
  | .alt a b => svOcc y a + svOcc y b
  | .new _ b => svOcc y b
  | .form _ b => svOcc y b
  | _ => 0

/-- **The count of holes inside quotations**: occurrences of `$y` inside the
quotations of authored text, at any depth. -/
def quoteOcc (y : X) : Src S X → ℕ
  | .quote c => svOcc y c
  | .pquote c => svOcc y c
  | .lam _ _ b => quoteOcc y b
  | .app f a => quoteOcc y f + quoteOcc y a
  | .letS p w b _ => quoteOcc y p + quoteOcc y w + quoteOcc y b
  | .unify p w b => quoteOcc y p + quoteOcc y w + quoteOcc y b
  | .alt a b => quoteOcc y a + quoteOcc y b
  | .new _ b => quoteOcc y b
  | .form _ b => quoteOcc y b
  | _ => 0

end Src

section Count

variable [DecidableEq X]

/-- The count is zero exactly when the spelling is not written. -/
theorem svOcc_eq_zero_iff (y : X) : ∀ t : Src S X, Src.svOcc y t = 0 ↔ mentionsSv y t = false
  | .sym _ | .fn _ | .par _ => by simp [Src.svOcc, mentionsSv]
  | .sv y' => by
      by_cases h : y' = y <;> simp [Src.svOcc, mentionsSv, h]
  | .lam _ _ b => by simp [Src.svOcc, mentionsSv, svOcc_eq_zero_iff y b]
  | .app f a => by
      simp [Src.svOcc, mentionsSv, svOcc_eq_zero_iff y f, svOcc_eq_zero_iff y a]
  | .quote c => by simp [Src.svOcc, mentionsSv, svOcc_eq_zero_iff y c]
  | .pquote c => by simp [Src.svOcc, mentionsSv, svOcc_eq_zero_iff y c]
  | .letS p w b _ => by
      simp [Src.svOcc, mentionsSv, svOcc_eq_zero_iff y p, svOcc_eq_zero_iff y w,
        svOcc_eq_zero_iff y b, and_assoc]
  | .unify p w b => by
      simp [Src.svOcc, mentionsSv, svOcc_eq_zero_iff y p, svOcc_eq_zero_iff y w,
        svOcc_eq_zero_iff y b, and_assoc]
  | .alt a b => by
      simp [Src.svOcc, mentionsSv, svOcc_eq_zero_iff y a, svOcc_eq_zero_iff y b]
  | .new _ b => by simp [Src.svOcc, mentionsSv, svOcc_eq_zero_iff y b]
  | .form _ b => by simp [Src.svOcc, mentionsSv, svOcc_eq_zero_iff y b]

/-- **The count is zero exactly when `quoteMentions` is false**: it is the
number behind the test `findCover` already makes at a covering pattern. -/
theorem quoteOcc_eq_zero_iff (y : X) :
    ∀ t : Src S X, Src.quoteOcc y t = 0 ↔ quoteMentions y t = false
  | .sym _ | .fn _ | .par _ | .sv _ => by simp [Src.quoteOcc, quoteMentions]
  | .quote c => by simp [Src.quoteOcc, quoteMentions, svOcc_eq_zero_iff y c]
  | .pquote c => by simp [Src.quoteOcc, quoteMentions, svOcc_eq_zero_iff y c]
  | .lam _ _ b => by simp [Src.quoteOcc, quoteMentions, quoteOcc_eq_zero_iff y b]
  | .app f a => by
      simp [Src.quoteOcc, quoteMentions, quoteOcc_eq_zero_iff y f, quoteOcc_eq_zero_iff y a]
  | .letS p w b _ => by
      simp [Src.quoteOcc, quoteMentions, quoteOcc_eq_zero_iff y p, quoteOcc_eq_zero_iff y w,
        quoteOcc_eq_zero_iff y b, and_assoc]
  | .unify p w b => by
      simp [Src.quoteOcc, quoteMentions, quoteOcc_eq_zero_iff y p, quoteOcc_eq_zero_iff y w,
        quoteOcc_eq_zero_iff y b, and_assoc]
  | .alt a b => by
      simp [Src.quoteOcc, quoteMentions, quoteOcc_eq_zero_iff y a, quoteOcc_eq_zero_iff y b]
  | .new _ b => by simp [Src.quoteOcc, quoteMentions, quoteOcc_eq_zero_iff y b]
  | .form _ b => by simp [Src.quoteOcc, quoteMentions, quoteOcc_eq_zero_iff y b]

/-- **The cover count for the both-sides configurations**: rule M's
occurrences, and the holes inside quotations. -/
def occMQ (E : List X) (y : X) (t : Src S X) : ℕ := occM E y t + Src.quoteOcc y t

/-- **The covering pattern for the both-sides configurations.**  The one
`findCover` finds, provided the cover count adds no hole inside a quotation of
the form, and the spelling is not among the listed spellings `H`.  Otherwise
there is none: the name is the root's own cell, which the slot model shares
with every hole of that spelling in the form's sealed code. -/
def findCoverQ (H E : List X) (y : X) (f : Bool) (t : Src S X) : Option Owner :=
  if occMQ E y t = occM E y t ∧ y ∉ H then findCover E y f t else none

/-- Rule M's root environment for the both-sides configurations. -/
def mRootEnvQ (H : List X) (R : Owner) (t : Src S X) : IEnv X := fun y =>
  match findCoverQ H (Src.direct t) y false t with
  | some P => ⟨y, R, R ++ P, .pat⟩
  | none => ⟨y, R, R, .head⟩

/-- Rule M with binder identities for the both-sides configurations, at a form
rooted at `R`. -/
def elabMFormAtQ (H : List X) (R : Owner) (t : Src S X) : Tm S (BId X) :=
  elabMId R (Src.direct t) [] (mRootEnvQ H R t) (pvRoot R) R R t

/-- The translator for the both-sides configurations, at a form rooted at `R`. -/
def toLexicalAtQ (H : List X) (R : Owner) (t : Src S X) : Src S X :=
  toLexAt (Src.direct t) [] (mRootEnvQ H R t) R R t

/-- The translator of a query, for the both-sides configurations. -/
def toLexicalQ (H : List X) (t : Src S X) : Src S X := toLexicalAtQ H [] t

theorem findCoverQ_eq_some {H E : List X} {y : X} {f : Bool} {t : Src S X} {P : Owner}
    (h : findCoverQ H E y f t = some P) : findCover E y f t = some P := by
  unfold findCoverQ at h
  split at h
  · exact h
  · cases h

/-- With no hole inside a quotation of the form and no other hole spelling, the
both-sides root environment is rule M's. -/
theorem mRootEnvQ_of_no_hole (R : Owner) (t : Src S X) (h : ∀ y, Src.quoteOcc y t = 0) :
    mRootEnvQ [] R t = mRootEnv R t := by
  funext y
  have hc : findCoverQ [] (Src.direct t) y false t = findCover (Src.direct t) y false t := by
    simp [findCoverQ, occMQ, h y]
  simp only [mRootEnvQ, mRootEnv, hc]
  cases findCover (Src.direct t) y false t <;> rfl

/-- The two root environments satisfy the invariant of the translation. -/
theorem corr_rootQ (H : List X) (R : Owner) (t : Src S X) :
    Corr (Src.direct t) [] (mRootEnvQ H R t) (lfRootEnv R) R R t := by
  intro y _
  cases hf : findCoverQ H (Src.direct t) y false t with
  | none =>
      left
      simp only [lfRootEnv, mRootEnvQ, hf]
  | some P =>
      right
      exact ⟨P, by simpa using findCoverQ_eq_some hf, by simp only [mRootEnvQ, hf]⟩

/-- **The translation is exact, at a form**, with the both-sides covering
patterns. -/
theorem elabLFFormAt_toLexicalAtQ (H : List X) (R : Owner) (t : Src S X) :
    elabLFFormAt R (toLexicalAtQ H R t) = elabMFormAtQ H R t :=
  elabLFId_toLexAt R t _ _ _ _ _ _ _ (corr_rootQ H R t)

variable [DecidableEq S]

/-- **The translation is exact at either direction.**  Lexical fresh on the
translated query and equations, and rule M on the source, run to the same bag
of results with final stores, under pattern-only and under both sides: the
elaborated terms are equal, so the translation keeps the matching direction. -/
theorem runDir_toLexical (dir : Direction) (u : X) (unit : S) (cl : S → Option (Src S X))
    (t : Src S X) (d : Disc) (n : ℕ) (π : Path) (σ : GStore S (BId X)) :
    runDir dir d (progLF u unit (toLexicalProg cl)) n π σ (elabLFFormAt [] (toLexical t)) =
      runDir dir d (progM u unit cl) n π σ (elabMFormAt [] t) := by
  rw [progLF_toLexicalProg, toLexical, elabLFFormAt_toLexicalAt]

/-- The same with the both-sides covering patterns at the query. -/
theorem runDir_toLexicalQ (dir : Direction) (H : List X) (u : X) (unit : S)
    (cl : S → Option (Src S X)) (t : Src S X) (d : Disc) (n : ℕ) (π : Path)
    (σ : GStore S (BId X)) :
    runDir dir d (progLF u unit (toLexicalProg cl)) n π σ (elabLFFormAt [] (toLexicalQ H t)) =
      runDir dir d (progM u unit cl) n π σ (elabMFormAtQ H [] t) := by
  rw [progLF_toLexicalProg, toLexicalQ, elabLFFormAt_toLexicalAtQ]

end Count

namespace IdSlot

variable [DecidableEq X]

/-- **The statement of the renaming theorem** for a run of the slot model and a
run of the identity model, each as a function of the fuel: defined together,
and their bags related result by result (`Renamed`). -/
def RenamingStatement (r₁ : ℕ → Option (Result S (Slot X)))
    (r₂ : ℕ → Option (Result S (BId X))) : Prop :=
  ((∃ n L₁, r₁ n = some L₁) ↔ ∃ m L₂, r₂ m = some L₂) ∧
    ∀ {n m : ℕ} {L₁ : Result S (Slot X)} {L₂ : Result S (BId X)},
      r₁ n = some L₁ → r₂ m = some L₂ → List.Forall₂ Renamed L₁ L₂

/-- Two defined runs whose bags differ in length refute the statement. -/
theorem not_renamingStatement_of_length {r₁ : ℕ → Option (Result S (Slot X))}
    {r₂ : ℕ → Option (Result S (BId X))} {n m a b : ℕ}
    (h₁ : (r₁ n).map List.length = some a) (h₂ : (r₂ m).map List.length = some b) (hab : a ≠ b) :
    ¬ RenamingStatement r₁ r₂ := by
  obtain ⟨L₁, e₁, rfl⟩ := Option.map_eq_some_iff.1 h₁
  obtain ⟨L₂, e₂, rfl⟩ := Option.map_eq_some_iff.1 h₂
  exact fun h => hab (h.2 e₁ e₂).length_eq

/-- **The statement of `transfer`** for the slot model's lexical-fresh run of a
translation, its rule-M run of the source, and the identity model's rule-M run
of the source: the first two are defined together, and both bags are renamings,
result by result, of one bag of the third. -/
def TransferStatement (rLF rM : ℕ → Option (Result S (Slot X)))
    (rI : ℕ → Option (Result S (BId X))) : Prop :=
  ((∃ n L, rLF n = some L) ↔ ∃ n L, rM n = some L) ∧
    ∀ {n n' : ℕ} {L L' : Result S (Slot X)}, rLF n = some L → rM n' = some L' →
      ∃ (k : ℕ) (L₂ : Result S (BId X)), rI k = some L₂ ∧
        List.Forall₂ Renamed L L₂ ∧ List.Forall₂ Renamed L' L₂

/-- Two slot bags of different lengths refute the statement, whatever the
identity run is. -/
theorem not_transferStatement_of_length {rLF rM : ℕ → Option (Result S (Slot X))}
    {rI : ℕ → Option (Result S (BId X))} {n n' a b : ℕ}
    (h₁ : (rLF n).map List.length = some a) (h₂ : (rM n').map List.length = some b)
    (hab : a ≠ b) : ¬ TransferStatement rLF rM rI := by
  obtain ⟨L, e₁, rfl⟩ := Option.map_eq_some_iff.1 h₁
  obtain ⟨L', e₂, rfl⟩ := Option.map_eq_some_iff.1 h₂
  intro h
  obtain ⟨_, L₂, _, hA, hB⟩ := h.2 e₁ e₂
  exact hab (hA.length_eq.trans hB.length_eq.symm)

theorem mRootEnvQ_ok (H : List X) (R : Owner) (t : Src S X) (E cr : List X) (env : IEnv X)
    (y : X) :
    (mRootEnvQ H R t y).spell = y ∧ (mRootEnvQ H R t y).frame = R ∧
      KeyOK R (annM E cr env R R t) (mRootEnvQ H R t y) := by
  unfold mRootEnvQ
  cases h : findCoverQ H (Src.direct t) y false t with
  | none => exact ⟨rfl, rfl, Or.inl rfl⟩
  | some P =>
      exact ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, P, rfl,
        findCover_not_letA t _ y _ P (findCoverQ_eq_some h) _ _ _ _ _⟩)⟩

variable [DecidableEq S]

/-- **The renaming theorem, rule M, with the both-sides covering patterns,
under pattern-only.**  For every list `H`, the identity model that names the
query's names by `findCoverQ H` is the slot model up to renaming. -/
theorem renaming_MQ (H : List X) (u : X) (unit : S) (cl : S → Option (Src S X)) (t : Src S X)
    (hcl : ∀ F body, cl F = some body → body.Admissible) (ht : t.Admissible) :
    RenamingStatement
      (fun n => run .static (progSlot cfgM u unit cl) n [] Store.empty (elabCfg cfgM [] t))
      (fun m => run .static (progM u unit cl) m [] Store.empty (elabMFormAtQ H [] t)) := by
  obtain ⟨h₂, h₃⟩ := ht
  have e₁ : elabCfg cfgM [] t =
      (annM (Src.direct t) [] (mRootEnvQ H [] t) [] [] t).slotOf [] (fun _ => []) [] :=
    elabMS_eq_slotOf _ t _ _ _ _ _ _ _
  have e₂ : elabMFormAtQ H [] t =
      (annM (Src.direct t) [] (mRootEnvQ H [] t) [] [] t).idOf [] (mRootEnvQ H [] t)
        (fun _ => []) [] [] :=
    elabMId_eq_idOf _ t _ _ _ _ _ _
  unfold RenamingStatement
  rw [e₁, e₂]
  exact renaming_of (progRel_M u unit cl hcl)
    (root_config (annM_WF t _ _ _ _ _ h₂) (by rw [freePars_annM]; exact h₃)
      (fun y => mRootEnvQ_ok H [] t _ _ _ y))

/-- **The translator's correctness in the slot model, with the both-sides
covering patterns, under pattern-only.** -/
theorem transferQ (H : List X) (u : X) (unit : S) (cl : S → Option (Src S X)) (t : Src S X)
    (hcl : ∀ F body, cl F = some body → body.Admissible) (ht : t.Admissible) :
    TransferStatement
      (fun n => run .static (progSlot cfgLF u unit (toLexicalProg cl)) n [] Store.empty
        (elabCfg cfgLF [] (toLexicalQ H t)))
      (fun n => run .static (progSlot cfgM u unit cl) n [] Store.empty (elabCfg cfgM [] t))
      (fun k => run .static (progM u unit cl) k [] Store.empty (elabMFormAtQ H [] t)) := by
  unfold TransferStatement
  dsimp only
  have hclT : ∀ F body, toLexicalProg cl F = some body → body.Admissible := by
    intro F body h
    simp only [toLexicalProg, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rfl⟩ := h
    exact admissible_toLexAt (hcl F b hb) _ _ _ _ _
  have htT : (toLexicalQ H t).Admissible := admissible_toLexAt ht _ _ _ _ _
  obtain ⟨hLF₁, hLF₂⟩ := renaming_LF u unit (toLexicalProg cl) (toLexicalQ H t) hclT htT
  have hM := renaming_MQ H u unit cl t hcl ht
  dsimp only [RenamingStatement] at hM
  obtain ⟨hM₁, hM₂⟩ := hM
  have heq : ∀ n, run .static (progLF u unit (toLexicalProg cl)) n [] Store.empty
      (elabLFFormAt [] (toLexicalQ H t)) = run .static (progM u unit cl) n [] Store.empty
        (elabMFormAtQ H [] t) := by
    intro n
    have h := runDir_toLexicalQ .patternOnly H u unit cl t .static n [] Store.empty
    rwa [runDir_patternOnly, runDir_patternOnly] at h
  refine ⟨?_, ?_⟩
  · rw [hLF₁, hM₁]
    simp only [heq]
  · intro n n' L L' h₁ h₂
    obtain ⟨m, L₂, hm⟩ := hLF₁.1 ⟨n, L, h₁⟩
    exact ⟨m, L₂, by rw [← heq]; exact hm, hLF₂ h₁ hm, hM₂ h₂ (by rw [← heq]; exact hm)⟩

/-! ## `SC_patAgree`, read with the both-sides code matcher -/

variable {X₁ X₂ : Type v} [DecidableEq X₁] [DecidableEq X₂] [CodeId X₁] [CodeId X₂]

/-- `Setting.PatAgree`, with the both-sides code matcher `matchCode2` in place of
`matchCode`. -/
def Setting.PatAgree2 (C : Setting S X₁ X₂) : Prop :=
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
    OptRel (StoreRel C ν D) (matchCode2 σ₁ c₁ q₁) (matchCode2 σ₂ c₂ q₂)

omit [DecidableEq X₁] [DecidableEq X₂] [CodeId X₁] [CodeId X₂] in
/-- **`SC_patAgree` fails for the both-sides code matcher.**  The pattern code
`s` against the sealed code `$y`: both models bind the hole of the value, and
the statement's domain `D` holds only the free names of the pattern code.  The
failing goal is `StoreRel.dom`: the first store binds a name outside `D`. -/
theorem not_SC_patAgree2 (s : S) (y : X) :
    ¬ (SC : Setting S (Slot X) (BId X)).PatAgree2 := by
  intro hP
  have h := @hP codeFwd codeFwd true (.sym s) (.sym s) (codeOf [] (.sv y)) (codeI [] (.sv y)) ∅
    Store.empty Store.empty (.sym s) rfl rfl (QR_codeOf (Or.inl rfl) (.sv y) codeFwd)
    (by simp [freeNames]) (Set.injOn_empty _) (fun _ h => h.elim)
    (fun _ h => by simp [sealedFree] at h)
    (fun n hn => by
      obtain ⟨y', rfl⟩ := codeVars_codeOf [] (.sv y) n hn
      exact Or.inr ⟨_, rfl, rfl⟩)
    (StoreRel.empty _ _)
  have e₁ : ∃ σ₁, matchCode2 (Store.empty : GStore S (Slot X)) (.sym s) (codeOf [] (.sv y)) =
      some σ₁ ∧ σ₁ (.src ([], y)) = some (.sym s) := ⟨_, rfl, by simp⟩
  have e₂ : ∃ σ₂, matchCode2 (Store.empty : GStore S (BId X)) (.sym s) (codeI [] (.sv y)) =
      some σ₂ := ⟨_, rfl⟩
  obtain ⟨σ₁, hσ₁, hb⟩ := e₁
  obtain ⟨σ₂, hσ₂⟩ := e₂
  rw [hσ₁, hσ₂] at h
  exact (h.dom (.src ([], y)) (by rw [hb]; simp)).elim

end IdSlot

end Mettapedia.GSLT.LanguageDef.TemplateScope
