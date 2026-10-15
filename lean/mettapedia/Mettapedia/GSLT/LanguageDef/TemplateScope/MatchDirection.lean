import Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotRun
import Mettapedia.GSLT.LanguageDef.TemplateScope.Surface

/-!
# Template scope: which side of a `let` may be filled

The evaluator of `TemplateScope.Evaluation` matches a `let` in one direction:
`matchT` and `matchCodeIn` write only store names of the pattern.  This module
adds the other reading beside it and changes neither.

* **Pattern-only** (`Direction.patternOnly`): the shipped evaluator.
* **Both sides** (`Direction.bothSides`): a `let` also refines unbound names of
  its value, and a hole in value code takes the code of the pattern part aligned
  with it.

## The both-sides matcher

`matchT2` walks pattern and value together through data application.  At a pair
of parts one of which is ground under the store, it runs the pattern-only
matcher `matchT` with the *other* part as its pattern (`exchange`): the
first-order part of both sides is `matchT` with the sides exchanged.  A pattern
quotation against a quotation is matched by `matchCode2In`, which extends
`matchCodeIn` by one rule: a hole of the value code takes the pattern part
aligned with it (`holeFill`), read along the value's binders, as contextual
code when it mentions a binder in scope.

**Two unbound names.**  Stores are ground (`GStore`): a cell holds a `GVal`, and
a store name is not one (`GVal.toTm_ne_var`).  So a pair of two different names,
both unbound, has no ground binding and the matcher answers `none`
(`matchT2_var_var_unbound`, `matchCode2In_hole_hole_unbound`).  The one place
the model has a stand-in for an alias: a `let` whose whole pattern is one name
that is unbound in the store, and whose value is not ground, substitutes the
value for the name in the body (`step`, `letCont2`), under both readings.

**A pattern that is one bound name.**  When the name already holds a value the
`let` is a match of the stored value against the new one.  Pattern-only gives
no answer when the new value is not ground or is a lambda written in place
(`IdSlot.letCont_var_bound`, `IdSlot.step_letP_some_bound`).  Both sides
matches the two with `matchT2` (`letCont2_var_bound`): the new value is then
the pattern, so its unbound names are refined from the stored value
(`matchT2_var_bound_nonground`); a lambda matches no stored value
(`matchT2_var_bound_lam`).

## The evaluator

`stepDir dir` is `step`, except that under `bothSides` a `let` whose value is
not a lambda written in place continues with `letCont2`.  `runDir dir` iterates
it.

## The direction axis

`DirConfig` pairs a `Config` (ownership, lifetime, readout: unchanged, with its
three-field spelling) with a `Direction`.  A `Config` is read at pattern-only
(`Config.patternOnly`, and the coercion); `Config.bothSides` is the other
reading of the same three fields.

## Main results

* `runDir_patternOnly` — at pattern-only the evaluator is `run`; hence
  `answersDirCfg_patternOnly`: an existing configuration, read at pattern-only,
  has the answers `answersCfg` gives.
* `runDir_mono` — fuel monotonicity under both readings.
* `letCont2_var_unbound`, `letCont2_var_bound`, `stepDir_bothSides_letLam_bound`
  — a pattern that is one name: substitution while the name is unbound, and the
  match of the stored value against the new one when it holds a value.
* `matchCodeIn_le_matchCode2In`, `matchT_le_matchT2` — the both-sides matchers
  extend the pattern-only ones: where those match, these match with the same
  store.
* `run_sublist_runDir` — **both sides only adds answers**: when both runs are
  defined, the pattern-only bag is a sublist of the both-sides bag.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

/-- Which side of a `let` a match may fill. -/
inductive Direction where
  /-- A `let` writes only store names of its pattern. -/
  | patternOnly
  /-- A `let` also refines unbound names of its value, and fills holes of value
  code. -/
  | bothSides
  deriving DecidableEq, Repr

variable {S : Type u} {X : Type v}

/-! ## Code -/

/-- The store names `matchCodeIn` reaches in pattern code: every occurrence
outside a sealed quotation, under any binder of the code.  (`freeNames` drops a
name a lambda of the code owns, which the matcher still writes; `Tm.vars` adds
the names of sealed quotations, which it never writes.) -/
def codeHoles : Tm S X → List (Nm X)
  | .var n => [n]
  | .lam _ _ b => codeHoles b
  | .app f a => codeHoles f ++ codeHoles a
  | .letP p w b => codeHoles p ++ codeHoles w ++ codeHoles b
  | .alt a b => codeHoles a ++ codeHoles b
  | .pquote c => codeHoles c
  | _ => []

variable [DecidableEq X] [CodeId X]

/-- Read the parameters of pattern code as the value binders aligned with them:
each binder `k` in scope replaces every parameter `CodeId` identifies with it. -/
def alignTo (bound : List (Nm X)) (q : Tm S X) : Tm S X :=
  bound.foldr (fun k t => substBinder k (.pvar k) t) q

/-- **What a hole of value code takes** from the pattern part aligned with it:
the part, read along the value's binders (`alignTo`) and under the store, when
no store name is left in it.  It is contextual code when it mentions a binder
in scope, and a ground value otherwise (`contextualVal`). -/
def holeFill (σ : GStore S X) (bound : List (Nm X)) (q : Tm S X) : Option (GVal S X) :=
  if (codeHoles (act σ (alignTo bound q))).isEmpty then
    contextualVal bound (act σ (alignTo bound q))
  else Option.none

variable [DecidableEq S]

/-- **Match inside a quotation, filling both sides.**  Every rule of
`matchCodeIn`, and two more.  A hole of the value code takes the aligned pattern
part (`holeFill`).  Two holes: the one that is unbound takes the other's value;
the same hole on both sides matches; two different unbound holes do not, since
no ground binding relates them. -/
def matchCode2In (σ : GStore S X) (bound : List (Nm X)) :
    Tm S X → Tm S X → Option (GStore S X)
  | .var n, t =>
      if CodeId.hole n then
        match contextualVal bound t with
        | some g => refineStep σ (n, g)
        | Option.none =>
            match t with
            | .var m =>
                if CodeId.hole m then
                  match σ m with
                  | some g => refineStep σ (n, g)
                  | Option.none =>
                      match σ n with
                      | some g => refineStep σ (m, g)
                      | Option.none => if n = m then some σ else Option.none
                else Option.none
            | _ => Option.none
      else
        match t with
        | .var m => if CodeId.same n m then some σ else Option.none
        | _ => Option.none
  | .pvar x, .pvar y => if CodeId.same x y then some σ else Option.none
  | .lam x₁ own₁ b₁, .lam x₂ own₂ b₂ =>
      if CodeId.same x₁ x₂ && decide (own₁ = own₂) then
        matchCode2In σ (bound ++ [x₂]) b₁ b₂
      else Option.none
  | .app p₁ p₂, .app t₁ t₂ =>
      match matchCode2In σ bound p₁ t₁ with
      | some σ' => matchCode2In σ' bound p₂ t₂
      | Option.none => Option.none
  | .letP p₁ w₁ b₁, .letP p₂ w₂ b₂ =>
      match matchCode2In σ bound p₁ p₂ with
      | some σ₁ =>
          match matchCode2In σ₁ bound w₁ w₂ with
          | some σ₂ => matchCode2In σ₂ bound b₁ b₂
          | Option.none => Option.none
      | Option.none => Option.none
  | .alt p₁ p₂, .alt t₁ t₂ =>
      match matchCode2In σ bound p₁ t₁ with
      | some σ' => matchCode2In σ' bound p₂ t₂
      | Option.none => Option.none
  | .sym s₁, .sym s₂ => if s₁ = s₂ then some σ else Option.none
  | .fn F₁, .fn F₂ => if F₁ = F₂ then some σ else Option.none
  | .quote c₁, .quote c₂ => if codeEq c₁ c₂ then some σ else Option.none
  | .pquote pc, .quote c => matchCode2In σ bound pc c
  | q, .var m =>
      if CodeId.hole m then
        match holeFill σ bound q with
        | some g => refineStep σ (m, g)
        | Option.none => Option.none
      else Option.none
  | _, _ => Option.none

/-- Match at the quotation's root, filling both sides. -/
def matchCode2 (σ : GStore S X) : Tm S X → Tm S X → Option (GStore S X) :=
  matchCode2In σ []

/-! ## First-order terms -/

/-- **A pair of parts, one of them ground under the store**: the pattern-only
matcher, with the other part as its pattern.  When the value part is ground it
is `matchT` as shipped.  When only the pattern part is ground, the value part
is the pattern, so its unbound names are refined.  When neither is ground there
is no ground binding to make. -/
def exchange (σ : GStore S X) (p t : Tm S X) : Option (GStore S X) :=
  match (act σ t).toGVal? with
  | some g => matchT σ p g.toTm
  | Option.none =>
      match (act σ p).toGVal? with
      | some g => matchT σ (act σ t) g.toTm
      | Option.none => Option.none

/-- **Match a pattern against a term, filling both sides.**  Data application
is matched component by component, left to right.  A pattern quotation is
matched as code by `matchCode2`; two quotations are compared by `codeEq`, as in
`matchT`.  The same name on both sides matches.  Every other pair is
`exchange`. -/
def matchT2 (σ : GStore S X) : Tm S X → Tm S X → Option (GStore S X)
  | .app p₁ p₂, .app t₁ t₂ =>
      match matchT2 σ p₁ t₁ with
      | some σ' => matchT2 σ' p₂ t₂
      | Option.none => Option.none
  | .pquote pc, .quote c => matchCode2 σ pc c
  | .quote c₁, .quote c₂ => if codeEq c₁ c₂ then some σ else Option.none
  | .var n, .var m => if n = m then some σ else exchange σ (.var n) (.var m)
  | p, t => exchange σ p t

/-! ## The evaluator -/

/-- Continue with the body under the store a match returned, or give no answer. -/
def letBody (rec : Runner S X) (π : Path) (b : Tm S X) :
    Option (GStore S X) → Option (Result S X)
  | some σ₂ => rec (π ++ [1]) σ₂ b
  | Option.none => some []

/-- **What a both-sides `let` does with one value of its right-hand side.**  A
ground value is matched by `matchT2`.  A value that is not ground is substituted
for a pattern that is one name unbound in the store, as under pattern-only.
Against a name that already holds a value, and against any other pattern, it is
matched by `matchT2`, where pattern-only gives no answer. -/
def letCont2 (rec : Runner S X) (π : Path) (p b : Tm S X) (r₁ : Tm S X × GStore S X) :
    Option (Result S X) :=
  match (act r₁.2 r₁.1).toGVal? with
  | some g => letBody rec π b (matchT2 r₁.2 p g.toTm)
  | Option.none =>
      match p with
      | .var f =>
          match r₁.2 f with
          | Option.none => rec (π ++ [1]) r₁.2 (subst (Sub.single f r₁.1) Sub.none b)
          | some _ => letBody rec π b (matchT2 r₁.2 (.var f) (act r₁.2 r₁.1))
      | _ => letBody rec π b (matchT2 r₁.2 p (act r₁.2 r₁.1))

/-- **One unfolding of the evaluator, at a matching direction.**  It is `step`,
except that under `bothSides` a `let` whose value is not a lambda written in
place continues with `letCont2`.  A lambda written in place is taken as `step`
takes it under both readings: substituted for an unbound name, and no answer
against a name that holds a value (`matchT2_var_bound_lam`: no stored value
matches a lambda). -/
def stepDir (dir : Direction) (d : Disc) (prog : S → Option (Tm S X)) (rec : Runner S X) :
    Runner S X :=
  fun π σ t =>
    match dir, t with
    | .bothSides, .letP p w b =>
        match letLam? p w with
        | some _ => step d prog rec π σ (.letP p w b)
        | Option.none => bindOpt (rec (π ++ [0]) σ w) (letCont2 rec π p b)
    | _, t => step d prog rec π σ t

/-- The evaluator with `n` units of fuel, at a matching direction. -/
def runDir (dir : Direction) (d : Disc) (prog : S → Option (Tm S X)) : ℕ → Runner S X
  | 0 => fun _ _ _ => Option.none
  | n + 1 => stepDir dir d prog (runDir dir d prog n)

/-- The answers at a matching direction: each result with its final store
applied. -/
def answersDir (dir : Direction) (d : Disc) (prog : S → Option (Tm S X)) (n : ℕ)
    (t : Tm S X) : Option (List (Tm S X)) :=
  (runDir dir d prog n [] Store.empty t).map (List.map fun r => act r.2 r.1)

/-! ## Pattern-only is the shipped evaluator -/

theorem stepDir_patternOnly (d : Disc) (prog : S → Option (Tm S X)) (rec : Runner S X) :
    stepDir .patternOnly d prog rec = step d prog rec := rfl

/-- **At pattern-only the evaluator is `run`.** -/
theorem runDir_patternOnly (d : Disc) (prog : S → Option (Tm S X)) :
    ∀ n, runDir .patternOnly d prog n = run d prog n
  | 0 => rfl
  | n + 1 => by
      show stepDir .patternOnly d prog (runDir .patternOnly d prog n) = step d prog (run d prog n)
      rw [runDir_patternOnly d prog n, stepDir_patternOnly]

theorem answersDir_patternOnly (d : Disc) (prog : S → Option (Tm S X)) (n : ℕ) (t : Tm S X) :
    answersDir .patternOnly d prog n t = answers d prog n t := by
  unfold answersDir answers
  rw [runDir_patternOnly]

/-- Under both sides, a `let` whose value is not a lambda written in place
continues with `letCont2`. -/
theorem stepDir_bothSides_letP (d : Disc) (prog : S → Option (Tm S X)) (rec : Runner S X)
    (π : Path) (σ : GStore S X) {p w b : Tm S X} (h : letLam? p w = Option.none) :
    stepDir .bothSides d prog rec π σ (.letP p w b) =
      bindOpt (rec (π ++ [0]) σ w) (letCont2 rec π p b) := by
  simp only [stepDir, h]

theorem stepDir_bothSides_letLam (d : Disc) (prog : S → Option (Tm S X)) (rec : Runner S X)
    (π : Path) (σ : GStore S X) {p w b : Tm S X} {f : Nm X} (h : letLam? p w = some f) :
    stepDir .bothSides d prog rec π σ (.letP p w b) = step d prog rec π σ (.letP p w b) := by
  simp only [stepDir, h]

/-- Under both sides, a term that is not a `let` unfolds as under `step`. -/
theorem stepDir_bothSides_of_ne_letP (d : Disc) (prog : S → Option (Tm S X)) (rec : Runner S X)
    (π : Path) (σ : GStore S X) {t : Tm S X} (h : ∀ p w b, t ≠ .letP p w b) :
    stepDir .bothSides d prog rec π σ t = step d prog rec π σ t := by
  cases t with
  | letP p w b => exact absurd rfl (h p w b)
  | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _
  | alt _ _ => rfl

/-! ## Fuel monotonicity under both readings -/

omit [DecidableEq X] [CodeId X] [DecidableEq S] in
theorem letBody_mono {r r' : Runner S X} (h : Runner.Le r r') (π : Path) (b : Tm S X)
    (o : Option (GStore S X)) {M : Result S X} (hM : letBody r π b o = some M) :
    letBody r' π b o = some M := by
  cases o with
  | some σ₂ => exact h _ _ _ _ hM
  | none => exact hM

theorem letCont2_mono {r r' : Runner S X} (h : Runner.Le r r') (π : Path) (p b : Tm S X)
    (a : Tm S X × GStore S X) (M : Result S X) (hM : letCont2 r π p b a = some M) :
    letCont2 r' π p b a = some M := by
  unfold letCont2 at hM ⊢
  cases hg : (act a.2 a.1).toGVal? with
  | some g =>
      rw [hg] at hM
      exact letBody_mono h π b _ hM
  | none =>
      rw [hg] at hM
      cases p with
      | var f =>
          simp only at hM ⊢
          cases hf : a.2 f with
          | none => rw [hf] at hM; exact h _ _ _ _ hM
          | some _ => rw [hf] at hM; exact letBody_mono h π b _ hM
      | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => exact letBody_mono h π b _ hM

theorem stepDir_mono (dir : Direction) (d : Disc) (prog : S → Option (Tm S X))
    {r r' : Runner S X} (h : Runner.Le r r') :
    Runner.Le (stepDir dir d prog r) (stepDir dir d prog r') := by
  intro π σ t L hL
  cases dir with
  | patternOnly => exact step_mono d prog h π σ t L hL
  | bothSides =>
      by_cases ht : ∃ p w b, t = .letP p w b
      · obtain ⟨p, w, b, rfl⟩ := ht
        cases hl : letLam? p w with
        | some f =>
            rw [stepDir_bothSides_letLam d prog _ π σ hl] at hL ⊢
            exact step_mono d prog h π σ _ L hL
        | none =>
            rw [stepDir_bothSides_letP d prog _ π σ hl] at hL ⊢
            exact bindOpt_mono (fun l hl => h _ _ _ _ hl) (letCont2_mono h π p b) hL
      · have e : ∀ ρ : Runner S X, stepDir .bothSides d prog ρ π σ t = step d prog ρ π σ t :=
          fun ρ => stepDir_bothSides_of_ne_letP d prog ρ π σ (fun p w b e => ht ⟨p, w, b, e⟩)
        rw [e] at hL ⊢
        exact step_mono d prog h π σ t L hL

theorem runDir_le_succ (dir : Direction) (d : Disc) (prog : S → Option (Tm S X)) :
    ∀ n, Runner.Le (runDir dir d prog n) (runDir dir d prog (n + 1))
  | 0 => fun _ _ _ _ h => by cases h
  | n + 1 => stepDir_mono dir d prog (runDir_le_succ dir d prog n)

/-- **Fuel monotonicity, at either direction.**  A defined run stays defined,
with the same bag. -/
theorem runDir_mono (dir : Direction) (d : Disc) (prog : S → Option (Tm S X)) {n m : ℕ}
    (hnm : n ≤ m) {π : Path} {σ : GStore S X} {t : Tm S X} {L : Result S X}
    (h : runDir dir d prog n π σ t = some L) : runDir dir d prog m π σ t = some L := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact runDir_le_succ dir d prog _ _ _ _ _ ih

/-- **Determinism, at either direction**: two defined runs agree. -/
theorem runDir_det (dir : Direction) {d : Disc} {prog : S → Option (Tm S X)} {n m : ℕ}
    {π : Path} {σ : GStore S X} {t : Tm S X} {L L' : Result S X}
    (h : runDir dir d prog n π σ t = some L) (h' : runDir dir d prog m π σ t = some L') :
    L = L' := by
  have e1 := runDir_mono dir d prog (le_max_left n m) h
  have e2 := runDir_mono dir d prog (le_max_right n m) h'
  rw [e1] at e2
  exact Option.some.inj e2

/-- **The answers do not depend on the fuel, at either direction**: two defined
answer bags of one term are equal. -/
theorem answersDir_det (dir : Direction) {d : Disc} {prog : S → Option (Tm S X)} {n m : ℕ}
    {t : Tm S X} {bag bag' : List (Tm S X)} (h : answersDir dir d prog n t = some bag)
    (h' : answersDir dir d prog m t = some bag') : bag = bag' := by
  unfold answersDir at h h'
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨L', hL', rfl⟩ := Option.map_eq_some_iff.1 h'
  rw [runDir_det dir hL hL']

/-! ## Both sides extends pattern-only -/

/-- **The both-sides code matcher extends `matchCodeIn`**: where the
pattern-only matcher returns a store, this one returns the same store. -/
theorem matchCodeIn_le_matchCode2In : ∀ (bound : List (Nm X)) (p t : Tm S X) (σ σ' : GStore S X),
    matchCodeIn σ bound p t = some σ' → matchCode2In σ bound p t = some σ'
  | bound, .var n, t, σ, σ', h => by
      simp only [matchCodeIn] at h
      simp only [matchCode2In]
      cases hhn : CodeId.hole n with
      | true =>
          simp only [hhn, if_true] at h ⊢
          cases hg : contextualVal bound t with
          | none => simp [hg] at h
          | some g =>
              simp only [hg] at h ⊢
              exact h
      | false =>
          simp only [hhn, Bool.false_eq_true, if_false] at h ⊢
          exact h
  | _, .pvar x, t, σ, σ', h => by
      cases t with
      | pvar y =>
          simp only [matchCodeIn] at h
          simp only [matchCode2In]
          exact h
      | sym _ | fn _ | var _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCodeIn] at h
  | bound, .lam x₁ own₁ b₁, t, σ, σ', h => by
      cases t with
      | lam x₂ own₂ b₂ =>
          simp only [matchCodeIn] at h
          simp only [matchCode2In]
          cases hcond : CodeId.same x₁ x₂ && decide (own₁ = own₂) with
          | true =>
              simp only [hcond, if_true] at h ⊢
              exact matchCodeIn_le_matchCode2In (bound ++ [x₂]) b₁ b₂ σ σ' h
          | false => simp [hcond] at h
      | sym _ | fn _ | var _ | pvar _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCodeIn] at h
  | bound, .app p₁ p₂, t, σ, σ', h => by
      cases t with
      | app t₁ t₂ =>
          simp only [matchCodeIn] at h
          simp only [matchCode2In]
          cases h₁ : matchCodeIn σ bound p₁ t₁ with
          | none => simp [h₁] at h
          | some σ₁ =>
              simp only [h₁] at h
              rw [matchCodeIn_le_matchCode2In bound p₁ t₁ σ σ₁ h₁]
              exact matchCodeIn_le_matchCode2In bound p₂ t₂ σ₁ σ' h
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCodeIn] at h
  | bound, .letP p₁ w₁ b₁, t, σ, σ', h => by
      cases t with
      | letP p₂ w₂ b₂ =>
          simp only [matchCodeIn] at h
          simp only [matchCode2In]
          cases h₁ : matchCodeIn σ bound p₁ p₂ with
          | none => simp [h₁] at h
          | some σ₁ =>
              simp only [h₁] at h
              cases h₂ : matchCodeIn σ₁ bound w₁ w₂ with
              | none => simp [h₂] at h
              | some σ₂ =>
                  simp only [h₂] at h
                  rw [matchCodeIn_le_matchCode2In bound p₁ p₂ σ σ₁ h₁]
                  simp only
                  rw [matchCodeIn_le_matchCode2In bound w₁ w₂ σ₁ σ₂ h₂]
                  exact matchCodeIn_le_matchCode2In bound b₁ b₂ σ₂ σ' h
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _
      | alt _ _ => simp [matchCodeIn] at h
  | bound, .alt p₁ p₂, t, σ, σ', h => by
      cases t with
      | alt t₁ t₂ =>
          simp only [matchCodeIn] at h
          simp only [matchCode2In]
          cases h₁ : matchCodeIn σ bound p₁ t₁ with
          | none => simp [h₁] at h
          | some σ₁ =>
              simp only [h₁] at h
              rw [matchCodeIn_le_matchCode2In bound p₁ t₁ σ σ₁ h₁]
              exact matchCodeIn_le_matchCode2In bound p₂ t₂ σ₁ σ' h
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _
      | letP _ _ _ => simp [matchCodeIn] at h
  | _, .sym _, t, σ, σ', h => by
      cases t with
      | sym _ =>
          simp only [matchCodeIn] at h
          simp only [matchCode2In]
          exact h
      | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCodeIn] at h
  | _, .fn _, t, σ, σ', h => by
      cases t with
      | fn _ =>
          simp only [matchCodeIn] at h
          simp only [matchCode2In]
          exact h
      | sym _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCodeIn] at h
  | _, .quote _, t, σ, σ', h => by
      cases t with
      | quote _ =>
          simp only [matchCodeIn] at h
          simp only [matchCode2In]
          exact h
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCodeIn] at h
  | bound, .pquote pc, t, σ, σ', h => by
      cases t with
      | quote c =>
          simp only [matchCodeIn] at h
          simp only [matchCode2In]
          exact matchCodeIn_le_matchCode2In bound pc c σ σ' h
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ => simp [matchCodeIn] at h
  | _, .ctx _ _, t, σ, σ', h => by simp [matchCodeIn] at h

theorem matchCode_le_matchCode2 (p t : Tm S X) (σ σ' : GStore S X)
    (h : matchCode σ p t = some σ') : matchCode2 σ p t = some σ' :=
  matchCodeIn_le_matchCode2In [] p t σ σ' h

/-- Against a ground value, `exchange` is the pattern-only matcher. -/
theorem exchange_ground (σ : GStore S X) (p : Tm S X) (g : GVal S X) :
    exchange σ p g.toTm = matchT σ p g.toTm := by
  unfold exchange
  rw [act_toTm, GVal.toTm_toGVal?]

/-- **The both-sides matcher extends `matchT`** on the values pattern-only
matches against (ground values): where `matchT` returns a store, `matchT2`
returns the same store. -/
theorem matchT_le_matchT2 : ∀ (p : Tm S X) (g : GVal S X) (σ σ' : GStore S X),
    matchT σ p g.toTm = some σ' → matchT2 σ p g.toTm = some σ'
  | .app p₁ p₂, .app f a, σ, σ', h => by
      simp only [GVal.toTm, matchT] at h
      simp only [GVal.toTm, matchT2]
      cases h₁ : matchT σ p₁ f.toTm with
      | none => simp [h₁] at h
      | some σ₁ =>
          simp only [h₁] at h
          rw [matchT_le_matchT2 p₁ f σ σ₁ h₁]
          exact matchT_le_matchT2 p₂ a σ₁ σ' h
  | .pquote pc, .quote c, σ, σ', h => by
      simp only [GVal.toTm, matchT] at h
      simp only [GVal.toTm, matchT2]
      exact matchCode_le_matchCode2 pc c σ σ' h
  | .quote c₁, .quote c₂, σ, σ', h => by
      simp only [GVal.toTm, matchT] at h
      simp only [GVal.toTm, matchT2]
      exact h
  | .var n, g, σ, σ', h => by
      have e : matchT2 σ (.var n) g.toTm = exchange σ (.var n) g.toTm := by cases g <;> rfl
      rw [e, exchange_ground]
      exact h
  | .app p₁ p₂, .sym s, σ, σ', h => by
      rw [← exchange_ground] at h
      exact h
  | .app p₁ p₂, .quote c, σ, σ', h => by
      rw [← exchange_ground] at h
      exact h
  | .app p₁ p₂, .ctx ks c, σ, σ', h => by
      rw [← exchange_ground] at h
      exact h
  | .pquote pc, .sym s, σ, σ', h => by
      rw [← exchange_ground] at h
      exact h
  | .pquote pc, .app f a, σ, σ', h => by
      rw [← exchange_ground] at h
      exact h
  | .pquote pc, .ctx ks c, σ, σ', h => by
      rw [← exchange_ground] at h
      exact h
  | .quote c₁, .sym s, σ, σ', h => by
      rw [← exchange_ground] at h
      exact h
  | .quote c₁, .app f a, σ, σ', h => by
      rw [← exchange_ground] at h
      exact h
  | .quote c₁, .ctx ks c, σ, σ', h => by
      rw [← exchange_ground] at h
      exact h
  | .sym s, g, σ, σ', h => by
      have e : matchT2 σ (.sym s) g.toTm = exchange σ (.sym s) g.toTm := by cases g <;> rfl
      rw [e, exchange_ground]
      exact h
  | .fn F, g, σ, σ', h => by
      have e : matchT2 σ (.fn F) g.toTm = exchange σ (.fn F) g.toTm := by cases g <;> rfl
      rw [e, exchange_ground]
      exact h
  | .pvar x, g, σ, σ', h => by
      have e : matchT2 σ (.pvar x) g.toTm = exchange σ (.pvar x) g.toTm := by cases g <;> rfl
      rw [e, exchange_ground]
      exact h
  | .lam x own b, g, σ, σ', h => by
      have e : matchT2 σ (.lam x own b) g.toTm = exchange σ (.lam x own b) g.toTm := by
        cases g <;> rfl
      rw [e, exchange_ground]
      exact h
  | .letP p w b, g, σ, σ', h => by
      have e : matchT2 σ (.letP p w b) g.toTm = exchange σ (.letP p w b) g.toTm := by
        cases g <;> rfl
      rw [e, exchange_ground]
      exact h
  | .alt t u, g, σ, σ', h => by
      have e : matchT2 σ (.alt t u) g.toTm = exchange σ (.alt t u) g.toTm := by cases g <;> rfl
      rw [e, exchange_ground]
      exact h
  | .ctx ks c, g, σ, σ', h => by
      have e : matchT2 σ (.ctx ks c) g.toTm = exchange σ (.ctx ks c) g.toTm := by cases g <;> rfl
      rw [e, exchange_ground]
      exact h

/-! ## Both sides only adds answers -/

/-- One runner's bags are sublists of another's, wherever both are defined. -/
def Runner.Sub (r r' : Runner S X) : Prop :=
  ∀ π σ t L L', r π σ t = some L → r' π σ t = some L' → L.Sublist L'

omit [DecidableEq X] [CodeId X] [DecidableEq S] in
/-- A sublist of the inputs, with pointwise sublists of the outputs, gives a
sublist of the bag. -/
theorem bindAll_sublist {α β : Type*} {g g' : α → Option (List β)}
    (hg : ∀ a M M', g a = some M → g' a = some M' → M.Sublist M') :
    ∀ {l l' : List α} {L L' : List β}, l.Sublist l' → bindAll l g = some L →
      bindAll l' g' = some L' → L.Sublist L'
  | _, _, L, L', .slnil, h, _ => by
      simp only [bindAll, Option.some.injEq] at h
      subst h
      exact List.nil_sublist L'
  | l, _, L, L', .cons (l₂ := l') a hs, h, h' => by
      unfold bindAll at h'
      cases hga : g' a with
      | none => rw [hga] at h'; cases h'
      | some m' =>
          cases hrest : bindAll l' g' with
          | none => rw [hga, hrest] at h'; cases h'
          | some R' =>
              rw [hga, hrest] at h'
              injection h' with h'
              subst h'
              exact (bindAll_sublist hg hs h hrest).trans (List.sublist_append_right m' R')
  | _, _, L, L', .cons_cons (l₁ := l) (l₂ := l') a hs, h, h' => by
      unfold bindAll at h h'
      cases hga : g a with
      | none => rw [hga] at h; cases h
      | some m =>
          cases hrest : bindAll l g with
          | none => rw [hga, hrest] at h; cases h
          | some R =>
              rw [hga, hrest] at h
              injection h with h
              subst h
              cases hga' : g' a with
              | none => rw [hga'] at h'; cases h'
              | some m' =>
                  cases hrest' : bindAll l' g' with
                  | none => rw [hga', hrest'] at h'; cases h'
                  | some R' =>
                      rw [hga', hrest'] at h'
                      injection h' with h'
                      subst h'
                      exact (hg a m m' hga hga').append (bindAll_sublist hg hs hrest hrest')

/-- The pattern-only `let` continuation against the both-sides one, on one
value: the same call of the body, or no answer under pattern-only. -/
theorem letCont_sub {r r' : Runner S X} (h : Runner.Sub r r') (π : Path) (p b : Tm S X)
    (a : Tm S X × GStore S X) (M M' : Result S X) (hM : IdSlot.letCont r π p b a = some M)
    (hM' : letCont2 r' π p b a = some M') : M.Sublist M' := by
  unfold IdSlot.letCont at hM
  unfold letCont2 at hM'
  cases hg : (act a.2 a.1).toGVal? with
  | some g =>
      rw [hg] at hM hM'
      simp only at hM hM'
      cases hm : matchT a.2 p g.toTm with
      | some σ₂ =>
          rw [hm] at hM
          rw [matchT_le_matchT2 p g a.2 σ₂ hm] at hM'
          exact h _ _ _ _ _ hM hM'
      | none =>
          rw [hm] at hM
          injection hM with hM
          subst hM
          exact List.nil_sublist M'
  | none =>
      rw [hg] at hM hM'
      simp only at hM hM'
      cases p with
      | var f =>
          simp only at hM hM'
          cases hf : a.2 f with
          | none =>
              rw [hf] at hM hM'
              exact h _ _ _ _ _ hM hM'
          | some _ =>
              rw [hf] at hM
              injection hM with hM
              subst hM
              exact List.nil_sublist M'
      | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
      | alt _ _ =>
          injection hM with hM
          subst hM
          exact List.nil_sublist M'

theorem step_sub_stepDir (d : Disc) (prog : S → Option (Tm S X)) {r r' : Runner S X}
    (h : Runner.Sub r r') : Runner.Sub (step d prog r) (stepDir .bothSides d prog r') := by
  intro π σ t L L' hL hL'
  cases t with
  | fn F =>
      change step d prog r' π σ (.fn F) = some L' at hL'
      simp only [step] at hL hL'
      cases hp : prog F with
      | none =>
          rw [hp] at hL hL'
          rw [← Option.some.inj hL, ← Option.some.inj hL']
      | some e =>
          rw [hp] at hL hL'
          exact h _ _ _ _ _ hL hL'
  | app f a =>
      change step d prog r' π σ (.app f a) = some L' at hL'
      simp only [step] at hL hL'
      obtain ⟨l₁, hl₁, hb₁⟩ := IdSlot.bindOpt_eq_some hL
      obtain ⟨l₁', hl₁', hb₁'⟩ := IdSlot.bindOpt_eq_some hL'
      refine bindAll_sublist ?_ (h _ _ _ _ _ hl₁ hl₁') hb₁ hb₁'
      intro r₁ M M' hM hM'
      obtain ⟨l₂, hl₂, hb₂⟩ := IdSlot.bindOpt_eq_some hM
      obtain ⟨l₂', hl₂', hb₂'⟩ := IdSlot.bindOpt_eq_some hM'
      refine bindAll_sublist ?_ (h _ _ _ _ _ hl₂ hl₂') hb₂ hb₂'
      intro r₂ N N' hN hN'
      cases r₁ with
      | mk fv σ₁ =>
          cases fv with
          | lam x own body => exact h _ _ _ _ _ hN hN'
          | sym _ | fn _ | var _ | pvar _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
          | alt _ _ =>
              rw [← Option.some.inj hN, ← Option.some.inj hN']
  | letP p w b =>
      cases hl : letLam? p w with
      | some f =>
          rw [stepDir_bothSides_letLam d prog _ π σ hl] at hL'
          cases hf : σ f with
          | none =>
              rw [IdSlot.step_letP_some hl hf] at hL hL'
              exact h _ _ _ _ _ hL hL'
          | some g =>
              rw [IdSlot.step_letP_some_bound hl hf] at hL
              rw [← Option.some.inj hL]
              exact List.nil_sublist L'
      | none =>
          rw [stepDir_bothSides_letP d prog _ π σ hl] at hL'
          rw [IdSlot.step_letP_none hl] at hL
          obtain ⟨l₁, hl₁, hb₁⟩ := IdSlot.bindOpt_eq_some hL
          obtain ⟨l₁', hl₁', hb₁'⟩ := IdSlot.bindOpt_eq_some hL'
          exact bindAll_sublist (letCont_sub h π p b) (h _ _ _ _ _ hl₁ hl₁') hb₁ hb₁'
  | alt t₁ t₂ =>
      change step d prog r' π σ (.alt t₁ t₂) = some L' at hL'
      simp only [step] at hL hL'
      cases h₁ : r (π ++ [0]) σ t₁ with
      | none => rw [h₁] at hL; cases hL
      | some l =>
          cases h₂ : r (π ++ [1]) σ t₂ with
          | none => rw [h₁, h₂] at hL; cases hL
          | some m =>
              rw [h₁, h₂] at hL
              cases h₁' : r' (π ++ [0]) σ t₁ with
              | none => rw [h₁'] at hL'; cases hL'
              | some l' =>
                  cases h₂' : r' (π ++ [1]) σ t₂ with
                  | none => rw [h₁', h₂'] at hL'; cases hL'
                  | some m' =>
                      rw [h₁', h₂'] at hL'
                      rw [← Option.some.inj hL, ← Option.some.inj hL']
                      exact (h _ _ _ _ _ h₁ h₁').append (h _ _ _ _ _ h₂ h₂')
  | sym _ | var _ | pvar _ | lam _ _ _ | quote _ | pquote _ | ctx _ _ =>
      have e : L = L' := Option.some.inj (hL.symm.trans hL')
      rw [e]

/-- **Both sides only adds answers.**  At every fuel, path, store and term,
when the pattern-only run and the both-sides run are both defined, the
pattern-only bag of results is a sublist of the both-sides bag: the same
results, with their stores, in the same order, and possibly more between
them. -/
theorem run_sublist_runDir (d : Disc) (prog : S → Option (Tm S X)) :
    ∀ n, Runner.Sub (run d prog n) (runDir .bothSides d prog n)
  | 0 => fun _ _ _ _ _ h _ => by cases h
  | n + 1 => step_sub_stepDir d prog (run_sublist_runDir d prog n)

/-- The same on answers. -/
theorem answers_sublist_answersDir (d : Disc) (prog : S → Option (Tm S X)) (n : ℕ)
    (t : Tm S X) {bag bag' : List (Tm S X)} (h : answers d prog n t = some bag)
    (h' : answersDir .bothSides d prog n t = some bag') : bag.Sublist bag' := by
  unfold answers at h
  unfold answersDir at h'
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨L', hL', rfl⟩ := Option.map_eq_some_iff.1 h'
  exact (run_sublist_runDir d prog n _ _ _ _ _ hL hL').map _

/-! ## Which pairs are refined, and which are not -/

/-- **A value-side unbound name against a ground pattern term is refined** to
that term. -/
theorem matchT2_ground_var (σ : GStore S X) (g : GVal S X) (m : Nm X) (hm : σ m = Option.none) :
    matchT2 σ g.toTm (.var m) = refineStep σ (m, g) := by
  have e : matchT2 σ g.toTm (.var m) = exchange σ g.toTm (.var m) := by cases g <;> rfl
  have hv : act σ (.var m) = (.var m : Tm S X) := by rw [act_var, hm]
  rw [e]
  unfold exchange
  rw [hv, act_toTm, GVal.toTm_toGVal?]
  simp only [Tm.toGVal?, matchT, GVal.toTm_toGVal?]

/-- The same name on both sides matches and binds nothing. -/
theorem matchT2_var_self (σ : GStore S X) (n : Nm X) :
    matchT2 σ (.var n) (.var n) = some σ := by
  simp only [matchT2, if_true]

/-- **Two different names, both unbound, do not match.**  A store cell holds a
ground value (`GVal`), and a store name is not one (`GVal.toTm_ne_var`): no
ground binding relates the two names. -/
theorem matchT2_var_var_unbound (σ : GStore S X) {n m : Nm X} (hnm : n ≠ m)
    (hn : σ n = Option.none) (hm : σ m = Option.none) :
    matchT2 σ (.var n) (.var m) = Option.none := by
  have hvn : act σ (.var n) = (.var n : Tm S X) := by rw [act_var, hn]
  have hvm : act σ (.var m) = (.var m : Tm S X) := by rw [act_var, hm]
  simp only [matchT2, if_neg hnm, exchange, hvn, hvm, Tm.toGVal?]

/-- A pattern name that holds a value passes it to an unbound value-side name. -/
theorem matchT2_var_var_bound (σ : GStore S X) {n m : Nm X} (hnm : n ≠ m) {g : GVal S X}
    (hn : σ n = some g) (hm : σ m = Option.none) :
    matchT2 σ (.var n) (.var m) = refineStep σ (m, g) := by
  have hvn : act σ (.var n) = g.toTm := by rw [act_var, hn]
  have hvm : act σ (.var m) = (.var m : Tm S X) := by rw [act_var, hm]
  simp only [matchT2, if_neg hnm, exchange, hvn, hvm, Tm.toGVal?, GVal.toTm_toGVal?, matchT]

/-! ## A pattern that is one name -/

/-- **A stored value against a new value that is not ground**: under both sides
the new value is the pattern, read under the store, and the stored value is
what it is matched against.  So the unbound names of the new value are refined
from the stored value. -/
theorem matchT2_var_bound_nonground (σ : GStore S X) {f : Nm X} {g : GVal S X} {t : Tm S X}
    (hf : σ f = some g) (ht : (act σ t).toGVal? = Option.none) :
    matchT2 σ (.var f) t = matchT σ (act σ t) g.toTm := by
  have hvf : act σ (.var f) = g.toTm := by rw [act_var, hf]
  have e : matchT2 σ (.var f) t = exchange σ (.var f) t := by
    cases t with
    | var m =>
        by_cases hfm : f = m
        · subst hfm
          rw [hvf, GVal.toTm_toGVal?] at ht
          cases ht
        · simp only [matchT2, if_neg hfm]
    | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _
    | alt _ _ => rfl
  rw [e]
  unfold exchange
  rw [ht, hvf, GVal.toTm_toGVal?]

/-- **No stored value matches a lambda**, under both sides: a cell holds a
ground value, and a lambda is not one. -/
theorem matchT2_var_bound_lam (σ : GStore S X) {f : Nm X} {g : GVal S X} (hf : σ f = some g)
    (x : Nm X) (own : List X) (body : Tm S X) :
    matchT2 σ (.var f) (.lam x own body) = Option.none := by
  have ht : (act σ (.lam x own body : Tm S X)).toGVal? = Option.none := by
    simp only [act_lam, Tm.toGVal?]
  rw [matchT2_var_bound_nonground σ hf ht, act_lam]
  simp only [matchT]
  rw [if_neg]
  intro heq
  cases g <;> simp [GVal.toTm] at heq

/-- **Both sides, one name unbound in the store, a value that is not ground**:
the value is substituted for the name in the body, as under pattern-only. -/
theorem letCont2_var_unbound {rec : Runner S X} {π : Path} {f : Nm X} {b v : Tm S X}
    {τ : GStore S X} (hg : (act τ v).toGVal? = Option.none) (hf : τ f = Option.none) :
    letCont2 rec π (.var f) b (v, τ) = rec (π ++ [1]) τ (subst (Sub.single f v) Sub.none b) := by
  simp only [letCont2, hg, hf]

/-- **Both sides, one name that already holds a value**: whatever the new
value is, the `let` continues with the match of the two by `matchT2`. -/
theorem letCont2_var_bound {rec : Runner S X} {π : Path} {f : Nm X} {b v : Tm S X}
    {τ : GStore S X} {g : GVal S X} (hf : τ f = some g) :
    letCont2 rec π (.var f) b (v, τ) = letBody rec π b (matchT2 τ (.var f) (act τ v)) := by
  cases hg : (act τ v).toGVal? with
  | some g' =>
      simp only [letCont2, hg]
      rw [CloTable.toGVal?_toTm hg]
  | none => simp only [letCont2, hg, hf]

/-- **Both sides, a lambda written in place on a name that already holds a
value**: no answer. -/
theorem stepDir_bothSides_letLam_bound (d : Disc) (prog : S → Option (Tm S X)) (rec : Runner S X)
    (π : Path) (σ : GStore S X) {f : Nm X} {g : GVal S X} (hf : σ f = some g) (x : Nm X)
    (own : List X) (body b : Tm S X) :
    stepDir .bothSides d prog rec π σ (.letP (.var f) (.lam x own body) b) = some [] := by
  rw [stepDir_bothSides_letLam d prog rec π σ (f := f) rfl]
  exact IdSlot.step_letP_some_bound rfl hf

/-- **A pattern code parameter against a value hole**: the hole is refined to
`holeFill` of the parameter, which is `contextualVal` of the value binder aligned
with it. -/
theorem matchCode2In_pvar_hole (σ : GStore S X) (bound : List (Nm X)) (x m : Nm X)
    (hm : CodeId.hole m = true) :
    matchCode2In σ bound (.pvar x) (.var m) =
      (holeFill σ bound (.pvar x)).bind fun g => refineStep σ (m, g) := by
  simp only [matchCode2In, hm, if_true]
  cases holeFill σ bound (.pvar x : Tm S X) <;> rfl

/-- **Two different holes, both unbound, do not match.** -/
theorem matchCode2In_hole_hole_unbound (σ : GStore S X) (bound : List (Nm X)) {n m : Nm X}
    (hnm : n ≠ m) (hn : σ n = Option.none) (hm : σ m = Option.none)
    (hhn : CodeId.hole n = true) :
    matchCode2In σ bound (.var n) (.var m) = Option.none := by
  have hc : contextualVal bound (.var m : Tm S X) = Option.none := by
    simp [contextualVal, mentioned, mentionsBinder, Tm.toGVal?]
  simp only [matchCode2In, hhn, if_true, hc, hn, hm, if_neg hnm]
  split <;> rfl

/-! ## The direction axis, beside the three of `Config` -/

/-- **A configuration with its matching direction.**  `scope` holds the three
axes of `Config`, unchanged; `direction` is the fourth. -/
structure DirConfig where
  scope : Config
  direction : Direction
  deriving DecidableEq, Repr

/-- An existing configuration, read at pattern-only. -/
def Config.patternOnly (c : Config) : DirConfig := ⟨c, .patternOnly⟩

/-- A configuration, read with both sides. -/
def Config.bothSides (c : Config) : DirConfig := ⟨c, .bothSides⟩

/-- An existing configuration is a configuration at pattern-only. -/
instance : Coe Config DirConfig := ⟨Config.patternOnly⟩

/-- Answers of an authored query under a configuration and its direction. -/
def answersDirCfg (c : DirConfig) (prog : S → Option (Tm S (Slot X))) (n : ℕ) (t : Src S X) :
    Option (List (Tm S (Slot X))) :=
  answersDir c.direction c.scope.disc prog n (elabCfg c.scope [] t)

omit [CodeId X] in
/-- **The existing configurations, at pattern-only, answer as before.** -/
theorem answersDirCfg_patternOnly (c : Config) (prog : S → Option (Tm S (Slot X))) (n : ℕ)
    (t : Src S X) : answersDirCfg c.patternOnly prog n t = answersCfg c prog n t :=
  answersDir_patternOnly _ _ _ _

/-- The three-field spelling of a configuration is unchanged, and such a
configuration is read at pattern-only. -/
example : ((⟨.lexicalFresh, .perCall, .reference⟩ : Config) : DirConfig) = cfgLF.patternOnly := rfl

/-- The direction is a fourth axis: the same three fields, both sides. -/
example : (⟨⟨.mercury, .perCall, .reference⟩, .bothSides⟩ : DirConfig) = cfgM.bothSides := rfl

/-- The two directions of one configuration are two configurations. -/
example : cfgM.patternOnly ≠ cfgM.bothSides := by decide

end Mettapedia.GSLT.LanguageDef.TemplateScope
