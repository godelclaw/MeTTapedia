import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Contexts

/-!
# The repaired rule returns values on code-free terms

Under `evaluatedValues` the only answers that are not values are syntax
returned on purpose: the reply of a head declared with an `Atom` result, the
tuple of `collapse`, and the child extracted by `car-atom`. A stuck call is a
value whatever its arguments reduced to.

A term is *code-free* for a program when none of its symbols names such an
operation (`Program.codeName`), and a program is code-free when its
right-hand sides are. Then:

* `eval_codeFree` — every result of a code-free term is a code-free value;
  hence evaluation is a projection on it (`eval_kleisli_idempotent_codeFree`).
* `eval_alias_codeFree` — an alias has exactly the results of its target.
* `eval_plugAll_codeFree`, `unfold_preserves_eval_codeFree` — evaluation
  contexts and linear unfolding, as multisets, with no hypothesis on the
  argument beyond code-freeness.

Negative examples: `(ga (fr a))` with `ga` declared `(-> Atom Atom)` is not
code-free and returns code (`Probes.ga_result_is_code`); under
`rustEqualToInput` the code-free term `(g (fr (h)))` has 4 answers where its
unfolding `(wrap (fr (h)))` has 2 (`Probes.rust_violates_alias`).
-/

namespace Mettapedia.Languages.MeTTa.HE.EvaluatedValues

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Symbols and code names -/

namespace MAtom

mutual
/-- The symbols occurring in a term. -/
def symbols : MAtom → List String
  | symbol s => [s]
  | expr _ cs => symbolsList cs
  | _ => []

/-- `symbols` on a list. -/
def symbolsList : List MAtom → List String
  | [] => []
  | c :: cs => symbols c ++ symbolsList cs
end

@[simp] theorem symbolsList_eq (cs : List MAtom) : symbolsList cs = cs.flatMap symbols := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [symbolsList, ih]

@[simp] theorem symbols_symbol (s : String) : (symbol s).symbols = [s] := by simp [symbols]
@[simp] theorem symbols_var (x : String) : (var x).symbols = [] := by simp [symbols]
@[simp] theorem symbols_grounded (g : GroundedValue) : (grounded g).symbols = [] := by
  simp [symbols]
@[simp] theorem symbols_expr (m : Bool) (cs : List MAtom) :
    (expr m cs).symbols = cs.flatMap symbols := by simp [symbols]

@[simp] theorem symbols_markIf (a : Atom) (t : MAtom) : (t.markIf a).symbols = t.symbols := by
  unfold markIf
  split
  · cases t <;> simp [mark]
  · rfl

theorem symbols_subst (σ : Subst) :
    ∀ t : MAtom, ∀ s ∈ (t.subst σ).symbols,
      s ∈ t.symbols ∨ ∃ x u, σ.lookup x = some u ∧ s ∈ u.symbols := by
  intro t
  induction t using MAtom.induction with
  | var x =>
    intro s hs
    simp only [subst_var] at hs
    cases h : σ.lookup x with
    | none => simp [h] at hs
    | some u => rw [h] at hs; exact Or.inr ⟨x, u, h, hs⟩
  | expr m cs ih =>
    intro s hs
    simp only [subst_expr, symbols_expr, List.mem_flatMap, List.mem_map] at hs
    obtain ⟨_, ⟨c, hc, rfl⟩, hs⟩ := hs
    rcases ih c hc s hs with h | h
    · exact Or.inl (by simp only [symbols_expr, List.mem_flatMap]; exact ⟨c, hc, h⟩)
    · exact Or.inr h
  | symbol s' => intro s hs; simp only [subst_symbol] at hs; exact Or.inl hs
  | grounded g => intro s hs; simp at hs

end MAtom

/-- Names whose calls return syntax: `collapse`, `car-atom`, and heads
declared with an `Atom` result. -/
def Program.codeName (P : Program) (s : String) : Bool :=
  s == "collapse" || s == "car-atom" ||
    match P.decl? s with
    | some d => d.result == .atom
    | none => false

/-- No symbol of `t` is a code name. -/
def Program.CodeFreeT (P : Program) (t : MAtom) : Prop := ∀ s ∈ t.symbols, P.codeName s = false

/-- Every right-hand side is code-free. -/
def Program.CodeFree (P : Program) : Prop := ∀ eq ∈ P.equations, P.CodeFreeT (code eq.2)

/-- A code-free value. -/
def Program.Good (P : Program) (t : MAtom) : Prop := P.CodeFreeT t ∧ t.isValue = true

variable {P : Program}

theorem CodeFreeT.expr_iff {m : Bool} {cs : List MAtom} :
    P.CodeFreeT (.expr m cs) ↔ ∀ c ∈ cs, P.CodeFreeT c := by
  simp only [Program.CodeFreeT, MAtom.symbols_expr, List.mem_flatMap]
  exact ⟨fun h c hc s hs => h s ⟨c, hc, hs⟩, fun h s ⟨c, hc, hs⟩ => h c hc s hs⟩

theorem CodeFreeT.child {m : Bool} {cs : List MAtom} (h : P.CodeFreeT (.expr m cs)) {c : MAtom}
    (hc : c ∈ cs) : P.CodeFreeT c := CodeFreeT.expr_iff.mp h c hc

theorem CodeFreeT.markIf {t : MAtom} (a : Atom) (h : P.CodeFreeT t) : P.CodeFreeT (t.markIf a) := by
  intro s hs
  rw [MAtom.symbols_markIf] at hs
  exact h s hs

theorem CodeFreeT.subst {σ : Subst} {t : MAtom} (ht : P.CodeFreeT t)
    (hσ : ∀ x u, σ.lookup x = some u → P.CodeFreeT u) : P.CodeFreeT (t.subst σ) := by
  intro s hs
  rcases MAtom.symbols_subst σ t s hs with h | ⟨x, u, hu, h⟩
  · exact ht s h
  · exact hσ x u hu s h

theorem codeName_prim {f : String} {p : Prim} (hp : Prim.ofName f = some p)
    (hf : P.codeName f = false) : p ≠ .collapse ∧ p ≠ .carAtom := by
  unfold Prim.ofName at hp
  split at hp <;> simp only [Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    simp_all [Program.codeName]

theorem resultMode_codeFree {f : String} (hf : P.codeName f = false) :
    P.resultMode (.symbol f) = .evaluate := by
  simp only [Program.resultMode]
  cases hd : P.decl? f with
  | none => rfl
  | some d =>
    simp only [Program.codeName, hd, Bool.or_eq_false_iff] at hf
    show d.result = _
    cases hr : d.result with
    | evaluate => rfl
    | atom => simp [hr] at hf

theorem callResultMode_codeFree {vs : List MAtom} (h : ∀ v ∈ vs, P.CodeFreeT v) :
    P.callResultMode vs = .evaluate := by
  cases vs with
  | nil => rfl
  | cons c vs =>
    cases c with
    | symbol f =>
      exact resultMode_codeFree (h _ List.mem_cons_self f (by simp))
    | _ => rfl

/-- Pattern matching binds subterms, so bindings inherit any property closed
under taking children. -/
theorem matchAtom_bindings (p : MAtom → Prop)
    (hclosed : ∀ m cs, p (.expr m cs) → ∀ c ∈ cs, p c) :
    ∀ (q : Atom) {t : MAtom} {σ σ' : Subst}, matchAtom q t σ = some σ' →
      (∀ x u, σ.lookup x = some u → p u) → p t → ∀ x u, σ'.lookup x = some u → p u := by
  intro q
  induction q using atomInduction with
  | var y =>
    intro t σ σ' h hσ ht x u hx
    simp only [matchAtom] at h
    split at h
    · split at h
      · cases h; exact hσ x u hx
      · cases h
    · cases h
      rw [Subst.lookup_cons] at hx
      split at hx
      · cases hx; exact ht
      · exact hσ x u hx
  | symbol s =>
    intro t σ σ' h hσ _
    cases t <;> simp only [matchAtom] at h
    all_goals first | (split at h <;> cases h <;> exact hσ) | cases h
  | grounded g =>
    intro t σ σ' h hσ _
    cases t <;> simp only [matchAtom] at h
    all_goals first | (split at h <;> cases h <;> exact hσ) | cases h
  | expression ps ih =>
    intro t σ σ' h hσ ht
    cases t with
    | expr m ts =>
      simp only [matchAtom] at h
      have hts : ∀ c ∈ ts, p c := hclosed m ts ht
      clear ht
      induction ps generalizing ts σ with
      | nil =>
        cases ts with
        | nil => simp only [matchList, Option.some.injEq] at h; subst h; exact hσ
        | cons _ _ => simp [matchList] at h
      | cons q qs ihqs =>
        cases ts with
        | nil => simp [matchList] at h
        | cons t ts =>
          simp only [matchList] at h
          cases h₁ : matchAtom q t σ with
          | none => simp [h₁] at h
          | some σ₁ =>
            simp only [h₁] at h
            have hσ₁ := ih q List.mem_cons_self h₁ hσ (hts t List.mem_cons_self)
            have hts' : ∀ c ∈ ts, p c := fun c hc => hts c (List.mem_cons_of_mem _ hc)
            apply ihqs (fun r hr => ih r (List.mem_cons_of_mem _ hr)) <;> assumption
    | _ => simp [matchAtom] at h

theorem mem_replies {call r : MAtom} (h : r ∈ P.replies call) :
    ∃ eq ∈ P.equations, ∃ σ, matchAtom eq.1 call [] = some σ ∧ r = (code eq.2).subst σ := by
  simp only [Program.replies, List.mem_filterMap, Option.map_eq_some_iff] at h
  obtain ⟨eq, heq, σ, hσ, rfl⟩ := h
  exact ⟨eq, heq, σ, hσ, rfl⟩

theorem replies_codeFree (hP : P.CodeFree) {vs : List MAtom} (hvs : ∀ v ∈ vs, P.CodeFreeT v)
    {r : MAtom} (hr : r ∈ P.replies (.expr false vs)) : P.CodeFreeT r := by
  obtain ⟨eq, heq, σ, hσ, rfl⟩ := mem_replies hr
  refine CodeFreeT.subst (hP eq heq) ?_
  exact matchAtom_bindings P.CodeFreeT (fun _ _ h c hc => CodeFreeT.child h hc) eq.1 hσ
    (by simp) (CodeFreeT.expr_iff.mpr hvs)

/-! ## A unary invariant on demand trees -/

namespace Demand

variable {α β : Type}

/-- Every demand satisfies `Q`, every continuation of an `Ans`-reply
continues the invariant, and every answer satisfies `A`. -/
inductive All (Q : MAtom → Prop) (Ans : List MAtom → Prop) (A : α → Prop) : Demand α → Prop where
  | done {a : α} : A a → All Q Ans A (done a)
  | need {t : MAtom} {k : List MAtom → Demand α} :
      Q t → (∀ r, Ans r → All Q Ans A (k r)) → All Q Ans A (need t k)

variable {Q : MAtom → Prop} {Ans : List MAtom → Prop}

theorem All.run {A : α → Prop} {q : Demand α} (h : All Q Ans A q) {ev : Evaluator}
    (hev : ∀ t r, Q t → ev t = some r → Ans r) {a : α} (hrun : q.run ev = some a) : A a := by
  induction h with
  | done ha => simp only [run_done, Option.some.injEq] at hrun; subst hrun; exact ha
  | @need t k ht _ ih =>
    simp only [run_need] at hrun
    cases h' : ev t with
    | none => simp [h'] at hrun
    | some r =>
      simp only [h', Option.bind_some] at hrun
      exact ih r (hev t r ht h') hrun

theorem All.bind {A : α → Prop} {B : β → Prop} {q : Demand α} {f : α → Demand β}
    (h : All Q Ans A q) (hf : ∀ a, A a → All Q Ans B (f a)) : All Q Ans B (q.bind f) := by
  induction h with
  | done ha => exact hf _ ha
  | need ht _ ih => exact .need ht fun r hr => ih r hr

theorem All.map {A : α → Prop} {B : β → Prop} {q : Demand α} {f : α → β}
    (h : All Q Ans A q) (hf : ∀ a, A a → B (f a)) : All Q Ans B (q.map f) :=
  h.bind fun a ha => .done (hf a ha)

theorem All.forEach {p : β → Prop} {l : List α} {f : α → Demand (List β)}
    (hl : ∀ a ∈ l, All Q Ans (fun R => ∀ r ∈ R, p r) (f a)) :
    All Q Ans (fun R => ∀ r ∈ R, p r) (Demand.forEach l f) := by
  induction l with
  | nil => exact .done (by simp)
  | cons a l ih =>
    exact (hl a List.mem_cons_self).bind fun r hr =>
      (ih fun b hb => hl b (List.mem_cons_of_mem _ hb)).bind fun rs hrs =>
        .done fun x hx => (List.mem_append.mp hx).elim (hr x) (hrs x)

theorem All.traverse {B : β → Prop} {l : List α} {f : α → Demand β}
    (hl : ∀ a ∈ l, All Q Ans B (f a)) :
    All Q Ans (fun bs => ∀ b ∈ bs, B b) (Demand.traverse l f) := by
  induction l with
  | nil => exact .done (by simp)
  | cons a l ih =>
    exact (hl a List.mem_cons_self).bind fun b hb =>
      (ih fun c hc => hl c (List.mem_cons_of_mem _ hc)).bind fun bs hbs =>
        .done fun x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ hb) (hbs x)

end Demand

/-! ## The invariant -/

/-- The relation used throughout: demands are code-free, replies are lists of
code-free values. -/
abbrev GoodTree (P : Program) {α : Type} (A : α → Prop) : Demand α → Prop :=
  Demand.All P.CodeFreeT (fun R => ∀ r ∈ R, P.Good r) A

theorem mem_withModes {ms : List ParamMode} {cs : List MAtom} {p : ParamMode × MAtom}
    (h : p ∈ withModes ms cs) : p.2 ∈ cs := by
  induction cs generalizing ms with
  | nil => simp [withModes] at h
  | cons c cs ih =>
    cases ms with
    | nil =>
      simp only [withModes, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)
    | cons m ms =>
      simp only [withModes, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

theorem argDemand_good {p : ParamMode × MAtom} (hp : P.CodeFreeT p.2) :
    GoodTree P (fun R => ∀ r ∈ R, P.CodeFreeT r) (argDemand p) := by
  obtain ⟨mode, c⟩ := p
  cases mode with
  | value => exact .need hp fun R hR => .done fun r hr => (hR r hr).1
  | atom => exact .done (by simpa using hp)

theorem argsDemand_good {cs : List MAtom} (hcs : ∀ c ∈ cs, P.CodeFreeT c) :
    GoodTree P (fun rss => ∀ R ∈ rss, ∀ r ∈ R, P.CodeFreeT r) (P.argsDemand cs) :=
  Demand.All.traverse fun _ hp => argDemand_good (hcs _ (mem_withModes hp))

theorem needDone_good {t : MAtom} (ht : P.CodeFreeT t) :
    GoodTree P (fun R => ∀ r ∈ R, P.Good r) (.need t .done) :=
  .need ht fun _ hR => .done hR

theorem queryDemand_good (hP : P.CodeFree) {vs : List MAtom} (hvs : ∀ v ∈ vs, P.CodeFreeT v) :
    GoodTree P (fun R => ∀ r ∈ R, P.Good r) (P.queryDemand true vs) := by
  have hcall : P.Good (.expr true vs) := ⟨CodeFreeT.expr_iff.mpr hvs, rfl⟩
  unfold Program.queryDemand
  rw [callResultMode_codeFree hvs]
  split
  · exact .done (by simpa using hcall)
  · rename_i r rs hreps
    refine Demand.All.forEach fun r' hr' => ?_
    have hr'c : P.CodeFreeT r' := replies_codeFree hP hvs (by rw [hreps]; exact hr')
    simp only [returnDemand]
    split
    · exact .done (by simpa using hcall)
    · exact needDone_good hr'c

theorem callDemand_good (hP : P.CodeFree) {vs : List MAtom} (hvs : ∀ v ∈ vs, P.CodeFreeT v) :
    GoodTree P (fun R => ∀ r ∈ R, P.Good r) (P.callDemand true vs) := by
  have hq := queryDemand_good hP hvs
  match vs, hvs with
  | [], _ => exact hq
  | .symbol f :: args, hvs =>
    simp only [Program.callDemand]
    cases hp : Prim.ofName f with
    | none => exact hq
    | some p =>
      have hf : P.codeName f = false := hvs _ List.mem_cons_self f (by simp)
      obtain ⟨hpc, hpa⟩ := codeName_prim hp hf
      have hargs : ∀ a ∈ args, P.CodeFreeT a := fun a ha => hvs a (List.mem_cons_of_mem _ ha)
      cases p with
      | collapse => exact absurd rfl hpc
      | carAtom => exact absurd rfl hpa
      | superpose =>
        dsimp only
        match args, hargs with
        | [], _ => exact hq
        | [.expr _ es], hargs =>
          exact Demand.All.forEach fun e he =>
            needDone_good (CodeFreeT.child (hargs _ List.mem_cons_self) he)
        | [.symbol _], _ => exact hq
        | [.var _], _ => exact hq
        | [.grounded _], _ => exact hq
        | a :: _ :: _, _ => cases a <;> exact hq
      | unique =>
        dsimp only
        match args, hargs with
        | [], _ => exact hq
        | [a], hargs =>
          exact .need (hargs a List.mem_cons_self) fun R hR =>
            Demand.All.forEach fun r hr =>
              needDone_good (hR r ((dedupErase_sublist R).subset hr)).1
        | _ :: _ :: _, _ => exact hq
      | let_ =>
        dsimp only
        match args, hargs with
        | [], _ => exact hq
        | [_], _ => exact hq
        | [_, _], _ => exact hq
        | [pat, val, body], hargs =>
          simp only [primDemand]
          cases hm : matchAtom pat.erase val [] with
          | none => exact .done (by simp)
          | some σ =>
            refine needDone_good (CodeFreeT.subst (hargs body (by simp)) ?_)
            exact matchAtom_bindings P.CodeFreeT (fun _ _ h c hc => CodeFreeT.child h hc)
              pat.erase hm (by simp) (hargs val (by simp))
        | _ :: _ :: _ :: _ :: _, _ => exact hq
  | .var _ :: _, _ => exact hq
  | .grounded _ :: _, _ => exact hq
  | .expr _ _ :: _, _ => exact hq

theorem openStep_good (hP : P.CodeFree) {t : MAtom} (ht : P.CodeFreeT t) :
    GoodTree P (fun R => ∀ r ∈ R, P.Good r) (openStep .evaluatedValues P t) := by
  cases t with
  | expr m cs =>
    simp only [openStep]
    refine Demand.All.map (A := fun R => ∀ r ∈ R, P.Good r) ?_ fun R hR r hr => ?_
    · refine (argsDemand_good fun c hc => CodeFreeT.child ht hc).bind fun rss hrss => ?_
      refine Demand.All.forEach fun vs hvs => callDemand_good hP fun v hv => ?_
      obtain ⟨R, hR, hvR⟩ := forall₂_exists_left (forall₂_mem_of_mem_combos hvs) hv
      exact hrss R hR v hvR
    · obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
      exact ⟨CodeFreeT.markIf _ (hR r₀ hr₀).1, by
        rw [MAtom.isValue_markIf_iff]; exact Or.inr (hR r₀ hr₀).2⟩
  | symbol s => exact .done (by simpa [Program.Good, MAtom.isValue] using ht)
  | var x => exact .done (by simpa [Program.Good, MAtom.isValue] using ht)
  | grounded g => exact .done (by simpa [Program.Good, MAtom.isValue] using ht)

theorem evalFuel_good (hP : P.CodeFree) :
    ∀ n {t : MAtom} {R : List MAtom}, P.CodeFreeT t → evalFuel .evaluatedValues P n t = some R →
      ∀ r ∈ R, P.Good r := by
  intro n
  induction n with
  | zero => intro t R _ h; simp at h
  | succ n ih =>
    intro t R ht h
    rw [evalFuel_succ] at h
    by_cases hk : ReturnRule.evaluatedValues.keeps t = true
    · simp only [stepDemand, hk, ↓reduceIte, Demand.run_done, Option.some.injEq] at h
      subst h
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      refine ⟨ht, ?_⟩
      cases r with
      | expr m cs =>
        simp only [ReturnRule.keeps, ReturnRule.honorsMark, Bool.true_and] at hk
        exact hk
      | _ => rfl
    · rw [stepDemand_of_not_keeps P (by simpa using hk)] at h
      exact (openStep_good hP ht).run (fun t' r ht' hr => ih ht' hr) h

/-- **Code-free terms return code-free values** under `evaluatedValues`. -/
theorem eval_codeFree (hP : P.CodeFree) {t : MAtom} (ht : P.CodeFreeT t) {R : List MAtom}
    (h : eval .evaluatedValues P t = some R) : ∀ r ∈ R, r.isValue = true ∧ P.CodeFreeT r := by
  obtain ⟨n, hn⟩ := eval_eq_some_iff.mp h
  exact fun r hr => ⟨(evalFuel_good hP n ht hn r hr).2, (evalFuel_good hP n ht hn r hr).1⟩

theorem ValueResults.of_codeFree (hP : P.CodeFree) {t : MAtom} (ht : P.CodeFreeT t) :
    ValueResults .evaluatedValues P t :=
  fun _ h r hr => (eval_codeFree hP ht h r hr).1

/-- **Projection law** on code-free terms. -/
theorem eval_kleisli_idempotent_codeFree (hP : P.CodeFree) {t : MAtom} (ht : P.CodeFreeT t) :
    kbind (eval .evaluatedValues P t) (eval .evaluatedValues P) = eval .evaluatedValues P t :=
  eval_kleisli_idempotent rfl P t (ValueResults.of_codeFree hP ht)

/-- Running a good tree with the evaluator gives code-free values. -/
theorem GoodTree.run_eval (hP : P.CodeFree) {q : Demand (List MAtom)}
    (h : GoodTree P (fun R => ∀ r ∈ R, P.Good r) q) {R : List MAtom}
    (hR : q.run (eval .evaluatedValues P) = some R) : ∀ r ∈ R, P.Good r :=
  h.run (fun _ _ ht hr r hrr => let h' := eval_codeFree hP ht hr r hrr; ⟨h'.2, h'.1⟩) hR

theorem codeName_of_untyped {f : String} (hp : Prim.ofName f = none) (hd : P.decl? f = none) :
    P.codeName f = false := by
  have h1 : f ≠ "collapse" := by rintro rfl; simp [Prim.ofName] at hp
  have h2 : f ≠ "car-atom" := by rintro rfl; simp [Prim.ofName] at hp
  simp [Program.codeName, h1, h2, hd]

theorem optFlatMap_single {α β : Type} (x : α) (f : α → Option (List β)) :
    optFlatMap [x] f = f x := by
  cases h : f x <;> simp [h]

theorem map_markIf_option (a : Atom) {o : Option (List MAtom)}
    (h : ∀ R, o = some R → ∀ r ∈ R, r.isValue = true) : o.map (List.map (MAtom.markIf a)) = o := by
  cases o with
  | none => rfl
  | some R => simp [map_markIf_of_values a (h R rfl)]

theorem optFlatMap_good {l : List (List MAtom)} {f : List MAtom → Option (List MAtom)}
    (hf : ∀ vs ∈ l, ∀ R, f vs = some R → ∀ r ∈ R, P.Good r) :
    ∀ R, optFlatMap l f = some R → ∀ r ∈ R, P.Good r := by
  intro R h r hr
  obtain ⟨vs, hvs, Q, hQ, hrQ⟩ := mem_of_optFlatMap h hr
  exact hf vs hvs Q hQ r hrQ

theorem combos_good {es : List MAtom} {Rs : List (List MAtom)} (hP : P.CodeFree)
    (hes : ∀ e ∈ es, P.CodeFreeT e) (hRs : optTraverse es (eval .evaluatedValues P) = some Rs)
    {vs : List MAtom} (hvs : vs ∈ combos Rs) : ∀ v ∈ vs, P.Good v := by
  intro v hv
  obtain ⟨R, hR, hvR⟩ := forall₂_exists_left (forall₂_mem_of_mem_combos hvs) hv
  obtain ⟨e, he, hRe⟩ := forall₂_exists_right (forall₂_of_optTraverse hRs) hR
  have := eval_codeFree hP (hes e he) hRe v hvR
  exact ⟨this.2, this.1⟩

/-! ## Laws without argument hypotheses -/

/-- **Alias law on code-free terms.** If `g` is defined by the single equation
`(g x₁ … xₙ) = (h x₁ … xₙ)` in a code-free program, both heads untyped, then
`(g e⃗)` and `(h e⃗)` have exactly the same results, marks included, for
code-free arguments. -/
theorem eval_alias_codeFree (hPc : P.CodeFree) (hP : P.SymbolHeaded) {g h : String}
    {xs : List String} (hxs : xs.Nodup) (hg : Prim.ofName g = none) (hh : Prim.ofName h = none)
    (hdg : P.decl? g = none) (hdh : P.decl? h = none)
    (hdef : P.defn g =
      [(.expression (.symbol g :: xs.map .var), .expression (.symbol h :: xs.map .var))])
    (es : List MAtom) (hlen : es.length = xs.length) (hes : ∀ e ∈ es, P.CodeFreeT e) :
    eval .evaluatedValues P (.expr false (.symbol g :: es)) =
      eval .evaluatedValues P (.expr false (.symbol h :: es)) := by
  rw [eval_call_untyped .evaluatedValues P es (by simp) hg hdg,
    eval_call_untyped .evaluatedValues P es (by simp) hh hdh]
  simp only [ReturnRule.marksStuck]
  cases hRs : optTraverse es (eval .evaluatedValues P) with
  | none => rfl
  | some Rs =>
    simp only [Option.bind_some]
    have hq : ∀ vs ∈ combos Rs, ∀ R,
        (P.queryDemand true (.symbol h :: vs)).run (eval .evaluatedValues P) = some R →
        ∀ r ∈ R, P.Good r := by
      intro vs hvs R hR
      have hgood := combos_good hPc hes hRs hvs
      have hcf : ∀ v ∈ MAtom.symbol h :: vs, P.CodeFreeT v := by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · intro s hs
          simp only [MAtom.symbols_symbol, List.mem_singleton] at hs
          subst hs
          exact codeName_of_untyped hh hdh
        · exact (hgood v hv).1
      exact GoodTree.run_eval hPc (queryDemand_good hPc hcf) hR
    have hcongr : ∀ vs ∈ combos Rs,
        (P.queryDemand true (.symbol g :: vs)).run (eval .evaluatedValues P) =
          (P.queryDemand true (.symbol h :: vs)).run (eval .evaluatedValues P) := by
      intro vs hvs
      have hvals : ∀ v ∈ vs, v.isValue = true := fun v hv => (combos_good hPc hes hRs hvs v hv).2
      have hlenvs : xs.length = vs.length := by
        rw [← hlen, (forall₂_of_optTraverse hRs).length_eq,
          (forall₂_mem_of_mem_combos hvs).length_eq]
      obtain ⟨σ, hσ, hfa, -⟩ := matchList_vars hxs (σ₀ := []) hlenvs (by simp)
      have hrep : P.replies (.expr false (.symbol g :: vs)) = [.expr false (.symbol h :: vs)] := by
        rw [replies_eq_defn hP, hdef]
        simp only [List.filterMap_cons, List.filterMap_nil, matchAtom, matchList, ↓reduceIte]
        rw [show (xs.map Atom.var) = xs.map Atom.var from rfl]
        simp only [hσ, Option.map_some, code_expression, List.map_cons, code_symbol, List.map_map]
        have hsub := subst_vars hfa
        simp only [Function.comp_def] at hsub ⊢
        simp only [MAtom.subst_expr, List.map_cons, MAtom.subst_symbol, List.any_cons,
          MAtom.touched_symbol, Bool.false_or, Bool.false_and, hsub]
      have hne : ¬ (Atom.expression (Atom.symbol h :: vs.map MAtom.erase) = Atom.notReducible) := by
        simp [Atom.notReducible]
      have hL : (P.queryDemand true (.symbol g :: vs)).run (eval .evaluatedValues P) =
          eval .evaluatedValues P (.expr false (.symbol h :: vs)) := by
        simp only [Program.queryDemand, hrep, Program.callResultMode, Program.resultMode, hdg,
          returnDemand, MAtom.erase_expr, MAtom.erase_symbol, List.map_cons, hne, ↓reduceIte,
          Demand.run_forEach, optFlatMap_cons, optFlatMap_nil, Demand.run_need, Demand.run_done]
        cases eval .evaluatedValues P (.expr false (.symbol h :: vs)) <;> simp
      rw [hL, eval_call_untyped .evaluatedValues P vs (by simp) hh hdh,
        optTraverse_eq_some (g := fun v => [v]) fun v hv => eval_value rfl P (hvals v hv)]
      simp only [Option.bind_some, combos_singletons, optFlatMap_single, ReturnRule.marksStuck]
      exact map_markIf_option _ fun R hR r hr => (hq vs hvs R hR r hr).2
    rw [optFlatMap_congr hcongr]
    have hgood := optFlatMap_good hq
    rw [map_markIf_option _ fun R hR r hr => (hgood R hR r hr).2,
      map_markIf_option _ fun R hR r hr => (hgood R hR r hr).2]

/-- A frame whose head and siblings are code-free. -/
def Frame.CodeFree (P : Program) (fr : Frame) : Prop :=
  P.CodeFreeT fr.head ∧ (∀ c ∈ fr.left, P.CodeFreeT c) ∧ ∀ c ∈ fr.right, P.CodeFreeT c

theorem plugAll_codeFree {x : MAtom} (hx : P.CodeFreeT x) :
    ∀ C : List Frame, (∀ fr ∈ C, fr.CodeFree P) → P.CodeFreeT (plugAll C x)
  | [], _ => hx
  | fr :: C, hC => by
    obtain ⟨hh, hl, hr⟩ := hC fr List.mem_cons_self
    have hin := plugAll_codeFree hx C fun f hf => hC f (List.mem_cons_of_mem _ hf)
    refine CodeFreeT.expr_iff.mpr fun c hc => ?_
    simp only [List.mem_cons, List.mem_append] at hc
    rcases hc with rfl | hc | rfl | hc
    · exact hh
    · exact hl c hc
    · exact hin
    · exact hr c hc

theorem codeFree_frames {x : MAtom} :
    ∀ C : List Frame, P.CodeFreeT (plugAll C x) → ∀ fr ∈ C, fr.CodeFree P
  | [], _ => by simp
  | fr :: C, h => by
    have hch := CodeFreeT.expr_iff.mp h
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨hch f.head (by simp), fun c hc => hch c (by simp [hc]),
        fun c hc => hch c (by simp [hc])⟩
    · exact codeFree_frames C (hch (plugAll C x) (by simp)) f hf

theorem optTraverse_args_codeFree (hP : P.CodeFree) {ms : List ParamMode} {cs : List MAtom}
    (hcs : ∀ c ∈ cs, P.CodeFreeT c) {Rs : List (List MAtom)}
    (h : optTraverse (withModes ms cs) (fun p => (argDemand p).run (eval .evaluatedValues P)) =
      some Rs) : ∀ R ∈ Rs, ∀ r ∈ R, P.CodeFreeT r := by
  intro R hR r hr
  obtain ⟨p, hp, hpR⟩ := forall₂_exists_right (forall₂_of_optTraverse h) hR
  have hc := hcs _ (mem_withModes hp)
  obtain ⟨mode, c⟩ := p
  cases mode with
  | value =>
    rw [argDemand_value_run] at hpR
    exact (eval_codeFree hP hc hpR r hr).2
  | atom =>
    rw [argDemand_atom_run] at hpR
    cases hpR
    simp only [List.mem_singleton] at hr
    subst hr
    exact hc

/-- On code-free inputs a frame's marking acts as the identity. -/
theorem Frame.continue_markIf (hP : P.CodeFree) {fr : Frame} (hfr : fr.CodeFree P)
    {RX : List MAtom} (hRX : ∀ r ∈ RX, P.CodeFreeT r) (a : Atom) :
    fr.continue .evaluatedValues P (MAtom.markIf a) RX = fr.continue .evaluatedValues P id RX := by
  obtain ⟨hh, hl, hr⟩ := hfr
  unfold Frame.continue
  cases h₁ : optTraverse (withModes (.value :: P.paramModes fr.head) (fr.head :: fr.left))
      (fun p => (argDemand p).run (eval .evaluatedValues P)) with
  | none => rfl
  | some Rs₁ =>
    cases h₂ : optTraverse (withModes ((P.paramModes fr.head).drop fr.left.length).tail fr.right)
        (fun p => (argDemand p).run (eval .evaluatedValues P)) with
    | none => rfl
    | some Rs₂ =>
      simp only [Option.bind_some]
      have hs₁ := optTraverse_args_codeFree hP
        (fun c hc => (List.mem_cons.mp hc).elim (fun h => h ▸ hh) (hl c)) h₁
      have hs₂ := optTraverse_args_codeFree hP hr h₂
      have hgood := optFlatMap_good (P := P)
        (l := combos (Rs₁ ++ RX :: Rs₂))
        (f := fun vs => (P.callDemand ReturnRule.evaluatedValues.marksStuck vs).run
          (eval .evaluatedValues P)) fun vs hvs R hR => by
          refine GoodTree.run_eval hP (callDemand_good hP fun v hv => ?_) hR
          obtain ⟨L, hL, hvL⟩ := forall₂_exists_left (forall₂_mem_of_mem_combos hvs) hv
          simp only [List.mem_append, List.mem_cons] at hL
          rcases hL with hL | rfl | hL
          · exact hs₁ L hL v hvL
          · exact hRX v hvL
          · exact hs₂ L hL v hvL
      cases hR : optFlatMap (combos (Rs₁ ++ RX :: Rs₂))
          (fun vs => (P.callDemand ReturnRule.evaluatedValues.marksStuck vs).run
            (eval .evaluatedValues P)) with
      | none => rfl
      | some R =>
        simp only [Option.map_some, List.map_id_fun, id_eq, Option.some.injEq]
        exact map_markIf_of_values a fun r hr => (hgood R hR r hr).2

/-- **Evaluation contexts on code-free terms.** Under `evaluatedValues`, when
`C[e]` converges its results are, as a multiset, those of `C[v]` over the
results `v` of `e`, for a code-free program, context and argument. -/
theorem eval_plugAll_codeFree (hP : P.CodeFree) :
    ∀ (C : List Frame), (∀ fr ∈ C, fr.Strict P) → (∀ fr ∈ C, fr.CodeFree P) →
      ∀ (e : MAtom), P.CodeFreeT e → ∀ {R : List MAtom},
      eval .evaluatedValues P (plugAll C e) = some R →
      ∃ R', kbind (eval .evaluatedValues P e) (fun v => eval .evaluatedValues P (plugAll C v)) =
        some R' ∧ (R : Multiset MAtom) = R' := by
  intro C
  induction C with
  | nil =>
    intro _ _ e he R h
    refine ⟨R, ?_, rfl⟩
    simp only [plugAll] at h ⊢
    rw [← h]
    exact eval_kleisli_idempotent_codeFree hP he
  | cons fr C ih =>
    intro hC hCf e he R h
    have hfr := hC fr List.mem_cons_self
    have hfrc := hCf fr List.mem_cons_self
    have hCf' : ∀ f ∈ C, f.CodeFree P := fun f hf => hCf f (List.mem_cons_of_mem _ hf)
    simp only [plugAll] at h
    rw [frame_eval _ P hfr] at h
    obtain ⟨RX, hX, hcont⟩ := Option.bind_eq_some_iff.mp h
    have hXc : P.CodeFreeT (plugAll C e) := plugAll_codeFree he C hCf'
    rw [Frame.continue_markIf hP hfrc (fun r hr => (eval_codeFree hP hXc hX r hr).2)] at hcont
    obtain ⟨R'', hR'', hXR''⟩ := ih (fun f hf => hC f (List.mem_cons_of_mem _ hf)) hCf' e he hX
    obtain ⟨Re, hRe', hRe⟩ := Option.bind_eq_some_iff.mp hR''
    obtain ⟨hall, rfl⟩ := optFlatMap_eq_some_iff.mp hRe
    obtain ⟨R₂, hR₂, hRR₂⟩ := fr.continue_perm _ hXR'' hcont
    obtain ⟨R₃, hR₃, hR₂₃⟩ := fr.continue_flatMap _ Re _ hR₂
    refine ⟨R₃, ?_, hRR₂.trans hR₂₃⟩
    simp only [kbind, hRe', Option.bind_some, plugAll]
    rw [← hR₃]
    apply optFlatMap_congr
    intro v hv
    rw [frame_eval _ P hfr]
    obtain ⟨Rv, hRv⟩ := Option.isSome_iff_exists.mp (hall v hv)
    have hvc : P.CodeFreeT v := (eval_codeFree hP he hRe' v hv).2
    have hpc : P.CodeFreeT (plugAll C v) := plugAll_codeFree hvc C hCf'
    rw [hRv, Option.bind_some,
      Frame.continue_markIf hP hfrc (fun r hr => (eval_codeFree hP hpc hRv r hr).2)]
    simp

/-- **Linear unfolding on code-free terms.** If `g` is defined by one equation
`(g $x) = rhs` of a code-free program, with `rhs = C[$x]` for a strict context
not mentioning `$x` elsewhere, then for a code-free argument `e`, when the
unfolded body `rhs[$x := e]` converges, `(g e)` converges to the same
multiset of results. -/
theorem unfold_preserves_eval_codeFree (hPc : P.CodeFree) (hP : P.SymbolHeaded) {g x : String}
    {rhs : Atom} (C : List Frame) (hC : ∀ fr ∈ C, fr.Strict P) (hne : C ≠ [])
    (hav : ∀ fr ∈ C, fr.Avoids x) (hrhs : code rhs = plugAll C (.var x))
    (hg : Prim.ofName g = none) (hdg : P.decl? g = none)
    (hdef : P.defn g = [(.expression [.symbol g, .var x], rhs)]) (e : MAtom) (he : P.CodeFreeT e)
    {R : List MAtom} (h : eval .evaluatedValues P ((code rhs).subst [(x, e)]) = some R) :
    ∃ R', eval .evaluatedValues P (.expr false [.symbol g, e]) = some R' ∧
      (R : Multiset MAtom) = R' := by
  have hmem : (Atom.expression [.symbol g, .var x], rhs) ∈ P.equations := by
    have : (Atom.expression [.symbol g, .var x], rhs) ∈ P.defn g := by rw [hdef]; simp
    exact (List.mem_filter.mp this).1
  have hrc : P.CodeFreeT (plugAll C (.var x)) := hrhs ▸ hPc _ hmem
  have hCf := codeFree_frames C hrc
  rw [hrhs, plugAll_subst x e C hav] at h
  obtain ⟨R'', hR'', hRR''⟩ := eval_plugAll_codeFree hPc C hC hCf e he h
  refine ⟨R'', ?_, hRR''⟩
  rw [eval_unfold_call .evaluatedValues hP C hne hav hrhs hg hdg hdef e, ← hR'']
  cases hRe : eval .evaluatedValues P e with
  | none => rfl
  | some Re =>
    simp only [kbind, Option.bind_some]
    apply optFlatMap_congr
    intro v hv
    have hvc : P.CodeFreeT v := (eval_codeFree hPc he hRe v hv).2
    exact map_markIf_option _ fun Rv hRv r hr =>
      (eval_codeFree hPc (plugAll_codeFree hvc C hCf) hRv r hr).1

end Mettapedia.Languages.MeTTa.HE.EvaluatedValues
