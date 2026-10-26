import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Closures

/-!
# Specializing a relation for the shape of a closure

A relation `f` whose first parameter is a closure of `g` can be specialized
for the shape `(partial g (list h₁ … hₘ))` instead of for each closure value:
the lifted relation `fs` takes the captured values as its first `m`
parameters.  Its equations are those of `f` with

* an application `($k e…)` of the closure parameter `k` made the call
  `(g h₁ … hₘ e…)`,
* a recursive call `(f $k e…)` that passes the closure on made the call
  `(fs h₁ … hₘ e…)`, and
* any other occurrence of `$k` made the closure again,
  `(partial g (list h₁ … hₘ))`.

One lifted relation serves every closure of the shape: `withLifted` depends on
the shape, never on captured values.  Within one program that holds both
relations, the transfer of a call `(f (partial g (list cs)) vs)` to
`(fs cs vs)` commutes with evaluation exactly: transferring and then
evaluating gives what evaluating gives (`apply_lifted_eq`, `apply_source_eq`),
for every `cs`.  The term-level statements are `eval_refines_lifted` and
`lifted_refines_eval`.

The square closes because nothing inspects the closure (`Lifts`, `Clean`):
every equation of `f` reads it with a variable, and no `let` binds that
variable again.  An equation that matched the closure against a pattern
observes the captured values, and a `let` that binds the parameter again makes
its later occurrences another value; in both cases the two calls answer
differently (`Controls.inspection_breaks_lifting`,
`Controls.rebinding_breaks_lifting`).

Fuel bounds evaluation depth.  Rebuilding an escaping closure takes two more
levels than reading the variable, so the lifted side may need two more units;
the source side reads the closure variable where the lifted call reads
nothing, so it may need one more.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.ClosureSpecialization

open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.DeterministicEquations.Closures

/-- A lifting: the source relation, its lifted relation, the closure's symbol
and the variables that stand for the captured values. -/
structure Lifting where
  source : String
  lifted : String
  callee : String
  holes : List String

variable (L : Lifting)

/-- The closure rebuilt from the hole variables. -/
def rebuild : Term :=
  .expr [.sym "partial", .sym L.callee, .list (L.holes.map .var)]

/-- An occurrence of a variable: the closure parameter is rebuilt. -/
def liftVar (k x : String) : Term :=
  if x = k then rebuild L else .var x

mutual

/-- The lifting of a term for the closure parameter `k`. -/
def liftTerm (k : String) : Term → Term
  | .var x => liftVar L k x
  | .sym s => .sym s
  | .lit s => .lit s
  | .list items => .list (liftTerms k items)
  | .expr (.var x :: args) =>
    if x = k then .expr (.sym L.callee :: (L.holes.map .var ++ liftTerms k args))
    else .expr (.var x :: liftTerms k args)
  | .expr (.sym f :: .var x :: rest) =>
    if f = L.source ∧ x = k then
      .expr (.sym L.lifted :: (L.holes.map .var ++ liftTerms k rest))
    else .expr (.sym f :: liftVar L k x :: liftTerms k rest)
  | .expr items => .expr (liftTerms k items)

/-- The lifting of a list of terms. -/
def liftTerms (k : String) : List Term → List Term
  | [] => []
  | t :: ts => liftTerm k t :: liftTerms k ts

end

/-! ## Shapes of evaluation steps -/

/-- The special forms the evaluator reads before calls. -/
def Ordinary (f : String) : Prop := f ≠ "let" ∧ f ≠ "metta-nullary"

theorem evalStep_call {ev : Env → Term → Outcome}
    {call : String → List Term → Outcome} {env : Env} {f : String}
    (hf : Ordinary f) (args : List Term) :
    Closures.evalStep ev call env (.expr (.sym f :: args)) =
      match evalItemsWith ev env args with
      | .values vs => call f vs
      | .stop o => o := by
  obtain ⟨hlet, hnull⟩ := hf
  unfold Closures.evalStep
  split <;> (try simp_all) <;> (try rfl)
  rename_i items _ hnot heq
  exact absurd heq.symm (hnot f args)

theorem evalStep_dynamic {ev : Env → Term → Outcome}
    {call : String → List Term → Outcome} {env : Env} {h : Term}
    (hh : ∀ s, h ≠ .sym s) (args : List Term) :
    Closures.evalStep ev call env (.expr (h :: args)) =
      match evalItemsWith ev env (h :: args) with
      | .values vs => applyValues call vs
      | .stop o => o := by
  unfold Closures.evalStep
  split <;> (try simp_all)
  all_goals rfl

/-! ## Shapes of the lifting -/

theorem liftTerms_nil (k : String) : liftTerms L k [] = [] := rfl

theorem liftTerms_cons (k : String) (t : Term) (ts : List Term) :
    liftTerms L k (t :: ts) = liftTerm L k t :: liftTerms L k ts := rfl

theorem liftTerm_apply (k : String) (args : List Term) :
    liftTerm L k (.expr (.var k :: args)) =
      .expr (.sym L.callee :: (L.holes.map .var ++ liftTerms L k args)) := by
  unfold liftTerm
  rw [if_pos rfl]

theorem liftTerm_forward (k : String) (rest : List Term) :
    liftTerm L k (.expr (.sym L.source :: .var k :: rest)) =
      .expr (.sym L.lifted :: (L.holes.map .var ++ liftTerms L k rest)) := by
  unfold liftTerm
  rw [if_pos ⟨rfl, rfl⟩]

theorem liftTerm_var_head (k x : String) (hx : x ≠ k) (args : List Term) :
    liftTerm L k (.expr (.var x :: args)) =
      .expr (.var x :: liftTerms L k args) := by
  unfold liftTerm
  rw [if_neg hx]

/-- A call of a symbol that is not the source relation passing the closure
parameter on keeps its head and lifts its arguments. -/
theorem liftTerm_call (k f : String) (args : List Term)
    (h : ¬ (f = L.source ∧ args.head? = some (.var k))) :
    liftTerm L k (.expr (.sym f :: args)) =
      .expr (.sym f :: liftTerms L k args) := by
  rcases args with _ | ⟨a, rest⟩
  · rfl
  · cases a with
    | var x =>
      have hx : ¬ (f = L.source ∧ x = k) := by
        rintro ⟨hf, rfl⟩
        exact h ⟨hf, rfl⟩
      unfold liftTerm
      rw [if_neg hx]
      rfl
    | sym _ => rfl
    | lit _ => rfl
    | list _ => rfl
    | expr _ => rfl

/-- A head that is neither a symbol nor a variable is lifted in place. -/
theorem liftTerm_other_head (k : String) (h : Term) (hs : ∀ s, h ≠ .sym s)
    (hv : ∀ x, h ≠ .var x) (args : List Term) :
    liftTerm L k (.expr (h :: args)) =
      .expr (liftTerm L k h :: liftTerms L k args) := by
  cases h with
  | var x => exact absurd rfl (hv x)
  | sym s => exact absurd rfl (hs s)
  | lit _ => rfl
  | list _ => rfl
  | expr _ => rfl

/-- The lifting of an expression is an expression. -/
theorem liftTerm_expr (k : String) (items : List Term) :
    ∃ items', liftTerm L k (.expr items) = .expr items' := by
  rcases items with _ | ⟨a, rest⟩
  · exact ⟨[], rfl⟩
  · cases a with
    | var x =>
      by_cases hx : x = k
      · exact ⟨_, by subst hx; exact liftTerm_apply L x rest⟩
      · exact ⟨_, liftTerm_var_head L k x hx rest⟩
    | sym f =>
      rcases rest with _ | ⟨b, rest⟩
      · exact ⟨_, rfl⟩
      · cases b with
        | var x =>
          by_cases hfx : f = L.source ∧ x = k
          · refine ⟨.sym L.lifted :: (L.holes.map .var ++ liftTerms L k rest), ?_⟩
            unfold liftTerm
            rw [if_pos hfx]
          · refine ⟨.sym f :: liftVar L k x :: liftTerms L k rest, ?_⟩
            unfold liftTerm
            rw [if_neg hfx]
        | sym _ => exact ⟨_, rfl⟩
        | lit _ => exact ⟨_, rfl⟩
        | list _ => exact ⟨_, rfl⟩
        | expr _ => exact ⟨_, rfl⟩
    | lit _ => exact ⟨_, rfl⟩
    | list _ => exact ⟨_, rfl⟩
    | expr _ => exact ⟨_, rfl⟩

/-- Lifting keeps a term that is not a symbol from becoming one. -/
theorem liftTerm_ne_sym (k : String) {t : Term} (ht : ∀ s, t ≠ .sym s) :
    ∀ s, liftTerm L k t ≠ .sym s := by
  intro s
  cases t with
  | var x =>
    show liftVar L k x ≠ .sym s
    unfold liftVar rebuild
    split <;> simp
  | sym s' => exact absurd rfl (ht s')
  | lit _ => exact fun h => Term.noConfusion h
  | list _ => exact fun h => Term.noConfusion h
  | expr items =>
    obtain ⟨items', h⟩ := liftTerm_expr L k items
    rw [h]
    exact fun h => Term.noConfusion h


/-- Lifting keeps a term that is not a variable from becoming one. -/
theorem liftTerm_ne_var (k : String) {t : Term} (ht : ∀ x, t ≠ .var x) :
    ∀ x, liftTerm L k t ≠ .var x := by
  intro x
  cases t with
  | var y => exact absurd rfl (ht y)
  | sym _ => exact fun h => Term.noConfusion h
  | lit _ => exact fun h => Term.noConfusion h
  | list _ => exact fun h => Term.noConfusion h
  | expr items =>
    obtain ⟨items', h⟩ := liftTerm_expr L k items
    rw [h]
    exact fun h => Term.noConfusion h

/-! ## Terms the lifting is sound on -/

/-- The special forms of an expression are well formed, and none binds the
closure parameter `k`: a `let` binds a variable other than `k`, and
`metta-nullary` names a symbol. -/
def SpecialOk (k : String) (items : List Term) : Prop :=
  (items.head? = some (.sym "let") →
    ∃ x e b, items = [.sym "let", .var x, e, b] ∧ x ≠ k) ∧
  (items.head? = some (.sym "metta-nullary") →
    ∃ s, items = [.sym "metta-nullary", .sym s])

/-- A term the lifting for `k` is sound on: it mentions no hole variable and
its special forms are well formed without binding `k`. -/
inductive Clean (k : String) : Term → Prop
  | var {x : String} : x ∉ L.holes → Clean k (.var x)
  | sym (s : String) : Clean k (.sym s)
  | lit (s : String) : Clean k (.lit s)
  | list {items : List Term} : (∀ t ∈ items, Clean k t) → Clean k (.list items)
  | expr {items : List Term} : SpecialOk k items →
      (∀ t ∈ items, Clean k t) → Clean k (.expr items)

/-! ## The environments of the two sides -/

theorem Env.lookup_cons (x y : String) (v : Term) (env : Env) :
    Env.lookup ((x, v) :: env) y = if x = y then some v else env.lookup y := by
  unfold Env.lookup
  by_cases h : x = y
  · subst h
    simp
  · simp [h]

theorem Env.lookup_append_of_lookup (env₁ env₂ : Env) (y : String) (v : Term)
    (h : env₁.lookup y = some v) : (env₁ ++ env₂).lookup y = some v := by
  unfold Env.lookup at *
  rw [List.find?_append]
  cases hf : List.find? (fun b => b.1 == y) env₁ with
  | none => rw [hf] at h; simp at h
  | some b => rw [hf] at h; simpa using h

theorem Env.lookup_append_of_none (env₁ env₂ : Env) (y : String)
    (h : env₁.lookup y = none) : (env₁ ++ env₂).lookup y = env₂.lookup y := by
  unfold Env.lookup at *
  rw [List.find?_append]
  cases hf : List.find? (fun b => b.1 == y) env₁ with
  | none => simp
  | some b => rw [hf] at h; simp at h

/-- The environments of a source call and its lifted call: the source side
binds `k` to the closure, the lifted side binds each hole to its captured
value, and the two agree on every other variable. -/
structure Rel (k : String) (cs : List Term) (env env' : Env) : Prop where
  closure : env.lookup k = some (closure L.callee cs)
  holes : L.holes.map env'.lookup = cs.map some
  others : ∀ x, x ≠ k → x ∉ L.holes → env'.lookup x = env.lookup x

theorem Rel.extend {k : String} {cs : List Term} {env env' : Env}
    (h : Rel L k cs env env') {x : String} (hk : x ≠ k) (hh : x ∉ L.holes)
    (v : Term) : Rel L k cs ((x, v) :: env) ((x, v) :: env') where
  closure := by rw [Env.lookup_cons, if_neg hk]; exact h.closure
  holes := by
    rw [← h.holes]
    apply List.map_congr_left
    intro y hy
    have hxy : x ≠ y := by
      rintro rfl
      exact hh hy
    rw [Env.lookup_cons, if_neg hxy]
  others := by
    intro y hyk hyh
    rw [Env.lookup_cons, Env.lookup_cons]
    split
    · rfl
    · exact h.others y hyk hyh

/-! ## Evaluating the holes and the rebuilt closure -/

theorem evalItemsWith_append_values {ev : Env → Term → Outcome} {env : Env}
    {xs : List Term} {us : List Term} (hx : evalItemsWith ev env xs = .values us)
    (ys : List Term) :
    evalItemsWith ev env (xs ++ ys) =
      match evalItemsWith ev env ys with
      | .values ws => .values (us ++ ws)
      | .stop o => .stop o := by
  induction xs generalizing us with
  | nil =>
    simp only [evalItemsWith] at hx
    cases hx
    simp only [List.nil_append]
    cases evalItemsWith ev env ys <;> rfl
  | cons x xs ih =>
    simp only [evalItemsWith] at hx
    split at hx
    · rename_i v hv
      split at hx
      · rename_i vs hvs
        cases hx
        simp only [List.cons_append, evalItemsWith, hv, ih hvs]
        cases evalItemsWith ev env ys <;> rfl
      · cases hx
    · cases hx

theorem evalItems_holes (P : Program) (H : Host) {k : String} {cs : List Term}
    {env env' : Env} (hr : Rel L k cs env env') (n : Nat) :
    evalItemsWith (Closures.eval P H (n + 1)) env' (L.holes.map .var) =
      .values cs := by
  have key : ∀ (hs : List String) (cs : List Term),
      hs.map env'.lookup = cs.map some →
      evalItemsWith (Closures.eval P H (n + 1)) env' (hs.map .var) = .values cs := by
    intro hs
    induction hs with
    | nil =>
      intro cs h
      cases cs with
      | nil => rfl
      | cons _ _ => simp at h
    | cons x xs ih =>
      intro cs h
      cases cs with
      | nil => simp at h
      | cons c cs =>
        simp only [List.map_cons, List.cons.injEq] at h
        have hv : Closures.eval P H (n + 1) env' (.var x) = .value c := by
          show Closures.evalStep _ _ env' (.var x) = _
          simp only [Closures.evalStep, h.1]
        simp only [List.map_cons, evalItemsWith, hv, ih cs h.2]
  exact key L.holes cs hr.holes

theorem eval_rebuild (P : Program) (H : Host) (hp : P.defines "partial" = false)
    (hh : ∀ vs, H.primitive "partial" vs = .unhandled) {k : String}
    {cs : List Term} {env env' : Env} (hr : Rel L k cs env env') (n : Nat) :
    Closures.eval P H (n + 3) env' (rebuild L) = .value (closure L.callee cs) := by
  have hord : Ordinary "partial" := by
    constructor <;> decide
  have hdef : P.definesAt "partial" 2 = false := by
    unfold Program.definesAt
    unfold Program.defines at hp
    simp only [List.any_eq_false, Bool.and_eq_true, beq_iff_eq] at hp ⊢
    intro e he h
    exact hp e he h.1
  show Closures.evalStep _ _ env' (.expr (.sym "partial" ::
    [.sym L.callee, .list (L.holes.map .var)])) = _
  rw [evalStep_call hord]
  have hlist : Closures.eval P H (n + 2) env' (.list (L.holes.map .var)) =
      .value (.list cs) := by
    show Closures.evalStep _ _ env' _ = _
    simp only [Closures.evalStep, evalItems_holes L P H hr n]
  have hsym : Closures.eval P H (n + 2) env' (.sym L.callee) =
      .value (.sym L.callee) := rfl
  have hitems : evalItemsWith (Closures.eval P H (n + 2)) env'
      [.sym L.callee, .list (L.holes.map .var)] =
      .values [.sym L.callee, .list cs] := by
    simp only [evalItemsWith, hsym, hlist]
  rw [hitems]
  show applyWith P H _ "partial" [.sym L.callee, .list cs] = _
  unfold applyWith
  rw [if_neg (by simp [hdef]), if_neg (by simp [hp]), hh]
  rfl


/-- Items whose evaluations refine each other under two maps evaluate to the
same values, unless the first side runs out of fuel. -/
theorem evalItemsWith_rel {ev ev' : Env → Term → Outcome} {env env' : Env}
    (a b : Term → Term) :
    ∀ items : List Term, (∀ t ∈ items, Refines (ev env (a t)) (ev' env' (b t))) →
      evalItemsWith ev env (items.map a) = .stop .exhausted ∨
      evalItemsWith ev env (items.map a) = evalItemsWith ev' env' (items.map b)
  | [], _ => Or.inr rfl
  | t :: ts, h => by
    simp only [evalItemsWith, List.map_cons]
    rcases h t (by simp) with ht | ht
    · rw [ht]
      exact Or.inl rfl
    · rw [← ht]
      split
      · rcases evalItemsWith_rel a b ts
            (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) with hs | hs
        · rw [hs]
          exact Or.inl rfl
        · rw [hs]
          exact Or.inr rfl
      · exact Or.inr rfl

theorem liftTerms_eq_map (k : String) :
    ∀ ts, liftTerms L k ts = ts.map (liftTerm L k)
  | [] => rfl
  | t :: ts => by rw [liftTerms_cons, liftTerms_eq_map k ts, List.map_cons]

/-! ## The lifted program -/

/-- The lifting of a source equation `f $k rest = body`. -/
def liftEquation (e : Equation) : Equation :=
  match e.params with
  | .var k :: rest =>
    ⟨e.name, L.lifted, L.holes.map .var ++ rest, liftTerm L k e.body⟩
  | _ => e

/-- The lifted relation's equations: the source relation's, in order. -/
def liftedEquations (P : Program) : Program :=
  (P.filter (fun e => e.head = L.source)).map (liftEquation L)

/-- A program with its lifted relation. -/
def withLifted (P : Program) : Program :=
  P ++ liftedEquations L P

/-- What the lifting asks of the program and the host: the relations are
distinct ordinary symbols; every equation of the source relation reads the
closure with a variable, and its body is clean for that variable; and the
closure can be rebuilt, since nothing defines or handles `partial`. -/
structure Lifts (P : Program) (H : Host) : Prop where
  source : Ordinary L.source
  lifted : Ordinary L.lifted
  callee : Ordinary L.callee
  source_ne_lifted : L.source ≠ L.lifted
  lifted_ne_partial : L.lifted ≠ "partial"
  holes_nodup : L.holes.Nodup
  fresh : ∀ e ∈ P, e.head ≠ L.lifted
  defined : P.defines L.source = true
  equations : ∀ e ∈ P, e.head = L.source →
    ∃ k rest, e.params = .var k :: rest ∧ Clean L k e.body
  partial_free : P.defines "partial" = false
  partial_host : ∀ vs, H.primitive "partial" vs = .unhandled

/-! ## Matching the two sides -/

theorem matchTerms_vars_append (ps vs : List Term) :
    ∀ (hs : List String) (cs : List Term), hs.length = cs.length →
      matchTerms (hs.map .var ++ ps) (cs ++ vs) =
        (matchTerms ps vs).map (hs.zip cs ++ ·)
  | [], [], _ => by simp
  | h :: hs, c :: cs, hl => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [List.map_cons, List.cons_append, matchTerms, matchTerm,
      matchTerms_vars_append ps vs hs cs hl, List.zip_cons_cons]
    cases matchTerms ps vs <;> rfl
  | [], _ :: _, hl => by simp at hl
  | _ :: _, [], hl => by simp at hl

theorem matchTerms_var_cons (k : String) (c : Term) (ps vs : List Term) :
    matchTerms (.var k :: ps) (c :: vs) =
      (matchTerms ps vs).map ((k, c) :: ·) := by
  simp only [matchTerms, matchTerm]
  cases matchTerms ps vs <;> rfl

theorem lookup_zip_holes :
    ∀ (hs : List String) (cs : List Term), hs.Nodup → hs.length = cs.length →
      hs.map (Env.lookup (hs.zip cs)) = cs.map some
  | [], [], _, _ => rfl
  | h :: hs, c :: cs, hn, hl => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [List.nodup_cons] at hn
    simp only [List.map_cons, List.zip_cons_cons, List.cons.injEq]
    refine ⟨by rw [Env.lookup_cons, if_pos rfl], ?_⟩
    rw [← lookup_zip_holes hs cs hn.2 hl]
    apply List.map_congr_left
    intro y hy
    rw [Env.lookup_cons, if_neg]
    rintro rfl
    exact hn.1 hy
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

theorem lookup_zip_none :
    ∀ (hs : List String) (cs : List Term) (x : String), x ∉ hs →
      Env.lookup (hs.zip cs) x = none
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | h :: hs, c :: cs, x, hx => by
    rw [List.mem_cons, not_or] at hx
    simp only [List.zip_cons_cons, Env.lookup_cons, if_neg (Ne.symm hx.1)]
    exact lookup_zip_none hs cs x hx.2

/-- The environments a source equation and its lifting bind. -/
theorem rel_matched (k : String) (cs : List Term) (σ : Env)
    (hn : L.holes.Nodup) (hl : L.holes.length = cs.length) :
    Rel L k cs ((k, closure L.callee cs) :: σ) (L.holes.zip cs ++ σ) where
  closure := by rw [Env.lookup_cons, if_pos rfl]
  holes := by
    rw [← lookup_zip_holes L.holes cs hn hl]
    apply List.map_congr_left
    intro h hh
    have := List.mem_map_of_mem (f := Env.lookup (L.holes.zip cs)) hh
    rw [lookup_zip_holes L.holes cs hn hl, List.mem_map] at this
    obtain ⟨c, _, hc⟩ := this
    rw [← hc]
    exact Env.lookup_append_of_lookup _ _ _ _ hc.symm
  others := by
    intro x hxk hxh
    rw [Env.lookup_append_of_none _ _ _ (lookup_zip_none _ _ _ hxh),
      Env.lookup_cons, if_neg (Ne.symm hxk)]


/-! ## Selecting the corresponding equations -/

/-- The selection test `Program.select` applies to each equation. -/
def selector (f : String) (vs : List Term) (e : Equation) :
    Option (Equation × Env) :=
  if e.head = f ∧ e.params.length = vs.length then
    (matchTerms e.params vs).map (fun σ => (e, σ))
  else none

theorem select_eq (P : Program) (f : String) (vs : List Term) :
    P.select f vs = P.findSome? (selector f vs) := rfl

theorem selector_other {f : String} {vs : List Term} {e : Equation}
    (h : e.head ≠ f) : selector f vs e = none := by
  simp [selector, h]

theorem findSome_absent {f : String} {vs : List Term} :
    ∀ (Q : Program), (∀ e ∈ Q, e.head ≠ f) → Q.findSome? (selector f vs) = none
  | [], _ => rfl
  | e :: Q, h => by
    rw [List.findSome?_cons, selector_other (h e (by simp))]
    exact findSome_absent Q (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

theorem findSome_filter {f : String} {vs : List Term} :
    ∀ (P : Program), P.findSome? (selector f vs) =
      (P.filter (fun e => e.head = f)).findSome? (selector f vs)
  | [] => rfl
  | e :: P => by
    by_cases h : e.head = f
    · simp only [List.filter_cons, h, decide_true, if_true, List.findSome?_cons]
      cases selector f vs e <;> simp only [findSome_filter P]
    · simp only [List.filter_cons, h, decide_false, Bool.false_eq_true, if_false,
        List.findSome?_cons, selector_other h, findSome_filter P]

theorem liftEquation_head {e : Equation} {k : String} {rest : List Term}
    (h : e.params = .var k :: rest) : (liftEquation L e).head = L.lifted := by
  unfold liftEquation
  rw [h]

theorem liftEquation_eq {e : Equation} {k : String} {rest : List Term}
    (h : e.params = .var k :: rest) :
    liftEquation L e =
      ⟨e.name, L.lifted, L.holes.map .var ++ rest, liftTerm L k e.body⟩ := by
  unfold liftEquation
  rw [h]

/-- Over source equations, the source selection and the lifted selection
choose the same equation, matched with environments the lifting relates. -/
theorem findSome_lifted (cs vs : List Term) (hcs : L.holes.length = cs.length) :
    ∀ (l : List Equation), (∀ e ∈ l, e.head = L.source ∧
        ∃ k rest, e.params = .var k :: rest ∧ Clean L k e.body) →
      (∃ e k rest σr, e ∈ l ∧ e.params = .var k :: rest ∧ Clean L k e.body ∧
        l.findSome? (selector L.source (closure L.callee cs :: vs)) =
          some (e, (k, closure L.callee cs) :: σr) ∧
        (l.map (liftEquation L)).findSome? (selector L.lifted (cs ++ vs)) =
          some (liftEquation L e, L.holes.zip cs ++ σr)) ∨
      (l.findSome? (selector L.source (closure L.callee cs :: vs)) = none ∧
        (l.map (liftEquation L)).findSome? (selector L.lifted (cs ++ vs)) = none)
  | [], _ => Or.inr ⟨rfl, rfl⟩
  | e :: l, hl => by
    obtain ⟨he, k, rest, hp, hc⟩ := hl e (by simp)
    have ih := findSome_lifted cs vs hcs l
      (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
    have hsrc : selector L.source (closure L.callee cs :: vs) e =
        if rest.length = vs.length then
          (matchTerms rest vs).map (fun σ => (e, (k, closure L.callee cs) :: σ))
        else none := by
      unfold selector
      rw [hp, matchTerms_var_cons]
      by_cases hlen : rest.length = vs.length
      · rw [if_pos ⟨he, by simp [hlen]⟩, if_pos hlen, Option.map_map]
        rfl
      · rw [if_neg (fun h => hlen (by simpa using h.2)), if_neg hlen]
    have hlift : selector L.lifted (cs ++ vs) (liftEquation L e) =
        if rest.length = vs.length then
          (matchTerms rest vs).map
            (fun σ => (liftEquation L e, L.holes.zip cs ++ σ))
        else none := by
      unfold selector
      rw [liftEquation_eq L hp]
      simp only
      rw [matchTerms_vars_append rest vs L.holes cs hcs]
      by_cases hlen : rest.length = vs.length
      · rw [if_pos ⟨by trivial, by simp [hlen, hcs]⟩, if_pos hlen, Option.map_map,
          ← liftEquation_eq L hp]
        rfl
      · rw [if_neg (fun h => hlen (by simp [hcs] at h; omega)), if_neg hlen]
    rw [List.findSome?_cons, List.map_cons, List.findSome?_cons, hsrc, hlift]
    by_cases hlen : rest.length = vs.length
    · rw [if_pos hlen, if_pos hlen]
      cases hm : matchTerms rest vs with
      | none =>
        simp only [Option.map_none]
        rcases ih with ⟨e', k', rest', σr, he', hp', hc', h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨e', k', rest', σr, List.mem_cons_of_mem _ he', hp', hc',
            h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
      | some σr =>
        exact Or.inl ⟨e, k, rest, σr, by simp, hp, hc, rfl, rfl⟩
    · rw [if_neg hlen, if_neg hlen]
      rcases ih with ⟨e', k', rest', σr, he', hp', hc', h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨e', k', rest', σr, List.mem_cons_of_mem _ he', hp', hc',
          h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩


/-! ## Calls of the source and the lifted relation -/

section Calls

variable {P : Program} {H : Host}

theorem mem_liftedEquations {e : Equation} (he : e ∈ liftedEquations L P) :
    ∃ e₀ ∈ P, e₀.head = L.source ∧ e = liftEquation L e₀ := by
  unfold liftedEquations at he
  rw [List.mem_map] at he
  obtain ⟨e₀, h₀, rfl⟩ := he
  rw [List.mem_filter] at h₀
  exact ⟨e₀, h₀.1, by simpa using h₀.2, rfl⟩

theorem liftedEquations_head (hL : Lifts L P H) {e : Equation}
    (he : e ∈ liftedEquations L P) : e.head = L.lifted := by
  obtain ⟨e₀, h₀, hs, rfl⟩ := mem_liftedEquations L he
  obtain ⟨k, rest, hp, _⟩ := hL.equations e₀ h₀ hs
  exact liftEquation_head L hp

theorem definesAt_iff_exists (Q : Program) (f : String) (n : Nat) :
    Q.definesAt f n = true ↔ ∃ e ∈ Q, e.head = f ∧ e.params.length = n := by
  simp [Program.definesAt, List.any_eq_true]

theorem defines_iff_exists (Q : Program) (f : String) :
    Q.defines f = true ↔ ∃ e ∈ Q, e.head = f := by
  simp [Program.defines, List.any_eq_true]

theorem definesAt_lifted (hL : Lifts L P H) (cs vs : List Term)
    (hcs : L.holes.length = cs.length) :
    (withLifted L P).definesAt L.lifted (cs ++ vs).length =
      (withLifted L P).definesAt L.source (closure L.callee cs :: vs).length := by
  apply Bool.eq_iff_iff.mpr
  rw [definesAt_iff_exists, definesAt_iff_exists]
  constructor
  · rintro ⟨e, he, hh, hl⟩
    rcases List.mem_append.mp he with heP | heL
    · exact absurd hh (hL.fresh e heP)
    · obtain ⟨e₀, h₀, hs, rfl⟩ := mem_liftedEquations L heL
      obtain ⟨k, rest, hp, _⟩ := hL.equations e₀ h₀ hs
      rw [liftEquation_eq L hp] at hl
      simp only [List.length_append, List.length_map, hcs] at hl
      refine ⟨e₀, List.mem_append_left _ h₀, hs, ?_⟩
      rw [hp]
      simp only [List.length_cons]
      omega
  · rintro ⟨e, he, hh, hl⟩
    rcases List.mem_append.mp he with heP | heL
    · obtain ⟨k, rest, hp, _⟩ := hL.equations e heP hh
      refine ⟨liftEquation L e, List.mem_append_right _ ?_, liftEquation_head L hp, ?_⟩
      · unfold liftedEquations
        exact List.mem_map_of_mem (List.mem_filter.mpr ⟨heP, by simpa using hh⟩)
      · rw [liftEquation_eq L hp]
        rw [hp] at hl
        simp only [List.length_cons] at hl
        simp only [List.length_append, List.length_map, hcs]
        omega
    · exact absurd hh (by rw [liftedEquations_head L hL heL]; exact Ne.symm hL.source_ne_lifted)

theorem defines_source (hL : Lifts L P H) :
    (withLifted L P).defines L.source = true := by
  obtain ⟨e, he, hh⟩ := (defines_iff_exists P L.source).mp hL.defined
  exact (defines_iff_exists _ _).mpr ⟨e, List.mem_append_left _ he, hh⟩

theorem defines_lifted (hL : Lifts L P H) :
    (withLifted L P).defines L.lifted = true := by
  obtain ⟨e, he, hh⟩ := (defines_iff_exists P L.source).mp hL.defined
  obtain ⟨k, rest, hp, _⟩ := hL.equations e he hh
  refine (defines_iff_exists _ _).mpr ⟨liftEquation L e, List.mem_append_right _ ?_,
    liftEquation_head L hp⟩
  unfold liftedEquations
  exact List.mem_map_of_mem (List.mem_filter.mpr ⟨he, by simpa using hh⟩)

/-- A call of the source relation on a closure and the call of the lifted
relation on its captured values correspond, for any relation between the
outcomes of the bodies that relates two failures. -/
theorem call_corr (hL : Lifts L P H) {R : Outcome → Outcome → Prop}
    (hfail : R .failure .failure) {ev ev' : Env → Term → Outcome}
    {cs : List Term} (hcs : L.holes.length = cs.length)
    (hbody : ∀ k env env' t, Rel L k cs env env' → Clean L k t →
      R (ev env t) (ev' env' (liftTerm L k t)))
    (vs : List Term) :
    R (applyWith (withLifted L P) H ev L.source (closure L.callee cs :: vs))
      (applyWith (withLifted L P) H ev' L.lifted (cs ++ vs)) := by
  unfold applyWith
  rw [definesAt_lifted L hL cs vs hcs]
  by_cases hd : (withLifted L P).definesAt L.source
      (closure L.callee cs :: vs).length = true
  · rw [if_pos hd, if_pos hd, select_eq, select_eq, withLifted,
      List.findSome?_append, List.findSome?_append,
      findSome_absent (liftedEquations L P)
        (fun e he => by rw [liftedEquations_head L hL he]; exact Ne.symm hL.source_ne_lifted),
      Option.or_none, findSome_absent P (fun e he => hL.fresh e he), Option.none_or,
      findSome_filter P]
    unfold liftedEquations
    have hl : ∀ e ∈ P.filter (fun e => e.head = L.source), e.head = L.source ∧
        ∃ k rest, e.params = .var k :: rest ∧ Clean L k e.body := by
      intro e he
      rw [List.mem_filter] at he
      have hs : e.head = L.source := by simpa using he.2
      exact ⟨hs, hL.equations e he.1 hs⟩
    rcases findSome_lifted L cs vs hcs _ hl with
      ⟨e, k, rest, σr, _, hp, hc, h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      simp only
      rw [liftEquation_eq L hp]
      exact hbody k _ _ e.body (rel_matched L k cs σr hL.holes_nodup hcs) hc
    · rw [h1, h2]
      exact hfail
  · rw [if_neg hd, if_neg hd, if_pos (defines_source L hL), if_pos (defines_lifted L hL)]
    exact hfail

end Calls


/-! ## The square -/

section Square

variable {P : Program} {H : Host}

/-- What an expression does with the outcome of its items. -/
def afterItems (f : List Term → Outcome) : ItemsOutcome → Outcome
  | .values vs => f vs
  | .stop o => o

theorem afterItems_refines {a b : ItemsOutcome} (h : a = .stop .exhausted ∨ a = b)
    {f g : List Term → Outcome} (hfg : ∀ vs, Refines (f vs) (g vs)) :
    Refines (afterItems f a) (afterItems g b) := by
  rcases h with h | h
  · subst h
    exact Or.inl rfl
  · subst h
    cases a with
    | values vs => exact hfg vs
    | stop o => exact Refines.refl _

theorem eval_var (Q : Program) (n : Nat) (env : Env) (x : String) :
    Closures.eval Q H (n + 1) env (.var x) =
      match env.lookup x with
      | some v => .value v
      | none => .failure := rfl

theorem eval_list (Q : Program) (n : Nat) (env : Env) (items : List Term) :
    Closures.eval Q H (n + 1) env (.list items) =
      afterItems (fun vs => .value (.list vs))
        (evalItemsWith (Closures.eval Q H n) env items) := rfl

theorem eval_call (Q : Program) (n : Nat) (env : Env) {f : String}
    (hf : Ordinary f) (args : List Term) :
    Closures.eval Q H (n + 1) env (.expr (.sym f :: args)) =
      afterItems (applyWith Q H (Closures.eval Q H n) f)
        (evalItemsWith (Closures.eval Q H n) env args) := by
  show Closures.evalStep _ _ env _ = _
  rw [evalStep_call hf]
  rfl

theorem eval_dynamic (Q : Program) (n : Nat) (env : Env) {h : Term}
    (hh : ∀ s, h ≠ .sym s) (args : List Term) :
    Closures.eval Q H (n + 1) env (.expr (h :: args)) =
      afterItems (applyValues (applyWith Q H (Closures.eval Q H n)))
        (evalItemsWith (Closures.eval Q H n) env (h :: args)) := by
  show Closures.evalStep _ _ env _ = _
  rw [evalStep_dynamic hh]
  rfl

theorem eval_let (Q : Program) (n : Nat) (env : Env) (x : String) (e b : Term) :
    Closures.eval Q H (n + 1) env (.expr [.sym "let", .var x, e, b]) =
      match Closures.eval Q H n env e with
      | .value v => Closures.eval Q H n ((x, v) :: env) b
      | o => o := rfl

theorem eval_nullary (Q : Program) (n : Nat) (env : Env) (s : String) :
    Closures.eval Q H (n + 1) env (.expr [.sym "metta-nullary", .sym s]) =
      .value (.expr [.sym s]) := rfl

theorem withLifted_partial_free (hL : Lifts L P H) :
    (withLifted L P).defines "partial" = false := by
  cases hd : (withLifted L P).defines "partial" with
  | false => rfl
  | true =>
    obtain ⟨e, he, hh⟩ := (defines_iff_exists _ _).mp hd
    rcases List.mem_append.mp he with heP | heL
    · have : P.defines "partial" = true :=
        (defines_iff_exists _ _).mpr ⟨e, heP, hh⟩
      rw [hL.partial_free] at this
      cases this
    · rw [liftedEquations_head L hL heL] at hh
      exact absurd hh hL.lifted_ne_partial

/-- Items evaluated by the source side with some fuel and by the lifted side
with two more: the same values, unless the source side runs out. -/
theorem items_forward {n : Nat} {k : String} {cs : List Term} {env env' : Env}
    (ih : ∀ (k : String) (env env' : Env) (t : Term), Rel L k cs env env' →
      Clean L k t → Refines (Closures.eval (withLifted L P) H n env t)
        (Closures.eval (withLifted L P) H (n + 2) env' (liftTerm L k t)))
    (hr : Rel L k cs env env') (items : List Term) (hall : ∀ t ∈ items, Clean L k t) :
    evalItemsWith (Closures.eval (withLifted L P) H n) env items = .stop .exhausted ∨
      evalItemsWith (Closures.eval (withLifted L P) H n) env items =
        evalItemsWith (Closures.eval (withLifted L P) H (n + 2)) env'
          (liftTerms L k items) := by
  have := evalItemsWith_rel (ev := Closures.eval (withLifted L P) H n)
    (ev' := Closures.eval (withLifted L P) H (n + 2)) (env := env) (env' := env')
    id (liftTerm L k) items (fun t ht => ih k env env' t hr (hall t ht))
  rw [List.map_id, ← liftTerms_eq_map] at this
  exact this

theorem monotone_call (Q : Program) (n : Nat) (f : String) (vs : List Term) :
    Refines (applyWith Q H (Closures.eval Q H n) f vs)
      (applyWith Q H (Closures.eval Q H (n + 2)) f vs) :=
  applyWith_refines Q H (fun env t => Closures.eval_refines_add Q H n 2 env t) f vs

/-- Items after a first value. -/
def consItems (v : Term) : ItemsOutcome → ItemsOutcome
  | .values vs => .values (v :: vs)
  | .stop o => .stop o

/-- Items after a prefix of values. -/
def appendItems (us : List Term) : ItemsOutcome → ItemsOutcome
  | .values vs => .values (us ++ vs)
  | .stop o => .stop o

theorem evalItemsWith_cons_value {ev : Env → Term → Outcome} {env : Env} {t : Term}
    {v : Term} (h : ev env t = .value v) (ts : List Term) :
    evalItemsWith ev env (t :: ts) = consItems v (evalItemsWith ev env ts) := by
  simp only [evalItemsWith, h]
  cases evalItemsWith ev env ts <;> rfl

theorem evalItemsWith_cons_exhausted {ev : Env → Term → Outcome} {env : Env}
    {t : Term} (h : ev env t = .exhausted) (ts : List Term) :
    evalItemsWith ev env (t :: ts) = .stop .exhausted := by
  simp only [evalItemsWith, h]

theorem evalItemsWith_append_prefix {ev : Env → Term → Outcome} {env : Env}
    {xs us : List Term} (hx : evalItemsWith ev env xs = .values us) (ys : List Term) :
    evalItemsWith ev env (xs ++ ys) = appendItems us (evalItemsWith ev env ys) := by
  rw [evalItemsWith_append_values hx]
  cases evalItemsWith ev env ys <;> rfl

theorem afterItems_consItems (F : List Term → Outcome) (v : Term) (X : ItemsOutcome) :
    afterItems F (consItems v X) = afterItems (fun vs => F (v :: vs)) X := by
  cases X <;> rfl

theorem afterItems_appendItems (F : List Term → Outcome) (us : List Term)
    (X : ItemsOutcome) :
    afterItems F (appendItems us X) = afterItems (fun vs => F (us ++ vs)) X := by
  cases X <;> rfl

theorem applyValues_closure (call : String → List Term → Outcome) (g : String)
    (cs vs : List Term) :
    applyValues call (closure g cs :: vs) = call g (cs ++ vs) := by
  simp [applyValues]

/-- The forward half of the square: the source side with some fuel is refined
by the lifted side with two more. -/
theorem eval_refines_lifted (hL : Lifts L P H) {cs : List Term}
    (hcs : L.holes.length = cs.length) :
    ∀ (n : Nat) (k : String) (env env' : Env) (t : Term), Rel L k cs env env' →
      Clean L k t → Refines (Closures.eval (withLifted L P) H n env t)
        (Closures.eval (withLifted L P) H (n + 2) env' (liftTerm L k t))
  | 0, _, _, _, _, _, _ => Or.inl rfl
  | n + 1, k, env, env', t, hr, hc => by
    have ih := eval_refines_lifted hL hcs n
    rw [show n + 1 + 2 = (n + 2) + 1 from rfl]
    cases hc with
    | @var x hx =>
      by_cases hxk : x = k
      · subst hxk
        have hl : liftTerm L x (.var x) = rebuild L := by
          show liftVar L x x = _
          simp [liftVar]
        rw [hl, show n + 2 + 1 = n + 3 from rfl,
          eval_rebuild L _ H (withLifted_partial_free L hL) hL.partial_host hr n,
          eval_var, hr.closure]
        exact Refines.refl _
      · have hl : liftTerm L k (.var x) = .var x := by
          show liftVar L k x = _
          simp [liftVar, hxk]
        rw [hl, eval_var, eval_var, hr.others x hxk hx]
        exact Refines.refl _
    | sym s => exact Refines.refl _
    | lit s => exact Refines.refl _
    | @list items hall =>
      rw [show liftTerm L k (.list items) = .list (liftTerms L k items) from rfl,
        eval_list, eval_list]
      exact afterItems_refines (items_forward L ih hr items hall)
        (fun vs => Refines.refl _)
    | @expr items hsp hall =>
      rcases items with _ | ⟨hd, args⟩
      · exact Refines.refl _
      have hhd : Clean L k hd := hall hd (by simp)
      have hargs : ∀ t ∈ args, Clean L k t := fun t ht => hall t (List.mem_cons_of_mem _ ht)
      cases hd with
      | var x =>
        by_cases hxk : x = k
        · subst hxk
          rw [liftTerm_apply, eval_dynamic _ _ _ (fun s h => Term.noConfusion h),
            eval_call _ _ _ hL.callee]
          rcases n with _ | m
          · rw [evalItemsWith_cons_exhausted (by rfl)]
            exact Or.inl rfl
          · rw [evalItemsWith_cons_value (by rw [eval_var, hr.closure]),
              afterItems_consItems,
              evalItemsWith_append_prefix (evalItems_holes L _ H hr (m + 2)),
              afterItems_appendItems]
            simp only [applyValues_closure]
            exact afterItems_refines (items_forward L ih hr args hargs)
              (fun vs => monotone_call _ _ _ _)
        · rw [liftTerm_var_head L k x hxk, eval_dynamic _ _ _ (fun s h => Term.noConfusion h),
            eval_dynamic _ _ _ (fun s h => Term.noConfusion h)]
          have hl : Term.var x :: liftTerms L k args = liftTerms L k (.var x :: args) := by
            rw [liftTerms_cons]
            show _ = liftVar L k x :: _
            simp [liftVar, hxk]
          rw [hl]
          exact afterItems_refines (items_forward L ih hr _ hall)
            (fun vs => applyValues_refines (fun f vs => monotone_call _ _ f vs) vs)
      | sym f =>
        by_cases hlet : f = "let"
        · subst hlet
          obtain ⟨x, e, b, heq, hxk⟩ := hsp.1 rfl
          cases heq
          have hx : x ∉ L.holes := by
            have := hall (.var x) (by simp)
            cases this with
            | var h => exact h
          have he : Clean L k e := hall e (by simp)
          have hb : Clean L k b := hall b (by simp)
          have hl : liftTerm L k (.expr [.sym "let", .var x, e, b]) =
              .expr [.sym "let", .var x, liftTerm L k e, liftTerm L k b] := by
            rw [liftTerm_call L k "let" _ (fun h => hL.source.1 (h.1 ▸ rfl))]
            show Term.expr (.sym "let" :: liftVar L k x :: _) = _
            simp [liftVar, hxk, liftTerms_cons, liftTerms_nil]
          rw [hl, eval_let, eval_let]
          rcases ih k env env' e hr he with h | h
          · rw [h]
            exact Or.inl rfl
          · rw [← h]
            cases hv : Closures.eval (withLifted L P) H n env e with
            | value v => exact ih k _ _ b (hr.extend L hxk hx v) hb
            | failure => exact Refines.refl _
            | exhausted => exact Refines.refl _
        by_cases hnull : f = "metta-nullary"
        · subst hnull
          obtain ⟨s', heq⟩ := hsp.2 rfl
          cases heq
          rw [liftTerm_call L k "metta-nullary" _ (fun h => hL.source.2 (h.1 ▸ rfl))]
          exact Refines.refl _
        have hf : Ordinary f := ⟨hlet, hnull⟩
        by_cases hfw : f = L.source ∧ args.head? = some (.var k)
        · obtain ⟨rfl, hh⟩ := hfw
          rcases args with _ | ⟨a, rest⟩
          · cases hh
          · simp only [List.head?_cons, Option.some.injEq] at hh
            subst hh
            have hrest : ∀ t ∈ rest, Clean L k t :=
              fun t ht => hargs t (List.mem_cons_of_mem _ ht)
            rw [liftTerm_forward, eval_call _ _ _ hL.source, eval_call _ _ _ hL.lifted]
            rcases n with _ | m
            · rw [evalItemsWith_cons_exhausted (by rfl)]
              exact Or.inl rfl
            · rw [evalItemsWith_cons_value (by rw [eval_var, hr.closure]),
                afterItems_consItems,
                evalItemsWith_append_prefix (evalItems_holes L _ H hr (m + 2)),
                afterItems_appendItems]
              exact afterItems_refines (items_forward L ih hr rest hrest)
                (fun vs => call_corr L hL (Refines.refl _) hcs ih vs)
        · rw [liftTerm_call L k f args hfw, eval_call _ _ _ hf, eval_call _ _ _ hf]
          exact afterItems_refines (items_forward L ih hr args hargs)
            (fun vs => monotone_call _ _ _ _)
      | lit s =>
        rw [liftTerm_other_head L k _ (fun _ h => Term.noConfusion h)
            (fun _ h => Term.noConfusion h),
          eval_dynamic _ _ _ (fun _ h => Term.noConfusion h),
          eval_dynamic _ _ _ (liftTerm_ne_sym L k (fun _ h => Term.noConfusion h))]
        exact afterItems_refines (items_forward L ih hr _ hall)
          (fun vs => applyValues_refines (fun f vs => monotone_call _ _ f vs) vs)
      | list items' =>
        rw [liftTerm_other_head L k _ (fun _ h => Term.noConfusion h)
            (fun _ h => Term.noConfusion h),
          eval_dynamic _ _ _ (fun _ h => Term.noConfusion h),
          eval_dynamic _ _ _ (liftTerm_ne_sym L k (fun _ h => Term.noConfusion h))]
        exact afterItems_refines (items_forward L ih hr _ hall)
          (fun vs => applyValues_refines (fun f vs => monotone_call _ _ f vs) vs)
      | expr items' =>
        rw [liftTerm_other_head L k _ (fun _ h => Term.noConfusion h)
            (fun _ h => Term.noConfusion h),
          eval_dynamic _ _ _ (fun _ h => Term.noConfusion h),
          eval_dynamic _ _ _ (liftTerm_ne_sym L k (fun _ h => Term.noConfusion h))]
        exact afterItems_refines (items_forward L ih hr _ hall)
          (fun vs => applyValues_refines (fun f vs => monotone_call _ _ f vs) vs)

/-- The holes evaluate to the captured values, or run out of fuel. -/
theorem evalItems_holes_any (Q : Program) {k : String} {cs : List Term}
    {env env' : Env} (hr : Rel L k cs env env') (hcs : L.holes.length = cs.length) :
    ∀ n, evalItemsWith (Closures.eval Q H n) env' (L.holes.map .var) = .stop .exhausted ∨
      evalItemsWith (Closures.eval Q H n) env' (L.holes.map .var) = .values cs
  | 0 => by
    cases hh : L.holes with
    | nil =>
      rw [hh] at hcs
      cases cs with
      | nil => exact Or.inr rfl
      | cons _ _ => simp at hcs
    | cons h hs =>
      left
      rfl
  | n + 1 => Or.inr (evalItems_holes L Q H hr n)

/-- The rebuilt closure, with any fuel: the closure, or out of fuel. -/
theorem eval_rebuild_any (hL : Lifts L P H) {k : String} {cs : List Term}
    {env env' : Env} (hr : Rel L k cs env env') (m : Nat) :
    Refines (Closures.eval (withLifted L P) H m env' (rebuild L))
      (.value (closure L.callee cs)) := by
  have h3 := eval_rebuild L (withLifted L P) H (withLifted_partial_free L hL)
    hL.partial_host hr m
  rcases Closures.eval_refines_add (withLifted L P) H m 3 env' (rebuild L) with h | h
  · exact Or.inl h
  · rw [h, h3]
    exact Refines.refl _

/-- Items evaluated by the lifted side with some fuel and by the source side
with one more: the same values, unless the lifted side runs out. -/
theorem items_backward {n : Nat} {k : String} {cs : List Term} {env env' : Env}
    (ih : ∀ (k : String) (env env' : Env) (t : Term), Rel L k cs env env' →
      Clean L k t → Refines (Closures.eval (withLifted L P) H n env' (liftTerm L k t))
        (Closures.eval (withLifted L P) H (n + 1) env t))
    (hr : Rel L k cs env env') (items : List Term) (hall : ∀ t ∈ items, Clean L k t) :
    evalItemsWith (Closures.eval (withLifted L P) H n) env' (liftTerms L k items) =
        .stop .exhausted ∨
      evalItemsWith (Closures.eval (withLifted L P) H n) env' (liftTerms L k items) =
        evalItemsWith (Closures.eval (withLifted L P) H (n + 1)) env items := by
  have := evalItemsWith_rel (ev := Closures.eval (withLifted L P) H n)
    (ev' := Closures.eval (withLifted L P) H (n + 1)) (env := env') (env' := env)
    (liftTerm L k) id items (fun t ht => ih k env env' t hr (hall t ht))
  rw [List.map_id, ← liftTerms_eq_map] at this
  exact this

theorem monotone_call_succ (Q : Program) (n : Nat) (f : String) (vs : List Term) :
    Refines (applyWith Q H (Closures.eval Q H n) f vs)
      (applyWith Q H (Closures.eval Q H (n + 1)) f vs) :=
  applyWith_refines Q H (fun env t => Closures.eval_refines_succ Q H n env t) f vs

theorem evalItemsWith_append_stop {ev : Env → Term → Outcome} {env : Env} :
    ∀ {xs : List Term} {o : Outcome} (ys : List Term),
      evalItemsWith ev env xs = .stop o → evalItemsWith ev env (xs ++ ys) = .stop o
  | [], _, _, h => by cases h
  | x :: xs, o, ys, h => by
    rw [List.cons_append]
    cases hx : ev env x with
    | value v =>
      rw [evalItemsWith_cons_value hx] at h ⊢
      cases hs : evalItemsWith ev env xs with
      | values vs =>
        rw [hs] at h
        cases h
      | stop o' =>
        rw [hs] at h
        cases h
        rw [evalItemsWith_append_stop ys hs]
        rfl
    | failure =>
      simp only [evalItemsWith, hx] at h ⊢
      exact h
    | exhausted =>
      simp only [evalItemsWith, hx] at h ⊢
      exact h

/-- After the holes: the lifted items are the captured values followed by the
lifted arguments, or the holes ran out of fuel. -/
theorem afterItems_holes {Q : Program} {k : String} {cs : List Term}
    {env env' : Env} (hr : Rel L k cs env env') (hcs : L.holes.length = cs.length)
    (n : Nat) (F : List Term → Outcome) (args : List Term) :
    afterItems F (evalItemsWith (Closures.eval Q H n) env'
        (L.holes.map .var ++ args)) = .exhausted ∨
      afterItems F (evalItemsWith (Closures.eval Q H n) env'
        (L.holes.map .var ++ args)) =
      afterItems (fun vs => F (cs ++ vs)) (evalItemsWith (Closures.eval Q H n) env' args) := by
  rcases evalItems_holes_any L Q (H := H) hr hcs n with h | h
  · left
    rw [evalItemsWith_append_stop _ h]
    rfl
  · right
    rw [evalItemsWith_append_prefix h, afterItems_appendItems]

/-- The backward half of the square: the lifted side with some fuel is refined
by the source side with one more. -/
theorem lifted_refines_eval (hL : Lifts L P H) {cs : List Term}
    (hcs : L.holes.length = cs.length) :
    ∀ (n : Nat) (k : String) (env env' : Env) (t : Term), Rel L k cs env env' →
      Clean L k t →
        Refines (Closures.eval (withLifted L P) H n env' (liftTerm L k t))
          (Closures.eval (withLifted L P) H (n + 1) env t)
  | 0, _, _, _, _, _, _ => Or.inl rfl
  | n + 1, k, env, env', t, hr, hc => by
    have ih := lifted_refines_eval hL hcs n
    rw [show n + 1 + 1 = (n + 1) + 1 from rfl]
    cases hc with
    | @var x hx =>
      by_cases hxk : x = k
      · subst hxk
        have hl : liftTerm L x (.var x) = rebuild L := by
          show liftVar L x x = _
          simp [liftVar]
        rw [hl, eval_var, hr.closure]
        exact eval_rebuild_any L hL hr (n + 1)
      · have hl : liftTerm L k (.var x) = .var x := by
          show liftVar L k x = _
          simp [liftVar, hxk]
        rw [hl, eval_var, eval_var, hr.others x hxk hx]
        exact Refines.refl _
    | sym s => exact Refines.refl _
    | lit s => exact Refines.refl _
    | @list items hall =>
      rw [show liftTerm L k (.list items) = .list (liftTerms L k items) from rfl,
        eval_list, eval_list]
      exact afterItems_refines (items_backward L ih hr items hall)
        (fun vs => Refines.refl _)
    | @expr items hsp hall =>
      rcases items with _ | ⟨hd, args⟩
      · exact Refines.refl _
      have hargs : ∀ t ∈ args, Clean L k t := fun t ht => hall t (List.mem_cons_of_mem _ ht)
      cases hd with
      | var x =>
        by_cases hxk : x = k
        · subst hxk
          rw [liftTerm_apply, eval_call _ _ _ hL.callee,
            eval_dynamic _ _ _ (fun s h => Term.noConfusion h),
            evalItemsWith_cons_value (by rw [eval_var, hr.closure]),
            afterItems_consItems]
          simp only [applyValues_closure]
          rcases afterItems_holes L hr hcs n
              (applyWith (withLifted L P) H (Closures.eval (withLifted L P) H n) L.callee)
              (liftTerms L x args) with h | h
          · rw [h]
            exact Or.inl rfl
          · rw [h]
            exact afterItems_refines (items_backward L ih hr args hargs)
              (fun vs => monotone_call_succ _ _ _ _)
        · rw [liftTerm_var_head L k x hxk, eval_dynamic _ _ _ (fun s h => Term.noConfusion h),
            eval_dynamic _ _ _ (fun s h => Term.noConfusion h)]
          have hl : Term.var x :: liftTerms L k args = liftTerms L k (.var x :: args) := by
            rw [liftTerms_cons]
            show _ = liftVar L k x :: _
            simp [liftVar, hxk]
          rw [hl]
          exact afterItems_refines (items_backward L ih hr _ hall)
            (fun vs => applyValues_refines (fun f vs => monotone_call_succ _ _ f vs) vs)
      | sym f =>
        by_cases hlet : f = "let"
        · subst hlet
          obtain ⟨x, e, b, heq, hxk⟩ := hsp.1 rfl
          cases heq
          have hx : x ∉ L.holes := by
            have := hall (.var x) (by simp)
            cases this with
            | var h => exact h
          have he : Clean L k e := hall e (by simp)
          have hb : Clean L k b := hall b (by simp)
          have hl : liftTerm L k (.expr [.sym "let", .var x, e, b]) =
              .expr [.sym "let", .var x, liftTerm L k e, liftTerm L k b] := by
            rw [liftTerm_call L k "let" _ (fun h => hL.source.1 (h.1 ▸ rfl))]
            show Term.expr (.sym "let" :: liftVar L k x :: _) = _
            simp [liftVar, hxk, liftTerms_cons, liftTerms_nil]
          rw [hl, eval_let, eval_let]
          rcases ih k env env' e hr he with h | h
          · rw [h]
            exact Or.inl rfl
          · rw [h]
            cases hv : Closures.eval (withLifted L P) H (n + 1) env e with
            | value v => exact ih k _ _ b (hr.extend L hxk hx v) hb
            | failure => exact Refines.refl _
            | exhausted => exact Refines.refl _
        by_cases hnull : f = "metta-nullary"
        · subst hnull
          obtain ⟨s', heq⟩ := hsp.2 rfl
          cases heq
          rw [liftTerm_call L k "metta-nullary" _ (fun h => hL.source.2 (h.1 ▸ rfl))]
          exact Refines.refl _
        have hf : Ordinary f := ⟨hlet, hnull⟩
        by_cases hfw : f = L.source ∧ args.head? = some (.var k)
        · obtain ⟨rfl, hh⟩ := hfw
          rcases args with _ | ⟨a, rest⟩
          · cases hh
          · simp only [List.head?_cons, Option.some.injEq] at hh
            subst hh
            have hrest : ∀ t ∈ rest, Clean L k t :=
              fun t ht => hargs t (List.mem_cons_of_mem _ ht)
            rw [liftTerm_forward, eval_call _ _ _ hL.lifted, eval_call _ _ _ hL.source,
              evalItemsWith_cons_value (by rw [eval_var, hr.closure]),
              afterItems_consItems]
            rcases afterItems_holes L hr hcs n
                (applyWith (withLifted L P) H (Closures.eval (withLifted L P) H n) L.lifted)
                (liftTerms L k rest) with h | h
            · rw [h]
              exact Or.inl rfl
            · rw [h]
              exact afterItems_refines (items_backward L ih hr rest hrest)
                (fun vs => call_corr L hL (R := fun o o' => Refines o' o) (Refines.refl _)
                  hcs ih vs)
        · rw [liftTerm_call L k f args hfw, eval_call _ _ _ hf, eval_call _ _ _ hf]
          exact afterItems_refines (items_backward L ih hr args hargs)
            (fun vs => monotone_call_succ _ _ _ _)
      | lit s =>
        rw [liftTerm_other_head L k _ (fun _ h => Term.noConfusion h)
            (fun _ h => Term.noConfusion h),
          eval_dynamic _ _ _ (liftTerm_ne_sym L k (fun _ h => Term.noConfusion h)),
          eval_dynamic _ _ _ (fun _ h => Term.noConfusion h)]
        exact afterItems_refines (items_backward L ih hr _ hall)
          (fun vs => applyValues_refines (fun f vs => monotone_call_succ _ _ f vs) vs)
      | list items' =>
        rw [liftTerm_other_head L k _ (fun _ h => Term.noConfusion h)
            (fun _ h => Term.noConfusion h),
          eval_dynamic _ _ _ (liftTerm_ne_sym L k (fun _ h => Term.noConfusion h)),
          eval_dynamic _ _ _ (fun _ h => Term.noConfusion h)]
        exact afterItems_refines (items_backward L ih hr _ hall)
          (fun vs => applyValues_refines (fun f vs => monotone_call_succ _ _ f vs) vs)
      | expr items' =>
        rw [liftTerm_other_head L k _ (fun _ h => Term.noConfusion h)
            (fun _ h => Term.noConfusion h),
          eval_dynamic _ _ _ (liftTerm_ne_sym L k (fun _ h => Term.noConfusion h)),
          eval_dynamic _ _ _ (fun _ h => Term.noConfusion h)]
        exact afterItems_refines (items_backward L ih hr _ hall)
          (fun vs => applyValues_refines (fun f vs => monotone_call_succ _ _ f vs) vs)

/-- The square for calls, forward: the source relation called on a closure is
refined by the lifted relation called on its captured values with two more
units of fuel. -/
theorem apply_refines_lifted (hL : Lifts L P H) {cs : List Term}
    (hcs : L.holes.length = cs.length) (n : Nat) (vs : List Term) :
    Refines (Closures.apply (withLifted L P) H n L.source (closure L.callee cs :: vs))
      (Closures.apply (withLifted L P) H (n + 2) L.lifted (cs ++ vs)) :=
  call_corr L hL (Refines.refl _) hcs (eval_refines_lifted L hL hcs n) vs

/-- The square for calls, backward: the lifted call is refined by the source
call with one more unit of fuel. -/
theorem lifted_apply_refines (hL : Lifts L P H) {cs : List Term}
    (hcs : L.holes.length = cs.length) (n : Nat) (vs : List Term) :
    Refines (Closures.apply (withLifted L P) H n L.lifted (cs ++ vs))
      (Closures.apply (withLifted L P) H (n + 1) L.source (closure L.callee cs :: vs)) :=
  call_corr L hL (R := fun o o' => Refines o' o) (Refines.refl _) hcs
    (lifted_refines_eval L hL hcs n) vs

/-- The transfer intertwines the two calls exactly: when either call ends, the
other ends with the same outcome. -/
theorem apply_lifted_eq (hL : Lifts L P H) {cs : List Term}
    (hcs : L.holes.length = cs.length) (n : Nat) (vs : List Term)
    (h : Closures.apply (withLifted L P) H n L.source (closure L.callee cs :: vs) ≠
      .exhausted) :
    Closures.apply (withLifted L P) H (n + 2) L.lifted (cs ++ vs) =
      Closures.apply (withLifted L P) H n L.source (closure L.callee cs :: vs) :=
  ((apply_refines_lifted L hL hcs n vs).eq h).symm

theorem apply_source_eq (hL : Lifts L P H) {cs : List Term}
    (hcs : L.holes.length = cs.length) (n : Nat) (vs : List Term)
    (h : Closures.apply (withLifted L P) H n L.lifted (cs ++ vs) ≠ .exhausted) :
    Closures.apply (withLifted L P) H (n + 1) L.source (closure L.callee cs :: vs) =
      Closures.apply (withLifted L P) H n L.lifted (cs ++ vs) :=
  ((lifted_apply_refines L hL hcs n vs).eq h).symm

end Square

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.ClosureSpecialization
