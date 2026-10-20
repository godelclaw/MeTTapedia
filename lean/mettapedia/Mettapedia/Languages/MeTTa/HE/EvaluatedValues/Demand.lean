import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Term

/-!
# Evaluation demands

One evaluation step of the call calculus is described as a `Demand`: a finite
tree that either finishes with an answer or demands the full result list of
evaluating a runtime term and continues with it. Running a demand against an
evaluator answers every demand; the fuelled evaluator, its limit and both
return rules share this one description.

Because every demand tree is finite, running is monotone in the evaluator
(`Demand.run_mono`) and continuous along increasing chains of evaluators
(`Demand.run_continuous`). These two facts make the limit of the fuelled
evaluator a fixed point of one step (see `Calculus`).

`Demand.Rel` relates two demand trees that ask related questions and finish
with related answers whenever their replies are related; `Demand.Rel.run`
transports a run of one tree to a run of the other. The conservativity theorem
uses it with erasure as the relation.

`combos` is the list of all argument combinations, first argument outermost.
-/

namespace Mettapedia.Languages.MeTTa.HE.EvaluatedValues

/-- A computation that may demand the results of evaluating runtime terms. -/
inductive Demand (α : Type) : Type where
  | done : α → Demand α
  | need : MAtom → (List MAtom → Demand α) → Demand α

/-- Partial evaluators: `none` means no answer within the available budget. -/
abbrev Evaluator := MAtom → Option (List MAtom)

/-- `ev'` answers everything `ev` answers, with the same answer. -/
def Evaluator.Extends (ev ev' : Evaluator) : Prop :=
  ∀ t r, ev t = some r → ev' t = some r

theorem Evaluator.Extends.refl (ev : Evaluator) : ev.Extends ev := fun _ _ h => h

theorem Evaluator.Extends.trans {ev₁ ev₂ ev₃ : Evaluator} (h₁ : ev₁.Extends ev₂)
    (h₂ : ev₂.Extends ev₃) : ev₁.Extends ev₃ := fun t r h => h₂ t r (h₁ t r h)

/-- Concatenate the answers of `f` along a list; `none` if one is missing. -/
def optFlatMap {α β : Type} (l : List α) (f : α → Option (List β)) : Option (List β) :=
  match l with
  | [] => some []
  | a :: as => (f a).bind fun r => (optFlatMap as f).map fun rs => r ++ rs

/-- Answer `f` at every element; `none` if one is missing. -/
def optTraverse {α β : Type} (l : List α) (f : α → Option β) : Option (List β) :=
  match l with
  | [] => some []
  | a :: as => (f a).bind fun b => (optTraverse as f).map fun bs => b :: bs

/-- Kleisli extension for result lists: run `f` on every result and
concatenate. -/
def kbind {α β : Type} (o : Option (List α)) (f : α → Option (List β)) : Option (List β) :=
  o.bind fun r => optFlatMap r f

@[simp] theorem optFlatMap_nil {α β : Type} (f : α → Option (List β)) :
    optFlatMap [] f = some [] := rfl

@[simp] theorem optFlatMap_cons {α β : Type} (a : α) (as : List α) (f : α → Option (List β)) :
    optFlatMap (a :: as) f = (f a).bind fun r => (optFlatMap as f).map fun rs => r ++ rs := rfl

@[simp] theorem optTraverse_nil {α β : Type} (f : α → Option β) : optTraverse [] f = some [] := rfl

@[simp] theorem optTraverse_cons {α β : Type} (a : α) (as : List α) (f : α → Option β) :
    optTraverse (a :: as) f = (f a).bind fun b => (optTraverse as f).map fun bs => b :: bs := rfl

theorem optFlatMap_singleton {α β : Type} (l : List α) (f : α → β) :
    optFlatMap l (fun a => some [f a]) = some (l.map f) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem optFlatMap_some {α β : Type} (l : List α) (f : α → List β) :
    optFlatMap l (fun a => some (f a)) = some (l.flatMap f) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem optFlatMap_append {α β : Type} (l₁ l₂ : List α) (f : α → Option (List β)) :
    optFlatMap (l₁ ++ l₂) f =
      (optFlatMap l₁ f).bind fun r₁ => (optFlatMap l₂ f).map fun r₂ => r₁ ++ r₂ := by
  induction l₁ with
  | nil => cases h : optFlatMap l₂ f <;> simp [h]
  | cons a as ih =>
    simp only [List.cons_append, optFlatMap_cons, ih]
    cases f a with
    | none => rfl
    | some r =>
      cases optFlatMap as f with
      | none => rfl
      | some rs => cases optFlatMap l₂ f <;> simp

theorem optFlatMap_congr {α β : Type} {l : List α} {f g : α → Option (List β)}
    (h : ∀ a ∈ l, f a = g a) : optFlatMap l f = optFlatMap l g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [optFlatMap_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem optFlatMap_map {α β γ : Type} (l : List α) (g : α → β) (f : β → Option (List γ)) :
    optFlatMap (l.map g) f = optFlatMap l (fun a => f (g a)) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem optFlatMap_flatMap {α β γ : Type} (l : List α) (g : α → List β)
    (f : β → Option (List γ)) :
    optFlatMap (l.flatMap g) f = optFlatMap l (fun a => optFlatMap (g a) f) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.flatMap_cons, optFlatMap_append, ih, optFlatMap_cons]

theorem optFlatMap_mapResults {α β γ : Type} (l : List α) (f : α → Option (List β))
    (g : β → γ) :
    (optFlatMap l f).map (List.map g) = optFlatMap l (fun a => (f a).map (List.map g)) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [optFlatMap_cons, ← ih]
    cases f a with
    | none => rfl
    | some r => cases optFlatMap as f <;> simp

/-- The answer of a total flat map is the concatenation of the answers. -/
theorem optFlatMap_eq_some {α β : Type} {l : List α} {f : α → Option (List β)}
    {g : α → List β} (h : ∀ a ∈ l, f a = some (g a)) : optFlatMap l f = some (l.flatMap g) := by
  rw [optFlatMap_congr h, optFlatMap_some]

theorem mem_of_optFlatMap {α β : Type} {l : List α} {f : α → Option (List β)} {R : List β}
    (h : optFlatMap l f = some R) {b : β} (hb : b ∈ R) :
    ∃ a ∈ l, ∃ r, f a = some r ∧ b ∈ r := by
  induction l generalizing R with
  | nil => simp at h; subst h; simp at hb
  | cons a as ih =>
    simp only [optFlatMap_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some r =>
      cases hrest : optFlatMap as f with
      | none => simp [hfa, hrest] at h
      | some rs =>
        simp only [hfa, hrest, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        rcases List.mem_append.mp hb with hb | hb
        · exact ⟨a, List.mem_cons_self, r, hfa, hb⟩
        · obtain ⟨a', ha', r', h1, h2⟩ := ih hrest hb
          exact ⟨a', List.mem_cons_of_mem _ ha', r', h1, h2⟩

theorem forall₂_of_optTraverse {α β : Type} {l : List α} {f : α → Option β} {bs : List β}
    (h : optTraverse l f = some bs) : List.Forall₂ (fun a b => f a = some b) l bs := by
  induction l generalizing bs with
  | nil => simp at h; subst h; exact .nil
  | cons a as ih =>
    simp only [optTraverse_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hrest : optTraverse as f with
      | none => simp [hfa, hrest] at h
      | some bs' =>
        simp only [hfa, hrest, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        exact .cons hfa (ih hrest)

theorem optTraverse_eq_some {α β : Type} {l : List α} {f : α → Option β} {g : α → β}
    (h : ∀ a ∈ l, f a = some (g a)) : optTraverse l f = some (l.map g) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [optTraverse_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb), Option.bind_some, Option.map_some,
      List.map_cons]

theorem optTraverse_map {α β γ : Type} (l : List α) (g : α → β) (f : β → Option γ) :
    optTraverse (l.map g) f = optTraverse l (fun a => f (g a)) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [ih]

/-- All argument combinations, the first position outermost. -/
def combos {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: xss => xs.flatMap fun x => (combos xss).map (x :: ·)

@[simp] theorem combos_nil {α : Type} : combos ([] : List (List α)) = [[]] := rfl

@[simp] theorem combos_cons {α : Type} (xs : List α) (xss : List (List α)) :
    combos (xs :: xss) = xs.flatMap fun x => (combos xss).map (x :: ·) := rfl

theorem combos_singletons {α : Type} (xs : List α) : combos (xs.map fun x => [x]) = [xs] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Every combination picks one element from each position. -/
theorem forall₂_mem_of_mem_combos {α : Type} :
    ∀ {xss : List (List α)} {vs : List α}, vs ∈ combos xss → List.Forall₂ (· ∈ ·) vs xss
  | [], vs, h => by simp at h; subst h; exact .nil
  | xs :: xss, vs, h => by
    simp only [combos_cons, List.mem_flatMap, List.mem_map] at h
    obtain ⟨x, hx, ws, hws, rfl⟩ := h
    exact .cons hx (forall₂_mem_of_mem_combos hws)

theorem forall₂_exists_left {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {a : α} (ha : a ∈ l₁) : ∃ b ∈ l₂, R a b := by
  induction h with
  | nil => simp at ha
  | @cons a' b' _ _ hab _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b', List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, h⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

theorem forall₂_exists_right {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => simp at hb
  | @cons a' b' _ _ hab _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a', List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, h⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

theorem forall₂_flatMap {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {l₁ : List α} {l₂ : List β} {f : α → List γ} {g : β → List δ}
    (h : List.Forall₂ R l₁ l₂) (hfg : ∀ a b, R a b → List.Forall₂ S (f a) (g b)) :
    List.Forall₂ S (l₁.flatMap f) (l₂.flatMap g) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact List.rel_append (hfg _ _ hab) ih

theorem forall₂_combos {α β : Type} {R : α → β → Prop} :
    ∀ {xss : List (List α)} {yss : List (List β)},
      List.Forall₂ (List.Forall₂ R) xss yss →
      List.Forall₂ (List.Forall₂ R) (combos xss) (combos yss)
  | _, _, .nil => .cons .nil .nil
  | _, _, .cons hxy hrest => by
    simp only [combos_cons]
    refine forall₂_flatMap hxy fun x y hxy' => ?_
    exact List.forall₂_map_left_iff.mpr
      (List.forall₂_map_right_iff.mpr
        ((forall₂_combos hrest).imp fun _ _ h => .cons hxy' h))

namespace Demand

variable {α β γ : Type}

/-- Sequencing. -/
def bind : Demand α → (α → Demand β) → Demand β
  | done a, f => f a
  | need t k, f => need t fun r => bind (k r) f

/-- Post-composition with a function. -/
def map (f : α → β) (q : Demand α) : Demand β := q.bind fun a => done (f a)

/-- Answer every demand with `ev`; `none` if some demand gets no answer. -/
def run (ev : Evaluator) : Demand α → Option α
  | done a => some a
  | need t k =>
    match ev t with
    | some r => run ev (k r)
    | none => none

/-- Concatenate the answers of `f` along a list. -/
def forEach (l : List α) (f : α → Demand (List β)) : Demand (List β) :=
  match l with
  | [] => done []
  | a :: as => (f a).bind fun r => (forEach as f).bind fun rs => done (r ++ rs)

/-- Answer `f` at every element of a list. -/
def traverse (l : List α) (f : α → Demand β) : Demand (List β) :=
  match l with
  | [] => done []
  | a :: as => (f a).bind fun b => (traverse as f).bind fun bs => done (b :: bs)

@[simp] theorem run_done (ev : Evaluator) (a : α) : (done a).run ev = some a := rfl

@[simp] theorem run_need (ev : Evaluator) (t : MAtom) (k : List MAtom → Demand α) :
    (need t k).run ev = (ev t).bind fun r => (k r).run ev := by
  simp only [run]
  cases ev t <;> rfl

@[simp] theorem done_bind (a : α) (f : α → Demand β) : (done a).bind f = f a := rfl

@[simp] theorem need_bind (t : MAtom) (k : List MAtom → Demand α) (f : α → Demand β) :
    (need t k).bind f = need t fun r => (k r).bind f := rfl

@[simp] theorem run_bind (ev : Evaluator) (q : Demand α) (f : α → Demand β) :
    (q.bind f).run ev = (q.run ev).bind fun a => (f a).run ev := by
  induction q with
  | done a => rfl
  | need t k ih =>
    simp only [need_bind, run_need, ih]
    cases ev t <;> rfl

@[simp] theorem run_map (ev : Evaluator) (f : α → β) (q : Demand α) :
    (q.map f).run ev = (q.run ev).map f := by
  simp only [map, run_bind, run_done]
  cases q.run ev <;> rfl

@[simp] theorem run_forEach (ev : Evaluator) (l : List α) (f : α → Demand (List β)) :
    (forEach l f).run ev = optFlatMap l fun a => (f a).run ev := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [forEach, run_bind, run_done, ih, optFlatMap_cons]
    cases (f a).run ev with
    | none => rfl
    | some r => cases optFlatMap as (fun a => (f a).run ev) <;> rfl

@[simp] theorem run_traverse (ev : Evaluator) (l : List α) (f : α → Demand β) :
    (traverse l f).run ev = optTraverse l fun a => (f a).run ev := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [traverse, run_bind, run_done, ih, optTraverse_cons]
    cases (f a).run ev with
    | none => rfl
    | some r => cases optTraverse as (fun a => (f a).run ev) <;> rfl

theorem bind_map (q : Demand α) (f : α → β) (g : β → Demand γ) :
    (q.map f).bind g = q.bind fun a => g (f a) := by
  induction q with
  | done a => rfl
  | need t k ih => simp only [map, need_bind] at ih ⊢; congr 1; funext r; exact ih r

/-- Running is monotone in the evaluator. -/
theorem run_mono {ev ev' : Evaluator} (hext : ev.Extends ev') {q : Demand α} {a : α}
    (h : q.run ev = some a) : q.run ev' = some a := by
  induction q with
  | done b => exact h
  | need t k ih =>
    simp only [run_need] at h ⊢
    cases hev : ev t with
    | none => simp [hev] at h
    | some r =>
      simp only [hev, Option.bind_some] at h
      rw [hext t r hev]
      exact ih r h

/-- Running is continuous: a run against the limit of an increasing chain of
evaluators is already a run against some member of the chain. -/
theorem run_continuous {evs : ℕ → Evaluator} (chain : ∀ n, (evs n).Extends (evs (n + 1)))
    {ev : Evaluator} (hlim : ∀ t r, ev t = some r → ∃ n, evs n t = some r)
    {q : Demand α} {a : α} (h : q.run ev = some a) : ∃ n, q.run (evs n) = some a := by
  have le : ∀ {n m}, n ≤ m → (evs n).Extends (evs m) := by
    intro n m hnm
    induction hnm with
    | refl => exact Evaluator.Extends.refl _
    | step _ ih => exact ih.trans (chain _)
  induction q with
  | done b => exact ⟨0, h⟩
  | need t k ih =>
    simp only [run_need] at h
    cases hev : ev t with
    | none => simp [hev] at h
    | some r =>
      simp only [hev, Option.bind_some] at h
      obtain ⟨n₁, h₁⟩ := ih r h
      obtain ⟨n₂, h₂⟩ := hlim t r hev
      refine ⟨max n₁ n₂, ?_⟩
      simp only [run_need, le (le_max_right n₁ n₂) t r h₂, Option.bind_some]
      exact run_mono (le (le_max_left n₁ n₂)) h₁

/-- `u` is demanded when `q` runs against `ev`: either the first demand, or a
demand of the continuation after `ev` answered the first one. -/
inductive Asks (ev : Evaluator) : Demand α → MAtom → Prop where
  | here {t : MAtom} {k : List MAtom → Demand α} : Asks ev (need t k) t
  | there {t u : MAtom} {k : List MAtom → Demand α} {r : List MAtom} :
      ev t = some r → Asks ev (k r) u → Asks ev (need t k) u

theorem Asks.mono {ev ev' : Evaluator} (hext : ev.Extends ev') {q : Demand α} {u : MAtom}
    (h : Asks ev q u) : Asks ev' q u := by
  induction h with
  | here => exact .here
  | there hr _ ih => exact .there (hext _ _ hr) ih

/-- The terms demanded when `q` runs against `ev`, in order, up to the first
unanswered demand. -/
def askList (ev : Evaluator) : Demand α → List MAtom
  | done _ => []
  | need t k =>
    t :: match ev t with
      | some r => askList ev (k r)
      | none => []

theorem Asks.mem_askList {ev : Evaluator} {q : Demand α} {u : MAtom} (h : Asks ev q u) :
    u ∈ askList ev q := by
  induction h with
  | here => simp [askList]
  | there hr _ ih => simp [askList, hr, ih]

/-- Along a converged run, a demand made with a larger evaluator is already
made, and answered, by the smaller one. -/
theorem Asks.of_run {ev ev' : Evaluator} (hext : ev.Extends ev') {q : Demand α} {a : α}
    (hrun : q.run ev = some a) {u : MAtom} (h : Asks ev' q u) :
    Asks ev q u ∧ ∃ r, ev u = some r := by
  induction h with
  | @here t k =>
    simp only [run_need] at hrun
    cases ht : ev t with
    | none => simp [ht] at hrun
    | some r => exact ⟨.here, r, rfl⟩
  | @there t u k r hr _ ih =>
    simp only [run_need] at hrun
    cases ht : ev t with
    | none => simp [ht] at hrun
    | some r' =>
      have : r' = r := by
        have := hext t r' ht
        rw [hr] at this
        exact (Option.some.inj this).symm
      subst this
      simp only [ht, Option.bind_some] at hrun
      obtain ⟨hask, hu⟩ := ih hrun
      exact ⟨.there ht hask, hu⟩

/-- Two demand trees that ask `Q`-related terms, continue `Ans`-related replies
in related ways, and finish with `A`-related answers. -/
inductive Rel (Q : MAtom → MAtom → Prop) (Ans : List MAtom → List MAtom → Prop)
    (A : α → β → Prop) : Demand α → Demand β → Prop where
  | done {a : α} {b : β} : A a b → Rel Q Ans A (done a) (done b)
  | need {t u : MAtom} {k : List MAtom → Demand α}
      {k' : List MAtom → Demand β} :
      Q t u → (∀ r s, Ans r s → Rel Q Ans A (k r) (k' s)) →
      Rel Q Ans A (need t k) (need u k')

namespace Rel

variable {Q : MAtom → MAtom → Prop} {Ans : List MAtom → List MAtom → Prop}

/-- Transport of runs along related demand trees. -/
theorem run {A : α → β → Prop} {q₁ : Demand α} {q₂ : Demand β} {ev₁ ev₂ : Evaluator}
    (hev : ∀ t u r, Q t u → ev₁ t = some r → ∃ s, ev₂ u = some s ∧ Ans r s)
    (h : Rel Q Ans A q₁ q₂) {a : α} (h₁ : q₁.run ev₁ = some a) :
    ∃ b, q₂.run ev₂ = some b ∧ A a b := by
  induction h with
  | done hab => simp only [run_done, Option.some.injEq] at h₁; subst h₁; exact ⟨_, rfl, hab⟩
  | @need t u k k' htu _ ih =>
    simp only [run_need] at h₁ ⊢
    cases h1t : ev₁ t with
    | none => simp [h1t] at h₁
    | some r =>
      simp only [h1t, Option.bind_some] at h₁
      obtain ⟨s, hs, hrs⟩ := hev t u r htu h1t
      simp only [hs, Option.bind_some]
      exact ih r s hrs h₁

/-- Transport of runs, needing the evaluator correspondence only on the terms
the two runs actually demand. -/
theorem run_asks {A : α → β → Prop} {q₁ : Demand α} {q₂ : Demand β} {ev₁ ev₂ : Evaluator}
    (h : Rel Q Ans A q₁ q₂)
    (hev : ∀ t u r, Q t u → Asks ev₁ q₁ t → Asks ev₂ q₂ u → ev₁ t = some r →
      ∃ s, ev₂ u = some s ∧ Ans r s)
    {a : α} (h₁ : q₁.run ev₁ = some a) : ∃ b, q₂.run ev₂ = some b ∧ A a b := by
  induction h with
  | done hab => simp only [run_done, Option.some.injEq] at h₁; subst h₁; exact ⟨_, rfl, hab⟩
  | @need t u k k' htu _ ih =>
    simp only [run_need] at h₁ ⊢
    cases h1t : ev₁ t with
    | none => simp [h1t] at h₁
    | some r =>
      simp only [h1t, Option.bind_some] at h₁
      obtain ⟨s, hs, hrs⟩ := hev t u r htu .here .here h1t
      simp only [hs, Option.bind_some]
      exact ih r s hrs (fun t' u' r' hq h₁' h₂' => hev t' u' r' hq (.there h1t h₁') (.there hs h₂'))
        h₁

theorem bind {A : α → β → Prop} {B : γ → δ → Prop} {q₁ : Demand α} {q₂ : Demand β}
    {f : α → Demand γ} {g : β → Demand δ} (h : Rel Q Ans A q₁ q₂)
    (hfg : ∀ a b, A a b → Rel Q Ans B (f a) (g b)) : Rel Q Ans B (q₁.bind f) (q₂.bind g) := by
  induction h with
  | done hab => exact hfg _ _ hab
  | need htu _ ih => exact .need htu fun r s hrs => ih r s hrs

theorem map {A : α → β → Prop} {B : γ → δ → Prop} {q₁ : Demand α} {q₂ : Demand β}
    {f : α → γ} {g : β → δ} (h : Rel Q Ans A q₁ q₂) (hfg : ∀ a b, A a b → B (f a) (g b)) :
    Rel Q Ans B (q₁.map f) (q₂.map g) :=
  h.bind fun a b hab => .done (hfg a b hab)

theorem imp {A B : α → β → Prop} {q₁ : Demand α} {q₂ : Demand β} (h : Rel Q Ans A q₁ q₂)
    (hAB : ∀ a b, A a b → B a b) : Rel Q Ans B q₁ q₂ := by
  induction h with
  | done hab => exact .done (hAB _ _ hab)
  | need htu _ ih => exact .need htu fun r s hrs => ih r s hrs

theorem flip {A : α → β → Prop} {q₁ : Demand α} {q₂ : Demand β} (h : Rel Q Ans A q₁ q₂) :
    Rel (fun u t => Q t u) (fun s r => Ans r s) (fun b a => A a b) q₂ q₁ := by
  induction h with
  | done hab => exact .done hab
  | need htu _ ih => exact .need htu fun s r hrs => ih r s hrs

theorem forEach {R : α → β → Prop} {S : γ → δ → Prop} {l₁ : List α} {l₂ : List β}
    {f : α → Demand (List γ)} {g : β → Demand (List δ)} (hl : List.Forall₂ R l₁ l₂)
    (hfg : ∀ a b, R a b → Rel Q Ans (List.Forall₂ S) (f a) (g b)) :
    Rel Q Ans (List.Forall₂ S) (Demand.forEach l₁ f) (Demand.forEach l₂ g) := by
  induction hl with
  | nil => exact .done .nil
  | cons hab _ ih =>
    exact (hfg _ _ hab).bind fun r s hrs => ih.bind fun rs ss hrss =>
      .done (List.rel_append hrs hrss)

theorem traverse {R : α → β → Prop} {B : γ → δ → Prop} {l₁ : List α} {l₂ : List β}
    {f : α → Demand γ} {g : β → Demand δ} (hl : List.Forall₂ R l₁ l₂)
    (hfg : ∀ a b, R a b → Rel Q Ans B (f a) (g b)) :
    Rel Q Ans (List.Forall₂ B) (Demand.traverse l₁ f) (Demand.traverse l₂ g) := by
  induction hl with
  | nil => exact .done .nil
  | cons hab _ ih =>
    exact (hfg _ _ hab).bind fun r s hrs => ih.bind fun rs ss hrss => .done (.cons hrs hrss)

end Rel

end Demand

end Mettapedia.Languages.MeTTa.HE.EvaluatedValues
