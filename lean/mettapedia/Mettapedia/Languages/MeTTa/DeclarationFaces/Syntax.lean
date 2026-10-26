import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation
import Mettapedia.Logic.Relation.Normalization

/-!
# The first-order fragment of MeTTa: terms, equations and their steps

A MeTTa program of the first-order fragment is a list of equations `(= lhs rhs)` between terms
built from variables `$x` and symbols applied to arguments. A bare symbol is a symbol applied to
no argument. The terms carry no types: as in MeTTa, typing is a separate judgment
(`DeclarationFaces.Sorting`).

* `Tm S` are the terms over symbols `S`, `Tm.subst` instantiates their variables, and
  `Tm.matchTm` matches a pattern against a term, returning the bindings.
* `RootStep P s t`: `t` is the right side of an equation of `P` instantiated where its left side,
  instantiated the same way, is `s`. This is MeTTa's equation application at one call.
* `Step P`: a root step at one argument position, at any depth. Every evaluation order is a
  choice among these steps.
* `rootResults P s`: the right sides of all equations whose left side matches `s`, in program
  order: MeTTa's one-step evaluation of a call, read as a multiset. When it is empty, MeTTa keeps
  `s` as inert data.
* `IsValue P`: a term built only from symbols that head no equation: constructor data.

Matching agrees with instantiation (`matchTm_sound`, `matchTm_complete`), so the executable
results are exactly the root steps when left sides are linear (`mem_rootResults_iff`).

Positive examples: `(add Z $n)` matches `(add Z (S Z))`, binding `$n`; a value takes no step.
Negative examples: `(add Z $n)` does not match `(add (S Z) Z)`; a left side whose head is a
variable would rewrite a value, so values are normal only when every left side is headed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces

universe u

/-- A term of the first-order fragment: a variable `$x`, or a symbol applied to a list of
arguments. The bare symbol `Z` is `app Z []`. -/
inductive Tm (S : Type u) where
  | var (name : String)
  | app (head : S) (args : List (Tm S))
  deriving Repr

namespace Tm

variable {S : Type u}

/-- Induction on terms with a hypothesis for every argument of an application. -/
@[elab_as_elim]
theorem induction' {motive : Tm S → Prop} (var : ∀ name, motive (.var name))
    (app : ∀ head args, (∀ a ∈ args, motive a) → motive (.app head args)) (t : Tm S) :
    motive t :=
  Tm.rec (motive_1 := motive) (motive_2 := fun args => ∀ a ∈ args, motive a) var
    (fun head args ih => app head args ih) (fun _ member => absurd member List.not_mem_nil)
    (fun first rest hFirst hRest a member => by
      rcases List.mem_cons.mp member with same | later
      · exact same ▸ hFirst
      · exact hRest a later) t

mutual
/-- Decidable equality of terms. -/
def decEq [DecidableEq S] : (s t : Tm S) → Decidable (s = t)
  | .var x, .var y =>
      if h : x = y then isTrue (h ▸ rfl) else isFalse (fun same => h (Tm.var.inj same))
  | .var _, .app _ _ => isFalse (fun same => by cases same)
  | .app _ _, .var _ => isFalse (fun same => by cases same)
  | .app f as, .app g bs =>
      if hf : f = g then
        match decEqList as bs with
        | isTrue ha => isTrue (hf ▸ ha ▸ rfl)
        | isFalse ha => isFalse (fun same => ha (Tm.app.inj same).2)
      else isFalse (fun same => hf (Tm.app.inj same).1)
/-- Decidable equality of lists of terms. -/
def decEqList [DecidableEq S] : (as bs : List (Tm S)) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun same => by cases same)
  | _ :: _, [] => isFalse (fun same => by cases same)
  | a :: as, b :: bs =>
      match decEq a b with
      | isTrue hab =>
          match decEqList as bs with
          | isTrue hrest => isTrue (hab ▸ hrest ▸ rfl)
          | isFalse hrest => isFalse (fun same => hrest (List.cons.inj same).2)
      | isFalse hab => isFalse (fun same => hab (List.cons.inj same).1)
end

instance [DecidableEq S] : DecidableEq (Tm S) := decEq

/-- The head symbol of an application. -/
def head? : Tm S → Option S
  | .var _ => none
  | .app head _ => some head

mutual
/-- The variables of a term, in order of occurrence, with repetitions. -/
def vars : Tm S → List String
  | .var name => [name]
  | .app _ args => varsList args
/-- The variables of a list of terms. -/
def varsList : List (Tm S) → List String
  | [] => []
  | a :: as => vars a ++ varsList as
end

theorem varsList_eq (args : List (Tm S)) : varsList args = args.flatMap vars := by
  induction args with
  | nil => rfl
  | cons a as ih => simp [varsList, ih]

@[simp] theorem vars_var (name : String) : (Tm.var name : Tm S).vars = [name] := by
  simp [vars]

@[simp] theorem vars_app (head : S) (args : List (Tm S)) :
    (Tm.app head args).vars = args.flatMap vars := by
  simp [vars, varsList_eq]

/-- A term without variables. -/
def Closed (t : Tm S) : Prop := t.vars = []

/-- A pattern in which no variable occurs twice. -/
def Linear (t : Tm S) : Prop := t.vars.Nodup

mutual
/-- Instantiate every variable. -/
def subst (σ : String → Tm S) : Tm S → Tm S
  | .var name => σ name
  | .app head args => .app head (substList σ args)
/-- Instantiate every variable of a list of terms. -/
def substList (σ : String → Tm S) : List (Tm S) → List (Tm S)
  | [] => []
  | a :: as => subst σ a :: substList σ as
end

theorem substList_eq (σ : String → Tm S) (args : List (Tm S)) :
    substList σ args = args.map (subst σ) := by
  induction args with
  | nil => rfl
  | cons a as ih => simp [substList, ih]

@[simp] theorem subst_var (σ : String → Tm S) (name : String) :
    (Tm.var name).subst σ = σ name := by
  simp [subst]

@[simp] theorem subst_app (σ : String → Tm S) (head : S) (args : List (Tm S)) :
    (Tm.app head args).subst σ = .app head (args.map (subst σ)) := by
  simp [subst, substList_eq]

/-- Instantiation reads only the variables of the term. -/
theorem subst_congr {σ τ : String → Tm S} :
    ∀ t : Tm S, (∀ x ∈ t.vars, σ x = τ x) → t.subst σ = t.subst τ := by
  intro t
  induction t using Tm.induction' with
  | var name => intro agree; simpa using agree name (by simp)
  | app head args ih =>
      intro agree
      simp only [subst_app, app.injEq, true_and]
      apply List.map_congr_left
      intro a member
      exact ih a member fun x hx => agree x (by simpa using ⟨a, member, hx⟩)

/-- The identity instantiation. -/
theorem subst_id : ∀ t : Tm S, t.subst Tm.var = t := by
  intro t
  induction t using Tm.induction' with
  | var name => rfl
  | app head args ih =>
      simp only [subst_app, app.injEq, true_and]
      conv_rhs => rw [← List.map_id args]
      exact List.map_congr_left ih

/-- Instantiating twice is instantiating once by the composite. -/
theorem subst_subst (σ τ : String → Tm S) :
    ∀ t : Tm S, (t.subst σ).subst τ = t.subst (fun x => (σ x).subst τ) := by
  intro t
  induction t using Tm.induction' with
  | var name => rfl
  | app head args ih =>
      simp only [subst_app, List.map_map, app.injEq, true_and]
      exact List.map_congr_left fun a member => ih a member

/-- A closed term is its own instance. -/
theorem subst_closed {t : Tm S} (closed : t.Closed) (σ : String → Tm S) : t.subst σ = t := by
  rw [subst_congr (τ := Tm.var) t (fun x hx => by simp [Closed] at closed; simp [closed] at hx),
    subst_id]

/-- The variables of an instance are the variables of the instantiating terms. -/
theorem vars_subst (σ : String → Tm S) :
    ∀ t : Tm S, (t.subst σ).vars = t.vars.flatMap fun x => (σ x).vars := by
  intro t
  induction t using Tm.induction' with
  | var name => simp
  | app head args ih =>
      simp only [subst_app, vars_app, List.flatMap_map, List.flatMap_assoc]
      exact List.flatMap_congr fun a member => ih a member

/-- An instance by closed terms is closed. -/
theorem closed_subst {σ : String → Tm S} (closedImage : ∀ x, (σ x).Closed) (t : Tm S) :
    (t.subst σ).Closed := by
  simp only [Closed, vars_subst, List.flatMap_eq_nil_iff]
  exact fun x _ => closedImage x

/-! ## Bindings and matching -/

/-- The value bound to a variable; an unbound variable stays itself. -/
def lookup : List (String × Tm S) → String → Tm S
  | [], name => .var name
  | (key, value) :: rest, name => if key = name then value else lookup rest name

/-- A substitution agrees with every binding. -/
def Agrees (σ : String → Tm S) (bindings : List (String × Tm S)) : Prop :=
  ∀ pair ∈ bindings, σ pair.1 = pair.2

/-- Looking up a bound variable gives the value every agreeing substitution has there. -/
theorem lookup_of_agrees {σ : String → Tm S} {bindings : List (String × Tm S)}
    (agree : Agrees σ bindings) {name : String} (bound : name ∈ bindings.map Prod.fst) :
    lookup bindings name = σ name := by
  induction bindings with
  | nil => simp at bound
  | cons pair rest ih =>
      obtain ⟨key, value⟩ := pair
      simp only [lookup]
      by_cases same : key = name
      · subst same
        simpa using (agree (key, value) List.mem_cons_self).symm
      · simp only [same, if_false]
        simp only [List.map_cons, List.mem_cons] at bound
        rcases bound with h | h
        · exact absurd h.symm same
        · exact ih (fun p member => agree p (by simp [member])) h

/-- With distinct keys, the lookup agrees with every binding. -/
theorem agrees_lookup {bindings : List (String × Tm S)} (distinct : (bindings.map Prod.fst).Nodup) :
    Agrees (lookup bindings) bindings := by
  induction bindings with
  | nil => intro p member; simp at member
  | cons pair rest ih =>
      obtain ⟨key, value⟩ := pair
      simp only [List.map_cons, List.nodup_cons] at distinct
      intro p member
      rcases List.mem_cons.mp member with same | later
      · subst same; simp [lookup]
      · have keyNe : key ≠ p.1 := fun h => distinct.1 (h ▸ List.mem_map_of_mem later)
        simp only [lookup, keyNe, if_false]
        exact ih distinct.2 p later

variable [DecidableEq S]

mutual
/-- Match a pattern against a term: a variable binds the term; an application matches an
application of the same symbol to as many arguments, argument by argument. -/
def matchTm : Tm S → Tm S → Option (List (String × Tm S))
  | .var name, t => some [(name, t)]
  | .app f ps, .app g ts => if f = g then matchList ps ts else none
  | .app _ _, .var _ => none
/-- Match a list of patterns against a list of terms of the same length. -/
def matchList : List (Tm S) → List (Tm S) → Option (List (String × Tm S))
  | [], [] => some []
  | p :: ps, t :: ts =>
      match matchTm p t, matchList ps ts with
      | some first, some rest => some (first ++ rest)
      | _, _ => none
  | [], _ :: _ => none
  | _ :: _, [] => none
end

mutual
/-- **Matching is sound**: its bindings bind exactly the pattern's variables, and every
substitution that agrees with them instantiates the pattern to the term. -/
theorem matchTm_sound : ∀ (p t : Tm S) (bindings : List (String × Tm S)),
    matchTm p t = some bindings →
      bindings.map Prod.fst = p.vars ∧
        ∀ σ : String → Tm S, Agrees σ bindings → p.subst σ = t
  | .var name, t, bindings, h => by
      simp only [matchTm, Option.some.injEq] at h
      subst h
      exact ⟨by simp, fun σ agree => by simpa using agree (name, t) (by simp)⟩
  | .app f ps, .app g ts, bindings, h => by
      simp only [matchTm] at h
      split at h
      · rename_i same
        subst same
        obtain ⟨keys, inst⟩ := matchList_sound ps ts bindings h
        refine ⟨by simpa [varsList_eq] using keys, fun σ agree => ?_⟩
        simp only [subst_app]
        rw [← substList_eq]
        exact congrArg _ (inst σ agree)
      · cases h
  | .app _ _, .var _, bindings, h => by simp [matchTm] at h
/-- Matching of lists is sound. -/
theorem matchList_sound : ∀ (ps ts : List (Tm S)) (bindings : List (String × Tm S)),
    matchList ps ts = some bindings →
      bindings.map Prod.fst = varsList ps ∧
        ∀ σ : String → Tm S, Agrees σ bindings → substList σ ps = ts
  | [], [], bindings, h => by
      simp only [matchList, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun _ _ => rfl⟩
  | p :: ps, t :: ts, bindings, h => by
      simp only [matchList] at h
      split at h
      · rename_i first rest hFirst hRest
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨keys₁, inst₁⟩ := matchTm_sound p t first hFirst
        obtain ⟨keys₂, inst₂⟩ := matchList_sound ps ts rest hRest
        refine ⟨by simp [varsList, keys₁, keys₂], fun σ agree => ?_⟩
        simp only [substList]
        rw [inst₁ σ (fun q member => agree q (by simp [member])),
          inst₂ σ (fun q member => agree q (by simp [member]))]
      · cases h
  | [], _ :: _, bindings, h => by simp [matchList] at h
  | _ :: _, [], bindings, h => by simp [matchList] at h
end

mutual
/-- **Matching is complete**: every instance of a pattern matches it, with bindings that agree
with the instantiating substitution. -/
theorem matchTm_complete : ∀ (p : Tm S) (σ : String → Tm S),
    ∃ bindings, matchTm p (p.subst σ) = some bindings ∧ Agrees σ bindings
  | .var name, σ => ⟨[(name, σ name)], by simp [matchTm], by simp [Agrees]⟩
  | .app f ps, σ => by
      obtain ⟨bindings, h, agree⟩ := matchList_complete ps σ
      refine ⟨bindings, ?_, agree⟩
      simp only [subst, matchTm, if_true]
      exact h
/-- Matching of lists is complete. -/
theorem matchList_complete : ∀ (ps : List (Tm S)) (σ : String → Tm S),
    ∃ bindings, matchList ps (substList σ ps) = some bindings ∧ Agrees σ bindings
  | [], σ => ⟨[], by simp [matchList, substList], by simp [Agrees]⟩
  | p :: ps, σ => by
      obtain ⟨first, h₁, agree₁⟩ := matchTm_complete p σ
      obtain ⟨rest, h₂, agree₂⟩ := matchList_complete ps σ
      refine ⟨first ++ rest, ?_, ?_⟩
      · simp only [substList, matchList, h₁, h₂]
      · intro pair member
        rcases List.mem_append.mp member with m | m
        · exact agree₁ pair m
        · exact agree₂ pair m
end

/-- A term matches a pattern exactly when it is an instance of it, for a linear pattern. -/
theorem matchTm_isSome_iff {p t : Tm S} (linear : p.Linear) :
    (matchTm p t).isSome ↔ ∃ σ, p.subst σ = t := by
  constructor
  · intro h
    obtain ⟨bindings, hb⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨keys, inst⟩ := matchTm_sound p t bindings hb
    exact ⟨lookup bindings, inst _ (agrees_lookup (by rw [keys]; exact linear))⟩
  · rintro ⟨σ, rfl⟩
    obtain ⟨bindings, h, _⟩ := matchTm_complete p σ
    simp [h]

end Tm

open Tm

/-! ## Equations, programs and steps -/

/-- An equation `(= lhs rhs)`. -/
structure Equation (S : Type u) where
  lhs : Tm S
  rhs : Tm S
  deriving Repr, DecidableEq

/-- A program: its equations. Their order carries no meaning for the steps. -/
abbrev Program (S : Type u) := List (Equation S)

variable {S : Type u}

/-- Some equation of the program has a left side headed by the symbol. -/
def Program.Defines (P : Program S) (f : S) : Prop := ∃ e ∈ P, e.lhs.head? = some f

/-- Every left side is an application of a symbol. -/
def Program.Headed (P : Program S) : Prop := ∀ e ∈ P, ∃ f args, e.lhs = .app f args

/-- **A root step**: an instance of an equation, read from left to right. -/
inductive RootStep (P : Program S) : Tm S → Tm S → Prop where
  | rule {e : Equation S} (σ : String → Tm S) : e ∈ P → RootStep P (e.lhs.subst σ) (e.rhs.subst σ)

/-- **A step**: a root step at one argument position, at any depth. -/
inductive Step (P : Program S) : Tm S → Tm S → Prop where
  | root {s t : Tm S} : RootStep P s t → Step P s t
  | arg (head : S) (args : List (Tm S)) (i : Nat) (lt : i < args.length) {t : Tm S} :
      Step P args[i] t → Step P (.app head args) (.app head (args.set i t))

/-- **Constructor data**: built only from symbols that head no equation. -/
inductive IsValue (P : Program S) : Tm S → Prop where
  | app {c : S} {args : List (Tm S)} : ¬ P.Defines c → (∀ a ∈ args, IsValue P a) →
      IsValue P (.app c args)

/-- An immediate argument of a term. -/
inductive Sub : Tm S → Tm S → Prop where
  | arg (head : S) {args : List (Tm S)} {a : Tm S} : a ∈ args → Sub (.app head args) a

open Mettapedia.Logic.Relation (IsNormal)

/-- A root step is an instance of an equation of the program. -/
theorem RootStep.exists_rule {P : Program S} {s t : Tm S} (step : RootStep P s t) :
    ∃ e ∈ P, ∃ σ : String → Tm S, s = e.lhs.subst σ ∧ t = e.rhs.subst σ := by
  cases step with
  | @rule e σ member => exact ⟨e, member, σ, rfl, rfl⟩

/-- A root step at a headed program starts at an application of a defined symbol. -/
theorem RootStep.defines_head {P : Program S} (headed : P.Headed) {s t : Tm S}
    (step : RootStep P s t) : ∃ f args, s = .app f args ∧ P.Defines f := by
  cases step with
  | @rule e σ member =>
      obtain ⟨f, args, hlhs⟩ := headed e member
      exact ⟨f, args.map (subst σ), by simp [hlhs], e, member, by simp [hlhs, head?]⟩

/-- **Values are normal** at a headed program. -/
theorem IsValue.normal {P : Program S} (headed : P.Headed) :
    ∀ {v : Tm S}, IsValue P v → IsNormal (Step P) v := by
  intro v value
  induction v using Tm.induction' with
  | var name => cases value
  | app c args ih =>
      cases value with
      | app undefined children =>
          intro target step
          cases step with
          | root root =>
              obtain ⟨f, args', same, defined⟩ := root.defines_head headed
              cases same
              exact undefined defined
          | arg _ _ i lt inner =>
              exact ih _ (List.getElem_mem lt) (children _ (List.getElem_mem lt)) _ inner

/-- Steps keep the head of an application whose head is not defined. -/
theorem Step.app_of_not_defines {P : Program S} (headed : P.Headed) {c : S} {args : List (Tm S)}
    (undefined : ¬ P.Defines c) {t : Tm S} (step : Step P (.app c args) t) :
    ∃ i, ∃ lt : i < args.length, ∃ a, Step P args[i] a ∧ t = .app c (args.set i a) := by
  cases step with
  | root root =>
      obtain ⟨f, args', same, defined⟩ := root.defines_head headed
      cases same
      exact absurd defined undefined
  | arg _ _ i lt inner => exact ⟨i, lt, _, inner, rfl⟩

/-! ## MeTTa's one-step evaluation of a call -/

variable [DecidableEq S]

/-- **The results of one call**: the right side of every equation whose left side matches the
term, instantiated by the match, in program order. MeTTa reads them as a multiset; when there
are none, MeTTa keeps the term as inert data. -/
def rootResults (P : Program S) (t : Tm S) : List (Tm S) :=
  P.filterMap fun e => (matchTm e.lhs t).map fun bindings => e.rhs.subst (lookup bindings)

/-- Every left side is linear. -/
def Program.LeftLinear (P : Program S) : Prop := ∀ e ∈ P, e.lhs.Linear

/-- Every variable of a right side occurs on its left side. -/
def Program.RightBound (P : Program S) : Prop := ∀ e ∈ P, ∀ x ∈ e.rhs.vars, x ∈ e.lhs.vars

/-- **The executable results are exactly the root steps**, for linear left sides whose right
sides use only their variables. -/
theorem mem_rootResults_iff {P : Program S} (linear : P.LeftLinear) (bound : P.RightBound)
    {s t : Tm S} : t ∈ rootResults P s ↔ RootStep P s t := by
  constructor
  · intro member
    simp only [rootResults, List.mem_filterMap, Option.map_eq_some_iff] at member
    obtain ⟨e, eMember, bindings, hMatch, rfl⟩ := member
    obtain ⟨keys, inst⟩ := matchTm_sound e.lhs s bindings hMatch
    have agree := agrees_lookup (S := S) (bindings := bindings) (by rw [keys]; exact linear e eMember)
    rw [← inst _ agree]
    exact .rule _ eMember
  · intro step
    cases step with
    | @rule e σ eMember =>
        obtain ⟨bindings, hMatch, agree⟩ := matchTm_complete e.lhs σ
        obtain ⟨keys, _⟩ := matchTm_sound e.lhs _ bindings hMatch
        simp only [rootResults, List.mem_filterMap, Option.map_eq_some_iff]
        refine ⟨e, eMember, bindings, hMatch, ?_⟩
        apply subst_congr
        intro x hx
        exact lookup_of_agrees agree (keys ▸ bound e eMember x hx)

/-! ## Examples -/

namespace Examples

/-- `(add Z $n)`. -/
def addZero : Tm String := .app "add" [.app "Z" [], .var "n"]

/-- Positive example: `(add Z (S Z))` matches `(add Z $n)`, binding `$n` to `(S Z)`. -/
example : matchTm addZero (.app "add" [.app "Z" [], .app "S" [.app "Z" []]]) =
    some [("n", .app "S" [.app "Z" []])] := by decide

/-- Negative example: `(add (S Z) Z)` does not match `(add Z $n)`. -/
example : matchTm addZero (.app "add" [.app "S" [.app "Z" []], .app "Z" []]) = none := by decide

/-- The two equations of addition. -/
def addRules : Program String :=
  [⟨addZero, .var "n"⟩,
   ⟨.app "add" [.app "S" [.var "m"], .var "n"], .app "S" [.app "add" [.var "m", .var "n"]]⟩]

/-- Positive example: one call of `add` has one result. -/
example : rootResults addRules (.app "add" [.app "S" [.app "Z" []], .app "Z" []]) =
    [.app "S" [.app "add" [.app "Z" [], .app "Z" []]]] := by decide

/-- Negative example: a call no equation matches has no result; MeTTa keeps it as data. -/
example : rootResults addRules (.app "add" [.app "K" [], .app "Z" []]) = [] := by decide

/-- A program with a variable for a left side. -/
def anything : Program String := [⟨.var "x", .app "K" []⟩]

/-- Negative example: with a variable for a left side, the constructor `Z` takes a step. -/
example : Step anything (.app "Z" []) (.app "K" []) := by
  have := RootStep.rule (P := anything) (e := ⟨.var "x", .app "K" []⟩) (fun _ => .app "Z" [])
    (by simp [anything])
  simpa using Step.root this

end Examples

end Mettapedia.Languages.MeTTa.DeclarationFaces
