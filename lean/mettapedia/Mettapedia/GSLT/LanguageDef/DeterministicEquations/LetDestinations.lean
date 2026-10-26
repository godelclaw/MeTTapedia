import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic

/-!
# Let destinations: value first and destination first

PeTTa translates `(let p v b)` into the goals `p = V, Gv, Gb`, where `V` is the
output skeleton of `v` and `Gv` its goals: the pattern unifies with the value's
skeleton before the value is computed.  A constructor's skeleton is built at
translation time, a call's output is the clause head's output skeleton, unified
when the call runs and before the callee's body, and an `if` unifies its branch's
skeleton with its output once the condition is computed.  A clash prunes the work
beneath it.  CeTTa's prepared machine computes the value first and matches the
pattern against it afterwards.  The two agree when the value ends; when it does
not, the destination-first reading may still fail at a clash.

This file states both readings over first-order terms and proves that they agree
on lets that carry destination evidence.

* Values are ground: atoms and cons cells ending in `nil`, as PeTTa's Prolog
  lists represent expressions.  Patterns are variables, atoms, `nil` and cons
  cells of patterns.  A program is a list of equations `f p = b` with one
  argument pattern, several arguments being one tuple; a call selects the first
  equation whose pattern matches its argument, which is Prolog's clause selection
  when at most one equation matches.  A host primitive is a partial function on
  values, and an `if` takes its first branch on the atom `True`.
* `evalV` is the value-first reading: call by value, a let matches its pattern
  against the computed value.
* `evalD` is the destination-first reading, stated by the values the
  unifications met so far leave possible: every evaluation carries the set of
  values its destination admits, and fails before computing anything when no
  value of its static skeleton (`Skel`) lies in that set.  The parts of a cons
  cell are refined by each other's skeleton and by the value already computed; a
  let's value is admitted when its pattern matches it and the body's skeleton can
  still meet the destination under the match; a call's body inherits the
  destination, which is the head unification; an `if` passes it to the branch it
  takes.  The goals of the translation themselves are not modelled here.
* `Certain W R t d`: the destination part `d` certainly meets every value `t`
  reaches.  A constructor spells the part's head, an atom matches it, and any
  other value faces a variable of `R`, the variables the let's pattern binds.
  Calls are judged per equation of the callee through the certificate `W`.
* `Admits W R t d`: `t` may be computed before it meets `d`: it certainly meets
  it, or what a clash could prune makes no call, judged per branch of an `if` and
  per equation of a call.
* `LetsAdmitted P sc t`: every let in `t` makes no call in its value, or has a
  linear pattern and a consistent certificate admitting its value.

Main results:
* `evalD_of_evalV`: when the value-first reading ends, the destination-first
  reading ends the same way, for every term.
* `evalV_ends_of_evalD`: on a well-scoped term of a program whose lets are all
  admitted, with an admitted destination, the value-first reading ends wherever
  the destination-first reading does.
* `destination_square`: on well-scoped terms of a program whose lets are all
  admitted, the two readings end with the same outcomes.

The controls (`LetDestinationsControls`) give the clashes on which the two
readings differ and lets the evidence admits.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.LetDestinations

/-! ## Terms, values and patterns -/

/-- Values: atoms, and cons cells ending in `nil`. -/
inductive Val where
  | atom (name : String)
  | nil
  | cons (head tail : Val)
  deriving DecidableEq, Repr

/-- Terms.  `call` applies a program relation and `prim` a host primitive to one
argument; `letp p v b` binds the pattern `p` to the value of `v` in `b`. -/
inductive Tm where
  | var (name : String)
  | atom (name : String)
  | nil
  | cons (head tail : Tm)
  | call (f : String) (arg : Tm)
  | prim (f : String) (arg : Tm)
  | ite (cond yes no : Tm)
  | letp (pattern value body : Tm)
  deriving DecidableEq, Repr

/-- Bindings of variables to values, the newest first. -/
abbrev Env := List (String × Val)

/-- The value a variable is bound to. -/
def lookup : Env → String → Option Val
  | [], _ => none
  | (y, v) :: env, x => if y = x then some v else lookup env x

/-- The variables of a pattern, in order, with repetitions. -/
def patVars : Tm → List String
  | .var x => [x]
  | .cons p q => patVars p ++ patVars q
  | _ => []

/-- Terms that are patterns. -/
def IsPat : Tm → Prop
  | .var _ => True
  | .atom _ => True
  | .nil => True
  | .cons p q => IsPat p ∧ IsPat q
  | _ => False

/-- A pattern in which no variable occurs twice. -/
def Linear (p : Tm) : Prop := (patVars p).Nodup

/-- Matching a pattern against a value.  A variable already bound must meet its
value, and an unbound one is bound to what it faces. -/
def matchPat (env : Env) : Tm → Val → Option Env
  | .var x, w =>
    match lookup env x with
    | some v => if v = w then some env else none
    | none => some ((x, w) :: env)
  | .atom a, .atom b => if a = b then some env else none
  | .nil, .nil => some env
  | .cons p q, .cons w₁ w₂ =>
    match matchPat env p w₁ with
    | some env' => matchPat env' q w₂
    | none => none
  | _, _ => none

/-- The values a pattern matches. -/
def MatchSet (env : Env) (p : Tm) : Set Val := {w | ∃ σ, matchPat env p w = some σ}

/-- An equation `head param = body`. -/
structure Equation where
  head : String
  param : Tm
  body : Tm
  deriving DecidableEq, Repr

/-- A program: its equations in order. -/
abbrev Program := List Equation

/-- The first equation of `f` whose pattern matches the argument, with the
match. -/
def select : Program → String → Val → Option (Equation × Env)
  | [], _, _ => none
  | e :: P, f, v =>
    if e.head = f then
      match matchPat [] e.param v with
      | some σ => some (e, σ)
      | none => select P f v
    else select P f v

/-- Host primitives. -/
abbrev Host := String → Val → Option Val

/-- The outcome of an evaluation. -/
inductive Outcome where
  | value (v : Val)
  | failure
  | exhausted
  deriving DecidableEq, Repr

/-- Continue a value; failure and exhaustion pass through. -/
def Outcome.bind : Outcome → (Val → Outcome) → Outcome
  | .value v, k => k v
  | .failure, _ => .failure
  | .exhausted, _ => .exhausted

@[simp] theorem Outcome.bind_value (v : Val) (k : Val → Outcome) :
    (Outcome.value v).bind k = k v := rfl
@[simp] theorem Outcome.bind_failure (k : Val → Outcome) :
    Outcome.failure.bind k = .failure := rfl
@[simp] theorem Outcome.bind_exhausted (k : Val → Outcome) :
    Outcome.exhausted.bind k = .exhausted := rfl

/-! ## The value-first reading -/

section Readings

variable (P : Program) (H : Host)

/-- One step of the value-first reading. -/
def stepV (ev : Env → Tm → Outcome) (env : Env) : Tm → Outcome
  | .var x =>
    match lookup env x with
    | some v => .value v
    | none => .failure
  | .atom a => .value (.atom a)
  | .nil => .value .nil
  | .cons a b =>
    (ev env a).bind fun x => (ev env b).bind fun y => .value (.cons x y)
  | .call f a =>
    (ev env a).bind fun v =>
      match select P f v with
      | some (e, σ) => ev σ e.body
      | none => .failure
  | .prim f a =>
    (ev env a).bind fun v =>
      match H f v with
      | some w => .value w
      | none => .failure
  | .ite c a b =>
    (ev env c).bind fun v => if v = .atom "True" then ev env a else ev env b
  | .letp p v b =>
    (ev env v).bind fun w =>
      match matchPat env p w with
      | some σ => ev σ b
      | none => .failure

/-- The value-first reading with some fuel. -/
def evalV : Nat → Env → Tm → Outcome
  | 0, _, _ => .exhausted
  | n + 1, env, t => stepV P H (evalV n) env t

/-! ## Skeletons and the destination-first reading -/

/-- `u` is a value of the output skeleton of `t` under `env`: a variable is its
value, an atom and `nil` themselves, a cons cell the cells of its parts' values, a
let its body's under some match of its pattern, and a call, a primitive or an
`if` any value. -/
def Skel : Env → Tm → Val → Prop
  | env, .var x, u => lookup env x = some u
  | _, .atom a, u => u = .atom a
  | _, .nil, u => u = .nil
  | env, .cons a b, u => ∃ x y, u = .cons x y ∧ Skel env a x ∧ Skel env b y
  | _, .call _ _, _ => True
  | _, .prim _ _, _ => True
  | _, .ite _ _ _, _ => True
  | env, .letp p _ b, u => ∃ w σ, matchPat env p w = some σ ∧ Skel σ b u

/-- The skeleton of `t` can meet the destination `M`. -/
def SkelMeets (env : Env) (t : Tm) (M : Set Val) : Prop := ∃ u ∈ M, Skel env t u

open Classical in
/-- One step of the destination-first reading, after the skeleton met the
destination. -/
noncomputable def stepD (ev : Env → Tm → Set Val → Outcome) (env : Env) (t : Tm)
    (M : Set Val) : Outcome :=
  match t with
  | .var x =>
    match lookup env x with
    | some v => .value v
    | none => .failure
  | .atom a => .value (.atom a)
  | .nil => .value .nil
  | .cons a b =>
    (ev env a {x | ∃ y, Skel env b y ∧ Val.cons x y ∈ M}).bind fun x =>
      (ev env b {y | Val.cons x y ∈ M}).bind fun y => .value (.cons x y)
  | .call f a =>
    (ev env a Set.univ).bind fun v =>
      match select P f v with
      | some (e, σ) => ev σ e.body M
      | none => .failure
  | .prim f a =>
    (ev env a Set.univ).bind fun v =>
      match H f v with
      | some w => if w ∈ M then .value w else .failure
      | none => .failure
  | .ite c a b =>
    (ev env c Set.univ).bind fun v => if v = .atom "True" then ev env a M else ev env b M
  | .letp p v b =>
    (ev env v {w | ∃ σ, matchPat env p w = some σ ∧ SkelMeets σ b M}).bind fun w =>
      match matchPat env p w with
      | some σ => ev σ b M
      | none => .failure

open Classical in
/-- The destination-first reading with some fuel: an evaluation whose skeleton
cannot meet its destination fails before it computes anything. -/
noncomputable def evalD : Nat → Env → Tm → Set Val → Outcome
  | 0, _, _, _ => .exhausted
  | n + 1, env, t, M =>
    if SkelMeets env t M then stepD P H (evalD n) env t M else .failure

end Readings

/-! ## Destination evidence -/

/-- A destination part certainly matches the literal `t` (an atom or `nil`): it
is a variable of `R`, or the same literal. -/
def CertMatch (R : List String) : Tm → Tm → Prop
  | .var x, _ => x ∈ R
  | .atom a, .atom b => a = b
  | .nil, .nil => True
  | _, _ => False

/-- A certificate: heads entered with a destination part, to be certainly met
(`true`) or admitted (`false`) by each of their equations. -/
abbrev Certificate := List (String × Tm × Bool)

/-- The destination part `d` certainly meets every value `t` reaches. -/
inductive Certain (W : Certificate) (R : List String) : Tm → Tm → Prop
  | recv {t : Tm} {x : String} : x ∈ R → Certain W R t (.var x)
  | atom {a : String} {d : Tm} : CertMatch R d (.atom a) → Certain W R (.atom a) d
  | nil {d : Tm} : CertMatch R d .nil → Certain W R .nil d
  | cons {a b da db : Tm} :
      Certain W R a da → Certain W R b db → Certain W R (.cons a b) (.cons da db)
  | call {f : String} {a d : Tm} : (f, d, true) ∈ W → Certain W R (.call f a) d
  | ite {c a b d : Tm} : Certain W R a d → Certain W R b d → Certain W R (.ite c a b) d
  | letp {p v b d : Tm} : Certain W R b d → Certain W R (.letp p v b) d

/-- Terms that make no call. -/
def CallFree : Tm → Prop
  | .call _ _ => False
  | .cons a b => CallFree a ∧ CallFree b
  | .prim _ a => CallFree a
  | .ite c a b => CallFree c ∧ CallFree a ∧ CallFree b
  | .letp _ v b => CallFree v ∧ CallFree b
  | _ => True

/-- `t` may be computed before it meets the destination part `d`. -/
inductive Admits (W : Certificate) (R : List String) : Tm → Tm → Prop
  | certain {t d : Tm} : Certain W R t d → Admits W R t d
  | callFree {t d : Tm} : CallFree t → Admits W R t d
  | ite {c a b d : Tm} : Admits W R a d → Admits W R b d → Admits W R (.ite c a b) d
  | call {f : String} {a d : Tm} : (f, d, false) ∈ W → Admits W R (.call f a) d

/-- A certificate is consistent when each equation of each head it lists certainly
meets, or admits, the listed destination part. -/
def Consistent (P : Program) (W : Certificate) (R : List String) : Prop :=
  ∀ f d c, (f, d, c) ∈ W → ∀ e ∈ P, e.head = f →
    (c = true → Certain W R e.body d) ∧ (c = false → Admits W R e.body d)

/-- The variables a let's pattern binds, given the variables in scope. -/
def receiving (sc : List String) (p : Tm) : List String :=
  (patVars p).filter (fun x => x ∉ sc)

/-- A let whose value may be computed before its pattern meets it. -/
def LetAdmitted (P : Program) (sc : List String) (p v : Tm) : Prop :=
  CallFree v ∨
    (Linear p ∧ ∃ W, Consistent P W (receiving sc p) ∧ Admits W (receiving sc p) v p)

/-- Every variable of `t` is in scope and every let's pattern is a pattern. -/
def WellScoped : List String → Tm → Prop
  | sc, .var x => x ∈ sc
  | _, .atom _ => True
  | _, .nil => True
  | sc, .cons a b => WellScoped sc a ∧ WellScoped sc b
  | sc, .call _ a => WellScoped sc a
  | sc, .prim _ a => WellScoped sc a
  | sc, .ite c a b => WellScoped sc c ∧ WellScoped sc a ∧ WellScoped sc b
  | sc, .letp p v b => IsPat p ∧ WellScoped sc v ∧ WellScoped (patVars p ++ sc) b

/-- Every let of `t` is admitted. -/
def LetsAdmitted (P : Program) : List String → Tm → Prop
  | _, .var _ => True
  | _, .atom _ => True
  | _, .nil => True
  | sc, .cons a b => LetsAdmitted P sc a ∧ LetsAdmitted P sc b
  | sc, .call _ a => LetsAdmitted P sc a
  | sc, .prim _ a => LetsAdmitted P sc a
  | sc, .ite c a b => LetsAdmitted P sc c ∧ LetsAdmitted P sc a ∧ LetsAdmitted P sc b
  | sc, .letp p v b =>
    LetAdmitted P sc p v ∧ LetsAdmitted P sc v ∧ LetsAdmitted P (patVars p ++ sc) b

/-- Every equation's parameter is a pattern and its body is well scoped with all
its lets admitted. -/
def ProgramAdmitted (P : Program) : Prop :=
  ∀ e ∈ P, IsPat e.param ∧ WellScoped (patVars e.param) e.body ∧
    LetsAdmitted P (patVars e.param) e.body


/-! ## Environments and matching -/

/-- The variables bound in `env` are exactly those of `sc`. -/
def EnvScope (env : Env) (sc : List String) : Prop := ∀ x, (lookup env x).isSome ↔ x ∈ sc

theorem lookup_cons (y x : String) (v : Val) (env : Env) :
    lookup ((y, v) :: env) x = if y = x then some v else lookup env x := rfl

theorem lookup_append_of_not_mem :
    ∀ (ext env : Env) (x : String), (∀ b ∈ ext, b.1 ≠ x) → lookup (ext ++ env) x = lookup env x
  | [], _, _, _ => rfl
  | (y, v) :: ext, env, x, h => by
    have hy : y ≠ x := h (y, v) (List.mem_cons_self ..)
    simp only [List.cons_append, lookup_cons, hy, if_false]
    exact lookup_append_of_not_mem ext env x (fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem matchPat_var_eq {env : Env} {x : String} {w : Val} {σ : Env} :
    matchPat env (.var x) w = some σ ↔
      (lookup env x = some w ∧ σ = env) ∨ (lookup env x = none ∧ σ = (x, w) :: env) := by
  simp only [matchPat]
  cases hx : lookup env x with
  | none => simp [eq_comm]
  | some v =>
    by_cases hv : v = w
    · subst hv
      simp [eq_comm]
    · simp [hv]

theorem matchPat_atom_eq {env : Env} {a : String} {w : Val} {σ : Env} :
    matchPat env (.atom a) w = some σ ↔ w = .atom a ∧ σ = env := by
  cases w with
  | atom b =>
    simp only [matchPat]
    by_cases hab : a = b
    · subst hab
      simp [eq_comm]
    · simp [hab, Ne.symm hab]
  | nil => simp [matchPat]
  | cons _ _ => simp [matchPat]

theorem matchPat_nil_eq {env : Env} {w : Val} {σ : Env} :
    matchPat env .nil w = some σ ↔ w = .nil ∧ σ = env := by
  cases w <;> simp [matchPat, eq_comm]

theorem matchPat_cons_eq {env : Env} {p q : Tm} {w : Val} {σ : Env} :
    matchPat env (.cons p q) w = some σ ↔
      ∃ w₁ w₂ env', w = .cons w₁ w₂ ∧ matchPat env p w₁ = some env' ∧
        matchPat env' q w₂ = some σ := by
  cases w with
  | atom _ => simp [matchPat]
  | nil => simp [matchPat]
  | cons w₁ w₂ =>
    simp only [matchPat]
    constructor
    · intro h
      cases h₁ : matchPat env p w₁ with
      | none => simp [h₁] at h
      | some env' =>
        rw [h₁] at h
        exact ⟨w₁, w₂, env', rfl, h₁, h⟩
    · rintro ⟨w₁', w₂', env', he, h₁, h₂⟩
      cases he
      rw [h₁]
      exact h₂

theorem matchPat_nonpattern {env : Env} {t : Tm} (ht : ¬IsPat t) (w : Val) :
    matchPat env t w = none := by
  cases t with
  | var _ => exact absurd trivial ht
  | atom _ => exact absurd trivial ht
  | nil => exact absurd trivial ht
  | cons p q =>
    cases w <;> simp only [matchPat]
    rename_i w₁ w₂
    simp only [IsPat, not_and_or] at ht
    rcases ht with ht | ht
    · rw [matchPat_nonpattern ht w₁]
    · cases matchPat env p w₁ with
      | none => rfl
      | some env' => exact matchPat_nonpattern ht w₂
  | call _ _ => cases w <;> rfl
  | prim _ _ => cases w <;> rfl
  | ite _ _ _ => cases w <;> rfl
  | letp _ _ _ => cases w <;> rfl

theorem isPat_of_matchPat {env : Env} {t : Tm} {w : Val} {σ : Env}
    (h : matchPat env t w = some σ) : IsPat t := by
  by_contra ht
  rw [matchPat_nonpattern ht] at h
  cases h

/-- A match extends its environment by bindings of the pattern's variables. -/
theorem matchPat_extends : ∀ {p : Tm} {env : Env} {w : Val} {σ : Env},
    matchPat env p w = some σ → ∃ ext : Env, σ = ext ++ env ∧ ∀ b ∈ ext, b.1 ∈ patVars p
  | .var x, env, w, σ, h => by
    rcases matchPat_var_eq.1 h with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨[], rfl, by simp⟩
    · exact ⟨[(x, w)], rfl, by simp [patVars]⟩
  | .atom a, env, w, σ, h => by
    obtain ⟨-, rfl⟩ := matchPat_atom_eq.1 h
    exact ⟨[], rfl, by simp⟩
  | .nil, env, w, σ, h => by
    obtain ⟨-, rfl⟩ := matchPat_nil_eq.1 h
    exact ⟨[], rfl, by simp⟩
  | .cons p q, env, w, σ, h => by
    obtain ⟨w₁, w₂, env', -, h₁, h₂⟩ := matchPat_cons_eq.1 h
    obtain ⟨e₁, rfl, he₁⟩ := matchPat_extends h₁
    obtain ⟨e₂, rfl, he₂⟩ := matchPat_extends h₂
    refine ⟨e₂ ++ e₁, by simp, fun b hb => ?_⟩
    simp only [patVars, List.mem_append]
    rcases List.mem_append.1 hb with hb | hb
    · exact Or.inr (he₂ b hb)
    · exact Or.inl (he₁ b hb)
  | .call _ _, _, _, _, h => absurd (isPat_of_matchPat h) id
  | .prim _ _, _, _, _, h => absurd (isPat_of_matchPat h) id
  | .ite _ _ _, _, _, _, h => absurd (isPat_of_matchPat h) id
  | .letp _ _ _, _, _, _, h => absurd (isPat_of_matchPat h) id

/-- Matching only reads the bindings of the pattern's variables. -/
theorem matchPat_agree {A : List String} : ∀ {p : Tm} {env₁ env₂ : Env} {w : Val} {σ₁ : Env},
    (∀ x ∈ A, lookup env₁ x = lookup env₂ x) → (∀ x ∈ patVars p, x ∈ A) →
    matchPat env₁ p w = some σ₁ →
    ∃ σ₂, matchPat env₂ p w = some σ₂ ∧ ∀ x ∈ A, lookup σ₁ x = lookup σ₂ x
  | .var x, env₁, env₂, w, σ₁, hA, hp, h => by
    have hx : lookup env₁ x = lookup env₂ x := hA x (hp x (by simp [patVars]))
    rcases matchPat_var_eq.1 h with ⟨hw, rfl⟩ | ⟨hn, rfl⟩
    · exact ⟨env₂, matchPat_var_eq.2 (Or.inl ⟨hx ▸ hw, rfl⟩), hA⟩
    · refine ⟨(x, w) :: env₂, matchPat_var_eq.2 (Or.inr ⟨hx ▸ hn, rfl⟩), fun y hy => ?_⟩
      simp only [lookup_cons]
      split
      · rfl
      · exact hA y hy
  | .atom a, env₁, env₂, w, σ₁, hA, _, h => by
    obtain ⟨rfl, rfl⟩ := matchPat_atom_eq.1 h
    exact ⟨env₂, matchPat_atom_eq.2 ⟨rfl, rfl⟩, hA⟩
  | .nil, env₁, env₂, w, σ₁, hA, _, h => by
    obtain ⟨rfl, rfl⟩ := matchPat_nil_eq.1 h
    exact ⟨env₂, matchPat_nil_eq.2 ⟨rfl, rfl⟩, hA⟩
  | .cons p q, env₁, env₂, w, σ₁, hA, hp, h => by
    obtain ⟨w₁, w₂, env', rfl, h₁, h₂⟩ := matchPat_cons_eq.1 h
    obtain ⟨σ', h₁', hσ'⟩ := matchPat_agree hA
      (fun x hx => hp x (List.mem_append_left _ hx)) h₁
    obtain ⟨σ₂, h₂', hσ₂⟩ := matchPat_agree hσ'
      (fun x hx => hp x (List.mem_append_right _ hx)) h₂
    exact ⟨σ₂, matchPat_cons_eq.2 ⟨w₁, w₂, σ', rfl, h₁', h₂'⟩, hσ₂⟩
  | .call _ _, _, _, _, _, _, _, h => absurd (isPat_of_matchPat h) id
  | .prim _ _, _, _, _, _, _, _, h => absurd (isPat_of_matchPat h) id
  | .ite _ _ _, _, _, _, _, _, _, h => absurd (isPat_of_matchPat h) id
  | .letp _ _ _, _, _, _, _, _, _, h => absurd (isPat_of_matchPat h) id

/-- Every pattern matches some value. -/
theorem matchPat_exists : ∀ {p : Tm}, IsPat p → ∀ env : Env, ∃ w σ, matchPat env p w = some σ
  | .var x, _, env => by
    cases hx : lookup env x with
    | none => exact ⟨.nil, _, matchPat_var_eq.2 (Or.inr ⟨hx, rfl⟩)⟩
    | some v => exact ⟨v, env, matchPat_var_eq.2 (Or.inl ⟨hx, rfl⟩)⟩
  | .atom a, _, env => ⟨.atom a, env, matchPat_atom_eq.2 ⟨rfl, rfl⟩⟩
  | .nil, _, env => ⟨.nil, env, matchPat_nil_eq.2 ⟨rfl, rfl⟩⟩
  | .cons p q, hp, env => by
    obtain ⟨w₁, σ₁, h₁⟩ := matchPat_exists hp.1 env
    obtain ⟨w₂, σ₂, h₂⟩ := matchPat_exists hp.2 σ₁
    exact ⟨.cons w₁ w₂, σ₂, matchPat_cons_eq.2 ⟨w₁, w₂, σ₁, rfl, h₁, h₂⟩⟩

theorem matchSet_nonempty {p : Tm} (hp : IsPat p) (env : Env) : (MatchSet env p).Nonempty := by
  obtain ⟨w, σ, h⟩ := matchPat_exists hp env
  exact ⟨w, σ, h⟩

/-- A variable no binding gives a value matches everything. -/
theorem matchSet_var {env : Env} {x : String} (hx : lookup env x = none) :
    MatchSet env (.var x) = Set.univ :=
  Set.eq_univ_of_forall fun _ => ⟨_, matchPat_var_eq.2 (Or.inr ⟨hx, rfl⟩)⟩

/-- A match binds the pattern's variables on top of what was bound. -/
theorem matchPat_scope : ∀ {p : Tm} {env : Env} {w : Val} {σ : Env},
    matchPat env p w = some σ →
    ∀ x, (lookup σ x).isSome ↔ (x ∈ patVars p ∨ (lookup env x).isSome)
  | .var y, env, w, σ, h, x => by
    rcases matchPat_var_eq.1 h with ⟨hw, rfl⟩ | ⟨-, rfl⟩
    · simp only [patVars, List.mem_singleton]
      constructor
      · exact Or.inr
      · rintro (rfl | hx)
        · simp [hw]
        · exact hx
    · simp only [lookup_cons, patVars, List.mem_singleton]
      by_cases hyx : y = x
      · subst hyx
        simp
      · simp [hyx, Ne.symm hyx]
  | .atom a, env, w, σ, h, x => by
    obtain ⟨-, rfl⟩ := matchPat_atom_eq.1 h
    simp [patVars]
  | .nil, env, w, σ, h, x => by
    obtain ⟨-, rfl⟩ := matchPat_nil_eq.1 h
    simp [patVars]
  | .cons p q, env, w, σ, h, x => by
    obtain ⟨w₁, w₂, env', -, h₁, h₂⟩ := matchPat_cons_eq.1 h
    rw [matchPat_scope h₂ x, matchPat_scope h₁ x]
    simp only [patVars, List.mem_append]
    tauto
  | .call _ _, _, _, _, h, _ => absurd (isPat_of_matchPat h) id
  | .prim _ _, _, _, _, h, _ => absurd (isPat_of_matchPat h) id
  | .ite _ _ _, _, _, _, h, _ => absurd (isPat_of_matchPat h) id
  | .letp _ _ _, _, _, _, h, _ => absurd (isPat_of_matchPat h) id

theorem EnvScope.matchPat {env : Env} {sc : List String} (hs : EnvScope env sc) {p : Tm}
    {w : Val} {σ : Env} (h : matchPat env p w = some σ) : EnvScope σ (patVars p ++ sc) := by
  intro x
  rw [matchPat_scope h x, hs x, List.mem_append]

theorem EnvScope.nil : EnvScope [] [] := fun x => by simp [lookup]

theorem EnvScope.lookup_none {env : Env} {sc : List String} (hs : EnvScope env sc) {x : String}
    (hx : x ∉ sc) : lookup env x = none := by
  cases h : lookup env x with
  | none => rfl
  | some v => exact absurd ((hs x).1 (by simp [h])) hx

theorem EnvScope.lookup_some {env : Env} {sc : List String} (hs : EnvScope env sc) {x : String}
    (hx : x ∈ sc) : ∃ v, lookup env x = some v := by
  have := (hs x).2 hx
  cases h : lookup env x with
  | none => simp [h] at this
  | some v => exact ⟨v, rfl⟩

/-- The values of a linear cons pattern are the cells of its parts' values. -/
theorem matchSet_cons {env : Env} {p q : Tm} (hl : Linear (.cons p q)) {x y : Val}
    (hx : x ∈ MatchSet env p) (hy : y ∈ MatchSet env q) :
    Val.cons x y ∈ MatchSet env (.cons p q) := by
  obtain ⟨σ₁, h₁⟩ := hx
  obtain ⟨σ', h'⟩ := hy
  obtain ⟨ext, rfl, hext⟩ := matchPat_extends h₁
  have hdisj : ∀ z ∈ patVars q, z ∉ patVars p := by
    intro z hzq hzp
    have hnd : (patVars p ++ patVars q).Nodup := hl
    exact (List.nodup_append.1 hnd).2.2 z hzp z hzq rfl
  obtain ⟨σ₂, h₂, -⟩ := matchPat_agree (A := patVars q) (env₁ := env) (env₂ := ext ++ env)
    (fun z hz => (lookup_append_of_not_mem ext env z
      (fun b hb hbz => hdisj z hz (hbz ▸ hext b hb))).symm)
    (fun z hz => hz) h'
  exact ⟨σ₂, matchPat_cons_eq.2 ⟨x, y, ext ++ env, rfl, h₁, h₂⟩⟩

theorem linear_cons {p q : Tm} (hl : Linear (.cons p q)) : Linear p ∧ Linear q := by
  have hnd : (patVars p ++ patVars q).Nodup := hl
  exact ⟨(List.nodup_append.1 hnd).1, (List.nodup_append.1 hnd).2.1⟩

/-- What `select` returns. -/
theorem select_some : ∀ {P : Program} {f : String} {v : Val} {e : Equation} {σ : Env},
    select P f v = some (e, σ) → e ∈ P ∧ e.head = f ∧ matchPat [] e.param v = some σ
  | [], _, _, _, _, h => by simp [select] at h
  | e' :: P, f, v, e, σ, h => by
    simp only [select] at h
    split at h
    · rename_i hf
      split at h
      · rename_i σ' hσ'
        cases h
        exact ⟨List.mem_cons_self .., hf, hσ'⟩
      · obtain ⟨he, h₁, h₂⟩ := select_some h
        exact ⟨List.mem_cons_of_mem _ he, h₁, h₂⟩
    · obtain ⟨he, h₁, h₂⟩ := select_some h
      exact ⟨List.mem_cons_of_mem _ he, h₁, h₂⟩

/-! ## Fuel -/

/-- An outcome refines another when it ran out of fuel or they are equal. -/
def Refines (o o' : Outcome) : Prop := o = .exhausted ∨ o = o'

theorem Refines.refl (o : Outcome) : Refines o o := Or.inr rfl

theorem Refines.eq {o o' : Outcome} (h : Refines o o') (ho : o ≠ .exhausted) : o = o' :=
  h.resolve_left ho

theorem Refines.bind {o o' : Outcome} {k k' : Val → Outcome} (h : Refines o o')
    (hk : ∀ v, Refines (k v) (k' v)) : Refines (o.bind k) (o'.bind k') := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · cases o with
    | value v => exact hk v
    | failure => exact Refines.refl _
    | exhausted => exact Refines.refl _

section Fuel

variable (P : Program) (H : Host)

theorem stepV_refines {ev ev' : Env → Tm → Outcome} (h : ∀ env t, Refines (ev env t) (ev' env t))
    (env : Env) : ∀ t, Refines (stepV P H ev env t) (stepV P H ev' env t)
  | .var _ => Refines.refl _
  | .atom _ => Refines.refl _
  | .nil => Refines.refl _
  | .cons a b => Refines.bind (h env a) (fun _ => Refines.bind (h env b) (fun _ => Refines.refl _))
  | .call f a => Refines.bind (h env a) (fun v => by
      cases select P f v with
      | none => exact Refines.refl _
      | some r => exact h _ _)
  | .prim _ a => Refines.bind (h env a) (fun _ => Refines.refl _)
  | .ite c a b => Refines.bind (h env c) (fun v => by
      by_cases hv : v = .atom "True"
      · simp only [hv, if_true]
        exact h env a
      · simp only [hv, if_false]
        exact h env b)
  | .letp p v b => Refines.bind (h env v) (fun w => by
      cases matchPat env p w with
      | none => exact Refines.refl _
      | some σ => exact h σ b)

theorem evalV_refines_succ : ∀ n env t, Refines (evalV P H n env t) (evalV P H (n + 1) env t)
  | 0, _, _ => Or.inl rfl
  | n + 1, env, t => stepV_refines P H (evalV_refines_succ n) env t

/-- Fuel is monotone for the value-first reading. -/
theorem evalV_mono (n k : Nat) (env : Env) (t : Tm) (h : evalV P H n env t ≠ .exhausted) :
    evalV P H (n + k) env t = evalV P H n env t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have := (evalV_refines_succ P H (n + k) env t).eq (by rw [ih]; exact h)
    rw [← Nat.add_assoc, ← this, ih]

theorem evalV_mono_le {n m : Nat} (hnm : n ≤ m) {env : Env} {t : Tm}
    (h : evalV P H n env t ≠ .exhausted) : evalV P H m env t = evalV P H n env t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact evalV_mono P H n k env t h

theorem stepD_refines {ev ev' : Env → Tm → Set Val → Outcome}
    (h : ∀ env t M, Refines (ev env t M) (ev' env t M)) (env : Env) (t : Tm) (M : Set Val) :
    Refines (stepD P H ev env t M) (stepD P H ev' env t M) := by
  cases t with
  | var _ => exact Refines.refl _
  | atom _ => exact Refines.refl _
  | nil => exact Refines.refl _
  | cons a b =>
    exact Refines.bind (h _ _ _) (fun _ => Refines.bind (h _ _ _) (fun _ => Refines.refl _))
  | call f a =>
    refine Refines.bind (h _ _ _) (fun v => ?_)
    cases select P f v with
    | none => exact Refines.refl _
    | some r => exact h _ _ _
  | prim _ a => exact Refines.bind (h _ _ _) (fun _ => Refines.refl _)
  | ite c a b =>
    refine Refines.bind (h _ _ _) (fun v => ?_)
    by_cases hv : v = .atom "True"
    · simp only [hv, if_true]
      exact h _ _ _
    · simp only [hv, if_false]
      exact h _ _ _
  | letp p v b =>
    refine Refines.bind (h _ _ _) (fun w => ?_)
    cases matchPat env p w with
    | none => exact Refines.refl _
    | some σ => exact h _ _ _

theorem evalD_refines_succ :
    ∀ n env t M, Refines (evalD P H n env t M) (evalD P H (n + 1) env t M)
  | 0, _, _, _ => Or.inl rfl
  | n + 1, env, t, M => by
    simp only [evalD]
    split
    · exact stepD_refines P H (evalD_refines_succ n) env t M
    · exact Refines.refl _

/-- Fuel is monotone for the destination-first reading. -/
theorem evalD_mono (n k : Nat) (env : Env) (t : Tm) (M : Set Val)
    (h : evalD P H n env t M ≠ .exhausted) : evalD P H (n + k) env t M = evalD P H n env t M := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have := (evalD_refines_succ P H (n + k) env t M).eq (by rw [ih]; exact h)
    rw [← Nat.add_assoc, ← this, ih]

/-- Two fuels that both end give the same outcome. -/
theorem evalD_unique {n m : Nat} {env : Env} {t : Tm} {M : Set Val}
    (hn : evalD P H n env t M ≠ .exhausted) (hm : evalD P H m env t M ≠ .exhausted) :
    evalD P H n env t M = evalD P H m env t M := by
  rcases Nat.le_total n m with hnm | hmn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact (evalD_mono P H n k env t M hn).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact evalD_mono P H m k env t M hm

end Fuel

/-! ## Outcomes of a continued value -/

theorem Outcome.bind_eq_value {o : Outcome} {k : Val → Outcome} {u : Val} :
    o.bind k = .value u ↔ ∃ v, o = .value v ∧ k v = .value u := by
  cases o <;> simp

theorem Outcome.bind_eq_failure {o : Outcome} {k : Val → Outcome} :
    o.bind k = .failure ↔ o = .failure ∨ ∃ v, o = .value v ∧ k v = .failure := by
  cases o <;> simp

theorem Outcome.ne_exhausted_of_bind {o : Outcome} {k : Val → Outcome}
    (h : o.bind k ≠ .exhausted) : o ≠ .exhausted := by
  rintro rfl
  exact h rfl

theorem Outcome.bind_ne_exhausted {o : Outcome} {k : Val → Outcome} (ho : o ≠ .exhausted)
    (hk : ∀ v, o = .value v → k v ≠ .exhausted) : o.bind k ≠ .exhausted := by
  cases o with
  | value v => exact hk v rfl
  | failure => simp
  | exhausted => exact absurd rfl ho

section Square

variable (P : Program) (H : Host)

theorem evalD_succ_pos {n : Nat} {env : Env} {t : Tm} {M : Set Val} (hm : SkelMeets env t M) :
    evalD P H (n + 1) env t M = stepD P H (evalD P H n) env t M := by
  simp only [evalD, if_pos hm]

theorem evalD_succ_neg {n : Nat} {env : Env} {t : Tm} {M : Set Val} (hm : ¬SkelMeets env t M) :
    evalD P H (n + 1) env t M = .failure := by
  simp only [evalD, if_neg hm]

/-! ## Value first: every value lies in the skeleton -/

theorem skel_of_evalV : ∀ (n : Nat) (env : Env) (t : Tm) (u : Val),
    evalV P H n env t = .value u → Skel env t u
  | 0, _, _, _, h => by simp [evalV] at h
  | n + 1, env, t, u, h => by
    cases t with
    | var x =>
      simp only [evalV, stepV] at h
      cases hx : lookup env x with
      | none => simp [hx] at h
      | some v =>
        simp only [hx, Outcome.value.injEq] at h
        subst h
        exact hx
    | atom a =>
      simp only [evalV, stepV, Outcome.value.injEq] at h
      exact h.symm
    | nil =>
      simp only [evalV, stepV, Outcome.value.injEq] at h
      exact h.symm
    | cons a b =>
      simp only [evalV, stepV] at h
      obtain ⟨x, hx, h⟩ := Outcome.bind_eq_value.1 h
      obtain ⟨y, hy, h⟩ := Outcome.bind_eq_value.1 h
      simp only [Outcome.value.injEq] at h
      exact ⟨x, y, h.symm, skel_of_evalV n env a x hx, skel_of_evalV n env b y hy⟩
    | call _ _ => trivial
    | prim _ _ => trivial
    | ite _ _ _ => trivial
    | letp p v b =>
      simp only [evalV, stepV] at h
      obtain ⟨w, -, h⟩ := Outcome.bind_eq_value.1 h
      cases hm : matchPat env p w with
      | none => simp [hm] at h
      | some σ =>
        rw [hm] at h
        exact ⟨w, σ, hm, skel_of_evalV n σ b u h⟩

/-! ## Value first ends, destination first ends the same way -/

/-- When the value-first reading ends, the destination-first reading ends with the
same fuel: with the value when the destination admits it, and with failure
otherwise. -/
theorem evalD_of_evalV : ∀ (n : Nat) (env : Env) (t : Tm),
    (∀ u, evalV P H n env t = .value u → ∀ M,
      (u ∈ M → evalD P H n env t M = .value u) ∧ (u ∉ M → evalD P H n env t M = .failure)) ∧
    (evalV P H n env t = .failure → ∀ M, evalD P H n env t M = .failure)
  | 0, _, _ => ⟨fun _ h => by simp [evalV] at h, fun h => by simp [evalV] at h⟩
  | n + 1, env, t => by
    have ih := evalD_of_evalV n
    refine ⟨fun u h M => ⟨fun huM => ?_, fun huM => ?_⟩, fun h M => ?_⟩
    · -- the destination admits the value
      have hs := skel_of_evalV P H (n + 1) env t u h
      rw [evalD_succ_pos P H ⟨u, huM, hs⟩]
      cases t with
      | var x =>
        simp only [evalV, stepV] at h
        simp only [stepD]
        cases hx : lookup env x <;> simp_all
      | atom a =>
        simp only [evalV, stepV, Outcome.value.injEq] at h
        simp [stepD, h]
      | nil =>
        simp only [evalV, stepV, Outcome.value.injEq] at h
        simp [stepD, h]
      | cons a b =>
        simp only [evalV, stepV] at h
        obtain ⟨x, hx, h⟩ := Outcome.bind_eq_value.1 h
        obtain ⟨y, hy, h⟩ := Outcome.bind_eq_value.1 h
        simp only [Outcome.value.injEq] at h
        subst h
        simp only [stepD]
        rw [((ih env a).1 x hx {x | ∃ y, Skel env b y ∧ Val.cons x y ∈ M}).1
            ⟨y, skel_of_evalV P H n env b y hy, huM⟩,
          Outcome.bind_value, ((ih env b).1 y hy _).1 huM, Outcome.bind_value]
      | call f a =>
        simp only [evalV, stepV] at h
        obtain ⟨v, hv, h⟩ := Outcome.bind_eq_value.1 h
        simp only [stepD]
        rw [((ih env a).1 v hv _).1 (Set.mem_univ v), Outcome.bind_value]
        cases hsel : select P f v with
        | none => simp [hsel] at h
        | some r =>
          obtain ⟨e, σ⟩ := r
          simp only [hsel] at h ⊢
          exact ((ih σ e.body).1 u h M).1 huM
      | prim f a =>
        simp only [evalV, stepV] at h
        obtain ⟨v, hv, h⟩ := Outcome.bind_eq_value.1 h
        simp only [stepD]
        rw [((ih env a).1 v hv _).1 (Set.mem_univ v), Outcome.bind_value]
        cases hw : H f v with
        | none => simp [hw] at h
        | some w =>
          simp only [hw, Outcome.value.injEq] at h
          subst h
          simp [huM]
      | ite c a b =>
        simp only [evalV, stepV] at h
        obtain ⟨v, hv, h⟩ := Outcome.bind_eq_value.1 h
        simp only [stepD]
        rw [((ih env c).1 v hv _).1 (Set.mem_univ v), Outcome.bind_value]
        by_cases hT : v = .atom "True"
        · simp only [hT, if_true] at h ⊢
          exact ((ih env a).1 u h M).1 huM
        · simp only [hT, if_false] at h ⊢
          exact ((ih env b).1 u h M).1 huM
      | letp p v b =>
        simp only [evalV, stepV] at h
        obtain ⟨w, hw, h⟩ := Outcome.bind_eq_value.1 h
        cases hm : matchPat env p w with
        | none => simp [hm] at h
        | some σ =>
          rw [hm] at h
          simp only [stepD]
          rw [((ih env v).1 w hw {w | ∃ σ, matchPat env p w = some σ ∧ SkelMeets σ b M}).1
              ⟨σ, hm, u, huM, skel_of_evalV P H n σ b u h⟩,
            Outcome.bind_value, hm]
          exact ((ih σ b).1 u h M).1 huM
    · -- the destination refuses the value
      by_cases hmeet : SkelMeets env t M
      · rw [evalD_succ_pos P H hmeet]
        cases t with
        | var x =>
          obtain ⟨u', hu'M, hu'⟩ := hmeet
          have hx : lookup env x = some u' := hu'
          simp only [evalV, stepV, hx, Outcome.value.injEq] at h
          exact absurd (h ▸ hu'M) huM
        | atom a =>
          obtain ⟨u', hu'M, hu'⟩ := hmeet
          simp only [evalV, stepV, Outcome.value.injEq] at h
          exact absurd (by rw [← h]; exact (show u' = .atom a from hu') ▸ hu'M) huM
        | nil =>
          obtain ⟨u', hu'M, hu'⟩ := hmeet
          simp only [evalV, stepV, Outcome.value.injEq] at h
          exact absurd (by rw [← h]; exact (show u' = .nil from hu') ▸ hu'M) huM
        | cons a b =>
          simp only [evalV, stepV] at h
          obtain ⟨x, hx, h⟩ := Outcome.bind_eq_value.1 h
          obtain ⟨y, hy, h⟩ := Outcome.bind_eq_value.1 h
          simp only [Outcome.value.injEq] at h
          subst h
          simp only [stepD]
          by_cases hxa : x ∈ {x | ∃ y, Skel env b y ∧ Val.cons x y ∈ M}
          · rw [((ih env a).1 x hx _).1 hxa, Outcome.bind_value,
              ((ih env b).1 y hy _).2 huM, Outcome.bind_failure]
          · rw [((ih env a).1 x hx _).2 hxa, Outcome.bind_failure]
        | call f a =>
          simp only [evalV, stepV] at h
          obtain ⟨v, hv, h⟩ := Outcome.bind_eq_value.1 h
          simp only [stepD]
          rw [((ih env a).1 v hv _).1 (Set.mem_univ v), Outcome.bind_value]
          cases hsel : select P f v with
          | none => simp [hsel] at h
          | some r =>
            obtain ⟨e, σ⟩ := r
            simp only [hsel] at h ⊢
            exact ((ih σ e.body).1 u h M).2 huM
        | prim f a =>
          simp only [evalV, stepV] at h
          obtain ⟨v, hv, h⟩ := Outcome.bind_eq_value.1 h
          simp only [stepD]
          rw [((ih env a).1 v hv _).1 (Set.mem_univ v), Outcome.bind_value]
          cases hw : H f v with
          | none => simp [hw] at h
          | some w =>
            simp only [hw, Outcome.value.injEq] at h
            subst h
            simp [huM]
        | ite c a b =>
          simp only [evalV, stepV] at h
          obtain ⟨v, hv, h⟩ := Outcome.bind_eq_value.1 h
          simp only [stepD]
          rw [((ih env c).1 v hv _).1 (Set.mem_univ v), Outcome.bind_value]
          by_cases hT : v = .atom "True"
          · simp only [hT, if_true] at h ⊢
            exact ((ih env a).1 u h M).2 huM
          · simp only [hT, if_false] at h ⊢
            exact ((ih env b).1 u h M).2 huM
        | letp p v b =>
          simp only [evalV, stepV] at h
          obtain ⟨w, hw, h⟩ := Outcome.bind_eq_value.1 h
          cases hm : matchPat env p w with
          | none => simp [hm] at h
          | some σ =>
            rw [hm] at h
            simp only [stepD]
            by_cases hwv : w ∈ {w | ∃ σ, matchPat env p w = some σ ∧ SkelMeets σ b M}
            · rw [((ih env v).1 w hw _).1 hwv, Outcome.bind_value, hm]
              exact ((ih σ b).1 u h M).2 huM
            · rw [((ih env v).1 w hw _).2 hwv, Outcome.bind_failure]
      · exact evalD_succ_neg P H hmeet
    · -- the value-first reading fails
      by_cases hmeet : SkelMeets env t M
      · rw [evalD_succ_pos P H hmeet]
        cases t with
        | var x =>
          simp only [evalV, stepV] at h
          simp only [stepD]
          cases hx : lookup env x <;> simp_all
        | atom a => simp [evalV, stepV] at h
        | nil => simp [evalV, stepV] at h
        | cons a b =>
          simp only [evalV, stepV] at h
          simp only [stepD]
          rcases Outcome.bind_eq_failure.1 h with ha | ⟨x, hx, h⟩
          · rw [(ih env a).2 ha _, Outcome.bind_failure]
          · rcases Outcome.bind_eq_failure.1 h with hb | ⟨y, -, h⟩
            · by_cases hxa : x ∈ {x | ∃ y, Skel env b y ∧ Val.cons x y ∈ M}
              · rw [((ih env a).1 x hx _).1 hxa, Outcome.bind_value, (ih env b).2 hb _,
                  Outcome.bind_failure]
              · rw [((ih env a).1 x hx _).2 hxa, Outcome.bind_failure]
            · simp at h
        | call f a =>
          simp only [evalV, stepV] at h
          simp only [stepD]
          rcases Outcome.bind_eq_failure.1 h with ha | ⟨v, hv, h⟩
          · rw [(ih env a).2 ha _, Outcome.bind_failure]
          · rw [((ih env a).1 v hv _).1 (Set.mem_univ v), Outcome.bind_value]
            cases hsel : select P f v with
            | none => rfl
            | some r =>
              obtain ⟨e, σ⟩ := r
              simp only [hsel] at h ⊢
              exact (ih σ e.body).2 h M
        | prim f a =>
          simp only [evalV, stepV] at h
          simp only [stepD]
          rcases Outcome.bind_eq_failure.1 h with ha | ⟨v, hv, h⟩
          · rw [(ih env a).2 ha _, Outcome.bind_failure]
          · rw [((ih env a).1 v hv _).1 (Set.mem_univ v), Outcome.bind_value]
            cases hw : H f v with
            | none => rfl
            | some w => simp [hw] at h
        | ite c a b =>
          simp only [evalV, stepV] at h
          simp only [stepD]
          rcases Outcome.bind_eq_failure.1 h with hc | ⟨v, hv, h⟩
          · rw [(ih env c).2 hc _, Outcome.bind_failure]
          · rw [((ih env c).1 v hv _).1 (Set.mem_univ v), Outcome.bind_value]
            by_cases hT : v = .atom "True"
            · simp only [hT, if_true] at h ⊢
              exact (ih env a).2 h M
            · simp only [hT, if_false] at h ⊢
              exact (ih env b).2 h M
        | letp p v b =>
          simp only [evalV, stepV] at h
          simp only [stepD]
          rcases Outcome.bind_eq_failure.1 h with hv | ⟨w, hw, h⟩
          · rw [(ih env v).2 hv _, Outcome.bind_failure]
          · by_cases hwv : w ∈ {w | ∃ σ, matchPat env p w = some σ ∧ SkelMeets σ b M}
            · rw [((ih env v).1 w hw _).1 hwv, Outcome.bind_value]
              cases hm : matchPat env p w with
              | none => rfl
              | some σ =>
                rw [hm] at h
                exact (ih σ b).2 h M
            · rw [((ih env v).1 w hw _).2 hwv, Outcome.bind_failure]
      · exact evalD_succ_neg P H hmeet

/-- The destination-first reading of a term with no destination ends wherever
the value-first reading does, with the same outcome. -/
theorem evalD_univ_of_evalV {n : Nat} {env : Env} {t : Tm} {r : Outcome}
    (h : evalV P H n env t = r) (hr : r ≠ .exhausted) : evalD P H n env t Set.univ = r := by
  cases r with
  | value u => exact ((evalD_of_evalV P H n env t).1 u h _).1 (Set.mem_univ u)
  | failure => exact (evalD_of_evalV P H n env t).2 h _
  | exhausted => exact absurd rfl hr

/-! ## Work without calls ends -/

theorem evalV_callFree : ∀ (t : Tm), CallFree t → ∀ env : Env,
    ∃ n, evalV P H n env t ≠ .exhausted
  | .var x, _, env => ⟨1, by cases h : lookup env x <;> simp [evalV, stepV, h]⟩
  | .atom _, _, _ => ⟨1, by simp [evalV, stepV]⟩
  | .nil, _, _ => ⟨1, by simp [evalV, stepV]⟩
  | .cons a b, hcf, env => by
    obtain ⟨n₁, h₁⟩ := evalV_callFree a hcf.1 env
    obtain ⟨n₂, h₂⟩ := evalV_callFree b hcf.2 env
    refine ⟨max n₁ n₂ + 1, ?_⟩
    simp only [evalV, stepV]
    rw [evalV_mono_le P H (le_max_left n₁ n₂) h₁]
    refine Outcome.bind_ne_exhausted h₁ (fun _ _ => ?_)
    rw [evalV_mono_le P H (le_max_right n₁ n₂) h₂]
    exact Outcome.bind_ne_exhausted h₂ (fun _ _ => by simp)
  | .call _ _, hcf, _ => absurd hcf id
  | .prim f a, hcf, env => by
    obtain ⟨n₁, h₁⟩ := evalV_callFree a hcf env
    refine ⟨n₁ + 1, ?_⟩
    simp only [evalV, stepV]
    refine Outcome.bind_ne_exhausted h₁ (fun v _ => ?_)
    cases H f v <;> simp
  | .ite c a b, hcf, env => by
    obtain ⟨n₁, h₁⟩ := evalV_callFree c hcf.1 env
    obtain ⟨n₂, h₂⟩ := evalV_callFree a hcf.2.1 env
    obtain ⟨n₃, h₃⟩ := evalV_callFree b hcf.2.2 env
    refine ⟨max n₁ (max n₂ n₃) + 1, ?_⟩
    simp only [evalV, stepV]
    rw [evalV_mono_le P H (le_max_left _ _) h₁]
    refine Outcome.bind_ne_exhausted h₁ (fun v _ => ?_)
    by_cases hT : v = .atom "True"
    · simp only [hT, if_true]
      rw [evalV_mono_le P H (le_trans (le_max_left n₂ n₃) (le_max_right _ _)) h₂]
      exact h₂
    · simp only [hT, if_false]
      rw [evalV_mono_le P H (le_trans (le_max_right n₂ n₃) (le_max_right _ _)) h₃]
      exact h₃
  | .letp p v b, hcf, env => by
    obtain ⟨n₁, h₁⟩ := evalV_callFree v hcf.1 env
    cases hv : evalV P H n₁ env v with
    | exhausted => exact absurd hv h₁
    | failure => exact ⟨n₁ + 1, by simp [evalV, stepV, hv]⟩
    | value w =>
      cases hm : matchPat env p w with
      | none => exact ⟨n₁ + 1, by simp [evalV, stepV, hv, hm]⟩
      | some σ =>
        obtain ⟨n₂, h₂⟩ := evalV_callFree b hcf.2 σ
        refine ⟨max n₁ n₂ + 1, ?_⟩
        simp only [evalV, stepV]
        rw [evalV_mono_le P H (le_max_left n₁ n₂) h₁, hv, Outcome.bind_value, hm]
        dsimp only
        rw [evalV_mono_le P H (le_max_right n₁ n₂) h₂]
        exact h₂

end Square

/-! ## Skeletons of well-scoped terms -/

theorem skel_exists : ∀ (t : Tm) (sc : List String) (env : Env), WellScoped sc t →
    EnvScope env sc → ∃ u, Skel env t u
  | .var _, _, _, hws, hs => hs.lookup_some hws
  | .atom a, _, _, _, _ => ⟨.atom a, rfl⟩
  | .nil, _, _, _, _ => ⟨.nil, rfl⟩
  | .cons a b, sc, env, hws, hs => by
    obtain ⟨x, hx⟩ := skel_exists a sc env hws.1 hs
    obtain ⟨y, hy⟩ := skel_exists b sc env hws.2 hs
    exact ⟨.cons x y, x, y, rfl, hx, hy⟩
  | .call _ _, _, _, _, _ => ⟨.nil, trivial⟩
  | .prim _ _, _, _, _, _ => ⟨.nil, trivial⟩
  | .ite _ _ _, _, _, _, _ => ⟨.nil, trivial⟩
  | .letp p _ b, sc, env, hws, hs => by
    obtain ⟨w, σ, hm⟩ := matchPat_exists hws.1 env
    obtain ⟨u, hu⟩ := skel_exists b _ σ hws.2.2 (hs.matchPat hm)
    exact ⟨u, w, σ, hm, hu⟩

/-! ## Certain meeting -/

section Evidence

variable {W : Certificate} {R : List String} {env₀ : Env}

theorem certMatch_atom (hR : ∀ x ∈ R, lookup env₀ x = none) {d : Tm} {a : String}
    (h : CertMatch R d (.atom a)) : Val.atom a ∈ MatchSet env₀ d := by
  cases d with
  | var x => rw [matchSet_var (hR x h)]; trivial
  | atom b =>
    have hab : b = a := h
    subst hab
    exact ⟨env₀, matchPat_atom_eq.2 ⟨rfl, rfl⟩⟩
  | nil => exact absurd h id
  | cons _ _ => exact absurd h id
  | call _ _ => exact absurd h id
  | prim _ _ => exact absurd h id
  | ite _ _ _ => exact absurd h id
  | letp _ _ _ => exact absurd h id

theorem certMatch_nil (hR : ∀ x ∈ R, lookup env₀ x = none) {d : Tm}
    (h : CertMatch R d .nil) : Val.nil ∈ MatchSet env₀ d := by
  cases d with
  | var x => rw [matchSet_var (hR x h)]; trivial
  | atom _ => exact absurd h id
  | nil => exact ⟨env₀, matchPat_nil_eq.2 ⟨rfl, rfl⟩⟩
  | cons _ _ => exact absurd h id
  | call _ _ => exact absurd h id
  | prim _ _ => exact absurd h id
  | ite _ _ _ => exact absurd h id
  | letp _ _ _ => exact absurd h id

/-- A destination part that certainly meets a term meets some value of its
skeleton. -/
theorem certain_skel (hR : ∀ x ∈ R, lookup env₀ x = none) {t d : Tm}
    (hc : Certain W R t d) : IsPat d → Linear d → ∀ (sc : List String) (env : Env),
      WellScoped sc t → EnvScope env sc → ∃ u, Skel env t u ∧ u ∈ MatchSet env₀ d := by
  induction hc with
  | recv hx =>
    intro _ _ sc env hws hs
    obtain ⟨u, hu⟩ := skel_exists _ sc env hws hs
    exact ⟨u, hu, by rw [matchSet_var (hR _ hx)]; trivial⟩
  | atom h => exact fun _ _ _ _ _ _ => ⟨_, rfl, certMatch_atom hR h⟩
  | nil h => exact fun _ _ _ _ _ _ => ⟨_, rfl, certMatch_nil hR h⟩
  | cons _ _ iha ihb =>
    intro hd hl sc env hws hs
    obtain ⟨x, hx, hxm⟩ := iha hd.1 (linear_cons hl).1 sc env hws.1 hs
    obtain ⟨y, hy, hym⟩ := ihb hd.2 (linear_cons hl).2 sc env hws.2 hs
    exact ⟨.cons x y, ⟨x, y, rfl, hx, hy⟩, matchSet_cons hl hxm hym⟩
  | call _ =>
    intro hd _ _ _ _ _
    obtain ⟨u, hu⟩ := matchSet_nonempty hd env₀
    exact ⟨u, trivial, hu⟩
  | ite _ _ _ _ =>
    intro hd _ _ _ _ _
    obtain ⟨u, hu⟩ := matchSet_nonempty hd env₀
    exact ⟨u, trivial, hu⟩
  | letp _ ih =>
    intro hd hl sc env hws hs
    obtain ⟨w, σ, hm⟩ := matchPat_exists hws.1 env
    obtain ⟨u, hu, hum⟩ := ih hd hl _ σ hws.2.2 (hs.matchPat hm)
    exact ⟨u, ⟨w, σ, hm, hu⟩, hum⟩

/-- Every value of a term a destination part certainly meets matches the part. -/
theorem certain_evalV (P : Program) (H : Host) (hW : Consistent P W R)
    (hR : ∀ x ∈ R, lookup env₀ x = none) :
    ∀ (n : Nat) {t d : Tm} (env : Env) (u : Val), Certain W R t d → IsPat d → Linear d →
      evalV P H n env t = .value u → u ∈ MatchSet env₀ d
  | 0, _, _, _, _, _, _, _, h => by simp [evalV] at h
  | n + 1, t, d, env, u, hc, hd, hl, h => by
    cases hc with
    | recv hx => rw [matchSet_var (hR _ hx)]; trivial
    | atom hcm =>
      simp only [evalV, stepV, Outcome.value.injEq] at h
      subst h
      exact certMatch_atom hR hcm
    | nil hcm =>
      simp only [evalV, stepV, Outcome.value.injEq] at h
      subst h
      exact certMatch_nil hR hcm
    | cons hca hcb =>
      simp only [evalV, stepV] at h
      obtain ⟨x, hx, h⟩ := Outcome.bind_eq_value.1 h
      obtain ⟨y, hy, h⟩ := Outcome.bind_eq_value.1 h
      simp only [Outcome.value.injEq] at h
      subst h
      exact matchSet_cons hl
        (certain_evalV P H hW hR n env x hca hd.1 (linear_cons hl).1 hx)
        (certain_evalV P H hW hR n env y hcb hd.2 (linear_cons hl).2 hy)
    | @call f _ _ hf =>
      simp only [evalV, stepV] at h
      obtain ⟨v, -, h⟩ := Outcome.bind_eq_value.1 h
      cases hsel : select P f v with
      | none => simp [hsel] at h
      | some r =>
        obtain ⟨e, σ⟩ := r
        simp only [hsel] at h
        obtain ⟨he, hhead, -⟩ := select_some hsel
        exact certain_evalV P H hW hR n σ u ((hW _ _ _ hf e he hhead).1 rfl) hd hl h
    | ite hca hcb =>
      simp only [evalV, stepV] at h
      obtain ⟨v, -, h⟩ := Outcome.bind_eq_value.1 h
      by_cases hT : v = .atom "True"
      · simp only [hT, if_true] at h
        exact certain_evalV P H hW hR n env u hca hd hl h
      · simp only [hT, if_false] at h
        exact certain_evalV P H hW hR n env u hcb hd hl h
    | @letp p _ _ _ hcb =>
      simp only [evalV, stepV] at h
      obtain ⟨w, -, h⟩ := Outcome.bind_eq_value.1 h
      cases hm : matchPat env p w with
      | none => simp [hm] at h
      | some σ =>
        rw [hm] at h
        exact certain_evalV P H hW hR n σ u hcb hd hl h

end Evidence

/-! ## Admitted destinations -/

/-- The destination `M` of `t` contains every value of a destination part that
`t` admits. -/
def Good (P : Program) (t : Tm) (M : Set Val) : Prop :=
  ∃ (W : Certificate) (R : List String) (d : Tm) (env₀ : Env), Consistent P W R ∧ IsPat d ∧
    Linear d ∧ (∀ x ∈ R, lookup env₀ x = none) ∧ Admits W R t d ∧ MatchSet env₀ d ⊆ M

section Good

variable {P : Program}

theorem Good.mono' {t : Tm} {M M' : Set Val} (hg : Good P t M) (h : ∀ u, u ∈ M → u ∈ M') :
    Good P t M' := by
  obtain ⟨W, R, d, env₀, hW, hd, hl, hR, hadm, hsub⟩ := hg
  exact ⟨W, R, d, env₀, hW, hd, hl, hR, hadm, fun u hu => h u (hsub hu)⟩

/-- No destination is the destination of a receiving variable. -/
theorem good_univ (t : Tm) : Good P t Set.univ :=
  ⟨[], ["x"], .var "x", [], fun _ _ _ h => absurd h List.not_mem_nil, trivial,
    by simp [Linear, patVars], fun _ _ => rfl, .certain (.recv (List.mem_singleton_self _)),
    Set.subset_univ _⟩

theorem univ_of_recv {R : List String} {env₀ : Env} {x : String} {M : Set Val}
    (hR : ∀ x ∈ R, lookup env₀ x = none) (hx : x ∈ R) (hsub : MatchSet env₀ (.var x) ⊆ M) :
    M = Set.univ := by
  rw [matchSet_var (hR x hx)] at hsub
  exact Set.univ_subset_iff.1 hsub

theorem Good.nonempty {t : Tm} {M : Set Val} (hg : Good P t M) : M.Nonempty := by
  obtain ⟨_, _, d, env₀, _, hd, _, _, _, hsub⟩ := hg
  exact (matchSet_nonempty hd env₀).mono hsub

theorem Good.skelMeets {t : Tm} {M : Set Val} (hg : Good P t M) (hcf : ¬CallFree t)
    {sc : List String} {env : Env} (hws : WellScoped sc t) (hs : EnvScope env sc) :
    SkelMeets env t M := by
  obtain ⟨W, R, d, env₀, hW, hd, hl, hR, hadm, hsub⟩ := hg
  cases hadm with
  | certain hc =>
    obtain ⟨u, hu, hum⟩ := certain_skel hR hc hd hl sc env hws hs
    exact ⟨u, hsub hum, hu⟩
  | callFree h => exact absurd h hcf
  | ite _ _ =>
    obtain ⟨u, hu⟩ := matchSet_nonempty hd env₀
    exact ⟨u, hsub hu, trivial⟩
  | call _ =>
    obtain ⟨u, hu⟩ := matchSet_nonempty hd env₀
    exact ⟨u, hsub hu, trivial⟩

theorem Good.call_body {f : String} {a : Tm} {M : Set Val} (hg : Good P (.call f a) M)
    {e : Equation} (he : e ∈ P) (hhead : e.head = f) : Good P e.body M := by
  obtain ⟨W, R, d, env₀, hW, hd, hl, hR, hadm, hsub⟩ := hg
  cases hadm with
  | certain hc =>
    cases hc with
    | recv hx => rw [univ_of_recv hR hx hsub]; exact good_univ _
    | call hf => exact ⟨W, R, d, env₀, hW, hd, hl, hR, .certain ((hW _ _ _ hf e he hhead).1 rfl),
        hsub⟩
  | callFree h => exact absurd h id
  | call hf => exact ⟨W, R, d, env₀, hW, hd, hl, hR, (hW _ _ _ hf e he hhead).2 rfl, hsub⟩

theorem Good.ite_branches {c a b : Tm} {M : Set Val} (hg : Good P (.ite c a b) M)
    (hcf : ¬CallFree (.ite c a b)) : Good P a M ∧ Good P b M := by
  obtain ⟨W, R, d, env₀, hW, hd, hl, hR, hadm, hsub⟩ := hg
  cases hadm with
  | certain hc =>
    cases hc with
    | recv hx =>
      rw [univ_of_recv hR hx hsub]
      exact ⟨good_univ _, good_univ _⟩
    | ite hca hcb =>
      exact ⟨⟨W, R, d, env₀, hW, hd, hl, hR, .certain hca, hsub⟩,
        ⟨W, R, d, env₀, hW, hd, hl, hR, .certain hcb, hsub⟩⟩
  | callFree h => exact absurd h hcf
  | ite ha hb =>
    exact ⟨⟨W, R, d, env₀, hW, hd, hl, hR, ha, hsub⟩, ⟨W, R, d, env₀, hW, hd, hl, hR, hb, hsub⟩⟩

theorem Good.letp_body {p v b : Tm} {M : Set Val} (hg : Good P (.letp p v b) M)
    (hcf : ¬CallFree (.letp p v b)) {sc : List String} {env : Env}
    (hws : WellScoped sc (.letp p v b)) (hs : EnvScope env sc) {w : Val} {σ : Env}
    (hm : matchPat env p w = some σ) : SkelMeets σ b M ∧ Good P b M := by
  obtain ⟨W, R, d, env₀, hW, hd, hl, hR, hadm, hsub⟩ := hg
  cases hadm with
  | certain hc =>
    cases hc with
    | recv hx =>
      rw [univ_of_recv hR hx hsub]
      obtain ⟨u, hu⟩ := skel_exists b _ σ hws.2.2 (hs.matchPat hm)
      exact ⟨⟨u, Set.mem_univ u, hu⟩, good_univ _⟩
    | letp hcb =>
      obtain ⟨u, hu, hum⟩ := certain_skel hR hcb hd hl _ σ hws.2.2 (hs.matchPat hm)
      exact ⟨⟨u, hsub hum, hu⟩, ⟨W, R, d, env₀, hW, hd, hl, hR, .certain hcb, hsub⟩⟩
  | callFree h => exact absurd h hcf

theorem Good.cons_parts (H : Host) {a b : Tm} {M : Set Val} (hg : Good P (.cons a b) M)
    (hcf : ¬CallFree (.cons a b)) {sc : List String} {env : Env}
    (hws : WellScoped sc (.cons a b)) (hs : EnvScope env sc) :
    Good P a {x | ∃ y, Skel env b y ∧ Val.cons x y ∈ M} ∧
      ∀ n x, evalV P H n env a = .value x →
        x ∈ {x | ∃ y, Skel env b y ∧ Val.cons x y ∈ M} ∧ Good P b {y | Val.cons x y ∈ M} := by
  obtain ⟨W, R, d, env₀, hW, hd, hl, hR, hadm, hsub⟩ := hg
  cases hadm with
  | certain hc =>
    cases hc with
    | recv hx =>
      have hM := univ_of_recv hR hx hsub
      subst hM
      have hall : ∀ x : Val, x ∈ {x | ∃ y, Skel env b y ∧ Val.cons x y ∈ Set.univ} := by
        intro x
        obtain ⟨y, hy⟩ := skel_exists b sc env hws.2 hs
        exact ⟨y, hy, Set.mem_univ _⟩
      refine ⟨(good_univ a).mono' (fun x _ => hall x), fun _ x _ => ⟨hall x, ?_⟩⟩
      exact (good_univ b).mono' (fun _ _ => Set.mem_univ _)
    | @cons _ _ da db hca hcb =>
      have hla := (linear_cons hl).1
      have hlb := (linear_cons hl).2
      refine ⟨⟨W, R, da, env₀, hW, hd.1, hla, hR, .certain hca, fun x hx => ?_⟩,
        fun n x hx => ?_⟩
      · obtain ⟨y, hy, hym⟩ := certain_skel hR hcb hd.2 hlb sc env hws.2 hs
        exact ⟨y, hy, hsub (matchSet_cons hl hx hym)⟩
      · have hxm := certain_evalV P H hW hR n env x hca hd.1 hla hx
        obtain ⟨y, hy, hym⟩ := certain_skel hR hcb hd.2 hlb sc env hws.2 hs
        exact ⟨⟨y, hy, hsub (matchSet_cons hl hxm hym)⟩,
          ⟨W, R, db, env₀, hW, hd.2, hlb, hR, .certain hcb,
            fun y hy => hsub (matchSet_cons hl hxm hy)⟩⟩
  | callFree h => exact absurd h hcf

end Good

/-! ## Destination first ends, value first ends -/

section Converse

variable (P : Program) (H : Host)

theorem evalD_eq_of_evalV_value {N n : Nat} {env : Env} {t : Tm} {M : Set Val} {u : Val}
    (hN : evalD P H N env t M ≠ .exhausted) (h : evalV P H n env t = .value u) (hu : u ∈ M) :
    evalD P H N env t M = .value u := by
  have h₂ := ((evalD_of_evalV P H n env t).1 u h M).1 hu
  rw [evalD_unique P H hN (by rw [h₂]; simp), h₂]

/-- Where the destination-first reading ends on a well-scoped term of a program
whose lets are admitted, and the destination is admitted, the value-first reading
ends too. -/
theorem evalV_ends_of_evalD (hP : ProgramAdmitted P) :
    ∀ (N : Nat) (env : Env) (t : Tm) (M : Set Val) (sc : List String),
      evalD P H N env t M ≠ .exhausted → WellScoped sc t → EnvScope env sc →
      LetsAdmitted P sc t → Good P t M → ∃ n, evalV P H n env t ≠ .exhausted
  | 0, _, _, _, _, hD, _, _, _, _ => by simp [evalD] at hD
  | N + 1, env, t, M, sc, hD, hws, hs, hl, hg => by
    by_cases hcf : CallFree t
    · exact evalV_callFree P H t hcf env
    rw [evalD_succ_pos P H (hg.skelMeets hcf hws hs)] at hD
    have ih := evalV_ends_of_evalD hP N
    cases t with
    | var _ => exact absurd trivial hcf
    | atom _ => exact absurd trivial hcf
    | nil => exact absurd trivial hcf
    | cons a b =>
      simp only [stepD] at hD
      obtain ⟨hga, hgb⟩ := hg.cons_parts H hcf hws hs
      have hDa := Outcome.ne_exhausted_of_bind hD
      obtain ⟨n₁, h₁⟩ := ih env a _ sc hDa hws.1 hs hl.1 hga
      cases ha : evalV P H n₁ env a with
      | exhausted => exact absurd ha h₁
      | failure => exact ⟨n₁ + 1, by simp [evalV, stepV, ha]⟩
      | value x =>
        obtain ⟨hxa, hgb'⟩ := hgb n₁ x ha
        rw [evalD_eq_of_evalV_value P H hDa ha hxa, Outcome.bind_value] at hD
        have hDb := Outcome.ne_exhausted_of_bind hD
        obtain ⟨n₂, h₂⟩ := ih env b _ sc hDb hws.2 hs hl.2 hgb'
        refine ⟨max n₁ n₂ + 1, ?_⟩
        simp only [evalV, stepV]
        rw [evalV_mono_le P H (le_max_left n₁ n₂) h₁, ha, Outcome.bind_value,
          evalV_mono_le P H (le_max_right n₁ n₂) h₂]
        exact Outcome.bind_ne_exhausted h₂ (fun _ _ => by simp)
    | call f a =>
      simp only [stepD] at hD
      have hDa := Outcome.ne_exhausted_of_bind hD
      obtain ⟨n₁, h₁⟩ := ih env a Set.univ sc hDa hws hs hl (good_univ a)
      cases ha : evalV P H n₁ env a with
      | exhausted => exact absurd ha h₁
      | failure => exact ⟨n₁ + 1, by simp [evalV, stepV, ha]⟩
      | value v =>
        rw [evalD_eq_of_evalV_value P H hDa ha (Set.mem_univ v), Outcome.bind_value] at hD
        cases hsel : select P f v with
        | none => exact ⟨n₁ + 1, by simp [evalV, stepV, ha, hsel]⟩
        | some r =>
          obtain ⟨e, σ⟩ := r
          simp only [hsel] at hD
          obtain ⟨he, hhead, hσ⟩ := select_some hsel
          obtain ⟨-, hwsb, hlb⟩ := hP e he
          have hsσ : EnvScope σ (patVars e.param) := by
            simpa using EnvScope.nil.matchPat hσ
          obtain ⟨n₂, h₂⟩ := ih σ e.body M _ hD hwsb hsσ hlb (hg.call_body he hhead)
          refine ⟨max n₁ n₂ + 1, ?_⟩
          simp only [evalV, stepV]
          rw [evalV_mono_le P H (le_max_left n₁ n₂) h₁, ha, Outcome.bind_value, hsel]
          dsimp only
          rw [evalV_mono_le P H (le_max_right n₁ n₂) h₂]
          exact h₂
    | prim f a =>
      simp only [stepD] at hD
      have hDa := Outcome.ne_exhausted_of_bind hD
      obtain ⟨n₁, h₁⟩ := ih env a Set.univ sc hDa hws hs hl (good_univ a)
      refine ⟨n₁ + 1, ?_⟩
      simp only [evalV, stepV]
      exact Outcome.bind_ne_exhausted h₁ (fun v _ => by cases H f v <;> simp)
    | ite c a b =>
      simp only [stepD] at hD
      have hDc := Outcome.ne_exhausted_of_bind hD
      obtain ⟨hga, hgb⟩ := hg.ite_branches hcf
      obtain ⟨n₁, h₁⟩ := ih env c Set.univ sc hDc hws.1 hs hl.1 (good_univ c)
      cases hc : evalV P H n₁ env c with
      | exhausted => exact absurd hc h₁
      | failure => exact ⟨n₁ + 1, by simp [evalV, stepV, hc]⟩
      | value v =>
        rw [evalD_eq_of_evalV_value P H hDc hc (Set.mem_univ v), Outcome.bind_value] at hD
        by_cases hT : v = .atom "True"
        · simp only [hT, if_true] at hD
          obtain ⟨n₂, h₂⟩ := ih env a M sc hD hws.2.1 hs hl.2.1 hga
          refine ⟨max n₁ n₂ + 1, ?_⟩
          simp only [evalV, stepV]
          rw [evalV_mono_le P H (le_max_left n₁ n₂) h₁, hc, Outcome.bind_value, if_pos hT,
            evalV_mono_le P H (le_max_right n₁ n₂) h₂]
          exact h₂
        · simp only [hT, if_false] at hD
          obtain ⟨n₂, h₂⟩ := ih env b M sc hD hws.2.2 hs hl.2.2 hgb
          refine ⟨max n₁ n₂ + 1, ?_⟩
          simp only [evalV, stepV]
          rw [evalV_mono_le P H (le_max_left n₁ n₂) h₁, hc, Outcome.bind_value, if_neg hT,
            evalV_mono_le P H (le_max_right n₁ n₂) h₂]
          exact h₂
    | letp p v b =>
      simp only [stepD] at hD
      have hDv := Outcome.ne_exhausted_of_bind hD
      have hbody : ∀ w σ, matchPat env p w = some σ → SkelMeets σ b M ∧ Good P b M :=
        fun w σ hm => hg.letp_body hcf hws hs hm
      obtain ⟨n₁, h₁⟩ : ∃ n, evalV P H n env v ≠ .exhausted := by
        rcases hl.1 with hcfv | ⟨hlin, W, hW, hadm⟩
        · exact evalV_callFree P H v hcfv env
        · refine ih env v _ sc hDv hws.2.1 hs hl.2.1
            ⟨W, receiving sc p, p, env, hW, hws.1, hlin, fun x hx => ?_, hadm, ?_⟩
          · simp only [receiving, List.mem_filter, decide_eq_true_eq] at hx
            exact hs.lookup_none hx.2
          · rintro w ⟨σ, hm⟩
            exact ⟨σ, hm, (hbody w σ hm).1⟩
      cases hv : evalV P H n₁ env v with
      | exhausted => exact absurd hv h₁
      | failure => exact ⟨n₁ + 1, by simp [evalV, stepV, hv]⟩
      | value w =>
        cases hm : matchPat env p w with
        | none => exact ⟨n₁ + 1, by simp [evalV, stepV, hv, hm]⟩
        | some σ =>
          obtain ⟨hmeet, hgb⟩ := hbody w σ hm
          rw [evalD_eq_of_evalV_value P H hDv hv ⟨σ, hm, hmeet⟩, Outcome.bind_value, hm] at hD
          dsimp only at hD
          obtain ⟨n₂, h₂⟩ := ih σ b M _ hD hws.2.2 (hs.matchPat hm) hl.2.2 hgb
          refine ⟨max n₁ n₂ + 1, ?_⟩
          simp only [evalV, stepV]
          rw [evalV_mono_le P H (le_max_left n₁ n₂) h₁, hv, Outcome.bind_value, hm]
          dsimp only
          rw [evalV_mono_le P H (le_max_right n₁ n₂) h₂]
          exact h₂

/-- The square: on a well-scoped query of a program whose lets are all admitted,
the value-first and the destination-first readings end with the same
outcomes. -/
theorem destination_square (hP : ProgramAdmitted P) {t : Tm} (hws : WellScoped [] t)
    (hl : LetsAdmitted P [] t) {r : Outcome} (hr : r ≠ .exhausted) :
    (∃ n, evalV P H n [] t = r) ↔ ∃ n, evalD P H n [] t Set.univ = r := by
  constructor
  · rintro ⟨n, h⟩
    exact ⟨n, evalD_univ_of_evalV P H h hr⟩
  · rintro ⟨n, h⟩
    have hn : evalD P H n [] t Set.univ ≠ .exhausted := by rw [h]; exact hr
    obtain ⟨m, hm⟩ := evalV_ends_of_evalD P H hP n [] t Set.univ [] hn hws EnvScope.nil hl
      (good_univ t)
    have h₂ := evalD_univ_of_evalV P H (rfl : evalV P H m [] t = _) hm
    have hm' : evalD P H m [] t Set.univ ≠ .exhausted := by rw [h₂]; exact hm
    exact ⟨m, h₂.symm.trans ((evalD_unique P H hn hm').symm.trans h)⟩

end Converse

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.LetDestinations
