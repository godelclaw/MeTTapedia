import Mettapedia.Languages.MeTTa.DeclarationFaces.Termination
import Mathlib.Data.List.Nodup

/-!
# Sorts of the first-order fragment: parameterized data and polymorphic functions

A signature declares datatypes and functions, as the type declarations `(: Z Nat)`,
`(: S (-> Nat Nat))`, `(: Cons (-> $a (List $a) (List $a)))` and `(: length (-> (List $a) Nat))`
do. Sorts are first-order terms over datatype names with sort variables (`Tm String`), so a
datatype may have parameters and a function a polymorphic scheme.

* `HasSort sig Γ t τ`: in the context `Γ` of sorts of variables, the term `t` has the sort `τ`. A
  constructor of a datatype with parameters, and a declared function, are used at any instTyped of
  their sorts. The judgment is a relation: terms carry no type, as in MeTTa.
* `Signature.WellFormed`: datatype names, constructor names and function names are distinct, no
  function is a constructor, and field sorts use only their datatype's parameters.
* `Signature.TypesProgram sig P`: every equation is a declared function applied to constructor
  patterns, typed at the function's argument sorts, with its right side at the result sort.

**Subject reduction** (`HasSort.step`): a step keeps the sort of a term. Its core is
`HasSort.pattern_inversion`: an instTyped of a pattern at an instTyped of the pattern's sort
instantiates every variable of the pattern at the instTyped of that variable's sort.

**Coverage** (`Signature.Covers`): every call of a declared function on values of its argument
sorts, at any instTyped of its scheme, is an instTyped of the left side of some equation.
**Closed normal forms are values** (`HasSort.value_of_normal`): under coverage, a closed sorted
term that takes no step is constructor data.

Positive example: `(Cons Z Nil)` has the sort `(List Nat)` (`Examples.cons_typed`), and the
equations of `length` are typed (`Examples.length_typed`). Negative example: `(S Nil)` has no sort
(`Examples.s_nil_untyped`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces

open Tm
open Mettapedia.Logic.Relation (IsNormal)

universe u

variable {S : Type u}

/-- A sort: a sort variable, or a datatype name applied to sorts. -/
abbrev Sort' := Tm String

/-- A datatype declaration: its name, its parameters, and its constructors with their field sorts
over the parameters. -/
structure DataDecl (S : Type u) where
  name : String
  params : List String
  ctors : List (S × List Sort')

/-- A function declaration: its symbol, and its argument and result sorts, over sort variables. -/
structure FunDecl (S : Type u) where
  name : S
  args : List Sort'
  result : Sort'

/-- A signature: its datatypes and its functions. -/
structure Signature (S : Type u) where
  data : List (DataDecl S)
  funs : List (FunDecl S)

/-- The sort of a datatype at its own parameters. -/
def DataDecl.sort (d : DataDecl S) : Sort' := .app d.name (d.params.map .var)

/-- A context: the sort of each variable that has one. -/
abbrev Ctx := String → Option Sort'

/-- The empty context. -/
def Ctx.empty : Ctx := fun _ => none

/-- Elements of two lists of one length are related position by position. -/
def Pointwise {α β : Type*} (R : α → β → Prop) (as : List α) (bs : List β) : Prop :=
  as.length = bs.length ∧ ∀ i (hi : i < as.length) (hj : i < bs.length), R as[i] bs[i]

/-- **The sorting judgment.** -/
inductive HasSort (sig : Signature S) (Γ : Ctx) : Tm S → Sort' → Prop where
  | var {x : String} {τ : Sort'} : Γ x = some τ → HasSort sig Γ (.var x) τ
  | ctor {d : DataDecl S} {c : S} {fields : List Sort'} {args : List (Tm S)}
      (θ : String → Sort') : d ∈ sig.data → (c, fields) ∈ d.ctors →
      args.length = fields.length →
      (∀ i (hi : i < args.length) (hj : i < fields.length),
        HasSort sig Γ args[i] (fields[i].subst θ)) →
      HasSort sig Γ (.app c args) (d.sort.subst θ)
  | call {fd : FunDecl S} {args : List (Tm S)} (θ : String → Sort') : fd ∈ sig.funs →
      args.length = fd.args.length →
      (∀ i (hi : i < args.length) (hj : i < fd.args.length),
        HasSort sig Γ args[i] (fd.args[i].subst θ)) →
      HasSort sig Γ (.app fd.name args) (fd.result.subst θ)

/-- Constructor names of a signature. -/
def Signature.ctorNames (sig : Signature S) : List S := sig.data.flatMap fun d => d.ctors.map (·.1)

/-- **A well-formed signature.** -/
structure Signature.WellFormed (sig : Signature S) : Prop where
  dataNames : (sig.data.map (·.name)).Nodup
  ctorNames : sig.ctorNames.Nodup
  funNames : (sig.funs.map (·.name)).Nodup
  disjoint : ∀ fd ∈ sig.funs, fd.name ∉ sig.ctorNames
  params : ∀ d ∈ sig.data, d.params.Nodup ∧ ∀ cf ∈ d.ctors, ∀ s ∈ cf.2, ∀ a ∈ s.vars, a ∈ d.params

/-- A constructor pattern: a variable, or a declared constructor applied to patterns. -/
inductive IsPattern (sig : Signature S) : Tm S → Prop where
  | var (x : String) : IsPattern sig (.var x)
  | ctor {c : S} {args : List (Tm S)} : c ∈ sig.ctorNames → (∀ a ∈ args, IsPattern sig a) →
      IsPattern sig (.app c args)

/-- **A typed equation**: a declared function applied to constructor patterns typed at its
argument sorts, with the right side at its result sort, in one context. -/
def Signature.TypesEquation (sig : Signature S) (e : Equation S) : Prop :=
  ∃ fd ∈ sig.funs, ∃ (ps : List (Tm S)) (Γ : Ctx), e.lhs = .app fd.name ps ∧
    (∀ p ∈ ps, IsPattern sig p) ∧ Pointwise (HasSort sig Γ) ps fd.args ∧ HasSort sig Γ e.rhs fd.result

/-- Every equation of the program is typed. -/
def Signature.TypesProgram (sig : Signature S) (P : Program S) : Prop := ∀ e ∈ P, sig.TypesEquation e

/-- Data of a signature: a declared constructor applied to data. -/
inductive Signature.IsData (sig : Signature S) : Tm S → Prop where
  | app {c : S} {args : List (Tm S)} : c ∈ sig.ctorNames → (∀ a ∈ args, sig.IsData a) →
      sig.IsData (.app c args)

/-- A value of a sort: data of the signature with that sort, in the empty context. -/
def Signature.IsValueOf (sig : Signature S) (v : Tm S) (τ : Sort') : Prop :=
  sig.IsData v ∧ HasSort sig Ctx.empty v τ

/-- **Coverage**: every call of a declared function on values of its argument sorts, at any
instTyped of its scheme, is an instTyped of the left side of some equation. -/
def Signature.Covers (sig : Signature S) (P : Program S) : Prop :=
  ∀ fd ∈ sig.funs, ∀ (θ : String → Sort') (args : List (Tm S)),
    Pointwise sig.IsValueOf args (fd.args.map (Tm.subst θ)) →
      ∃ e ∈ P, ∃ σ : String → Tm S, e.lhs.subst σ = .app fd.name args

/-! ## Uniqueness of declarations in a well-formed signature -/

namespace Signature.WellFormed

variable {sig : Signature S} (wf : sig.WellFormed)
include wf

/-- A constructor belongs to one datatype, with one list of fields. -/
theorem ctor_unique {d d' : DataDecl S} {c : S} {fields fields' : List Sort'}
    (hd : d ∈ sig.data) (hd' : d' ∈ sig.data) (hc : (c, fields) ∈ d.ctors)
    (hc' : (c, fields') ∈ d'.ctors) : d = d' ∧ fields = fields' := by
  have dataNodup : sig.data.Nodup := List.Nodup.of_map _ wf.dataNames
  have ctors := wf.ctorNames
  unfold Signature.ctorNames at ctors
  rw [List.nodup_flatMap] at ctors
  obtain ⟨each, pairwise⟩ := ctors
  have sameData : d = d' := by
    by_contra ne
    rcases List.mem_iff_getElem.mp hd with ⟨i, hi, rfl⟩
    rcases List.mem_iff_getElem.mp hd' with ⟨j, hj, rfl⟩
    have ij : i ≠ j := fun same => ne (by subst same; rfl)
    rcases Nat.lt_or_gt_of_ne ij with lt | gt
    · have := List.pairwise_iff_getElem.mp pairwise i j hi hj lt
      exact this (List.mem_map.mpr ⟨_, hc, rfl⟩) (List.mem_map.mpr ⟨_, hc', rfl⟩)
    · have := List.pairwise_iff_getElem.mp pairwise j i hj hi gt
      exact this (List.mem_map.mpr ⟨_, hc', rfl⟩) (List.mem_map.mpr ⟨_, hc, rfl⟩)
  subst sameData
  refine ⟨rfl, ?_⟩
  have := List.inj_on_of_nodup_map (each d hd) hc hc' rfl
  exact (Prod.mk.inj this).2

/-- A function name belongs to one declaration. -/
theorem fun_unique {fd fd' : FunDecl S} (h : fd ∈ sig.funs) (h' : fd' ∈ sig.funs)
    (same : fd.name = fd'.name) : fd = fd' :=
  List.inj_on_of_nodup_map wf.funNames h h' same

/-- No function is a constructor of a datatype. -/
theorem fun_not_ctor {fd : FunDecl S} {d : DataDecl S} {fields : List Sort'} (h : fd ∈ sig.funs)
    (hd : d ∈ sig.data) (hc : (fd.name, fields) ∈ d.ctors) : False :=
  wf.disjoint fd h (List.mem_flatMap.mpr ⟨d, hd, List.mem_map_of_mem hc⟩)

end Signature.WellFormed

/-- A constructor name of a signature is the constructor of some datatype. -/
theorem Signature.mem_ctorNames {sig : Signature S} {c : S} :
    c ∈ sig.ctorNames ↔ ∃ d ∈ sig.data, ∃ fields, (c, fields) ∈ d.ctors := by
  simp only [Signature.ctorNames, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨d, hd, ⟨c', fields⟩, hc, rfl⟩; exact ⟨d, hd, fields, hc⟩
  · rintro ⟨d, hd, fields, hc⟩; exact ⟨d, hd, (c, fields), hc, rfl⟩

/-! ## Inversion and substitution -/

namespace HasSort

variable {sig : Signature S} {Γ : Ctx}

/-- **Inversion at an application**: the head is a constructor or a declared function. -/
theorem app_inv {h : S} {args : List (Tm S)} {τ : Sort'} (typed : HasSort sig Γ (.app h args) τ) :
    (∃ d ∈ sig.data, ∃ fields, (h, fields) ∈ d.ctors ∧ ∃ θ, τ = d.sort.subst θ ∧
        Pointwise (HasSort sig Γ) args (fields.map (Tm.subst θ))) ∨
      (∃ fd ∈ sig.funs, fd.name = h ∧ ∃ θ, τ = fd.result.subst θ ∧
        Pointwise (HasSort sig Γ) args (fd.args.map (Tm.subst θ))) := by
  cases typed with
  | ctor θ hd hc len each =>
      exact .inl ⟨_, hd, _, hc, θ, rfl, by simpa using len,
        fun i hi hj => by simpa using each i hi (by simpa using hj)⟩
  | call θ hfd len each =>
      exact .inr ⟨_, hfd, rfl, θ, rfl, by simpa using len,
        fun i hi hj => by simpa using each i hi (by simpa using hj)⟩

/-- No variable has a sort in the empty context. -/
theorem not_var_empty {x : String} {τ : Sort'} : ¬ HasSort sig Ctx.empty (.var x) τ := by
  intro typed
  cases typed with
  | var h => cases h

/-- A term with a sort in the empty context is closed. -/
theorem closed_of_empty : ∀ {t : Tm S} {τ : Sort'}, HasSort sig Ctx.empty t τ → t.Closed := by
  intro t
  induction t using Tm.induction' with
  | var x => intro τ typed; exact absurd typed not_var_empty
  | app h args ih =>
      intro τ typed
      have each : ∀ a ∈ args, a.Closed := by
        intro a member
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp member
        rcases app_inv typed with ⟨d, _, fields, _, θ, _, len, typedArgs⟩ |
            ⟨fd, _, _, θ, _, len, typedArgs⟩
        · exact ih _ member (typedArgs i hi (by simpa [← len] using hi))
        · exact ih _ member (typedArgs i hi (by simpa [← len] using hi))
      simp only [Closed, vars_app, List.flatMap_eq_nil_iff]
      exact each

/-- **Sort substitution**: a sorting at sort variables holds at every instTyped of them. -/
theorem substSort (ρ : String → Sort') :
    ∀ {t : Tm S} {τ : Sort'}, HasSort sig Γ t τ →
      HasSort sig (fun x => (Γ x).map (Tm.subst ρ)) t (τ.subst ρ) := by
  intro t τ typed
  induction typed with
  | var h => exact .var (by simp [h])
  | @ctor d c fields args θ hd hc len each ih =>
      rw [subst_subst]
      exact .ctor _ hd hc len fun i hi hj => by
        have := ih i hi hj
        rwa [subst_subst] at this
  | @call fd args θ hfd len each ih =>
      rw [subst_subst]
      exact .call _ hfd len fun i hi hj => by
        have := ih i hi hj
        rwa [subst_subst] at this

/-- **Term substitution**: instantiating the variables of a term by terms of their sorts keeps
its sort. Only the variables of the term are read. -/
theorem substTerm {Δ : Ctx} (σ : String → Tm S) :
    ∀ {t : Tm S} {τ : Sort'}, HasSort sig Γ t τ →
      (∀ x ∈ t.vars, ∀ τx, Γ x = some τx → HasSort sig Δ (σ x) τx) →
      HasSort sig Δ (t.subst σ) τ := by
  intro t τ typed
  induction typed with
  | @var x τ h => intro instances; exact instances x (by simp) τ h
  | @ctor d c fields args θ hd hc len each ih =>
      intro instances
      rw [subst_app]
      exact .ctor θ hd hc (by simpa using len) fun i hi hj => by
        simp only [List.getElem_map]
        exact ih i (by simpa using hi) hj fun x hx τx hτ =>
          instances x (by simpa using ⟨args[i], List.getElem_mem _, hx⟩) τx hτ
  | @call fd args θ hfd len each ih =>
      intro instances
      rw [subst_app]
      exact .call θ hfd (by simpa using len) fun i hi hj => by
        simp only [List.getElem_map]
        exact ih i (by simpa using hi) hj fun x hx τx hτ =>
          instances x (by simpa using ⟨args[i], List.getElem_mem _, hx⟩) τx hτ

end HasSort

/-! ## Patterns invert their instances -/

/-- Two instances of a datatype's sort that agree are instances by substitutions that agree on
its parameters. -/
theorem DataDecl.sort_subst_inj (d : DataDecl S) {θ θ' : String → Sort'}
    (same : d.sort.subst θ = d.sort.subst θ') : ∀ a ∈ d.params, θ a = θ' a := by
  intro a member
  simp only [DataDecl.sort, subst_app, List.map_map, app.injEq, true_and] at same
  have := congrArg (fun l => l.map id) same
  have hmap := List.map_inj_left.mp same a member
  simpa using hmap

namespace HasSort

variable {sig : Signature S}

/-- **Pattern inversion**: when an instTyped of a constructor pattern has an instTyped of the
pattern's sort, every variable of the pattern is instantiated by a term of the corresponding
instTyped of its sort. -/
theorem pattern_inversion (wf : sig.WellFormed) {Γ Δ : Ctx} (σ : String → Tm S)
    (ρ : String → Sort') :
    ∀ {p : Tm S} {τ : Sort'}, HasSort sig Γ p τ → IsPattern sig p →
      HasSort sig Δ (p.subst σ) (τ.subst ρ) →
      ∀ x ∈ p.vars, ∀ τx, Γ x = some τx → HasSort sig Δ (σ x) (τx.subst ρ) := by
  intro p τ typed
  induction typed with
  | @var x τ h =>
      intro _ instTyped y member τy hy
      simp only [vars_var, List.mem_singleton] at member
      subst member
      rw [h] at hy
      cases hy
      simpa using instTyped
  | @ctor d c fields args θ hd hc len each ih =>
      intro pattern instTyped y member τy hy
      cases pattern with
      | ctor _ argsPatterns =>
      rw [subst_app, subst_subst] at instTyped
      rcases app_inv instTyped with ⟨d', hd', fields', hc', θ', hsort, len', typedArgs⟩ |
          ⟨fd, hfd, hname, _, _, _⟩
      · obtain ⟨rfl, rfl⟩ := wf.ctor_unique hd hd' hc hc'
        have agree := DataDecl.sort_subst_inj d hsort
        simp only [vars_app, List.mem_flatMap] at member
        obtain ⟨a, aMember, yMember⟩ := member
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp aMember
        have hj : i < fields.length := by rw [← len]; exact hi
        apply ih i hi hj (argsPatterns _ aMember)
        · have := typedArgs i (by simpa using hi) (by simpa using hj)
          simp only [List.getElem_map] at this
          rw [subst_subst]
          convert this using 1
          apply subst_congr
          intro b hb
          have bParam := (wf.params d hd).2 (c, fields) hc fields[i] (List.getElem_mem _) b hb
          exact agree b bParam
        · exact yMember
        · exact hy
      · exact absurd hc (fun hc => wf.fun_not_ctor hfd hd (hname ▸ hc))
  | @call fd args θ hfd _ _ _ =>
      intro pattern
      cases pattern with
      | ctor isCtor _ =>
          obtain ⟨d, hd, fields, hc⟩ := Signature.mem_ctorNames.mp isCtor
          exact absurd hc (fun hc => wf.fun_not_ctor hfd hd hc)

end HasSort

/-! ## Subject reduction -/

/-- In a well-formed signature that types the program, symbols that are constructors head no
equation. -/
theorem Signature.not_defines_ctor {sig : Signature S} {P : Program S} (wf : sig.WellFormed)
    (typesP : sig.TypesProgram P) {c : S} (isCtor : c ∈ sig.ctorNames) : ¬ P.Defines c := by
  rintro ⟨e, eMember, head⟩
  obtain ⟨fd, hfd, ps, Γ, hlhs, _⟩ := typesP e eMember
  rw [hlhs] at head
  simp only [head?, Option.some.injEq] at head
  exact wf.disjoint fd hfd (head ▸ isCtor)

/-- A program typed by a signature is headed. -/
theorem Signature.TypesProgram.headed {sig : Signature S} {P : Program S}
    (typesP : sig.TypesProgram P) : P.Headed := by
  intro e eMember
  obtain ⟨fd, _, ps, _, hlhs, _⟩ := typesP e eMember
  exact ⟨fd.name, ps, hlhs⟩

namespace HasSort

variable {sig : Signature S} {P : Program S}

/-- **A root step keeps the sort.** -/
theorem rootStep (wf : sig.WellFormed) (typesP : sig.TypesProgram P) (bound : P.RightBound)
    {Δ : Ctx} {s t : Tm S} {τ : Sort'} (step : RootStep P s t) (typed : HasSort sig Δ s τ) :
    HasSort sig Δ t τ := by
  obtain ⟨e, eMember, σ, rfl, rfl⟩ := step.exists_rule
  obtain ⟨fd, hfd, ps, Γ, hlhs, patterns, ⟨len, typedPs⟩, typedRhs⟩ := typesP e eMember
  rw [hlhs, subst_app] at typed
  rcases app_inv typed with ⟨d, hd, fields, hc, _, _, _⟩ | ⟨fd', hfd', hname, θ, rfl, len', typedArgs⟩
  · exact absurd hc (fun hc => wf.fun_not_ctor hfd hd hc)
  · obtain rfl := wf.fun_unique hfd' hfd hname
    have varsOk : ∀ x ∈ e.rhs.vars, ∀ τx, (fun y => (Γ y).map (Tm.subst θ)) x = some τx →
        HasSort sig Δ (σ x) τx := by
      intro x hx τx hτ
      have hl := bound e eMember x hx
      rw [hlhs, vars_app, List.mem_flatMap] at hl
      obtain ⟨p, pMember, xMember⟩ := hl
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp pMember
      simp only [Option.map_eq_some_iff] at hτ
      obtain ⟨τ0, h0, rfl⟩ := hτ
      have hj : i < fd'.args.length := by rw [← len]; exact hi
      apply pattern_inversion wf σ θ (typedPs i hi hj) (patterns _ pMember) _ x xMember τ0 h0
      have := typedArgs i (by simpa using hi) (by simpa using hj)
      simpa using this
    exact substTerm σ (substSort θ typedRhs) varsOk

/-- **Subject reduction**: a step keeps the sort of a term. -/
theorem step (wf : sig.WellFormed) (typesP : sig.TypesProgram P) (bound : P.RightBound) {Δ : Ctx} :
    ∀ {s t : Tm S}, Step P s t → ∀ {τ : Sort'}, HasSort sig Δ s τ → HasSort sig Δ t τ := by
  intro s t stepped
  induction stepped with
  | root root => intro τ typed; exact rootStep wf typesP bound root typed
  | @arg h args i lt b _ ih =>
      intro τ typed
      have setArgs : ∀ (sorts : List Sort'), Pointwise (HasSort sig Δ) args sorts →
          Pointwise (HasSort sig Δ) (args.set i b) sorts := by
        rintro sorts ⟨len, each⟩
        refine ⟨by simpa using len, fun j hj hk => ?_⟩
        by_cases same : i = j
        · subst same
          simp only [List.getElem_set_self]
          exact ih (each i lt hk)
        · simp only [List.getElem_set_ne same]
          exact each j (by simpa using hj) hk
      rcases app_inv typed with ⟨d, hd, fields, hc, θ, rfl, typedArgs⟩ |
          ⟨fd, hfd, rfl, θ, rfl, typedArgs⟩
      · obtain ⟨len, each⟩ := setArgs _ typedArgs
        exact .ctor θ hd hc (by simpa using len) fun j hj hk => by
          have := each j hj (by simpa using hk)
          simpa only [List.getElem_map] using this
      · obtain ⟨len, each⟩ := setArgs _ typedArgs
        exact .call θ hfd (by simpa using len) fun j hj hk => by
          have := each j hj (by simpa using hk)
          simpa only [List.getElem_map] using this

/-- Subject reduction along many steps. -/
theorem steps (wf : sig.WellFormed) (typesP : sig.TypesProgram P) (bound : P.RightBound) {Δ : Ctx}
    {s t : Tm S} (steps : Relation.ReflTransGen (Step P) s t) {τ : Sort'}
    (typed : HasSort sig Δ s τ) : HasSort sig Δ t τ := by
  induction steps with
  | refl => exact typed
  | tail _ last ih => exact step wf typesP bound last ih

/-- **Closed normal forms are data**: under coverage, a sorted term of the empty context that
takes no step is built from declared constructors. -/
theorem data_of_normal (covers : sig.Covers P) :
    ∀ {t : Tm S} {τ : Sort'}, HasSort sig Ctx.empty t τ → IsNormal (Step P) t → sig.IsData t := by
  intro t
  induction t using Tm.induction' with
  | var x => intro τ typed; exact absurd typed not_var_empty
  | app h args ih =>
      intro τ typed normal
      have argNormal : ∀ i (hi : i < args.length), IsNormal (Step P) args[i] := by
        intro i hi target stepAt
        exact normal _ (Step.arg h args i hi stepAt)
      rcases app_inv typed with ⟨d, hd, fields, hc, θ, rfl, len, typedArgs⟩ |
          ⟨fd, hfd, rfl, θ, rfl, len, typedArgs⟩
      · refine .app (Signature.mem_ctorNames.mpr ⟨d, hd, fields, hc⟩) fun a member => ?_
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp member
        exact ih _ member (typedArgs i hi (by simpa [← len] using hi)) (argNormal i hi)
      · exfalso
        have values : Pointwise sig.IsValueOf args (fd.args.map (Tm.subst θ)) :=
          ⟨len, fun i hi hj => ⟨ih _ (List.getElem_mem hi) (typedArgs i hi hj) (argNormal i hi),
            typedArgs i hi hj⟩⟩
        obtain ⟨e, eMember, σ, hσ⟩ := covers fd hfd θ args values
        exact normal _ (Step.root (hσ ▸ RootStep.rule σ eMember))

/-- Data of a signature that types the program is a value: no symbol of it heads an equation. -/
theorem _root_.Mettapedia.Languages.MeTTa.DeclarationFaces.Signature.IsData.isValue
    (wf : sig.WellFormed) (typesP : sig.TypesProgram P) : ∀ {v : Tm S}, sig.IsData v → IsValue P v := by
  intro v data
  induction data with
  | app isCtor _ ih => exact .app (Signature.not_defines_ctor wf typesP isCtor) ih

/-- **Closed normal forms are values** under coverage. -/
theorem value_of_normal (wf : sig.WellFormed) (typesP : sig.TypesProgram P) (covers : sig.Covers P)
    {t : Tm S} {τ : Sort'} (typed : HasSort sig Ctx.empty t τ) (normal : IsNormal (Step P) t) :
    IsValue P t :=
  (data_of_normal covers typed normal).isValue wf typesP

end HasSort

end Mettapedia.Languages.MeTTa.DeclarationFaces
