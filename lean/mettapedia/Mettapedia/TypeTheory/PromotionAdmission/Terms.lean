import Mathlib.Logic.Relation
import Mathlib.Data.List.Forall2
import Mathlib.Order.Basic

/-!
# First-order terms, rules and their rewriting steps

The rules a bubble may promote are equations between first-order terms: variables, and
symbols applied to lists of arguments. A rule `l ↦ r` rewrites any instance of `l`, at any
position, to the same instance of `r`. This module fixes the syntax shared by the admission
criterion.

* `Term F V`: terms over symbols `F` and variables `V`. A symbol may be applied to any number
  of arguments, as in a MeTTa expression; `app f []` is a constant.
* `Term.subst`: instantiation of variables by terms over another variable type. It is the bind
  of the term monad: `subst_subst` composes, `subst_var` is the unit.
* `Step R`: one rewrite step of the rule list `R`, at the root (`Step.root`) or inside one
  argument (`Step.arg`). Steps are closed under instantiation (`Step.subst`) and under contexts
  (`Step.fill`).
* `Ctx`: one-hole contexts. `Term.positions` lists every decomposition of a term into a context
  and a subterm that is not a variable: exactly the places where another rule can overlap
  (`mem_positions_iff`).
* `Interpretation`: a model of the symbols. A rule is valid when its two sides have equal
  values under every valuation; then every conversion of valid rules is an equality of values
  (`conv_sound`).

Positive example: `add x zero ↦ x` rewrites `add (succ y) zero` to `succ y` at the root.
Negative example: the variable `x` is not a non-variable position of `add x zero`, so no
overlap is ever sought there.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PromotionAdmission

universe u v w w' uD

/-- A first-order term: a variable, or a symbol applied to a list of arguments. -/
inductive Term (F : Type u) (V : Type v) where
  | var (x : V)
  | app (f : F) (args : List (Term F V))
  deriving Repr

namespace Term

variable {F : Type u} {V : Type v} {W : Type w} {X : Type w'}

/-- Induction on terms with a hypothesis for every argument of an application. -/
@[elab_as_elim]
theorem induction' {motive : Term F V → Prop} (var : ∀ x, motive (.var x))
    (app : ∀ f args, (∀ a ∈ args, motive a) → motive (.app f args)) (t : Term F V) :
    motive t :=
  Term.rec (motive_1 := motive) (motive_2 := fun args => ∀ a ∈ args, motive a) var
    (fun f args ih => app f args ih) (fun _ member => absurd member List.not_mem_nil)
    (fun first rest hFirst hRest a member => by
      rcases List.mem_cons.mp member with same | later
      · exact same ▸ hFirst
      · exact hRest a later) t

section DecEq

variable [DecidableEq F] [DecidableEq V]

mutual
/-- Decidable equality of terms. -/
def decEq : (s t : Term F V) → Decidable (s = t)
  | .var x, .var y =>
      if h : x = y then isTrue (h ▸ rfl) else isFalse (fun same => h (Term.var.inj same))
  | .var _, .app _ _ => isFalse (fun same => by cases same)
  | .app _ _, .var _ => isFalse (fun same => by cases same)
  | .app f as, .app g bs =>
      if hf : f = g then
        match decEqList as bs with
        | isTrue ha => isTrue (hf ▸ ha ▸ rfl)
        | isFalse ha => isFalse (fun same => ha (Term.app.inj same).2)
      else isFalse (fun same => hf (Term.app.inj same).1)
/-- Decidable equality of lists of terms. -/
def decEqList : (as bs : List (Term F V)) → Decidable (as = bs)
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

instance : DecidableEq (Term F V) := decEq

end DecEq

/-- The head symbol of an application. -/
def head? : Term F V → Option F
  | .var _ => none
  | .app f _ => some f

/-- An application, not a variable. -/
def isApp : Term F V → Bool
  | .var _ => false
  | .app _ _ => true

theorem isApp_iff (t : Term F V) : t.isApp = true ↔ ∃ f args, t = .app f args := by
  cases t <;> simp [isApp]

mutual
/-- The variables of a term, in order of occurrence, with repetitions. -/
def vars : Term F V → List V
  | .var x => [x]
  | .app _ args => varsList args
/-- The variables of a list of terms. -/
def varsList : List (Term F V) → List V
  | [] => []
  | a :: as => vars a ++ varsList as
end

theorem varsList_eq (args : List (Term F V)) : varsList args = args.flatMap vars := by
  induction args with
  | nil => rfl
  | cons a as ih => simp [varsList, ih]

@[simp] theorem vars_var (x : V) : (Term.var x : Term F V).vars = [x] := by simp [vars]

@[simp] theorem vars_app (f : F) (args : List (Term F V)) :
    (Term.app f args).vars = args.flatMap vars := by
  simp [vars, varsList_eq]

mutual
/-- The symbols of a term, with repetitions. -/
def symbols : Term F V → List F
  | .var _ => []
  | .app f args => f :: symbolsList args
/-- The symbols of a list of terms. -/
def symbolsList : List (Term F V) → List F
  | [] => []
  | a :: as => symbols a ++ symbolsList as
end

theorem symbolsList_eq (args : List (Term F V)) : symbolsList args = args.flatMap symbols := by
  induction args with
  | nil => rfl
  | cons a as ih => simp [symbolsList, ih]

@[simp] theorem symbols_var (x : V) : (Term.var x : Term F V).symbols = [] := by simp [symbols]

@[simp] theorem symbols_app (f : F) (args : List (Term F V)) :
    (Term.app f args).symbols = f :: args.flatMap symbols := by
  simp [symbols, symbolsList_eq]

mutual
/-- The number of nodes of a term. -/
def size : Term F V → ℕ
  | .var _ => 1
  | .app _ args => sizeList args + 1
/-- The number of nodes of a list of terms. -/
def sizeList : List (Term F V) → ℕ
  | [] => 0
  | a :: as => size a + sizeList as
end

theorem sizeList_eq (args : List (Term F V)) : sizeList args = (args.map size).sum := by
  induction args with
  | nil => rfl
  | cons a as ih => simp [sizeList, ih]

@[simp] theorem size_var (x : V) : (Term.var x : Term F V).size = 1 := by simp [size]

@[simp] theorem size_app (f : F) (args : List (Term F V)) :
    (Term.app f args).size = (args.map size).sum + 1 := by
  simp [size, sizeList_eq]

theorem size_pos (t : Term F V) : 0 < t.size := by
  cases t <;> simp

/-! ## Instantiation -/

mutual
/-- Instantiate every variable by a term over another variable type. -/
def subst (σ : V → Term F W) : Term F V → Term F W
  | .var x => σ x
  | .app f args => .app f (substList σ args)
/-- Instantiate every variable of a list of terms. -/
def substList (σ : V → Term F W) : List (Term F V) → List (Term F W)
  | [] => []
  | a :: as => subst σ a :: substList σ as
end

theorem substList_eq (σ : V → Term F W) (args : List (Term F V)) :
    substList σ args = args.map (subst σ) := by
  induction args with
  | nil => rfl
  | cons a as ih => simp [substList, ih]

@[simp] theorem subst_var (σ : V → Term F W) (x : V) : (Term.var x).subst σ = σ x := by
  simp [subst]

@[simp] theorem subst_app (σ : V → Term F W) (f : F) (args : List (Term F V)) :
    (Term.app f args).subst σ = .app f (args.map (subst σ)) := by
  simp [subst, substList_eq]

/-- Instantiation reads only the variables of the term. -/
theorem subst_congr {σ τ : V → Term F W} :
    ∀ t : Term F V, (∀ x ∈ t.vars, σ x = τ x) → t.subst σ = t.subst τ := by
  intro t
  induction t using Term.induction' with
  | var x => intro agree; simpa using agree x (by simp)
  | app f args ih =>
      intro agree
      simp only [subst_app, app.injEq, true_and]
      apply List.map_congr_left
      intro a member
      exact ih a member fun x hx => agree x (by simpa using ⟨a, member, hx⟩)

/-- Instantiating every variable by itself is the identity. -/
theorem subst_id : ∀ t : Term F V, t.subst Term.var = t := by
  intro t
  induction t using Term.induction' with
  | var x => rfl
  | app f args ih =>
      simp only [subst_app, app.injEq, true_and]
      conv_rhs => rw [← List.map_id args]
      exact List.map_congr_left ih

/-- Instantiating twice is instantiating once by the composite. -/
theorem subst_subst (σ : V → Term F W) (τ : W → Term F X) :
    ∀ t : Term F V, (t.subst σ).subst τ = t.subst (fun x => (σ x).subst τ) := by
  intro t
  induction t using Term.induction' with
  | var x => rfl
  | app f args ih =>
      simp only [subst_app, List.map_map, app.injEq, true_and]
      exact List.map_congr_left fun a member => ih a member

/-- The variables of an instance are the variables of the instantiating terms. -/
theorem vars_subst (σ : V → Term F W) :
    ∀ t : Term F V, (t.subst σ).vars = t.vars.flatMap fun x => (σ x).vars := by
  intro t
  induction t using Term.induction' with
  | var x => simp
  | app f args ih =>
      simp only [subst_app, vars_app, List.flatMap_map, List.flatMap_assoc]
      exact List.flatMap_congr fun a member => ih a member

/-- Renaming of variables. -/
def rename (g : V → W) (t : Term F V) : Term F W := t.subst fun x => .var (g x)

/-- A member of a list of numbers is at most its sum. -/
theorem nat_le_sum_of_mem {xs : List ℕ} {x : ℕ} (member : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at member
  | cons y ys ih =>
      simp only [List.mem_cons] at member
      simp only [List.sum_cons]
      rcases member with rfl | later
      · omega
      · have := ih later; omega

/-- A variable's value is no larger than an instance of a term in which it occurs. -/
theorem size_le_subst_of_mem (σ : V → Term F W) {x : V} :
    ∀ t : Term F V, x ∈ t.vars → (σ x).size ≤ (t.subst σ).size := by
  intro t
  induction t using Term.induction' with
  | var y => intro member; simp at member; subst member; simp
  | app f args ih =>
      intro member
      simp only [vars_app, List.mem_flatMap] at member
      obtain ⟨a, aMember, xMember⟩ := member
      have inner := ih a aMember xMember
      simp only [subst_app, size_app, List.map_map]
      have le : (a.subst σ).size ≤ (args.map ((size) ∘ subst σ)).sum :=
        nat_le_sum_of_mem (List.mem_map_of_mem aMember)
      omega

/-- **The occurs check**: a variable occurring strictly inside an application is strictly
smaller than every instance of the application. -/
theorem size_lt_subst_of_mem_app (σ : V → Term F W) {x : V} {f : F} {args : List (Term F V)}
    (member : x ∈ (Term.app f args).vars) : (σ x).size < ((Term.app f args).subst σ).size := by
  simp only [vars_app, List.mem_flatMap] at member
  obtain ⟨a, aMember, xMember⟩ := member
  have inner := size_le_subst_of_mem σ a xMember
  simp only [subst_app, size_app, List.map_map]
  have le : (a.subst σ).size ≤ (args.map ((size) ∘ subst σ)).sum :=
    nat_le_sum_of_mem (List.mem_map_of_mem aMember)
  omega

end Term

/-! ## Rules and steps -/

/-- A rewrite rule `lhs ↦ rhs`. -/
structure Rule (F : Type u) (V : Type v) where
  lhs : Term F V
  rhs : Term F V
  deriving Repr

namespace Rule

variable {F : Type u} {V : Type v}

/-- **The rule format**: the left side is an application and the right side uses only its
variables. Without the first, a rule rewrites every term; without the second, an instance is
not determined by the term it rewrites. -/
def WellFormed (ρ : Rule F V) : Prop :=
  ρ.lhs.isApp = true ∧ ∀ x ∈ ρ.rhs.vars, x ∈ ρ.lhs.vars

/-- The executable test of the rule format. -/
def wellFormed [DecidableEq V] (ρ : Rule F V) : Bool :=
  ρ.lhs.isApp && ρ.rhs.vars.all fun x => decide (x ∈ ρ.lhs.vars)

theorem wellFormed_iff [DecidableEq V] (ρ : Rule F V) : ρ.wellFormed = true ↔ ρ.WellFormed := by
  simp [wellFormed, WellFormed]

end Rule

open Term

variable {F : Type u} {V : Type v} {W : Type w} {X : Type w'}

/-- One rewrite step of a rule list, at the root or inside one argument. -/
inductive Step (R : List (Rule F V)) : Term F W → Term F W → Prop where
  | root {ρ : Rule F V} (mem : ρ ∈ R) (σ : V → Term F W) :
      Step R (ρ.lhs.subst σ) (ρ.rhs.subst σ)
  | arg (f : F) (args : List (Term F W)) (i : ℕ) (h : i < args.length) {t' : Term F W} :
      Step R args[i] t' → Step R (.app f args) (.app f (args.set i t'))

/-- Reduction: finitely many steps. -/
abbrev Steps (R : List (Rule F V)) : Term F W → Term F W → Prop :=
  Relation.ReflTransGen (Step R)

namespace Step

variable {R : List (Rule F V)}

theorem set_middle (pre post : List (Term F W)) (a a' : Term F W) :
    (pre ++ a :: post).set pre.length a' = pre ++ a' :: post := by
  simp [List.set_append_right]

/-- A step inside the argument between `pre` and `post`. -/
theorem inArg (f : F) (pre post : List (Term F W)) {a a' : Term F W} (step : Step R a a') :
    Step R (.app f (pre ++ a :: post)) (.app f (pre ++ a' :: post)) := by
  have h : pre.length < (pre ++ a :: post).length := by simp
  have stepped := Step.arg (R := R) f (pre ++ a :: post) pre.length h
    (t' := a') (by simpa using step)
  rwa [set_middle] at stepped

/-- **Steps are stable under instantiation.** -/
theorem subst (τ : W → Term F X) {s t : Term F W} (step : Step R s t) :
    Step R (s.subst τ) (t.subst τ) := by
  induction step with
  | root mem σ =>
      rw [subst_subst, subst_subst]
      exact .root mem _
  | arg f args i h inner ih =>
      simp only [subst_app, List.map_set]
      exact .arg f (args.map (Term.subst τ)) i (by simpa using h) (by simpa using ih)

/-- Steps of a sublist of rules are steps of the larger list. -/
theorem mono {R R' : List (Rule F V)} (sub : ∀ ρ ∈ R, ρ ∈ R') {s t : Term F W}
    (step : Step R s t) : Step R' s t := by
  induction step with
  | root mem σ => exact .root (sub _ mem) σ
  | arg f args i h _ ih => exact .arg f args i h ih

end Step

namespace Steps

variable {R : List (Rule F V)}

theorem inArg (f : F) (pre post : List (Term F W)) {a a' : Term F W} (steps : Steps R a a') :
    Steps R (.app f (pre ++ a :: post)) (.app f (pre ++ a' :: post)) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Step.inArg f pre post step)

/-- Reduction of every argument is reduction of the application. -/
theorem args (f : F) : ∀ {as bs : List (Term F W)} (pre : List (Term F W)),
    List.Forall₂ (Steps R) as bs → Steps R (.app f (pre ++ as)) (.app f (pre ++ bs))
  | _, _, _, .nil => .refl
  | a :: as, b :: bs, pre, .cons head tail => by
      have first := Steps.inArg (R := R) f pre as head
      have rest := Steps.args f (pre ++ [b]) tail
      simp only [List.append_assoc, List.singleton_append] at rest
      exact first.trans rest

theorem subst (τ : W → Term F X) {s t : Term F W} (steps : Steps R s t) :
    Steps R (s.subst τ) (t.subst τ) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.subst τ)

/-- **Reduction of the instantiating terms is reduction of the instance.** -/
theorem subst_pointwise {σ τ : X → Term F W} (each : ∀ x, Steps R (σ x) (τ x)) :
    ∀ t : Term F X, Steps R (t.subst σ) (t.subst τ) := by
  intro t
  induction t using Term.induction' with
  | var x => simpa using each x
  | app f args ih =>
      simp only [subst_app]
      have pointwise : List.Forall₂ (Steps R) (args.map (Term.subst σ)) (args.map (Term.subst τ)) := by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact List.forall₂_same.mpr ih
      simpa using Steps.args (R := R) f [] pointwise

theorem mono {R R' : List (Rule F V)} (sub : ∀ ρ ∈ R, ρ ∈ R') {s t : Term F W}
    (steps : Steps R s t) : Steps R' s t := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.mono sub)

end Steps

/-! ## Contexts and non-variable positions -/

/-- A one-hole context. -/
inductive Ctx (F : Type u) (V : Type v) where
  | hole
  | app (f : F) (before : List (Term F V)) (inner : Ctx F V) (after : List (Term F V))
  deriving Repr

namespace Ctx

/-- Put a term in the hole. -/
def fill : Ctx F V → Term F V → Term F V
  | .hole, t => t
  | .app f before inner after, t => .app f (before ++ inner.fill t :: after)

/-- Instantiate the variables of a context. -/
def subst (σ : V → Term F W) : Ctx F V → Ctx F W
  | .hole => .hole
  | .app f before inner after =>
      .app f (before.map (Term.subst σ)) (inner.subst σ) (after.map (Term.subst σ))

theorem fill_subst (σ : V → Term F W) (c : Ctx F V) (t : Term F V) :
    (c.fill t).subst σ = (c.subst σ).fill (t.subst σ) := by
  induction c with
  | hole => rfl
  | app f before inner after ih => simp [fill, subst, ih]

theorem subst_subst (σ : V → Term F W) (τ : W → Term F X) (c : Ctx F V) :
    (c.subst σ).subst τ = c.subst (fun x => (σ x).subst τ) := by
  induction c with
  | hole => rfl
  | app f before inner after ih =>
      simp [subst, ih, List.map_map, Function.comp_def, Term.subst_subst]

/-- A step in the hole is a step of the filled context. -/
theorem step_fill {R : List (Rule F V)} (c : Ctx F W) {s t : Term F W} (step : Step R s t) :
    Step R (c.fill s) (c.fill t) := by
  induction c with
  | hole => exact step
  | app f before inner after ih => exact Step.inArg f before after ih

theorem steps_fill {R : List (Rule F V)} (c : Ctx F W) {s t : Term F W} (steps : Steps R s t) :
    Steps R (c.fill s) (c.fill t) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step_fill c step)

end Ctx

namespace Term

mutual
/-- **Non-variable positions**: every way to write the term as a context filled with an
application. -/
def positions : Term F V → List (Ctx F V × Term F V)
  | .var _ => []
  | .app f args => (.hole, .app f args) :: positionsList f [] args
/-- Non-variable positions inside the arguments after `before`. -/
def positionsList (f : F) (before : List (Term F V)) :
    List (Term F V) → List (Ctx F V × Term F V)
  | [] => []
  | a :: after =>
      (positions a).map (fun p => (.app f before p.1 after, p.2)) ++
        positionsList f (before ++ [a]) after
end

theorem mem_positionsList_middle (f : F) (c : Ctx F V) (s : Term F V) :
    ∀ (xs : List (Term F V)) (before : List (Term F V)) (a : Term F V) (ys : List (Term F V)),
      (c, s) ∈ a.positions →
        (Ctx.app f (before ++ xs) c ys, s) ∈ positionsList f before (xs ++ a :: ys)
  | [], before, a, ys, member => by
      simp only [List.nil_append, positionsList, List.append_nil, List.mem_append, List.mem_map]
      exact Or.inl ⟨(c, s), member, rfl⟩
  | x :: xs, before, a, ys, member => by
      simp only [List.cons_append, positionsList, List.mem_append]
      right
      have := mem_positionsList_middle f c s xs (before ++ [x]) a ys member
      simpa using this

/-- **Every decomposition into a context and an application is listed.** -/
theorem mem_positions_fill {s : Term F V} (app : s.isApp = true) :
    ∀ c : Ctx F V, (c, s) ∈ (c.fill s).positions := by
  intro c
  induction c with
  | hole =>
      obtain ⟨f, args, rfl⟩ := (isApp_iff s).mp app
      simp [Ctx.fill, positions]
  | app f before inner after ih =>
      simp only [Ctx.fill, positions, List.mem_cons]
      right
      simpa using mem_positionsList_middle f inner s before [] (inner.fill s) after ih

theorem positions_spec :
    ∀ (t : Term F V) (c : Ctx F V) (s : Term F V), (c, s) ∈ t.positions →
      c.fill s = t ∧ s.isApp = true := by
  intro t
  induction t using Term.induction' with
  | var x => intro c s member; simp [positions] at member
  | app f args ih =>
      intro c s member
      simp only [positions, List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩ | inner
      · exact ⟨rfl, rfl⟩
      · have general : ∀ (rest before : List (Term F V)), (∀ a ∈ rest, a ∈ args) →
            (c, s) ∈ positionsList f before rest →
              c.fill s = .app f (before ++ rest) ∧ s.isApp = true := by
          intro rest
          induction rest with
          | nil => intro before _ member; simp [positionsList] at member
          | cons a after ihRest =>
              intro before sub member
              simp only [positionsList, List.mem_append, List.mem_map] at member
              rcases member with ⟨⟨c', s'⟩, member', same⟩ | later
              · simp only [Prod.mk.injEq] at same
                obtain ⟨rfl, rfl⟩ := same
                obtain ⟨filled, isApp⟩ := ih a (sub a (by simp)) c' s' member'
                exact ⟨by simp [Ctx.fill, filled], isApp⟩
              · have := ihRest (before ++ [a]) (fun b hb => sub b (by simp [hb])) later
                simpa using this
        simpa using general args [] (fun a h => h) inner

/-- **Non-variable positions are exactly the decompositions into a context and an
application.** -/
theorem mem_positions_iff (t : Term F V) (c : Ctx F V) (s : Term F V) :
    (c, s) ∈ t.positions ↔ c.fill s = t ∧ s.isApp = true := by
  constructor
  · exact positions_spec t c s
  · rintro ⟨rfl, app⟩
    exact mem_positions_fill app c

end Term

/-! ## Models -/

/-- A model of the symbols: each symbol is an operation on a list of values. -/
structure Interpretation (F : Type u) (D : Type w) where
  op : F → List D → D

namespace Interpretation

variable {D : Type uD} (I : Interpretation F D)

mutual
/-- The value of a term under a valuation. -/
def eval (α : W → D) : Term F W → D
  | .var x => α x
  | .app f args => I.op f (evalList α args)
/-- The values of a list of terms. -/
def evalList (α : W → D) : List (Term F W) → List D
  | [] => []
  | a :: as => eval α a :: evalList α as
end

theorem evalList_eq (α : W → D) (args : List (Term F W)) :
    I.evalList α args = args.map (I.eval α) := by
  induction args with
  | nil => rfl
  | cons a as ih => simp [evalList, ih]

@[simp] theorem eval_var (α : W → D) (x : W) : I.eval α (.var x) = α x := by simp [eval]

@[simp] theorem eval_app (α : W → D) (f : F) (args : List (Term F W)) :
    I.eval α (.app f args) = I.op f (args.map (I.eval α)) := by
  simp [eval, evalList_eq]

theorem eval_subst (α : X → D) (σ : W → Term F X) :
    ∀ t : Term F W, I.eval α (t.subst σ) = I.eval (fun x => I.eval α (σ x)) t := by
  intro t
  induction t using Term.induction' with
  | var x => simp
  | app f args ih =>
      simp only [subst_app, eval_app, List.map_map]
      congr 1
      exact List.map_congr_left fun a member => ih a member

/-- A rule is valid in the model when its sides have equal values under every valuation. -/
def Valid (ρ : Rule F V) : Prop := ∀ α : V → D, I.eval α ρ.lhs = I.eval α ρ.rhs

/-- **A step of valid rules keeps the value.** -/
theorem step_sound {R : List (Rule F V)} (valid : ∀ ρ ∈ R, I.Valid ρ) {s t : Term F W}
    (step : Step R s t) (α : W → D) : I.eval α s = I.eval α t := by
  induction step with
  | root mem σ => rw [eval_subst, eval_subst]; exact valid _ mem _
  | arg f args i h _ ih =>
      simp only [eval_app, List.map_set]
      rw [← ih, ← List.getElem_map (I.eval α) (h := by simpa using h), List.set_getElem_self]

/-- **Every conversion of valid rules is an equality of values.** -/
theorem conv_sound {R : List (Rule F V)} (valid : ∀ ρ ∈ R, I.Valid ρ) {s t : Term F W}
    (converted : Relation.EqvGen (Step R) s t) (α : W → D) : I.eval α s = I.eval α t := by
  induction converted with
  | rel _ _ step => exact I.step_sound valid step α
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

end Interpretation

end Mettapedia.TypeTheory.PromotionAdmission
