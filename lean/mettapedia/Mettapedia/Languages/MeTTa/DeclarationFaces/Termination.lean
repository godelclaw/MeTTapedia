import Mettapedia.Languages.MeTTa.DeclarationFaces.Syntax

/-!
# Structural descent: every evaluation order terminates

A **descent certificate** gives every symbol a rank and a position. An equation of `f` descends
when every call `(g us)` its right side makes is a call of a symbol that heads no equation, or of a
symbol of smaller rank, or of `f` itself whose argument at `f`'s position is a proper part of the
pattern at that position. Ranks forbid mutual recursion; the position is the argument on which
`f` recurses structurally, and it need not be the first.

**Strong normalization** (`Descends.stronglyNormalizing`): under a headed program whose equations
descend and whose right sides use only their left side's variables, every term, closed or open,
sorted or not, starts no infinite sequence of steps. Steps may be taken at any position in any
order, so every evaluation strategy terminates.

The proof follows the classical argument for recursion schemes: a call of a defined symbol on
strongly normalizing arguments is strongly normalizing, by induction on the rank, then on the
argument at the recursion position under steps and proper parts together (`acc_below`), then on
the arguments under steps (`acc_listStep`).

Positive example: the two equations of addition descend at position 0
(`Examples.add_descends`). Negative example: the equation `(loop $x) = (loop $x)` makes a call at
the same argument and does not descend (`Examples.loop_not_descends`); it has an infinite sequence
of steps (`Examples.loop_not_terminating`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces

open Relation
open Mettapedia.Logic.Relation (IsNormal accessible_transitiveClosure)
open Tm

universe u

variable {S : Type u}

/-- Strong normalization at a term: every sequence of steps from it is finite. -/
abbrev SN (P : Program S) (t : Tm S) : Prop := Acc (fun target source => Step P source target) t

/-- A term is a proper part of another. -/
abbrev ProperSub (outer inner : Tm S) : Prop := TransGen Sub outer inner

/-- **A descent certificate**: a rank and a recursion position for every symbol. -/
structure Certificate (S : Type u) where
  rank : S → ℕ
  position : S → ℕ

/-- A call `(g us)` made by an equation of `f` with argument patterns `ps` descends. -/
def CallDescends (P : Program S) (c : Certificate S) (f : S) (ps : List (Tm S)) (g : S)
    (us : List (Tm S)) : Prop :=
  ¬ P.Defines g ∨ c.rank g < c.rank f ∨
    (g = f ∧ ∃ (hu : c.position f < us.length) (hp : c.position f < ps.length),
      ProperSub ps[c.position f] us[c.position f])

/-- Every application inside a term satisfies a condition. -/
inductive EveryCall (Q : S → List (Tm S) → Prop) : Tm S → Prop where
  | var (name : String) : EveryCall Q (.var name)
  | app {g : S} {us : List (Tm S)} : Q g us → (∀ u ∈ us, EveryCall Q u) → EveryCall Q (.app g us)

/-- **A descending program**: every equation is a call of a symbol on argument patterns, and every
call of its right side descends. -/
def Program.Descends (P : Program S) (c : Certificate S) : Prop :=
  ∀ e ∈ P, ∃ f ps, e.lhs = .app f ps ∧ EveryCall (CallDescends P c f ps) e.rhs

/-! ## Parts and steps -/

/-- A variable of a pattern is instantiated by a part of the instance. -/
theorem subStar_subst_var (σ : String → Tm S) :
    ∀ (p : Tm S) {x : String}, x ∈ p.vars → ReflTransGen Sub (p.subst σ) (σ x) := by
  intro p
  induction p using Tm.induction' with
  | var name => intro x member; simp at member; subst member; exact .refl
  | app head args ih =>
      intro x member
      simp only [vars_app, List.mem_flatMap] at member
      obtain ⟨a, aMember, xMember⟩ := member
      rw [subst_app]
      exact ReflTransGen.head (Sub.arg head (List.mem_map_of_mem aMember)) (ih a aMember xMember)

/-- Instantiation keeps proper parts proper. -/
theorem properSub_subst (σ : String → Tm S) {outer inner : Tm S}
    (part : ProperSub outer inner) : ProperSub (outer.subst σ) (inner.subst σ) := by
  induction part with
  | single sub =>
      cases sub with
      | arg head member => rw [subst_app]; exact .single (Sub.arg head (List.mem_map_of_mem member))
  | tail _ sub ih =>
      cases sub with
      | arg head member =>
          rw [subst_app] at ih
          exact ih.tail (Sub.arg head (List.mem_map_of_mem member))

/-- A variable takes no step in a headed program. -/
theorem var_normal {P : Program S} (headed : P.Headed) (name : String) :
    IsNormal (Step P) (.var name) := by
  intro target step
  cases step with
  | root root =>
      obtain ⟨f, args, same, _⟩ := root.defines_head headed
      cases same

/-- A step inside a part is a step of the whole, with the reduct as the corresponding part. -/
theorem Step.lift_subStar {P : Program S} {whole part part' : Tm S}
    (inside : ReflTransGen Sub whole part) (step : Step P part part') :
    ∃ whole', Step P whole whole' ∧ ReflTransGen Sub whole' part' := by
  induction inside generalizing part' with
  | refl => exact ⟨part', step, .refl⟩
  | @tail middle _ _ sub ih =>
      cases sub with
      | @arg head args _ member =>
          obtain ⟨i, lt, same⟩ := List.getElem_of_mem member
          subst same
          obtain ⟨whole', wholeStep, inside'⟩ := ih (Step.arg head args i lt step)
          refine ⟨whole', wholeStep, inside'.tail (Sub.arg head ?_)⟩
          exact List.mem_iff_getElem.mpr ⟨i, by simpa using lt, by simp⟩

/-- A part of a strongly normalizing term is strongly normalizing. -/
theorem SN.of_subStar {P : Program S} {whole part : Tm S} (sn : SN P whole)
    (inside : ReflTransGen Sub whole part) : SN P part := by
  induction sn generalizing part with
  | intro whole _ ih =>
      constructor
      intro part' step
      obtain ⟨whole', wholeStep, inside'⟩ := step.lift_subStar inside
      exact ih whole' wholeStep inside'

/-- Steps and immediate parts, as one relation read from a term to its successors. -/
abbrev Below (P : Program S) : Tm S → Tm S → Prop :=
  fun target source => Step P source target ∨ Sub source target

/-- **Steps and parts together terminate on strongly normalizing terms.** -/
theorem acc_below {P : Program S} {t : Tm S} (sn : SN P t) : Acc (Below P) t := by
  suffices ∀ part, ReflTransGen Sub t part → Acc (Below P) part from this t .refl
  induction sn with
  | intro whole _ ih =>
      intro part inside
      induction part using Tm.induction' with
      | var name =>
          constructor
          intro target below
          rcases below with step | sub
          · obtain ⟨whole', wholeStep, inside'⟩ := step.lift_subStar inside
            exact ih whole' wholeStep target inside'
          · cases sub
      | app head args ihArgs =>
          constructor
          intro target below
          rcases below with step | sub
          · obtain ⟨whole', wholeStep, inside'⟩ := step.lift_subStar inside
            exact ih whole' wholeStep target inside'
          · cases sub with
            | arg _ member => exact ihArgs target member (inside.tail (Sub.arg head member))

/-! ## Steps inside lists of arguments -/

/-- One step at one element of a list. -/
def ListStep (P : Program S) (as bs : List (Tm S)) : Prop :=
  ∃ i, ∃ lt : i < as.length, ∃ b, Step P as[i] b ∧ bs = as.set i b

/-- **Lists of strongly normalizing terms take no infinite sequence of element steps.** -/
theorem acc_listStep {P : Program S} :
    ∀ as : List (Tm S), (∀ a ∈ as, SN P a) → Acc (fun bs as => ListStep P as bs) as := by
  intro as
  induction as with
  | nil =>
      intro _
      constructor
      rintro bs ⟨i, lt, _⟩
      simp at lt
  | cons a rest ih =>
      intro sn
      have headSN : SN P a := sn a List.mem_cons_self
      have restAcc := ih fun b member => sn b (List.mem_cons_of_mem a member)
      clear ih sn
      induction headSN generalizing rest with
      | intro a _ iha =>
          induction restAcc with
          | intro rest restSteps ihRest =>
              constructor
              rintro bs ⟨i, lt, b, step, rfl⟩
              cases i with
              | zero => exact iha b step rest (Acc.intro rest restSteps)
              | succ j =>
                  have lt' : j < rest.length := by simpa using lt
                  simp only [List.set_cons_succ]
                  exact ihRest (rest.set j b) ⟨j, lt', b, by simpa using step, rfl⟩

/-- A list step keeps every element strongly normalizing. -/
theorem ListStep.sn {P : Program S} {as bs : List (Tm S)} (step : ListStep P as bs)
    (sn : ∀ a ∈ as, SN P a) : ∀ b ∈ bs, SN P b := by
  obtain ⟨i, lt, b, stepAt, rfl⟩ := step
  intro c member
  rcases List.mem_or_eq_of_mem_set member with old | new
  · exact sn c old
  · subst new; exact (sn _ (List.getElem_mem lt)).inv stepAt

/-! ## Calls of constructors and of defined symbols -/

/-- **A symbol that heads no equation, applied to strongly normalizing arguments, is strongly
normalizing.** -/
theorem sn_constructor {P : Program S} (headed : P.Headed) {c : S} (undefined : ¬ P.Defines c) :
    ∀ args : List (Tm S), (∀ a ∈ args, SN P a) → SN P (.app c args) := by
  intro args sn
  have acc := acc_listStep args sn
  induction acc with
  | intro args _ ih =>
      constructor
      intro target step
      obtain ⟨i, lt, a, stepAt, rfl⟩ := step.app_of_not_defines headed undefined
      have listStep : ListStep P args (args.set i a) := ⟨i, lt, a, stepAt, rfl⟩
      exact ih _ listStep (listStep.sn sn)

/-- A proper part, read as a chain of steps and parts from the part to the whole. -/
theorem below_of_properSub {P : Program S} {outer inner : Tm S} (part : ProperSub outer inner) :
    TransGen (Below P) inner outer := by
  induction part with
  | single sub => exact .single (Or.inr sub)
  | tail _ sub ih => exact TransGen.head (Or.inr sub) ih

/-- The argument at the recursion position of a symbol, or a variable when there is none. -/
def recursionKey (c : Certificate S) (f : S) (args : List (Tm S)) : Tm S :=
  args[c.position f]?.getD (.var "")

theorem recursionKey_set_ne (c : Certificate S) (f : S) (args : List (Tm S)) {i : Nat}
    (ne : i ≠ c.position f) (b : Tm S) :
    recursionKey c f (args.set i b) = recursionKey c f args := by
  simp [recursionKey, List.getElem?_set_ne ne]

theorem recursionKey_set_eq (c : Certificate S) (f : S) (args : List (Tm S)) {i : Nat}
    (same : i = c.position f) (lt : i < args.length) (b : Tm S) :
    recursionKey c f (args.set i b) = b := by
  subst same
  simp [recursionKey, lt]

theorem recursionKey_of_lt (c : Certificate S) (f : S) (args : List (Tm S))
    (lt : c.position f < args.length) : recursionKey c f args = args[c.position f] := by
  simp [recursionKey, lt]

/-- An instance of a term whose calls satisfy a condition is strongly normalizing when the
instantiating terms of its variables are, and every call satisfying the condition, on strongly
normalizing arguments, is. -/
theorem sn_instance {P : Program S} {Q : S → List (Tm S) → Prop} (σ : String → Tm S)
    (calls : ∀ g us, Q g us → (∀ a ∈ us.map (subst σ), SN P a) →
      SN P (.app g (us.map (subst σ)))) :
    ∀ {u : Tm S}, EveryCall Q u → (∀ x ∈ u.vars, SN P (σ x)) → SN P (u.subst σ) := by
  intro u every
  induction every with
  | var name => intro varsSN; simpa using varsSN name (by simp)
  | @app g us holds _ ih =>
      intro varsSN
      rw [subst_app]
      apply calls g us holds
      intro a member
      obtain ⟨u, uMember, rfl⟩ := List.mem_map.mp member
      exact ih u uMember fun x hx => varsSN x (by simpa using ⟨u, uMember, hx⟩)

/-- **A call on strongly normalizing arguments is strongly normalizing**, in a headed, descending
program whose right sides use only their left side's variables. -/
theorem sn_call {P : Program S} (headed : P.Headed) (bound : P.RightBound) {c : Certificate S}
    (descends : P.Descends c) :
    ∀ (f : S) (args : List (Tm S)), (∀ a ∈ args, SN P a) → SN P (.app f args) := by
  suffices ∀ n (f : S), c.rank f = n → ∀ args : List (Tm S), (∀ a ∈ args, SN P a) →
      SN P (.app f args) from fun f => this _ f rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihRank =>
  intro f hr
  by_cases defined : P.Defines f
  swap
  · exact sn_constructor headed defined
  intro args sn
  have keySN : SN P (recursionKey c f args) := by
    unfold recursionKey
    cases h : args[c.position f]? with
    | none => exact Acc.intro _ fun target step => absurd step (var_normal headed "" target)
    | some a => exact sn a (List.mem_of_getElem? h)
  have keyAcc := accessible_transitiveClosure (acc_below keySN)
  clear keySN
  generalize hk : recursionKey c f args = k at keyAcc
  induction keyAcc generalizing args with
  | intro k _ ihKey =>
  have argsAcc := acc_listStep args sn
  induction argsAcc with
  | intro args _ ihArgs =>
  constructor
  intro target step
  cases step with
  | root root =>
      obtain ⟨e, eMember, σ, hs, rfl⟩ := root.exists_rule
      obtain ⟨f', ps, hlhs, every⟩ := descends e eMember
      rw [hlhs, subst_app] at hs
      obtain ⟨hf, hargs⟩ := Tm.app.inj hs
      subst hf
      subst hargs
      apply sn_instance σ _ every
      · intro x hx
        have hx' := bound e eMember x hx
        rw [hlhs, vars_app, List.mem_flatMap] at hx'
        obtain ⟨p, pMember, xMember⟩ := hx'
        exact SN.of_subStar (sn _ (List.mem_map_of_mem pMember)) (subStar_subst_var σ p xMember)
      · intro g us descent argsSN
        rcases descent with undefined | lower | ⟨rfl, hu, hp, part⟩
        · exact sn_constructor headed undefined _ argsSN
        · exact ihRank (c.rank g) (hr ▸ lower) g rfl _ argsSN
        · apply ihKey ((us[c.position g]).subst σ) _ (us.map (subst σ)) argsSN
          · rw [recursionKey_of_lt c g _ (by simpa using hu)]
            simp
          · rw [← hk, recursionKey_of_lt c g _ (by simpa using hp)]
            simpa using below_of_properSub (P := P) (properSub_subst σ part)
  | arg _ _ i lt stepAt =>
      rename_i b
      have listStep : ListStep P args (args.set i b) := ⟨i, lt, b, stepAt, rfl⟩
      by_cases atKey : i = c.position f
      · apply ihKey b _ (args.set i b) (listStep.sn sn) (recursionKey_set_eq c f args atKey lt b)
        rw [← hk, recursionKey_of_lt c f args (atKey ▸ lt)]
        exact .single (Or.inl (by simpa [atKey] using stepAt))
      · exact ihArgs _ listStep (listStep.sn sn)
          (by rw [recursionKey_set_ne c f args atKey]; exact hk)

/-- **Strong normalization**: in a headed, descending program whose right sides use only their
left side's variables, every term starts no infinite sequence of steps. So every evaluation
strategy terminates on every term. -/
theorem Program.Descends.stronglyNormalizing {P : Program S} {c : Certificate S}
    (descends : P.Descends c) (headed : P.Headed) (bound : P.RightBound) : ∀ t, SN P t := by
  intro t
  induction t using Tm.induction' with
  | var name => exact Acc.intro _ fun target step => absurd step (var_normal headed name target)
  | app head args ih => exact sn_call headed bound descends head args ih

end Mettapedia.Languages.MeTTa.DeclarationFaces
