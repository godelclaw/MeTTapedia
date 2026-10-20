import Mettapedia.TypeTheory.ContextualCBPVScopedNeedComplete

/-!
# Strategy-annotated binders elaborated into scoped need code

An annotated program binds every variable in one scope, and each binder
names its strategy: `value` (evaluated once, before the body), `need` (a memo
cell, evaluated at its first demand) or `name` (evaluated again at every
demand).  As in call-by-push-value, only value variables occur inside native
terms; a need or name variable is read by `use`, and its answer is bound by a
value binder before a term mentions it.

Scoped need code keeps native values and suspension references in separate
scopes.  The elaboration (`elaborate`) sends a value binder to `sequence` (a native
variable), a need binder to `letNeed` (a reference) and a name binder to its
producer, inlined at every use and weakened under every later binder.  Its
result is intrinsically scoped, so the elaboration is scope-correct by
construction: where a source variable lives (`Strategy.locate`) is computed
from the scope, no index can fall outside it, and every native value,
reference and producer belongs to exactly one source variable
(`Strategy.locate_bijective`).

**Correctness.** The reading of the elaborated code is the strategy semantics
of the annotated program (`elaborate_reading`): a value variable answers its value,
a need variable demands its cell, and a name variable runs its producer
again.  The strategy semantics (`denote`) reads the annotated program in its
own scope, with one environment entry per binder; the proof rests on the
reading of renamed code (`reading_rename`, `reading_renameHandles`).

**Examples**, with the natural semantics through `closed_agreement`: a choice
demanded twice gives two pairs under need and under value, and four under
name; a choice never demanded gives one answer under need and under name, and
two under value.  The need elaboration of the first is the shared pair of
`ContextualCBPVScopedNeedComplete`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV.ScopedNeed

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualDependentSequencing
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open ScopedNeedComputation (Code)
open ScopedNeedNaturalSemantics (Eval pairOutcome)

/-! ## Strategies and scopes -/

/-- How a binder evaluates what it binds. -/
inductive Strategy where
  /-- Once, before the body. -/
  | value
  /-- Once, at the first demand: a memo cell. -/
  | need
  /-- At every demand. -/
  | name
  deriving DecidableEq, Repr

namespace Strategy

/-- The native values a scope binds. -/
def values : List Strategy → Nat
  | [] => 0
  | .value :: rest => values rest + 1
  | .need :: rest => values rest
  | .name :: rest => values rest

/-- The suspension references a scope binds. -/
def needs : List Strategy → Nat
  | [] => 0
  | .value :: rest => needs rest
  | .need :: rest => needs rest + 1
  | .name :: rest => needs rest

/-- The producers a scope binds by name. -/
def names : List Strategy → Nat
  | [] => 0
  | .value :: rest => names rest
  | .need :: rest => names rest
  | .name :: rest => names rest + 1

/-- Where a variable of a scope lives in scoped code. -/
inductive Place (scope : List Strategy) where
  | native (index : Fin (values scope))
  | reference (index : Fin (needs scope))
  | producer (index : Fin (names scope))

/-- The place of the variable a binder introduces. -/
def Place.here : (strategy : Strategy) → {rest : List Strategy} → Place (strategy :: rest)
  | .value, rest => .native (0 : Fin (values rest + 1))
  | .need, rest => .reference (0 : Fin (needs rest + 1))
  | .name, rest => .producer (0 : Fin (names rest + 1))

/-- A place below one more binder. -/
def Place.weaken {rest : List Strategy} : (strategy : Strategy) → Place rest → Place (strategy :: rest)
  | .value, .native index => .native index.succ
  | .value, .reference index => .reference index
  | .value, .producer index => .producer index
  | .need, .native index => .native index
  | .need, .reference index => .reference index.succ
  | .need, .producer index => .producer index
  | .name, .native index => .native index
  | .name, .reference index => .reference index
  | .name, .producer index => .producer index.succ

/-- Where a variable lives, counted among the binders of its strategy. -/
def locate : (scope : List Strategy) → Fin scope.length → Place scope
  | [], index => index.elim0
  | strategy :: rest, index => Fin.cases (Place.here strategy) (fun j => (locate rest j).weaken strategy) index

theorem Place.here_ne_weaken {rest : List Strategy} (strategy : Strategy) (place : Place rest) :
    Place.here strategy ≠ place.weaken strategy := by
  intro equal
  cases strategy <;> cases place <;> simp only [Place.here, Place.weaken] at equal <;> cases equal

theorem Place.weaken_injective {rest : List Strategy} (strategy : Strategy) :
    Function.Injective (Place.weaken (rest := rest) strategy) := by
  intro first second equal
  cases strategy <;> cases first <;> cases second <;> simp only [Place.weaken] at equal <;>
    first
    | (cases equal <;> rfl)
    | (injection equal with same; exact congrArg _ (Fin.succ_injective _ same))

theorem Place.here_or_weaken {rest : List Strategy} (strategy : Strategy) (place : Place (strategy :: rest)) :
    place = Place.here strategy ∨ ∃ below : Place rest, place = below.weaken strategy := by
  cases strategy with
  | value =>
      cases place with
      | native index =>
          refine Fin.cases (Or.inl rfl) (fun j => Or.inr ⟨.native j, rfl⟩) index
      | reference index => exact Or.inr ⟨.reference index, rfl⟩
      | producer index => exact Or.inr ⟨.producer index, rfl⟩
  | need =>
      cases place with
      | native index => exact Or.inr ⟨.native index, rfl⟩
      | reference index =>
          refine Fin.cases (Or.inl rfl) (fun j => Or.inr ⟨.reference j, rfl⟩) index
      | producer index => exact Or.inr ⟨.producer index, rfl⟩
  | name =>
      cases place with
      | native index => exact Or.inr ⟨.native index, rfl⟩
      | reference index => exact Or.inr ⟨.reference index, rfl⟩
      | producer index =>
          refine Fin.cases (Or.inl rfl) (fun j => Or.inr ⟨.producer j, rfl⟩) index

/-- **Every place belongs to exactly one variable**: the elaboration neither
merges two variables nor leaves a native value, a reference or a producer
without its binder. -/
theorem locate_bijective : (scope : List Strategy) → Function.Bijective (locate scope)
  | [] => ⟨fun index => index.elim0, fun place => by cases place <;> rename_i index <;> exact index.elim0⟩
  | strategy :: rest => by
      obtain ⟨injective, surjective⟩ := locate_bijective rest
      constructor
      · intro first second equal
        induction first using Fin.cases with
        | zero =>
            induction second using Fin.cases with
            | zero => rfl
            | succ j => exact absurd equal (Place.here_ne_weaken strategy _)
        | succ i =>
            induction second using Fin.cases with
            | zero => exact absurd equal.symm (Place.here_ne_weaken strategy _)
            | succ j =>
                simp only [locate, Fin.cases_succ] at equal
                rw [injective (Place.weaken_injective strategy equal)]
      · intro place
        rcases Place.here_or_weaken strategy place with here | ⟨below, rfl⟩
        · exact ⟨0, by rw [here]; rfl⟩
        · obtain ⟨j, located⟩ := surjective below
          exact ⟨j.succ, by simp only [locate, Fin.cases_succ, located]⟩

end Strategy

open Strategy (values needs names Place locate)

/-! ## Annotated programs -/

/-- Programs over one scope whose binders carry strategies. -/
inductive Annotated (Head Operation Effect : Type) : List Strategy → Type where
  /-- Return a native term over the value variables. -/
  | ret {scope : List Strategy} (term : Tm Head (values scope)) : Annotated Head Operation Effect scope
  | call {scope : List Strategy} (operation : Operation) (argument : Tm Head (values scope)) :
      Annotated Head Operation Effect scope
  | emit {scope : List Strategy} (effect : Effect) (next : Annotated Head Operation Effect scope) :
      Annotated Head Operation Effect scope
  | choose {scope : List Strategy} (left right : Annotated Head Operation Effect scope) :
      Annotated Head Operation Effect scope
  /-- Read a variable as its binder's strategy says. -/
  | use {scope : List Strategy} (position : Fin scope.length) : Annotated Head Operation Effect scope
  /-- Bind the answer of `bound` by a strategy. -/
  | bind {scope : List Strategy} (strategy : Strategy) (bound : Annotated Head Operation Effect scope)
      (body : Annotated Head Operation Effect (strategy :: scope)) : Annotated Head Operation Effect scope
  /-- Pair a native answer with the answer of the body, which binds it by value. -/
  | pair {scope : List Strategy} (first : Annotated Head Operation Effect scope)
      (body : Annotated Head Operation Effect (.value :: scope)) : Annotated Head Operation Effect scope

variable {Head Operation Effect StableFault NativeFault : Type} {m : Nat}

/-- The producers of the name variables, as code of the current scope. -/
abbrev Producers (Head Operation Effect : Type) (scope : List Strategy) :=
  Fin (names scope) → Code Head Operation Effect (values scope) (needs scope)

/-- **The elaboration.**  Its type is the scope-correctness statement. -/
def elaborate : {scope : List Strategy} → Annotated Head Operation Effect scope →
    Producers Head Operation Effect scope → Code Head Operation Effect (values scope) (needs scope)
  | _, .ret term, _ => .returnValue term
  | _, .call operation argument, _ => .call operation argument
  | _, .emit effect next, producers => .emit effect (elaborate next producers)
  | _, .choose left right, producers => .choose (elaborate left producers) (elaborate right producers)
  | scope, .use position, producers =>
      match locate scope position with
      | .native index => .returnValue (.var index)
      | .reference index => .force index
      | .producer index => producers index
  | _, .bind .value bound body, producers =>
      .sequence (elaborate bound producers) (elaborate body fun j => (producers j).rename wk)
  | _, .bind .need bound body, producers =>
      .letNeed (elaborate bound producers) (elaborate body fun j => (producers j).renameHandles Fin.succ)
  | scope, .bind .name bound body, producers =>
      let inlined : Fin (names scope + 1) → Code Head Operation Effect (values scope) (needs scope) :=
        Fin.cases (elaborate bound producers) producers
      elaborate (scope := .name :: scope) body inlined
  | _, .pair first body, producers =>
      .sequenceSigma (elaborate first producers) (elaborate body fun j => (producers j).rename wk)

/-! ## Reading renamed code -/

variable (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault)

theorem reading_rename {n n' k : Nat} (ρ : Presentation.Ren n n') (code : Code Head Operation Effect n k)
    (values : Sub Head n' m) (refs : Fin k → Ref Head Effect StableFault NativeFault m) :
    reading primitive (code.rename ρ) values refs = reading primitive code (fun i => values (ρ i)) refs := by
  induction code generalizing n' with
  | returnValue term => simp only [Code.rename, reading, subst_rename]
  | call operation argument => simp only [Code.rename, reading, subst_rename]
  | emit effect next ih => simp only [Code.rename, reading, ih]
  | choose left right ihLeft ihRight => simp only [Code.rename, reading, ihLeft, ihRight]
  | sequence first body ihFirst ihBody =>
      have lifted : ∀ value : Tm Head m,
          (fun i => (Fin.cases value values : Sub Head (n' + 1) m) (liftRen ρ i)) =
            Fin.cases value fun i => values (ρ i) := by
        intro value
        funext i
        refine Fin.cases rfl (fun j => rfl) i
      simp only [Code.rename, reading, ihFirst, ihBody, lifted]
  | sequenceSigma first body ihFirst ihBody =>
      have lifted : ∀ value : Tm Head m,
          (fun i => (Fin.cases value values : Sub Head (n' + 1) m) (liftRen ρ i)) =
            Fin.cases value fun i => values (ρ i) := by
        intro value
        funext i
        refine Fin.cases rfl (fun j => rfl) i
      simp only [Code.rename, reading, ihFirst, ihBody, lifted]
  | letNeed suspended body ihSuspended ihBody => simp only [Code.rename, reading, ihSuspended, ihBody]
  | force reference => rfl

theorem reading_renameHandles {n k k' : Nat} (θ : Fin k → Fin k') (code : Code Head Operation Effect n k)
    (values : Sub Head n m) (refs : Fin k' → Ref Head Effect StableFault NativeFault m) :
    reading primitive (code.renameHandles θ) values refs =
      reading primitive code values (fun j => refs (θ j)) := by
  induction code generalizing k' with
  | returnValue term => rfl
  | call operation argument => rfl
  | emit effect next ih => simp only [Code.renameHandles, reading, ih]
  | choose left right ihLeft ihRight => simp only [Code.renameHandles, reading, ihLeft, ihRight]
  | sequence first body ihFirst ihBody => simp only [Code.renameHandles, reading, ihFirst, ihBody]
  | sequenceSigma first body ihFirst ihBody => simp only [Code.renameHandles, reading, ihFirst, ihBody]
  | letNeed suspended body ihSuspended ihBody =>
      have lifted : ∀ ref : Ref Head Effect StableFault NativeFault m,
          (fun j => (Fin.cases ref refs : Fin (k' + 1) → Ref Head Effect StableFault NativeFault m)
            (liftRen θ j)) = Fin.cases ref fun j => refs (θ j) := by
        intro ref
        funext j
        refine Fin.cases rfl (fun j' => rfl) j
      simp only [Code.renameHandles, reading, ihSuspended, ihBody, lifted]
  | force reference => rfl

/-! ## The strategy semantics -/

/-- The run-time meaning of every variable of a scope: the value of a value
variable, the reference of a need variable, and the program and producer of
a name variable. -/
structure Env (Head Effect StableFault NativeFault : Type) (m : Nat) (scope : List Strategy) where
  native : Sub Head (values scope) m
  references : Fin (needs scope) → Ref Head Effect StableFault NativeFault m
  producers : Fin (names scope) →
    Run Head Effect StableFault NativeFault m × Run Head Effect StableFault NativeFault m

/-- Bind a value variable. -/
def Env.bindValue {scope : List Strategy} (env : Env Head Effect StableFault NativeFault m scope)
    (value : Tm Head m) : Env Head Effect StableFault NativeFault m (.value :: scope) :=
  ⟨Fin.cases value env.native, env.references, env.producers⟩

/-- Bind a need variable to its reference. -/
def Env.bindNeed {scope : List Strategy} (env : Env Head Effect StableFault NativeFault m scope)
    (ref : Ref Head Effect StableFault NativeFault m) : Env Head Effect StableFault NativeFault m (.need :: scope) :=
  ⟨env.native, Fin.cases ref env.references, env.producers⟩

/-- Bind a name variable to its program and producer. -/
def Env.bindName {scope : List Strategy} (env : Env Head Effect StableFault NativeFault m scope)
    (producer : Run Head Effect StableFault NativeFault m × Run Head Effect StableFault NativeFault m) :
    Env Head Effect StableFault NativeFault m (.name :: scope) :=
  ⟨env.native, env.references, Fin.cases producer env.producers⟩

/-- The meaning of a variable: a value answers itself, a need variable
demands its cell, a name variable runs its producer again. -/
def Env.meaning {scope : List Strategy} (env : Env Head Effect StableFault NativeFault m scope) :
    Place scope → Run Head Effect StableFault NativeFault m × Run Head Effect StableFault NativeFault m
  | .native index => (.pure (.value (env.native index)), .pure (.value (env.native index)))
  | .reference index =>
      (demand (env.references index).1 (env.references index).2,
       demand (env.references index).1 (env.references index).2)
  | .producer index => env.producers index

/-- **The strategy semantics**: the program of an annotated program, and the
program its cell runs when it is a bound producer (a choice selects an
alternative). -/
def denote : {scope : List Strategy} → Annotated Head Operation Effect scope →
    Env Head Effect StableFault NativeFault m scope →
      Run Head Effect StableFault NativeFault m × Run Head Effect StableFault NativeFault m
  | _, .ret term, env => (.pure (.value (subst env.native term)), .pure (.value (subst env.native term)))
  | _, .call operation argument, env =>
      (.pure (ScopedNeedMachine.liftOutcome (primitive operation (subst env.native argument))),
       .pure (ScopedNeedMachine.liftOutcome (primitive operation (subst env.native argument))))
  | _, .emit effect next, env => (.intent effect (denote next env).1, .intent effect (denote next env).1)
  | _, .choose left right, env =>
      (alloc fun cell => demand cell (.choose (denote left env).1 (denote right env).1),
       .choose (denote left env).1 (denote right env).1)
  | scope, .use position, env => env.meaning (locate scope position)
  | _, .bind .value bound body, env =>
      (alloc fun cell => (demand cell (denote bound env).2).bind
          (onValue fun value => (denote body (env.bindValue value)).1),
       alloc fun cell => (demand cell (denote bound env).2).bind
          (onValue fun value => (denote body (env.bindValue value)).1))
  | _, .bind .need bound body, env =>
      (alloc fun cell => (denote body (env.bindNeed (cell, (denote bound env).2))).1,
       alloc fun cell => (denote body (env.bindNeed (cell, (denote bound env).2))).1)
  | _, .bind .name bound body, env => denote body (env.bindName (denote bound env))
  | _, .pair first body, env =>
      (alloc fun cell => (demand cell (denote first env).2).bind
          (onValue fun value => Program.map (pairOutcome value) (denote body (env.bindValue value)).1),
       alloc fun cell => (demand cell (denote first env).2).bind
          (onValue fun value => Program.map (pairOutcome value) (denote body (env.bindValue value)).1))

/-! ## Correctness -/

/-- **The elaboration is correct.**  Under an environment whose name
variables mean the readings of their producers, the reading of the elaborated
code is the strategy semantics of the annotated program. -/
theorem elaborate_reading {scope : List Strategy} (program : Annotated Head Operation Effect scope)
    (env : Env Head Effect StableFault NativeFault m scope) (producers : Producers Head Operation Effect scope)
    (agree : ∀ j, env.producers j = reading primitive (producers j) env.native env.references) :
    reading primitive (elaborate program producers) env.native env.references = denote primitive program env := by
  induction program with
  | ret term => rfl
  | call operation argument => rfl
  | emit effect next ih => simp only [elaborate, reading, denote, ih env producers agree]
  | choose left right ihLeft ihRight =>
      simp only [elaborate, reading, denote, ihLeft env producers agree, ihRight env producers agree]
  | use position =>
      simp only [elaborate, denote]
      cases locate _ position with
      | native index => rfl
      | reference index => rfl
      | producer index => exact (agree index).symm
  | @bind inner strategy bound body ihBound ihBody =>
      cases strategy with
      | value =>
          have continued : ∀ value : Tm Head m,
              reading primitive (n := values inner + 1) (k := needs inner)
                (elaborate body fun j => (producers j).rename wk) (Fin.cases value env.native) env.references =
                denote primitive body (env.bindValue value) :=
            fun value => ihBody (env.bindValue value) _ fun j => (agree j).trans
              (reading_rename primitive wk (producers j) (env.bindValue value).native
                (env.bindValue value).references).symm
          simp only [elaborate, reading, denote, ihBound env producers agree, continued]
      | need =>
          have continued : ∀ ref : Ref Head Effect StableFault NativeFault m,
              reading primitive (n := values inner) (k := needs inner + 1)
                (elaborate body fun j => (producers j).renameHandles Fin.succ) env.native
                (Fin.cases ref env.references) = denote primitive body (env.bindNeed ref) :=
            fun ref => ihBody (env.bindNeed ref) _ fun j => (agree j).trans
              (reading_renameHandles primitive Fin.succ (producers j) (env.bindNeed ref).native
                (env.bindNeed ref).references).symm
          simp only [elaborate, reading, denote, ihBound env producers agree, continued]
      | name =>
          simp only [elaborate, denote]
          refine ihBody (env.bindName (denote primitive bound env)) _ fun j => ?_
          refine Fin.cases ?_ (fun j' => ?_) j
          · exact (ihBound env producers agree).symm
          · exact agree j'
  | @pair inner first body ihFirst ihBody =>
      have continued : ∀ value : Tm Head m,
          reading primitive (n := values inner + 1) (k := needs inner)
            (elaborate body fun j => (producers j).rename wk) (Fin.cases value env.native) env.references =
            denote primitive body (env.bindValue value) :=
        fun value => ihBody (env.bindValue value) _ fun j => (agree j).trans
          (reading_rename primitive wk (producers j) (env.bindValue value).native
            (env.bindValue value).references).symm
      simp only [elaborate, reading, denote, ihFirst env producers agree, continued]

/-- For a closed program, the answers of the elaborated code are the answers
of the strategy semantics. -/
theorem elaborate_answers (program : Annotated Head Operation Effect []) (values : Sub Head 0 m) :
    answers (Effect := Effect) primitive (elaborate program Fin.elim0) values =
      (runWorlds (denote primitive program ⟨values, Fin.elim0, Fin.elim0⟩).1 []).map WorldResult.answer := by
  have reads := elaborate_reading primitive program
    (⟨values, Fin.elim0, Fin.elim0⟩ : Env Head Effect StableFault NativeFault m []) Fin.elim0 (fun j => j.elim0)
  unfold answers
  exact congrArg (fun run => (runWorlds run.1 []).map WorldResult.answer) reads

#print axioms Strategy.locate_bijective
#print axioms elaborate_reading

/-! ## Examples -/

namespace Examples

open ScopedNeedNaturalSemantics.Examples (ExampleOperation emptyWorld)

/-- In the scope `x₀ : value, x₁ : need, x₂ : value, x₃ : name` (innermost
first), the value variables are the native values 0 and 1, the need
variable is reference 0 and the name variable is producer 0. -/
theorem locate_example :
    (locate [.value, .need, .value, .name] 0, locate [.value, .need, .value, .name] 1,
      locate [.value, .need, .value, .name] 2, locate [.value, .need, .value, .name] 3) =
    (.native (0 : Fin 2), .reference (0 : Fin 1), .native (1 : Fin 2), .producer (0 : Fin 1)) := rfl

/-- A choice between two heads. -/
def coin {scope : List Strategy} : Annotated Nat ExampleOperation Nat scope :=
  .choose (.ret (.head 1)) (.ret (.head 2))

/-- Bind the choice by a strategy, read it twice and pair the two answers. -/
def twice (strategy : Strategy) : Annotated Nat ExampleOperation Nat [] :=
  .bind strategy coin (.pair (.use 0) (.use 1))

/-- Bind the choice by a strategy and never read it. -/
def unused (strategy : Strategy) : Annotated Nat ExampleOperation Nat [] :=
  .bind strategy coin (.ret (.head 3))

/-- The need elaboration of `twice` is the shared pair. -/
theorem twice_need_elaborates : elaborate (twice .need) Fin.elim0 = sharedPair := rfl

/-- **Need**: the two reads share one choice. -/
theorem twice_need :
    answers (Effect := Nat) examplePrimitive (elaborate (twice .need) Fin.elim0) ids =
      [.value (.pair (.head 1) (.head 1)), .value (.pair (.head 2) (.head 2))] := by
  decide

/-- **Value**: the choice is made once, before the body. -/
theorem twice_value :
    answers (Effect := Nat) examplePrimitive (elaborate (twice .value) Fin.elim0) ids =
      [.value (.pair (.head 1) (.head 1)), .value (.pair (.head 2) (.head 2))] := by
  decide

/-- **Name**: every read chooses again. -/
theorem twice_name :
    answers (Effect := Nat) examplePrimitive (elaborate (twice .name) Fin.elim0) ids =
      [.value (.pair (.head 1) (.head 1)), .value (.pair (.head 1) (.head 2)),
       .value (.pair (.head 2) (.head 1)), .value (.pair (.head 2) (.head 2))] := by
  decide

/-- The correctness of the elaboration, at the name elaboration of `twice`:
its reading is the strategy semantics. -/
theorem twice_name_denote :
    reading (Effect := Nat) examplePrimitive (elaborate (twice .name) Fin.elim0) ids Fin.elim0 =
      denote examplePrimitive (twice .name) ⟨ids, Fin.elim0, Fin.elim0⟩ :=
  elaborate_reading examplePrimitive (twice .name) ⟨ids, Fin.elim0, Fin.elim0⟩ Fin.elim0 (fun j => j.elim0)

/-- An unread need or name binding never runs its producer. -/
theorem unused_need :
    answers (Effect := Nat) examplePrimitive (elaborate (unused .need) Fin.elim0) ids = [.value (.head 3)] := by
  decide

theorem unused_name :
    answers (Effect := Nat) examplePrimitive (elaborate (unused .name) Fin.elim0) ids = [.value (.head 3)] := by
  decide

/-- An unread value binding still runs its producer, in each alternative. -/
theorem unused_value :
    answers (Effect := Nat) examplePrimitive (elaborate (unused .value) Fin.elim0) ids =
      [.value (.head 3), .value (.head 3)] := by
  decide

/-- **Name differs from need**, in the natural semantics: the mixed pair is
derived from the name elaboration and not from the need elaboration. -/
theorem twice_name_mixed :
    ∃ final, Nonempty (Eval examplePrimitive ⟨0, 0, elaborate (twice .name) Fin.elim0, ids, Fin.elim0⟩
      emptyWorld (.value (.pair (.head 1) (.head 2))) final) :=
  (closed_agreement (Effect := Nat) examplePrimitive (elaborate (twice .name) Fin.elim0) ids emptyWorld
    (Fresh.empty _ emptyWorld_lookup) _).mp (by rw [twice_name]; simp)

theorem twice_need_not_mixed :
    ¬ ∃ final, Nonempty (Eval examplePrimitive ⟨0, 0, elaborate (twice .need) Fin.elim0, ids, Fin.elim0⟩
      emptyWorld (.value (.pair (.head 1) (.head 2))) final) := by
  intro derived
  have member := (closed_agreement (Effect := Nat) examplePrimitive (elaborate (twice .need) Fin.elim0) ids
    emptyWorld (Fresh.empty _ emptyWorld_lookup) _).mpr derived
  rw [twice_need] at member
  simp at member

end Examples

end Mettapedia.TypeTheory.ContextualCBPV.ScopedNeed
