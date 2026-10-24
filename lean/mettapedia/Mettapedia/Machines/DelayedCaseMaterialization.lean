import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Delaying case-body materialization across ordered selection

Patterns have already been prepared in their authored order. A trial may
change the world and emit observations even when its state bindings fail.
Selection commits to the first successful trial; failed state bindings are
rolled back, while world changes and observations remain.

The eager representation materializes every body before this selection. The
scoped representation selects the source body first. The theorem preserves
the selected occurrence, state bindings, final world and complete trace.
The cost result counts source-body nodes visited by materialization only;
pattern preparation, frame retention and native allocation are not covered.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.DelayedCaseMaterialization

inductive Term (Var : Type) where
  | literal (value : Nat)
  | var (name : Var)
  | pair (left right : Term Var)
  deriving DecidableEq

def rename {A B : Type} (frame : A → B) : Term A → Term B
  | .literal n => .literal n
  | .var a => .var (frame a)
  | .pair left right => .pair (rename frame left) (rename frame right)

def observe {A V : Type} (store : A → Term V) : Term A → Term V
  | .literal n => .literal n
  | .var a => store a
  | .pair left right => .pair (observe store left) (observe store right)

/-- A selected source uses the same frame and the current store. The store
may contain the successful pattern trial's newly established bindings. -/
theorem observe_rename {A B V : Type} (frame : A → B) (store : B → Term V)
    (body : Term A) :
    observe store (rename frame body) = observe (store ∘ frame) body := by
  induction body with
  | literal n => rfl
  | var a => rfl
  | pair left right ihLeft ihRight => simp [rename, observe, ihLeft, ihRight]

def nodes {A : Type} : Term A → Nat
  | .literal _ | .var _ => 1
  | .pair left right => 1 + nodes left + nodes right

theorem rename_nodes {A B : Type} (frame : A → B) (body : Term A) :
    nodes (rename frame body) = nodes body := by
  induction body with
  | literal n => rfl
  | var a => rfl
  | pair left right ihLeft ihRight => simp [rename, nodes, ihLeft, ihRight]

structure Trial (Local World Event : Type) where
  bindings : Option Local
  world : World
  trace : List Event
  deriving DecidableEq

structure Selection (Body Local World Event : Type) where
  answer : Option (Body × Local)
  world : World
  trace : List Event
  deriving DecidableEq

variable {Pattern Body Image Local World Event : Type}

def select (trial : Pattern → Local → World → Trial Local World Event) :
    List (Pattern × Body) → Local → World → Selection Body Local World Event
  | [], _, world => ⟨none, world, []⟩
  | (pattern, body) :: rest, state, world =>
      let step := trial pattern state world
      match step.bindings with
      | some next => ⟨some (body, next), step.world, step.trace⟩
      | none =>
          let tail := select trial rest state step.world
          ⟨tail.answer, tail.world, step.trace ++ tail.trace⟩

def mapBody (materialize : Body → Image) (arms : List (Pattern × Body)) :
    List (Pattern × Image) := arms.map fun arm => (arm.1, materialize arm.2)

def forceSelected (materialize : Body → Image)
    (selected : Selection Body Local World Event) : Selection Image Local World Event :=
  ⟨selected.answer.map (fun chosen => (materialize chosen.1, chosen.2)),
   selected.world, selected.trace⟩

/-- Eager whole-arm mapping and selective materialization have equal ordered
observations. Materialization is a pure representation operation here. -/
theorem select_mapBody (trial : Pattern → Local → World → Trial Local World Event)
    (materialize : Body → Image) (arms : List (Pattern × Body))
    (state : Local) (world : World) :
    select trial (mapBody materialize arms) state world =
      forceSelected materialize (select trial arms state world) := by
  induction arms generalizing world with
  | nil => rfl
  | cons arm rest ih =>
      rcases arm with ⟨pattern, body⟩
      simp only [mapBody, List.map_cons, select]
      cases found : (trial pattern state world).bindings with
      | some next => simp [forceSelected]
      | none =>
          have tail := ih (trial pattern state world).world
          simp only [mapBody] at tail
          rw [tail]
          rfl

/-- Keeping source plus frame cannot change which arm wins. Its current-store
observation is also equal by `observe_rename`. -/
theorem scoped_selection {A B : Type}
    (trial : Pattern → Local → World → Trial Local World Event)
    (frame : A → B) (arms : List (Pattern × Term A)) (state : Local) (world : World) :
    select trial (mapBody (rename frame) arms) state world =
      forceSelected (rename frame) (select trial arms state world) :=
  select_mapBody trial (rename frame) arms state world

def eagerCost (cost : Body → Nat) (arms : List (Pattern × Body)) : Nat :=
  (arms.map (fun arm => cost arm.2)).sum

def selectedCost (cost : Body → Nat) (selected : Selection Body Local World Event) : Nat :=
  match selected.answer with
  | none => 0
  | some (body, _) => cost body

theorem selective_cost_le (trial : Pattern → Local → World → Trial Local World Event)
    (cost : Body → Nat) (arms : List (Pattern × Body)) (state : Local) (world : World) :
    selectedCost cost (select trial arms state world) ≤ eagerCost cost arms := by
  induction arms generalizing world with
  | nil => simp [select, selectedCost, eagerCost]
  | cons arm rest ih =>
      rcases arm with ⟨pattern, body⟩
      simp only [select]
      cases found : (trial pattern state world).bindings with
      | some next => simp [selectedCost, eagerCost]
      | none =>
          simp only [selectedCost]
          have bound := ih (trial pattern state world).world
          unfold selectedCost at bound
          simp only [eagerCost, List.map_cons, List.sum_cons]
          exact bound.trans (Nat.le_add_left _ _)

/-- Zero represents the distinguished Empty literal in this source-marker
model. Resolving a variable to that literal does not change its source role. -/
def emptyMarker {A : Type} : Term A → Bool
  | .literal 0 => true
  | _ => false

theorem marker_rename {A B : Type} (frame : A → B) (pattern : Term A) :
    emptyMarker (rename frame pattern) = emptyMarker pattern := by
  cases pattern with
  | literal n => cases n <;> rfl
  | var a => rfl
  | pair left right => rfl

example : emptyMarker (Term.var (0 : Nat)) = false ∧
    emptyMarker (observe (fun _ : Nat => Term.literal 0) (.var 0) : Term Nat) = true := by
  decide

private def trial (pattern state world : Nat) : Trial Nat Nat Nat :=
  ⟨if pattern = 7 then some (state + 1) else none, world + 1, [pattern]⟩

-- Failed trials retain their observations and world updates. The first of
-- two matching occurrences wins; later arms are not tried.
example : select trial [(2, 20), (7, 70), (7, 71)] 10 0 =
    (⟨some (70, 11), 2, [2, 7]⟩ : Selection Nat Nat Nat Nat) := by decide

-- Materializing unselected bodies is measurable work, even though it has
-- no semantic effects in this admitted representation region.
example : selectedCost id (select trial [(2, 1000), (7, 3), (7, 2000)] 0 0) = 3 ∧
    eagerCost id [(2, 1000), (7, 3), (7, 2000)] = 3003 := by decide

-- A frame cannot be replaced by a superficially similar source variable.
example : observe (fun n : Nat => Term.literal n)
    (rename (fun n : Nat => n + 10) (.var 2)) ≠
      (observe (fun n : Nat => Term.literal n) (.var 2) : Term Nat) := by decide

-- First-success commitment is observable; reversing arms is not admitted.
example : (select trial [(7, 70), (7, 71)] 0 0).answer ≠
    (select trial [(7, 71), (7, 70)] 0 0).answer := by decide

end Mettapedia.Machines.DelayedCaseMaterialization
