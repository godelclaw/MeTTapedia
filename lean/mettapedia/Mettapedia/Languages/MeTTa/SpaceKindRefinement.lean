import Mettapedia.Languages.MeTTa.SpaceKindContracts
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.List.Rotate

/-!
# Occurrence-level refinement of space kinds: a kind specifies a behaviour, an engine refines it

A space kind is a specification: the commands of its interface, a reference
state with the kind's disciplines, and the observations its contract fixes. An
engine is an implementation: its own state, its own operations, its own way of
computing the observations. Both are machines (`Machine`); what a machine shows
is its behaviour, the observation after every program (`Machine.behaviour`).

* **Implementing a kind is having its behaviour.** An abstraction function
  from the engine's states to the kind's states that commutes with every
  command and preserves the observation (`Refinement`, a forward simulation)
  proves it (`Refinement.behaviour_eq`), so **any two engines refining one
  kind give the same answers to every program** (`engines_agree`). The method
  is complete: an engine refines the machine whose states are behaviours
  exactly when it has that behaviour (`refines_final_iff`). Refinements
  compose (`Refinement.trans`), and an engine may be restricted to an
  invariant without changing its behaviour (`Machine.behaviour_restrict`).
* **Engines of the atom kind** (`atomMachine`, observing the bag): CeTTa's
  native storage, a list of rows from which `remove-atom` swaps the last row
  into the removed one (`nativeBag`, `swapRemove`), and a counted store such as
  a counted PathMap trie (`countedBag`). Both refine the atom kind
  (`nativeBag_refines`, `countedBag_refines`), so `match` gives the same bag of
  answers on both. A store of the support alone is a lawful set engine and not
  an atom engine (`Controls.support_not_atom_engine`).
* **The set kind on an atom engine.** Inserting only through
  `add-atom-nodup` on any engine of the atom kind refines the set kind
  (`nodupRefinesSet`); one plain `add-atom` breaks it
  (`Controls.plain_add_breaks_nodup`).
* **Engines of ordered kinds.** CeTTa's queue keeps a buffer and an offset
  (`offsetQueue`); a functional queue keeps a front list and a reversed back
  list (`twoListQueue`). Both refine the queue kind, reading the front
  natively (`offsetQueue_refines`, `twoListQueue_refines`). A linked stack
  kept top first refines CeTTa's stack, whose removal takes the oldest
  occurrence (`linkedStack_refines`).
* **What an engine must store.** An engine has to tell apart whatever its
  kind's observations tell apart: any queue engine reaches different states on
  two insertion orders of the same atoms (`Controls.queue_engine_keeps_order`),
  so a store of counts serves bag kinds and not ordered ones.
* **Order is not in the contract.** Listing the same bag, the native engine
  gives insertion order and the counted engine canonical order
  (`Controls.enumeration_order_differs`); after a removal the native order is
  that of the swap (`Controls.swapRemove_example`).

**Relation to other space theory.** The observations here are occurrence
bags, for every program. `CeTTaSpaceEngineRefinement` states engine refinement
at the level of the atoms present, against one concrete HE space
(`SharedQueryRefinement`, built on `HE.FaithfulBackend`), together with the
separation of execution authority. `SpaceKindSupportBridge` proves that a
refinement of the atom kind here induces that seam for programs whose
equations are closed, why it cannot for open ones (HE's equation query
freshens variables by list position), and that the converse fails: a store of
the support alone gives the seam without being an atom engine
(`supportSet_not_refines_atom`). LeaTTa's named spaces append on the right and
erase the first occurrence (`HE.SpaceAlgebraLeaTTa`): the history kind with
removal from the front. A PathMap trie keeps the support and needs multiplicity
in a separate layer (`OSLF.PathMap.HEBridge`), as `countedBag` does. The
revisioned-world modules (`MeTTaRevisionedQueryBindEval`,
`MeTTaFiniteRevisionedKernel`) likewise compare occurrence bags, not row order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceKindRefinement

open Mettapedia.Languages.MeTTa.SpaceKinds
open Mettapedia.Languages.MeTTa.SpaceKindContracts

universe u v w w₁ w₂ w₃

/-! ## Machines, behaviours and refinement -/

/-- A deterministic machine with an observation: the commands of an interface
act on its state, and the observation is what a client can see. -/
structure Machine (Cmd : Type u) (Obs : Type v) where
  State : Type w
  init : State
  step : State → Cmd → State
  observe : State → Obs

namespace Machine

variable {Cmd : Type u} {Obs : Type v}

/-- What a machine shows from a state: the observation after each program. -/
def behaviourFrom (machine : Machine.{u, v, w} Cmd Obs) (state : machine.State)
    (program : List Cmd) : Obs :=
  machine.observe (program.foldl machine.step state)

/-- What a machine shows: the observation after each program run from the
initial state. -/
def behaviour (machine : Machine.{u, v, w} Cmd Obs) : List Cmd → Obs :=
  machine.behaviourFrom machine.init

/-- The state a program reaches. -/
def run (machine : Machine.{u, v, w} Cmd Obs) (program : List Cmd) : machine.State :=
  program.foldl machine.step machine.init

theorem behaviourFrom_cons (machine : Machine.{u, v, w} Cmd Obs) (state : machine.State)
    (command : Cmd) (program : List Cmd) :
    machine.behaviourFrom state (command :: program) =
      machine.behaviourFrom (machine.step state command) program := rfl

/-- The machine whose states are behaviours: a command shifts the behaviour,
and the observation is what the behaviour shows now. -/
abbrev final (shown : List Cmd → Obs) : Machine.{u, v, max u v} Cmd Obs where
  State := List Cmd → Obs
  init := shown
  step current command := fun program => current (command :: program)
  observe current := current []

/-- Restrict a machine to an invariant of its reachable states. -/
abbrev restrict (machine : Machine.{u, v, w} Cmd Obs) (invariant : machine.State → Prop)
    (initial : invariant machine.init)
    (preserved : ∀ state command, invariant state → invariant (machine.step state command)) :
    Machine.{u, v, w} Cmd Obs where
  State := {state // invariant state}
  init := ⟨machine.init, initial⟩
  step state command := ⟨machine.step state.1 command, preserved state.1 command state.2⟩
  observe state := machine.observe state.1

/-- Restricting to an invariant does not change the behaviour. -/
theorem behaviour_restrict (machine : Machine.{u, v, w} Cmd Obs)
    (invariant : machine.State → Prop) (initial : invariant machine.init)
    (preserved : ∀ state command, invariant state → invariant (machine.step state command)) :
    (machine.restrict invariant initial preserved).behaviour = machine.behaviour := by
  funext program
  suffices ∀ state : {state // invariant state},
      (machine.restrict invariant initial preserved).behaviourFrom state program =
        machine.behaviourFrom state.1 program from this _
  induction program with
  | nil => intro state; rfl
  | cons command rest ih => intro state; exact ih _

end Machine

/-- **A refinement**: an abstraction function from the implementation's
states to the specification's, commuting with every command and preserving
the observation. -/
structure Refinement {Cmd : Type u} {Obs : Type v} (impl : Machine.{u, v, w₁} Cmd Obs)
    (spec : Machine.{u, v, w₂} Cmd Obs) where
  abs : impl.State → spec.State
  abs_init : abs impl.init = spec.init
  abs_step : ∀ state command, abs (impl.step state command) = spec.step (abs state) command
  observe_abs : ∀ state, impl.observe state = spec.observe (abs state)

namespace Refinement

variable {Cmd : Type u} {Obs : Type v}

theorem behaviourFrom_abs {impl : Machine.{u, v, w₁} Cmd Obs} {spec : Machine.{u, v, w₂} Cmd Obs}
    (refinement : Refinement impl spec) (state : impl.State) (program : List Cmd) :
    spec.behaviourFrom (refinement.abs state) program = impl.behaviourFrom state program := by
  induction program generalizing state with
  | nil => exact (refinement.observe_abs state).symm
  | cons command rest ih =>
      rw [Machine.behaviourFrom_cons, Machine.behaviourFrom_cons, ← refinement.abs_step, ih]

/-- The abstraction of the state a program reaches is the state the
specification reaches. -/
theorem abs_run {impl : Machine.{u, v, w₁} Cmd Obs} {spec : Machine.{u, v, w₂} Cmd Obs}
    (refinement : Refinement impl spec) (program : List Cmd) :
    refinement.abs (impl.run program) = spec.run program := by
  suffices ∀ state : impl.State,
      refinement.abs (program.foldl impl.step state) = program.foldl spec.step (refinement.abs state) by
    rw [Machine.run, Machine.run, this, refinement.abs_init]
  induction program with
  | nil => intro state; rfl
  | cons command rest ih =>
      intro state
      rw [List.foldl_cons, List.foldl_cons, ih, refinement.abs_step]

/-- **A refinement preserves behaviour.** -/
theorem behaviour_eq {impl : Machine.{u, v, w₁} Cmd Obs} {spec : Machine.{u, v, w₂} Cmd Obs}
    (refinement : Refinement impl spec) : impl.behaviour = spec.behaviour := by
  funext program
  rw [Machine.behaviour, Machine.behaviour, ← refinement.abs_init, refinement.behaviourFrom_abs]

/-- Every machine refines itself. -/
def refl (machine : Machine.{u, v, w} Cmd Obs) : Refinement machine machine where
  abs := id
  abs_init := rfl
  abs_step _ _ := rfl
  observe_abs _ := rfl

/-- Refinements compose. -/
def trans {first : Machine.{u, v, w₁} Cmd Obs} {second : Machine.{u, v, w₂} Cmd Obs}
    {third : Machine.{u, v, w₃} Cmd Obs} (lower : Refinement first second)
    (upper : Refinement second third) : Refinement first third where
  abs := upper.abs ∘ lower.abs
  abs_init := by simp [lower.abs_init, upper.abs_init]
  abs_step state command := by simp [lower.abs_step, upper.abs_step]
  observe_abs state := (lower.observe_abs state).trans (upper.observe_abs _)

end Refinement

/-- **Engine independence**: two engines refining one specification answer
every program alike. -/
theorem engines_agree {Cmd : Type u} {Obs : Type v} {spec : Machine.{u, v, w} Cmd Obs}
    {first : Machine.{u, v, w₁} Cmd Obs} {second : Machine.{u, v, w₂} Cmd Obs}
    (firstRefines : Refinement first spec) (secondRefines : Refinement second spec) :
    first.behaviour = second.behaviour :=
  firstRefines.behaviour_eq.trans secondRefines.behaviour_eq.symm

/-- Every machine refines the machine of its own behaviour. -/
def toFinal {Cmd : Type u} {Obs : Type v} (machine : Machine.{u, v, w} Cmd Obs) :
    Refinement machine (Machine.final machine.behaviour) where
  abs := machine.behaviourFrom
  abs_init := rfl
  abs_step _ _ := rfl
  observe_abs _ := rfl

theorem final_behaviour {Cmd : Type u} {Obs : Type v} (shown : List Cmd → Obs) :
    (Machine.final shown).behaviour = shown := by
  funext program
  suffices ∀ current : List Cmd → Obs,
      (Machine.final shown).behaviourFrom current program = current program from this shown
  induction program with
  | nil => intro current; rfl
  | cons command rest ih =>
      intro current
      exact ih fun program => current (command :: program)

/-- **Refinement is complete**: a machine refines the machine of a behaviour
exactly when it has that behaviour. -/
theorem refines_final_iff {Cmd : Type u} {Obs : Type v} (machine : Machine.{u, v, w} Cmd Obs)
    (shown : List Cmd → Obs) :
    Nonempty (Refinement machine (Machine.final shown)) ↔ machine.behaviour = shown := by
  constructor
  · rintro ⟨refinement⟩
    rw [refinement.behaviour_eq, final_behaviour]
  · intro same
    subst same
    exact ⟨toFinal machine⟩

/-! ## The machines of the kinds -/

/-- The commands of the common interface. -/
inductive Command (α : Type u) where
  | add (atom : α)
  | remove (atom : α)

/-- The commands of an ordered space. -/
inductive OrderedCommand (α : Type u) where
  | add (atom : α)
  | remove (atom : α)
  | pop

variable {α : Type u}

/-- A kind under the common interface: it shows its space view. -/
abbrev kindMachine (κ : Kind.{u, v} α) : Machine.{u, u, v} (Command α) (Multiset α) where
  State := κ.State
  init := κ.empty
  step state
    | .add atom => κ.add state atom
    | .remove atom => κ.remove state atom
  observe := κ.contents

/-- The atom kind as a machine. -/
abbrev atomMachine [DecidableEq α] : Machine.{u, u, u} (Command α) (Multiset α) :=
  kindMachine atomKind

/-- The set kind as a machine. -/
abbrev setMachine [DecidableEq α] : Machine.{u, u, u} (Command α) (Multiset α) :=
  kindMachine setKind

/-- An ordered space as a machine: it shows its space view and the element it
reads next. -/
abbrev orderedMachine [DecidableEq α] (ordered : Ordered) :
    Machine.{u, u, u} (OrderedCommand α) (Multiset α × Option α) where
  State := List α
  init := []
  step state
    | .add atom => state ++ [atom]
    | .remove atom => eraseAt ordered.removal state atom
    | .pop => popAt ordered.access state
  observe state := ((state : Multiset α), peekAt ordered.access state)

/-! ## Engines of the atom kind -/

section Atom

variable [DecidableEq α]

/-- CeTTa's removal from an unordered space: the first occurrence is replaced
by the last row, and the last row is dropped. -/
def swapRemove (stored : List α) (atom : α) : List α :=
  let after := (stored.dropWhile (· != atom)).drop 1
  stored.takeWhile (· != atom) ++ after.rotate (after.length - 1)

theorem erase_eq_takeWhile_append (stored : List α) (atom : α) :
    stored.erase atom = stored.takeWhile (· != atom) ++ (stored.dropWhile (· != atom)).drop 1 := by
  induction stored with
  | nil => rfl
  | cons head tail ih =>
      by_cases same : head = atom
      · subst same
        simp
      · rw [List.erase_cons_tail (by simpa using same)]
        simp [same, ih]

/-- Swapping the last row in takes one occurrence off the bag. -/
theorem coe_swapRemove (stored : List α) (atom : α) :
    ((swapRemove stored atom : List α) : Multiset α) = (stored : Multiset α).erase atom := by
  rw [Multiset.coe_erase, erase_eq_takeWhile_append, swapRemove]
  exact Multiset.coe_eq_coe.mpr ((List.rotate_perm _ _).append_left _)

/-- CeTTa's native storage of an unordered space: rows in a list, appended on
insertion, swap-removed on removal. -/
abbrev nativeBag : Machine.{u, u, u} (Command α) (Multiset α) where
  State := List α
  init := []
  step stored
    | .add atom => stored ++ [atom]
    | .remove atom => swapRemove stored atom
  observe stored := stored

def nativeBag_refines : Refinement (nativeBag (α := α)) atomMachine where
  abs stored := ((stored : List α) : Multiset α)
  abs_init := rfl
  abs_step stored command := by
    cases command with
    | add atom =>
        exact Multiset.coe_eq_coe.mpr (List.perm_append_singleton atom stored)
    | remove atom => exact coe_swapRemove stored atom
  observe_abs _ := rfl

theorem toMultiset_sub_single (counts : α →₀ ℕ) (atom : α) :
    Finsupp.toMultiset (counts - Finsupp.single atom 1) = (Finsupp.toMultiset counts).erase atom := by
  ext other
  rw [Finsupp.count_toMultiset, Finsupp.coe_tsub, Pi.sub_apply]
  by_cases same : other = atom
  · subst same
    rw [Multiset.count_erase_self, Finsupp.count_toMultiset, Finsupp.single_eq_same]
  · rw [Multiset.count_erase_of_ne same, Finsupp.count_toMultiset,
      Finsupp.single_eq_of_ne same, Nat.sub_zero]

/-- A counted store: each atom with the number of its occurrences, as a
counted trie keeps them. -/
noncomputable abbrev countedBag : Machine.{u, u, u} (Command α) (Multiset α) where
  State := α →₀ ℕ
  init := 0
  step counts
    | .add atom => counts + Finsupp.single atom 1
    | .remove atom => counts - Finsupp.single atom 1
  observe := Finsupp.toMultiset

noncomputable def countedBag_refines : Refinement (countedBag (α := α)) atomMachine where
  abs := Finsupp.toMultiset
  abs_init := Finsupp.toMultiset_zero
  abs_step counts command := by
    cases command with
    | add atom =>
        show Finsupp.toMultiset ((counts : α →₀ ℕ) + Finsupp.single atom 1) =
          atom ::ₘ Finsupp.toMultiset (counts : α →₀ ℕ)
        rw [Finsupp.toMultiset_add, Finsupp.toMultiset_single, one_smul, add_comm,
          Multiset.singleton_add]
    | remove atom => exact toMultiset_sub_single counts atom
  observe_abs _ := rfl

/-- **The native engine and a counted engine answer every program alike.** -/
theorem nativeBag_countedBag_agree :
    (nativeBag (α := α)).behaviour = (countedBag (α := α)).behaviour :=
  engines_agree nativeBag_refines countedBag_refines

/-- A store of the support alone. -/
abbrev supportSet : Machine.{u, u, u} (Command α) (Multiset α) where
  State := Finset α
  init := ∅
  step stored
    | .add atom => insert atom stored
    | .remove atom => stored.erase atom
  observe stored := stored.val

def supportSet_refines : Refinement (supportSet (α := α)) setMachine where
  abs stored := stored
  abs_init := rfl
  abs_step stored command := by cases command <;> rfl
  observe_abs _ := rfl

end Atom

/-- **A store of the support alone is no atom engine**, over any type of
atoms: after adding an atom twice it shows one copy, the atom kind two. -/
theorem supportSet_not_refines_atom [DecidableEq α] (atom : α) :
    IsEmpty (Refinement (supportSet (α := α)) atomMachine) := by
  refine ⟨fun refinement => ?_⟩
  have shown := congrFun refinement.behaviour_eq [.add atom, .add atom]
  have counted := congrArg Multiset.card shown
  change Multiset.card (insert atom (insert atom (∅ : Finset α))).val =
    Multiset.card (atom ::ₘ atom ::ₘ (0 : Multiset α)) at counted
  rw [Finset.insert_eq_of_mem (Finset.mem_insert_self atom ∅)] at counted
  simp at counted

/-! ## The set kind on an atom engine -/

section Nodup

variable [DecidableEq α]

/-- Insert through `add-atom-nodup` on an engine: add unless already shown. -/
abbrev nodupOver (engine : Machine.{u, u, w} (Command α) (Multiset α)) :
    Machine.{u, u, w} (Command α) (Multiset α) where
  State := engine.State
  init := engine.init
  step state
    | .add atom => if atom ∈ engine.observe state then state else engine.step state (.add atom)
    | .remove atom => engine.step state (.remove atom)
  observe := engine.observe

theorem observe_step_add {engine : Machine.{u, u, w} (Command α) (Multiset α)}
    (refines : Refinement engine atomMachine) (state : engine.State) (atom : α) :
    engine.observe (engine.step state (.add atom)) = atom ::ₘ engine.observe state := by
  rw [refines.observe_abs, refines.abs_step, refines.observe_abs]
  rfl

theorem observe_step_remove {engine : Machine.{u, u, w} (Command α) (Multiset α)}
    (refines : Refinement engine atomMachine) (state : engine.State) (atom : α) :
    engine.observe (engine.step state (.remove atom)) = (engine.observe state).erase atom := by
  rw [refines.observe_abs, refines.abs_step, refines.observe_abs]
  rfl

/-- Inserting through `add-atom-nodup` keeps the shown bag duplicate-free. -/
theorem nodupOver_preserves {engine : Machine.{u, u, w} (Command α) (Multiset α)}
    (refines : Refinement engine atomMachine) (state : engine.State) (command : Command α)
    (nodup : (engine.observe state).Nodup) :
    ((nodupOver engine).observe ((nodupOver engine).step state command)).Nodup := by
  cases command with
  | add atom =>
      show (engine.observe (if atom ∈ engine.observe state then state
        else engine.step state (.add atom))).Nodup
      split_ifs with present
      · exact nodup
      · rw [observe_step_add refines]
        exact Multiset.nodup_cons.mpr ⟨present, nodup⟩
  | remove atom =>
      show (engine.observe (engine.step state (.remove atom))).Nodup
      rw [observe_step_remove refines]
      exact nodup.erase atom

theorem nodupOver_init {engine : Machine.{u, u, w} (Command α) (Multiset α)}
    (refines : Refinement engine atomMachine) : (engine.observe engine.init).Nodup := by
  rw [refines.observe_abs, refines.abs_init]
  exact Multiset.nodup_zero

/-- `add-atom-nodup` on an atom engine, restricted to the duplicate-free
states it reaches. -/
abbrev nodupEngine {engine : Machine.{u, u, w} (Command α) (Multiset α)}
    (refines : Refinement engine atomMachine) : Machine.{u, u, w} (Command α) (Multiset α) :=
  (nodupOver engine).restrict (fun state => (engine.observe state).Nodup)
    (nodupOver_init refines) (nodupOver_preserves refines)

/-- **Inserting only through `add-atom-nodup` on any engine of the atom kind
refines the set kind.** -/
def nodupRefinesSet {engine : Machine.{u, u, w} (Command α) (Multiset α)}
    (refines : Refinement engine atomMachine) : Refinement (nodupEngine refines) setMachine where
  abs state := ⟨engine.observe state.1, state.2⟩
  abs_init := by
    apply Finset.val_injective
    show engine.observe engine.init = 0
    rw [refines.observe_abs, refines.abs_init]
    rfl
  abs_step state command := by
    apply Finset.val_injective
    cases command with
    | add atom =>
        show engine.observe (if atom ∈ engine.observe state.1 then state.1
          else engine.step state.1 (.add atom)) =
          Multiset.ndinsert atom (engine.observe state.1)
        by_cases present : atom ∈ engine.observe state.1
        · rw [if_pos present, Multiset.ndinsert_of_mem present]
        · rw [if_neg present, Multiset.ndinsert_of_notMem present]
          exact observe_step_add refines state.1 atom
    | remove atom =>
        show engine.observe (engine.step state.1 (.remove atom)) =
          (engine.observe state.1).erase atom
        exact observe_step_remove refines state.1 atom
  observe_abs _ := rfl

/-- The native engine under `add-atom-nodup` and the set kind answer alike. -/
theorem nodup_native_agrees_with_set :
    (nodupOver (nativeBag (α := α))).behaviour = (setMachine (α := α)).behaviour := by
  rw [← Machine.behaviour_restrict (nodupOver nativeBag) _ (nodupOver_init nativeBag_refines)
    (nodupOver_preserves nativeBag_refines)]
  exact (nodupRefinesSet nativeBag_refines).behaviour_eq

end Nodup

/-! ## Engines of ordered kinds -/

section Ordered

variable [DecidableEq α]

/-- CeTTa's queue storage: the offset of the front in a buffer. Popping an
empty queue changes nothing; removal linearizes the buffer first. -/
abbrev offsetBuffer : Machine.{u, u, u} (OrderedCommand α) (Multiset α × Option α) where
  State := ℕ × List α
  init := (0, [])
  step state
    | .add atom => (state.1, state.2 ++ [atom])
    | .remove atom => (0, (state.2.drop state.1).erase atom)
    | .pop => if state.1 < state.2.length then (state.1 + 1, state.2) else state
  observe state := ((state.2.drop state.1 : Multiset α), state.2[state.1]?)

theorem offsetBuffer_preserves (state : ℕ × List α) (command : OrderedCommand α)
    (within : state.1 ≤ state.2.length) :
    ((offsetBuffer (α := α)).step state command).1 ≤ ((offsetBuffer (α := α)).step state command).2.length := by
  cases command with
  | add atom =>
      show state.1 ≤ (state.2 ++ [atom]).length
      simp only [List.length_append, List.length_singleton]
      omega
  | remove atom => exact Nat.zero_le _
  | pop =>
      show (if state.1 < state.2.length then (state.1 + 1, state.2) else state).1 ≤
        (if state.1 < state.2.length then (state.1 + 1, state.2) else state).2.length
      split_ifs with below
      · exact below
      · exact within

/-- The queue storage, restricted to offsets within the buffer. -/
abbrev offsetQueue : Machine.{u, u, u} (OrderedCommand α) (Multiset α × Option α) :=
  (offsetBuffer (α := α)).restrict (fun state => state.1 ≤ state.2.length) (Nat.le_refl 0)
    offsetBuffer_preserves

def offsetQueue_refines : Refinement (offsetQueue (α := α)) (orderedMachine (α := α) queue) where
  abs state := state.1.2.drop state.1.1
  abs_init := rfl
  abs_step state command := by
    obtain ⟨⟨start, buffer⟩, within⟩ := state
    cases command with
    | add atom => exact List.drop_append_of_le_length within
    | remove atom => rfl
    | pop =>
        show (if start < buffer.length then (start + 1, buffer) else (start, buffer)).2.drop
            (if start < buffer.length then (start + 1, buffer) else (start, buffer)).1 =
          (buffer.drop start).tail
        split_ifs with below
        · exact List.tail_drop.symm
        · have atEnd : buffer.length ≤ start := Nat.le_of_not_lt below
          simp [List.drop_eq_nil_of_le atEnd]
  observe_abs state := by
    show ((state.1.2.drop state.1.1 : Multiset α), state.1.2[state.1.1]?) =
      ((state.1.2.drop state.1.1 : Multiset α), (state.1.2.drop state.1.1).head?)
    rw [List.head?_drop]

/-- A functional queue: the front in order and the back reversed. -/
abbrev twoListQueue : Machine.{u, u, u} (OrderedCommand α) (Multiset α × Option α) where
  State := List α × List α
  init := ([], [])
  step state
    | .add atom => (state.1, atom :: state.2)
    | .remove atom => ((state.1 ++ state.2.reverse).erase atom, [])
    | .pop =>
        match state.1 with
        | _ :: rest => (rest, state.2)
        | [] => (state.2.reverse.tail, [])
  observe state := ((state.1 ++ state.2.reverse : Multiset α), state.1.head?.or state.2.getLast?)

def twoListQueue_refines : Refinement (twoListQueue (α := α)) (orderedMachine (α := α) queue) where
  abs state := state.1 ++ state.2.reverse
  abs_init := rfl
  abs_step state command := by
    obtain ⟨front, back⟩ := state
    cases command with
    | add atom => simp [orderedMachine]
    | remove atom => simp [orderedMachine, queue, eraseAt]
    | pop =>
        cases front with
        | nil => simp [orderedMachine, queue, popAt]
        | cons head rest => simp [orderedMachine, queue, popAt]
  observe_abs state := by
    obtain ⟨front, back⟩ := state
    show ((front ++ back.reverse : Multiset α), front.head?.or back.getLast?) =
      ((front ++ back.reverse : Multiset α), (front ++ back.reverse).head?)
    rw [List.head?_append, List.head?_reverse]

/-- **The offset queue and the functional queue answer every program
alike.** -/
theorem queues_agree :
    (offsetQueue (α := α)).behaviour = (twoListQueue (α := α)).behaviour :=
  engines_agree offsetQueue_refines twoListQueue_refines

/-- A linked stack kept top first; `remove-atom` takes the oldest occurrence,
the last in this order, as CeTTa's stack does. -/
abbrev linkedStack : Machine.{u, u, u} (OrderedCommand α) (Multiset α × Option α) where
  State := List α
  init := []
  step state
    | .add atom => atom :: state
    | .remove atom => (state.reverse.erase atom).reverse
    | .pop => state.tail
  observe state := ((state : Multiset α), state.head?)

def linkedStack_refines : Refinement (linkedStack (α := α)) (orderedMachine (α := α) stack) where
  abs := List.reverse
  abs_init := rfl
  abs_step state command := by
    cases command with
    | add atom => simp [orderedMachine]
    | remove atom => simp [orderedMachine, stack, eraseAt]
    | pop => simp [orderedMachine, stack, popAt, List.dropLast_reverse]
  observe_abs state := by
    show ((state : Multiset α), state.head?) =
      ((state.reverse : Multiset α), state.reverse.getLast?)
    rw [List.getLast?_reverse, Multiset.coe_reverse]

end Ordered

/-! ## Controls -/

namespace Controls

/-- **A store of the support alone is not an atom engine**: after adding `1`
twice it shows one copy where the atom kind shows two, so no refinement
exists. -/
theorem support_not_atom_engine :
    (supportSet (α := ℕ)).behaviour [.add 1, .add 1] ≠ (atomMachine (α := ℕ)).behaviour [.add 1, .add 1] ∧
      IsEmpty (Refinement (supportSet (α := ℕ)) atomMachine) := by
  have differs : (supportSet (α := ℕ)).behaviour [.add 1, .add 1] ≠
      (atomMachine (α := ℕ)).behaviour [.add 1, .add 1] := by
    decide
  exact ⟨differs, ⟨fun refinement => differs (congrFun refinement.behaviour_eq _)⟩⟩

/-- One plain `add-atom` on the native engine shows a repeated atom, which the
set kind never shows. -/
theorem plain_add_breaks_nodup :
    (nativeBag (α := ℕ)).behaviour [.add 1, .add 1] ≠ (setMachine (α := ℕ)).behaviour [.add 1, .add 1] := by
  decide

/-- **Listing order is not in the contract**: after adding `2` then `1`, the
native engine lists its rows as `[2, 1]`; the canonical listing of the same
bag, which a counted trie gives, is `[1, 2]`. -/
theorem enumeration_order_differs :
    ((nativeBag (α := ℕ)).run [.add 2, .add 1] : List ℕ) = [2, 1] ∧
      (((nativeBag (α := ℕ)).run [.add 2, .add 1] : List ℕ) : Multiset ℕ).sort (· ≤ ·) = [1, 2] ∧
      (([2, 1] : List ℕ) : Multiset ℕ) = (([1, 2] : List ℕ) : Multiset ℕ) := by
  refine ⟨rfl, sort_eq_of_pairwise (by decide) (by decide), by decide⟩

/-- **A queue engine keeps insertion order**: whatever its storage, it
reaches different states on `[add 1, add 2]` and `[add 2, add 1]`, which have
the same atoms. A store of counts alone cannot serve a queue. -/
theorem queue_engine_keeps_order
    (engine : Machine.{0, 0, w} (OrderedCommand ℕ) (Multiset ℕ × Option ℕ))
    (refines : Refinement engine (orderedMachine (α := ℕ) queue)) :
    engine.run [.add 1, .add 2] ≠ engine.run [.add 2, .add 1] := by
  intro same
  have observed := congrArg engine.observe same
  rw [refines.observe_abs, refines.observe_abs, refines.abs_run, refines.abs_run] at observed
  revert observed
  decide

/-- Swap removal reorders the remaining rows: removing `1` from `[1, 2, 3]`
leaves `[3, 2]`. -/
theorem swapRemove_example : swapRemove ([1, 2, 3] : List ℕ) 1 = [3, 2] := by decide

end Controls

end Mettapedia.Languages.MeTTa.SpaceKindRefinement
