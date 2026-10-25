import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mettapedia.Machines.ResourceTraceWork

/-!
# Acyclicity evidence during a fixed foreign-term read

A successful graph check applies to every reachable child while the graph
remains fixed. The independently recursive reference validates guarded nodes;
the second reader materializes the same ordered image without those checks.
The validator is a proof-producing interface. Correctness of a native
validator, native getters, variable mapping and graph fallback are separate
implementation obligations.

Depth exhaustion and the request for graph decoding are distinct results.
Sharing does not authorize deduplicating child occurrences. Certificates name
the actual heap: a later foreign operation cannot reuse one on a changed heap.

The final cost model prices validation by the number of nested list cells and
charges one unit per materialized node. Its linear bound concerns this eager
representation, not arbitrary observers, allocation bytes or native time.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AcyclicReadScope

universe u v
variable {Address : Type u} {Label : Type v}

abbrev Heap (Address : Type u) (Label : Type v) :=
  Address → Option (Label × List Address)

def Edge (heap : Heap Address Label) (parent child : Address) : Prop :=
  ∃ label children, heap parent = some (label, children) ∧ child ∈ children

def AcyclicFrom (heap : Heap Address Label) (root : Address) : Prop :=
  ∀ vertex, Relation.ReflTransGen (Edge heap) root vertex →
    ¬ Relation.TransGen (Edge heap) vertex vertex

theorem acyclic_descendant (heap : Heap Address Label) (root child : Address)
    (safe : AcyclicFrom heap root)
    (path : Relation.ReflTransGen (Edge heap) root child) :
    AcyclicFrom heap child := by
  intro vertex onward cycle
  exact safe vertex (path.trans onward) cycle

theorem acyclic_child (heap : Heap Address Label) (root child : Address)
    (safe : AcyclicFrom heap root) (edge : Edge heap root child) :
    AcyclicFrom heap child :=
  acyclic_descendant heap root child safe (.tail .refl edge)

theorem path_decreases (heap : Heap Address Label) (rank : Address → Nat)
    (decreasing : ∀ parent child, Edge heap parent child → rank child < rank parent)
    {parent child : Address} (path : Relation.TransGen (Edge heap) parent child) :
    rank child < rank parent := by
  induction path with
  | single edge => exact decreasing _ _ edge
  | tail _ edge ih => exact (decreasing _ _ edge).trans ih

theorem acyclic_of_rank (heap : Heap Address Label) (rank : Address → Nat)
    (decreasing : ∀ parent child, Edge heap parent child → rank child < rank parent)
    (root : Address) : AcyclicFrom heap root := by
  intro vertex _ cycle
  have impossible := path_decreases heap rank decreasing cycle
  exact (Nat.lt_irrefl _ impossible)

inductive Image (Label : Type v)
  | node (label : Label) (children : List (Image Label))

inductive ReadFailure
  | missing
  | depth
  | needsGraph
  deriving DecidableEq

def readRaw (heap : Heap Address Label) : Nat → Address → Except ReadFailure (Image Label)
  | 0, _ => .error .depth
  | budget + 1, root =>
      match heap root with
      | none => .error .missing
      | some (label, children) =>
          (children.mapM (readRaw heap budget)).map (Image.node label)

def readChecked (heap : Heap Address Label)
    (validate : ∀ root, Decidable (AcyclicFrom heap root)) (guarded : Address → Bool) :
    Nat → Address → Except ReadFailure (Image Label)
  | 0, _ => .error .depth
  | budget + 1, root =>
      match heap root with
      | none => .error .missing
      | some (label, children) =>
          if guarded root then
            match validate root with
            | .isFalse _ => .error .needsGraph
            | .isTrue _ =>
                (children.mapM (readChecked heap validate guarded budget)).map
                  (Image.node label)
          else
            (children.mapM (readChecked heap validate guarded budget)).map
              (Image.node label)

theorem mapM_congr {α β ε : Type*} (items : List α) (left right : α → Except ε β)
    (same : ∀ item ∈ items, left item = right item) :
    items.mapM left = items.mapM right := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      have head := same item (by simp)
      have tail := ih (fun child member => same child (by simp [member]))
      simp [List.mapM_cons, head, tail]

/-- Carrying a successful root certificate erases only redundant checks.
The image, order, duplicate children and depth behavior are unchanged. -/
theorem checked_eq_raw (heap : Heap Address Label)
    (validate : ∀ root, Decidable (AcyclicFrom heap root)) (guarded : Address → Bool)
    (budget : Nat) (root : Address) (safe : AcyclicFrom heap root) :
    readChecked heap validate guarded budget root = readRaw heap budget root := by
  induction budget generalizing root with
  | zero => rfl
  | succ budget ih =>
      cases found : heap root with
      | none => simp [readChecked, readRaw, found]
      | some cell =>
          rcases cell with ⟨label, children⟩
          have sameChildren :
              children.mapM (readChecked heap validate guarded budget) =
                children.mapM (readRaw heap budget) := by
            apply mapM_congr
            intro child member
            exact ih child (acyclic_child heap root child safe
              ⟨label, children, found, member⟩)
          cases marked : guarded root with
          | false => simp [readChecked, readRaw, found, marked, sameChildren]
          | true =>
              cases result : validate root with
              | isFalse refused => exact False.elim (refused safe)
              | isTrue accepted =>
                  simp [readChecked, readRaw, found, marked, result, sameChildren]

def emptyHeap : Heap Nat Nat := fun _ => none

theorem empty_acyclic (root : Nat) : AcyclicFrom emptyHeap root := by
  have noPath : ∀ {first last}, Relation.TransGen (Edge emptyHeap) first last → False := by
    intro first last path
    induction path with
    | single edge => simp [Edge, emptyHeap] at edge
    | tail _ _ ih => exact ih
  intro vertex _ cycle
  exact noPath cycle

def cyclicHeap : Heap Nat Nat := fun vertex => if vertex = 0 then some (7, [0]) else none

theorem cyclic_root : ¬ AcyclicFrom cyclicHeap 0 := by
  intro safe
  apply safe 0 .refl
  exact .single ⟨7, [0], by simp [cyclicHeap], by simp⟩

/-- The heap index of the certificate matters. A foreign mutation may create
a cycle at precisely the root that the previous read knew was harmless. -/
theorem mutation_reopens_validation :
    AcyclicFrom emptyHeap 0 ∧ ¬ AcyclicFrom cyclicHeap 0 :=
  ⟨empty_acyclic 0, cyclic_root⟩

theorem cyclic_checked
    (validate : ∀ root, Decidable (AcyclicFrom cyclicHeap root)) (budget : Nat) :
    readChecked cyclicHeap validate (fun _ => true) (budget + 1) 0 =
      .error .needsGraph := by
  cases result : validate 0 with
  | isFalse refused => simp [readChecked, cyclicHeap, result]
  | isTrue accepted => exact False.elim (cyclic_root accepted)

theorem cyclic_raw (budget : Nat) :
    readRaw cyclicHeap budget 0 = .error .depth := by
  induction budget with
  | zero => rfl
  | succ budget ih => simp [readRaw, cyclicHeap, List.mapM_cons, ih, Except.map]

/-- A forged acyclicity flag loses a real control distinction. -/
theorem unchecked_cycle_changes_outcome
    (validate : ∀ root, Decidable (AcyclicFrom cyclicHeap root)) (budget : Nat) :
    readChecked cyclicHeap validate (fun _ => true) (budget + 1) 0 ≠
      readRaw cyclicHeap (budget + 1) 0 := by
  rw [cyclic_checked, cyclic_raw]
  intro impossible
  cases impossible

/-- A shared child remains present twice in the ordered materialized image. -/
example : readRaw (fun vertex : Nat =>
    if vertex = 0 then some (7, [1, 1]) else some (9, [])) 2 0 =
      .ok (.node 7 [.node 9 [], .node 9 []]) := by rfl

def repeatedValidationWork : Nat → Nat
  | 0 => 1
  | depth + 1 => repeatedValidationWork depth + (depth + 1) + 1

def certifiedReadWork (depth : Nat) : Nat := depth + (depth + 1)

theorem repeated_work_exact (depth : Nat) :
    2 * repeatedValidationWork depth = (depth + 1) * (depth + 2) := by
  induction depth with
  | zero => simp [repeatedValidationWork]
  | succ depth ih =>
      simp only [repeatedValidationWork]
      nlinarith

/-- This eager representation must materialize its leaf and every wrapper.
The certified read uses at most twice that constructor-count lower bound. -/
theorem certified_work_within_twice_output (depth : Nat) :
    certifiedReadWork depth ≤ 2 * (depth + 1) := by
  simp [certifiedReadWork]
  omega

theorem certified_work_le_repeated (depth : Nat) :
    certifiedReadWork depth ≤ repeatedValidationWork depth := by
  cases depth with
  | zero => simp [certifiedReadWork, repeatedValidationWork]
  | succ depth =>
      have exactWork := repeated_work_exact (depth + 1)
      simp only [certifiedReadWork]
      nlinarith [Nat.zero_le (depth * depth)]

/-- Connect the family cost to the existing complete-traversal lower bound.
The comparison class queries its root and follows every queried cell's
references. Its local obligations force all chain cells to be queried;
they do not assume the transitive footprint or the desired lower bound.
Previously retained summaries and demand-only root observations are outside
this full-reference survey class. -/
theorem certified_chain_within_twice_survey
    (depth : Nat) (queries : List Nat)
    (survey : ResourceOwnership.TraceWork.CompleteSurvey
      (ResourceOwnership.Examples.chainHeap depth)
      ResourceOwnership.Examples.oneRoot queries) :
    certifiedReadWork depth ≤ 2 * queries.length := by
  have lower := ResourceOwnership.TraceWork.trace_minimal_expansions
    (ResourceOwnership.Examples.chainHeap depth)
    ResourceOwnership.Examples.oneRoot queries survey
  rw [ResourceOwnership.TraceWork.Controls.chain_expansion_count] at lower
  exact (certified_work_within_twice_output depth).trans
    (Nat.mul_le_mul_left 2 lower)

end Mettapedia.Machines.AcyclicReadScope
