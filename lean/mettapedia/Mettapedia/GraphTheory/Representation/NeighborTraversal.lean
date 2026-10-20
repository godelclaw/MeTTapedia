import Mettapedia.GraphTheory.Representation.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Ordered neighbor enumeration and sparse graph frontiers

An enumeration retains traversal order while presenting exactly the neighbors
of an independently supplied graph. Its no-duplication law is needed when
additive traversal counts occurrences. The graph, its adjacency predicate and
its matrix meaning are not defined by the traversal algorithm.

The shared fold below visits only the listed neighbors. Over an additive
commutative monoid its result is independent of their order; over a semiring
it is the corresponding adjacency-matrix action. Iterating that sparse action
therefore computes the existing length-indexed walk counts.

These are exact arithmetic and entry-visit statements. List slicing, indexing,
allocation and physical execution costs are not included in the visit count.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.Representation

open scoped BigOperators
open Matrix

/-- An ordered, duplicate-free enumeration of an independent graph's neighbors.
No finite vertex universe or decidable adjacency oracle is required. -/
structure NeighborEnumeration {V : Type*} (graph : SimpleGraph V) where
  row : V → List V
  nodup : ∀ vertex, (row vertex).Nodup
  mem_iff : ∀ source target, target ∈ row source ↔ graph.Adj source target

namespace NeighborEnumeration

variable {V A : Type*} {graph : SimpleGraph V}

/-- Change the stated graph meaning along an equality, retaining every entry
and its order. This does not re-enumerate the neighbors. -/
def transport (enumeration : NeighborEnumeration graph) {other : SimpleGraph V}
    (same : graph = other) : NeighborEnumeration other where
  row := enumeration.row
  nodup := enumeration.nodup
  mem_iff source target := by rw [← same]; exact enumeration.mem_iff source target

/-- A genuine left-to-right accumulator, preserving its initial value. -/
def accumulate [AddMonoid A] (values : V → A) (entries : List V) (initial : A) : A :=
  entries.foldl (fun total vertex => total + values vertex) initial

theorem accumulate_eq_add_sum [AddMonoid A] (values : V → A)
    (entries : List V) (initial : A) :
    accumulate values entries initial = initial + (entries.map values).sum := by
  induction entries generalizing initial with
  | nil => simp [accumulate]
  | cons vertex entries inductionHypothesis =>
      simpa only [accumulate, List.foldl_cons, List.map_cons, List.sum_cons,
        add_assoc] using inductionHypothesis (initial + values vertex)

theorem accumulate_append [AddMonoid A] (values : V → A)
    (first second : List V) (initial : A) :
    accumulate values (first ++ second) initial =
      accumulate values second (accumulate values first initial) := by
  exact List.foldl_append

/-- Values may be regrouped or reordered only after the relevant algebraic
law has been supplied. Addition in this theorem is commutative. -/
theorem accumulate_perm [AddCommMonoid A] (values : V → A)
    {first second : List V} (permutation : first.Perm second) (initial : A) :
    accumulate values first initial = accumulate values second initial := by
  rw [accumulate_eq_add_sum, accumulate_eq_add_sum,
    (permutation.map values).sum_eq]

/-- A sparse update returns its sum and the exact number of listed visits. -/
def update [AddMonoid A] (enumeration : NeighborEnumeration graph)
    (values : V → A) (target : V) : Measured A :=
  ⟨accumulate values (enumeration.row target) 0, (enumeration.row target).length⟩

@[simp] theorem update_work [AddMonoid A] (enumeration : NeighborEnumeration graph)
    (values : V → A) (target : V) :
    (enumeration.update values target).work = (enumeration.row target).length := rfl

theorem update_value [AddMonoid A] (enumeration : NeighborEnumeration graph)
    (values : V → A) (target : V) :
    (enumeration.update values target).value =
      ((enumeration.row target).map values).sum := by
  simp [update, accumulate_eq_add_sum]

/-- Distinct neighbor orderings have the same sum. Their work also agrees,
because each neighbor occurs exactly once in both enumerations. -/
theorem rows_perm (first second : NeighborEnumeration graph) (vertex : V) :
    (first.row vertex).Perm (second.row vertex) := by
  apply (List.perm_ext_iff_of_nodup (first.nodup vertex) (second.nodup vertex)).2
  intro neighbor
  rw [first.mem_iff, second.mem_iff]

theorem update_eq [AddCommMonoid A] (first second : NeighborEnumeration graph)
    (values : V → A) (vertex : V) : first.update values vertex = second.update values vertex := by
  have permutation := rows_perm first second vertex
  unfold update
  rw [accumulate_perm values permutation, permutation.length_eq]

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel graph.Adj]

/-- The stored row is exactly Mathlib's neighbor finset, with order retained
on the list side. -/
theorem row_toFinset (enumeration : NeighborEnumeration graph) (vertex : V) :
    (enumeration.row vertex).toFinset = graph.neighborFinset vertex := by
  ext neighbor
  simp [enumeration.mem_iff, SimpleGraph.mem_neighborFinset]

theorem update_eq_neighbor_sum [AddCommMonoid A]
    (enumeration : NeighborEnumeration graph) (values : V → A) (vertex : V) :
    (enumeration.update values vertex).value = ∑ neighbor ∈ graph.neighborFinset vertex,
      values neighbor := by
  rw [update_value, ← List.sum_toFinset values (enumeration.nodup vertex), row_toFinset]

theorem update_work_eq_degree [AddMonoid A]
    (enumeration : NeighborEnumeration graph) (values : V → A) (vertex : V) :
    (enumeration.update values vertex).work = graph.degree vertex := by
  rw [update_work, ← List.toFinset_card_of_nodup (enumeration.nodup vertex), row_toFinset]
  rfl

/-- Sparse neighbor gathering agrees with dense matrix-vector multiplication.
The coefficient order is fixed by the column-vector convention. -/
theorem update_eq_mulVec {R : Type*} [Semiring R]
    (enumeration : NeighborEnumeration graph) (values : V → R) (vertex : V) :
    (enumeration.update values vertex).value = (graph.adjMatrix R *ᵥ values) vertex := by
  rw [update_eq_neighbor_sum]
  simp [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply,
    SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]

/-- The matrix coefficient of a natural update is not an assumed adjacency
oracle: it is obtained by the sparse enumeration fold. -/
theorem update_eq_row_action {R : Type*} [Semiring R]
    (enumeration : NeighborEnumeration graph) (values : V → R) (target : V) :
    (enumeration.update values target).value =
      ∑ source, values source * graph.adjMatrix R source target := by
  rw [update_eq_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro source _
  by_cases adjacent : graph.Adj target source
  · have reverse := graph.adj_symm adjacent
    simp [SimpleGraph.adjMatrix_apply, adjacent, reverse]
  · have reverse : ¬ graph.Adj source target := fun h => adjacent (graph.adj_symm h)
    simp [SimpleGraph.adjMatrix_apply, adjacent, reverse]

end Finite

/-- Apply one sparse update simultaneously to every target. Each row is
visited once; no scan over the full vertex universe occurs in an update. -/
def act [AddMonoid A] (enumeration : NeighborEnumeration graph) (values : V → A) : V → A :=
  fun target => (enumeration.update values target).value

theorem act_eq_mulVec {R : Type*} [Semiring R]
    [Fintype V] [DecidableEq V] [DecidableRel graph.Adj]
    (enumeration : NeighborEnumeration graph) (values : V → R) :
    enumeration.act values = graph.adjMatrix R *ᵥ values := by
  funext vertex
  exact update_eq_mulVec enumeration values vertex

/-- Independently iterate the sparse neighbor fold. -/
def iterate [AddMonoid A] (enumeration : NeighborEnumeration graph)
    (initial : V → A) : Nat → V → A
  | 0 => initial
  | length + 1 => enumeration.act (enumeration.iterate initial length)

@[simp] theorem iterate_transport [AddMonoid A] (enumeration : NeighborEnumeration graph)
    {other : SimpleGraph V} (same : graph = other) (initial : V → A) (length : Nat) :
    (enumeration.transport same).iterate initial length = enumeration.iterate initial length := by
  cases same
  rfl

/-- Equal stored rows induce equal traversals even when their graph
invariants were packaged or transported differently. -/
theorem iterate_congr_rows [AddMonoid A] {other : SimpleGraph V}
    (first : NeighborEnumeration graph) (second : NeighborEnumeration other)
    (same : first.row = second.row) (initial : V → A) (length : Nat) :
    first.iterate initial length = second.iterate initial length := by
  induction length with
  | zero => rfl
  | succ length inductionHypothesis =>
      simp only [iterate, inductionHypothesis]
      funext vertex
      simp only [act, update, same]

theorem iterate_eq [AddCommMonoid A] (first second : NeighborEnumeration graph)
    (initial : V → A) (length : Nat) :
    first.iterate initial length = second.iterate initial length := by
  induction length with
  | zero => rfl
  | succ length inductionHypothesis =>
      simp only [iterate, inductionHypothesis]
      funext vertex
      exact congrArg Measured.value (update_eq first second _ vertex)

theorem iterate_eq_pow_mulVec {R : Type*} [Semiring R]
    [Fintype V] [DecidableEq V] [DecidableRel graph.Adj]
    (enumeration : NeighborEnumeration graph) (initial : V → R) (length : Nat) :
    enumeration.iterate initial length = graph.adjMatrix R ^ length *ᵥ initial := by
  induction length with
  | zero => simp [iterate]
  | succ length inductionHypothesis =>
      rw [iterate, act_eq_mulVec, inductionHypothesis, Matrix.mulVec_mulVec, ← pow_succ']

/-- Additive interpretation maps commute with actual sparse execution. This
permits optional readouts without assuming that they preserve information. -/
theorem update_map {B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (interpretation : A →+ B) (enumeration : NeighborEnumeration graph)
    (values : V → A) (target : V) :
    interpretation (enumeration.update values target).value =
      (enumeration.update (interpretation ∘ values) target).value := by
  simp only [update_value, map_list_sum, List.map_map, Function.comp_def]

theorem iterate_map {B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (interpretation : A →+ B) (enumeration : NeighborEnumeration graph)
    (initial : V → A) (length : Nat) :
    interpretation ∘ enumeration.iterate initial length =
      enumeration.iterate (interpretation ∘ initial) length := by
  induction length with
  | zero => rfl
  | succ length inductionHypothesis =>
      funext target
      simpa only [iterate, act, Function.comp_apply, inductionHypothesis] using
        update_map interpretation enumeration (enumeration.iterate initial length) target

end NeighborEnumeration

end Mettapedia.GraphTheory.Representation
