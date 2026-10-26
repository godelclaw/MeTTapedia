import Mettapedia.Algorithms.LazyProductPrefixes

/-!
# Lazy union of alternative derivation caches

The two alternatives keep disjoint identities. Their first ranks are the
only initial candidates; selecting a rank admits its next rank. Child
prefixes suffice for a global k-prefix, including tied costs and empty
alternatives. This is the alternative-family operation paired with the
lazy child-product operation.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.LazyUnionPrefixes

open Mettapedia.GSLT.Core.BranchingTemporal
open MonotoneRankEnumeration DerivationPrefix LazyProductPrefixes

variable {Left Right : Type}

def sumCost (leftCost : Left → Nat) (rightCost : Right → Nat) : Left ⊕ Right → Nat
  | .inl value => leftCost value
  | .inr value => rightCost value

def sumSource (leftSource : Left → Prop) (rightSource : Right → Prop) : Left ⊕ Right → Prop
  | .inl value => leftSource value
  | .inr value => rightSource value

abbrev Index (left : List Left) (right : List Right) := Fin left.length ⊕ Fin right.length

def decode (left : List Left) (right : List Right) : Index left right → Left ⊕ Right
  | .inl index => .inl (left.get index)
  | .inr index => .inr (right.get index)

def neighbors (left : List Left) (right : List Right) :
    Index left right → List (Index left right)
  | .inl index => if within : index.val + 1 < left.length then
      [.inl ⟨index.val + 1, within⟩] else []
  | .inr index => if within : index.val + 1 < right.length then
      [.inr ⟨index.val + 1, within⟩] else []

def roots (left : List Left) (right : List Right) : List (Index left right) :=
  (if positive : 0 < left.length then [.inl ⟨0, positive⟩] else []) ++
    (if positive : 0 < right.length then [.inr ⟨0, positive⟩] else [])

def graph (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost) :
    Graph (Index left.values right.values) :=
  ⟨neighbors left.values right.values, sumCost leftCost rightCost ∘ decode left.values right.values⟩

theorem monotone (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost) :
    MonotoneRankEnumeration.Monotone (graph leftCost rightCost left right) := by
  rintro (index | index) child present <;>
    change child ∈ (if within : _ then [_] else []) at present <;> split at present
  all_goals try { simp at present }
  all_goals
    have same := List.mem_singleton.mp present
    subst child
    first
    | exact left.ordered.rel_get_of_lt (by change index.val < index.val + 1; omega)
    | exact right.ordered.rel_get_of_lt (by change index.val < index.val + 1; omega)

theorem left_reachable (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost)
    (index : Nat) (within : index < left.values.length) :
    Source (graph leftCost rightCost left right) (roots left.values right.values)
      (.inl ⟨index, within⟩) := by
  exact source_of_fin_chain (graph leftCost rightCost left right) (roots left.values right.values)
    Sum.inl (fun within => by simp [roots, within])
    (fun index within => by simp [graph, neighbors, within]) ⟨index, within⟩

theorem right_reachable (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost)
    (index : Nat) (within : index < right.values.length) :
    Source (graph leftCost rightCost left right) (roots left.values right.values)
      (.inr ⟨index, within⟩) := by
  exact source_of_fin_chain (graph leftCost rightCost left right) (roots left.values right.values)
    Sum.inr (fun within => by simp [roots, within])
    (fun index within => by simp [graph, neighbors, within]) ⟨index, within⟩

theorem all_reachable (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost)
    (index : Index left.values right.values) :
    Source (graph leftCost rightCost left right) (roots left.values right.values) index := by
  cases index with
  | inl index => exact left_reachable leftCost rightCost left right index.val index.isLt
  | inr index => exact right_reachable leftCost rightCost left right index.val index.isLt

theorem decode_injective (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost) :
    Function.Injective (decode left.values right.values) := by
  intro first second same
  apply (Sum.map_injective.mpr ⟨left.distinct.injective_get, right.distinct.injective_get⟩)
  cases first <;> cases second <;> simp_all [decode]

theorem decode_image (left : List Left) (right : List Right) (value : Left ⊕ Right) :
    (∃ index, decode left right index = value) ↔
      sumSource (· ∈ left) (· ∈ right) value := by
  cases value <;> simp [Sum.exists, decode, sumSource, List.mem_iff_get]

def selected (requested : Nat) (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost) : List (Left ⊕ Right) :=
  (((demandMachine (graph leftCost rightCost left right) requested).runSlice requested
    (MonotoneRankEnumeration.initial (roots left.values right.values))).1.published).map
      (decode left.values right.values)

theorem selected_retained_correct (requested : Nat)
    (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost) :
    Correct requested (sumCost leftCost rightCost)
      (sumSource (· ∈ left.values) (· ∈ right.values))
      (selected requested leftCost rightCost left right) := by
  have rankCorrect := graph_prefix_correct (graph leftCost rightCost left right)
    (monotone leftCost rightCost left right) (roots left.values right.values)
    (all_reachable leftCost rightCost left right) requested
  have mapped := map_correct requested (graph leftCost rightCost left right).cost
    (sumCost leftCost rightCost) (fun _ => True) _ rankCorrect
    (decode left.values right.values) (decode_injective leftCost rightCost left right)
    (fun _ => rfl)
  exact mapped.congr_source fun value => by simpa using decode_image left.values right.values value

theorem selected_source_correct (requested : Nat)
    (leftCost : Left → Nat) (rightCost : Right → Nat)
    (leftSource : Left → Prop) (rightSource : Right → Prop)
    (left : Cache Left leftCost) (right : Cache Right rightCost)
    (leftCorrect : Correct requested leftCost leftSource left.values)
    (rightCorrect : Correct requested rightCost rightSource right.values) :
    Correct requested (sumCost leftCost rightCost) (sumSource leftSource rightSource)
      (selected requested leftCost rightCost left right) := by
  classical
  apply extend_by_dominance requested (sumCost leftCost rightCost)
    (sumSource leftSource rightSource) (sumSource (· ∈ left.values) (· ∈ right.values)) _
    (selected_retained_correct requested leftCost rightCost left right)
  · intro value member
    cases value with
    | inl value => exact leftCorrect.sound value member
    | inr value => exact rightCorrect.sound value member
  · intro value allowed missing
    cases value with
    | inl value =>
        exact mapped_witnesses requested (sumCost leftCost rightCost)
          (sumSource (· ∈ left.values) (· ∈ right.values)) (leftCost value)
          left.values left.distinct (leftCorrect.omitted value allowed missing).1 Sum.inl
          Sum.inl_injective (fun _ present => present)
          (fun original present => (leftCorrect.omitted value allowed missing).2 original present)
    | inr value =>
        exact mapped_witnesses requested (sumCost leftCost rightCost)
          (sumSource (· ∈ left.values) (· ∈ right.values)) (rightCost value)
          right.values right.distinct (rightCorrect.omitted value allowed missing).1 Sum.inr
          Sum.inr_injective (fun _ present => present)
          (fun original present => (rightCorrect.omitted value allowed missing).2 original present)

def combined (requested : Nat) (leftCost : Left → Nat) (rightCost : Right → Nat)
    (left : Cache Left leftCost) (right : Cache Right rightCost) :
    Cache (Left ⊕ Right) (sumCost leftCost rightCost) where
  values := selected requested leftCost rightCost left right
  distinct := (selected_retained_correct requested leftCost rightCost left right).distinct
  ordered := (selected_retained_correct requested leftCost rightCost left right).ordered

namespace Controls

def left : Cache Nat id := ⟨[1, 2, 4], by decide, by decide⟩
def right : Cache Nat id := ⟨[1, 3], by decide, by decide⟩

example : (selected 4 id id left right).map (sumCost id id) = [1, 1, 2, 3] := by decide
example : (selected 7 id id left right).length = 5 := by decide
example : (selected 2 id id left right).length = 2 := by decide

end Controls

end Mettapedia.Algorithms.LazyUnionPrefixes
