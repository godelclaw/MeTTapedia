import Mettapedia.GSLT.Parsing.ClassAwarePackedForestKBest
import Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract

/-!
# Policy-directed extraction from immutable packed storage

The policy is tested on a physical family before any child Cartesian product
is expanded. The resulting ordered derivation list is exactly unrestricted
extraction followed by the recursive family policy. Neither the store nor its
provenance is pruned. This is a selection theorem, not parser completeness.

Finite unfolding depth is an explicit reference parameter. No finite depth is
asserted complete for arbitrary cyclic packed storage.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PackedForestSelection

universe u v

/-- Physical families, including their ordered source occurrence, are retained
at every derivation node. Equal rendered CSTs need not identify derivations. -/
inductive Derivation (Family : Type u) where
  | node (family : Family) (children : List (Derivation Family))
  deriving Repr

mutual
  def selected {Family : Type u} (allow : Family → Bool) : Derivation Family → Bool
    | .node family children => allow family && selectedChildren allow children
  def selectedChildren {Family : Type u} (allow : Family → Bool) : List (Derivation Family) → Bool
    | [] => true
    | child :: rest => selected allow child && selectedChildren allow rest
end

theorem selectedChildren_eq_all {Family : Type u} (allow : Family → Bool)
    (children : List (Derivation Family)) :
    selectedChildren allow children = children.all (selected allow) := by
  induction children with
  | nil => rfl
  | cons child rest ih => simp [selectedChildren, ih]

def combinations {α : Type u} : List (List α) → List (List α)
  | [] => [[]]
  | choices :: rest => choices.flatMap fun first => (combinations rest).map (first :: ·)

theorem combinations_filter {α : Type u} (allow : α → Bool) (choices : List (List α)) :
    combinations (choices.map (List.filter allow)) =
      (combinations choices).filter (List.all · allow) := by
  induction choices with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, combinations, ih, List.filter_flatMap]
      induction first with
      | nil => rfl
      | cons head tail tailIH =>
          cases accepted : allow head <;>
            simp [accepted, List.filter_map, Function.comp_def, tailIH]

/-- A direct extraction algorithm over shared family references. Rejected
families do not demand or combine any of their child results. -/
def extract {Key : Type u} {Family : Type v}
    (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool) :
    Nat → Key → List (Derivation Family)
  | 0, _ => []
  | depth + 1, key => (families key).flatMap fun family =>
      if allow family then
        (combinations ((children family).map (extract families children allow depth))).map (.node family)
      else []

theorem extract_all_selected {Key : Type u} {Family : Type v}
    (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (depth : Nat) (key : Key) :
    extract families children allow depth key =
      (extract families children (fun _ => true) depth key).filter (selected allow) := by
  induction depth generalizing key with
  | zero => rfl
  | succ depth ih =>
      simp only [extract, ↓reduceIte, List.filter_flatMap]
      apply congrArg (List.flatMap · (families key))
      funext family
      simp only [List.filter_map, Function.comp_def, selected, selectedChildren_eq_all]
      cases allow family with
      | false => simp
      | true =>
          simp only [Bool.true_and, ↓reduceIte]
          apply congrArg (List.map (Derivation.node family))
          have childrenExact :
              (children family).map (extract families children allow depth) =
                ((children family).map (extract families children (fun _ => true) depth)).map
                  (List.filter (selected allow)) := by
            simp only [List.map_map, Function.comp_def]
            apply List.map_congr_left
            intro child present
            exact ih child
          rw [childrenExact, combinations_filter]

/-- Exact ordered output equality transports through any subsequent semantic
projection, including partial projection. No injectivity or deduplication is
assumed, so occurrence multiplicity remains observable. -/
theorem selected_projections_exact {Key : Type u} {Family : Type v} {Output : Type}
    (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (project : Derivation Family → Option Output) (depth : Nat) (key : Key) :
    (extract families children allow depth key).filterMap project =
      ((extract families children (fun _ => true) depth key).filter (selected allow)).filterMap project := by
  rw [extract_all_selected]

/-- A physical flattened-family identity includes its array occurrence, not
merely equal payload. Existing terminal references and span keys stay in the
same `family` value. -/
structure PhysicalFamily where
  position : Nat
  family : ClassAwarePackedForest.Family
  deriving Repr, DecidableEq

def physicalFamilies (forest : ClassAwarePackedForest.Forest)
    (key : ClassAwarePackedForest.NodeKey) : List PhysicalFamily :=
  (forest.families.zipIdx).filterMap fun entry =>
    if entry.1.parent = key then some ⟨entry.2, entry.1⟩ else none

def physicalChildren (family : PhysicalFamily) : List ClassAwarePackedForest.NodeKey :=
  ClassAwarePackedForestKBest.nodeChildren family.family.children

def extractForest (forest : ClassAwarePackedForest.Forest) (allow : PhysicalFamily → Bool)
    (depth : Nat) (key : ClassAwarePackedForest.NodeKey) : List (Derivation PhysicalFamily) :=
  extract (physicalFamilies forest) physicalChildren allow depth key

theorem extractForest_selected_exact (forest : ClassAwarePackedForest.Forest)
    (allow : PhysicalFamily → Bool) (depth : Nat) (key : ClassAwarePackedForest.NodeKey) :
    extractForest forest allow depth key =
      (extractForest forest (fun _ => true) depth key).filter (selected allow) :=
  extract_all_selected _ _ _ _ _

theorem rejected_family_performs_no_child_expansion {Key : Type u} {Family : Type v}
    (children : Family → List Key) (allow : Family → Bool) (family : Family)
    (rejected : allow family = false) (depth : Nat) (key : Key) :
    extract (fun _ : Key => [family]) children allow (depth + 1) key = [] := by
  simp [extract, rejected]

namespace Controls

private def families : Nat → List Nat
  | 0 => [10, 11]
  | 1 => [20, 21]
  | _ => []

private def children : Nat → List Nat
  | 10 | 11 => [1, 1]
  | _ => []

private def keep (family : Nat) : Bool := family != 20

theorem child_filter_precedes_cartesian_product :
    (extract families children keep 2 0).length = 2 ∧
      (extract families children (fun _ => true) 2 0).length = 8 := by decide

theorem equal_outputs_retain_distinct_family_occurrences :
    (extract families children keep 2 0).map (fun _ => "same") = ["same", "same"] := by decide

theorem rejected_parent_cannot_leak_a_selected_descendant :
    extract (fun _ : Nat => [10]) children (fun family => family != 10) 2 0 = [] := by
  simp [extract]

end Controls

end Mettapedia.GSLT.Parsing.PackedForestSelection
