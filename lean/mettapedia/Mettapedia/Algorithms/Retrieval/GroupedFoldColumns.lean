import Mettapedia.Algorithms.Retrieval.OrderedGroupedFold
import Mathlib.Data.List.OfFn

/-!
Typed dense columns for the result of an ordered grouped fold. Labels retain
first-group encounter order; each field has its own scalar type. Transposing
the completed states changes neither any field value nor the event schedule.

The exact native leaf gate preserves integer and floating payload bits. Its
unsupported cases use the authored constructors instead. The laws below are
representation/operation correspondence, not native implementation proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Retrieval.GroupedFoldColumns

variable {Group Field Event : Type*} {Scalar : Field → Type*}

structure Columns (Group Field : Type*) (Scalar : Field → Type*) (count : Nat) where
  labels : Fin count → Group
  values : (field : Field) → Fin count → Scalar field

def pack (rows : List (Group × ((field : Field) → Scalar field))) :
    Columns Group Field Scalar rows.length where
  labels position := rows[position].1
  values field position := rows[position].2 field

def inspect {count : Nat} (columns : Columns Group Field Scalar count) :
    List (Group × ((field : Field) → Scalar field)) :=
  List.ofFn fun position => (columns.labels position, fun field => columns.values field position)

/-- Reconstruction joins the independently stored columns, in their original
row order, without sorting labels or forgetting repeated occurrences. -/
theorem inspect_pack (rows : List (Group × ((field : Field) → Scalar field))) :
    inspect (pack rows) = rows := by
  change List.ofFn (fun position : Fin rows.length => rows[position]) = rows
  exact List.ofFn_getElem

theorem labels_pack (rows : List (Group × ((field : Field) → Scalar field))) :
    List.ofFn (pack rows).labels = rows.map Prod.fst := by
  have restored := congrArg (List.map Prod.fst) (inspect_pack rows)
  simpa [inspect, List.map_ofFn, Function.comp_def] using restored

theorem field_pack (rows : List (Group × ((field : Field) → Scalar field))) (field : Field) :
    List.ofFn ((pack rows).values field) = rows.map (fun row => row.2 field) := by
  have restored := congrArg (List.map (fun row => row.2 field)) (inspect_pack rows)
  simpa [inspect, List.map_ofFn, Function.comp_def] using restored

/-- Any ordered grouped algorithm can publish columns and retain exactly its
original per-group left fold. No independence or associativity is assumed. -/
theorem observe_grouped_columns [DecidableEq Group]
    (project : Event → Group)
    (step : ((field : Field) → Scalar field) → Event → ((field : Field) → Scalar field))
    (initial : Group → ((field : Field) → Scalar field))
    (state : List (Group × ((field : Field) → Scalar field))) (events : List Event) (group : Group) :
    OrderedGroupedFold.observe initial
      (inspect (pack (OrderedGroupedFold.groupedBy project step initial state events))) group =
      events.foldl (fun accumulator event =>
        if project event = group then step accumulator event else accumulator)
        (OrderedGroupedFold.observe initial state group) := by
  rw [inspect_pack, OrderedGroupedFold.observe_groupedBy]

theorem grouped_column_label_order [DecidableEq Group]
    (project : Event → Group)
    (step : ((field : Field) → Scalar field) → Event → ((field : Field) → Scalar field))
    (initial : Group → ((field : Field) → Scalar field))
    (state : List (Group × ((field : Field) → Scalar field))) (events : List Event) :
    List.ofFn (pack (OrderedGroupedFold.groupedBy project step initial state events)).labels =
      events.foldl (fun labels event =>
        if project event ∈ labels then labels else labels ++ [project event]) (state.map Prod.fst) := by
  rw [labels_pack, OrderedGroupedFold.keys_groupedBy]

inductive DType where
  | i64 | f64
  deriving DecidableEq

inductive Leaf where
  | integer (bits : UInt64)
  | floating (bits : UInt64)
  deriving DecidableEq

def exactLeaf : DType → Leaf → Option UInt64
  | .i64, .integer bits => some bits
  | .f64, .floating bits => some bits
  | _, _ => none

def restoreLeaf : DType → UInt64 → Leaf
  | .i64, bits => .integer bits
  | .f64, bits => .floating bits

theorem exactLeaf_restore (dtype : DType) (bits : UInt64) :
    exactLeaf dtype (restoreLeaf dtype bits) = some bits := by cases dtype <;> rfl

/-- Successful exact admission retains both the dtype tag and all scalar bits.
It cannot silently reinterpret or round an integer as a floating value. -/
theorem restore_exactLeaf (dtype : DType) (leaf : Leaf) (bits : UInt64)
    (admitted : exactLeaf dtype leaf = some bits) : restoreLeaf dtype bits = leaf := by
  cases dtype <;> cases leaf <;> simp_all [exactLeaf, restoreLeaf]

example : exactLeaf .f64 (.integer 7) = none := rfl
example : restoreLeaf .f64 0 ≠ restoreLeaf .f64 0x8000000000000000 := by decide +kernel
example : List.ofFn (pack ([(3, fun (_ : Unit) => 0), (3, fun _ => 0)] :
    List (Nat × (Unit → Nat)))).labels = [3, 3] := by rw [labels_pack]; rfl
example : List.ofFn ((pack ([(3, fun (_ : Unit) => 0)] : List (Nat × (Unit → Nat)))).values ()) =
    [0] := by rw [field_pack]; rfl

#print axioms inspect_pack
#print axioms observe_grouped_columns
#print axioms grouped_column_label_order
#print axioms restore_exactLeaf

end Mettapedia.Algorithms.Retrieval.GroupedFoldColumns
