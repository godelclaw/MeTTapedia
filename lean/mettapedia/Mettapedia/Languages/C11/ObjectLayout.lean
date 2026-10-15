import Mettapedia.Languages.C11.ArrayPointers
import Mathlib.Algebra.Order.Floor.Div

/-!
# Constructed array and aggregate layouts

The admitted layout policy uses power-of-two byte alignments, ordered
structure members with minimal inter-member padding, and final padding to
the maximum member alignment. Union members start together and may overlap.
Arrays use the complete padded element size as their stride. Every
construction proves its alignment, positivity and byte bounds, for arbitrary
member lists and recursively constructed element layouts.

This is a named layout policy, not a theorem that every native C ABI chooses
it. Scalar sizes/alignments are inputs supplied by an implementation profile.
Bit-field allocation units, flexible array members, over-alignment and GNU
packed/empty aggregates require further profiles. Member types, effective
types and elaboration from declarations are not erased by a layout theorem;
their source connection is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ObjectLayout

structure Layout where
  alignmentExponent : Nat
  bytes : Nat
  positive : 0 < bytes
  alignedSize : 2 ^ alignmentExponent ∣ bytes
  deriving DecidableEq, Repr

def Layout.alignment (layout : Layout) : Nat := 2 ^ layout.alignmentExponent

theorem Layout.alignment_positive (layout : Layout) : 0 < layout.alignment :=
  Nat.pow_pos (by decide)

def roundUp (offset alignment : Nat) : Nat := alignment * (offset ⌈/⌉ alignment)

theorem roundUp_ge (offset alignment : Nat) (positive : 0 < alignment) :
    offset ≤ roundUp offset alignment := by
  exact (ceilDiv_le_iff_le_mul positive).mp (Nat.le_refl (offset ⌈/⌉ alignment))

theorem roundUp_aligned (offset alignment : Nat) : alignment ∣ roundUp offset alignment := by
  exact ⟨offset ⌈/⌉ alignment, rfl⟩

theorem roundUp_le (offset alignment bound : Nat) (positive : 0 < alignment)
    (aligned : alignment ∣ bound) (lower : offset ≤ bound) : roundUp offset alignment ≤ bound := by
  obtain ⟨multiple, rfl⟩ := aligned
  have quotient : offset ⌈/⌉ alignment ≤ multiple := (ceilDiv_le_iff_le_mul positive).mpr lower
  exact Nat.mul_le_mul_left alignment quotient

theorem roundUp_of_aligned (offset alignment : Nat) (positive : 0 < alignment)
    (aligned : alignment ∣ offset) : roundUp offset alignment = offset :=
  Nat.le_antisymm (roundUp_le offset alignment offset positive aligned (Nat.le_refl _))
    (roundUp_ge offset alignment positive)

def array (element : Layout) (count : Nat) (positive : 0 < count) : Layout where
  alignmentExponent := element.alignmentExponent
  bytes := element.bytes * count
  positive := Nat.mul_pos element.positive positive
  alignedSize := dvd_mul_of_dvd_left element.alignedSize count

@[simp]
theorem array_bytes (element : Layout) (count : Nat) (positive : 0 < count) :
    (array element count positive).bytes = element.bytes * count := rfl

@[simp]
theorem array_alignment (element : Layout) (count : Nat) (positive : 0 < count) :
    (array element count positive).alignment = element.alignment := rfl

structure Member where
  layout : Layout
  offset : Nat
  deriving DecidableEq, Repr

def Member.endOffset (member : Member) : Nat := member.offset + member.layout.bytes

def place (fields : List Layout) (cursor : Nat) : List Member × Nat := match fields with
  | [] => ([], cursor)
  | head :: tail =>
      let start := roundUp cursor head.alignment
      let rest := place tail (start + head.bytes)
      (⟨head, start⟩ :: rest.1, rest.2)

theorem place_shape (fields : List Layout) (cursor : Nat) :
    (place fields cursor).1.map Member.layout = fields := by
  induction fields generalizing cursor with
  | nil => rfl
  | cons head tail ih => simp only [place, List.map_cons, ih]

theorem place_end_ge (fields : List Layout) (cursor : Nat) : cursor ≤ (place fields cursor).2 := by
  induction fields generalizing cursor with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
      have start := roundUp_ge cursor head.alignment head.alignment_positive
      have rest := ih (roundUp cursor head.alignment + head.bytes)
      change cursor ≤ (place tail (roundUp cursor head.alignment + head.bytes)).2
      omega

theorem place_member_bounds (fields : List Layout) (cursor : Nat) (member : Member)
    (present : member ∈ (place fields cursor).1) :
    cursor ≤ member.offset ∧ member.endOffset ≤ (place fields cursor).2 ∧
      member.layout.alignment ∣ member.offset := by
  induction fields generalizing cursor with
  | nil => cases present
  | cons head tail ih =>
      have startBound := roundUp_ge cursor head.alignment head.alignment_positive
      simp only [place, List.mem_cons] at present
      rcases present with rfl | present
      · exact ⟨startBound, place_end_ge tail _, roundUp_aligned _ _⟩
      · obtain ⟨lower, upper, aligned⟩ := ih _ present
        exact ⟨by omega, upper, aligned⟩

theorem place_ordered (fields : List Layout) (cursor : Nat) :
    (place fields cursor).1.Pairwise (fun left right => left.endOffset ≤ right.offset) := by
  induction fields generalizing cursor with
  | nil => exact .nil
  | cons head tail ih =>
      apply List.pairwise_cons.mpr
      exact ⟨fun member present => (place_member_bounds tail _ member present).1, ih _⟩

theorem place_positive_end (fields : List Layout) (cursor : Nat) (nonempty : fields ≠ []) :
    0 < (place fields cursor).2 := by
  cases fields with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      have rest := place_end_ge tail (roundUp cursor head.alignment + head.bytes)
      have positive := head.positive
      change 0 < (place tail (roundUp cursor head.alignment + head.bytes)).2
      omega

def maximumAlignmentExponent : List Layout → Nat
  | [] => 0
  | head :: tail => max head.alignmentExponent (maximumAlignmentExponent tail)

theorem alignmentExponent_le_maximum (fields : List Layout) (field : Layout) (present : field ∈ fields) :
    field.alignmentExponent ≤ maximumAlignmentExponent fields := by
  induction fields with
  | nil => cases present
  | cons head tail ih =>
      rcases List.mem_cons.mp present with rfl | present
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih present) (Nat.le_max_right _ _)

def record (fields : List Layout) (nonempty : fields ≠ []) : Layout where
  alignmentExponent := maximumAlignmentExponent fields
  bytes := roundUp (place fields 0).2 (2 ^ maximumAlignmentExponent fields)
  positive := Nat.lt_of_lt_of_le (place_positive_end fields 0 nonempty)
    (roundUp_ge _ _ (Nat.pow_pos (by decide)))
  alignedSize := roundUp_aligned _ _

theorem record_member_bounds (fields : List Layout) (nonempty : fields ≠ []) (member : Member)
    (present : member ∈ (place fields 0).1) : member.endOffset ≤ (record fields nonempty).bytes := by
  exact Nat.le_trans (place_member_bounds fields 0 member present).2.1
    (roundUp_ge _ _ (Nat.pow_pos (by decide)))

theorem record_member_alignment (fields : List Layout) (nonempty : fields ≠ []) (field : Layout)
    (present : field ∈ fields) : field.alignment ∣ (record fields nonempty).alignment := by
  exact Nat.pow_dvd_pow 2 (alignmentExponent_le_maximum fields field present)

def maximumBytes : List Layout → Nat
  | [] => 0
  | head :: tail => max head.bytes (maximumBytes tail)

theorem bytes_le_maximum (fields : List Layout) (field : Layout) (present : field ∈ fields) :
    field.bytes ≤ maximumBytes fields := by
  induction fields with
  | nil => cases present
  | cons head tail ih =>
      rcases List.mem_cons.mp present with rfl | present
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih present) (Nat.le_max_right _ _)

theorem maximumBytes_positive (fields : List Layout) (nonempty : fields ≠ []) :
    0 < maximumBytes fields := by
  cases fields with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail => exact Nat.lt_of_lt_of_le head.positive (Nat.le_max_left _ _)

def union (fields : List Layout) (nonempty : fields ≠ []) : Layout where
  alignmentExponent := maximumAlignmentExponent fields
  bytes := roundUp (maximumBytes fields) (2 ^ maximumAlignmentExponent fields)
  positive := Nat.lt_of_lt_of_le (maximumBytes_positive fields nonempty)
    (roundUp_ge _ _ (Nat.pow_pos (by decide)))
  alignedSize := roundUp_aligned _ _

theorem union_member_bounds (fields : List Layout) (nonempty : fields ≠ []) (field : Layout)
    (present : field ∈ fields) : field.bytes ≤ (union fields nonempty).bytes :=
  Nat.le_trans (bytes_le_maximum fields field present) (roundUp_ge _ _ (Nat.pow_pos (by decide)))

theorem union_member_alignment (fields : List Layout) (nonempty : fields ≠ []) (field : Layout)
    (present : field ∈ fields) : field.alignment ∣ (union fields nonempty).alignment :=
  Nat.pow_dvd_pow 2 (alignmentExponent_le_maximum fields field present)

/-- The array descriptor's stride is constructed from the padded element
layout, including the size of a nested array or aggregate. -/
def view (allocation : Nat) (origin : Nat) (element : Layout) (count : Nat) : ArrayPointers.Descriptor :=
  ⟨allocation, origin, element.bytes, count⟩

theorem view_stride_positive (allocation origin : Nat) (element : Layout) (count : Nat) :
    0 < (view allocation origin element count).elementBytes := element.positive

theorem nested_array_stride (allocation origin : Nat) (element : Layout) (columns rows : Nat)
    (positive : 0 < columns) :
    (view allocation origin (array element columns positive) rows).elementBytes = element.bytes * columns := rfl

end Mettapedia.Languages.C11.ObjectLayout
