import Mettapedia.Languages.C11.ObjectLayout
import Mettapedia.Machines.CMemory.Borrowing

/-!
# Subobject layout and ownership ranges

The layout model supplies padded sizes and member offsets. This bridge proves
that projecting record members and array elements supplies contained regions,
and that distinct non-overlapping subobjects can be borrowed independently.
Union alternatives deliberately do not satisfy that independence rule.

The ABI profile and the native frontend's calculation of layouts are separate
implementation obligations. These results apply to every layout admitted by
the existing mathematical model, not just one concrete record.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.BorrowingLayouts

open ObjectLayout
open Mettapedia.Machines.CMemory.Borrowing

def objectRegion (root origin : Nat) (layout : Layout) : Region :=
  ⟨root, origin, layout.bytes⟩

def memberRegion (root origin : Nat) (member : Member) : Region :=
  ⟨root, origin + member.offset, member.layout.bytes⟩

theorem member_contained (root origin : Nat) (fields : List Layout) (nonempty : fields ≠ [])
    (member : Member) (present : member ∈ (place fields 0).1) :
    (objectRegion root origin (record fields nonempty)).Contains (memberRegion root origin member) := by
  have bound := record_member_bounds fields nonempty member present
  unfold Region.Contains Region.finish objectRegion memberRegion
  dsimp
  constructor
  · rfl
  · constructor
    · omega
    · change member.offset + member.layout.bytes ≤ _ at bound
      omega

theorem ordered_members_disjoint (root origin : Nat) {left right : Member}
    (order : left.endOffset ≤ right.offset) :
    (memberRegion root origin left).Disjoint (memberRegion root origin right) := by
  apply Or.inr
  apply Or.inl
  change origin + left.offset + left.layout.bytes ≤ origin + right.offset
  unfold Member.endOffset at order
  omega

theorem record_regions_pairwise_disjoint (root origin : Nat) (fields : List Layout) :
    ((place fields 0).1.map (memberRegion root origin)).Pairwise Region.Disjoint := by
  rw [List.pairwise_map]
  exact (place_ordered fields 0).imp (fun ordered => ordered_members_disjoint root origin ordered)

def elementRegion (root origin : Nat) (element : Layout) (index : Nat) : Region :=
  ⟨root, origin + index * element.bytes, element.bytes⟩

theorem array_element_contained (root origin : Nat) (element : Layout) {count index : Nat}
    (positive : 0 < count) (inside : index < count) :
    (objectRegion root origin (array element count positive)).Contains
      (elementRegion root origin element index) := by
  have bound := Nat.mul_le_mul_right element.bytes (Nat.succ_le_of_lt inside)
  simp only [Nat.succ_mul] at bound
  rw [Nat.mul_comm count element.bytes] at bound
  unfold Region.Contains Region.finish objectRegion elementRegion array
  dsimp
  constructor
  · rfl
  · constructor
    · omega
    · omega

theorem array_elements_disjoint (root origin : Nat) (element : Layout) {i j : Nat}
    (different : i ≠ j) :
    (elementRegion root origin element i).Disjoint (elementRegion root origin element j) := by
  rcases Nat.lt_or_gt_of_ne different with before | after
  · have bound := Nat.mul_le_mul_right element.bytes (Nat.succ_le_of_lt before)
    simp only [Nat.succ_mul] at bound
    apply Or.inr; apply Or.inl
    change origin + i * element.bytes + element.bytes ≤ origin + j * element.bytes
    omega
  · have bound := Nat.mul_le_mul_right element.bytes (Nat.succ_le_of_lt after)
    simp only [Nat.succ_mul] at bound
    apply Or.inr; apply Or.inr
    change origin + j * element.bytes + element.bytes ≤ origin + i * element.bytes
    omega

/-- Treating union alternatives as separate fields would permit two exclusive
loans to the same bytes; the record rule cannot be used for a union. -/
theorem union_alternatives_overlap (root origin : Nat) (left right : Layout) :
    ¬(objectRegion root origin left).Disjoint (objectRegion root origin right) := by
  intro apart
  have lp := left.positive
  have rp := right.positive
  unfold Region.Disjoint Region.finish objectRegion at apart
  dsimp at apart
  rcases apart with wrong | wrong | wrong
  · exact wrong rfl
  · omega
  · omega

end Mettapedia.Languages.C11.BorrowingLayouts
