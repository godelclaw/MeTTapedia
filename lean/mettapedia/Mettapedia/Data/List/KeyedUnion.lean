import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Image

/-!
# Ordered union by a retained representation key

Insert the left list into the right list in source order. A key already
present keeps its existing representative. Mapping the keys commutes with
this operation. A logical readout preserves union precisely when equal keys
identify equal readouts on the admitted inputs.
-/

set_option autoImplicit false

namespace List.KeyedUnion

universe u v w
variable {Value : Type u} {Key : Type v} {View : Type w}

def merge [DecidableEq Key] (key : Value → Key) : List Value → List Value → List Value
  | [], right => right
  | first :: rest, right =>
      merge key rest (if key first ∈ right.map key then right else first :: right)

theorem map_keys [DecidableEq Key] (key : Value → Key) (left right : List Value) :
    (merge key left right).map key =
      (left.map key).foldl (fun items item => if item ∈ items then items else item :: items)
        (right.map key) := by
  induction left generalizing right with
  | nil => rfl
  | cons first rest ih =>
      simp only [merge, List.map_cons, List.foldl_cons]
      split <;> simp only [ih, List.map_cons]

theorem mem_subset [DecidableEq Key] (key : Value → Key) (left right : List Value)
    {value : Value} (member : value ∈ merge key left right) : value ∈ left ++ right := by
  induction left generalizing right with
  | nil => exact member
  | cons first rest ih =>
      simp only [merge] at member
      split at member
      · have smaller := ih right member
        simp only [List.mem_append, List.mem_cons] at smaller ⊢
        tauto
      · have smaller := ih (first :: right) member
        simp only [List.mem_append, List.mem_cons] at smaller ⊢
        tauto

theorem key_mem [DecidableEq Key] (key : Value → Key) (left right : List Value) (item : Key) :
    item ∈ (merge key left right).map key ↔ item ∈ left.map key ∨ item ∈ right.map key := by
  induction left generalizing right with
  | nil => simp [merge]
  | cons first rest ih =>
      simp only [merge]
      split
      · rename_i present
        rw [ih]
        simp only [List.map_cons, List.mem_cons]
        constructor
        · rintro (member | member)
          · exact Or.inl (Or.inr member)
          · exact Or.inr member
        · rintro ((rfl | member) | member)
          · exact Or.inr present
          · exact Or.inl member
          · exact Or.inr member
      · rw [ih]
        simp only [List.map_cons, List.mem_cons]
        tauto

/-- Faithfulness is needed only on the actual input inventory. -/
theorem readout_support [DecidableEq Key] [DecidableEq View]
    (key : Value → Key) (readout : Value → View) (left right : List Value)
    (faithful : ∀ first ∈ left ++ right, ∀ second ∈ left ++ right,
      key first = key second → readout first = readout second) :
    ((merge key left right).map readout).toFinset =
      (left.map readout).toFinset ∪ (right.map readout).toFinset := by
  apply Finset.ext
  intro observed
  simp only [List.mem_toFinset, Finset.mem_union]
  constructor
  · intro member
    obtain ⟨value, present, rfl⟩ := List.mem_map.mp member
    have admitted := mem_subset key left right present
    rcases List.mem_append.mp admitted with before | after
    · exact Or.inl (List.mem_map.mpr ⟨value, before, rfl⟩)
    · exact Or.inr (List.mem_map.mpr ⟨value, after, rfl⟩)
  · intro member
    have witness : ∃ value ∈ left ++ right, readout value = observed := by
      rcases member with before | after
      · obtain ⟨value, present, same⟩ := List.mem_map.mp before
        exact ⟨value, List.mem_append_left right present, same⟩
      · obtain ⟨value, present, same⟩ := List.mem_map.mp after
        exact ⟨value, List.mem_append_right left present, same⟩
    obtain ⟨value, admitted, same⟩ := witness
    have keyPresent : key value ∈ (merge key left right).map key := by
      apply (key_mem key left right (key value)).mpr
      rcases List.mem_append.mp admitted with before | after
      · exact Or.inl (List.mem_map.mpr ⟨value, before, rfl⟩)
      · exact Or.inr (List.mem_map.mpr ⟨value, after, rfl⟩)
    obtain ⟨retained, present, sameKey⟩ := List.mem_map.mp keyPresent
    exact List.mem_map.mpr ⟨retained, present,
      (faithful retained (mem_subset key left right present) value admitted sameKey).trans same⟩

theorem repeated_keys_retain_source_order :
    merge id [1, 2, 1] [3, 1] = [2, 3, 1] := by decide

/-- A key that erases a distinguished field cannot preserve that readout. -/
theorem unequal_payload_readout_not_preserved :
    ((merge Prod.fst [(1, 7), (1, 8)] []).map Prod.snd).toFinset ≠
      (([(1, 7), (1, 8)] : List (Nat × Nat)).map Prod.snd).toFinset := by decide

end List.KeyedUnion
